import os
import re
import subprocess
from pathlib import Path

def _extract_define_funs(s: str):
    out, i = [], 0
    while True:
        i = s.find("(define-fun", i)
        if i == -1: break
        depth, j = 0, i
        while j < len(s):
            if s[j] == "(": depth += 1
            elif s[j] == ")":
                depth -= 1
                if depth == 0:
                    j += 1; break
            j += 1
        block = s[i:j]
        m = re.search(r"\(define-fun\s+([^\s()]+)", block)
        if m: out.append((m.group(1), block))
        i = j
    return out  # list[(name, block)]

def _split_define_fun(block: str):
    """
    Robustly split a single (define-fun ...) into:
      name, params(list[str]), header(str up to and incl. return sort), body(str, without final ')')
    Works regardless of newlines/spacing.
    """
    b = block.lstrip()
    m = re.match(r"\(define-fun\s+([^\s()]+)\s*", b)
    if not m:
        raise ValueError("Not a (define-fun ...) block")
    name = m.group(1)
    i = m.end()

    def _skip_ws(s, k):
        while k < len(s) and s[k].isspace():
            k += 1
        return k

    def _read_sexpr(s, k):
        assert s[k] == "(", "Expected '('"
        depth = 0
        j = k
        while j < len(s):
            ch = s[j]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    return j + 1  # index just after closing ')'
            j += 1
        raise ValueError("Unbalanced parentheses")

    # params s-expr
    i = _skip_ws(b, i)
    if b[i] != "(":
        raise ValueError("Expected '(' starting params")
    params_end = _read_sexpr(b, i)
    params_str = b[i:params_end]
    params = re.findall(r"\(\s*([A-Za-z_]\w*)\s+\([^)]+\)\s*\)", params_str)

    # return sort s-expr
    i = _skip_ws(b, params_end)
    if b[i] != "(":
        raise ValueError("Expected '(' starting return sort")
    ret_end = _read_sexpr(b, i)

    # header is everything up to (and incl.) return sort
    header = b[:ret_end]

    # body is the remainder minus the final ')'
    body = b[ret_end:].strip()
    if not body.endswith(")"):
        raise ValueError("define-fun body missing closing ')'")
    body = body[:-1].strip()

    return name, params, header, body

def _inline_helpers_in_block(block: str, helper_index: dict[str, str]) -> str:
    name, params, header, body = _split_define_fun(block)

    # Inline calls to known helpers with identifier args
    changed = True
    while changed:
        changed = False
        for hname, hblock in helper_index.items():
            h_nm, h_params, _h_header, h_body = _split_define_fun(hblock)
            if h_nm != hname:
                continue
            new_body = _inline_one_call(body, hname, h_params, h_body)
            if new_body != body:
                body = new_body
                changed = True

    # Rebuild: original header + (possibly inlined) body + ')'
    return header + " " + body + ")"

def _mangle_locals(body: str, callee: str) -> str:
    # Rename typical helper locals like _let_1 to avoid collisions
    # Only touches the callee body, so it can’t affect caller bindings.
    return re.sub(r"\b_let_(\d+)\b", rf"__{callee}__let_\1", body)

def _inline_one_call(body: str, callee: str, formals: list[str], callee_body: str):
    args_pat = r"\s+".join([r"([A-Za-z_]\w*)"] * len(formals))
    pat = re.compile(r"\(" + re.escape(callee) + r"\s+" + args_pat + r"\)")

    def repl(m):
        actuals = m.groups()
        sub = _mangle_locals(callee_body, callee)
        for f, a in zip(formals, actuals):
            sub = re.sub(rf"\b{re.escape(f)}\b", a, sub)
        return sub

    prev = None
    while prev != body:
        prev, body = body, pat.sub(repl, body)
    return body


def _build_helper_index(smt_dir: Path) -> dict[str, str]:
    index = {}
    for p in smt_dir.glob("*.smt2"):
        try:
            txt = p.read_text()
            for nm, blk in _extract_define_funs(txt):
                index[nm] = blk
        except Exception:
            pass
    return index

def _debug_dump_inlined(block: str, smt_path: str, func_name: str) -> str:
    dbg_dir = Path(smt_path).parent / "_debug"
    dbg_dir.mkdir(parents=True, exist_ok=True)
    dbg_file = dbg_dir / f"inlined_{func_name}.smt2"
    dbg_file.write_text(block + "\n")

    # Quick, actionable checks
    opens, closes = block.count("("), block.count(")")
    if opens != closes:
        print(f"[DEBUG] Paren mismatch: opens={opens} closes={closes}")

    # Did we forget to inline any helpers?
    leftover = re.findall(r"\(\s*(align_mantissas|select_exponent|[A-Za-z_]\w+)\s", block)
    # Filter out the current top function name and SMT keywords
    keywords = {"define-fun","let","concat","bvadd","bvashr","bvsub","sign_extend","extract",
                "ite","bvsge","bvslt","bvsle","bvneg"}
    leftover = [x for x in leftover if x not in keywords and x != func_name]
    if leftover:
        print(f"[DEBUG] Possible uninlined calls still present: {sorted(set(leftover))}")

    print(f"[DEBUG] Wrote inlined SMT to: {dbg_file}")
    return str(dbg_file)

def _run_smt2c_block(block: str, smt2c_path: str, smt_path: str, func_name: str) -> str | None:
    # Save for inspection even on success.
    dbg_file = _debug_dump_inlined(block, smt_path, func_name)

    # IMPORTANT: smt2c expects the full (define-fun ...) as a single arg
    one_line = re.sub(r"\s+", " ", block.strip())

    try:
        res = subprocess.run([smt2c_path, one_line],
                             capture_output=True, text=True, check=True, timeout=30)
        out = res.stdout.strip()
        if not out:
            print("[ERROR] smt2c produced no output.")
            print(f"[DEBUG] Input length={len(one_line)}; preview='{one_line[:140]}...'")
            print(f"[DEBUG] See {dbg_file}")
            return None
        return out
    except subprocess.CalledProcessError as e:
        print("[ERROR] smt2c failed.")
        print(f"[DEBUG] returncode={e.returncode}")
        if e.stderr: print(f"[DEBUG] stderr:\n{e.stderr.strip()}")
        if e.stdout: print(f"[DEBUG] stdout:\n{e.stdout.strip()}")
        # Always show a short preview of the exact input
        print(f"[DEBUG] Arg length={len(one_line)}")
        print(f"[DEBUG] Arg start: {one_line[:180]}")
        print(f"[DEBUG] Arg end  : {one_line[-180:]}")
        print(f"[DEBUG] Full inlined SMT written to: {dbg_file}")
        return None

def run_smt2c_translation(smt_path: str, save_dir: str) -> str | None:
    smt2c_path = os.path.expanduser("~/Desktop/Uni/Year_4/Dissertation/smt2c/src/smt2c")
    if not os.path.exists(smt2c_path):
        print(f"[ERROR] smt2c binary not found at {smt2c_path}")
        return None
    if not os.path.exists(smt_path):
        print(f"[WARN] SMT2 file not found at {smt_path}")
        return None

    print("\nTranslating SMT output to C using smt2c...\n")
    smt_dir = Path(smt_path).parent
    smt_text = Path(smt_path).read_text()

    # Build an index of all available helpers from results/smt2/
    helper_index = _build_helper_index(smt_dir)

    # This file may contain one or many define-funs; translate each
    defs = _extract_define_funs(smt_text)
    if not defs:
        print("[ERROR] No (define-fun ...) found.")
        return None

    c_funcs = []
    for name, block in defs:
        inlined_block = _inline_helpers_in_block(block, helper_index)
        c_text = _run_smt2c_block(inlined_block, smt2c_path, smt_path, name)
        if c_text:
            c_funcs.append(c_text)
        else:
            print(f"[WARN] Skipping function '{name}' due to smt2c error.")

    if not c_funcs:
        return None

    os.makedirs(save_dir, exist_ok=True)
    out_path = os.path.join(save_dir, f"{Path(smt_path).stem}.c")
    Path(out_path).write_text("\n\n".join(c_funcs) + "\n")
    print(f"C file saved to: {out_path}\n")
    print("Generated C code:\n")
    print("\n\n".join(c_funcs))
    return out_path


if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python translate_smt_to_c.py <path_to_smt2_file>")
        sys.exit(1)

    run_smt2c_translation(sys.argv[1], "results/c")
