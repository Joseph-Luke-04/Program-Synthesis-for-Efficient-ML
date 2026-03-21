import os, re
from pathlib import Path

_HEADER = "#include <ap_int.h>\n\n"

# Header & cast normalisation (preserve parens)
def _ensure_header(s: str) -> str:
    return s if "#include <ap_int.h>" in s else _HEADER + s.strip()

def _normalize_char_types_and_casts(s: str) -> str:
    s = re.sub(r"\b__CPROVER_bool\b", "bool", s)

    # Decls
    s = re.sub(r"\bunsigned\s+short\s+int\b", "ap_uint<16>", s)
    s = re.sub(r"\bsigned\s+short\s+int\b", "ap_int<16>", s)
    s = re.sub(r"(?<!unsigned\s)(?<!signed\s)\bshort\s+int\b", "ap_int<16>", s)
    s = re.sub(r"\bunsigned\s+char\b", "ap_uint<8>", s)
    s = re.sub(r"\bsigned\s+char\b",   "ap_int<8>",  s)
    s = re.sub(r'\bunsigned\s+int\b', 'ap_uint<32>', s)
    s = re.sub(r'(?<!unsigned\s)\bint\b', 'ap_int<32>', s)

    # Casts (keep parentheses intact)
    s = re.sub(r"\(\s*unsigned\s+short\s+int\s*\)", "(ap_uint<16>)", s)
    s = re.sub(r"\(\s*signed\s+short\s+int\s*\)",   "(ap_int<16>)",  s)
    s = re.sub(r"\(\s*short\s+int\s*\)",            "(ap_int<16>)",  s)
    s = re.sub(r"\(\s*unsigned\s+char\s*\)", "(ap_uint<8>)", s)
    s = re.sub(r"\(\s*signed\s+char\s*\)",   "(ap_int<8>)",  s)
    return s

_NUM = r"(?:0|[1-9]\d*)"

def _replace_bracket_slices_constants(code: str) -> str:
    """
    Turn x[H+K, L] or x[H, L] into x.range(H+K, L), with H,K,L decimal constants.
    Critically: only match a *bare identifier* before the '[', never a ')'.
    """
    def repl_sum(m):
        var, h, k, l = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4))
        return f"{var}.range({h+k}, {l})"
    def repl_pair(m):
        var, h, l = m.group(1), int(m.group(2)), int(m.group(3))
        return f"{var}.range({h}, {l})"

    # x[H+K, L]
    code = re.sub(rf"\b([A-Za-z_]\w*)\s*\[\s*({_NUM})\s*\+\s*({_NUM})\s*,\s*({_NUM})\s*\]", repl_sum, code)
    # x[H, L]
    code = re.sub(rf"\b([A-Za-z_]\w*)\s*\[\s*({_NUM})\s*,\s*({_NUM})\s*\]", repl_pair, code)
    return code

def _wrap_simple_shift_before_slice(code: str) -> str:
    """
    Fix smt2c artifact: x << 2[3,0] -> (x << 2)[3,0].
    This enables _replace_bit_extractions to rewrite the slice.
    """
    return re.sub(rf"\b([A-Za-z_]\w*)\s*(<<|>>)\s*({_NUM})\s*\[", r"(\1 \2 \3)[", code)

def _safer_unsigned_negation(s: str) -> str:
    # Unary:  -(ap_uint<N>)(EXPR)  ->  ap_uint<N>(-(ap_int<N>)(EXPR))
    # Guard carefully so we do not rewrite binary subtraction like:
    #   lhs - (ap_uint<N>)(EXPR)
    pat = re.compile(
        r"(^|[=(:,?+\-*/%&|^!~<>]\s*|return\s+)"
        r"-\s*\(\s*ap_uint<(\d+)>\s*\)\s*\(\s*(.+?)\s*\)",
        re.MULTILINE,
    )

    def fix(m):
        prefix, N, expr = m.group(1), m.group(2), m.group(3)
        return f"{prefix}ap_uint<{N}>(-(ap_int<{N}>)( {expr} ))"

    return pat.sub(fix, s)

def _replace_bit_extractions(c_code: str) -> str:
    """
    Convert  (EXPR)[HI(+K), LO]  into  ap_uint<HI+1>((EXPR)).range(HI, LO)
    where EXPR may be a parenthesized expr or a function call like foo(...).

    Steps:
      (1) locate [...]
      (2) ensure char before '[' is ')'
      (3) walk backwards to match its '('
      (4) extend left to include the callee token if it's a function call.
    """
    s = c_code
    out = []
    i, n = 0, len(s)

    while i < n:
        rb = s.find(']', i)
        if rb == -1:
            out.append(s[i:]); break

        lb = s.rfind('[', i, rb)
        if lb == -1:
            out.append(s[i:rb+1]); i = rb + 1; continue

        inside = s[lb+1:rb]
        m = re.match(r"\s*(\d+)\s*(?:\+\s*(\d+))?\s*,\s*(\d+)\s*$", inside)
        if not m:
            out.append(s[i:lb+1]); i = lb + 1; continue

        hi = int(m.group(1)) + (int(m.group(2)) if m.group(2) else 0)
        lo = int(m.group(3))
        container_w = hi + 1   # container width, not slice width

        # The thing being sliced must end with ')'
        p = lb - 1
        while p >= 0 and s[p].isspace():
            p -= 1
        if p < 0 or s[p] != ')':
            out.append(s[i:lb+1]); i = lb + 1; continue

        # Find matching '(' for this ')'
        depth = 0
        q = p
        while q >= 0:
            if s[q] == ')':
                depth += 1
            elif s[q] == '(':
                depth -= 1
                if depth == 0:
                    break
            q -= 1
        if q < 0:
            out.append(s[i:rb+1]); i = rb + 1; continue

        # Try to include a callee token just before '(' (function call case)
        k = q - 1
        while k >= 0 and s[k].isspace():
            k -= 1
        name_end = k + 1
        while k >= 0 and (s[k].isalnum() or s[k] == '_'):
            k -= 1
        name_start = k + 1
        expr_start = name_start if (name_start < name_end and re.match(r"[A-Za-z_]\w*$", s[name_start:name_end])) else q

        expr = s[expr_start:p+1]  # inclusive of ')'
        rep  = f"(ap_uint<{container_w}>(({expr}))).range({hi}, {lo})"

        out.append(s[i:expr_start])
        out.append(rep)
        i = rb + 1

    return ''.join(out)

# Make leading casts apply to the WHOLE product
def _cast_entire_product(s: str) -> str:
    """
    Turn '(ap_*<N>) LHS * RHS' into 'ap_*<N>((LHS * RHS))' so the product
    has the intended width. Apply repeatedly.
    """
    token = r"(?:\([^()]*\)|[^\s();,])+"
    pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*(" + token + r")\s*\*\s*(" + token + r")")
    cast_only_pat = re.compile(r"^\(\s*ap_(?:u)?int<\d+>\s*\)$")
    # Chained cast: (ap_uint<5>)(ap_int<5>)x — TWO consecutive casts
    chained_cast_pat = re.compile(r"^\(\s*ap_(?:u)?int<\d+>\s*\)\s*\(\s*ap_(?:u)?int<\d+>\s*\)")
    def repl(m):
        ty, lhs, rhs = m.group(1), m.group(2), m.group(3)
        # Guard against partial matches like:
        #   (ap_uint<48>)Ma * (ap_uint<48>)Mb
        # where rhs could be mis-captured as '(ap_uint<48>)' only.
        if cast_only_pat.match(lhs.strip()) or cast_only_pat.match(rhs.strip()):
            return m.group(0)
        # Do not rewrite chained casts like:
        #   (ap_uint<5>)(ap_int<5>)x * ...
        # Those are already width-controlled and the generic rewrite can
        # collapse them into the wrong intermediate type.
        # But DO rewrite single casts like (ap_uint<25>)var * other_var.
        if chained_cast_pat.match(lhs.strip()) or chained_cast_pat.match(rhs.strip()):
            return m.group(0)
        return f"{ty}(({lhs} * {rhs}))"
    prev = None
    while prev != s:
        prev, s = s, pat.sub(repl, s)
    return s

def _scan_balanced_token(s: str, pos: int) -> int:
    """Starting at *pos*, consume one balanced token (handles nested parens).
    Returns the index one past the last character of the token, or *pos* if
    nothing could be consumed."""
    n = len(s)
    while pos < n:
        ch = s[pos]
        if ch == '(':
            # Consume balanced parens
            depth = 1
            pos += 1
            while pos < n and depth > 0:
                if s[pos] == '(':
                    depth += 1
                elif s[pos] == ')':
                    depth -= 1
                pos += 1
        elif ch in ' \t\n\r;,)':
            break
        else:
            pos += 1
    return pos


def _cast_entire_addsub(s: str) -> str:
    cast_pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)")
    chained_cast_pat = re.compile(r"^\(\s*ap_(?:u)?int<\d+>\s*\)\s*\(\s*ap_(?:u)?int<\d+>\s*\)")
    changed = True
    while changed:
        changed = False
        for m in cast_pat.finditer(s):
            ty = m.group(1)
            after_cast = m.end()
            # Skip whitespace after cast
            p = after_cast
            while p < len(s) and s[p] in ' \t':
                p += 1
            # Scan the LHS token (balanced)
            lhs_start = p
            lhs_end = _scan_balanced_token(s, p)
            if lhs_end == lhs_start:
                continue
            lhs = s[lhs_start:lhs_end]
            # Skip whitespace
            p = lhs_end
            while p < len(s) and s[p] in ' \t':
                p += 1
            # Expect +/-
            if p >= len(s) or s[p] not in '+-':
                continue
            op = s[p]
            p += 1
            # Skip whitespace
            while p < len(s) and s[p] in ' \t':
                p += 1
            # Scan the RHS token (balanced)
            rhs_start = p
            rhs_end = _scan_balanced_token(s, p)
            if rhs_end == rhs_start:
                continue
            rhs = s[rhs_start:rhs_end]
            # Guard: skip if LHS or RHS is just a cast (partial match)
            cast_only_pat = re.compile(r"^\(\s*ap_(?:u)?int<\d+>\s*\)$")
            if cast_only_pat.match(lhs.strip()) or cast_only_pat.match(rhs.strip()):
                continue
            # Guard: skip chained casts like (ap_uint<5>)(ap_int<5>)x
            if chained_cast_pat.match(lhs.strip()) or chained_cast_pat.match(rhs.strip()):
                continue
            # Rewrite: (ap_uint<N>) LHS op RHS -> ap_uint<N>((LHS op RHS))
            replacement = f"{ty}(({lhs} {op} {rhs}))"
            s = s[:m.start()] + replacement + s[rhs_end:]
            changed = True
            break  # restart after mutation
    return s


def _cast_var_addsub_paren_rhs(s: str) -> str:
    """
    Fix ternary-shaped cases that the regex-only add/sub hoist misses, e.g.
      (ap_uint<8>) target_exponent + (_let_26 ? ... : ...)
    by turning them into
      ap_uint<8>((target_exponent + (_let_26 ? ... : ...)))
    """
    pat = re.compile(
        r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*([A-Za-z_]\w*)\s*([+-])\s*\(",
        re.MULTILINE,
    )

    out = []
    i = 0
    while i < len(s):
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break

        out.append(s[i:m.start()])
        ty, lhs, op = m.group(1), m.group(2), m.group(3)
        rhs_open = m.end() - 1

        depth = 0
        j = rhs_open
        while j < len(s):
            if s[j] == '(':
                depth += 1
            elif s[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1

        if j >= len(s):
            out.append(s[m.start():])
            break

        rhs = s[rhs_open:j + 1]
        # Only rewrite the wide parenthesized ternary forms this helper was
        # introduced for. Casted RHS expressions like `(ap_uint<24>)foo(...)`
        # are handled correctly by the normal path and must be left alone.
        if "?" not in rhs:
            out.append(s[m.start():j + 1])
            i = j + 1
            continue
        out.append(f"{ty}(({lhs} {op} {rhs}))")
        i = j + 1

    return ''.join(out)


def _cast_paren_lhs_addsub_simple_rhs(s: str) -> str:
    """
    Fix cases like:
      (ap_uint<8>) (_let_3 ? e1 : e2) + exp_delta(...)
    by turning them into:
      ap_uint<8>(((_let_3 ? e1 : e2) + exp_delta(...)))
    The regex-only add/sub cast hoist cannot see through nested parentheses in
    the lhs, so it leaves mixed-width conditional arms behind for HLS.
    """
    pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*\(", re.MULTILINE)
    token = re.compile(r"(?:\([^()]*\)|[^\s();,])+")

    out = []
    i = 0
    while i < len(s):
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            break

        # Skip if this cast is part of a chain like (ap_uint<5>)(ap_int<5>)(ap_int<4>)(...)
        # — the preceding ')' means another cast already controls the width.
        pre = m.start() - 1
        while pre >= 0 and s[pre].isspace():
            pre -= 1
        if pre >= 0 and s[pre] == ')':
            out.append(s[i:m.start() + 1])
            i = m.start() + 1
            continue

        out.append(s[i:m.start()])
        ty = m.group(1)
        lhs_open = m.end() - 1

        depth = 0
        j = lhs_open
        while j < len(s):
            if s[j] == '(':
                depth += 1
            elif s[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1

        if j >= len(s):
            out.append(s[m.start():])
            break

        lhs = s[lhs_open:j + 1]
        if "?" not in lhs:
            out.append(s[m.start():m.start() + 1])
            i = m.start() + 1
            continue

        k = j + 1
        while k < len(s) and s[k].isspace():
            k += 1
        if k >= len(s) or s[k] not in "+-":
            out.append(s[m.start():m.start() + 1])
            i = m.start() + 1
            continue

        op = s[k]
        rhs_start = k + 1
        while rhs_start < len(s) and s[rhs_start].isspace():
            rhs_start += 1

        rhs_match = token.match(s, rhs_start)
        if not rhs_match:
            out.append(s[m.start():m.start() + 1])
            i = m.start() + 1
            continue

        rhs = rhs_match.group(0)
        out.append(f"{ty}(({lhs} {op} {rhs}))")
        i = rhs_match.end()

    return ''.join(out)

# Find the function header *before* a given offset and return its type
_FUNC_HDR_RE = re.compile(
    r'^\s*(ap_(?:u)?int<\d+>|bool)\s+[A-Za-z_]\w*\s*\([^;{]*\)\s*\{',
    re.M
)

def _ret_type_before_pos(code: str, pos: int) -> str | None:
    last = None
    for m in _FUNC_HDR_RE.finditer(code):
        if m.start() < pos:
            last = m
        else:
            break
    return last.group(1) if last else None

def _strip_outer_parens(s: str) -> str:
    s2 = s.strip()
    if not (s2.startswith("(") and s2.endswith(")")):
        return s
    depth = 0
    for i,ch in enumerate(s2):
        if ch == '(': depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0 and i != len(s2)-1:
                return s    # unmatched outer pair
    return s2[1:-1]         # whole expr wrapped once

def _split_top_comma(s: str):
    d = 0
    b = 0
    for i, ch in enumerate(s):
        if ch == '(': d += 1
        elif ch == ')': d = max(0, d-1)
        elif ch == '[': b += 1
        elif ch == ']': b = max(0, b-1)
        elif ch == ',' and d == 0 and b == 0:
            return s[:i].strip(), s[i+1:].strip()
    return None

def _ret_width(ret_ty: str) -> int | None:
    m = re.match(r"ap_(?:u)?int<(\d+)>", ret_ty or "")
    return int(m.group(1)) if m else None

def _pack_hi_lo(ret_ty: str, hi: str, lo: str) -> str:
    W = _ret_width(ret_ty)
    if W is None:
        return f"{ret_ty}((({hi})), ({lo}))"
    if W == 8:  # {4,4}
        return (
            f"{ret_ty}((({ret_ty})(({ret_ty})(({hi})) << 4)) | "
            f"(ap_uint<4>)(({lo})))"
        )
    if W == 9:  # {5,4}
        return (
            f"{ret_ty}((({ret_ty})((ap_uint<5>)(({hi})) << 4)) | "
            f"(ap_uint<4>)(({lo})))"
        )
    # generic: shift by W-4 assuming low is 4-bit exponent
    return (
        f"{ret_ty}((({ret_ty})(({ret_ty})(({hi})) << {W-4})) | "
        f"(ap_uint<4>)(({lo})))"
    )

def _wrap_return_top_concat(c_code: str) -> str:
    """
    Rewrites:  return (HI_expr, LO_expr);
    into a proper packed value using the *enclosing function's* return type width.
    Works across the whole file; keeps line endings.
    """
    out = []
    cursor = 0  # running index over the original string
    for line in c_code.splitlines(True):  # keep '\n'
        m = re.match(r"(\s*return\s+)(.+?)(;\s*)$", line)
        if not m:
            out.append(line)
            cursor += len(line)
            continue

        prefix, body, suffix = m.group(1), m.group(2).strip(), m.group(3)
        ret_ty = _ret_type_before_pos(c_code, cursor)  # <-- per-return type!

        core = _strip_outer_parens(body)
        xy = _split_top_comma(core)
        if not xy and core.startswith("(") and core.endswith(")"):
            xy = _split_top_comma(core[1:-1])

        if ret_ty and xy:
            hi, lo = xy
            packed = _pack_hi_lo(ret_ty, hi, lo)
            out.append(f"{prefix}{packed}{suffix}")
        else:
            out.append(line)

        cursor += len(line)

    return "".join(out)

def _find_top_level_ternary(rhs: str):
    """
    Find the positions of the top-level '?' and ':' (at paren depth 0) in rhs.
    Returns (q_pos, c_pos) or None if no top-level ternary exists.
    """
    depth = 0
    q_pos = None
    for i, ch in enumerate(rhs):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == '?' and depth == 0:
            q_pos = i
        elif ch == ':' and depth == 0 and q_pos is not None:
            return (q_pos, i)
    return None


def _already_exact_cast(branch: str, ty: str) -> bool:
    """True if the branch is already exactly `(ty)expr` with nothing else."""
    branch = branch.strip()
    prefix = f"({ty})"
    if not branch.startswith(prefix):
        return False
    rest = branch[len(prefix):].strip()
    return bool(re.match(r"^[A-Za-z_]\w*$", rest) or re.match(r"^\(.*\)$", rest))


def _cast_ternary_branches(code: str) -> str:
    """
    Fix Vitis HLS ambiguity when ternary branches have mismatched types.
    Only rewrites statements where the RHS has a TOP-LEVEL ternary (? at
    paren depth 0). Skips lines where ? is buried inside a cast chain or
    nested expression, which the old regex-based approach incorrectly split.
    """
    decl_pat = re.compile(
        r"^(\s*)(ap_(?:u)?int<\d+>)\s+(\w+)\s*=\s*(.+?)\s*;$",
        re.MULTILINE,
    )

    out = []
    prev = 0
    for m in decl_pat.finditer(code):
        out.append(code[prev:m.start()])
        indent, ty, var, rhs = m.group(1), m.group(2), m.group(3), m.group(4)

        result = _find_top_level_ternary(rhs)
        if result is None:
            out.append(m.group(0))
        else:
            q_pos, c_pos = result
            cond     = rhs[:q_pos].strip()
            true_br  = rhs[q_pos + 1:c_pos].strip()
            false_br = rhs[c_pos + 1:].strip()
            if not _already_exact_cast(true_br, ty):
                true_br = f"({ty})({true_br})"
            if not _already_exact_cast(false_br, ty):
                false_br = f"({ty})({false_br})"
            out.append(f"{indent}{ty} {var} = {cond} ? {true_br} : {false_br};")
        prev = m.end()
    out.append(code[prev:])
    return ''.join(out)


def _peephole_simplify(code: str) -> str:
    # shift/add/sub no-ops
    code = re.sub(r'\s*<<\s*0\b', '', code)
    code = re.sub(r'\b([A-Za-z_]\w*|\([^()]+\))\s*-\s*0\b', r'\1', code)
    code = re.sub(r'\b\(\s*ap_uint<(\d+)>\s*\)\s*\(\s*ap_uint<\1>\s*\(([^()]+)\)\s*\)', r'ap_uint<\1>(\2)', code)
    # strip double casts on the happy path
    code = re.sub(r'ap_uint<4>\(\(\s*ap_uint<4>\(([^()]+)\)\s*\)\)', r'ap_uint<4>(\1)', code)
    return code

def _clean(s: str) -> str:
    s = "\n".join(ln.rstrip() for ln in s.splitlines())
    s = re.sub(r"\n\s*\n\s*}", "\n}", s)
    return s.strip() + "\n"

def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    code = Path(c_input_path).read_text()

    # 0) Header + type normalisation
    code = _ensure_header(code)
    code = _normalize_char_types_and_casts(code)
    if "irep(" in code:
        raise ValueError(
            "translate_to_hls_cpp.py no longer rewrites irep(...) artifacts. "
            "Regenerate the C file with the patched smt2c pipeline."
        )

    code = _safer_unsigned_negation(code)
    # smt2c frequently emits ternary branches like `(ap_uint<5>) x + 2`,
    # where the cast only applies to the left operand. HLS then sees
    # mixed-width conditional arms.
    code = _cast_entire_addsub(code)
    code = _cast_var_addsub_paren_rhs(code)
    code = _cast_paren_lhs_addsub_simple_rhs(code)

    # 1) Fix bracket slices on bare identifiers (safe)
    code = _replace_bracket_slices_constants(code)

    # 2) Fix smt2c bug: x << 2[3,0] -> (x << 2)[3,0]
    code = _wrap_simple_shift_before_slice(code)

    # 3) Convert (EXPR)[HI, LO] -> ap_uint<...>((EXPR)).range(HI, LO)
    code = _replace_bit_extractions(code)

    # 4) Treat 'return (A,B,...)' as a packed value, not comma-operator
    code = _wrap_return_top_concat(code)

    # 5) Disambiguate ternary branches for Vitis HLS
    code = _cast_ternary_branches(code)

    # 6) Final tidy
    code = _peephole_simplify(code)
    code = _clean(code)

    if save_output:
        base = Path(c_input_path).stem
        results_root = Path(c_input_path).resolve().parents[1]
        cpp_dir = results_root / "cpp"
        cpp_dir.mkdir(parents=True, exist_ok=True)
        out = cpp_dir / f"{base}.cpp"
        out.write_text(code)
        print(f"HLS C++ file saved to: {out}")
        print("Generated HLS-ready C++ code:\n")
        print(code)
        return str(out)
    return code

def run_hls_conversion(c_output_path: str):
    if not c_output_path or not os.path.exists(c_output_path):
        print("[WARN] No C file found to convert for HLS.")
        return None
    print("\nConverting C output to HLS-compatible C++...\n")
    try:
        return convert_cp_to_hls(c_output_path)
    except Exception as e:
        print(f"[ERROR] Failed to convert C to HLS C++: {e}")
        return None

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python translate_to_hls_cpp.py <path_to_c_file>")
        sys.exit(1)
    convert_cp_to_hls(sys.argv[1])
