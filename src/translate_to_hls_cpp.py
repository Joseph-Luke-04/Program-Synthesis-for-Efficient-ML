import os, re
from pathlib import Path

_HEADER = "#include <ap_int.h>\n\n"

# Header & cast normalisation (preserve parens)
def _ensure_header(s: str) -> str:
    return s if "#include <ap_int.h>" in s else _HEADER + s.strip()

def _normalize_char_types_and_casts(s: str) -> str:
    # Decls
    s = re.sub(r"\bunsigned\s+char\b", "ap_uint<8>", s)
    s = re.sub(r"\bsigned\s+char\b",   "ap_int<8>",  s)
    # Casts (keep parentheses intact)
    s = re.sub(r"\(\s*unsigned\s+char\s*\)", "(ap_uint<8>)", s)
    s = re.sub(r"\(\s*signed\s+char\s*\)",   "(ap_int<8>)",  s)
    return s

def _safer_unsigned_negation(s: str) -> str:
    # -(ap_uint<N>)(EXPR)  ->  ap_uint<N>(-(ap_int<N>)(EXPR))
    def fix(m):
        N, expr = m.group(1), m.group(2)
        return f"ap_uint<{N}>(-(ap_int<{N}>)({expr}))"
    return re.sub(r"-\s*\(\s*ap_uint<(\d+)>\s*\)\s*\(\s*(.+?)\s*\)", fix, s)

def _replace_bit_extractions(c_code: str) -> str:
    # 1) fold constants like 4+3
    c_code = _fold_simple_int_additions(c_code)

    # 2) ( <EXPR> )[HI, LO]  ->  ap_uint<HI-LO+1>((<EXPR>)).range(HI, LO)
    def slice_repl(m):
        expr, hi, lo = m.group(1).strip(), int(m.group(2)), int(m.group(3))
        w = hi - lo + 1
        return f"(ap_uint<{w}>(({expr}))).range({hi}, {lo})"

    # IMPORTANT: use a greedy expr capture to grab the right '(' pairing
    return re.sub(r"\(\s*(.+)\s*\)\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]", slice_repl, c_code)

def _replace_any_bracket_slices(c_code: str) -> str:
    c_code = _fold_simple_int_additions(c_code)

    # EXPR[HI, LO] -> ap_uint<HI-LO+1>((EXPR)).range(HI, LO)
    # DO NOT cross newlines: add '\n' to the negated class.
    pat = re.compile(r"([^\[\];\n]+?)\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]")

    def repl(m):
        raw_expr = m.group(1)
        hi, lo = int(m.group(2)), int(m.group(3))
        w = hi - lo + 1

        # Preserve leading whitespace so indentation stays intact.
        leading_ws_len = len(raw_expr) - len(raw_expr.lstrip(" \t"))
        leading_ws = raw_expr[:leading_ws_len]

        expr = raw_expr.lstrip()

        # Special-case 'return <expr>[hi, lo]' so we don't drop the return keyword.
        prefix = leading_ws
        m_return = re.match(r"(return\b\s*)(.*)", expr)
        if m_return:
            prefix += m_return.group(1)
            expr = m_return.group(2)

        expr = expr.rstrip()
        replacement = f"(ap_uint<{w}>(({expr}))).range({hi}, {lo})"
        return prefix + replacement

    prev = None
    while prev != c_code:
        prev, c_code = c_code, pat.sub(repl, c_code)
    return c_code

# Make leading casts apply to the WHOLE product
def _cast_entire_product(s: str) -> str:
    """
    Turn '(ap_*<N>) LHS * RHS' into 'ap_*<N>((LHS * RHS))' so the product
    has the intended width. Apply repeatedly.
    """
    token = r"(?:\([^()]*\)|[^\s()])+"
    pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*(" + token + r")\s*\*\s*(" + token + r")")
    def repl(m):
        ty, lhs, rhs = m.group(1), m.group(2), m.group(3)
        return f"{ty}(({lhs} * {rhs}))"
    prev = None
    while prev != s:
        prev, s = s, pat.sub(repl, s)
    return s

# Ternary unifier (works for nested ?:)
_APTY_RE = r"\b(ap_(?:u)?int<\d+>)"

def _extract_common_ap_type(a: str, b: str) -> str | None:
    ta = re.findall(_APTY_RE, a)
    tb = re.findall(_APTY_RE, b)
    for t in ta:
        if t in tb:
            return t
    return None

def _has_top_level_comma(expr: str) -> bool:
    d = 0
    for ch in expr:
        if ch == "(": d += 1
        elif ch == ")": d = max(0, d-1)
        elif ch == "," and d == 0: return True
    return False

def _split_top_ternary(s: str):
    d = 0; q = None
    for i, ch in enumerate(s):
        if ch == "(": d += 1
        elif ch == ")": d -= 1
        elif ch == "?" and d == 0: q = i; break
    if q is None: return None
    d = 0; c = None
    for j in range(q+1, len(s)):
        ch = s[j]
        if ch == "(": d += 1
        elif ch == ")": d -= 1
        elif ch == ":" and d == 0: c = j; break
    if c is None: return None
    return s[:q].strip(), s[q+1:c].strip(), s[c+1:].strip()

def _unify_ternaries_rec(s: str) -> str:
    split = _split_top_ternary(s)
    if not split:
        return s
    cond, a, b = split
    # Also recurse into condition
    cond2 = _unify_ternaries_rec(cond)
    a2 = _unify_ternaries_rec(a)
    b2 = _unify_ternaries_rec(b)
    if _has_top_level_comma(a2) or _has_top_level_comma(b2):
        return f"{cond2} ? {a2} : {b2}"
    ty = _extract_common_ap_type(a2, b2)
    if ty:
        a2 = f"{ty}(({a2}))"
        b2 = f"{ty}(({b2}))"
    return f"{cond2} ? {a2} : {b2}"

def _unify_all_ternaries(s: str) -> str:
    out = []
    for line in s.splitlines():
        if "?" in line and ":" in line:
            # Case 1: 'return <expr>;' — unify inside the expression and keep the semicolon outside
            m = re.match(r"(\s*return\s+)(.+?)(;\s*)$", line)
            if m:
                prefix, expr, suffix = m.group(1), m.group(2).strip(), m.group(3)
                out.append(f"{prefix}{_unify_ternaries_rec(expr)}{suffix}")
                continue
            # Case 2: generic line ending with ';' — do the same (avoid dragging ';' into a branch)
            m2 = re.match(r"(\s*)(.+?)(;\s*)$", line)
            if m2:
                lead, expr, suffix = m2.group(1), m2.group(2), m2.group(3)
                out.append(f"{lead}{_unify_ternaries_rec(expr)}{suffix}")
                continue
            # Case 3: no trailing ';' — safe to process whole line
            out.append(_unify_ternaries_rec(line))
        else:
            out.append(line)
    return "\n".join(out)

def _fold_simple_int_additions(s: str) -> str:
    return re.sub(r"\b(\d+)\s*\+\s*(\d+)\b", lambda m: str(int(m.group(1))+int(m.group(2))), s)

def _get_function_return_type(c_code: str) -> str | None:
    # Matches: ap_uint<N> | ap_int<N> | bool   before the function name
    m = re.search(r"\b(ap_(?:u)?int<\d+>|bool)\s+[A-Za-z_]\w*\s*\(", c_code)
    return m.group(1) if m else None

def _wrap_return_top_concat(c_code: str) -> str:
    ret_ty = _get_function_return_type(c_code)
    if not ret_ty:
        return c_code

    out = []
    for line in c_code.splitlines():
        m = re.match(r"(\s*return\s+)(.+?)(;\s*)$", line)
        if not m:
            out.append(line)
            continue

        body = m.group(2).strip()
        need_wrap = False

        # Case 1: comma at top level
        if _has_top_level_comma(body):
            need_wrap = True
        # Case 2: body is a single parenthesized expr "( ... )" whose inside has a top-level comma
        elif body.startswith("(") and body.endswith(")"):
            inner = body[1:-1].strip()
            if _has_top_level_comma(inner):
                body = inner  # drop the outer parens, we'll add ret_ty((...)) anyway
                need_wrap = True

        if need_wrap:
            out.append(f"{m.group(1)}{ret_ty}(({body})){m.group(3)}")
        else:
            out.append(line)

    return "\n".join(out)

def _clean(s: str) -> str:
    s = "\n".join(ln.rstrip() for ln in s.splitlines())
    s = re.sub(r"\n\s*\n\s*}", "\n}", s)
    return s.strip() + "\n"

def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    code = Path(c_input_path).read_text()

    code = _ensure_header(code)
    code = _normalize_char_types_and_casts(code)
    code = _safer_unsigned_negation(code)

    # Slices & constants (fixes '[4+3,4]' and concat slicing)
    code = _fold_simple_int_additions(code)
    code = _replace_bit_extractions(code)

    # Width correctness + ?: unification
    code = _cast_entire_product(code)
    code = _unify_all_ternaries(code)

    # Convert any remaining bracket slices introduced by later passes
    code = _replace_any_bracket_slices(code)

    # Treat 'return (A,B);' as value, not comma operator
    code = _wrap_return_top_concat(code)

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
