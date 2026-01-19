import os, re
from pathlib import Path
from .canonicalisers import (
    _canonicalise_add_full_sum, 
    _canonicalise_mxint8_normaliser_rounded, 
    _canonicalise_mxint8_raw_adder, 
    _canonicalise_mxint8_alignment, 
    _canonicalise_mxint8_mult_mant,
    _canonicalise_mxint8_mult_renorm_flag,
    _canonicalise_fp32_aligner,
    _canonicalise_fp32_raw_summer,
    _canonicalise_fp32_normaliser, 
    _canonicalise_fp32_sum
)

_HEADER = "#include <ap_int.h>\n\n"

# Header & cast normalisation (preserve parens)
def _ensure_header(s: str) -> str:
    return s if "#include <ap_int.h>" in s else _HEADER + s.strip()

def _normalize_char_types_and_casts(s: str) -> str:
    # Decls
    s = re.sub(r"\bunsigned\s+char\b", "ap_uint<8>", s)
    s = re.sub(r"\bsigned\s+char\b",   "ap_int<8>",  s)
    s = re.sub(r'\bunsigned\s+int\b', 'ap_uint<32>', s)
    s = re.sub(r'(?<!unsigned\s)\bint\b', 'ap_int<32>', s)

    # Casts (keep parentheses intact)
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

def _safer_unsigned_negation(s: str) -> str:
    # -(ap_uint<N>)(EXPR)  ->  ap_uint<N>(-(ap_int<N>)(EXPR))
    def fix(m):
        N, expr = m.group(1), m.group(2)
        return f"ap_uint<{N}>(-(ap_int<{N}>)({expr}))"
    return re.sub(r"-\s*\(\s*ap_uint<(\d+)>\s*\)\s*\(\s*(.+?)\s*\)", fix, s)

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
    def repl(m):
        ty, lhs, rhs = m.group(1), m.group(2), m.group(3)
        return f"{ty}(({lhs} * {rhs}))"
    prev = None
    while prev != s:
        prev, s = s, pat.sub(repl, s)
    return s

def _cast_entire_addsub(s: str) -> str:
    token = r"(?:\([^()]*\)|[^\s();,])+"
    pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*(" + token + r")\s*([+-])\s*(" + token + r")")
    def repl(m):
        ty, lhs, op, rhs = m.group(1), m.group(2), m.group(3), m.group(4)
        return f"{ty}(({lhs} {op} {rhs}))"
    prev = None
    while prev != s:
        prev, s = s, pat.sub(repl, s)
    return s

# Ternary unifier (works for nested ?:)
_APTY_RE = r"\b(ap_(?:u)?int<\d+>|bool)\b"

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
        elif ch == ")": d = max(0, d-1)
        elif ch == "?" and d == 0: q = i; break
    if q is None: return None
    d = 0; c = None
    for j in range(q+1, len(s)):
        ch = s[j]
        if ch == "(": d += 1
        elif ch == ")": d = max(0, d-1)
        elif ch == ":" and d == 0: c = j; break
    if c is None: return None
    return s[:q].strip(), s[q+1:c].strip(), s[c+1:].strip()

def _unify_ternaries_rec(s: str, target_ty: str | None = None) -> str:
    split = _split_top_ternary(s)
    if not split:
        return s
    cond, a, b = split
    cond2 = _unify_ternaries_rec(cond, target_ty)
    a2 = _unify_ternaries_rec(a, target_ty)
    b2 = _unify_ternaries_rec(b, target_ty)

    # If either side already has commas at top level (concats), don't try to hoist casts inside them.
    if _has_top_level_comma(a2) or _has_top_level_comma(b2):
        return f"{cond2} ? {a2} : {b2}"

    ty = _extract_common_ap_type(a2, b2)
    if not ty and target_ty:
        ty = target_ty   # Fallback to the known destination type

    if ty:
        a2 = f"{ty}(({a2}))"
        b2 = f"{ty}(({b2}))"
    return f"{cond2} ? {a2} : {b2}"

def _get_declared_lhs_type(line: str) -> tuple[str | None, str | None, str | None]:
    """
    Try to parse 'ap_uint<N> name = RHS;' or 'ap_int<N> name = RHS;' or 'bool name = RHS;'
    Returns (lhs_type, lhs_name, rhs) or (None, None, None).
    """
    m = re.match(r"\s*(ap_(?:u)?int<\d+>|bool)\s+([A-Za-z_]\w*)\s*=\s*(.+?);\s*$", line)
    if not m:
        return None, None, None
    return m.group(1), m.group(2), m.group(3)

def _unify_all_ternaries(code: str) -> str:
    out = []
    cursor = 0  # running index in the original string
    for line in code.splitlines(True):  # keep line endings
        if "?" in line and ":" in line:
            # Case A: return ...;
            m_ret = re.match(r"(\s*return\s+)(.+?)(;\s*)$", line)
            if m_ret:
                ret_ty = _ret_type_before_pos(code, cursor)
                expr = _unify_ternaries_rec(m_ret.group(2).strip(), ret_ty)
                out.append(f"{m_ret.group(1)}{expr}{m_ret.group(3)}")
            else:
                # Case B: typed assignment
                lhs_ty, lhs_name, rhs = _get_declared_lhs_type(line)
                if lhs_ty:
                    lead = line[:line.find(lhs_ty)]
                    out.append(f"{lead}{lhs_ty} {lhs_name} = {_unify_ternaries_rec(rhs, lhs_ty)};")
                else:
                    # Generic
                    m_any = re.match(r"(\s*)(.+?)(;\s*)$", line)
                    if m_any:
                        out.append(f"{m_any.group(1)}{_unify_ternaries_rec(m_any.group(2), None)}{m_any.group(3)}")
                    else:
                        out.append(_unify_ternaries_rec(line, None))
        else:
            out.append(line)
        cursor += len(line)
    return "".join(out)

def _fold_simple_int_additions(s: str) -> str:
    return re.sub(r"\b(\d+)\s*\+\s*(\d+)\b", lambda m: str(int(m.group(1))+int(m.group(2))), s)

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
    for i, ch in enumerate(s):
        if ch == '(': d += 1
        elif ch == ')': d = max(0, d-1)
        elif ch == ',' and d == 0:
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

def _strip_irep_noise(code: str) -> str:
    """Replace any irep(...) (which may contain nested parens inside quoted strings)
       with 0. This handles forms like: irep("(\"zero_extend\" ... (\"0\") ... )")."""
    out = []
    i, n = 0, len(code)
    needle = 'irep('

    while True:
        j = code.find(needle, i)
        if j == -1:
            out.append(code[i:]); break
        out.append(code[i:j])        # keep text before irep(
        k = j + len(needle)          # start after 'irep('
        depth = 1
        in_str = False
        esc = False
        while k < n and depth > 0:
            ch = code[k]
            if in_str:
                if esc:
                    esc = False
                elif ch == '\\':
                    esc = True
                elif ch == '"':
                    in_str = False
            else:
                if ch == '"':
                    in_str = True
                elif ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
            k += 1
        # swallow entire irep(...) and emit 0
        out.append('0')
        i = k

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
    code = _strip_irep_noise(code)
    code = _safer_unsigned_negation(code)

    # 1) Fix bracket slices on bare identifiers (safe)
    code = _replace_bracket_slices_constants(code)

    # 2) Simple folds
    code = _fold_simple_int_additions(code)

    # 3) Convert (EXPR)[HI, LO] -> ap_uint<...>((EXPR)).range(HI, LO)
    code = _replace_bit_extractions(code)

    # 4) Width correctness
    code = _cast_entire_product(code)
    code = _cast_entire_addsub(code)

    # 5) Ternary unification (make both arms same ap_*int<N>)
    code = _unify_all_ternaries(code)
    code = _replace_bracket_slices_constants(code)  # in case new slices appeared
    code = _replace_bit_extractions(code)  # in case new bit extractions appeared

    # 6) Treat 'return (A,B,...)' as a packed value, not comma-operator
    code = _wrap_return_top_concat(code)

    # 7) Canonicalisers (not all scripts actually output correct C++)
    code = _canonicalise_fp32_aligner(code)
    code = _canonicalise_fp32_raw_summer(code)
    code = _canonicalise_fp32_normaliser(code)
    code = _canonicalise_fp32_sum(code)

    code = _canonicalise_mxint8_alignment(code)
    code = _canonicalise_mxint8_raw_adder(code)
    code = _canonicalise_mxint8_normaliser_rounded(code)
    code = _canonicalise_mxint8_mult_renorm_flag(code)
    code = _canonicalise_mxint8_mult_mant(code)

    code = _canonicalise_add_full_sum(code)

    # 8) Final tidy
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
