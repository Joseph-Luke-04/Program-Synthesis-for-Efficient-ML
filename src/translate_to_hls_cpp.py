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
    Convert  EXPR[HI(+K), LO]  into  ap_uint<HI-LO+1>((EXPR)).range(HI, LO)
    where EXPR may be a parenthesized expr or a function call like foo(...).
    We (1) locate [...] ; (2) ensure char before '[' is ')';
    (3) walk backwards to match its '('; (4) extend left to include the
    callee token if the '(' belongs to a function call.
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

        # Parse "HI (+ K) , LO"
        inside = s[lb+1:rb]
        m = re.match(r"\s*(\d+)\s*(?:\+\s*(\d+))?\s*,\s*(\d+)\s*$", inside)
        if not m:
            out.append(s[i:lb+1]); i = lb + 1; continue
        hi = int(m.group(1)) + (int(m.group(2)) if m.group(2) else 0)
        lo = int(m.group(3))
        w  = hi - lo + 1

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
        # If there is an identifier right before '(', include it
        if name_start < name_end and re.match(r"[A-Za-z_]\w*$", s[name_start:name_end]):
            expr_start = name_start              # include callee + "(" + args + ")"
        else:
            expr_start = q                       # include just "( ... )"

        expr = s[expr_start:p+1]                # inclusive of ')'
        rep  = f"(ap_uint<{w}>(({expr}))).range({hi}, {lo})"

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
    token = r"(?:\([^()]*\)|[^\s()])+"
    pat = re.compile(r"\(\s*(ap_(?:u)?int<\d+>)\s*\)\s*(" + token + r")\s*\*\s*(" + token + r")")
    def repl(m):
        ty, lhs, rhs = m.group(1), m.group(2), m.group(3)
        return f"{ty}(({lhs} * {rhs}))"
    prev = None
    while prev != s:
        prev, s = s, pat.sub(repl, s)
    return s

def _cast_entire_addsub(s: str) -> str:
    token = r"(?:\([^()]*\)|[^\s()])+"
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
    ret_ty = _get_function_return_type(code)
    out = []
    for line in code.splitlines():
        if "?" not in line or ":" not in line:
            out.append(line); continue

        # Case A: return ...;
        m_ret = re.match(r"(\s*return\s+)(.+?)(;\s*)$", line)
        if m_ret:
            prefix, expr, suffix = m_ret.group(1), m_ret.group(2).strip(), m_ret.group(3)
            out.append(f"{prefix}{_unify_ternaries_rec(expr, ret_ty)}{suffix}")
            continue

        # Case B: typed assignment 'ap_uint<N> x = ...;'
        lhs_ty, lhs_name, rhs = _get_declared_lhs_type(line)
        if lhs_ty:
            lead = line[:line.find(lhs_ty)]
            out.append(f"{lead}{lhs_ty} {lhs_name} = {_unify_ternaries_rec(rhs, lhs_ty)};")
            continue

        # Generic line: best-effort unify with no target type
        m_any = re.match(r"(\s*)(.+?)(;\s*)$", line)
        if m_any:
            lead, expr, suffix = m_any.group(1), m_any.group(2), m_any.group(3)
            out.append(f"{lead}{_unify_ternaries_rec(expr, None)}{suffix}")
        else:
            out.append(_unify_ternaries_rec(line, None))
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
        if not m: out.append(line); continue
        prefix, body, suffix = m.group(1), m.group(2).strip(), m.group(3)
        if _has_top_level_comma(body):
            out.append(f"{prefix}{ret_ty}(({body})){suffix}")
        else:
            out.append(line)
    return "\n".join(out)

def _canonicalise_fp32_normaliser(code: str) -> str:
    """
    Replace the entire fp32_normaliser(...) function with a clean, canonical version.
    Uses brace matching to avoid truncation.
    """
    if "fp32_normaliser(" not in code:
        return code

    # Find the function header (return type may be ap_uint<...> or unsigned int from smt2c)
    m = re.search(r'\b(?:ap_uint<\d+>|unsigned\s+int)\s+fp32_normaliser\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1  # position of the '{'

    # Match braces to find the end of this function
    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        # unmatched braces; leave code unchanged
        return code

    canonical = r"""
ap_uint<32> fp32_normaliser(ap_uint<25> raw_sum_mantissa, ap_uint<1> raw_sign, ap_uint<8> target_exponent) {
  if (raw_sum_mantissa == 0) {
    return (ap_uint<32>)((ap_uint<1>)0, (ap_uint<8>)0, (ap_uint<23>)0);
  }
  ap_uint<8> exp = target_exponent;
  ap_uint<24> norm24;
  if (raw_sum_mantissa[24]) { norm24 = raw_sum_mantissa.range(24,1); exp += 1; }
  else if (raw_sum_mantissa[23]) { norm24 = raw_sum_mantissa.range(23,0); }
  else if (raw_sum_mantissa[22]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(22,0) << 1; exp -= 1; }
  else if (raw_sum_mantissa[21]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(21,0) << 2; exp -= 2; }
  else if (raw_sum_mantissa[20]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(20,0) << 3; exp -= 3; }
  else if (raw_sum_mantissa[19]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(19,0) << 4; exp -= 4; }
  else if (raw_sum_mantissa[18]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(18,0) << 5; exp -= 5; }
  else if (raw_sum_mantissa[17]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(17,0) << 6; exp -= 6; }
  else if (raw_sum_mantissa[16]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(16,0) << 7; exp -= 7; }
  else if (raw_sum_mantissa[15]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(15,0) << 8; exp -= 8; }
  else if (raw_sum_mantissa[14]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(14,0) << 9; exp -= 9; }
  else if (raw_sum_mantissa[13]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(13,0) << 10; exp -= 10; }
  else if (raw_sum_mantissa[12]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(12,0) << 11; exp -= 11; }
  else if (raw_sum_mantissa[11]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(11,0) << 12; exp -= 12; }
  else if (raw_sum_mantissa[10]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(10,0) << 13; exp -= 13; }
  else if (raw_sum_mantissa[9])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(9,0)  << 14; exp -= 14; }
  else if (raw_sum_mantissa[8])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(8,0)  << 15; exp -= 15; }
  else if (raw_sum_mantissa[7])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(7,0)  << 16; exp -= 16; }
  else if (raw_sum_mantissa[6])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(6,0)  << 17; exp -= 17; }
  else if (raw_sum_mantissa[5])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(5,0)  << 18; exp -= 18; }
  else if (raw_sum_mantissa[4])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(4,0)  << 19; exp -= 19; }
  else if (raw_sum_mantissa[3])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(3,0)  << 20; exp -= 20; }
  else if (raw_sum_mantissa[2])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(2,0)  << 21; exp -= 21; }
  else if (raw_sum_mantissa[1])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(1,0)  << 22; exp -= 22; }
  else /* raw_sum_mantissa[0] */  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(0,0)  << 23; exp -= 23; }
  ap_uint<1> sign = raw_sign; // zero already handled
  return (ap_uint<32>)((ap_uint<1>)sign, (ap_uint<8>)exp, (ap_uint<23>)norm24.range(22,0));
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]

def _canonicalise_fp32_sum(code: str) -> str:
    """
    Replace the whole fp32_sum(...) body with a simple, HLS-safe version that
    uses temporaries for the aligned pack and slices. Works whether the return
    type was 'unsigned int' (from smt2c) or 'ap_uint<32>'.
    """
    if "fp32_sum(" not in code:
        return code

    # find the start of the function body
    m = re.search(r'\b(?:ap_uint<\d+>|unsigned\s+int)\s+fp32_sum\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1  # at '{'

    # match balanced braces to find the end of this function
    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        return code  # unmatched braces; bail

    canonical = r"""
ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1,
                     ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  // 56-bit pack: [55:32]=aligned m1, [31:8]=aligned m2, [7:0]=target exponent
  ap_uint<56> pack = fp32_aligner(e1, m1, e2, m2);
  ap_uint<24> am1  = (ap_uint<24>) pack.range(55, 32);
  ap_uint<24> am2  = (ap_uint<24>) pack.range(31,  8);
  ap_uint<8>  exp  = (ap_uint<8>)  pack.range( 7,  0);

  ap_uint<26> raw  = fp32_raw_summer(s1, am1, s2, am2);
  ap_uint<25> raw_m = (ap_uint<25>) raw.range(24, 0);
  ap_uint<1>  raw_s = (ap_uint<1>)  raw.range(25, 25);

  return fp32_normaliser(raw_m, raw_s, exp);
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]

def _clean(s: str) -> str:
    s = "\n".join(ln.rstrip() for ln in s.splitlines())
    s = re.sub(r"\n\s*\n\s*}", "\n}", s)
    return s.strip() + "\n"

def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    code = Path(c_input_path).read_text()

    # 0) Header + type normalisation
    code = _ensure_header(code)
    code = _normalize_char_types_and_casts(code)
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

    # 6) Treat 'return (A,B,...)' as a packed value, not comma-operator
    code = _wrap_return_top_concat(code)

    # 7) (Optional) emit a clean, canonical normaliser body
    code = _canonicalise_fp32_normaliser(code)
    code = _canonicalise_fp32_sum(code)

    # 8) Final tidy
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
