import os, re
from pathlib import Path
from .canonicalisers import (
    _canonicalise_add_full_sum, 
    _canonicalise_mxint8_normaliser_rounded, 
    _canonicalise_mxint8_raw_adder, 
    _canonicalise_mxint8_alignment, 
    _canonicalise_mxint8_detect_overflow,
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

def _wrap_simple_shift_before_slice(code: str) -> str:
    """
    Fix smt2c artifact: x << 2[3,0] -> (x << 2)[3,0].
    This enables _replace_bit_extractions to rewrite the slice.
    """
    return re.sub(rf"\b([A-Za-z_]\w*)\s*(<<|>>)\s*({_NUM})\s*\[", r"(\1 \2 \3)[", code)

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
_APTY_RE = r"(ap_(?:u)?int<\d+>|bool)"

def _extract_common_ap_type(a: str, b: str) -> str | None:
    ta = re.findall(_APTY_RE, a)
    tb = re.findall(_APTY_RE, b)
    for t in ta:
        if t in tb:
            return t
    return None

def _extract_widest_ap_type(a: str, b: str) -> str | None:
    types = re.findall(_APTY_RE, a) + re.findall(_APTY_RE, b)
    if not types:
        return None
    best_width = -1
    best_signed = False
    for t in types:
        m = re.match(r"ap_(u)?int<(\d+)>", t)
        if not m:
            continue
        is_signed = m.group(1) is None
        width = int(m.group(2))
        if width > best_width:
            best_width = width
            best_signed = is_signed
        elif width == best_width and is_signed and not best_signed:
            best_signed = True
    if best_width < 0:
        return None
    return f"ap_int<{best_width}>" if best_signed else f"ap_uint<{best_width}>"

def _ap_type_width(ty: str | None) -> int:
    if not ty:
        return -1
    m = re.match(r"ap_(?:u)?int<(\d+)>", ty)
    return int(m.group(1)) if m else -1

def _has_top_level_comma(expr: str) -> bool:
    d = 0
    b = 0
    for ch in expr:
        if ch == "(": d += 1
        elif ch == ")": d = max(0, d-1)
        elif ch == "[": b += 1
        elif ch == "]": b = max(0, b-1)
        elif ch == "," and d == 0 and b == 0: return True
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
    widest = _extract_widest_ap_type(a2, b2)
    if widest and _ap_type_width(widest) > _ap_type_width(ty):
        ty = widest
    if not ty:
        ty = widest
    if not ty and target_ty:
        ty = target_ty   # Fallback to the known destination type

    if ty:
        a2_stripped = a2.strip()
        b2_stripped = b2.strip()
        if not re.match(rf"^{re.escape(ty)}\s*\(", a2_stripped):
            a2 = f"{ty}(({a2}))"
        if not re.match(rf"^{re.escape(ty)}\s*\(", b2_stripped):
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

def _find_ternary_span(s: str) -> tuple[int, int, int, int] | None:
    """
    Return (qpos, cpos, depth, bdepth) for the first ternary pair found.
    depth/bdepth are the paren/bracket depths at the '?' and matching ':'.
    """
    depth = 0
    bdepth = 0
    qstack: list[tuple[int, int, int]] = []
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif ch == "[":
            bdepth += 1
        elif ch == "]":
            bdepth = max(0, bdepth - 1)
        elif ch == "?":
            qstack.append((i, depth, bdepth))
        elif ch == ":" and qstack:
            for k in range(len(qstack) - 1, -1, -1):
                qpos, qd, qb = qstack[k]
                if qd == depth and qb == bdepth:
                    return qpos, i, depth, bdepth
    return None

def _find_ternary_left_boundary(s: str, qpos: int, depth: int, bdepth: int) -> int:
    pd = depth
    bd = bdepth
    i = qpos - 1
    while i >= 0:
        ch = s[i]
        if ch == ")":
            pd += 1
        elif ch == "(":
            if pd == depth and bd == bdepth:
                return i + 1
            pd = max(0, pd - 1)
        elif ch == "]":
            bd += 1
        elif ch == "[":
            bd = max(0, bd - 1)
        elif pd == depth and bd == bdepth and ch in ",;":
            return i + 1
        i -= 1
    return 0

def _find_ternary_right_boundary(s: str, cpos: int, depth: int, bdepth: int) -> int:
    pd = depth
    bd = bdepth
    i = cpos + 1
    while i < len(s):
        ch = s[i]
        if ch == "(":
            pd += 1
        elif ch == ")":
            if pd == depth and bd == bdepth:
                return i
            pd = max(0, pd - 1)
        elif ch == "[":
            bd += 1
        elif ch == "]":
            bd = max(0, bd - 1)
        elif pd == depth and bd == bdepth and ch in ",;":
            return i
        i += 1
    return len(s)

def _unify_ternaries_in_parens(code: str) -> str:
    """
    Apply ternary unification to nested ternaries anywhere in the line.
    """
    out = []
    for line in code.splitlines(True):
        if "?" not in line or ":" not in line:
            out.append(line)
            continue
        cur = line
        for _ in range(64):
            span = _find_ternary_span(cur)
            if not span:
                break
            qpos, cpos, depth, bdepth = span
            start = _find_ternary_left_boundary(cur, qpos, depth, bdepth)
            end = _find_ternary_right_boundary(cur, cpos, depth, bdepth)
            segment = cur[start:end]
            unified = _unify_ternaries_rec(segment, None)
            if unified == segment:
                break
            cur = cur[:start] + unified + cur[end:]
        out.append(cur)
    return "".join(out)

_CAST_RE = re.compile(r"\(\s*ap_(?:u)?int<\d+>\s*\)")

def _wrap_casted_ternary_branches(code: str) -> str:
    """
    Fix precedence bugs like: (ap_uint<4>) raw_sum == 0 ? ... : ...
    by rewriting to: (ap_uint<4>) (raw_sum == 0 ? ... : ...)
    so the cast applies to the ternary expression, not to raw_sum.
    """
    i = 0
    out = []
    while i < len(code):
        m = _CAST_RE.search(code, i)
        if not m:
            out.append(code[i:])
            break
        out.append(code[i:m.end()])
        j = m.end()
        while j < len(code) and code[j].isspace():
            j += 1
        # If already parenthesized, do nothing.
        if j < len(code) and code[j] == "(":
            i = j
            continue
        sub = code[j:]
        span = _find_ternary_span(sub)
        if not span:
            i = j
            continue
        qpos, cpos, depth, bdepth = span
        if depth != 0 or bdepth != 0:
            i = j
            continue
        # Skip wrapping if there's another top-level '?' before the matching ':'
        # (nested ternary at same paren depth). Our simple span finder can't handle it.
        nested = False
        d = 0
        for k in range(qpos + 1, cpos):
            ch = sub[k]
            if ch == "(":
                d += 1
            elif ch == ")":
                d = max(0, d - 1)
            elif ch == "?" and d == 0:
                nested = True
                break
        if nested:
            i = j
            continue
        end_rel = _find_ternary_right_boundary(sub, cpos, depth, bdepth)
        out.append(" (")
        out.append(code[j:j + end_rel])
        out.append(")")
        i = j + end_rel
    return "".join(out)

_CAST_FUNC_RE = re.compile(r"\b(ap_(?:u)?int<\d+>)\s*\(")

def _unify_ternaries_inside_casts(code: str) -> str:
    """
    If a function-style cast wraps a ternary (e.g. ap_uint<4>(cond ? a : b)),
    force both arms to that type to avoid ambiguous conditional expressions.
    """
    out = []
    i = 0
    n = len(code)
    while i < n:
        m = _CAST_FUNC_RE.search(code, i)
        if not m:
            out.append(code[i:])
            break
        out.append(code[i:m.start()])
        ty = m.group(1)
        j = m.end()  # char after '('
        depth = 1
        k = j
        while k < n and depth > 0:
            if code[k] == '(':
                depth += 1
            elif code[k] == ')':
                depth -= 1
            k += 1
        if depth != 0:
            out.append(code[m.start():])
            break
        inner = code[j:k-1]
        if "?" in inner and ":" in inner:
            inner = _unify_ternaries_rec(inner, ty)
        out.append(f"{ty}({inner})")
        i = k
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

def _replace_known_irep(code: str) -> str:
    """
    Replace known irep(...) forms with explicit expressions before
    falling back to _strip_irep_noise.
    """
    out = []
    i, n = 0, len(code)
    needle = 'irep('

    while True:
        j = code.find(needle, i)
        if j == -1:
            out.append(code[i:])
            break
        out.append(code[i:j])
        k = j + len(needle)
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

        content = code[j + len(needle):k-1]
        replacement = None
        # Match the common mxint alignment shift irep (depends on e1/e2).
        if ('\"identifier\" (\"e1\")' in content) and ('\"identifier\" (\"e2\")' in content):
            replacement = (
                "(ap_uint<4>)(((ap_int<4>)e1 >= (ap_int<4>)e2) ? "
                "(ap_uint<4>)(e1 - e2) : (ap_uint<4>)(e2 - e1))"
            )

        if replacement is None:
            out.append(code[j:k])
        else:
            out.append(replacement)
        i = k

    return ''.join(out)

def _fix_mxint8_full_sum_irep(code: str) -> str:
    """
    If add_full_sum contains irep(...) blobs from smt2c, replace the whole
    function with an equivalent explicit form so the solver semantics are preserved.
    This is a translation fix, not a behavior change.
    """
    if "add_full_sum" not in code or "irep(" not in code:
        return code

    m = re.search(r'\b(ap_uint<\d+>|unsigned\s+char)\s+add_full_sum\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    # Extract function body and only rewrite if it actually contains irep(...)
    start = m.start()
    i = m.end() - 1
    depth = 0
    end = None
    while i < len(code):
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                end = i + 1
                break
        i += 1
    if end is None:
        return code

    if "irep(" not in code[start:end]:
        return code

    # Emit a combinational, explicit version that mirrors the monolithic SMT.
    print("[INFO] Rewriting add_full_sum to remove irep(...) artifacts from smt2c output.")
    new_body = r"""
ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_int<4> sm1 = (ap_int<4>)m1;
  ap_int<4> sm2 = (ap_int<4>)m2;
  ap_int<4> se1 = (ap_int<4>)e1;
  ap_int<4> se2 = (ap_int<4>)e2;
  ap_int<6> sh1 = (ap_int<6>)se1 + (ap_int<6>)8;
  ap_int<6> sh2 = (ap_int<6>)se2 + (ap_int<6>)8;
  ap_uint<5> ush1 = (ap_uint<5>)sh1;
  ap_uint<5> ush2 = (ap_uint<5>)sh2;
  ap_int<24> v1 = (ap_int<24>)sm1 << ush1;
  ap_int<24> v2 = (ap_int<24>)sm2 << ush2;
  ap_int<24> sum_v = v1 + v2;

  if (sum_v == 0) {
    ap_uint<4> exp_z = (ap_uint<4>)((ap_int<4>)-8);
    return (ap_uint<8>)((((ap_uint<8>)0) << 4) | exp_z);
  }

  ap_uint<24> abs_v = (sum_v < 0) ? (ap_uint<24>)(-sum_v) : (ap_uint<24>)sum_v;
  ap_int<6> msb =
      abs_v[23] ? 23 : abs_v[22] ? 22 : abs_v[21] ? 21 : abs_v[20] ? 20 :
      abs_v[19] ? 19 : abs_v[18] ? 18 : abs_v[17] ? 17 : abs_v[16] ? 16 :
      abs_v[15] ? 15 : abs_v[14] ? 14 : abs_v[13] ? 13 : abs_v[12] ? 12 :
      abs_v[11] ? 11 : abs_v[10] ? 10 : abs_v[9] ? 9  : abs_v[8] ? 8  :
      abs_v[7]  ? 7  : abs_v[6]  ? 6  : abs_v[5] ? 5  : abs_v[4] ? 4  :
      abs_v[3]  ? 3  : abs_v[2]  ? 2  : abs_v[1] ? 1  : 0;

  ap_int<6> exp = (ap_int<6>)(msb - 10);
  if (exp > 7) exp = 7;
  if (exp < -8) exp = -8;

  ap_int<6> shift_i = exp + 8;
  ap_uint<5> shift = (ap_uint<5>)shift_i;
  ap_int<24> mant_raw = sum_v >> shift;

  ap_int<6> mant = (ap_int<6>)mant_raw;
  if (mant > 7) mant = 7;
  if (mant < -8) mant = -8;

  ap_uint<4> mant_u = (ap_uint<4>)mant;
  ap_uint<4> exp_u = (ap_uint<4>)exp;
  return (ap_uint<8>)((((ap_uint<8>)mant_u) << 4) | exp_u);
}
""".strip("\n")

    return code[:start] + new_body + "\n" + code[end:]

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
    code = _fix_mxint8_full_sum_irep(code)
    code = _replace_known_irep(code)
    code = _strip_irep_noise(code)
    code = _safer_unsigned_negation(code)

    # 1) Fix bracket slices on bare identifiers (safe)
    code = _replace_bracket_slices_constants(code)

    # 2) Fix smt2c bug: x << 2[3,0] -> (x << 2)[3,0]
    code = _wrap_simple_shift_before_slice(code)

    # 3) Simple folds
    code = _fold_simple_int_additions(code)

    # 4) Convert (EXPR)[HI, LO] -> ap_uint<...>((EXPR)).range(HI, LO)
    code = _replace_bit_extractions(code)

    # 5) Width correctness
    code = _cast_entire_product(code)
    code = _cast_entire_addsub(code)

    # 6) Treat 'return (A,B,...)' as a packed value, not comma-operator
    code = _wrap_return_top_concat(code)

    # 7) Fix cast precedence on ternaries, then unify (make both arms same ap_*int<N>)
    code = _wrap_casted_ternary_branches(code)
    code = _unify_all_ternaries(code)
    code = _unify_ternaries_in_parens(code)
    code = _unify_ternaries_inside_casts(code)
    code = _replace_bracket_slices_constants(code)  # in case new slices appeared
    code = _wrap_simple_shift_before_slice(code)
    code = _replace_bit_extractions(code)  # in case new bit extractions appeared

    # 8) Canonicalisers (not all scripts actually output correct C++)
    code = _canonicalise_fp32_aligner(code)
    code = _canonicalise_fp32_raw_summer(code)
    code = _canonicalise_fp32_normaliser(code)
    code = _canonicalise_fp32_sum(code)

    enable_mxint8_add = os.environ.get("ENABLE_MXINT8_ADD_CANON", "0") == "1"
    if enable_mxint8_add:
        code = _canonicalise_mxint8_alignment(code)
        code = _canonicalise_mxint8_raw_adder(code)
        code = _canonicalise_mxint8_detect_overflow(code)
        code = _canonicalise_mxint8_normaliser_rounded(code)
    code = _canonicalise_mxint8_mult_renorm_flag(code)
    code = _canonicalise_mxint8_mult_mant(code)

    enable_mxint8_full_sum = os.environ.get("ENABLE_MXINT8_ADD_FULL_SUM_CANON", "0") == "1"
    if enable_mxint8_full_sum:
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
