import re
import os
from pathlib import Path

# ================= Type mapping ==================
def _replace_bitvectors(c_code: str) -> str:
    def _unsigned(m):
        w = int(m.group(1))
        return "bool" if w == 1 else f"ap_uint<{w}>"
    def _signed(m):
        w = int(m.group(1))
        return "bool" if w == 1 else f"ap_int<{w}>"
    c_code = re.sub(r"unsigned\s+__CPROVER_bitvector\s*\[(\d+)\]", _unsigned, c_code)
    c_code = re.sub(r"signed\s+__CPROVER_bitvector\s*\[(\d+)\]", _signed, c_code)
    return c_code

# ============ Bool condition simplifier ===============
def _collect_bool_names(c_code: str) -> set:
    names = set()
    for m in re.finditer(r"\bbool\s+([A-Za-z_]\w*)", c_code):
        names.add(m.group(1))
    return names

def _simplify_bool_comparisons(c_code: str) -> str:
    bools = _collect_bool_names(c_code)
    for name in bools:
        c_code = re.sub(rf"\b{name}\s*==\s*1\b", name, c_code)
        c_code = re.sub(rf"\b1\s*==\s*{name}\b", name, c_code)
        c_code = re.sub(rf"\b{name}\s*!=\s*0\b", name, c_code)
        c_code = re.sub(rf"\b0\s*!=\s*{name}\b", name, c_code)
        c_code = re.sub(rf"\b{name}\s*==\s*0\b", f"!{name}", c_code)
        c_code = re.sub(rf"\b0\s*==\s*{name}\b", f"!{name}", c_code)
        c_code = re.sub(rf"\b{name}\s*!=\s*1\b", f"!{name}", c_code)
        c_code = re.sub(rf"\b1\s*!=\s*{name}\b", f"!{name}", c_code)
    return c_code

# ================== Bit extraction fixes ====================
def _replace_bit_extractions(c_code: str) -> str:
    c_code = re.sub(r"\b0\s*\+\s*(\d+)", r"\1", c_code)
    def looks_like_top_ap(expr: str) -> bool:
        s = expr.strip()
        if s.startswith("(") and s.endswith(")"):
            inner = s[1:-1].strip()
            if inner.startswith(("ap_uint<","ap_int<")): return True
            s = inner
        if s.startswith(("(ap_uint<","(ap_int<")): return True
        return bool(re.fullmatch(r"[A-Za-z_]\w*", s))
    def slice_repl(m):
        expr, high, low = m.group(1).strip(), int(m.group(2)), int(m.group(3))
        return f"({expr}).range({high}, {low})" if looks_like_top_ap(expr) \
               else f"(ap_uint<{high-low+1}>(({expr})))"
    return re.sub(r"\(\s*(.+?)\s*\)\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]", slice_repl, c_code)

# ================ Force ternary branches to return type =================
def _get_function_return_type(c_code: str) -> str | None:
    # Grab the first function’s return type: ap_uint<N> | ap_int<N> | bool
    m = re.search(r"\b(ap_u?int<\d+>|bool)\s+[A-Za-z_]\w*\s*\(", c_code)
    return m.group(1) if m else None

def _wrap_as_type(expr: str, ty: str) -> str:
    expr = expr.strip()
    # ap_* need constructor-style cast; bool can use C cast
    if ty.startswith(("ap_uint<","ap_int<")):
        return f"{ty}(({expr}))"
    else:
        return f"({ty})({expr})"

def _force_ternary_return_casts(c_code: str) -> str:
    ret_ty = _get_function_return_type(c_code)
    if not ret_ty:
        return c_code

    # Match "return cond ? a : b;" (non-greedy up to semicolon)
    def repl(m):
        cond = m.group(1).strip()
        a    = m.group(2).strip()
        b    = m.group(3).strip()
        a_cast = _wrap_as_type(a, ret_ty)
        b_cast = _wrap_as_type(b, ret_ty)
        return f"return {cond} ? {a_cast} : {b_cast};"

    pattern = r"return\s+(.+?)\?\s*(.+?)\s*:\s*(.+?)\s*;"
    return re.sub(pattern, repl, c_code)

def _clean_whitespace(c_code: str) -> str:
    lines = [line.rstrip() for line in c_code.splitlines()]
    c_code = "\n".join(lines)
    c_code = re.sub(r"\n\s*\n\s*}", "\n}", c_code)
    return c_code.strip() + "\n"

# =========================== Main ================================
def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    with open(c_input_path, "r") as f:
        c_code = f.read()

    if "#include <ap_int.h>" not in c_code:
        c_code = "#include <ap_int.h>\n\n" + c_code.strip()

    c_code = _replace_bitvectors(c_code)
    c_code = _simplify_bool_comparisons(c_code)
    c_code = _replace_bit_extractions(c_code)
    c_code = _force_ternary_return_casts(c_code)
    c_code = _clean_whitespace(c_code)

    if save_output:
        base_name = Path(c_input_path).stem
        results_root = Path(c_input_path).resolve().parents[1]
        cpp_dir = results_root / "cpp"
        os.makedirs(cpp_dir, exist_ok=True)
        cpp_path = cpp_dir / f"{base_name}.cpp"
        with open(cpp_path, "w") as f:
            f.write(c_code)
        print(f"HLS C++ file saved to: {cpp_path}")
        print("Generated HLS-ready C++ code:\n")
        print(c_code)
        return str(cpp_path)
    return c_code

def run_hls_conversion(c_output_path: str):
    if not os.path.exists(c_output_path):
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
