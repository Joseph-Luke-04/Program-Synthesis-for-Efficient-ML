import re
import os
from pathlib import Path

# ------------------------------
# Type replacements
# ------------------------------
def _replace_bitvectors(c_code: str) -> str:
    """
    Map __CPROVER bitvectors to HLS-friendly types:
      - unsigned -> ap_uint<N>
      - signed   -> ap_int<N>
    """
    c_code = re.sub(r"unsigned\s+__CPROVER_bitvector\s*\[(\d+)\]", r"ap_uint<\1>", c_code)
    c_code = re.sub(r"signed\s+__CPROVER_bitvector\s*\[(\d+)\]", r"ap_int<\1>", c_code)
    return c_code

# ------------------------------
# Balanced parser for top-level ternary in return
# ------------------------------
def _rewrite_ternary_returns_balanced(c_code: str) -> str:
    """
    Replace any top-level 'return <cond> ? <a> : <b>;' with:
        { if (<cond>) { return <a>; } else { return <b>; } }
    Works even with nested parentheses and casts inside cond/a/b.
    """
    out = []
    i = 0
    n = len(c_code)
    while i < n:
        j = c_code.find("return", i)
        if j == -1:
            out.append(c_code[i:])
            break
        out.append(c_code[i:j])
        k = j + len("return")
        while k < n and c_code[k].isspace():
            k += 1

        # Find the terminating ';' of this return, tracking parentheses
        depth = 0
        pos = k
        qpos = -1
        cpos = -1
        while pos < n:
            ch = c_code[pos]
            if ch == '(':
                depth += 1
            elif ch == ')':
                if depth > 0:
                    depth -= 1
            elif ch == '?' and depth == 0 and qpos == -1:
                qpos = pos
            elif ch == ':' and depth == 0 and qpos != -1 and cpos == -1:
                cpos = pos
            elif ch == ';' and depth == 0:
                break
            pos += 1

        if pos >= n:
            out.append(c_code[j:])
            break

        ret_stmt = c_code[j:pos+1]
        if qpos == -1 or cpos == -1:
            out.append(ret_stmt)
            i = pos + 1
            continue

        cond = c_code[k:qpos].strip()
        expr_true = c_code[qpos+1:cpos].strip()
        expr_false = c_code[cpos+1:pos].strip()

        # Close any unbalanced '(' in cond (defensive)
        if cond.count("(") > cond.count(")"):
            cond += ")" * (cond.count("(") - cond.count(")"))

        repl = (
            "{\n"
            f"    if ({cond}) {{ return {expr_true}; }}\n"
            f"    else {{ return {expr_false}; }}\n"
            "}\n"
        )
        out.append(repl)
        i = pos + 1

    return "".join(out)

# ------------------------------
# Bit extraction fixer
# ------------------------------
def _replace_bit_extractions(c_code: str) -> str:
    """
    Replace invalid bit extraction syntax:
        (EXPR)[H, 0]  -> ap_uint<H+1>((EXPR))
        (EXPR)[H, L]  -> (EXPR).range(H, L)   (when L != 0)
    Also simplifies '0 + N' -> 'N'.
    """
    # Simplify trivial '0 + N'
    c_code = re.sub(r"\b0\s*\+\s*(\d+)", r"\1", c_code)

    # [H, 0]  ->  ap_uint<H+1>((EXPR))   (safe for native ints or ap_* types)
    def low_slice_repl(m):
        expr = m.group(1).strip()
        high = int(m.group(2))
        width = high + 1
        return f"(ap_uint<{width}>(({expr})))"

    c_code = re.sub(r"\(\s*(.+?)\s*\)\s*\[\s*(\d+)\s*,\s*0\s*\]", low_slice_repl, c_code)

    # General [H, L] -> (EXPR).range(H, L)
    def general_slice_repl(m):
        expr = m.group(1).strip()
        high = m.group(2).strip()
        low = m.group(3).strip()
        return f"({expr}).range({high}, {low})"

    c_code = re.sub(r"\(\s*(.+?)\s*\)\s*\[\s*([\d]+)\s*,\s*([\d]+)\s*\]", general_slice_repl, c_code)

    return c_code

# ------------------------------
# Main conversion
# ------------------------------
def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    """
    Converts a C file with __CPROVER_bitvector[n] types to HLS-compatible C++ using ap_uint/ap_int.
    Also:
      - rewrites top-level ternary returns to if/else blocks (balanced)
      - converts bit extraction of the form (EXPR)[H, L]:
           * [H, 0] -> ap_uint<H+1>((EXPR))
           * [H, L!=0] -> (EXPR).range(H, L)
    """
    with open(c_input_path, "r") as f:
        c_code = f.read()

    # Add header if missing
    if "#include <ap_int.h>" not in c_code:
        c_code = "#include <ap_int.h>\n\n" + c_code.strip()

    # 1) Replace bitvectors
    c_code = _replace_bitvectors(c_code)

    # 2) Rewrite top-level ternary returns robustly
    c_code = _rewrite_ternary_returns_balanced(c_code)

    # 3) Fix bit extractions
    c_code = _replace_bit_extractions(c_code)

    # 4) Clean up spacing
    c_code = re.sub(r"\s+\)", ")", c_code)
    c_code = re.sub(r"\(\s+", "(", c_code)
    c_code = c_code.strip() + "\n"

    # --- Save converted file into results/cpp ---
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
    """Wrapper used by synthesis_driver.py."""
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
