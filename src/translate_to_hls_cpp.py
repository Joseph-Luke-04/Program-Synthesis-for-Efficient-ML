import re
import os
from pathlib import Path

def convert_cp_to_hls(c_input_path: str, save_output: bool = True) -> str:
    """
    Converts a C file with __CPROVER_bitvector[n] types to HLS-compatible C++ using ap_uint/ap_int.
    Adds '#include <ap_int.h>' at the top.
    """

    # Read input file
    with open(c_input_path, "r") as f:
        c_code = f.read()

    # Add #include <ap_int.h> if missing
    if "#include <ap_int.h>" not in c_code:
        c_code = "#include <ap_int.h>\n\n" + c_code.strip()

    # Replace unsigned __CPROVER_bitvector[n] with ap_uint<n>
    c_code = re.sub(
        r"unsigned\s+__CPROVER_bitvector\s*\[(\d+)\]",
        r"ap_uint<\1>",
        c_code
    )

    # Replace signed __CPROVER_bitvector[n] with ap_int<n>
    c_code = re.sub(
        r"signed\s+__CPROVER_bitvector\s*\[(\d+)\]",
        r"ap_int<\1>",
        c_code
    )

    # Clean up redundant parentheses or spacing
    c_code = re.sub(r"\s+\)", ")", c_code)
    c_code = re.sub(r"\(\s+", "(", c_code)
    c_code = c_code.strip() + "\n"

    # --- Save converted file into results/cpp ---
    if save_output:
        base_name = Path(c_input_path).stem  # e.g. "solution_addition_overflow"

        # From results/c → results/, then into cpp/
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
    """
    Wrapper used by synthesis_driver.py.
    Checks for the .c file and converts it if present.
    """
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
