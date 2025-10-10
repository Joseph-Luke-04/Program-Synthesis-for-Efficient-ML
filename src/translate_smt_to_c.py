import os
import re
import subprocess
from pathlib import Path


def run_smt2c_translation(smt_path: str, save_dir: str) -> str:
    """
    Translates an SMT2 solution file into equivalent C code using smt2c.
    Saves the output in the provided save_dir (e.g. 'results/c').

    Args:
        smt_path: Path to the .smt2 solution file.
        save_dir: Directory where the .c file will be saved.

    Returns:
        Path to the generated .c file, or None if translation fails.
    """
    try:
        smt2c_path = os.path.expanduser("~/Desktop/Uni/Year_4/Dissertation/smt2c/src/smt2c")

        if not os.path.exists(smt2c_path):
            print(f"[ERROR] smt2c binary not found at {smt2c_path}")
            return None
        if not os.path.exists(smt_path):
            print(f"[WARN] SMT2 file not found at {smt_path}")
            return None

        print("\nTranslating SMT output to C using smt2c...\n")

        # Read SMT file contents
        with open(smt_path, "r") as f:
            smt_code = f.read().strip()

        # Collapse whitespace/newlines for safe CLI use
        smt_code = re.sub(r"\s+", " ", smt_code)

        # Build output filename (in results/c)
        base_name = Path(smt_path).stem  # e.g., "solution_addition_overflow"
        os.makedirs(save_dir, exist_ok=True)
        c_output_path = os.path.join(save_dir, f"{base_name}.c")

        # Run smt2c and capture output
        result = subprocess.run(
            [smt2c_path, smt_code],
            capture_output=True,
            text=True,
            check=True
        )

        # Save output
        with open(c_output_path, "w") as f:
            f.write(result.stdout.strip() + "\n")

        print(f"C file saved to: {c_output_path}\n")
        print("Generated C code:\n")
        print(result.stdout.strip())

        return c_output_path

    except subprocess.CalledProcessError as e:
        print(f"[ERROR] smt2c failed:\n{e.stderr}")
    except Exception as e:
        print(f"[ERROR] Failed to run smt2c: {e}")

    return None


if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python translate_smt_to_c.py <path_to_smt2_file>")
        sys.exit(1)

    run_smt2c_translation(sys.argv[1], "results/c")
