import os, re, subprocess
from pathlib import Path
from src.dependencies import DEPENDENCY_MAP

def _extract_define_funs(s: str) -> list[str]:
    blocks, i = [], 0
    while True:
        i = s.find("(define-fun", i)
        if i == -1: break
        depth, j = 0, i
        while j < len(s):
            ch = s[j]
            if ch == "(": depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    blocks.append(s[i:j+1]); i = j + 1; break
            j += 1
        else:
            break
    return blocks

def _block_name(blk: str) -> str:
    m = re.search(r"\(define-fun\s+([^\s()]+)", blk)
    return m.group(1) if m else "<unknown>"

def run_smt2c_translation(smt_path: str, save_dir: str) -> str | None:
    smt2c_path = os.path.expanduser("~/Desktop/Uni/Year_4/Dissertation/smt2c/src/smt2c")
    if not os.path.exists(smt2c_path):
        print(f"[ERROR] smt2c binary not found at {smt2c_path}")
        return None
    if not os.path.exists(smt_path):
        print(f"[ERROR] SMT2 file not found at {smt_path}")
        return None

    print("\nTranslating SMT output to C using smt2c...")

    base_name = Path(smt_path).stem                    # e.g. 'solution_fp32addition_fp32_full_sum'
    component_key = base_name.replace("solution_", "") # e.g. 'fp32addition_fp32_full_sum'

    smt_dir = Path(smt_path).parent
    all_blocks: list[str] = []

    # Load dependencies first (so helpers come before top)
    deps = DEPENDENCY_MAP.get(component_key, [])
    if deps:
        print(f"[INFO] Component '{component_key}' has dependencies: {deps}")
    for dep in deps:
        dep_file = smt_dir / f"solution_{dep}.smt2"
        if not dep_file.exists():
            print(f"[ERROR] Dependency file not found: {dep_file}")
            return None
        print(f"       -> Loading functions from: {dep_file.name}")
        dep_text = dep_file.read_text()
        all_blocks.extend(_extract_define_funs(dep_text))

    # Load main file blocks
    main_text = Path(smt_path).read_text()
    all_blocks.extend(_extract_define_funs(main_text))

    if not all_blocks:
        print("[ERROR] No '(define-fun ...)' expressions found.")
        return None

    print(f"[INFO] Found {len(all_blocks)} define-fun block(s). Order passed to smt2c:")
    for nm in map(_block_name, all_blocks):
        print(f"    - {nm}")

    # One-shot call to smt2c with ALL blocks as separate argv items
    argv = [smt2c_path] + [re.sub(r"\s+", " ", b).strip() for b in all_blocks]

    try:
        result = subprocess.run(argv, capture_output=True, text=True, check=True, timeout=120)
    except subprocess.CalledProcessError as e:
        print("[ERROR] smt2c failed.")
        if e.stderr: print(e.stderr.strip())
        return None

    final_c_code = (result.stdout or "").strip()
    if not final_c_code:
        print("[ERROR] smt2c produced empty output.")
        return None

    os.makedirs(save_dir, exist_ok=True)
    out_path = str(Path(save_dir) / f"{base_name}.c")
    Path(out_path).write_text(final_c_code + "\n")
    print(f"C file saved to: {out_path}\n")
    print("Generated C code:\n")
    print(final_c_code)
    return out_path
