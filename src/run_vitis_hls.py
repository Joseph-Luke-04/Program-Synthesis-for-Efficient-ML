#!/usr/bin/env python3
import os, sys, re, textwrap, subprocess
from pathlib import Path

def _detect_top_func_from_cpp(src: str) -> str | None:
    """
    Return the first non-main free function whose return type is ap_int<>/ap_uint<>.
    Handles optional qualifiers like 'static'/'inline'.
    """
    # strip C++ comments to avoid false matches in comments
    src = re.sub(r'//.*', '', src)
    src = re.sub(r'/\*.*?\*/', '', src, flags=re.S)
    # e.g. 'ap_uint<4> foo(' or 'static inline ap_int<5> bar('
    pat = r'\b(?:static\s+|inline\s+|constexpr\s+)*ap_(?:u)?int\s*<\s*\d+\s*>\s+([A-Za-z_]\w*)\s*\('
    m = re.findall(pat, src)
    for name in m:
        if name != "main":
            return name
    return None

def create_vitis_tcl(design_path: Path, top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "vitis.tcl"
    design_name = design_path.stem
    tcl = f"""
    open_component -reset {design_name}_component -flow_target vivado
    set_top {top_func}

    # Design sources
    add_files {design_path}

    # Target device & clock
    set_part {{xc7z020clg400-1}}
    create_clock -period 4

    # Synthesize to RTL (no csim/cosim since there is no main())
    csynth_design

    # Export RTL + reports
    export_design -format ip_catalog -rtl verilog -output {output_dir}/{design_name}_export
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path

def run_vitis_hls(design_path: str, top_func: str = None):
    design_path = Path(design_path).resolve()
    if not design_path.exists():
        print(f"[ERROR] Design file not found: {design_path}")
        sys.exit(1)

    src_text = design_path.read_text()

    # If user didn't pass --top, auto-detect from the file
    if top_func is None:
        auto = _detect_top_func_from_cpp(src_text)
        if auto:
            top_func = auto
            print(f"[INFO] Auto-detected top function: {top_func}")
        else:
            print("[ERROR] Could not auto-detect a top function. Pass --top <name>.")
            sys.exit(1)

    # Per-design output dir
    project_root = Path("/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS")
    output_dir = project_root / design_path.stem
    os.makedirs(output_dir, exist_ok=True)

    # Generate TCL
    tcl_path = create_vitis_tcl(design_path, top_func, output_dir)
    print(f"[INFO] Generated Vitis TCL script: {tcl_path}")

    vitis_settings = "/tools/Xilinx/2025.1/Vitis/settings64.sh"

    cmd = f"""
    bash -c "source {vitis_settings} && \
    cd {output_dir} && \
    vitis-run --mode hls --tcl {tcl_path} > vitis_run.log 2>&1"
    """
    print("[INFO] Running Vitis HLS synthesis (this may take a few minutes)...")
    ret = os.system(cmd)

    if ret == 0:
        print("\n[SUCCESS] Vitis HLS run completed successfully.")
        print(f"Logs and reports saved under: {output_dir}")
    else:
        print("\n[ERROR] Vitis HLS run failed. Check:")
        print(f"  {output_dir}/vitis_run.log")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python run_vitis_hls.py <path_to_cpp_file> [--top <function_name>]")
        sys.exit(1)

    cpp_file = sys.argv[1]
    top_func = None
    if "--top" in sys.argv:
        top_func = sys.argv[sys.argv.index("--top") + 1]

    run_vitis_hls(cpp_file, top_func)
