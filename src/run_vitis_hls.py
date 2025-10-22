# Some code copied from https://github.com/craft-edinburgh/docker-example-hls/blob/main/report_hls.py
import os, sys, re, json, xml.etree.ElementTree as ET
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


def create_hls_tcl(design_path: Path, top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "hls.tcl"
    design_name = design_path.stem

    tcl = f"""
    open_component -reset {design_name}_component -flow_target vivado
    set_top {top_func}
    add_files {design_path}
    set_part {{xc7z020clg400-1}}
    create_clock -period 4ns
    csynth_design
    export_design -rtl verilog
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def create_vivado_tcl(top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "vivado.tcl"
    verilog_dir = output_dir / "verilog_out"

    tcl = f"""
    # --- Non-project flow: read RTL, synth, implement, report ---

    # Collect RTL
    set v_files  [glob -nocomplain {{{verilog_dir}/*.v}}]
    set sv_files [glob -nocomplain {{{verilog_dir}/*.sv}}]
    if {{[llength $v_files] == 0 && [llength $sv_files] == 0}} {{
      puts "ERROR: No RTL files found in {verilog_dir}"
      exit 1
    }}
    if {{[llength $v_files]  > 0}} {{ read_verilog $v_files }}
    foreach f $sv_files {{ read_verilog -sv $f }}

    # Synthesis
    synth_design -top {top_func} -part xc7z020clg400-1

    # Add a clock ONLY if the port exists (combinational designs won't have ap_clk)
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      create_clock -name ap_clk -period 4.000 [get_ports ap_clk]
    }} else {{
      puts "INFO: No ap_clk port found; skipping create_clock (design appears combinational)."
    }}

    # Implementation
    opt_design
    place_design
    route_design

    # Reports
    report_utilization    -file {output_dir}/utilization.rpt
    report_timing_summary -file {output_dir}/timing.rpt

    # Try XML (RPX) timing if supported (avoid nested braces in catch)
    set rpx_path "{output_dir}/timing.rpx"
    if {{[catch {{report_timing_summary -rpx $rpx_path}} err]}} {{
      puts "INFO: RPX timing not available: $err"
    }}
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def parse_reports(output_dir: Path, top_func: str, design_name: str, run_impl: bool) -> dict:
    results = {"LUTs": -1, "FFs": -1, "DSPs": -1, "BRAMs": -1, "Cycles": -1, "Fmax_MHz": -1}
    comp = output_dir / f"{design_name}_component"

    def parse_hls_cycles() -> int:
        # 1) Prefer csynth.xml (always produced by csynth)
        for p in comp.rglob("*csynth.xml"):
            try:
                import xml.etree.ElementTree as ET, re
                root = ET.parse(p).getroot()
                lat = root.find(".//PerformanceEstimates/SummaryOfOverallLatency")
                if lat is not None:
                    def get_num(tag: str):
                        e = lat.find(tag)
                        if e is None:
                            return None
                        # attribute form: <Best-caseLatency value="3"/>
                        v = e.attrib.get("value")
                        if v and v.isdigit():
                            return int(v)
                        # text form: "min = 3, max = 3, avg = 3"
                        nums = [int(x) for x in re.findall(r"\d+", (e.text or ""))]
                        return nums[0] if nums else None
                    worst = get_num("Worst-caseLatency")
                    best  = get_num("Best-caseLatency")
                    if worst is not None: return worst
                    if best  is not None: return best
            except Exception:
                pass

        # 2) Cosim report (only exists if you run cosim)
        for p in comp.rglob(f"*{top_func}*cosim.rpt"):
            try:
                with open(p, encoding="utf-8", errors="ignore") as f:
                    for line in f:
                        if "Verilog|" in line:
                            cols = [x.strip() for x in line.split("|")]
                            if len(cols) > 4 and cols[4].isdigit():
                                return int(cols[4])
                            # fallback: last integer on the row
                            import re
                            nums = [int(x) for x in re.findall(r"\d+", line)]
                            if nums:
                                return nums[-1]
            except Exception:
                pass

        # 3) Text csynth.rpt
        for p in comp.rglob("*csynth.rpt"):
            try:
                import re
                with open(p, encoding="utf-8", errors="ignore") as f:
                    it = iter(f)
                    for line in it:
                        if "Latency (cycles)" in line:
                            next(it, None)          # separator
                            row = next(it, "")      # numbers row
                            nums = [int(n) for n in re.findall(r"\d+", row)]
                            if nums:
                                # usually: min, max, avg – report worst-case if present
                                return (nums[1] if len(nums) > 1 else nums[0])
            except Exception:
                pass

        return -1

    if run_impl:
        # =================== Parse Vivado utilization.rpt ========================
        try:
            with open(output_dir / "utilization.rpt", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    s = line.strip().lower()
                    def first_int(text):
                        m = re.search(r"\b(\d+)\b", text);  return int(m.group(1)) if m else None
                    if any(k in s for k in ("slice luts","clb luts","| luts |","luts (used)","luts")):
                        v = first_int(line);  results["LUTs"] = v if v is not None else results["LUTs"]
                    if any(k in s for k in ("slice registers","clb registers","| ffs |","flip-flops","registers (used)","ffs")):
                        v = first_int(line);  results["FFs"]  = v if v is not None else results["FFs"]
                    if re.search(r"\bdsp", s):
                        v = first_int(line);  results["DSPs"] = v if v is not None else results["DSPs"]
                    if ("block ram" in s) or s.startswith("bram") or ("ramb" in s):
                        v = first_int(line);  results["BRAMs"] = v if v is not None else results["BRAMs"]
        except Exception as e:
            print(f"[WARN] Could not parse utilization.rpt: {e}")

        # =================== Parse Vivado timing.rpt for Fmax ========================
        try:
            with open(output_dir / "timing.rpt", encoding="utf-8", errors="ignore") as f:
                in_clk = False; hdr = False
                for raw in f:
                    line = raw.rstrip("\n")
                    if not in_clk and re.search(r"\bClock\s+Summary\b", line, re.IGNORECASE):
                        in_clk = True; continue
                    if in_clk and not hdr and re.search(r"^\s*Clock\s+Waveform", line):
                        hdr = True; continue
                    if not (in_clk and hdr): continue
                    r = line.strip()
                    if not r or set(r) <= set("-|"): continue
                    if r.startswith("ap_clk"):
                        cols = re.split(r"\s{2,}", r)
                        if len(cols) >= 3:
                            try:
                                results["Fmax_MHz"] = float(cols[-1])
                            except ValueError:
                                pass
                            if results["Fmax_MHz"] == -1:
                                try:
                                    period_ns = float(cols[-2])
                                    if period_ns > 0:
                                        results["Fmax_MHz"] = round(1000.0/period_ns, 3)
                                except ValueError:
                                    pass
                        break
        except Exception as e:
            print(f"[WARN] Could not parse timing.rpt: {e}")

        # ================ ALSO parse HLS latency (cycles) ===================
        results["Cycles"] = parse_hls_cycles()
        return results

    # HLS-only path
    results["Cycles"] = parse_hls_cycles()
    return results


def run_vitis_hls(design_path: str, top_func: str = None, impl: bool = False):
    design_path = Path(design_path).resolve()
    if not design_path.exists():
        print(f"[ERROR] Design file not found: {design_path}")
        sys.exit(1)
    
    design_name = design_path.stem
    src_text = design_path.read_text()

    if top_func is None:
        auto = _detect_top_func_from_cpp(src_text)
        if auto:
            top_func = auto
            print(f"[INFO] Auto-detected top function: {top_func}")
        else:
            print("[ERROR] Could not auto-detect a top function. Pass --top <name>.")
            sys.exit(1)

    project_root = Path("/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS")
    output_dir = project_root / design_path.stem
    os.makedirs(output_dir, exist_ok=True)
    
    vitis_settings = "/tools/Xilinx/2025.1/Vitis/settings64.sh"
    vivado_settings = "/tools/Xilinx/2025.1/Vivado/settings64.sh" # Vivado has its own settings script

    # STAGE 1: HLS Synthesis
    hls_tcl_path = create_hls_tcl(design_path, top_func, output_dir)
    print(f"[INFO] Generated HLS TCL script: {hls_tcl_path}")
    
    hls_cmd = f"""
    bash -c "source {vitis_settings} && \
    cd {output_dir} && \
    vitis-run --mode hls --tcl {hls_tcl_path} > vitis_hls.log 2>&1"
    """
    print("[INFO] Running Vitis HLS synthesis...")
    ret_hls = os.system(hls_cmd)

    if ret_hls != 0:
        print("\n[ERROR] Vitis HLS run failed. Check:")
        print(f"  {output_dir}/vitis_hls.log")
        return # Stop if HLS fails

    print("\n[SUCCESS] Vitis HLS run completed successfully.")
    
    from glob import glob
    import shutil

    # Locate HLS RTL and stage it into <output_dir>/verilog_out
    component_dir = output_dir / f"{design_name}_component"
    rtl_candidates = [
        component_dir / "hls" / "syn" / "verilog",
        component_dir / "hls" / "syn" / "hdl",       # some versions use 'hdl'
    ]
    verilog_out = output_dir / "verilog_out"
    verilog_out.mkdir(parents=True, exist_ok=True)

    copied = 0
    for d in rtl_candidates:
        if d.exists():
            for ext in ("*.v", "*.sv"):
                for v in glob(str(d / ext)):
                    shutil.copy2(v, verilog_out)
                    copied += 1

    if copied == 0:
        print(f"[ERROR] No RTL .v files found under: {rtl_candidates}")
        print(f"        Check {output_dir}/vitis_hls.log to see where csynth wrote RTL.")
        return
    else:
        print(f"[INFO] Staged {copied} Verilog files into: {verilog_out}")

    # Optional: print candidate module names in the staged RTL
    mods = []
    for ext in ("*.v", "*.sv"):
        for v in verilog_out.glob(ext):
            with open(v) as f:
                for line in f:
                    m = re.search(r"^\s*module\s+([A-Za-z_]\w*)\b", line)
                    if m:
                        mods.append(m.group(1))
                        break
    if mods:
        print(f"[INFO] Candidate RTL modules: {sorted(set(mods))}")

    # STAGE 2: Vivado Implementation (if requested)
    if impl:
        vivado_tcl_path = create_vivado_tcl(top_func, output_dir)
        print(f"[INFO] Generated Vivado TCL script: {vivado_tcl_path}")

        print("[INFO] Cleaning up previous Vivado log and journal files...")
        log_path = output_dir / "vivado.log"
        jou_path = output_dir / "vivado.jou"
        if log_path.exists():
            log_path.unlink() # Deletes the file
        if jou_path.exists():
            jou_path.unlink() # Deletes the file

        vivado_cmd = f"""
        bash -c "source {vivado_settings} && \
        cd {output_dir} && \
        vivado -mode batch -source {vivado_tcl_path} > vivado.log 2>&1"
        """
        print("[INFO] Running Vivado implementation (this will take several minutes)...")
        ret_vivado = os.system(vivado_cmd)

        if ret_vivado != 0:
            print("\n[ERROR] Vivado implementation run failed. Check:")
            print(f"  {output_dir}/vivado.log")
            return

        print("\n[SUCCESS] Vivado implementation completed successfully.")

    # Parse Reports
    print("\n--- Hardware Results ---")
    results = parse_reports(output_dir, top_func, design_path.stem, impl)
    print(json.dumps(results, indent=4))

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python run_vitis_hls.py <path_to_cpp_file> [--top <function_name>] [--impl]")
        sys.exit(1)

    cpp_file = sys.argv[1]
    top_func = None
    if "--top" in sys.argv:
        try:
            top_func = sys.argv[sys.argv.index("--top") + 1]
        except IndexError:
            print("[ERROR] --top requires a function name.")
            sys.exit(1)
            
    # Check if the --impl flag is present
    run_impl = "--impl" in sys.argv

    run_vitis_hls(cpp_file, top_func, run_impl)
