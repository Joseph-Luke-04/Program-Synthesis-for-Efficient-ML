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
    pipeline_line = ""
    if "fp32" in top_func:
        pipeline_line = (
            f"set_directive_pipeline -II 1 {top_func}\n"
            f"    set_directive_latency -min 1 -max 1 {top_func}"
        )
    elif top_func in {"add_full_sum", "mult_mxint_full_product"}:
        pipeline_line = (
            f"set_directive_pipeline -II 1 {top_func}\n"
            f"    set_directive_latency -min 1 -max 1 {top_func}"
        )

    tcl = f"""
    open_component -reset {design_name}_component -flow_target vivado
    set_top {top_func}
    add_files {design_path}
    set_part {{xc7z020clg400-1}}
    create_clock -period 1000000ns
    {pipeline_line}
    csynth_design
    export_design -rtl verilog
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def create_vivado_tcl(top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "vivado.tcl"
    verilog_dir = output_dir / "verilog_out"
    clk_period_ns = float(os.environ.get("VIVADO_CLK_PERIOD_NS", "4.000"))

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
      create_clock -name ap_clk -period {clk_period_ns:.3f} [get_ports ap_clk]
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

    # Critical path detail (only if clock exists)
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      report_timing -delay_type max -max_paths 1 -nworst 1 -file {output_dir}/timing_detail.rpt
    }}
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def parse_reports(output_dir: Path, top_func: str, design_name: str, run_impl: bool) -> dict:
    results = {"LUTs": -1, "FFs": -1, "DSPs": -1, "BRAMs": -1, "Cycles": -1, "Fmax_MHz": -1}
    comp = output_dir / f"{design_name}_component"

    def parse_vivado_critical_delay_ns() -> float | None:
        rpt = output_dir / "timing_detail.rpt"
        if not rpt.exists():
            return None
        try:
            with open(rpt, encoding="utf-8", errors="ignore") as f:
                for line in f:
                    m = re.search(r"Data Path Delay\s*:\s*([0-9.]+)\s*ns", line)
                    if m:
                        return float(m.group(1))
                    m = re.search(r"Data Path Delay\s*:\s*([0-9.]+)\b", line)
                    if m:
                        return float(m.group(1))
        except Exception:
            return None
        return None

    def parse_hls_estimated_clock_ns() -> float | None:
        # Prefer csynth.xml (always produced by csynth)
        for p in comp.rglob("*csynth.xml"):
            try:
                root = ET.parse(p).getroot()
                timing = root.find(".//PerformanceEstimates/SummaryOfTimingAnalysis")
                if timing is None:
                    continue
                unit = (timing.findtext("unit") or "ns").strip().lower()
                val = timing.findtext("EstimatedClockPeriod")
                if not val:
                    continue
                period = float(val)
                if unit == "ns":
                    return period
                if unit == "us":
                    return period * 1e3
                if unit == "ms":
                    return period * 1e6
            except Exception:
                pass
        return None

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
            period_ns = None
            wns_ns = None
            with open(output_dir / "timing.rpt", encoding="utf-8", errors="ignore") as f:
                in_clk = False; hdr = False
                in_intra = False; intra_hdr = False
                for raw in f:
                    line = raw.rstrip("\n")
                    if not in_clk and re.search(r"\bClock\s+Summary\b", line, re.IGNORECASE):
                        in_clk = True; continue
                    if in_clk and not hdr and re.search(r"^\s*Clock\s+Waveform", line):
                        hdr = True; continue
                    if in_clk and hdr:
                        r = line.strip()
                        if not r or set(r) <= set("-|"): 
                            continue
                        if r.startswith("ap_clk"):
                            cols = re.split(r"\s{2,}", r)
                            if len(cols) >= 3:
                                try:
                                    period_ns = float(cols[-2])
                                    results["Fmax_MHz"] = float(cols[-1])
                                except ValueError:
                                    pass
                            continue
                    if not in_intra and re.search(r"\bIntra Clock Table\b", line, re.IGNORECASE):
                        in_intra = True; continue
                    if in_intra and not intra_hdr and re.search(r"^\s*Clock\s+WNS", line):
                        intra_hdr = True; continue
                    if in_intra and intra_hdr:
                        r = line.strip()
                        if not r or set(r) <= set("-|"):
                            continue
                        if r.startswith("ap_clk"):
                            cols = re.split(r"\s{2,}", r)
                            if len(cols) >= 2:
                                try:
                                    wns_ns = float(cols[1])
                                except ValueError:
                                    wns_ns = None
                            break
            if period_ns is not None and wns_ns is not None:
                # If WNS is positive, design can run faster than the constraint.
                eff_period = period_ns - wns_ns
                if eff_period > 0:
                    results["Fmax_MHz"] = round(1000.0 / eff_period, 3)
            elif results["Fmax_MHz"] == -1 and period_ns is not None and period_ns > 0:
                results["Fmax_MHz"] = round(1000.0 / period_ns, 3)
        except Exception as e:
            print(f"[WARN] Could not parse timing.rpt: {e}")

        # Prefer critical path delay if report_timing detail exists.
        delay_ns = parse_vivado_critical_delay_ns()
        if delay_ns is not None and delay_ns > 0:
            results["Fmax_MHz"] = round(1000.0 / delay_ns, 3)

        # Fallback to HLS estimated clock if no ap_clk entry
        if results["Fmax_MHz"] == -1:
            period_ns = parse_hls_estimated_clock_ns()
            if period_ns and period_ns > 0:
                results["Fmax_MHz"] = round(1000.0 / period_ns, 3)

        # ================ ALSO parse HLS latency (cycles) ===================
        results["Cycles"] = parse_hls_cycles()
        return results

    # HLS-only path
    results["Cycles"] = parse_hls_cycles()
    if results["Fmax_MHz"] == -1:
        period_ns = parse_hls_estimated_clock_ns()
        if period_ns and period_ns > 0:
            results["Fmax_MHz"] = round(1000.0 / period_ns, 3)
    return results


def run_vitis_hls(design_path: str, top_func: str = None, impl: bool = False):
    design_path = Path(design_path).resolve()
    if not design_path.exists():
        print(f"[ERROR] Design file not found: {design_path}")
        sys.exit(1)
    
    design_name = design_path.stem
    src_text = design_path.read_text()

    # Prefer: explicit CLI > filename hint > strong symbol > generic autodetect
    TOP_HINTS = {
        "solution_fp32addition_fp32_full_sum": "fp32_sum",
        "solution_fp32addition_fp32_full_sum_combined": "fp32_sum",
        "solution_addition_raw_sum": "add_raw",
        "solution_addition_full_sum": "add_full_sum",
        "solution_mxint8addition_full_sum": "add_full_sum",
        "solution_mxint8addition_full_sum_combined": "add_full_sum",
        "solution_mxint8addition_alignment": "align_mantissas",
        "solution_mxint8addition_raw_sum": "add_raw",
        "solution_mxint8multiplication_full_product": "mult_mxint_full_product",
        "solution_mxint8multiplication_full_product_combined": "mult_mxint_full_product",
        "solution_fp32multiplication_full_product": "fp32_full_mul",
        "solution_fp32multiplication_full_product_combined": "fp32_full_mul",
        "solution_fp32multiplication_renorm": "fp32_mult_renorm",
        "solution_fp32multiplication_exp": "fp32_mult_exp",
        "solution_fp32multiplication_mant": "fp32_mult_mant",
    }

    if top_func is None:
        # 1) filename hint
        top_func = TOP_HINTS.get(design_name)
        if top_func:
            print(f"[INFO] Using top from filename hint: {top_func}")
        else:
            # 2) strong symbol preference if present
            if re.search(r'\bap_(?:u)?int\s*<\s*\d+\s*>\s+fp32_sum\s*\(', src_text):
                top_func = "fp32_sum"
                print(f"[INFO] Selected top by symbol presence: {top_func}")
            else:
                # 3) fallback to generic first-match autodetect
                auto = _detect_top_func_from_cpp(src_text)
                if auto:
                    top_func = auto
                    print(f"[INFO] Auto-detected top function: {top_func}")
                else:
                    print("[ERROR] Could not auto-detect a top function. Pass --top <name>.")
                    sys.exit(1)

    # Sanity check that the chosen top exists in the source
    if not re.search(rf'\b{re.escape(top_func)}\s*\(', src_text):
        print(f"[ERROR] Top '{top_func}' not found in {design_path.name}.")
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
