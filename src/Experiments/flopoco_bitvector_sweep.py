import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from .bitvector_sweep import (
        compute_area_score,
        parse_cocotb_metrics,
        parse_int_sweep,
        pick_optuna_accuracy_objective,
    )
    from ..run_vitis_hls import parse_reports
except ImportError:
    from src.Experiments.bitvector_sweep import (
        compute_area_score,
        parse_cocotb_metrics,
        parse_int_sweep,
        pick_optuna_accuracy_objective,
    )
    from run_vitis_hls import parse_reports


@dataclass(frozen=True)
class FlopocoTarget:
    key: str
    op: str
    dtype: str
    base_solution: str
    wrapper_filename: str
    top_func: str
    cocotb_module: str
    variant_env: str
    fp32: bool
    is_mul: bool


TARGETS: dict[str, FlopocoTarget] = {
    "fp32_add": FlopocoTarget(
        key="fp32_add",
        op="Addition",
        dtype="FP32",
        base_solution="solution_fp32addition_flopoco",
        wrapper_filename="fp32_sum_flopoco.vhd",
        top_func="fp32_sum_flopoco",
        cocotb_module="tests.addition.test_fp32_adder",
        variant_env="FP32_ADD_VARIANT",
        fp32=True,
        is_mul=False,
    ),
    "fp32_mul": FlopocoTarget(
        key="fp32_mul",
        op="Multiplication",
        dtype="FP32",
        base_solution="solution_fp32multiplication_flopoco",
        wrapper_filename="fp32_full_mul_flopoco.vhd",
        top_func="fp32_full_mul_flopoco",
        cocotb_module="tests.multiplication.test_fp32_multiplier",
        variant_env="FP32_MUL_VARIANT",
        fp32=True,
        is_mul=True,
    ),
}

FULL_FP32_EXP_BITS = 8


def parse_mant_bits(spec: str) -> list[int]:
    return parse_int_sweep(spec, "--mant-bits", min_value=1, max_value=24, default_step=1)


def _zeros(width: int) -> str:
    return '"' + ("0" * width) + '"'


def _quantise_expr(signal: str, width: int, keep_msb_bits: int) -> str:
    if keep_msb_bits >= width:
        return signal
    if keep_msb_bits <= 0:
        return "(others => '0')"
    drop = width - keep_msb_bits
    return f"{signal}({width - 1} downto {drop}) & {_zeros(drop)}"


def render_fp32_add_wrapper(mant_bits: int) -> str:
    frac_bits = max(0, mant_bits - 1)
    e1_expr = "e1"
    e2_expr = "e2"
    m1_expr = _quantise_expr("m1", width=23, keep_msb_bits=frac_bits)
    m2_expr = _quantise_expr("m2", width=23, keep_msb_bits=frac_bits)
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_sum_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        s1        : in  std_logic_vector(0 downto 0);
        e1        : in  std_logic_vector(7 downto 0);
        m1        : in  std_logic_vector(22 downto 0);
        s2        : in  std_logic_vector(0 downto 0);
        e2        : in  std_logic_vector(7 downto 0);
        m2        : in  std_logic_vector(22 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_sum_flopoco is
    component fp32_add_flopoco is
        port (
            clk : in  std_logic;
            X   : in  std_logic_vector(31 downto 0);
            Y   : in  std_logic_vector(31 downto 0);
            R   : out std_logic_vector(31 downto 0)
        );
    end component;

    signal e1_q      : std_logic_vector(7 downto 0);
    signal e2_q      : std_logic_vector(7 downto 0);
    signal m1_q      : std_logic_vector(22 downto 0);
    signal m2_q      : std_logic_vector(22 downto 0);
    signal x_pack    : std_logic_vector(31 downto 0);
    signal y_pack    : std_logic_vector(31 downto 0);
    signal r_pack    : std_logic_vector(31 downto 0);
    signal done_pipe : std_logic_vector(7 downto 0) := (others => '0');
begin
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                done_pipe <= (others => '0');
            else
                done_pipe <= done_pipe(6 downto 0) & ap_start;
            end if;
        end if;
    end process;

    e1_q <= {e1_expr};
    e2_q <= {e2_expr};
    m1_q <= {m1_expr};
    m2_q <= {m2_expr};
    x_pack <= s1 & e1_q & m1_q;
    y_pack <= s2 & e2_q & m2_q;

    ap_done   <= done_pipe(7);
    ap_idle   <= '1';
    ap_ready  <= '1';
    ap_return <= r_pack;

    u_fp32_add_flopoco : fp32_add_flopoco
        port map (
            clk => ap_clk,
            X   => x_pack,
            Y   => y_pack,
            R   => r_pack
        );
end architecture;
"""


def render_fp32_mul_wrapper(mant_bits: int) -> str:
    frac_bits = max(0, mant_bits - 1)
    ea_expr = "ea_in"
    eb_expr = "eb_in"
    ma_expr = _quantise_expr("ma_in", width=23, keep_msb_bits=frac_bits)
    mb_expr = _quantise_expr("mb_in", width=23, keep_msb_bits=frac_bits)
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_full_mul_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        a         : in  std_logic_vector(31 downto 0);
        b         : in  std_logic_vector(31 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_full_mul_flopoco is
    component fp32_fma_flopoco is
        port (
            clk      : in  std_logic;
            A        : in  std_logic_vector(31 downto 0);
            B        : in  std_logic_vector(31 downto 0);
            C        : in  std_logic_vector(31 downto 0);
            negateAB : in  std_logic;
            negateC  : in  std_logic;
            RndMode  : in  std_logic_vector(1 downto 0);
            R        : out std_logic_vector(31 downto 0)
        );
    end component;

    signal ea_in    : std_logic_vector(7 downto 0);
    signal eb_in    : std_logic_vector(7 downto 0);
    signal ma_in    : std_logic_vector(22 downto 0);
    signal mb_in    : std_logic_vector(22 downto 0);
    signal ea_q     : std_logic_vector(7 downto 0);
    signal eb_q     : std_logic_vector(7 downto 0);
    signal ma_q     : std_logic_vector(22 downto 0);
    signal mb_q     : std_logic_vector(22 downto 0);
    signal a_q      : std_logic_vector(31 downto 0);
    signal b_q      : std_logic_vector(31 downto 0);
    signal donepipe : std_logic_vector(4 downto 0) := (others => '0');
begin
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                donepipe <= (others => '0');
            else
                donepipe <= donepipe(3 downto 0) & ap_start;
            end if;
        end if;
    end process;

    ea_in <= a(30 downto 23);
    eb_in <= b(30 downto 23);
    ma_in <= a(22 downto 0);
    mb_in <= b(22 downto 0);
    ea_q <= {ea_expr};
    eb_q <= {eb_expr};
    ma_q <= {ma_expr};
    mb_q <= {mb_expr};
    a_q <= a(31) & ea_q & ma_q;
    b_q <= b(31) & eb_q & mb_q;

    ap_done  <= donepipe(4);
    ap_idle  <= '1';
    ap_ready <= '1';

    u_fp32_fma_flopoco : fp32_fma_flopoco
        port map (
            clk      => ap_clk,
            A        => a_q,
            B        => b_q,
            C        => (others => '0'),
            negateAB => '0',
            negateC  => '0',
            RndMode  => "00",
            R        => ap_return
        );
end architecture;
"""


def render_wrapper(target: FlopocoTarget, mant_bits: int) -> str:
    if target.key == "fp32_add":
        return render_fp32_add_wrapper(mant_bits)
    if target.key == "fp32_mul":
        return render_fp32_mul_wrapper(mant_bits)
    raise ValueError(f"Unsupported target: {target.key}")


def create_vivado_tcl_for_rtl(top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "vivado.tcl"
    rtl_dir = output_dir / "verilog_out"
    clk_period_ns = float(os.environ.get("VIVADO_CLK_PERIOD_NS", "4.000"))
    tcl = f"""
    set vhdl_files [concat [glob -nocomplain {{{rtl_dir}/*.vhd}}] [glob -nocomplain {{{rtl_dir}/*.vhdl}}]]
    set v_files    [glob -nocomplain {{{rtl_dir}/*.v}}]
    set sv_files   [glob -nocomplain {{{rtl_dir}/*.sv}}]

    if {{[llength $vhdl_files] == 0 && [llength $v_files] == 0 && [llength $sv_files] == 0}} {{
      puts "ERROR: No RTL sources found in {rtl_dir}"
      exit 1
    }}

    if {{[llength $vhdl_files] > 0}} {{ foreach f $vhdl_files {{ read_vhdl $f }} }}
    if {{[llength $v_files] > 0}}    {{ read_verilog $v_files }}
    foreach f $sv_files {{ read_verilog -sv $f }}

    synth_design -top {top_func} -part xc7z020clg400-1
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      create_clock -name ap_clk -period {clk_period_ns:.3f} [get_ports ap_clk]
    }}
    opt_design
    place_design
    route_design
    report_utilization    -file {output_dir}/utilization.rpt
    report_timing_summary -file {output_dir}/timing.rpt
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      report_timing -delay_type max -max_paths 1 -nworst 1 -file {output_dir}/timing_detail.rpt
    }}
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def run_vivado_rtl_impl(output_dir: Path, top_func: str, impl: bool) -> dict[str, Any]:
    if impl:
        tcl_path = create_vivado_tcl_for_rtl(top_func, output_dir)
        vivado_settings = "/tools/Xilinx/2025.1/Vivado/settings64.sh"
        cmd = f"source {vivado_settings} && cd {output_dir} && vivado -mode batch -source {tcl_path} > vivado.log 2>&1"
        proc = subprocess.run(["bash", "-lc", cmd], capture_output=True, text=True)
        if proc.returncode != 0:
            print(f"[WARN] Vivado impl failed for {output_dir.name}. Check {output_dir / 'vivado.log'}")
    return parse_reports(output_dir, top_func, output_dir.name, run_impl=impl)


def stage_variant(
    target: FlopocoTarget,
    base_rtl_dir: Path,
    variants_root: Path,
    variant_soln: str,
    wrapper_text: str,
) -> tuple[Path, Path]:
    variant_dir = variants_root / variant_soln
    rtl_out = variant_dir / "verilog_out"
    if variant_dir.exists():
        shutil.rmtree(variant_dir)
    rtl_out.mkdir(parents=True, exist_ok=True)

    copied = 0
    for ext in ("*.vhd", "*.vhdl", "*.v", "*.sv"):
        for src in base_rtl_dir.glob(ext):
            shutil.copy2(src, rtl_out / src.name)
            copied += 1
    if copied == 0:
        raise FileNotFoundError(f"No RTL files found in base dir: {base_rtl_dir}")

    wrapper_path = rtl_out / target.wrapper_filename
    wrapper_with_header = f"-- AUTO-GENERATED FLOPOCO WRAPPER variant={variant_soln}\n" + wrapper_text
    wrapper_path.write_text(wrapper_with_header)
    return variant_dir, wrapper_path


def run_cocotb_accuracy(
    repo_root: Path,
    rtl_root: Path,
    variant_soln: str,
    target: FlopocoTarget,
    timeout_seconds: int,
    log_path: Path,
    rel_error_pct: float,
    cocotb_mode: str,
) -> dict[str, Any]:
    acc_root = repo_root / "accuracy_tests"
    rtl_dir = (rtl_root / variant_soln / "verilog_out").resolve()
    wrapper_path = rtl_dir / target.wrapper_filename
    if not rtl_dir.exists():
        raise FileNotFoundError(f"Variant RTL dir not found for cocotb: {rtl_dir}")
    if not wrapper_path.exists():
        raise FileNotFoundError(f"Variant wrapper VHDL not found for cocotb: {wrapper_path}")

    env = os.environ.copy()
    env["SIM"] = "ghdl"
    env["TOPLEVEL_LANG"] = "vhdl"
    env["GHDL_ARGS"] = "-fsynopsys -fexplicit"
    env["GHDL_ELABORATE_ARGS"] = "-fsynopsys -fexplicit"
    env[target.variant_env] = "flopoco"
    env["COCOTB_RESULTS_FILE"] = str((log_path.parent / f"{variant_soln}_results.xml").resolve())

    if target.is_mul:
        env["FP32_MUL_REL_ERR_PCT"] = f"{rel_error_pct}"
        env["FP32_MUL_MODE"] = cocotb_mode

    cmd = [
        "make",
        f"HLS_BASE={rtl_root}",
        f"HLS_SOLN={variant_soln}",
        f"TOPLEVEL={target.top_func}",
        f"MODULE={target.cocotb_module}",
        f"SIM_BUILD={(acc_root / 'sim_build' / f'{target.top_func}_{variant_soln}').resolve()}",
        "TOPLEVEL_LANG=vhdl",
    ]

    try:
        proc = subprocess.run(
            cmd,
            cwd=acc_root,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_seconds if timeout_seconds > 0 else None,
        )
        output = (proc.stdout or "") + ("\n" + proc.stderr if proc.stderr else "")
        log_path.write_text(output)
        metrics = parse_cocotb_metrics(output, target)
        metrics["cocotb_passed"] = proc.returncode == 0
        metrics["cocotb_returncode"] = proc.returncode
        return metrics
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + ("\n" + exc.stderr if exc.stderr else "")
        log_path.write_text(output + "\n[TIMEOUT]\n")
        metrics = parse_cocotb_metrics(output, target)
        metrics["cocotb_passed"] = False
        metrics["cocotb_returncode"] = -9
        return metrics


def run_one_target(args: argparse.Namespace, target: FlopocoTarget) -> None:
    src_dir = Path(__file__).resolve().parent
    repo_root = src_dir.parent.parent
    base_rtl_dir = (
        Path(args.base_rtl).resolve()
        if args.base_rtl
        else (repo_root / "results" / "FLOPOCO" / target.base_solution / "verilog_out").resolve()
    )
    if not base_rtl_dir.exists():
        raise FileNotFoundError(f"Base FLOPOCO RTL dir not found: {base_rtl_dir}")

    mode_tag = (
        re.sub(r"[^a-zA-Z0-9_.-]+", "_", str(args.cocotb_mode).strip().lower())
        if target.is_mul
        else "default"
    )
    out_root = (
        Path(args.output_dir).resolve()
        if args.output_dir
        else (repo_root / "results" / "sweeps" / f"flopoco_bitvector_{target.key}").resolve()
    )
    variants_root = out_root / "rtl_variants"
    logs_dir = out_root / "accuracy_logs"
    variants_root.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    mant_spec = args.mant_bits if args.mant_bits else "24:1:1"
    mant_bits_list = parse_mant_bits(mant_spec)
    candidates = mant_bits_list

    print(f"[INFO] Target: {target.key} ({target.dtype} {target.op})")
    print(f"[INFO] Base RTL: {base_rtl_dir}")
    if args.exp_bits:
        print("[INFO] Ignoring --exp-bits in mantissa-only mode.")
    pair_labels = ", ".join(f"{m}x{m}" for m in candidates)
    print(f"[INFO] Candidate mantissa pairs: {pair_labels}")
    print(f"[INFO] Search mode: {args.search}")
    if args.search == "optuna" and not args.impl:
        raise ValueError("Optuna multi-objective requires area metrics; use --impl.")

    rows: list[dict[str, Any]] = []

    def evaluate_candidate(mant_bits: int, eval_label: str = "") -> dict[str, Any]:
        variant_soln = f"{target.base_solution}_m{mant_bits}"
        wrapper_text = render_wrapper(target, mant_bits)
        variant_dir, wrapper_path = stage_variant(
            target=target,
            base_rtl_dir=base_rtl_dir,
            variants_root=variants_root,
            variant_soln=variant_soln,
            wrapper_text=wrapper_text,
        )
        prefix = "[EVAL]" if not eval_label else f"[EVAL:{eval_label}]"
        variant_rtl_dir = variant_dir / "verilog_out"
        print(
            f"{prefix} mantissa_bits={mant_bits} "
            f"rtl_dir={variant_rtl_dir} wrapper={wrapper_path}"
        )

        hw = run_vivado_rtl_impl(variant_dir, top_func=target.top_func, impl=args.impl)
        cocotb_log = logs_dir / f"{variant_soln}_{mode_tag}.log"
        acc = run_cocotb_accuracy(
            repo_root=repo_root,
            rtl_root=variants_root,
            variant_soln=variant_soln,
            target=target,
            timeout_seconds=args.cocotb_timeout,
            log_path=cocotb_log,
            rel_error_pct=float(args.rel_error_pct),
            cocotb_mode=str(args.cocotb_mode),
        )

        print(
            f"[ACC] exact={acc.get('accuracy_exact_match', -1.0):.6f} "
            f"within={acc.get('within_rel_pct', -1.0):.6f} "
            f"ulp_p99={acc.get('ulp_p99', -1)} pass={acc.get('cocotb_passed')} "
            f"log={cocotb_log}"
        )

        row: dict[str, Any] = {
            "search_mode": args.search,
            "target": target.key,
            "op": target.op,
            "dtype": target.dtype,
            "variant_solution": variant_soln,
            "variant_wrapper_vhdl": str(wrapper_path),
            "mantissa_bits": mant_bits,
            "exponent_bits": FULL_FP32_EXP_BITS,
            "accuracy_source": acc.get("accuracy_source"),
            "cocotb_mode": args.cocotb_mode if target.is_mul else "",
            "exact_matches": acc.get("exact_matches", -1),
            "total_cases": acc.get("total_cases", -1),
            "accuracy_exact_match": acc.get("accuracy_exact_match", -1.0),
            "within_rel_pct": acc.get("within_rel_pct", -1.0),
            "within_rel_threshold_pct": acc.get("within_rel_threshold_pct", -1.0),
            "within_5pct_rel": acc.get("within_5pct_rel", -1.0),
            "ulp_avg": acc.get("ulp_avg", -1.0),
            "ulp_p99": acc.get("ulp_p99", -1),
            "ulp_max": acc.get("ulp_max", -1),
            "abs_err_avg": acc.get("abs_err_avg", -1.0),
            "abs_err_p99": acc.get("abs_err_p99", -1.0),
            "abs_err_max": acc.get("abs_err_max", -1.0),
            "cocotb_passed": acc.get("cocotb_passed"),
            "cocotb_returncode": acc.get("cocotb_returncode"),
            "accuracy_log": str(cocotb_log),
            "LUTs": hw.get("LUTs", -1),
            "FFs": hw.get("FFs", -1),
            "DSPs": hw.get("DSPs", -1),
            "BRAMs": hw.get("BRAMs", -1),
            "Cycles": hw.get("Cycles", -1),
            "Fmax_MHz": hw.get("Fmax_MHz", -1),
            "Latency_ns": hw.get("Latency_ns", -1),
        }
        row["area_score"] = compute_area_score(
            row,
            args.area_lut_weight,
            args.area_ff_weight,
            args.area_dsp_weight,
            args.area_bram_weight,
        )
        print(
            f"[AREA] LUTs={row['LUTs']} FFs={row['FFs']} DSPs={row['DSPs']} BRAMs={row['BRAMs']} "
            f"area_score={row['area_score']:.3f}"
        )
        print(f"[PERF] Cycles={row['Cycles']} Fmax_MHz={row['Fmax_MHz']} Latency_ns={row['Latency_ns']}")
        rows.append(row)
        return row

    if args.search == "sweep":
        for m in candidates:
            evaluate_candidate(m)
    else:
        try:
            import optuna
        except ImportError as exc:
            raise RuntimeError(
                "Optuna is not installed. Install it (pip install optuna) or use --search sweep."
            ) from exc

        if args.optuna_sampler == "nsga2":
            sampler = optuna.samplers.NSGAIISampler(seed=args.optuna_seed)
        elif args.optuna_sampler == "tpe":
            sampler = optuna.samplers.TPESampler(seed=args.optuna_seed)
        else:
            sampler = optuna.samplers.RandomSampler(seed=args.optuna_seed)

        study = optuna.create_study(
            # accuracy max, area min, cycles min, Fmax max
            directions=["maximize", "minimize", "minimize", "maximize"],
            sampler=sampler,
            study_name=args.optuna_study_name,
            storage=args.optuna_storage if args.optuna_storage else None,
            load_if_exists=True,
        )
        labels = [str(m) for m in candidates]
        cache: dict[int, dict[str, Any]] = {}

        def objective(trial):
            label = str(trial.suggest_categorical("mantissa_bits", labels))
            m = int(label)
            key = m
            row = cache.get(key)
            if row is None:
                row = evaluate_candidate(m, eval_label=f"trial-{trial.number}")
                cache[key] = row

            acc, acc_metric = pick_optuna_accuracy_objective(row, target)
            area = row["area_score"]
            cycles = row.get("Cycles", -1)
            fmax = row.get("Fmax_MHz", -1)
            cycles_obj = float(cycles) if isinstance(cycles, (int, float)) and float(cycles) >= 0 else 1e15
            fmax_obj = float(fmax) if isinstance(fmax, (int, float)) and float(fmax) > 0 else -1e15

            trial.set_user_attr("variant_solution", row["variant_solution"])
            trial.set_user_attr("mantissa_bits", row["mantissa_bits"])
            trial.set_user_attr("exponent_bits", row["exponent_bits"])
            trial.set_user_attr("LUTs", row["LUTs"])
            trial.set_user_attr("DSPs", row["DSPs"])
            trial.set_user_attr("Cycles", row["Cycles"])
            trial.set_user_attr("Fmax_MHz", row["Fmax_MHz"])
            trial.set_user_attr("accuracy_metric", acc_metric)
            return float(acc), float(area), float(cycles_obj), float(fmax_obj)

        study.optimize(objective, n_trials=max(1, int(args.optuna_trials)))

    if not rows:
        raise RuntimeError("No variants were evaluated.")

    summary_csv = out_root / "summary.csv"
    summary_json = out_root / "summary.json"
    with open(summary_csv, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    summary_json.write_text(json.dumps(rows, indent=2))
    print(f"[INFO] Wrote summary: {summary_csv}")
    print(f"[INFO] Wrote summary: {summary_json}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Bitvector truncation sweep/Optuna search for off-the-shelf FLOPOCO FP32 add/mul "
            "by rewriting only the wrapper VHDL input packing (mantissa-only; exponent fixed at 8)."
        )
    )
    parser.add_argument("--target", choices=list(TARGETS.keys()), required=False)
    parser.add_argument("--all-targets", action="store_true", help="Run both fp32_add and fp32_mul.")
    parser.add_argument("--base-rtl", default="", help="Optional explicit base FLOPOCO verilog_out dir.")
    parser.add_argument("--mant-bits", default="", help="Mantissa bit candidates: N or START:STOP[:STEP].")
    parser.add_argument(
        "--exp-bits",
        default="",
        help="Deprecated for FP32 mantissa-only mode; ignored (exponent fixed at 8).",
    )
    parser.add_argument("--cocotb-timeout", type=int, default=0, help="Per-variant cocotb timeout seconds.")
    parser.add_argument("--rel-error-pct", type=float, default=5.0, help="FP32 mul relative-error threshold (%%).")
    parser.add_argument(
        "--cocotb-mode",
        default="bits",
        choices=["bits", "normal_full", "wide", "small"],
        help="FP32 multiplier operand sampler mode in cocotb tests.",
    )
    parser.add_argument(
        "--impl",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Run Vivado implementation per variant (default: enabled).",
    )
    parser.add_argument("--search", default="sweep", choices=["sweep", "optuna"], help="Exhaustive sweep or Optuna.")
    parser.add_argument("--optuna-trials", type=int, default=24, help="Number of Optuna trials.")
    parser.add_argument("--optuna-sampler", default="nsga2", choices=["nsga2", "tpe", "random"], help="Optuna sampler.")
    parser.add_argument("--optuna-seed", type=int, default=7, help="Seed for Optuna sampler.")
    parser.add_argument("--optuna-study-name", default="flopoco_bitvector_multiobj", help="Optuna study name.")
    parser.add_argument("--optuna-storage", default="", help="Optional Optuna storage URL.")
    parser.add_argument("--area-lut-weight", type=float, default=1.0, help="Area objective LUT weight.")
    parser.add_argument("--area-ff-weight", type=float, default=0.1, help="Area objective FF weight.")
    parser.add_argument("--area-dsp-weight", type=float, default=200.0, help="Area objective DSP weight.")
    parser.add_argument("--area-bram-weight", type=float, default=1000.0, help="Area objective BRAM weight.")
    parser.add_argument("--output-dir", default="", help="Output directory root for this run.")
    args = parser.parse_args()

    if not args.all_targets and not args.target:
        parser.error("Either --target or --all-targets must be provided.")
    if args.all_targets and args.base_rtl:
        parser.error("--base-rtl is only supported with a single --target run.")

    if args.all_targets:
        repo_root = Path(__file__).resolve().parent.parent.parent
        combined_rows: list[dict[str, Any]] = []
        for key in ("fp32_add", "fp32_mul"):
            cmd = [sys.executable, "-m", "src.Experiments.flopoco_bitvector_sweep", "--target", key]
            if args.mant_bits:
                cmd += ["--mant-bits", str(args.mant_bits)]
            if args.cocotb_timeout:
                cmd += ["--cocotb-timeout", str(args.cocotb_timeout)]
            if key == "fp32_mul":
                cmd += ["--rel-error-pct", str(args.rel_error_pct), "--cocotb-mode", str(args.cocotb_mode)]
            cmd += ["--search", str(args.search)]
            cmd += ["--optuna-trials", str(args.optuna_trials)]
            cmd += ["--optuna-sampler", str(args.optuna_sampler)]
            cmd += ["--optuna-seed", str(args.optuna_seed)]
            cmd += ["--optuna-study-name", f"{args.optuna_study_name}_{key}"]
            if args.optuna_storage:
                storage = str(args.optuna_storage)
                if storage.startswith("sqlite:///"):
                    storage = storage[:-3] + f"_{key}.db"
                cmd += ["--optuna-storage", storage]
            cmd += ["--impl" if args.impl else "--no-impl"]
            cmd += ["--area-lut-weight", str(args.area_lut_weight)]
            cmd += ["--area-ff-weight", str(args.area_ff_weight)]
            cmd += ["--area-dsp-weight", str(args.area_dsp_weight)]
            cmd += ["--area-bram-weight", str(args.area_bram_weight)]
            child_out = Path(args.output_dir).resolve() / key if args.output_dir else (
                repo_root / "results" / "sweeps" / f"flopoco_bitvector_{key}"
            )
            cmd += ["--output-dir", str(child_out)]

            print(f"[ALL-TARGETS] Running: {' '.join(cmd)}")
            proc = subprocess.run(cmd, cwd=repo_root)
            if proc.returncode != 0:
                raise RuntimeError(f"--all-targets failed for {key} (rc={proc.returncode}).")

            summary_csv = child_out / "summary.csv"
            if summary_csv.exists():
                with open(summary_csv, newline="") as f:
                    for row in csv.DictReader(f):
                        row["run_target"] = key
                        combined_rows.append(row)

        out_root = Path(args.output_dir).resolve() if args.output_dir else (
            repo_root / "results" / "sweeps" / "flopoco_bitvector_all"
        )
        out_root.mkdir(parents=True, exist_ok=True)
        if combined_rows:
            combined_csv = out_root / "summary_all_targets.csv"
            combined_json = out_root / "summary_all_targets.json"
            with open(combined_csv, "w", newline="") as f:
                writer = csv.DictWriter(f, fieldnames=list(combined_rows[0].keys()))
                writer.writeheader()
                writer.writerows(combined_rows)
            combined_json.write_text(json.dumps(combined_rows, indent=2))
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_csv}")
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_json}")
        return

    run_one_target(args, TARGETS[args.target])


if __name__ == "__main__":
    main()
