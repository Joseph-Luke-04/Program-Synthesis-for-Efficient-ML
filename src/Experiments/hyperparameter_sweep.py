"""Hyperparameter sweep: find optimal (timeout, num_iterations) operating point.

Always runs a joint 2-D grid over timeout × num_iterations.  Hardware quality
(LUTs, Fmax, Latency_ns, ADP) and accuracy are always evaluated.

Two recommended invocations
─────────────────────────────
Coarse (preliminary — informs pipeline/bitvector sweep choices):
  python -m src.Experiments.hyperparameter_sweep \\
      --preset coarse \\
      --output-dir results/hyperparameter_sweep/coarse

  Grid: timeouts=[30,60,180] × iterations=[15,30]  →  6 pts × 8 benchmarks × 3 reps = 144 runs
  Note: t=30 is below the empirical safe floor for MXINT8 (t≥60); those points may have reduced solve rates.

Fine:
  python -m src.Experiments.hyperparameter_sweep \\
      --preset fine \\
      --output-dir results/hyperparameter_sweep/fine

  Grid: timeouts=[30,60,120,180,300] × iterations=[10,15,20,30]  →  20 pts × 8 benchmarks × 3 reps = 480 runs
  Note: t=30 is below the empirical safe floor for MXINT8 (t≥60); those points may have reduced solve rates.

Both grids can be overridden with explicit --timeouts / --iterations flags.

Recommendation rule (applied per benchmark)
────────────────────────────────────────────
1. Compute the Pareto-optimal set over four objectives:
     accuracy (within_rel_pct) ↑,  LUTs ↓,  Latency_ns ↓,  ADP (LUT·ns) ↓
2. Retain points within --accuracy-slack-pct-points (default 1 pp) of the
   best observed accuracy among Pareto-optimal points.
3. Select the minimum-ADP point from that set.
4. Break ties: latency_ns → LUTs → mean solver runtime.
"""

import argparse
import csv
import json
import os
import sys
import time
from dataclasses import dataclass
from itertools import product as cartesian
from pathlib import Path
from typing import Any

# Reuse benchmark definitions and helpers from the grammar study.
from src.Experiments.grammar_selection_study import (
    BENCHMARKS as _V2_BENCHMARKS,
    GrammarBenchmark,
    _run_and_tee,
)

# V1 benchmarks: same monolithic component as V2 but with the broader V1 grammar.
# template= forces the V1 grammar file; V2 benchmarks leave template="" so the
# synthesis target's default (which is the V2 template for *_v2 components) is used.
_V1_BENCHMARKS: tuple[GrammarBenchmark, ...] = (
    GrammarBenchmark(key="mxint8_add_v1", synth_target="mxint8_add", component="full_sum_v2",
                     v2_template="sygus_grammars/addition/MXINT8/mxint8_add_full_sum_v2_template.sl",
                     template="sygus_grammars/addition/MXINT8/mxint8_add_full_sum_v1_template.sl"),
    GrammarBenchmark(key="mxint8_mul_v1", synth_target="mxint8_mul", component="full_product_v2",
                     v2_template="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v2_template.sl",
                     template="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v1_template.sl"),
    GrammarBenchmark(key="fp32_add_v1", synth_target="fp32_add", component="full_sum_v2",
                     v2_template="sygus_grammars/addition/FP32/fp32_full_sum_v2_template.sl",
                     template="sygus_grammars/addition/FP32/fp32_full_sum_v1_template.sl"),
    GrammarBenchmark(key="fp32_mul_v1", synth_target="fp32_mul", component="full_product_v2",
                     v2_template="sygus_grammars/multiplication/FP32/fp32_full_prod_v2_template.sl",
                     template="sygus_grammars/multiplication/FP32/fp32_full_prod_v1_template.sl"),
)

# Subcomponent benchmarks (the decomposed pipeline approach).
_SUBCOMPONENT_BENCHMARKS: tuple[GrammarBenchmark, ...] = (
    GrammarBenchmark(key="mxint8_add_sub", synth_target="mxint8_add", component="full_sum",
                     v2_template="sygus_grammars/addition/MXINT8/mxint8_add_full_sum_v2_template.sl"),
    GrammarBenchmark(key="mxint8_mul_sub", synth_target="mxint8_mul", component="full_product",
                     v2_template="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v2_template.sl"),
    GrammarBenchmark(key="fp32_add_sub", synth_target="fp32_add", component="full_sum",
                     v2_template="sygus_grammars/addition/FP32/fp32_full_sum_v2_template.sl"),
    GrammarBenchmark(key="fp32_mul_sub", synth_target="fp32_mul", component="full_product",
                     v2_template="sygus_grammars/multiplication/FP32/fp32_full_prod_v2_template.sl"),
)

BENCHMARKS = _V1_BENCHMARKS + _V2_BENCHMARKS + _SUBCOMPONENT_BENCHMARKS


def _summary_float(value: Any) -> float | None:
    if isinstance(value, (int, float)):
        return float(value)
    return None


def _mean(values: list[float]) -> float | None:
    return sum(values) / len(values) if values else None


def _valid_nonneg(x: Any) -> bool:
    return isinstance(x, (int, float)) and float(x) >= 0


def _valid_pos(x: Any) -> bool:
    return isinstance(x, (int, float)) and float(x) > 0


@dataclass
class SweepPoint:
    timeout: int
    num_iterations: int


def _flatten_sweep_row(
    bench: GrammarBenchmark,
    point: SweepPoint,
    repetition: int,
    summary: dict[str, Any],
    driver_returncode: int,
    wall_seconds: float,
) -> dict[str, Any]:
    comp = summary.get("components", {}).get(bench.component, {})
    accuracy = summary.get("accuracy", {}) if isinstance(summary.get("accuracy"), dict) else {}

    hw = summary.get("hardware", {}) if isinstance(summary.get("hardware"), dict) else {}
    luts = hw.get("LUTs", -1)
    latency_ns = hw.get("Latency_ns", -1)
    adp = (
        float(luts) * float(latency_ns)
        if _valid_pos(luts) and _valid_pos(latency_ns)
        else -1.0
    )

    return {
        "benchmark": bench.key,
        "synth_target": bench.synth_target,
        "component": bench.component,
        "timeout": point.timeout,
        "num_iterations": point.num_iterations,
        "repetition": repetition,
        "driver_returncode": driver_returncode,
        "run_status": summary.get("status", "unknown"),
        "component_solve_status": comp.get("solve_status", "unknown"),
        "solution_found": bool(comp.get("solution_found", False)),
        "accepted_constraints": comp.get("accepted_constraints", -1),
        "total_constraints": comp.get("total_constraints", -1),
        "solver_attempts": comp.get("solver_attempts", -1),
        "solver_runtime_seconds_total": comp.get("solver_runtime_seconds_total", -1.0),
        "solver_runtime_seconds_max": comp.get("solver_runtime_seconds_max", -1.0),
        "enum_count_primary_total": comp.get("enum_count_primary_total"),
        "enum_count_primary_last": comp.get("enum_count_primary_last"),
        "wall_seconds": wall_seconds,
        "random_seed": summary.get("config", {}).get("random_seed", -1),
        # Hardware metrics from HLS synthesis (estimated, no implementation needed)
        "luts": luts,
        "ffs": hw.get("FFs", -1),
        "dsps": hw.get("DSPs", -1),
        "fmax_mhz": hw.get("Fmax_MHz", -1),
        "latency_ns": latency_ns,
        "adp_lut_ns": adp,
        # Accuracy metrics from cocotb (populated when --run-accuracy is set)
        "accuracy_exact_match": accuracy.get("accuracy_exact_match", -1.0),
        "within_rel_pct": accuracy.get("within_rel_pct", -1.0),
        "abs_err_avg": accuracy.get("abs_err_avg", -1.0),
        "abs_err_max": accuracy.get("abs_err_max", -1.0),
        "summary_path": summary.get("_summary_path", ""),
        "log_path": summary.get("_log_path", ""),
    }


def _build_aggregate(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Group by (benchmark, timeout, num_iterations) and compute per-point means."""
    grouped: dict[tuple[str, int, int], list[dict[str, Any]]] = {}
    for r in rows:
        key = (r["benchmark"], r["timeout"], r["num_iterations"])
        grouped.setdefault(key, []).append(r)

    out: list[dict[str, Any]] = []
    for (benchmark, timeout, num_iterations), items in sorted(grouped.items()):
        runtimes = [x for x in (_summary_float(r["solver_runtime_seconds_total"]) for r in items) if x is not None and x >= 0]
        walls = [r["wall_seconds"] for r in items if r["wall_seconds"] >= 0]
        acc = [float(r["accuracy_exact_match"]) for r in items if _valid_nonneg(r.get("accuracy_exact_match"))]
        within = [float(r["within_rel_pct"]) for r in items if _valid_nonneg(r.get("within_rel_pct"))]
        luts = [float(r["luts"]) for r in items if _valid_pos(r.get("luts"))]
        fmax = [float(r["fmax_mhz"]) for r in items if _valid_pos(r.get("fmax_mhz"))]
        latency = [float(r["latency_ns"]) for r in items if _valid_pos(r.get("latency_ns"))]
        # ADP is averaged from per-run values, not recomputed from means.
        adp = [float(r["adp_lut_ns"]) for r in items if _valid_pos(r.get("adp_lut_ns"))]

        out.append({
            "benchmark": benchmark,
            "timeout": timeout,
            "num_iterations": num_iterations,
            "runs": len(items),
            "solve_successes": sum(1 for r in items if r.get("solution_found")),
            "solve_rate": sum(1 for r in items if r.get("solution_found")) / float(len(items)),
            "mean_solver_runtime_s": _mean(runtimes),
            "mean_wall_seconds": _mean(walls),
            "mean_accepted_constraints": _mean([float(r["accepted_constraints"]) for r in items if r["accepted_constraints"] >= 0]),
            "mean_accuracy_exact_match": _mean(acc),
            "mean_within_rel_pct": _mean(within),
            "mean_luts": _mean(luts),
            "mean_fmax_mhz": _mean(fmax),
            "mean_latency_ns": _mean(latency),
            "mean_adp_lut_ns": _mean(adp),
        })
    return out


def _annotate_normalised_metrics(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """
    Add per-benchmark normalised overhead metrics.

    For cost metrics (area, latency, ADP):
      - *_norm_to_best  = value / best_value   (1.0 = best, >1 = overhead)
      - *_overhead_pct  = 100 * (value - best) / best

    For accuracy (higher is better):
      - accuracy_retention     = value / best_accuracy
      - accuracy_loss_pct      = 100 * (best - value) / best

    Normalisation is per-benchmark so benchmarks with very different absolute
    scales remain comparable. The reference ("best") is the observed optimum
    within the sweep for that benchmark.
    """
    by_bench: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        by_bench.setdefault(row["benchmark"], []).append(row)

    out: list[dict[str, Any]] = []
    for benchmark, items in by_bench.items():
        best_acc = max(
            (float(r["mean_within_rel_pct"]) for r in items if _valid_nonneg(r.get("mean_within_rel_pct"))),
            default=None,
        )
        best_area = min(
            (float(r["mean_luts"]) for r in items if _valid_pos(r.get("mean_luts"))),
            default=None,
        )
        best_lat = min(
            (float(r["mean_latency_ns"]) for r in items if _valid_pos(r.get("mean_latency_ns"))),
            default=None,
        )
        best_adp = min(
            (float(r["mean_adp_lut_ns"]) for r in items if _valid_pos(r.get("mean_adp_lut_ns"))),
            default=None,
        )

        for r in items:
            rr = dict(r)

            acc = float(r["mean_within_rel_pct"]) if _valid_nonneg(r.get("mean_within_rel_pct")) else None
            area = float(r["mean_luts"]) if _valid_pos(r.get("mean_luts")) else None
            lat = float(r["mean_latency_ns"]) if _valid_pos(r.get("mean_latency_ns")) else None
            adp = float(r["mean_adp_lut_ns"]) if _valid_pos(r.get("mean_adp_lut_ns")) else None

            # Store per-benchmark bests for reference
            rr["accuracy_best_pct"] = best_acc
            rr["area_best_luts"] = best_area
            rr["latency_best_ns"] = best_lat
            rr["adp_best_lut_ns_ref"] = best_adp

            # Accuracy (higher is better)
            rr["accuracy_retention"] = (acc / best_acc) if (acc is not None and best_acc) else None
            rr["accuracy_loss_pct"] = (100.0 * (best_acc - acc) / best_acc) if (acc is not None and best_acc) else None

            # Cost metrics (lower is better — norm_to_best >= 1.0, overhead_pct >= 0)
            rr["area_norm_to_best"] = (area / best_area) if (area is not None and best_area) else None
            rr["latency_norm_to_best"] = (lat / best_lat) if (lat is not None and best_lat) else None
            rr["adp_norm_to_best"] = (adp / best_adp) if (adp is not None and best_adp) else None

            rr["area_overhead_pct"] = (100.0 * (area - best_area) / best_area) if (area is not None and best_area) else None
            rr["latency_overhead_pct"] = (100.0 * (lat - best_lat) / best_lat) if (lat is not None and best_lat) else None
            rr["adp_overhead_pct"] = (100.0 * (adp - best_adp) / best_adp) if (adp is not None and best_adp) else None

            out.append(rr)

    return out


def _dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
    """a dominates b: no worse on all four objectives, strictly better on at least one."""
    no_worse = (
        float(a["mean_within_rel_pct"]) >= float(b["mean_within_rel_pct"]) and
        float(a["mean_luts"]) <= float(b["mean_luts"]) and
        float(a["mean_latency_ns"]) <= float(b["mean_latency_ns"]) and
        float(a["mean_adp_lut_ns"]) <= float(b["mean_adp_lut_ns"])
    )
    strictly_better = (
        float(a["mean_within_rel_pct"]) > float(b["mean_within_rel_pct"]) or
        float(a["mean_luts"]) < float(b["mean_luts"]) or
        float(a["mean_latency_ns"]) < float(b["mean_latency_ns"]) or
        float(a["mean_adp_lut_ns"]) < float(b["mean_adp_lut_ns"])
    )
    return no_worse and strictly_better


def _hw_quality_exclusion_reason(r: dict[str, Any]) -> str:
    """Return a short string explaining why a row is excluded from Pareto/selection, or '' if eligible."""
    missing = []
    if not _valid_nonneg(r.get("mean_within_rel_pct")):
        missing.append("accuracy")
    if not _valid_pos(r.get("mean_luts")):
        missing.append("luts")
    if not _valid_pos(r.get("mean_latency_ns")):
        missing.append("latency")
    if not _valid_pos(r.get("mean_adp_lut_ns")):
        missing.append("adp")
    return "missing_" + "+".join(missing) if missing else ""


def _is_hw_quality_candidate(r: dict[str, Any]) -> bool:
    """Row has all four metrics needed for Pareto/selection logic."""
    return _hw_quality_exclusion_reason(r) == ""


def _mark_pareto_and_select(
    rows: list[dict[str, Any]],
    accuracy_slack_pct_points: float = 1.0,
) -> list[dict[str, Any]]:
    """
    Per benchmark:
      1. Mark Pareto-optimal points (non-dominated over accuracy↑, area↓, latency↓, ADP↓).
      2. Among Pareto-optimal points, keep those within `accuracy_slack_pct_points` of best.
      3. Select the one with minimum ADP; break ties by latency, then area, then solver runtime.

    This avoids weighted aggregation entirely — each metric is preserved separately and
    the selection rule is a lexicographic priority over clearly ordered objectives.
    """
    by_bench: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        row.setdefault("is_pareto", False)
        row.setdefault("is_recommended", False)
        row.setdefault("selection_reason", "")
        excl = _hw_quality_exclusion_reason(row)
        row["hw_quality_candidate"] = excl == ""
        row["hw_quality_exclusion_reason"] = excl
        by_bench.setdefault(row["benchmark"], []).append(row)

    for benchmark, items in by_bench.items():
        candidates = [r for r in items if _is_hw_quality_candidate(r)]
        if not candidates:
            continue

        # Pareto front
        pareto: list[dict[str, Any]] = []
        for r in candidates:
            if not any(_dominates(other, r) for other in candidates if other is not r):
                r["is_pareto"] = True
                pareto.append(r)

        if not pareto:
            continue

        best_acc = max(float(r["mean_within_rel_pct"]) for r in pareto)
        near_best = [r for r in pareto if float(r["mean_within_rel_pct"]) >= best_acc - accuracy_slack_pct_points]
        pool = near_best if near_best else pareto

        chosen = min(
            pool,
            key=lambda r: (
                float(r["mean_adp_lut_ns"]),
                float(r["mean_latency_ns"]),
                float(r["mean_luts"]),
                float(r["mean_solver_runtime_s"]) if _valid_nonneg(r.get("mean_solver_runtime_s")) else float("inf"),
            ),
        )
        chosen["is_recommended"] = True
        chosen["selection_reason"] = (
            f"Pareto-optimal; within {accuracy_slack_pct_points:.2f} ppt of best accuracy "
            f"({best_acc:.4f}); minimum ADP among remaining candidates"
        )

    return rows


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    keys: list[str] = []
    seen: set[str] = set()
    for row in rows:
        for key in row.keys():
            if key not in seen:
                seen.add(key)
                keys.append(key)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)


def run_sweep_point(
    repo_root: Path,
    bench: GrammarBenchmark,
    point: SweepPoint,
    repetition: int,
    out_dir: Path,
    args: argparse.Namespace,
    run_index: int,
    total_runs: int,
) -> tuple[dict[str, Any], int, float]:
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    tag = f"{bench.key}_t{point.timeout}_i{point.num_iterations}_r{repetition:02d}"
    summary_path = raw_dir / f"{tag}.json"
    log_path = raw_dir / f"{tag}.log"
    solution_stem = f"hpsweep_{tag}"
    run_seed = args.seed + repetition - 1 + (args.benchmark_order[bench.key] * 1000)

    env = os.environ.copy()
    env.update({
        "SYNTH_TARGET": bench.synth_target,
        "SYNTH_COMPONENT": bench.component,
        "SYNTH_SOLVER_TIMEOUT": str(point.timeout),
        "SYNTH_NUM_ITERATIONS": str(point.num_iterations),
        "SYNTH_RUN_IMPL": "1",
        "SYNTH_RUN_ACCURACY": "1",
        "SYNTH_ENABLE_DIRECTED_IO": "1" if args.directed_io else "0",
        "SYNTH_ENABLE_SYGUS_DUMP": "0",
        "SYNTH_ENABLE_SYGUS_FAST_ENUM": "0",
        "SYNTH_ENABLE_SYGUS_PBE": "1",
        "SYNTH_ENABLE_SYGUS_SYM_BREAK_PBE": "1",
        "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "1" if args.mxint8_auto_relax else "0",
        "SYNTH_MXINT8_RESET_BITS_PER_SAMPLE": "1" if args.mxint8_auto_relax else "0",
        "SYNTH_MXINT8_RELAX_ON_TIMEOUT": "1" if args.mxint8_auto_relax else "0",
        "SYNTH_MXINT8_RELAX_ON_INFEASIBLE": "1" if args.mxint8_auto_relax else "0",
        "SYNTH_MXINT8_RELAX_ON_FAIL": "1" if args.mxint8_auto_relax else "0",
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_OUTPUT_MATCH_MSB_BITS": str(args.fp32_output_match_msb_bits),
        "SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS": str(args.fp32_min_output_match_msb_bits),
        "SYNTH_FP32_OUTPUT_MATCH_STEP": str(args.fp32_output_match_step),
        "SYNTH_FP32_RELAX_SCHEDULE": args.fp32_relax_schedule,
        "SYNTH_FP32_STAGE_MANTISSA_BITS": str(args.fp32_stage_mantissa_bits),
        "SYNTH_FP32_RESET_MSB_PER_SAMPLE": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_RELAX_ON_TIMEOUT": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_TIMEOUT_RETRY_ONCE": "0",
        "SYNTH_FP32_RELAX_ON_INFEASIBLE": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_RELAX_ON_FAIL": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_MUL_MODE": args.fp32_mul_mode,
        "SYNTH_SUMMARY_PATH": str(summary_path),
        "SYNTH_SOLUTION_STEM": solution_stem,
        "SYNTH_RANDOM_SEED": str(run_seed),
        "PYTHONHASHSEED": str(run_seed),
    })

    # Per-benchmark template takes priority over the global --template-override flag.
    # Subcomponent benchmarks leave bench.template="" so no override is set.
    effective_template = bench.template or args.template_override
    if effective_template:
        env["SYNTH_TEMPLATE_OVERRIDE"] = effective_template

    cmd = [sys.executable, "-m", "src.synthesis_driver"]
    print(
        f"[RUN {run_index}/{total_runs}] benchmark={bench.key} "
        f"timeout={point.timeout} iterations={point.num_iterations} "
        f"repetition={repetition} seed={run_seed}"
    )
    start = time.time()
    proc = _run_and_tee(cmd, cwd=repo_root, env=env, log_path=log_path)
    wall = time.time() - start

    if not summary_path.exists():
        print(f"[RUN {run_index}/{total_runs} DONE] status=missing_summary elapsed={wall:.1f}s")
        return {
            "_summary_path": str(summary_path),
            "_log_path": str(log_path),
            "status": "missing_summary",
            "config": {"random_seed": run_seed},
        }, proc.returncode, wall

    summary = json.loads(summary_path.read_text())
    summary["_summary_path"] = str(summary_path)
    summary["_log_path"] = str(log_path)
    comp = summary.get("components", {}).get(bench.component, {})
    accepted = comp.get("accepted_constraints", "?")
    total = comp.get("total_constraints", "?")
    status = comp.get("solve_status", summary.get("status", "unknown"))
    print(
        f"[RUN {run_index}/{total_runs} DONE] status={status} "
        f"accepted={accepted}/{total} elapsed={wall:.1f}s"
    )
    return summary, proc.returncode, wall


_PRESETS: dict[str, dict[str, list[int]]] = {
    # Preliminary / fast: 3×2 = 6 grid points.
    # t=30 is below the empirical MXINT8 safe floor (60 s); may yield sparse results at that point.
    # 8 benchmarks × 6 pts × 3 reps = 144 runs.
    "coarse": {"timeouts": [30, 60, 180], "iterations": [15, 30]},
    # Dissertation quality: 4×4 = 16 grid points.
    # 8 benchmarks × 16 pts × 3 reps = 384 runs.
    "fine":   {"timeouts": [30, 60, 120, 180, 300], "iterations": [10, 15, 20, 30]},
}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Hyperparameter sweep (joint 2-D grid) for timeout × iteration counts.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--output-dir", default="results/hyperparameter_sweep")
    parser.add_argument("--benchmarks", nargs="+", default=[],
                        help="Benchmark keys to sweep. Defaults to all 8 (4 v2 + 4 subcomponent).")
    parser.add_argument("--repetitions", type=int, default=3,
                        help="Repetitions per grid point for statistical robustness.")
    parser.add_argument("--seed", type=int, default=42)

    # Grid — use preset or specify explicitly
    parser.add_argument("--preset", choices=list(_PRESETS), default=None,
                        help="Built-in grid preset. Overrides --timeouts and --iterations when set.")
    parser.add_argument("--timeouts", nargs="+", type=int,
                        default=[60, 120, 300],
                        help="Timeout values to sweep (seconds). Minimum recommended: 60.")
    parser.add_argument("--iterations", nargs="+", type=int,
                        default=[10, 20],
                        help="Iteration counts to sweep. Minimum recommended: 10.")

    # Template override
    parser.add_argument("--template-override", default="",
                        help="Force a specific grammar template for all runs.")

    # Multi-metric selection
    parser.add_argument("--accuracy-slack-pct-points", type=float, default=1.0,
                        help="Retain Pareto-optimal points within this many percentage points of "
                             "best accuracy, then choose minimum ADP.")

    # Synthesis settings
    parser.add_argument("--directed-io", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--mxint8-auto-relax", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("--fp32-auto-relax", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--fp32-output-match-msb-bits", type=int, default=32)
    parser.add_argument("--fp32-min-output-match-msb-bits", type=int, default=24)
    parser.add_argument("--fp32-output-match-step", type=int, default=1)
    parser.add_argument("--fp32-relax-schedule", default="staged", choices=["linear", "staged"])
    parser.add_argument("--fp32-stage-mantissa-bits", type=int, default=15)
    parser.add_argument("--fp32-mul-mode", default="default", choices=["default", "wide", "small"])

    args = parser.parse_args()

    # Apply preset (overrides explicit grid flags)
    if args.preset is not None:
        args.timeouts = _PRESETS[args.preset]["timeouts"]
        args.iterations = _PRESETS[args.preset]["iterations"]
        print(f"[INFO] Using preset '{args.preset}': timeouts={args.timeouts}, iterations={args.iterations}")

    # Accuracy is always on — the multi-metric analysis requires hardware quality data.
    args.run_accuracy = True

    if any(t <= 0 for t in args.timeouts):
        raise ValueError(f"All timeout values must be positive. Got: {args.timeouts}")
    if any(n <= 0 for n in args.iterations):
        raise ValueError(f"All iteration counts must be positive. Got: {args.iterations}")

    if min(args.timeouts) < 60:
        print(
            f"[WARNING] Minimum timeout {min(args.timeouts)} s is below 60 s. "
            "Short timeouts can degrade solution quality, particularly for MXINT8."
        )
    if min(args.iterations) < 10:
        print(
            f"[WARNING] Minimum iterations {min(args.iterations)} is below 10. "
            "mxint8_add_combined has been observed to fail reliably at i=5."
        )

    repo_root = Path(__file__).resolve().parents[2]
    output_dir = Path(args.output_dir).expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    # Select benchmarks
    selected = list(BENCHMARKS)
    if args.benchmarks:
        wanted = set(args.benchmarks)
        selected = [b for b in BENCHMARKS if b.key in wanted]
        missing = sorted(wanted - {b.key for b in selected})
        if missing:
            valid = ", ".join(b.key for b in BENCHMARKS)
            raise ValueError(f"Unknown benchmark(s): {', '.join(missing)}. Valid: {valid}")
    args.benchmark_order = {b.key: i for i, b in enumerate(selected)}

    # Build joint grid — iterations are the inner loop per timeout
    grid = [SweepPoint(t, n) for t, n in cartesian(args.timeouts, args.iterations)]
    grid_by_timeout: list[list[SweepPoint]] = []
    for t in sorted(set(p.timeout for p in grid)):
        grid_by_timeout.append(sorted([p for p in grid if p.timeout == t], key=lambda p: p.num_iterations))

    total_runs_max = len(selected) * len(grid) * args.repetitions
    print(f"Sweep: {len(selected)} benchmarks × {len(grid)} grid points × {args.repetitions} reps = {total_runs_max} runs")
    print(f"Grid:  timeouts={sorted(set(p.timeout for p in grid))}  iterations={sorted(set(p.num_iterations for p in grid))}")

    all_rows: list[dict[str, Any]] = []
    raw_jsonl = output_dir / "runs.jsonl"

    # ── Resume support: load only rows that belong to the current grid ──
    # Rows from a different grid (stale preset, different timeouts, etc.) are
    # silently ignored so they cannot pollute the aggregated summary.
    valid_points: set[tuple[str, int, int]] = {
        (b.key, p.timeout, p.num_iterations)
        for b in selected
        for p in grid
    }
    done_keys: set[tuple[str, int, int, int]] = set()
    if raw_jsonl.exists():
        stale_count = 0
        for line in raw_jsonl.read_text().strip().split("\n"):
            if not line:
                continue
            try:
                prev = json.loads(line)
                key3 = (prev["benchmark"], prev["timeout"], prev["num_iterations"])
                key4 = (prev["benchmark"], prev["timeout"], prev["num_iterations"], prev["repetition"])
                if key3 not in valid_points:
                    stale_count += 1
                    continue
                if key4 in done_keys:
                    continue  # deduplicate
                done_keys.add(key4)
                all_rows.append(prev)
            except (json.JSONDecodeError, KeyError):
                continue
        if done_keys:
            print(f"[RESUME] Found {len(done_keys)} completed runs in {raw_jsonl}, skipping them.")
        if stale_count:
            print(f"[RESUME] Ignored {stale_count} stale rows not in the current grid.")

    run_index = 0
    for bench in selected:
        for timeout_row in grid_by_timeout:
            for point in timeout_row:
                for rep in range(1, args.repetitions + 1):
                    run_index += 1
                    resume_key = (bench.key, point.timeout, point.num_iterations, rep)
                    if resume_key in done_keys:
                        print(
                            f"  [{run_index}/{total_runs_max}] "
                            f"benchmark={bench.key} t={point.timeout} "
                            f"i={point.num_iterations} rep={rep} — RESUMED (skipped)"
                        )
                        continue
                    summary, rc, wall = run_sweep_point(
                        repo_root, bench, point, rep, output_dir, args,
                        run_index, total_runs_max,
                    )
                    row = _flatten_sweep_row(bench, point, rep, summary, rc, wall)
                    all_rows.append(row)
                    with raw_jsonl.open("a") as f:
                        f.write(json.dumps(row, sort_keys=True) + "\n")

    _write_csv(output_dir / "runs.csv", all_rows)

    agg = _build_aggregate(all_rows)
    agg = _annotate_normalised_metrics(agg)
    agg = _mark_pareto_and_select(agg, accuracy_slack_pct_points=args.accuracy_slack_pct_points)

    _write_csv(output_dir / "summary.csv", agg)
    (output_dir / "summary.json").write_text(json.dumps(agg, indent=2, sort_keys=True) + "\n")

    pareto_rows = [r for r in agg if r.get("is_pareto")]
    recommended_rows = [r for r in agg if r.get("is_recommended")]
    _write_csv(output_dir / "pareto.csv", pareto_rows)
    _write_csv(output_dir / "recommended.csv", recommended_rows)

    print(f"\n[DONE] {len(all_rows)} runs written to {output_dir / 'runs.csv'}")
    print(f"[DONE] Aggregated summary:  {output_dir / 'summary.csv'}")
    print(f"[DONE] Pareto front:        {output_dir / 'pareto.csv'}  ({len(pareto_rows)} points)")
    print(f"[DONE] Recommended points:  {output_dir / 'recommended.csv'}  ({len(recommended_rows)} points)")

    # Print summary table: all points with key metrics and flags
    print(f"\n{'='*130}")
    print("SUMMARY  (per benchmark × sweep point  |  [R]=recommended  [P]=Pareto-optimal)")
    print(f"{'='*130}")
    for entry in agg:
        tag = "  [R]" if entry.get("is_recommended") else ("  [P]" if entry.get("is_pareto") else "     ")
        acc     = entry.get("mean_within_rel_pct")
        luts    = entry.get("mean_luts")
        lat     = entry.get("mean_latency_ns")
        adp     = entry.get("mean_adp_lut_ns")
        acc_l   = entry.get("accuracy_loss_pct")
        area_ov = entry.get("area_overhead_pct")
        lat_ov  = entry.get("latency_overhead_pct")
        adp_ov  = entry.get("adp_overhead_pct")
        print(
            f"{entry['benchmark']:22s}  t={entry['timeout']:4d}  i={entry['num_iterations']:3d}  "
            f"acc={acc if acc is not None else -1:6.3f}  "
            f"luts={luts if luts is not None else -1:8.1f}  "
            f"lat_ns={lat if lat is not None else -1:8.3f}  "
            f"adp={adp if adp is not None else -1:10.1f}  "
            f"acc_loss={acc_l if acc_l is not None else -1:6.2f}%  "
            f"area_ov={area_ov if area_ov is not None else -1:6.1f}%  "
            f"lat_ov={lat_ov if lat_ov is not None else -1:6.1f}%  "
            f"adp_ov={adp_ov if adp_ov is not None else -1:6.1f}%"
            f"{tag}"
        )


if __name__ == "__main__":
    main()
