"""Hyperparameter sweep: find optimal timeout and iteration counts.

Three modes:
  1. timeout-sweep  -- sweep timeout with fixed iterations
  2. iter-sweep     -- sweep iterations with fixed timeout
  3. joint          -- 2D grid over both

Uses the same synthesis driver subprocess mechanism as grammar_selection_study.py.
Runs all 4 combined benchmarks by default (mxint8_add, mxint8_mul, fp32_add, fp32_mul).
"""

import argparse
import csv
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from itertools import product as cartesian
from pathlib import Path
from typing import Any

# Reuse benchmark definitions and helpers from the grammar study.
from src.Experiments.grammar_selection_study import (
    BENCHMARKS as _COMBINED_BENCHMARKS,
    GrammarBenchmark,
    analyze_sygus_grammar,
    _run_and_tee,
)

# Subcomponent benchmarks (the decomposed pipeline approach).
_SUBCOMPONENT_BENCHMARKS: tuple[GrammarBenchmark, ...] = (
    # MXINT8 Addition subcomponents
    GrammarBenchmark(key="mxint8_add_sub", synth_target="mxint8_add", component="full_sum",
                     v2_template="sygus_grammars/addition/MXINT8/mxint8_add_full_sum_combined_template.sl"),
    # MXINT8 Multiplication subcomponents
    GrammarBenchmark(key="mxint8_mul_sub", synth_target="mxint8_mul", component="full_product",
                     v2_template="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_combined_template.sl"),
    # FP32 Addition subcomponents
    GrammarBenchmark(key="fp32_add_sub", synth_target="fp32_add", component="full_sum",
                     v2_template="sygus_grammars/addition/FP32/fp32_full_sum_combined_template.sl"),
    # FP32 Multiplication subcomponents
    GrammarBenchmark(key="fp32_mul_sub", synth_target="fp32_mul", component="full_product",
                     v2_template="sygus_grammars/multiplication/FP32/fp32_full_prod_combined_template.sl"),
)

BENCHMARKS = _COMBINED_BENCHMARKS + _SUBCOMPONENT_BENCHMARKS


def _summary_float(value: Any) -> float | None:
    if isinstance(value, (int, float)):
        return float(value)
    return None


def _mean(values: list[float]) -> float | None:
    return sum(values) / len(values) if values else None


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
        "accuracy_exact_match": accuracy.get("accuracy_exact_match", -1.0),
        "within_rel_pct": accuracy.get("within_rel_pct", -1.0),
        "abs_err_avg": accuracy.get("abs_err_avg", -1.0),
        "abs_err_max": accuracy.get("abs_err_max", -1.0),
        "summary_path": summary.get("_summary_path", ""),
        "log_path": summary.get("_log_path", ""),
    }


def _build_aggregate(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Group by (benchmark, timeout, num_iterations) and compute stats."""
    grouped: dict[tuple[str, int, int], list[dict[str, Any]]] = {}
    for r in rows:
        key = (r["benchmark"], r["timeout"], r["num_iterations"])
        grouped.setdefault(key, []).append(r)

    out: list[dict[str, Any]] = []
    for (benchmark, timeout, num_iterations), items in sorted(grouped.items()):
        runtimes = [x for x in (_summary_float(r["solver_runtime_seconds_total"]) for r in items) if x is not None and x >= 0]
        walls = [r["wall_seconds"] for r in items if r["wall_seconds"] >= 0]
        acc = [float(r["accuracy_exact_match"]) for r in items if isinstance(r.get("accuracy_exact_match"), (int, float)) and float(r["accuracy_exact_match"]) >= 0]

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
        })
    return out


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
        "SYNTH_RUN_IMPL": "0",
        "SYNTH_RUN_ACCURACY": "0",
        "SYNTH_ENABLE_DIRECTED_IO": "1" if args.directed_io else "0",
        "SYNTH_ENABLE_SYGUS_DUMP": "0",
        "SYNTH_ENABLE_SYGUS_FAST_ENUM": "0",
        "SYNTH_ENABLE_SYGUS_PBE": "1",
        "SYNTH_ENABLE_SYGUS_SYM_BREAK_PBE": "1",
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH": "1" if args.fp32_auto_relax else "0",
        "SYNTH_FP32_OUTPUT_MATCH_MSB_BITS": str(args.fp32_output_match_msb_bits),
        "SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS": str(args.fp32_min_output_match_msb_bits),
        "SYNTH_FP32_OUTPUT_MATCH_STEP": str(args.fp32_output_match_step),
        "SYNTH_FP32_RELAX_SCHEDULE": args.fp32_relax_schedule,
        "SYNTH_FP32_STAGE_MANTISSA_BITS": str(args.fp32_stage_mantissa_bits),
        "SYNTH_FP32_RESET_MSB_PER_SAMPLE": "1",
        "SYNTH_FP32_RELAX_ON_TIMEOUT": "1",
        "SYNTH_FP32_TIMEOUT_RETRY_ONCE": "0",
        "SYNTH_FP32_RELAX_ON_INFEASIBLE": "1",
        "SYNTH_FP32_RELAX_ON_FAIL": "1",
        "SYNTH_FP32_MUL_MODE": args.fp32_mul_mode,
        "SYNTH_SUMMARY_PATH": str(summary_path),
        "SYNTH_SOLUTION_STEM": solution_stem,
        "SYNTH_RANDOM_SEED": str(run_seed),
        "PYTHONHASHSEED": str(run_seed),
    })

    # Use template override if provided, otherwise let driver pick default
    if args.template_override:
        env["SYNTH_TEMPLATE_OVERRIDE"] = args.template_override

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


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Hyperparameter sweep for timeout and iteration counts."
    )
    parser.add_argument(
        "mode", choices=["timeout-sweep", "iter-sweep", "joint"],
        help="Sweep mode: timeout-sweep, iter-sweep, or joint (2D grid)."
    )
    parser.add_argument("--output-dir", default="results/hyperparameter_sweep")
    parser.add_argument("--benchmarks", nargs="+", default=[],
                        help="Benchmark keys to sweep. Defaults to all 8 (4 combined + 4 subcomponent).")
    parser.add_argument("--repetitions", type=int, default=3,
                        help="Repetitions per sweep point for statistical significance.")
    parser.add_argument("--seed", type=int, default=42)

    # Timeout sweep parameters
    parser.add_argument("--timeouts", nargs="+", type=int,
                        default=[10, 30, 60, 120, 180, 300],
                        help="Timeout values to sweep (seconds).")
    parser.add_argument("--fixed-iterations", type=int, default=30,
                        help="Fixed iteration count when sweeping timeout.")

    # Iteration sweep parameters
    parser.add_argument("--iterations", nargs="+", type=int,
                        default=[5, 10, 15, 20, 30, 50],
                        help="Iteration counts to sweep.")
    parser.add_argument("--fixed-timeout", type=int, default=120,
                        help="Fixed timeout when sweeping iterations.")

    # Template override (use default combined grammars unless specified)
    parser.add_argument("--template-override", default="",
                        help="Force a specific grammar template for all runs.")

    # Early stopping
    parser.add_argument("--patience", type=int, default=0,
                        help="Stop sweeping a dimension early if accepted constraints "
                             "don't improve for this many consecutive grid points. "
                             "0 = disabled (run full grid).")
    parser.add_argument("--early-stop-metric", default="accepted_constraints",
                        choices=["accepted_constraints", "solution_found"],
                        help="Metric to track for early stopping.")

    # Synthesis settings
    parser.add_argument("--directed-io", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--fp32-auto-relax", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--fp32-output-match-msb-bits", type=int, default=32)
    parser.add_argument("--fp32-min-output-match-msb-bits", type=int, default=24)
    parser.add_argument("--fp32-output-match-step", type=int, default=1)
    parser.add_argument("--fp32-relax-schedule", default="staged", choices=["linear", "staged"])
    parser.add_argument("--fp32-stage-mantissa-bits", type=int, default=15)
    parser.add_argument("--fp32-mul-mode", default="small", choices=["default", "wide", "small"])

    args = parser.parse_args()

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

    # Build sweep grid
    if args.mode == "timeout-sweep":
        grid = [SweepPoint(t, args.fixed_iterations) for t in args.timeouts]
    elif args.mode == "iter-sweep":
        grid = [SweepPoint(args.fixed_timeout, n) for n in args.iterations]
    else:  # joint
        grid = [SweepPoint(t, n) for t, n in cartesian(args.timeouts, args.iterations)]

    # For joint mode, restructure grid so iterations are the inner loop per timeout.
    # This lets early stopping cut iteration sweeps short per timeout level.
    if args.mode == "joint":
        grid_by_timeout: list[list[SweepPoint]] = []
        for t in sorted(set(p.timeout for p in grid)):
            row = sorted([p for p in grid if p.timeout == t], key=lambda p: p.num_iterations)
            grid_by_timeout.append(row)
    else:
        grid_by_timeout = [sorted(grid, key=lambda p: (p.timeout, p.num_iterations))]

    total_runs_max = len(selected) * len(grid) * args.repetitions
    print(f"Sweep: {len(selected)} benchmarks x {len(grid)} points x {args.repetitions} reps = {total_runs_max} runs (max)")
    print(f"Grid: {[(p.timeout, p.num_iterations) for p in grid]}")
    if args.patience > 0:
        print(f"Early stopping: patience={args.patience}, metric={args.early_stop_metric}")

    all_rows: list[dict[str, Any]] = []
    raw_jsonl = output_dir / "runs.jsonl"
    if raw_jsonl.exists():
        raw_jsonl.unlink()

    run_index = 0
    skipped_count = 0
    for bench in selected:
        for timeout_row in grid_by_timeout:
            best_metric = -1.0
            stale_count = 0

            for point in timeout_row:
                # Check early stopping before running
                if args.patience > 0 and stale_count >= args.patience:
                    n_skipped = args.repetitions
                    skipped_count += n_skipped
                    run_index += n_skipped
                    print(
                        f"[SKIP] benchmark={bench.key} timeout={point.timeout} "
                        f"iterations={point.num_iterations} — no improvement "
                        f"for {args.patience} consecutive points"
                    )
                    continue

                point_rows: list[dict[str, Any]] = []
                for rep in range(1, args.repetitions + 1):
                    run_index += 1
                    summary, rc, wall = run_sweep_point(
                        repo_root, bench, point, rep, output_dir, args,
                        run_index, total_runs_max,
                    )
                    row = _flatten_sweep_row(bench, point, rep, summary, rc, wall)
                    point_rows.append(row)
                    all_rows.append(row)
                    with raw_jsonl.open("a") as f:
                        f.write(json.dumps(row, sort_keys=True) + "\n")

                # Update early stopping tracker
                if args.patience > 0:
                    if args.early_stop_metric == "accepted_constraints":
                        vals = [r["accepted_constraints"] for r in point_rows if r["accepted_constraints"] >= 0]
                        current = sum(vals) / len(vals) if vals else -1.0
                    else:  # solution_found
                        current = sum(1 for r in point_rows if r.get("solution_found")) / len(point_rows)

                    if current > best_metric + 1e-9:
                        best_metric = current
                        stale_count = 0
                    else:
                        stale_count += 1
                        print(
                            f"[EARLY-STOP] benchmark={bench.key} timeout={point.timeout} "
                            f"iterations={point.num_iterations} — metric={current:.1f} "
                            f"not better than best={best_metric:.1f} "
                            f"(stale {stale_count}/{args.patience})"
                        )

    if skipped_count > 0:
        print(f"\n[INFO] Early stopping saved {skipped_count} runs")

    _write_csv(output_dir / "runs.csv", all_rows)
    agg = _build_aggregate(all_rows)
    _write_csv(output_dir / "summary.csv", agg)
    (output_dir / "summary.json").write_text(json.dumps(agg, indent=2, sort_keys=True) + "\n")

    print(f"\n[DONE] {len(all_rows)} runs written to {output_dir / 'runs.csv'}")
    print(f"[DONE] Aggregated summary: {output_dir / 'summary.csv'}")

    # Print a quick summary table
    print(f"\n{'='*80}")
    print("SUMMARY (solve rate by benchmark x sweep point)")
    print(f"{'='*80}")
    for entry in agg:
        print(
            f"  {entry['benchmark']:30s}  timeout={entry['timeout']:4d}  "
            f"iters={entry['num_iterations']:3d}  "
            f"solve_rate={entry['solve_rate']:.0%}  "
            f"mean_solver_s={entry.get('mean_solver_runtime_s', -1) or -1:7.1f}  "
            f"mean_wall_s={entry.get('mean_wall_seconds', -1) or -1:7.1f}  "
            f"mean_accepted={entry.get('mean_accepted_constraints', -1) or -1:5.1f}"
        )


if __name__ == "__main__":
    main()
