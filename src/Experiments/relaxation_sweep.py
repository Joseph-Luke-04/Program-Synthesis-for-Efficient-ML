"""Relaxation ablation sweep — tiered design.

Three-tier run structure
─────────────────────────
Full sweep  (all fixed levels + staged, nominal budget):
    All V1 targets (fp32_add, fp32_mul, mxint8_add, mxint8_mul)
    V2 mxint8_add   ← only V2 case where relaxation still clearly matters

Reduced control (strict + midpoint + staged, nominal budget):
    V2 fp32_add, V2 mxint8_mul, V2 fp32_mul
    ← V2 grammars that mostly saturate at strict; three points are enough

Stress follow-up (strict + staged, tighter budget):
    V2 fp32_mul, V2 mxint8_mul, V2 fp32_add
    ← tests whether relaxation becomes useful when solver budget is cut

FP32  fixed levels (full): 9, 14, 19, 24, 26, 28, 30, 32
MXINT8 fixed levels (full): 4, 5, 6, 7, 8
FP32  reduced levels: 32 (strict), 24 (midpoint)
MXINT8 reduced levels: 8 (strict), 6 (midpoint)

Usage
─────
python -m src.Experiments.relaxation_sweep \\
    --output-dir results/relaxation_sweep/run1 \\
    --repetitions 3 \\
    --timeout 180 \\
    2>&1 | tee logs/relaxation_sweep.log
"""

import argparse
import csv
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

from src.Experiments.grammar_selection_study import _run_and_tee

ROOT = Path(__file__).resolve().parents[2]
VARIANTS_JSON = ROOT / "src" / "Experiments" / "grammar_selection_variants.json"

# ── Benchmark definitions ──────────────────────────────────────────────────────

_FP32_TARGETS = [
    {"key": "fp32_add", "synth_target": "fp32_add",   "component": "full_sum_v2",     "dtype": "FP32"},
    {"key": "fp32_mul", "synth_target": "fp32_mul",   "component": "full_product_v2", "dtype": "FP32"},
]
_MXINT8_TARGETS = [
    {"key": "mxint8_add", "synth_target": "mxint8_add", "component": "full_sum_v2",     "dtype": "MXINT8"},
    {"key": "mxint8_mul", "synth_target": "mxint8_mul", "component": "full_product_v2", "dtype": "MXINT8"},
]

# Fixed-mode sweep levels for full-profile targets.
DEFAULT_FP32_LEVELS   = [9, 19, 24, 28, 32]
DEFAULT_MXINT8_LEVELS = [4, 5, 6, 7, 8]

# Reduced-profile: strict top and midpoint only.
FP32_STRICT     = 32
MXINT8_STRICT   = 8
FP32_MIDPOINT   = 24
MXINT8_MIDPOINT = 6

# Profile assignment by (benchmark_key, variant).
# "full"    → all fixed levels + staged at nominal budget
# "reduced" → strict + midpoint + staged at nominal budget
_FULL_PROFILE = frozenset({
    ("fp32_add",   "V1"), ("fp32_mul",   "V1"),
    ("mxint8_add", "V1"), ("mxint8_mul", "V1"),
    ("mxint8_add", "V2"),
})
_REDUCED_PROFILE = frozenset({
    ("fp32_add",   "V2"), ("fp32_mul",   "V2"), ("mxint8_mul", "V2"),
})
# Stress targets: also get a tighter-budget run (strict + staged only).
_STRESS_TARGETS = frozenset({
    ("fp32_add",   "V2"), ("fp32_mul",   "V2"), ("mxint8_mul", "V2"),
})

VARIANTS = ["V1", "V2"]

# ── Helpers ────────────────────────────────────────────────────────────────────

def _load_templates(variant_manifest: dict, target_key: str) -> dict[str, str]:
    entry = variant_manifest.get(target_key, {})
    return {v: entry[v] for v in VARIANTS if v in entry}


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    keys: list[str] = []
    seen: set[str] = set()
    for row in rows:
        for k in row.keys():
            if k not in seen:
                seen.add(k)
                keys.append(k)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)


def _extract_row(
    target: dict[str, str],
    variant: str,
    match_bits: int,
    relax_mode: str,
    budget: str,
    repetition: int,
    seed: int,
    summary: dict[str, Any],
    returncode: int,
    wall_seconds: float,
) -> dict[str, Any]:
    comp     = summary.get("components", {}).get(target["component"], {})
    accuracy = summary.get("accuracy") or {}
    hw       = summary.get("hardware") or {}

    luts       = hw.get("LUTs", -1)
    latency_ns = hw.get("Latency_ns", -1)
    adp = (float(luts) * float(latency_ns)
           if isinstance(luts, (int, float)) and luts > 0
           and isinstance(latency_ns, (int, float)) and latency_ns > 0
           else -1.0)

    accepted                 = comp.get("accepted_constraints", -1)
    accepted_strict          = comp.get("accepted_strict", -1)
    accepted_final_strict    = comp.get("accepted_final_strict", -1)
    accepted_stage1          = comp.get("accepted_stage1", -1)
    accepted_stage0          = comp.get("accepted_stage0", -1)
    accepted_used_relaxation = comp.get("accepted_used_relaxation", -1)
    true_skips               = comp.get("true_skips", -1)
    invalid_gt_skips         = comp.get("invalid_ground_truth_skips", -1)
    used_relaxation = (
        isinstance(accepted_used_relaxation, int)
        and accepted_used_relaxation > 0
    )

    return {
        "benchmark":                    target["key"],
        "dtype":                        target["dtype"],
        "variant":                      variant,
        "match_bits":                   match_bits,
        "relax_mode":                   relax_mode,
        "budget":                       budget,
        "repetition":                   repetition,
        "random_seed":                  seed,
        "driver_returncode":            returncode,
        "run_status":                   summary.get("status", "unknown"),
        "component_solve_status":       comp.get("solve_status", "unknown"),
        "solution_found":               bool(comp.get("solution_found", False)),
        "accepted_constraints":         accepted,
        "total_constraints":            comp.get("total_constraints", -1),
        "accepted_strict":              accepted_strict,
        "accepted_final_strict":        accepted_final_strict,
        "accepted_stage1":              accepted_stage1,
        "accepted_stage0":              accepted_stage0,
        "accepted_used_relaxation":     accepted_used_relaxation,
        "true_skips":                   true_skips,
        "invalid_ground_truth_skips":   invalid_gt_skips,
        "used_relaxation":              used_relaxation,
        "attempt_status_counts":        comp.get("attempt_status_counts", {}),
        "solver_attempts":              comp.get("solver_attempts", -1),
        "solver_runtime_seconds_total": comp.get("solver_runtime_seconds_total", -1.0),
        "solver_runtime_seconds_max":   comp.get("solver_runtime_seconds_max", -1.0),
        "enum_count_primary_total":     comp.get("enum_count_primary_total", -1),
        "wall_seconds":                 wall_seconds,
        "luts":                         luts,
        "ffs":                          hw.get("FFs", -1),
        "dsps":                         hw.get("DSPs", -1),
        "fmax_mhz":                     hw.get("Fmax_MHz", -1),
        "latency_ns":                   latency_ns,
        "adp_lut_ns":                   adp,
        "within_rel_pct":               accuracy.get("within_rel_pct", -1.0),
        "abs_err_avg":                  accuracy.get("abs_err_avg", -1.0),
        "abs_err_max":                  accuracy.get("abs_err_max", -1.0),
        "error_samples_npz":            "",
    }


def _run_one(
    target: dict[str, str],
    variant: str,
    match_bits: int,
    relax_mode: str,
    budget: str,
    repetition: int,
    seed: int,
    template_path: str,
    timeout: int,
    num_iterations: int,
    run_impl: bool,
    run_accuracy: bool,
    out_dir: Path,
    run_index: int,
    total_runs: int,
) -> tuple[dict[str, Any], int]:
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    budget_tag   = "_stress" if budget == "stress" else ""
    mode_tag     = "staged" if relax_mode == "staged" else f"{match_bits}b"
    tag          = f"{target['key']}_{variant.lower()}_{mode_tag}{budget_tag}_r{repetition:02d}"
    summary_path = raw_dir / f"{tag}.json"
    log_path     = raw_dir / f"{tag}.log"
    solution_stem = f"relaxsweep_{tag}"

    env = os.environ.copy()
    base_env: dict[str, str] = {
        "SYNTH_TARGET":                     target["synth_target"],
        "SYNTH_COMPONENT":                  target["component"],
        "SYNTH_TEMPLATE_OVERRIDE":          template_path,
        "SYNTH_SOLVER_TIMEOUT":             str(timeout),
        "SYNTH_NUM_ITERATIONS":             str(num_iterations),
        "SYNTH_RUN_IMPL":                   "1" if run_impl else "0",
        "SYNTH_RUN_ACCURACY":               "1" if run_accuracy else "0",
        "SYNTH_ENABLE_DIRECTED_IO":         "1",
        "SYNTH_ENABLE_SYGUS_DUMP":          "0",
        "SYNTH_ENABLE_SYGUS_FAST_ENUM":     "0",
        "SYNTH_ENABLE_SYGUS_PBE":           "1",
        "SYNTH_ENABLE_SYGUS_SYM_BREAK_PBE": "1",
        "SYNTH_SUMMARY_PATH":               str(summary_path),
        "SYNTH_SOLUTION_STEM":              solution_stem,
        "SYNTH_RANDOM_SEED":                str(seed),
        "PYTHONHASHSEED":                   str(seed),
        "SYNTH_FP32_TIMEOUT_RETRY_ONCE":    "0",
    }

    if relax_mode == "staged":
        if target["dtype"] == "FP32":
            base_env.update({
                "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH":   "1",
                "SYNTH_FP32_OUTPUT_MATCH_MSB_BITS":     "32",
                "SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS": "9",
                "SYNTH_FP32_RELAX_SCHEDULE":            "staged",
                "SYNTH_FP32_RELAX_ON_TIMEOUT":          "1",
                "SYNTH_FP32_RELAX_ON_INFEASIBLE":       "1",
                "SYNTH_FP32_RELAX_ON_FAIL":             "1",
                "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "0",
                "SYNTH_MXINT8_RELAX_ON_TIMEOUT":        "0",
                "SYNTH_MXINT8_RELAX_ON_INFEASIBLE":     "0",
                "SYNTH_MXINT8_RELAX_ON_FAIL":           "0",
            })
        else:
            base_env.update({
                "SYNTH_MXINT8_OUTPUT_MATCH_BITS":       "8",
                "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "1",
                "SYNTH_MXINT8_RELAX_ON_TIMEOUT":        "1",
                "SYNTH_MXINT8_RELAX_ON_INFEASIBLE":     "1",
                "SYNTH_MXINT8_RELAX_ON_FAIL":           "1",
                "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH":   "0",
                "SYNTH_FP32_RELAX_ON_TIMEOUT":          "0",
                "SYNTH_FP32_RELAX_ON_INFEASIBLE":       "0",
                "SYNTH_FP32_RELAX_ON_FAIL":             "0",
            })
    else:
        # Fixed mode: pin to exactly match_bits, no fallback.
        base_env.update({
            "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH":   "0",
            "SYNTH_FP32_RELAX_ON_TIMEOUT":          "0",
            "SYNTH_FP32_RELAX_ON_INFEASIBLE":       "0",
            "SYNTH_FP32_RELAX_ON_FAIL":             "0",
            "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "0",
            "SYNTH_MXINT8_RELAX_ON_TIMEOUT":        "0",
            "SYNTH_MXINT8_RELAX_ON_INFEASIBLE":     "0",
            "SYNTH_MXINT8_RELAX_ON_FAIL":           "0",
        })
        if target["dtype"] == "FP32":
            base_env["SYNTH_FP32_OUTPUT_MATCH_MSB_BITS"]     = str(match_bits)
            base_env["SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS"] = str(match_bits)
        else:
            base_env["SYNTH_MXINT8_OUTPUT_MATCH_BITS"] = str(match_bits)

    env.update(base_env)

    # Set per-sample dump paths so cocotb saves NPZ error data
    npz_dir = out_dir / "error_samples"
    npz_dir.mkdir(parents=True, exist_ok=True)
    npz_stem = f"{tag}.npz"
    npz_path = npz_dir / npz_stem
    dump_env_keys = {
        "fp32_add":   "FP32_ADD_DUMP_PATH",
        "fp32_mul":   "FP32_MUL_DUMP_PATH",
        "mxint8_add": "MXINT8_ADD_DUMP_PATH",
        "mxint8_mul": "MXINT8_MUL_DUMP_PATH",
    }
    dump_key = dump_env_keys.get(target["key"])
    if dump_key:
        env[dump_key] = str(npz_path.resolve())

    print(
        f"[RUN {run_index}/{total_runs}] "
        f"benchmark={target['key']} variant={variant} "
        f"relax_mode={relax_mode} match_bits={match_bits} "
        f"budget={budget} rep={repetition} seed={seed}"
    )

    t0   = time.time()
    proc = _run_and_tee(
        [sys.executable, "-m", "src.synthesis_driver"],
        cwd=ROOT, env=env, log_path=log_path,
    )
    wall = time.time() - t0

    if not summary_path.exists():
        print(
            f"[RUN {run_index}/{total_runs} DONE] "
            f"benchmark={target['key']} variant={variant} "
            f"relax_mode={relax_mode} match_bits={match_bits} "
            f"budget={budget} rep={repetition} "
            f"status=missing_summary returncode={proc.returncode} elapsed={wall:.2f}s"
        )
        return {
            "_summary_path": str(summary_path),
            "_log_path":     str(log_path),
            "_wall_seconds": wall,
            "status":        "missing_summary",
        }, proc.returncode

    summary = json.loads(summary_path.read_text())
    summary["_summary_path"] = str(summary_path)
    summary["_log_path"]     = str(log_path)
    summary["_wall_seconds"] = wall

    comp     = summary.get("components", {}).get(target["component"], {})
    accepted = comp.get("accepted_constraints", "?")
    total    = comp.get("total_constraints", "?")
    status   = comp.get("solve_status", summary.get("status", "unknown"))
    print(
        f"[RUN {run_index}/{total_runs} DONE] "
        f"benchmark={target['key']} variant={variant} "
        f"relax_mode={relax_mode} match_bits={match_bits} "
        f"budget={budget} rep={repetition} "
        f"status={status} accepted={accepted}/{total} "
        f"returncode={proc.returncode} elapsed={wall:.2f}s"
    )
    return summary, proc.returncode


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Relaxation ablation: tiered sweep of output-match strictness."
    )
    parser.add_argument("--output-dir", default="results/relaxation_sweep",
                        help="Directory to write results.")
    parser.add_argument("--fp32-levels", type=int, nargs="+", default=DEFAULT_FP32_LEVELS,
                        help="FP32 fixed levels for full-profile targets (default: 9 14 19 24 26 28 30 32).")
    parser.add_argument("--mxint8-levels", type=int, nargs="+", default=DEFAULT_MXINT8_LEVELS,
                        help="MXINT8 fixed levels for full-profile targets (default: 4 5 6 7 8).")
    parser.add_argument("--variants", nargs="+", default=["V1", "V2"], choices=["V1", "V2"],
                        help="Grammar variants to run (default: V1 V2).")
    parser.add_argument("--relax-modes", nargs="+", default=["fixed", "staged"],
                        choices=["fixed", "staged"],
                        help="Relax modes to include (default: fixed staged).")
    parser.add_argument("--no-staged", action="store_true", default=False,
                        help="Shorthand for --relax-modes fixed.")
    parser.add_argument("--repetitions", type=int, default=3,
                        help="Repetitions per (benchmark, variant, level) point.")
    parser.add_argument("--seed", type=int, default=12345,
                        help="Base RNG seed; incremented per repetition.")
    parser.add_argument("--timeout", type=int, default=180,
                        help="Nominal per-solver timeout in seconds.")
    parser.add_argument("--num-iterations", type=int, default=30,
                        help="Synthesis iterations per nominal run.")
    parser.add_argument("--no-stress", action="store_true", default=False,
                        help="Skip stress-budget follow-up runs for reduced V2 targets.")
    parser.add_argument("--stress-timeout", type=int, default=60,
                        help="Solver timeout for stress-budget runs (default: 60).")
    parser.add_argument("--stress-iterations", type=int, default=10,
                        help="Synthesis iterations for stress-budget runs (default: 10).")
    parser.add_argument("--run-impl", action=argparse.BooleanOptionalAction, default=True,
                        help="Run HLS implementation.")
    parser.add_argument("--run-accuracy", action=argparse.BooleanOptionalAction, default=True,
                        help="Run cocotb accuracy tests.")
    parser.add_argument("--benchmarks", nargs="+", default=[],
                        help="Restrict to these benchmark keys (default: all four).")
    args = parser.parse_args()

    selected_modes = set(args.relax_modes)
    if args.no_staged:
        selected_modes.discard("staged")

    out_dir = Path(args.output_dir).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    variant_manifest: dict = json.loads(VARIANTS_JSON.read_text())

    all_targets = _FP32_TARGETS + _MXINT8_TARGETS
    if args.benchmarks:
        wanted = set(args.benchmarks)
        all_targets = [t for t in all_targets if t["key"] in wanted]
        missing = wanted - {t["key"] for t in all_targets}
        if missing:
            valid = ", ".join(t["key"] for t in _FP32_TARGETS + _MXINT8_TARGETS)
            raise ValueError(f"Unknown benchmark(s): {', '.join(missing)}. Valid: {valid}")

    selected_variants = [v for v in VARIANTS if v in args.variants]

    # Each entry: (target, variant, bits, relax_mode, budget, rep, seed, tpl, timeout, num_iters)
    runs: list[tuple] = []

    for target in all_targets:
        templates   = _load_templates(variant_manifest, target["key"])
        strict_bits = FP32_STRICT   if target["dtype"] == "FP32" else MXINT8_STRICT
        midpoint    = FP32_MIDPOINT if target["dtype"] == "FP32" else MXINT8_MIDPOINT
        all_levels  = args.fp32_levels if target["dtype"] == "FP32" else args.mxint8_levels

        for variant in selected_variants:
            tpl = templates.get(variant, "")
            if not tpl:
                print(f"[WARN] No template for {target['key']}/{variant} in manifest — skipping.")
                continue

            key = (target["key"], variant)
            if key in _FULL_PROFILE:
                fixed_levels = all_levels
            elif key in _REDUCED_PROFILE:
                fixed_levels = sorted({strict_bits, midpoint})
            else:
                continue

            # ── Nominal-budget runs ────────────────────────────────────────────
            if "fixed" in selected_modes:
                for bits in fixed_levels:
                    for rep in range(1, args.repetitions + 1):
                        seed = args.seed + (rep - 1)
                        runs.append((target, variant, bits, "fixed", "nominal",
                                     rep, seed, tpl, args.timeout, args.num_iterations))
            if "staged" in selected_modes:
                for rep in range(1, args.repetitions + 1):
                    seed = args.seed + (rep - 1)
                    runs.append((target, variant, strict_bits, "staged", "nominal",
                                 rep, seed, tpl, args.timeout, args.num_iterations))

            # ── Stress-budget runs (reduced V2 targets only) ───────────────────
            if not args.no_stress and key in _STRESS_TARGETS:
                if "fixed" in selected_modes:
                    for rep in range(1, args.repetitions + 1):
                        seed = args.seed + (rep - 1)
                        runs.append((target, variant, strict_bits, "fixed", "stress",
                                     rep, seed, tpl, args.stress_timeout, args.stress_iterations))
                if "staged" in selected_modes:
                    for rep in range(1, args.repetitions + 1):
                        seed = args.seed + (rep - 1)
                        runs.append((target, variant, strict_bits, "staged", "stress",
                                     rep, seed, tpl, args.stress_timeout, args.stress_iterations))

    total     = len(runs)
    n_nominal = sum(1 for r in runs if r[4] == "nominal")
    n_stress  = sum(1 for r in runs if r[4] == "stress")
    n_fixed   = sum(1 for r in runs if r[3] == "fixed")
    n_staged  = sum(1 for r in runs if r[3] == "staged")
    print(
        f"Relaxation ablation sweep: {total} runs "
        f"({n_nominal} nominal + {n_stress} stress | "
        f"{n_fixed} fixed + {n_staged} staged) across "
        f"{len(all_targets)} benchmarks × {len(selected_variants)} variants × {args.repetitions} reps"
    )
    print(f"Output: {out_dir}\n")

    raw_jsonl = out_dir / "runs.jsonl"

    all_rows: list[dict[str, Any]] = []

    for idx, (target, variant, bits, relax_mode, budget, rep, seed, tpl, timeout, num_iters) in enumerate(runs, start=1):
        summary, rc = _run_one(
            target=target, variant=variant, match_bits=bits,
            relax_mode=relax_mode, budget=budget,
            repetition=rep, seed=seed, template_path=tpl,
            timeout=timeout, num_iterations=num_iters,
            run_impl=args.run_impl, run_accuracy=args.run_accuracy,
            out_dir=out_dir, run_index=idx, total_runs=total,
        )
        row = _extract_row(
            target, variant, bits, relax_mode, budget, rep, seed,
            summary, rc, summary.get("_wall_seconds", -1.0),
        )
        # Record NPZ path if the dump file was created
        budget_tag   = "_stress" if budget == "stress" else ""
        mode_tag     = "staged" if relax_mode == "staged" else f"{bits}b"
        tag          = f"{target['key']}_{variant.lower()}_{mode_tag}{budget_tag}_r{rep:02d}"
        npz_file = out_dir / "error_samples" / f"{tag}.npz"
        if npz_file.exists():
            row["error_samples_npz"] = str(npz_file)
        all_rows.append(row)
        with raw_jsonl.open("a") as f:
            f.write(json.dumps(row) + "\n")

    _write_csv(out_dir / "runs.csv", all_rows)
    print(f"\n[DONE] {len(all_rows)} rows written to {out_dir / 'runs.csv'}")

    # ── Per-point aggregated summary ───────────────────────────────────────────
    from collections import defaultdict
    import statistics

    groups: dict[tuple, list[dict]] = defaultdict(list)
    for row in all_rows:
        k = (row["benchmark"], row["dtype"], row["variant"],
             row["relax_mode"], row["budget"], row["match_bits"])
        groups[k].append(row)

    def _mean(vals: list) -> float | None:
        clean = [v for v in vals if isinstance(v, (int, float)) and v >= 0]
        return statistics.mean(clean) if clean else None

    agg_rows: list[dict[str, Any]] = []
    for (benchmark, dtype, variant, relax_mode, budget, bits), grp in sorted(groups.items()):
        agg_rows.append({
            "benchmark":                 benchmark,
            "dtype":                     dtype,
            "variant":                   variant,
            "relax_mode":                relax_mode,
            "budget":                    budget,
            "match_bits":                bits,
            "n_reps":                    len(grp),
            "solve_rate":                sum(1 for r in grp if r.get("solution_found")) / len(grp),
            "mean_accepted":                    _mean([r["accepted_constraints"]         for r in grp]),
            "mean_accepted_strict":             _mean([r["accepted_strict"]               for r in grp]),
            "mean_accepted_final_strict":       _mean([r["accepted_final_strict"]         for r in grp]),
            "mean_accepted_stage1":             _mean([r["accepted_stage1"]               for r in grp]),
            "mean_accepted_stage0":             _mean([r["accepted_stage0"]               for r in grp]),
            "mean_accepted_used_relaxation":    _mean([r["accepted_used_relaxation"]      for r in grp]),
            "mean_true_skips":                  _mean([r["true_skips"]                    for r in grp]),
            "mean_invalid_gt_skips":            _mean([r["invalid_ground_truth_skips"]    for r in grp]),
            "frac_reps_with_relaxation":        sum(
                1 for r in grp
                if isinstance(r.get("accepted_used_relaxation"), int) and r["accepted_used_relaxation"] > 0
            ) / len(grp),
            "mean_solver_attempts":             _mean([r["solver_attempts"]              for r in grp]),
            "mean_solver_runtime_total":        _mean([r["solver_runtime_seconds_total"]  for r in grp]),
            "mean_enum_count_total":            _mean([r["enum_count_primary_total"]      for r in grp]),
            "mean_within_rel_pct":       _mean([r["within_rel_pct"]              for r in grp]),
            "mean_luts":                 _mean([r["luts"]                        for r in grp]),
            "mean_fmax_mhz":             _mean([r["fmax_mhz"]                    for r in grp]),
            "mean_latency_ns":           _mean([r["latency_ns"]                  for r in grp]),
            "mean_adp_lut_ns":           _mean([r["adp_lut_ns"]                  for r in grp]),
            "mean_wall_seconds":         _mean([r["wall_seconds"]                for r in grp]),
        })

    _write_csv(out_dir / "summary.csv", agg_rows)
    print(f"[DONE] Aggregated summary written to {out_dir / 'summary.csv'}")


if __name__ == "__main__":
    main()
