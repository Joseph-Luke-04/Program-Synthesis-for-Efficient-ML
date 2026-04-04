#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=1000000000
export HLS_CLK_UNCERTAINTY_NS=0
export VIVADO_CLK_PERIOD_NS=1000000000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then
    VENV="python3"
fi

echo "=== Relaxation sweep rerun: mxint8_mul mode=normal_full ==="
export PYTHONUNBUFFERED=1
FP32_ADD_MODE=normal_full FP32_MUL_MODE=normal_full \
MXINT8_ADD_MODE=normal_full MXINT8_MUL_MODE=normal_full \
"$VENV" -u -m src.Experiments.relaxation_sweep \
    --output-dir results/relaxation_sweep/run1_normal_full \
    --benchmarks mxint8_mul \
    --repetitions 3 \
    --timeout 180 \
    --run-impl \
    --run-accuracy \
    2>&1 | tee logs/relaxation_sweep_mxint8_mul_normal_full.log

"$VENV" - <<'PY'
import csv
import json
import statistics
from collections import defaultdict
from pathlib import Path

out_dir = Path("results/relaxation_sweep/run1_normal_full")
jsonl = out_dir / "runs.jsonl"
rows = []
for line in jsonl.read_text().splitlines():
    if line.strip():
        rows.append(json.loads(line))

if rows:
    keys = []
    seen = set()
    for row in rows:
        for key in row.keys():
            if key not in seen:
                seen.add(key)
                keys.append(key)
    with (out_dir / "runs.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)

    groups = defaultdict(list)
    for row in rows:
        group_key = (
            row["benchmark"],
            row["dtype"],
            row["variant"],
            row["relax_mode"],
            row["budget"],
            row["match_bits"],
        )
        groups[group_key].append(row)

    def mean(vals):
        clean = [v for v in vals if isinstance(v, (int, float)) and v >= 0]
        return statistics.mean(clean) if clean else None

    agg_rows = []
    for (benchmark, dtype, variant, relax_mode, budget, bits), grp in sorted(groups.items()):
        agg_rows.append({
            "benchmark": benchmark,
            "dtype": dtype,
            "variant": variant,
            "relax_mode": relax_mode,
            "budget": budget,
            "match_bits": bits,
            "n_reps": len(grp),
            "solve_rate": sum(1 for r in grp if r.get("solution_found")) / len(grp),
            "mean_accepted": mean([r["accepted_constraints"] for r in grp]),
            "mean_accepted_strict": mean([r["accepted_strict"] for r in grp]),
            "mean_accepted_final_strict": mean([r["accepted_final_strict"] for r in grp]),
            "mean_accepted_stage1": mean([r["accepted_stage1"] for r in grp]),
            "mean_accepted_stage0": mean([r["accepted_stage0"] for r in grp]),
            "mean_accepted_used_relaxation": mean([r["accepted_used_relaxation"] for r in grp]),
            "mean_true_skips": mean([r["true_skips"] for r in grp]),
            "mean_invalid_gt_skips": mean([r["invalid_ground_truth_skips"] for r in grp]),
            "frac_reps_with_relaxation": sum(
                1
                for r in grp
                if isinstance(r.get("accepted_used_relaxation"), int)
                and r["accepted_used_relaxation"] > 0
            ) / len(grp),
            "mean_solver_attempts": mean([r["solver_attempts"] for r in grp]),
            "mean_solver_runtime_total": mean([r["solver_runtime_seconds_total"] for r in grp]),
            "mean_enum_count_total": mean([r["enum_count_primary_total"] for r in grp]),
            "mean_within_rel_pct": mean([r["within_rel_pct"] for r in grp]),
            "mean_luts": mean([r["luts"] for r in grp]),
            "mean_fmax_mhz": mean([r["fmax_mhz"] for r in grp]),
            "mean_latency_ns": mean([r["latency_ns"] for r in grp]),
            "mean_adp_lut_ns": mean([r["adp_lut_ns"] for r in grp]),
            "mean_wall_seconds": mean([r["wall_seconds"] for r in grp]),
        })

    keys = []
    seen = set()
    for row in agg_rows:
        for key in row.keys():
            if key not in seen:
                seen.add(key)
                keys.append(key)
    with (out_dir / "summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        writer.writerows(agg_rows)

    print(f"[DONE] rebuilt runs.csv and summary.csv from {jsonl}")
PY

echo "[DONE] relax_mxint8_mul_normal_full rerun finished"
