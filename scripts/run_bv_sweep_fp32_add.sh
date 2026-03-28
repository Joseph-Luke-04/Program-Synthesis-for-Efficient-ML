#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

# Subcomponent target (mantissa truncation sweep, default mode only — no FP32 mode applies to subcomponent cocotb)
echo "=== BV Sweep: fp32_add subcomponent ==="
$VENV -m src.Experiments.bitvector_sweep \
    --target fp32_add \
    --impl \
    --output-dir results/sweeps/bitvector_all \
    2>&1 | tee logs/bv_sweep_fp32_add_sub.log || echo "[WARN] fp32_add sub failed"

# V1 monolithic — 3 cocotb modes
for MODE in normal_full small wide; do
    echo "=== BV Sweep: fp32_add_v1 mode=$MODE ==="
    $VENV -m src.Experiments.bitvector_sweep \
        --target fp32_add_v1 \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_fp32_add_v1_${MODE}.log" || echo "[WARN] fp32_add_v1 $MODE failed"
done

# V2 monolithic — 3 cocotb modes
for MODE in normal_full small wide; do
    echo "=== BV Sweep: fp32_add_v2 mode=$MODE ==="
    $VENV -m src.Experiments.bitvector_sweep \
        --target fp32_add_v2 \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_fp32_add_v2_${MODE}.log" || echo "[WARN] fp32_add_v2 $MODE failed"
done

echo "[DONE] BV sweep fp32_add complete"
