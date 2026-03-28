#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

FLOPOCO_BIN="/home/josephluke/flopoco/build/flopoco"

for MODE in normal_full small wide; do
    echo "=== FloPoCo BV Sweep: fp32_mul mode=$MODE ==="
    $VENV -m src.Experiments.flopoco_bitvector_sweep \
        --target fp32_mul \
        --flopoco-bin "$FLOPOCO_BIN" \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/flopoco_bitvector_impl_fp32_mul" \
        2>&1 | tee "logs/flopoco_bv_fp32_mul_${MODE}.log" || echo "[WARN] fp32_mul $MODE failed"
done

echo "[DONE] FloPoCo BV sweep fp32_mul complete"
