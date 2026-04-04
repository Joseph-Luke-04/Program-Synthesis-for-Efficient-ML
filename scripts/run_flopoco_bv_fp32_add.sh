#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=1000000000
export HLS_CLK_UNCERTAINTY_NS=0
export VIVADO_CLK_PERIOD_NS=1000000000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

FLOPOCO_BIN="/home/josephluke/flopoco/build/flopoco"

for MODE in normal_full small wide; do
    echo "=== FloPoCo BV Sweep: fp32_add mode=$MODE ==="
    $VENV -m src.Experiments.flopoco_bitvector_sweep \
        --target fp32_add \
        --flopoco-bin "$FLOPOCO_BIN" \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/flopoco_bitvector_impl_fp32_add" \
        2>&1 | tee "logs/flopoco_bv_fp32_add_${MODE}.log" || echo "[WARN] fp32_add $MODE failed"
done

echo "[DONE] FloPoCo BV sweep fp32_add complete"
