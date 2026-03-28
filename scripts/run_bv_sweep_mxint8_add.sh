#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

# Subcomponent target — 3 cocotb modes
for MODE in normal_full small wide; do
    echo "=== BV Sweep: mxint8_add subcomponent mode=$MODE ==="
    $VENV -m src.Experiments.bitvector_sweep \
        --target mxint8_add \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir results/sweeps/bitvector_all \
        2>&1 | tee "logs/bv_sweep_mxint8_add_sub_${MODE}.log" || echo "[WARN] mxint8_add sub $MODE failed"
done

# V1 monolithic — 3 cocotb modes
for MODE in normal_full small wide; do
    echo "=== BV Sweep: mxint8_add_v1 mode=$MODE ==="
    $VENV -m src.Experiments.bitvector_sweep \
        --target mxint8_add_v1 \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_mxint8_add_v1_${MODE}.log" || echo "[WARN] mxint8_add_v1 $MODE failed"
done

# V2 monolithic — 3 cocotb modes
for MODE in normal_full small wide; do
    echo "=== BV Sweep: mxint8_add_v2 mode=$MODE ==="
    $VENV -m src.Experiments.bitvector_sweep \
        --target mxint8_add_v2 \
        --impl \
        --cocotb-mode "$MODE" \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_mxint8_add_v2_${MODE}.log" || echo "[WARN] mxint8_add_v2 $MODE failed"
done

echo "[DONE] BV sweep mxint8_add complete"
