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
    echo "=== FloPoCo BV Sweep: mode=$MODE ==="
    for TARGET in fp32_add fp32_mul; do
        echo "--- $TARGET ($MODE) ---"
        $VENV -m src.Experiments.flopoco_bitvector_sweep \
            --target "$TARGET" \
            --flopoco-bin "$FLOPOCO_BIN" \
            --impl \
            --cocotb-mode "$MODE" \
            --output-dir "results/sweeps/flopoco_bitvector_impl_${TARGET}" \
            2>&1 | tee "logs/flopoco_bv_${TARGET}_${MODE}.log" || echo "[WARN] $TARGET $MODE failed"
    done
done

echo "[DONE] All FloPoCo BV sweeps complete"
