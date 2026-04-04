#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=1000000000
export HLS_CLK_UNCERTAINTY_NS=0
export VIVADO_CLK_PERIOD_NS=1000000000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

# Subcomponent target — mantissa truncation sweep, default cocotb mode
echo "=== BV Sweep: fp32_add subcomponent ==="
$VENV -m src.Experiments.bitvector_sweep \
    --target fp32_add \
    --impl \
    --output-dir results/sweeps/bitvector_all \
    2>&1 | tee logs/bv_sweep_fp32_add_sub.log || echo "[WARN] fp32_add sub failed"

echo "[DONE] BV sweep fp32_add complete"
