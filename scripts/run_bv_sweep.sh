#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

echo "=== Bitvector Sweep: Subcomponent targets (all 4) ==="
$VENV -m src.Experiments.bitvector_sweep \
    --all-targets \
    --impl \
    --output-dir results/sweeps/bitvector_all \
    2>&1 | tee logs/bv_sweep_subcomponents.log

echo ""
echo "=== Bitvector Sweep: V1 monolithic targets ==="
for t in fp32_add_v1 fp32_mul_v1 mxint8_add_v1 mxint8_mul_v1; do
    echo "--- $t ---"
    $VENV -m src.Experiments.bitvector_sweep \
        --target "$t" \
        --impl \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_${t}.log" || echo "[WARN] $t failed"
done

echo ""
echo "=== Bitvector Sweep: V2 monolithic targets ==="
for t in fp32_add_v2 fp32_mul_v2 mxint8_add_v2 mxint8_mul_v2; do
    echo "--- $t ---"
    $VENV -m src.Experiments.bitvector_sweep \
        --target "$t" \
        --impl \
        --output-dir "results/sweeps/bitvector_all" \
        2>&1 | tee "logs/bv_sweep_${t}.log" || echo "[WARN] $t failed"
done

echo "[DONE] All BV sweeps complete"
