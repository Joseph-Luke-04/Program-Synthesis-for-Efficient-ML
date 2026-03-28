#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

echo "=== mxint8_mul_subcomponents ==="
SYNTH_TARGET="mxint8_mul" \
SYNTH_COMPONENT="full_product" \
SYNTH_RUN_IMPL="1" \
SYNTH_RUN_ACCURACY="1" \
SYNTH_ENABLE_DIRECTED_IO="1" \
SYNTH_NUM_ITERATIONS="30" \
SYNTH_SOLVER_TIMEOUT="200" \
SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH="0" \
  $VENV -m src.synthesis_driver || echo "[WARN] mxint8_mul_subcomponents failed"

echo "=== mxint8_mul_v1 ==="
SYNTH_TARGET="mxint8_mul" \
SYNTH_COMPONENT="full_product_v2" \
SYNTH_RUN_IMPL="1" \
SYNTH_RUN_ACCURACY="1" \
SYNTH_ENABLE_DIRECTED_IO="1" \
SYNTH_NUM_ITERATIONS="30" \
SYNTH_SOLVER_TIMEOUT="200" \
SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH="0" \
SYNTH_TEMPLATE_OVERRIDE_FULL_PRODUCT_V2="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v1_template.sl" \
SYNTH_SOLUTION_STEM="solution_mxint8multiplication_full_product_v1" \
  $VENV -m src.synthesis_driver || echo "[WARN] mxint8_mul_v1 failed"

echo "=== mxint8_mul_v2 ==="
SYNTH_TARGET="mxint8_mul" \
SYNTH_COMPONENT="full_product_v2" \
SYNTH_RUN_IMPL="1" \
SYNTH_RUN_ACCURACY="1" \
SYNTH_ENABLE_DIRECTED_IO="1" \
SYNTH_NUM_ITERATIONS="30" \
SYNTH_SOLVER_TIMEOUT="200" \
SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH="0" \
  $VENV -m src.synthesis_driver || echo "[WARN] mxint8_mul_v2 failed"

echo "[DONE] All mxint8_mul pipeline jobs complete"
