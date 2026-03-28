#!/usr/bin/env bash
# Re-run cocotb accuracy tests for all 12 pipeline solutions.
# Writes output to logs/pipeline_*.log in the format the analysis notebook expects:
#   HLS_SOLN=<solution_name> ... followed by cocotb output
# Requires .venv with cocotb installed.
set -euo pipefail
cd "$(dirname "$0")/.."

export PATH="$(pwd)/.venv/bin:$PATH"
export PYTHON="$(pwd)/.venv/bin/python"

HLS_BASE="$(pwd)/results/HLS"
ACC_DIR="accuracy_tests"

# Define all 12 pipeline solutions grouped by target (matching pipeline log names)
declare -A TARGET_LOG  # solution -> log file base
declare -A TARGET_TL   # solution -> toplevel
declare -A TARGET_MOD  # solution -> cocotb module

for SOLN in solution_fp32addition_full_sum solution_fp32addition_full_sum_v1 solution_fp32addition_full_sum_v2; do
    TARGET_LOG[$SOLN]="logs/pipeline_fp32_add.log"
    TARGET_TL[$SOLN]="fp32_sum"
    TARGET_MOD[$SOLN]="tests.addition.test_fp32_adder"
done

for SOLN in solution_fp32multiplication_full_product solution_fp32multiplication_full_product_v1 solution_fp32multiplication_full_product_v2; do
    TARGET_LOG[$SOLN]="logs/pipeline_fp32_mul.log"
    TARGET_TL[$SOLN]="fp32_full_mul"
    TARGET_MOD[$SOLN]="tests.multiplication.test_fp32_multiplier"
done

for SOLN in solution_mxint8addition_full_sum solution_mxint8addition_full_sum_v1 solution_mxint8addition_full_sum_v2; do
    TARGET_LOG[$SOLN]="logs/pipeline_mxint8_add.log"
    TARGET_TL[$SOLN]="add_full_sum"
    TARGET_MOD[$SOLN]="tests.addition.test_mxint8_adder"
done

for SOLN in solution_mxint8multiplication_full_product solution_mxint8multiplication_full_product_v1 solution_mxint8multiplication_full_product_v2; do
    TARGET_LOG[$SOLN]="logs/pipeline_mxint8_mul.log"
    TARGET_TL[$SOLN]="mult_mxint_full_product"
    TARGET_MOD[$SOLN]="tests.multiplication.test_mxint8_multiplier"
done

# Clear old pipeline logs so notebook reads only fresh accuracy data
for LOG in logs/pipeline_fp32_add.log logs/pipeline_fp32_mul.log logs/pipeline_mxint8_add.log logs/pipeline_mxint8_mul.log; do
    > "$LOG"
done

PASS=0
FAIL=0

for SOLN in "${!TARGET_LOG[@]}"; do
    LOG="${TARGET_LOG[$SOLN]}"
    TL="${TARGET_TL[$SOLN]}"
    MOD="${TARGET_MOD[$SOLN]}"

    echo "=== $SOLN ==="

    # Check HLS output exists
    if [ ! -d "$HLS_BASE/$SOLN/verilog_out" ]; then
        echo "[SKIP] No verilog_out for $SOLN"
        continue
    fi

    # Write the HLS_SOLN marker the notebook regex looks for, then full cocotb output
    {
        echo ""
        echo "[ACC-CMD] PYTHON=$PYTHON make HLS_BASE=$HLS_BASE HLS_SOLN=$SOLN TOPLEVEL=$TL MODULE=$MOD TOPLEVEL_LANG=verilog"
        echo ""
        make -C "$ACC_DIR" \
            HLS_BASE="$HLS_BASE" \
            HLS_SOLN="$SOLN" \
            TOPLEVEL="$TL" \
            MODULE="$MOD" \
            TOPLEVEL_LANG=verilog \
            2>&1 && RC=0 || RC=$?
        if [ $RC -eq 0 ]; then
            echo "[ACC] Accuracy run completed successfully (rc=0)."
        else
            echo "[WARN] Accuracy run exited with return code $RC (cocotb may still have passed — check log)."
        fi
    } | tee -a "$LOG"

    # Track pass/fail
    if grep -q "FAIL=0" "$LOG" 2>/dev/null; then
        PASS=$((PASS + 1))
    else
        FAIL=$((FAIL + 1))
    fi

    echo ""
done

echo "==============================="
echo "[DONE] Accuracy re-runs complete: $PASS passed, $FAIL failed"
echo "Logs written to: logs/pipeline_*.log"
