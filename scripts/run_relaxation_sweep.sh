#!/usr/bin/env bash
# Relaxation sweep: all benchmarks, V1+V2, fixed+staged, 3 reps.
# Launches one tmux session per benchmark target (fp32_add, fp32_mul, mxint8_add, mxint8_mul).
# Each session runs all 3 cocotb modes (normal_full, small, wide) sequentially for its target.
# The mode env vars propagate through synthesis_driver to cocotb accuracy tests.
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=1000000000
export HLS_CLK_UNCERTAINTY_NS=0
export VIVADO_CLK_PERIOD_NS=1000000000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

ROOT="$(pwd)"

for TARGET in fp32_add fp32_mul mxint8_add mxint8_mul; do
    for MODE in normal_full small wide; do
        SESSION="relax_${TARGET}_${MODE}"
        tmux new-session -d -s "$SESSION" bash -c "
            cd $ROOT
            export HLS_CLK_PERIOD_NS=1000000000
            export HLS_CLK_UNCERTAINTY_NS=0
            export VIVADO_CLK_PERIOD_NS=1000000000

            echo '=== Relaxation sweep: ${TARGET} mode=${MODE} ==='
            FP32_ADD_MODE=${MODE} FP32_MUL_MODE=${MODE} \
            MXINT8_ADD_MODE=${MODE} MXINT8_MUL_MODE=${MODE} \
            $VENV -m src.Experiments.relaxation_sweep \
                --output-dir 'results/relaxation_sweep/run1_${MODE}' \
                --benchmarks $TARGET \
                --repetitions 3 \
                --timeout 180 \
                --run-impl \
                --run-accuracy \
                2>&1 | tee 'logs/relaxation_sweep_${TARGET}_${MODE}.log' \
                || echo '[WARN] Relaxation sweep ${TARGET} ${MODE} failed'
            echo '[DONE] Relaxation sweep ${TARGET} ${MODE} finished'
            bash
        "
        echo "Launched tmux session: $SESSION"
    done
done

echo ""
echo "Monitor with: tmux ls | grep relax"
echo "Attach with:  tmux attach -t relax_fp32_add_normal_full"
