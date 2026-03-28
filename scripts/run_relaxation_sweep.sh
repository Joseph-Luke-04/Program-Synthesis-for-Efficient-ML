#!/usr/bin/env bash
# Relaxation sweep: all benchmarks, V1+V2, fixed+staged, 3 reps.
# Launches one tmux session per cocotb mode (normal_full, small, wide) for parallelism.
# The mode env vars (FP32_ADD_MODE, FP32_MUL_MODE, MXINT8_ADD_MODE, MXINT8_MUL_MODE)
# propagate through synthesis_driver to cocotb accuracy tests.
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

for MODE in normal_full small wide; do
    SESSION="relax_${MODE}"
    tmux new-session -d -s "$SESSION" bash -c "
        cd $(pwd)
        export HLS_CLK_PERIOD_NS=5.000
        export HLS_CLK_UNCERTAINTY_NS=0.200
        export VIVADO_CLK_PERIOD_NS=5.000
        FP32_ADD_MODE=$MODE FP32_MUL_MODE=$MODE \
        MXINT8_ADD_MODE=$MODE MXINT8_MUL_MODE=$MODE \
        $VENV -m src.Experiments.relaxation_sweep \
            --output-dir 'results/relaxation_sweep/run1_${MODE}' \
            --repetitions 3 \
            --timeout 180 \
            --run-impl \
            --run-accuracy \
            2>&1 | tee 'logs/relaxation_sweep_${MODE}.log'
        echo '[DONE] Relaxation sweep $MODE finished'
    "
    echo "Launched tmux session: $SESSION"
done

echo ""
echo "Monitor with: tmux ls | grep relax"
echo "Attach with:  tmux attach -t relax_normal_full"
