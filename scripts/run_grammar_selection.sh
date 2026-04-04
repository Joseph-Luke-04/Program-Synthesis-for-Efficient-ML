#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=1000000000
export HLS_CLK_UNCERTAINTY_NS=0
export VIVADO_CLK_PERIOD_NS=1000000000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

OUT_DIR="results/grammar_selection"
mkdir -p "$OUT_DIR"

# Clean old results
rm -f "$OUT_DIR"/runs.jsonl "$OUT_DIR"/runs.csv "$OUT_DIR"/summary.csv "$OUT_DIR"/summary.json

# Launch 3 tmux sessions, one per grammar version
for VER in Subcomponents V1 V2; do
    SESSION="gs_${VER,,}"
    tmux new-session -d -s "$SESSION" bash -c "
        cd $(pwd)
        export HLS_CLK_PERIOD_NS=1000000000
        export HLS_CLK_UNCERTAINTY_NS=0
        export VIVADO_CLK_PERIOD_NS=1000000000
        $VENV -m src.Experiments.grammar_selection_study \
            --output-dir '$OUT_DIR' \
            --versions $VER \
            --repetitions 3 \
            --timeout 200 \
            --num-iterations 30 \
            --run-impl \
            --run-accuracy \
            2>&1 | tee 'logs/grammar_selection_${VER,,}.log'
        echo '[DONE] Grammar selection $VER finished'
    "
    echo "Launched tmux session: $SESSION"
done

echo ""
echo "Monitor with: tmux ls"
echo "Attach with:  tmux attach -t gs_subcomponents"
