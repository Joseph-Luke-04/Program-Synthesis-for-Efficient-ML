#!/usr/bin/env bash
# Launches 12 parallel HP sweep sessions (one per benchmark target).
# Fine preset: timeouts=[30,60,120,180,300] × iterations=[10,15,20,30], 3 reps.
# Uses --no-fp32-auto-relax per dissertation requirements.
set -euo pipefail
cd "$(dirname "$0")/.."

export HLS_CLK_PERIOD_NS=5.000
export HLS_CLK_UNCERTAINTY_NS=0.200
export VIVADO_CLK_PERIOD_NS=5.000

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

OUTDIR="results/hyperparameter_sweep/fine_v4"

BENCHMARKS=(
    mxint8_add_v1 mxint8_mul_v1 fp32_add_v1 fp32_mul_v1
    mxint8_add mxint8_mul fp32_add fp32_mul
    mxint8_add_sub mxint8_mul_sub fp32_add_sub fp32_mul_sub
)

for BM in "${BENCHMARKS[@]}"; do
    echo "Launching HP sweep session: hp_$BM"
    tmux new-session -d -s "hp_$BM" \
        "export HLS_CLK_PERIOD_NS=5.000 HLS_CLK_UNCERTAINTY_NS=0.200 VIVADO_CLK_PERIOD_NS=5.000; \
         cd $(pwd); \
         $VENV -m src.Experiments.hyperparameter_sweep \
            --preset fine \
            --benchmarks $BM \
            --repetitions 3 \
            --no-fp32-auto-relax \
            --output-dir $OUTDIR \
            2>&1 | tee logs/hp_sweep_${BM}.log; \
         echo \"HP sweep $BM DONE\"; bash"
done

echo ""
echo "Launched 12 HP sweep sessions:"
printf "  hp_%s\n" "${BENCHMARKS[@]}"
echo ""
echo "Monitor: tmux attach -t hp_<benchmark>"
