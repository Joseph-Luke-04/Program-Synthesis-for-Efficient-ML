#!/usr/bin/env bash
# =============================================================================
# Clean up ALL results and re-launch ALL experiments from scratch in parallel.
# Everything runs in tmux sessions.
#
# Clock settings: 5ns period (200MHz target), 0.2ns uncertainty.
#
# Configuration summary:
#   Pipeline (4 sessions, 12 jobs total):
#     - 4 components × 3 grammars (Subcomponents, V1, V2)
#     - 30 iterations, 200s solver timeout
#     - SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH=0
#     - SYNTH_ENABLE_DIRECTED_IO=1, SYNTH_RUN_IMPL=1, SYNTH_RUN_ACCURACY=1
#
#   HP Sweep (12 sessions, one per benchmark):
#     - Fine preset: timeouts=[30,60,120,180,300] × iterations=[10,15,20,30]
#     - 3 repetitions per grid point, --no-fp32-auto-relax
#
#   Relaxation Sweep (1 session):
#     - V1+V2 variants, fixed+staged, 3 reps, 3 cocotb modes per run
#     - Nominal + stress budgets, --run-impl, --run-accuracy
#
#   BV Sweep (4 sessions, one per component):
#     - Sub + V1 + V2 targets, 3 cocotb modes each (normal_full, small, wide)
#     - --impl enabled
#
#   FloPoCo BV Sweep (2 sessions: fp32_add + fp32_mul):
#     - 3 cocotb modes each (normal_full, small, wide), --impl enabled
#
# Total: 4 pipeline + 12 HP + 1 relax + 2 flopoco = 19 immediate sessions
#        + 4 BV sweep = deferred (need synthesised solutions from pipeline)
# =============================================================================
set -euo pipefail
cd "$(dirname "$0")/.."

PROJECT_ROOT="$(pwd)"

echo "=== CLEANUP: Removing ALL old experiment results ==="

rm -rf results/HLS/
rm -rf results/c/
rm -rf results/cpp/
rm -rf results/smt2/
rm -rf results/CPP/
rm -rf results/relaxation_sweep/
rm -rf results/sweeps/
rm -rf results/grammar_selection_v2/
rm -rf results/grammar_selection/
rm -rf results/notebooks/
rm -rf results/hyperparameter_sweep/fine_v4/
rm -rf logs/*.log

mkdir -p results/HLS results/c results/cpp results/smt2
mkdir -p results/relaxation_sweep results/sweeps
mkdir -p results/grammar_selection_v2 results/notebooks
mkdir -p results/hyperparameter_sweep/fine_v4
mkdir -p logs

echo "=== CLEANUP COMPLETE ==="
echo ""

# Make all sub-scripts executable
chmod +x scripts/run_pipeline_*.sh \
         scripts/run_bv_sweep_*.sh \
         scripts/run_flopoco_bv_*.sh \
         scripts/run_relaxation_sweep.sh \
         scripts/run_hp_sweep.sh

# ── ENV VARS (exported for child shells in tmux) ─────────────────────────────
ENV_EXPORTS="export HLS_CLK_PERIOD_NS=5.000 HLS_CLK_UNCERTAINTY_NS=0.200 VIVADO_CLK_PERIOD_NS=5.000"

# ── 4 PIPELINE SESSIONS ──────────────────────────────────────────────────────
echo "=== LAUNCHING 4 PIPELINE SESSIONS ==="

tmux new-session -d -s pipe_mxint8_add \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_pipeline_mxint8_add.sh 2>&1 | tee logs/pipeline_mxint8_add.log; echo 'Pipeline mxint8_add DONE'; bash"

tmux new-session -d -s pipe_mxint8_mul \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_pipeline_mxint8_mul.sh 2>&1 | tee logs/pipeline_mxint8_mul.log; echo 'Pipeline mxint8_mul DONE'; bash"

tmux new-session -d -s pipe_fp32_add \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_pipeline_fp32_add.sh 2>&1 | tee logs/pipeline_fp32_add.log; echo 'Pipeline fp32_add DONE'; bash"

tmux new-session -d -s pipe_fp32_mul \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_pipeline_fp32_mul.sh 2>&1 | tee logs/pipeline_fp32_mul.log; echo 'Pipeline fp32_mul DONE'; bash"

# ── 12 HP SWEEP SESSIONS ─────────────────────────────────────────────────────
echo "=== LAUNCHING 12 HP SWEEP SESSIONS ==="

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

HP_BENCHMARKS=(
    mxint8_add_v1 mxint8_mul_v1 fp32_add_v1 fp32_mul_v1
    mxint8_add mxint8_mul fp32_add fp32_mul
    mxint8_add_sub mxint8_mul_sub fp32_add_sub fp32_mul_sub
)
HP_OUTDIR="results/hyperparameter_sweep/fine_v4"

for BM in "${HP_BENCHMARKS[@]}"; do
    tmux new-session -d -s "hp_$BM" \
        "$ENV_EXPORTS; cd $PROJECT_ROOT; \
         $VENV -m src.Experiments.hyperparameter_sweep \
            --preset fine \
            --benchmarks $BM \
            --repetitions 3 \
            --no-fp32-auto-relax \
            --output-dir $HP_OUTDIR \
            2>&1 | tee logs/hp_sweep_${BM}.log; \
         echo 'HP sweep $BM DONE'; bash"
done

# ── 3 RELAXATION SWEEP SESSIONS (one per cocotb mode) ────────────────────────
echo "=== LAUNCHING 3 RELAXATION SWEEP SESSIONS ==="

for MODE in normal_full small wide; do
    tmux new-session -d -s "relax_${MODE}" \
        "$ENV_EXPORTS; cd $PROJECT_ROOT; \
         FP32_ADD_MODE=$MODE FP32_MUL_MODE=$MODE \
         MXINT8_ADD_MODE=$MODE MXINT8_MUL_MODE=$MODE \
         $VENV -m src.Experiments.relaxation_sweep \
            --output-dir results/relaxation_sweep/run1_${MODE} \
            --repetitions 3 \
            --timeout 180 \
            --run-impl \
            --run-accuracy \
            2>&1 | tee logs/relaxation_sweep_${MODE}.log; \
         echo 'Relaxation sweep $MODE DONE'; bash"
done

# ── 2 FLOPOCO BV SESSIONS ────────────────────────────────────────────────────
echo "=== LAUNCHING 2 FLOPOCO BV SESSIONS ==="

tmux new-session -d -s flopoco_bv_add \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_flopoco_bv_fp32_add.sh 2>&1 | tee logs/flopoco_bv_fp32_add_session.log; echo 'FloPoCo BV fp32_add DONE'; bash"

tmux new-session -d -s flopoco_bv_mul \
    "$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_flopoco_bv_fp32_mul.sh 2>&1 | tee logs/flopoco_bv_fp32_mul_session.log; echo 'FloPoCo BV fp32_mul DONE'; bash"

echo ""
echo "================================================================="
echo "21 sessions launched. Summary:"
echo ""
echo "  PIPELINE (4):"
echo "    pipe_mxint8_add  - MXINT8 Add (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_mxint8_mul  - MXINT8 Mul (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_fp32_add    - FP32 Add (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_fp32_mul    - FP32 Mul (Sub + V1 + V2), 30 iter, 200s timeout"
echo ""
echo "  HP SWEEP (12):"
echo "    hp_mxint8_add_v1, hp_mxint8_mul_v1, hp_fp32_add_v1, hp_fp32_mul_v1"
echo "    hp_mxint8_add,    hp_mxint8_mul,    hp_fp32_add,    hp_fp32_mul"
echo "    hp_mxint8_add_sub, hp_mxint8_mul_sub, hp_fp32_add_sub, hp_fp32_mul_sub"
echo "    Fine preset, 3 reps, --no-fp32-auto-relax"
echo ""
echo "  RELAXATION SWEEP (3, one per cocotb mode):"
echo "    relax_normal_full - V1+V2, fixed+staged, 3 reps"
echo "    relax_small       - V1+V2, fixed+staged, 3 reps"
echo "    relax_wide        - V1+V2, fixed+staged, 3 reps"
echo ""
echo "  FLOPOCO BV (2):"
echo "    flopoco_bv_add - fp32_add, 3 modes (normal_full, small, wide)"
echo "    flopoco_bv_mul - fp32_mul, 3 modes (normal_full, small, wide)"
echo ""
echo "  DEFERRED — launch AFTER all 4 pipeline sessions finish:"
echo "    tmux new-session -d -s bv_fp32_add    '$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_bv_sweep_fp32_add.sh 2>&1 | tee logs/bv_fp32_add_session.log; bash'"
echo "    tmux new-session -d -s bv_fp32_mul    '$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_bv_sweep_fp32_mul.sh 2>&1 | tee logs/bv_fp32_mul_session.log; bash'"
echo "    tmux new-session -d -s bv_mxint8_add  '$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_bv_sweep_mxint8_add.sh 2>&1 | tee logs/bv_mxint8_add_session.log; bash'"
echo "    tmux new-session -d -s bv_mxint8_mul  '$ENV_EXPORTS; cd $PROJECT_ROOT; bash scripts/run_bv_sweep_mxint8_mul.sh 2>&1 | tee logs/bv_mxint8_mul_session.log; bash'"
echo ""
echo "Monitor: tmux attach -t <session>"
echo "List:    tmux list-sessions"
echo "================================================================="
