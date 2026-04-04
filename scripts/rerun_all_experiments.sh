#!/usr/bin/env bash
# =============================================================================
# Clean up ALL results and re-launch ALL experiments from scratch in parallel.
# Everything runs in tmux sessions.
#
# Uses code-default clock settings (5ns period, 0.2ns uncertainty).
#
# Configuration summary:
#   Pipeline (4 sessions, 12 jobs total):
#     - 4 components × 3 grammars (Subcomponents, V1, V2)
#     - 30 iterations, 200s solver timeout
#     - SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH=0
#     - SYNTH_ENABLE_DIRECTED_IO=1, SYNTH_RUN_IMPL=1, SYNTH_RUN_ACCURACY=1
#
#   Grammar Selection (3 sessions, one per variant):
#     - Subcomponents, V1, V2 across all 4 ops
#     - 3 repetitions, 30 iter, 200s timeout, --run-impl, --run-accuracy
#
#   HP Sweep (12 sessions, one per benchmark):
#     - Fine preset: timeouts=[30,60,120,180,300] × iterations=[10,15,20,30]
#     - 3 repetitions per grid point, --no-fp32-auto-relax
#
#   Relaxation Sweep (3 sessions, one per cocotb mode):
#     - V1+V2 variants, fixed+staged, 3 reps
#     - Nominal + stress budgets, --run-impl, --run-accuracy
#
#   FloPoCo BV Sweep (2 sessions: fp32_add + fp32_mul):
#     - 3 cocotb modes each (normal_full, small, wide), --impl enabled
#
#   CVC5 BV Sweep (4 sessions, auto-launched when pipeline finishes):
#     - Sub + V1 + V2 targets, 3 cocotb modes each, --impl enabled
#     - Watcher session polls until all 12 pipeline solutions exist
#
# Total: 4 pipeline + 3 grammar + 12 HP + 3 relax + 2 flopoco + 1 watcher = 25
#        + 4 BV sweep (auto) = 29 sessions
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
rm -rf results/FLOPOCO/
rm -f logs/*.log

mkdir -p results/HLS results/c results/cpp results/smt2
mkdir -p results/relaxation_sweep results/sweeps
mkdir -p results/grammar_selection
mkdir -p results/hyperparameter_sweep/fine_v4
mkdir -p logs

echo "=== CLEANUP COMPLETE ==="
echo ""

# Make all sub-scripts executable
chmod +x scripts/run_pipeline_*.sh \
         scripts/run_bv_sweep_*.sh \
         scripts/run_flopoco_bv_*.sh \
         scripts/run_relaxation_sweep.sh \
         scripts/run_hp_sweep.sh \
         scripts/run_grammar_selection.sh

VENV=".venv/bin/python"
if [ ! -f "$VENV" ]; then VENV="python3"; fi

# ── 4 PIPELINE SESSIONS ──────────────────────────────────────────────────────
echo "=== LAUNCHING 4 PIPELINE SESSIONS ==="

tmux new-session -d -s pipe_mxint8_add \
    "cd $PROJECT_ROOT; bash scripts/run_pipeline_mxint8_add.sh 2>&1 | tee logs/pipeline_mxint8_add.log; echo 'Pipeline mxint8_add DONE'; bash"

tmux new-session -d -s pipe_mxint8_mul \
    "cd $PROJECT_ROOT; bash scripts/run_pipeline_mxint8_mul.sh 2>&1 | tee logs/pipeline_mxint8_mul.log; echo 'Pipeline mxint8_mul DONE'; bash"

tmux new-session -d -s pipe_fp32_add \
    "cd $PROJECT_ROOT; bash scripts/run_pipeline_fp32_add.sh 2>&1 | tee logs/pipeline_fp32_add.log; echo 'Pipeline fp32_add DONE'; bash"

tmux new-session -d -s pipe_fp32_mul \
    "cd $PROJECT_ROOT; bash scripts/run_pipeline_fp32_mul.sh 2>&1 | tee logs/pipeline_fp32_mul.log; echo 'Pipeline fp32_mul DONE'; bash"

# ── 3 GRAMMAR SELECTION SESSIONS ─────────────────────────────────────────────
echo "=== LAUNCHING 3 GRAMMAR SELECTION SESSIONS ==="

GS_OUTDIR="results/grammar_selection"

for VER in Subcomponents V1 V2; do
    SESSION="gs_${VER,,}"
    tmux new-session -d -s "$SESSION" \
        "cd $PROJECT_ROOT; \
         $VENV -m src.Experiments.grammar_selection_study \
            --output-dir $GS_OUTDIR \
            --versions $VER \
            --repetitions 3 \
            --timeout 200 \
            --num-iterations 30 \
            --run-impl \
            --run-accuracy \
            2>&1 | tee logs/grammar_selection_${VER,,}.log; \
         echo 'Grammar selection $VER DONE'; bash"
done

# ── 12 HP SWEEP SESSIONS ─────────────────────────────────────────────────────
echo "=== LAUNCHING 12 HP SWEEP SESSIONS ==="

HP_BENCHMARKS=(
    mxint8_add_v1 mxint8_mul_v1 fp32_add_v1 fp32_mul_v1
    mxint8_add mxint8_mul fp32_add fp32_mul
    mxint8_add_sub mxint8_mul_sub fp32_add_sub fp32_mul_sub
)
HP_OUTDIR="results/hyperparameter_sweep/fine_v4"

for BM in "${HP_BENCHMARKS[@]}"; do
    tmux new-session -d -s "hp_$BM" \
        "cd $PROJECT_ROOT; \
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
        "cd $PROJECT_ROOT; \
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
    "cd $PROJECT_ROOT; bash scripts/run_flopoco_bv_fp32_add.sh 2>&1 | tee logs/flopoco_bv_fp32_add_session.log; echo 'FloPoCo BV fp32_add DONE'; bash"

tmux new-session -d -s flopoco_bv_mul \
    "cd $PROJECT_ROOT; bash scripts/run_flopoco_bv_fp32_mul.sh 2>&1 | tee logs/flopoco_bv_fp32_mul_session.log; echo 'FloPoCo BV fp32_mul DONE'; bash"

# ── BV SWEEP AUTO-LAUNCHER (waits for pipeline, then launches 4 sessions) ───
echo "=== LAUNCHING BV SWEEP WATCHER ==="

# All 12 pipeline solution dirs that must exist before BV sweeps can run
SOLUTIONS=(
    solution_fp32addition_full_sum
    solution_fp32addition_full_sum_v1
    solution_fp32addition_full_sum_v2
    solution_fp32multiplication_full_product
    solution_fp32multiplication_full_product_v1
    solution_fp32multiplication_full_product_v2
    solution_mxint8addition_full_sum
    solution_mxint8addition_full_sum_v1
    solution_mxint8addition_full_sum_v2
    solution_mxint8multiplication_full_product
    solution_mxint8multiplication_full_product_v1
    solution_mxint8multiplication_full_product_v2
)

# Write the watcher inline — polls every 60s for all pipeline solutions to exist
WATCHER_CMD="cd $PROJECT_ROOT; echo '[BV-WATCHER] Waiting for all 12 pipeline solutions...'; "
WATCHER_CMD+="while true; do ALL_READY=true; "
for SOL in "${SOLUTIONS[@]}"; do
    WATCHER_CMD+="[ ! -d results/HLS/${SOL}/verilog_out ] && ALL_READY=false; "
done
WATCHER_CMD+="if \$ALL_READY; then break; fi; "
WATCHER_CMD+="FOUND=\$(ls -d results/HLS/solution_*/verilog_out 2>/dev/null | wc -l); "
WATCHER_CMD+="echo \"[BV-WATCHER] \$(date +%H:%M) — \$FOUND/12 pipeline solutions ready. Checking again in 60s...\"; "
WATCHER_CMD+="sleep 60; done; "
WATCHER_CMD+="echo '[BV-WATCHER] All 12 pipeline solutions found! Launching 4 BV sweep sessions...'; "
WATCHER_CMD+="tmux new-session -d -s bv_fp32_add  'cd $PROJECT_ROOT; bash scripts/run_bv_sweep_fp32_add.sh  2>&1 | tee logs/bv_fp32_add_session.log; echo BV_fp32_add_DONE; bash'; "
WATCHER_CMD+="tmux new-session -d -s bv_fp32_mul  'cd $PROJECT_ROOT; bash scripts/run_bv_sweep_fp32_mul.sh  2>&1 | tee logs/bv_fp32_mul_session.log; echo BV_fp32_mul_DONE; bash'; "
WATCHER_CMD+="tmux new-session -d -s bv_mxint8_add 'cd $PROJECT_ROOT; bash scripts/run_bv_sweep_mxint8_add.sh 2>&1 | tee logs/bv_mxint8_add_session.log; echo BV_mxint8_add_DONE; bash'; "
WATCHER_CMD+="tmux new-session -d -s bv_mxint8_mul 'cd $PROJECT_ROOT; bash scripts/run_bv_sweep_mxint8_mul.sh 2>&1 | tee logs/bv_mxint8_mul_session.log; echo BV_mxint8_mul_DONE; bash'; "
WATCHER_CMD+="echo '[BV-WATCHER] All 4 BV sweep sessions launched!'; bash"

tmux new-session -d -s bv_watcher "$WATCHER_CMD"

echo ""
echo "================================================================="
echo "25 sessions launched (+ 4 BV auto-launched when pipeline finishes)."
echo ""
echo "  PIPELINE (4):"
echo "    pipe_mxint8_add  - MXINT8 Add (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_mxint8_mul  - MXINT8 Mul (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_fp32_add    - FP32 Add (Sub + V1 + V2), 30 iter, 200s timeout"
echo "    pipe_fp32_mul    - FP32 Mul (Sub + V1 + V2), 30 iter, 200s timeout"
echo ""
echo "  GRAMMAR SELECTION (3):"
echo "    gs_subcomponents - All ops, Subcomponents variant, 3 reps"
echo "    gs_v1            - All ops, V1 variant, 3 reps"
echo "    gs_v2            - All ops, V2 variant, 3 reps"
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
echo "  BV SWEEP WATCHER (1 → spawns 4 when pipeline done):"
echo "    bv_watcher → bv_fp32_add, bv_fp32_mul, bv_mxint8_add, bv_mxint8_mul"
echo ""
echo "Monitor: tmux attach -t <session>"
echo "List:    tmux list-sessions"
echo "================================================================="
