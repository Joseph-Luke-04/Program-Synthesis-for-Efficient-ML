"""Run the full synthesis+accuracy pipeline for all 12 targets sequentially.

Covers Subcomponents, V1, and V2 grammars for all 4 ops (mxint8_add, mxint8_mul, fp32_add, fp32_mul).

Usage:
    .venv/bin/python -m src.Experiments.run_pipeline 2>&1 | tee logs/pipeline.log
"""

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_SYGUS = ROOT / "sygus_grammars"

JOBS = [
    # ── MXINT8 Addition ──
    {"name": "mxint8_add_subcomponents", "target": "mxint8_add", "component": "full_sum"},
    {"name": "mxint8_add_v1", "target": "mxint8_add", "component": "full_sum_v2",
     "extra_env": {
         "SYNTH_TEMPLATE_OVERRIDE_FULL_SUM_V2": str(_SYGUS / "addition/MXINT8/mxint8_add_full_sum_v1_template.sl"),
         "SYNTH_SOLUTION_STEM": "solution_mxint8addition_full_sum_v1",
     }},
    {"name": "mxint8_add_v2", "target": "mxint8_add", "component": "full_sum_v2"},
    # ── MXINT8 Multiplication ──
    {"name": "mxint8_mul_subcomponents", "target": "mxint8_mul", "component": "full_product"},
    {"name": "mxint8_mul_v1", "target": "mxint8_mul", "component": "full_product_v2",
     "extra_env": {
         "SYNTH_TEMPLATE_OVERRIDE_FULL_PRODUCT_V2": str(_SYGUS / "multiplication/MXINT8/mxint8_mult_full_product_v1_template.sl"),
         "SYNTH_SOLUTION_STEM": "solution_mxint8multiplication_full_product_v1",
     }},
    {"name": "mxint8_mul_v2", "target": "mxint8_mul", "component": "full_product_v2"},
    # ── FP32 Addition ──
    {"name": "fp32_add_subcomponents", "target": "fp32_add", "component": "full_sum"},
    {"name": "fp32_add_v1", "target": "fp32_add", "component": "full_sum_v2",
     "extra_env": {
         "SYNTH_TEMPLATE_OVERRIDE_FULL_SUM_V2": str(_SYGUS / "addition/FP32/fp32_full_sum_v1_template.sl"),
         "SYNTH_SOLUTION_STEM": "solution_fp32addition_full_sum_v1",
     }},
    {"name": "fp32_add_v2", "target": "fp32_add", "component": "full_sum_v2"},
    # ── FP32 Multiplication ──
    {"name": "fp32_mul_subcomponents", "target": "fp32_mul", "component": "full_product"},
    {"name": "fp32_mul_v1", "target": "fp32_mul", "component": "full_product_v2",
     "extra_env": {
         "SYNTH_TEMPLATE_OVERRIDE_FULL_PRODUCT_V2": str(_SYGUS / "multiplication/FP32/fp32_full_prod_v1_template.sl"),
         "SYNTH_SOLUTION_STEM": "solution_fp32multiplication_full_product_v1",
     }},
    {"name": "fp32_mul_v2", "target": "fp32_mul", "component": "full_product_v2"},
]

NUM_ITERATIONS = 30
SOLVER_TIMEOUT_SECONDS = 180

results = []

print(f"Running synthesis+accuracy pipeline for {len(JOBS)} jobs")
print(f"NUM_ITERATIONS={NUM_ITERATIONS}, SOLVER_TIMEOUT={SOLVER_TIMEOUT_SECONDS}s, FP32_AUTO_RELAX=OFF\n")

for job in JOBS:
    print(f"\n{'='*60}")
    print(f"=== {job['name']}  (timeout={SOLVER_TIMEOUT_SECONDS}s, iters={NUM_ITERATIONS}) ===")
    print(f"{'='*60}", flush=True)

    env = os.environ.copy()
    env.update({
        "SYNTH_TARGET":                       job["target"],
        "SYNTH_COMPONENT":                    job["component"],
        "SYNTH_RUN_IMPL":                     "1",
        "SYNTH_RUN_ACCURACY":                 "1",
        "SYNTH_ENABLE_DIRECTED_IO":           "1",
        "SYNTH_NUM_ITERATIONS":               str(NUM_ITERATIONS),
        "SYNTH_SOLVER_TIMEOUT":               str(SOLVER_TIMEOUT_SECONDS),
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH": "0",
    })
    if job.get("extra_env"):
        env.update(job["extra_env"])

    proc = subprocess.run(
        [sys.executable, "-m", "src.synthesis_driver"],
        cwd=ROOT, env=env, text=True,
    )

    status = "PASS" if proc.returncode == 0 else "FAIL"
    results.append({"name": job["name"], "returncode": proc.returncode, "status": status})
    print(f"\n[{status}] {job['name']} exited with code {proc.returncode}", flush=True)

print(f"\n{'='*60}")
print("=== FINAL SUMMARY ===")
print(f"{'='*60}")
for r in results:
    print(f"  {r['status']}  {r['name']}")

failed = [r for r in results if r["returncode"] != 0]
if failed:
    print(f"\n{len(failed)} job(s) failed.")
    sys.exit(1)
else:
    print("\nAll jobs completed successfully.")
