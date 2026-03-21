"""Run the full synthesis+accuracy pipeline for all 8 targets sequentially.

Usage:
    .venv/bin/python -m src.Experiments.run_pipeline 2>&1 | tee logs/pipeline.log
"""

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

JOBS = [
    # --- Subcomponent pipeline (dependency chain synthesis) ---
    {"name": "mxint8_add_subcomponents", "target": "mxint8_add", "component": "full_sum",       "timeout": 180},
    {"name": "mxint8_mul_subcomponents", "target": "mxint8_mul", "component": "full_product",    "timeout": 60},
    {"name": "fp32_add_subcomponents",   "target": "fp32_add",   "component": "full_sum",        "timeout": 60},
    {"name": "fp32_mul_subcomponents",   "target": "fp32_mul",   "component": "full_product",    "timeout": 60},
    # --- V1 combined (monolithic grammar, broad search space) ---
    {"name": "mxint8_add_v1", "target": "mxint8_add", "component": "full_sum_v2",     "timeout": 180,
     "template": "sygus_grammars/addition/MXINT8/mxint8_add_full_sum_v1_template.sl",
     "stem": "solution_mxint8addition_full_sum_v1"},
    {"name": "mxint8_mul_v1", "target": "mxint8_mul", "component": "full_product_v2", "timeout": 180,
     "template": "sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v1_template.sl",
     "stem": "solution_mxint8multiplication_full_product_v1"},
    {"name": "fp32_add_v1",   "target": "fp32_add",   "component": "full_sum_v2",     "timeout": 180,
     "template": "sygus_grammars/addition/FP32/fp32_full_sum_v1_template.sl",
     "stem": "solution_fp32addition_full_sum_v1"},
    {"name": "fp32_mul_v1",   "target": "fp32_mul",   "component": "full_product_v2", "timeout": 180,
     "template": "sygus_grammars/multiplication/FP32/fp32_full_prod_v1_template.sl",
     "stem": "solution_fp32multiplication_full_product_v1"},
    # --- V2 combined (monolithic grammar, tight structural sketch) ---
    {"name": "mxint8_add_combined", "target": "mxint8_add", "component": "full_sum_v2",     "timeout": 180},
    {"name": "mxint8_mul_combined", "target": "mxint8_mul", "component": "full_product_v2", "timeout": 60},
    {"name": "fp32_add_combined",   "target": "fp32_add",   "component": "full_sum_v2",     "timeout": 60},
    {"name": "fp32_mul_combined",   "target": "fp32_mul",   "component": "full_product_v2", "timeout": 60},
]

NUM_ITERATIONS = 30

results = []

print(f"Running synthesis+accuracy pipeline for {len(JOBS)} jobs")
print(f"NUM_ITERATIONS={NUM_ITERATIONS}, FP32_AUTO_RELAX=OFF\n")

for job in JOBS:
    print(f"\n{'='*60}")
    print(f"=== {job['name']}  (timeout={job['timeout']}s, iters={NUM_ITERATIONS}) ===")
    print(f"{'='*60}")

    env = os.environ.copy()
    env.update({
        "SYNTH_TARGET":                    job["target"],
        "SYNTH_COMPONENT":                 job["component"],
        "SYNTH_RUN_IMPL":                  "1",
        "SYNTH_RUN_ACCURACY":              "1",
        "SYNTH_ENABLE_DIRECTED_IO":        "1",
        "SYNTH_NUM_ITERATIONS":            str(NUM_ITERATIONS),
        "SYNTH_SOLVER_TIMEOUT":            str(job["timeout"]),
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH": "0",
        "SYNTH_FP32_RELAX_ON_TIMEOUT":     "0",
        "SYNTH_FP32_RELAX_ON_INFEASIBLE":  "0",
        "SYNTH_FP32_RELAX_ON_FAIL":        "0",
        "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "0",
    })
    if job.get("template"):
        env["SYNTH_TEMPLATE_OVERRIDE"] = job["template"]
    if job.get("stem"):
        env["SYNTH_SOLUTION_STEM"] = job["stem"]

    proc = subprocess.run(
        [sys.executable, "-m", "src.synthesis_driver"],
        cwd=ROOT, env=env, text=True,
    )

    status = "PASS" if proc.returncode == 0 else "FAIL"
    results.append({"name": job["name"], "returncode": proc.returncode, "status": status})
    print(f"\n[{status}] {job['name']} exited with code {proc.returncode}")

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
