import argparse
import csv
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class GrammarBenchmark:
    key: str
    synth_target: str
    component: str          # V1/V2 combined component (e.g. "full_sum_v2")
    v2_template: str
    subcomp_component: str = ""  # Subcomponent top-level component (e.g. "full_sum"); "" = no subcomponent variant
    template: str = ""      # Per-benchmark template override for sweep runs ("" = use synthesis target default)
    min_timeout: int = 0    # Minimum solver timeout for this benchmark; 0 = no floor (used by HP sweep for V1)


BENCHMARKS: tuple[GrammarBenchmark, ...] = (
    GrammarBenchmark(
        key="mxint8_add",
        synth_target="mxint8_add",
        component="full_sum_v2",
        v2_template="sygus_grammars/addition/MXINT8/mxint8_add_full_sum_v2_template.sl",
        subcomp_component="full_sum",
    ),
    GrammarBenchmark(
        key="mxint8_mul",
        synth_target="mxint8_mul",
        component="full_product_v2",
        v2_template="sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_v2_template.sl",
        subcomp_component="full_product",
    ),
    GrammarBenchmark(
        key="fp32_add",
        synth_target="fp32_add",
        component="full_sum_v2",
        v2_template="sygus_grammars/addition/FP32/fp32_full_sum_v2_template.sl",
        subcomp_component="full_sum",
    ),
    GrammarBenchmark(
        key="fp32_mul",
        synth_target="fp32_mul",
        component="full_product_v2",
        v2_template="sygus_grammars/multiplication/FP32/fp32_full_prod_v2_template.sl",
        subcomp_component="full_product",
    ),
)

# Grammar template files used by each subcomponent chain (in synthesis order).
# Includes the top-level template that assembles the subcomponents.
SUBCOMPONENT_GRAMMAR_FILES: dict[str, list[str]] = {
    "mxint8_add": [
        "sygus_grammars/addition/MXINT8/mxint8_add_alignment_template.sl",
        "sygus_grammars/addition/MXINT8/mxint8_add_raw_sum_template.sl",
        "sygus_grammars/addition/MXINT8/mxint8_add_detect_overflow_template.sl",
        "sygus_grammars/addition/MXINT8/mxint8_add_normalisation_template.sl",
        "sygus_grammars/addition/MXINT8/mxint8_add_full_sum_template.sl",
    ],
    "mxint8_mul": [
        "sygus_grammars/multiplication/MXINT8/mxint8_mult_renorm_flag_template.sl",
        "sygus_grammars/multiplication/MXINT8/mxint8_mult_exp_template.sl",
        "sygus_grammars/multiplication/MXINT8/mxint8_mult_mant_template.sl",
        "sygus_grammars/multiplication/MXINT8/mxint8_mult_full_product_template.sl",
    ],
    "fp32_add": [
        "sygus_grammars/addition/FP32/fp32_alignment_template.sl",
        "sygus_grammars/addition/FP32/fp32_raw_sum_template.sl",
        "sygus_grammars/addition/FP32/fp32_normalisation_template.sl",
        "sygus_grammars/addition/FP32/fp32_full_sum_template.sl",
    ],
    "fp32_mul": [
        "sygus_grammars/multiplication/FP32/fp32_mult_renorm_template.sl",
        "sygus_grammars/multiplication/FP32/fp32_mult_round_carry_template.sl",
        "sygus_grammars/multiplication/FP32/fp32_mult_exp_template.sl",
        "sygus_grammars/multiplication/FP32/fp32_mult_mant_template.sl",
        "sygus_grammars/multiplication/FP32/fp32_full_prod_template.sl",
    ],
}

# Component keys stored in summary["components"] for each subcomponent chain.
SUBCOMPONENT_COMPONENT_KEYS: dict[str, list[str]] = {
    "mxint8_add": ["alignment", "raw_sum", "overflow", "normalisation", "full_sum"],
    "mxint8_mul": ["renorm_flag", "exp", "mant", "full_product"],
    "fp32_add":   ["alignment", "raw_sum", "normalisation", "full_sum"],
    "fp32_mul":   ["renorm", "round_carry", "exp", "mant", "full_product"],
}


def _strip_comments(text: str) -> str:
    return re.sub(r";[^\n]*", "", text)


def _tokenize_sexpr(text: str) -> list[str]:
    return re.findall(r"\(|\)|[^\s()]+", _strip_comments(text))


def _parse_sexpr_tokens(tokens: list[str], pos: int = 0) -> tuple[Any, int]:
    if tokens[pos] != "(":
        return tokens[pos], pos + 1
    out: list[Any] = []
    pos += 1
    while pos < len(tokens) and tokens[pos] != ")":
        node, pos = _parse_sexpr_tokens(tokens, pos)
        out.append(node)
    if pos >= len(tokens):
        raise ValueError("Unbalanced S-expression while parsing grammar template.")
    return out, pos + 1


def _parse_all_sexprs(text: str) -> list[Any]:
    tokens = _tokenize_sexpr(text)
    out: list[Any] = []
    pos = 0
    while pos < len(tokens):
        node, pos = _parse_sexpr_tokens(tokens, pos)
        out.append(node)
    return out


def _sexpr_contains_symbol(node: Any, symbol: str) -> bool:
    if isinstance(node, str):
        return node == symbol
    if isinstance(node, list):
        return any(_sexpr_contains_symbol(child, symbol) for child in node)
    return False


def analyze_sygus_grammar(path: Path) -> dict[str, Any]:
    roots = _parse_all_sexprs(path.read_text())
    synth_fun = next(
        (node for node in roots if isinstance(node, list) and node and node[0] == "synth-fun"),
        None,
    )
    if synth_fun is None or len(synth_fun) < 6:
        raise ValueError(f"Could not locate a well-formed synth-fun in {path}.")

    grammar_rules = synth_fun[5]
    if not isinstance(grammar_rules, list):
        raise ValueError(f"Malformed grammar rules block in {path}.")

    productions_per_nonterminal: dict[str, int] = {}
    constant_nonterminals: set[str] = set()
    self_recursive_nonterminals: set[str] = set()
    for entry in grammar_rules:
        if not isinstance(entry, list) or len(entry) < 3:
            continue
        nt_name = str(entry[0])
        productions = entry[2]
        prod_count = len(productions) if isinstance(productions, list) else 1
        productions_per_nonterminal[nt_name] = prod_count
        prod_items = productions if isinstance(productions, list) else [productions]
        for prod in prod_items:
            if isinstance(prod, list) and prod and prod[0] == "Constant":
                constant_nonterminals.add(nt_name)
            if _sexpr_contains_symbol(prod, nt_name):
                self_recursive_nonterminals.add(nt_name)

    branching = {k: v for k, v in productions_per_nonterminal.items() if v > 1}
    search_space_proxy = 1
    for count in branching.values():
        search_space_proxy *= count

    return {
        "grammar_path": str(path),
        "nonterminals": len(productions_per_nonterminal),
        "total_productions": sum(productions_per_nonterminal.values()),
        "branching_nonterminals": len(branching),
        "single_production_nonterminals": sum(1 for v in productions_per_nonterminal.values() if v == 1),
        "productions_per_nonterminal": productions_per_nonterminal,
        "has_constant_production": bool(constant_nonterminals),
        "constant_nonterminals": sorted(constant_nonterminals),
        "has_self_recursive_nonterminal": bool(self_recursive_nonterminals),
        "self_recursive_nonterminals": sorted(self_recursive_nonterminals),
        "search_space_proxy_is_lower_bound": bool(constant_nonterminals or self_recursive_nonterminals),
        "search_space_proxy": str(search_space_proxy),
    }


def _aggregate_subcomponent_grammar_metrics(paths: list[Path]) -> dict[str, Any]:
    """Aggregate grammar metrics across all subcomponent template files."""
    all_metrics = [analyze_sygus_grammar(p) for p in paths]
    return {
        "grammar_path": ";".join(str(p) for p in paths),
        "nonterminals": sum(m["nonterminals"] for m in all_metrics),
        "total_productions": sum(m["total_productions"] for m in all_metrics),
        "branching_nonterminals": sum(m["branching_nonterminals"] for m in all_metrics),
        "single_production_nonterminals": sum(m["single_production_nonterminals"] for m in all_metrics),
        "has_constant_production": any(m["has_constant_production"] for m in all_metrics),
        "constant_nonterminals": sorted({nt for m in all_metrics for nt in m["constant_nonterminals"]}),
        "has_self_recursive_nonterminal": any(m["has_self_recursive_nonterminal"] for m in all_metrics),
        "self_recursive_nonterminals": sorted({nt for m in all_metrics for nt in m["self_recursive_nonterminals"]}),
        "search_space_proxy_is_lower_bound": any(m["search_space_proxy_is_lower_bound"] for m in all_metrics),
        "search_space_proxy": str(sum(int(m["search_space_proxy"]) for m in all_metrics)),
    }


def _aggregate_subcomponent_comp_metrics(summary: dict[str, Any], component_keys: list[str]) -> dict[str, Any]:
    """Aggregate component-level metrics across all subcomponent entries in a summary."""
    comps = summary.get("components", {})
    all_solved = all(comps.get(k, {}).get("solution_found", False) for k in component_keys)
    statuses = [comps.get(k, {}).get("solve_status", "unknown") for k in component_keys]
    if all(s == "solved" for s in statuses):
        solve_status = "solved"
    elif any(s == "timeout" for s in statuses):
        solve_status = "timeout"
    else:
        first_non_solved = next((s for s in statuses if s != "solved"), "unknown")
        solve_status = first_non_solved

    def _safe_sum(field: str) -> float:
        return sum(comps.get(k, {}).get(field) or 0 for k in component_keys)

    return {
        "solve_status": solve_status,
        "solution_found": all_solved,
        "accepted_constraints": int(_safe_sum("accepted_constraints")),
        "total_constraints": int(_safe_sum("total_constraints")),
        "solver_attempts": int(_safe_sum("solver_attempts")),
        "solver_runtime_seconds_total": _safe_sum("solver_runtime_seconds_total"),
        "solver_runtime_seconds_max": max(
            (comps.get(k, {}).get("solver_runtime_seconds_max") or 0 for k in component_keys), default=0
        ),
        "enum_count_primary_total": int(_safe_sum("enum_count_primary_total")),
        "enum_count_primary_last": None,
        "enum_primary_keys_seen": [],
    }


def _default_v1_from_v2(v2_path: str) -> str:
    """Derive V1 template path from V2 path by replacing '_v2' with '_v1'."""
    p = Path(v2_path)
    new_name = p.name.replace("_v2_template", "_v1_template").replace("_v2.", "_v1.")
    return str(p.with_name(new_name))


def load_variant_manifest(manifest_path: Path | None) -> dict[str, dict[str, str]]:
    manifest: dict[str, dict[str, str]] = {}
    for bench in BENCHMARKS:
        manifest[bench.key] = {
            "V1": _default_v1_from_v2(bench.v2_template),
            "V2": bench.v2_template,
        }

    if manifest_path is None or not manifest_path.exists():
        return manifest

    user_manifest = json.loads(manifest_path.read_text())
    for bench_key, variants in user_manifest.items():
        if bench_key not in manifest or not isinstance(variants, dict):
            continue
        for version in ("V1", "V2"):
            if version in variants:
                manifest[bench_key][version] = str(variants[version])
    return manifest


def _summary_float(value: Any) -> float | None:
    if isinstance(value, (int, float)):
        return float(value)
    return None


def _flatten_run_summary(
    bench: GrammarBenchmark,
    version: str,
    repetition: int,
    template_path: Path | None,
    grammar_metrics: dict[str, Any],
    summary: dict[str, Any],
    driver_returncode: int,
    comp_override: dict[str, Any] | None = None,
    num_subcomponents: int = 1,
) -> dict[str, Any]:
    comp = comp_override if comp_override is not None else summary.get("components", {}).get(bench.component, {})
    hardware = summary.get("hardware", {}) if isinstance(summary.get("hardware"), dict) else {}
    accuracy = summary.get("accuracy", {}) if isinstance(summary.get("accuracy"), dict) else {}

    row: dict[str, Any] = {
        "benchmark": bench.key,
        "synth_target": bench.synth_target,
        "component": bench.component if comp_override is None else bench.subcomp_component,
        "grammar_version": version,
        "num_subcomponents": num_subcomponents,
        "repetition": repetition,
        "template_path": str(template_path) if template_path is not None else "",
        "driver_returncode": driver_returncode,
        "run_status": summary.get("status", "unknown"),
        "component_solve_status": comp.get("solve_status", "unknown"),
        "solution_found": bool(comp.get("solution_found", False)),
        "accepted_constraints": comp.get("accepted_constraints", -1),
        "total_constraints": comp.get("total_constraints", -1),
        "solver_attempts": comp.get("solver_attempts", -1),
        "solver_runtime_seconds_total": comp.get("solver_runtime_seconds_total", -1.0),
        "solver_runtime_seconds_max": comp.get("solver_runtime_seconds_max", -1.0),
        "enum_count_primary_total": comp.get("enum_count_primary_total"),
        "enum_count_primary_last": comp.get("enum_count_primary_last"),
        "enum_primary_keys_seen": ";".join(comp.get("enum_primary_keys_seen", [])),
        "nonterminals": grammar_metrics["nonterminals"],
        "total_productions": grammar_metrics["total_productions"],
        "branching_nonterminals": grammar_metrics["branching_nonterminals"],
        "single_production_nonterminals": grammar_metrics["single_production_nonterminals"],
        "has_constant_production": grammar_metrics["has_constant_production"],
        "constant_nonterminals": ";".join(grammar_metrics["constant_nonterminals"]),
        "has_self_recursive_nonterminal": grammar_metrics["has_self_recursive_nonterminal"],
        "self_recursive_nonterminals": ";".join(grammar_metrics["self_recursive_nonterminals"]),
        "search_space_proxy_is_lower_bound": grammar_metrics["search_space_proxy_is_lower_bound"],
        "search_space_proxy": grammar_metrics["search_space_proxy"],
        "random_seed": summary.get("config", {}).get("random_seed", -1),
        "accuracy_exact_match": accuracy.get("accuracy_exact_match", -1.0),
        "within_rel_pct": accuracy.get("within_rel_pct", -1.0),
        "within_rel_threshold_pct": accuracy.get("within_rel_threshold_pct", -1.0),
        "abs_err_avg": accuracy.get("abs_err_avg", -1.0),
        "abs_err_p99": accuracy.get("abs_err_p99", -1.0),
        "abs_err_max": accuracy.get("abs_err_max", -1.0),
        "ulp_avg": accuracy.get("ulp_avg", -1.0),
        "ulp_p99": accuracy.get("ulp_p99", -1),
        "ulp_max": accuracy.get("ulp_max", -1),
        "cocotb_passed": accuracy.get("cocotb_passed", False),
        "LUTs": hardware.get("LUTs", -1),
        "FFs": hardware.get("FFs", -1),
        "DSPs": hardware.get("DSPs", -1),
        "BRAMs": hardware.get("BRAMs", -1),
        "Cycles": hardware.get("Cycles", -1),
        "Fmax_MHz": hardware.get("Fmax_MHz", -1),
        "Latency_ns": hardware.get("Latency_ns", -1),
        "summary_path": summary.get("_summary_path", ""),
        "log_path": summary.get("_log_path", ""),
    }
    return row


def _mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / float(len(values))


def build_aggregate_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for row in rows:
        grouped.setdefault((row["benchmark"], row["grammar_version"]), []).append(row)

    by_benchmark: dict[str, dict[str, dict[str, Any]]] = {}
    for (benchmark, version), items in grouped.items():
        runtimes = [_summary_float(r["solver_runtime_seconds_total"]) for r in items]
        runtimes = [x for x in runtimes if x is not None and x >= 0]
        enums = [_summary_float(r["enum_count_primary_total"]) for r in items]
        enums = [x for x in enums if x is not None and x >= 0]

        agg = {
            "benchmark": benchmark,
            "grammar_version": version,
            "num_subcomponents": items[0].get("num_subcomponents", 1),
            "runs": len(items),
            "solve_successes": sum(1 for r in items if r.get("solution_found")),
            "solve_rate": sum(1 for r in items if r.get("solution_found")) / float(len(items)),
            "mean_runtime_seconds": _mean(runtimes),
            "mean_enum_count": _mean(enums),
            "nonterminals": items[0]["nonterminals"],
            "total_productions": items[0]["total_productions"],
            "branching_nonterminals": items[0]["branching_nonterminals"],
            "has_constant_production": items[0]["has_constant_production"],
            "has_self_recursive_nonterminal": items[0]["has_self_recursive_nonterminal"],
            "search_space_proxy_is_lower_bound": items[0]["search_space_proxy_is_lower_bound"],
            "search_space_proxy": items[0]["search_space_proxy"],
            "mean_accuracy_exact_match": _mean([
                float(r["accuracy_exact_match"])
                for r in items
                if isinstance(r.get("accuracy_exact_match"), (int, float)) and float(r["accuracy_exact_match"]) >= 0.0
            ]),
            "mean_within_rel_pct": _mean([
                float(r["within_rel_pct"])
                for r in items
                if isinstance(r.get("within_rel_pct"), (int, float)) and float(r["within_rel_pct"]) >= 0.0
            ]),
            "mean_LUTs": _mean([
                float(r["LUTs"])
                for r in items
                if isinstance(r.get("LUTs"), (int, float)) and float(r["LUTs"]) >= 0.0
            ]),
            "mean_Fmax_MHz": _mean([
                float(r["Fmax_MHz"])
                for r in items
                if isinstance(r.get("Fmax_MHz"), (int, float)) and float(r["Fmax_MHz"]) >= 0.0
            ]),
            "mean_Latency_ns": _mean([
                float(r["Latency_ns"])
                for r in items
                if isinstance(r.get("Latency_ns"), (int, float)) and float(r["Latency_ns"]) >= 0.0
            ]),
        }
        by_benchmark.setdefault(benchmark, {})[version] = agg

    out: list[dict[str, Any]] = []
    for benchmark, variants in sorted(by_benchmark.items()):
        v1 = variants.get("V1")
        for version in ("V1", "V2", "Subcomponents"):
            if version not in variants:
                continue
            row = dict(variants[version])
            if version == "V2" and v1:
                cur_rt = row.get("mean_runtime_seconds")
                v1_rt = v1.get("mean_runtime_seconds")
                cur_enum = row.get("mean_enum_count")
                v1_enum = v1.get("mean_enum_count")
                row["runtime_ratio_vs_v1"] = (
                    v1_rt / cur_rt if isinstance(cur_rt, (int, float)) and cur_rt not in {0, None}
                    and isinstance(v1_rt, (int, float)) else None
                )
                row["enum_ratio_vs_v1"] = (
                    v1_enum / cur_enum if isinstance(cur_enum, (int, float)) and cur_enum not in {0, None}
                    and isinstance(v1_enum, (int, float)) else None
                )
            if version == "Subcomponents" and v1:
                cur_rt = row.get("mean_runtime_seconds")
                v1_rt = v1.get("mean_runtime_seconds")
                cur_enum = row.get("mean_enum_count")
                v1_enum = v1.get("mean_enum_count")
                row["runtime_ratio_vs_v1"] = (
                    v1_rt / cur_rt if isinstance(cur_rt, (int, float)) and cur_rt not in {0, None}
                    and isinstance(v1_rt, (int, float)) else None
                )
                row["enum_ratio_vs_v1"] = (
                    v1_enum / cur_enum if isinstance(cur_enum, (int, float)) and cur_enum not in {0, None}
                    and isinstance(v1_enum, (int, float)) else None
                )
            out.append(row)
    return out


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    keys: list[str] = []
    seen: set[str] = set()
    for row in rows:
        for key in row.keys():
            if key not in seen:
                seen.add(key)
                keys.append(key)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)


def _run_and_tee(cmd: list[str], cwd: Path, env: dict[str, str], log_path: Path) -> subprocess.CompletedProcess[str]:
    with log_path.open("w") as log_file:
        proc = subprocess.Popen(
            cmd,
            cwd=cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        collected: list[str] = []
        assert proc.stdout is not None
        for line in proc.stdout:
            collected.append(line)
            print(line, end="")
            log_file.write(line)
        returncode = proc.wait()
    return subprocess.CompletedProcess(cmd, returncode, "".join(collected), "")


def run_driver_once(
    repo_root: Path,
    bench: GrammarBenchmark,
    version: str,
    repetition: int,
    template_path: Path | None,
    out_dir: Path,
    args: argparse.Namespace,
    run_index: int,
    total_runs: int,
    synth_component_override: str = "",
    timeout_override: int | None = None,
) -> tuple[dict[str, Any], int]:
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    summary_path = raw_dir / f"{bench.key}_{version.lower()}_r{repetition:02d}.json"
    log_path = raw_dir / f"{bench.key}_{version.lower()}_r{repetition:02d}.log"
    solution_stem = f"grammarstudy_{bench.key}_{version.lower()}_r{repetition:02d}"
    run_seed = args.seed + repetition - 1 + (args.benchmark_order[bench.key] * 1000)

    synth_component = synth_component_override if synth_component_override else bench.component
    effective_timeout = timeout_override if timeout_override is not None else args.timeout

    env = os.environ.copy()
    env.update({
        "SYNTH_TARGET": bench.synth_target,
        "SYNTH_COMPONENT": synth_component,
        "SYNTH_TEMPLATE_OVERRIDE": str(template_path) if template_path is not None else "",
        "SYNTH_SOLVER_TIMEOUT": str(effective_timeout),
        "SYNTH_NUM_ITERATIONS": str(args.num_iterations),
        "SYNTH_RUN_IMPL": "1" if args.run_impl else "0",
        "SYNTH_RUN_ACCURACY": "1" if args.run_accuracy else "0",
        "SYNTH_ENABLE_DIRECTED_IO": "1" if args.directed_io else "0",
        "SYNTH_ENABLE_SYGUS_DUMP": "0",
        "SYNTH_ENABLE_SYGUS_FAST_ENUM": "1" if args.sygus_fast_enum else "0",
        "SYNTH_ENABLE_SYGUS_PBE": "1" if args.sygus_pbe else "0",
        "SYNTH_ENABLE_SYGUS_SYM_BREAK_PBE": "1" if args.sygus_sym_break_pbe else "0",
        "SYNTH_MXINT8_AUTO_RELAX_OUTPUT_MATCH": "0",
        "SYNTH_MXINT8_RELAX_ON_TIMEOUT": "0",
        "SYNTH_MXINT8_RELAX_ON_INFEASIBLE": "0",
        "SYNTH_MXINT8_RELAX_ON_FAIL": "0",
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH": "0",
        "SYNTH_FP32_RELAX_ON_TIMEOUT": "0",
        "SYNTH_FP32_TIMEOUT_RETRY_ONCE": "0",
        "SYNTH_FP32_RELAX_ON_INFEASIBLE": "0",
        "SYNTH_FP32_RELAX_ON_FAIL": "0",
        "SYNTH_FP32_OUTPUT_MATCH_MSB_BITS": str(args.fp32_output_match_msb_bits),
        "SYNTH_FP32_STAGE_MANTISSA_BITS": str(args.fp32_stage_mantissa_bits),
        "SYNTH_FP32_MUL_MODE": args.fp32_mul_mode,
        "SYNTH_SUMMARY_PATH": str(summary_path),
        "SYNTH_SOLUTION_STEM": solution_stem,
        "SYNTH_RANDOM_SEED": str(run_seed),
        "PYTHONHASHSEED": str(run_seed),
    })

    cmd = [sys.executable, "-m", "src.synthesis_driver"]
    template_str = str(template_path) if template_path is not None else "(driver default)"
    print(
        f"[RUN {run_index}/{total_runs}] benchmark={bench.key} grammar={version} repetition={repetition} "
        f"seed={run_seed} template={template_str}"
    )
    start = time.time()
    proc = _run_and_tee(cmd, cwd=repo_root, env=env, log_path=log_path)
    elapsed = time.time() - start

    if not summary_path.exists():
        print(
            f"[RUN {run_index}/{total_runs} DONE] benchmark={bench.key} grammar={version} repetition={repetition} "
            f"status=missing_summary returncode={proc.returncode} elapsed={elapsed:.2f}s"
        )
        return {
            "_summary_path": str(summary_path),
            "_log_path": str(log_path),
            "status": "missing_summary",
            "error": "Expected synthesis summary JSON was not produced.",
            "config": {"random_seed": run_seed},
        }, proc.returncode

    summary = json.loads(summary_path.read_text())
    summary["_summary_path"] = str(summary_path)
    summary["_log_path"] = str(log_path)
    # Use subcomp_component key for subcomponent runs, combined component otherwise.
    lookup_component = synth_component_override if synth_component_override else bench.component
    comp = summary.get("components", {}).get(lookup_component, {})
    accepted = comp.get("accepted_constraints", "?")
    total = comp.get("total_constraints", "?")
    solve_status = comp.get("solve_status", summary.get("status", "unknown"))
    print(
        f"[RUN {run_index}/{total_runs} DONE] benchmark={bench.key} grammar={version} repetition={repetition} "
        f"status={solve_status} accepted={accepted}/{total} returncode={proc.returncode} elapsed={elapsed:.2f}s"
    )
    return summary, proc.returncode


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run V1 vs V2 vs Subcomponents grammar selection experiments."
    )
    parser.add_argument("--output-dir", default="results/grammar_selection", help="Experiment output directory.")
    parser.add_argument("--variant-manifest", default="", help="Optional JSON manifest overriding V1/V2 template paths.")
    parser.add_argument("--benchmarks", nargs="+", default=[], help="Optional benchmark keys to run. Defaults to all.")
    parser.add_argument("--versions", nargs="+", default=[], help="Optional grammar versions to run (V1, V2, Subcomponents). Defaults to all.")
    parser.add_argument("--repetitions", type=int, default=1, help="Number of repetitions per benchmark/version.")
    parser.add_argument("--seed", type=int, default=12345, help="Base RNG seed. Same seed is used for V1/V2 within a repetition.")
    parser.add_argument("--timeout", type=int, default=120, help="Per-driver solver timeout in seconds.")
    parser.add_argument("--v1-timeout", type=int, default=None, help="Solver timeout for V1 grammar runs (overrides --timeout for V1 only).")
    parser.add_argument("--num-iterations", type=int, default=30, help="Synthesis iterations per run.")
    parser.add_argument("--run-impl", action=argparse.BooleanOptionalAction, default=True, help="Run post-implementation flow.")
    parser.add_argument("--run-accuracy", action=argparse.BooleanOptionalAction, default=True, help="Run cocotb accuracy.")
    parser.add_argument("--directed-io", action=argparse.BooleanOptionalAction, default=True, help="Freeze directed IO constraints on/off for all runs.")
    parser.add_argument("--sygus-fast-enum", action=argparse.BooleanOptionalAction, default=False, help="Freeze cvc5 --sygus-enum=fast.")
    parser.add_argument("--sygus-pbe", action=argparse.BooleanOptionalAction, default=True, help="Freeze cvc5 --sygus-pbe.")
    parser.add_argument("--sygus-sym-break-pbe", action=argparse.BooleanOptionalAction, default=True, help="Freeze cvc5 --sygus-sym-break-pbe.")
    parser.add_argument("--fp32-output-match-msb-bits", type=int, default=32)
    parser.add_argument("--fp32-stage-mantissa-bits", type=int, default=15)
    parser.add_argument("--fp32-mul-mode", default="default", choices=["default", "wide", "small"])
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    output_dir = Path(args.output_dir).expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    manifest_path = Path(args.variant_manifest).expanduser().resolve() if args.variant_manifest else None
    variant_manifest = load_variant_manifest(manifest_path)
    selected_benchmarks = list(BENCHMARKS)
    if args.benchmarks:
        wanted = set(args.benchmarks)
        selected_benchmarks = [bench for bench in BENCHMARKS if bench.key in wanted]
        missing = sorted(wanted - {bench.key for bench in selected_benchmarks})
        if missing:
            valid = ", ".join(sorted(bench.key for bench in BENCHMARKS))
            raise ValueError(f"Unknown benchmark key(s): {', '.join(missing)}. Valid: {valid}")
    args.benchmark_order = {bench.key: idx for idx, bench in enumerate(selected_benchmarks)}

    # Version filtering
    selected_versions = set(args.versions) if args.versions else {"V1", "V2", "Subcomponents"}
    valid_versions = {"V1", "V2", "Subcomponents"}
    invalid = selected_versions - valid_versions
    if invalid:
        raise ValueError(f"Unknown version(s): {', '.join(sorted(invalid))}. Valid: {', '.join(sorted(valid_versions))}")

    all_rows: list[dict[str, Any]] = []
    raw_jsonl = output_dir / "runs.jsonl"
    # Append mode: don't delete if other sessions may be writing to the same dir
    if raw_jsonl.exists() and not args.versions:
        raw_jsonl.unlink()

    # Count runs
    def _versions_for_bench(bench):
        v = []
        if "V1" in selected_versions: v.append("V1")
        if "V2" in selected_versions: v.append("V2")
        if "Subcomponents" in selected_versions and bench.subcomp_component: v.append("Subcomponents")
        return v

    total_runs = sum(len(_versions_for_bench(b)) for b in selected_benchmarks) * args.repetitions
    run_index = 0

    for bench in selected_benchmarks:
        # --- V1 and V2 combined-grammar runs ---
        for version in ("V1", "V2"):
            if version not in selected_versions:
                continue
            template_path = (repo_root / variant_manifest[bench.key][version]).resolve()
            if not template_path.exists():
                raise FileNotFoundError(
                    f"Missing grammar for {bench.key} {version}: {template_path}\n"
                    "Provide it via --variant-manifest or add the expected file."
                )
            grammar_metrics = analyze_sygus_grammar(template_path)
            v1_timeout = args.v1_timeout if version == "V1" and args.v1_timeout is not None else None
            for repetition in range(1, args.repetitions + 1):
                run_index += 1
                summary, returncode = run_driver_once(
                    repo_root=repo_root,
                    bench=bench,
                    version=version,
                    repetition=repetition,
                    template_path=template_path,
                    out_dir=output_dir,
                    args=args,
                    run_index=run_index,
                    total_runs=total_runs,
                    timeout_override=v1_timeout,
                )
                row = _flatten_run_summary(
                    bench=bench,
                    version=version,
                    repetition=repetition,
                    template_path=template_path,
                    grammar_metrics=grammar_metrics,
                    summary=summary,
                    driver_returncode=returncode,
                    num_subcomponents=1,
                )
                all_rows.append(row)
                with raw_jsonl.open("a") as f:
                    f.write(json.dumps(row, sort_keys=True) + "\n")

        # --- Subcomponents run (uses driver's dependency chain, no template override) ---
        if bench.subcomp_component and "Subcomponents" in selected_versions:
            subcomp_files = [
                (repo_root / rel).resolve()
                for rel in SUBCOMPONENT_GRAMMAR_FILES[bench.synth_target]
            ]
            for f in subcomp_files:
                if not f.exists():
                    raise FileNotFoundError(f"Missing subcomponent grammar: {f}")
            subcomp_keys = SUBCOMPONENT_COMPONENT_KEYS[bench.synth_target]
            grammar_metrics = _aggregate_subcomponent_grammar_metrics(subcomp_files)
            num_subcomponents = len(subcomp_keys)
            version = "Subcomponents"
            for repetition in range(1, args.repetitions + 1):
                run_index += 1
                summary, returncode = run_driver_once(
                    repo_root=repo_root,
                    bench=bench,
                    version=version,
                    repetition=repetition,
                    template_path=None,  # no template override — use driver defaults
                    out_dir=output_dir,
                    args=args,
                    run_index=run_index,
                    total_runs=total_runs,
                    synth_component_override=bench.subcomp_component,
                )
                comp_agg = _aggregate_subcomponent_comp_metrics(summary, subcomp_keys)
                row = _flatten_run_summary(
                    bench=bench,
                    version=version,
                    repetition=repetition,
                    template_path=None,
                    grammar_metrics=grammar_metrics,
                    summary=summary,
                    driver_returncode=returncode,
                    comp_override=comp_agg,
                    num_subcomponents=num_subcomponents,
                )
                all_rows.append(row)
                with raw_jsonl.open("a") as f:
                    f.write(json.dumps(row, sort_keys=True) + "\n")

    _write_csv(output_dir / "runs.csv", all_rows)
    aggregate_rows = build_aggregate_rows(all_rows)
    _write_csv(output_dir / "summary.csv", aggregate_rows)
    (output_dir / "summary.json").write_text(json.dumps(aggregate_rows, indent=2, sort_keys=True) + "\n")

    print(f"[DONE] Wrote run rows to {output_dir / 'runs.csv'}")
    print(f"[DONE] Wrote aggregated summary to {output_dir / 'summary.csv'}")


if __name__ == "__main__":
    main()
