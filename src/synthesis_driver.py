import os, random, math, subprocess, tempfile, re, sys, json, time, logging
from pathlib import Path
from typing import List, Tuple, Dict, Optional, Callable, Literal, Any
from src.dependencies import DEPENDENCY_MAP

from .synthesis_targets.addition.mxint8_addition import MXINT8AdditionTarget
from .synthesis_targets.multiplication.mxint8_multiplication import MXINT8MultiplicationTarget

from .synthesis_targets.addition.fp32_addition import FP32AdditionTarget
from .synthesis_targets.multiplication.fp32_multiplication import FP32MultiplicationTarget
from .synthesis_targets.addition.naive_adder import NaiveAdderTarget
from .synthesis_targets.multiplication.naive_multiplier import NaiveMultiplierTarget

from .synthesis_targets.dot_product import DotProductTarget

# The HLS C++ translation path now assumes current smt2c output and uses only
# the remaining active safe rewrites in translate_to_hls_cpp.py.

# ============================ TWEAKABLE KNOBS ============================
# Change defaults here. Environment variables still override these values.
# =========================================================================
    #
    # Select ONE target operation:
    #   DotProductTarget(), 
    #   MXINT8AdditionTarget(), 
    #   MXINT8MultiplicationTarget(),
    #   FP32AdditionTarget(), 
    #   FP32MultiplicationTarget()
    #
    # =========================================================================
    #
    # Naive baselines:
    #   NaiveAdderTarget(kind="int", width=32|8) or NaiveAdderTarget(kind="fp32")
    #   NaiveMultiplierTarget(kind="int", width=32|8) or NaiveMultiplierTarget(kind="fp32")
    #
    # =========================================================================
    #
    # Components (per target):
    # -----------------------------------------------------------------------------------
    #   MXINT8AdditionTarget:       ["alignment", "raw_sum", "overflow", "normalisation", 
    #                                "full_sum", "full_sum_combined"]
    # -----------------------------------------------------------------------------------
    #   MXINT8MultiplicationTarget: ["renorm_flag", "exp", "mant", "full_product", "full_product_combined"]
    # -----------------------------------------------------------------------------------
    #   FP32AdditionTarget:         ["alignment", "raw_sum", "normalisation",
    #                                "full_sum", "full_sum_combined"]
    # -----------------------------------------------------------------------------------
    #   FP32MultiplicationTarget:   ["renorm", "round_carry", "exp", "mant", "full_product", "full_product_combined"]
    # -----------------------------------------------------------------------------------
    #   NaiveAdderTarget:           ["int_add", "fp32_adder"]
    # -----------------------------------------------------------------------------------
    #   NaiveMultiplierTarget:      ["int_mul", "fp32_mul"]
    # =========================================================================

# Target/component defaults when running `python -m src.synthesis_driver`.
# Use class-style defaults directly (can be switched to any target class instance).
DEFAULT_TARGET_OPERATION = MXINT8MultiplicationTarget()
DEFAULT_COMPONENT = "full_product"

# Pipeline toggles.

# False for a quick post-synthesis estimate (-p),
# True for a full post-implementation run (-i)
DEFAULT_RUN_IMPLEMENTATION = True
# Run cocotb accuracy after HLS/implementation in full pipeline.
DEFAULT_RUN_ACCURACY = True

DEFAULT_ENABLE_DIRECTED_IO_CONSTRAINTS = True
DEFAULT_SHOW_SMT2C_OUTPUT = True

# cvc5 / SyGuS flags.
DEFAULT_ENABLE_SYGUS_DUMP = False
DEFAULT_ENABLE_SYGUS_FAST_ENUM = False
DEFAULT_ENABLE_SYGUS_PBE = True
DEFAULT_ENABLE_SYGUS_SYM_BREAK_PBE = False

# Core synthesis loop defaults.
DEFAULT_SOLVER_TIMEOUT_SECONDS = 120
DEFAULT_NUM_ITERATIONS = 30

# FP32 output-match relaxation defaults.
DEFAULT_FP32_OUTPUT_MATCH_MSB_BITS = 32
DEFAULT_FP32_AUTO_RELAX_OUTPUT_MATCH = True
DEFAULT_FP32_MIN_OUTPUT_MATCH_MSB_BITS = 24
DEFAULT_FP32_OUTPUT_MATCH_STEP = 1
DEFAULT_FP32_RELAX_SCHEDULE = "staged"  # one of: linear, staged
DEFAULT_FP32_STAGE_MANTISSA_BITS = 15
DEFAULT_FP32_RESET_MSB_PER_SAMPLE = True
DEFAULT_FP32_RELAX_ON_TIMEOUT = True
DEFAULT_FP32_TIMEOUT_RETRY_ONCE = False
DEFAULT_FP32_TIMEOUT_RETRY_MULTIPLIER = 4
DEFAULT_FP32_RELAX_ON_INFEASIBLE = True
DEFAULT_FP32_RELAX_ON_FAIL = True
# FP32 multiplication synthesis sampling mode: default | wide | small
DEFAULT_SYNTH_FP32_MUL_MODE = "default"
# FP32 addition synthesis sampling mode: default | wide | small
DEFAULT_SYNTH_FP32_ADD_MODE = "default"
# ========================================================================

# Runtime flags consumed by run_cvc5_synthesis.
ENABLE_SYGUS_DUMP = DEFAULT_ENABLE_SYGUS_DUMP
ENABLE_SYGUS_FAST_ENUM = DEFAULT_ENABLE_SYGUS_FAST_ENUM
ENABLE_SYGUS_PBE = DEFAULT_ENABLE_SYGUS_PBE
ENABLE_SYGUS_SYM_BREAK_PBE = DEFAULT_ENABLE_SYGUS_SYM_BREAK_PBE

# Runtime codegen/debug toggle.
SHOW_SMT2C_OUTPUT = DEFAULT_SHOW_SMT2C_OUTPUT
SolveStatus = Literal["solved", "timeout", "fail", "infeasible", "unknown"]

_CVC5_STAT_LINE_RE = re.compile(
    r"^\s*([A-Za-z0-9_:.\/-]+)\s*(?:=|:)\s*([-+]?\d+(?:\.\d+)?)\s*$",
    re.MULTILINE,
)

_ENUM_KEY_PREFERENCES = (
    "sygus::cegqi::si::enum",
    "SynthEngine::cegqi-si-enum",
    "sygus::enum",
    "enum",
)

def unwrap_extra_parens(solution_text: str) -> str:
    """Remove a single outer s-expression wrapper when present.

    CVC5 usually returns solutions in the form "(define-fun ...)". Occasionally it
    wraps the solution in an extra layer like "(\n(define-fun ...)\n)". We detect
    that pattern by checking for an opening parenthesis with another s-expression as
    the next non-whitespace token, and safely strip only that redundant wrapper.
    """

    stripped = solution_text.strip()
    if not stripped or stripped[0] != '(':
        return stripped

    # Find the first non-whitespace character after the initial "(".
    idx = 1
    length = len(stripped)
    while idx < length and stripped[idx].isspace():
        idx += 1

    # Only unwrap if the next significant token is another "(".
    if idx < length and stripped[idx] == '(' and stripped[-1] == ')':
        return stripped[1:-1].strip()

    return stripped

# Helper functions to read the latest synthesized helper definition so that
# it can be included in the synthesis query of a dependent component/target.
# (Essentially updates any newly synthesised helpers automatically)

def _read_latest(path_glob: str) -> str | None:
    paths = list(Path("results/smt2").glob(path_glob))
    if not paths:
        return None
    paths.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return paths[0].read_text().strip()

def _extract_define_fun_blocks(s: str) -> list[str]:
    blocks, i = [], 0
    while True:
        i = s.find("(define-fun", i)
        if i == -1: break
        depth, j = 0, i
        while j < len(s):
            ch = s[j]
            if ch == "(": depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    blocks.append(s[i:j+1]); i = j + 1; break
            j += 1
        else:
            break
    return blocks

def _block_name(blk: str) -> str:
    m = re.search(r"\(define-fun\s+([A-Za-z0-9_]+)\s*\(", blk)
    return m.group(1) if m else "<unknown>"

def collect_helper_definitions(deps: list[str]) -> str:
    acc, seen = [], set()
    for comp in deps:
        smt = _read_latest(f"solution_{comp}.smt2")
        if not smt:
            raise FileNotFoundError(
                f"Missing helper for {comp} "
                f"(expected results/smt2/solution_{comp}.smt2)."
            )
        # Remove standalone set-logic commands to avoid duplicates.
        smt_clean = re.sub(r"\(set-logic[^\)]*\)\s*", "", smt, flags=re.IGNORECASE)

        for blk in _extract_define_fun_blocks(smt_clean):
            nm = _block_name(blk)
            if nm not in seen:
                seen.add(nm)
                acc.append(blk)
    return "\n\n".join(acc) + "\n"


class SynthesisConfig:
    """Configuration settings for the SyGuS synthesis."""
    
    # MXInt Settings
    MANTISSA_WIDTH: int = 4
    EXPONENT_WIDTH: int = 4
    RAW_SUM_MANTISSA_WIDTH: int = 5 
    
    # Quantization settings
    Q_CONFIG_IN: Dict[str, int] = {"width": 4, "exponent_width": EXPONENT_WIDTH, "round_bits": 0}
    Q_CONFIG_OUT: Dict[str, int] = {"width": 4, "exponent_width": EXPONENT_WIDTH, "round_bits": 0}
    PARALLELISM: List[int] = [1, 1]
    
    # Solver settings
    SOLVER_TIMEOUT_SECONDS: int = DEFAULT_SOLVER_TIMEOUT_SECONDS
    NUM_ITERATIONS: int = DEFAULT_NUM_ITERATIONS

    # FP32 full-output constraint strictness:
    #   32 -> exact 32-bit match
    #   30 -> match top 30 bits (allow 2 LSBs to differ), etc.
    FP32_OUTPUT_MATCH_MSB_BITS: int = DEFAULT_FP32_OUTPUT_MATCH_MSB_BITS
    # If enabled for FP32 addition full-sum components, retry synthesis with
    # progressively fewer required MSBs until a program is found.
    FP32_AUTO_RELAX_OUTPUT_MATCH: bool = DEFAULT_FP32_AUTO_RELAX_OUTPUT_MATCH
    FP32_MIN_OUTPUT_MATCH_MSB_BITS: int = DEFAULT_FP32_MIN_OUTPUT_MATCH_MSB_BITS
    FP32_OUTPUT_MATCH_STEP: int = DEFAULT_FP32_OUTPUT_MATCH_STEP
    FP32_RELAX_SCHEDULE: str = DEFAULT_FP32_RELAX_SCHEDULE
    FP32_STAGE_MANTISSA_BITS: int = DEFAULT_FP32_STAGE_MANTISSA_BITS
    # If true, each new sample starts retrying from the configured strict MSB
    # target (instead of carrying over the previous sample's relaxed value).
    FP32_RESET_MSB_PER_SAMPLE: bool = DEFAULT_FP32_RESET_MSB_PER_SAMPLE
    # If true, treat cvc5 "timeout" as relaxable for this sample.
    FP32_RELAX_ON_TIMEOUT: bool = DEFAULT_FP32_RELAX_ON_TIMEOUT
    # If a solve times out, retry once with a larger timeout before deciding status.
    FP32_TIMEOUT_RETRY_ONCE: bool = DEFAULT_FP32_TIMEOUT_RETRY_ONCE
    FP32_TIMEOUT_RETRY_MULTIPLIER: int = DEFAULT_FP32_TIMEOUT_RETRY_MULTIPLIER
    # If true, treat cvc5 "infeasible" as relaxable for this sample.
    FP32_RELAX_ON_INFEASIBLE: bool = DEFAULT_FP32_RELAX_ON_INFEASIBLE
    # If true, treat cvc5 "fail" as relaxable for this sample.
    FP32_RELAX_ON_FAIL: bool = DEFAULT_FP32_RELAX_ON_FAIL
    

# For the grammar selection study comparing V1 to V2 templates
def _parse_cvc5_stats(stderr_text: str) -> dict[str, Any]:
    stats_text = (stderr_text or "").strip()
    stats_map: dict[str, int | float] = {}
    enum_matches: list[dict[str, Any]] = []

    for m in _CVC5_STAT_LINE_RE.finditer(stats_text):
        key = m.group(1).strip()
        raw_val = m.group(2).strip()
        value: int | float
        try:
            value = int(raw_val)
        except ValueError:
            try:
                value = float(raw_val)
            except ValueError:
                continue
        stats_map[key] = value
        if "enum" in key.lower():
            enum_matches.append({"key": key, "value": value})

    primary_key = None
    primary_value: int | float | None = None
    for preferred in _ENUM_KEY_PREFERENCES:
        if preferred in stats_map:
            primary_key = preferred
            primary_value = stats_map[preferred]
            break
    if primary_key is None and enum_matches:
        best = max(
            enum_matches,
            key=lambda item: float(item["value"]) if isinstance(item["value"], (int, float)) else float("-inf"),
        )
        primary_key = str(best["key"])
        primary_value = best["value"]

    return {
        "stats_raw": stats_text,
        "stats_map": stats_map,
        "enum_matches": enum_matches,
        "enum_count_primary_key": primary_key,
        "enum_count_primary": primary_value,
    }


def _template_override_for_component(component_name: str) -> str | None:
    env_key = "SYNTH_TEMPLATE_OVERRIDE_" + re.sub(r"[^A-Za-z0-9]+", "_", component_name).upper()
    override = os.getenv(env_key, "").strip()
    if override:
        return override
    generic = os.getenv("SYNTH_TEMPLATE_OVERRIDE", "").strip()
    return generic or None


def run_cvc5_synthesis(sygus_query: str, timeout: int) -> Tuple[Optional[str], SolveStatus, dict[str, Any]]:
  
    with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=".sl") as temp_f:
        temp_f.write(sygus_query)
        temp_filepath = temp_f.name
        
    cmd = ["cvc5", "--lang=sygus2"]
    if ENABLE_SYGUS_PBE:
        cmd.append("--sygus-pbe")
        if ENABLE_SYGUS_SYM_BREAK_PBE:
            cmd.append("--sygus-sym-break-pbe")
    if ENABLE_SYGUS_FAST_ENUM:
        cmd.append("--sygus-enum=fast")
    if ENABLE_SYGUS_DUMP:
        cmd += ["-o", "sygus"]
    cmd.append("--stats")
    cmd.append("--stats-internal")
    cmd.append(temp_filepath)
    t0 = time.perf_counter()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True, text=True, timeout=timeout
        )
        runtime_seconds = time.perf_counter() - t0
        if result.stderr:
            logging.debug("CVC5 STDERR:\n%s", result.stderr)
        meta = {
            "timeout_seconds": timeout,
            "runtime_seconds": runtime_seconds,
            **_parse_cvc5_stats(result.stderr or ""),
        }

        solution_text = (result.stdout or "").strip()
        if "(define-fun" in solution_text:
            # CVC5 sometimes wraps the solution in an extra top-level s-expression
            # like "(\n(define-fun ...)\n)", which complicates downstream parsing.
            # We remove that outer wrapper while keeping the inner definitions intact.
            solution_text = unwrap_extra_parens(solution_text)
            return solution_text, "solved", meta

        norm = solution_text.lower()
        if norm == "fail":
            return None, "fail", meta
        if norm == "infeasible":
            return None, "infeasible", meta

        print(f"[CVC5] Solver did not return a valid solution.\n[STDOUT]:\n{solution_text}")
        return None, "unknown", meta

    except subprocess.TimeoutExpired as exc:
        runtime_seconds = time.perf_counter() - t0
        print(f"[CVC5] Solver timed out after {timeout} seconds.")
        stderr_text = (exc.stderr or "") if hasattr(exc, "stderr") else ""
        meta = {
            "timeout_seconds": timeout,
            "runtime_seconds": runtime_seconds,
            **_parse_cvc5_stats(stderr_text),
        }
        return None, "timeout", meta
    except FileNotFoundError:
        print("[ERROR] 'cvc5' command not found.")
        meta = {
            "timeout_seconds": timeout,
            "runtime_seconds": 0.0,
            **_parse_cvc5_stats(""),
        }
        return None, "unknown", meta
    finally:
    
        if os.path.exists(temp_filepath):
            os.remove(temp_filepath)
            

def synthesis_loop(
    target, 
    component_name: str,
    test_cases: List[Tuple[float, float]],
    config: SynthesisConfig
) -> Tuple[Optional[str], dict[str, Any]]:
    try:
        component = target.get_components()[component_name]
        template_file = component["template"]
        template_override = _template_override_for_component(component_name)
        if template_override:
            template_file = template_override
        constraint_generator = component["generator"]
    except KeyError:
        print(f"[ERROR] Component '{component_name}' not found for target '{target.__class__.__name__}'.")
        print(f"Available components are: {list(target.get_components().keys())}")
        return None, {
            "component": component_name,
            "template_file": "",
            "solution_found": False,
            "accepted_constraints": 0,
            "total_constraints": len(test_cases),
            "solve_status": "unknown",
            "solver_attempts": 0,
            "solver_runtime_seconds_total": 0.0,
            "solver_runtime_seconds_max": 0.0,
            "enum_count_primary_total": None,
            "enum_count_primary_last": None,
            "enum_primary_keys_seen": [],
            "attempt_status_counts": {},
            "attempts": [],
        }

    print(f"--- Starting Synthesis for [{target.__class__.__name__} -> {component_name}] ---")
    
    try:
        with open(template_file, "r") as f:
            template_query = f.read()
            op_name = target.get_op_name()
            dep_map = target.get_dependency_map()
            dep_key = f"{op_name}_{component_name}"
            deps = dep_map.get(dep_key, [])

            # Ensure (set-logic ...) remains the very first command even after
            # we prepend helper definitions.
            logic_match = re.match(r"\s*(\(set-logic[^\)]*\)\s*)", template_query, re.IGNORECASE)
            if logic_match:
                logic_cmd = logic_match.group(1)
                rest_query = template_query[logic_match.end():]
            else:
                logic_cmd = "(set-logic ALL)\n"
                rest_query = template_query

            # Helper define-funs declared inside the component template itself
            # (e.g., sketch helper library) are needed by downstream smt2c.
            template_helper_blocks = _extract_define_fun_blocks(template_query)
            template_helper_prefix = (
                "\n\n".join(template_helper_blocks).strip() + "\n"
                if template_helper_blocks else ""
            )

            if deps:
                helper_defs = collect_helper_definitions(deps)
                base_sygus_query = logic_cmd + helper_defs + "\n" + rest_query
            else:
                base_sygus_query = logic_cmd + rest_query
            
    except FileNotFoundError:
        print(f"[ERROR] Template file not found: {template_file}")
        return None

    accepted_constraints: List[str] = []
    current_best_program = None
    solver_attempts: list[dict[str, Any]] = []
    total_solver_runtime = 0.0
    max_solver_runtime = 0.0
    enum_total: int | float | None = 0
    last_enum_primary: int | float | None = None
    enum_keys_seen: set[str] = set()
    attempt_status_counts: dict[str, int] = {}
    last_status: SolveStatus = "unknown"
    initial_strict_bits = config.FP32_OUTPUT_MATCH_MSB_BITS
    auto_relax_components = {
        "full_sum",
        "full_sum_combined",
        "full_product",
        "full_product_combined",
    }
    can_relax = (
        isinstance(target, (FP32AdditionTarget, FP32MultiplicationTarget))
        and component_name in auto_relax_components
        and getattr(config, "FP32_AUTO_RELAX_OUTPUT_MATCH", False)
    )

    for i, args in enumerate(test_cases):
        print(f"\n--- Iteration {i+1}/{len(test_cases)} ---")
        print(f"Generating new constraint with inputs: {args}")
        
        ground_truth_data = target.calculate_ground_truth(*args, config)
        
        if not ground_truth_data:
            print(f"Could not generate ground truth for inputs {args}. Skipping.")
            continue

        if can_relax:
            start_bits = (
                initial_strict_bits
                if getattr(config, "FP32_RESET_MSB_PER_SAMPLE", True)
                else config.FP32_OUTPUT_MATCH_MSB_BITS
            )
            msb_candidates = _fp32_relax_candidates(config, start_bits)
        else:
            start_bits = initial_strict_bits
            msb_candidates = [start_bits]

        accepted_this_iter = False
        accepted_bits_this_iter: Optional[int] = None
        spec_relax_statuses = set()
        if getattr(config, "FP32_RELAX_ON_INFEASIBLE", True):
            spec_relax_statuses.add("infeasible")
        if getattr(config, "FP32_RELAX_ON_FAIL", True):
            spec_relax_statuses.add("fail")
        timeout_status = "timeout"
        relax_schedule = str(getattr(config, "FP32_RELAX_SCHEDULE", "linear")).strip().lower()

        def _query_with_constraints(constraints: List[str]) -> str:
            return (
                base_sygus_query +
                "\n; --- CONSTRAINTS ---\n" +
                "\n".join(constraints) +
                "\n\n(check-synth)\n"
            )

        def _decorate_solution(solution_text: str) -> str:
            if template_helper_prefix:
                return template_helper_prefix + "\n" + solution_text
            return solution_text

        def _record_attempt(status: SolveStatus, meta: dict[str, Any], bits: int) -> None:
            nonlocal total_solver_runtime, max_solver_runtime, enum_total, last_enum_primary, last_status
            runtime_seconds = float(meta.get("runtime_seconds", 0.0) or 0.0)
            total_solver_runtime += runtime_seconds
            max_solver_runtime = max(max_solver_runtime, runtime_seconds)
            enum_primary = meta.get("enum_count_primary")
            if isinstance(enum_primary, (int, float)):
                if enum_total is None:
                    enum_total = 0
                enum_total += enum_primary
                last_enum_primary = enum_primary
            key = meta.get("enum_count_primary_key")
            if isinstance(key, str) and key:
                enum_keys_seen.add(key)
            attempt_status_counts[status] = attempt_status_counts.get(status, 0) + 1
            solver_attempts.append({
                "status": status,
                "bits": bits,
                "runtime_seconds": runtime_seconds,
                "timeout_seconds": meta.get("timeout_seconds"),
                "enum_count_primary": enum_primary,
                "enum_count_primary_key": key,
                "enum_matches": meta.get("enum_matches", []),
                "stats_raw": meta.get("stats_raw", ""),
            })
            last_status = status

        def _solve_with_bits(bits: int, prefix: List[str], timeout: int) -> Tuple[Optional[str], SolveStatus, str]:
            config.FP32_OUTPUT_MATCH_MSB_BITS = bits
            c = constraint_generator(ground_truth_data, config)
            print(c)
            q = _query_with_constraints(prefix + [c])
            sol, st, meta = run_cvc5_synthesis(q, timeout)
            _record_attempt(st, meta, bits)
            return sol, st, c

        def _stage_label(bits: int, stage1_bits: int) -> str:
            if relax_schedule != "staged":
                return f"MSB={bits}"
            if bits == 9:
                return "stage-0 (sign+exp, MSB=9)"
            if bits == stage1_bits:
                return f"stage-1 (MSB={bits})"
            if bits == start_bits:
                return f"stage-2 strict (MSB={bits})"
            return f"MSB={bits}"

        def _try_upgrade_last_constraint(upgrade_bits: List[int], timeout: int) -> Tuple[Optional[str], Optional[int]]:
            """Try to replace accepted_constraints[-1] with a stronger version (same sample)."""
            if not accepted_constraints:
                return None, None
            prefix = accepted_constraints[:-1]
            for b in upgrade_bits:
                sol, st, c = _solve_with_bits(b, prefix, timeout)
                if sol:
                    accepted_constraints[-1] = c
                    return sol, b
                if st == timeout_status:
                    break
            return None, None

        for bits in msb_candidates:
            solution, status, new_constraint = _solve_with_bits(
                bits,
                accepted_constraints,
                config.SOLVER_TIMEOUT_SECONDS,
            )
            if (
                not solution
                and status == timeout_status
                and getattr(config, "FP32_TIMEOUT_RETRY_ONCE", True)
            ):
                retry_timeout = max(
                    config.SOLVER_TIMEOUT_SECONDS + 1,
                    config.SOLVER_TIMEOUT_SECONDS * max(1, int(getattr(config, "FP32_TIMEOUT_RETRY_MULTIPLIER", 4))),
                )
                print(
                    f"[INFO] timeout at MSB match = {bits}. Retrying once with timeout={retry_timeout}s."
                )
                q_retry = _query_with_constraints(accepted_constraints + [new_constraint])
                solution, status, meta = run_cvc5_synthesis(q_retry, retry_timeout)
                _record_attempt(status, meta, bits)
            if solution:
                accepted_constraints.append(new_constraint)
                # Persist template-local helper define-funs together with the
                # synthesized function so external tools (e.g., smt2c) can
                # resolve helper symbols used in the final body.
                current_best_program = _decorate_solution(solution)
                accepted_this_iter = True
                accepted_bits_this_iter = bits
                print(f"SUCCESS: accepted (MSB match = {bits}). Total constraints: {len(accepted_constraints)}")
                # If stage-0 (sign+exp) was accepted, try immediate upgrade for the same sample.
                if can_relax and relax_schedule == "staged" and bits == 9:
                    stage1_bits = 9 + int(getattr(config, "FP32_STAGE_MANTISSA_BITS", 15))
                    upgrade_sol, upgraded_bits = _try_upgrade_last_constraint(
                        [stage1_bits, start_bits],
                        config.SOLVER_TIMEOUT_SECONDS,
                    )
                    if upgrade_sol:
                        current_best_program = _decorate_solution(upgrade_sol)
                        accepted_bits_this_iter = upgraded_bits
                        print(
                            f"[INFO] Upgraded stage-0 -> {_stage_label(upgraded_bits, stage1_bits)} for this sample."
                        )
                    else:
                        print("[INFO] Stage-0 accepted, but no upgrade succeeded for this sample.")
                # Keep strict baseline for next sample if reset mode is enabled.
                if getattr(config, "FP32_RESET_MSB_PER_SAMPLE", True):
                    config.FP32_OUTPUT_MATCH_MSB_BITS = initial_strict_bits
                break

            if status == timeout_status:
                if can_relax and relax_schedule == "staged":
                    stage0_bits = 9
                    if bits != stage0_bits:
                        print("[INFO] Timeout at this stage. Trying stage-0 (sign+exp) fallback...")
                        sol0, st0, c0 = _solve_with_bits(
                            stage0_bits,
                            accepted_constraints,
                            config.SOLVER_TIMEOUT_SECONDS,
                        )
                        if sol0:
                            accepted_constraints.append(c0)
                            current_best_program = _decorate_solution(sol0)
                            accepted_this_iter = True
                            accepted_bits_this_iter = stage0_bits
                            print("SUCCESS: accepted at stage-0 after timeout.")

                            stage1_bits = 9 + int(getattr(config, "FP32_STAGE_MANTISSA_BITS", 15))
                            upgrade_sol, upgraded_bits = _try_upgrade_last_constraint(
                                [stage1_bits, start_bits],
                                config.SOLVER_TIMEOUT_SECONDS,
                            )
                            if upgrade_sol:
                                current_best_program = _decorate_solution(upgrade_sol)
                                accepted_bits_this_iter = upgraded_bits
                                print(
                                    f"[INFO] Upgraded stage-0 -> {_stage_label(upgraded_bits, stage1_bits)} for this sample."
                                )
                            else:
                                print("[INFO] Stage-0 accepted, but no upgrade succeeded for this sample.")
                            if getattr(config, "FP32_RESET_MSB_PER_SAMPLE", True):
                                config.FP32_OUTPUT_MATCH_MSB_BITS = initial_strict_bits
                            break
                print("[INFO] Timeout. No staged fallback; skipping this sample.")
                break

            if can_relax and status in spec_relax_statuses:
                print(f"[INFO] {status} at MSB match = {bits}. Trying weaker match...")
                continue

            print(f"[INFO] Not relaxable (status={status}); not relaxing further for this sample.")
            break

        if accepted_this_iter and accepted_bits_this_iter is not None and can_relax and relax_schedule == "staged":
            stage1_bits = 9 + int(getattr(config, "FP32_STAGE_MANTISSA_BITS", 15))
            print(
                f"[INFO] Final accepted level for this sample: {_stage_label(accepted_bits_this_iter, stage1_bits)}."
            )

        if not accepted_this_iter:
            # Keep previously active strictness when current sample could not be added.
            config.FP32_OUTPUT_MATCH_MSB_BITS = start_bits
            a, b = args
            print(f"SKIPPED: ({a:.3f}, {b:.3f}) could not be added (even after relaxation).")

    print("\n\n--- Synthesis Complete! ---")
    print(f"\nConstraints accepted: {len(accepted_constraints)}/{len(test_cases)}")
    if current_best_program:
        print("\n--- Final Synthesized Program ---")
        print(current_best_program)
    else:
        print("Could not find a valid program that satisfies any constraints.")
    return current_best_program, {
        "component": component_name,
        "template_file": template_file,
        "solution_found": current_best_program is not None,
        "accepted_constraints": len(accepted_constraints),
        "total_constraints": len(test_cases),
        "solve_status": "solved" if current_best_program else last_status,
        "solver_attempts": len(solver_attempts),
        "solver_runtime_seconds_total": total_solver_runtime,
        "solver_runtime_seconds_max": max_solver_runtime,
        "enum_count_primary_total": enum_total if solver_attempts else None,
        "enum_count_primary_last": last_enum_primary,
        "enum_primary_keys_seen": sorted(enum_keys_seen),
        "attempt_status_counts": attempt_status_counts,
        "attempts": solver_attempts,
    }


def _op_name_for_target(target) -> str:
    if hasattr(target, "get_op_name"):
        return target.get_op_name()
    return target.__class__.__name__.replace('Target', '').lower()


def resolve_component_plan(target, component_name: str) -> list[str]:
    if not hasattr(target, "get_dependency_map"):
        return [component_name]

    op_name = _op_name_for_target(target)
    dep_map = target.get_dependency_map()
    root_key = f"{op_name}_{component_name}"
    deps = dep_map.get(root_key, [])
    if not deps:
        return [component_name]

    order: list[str] = []
    visited: set[str] = set()

    def dfs(key: str) -> None:
        if key in visited:
            return
        visited.add(key)
        for dep in dep_map.get(key, []):
            dfs(dep)
        order.append(key)

    dfs(root_key)

    components = []
    available = set(target.get_components().keys())
    for key in order:
        comp = key[len(op_name) + 1:] if key.startswith(f"{op_name}_") else key
        if comp in available:
            components.append(comp)
        else:
            print(f"[WARN] Dependency '{key}' not found in target components. Skipping.")

    return components if components else [component_name]


def _env_flag(name: str, default: bool) -> bool:
    raw = os.getenv(name)
    if raw is None:
        return default
    value = raw.strip().lower()
    if value in {"1", "true", "yes", "on"}:
        return True
    if value in {"0", "false", "no", "off"}:
        return False
    return default

def _descending_msb_candidates(start: int, minimum: int, step: int) -> list[int]:
    """Build a descending candidate list and always include the minimum endpoint."""
    if step <= 0:
        step = 1
    start = max(1, min(32, start))
    minimum = max(1, min(32, minimum))
    if minimum > start:
        minimum = start

    values = list(range(start, minimum - 1, -step))
    if values[-1] != minimum:
        values.append(minimum)
    return values


def _staged_msb_candidates(start: int, stage_mantissa_bits: int, minimum: int) -> list[int]:
    """Build staged FP32 relaxation candidates:
    full -> sign+exp+top-mantissa(K) -> sign+exp -> minimum.
    """
    start = max(1, min(32, start))
    minimum = max(1, min(32, minimum))
    stage_mantissa_bits = max(0, min(23, stage_mantissa_bits))

    signexp_bits = 9  # 1 sign + 8 exponent
    signexp_mant_bits = signexp_bits + stage_mantissa_bits

    candidates: list[int] = [start]
    for b in (signexp_mant_bits, signexp_bits, minimum):
        if b < candidates[-1]:
            candidates.append(b)
    return candidates


def _fp32_relax_candidates(config: SynthesisConfig, start_bits: int) -> list[int]:
    """Return FP32 MSB-match candidates according to selected relaxation schedule."""
    schedule = str(getattr(config, "FP32_RELAX_SCHEDULE", "linear")).strip().lower()
    min_bits = config.FP32_MIN_OUTPUT_MATCH_MSB_BITS
    if schedule == "staged":
        return _staged_msb_candidates(
            start=start_bits,
            stage_mantissa_bits=getattr(config, "FP32_STAGE_MANTISSA_BITS", 15),
            minimum=min_bits,
        )
    return _descending_msb_candidates(start_bits, min_bits, config.FP32_OUTPUT_MATCH_STEP)


def _target_from_name(name: str):
    key = name.strip().lower()
    mapping: dict[str, Callable[[], object]] = {
        "mxint8_add": MXINT8AdditionTarget,
        "mxint8_mul": MXINT8MultiplicationTarget,
        "fp32_add": FP32AdditionTarget,
        "fp32_mul": FP32MultiplicationTarget,
        "dot_product": DotProductTarget,
        "naive_int8_add": lambda: NaiveAdderTarget(kind="int", width=8),
        "naive_int32_add": lambda: NaiveAdderTarget(kind="int", width=32),
        "naive_fp32_add": lambda: NaiveAdderTarget(kind="fp32"),
        "naive_int8_mul": lambda: NaiveMultiplierTarget(kind="int", width=8),
        "naive_int32_mul": lambda: NaiveMultiplierTarget(kind="int", width=32),
        "naive_fp32_mul": lambda: NaiveMultiplierTarget(kind="fp32"),
    }
    ctor = mapping.get(key)
    if ctor is None:
        valid = ", ".join(sorted(mapping.keys()))
        raise ValueError(f"Unknown SYNTH_TARGET='{name}'. Valid: {valid}")
    return ctor()

def _accuracy_make_config(target, component_name: str) -> dict[str, str] | None:
    """Map synthesized top component to accuracy_tests make variables."""
    if isinstance(target, FP32MultiplicationTarget) and component_name in {"full_product", "full_product_combined"}:
        return {
            "variant_env": "FP32_MUL_VARIANT",
            "variant_val": "combined" if component_name == "full_product_combined" else "subcomponents",
            "toplevel": "fp32_full_mul",
            "module": "tests.multiplication.test_fp32_multiplier",
        }
    if isinstance(target, FP32AdditionTarget) and component_name in {"full_sum", "full_sum_combined"}:
        return {
            "variant_env": "FP32_ADD_VARIANT",
            "variant_val": "combined" if component_name == "full_sum_combined" else "subcomponents",
            "toplevel": "fp32_sum",
            "module": "tests.addition.test_fp32_adder",
        }
    if isinstance(target, MXINT8MultiplicationTarget) and component_name in {"full_product", "full_product_combined"}:
        return {
            "variant_env": "MXINT8_MUL_VARIANT",
            "variant_val": "combined" if component_name == "full_product_combined" else "subcomponents",
            "toplevel": "mult_mxint_full_product",
            "module": "tests.multiplication.test_mxint8_multiplier",
        }
    if isinstance(target, MXINT8AdditionTarget) and component_name in {"full_sum", "full_sum_combined"}:
        return {
            "variant_env": "MXINT8_ADD_VARIANT",
            "variant_val": "combined" if component_name == "full_sum_combined" else "subcomponents",
            "toplevel": "add_full_sum",
            "module": "tests.addition.test_mxint8_adder",
        }
    return None

def run_accuracy_tests_for_solution(target, component_name: str, solution_name: str, repo_root: Path) -> dict[str, Any]:
    """Run cocotb accuracy for a synthesized solution via accuracy_tests/Makefile."""
    cfg = _accuracy_make_config(target, component_name)
    if cfg is None:
        print(
            f"[INFO] Accuracy step skipped: no accuracy mapping for "
            f"{target.__class__.__name__}.{component_name}"
        )
        return {"ran": False, "skipped": True, "cocotb_passed": True}

    accuracy_root = repo_root / "accuracy_tests"
    if not accuracy_root.exists():
        print(f"[WARN] accuracy_tests directory not found at {accuracy_root}; skipping accuracy step.")
        return {"ran": False, "skipped": True, "cocotb_passed": False}

    hls_base = Path(
        os.environ.get(
            "SYNTH_ACCURACY_HLS_BASE",
            os.environ.get("VITIS_HLS_RESULTS_ROOT", str(repo_root / "results" / "HLS")),
        )
    ).resolve()

    env = os.environ.copy()
    env[cfg["variant_env"]] = cfg["variant_val"]
    env["TOPLEVEL_LANG"] = "verilog"

    # Optional override to run cocotb in a different Python env.
    acc_python = os.environ.get("SYNTH_ACCURACY_PYTHON", "").strip()
    if acc_python:
        env["PYTHON"] = acc_python
        py_bin = str(Path(acc_python).expanduser().resolve().parent)
        env["PATH"] = py_bin + os.pathsep + env.get("PATH", "")
    else:
        env.setdefault("PYTHON", sys.executable)

    rel_err_pct = os.environ.get("SYNTH_FP32_MUL_REL_ERR_PCT", "").strip()
    if rel_err_pct:
        env["FP32_MUL_REL_ERR_PCT"] = rel_err_pct

    cmd = [
        "make",
        f"HLS_BASE={hls_base}",
        f"HLS_SOLN={solution_name}",
        f"TOPLEVEL={cfg['toplevel']}",
        f"MODULE={cfg['module']}",
        "TOPLEVEL_LANG=verilog",
    ]
    print(
        "[ACC-CMD] "
        f"{cfg['variant_env']}={cfg['variant_val']} "
        f"PYTHON={env.get('PYTHON', '')} " + " ".join(cmd)
    )
    proc = subprocess.run(cmd, cwd=accuracy_root, env=env, capture_output=True, text=True)
    combined_output = (proc.stdout or "") + ("\n" + proc.stderr if proc.stderr else "")
    if combined_output.strip():
        print(combined_output, end="" if combined_output.endswith("\n") else "\n")

    metrics: dict[str, Any]
    try:
        from src.Experiments.bitvector_sweep import parse_cocotb_metrics
        class _ParseTarget:
            fp32 = isinstance(target, (FP32AdditionTarget, FP32MultiplicationTarget))
        metrics = parse_cocotb_metrics(combined_output, _ParseTarget())
    except Exception:
        metrics = {}

    metrics.update({
        "ran": True,
        "skipped": False,
        "cocotb_passed": proc.returncode == 0,
        "cocotb_returncode": proc.returncode,
    })

    if proc.returncode == 0:
        print("[SUCCESS] Accuracy run completed successfully.")
        return metrics
    print(f"[WARN] Accuracy run failed with return code {proc.returncode}.")
    return metrics


if __name__ == "__main__":
    config = SynthesisConfig()
    run_summary: dict[str, Any] = {
        "status": "started",
        "error": "",
        "target": "",
        "component": "",
        "op_name": "",
        "component_plan": [],
        "config": {},
        "components": {},
        "paths": {},
        "hardware": {},
        "accuracy": {},
    }
 
    target_operation = DEFAULT_TARGET_OPERATION
    target_component = DEFAULT_COMPONENT
    random_seed: int | None = None

    # Optional env-driven override for automation/notebooks.
    # Examples:
    #   SYNTH_TARGET=fp32_mul SYNTH_COMPONENT=full_product_combined python -m src.synthesis_driver
    #   SYNTH_TARGET=mxint8_add SYNTH_COMPONENT=full_sum python -m src.synthesis_driver
    env_target = os.getenv("SYNTH_TARGET", "").strip()
    env_component = os.getenv("SYNTH_COMPONENT", "").strip()
    if env_target:
        target_operation = _target_from_name(env_target)
    if env_component:
        target_component = env_component
    env_random_seed = os.getenv("SYNTH_RANDOM_SEED", "").strip()
    if env_random_seed:
        try:
            random_seed = int(env_random_seed)
            random.seed(random_seed)
        except ValueError:
            print(f"[WARN] Invalid SYNTH_RANDOM_SEED='{env_random_seed}', using default RNG state.")
 
    # False for a quick post-synthesis estimate (-p)
    # True for a full post-implementation run (-i)
    RUN_IMPLEMENTATION = _env_flag("SYNTH_RUN_IMPL", DEFAULT_RUN_IMPLEMENTATION)
    # Run cocotb accuracy after HLS/implementation from the same command.
    RUN_ACCURACY = _env_flag("SYNTH_RUN_ACCURACY", DEFAULT_RUN_ACCURACY)
    # Directed (hand-picked) IO constraint seeds to 
    # guide synthesiser for monolithic components.
    ENABLE_DIRECTED_IO_CONSTRAINTS = _env_flag(
        "SYNTH_ENABLE_DIRECTED_IO",
        DEFAULT_ENABLE_DIRECTED_IO_CONSTRAINTS,
    )
    ENABLE_SYGUS_DUMP = _env_flag("SYNTH_ENABLE_SYGUS_DUMP", ENABLE_SYGUS_DUMP)
    ENABLE_SYGUS_FAST_ENUM = _env_flag("SYNTH_ENABLE_SYGUS_FAST_ENUM", ENABLE_SYGUS_FAST_ENUM)
    ENABLE_SYGUS_PBE = _env_flag("SYNTH_ENABLE_SYGUS_PBE", ENABLE_SYGUS_PBE)
    ENABLE_SYGUS_SYM_BREAK_PBE = _env_flag(
        "SYNTH_ENABLE_SYGUS_SYM_BREAK_PBE",
        ENABLE_SYGUS_SYM_BREAK_PBE,
    )
    SHOW_SMT2C_OUTPUT = _env_flag("SYNTH_SHOW_SMT2C_OUTPUT", SHOW_SMT2C_OUTPUT)

    env_num_iters = os.getenv("SYNTH_NUM_ITERATIONS", "").strip()
    if env_num_iters:
        try:
            config.NUM_ITERATIONS = int(env_num_iters)
        except ValueError:
            print(f"[WARN] Invalid SYNTH_NUM_ITERATIONS='{env_num_iters}', using default {config.NUM_ITERATIONS}.")

    env_solver_timeout = os.getenv("SYNTH_SOLVER_TIMEOUT", "").strip()
    if env_solver_timeout:
        try:
            config.SOLVER_TIMEOUT_SECONDS = int(env_solver_timeout)
        except ValueError:
            print(f"[WARN] Invalid SYNTH_SOLVER_TIMEOUT='{env_solver_timeout}', using default {config.SOLVER_TIMEOUT_SECONDS}.")

    env_fp32_msb_bits = os.getenv("SYNTH_FP32_OUTPUT_MATCH_MSB_BITS", "").strip()
    if env_fp32_msb_bits:
        try:
            parsed = int(env_fp32_msb_bits)
            if 1 <= parsed <= 32:
                config.FP32_OUTPUT_MATCH_MSB_BITS = parsed
            else:
                print(
                    f"[WARN] SYNTH_FP32_OUTPUT_MATCH_MSB_BITS must be in [1, 32], "
                    f"got '{env_fp32_msb_bits}'. Using default {config.FP32_OUTPUT_MATCH_MSB_BITS}."
                )
        except ValueError:
            print(
                f"[WARN] Invalid SYNTH_FP32_OUTPUT_MATCH_MSB_BITS='{env_fp32_msb_bits}', "
                f"using default {config.FP32_OUTPUT_MATCH_MSB_BITS}."
            )

    config.FP32_AUTO_RELAX_OUTPUT_MATCH = _env_flag(
        "SYNTH_FP32_AUTO_RELAX_OUTPUT_MATCH",
        config.FP32_AUTO_RELAX_OUTPUT_MATCH,
    )
    config.FP32_RESET_MSB_PER_SAMPLE = _env_flag(
        "SYNTH_FP32_RESET_MSB_PER_SAMPLE",
        config.FP32_RESET_MSB_PER_SAMPLE,
    )
    config.FP32_RELAX_ON_TIMEOUT = _env_flag(
        "SYNTH_FP32_RELAX_ON_TIMEOUT",
        config.FP32_RELAX_ON_TIMEOUT,
    )
    config.FP32_TIMEOUT_RETRY_ONCE = _env_flag(
        "SYNTH_FP32_TIMEOUT_RETRY_ONCE",
        config.FP32_TIMEOUT_RETRY_ONCE,
    )
    config.FP32_RELAX_ON_INFEASIBLE = _env_flag(
        "SYNTH_FP32_RELAX_ON_INFEASIBLE",
        config.FP32_RELAX_ON_INFEASIBLE,
    )
    config.FP32_RELAX_ON_FAIL = _env_flag(
        "SYNTH_FP32_RELAX_ON_FAIL",
        config.FP32_RELAX_ON_FAIL,
    )
    env_fp32_timeout_retry_mult = os.getenv("SYNTH_FP32_TIMEOUT_RETRY_MULTIPLIER", "").strip()
    if env_fp32_timeout_retry_mult:
        try:
            parsed = int(env_fp32_timeout_retry_mult)
            if parsed >= 1:
                config.FP32_TIMEOUT_RETRY_MULTIPLIER = parsed
            else:
                print(
                    f"[WARN] SYNTH_FP32_TIMEOUT_RETRY_MULTIPLIER must be >= 1, "
                    f"got '{env_fp32_timeout_retry_mult}'. Using default {config.FP32_TIMEOUT_RETRY_MULTIPLIER}."
                )
        except ValueError:
            print(
                f"[WARN] Invalid SYNTH_FP32_TIMEOUT_RETRY_MULTIPLIER='{env_fp32_timeout_retry_mult}', "
                f"using default {config.FP32_TIMEOUT_RETRY_MULTIPLIER}."
            )

    env_fp32_msb_min = os.getenv("SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS", "").strip()
    if env_fp32_msb_min:
        try:
            parsed = int(env_fp32_msb_min)
            if 1 <= parsed <= 32:
                config.FP32_MIN_OUTPUT_MATCH_MSB_BITS = parsed
            else:
                print(
                    f"[WARN] SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS must be in [1, 32], "
                    f"got '{env_fp32_msb_min}'. Using default {config.FP32_MIN_OUTPUT_MATCH_MSB_BITS}."
                )
        except ValueError:
            print(
                f"[WARN] Invalid SYNTH_FP32_MIN_OUTPUT_MATCH_MSB_BITS='{env_fp32_msb_min}', "
                f"using default {config.FP32_MIN_OUTPUT_MATCH_MSB_BITS}."
            )

    env_fp32_msb_step = os.getenv("SYNTH_FP32_OUTPUT_MATCH_STEP", "").strip()
    if env_fp32_msb_step:
        try:
            parsed = int(env_fp32_msb_step)
            if parsed > 0:
                config.FP32_OUTPUT_MATCH_STEP = parsed
            else:
                print(
                    f"[WARN] SYNTH_FP32_OUTPUT_MATCH_STEP must be > 0, got '{env_fp32_msb_step}'. "
                    f"Using default {config.FP32_OUTPUT_MATCH_STEP}."
                )
        except ValueError:
            print(
                f"[WARN] Invalid SYNTH_FP32_OUTPUT_MATCH_STEP='{env_fp32_msb_step}', "
                f"using default {config.FP32_OUTPUT_MATCH_STEP}."
            )

    env_fp32_relax_schedule = os.getenv("SYNTH_FP32_RELAX_SCHEDULE", "").strip().lower()
    if env_fp32_relax_schedule:
        if env_fp32_relax_schedule in {"linear", "staged"}:
            config.FP32_RELAX_SCHEDULE = env_fp32_relax_schedule
        else:
            print(
                f"[WARN] Invalid SYNTH_FP32_RELAX_SCHEDULE='{env_fp32_relax_schedule}', "
                f"using default {config.FP32_RELAX_SCHEDULE}."
            )

    env_fp32_stage_mant_bits = os.getenv("SYNTH_FP32_STAGE_MANTISSA_BITS", "").strip()
    if env_fp32_stage_mant_bits:
        try:
            parsed = int(env_fp32_stage_mant_bits)
            if 0 <= parsed <= 23:
                config.FP32_STAGE_MANTISSA_BITS = parsed
            else:
                print(
                    f"[WARN] SYNTH_FP32_STAGE_MANTISSA_BITS must be in [0, 23], "
                    f"got '{env_fp32_stage_mant_bits}'. Using default {config.FP32_STAGE_MANTISSA_BITS}."
                )
        except ValueError:
            print(
                f"[WARN] Invalid SYNTH_FP32_STAGE_MANTISSA_BITS='{env_fp32_stage_mant_bits}', "
                f"using default {config.FP32_STAGE_MANTISSA_BITS}."
            )

    fp32_mul_synth_mode = os.getenv(
        "SYNTH_FP32_MUL_MODE",
        DEFAULT_SYNTH_FP32_MUL_MODE,
    ).strip().lower()
    if not fp32_mul_synth_mode:
        fp32_mul_synth_mode = DEFAULT_SYNTH_FP32_MUL_MODE
    if fp32_mul_synth_mode not in {"default", "wide", "small"}:
        print(
            f"[WARN] Invalid SYNTH_FP32_MUL_MODE='{fp32_mul_synth_mode}', "
            f"using default '{DEFAULT_SYNTH_FP32_MUL_MODE}'."
        )
        fp32_mul_synth_mode = DEFAULT_SYNTH_FP32_MUL_MODE

    fp32_add_synth_mode = os.getenv(
        "SYNTH_FP32_ADD_MODE",
        DEFAULT_SYNTH_FP32_ADD_MODE,
    ).strip().lower()
    if not fp32_add_synth_mode:
        fp32_add_synth_mode = DEFAULT_SYNTH_FP32_ADD_MODE
    if fp32_add_synth_mode not in {"default", "wide", "small"}:
        print(
            f"[WARN] Invalid SYNTH_FP32_ADD_MODE='{fp32_add_synth_mode}', "
            f"using default '{DEFAULT_SYNTH_FP32_ADD_MODE}'."
        )
        fp32_add_synth_mode = DEFAULT_SYNTH_FP32_ADD_MODE

    if config.FP32_MIN_OUTPUT_MATCH_MSB_BITS > config.FP32_OUTPUT_MATCH_MSB_BITS:
        print(
            f"[WARN] FP32 min MSB ({config.FP32_MIN_OUTPUT_MATCH_MSB_BITS}) is greater than start "
            f"({config.FP32_OUTPUT_MATCH_MSB_BITS}); clamping min to start."
        )
        config.FP32_MIN_OUTPUT_MATCH_MSB_BITS = config.FP32_OUTPUT_MATCH_MSB_BITS

    print(f"[INFO] Target: {target_operation.__class__.__name__} | Component: {target_component}")
    print(
        f"[INFO] NUM_ITERATIONS={config.NUM_ITERATIONS}, TIMEOUT={config.SOLVER_TIMEOUT_SECONDS}s, "
        f"RUN_IMPLEMENTATION={RUN_IMPLEMENTATION}, DIRECTED_IO={ENABLE_DIRECTED_IO_CONSTRAINTS}, "
        f"RUN_ACCURACY={RUN_ACCURACY}, "
        f"SYNTH_FP32_MUL_MODE={fp32_mul_synth_mode}, "
        f"SYNTH_FP32_ADD_MODE={fp32_add_synth_mode}, "
        f"SYGUS_DUMP={ENABLE_SYGUS_DUMP}, "
        f"SYGUS_FAST_ENUM={ENABLE_SYGUS_FAST_ENUM}, "
        f"SYGUS_PBE={ENABLE_SYGUS_PBE}, "
        f"SYGUS_SYM_BREAK_PBE={ENABLE_SYGUS_SYM_BREAK_PBE}, "
        f"FP32_OUTPUT_MATCH_MSB_BITS={config.FP32_OUTPUT_MATCH_MSB_BITS}, "
        f"FP32_AUTO_RELAX_OUTPUT_MATCH={config.FP32_AUTO_RELAX_OUTPUT_MATCH}, "
        f"FP32_RESET_MSB_PER_SAMPLE={config.FP32_RESET_MSB_PER_SAMPLE}, "
        f"FP32_RELAX_ON_TIMEOUT={config.FP32_RELAX_ON_TIMEOUT}, "
        f"FP32_TIMEOUT_RETRY_ONCE={config.FP32_TIMEOUT_RETRY_ONCE}, "
        f"FP32_TIMEOUT_RETRY_MULTIPLIER={config.FP32_TIMEOUT_RETRY_MULTIPLIER}, "
        f"FP32_RELAX_ON_INFEASIBLE={config.FP32_RELAX_ON_INFEASIBLE}, "
        f"FP32_RELAX_ON_FAIL={config.FP32_RELAX_ON_FAIL}, "
        f"FP32_RELAX_SCHEDULE={config.FP32_RELAX_SCHEDULE}, "
        f"FP32_STAGE_MANTISSA_BITS={config.FP32_STAGE_MANTISSA_BITS}, "
        f"FP32_MIN_OUTPUT_MATCH_MSB_BITS={config.FP32_MIN_OUTPUT_MATCH_MSB_BITS}, "
        f"FP32_OUTPUT_MATCH_STEP={config.FP32_OUTPUT_MATCH_STEP}, "
        f"RANDOM_SEED={random_seed}"
    )
    run_summary["target"] = target_operation.__class__.__name__
    run_summary["component"] = target_component
    run_summary["config"] = {
        "num_iterations": config.NUM_ITERATIONS,
        "solver_timeout_seconds": config.SOLVER_TIMEOUT_SECONDS,
        "run_implementation": RUN_IMPLEMENTATION,
        "run_accuracy": RUN_ACCURACY,
        "directed_io": ENABLE_DIRECTED_IO_CONSTRAINTS,
        "sygus_dump": ENABLE_SYGUS_DUMP,
        "sygus_fast_enum": ENABLE_SYGUS_FAST_ENUM,
        "sygus_pbe": ENABLE_SYGUS_PBE,
        "sygus_sym_break_pbe": ENABLE_SYGUS_SYM_BREAK_PBE,
        "fp32_output_match_msb_bits": config.FP32_OUTPUT_MATCH_MSB_BITS,
        "fp32_auto_relax_output_match": config.FP32_AUTO_RELAX_OUTPUT_MATCH,
        "fp32_reset_msb_per_sample": config.FP32_RESET_MSB_PER_SAMPLE,
        "fp32_relax_on_timeout": config.FP32_RELAX_ON_TIMEOUT,
        "fp32_timeout_retry_once": config.FP32_TIMEOUT_RETRY_ONCE,
        "fp32_timeout_retry_multiplier": config.FP32_TIMEOUT_RETRY_MULTIPLIER,
        "fp32_relax_on_infeasible": config.FP32_RELAX_ON_INFEASIBLE,
        "fp32_relax_on_fail": config.FP32_RELAX_ON_FAIL,
        "fp32_relax_schedule": config.FP32_RELAX_SCHEDULE,
        "fp32_stage_mantissa_bits": config.FP32_STAGE_MANTISSA_BITS,
        "fp32_min_output_match_msb_bits": config.FP32_MIN_OUTPUT_MATCH_MSB_BITS,
        "fp32_output_match_step": config.FP32_OUTPUT_MATCH_STEP,
        "fp32_mul_mode": fp32_mul_synth_mode,
        "random_seed": random_seed,
    }
    
    synthesis_test_cases = []

    if isinstance(target_operation, (NaiveAdderTarget, NaiveMultiplierTarget)):
        cases = []
        if target_operation.kind == "int":
            W = target_operation.width
            # Slightly different seed sets for add vs mul (mul gets (1,1) too)
            if isinstance(target_operation, NaiveMultiplierTarget):
                seeds = [(0, 0), (1, 0), (1, 1),
                        ((1 << W) - 1, 1), ((1 << W) - 1, (1 << W) - 1)]
            else:  # NaiveAdderTarget int
                seeds = [(0, 0), (1, 0),
                        ((1 << W) - 1, 1), ((1 << W) - 1, (1 << W) - 1)]

            cases.extend(seeds[:min(len(seeds), config.NUM_ITERATIONS)])

            # Fill the rest with random modular-int pairs
            while len(cases) < config.NUM_ITERATIONS:
                x = random.getrandbits(W)   # cleaner than randrange
                y = random.getrandbits(W)
                cases.append((x, y))

        else:  # kind == "fp32"
            max_val = 1e4
            cases = [
                (random.uniform(-max_val, max_val), random.uniform(-max_val, max_val))
                for _ in range(config.NUM_ITERATIONS)
            ]

        synthesis_test_cases = cases

    elif isinstance(target_operation, DotProductTarget):
            vec_len = 2 
            max_val = 10 
            for _ in range(config.NUM_ITERATIONS):
                vec1 = [random.uniform(-max_val, max_val) for _ in range(vec_len)]
                vec2 = [random.uniform(-max_val, max_val) for _ in range(vec_len)]
                synthesis_test_cases.append((vec1, vec2))

    elif isinstance(target_operation, (MXINT8AdditionTarget, MXINT8MultiplicationTarget, FP32AdditionTarget, FP32MultiplicationTarget)):
        alignment_directed_cases: list[tuple[float, float]] = []
        fp32_add_directed_cases: list[tuple[float, float]] = []
        fp32_mult_directed_cases: list[tuple[float, float]] = []
        sample_lo: Optional[float] = None
        sample_hi: Optional[float] = None
        if isinstance(target_operation, MXINT8AdditionTarget):
            max_val = 66
            # Directed cases to exercise rounding and large-shift behavior.
            scale = 1 << (config.MANTISSA_WIDTH - 1)

            def mxint8_float(m: int, e: int) -> float:
                return (m * (2.0 ** e)) / float(scale)

            directed_pairs = [
                ((5, 3), (5, 2)),   # d=1
                ((5, 3), (-5, 2)),
                ((5, 3), (5, 1)),   # d=2
                ((5, 3), (-5, 1)),
                ((5, 3), (5, 0)),   # d=3
                ((5, 3), (-5, 0)),
                ((5, 3), (5, -2)),  # d>=4
                ((5, 3), (-5, -2)),
                ((5, 2), (5, 3)),   # reverse (shift m1)
                ((-5, 2), (5, 3)),
                ((5, 1), (5, 3)),
                ((5, 0), (5, 3)),
                ((5, -2), (5, 3)),
            ]

            for (m1, e1), (m2, e2) in directed_pairs:
                alignment_directed_cases.append((mxint8_float(m1, e1), mxint8_float(m2, e2)))

        elif isinstance(target_operation, MXINT8MultiplicationTarget):
            max_val = math.sqrt(112)
        elif isinstance(target_operation, FP32MultiplicationTarget):
            fp32_mul_mode = fp32_mul_synth_mode
            if fp32_mul_mode == "small":
                sample_lo, sample_hi = 0.0, 1.0
                # Keep directed vectors inside [0, 1] for both operands.
                # These still exercise different renorm/rounding behaviors.
                fp32_mult_directed_cases = [
                    (0.75, 0.75),     # renorm=1 tendency
                    (0.625, 0.625),   # renorm=0 tendency
                    (0.5, 0.5),
                    (0.875, 0.5),
                    (float.fromhex("0x1.000002p-1"), float.fromhex("0x1.000002p-1")),
                ]
            elif fp32_mul_mode == "wide":
                sample_lo, sample_hi = -1024.0, 1024.0
            else:
                sample_lo, sample_hi = -1e4, 1e4
                if fp32_mul_mode not in {"default", ""}:
                    print(
                        f"[WARN] Unknown SYNTH_FP32_MUL_MODE='{fp32_mul_mode}', "
                        "falling back to default range [-1e4, 1e4]."
                    )
            print(
                f"[INFO] FP32 synthesis operand mode={fp32_mul_mode or 'default'} "
                f"range=[{sample_lo}, {sample_hi}]"
            )
            # Diagnostic FP32 mult cases to hit specific branches early.
            # Renorm=1 tends to occur when product in [2,4).
            # Renorm=0 tends to occur when product in [1,2).
            if not fp32_mult_directed_cases:
                fp32_mult_directed_cases = [
                    (1.5, 1.5),   # renorm = 1 (approx 2.25)
                    (1.25, 1.25), # renorm = 0 (approx 1.5625)
                    (-1.5, 1.5),  # mixed sign
                    (1.5, -1.5),  # mixed sign (opposite)
                    # Rounding-sensitive: near-halfway in mantissa rounding
                    (float.fromhex("0x1.000002p+0"), float.fromhex("0x1.000002p+0")),
                ]
        elif isinstance(target_operation, FP32AdditionTarget):
            fp32_add_mode = fp32_add_synth_mode
            if fp32_add_mode == "small":
                sample_lo, sample_hi = 0.0, 1.0
            elif fp32_add_mode == "wide":
                sample_lo, sample_hi = -1024.0, 1024.0
            else:
                sample_lo, sample_hi = -1e4, 1e4
                if fp32_add_mode not in {"default", ""}:
                    print(
                        f"[WARN] Unknown SYNTH_FP32_ADD_MODE='{fp32_add_mode}', "
                        "falling back to default range [-1e4, 1e4]."
                    )
            max_val = sample_hi  # fallback for any code using max_val
            print(
                f"[INFO] FP32 add synthesis operand mode={fp32_add_mode or 'default'} "
                f"range=[{sample_lo}, {sample_hi}]"
            )
            # Directed FP32 add cases to exercise specific branches first.
            fp32_add_directed_cases = [
                # Easiest bootstrap first: same-sign, equal exponents.
                (1.0, 1.0),

                # Subtraction basics.
                (1.5, -1.5),
                (1.5, -0.5),

                # Subtraction with cancellation (left-normalization pressure).
                (1.5, -1.25),
                (1.25, -1.0),

                # Same-sign growth / overflow normalization.
                (1.5, 1.5),
                (1.75, 1.75),

                # Small exponent gaps (clean alignment).
                (1.5, 0.75),
                (1.5, 0.375),
                (1.5, 0.1875),

                # Swap / exp tie-break by mantissa.
                (1.25, 1.5),
                (1.5, 1.25),

                # Huge exponent gap where small addend is negligible.
                (8192.0, 1e-6),
            ]

        if ENABLE_DIRECTED_IO_CONSTRAINTS and fp32_add_directed_cases:
            synthesis_test_cases.extend(fp32_add_directed_cases[:config.NUM_ITERATIONS])
        if ENABLE_DIRECTED_IO_CONSTRAINTS and fp32_mult_directed_cases:
            synthesis_test_cases.extend(fp32_mult_directed_cases[:config.NUM_ITERATIONS])

        while len(synthesis_test_cases) < config.NUM_ITERATIONS:
            if sample_lo is not None and sample_hi is not None:
                f1 = random.uniform(sample_lo, sample_hi)
                f2 = random.uniform(sample_lo, sample_hi)
            else:
                f1 = random.uniform(-max_val, max_val)
                f2 = random.uniform(-max_val, max_val)
            synthesis_test_cases.append((f1, f2))

    # ===================================================================

    op_name = _op_name_for_target(target_operation)
    component_plan = resolve_component_plan(target_operation, target_component)
    run_summary["op_name"] = op_name
    run_summary["component_plan"] = component_plan
    if len(component_plan) > 1:
        print(f"[INFO] Synthesizing dependency chain: {component_plan}")

    final_program = None
    final_component = component_plan[-1]
    programs_by_component: dict[str, str] = {}
    component_metrics: dict[str, Any] = {}

    # Create organized results subdirectories
    smt_dir = os.path.join('results', 'smt2')
    c_dir = os.path.join('results', 'c')
    cpp_dir = os.path.join('results', 'cpp')
    os.makedirs(smt_dir, exist_ok=True)
    os.makedirs(c_dir, exist_ok=True)
    os.makedirs(cpp_dir, exist_ok=True)

    # Avoid stale helper definitions when grammars change.
    solution_stem_override = os.getenv("SYNTH_SOLUTION_STEM", "").strip()
    for component in component_plan:
        if solution_stem_override:
            stem = solution_stem_override if component == final_component else f"{solution_stem_override}_{component}"
        else:
            stem = f"solution_{op_name}_{component}"
        stale = os.path.join(smt_dir, f"{stem}.smt2")
        if os.path.exists(stale):
            os.remove(stale)

    summary_path_env = os.getenv("SYNTH_SUMMARY_PATH", "").strip()
    try:
        for component in component_plan:
            # Only top-level components get directed I/O cases;
            # subcomponents use purely random samples so directed
            # cases (designed for full-pipeline semantics) don't
            # confuse intermediate representations.
            top_level_components = {
                "full_sum", "full_sum_combined",
                "full_product", "full_product_combined",
            }
            is_top_level = component in top_level_components

            if (
                isinstance(target_operation, MXINT8AdditionTarget)
                and component == "alignment"
                and alignment_directed_cases
            ):
                remaining = max(0, config.NUM_ITERATIONS - len(alignment_directed_cases))
                test_cases = alignment_directed_cases[:config.NUM_ITERATIONS] + synthesis_test_cases[:remaining]
            elif is_top_level:
                test_cases = synthesis_test_cases
            else:
                # Strip directed cases — use only random samples for subcomponents.
                n_directed = len(fp32_add_directed_cases) + len(fp32_mult_directed_cases)
                random_cases = synthesis_test_cases[n_directed:]
                # Ensure we have enough random cases.
                while len(random_cases) < config.NUM_ITERATIONS:
                    if sample_lo is not None and sample_hi is not None:
                        f1 = random.uniform(sample_lo, sample_hi)
                        f2 = random.uniform(sample_lo, sample_hi)
                    else:
                        f1 = random.uniform(-max_val, max_val)
                        f2 = random.uniform(-max_val, max_val)
                    random_cases.append((f1, f2))
                test_cases = random_cases[:config.NUM_ITERATIONS]

            program, metrics = synthesis_loop(
                target=target_operation,
                component_name=component,
                test_cases=test_cases,
                config=config
            )
            component_metrics[component] = metrics

            if not program:
                print(f"[ERROR] Synthesis failed for component '{component}'. Aborting.")
                break
            programs_by_component[component] = program

            if solution_stem_override:
                stem = solution_stem_override if component == final_component else f"{solution_stem_override}_{component}"
            else:
                stem = f"solution_{op_name}_{component}"
            output_filename = f"{stem}.smt2"
            output_path = os.path.join(smt_dir, output_filename)
            with open(output_path, "w") as f:
                f.write(program)
            print(f"\n Solution saved to: {output_path}")
            run_summary["paths"].setdefault("smt2", {})[component] = output_path

            if component == final_component:
                final_program = program
            else:
                print(f"[INFO] Completed helper component '{component}'.")

        run_summary["components"] = component_metrics

        if final_program and len(component_plan) > 1:
            print("\n--- All Synthesized Programs (Dependency Chain) ---")
            for component in component_plan:
                program = programs_by_component.get(component)
                if not program:
                    continue
                print(f"\n--- {component} ---")
                print(program.strip())

        if final_program:
            # Run the smt2c translation to get the C-like code
            from src.translate_smt_to_c import run_smt2c_translation
            final_stem = solution_stem_override or f"solution_{op_name}_{final_component}"
            c_output_path = run_smt2c_translation(
                os.path.join(smt_dir, f"{final_stem}.smt2"),
                c_dir,
                show_generated_code=SHOW_SMT2C_OUTPUT,
            )
            if not c_output_path:
                print("[ERROR] Stopping pipeline: smt2c translation failed.")
                raise SystemExit(1)
            run_summary["paths"]["c"] = c_output_path

            # Convert the generated C code to HLS-compatible C++
            from src.translate_to_hls_cpp import run_hls_conversion
            hls_cpp_path = run_hls_conversion(c_output_path)
            if not hls_cpp_path or not os.path.exists(hls_cpp_path):
                print("[ERROR] Stopping pipeline: HLS C++ conversion failed.")
                raise SystemExit(1)
            run_summary["paths"]["cpp"] = hls_cpp_path

            # Run the conversion from C++ to Verilog using Vitis HLS
            from src.run_vitis_hls import run_vitis_hls
            hw_metrics = run_vitis_hls(hls_cpp_path, impl=RUN_IMPLEMENTATION) or {}
            run_summary["hardware"] = hw_metrics
            if RUN_ACCURACY:
                repo_root = Path(__file__).resolve().parents[1]
                acc_metrics = run_accuracy_tests_for_solution(
                    target=target_operation,
                    component_name=final_component,
                    solution_name=Path(hls_cpp_path).stem,
                    repo_root=repo_root,
                )
                run_summary["accuracy"] = acc_metrics
            run_summary["status"] = "solved"
        else:
            run_summary["status"] = "failed"
    except Exception as exc:
        run_summary["status"] = "error"
        run_summary["error"] = f"{type(exc).__name__}: {exc}"
        raise
    finally:
        if summary_path_env:
            summary_path = Path(summary_path_env).expanduser().resolve()
            summary_path.parent.mkdir(parents=True, exist_ok=True)
            summary_path.write_text(json.dumps(run_summary, indent=2, sort_keys=True) + "\n")
