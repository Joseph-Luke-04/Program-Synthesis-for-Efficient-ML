import os, random, math, subprocess, tempfile, re
from pathlib import Path
from typing import List, Tuple, Dict, Optional, Callable
from src.dependencies import DEPENDENCY_MAP

from .synthesis_targets.addition.mxint8_addition import MXINT8AdditionTarget
from .synthesis_targets.multiplication.mxint8_multiplication import MXINT8MultiplicationTarget

from .synthesis_targets.addition.fp32_addition import FP32AdditionTarget
from .synthesis_targets.multiplication.fp32_multiplication import FP32MultiplicationTarget
from .synthesis_targets.addition.naive_adder import NaiveAdderTarget
from .synthesis_targets.multiplication.naive_multiplier import NaiveMultiplierTarget

from .synthesis_targets.dot_product import DotProductTarget

# Default: preserve solver output (disable add_full_sum canonicaliser).
# Set ENABLE_MXINT8_ADD_FULL_SUM_CANON=1 to force the canonicaliser.
os.environ.setdefault("ENABLE_MXINT8_ADD_FULL_SUM_CANON", "0")

# Toggle SyGuS candidate dump (-o sygus) here. Set to True to enable.
ENABLE_SYGUS_DUMP = False
# Toggle fast SyGuS enumerator (cvc5 --sygus-enum=fast) here.
ENABLE_SYGUS_FAST_ENUM = False
# Toggle printing full smt2c-generated C code in terminal.
SHOW_SMT2C_OUTPUT = False


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
    SOLVER_TIMEOUT_SECONDS: int = 15
    NUM_ITERATIONS: int = 30
    

def run_cvc5_synthesis(sygus_query: str, timeout: int) -> Optional[str]:
  
    with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=".sl") as temp_f:
        temp_f.write(sygus_query)
        temp_filepath = temp_f.name
        
    cmd = ["cvc5", "--lang=sygus2"]
    if ENABLE_SYGUS_FAST_ENUM:
        cmd.append("--sygus-enum=fast")
    if ENABLE_SYGUS_DUMP:
        cmd += ["-o", "sygus"]
    cmd.append(temp_filepath)
    try:
        result = subprocess.run(
            cmd,
            capture_output=True, text=True, timeout=timeout
        )
        if result.stderr:
            print(f"[CVC5 STDERR]:\n{result.stderr}")

        solution_text = result.stdout.strip()
        if "(define-fun" in solution_text:
            # CVC5 sometimes wraps the solution in an extra top-level s-expression
            # like "(\n(define-fun ...)\n)", which complicates downstream parsing.
            # We remove that outer wrapper while keeping the inner definitions intact.
            solution_text = unwrap_extra_parens(solution_text)
            return solution_text
        else:
            print(f"[CVC5] Solver did not return a valid solution.\n[STDOUT]:\n{solution_text}")
            return None

    except subprocess.TimeoutExpired:
        print(f"[CVC5] Solver timed out after {timeout} seconds.")
        return None
    except FileNotFoundError:
        print("[ERROR] 'cvc5' command not found.")
        return None
    finally:
    
        if os.path.exists(temp_filepath):
            os.remove(temp_filepath)
            

def synthesis_loop(
    target, 
    component_name: str,
    test_cases: List[Tuple[float, float]],
    config: SynthesisConfig
) -> Optional[str]:
   
    try:
        component = target.get_components()[component_name]
        template_file = component["template"]
        constraint_generator = component["generator"]
    except KeyError:
        print(f"[ERROR] Component '{component_name}' not found for target '{target.__class__.__name__}'.")
        print(f"Available components are: {list(target.get_components().keys())}")
        return None

    print(f"--- Starting Synthesis for [{target.__class__.__name__} -> {component_name}] ---")
    
    try:
        with open(template_file, "r") as f:
            base_sygus_query = f.read()
            op_name = target.get_op_name()
            dep_map = target.get_dependency_map()
            dep_key = f"{op_name}_{component_name}"
            deps = dep_map.get(dep_key, [])

            # Ensure (set-logic ...) remains the very first command even after
            # we prepend helper definitions.
            logic_match = re.match(r"\s*(\(set-logic[^\)]*\)\s*)", base_sygus_query, re.IGNORECASE)
            if logic_match:
                logic_cmd = logic_match.group(1)
                rest_query = base_sygus_query[logic_match.end():]
            else:
                logic_cmd = "(set-logic ALL)\n"
                rest_query = base_sygus_query

            if deps:
                helper_defs = collect_helper_definitions(deps)
                base_sygus_query = logic_cmd + helper_defs + "\n" + rest_query
            else:
                base_sygus_query = logic_cmd + rest_query
            
    except FileNotFoundError:
        print(f"[ERROR] Template file not found: {template_file}")
        return None

    accepted_constraints = []
    current_best_program = None

    for i, args in enumerate(test_cases):
        print(f"\n--- Iteration {i+1}/{len(test_cases)} ---")
        print(f"Generating new constraint with inputs: {args}")
        
        ground_truth_data = target.calculate_ground_truth(*args, config)
        
        if not ground_truth_data:
            print(f"Could not generate ground truth for inputs {args}. Skipping.")
            continue
        

        new_constraint = constraint_generator(ground_truth_data, config)
        print(new_constraint)
        constraints_to_test = accepted_constraints + [new_constraint]
        
        sygus_query = (
            base_sygus_query + 
            "\n; --- CONSTRAINTS ---\n" + 
            "\n".join(constraints_to_test) + 
            "\n\n(check-synth)\n"
        )
        
        solution = run_cvc5_synthesis(sygus_query, config.SOLVER_TIMEOUT_SECONDS)

        if solution:
            accepted_constraints.append(new_constraint)
            current_best_program = solution
            print(f"SUCCESS: Constraint accepted. Total constraints: {len(accepted_constraints)}")
        else:
            a, b = args
            print(f"SKIPPED: Constraint from ({a:.3f}, {b:.3f}) caused timeout or error.")

    print("\n\n--- Synthesis Complete! ---")
    print(f"\nConstraints accepted: {len(accepted_constraints)}/{len(test_cases)}")
    if current_best_program:
        print("\n--- Final Synthesized Program ---")
        print(current_best_program)
    else:
        print("Could not find a valid program that satisfies any constraints.")
    return current_best_program


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


if __name__ == "__main__":
    config = SynthesisConfig()

    # Representable range is +-112
    
    #max_val = 66
    max_val = math.sqrt(112)
    
    custom_cases = [
        (1.5, 1.5), (0.75, 1.0), (7.5, 0.25), (0.25, 0.5),
        (4.0, 4.0), (-2.0, 3.5), (1.0, 1.0), (7.5, 7.5)
    ]

    """
    num_needed = config.NUM_ITERATIONS - len(custom_cases)
    if num_needed > 0:
        random_cases = [(random.uniform(-max_val, max_val), random.uniform(-max_val, max_val))
                        for _ in range(num_needed)]
        synthesis_test_cases = custom_cases + random_cases
    else:
        synthesis_test_cases = custom_cases[:config.NUM_ITERATIONS]
    """
 
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
    #   FP32AdditionTarget:         ["fp32_alignment", "fp32_raw_sum", "fp32_normalisation", 
    #                                "fp32_full_sum", "fp32_full_sum_combined"]
    # -----------------------------------------------------------------------------------
    #   FP32MultiplicationTarget:   ["renorm", "exp", "mant", "full_product", "full_product_combined"]
    # -----------------------------------------------------------------------------------
    #   NaiveAdderTarget:           ["int_add", "fp32_adder"]
    # -----------------------------------------------------------------------------------
    #   NaiveMultiplierTarget:      ["int_mul", "fp32_mul"]
    # =========================================================================

    target_operation = MXINT8AdditionTarget()
    target_component = "full_sum"

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
 
    # False for a quick post-synthesis estimate (-p)
    # True for a full post-implementation run (-i)
    RUN_IMPLEMENTATION = _env_flag("SYNTH_RUN_IMPL", True)
    # Directed (hand-picked) IO constraint seeds to 
    # guide synthesiser for monolithic components.
    ENABLE_DIRECTED_IO_CONSTRAINTS = _env_flag("SYNTH_ENABLE_DIRECTED_IO", True)

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

    print(f"[INFO] Target: {target_operation.__class__.__name__} | Component: {target_component}")
    print(f"[INFO] NUM_ITERATIONS={config.NUM_ITERATIONS}, TIMEOUT={config.SOLVER_TIMEOUT_SECONDS}s, RUN_IMPLEMENTATION={RUN_IMPLEMENTATION}, DIRECTED_IO={ENABLE_DIRECTED_IO_CONSTRAINTS}")
    
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
            max_val = 1e4
            # Diagnostic FP32 mult cases to hit specific branches early.
            # Renorm=1 tends to occur when product in [2,4).
            # Renorm=0 tends to occur when product in [1,2).
            fp32_mult_directed_cases = [
                (1.5, 1.5),   # renorm = 1 (approx 2.25)
                (1.25, 1.25), # renorm = 0 (approx 1.5625)
                (-1.5, 1.5),  # mixed sign
                (1.5, -1.5),  # mixed sign (opposite)
                # Rounding-sensitive: near-halfway in mantissa rounding
                (float.fromhex("0x1.000002p+0"), float.fromhex("0x1.000002p+0")),
            ]
        elif isinstance(target_operation, FP32AdditionTarget):
            max_val = 1e4
            # Directed FP32 add cases to exercise specific branches first.
            fp32_add_directed_cases = [
                # Swap / exp tie-break by mantissa.
                (1.25, 1.5),
                (1.5, 1.25),

                # Small exponent gaps (clean alignment).
                (1.5, 0.75),
                (1.5, 0.375),
                (1.5, 0.1875),

                # Same-sign overflow (right shift + exp increment).
                (1.5, 1.5),
                (1.75, 1.75),

                # Opposite-sign controlled cancellation (<=2 left shifts).
                (1.5, -1.25),
                (1.25, -1.0),

                # Huge exponent gap where small addend is negligible.
                (8192.0, 1e-6),
            ]

        if ENABLE_DIRECTED_IO_CONSTRAINTS and fp32_add_directed_cases:
            synthesis_test_cases.extend(fp32_add_directed_cases[:config.NUM_ITERATIONS])
        if ENABLE_DIRECTED_IO_CONSTRAINTS and fp32_mult_directed_cases:
            synthesis_test_cases.extend(fp32_mult_directed_cases[:config.NUM_ITERATIONS])

        while len(synthesis_test_cases) < config.NUM_ITERATIONS:
            f1 = random.uniform(-max_val, max_val)
            f2 = random.uniform(-max_val, max_val)
            synthesis_test_cases.append((f1, f2))

    # ===================================================================

    op_name = _op_name_for_target(target_operation)
    component_plan = resolve_component_plan(target_operation, target_component)
    if len(component_plan) > 1:
        print(f"[INFO] Synthesizing dependency chain: {component_plan}")

    final_program = None
    final_component = component_plan[-1]
    programs_by_component: dict[str, str] = {}

    # Create organized results subdirectories
    smt_dir = os.path.join('results', 'smt2')
    c_dir = os.path.join('results', 'c')
    cpp_dir = os.path.join('results', 'cpp')
    os.makedirs(smt_dir, exist_ok=True)
    os.makedirs(c_dir, exist_ok=True)
    os.makedirs(cpp_dir, exist_ok=True)

    # Avoid stale helper definitions when grammars change.
    for component in component_plan:
        stale = os.path.join(smt_dir, f"solution_{op_name}_{component}.smt2")
        if os.path.exists(stale):
            os.remove(stale)

    for component in component_plan:
        if (
            isinstance(target_operation, MXINT8AdditionTarget)
            and component == "alignment"
            and alignment_directed_cases
        ):
            remaining = max(0, config.NUM_ITERATIONS - len(alignment_directed_cases))
            test_cases = alignment_directed_cases[:config.NUM_ITERATIONS] + synthesis_test_cases[:remaining]
        else:
            test_cases = synthesis_test_cases

        program = synthesis_loop(
            target=target_operation,
            component_name=component,
            test_cases=test_cases,
            config=config
        )
        if not program:
            print(f"[ERROR] Synthesis failed for component '{component}'. Aborting.")
            break
        programs_by_component[component] = program

        output_filename = f"solution_{op_name}_{component}.smt2"
        output_path = os.path.join(smt_dir, output_filename)
        with open(output_path, "w") as f:
            f.write(program)
        print(f"\n Solution saved to: {output_path}")

        if component == final_component:
            final_program = program
        else:
            print(f"[INFO] Completed helper component '{component}'.")

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
        c_output_path = run_smt2c_translation(
            os.path.join(smt_dir, f"solution_{op_name}_{final_component}.smt2"),
            c_dir,
            show_generated_code=SHOW_SMT2C_OUTPUT,
        )

        # Convert the generated C code to HLS-compatible C++
        from src.translate_to_hls_cpp import run_hls_conversion
        run_hls_conversion(c_output_path)

        # Run the conversion from C++ to Verilog using Vitis HLS
        from src.run_vitis_hls import run_vitis_hls
        hls_cpp_path = os.path.join("results", "cpp", f"solution_{op_name}_{final_component}.cpp")
        run_vitis_hls(hls_cpp_path, impl=RUN_IMPLEMENTATION)
