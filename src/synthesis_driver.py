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
        
    try:
        result = subprocess.run(
            ["cvc5", "--lang=sygus2", temp_filepath],
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
 
    #target_operation = DotProductTarget()
    #target_operation = MXINT8AdditionTarget()
    #target_operation = MXINT8MultiplicationTarget()
    #target_operation = FP32AdditionTarget()
    #target_operation = FP32MultiplicationTarget()

    # Operations for for NaiveAdderTarget(): 
    # NaiveAdderTarget(kind="int", width=32 or 8)
    # NaiveAdderTarget(kind="fp32")

    # Operations for for NaiveMultiplierTarget():
    # NaiveMultiplierTarget(kind="int", width=32 or 8)
    # NaiveMultiplierTarget(kind="fp32")
    
    target_operation = MXINT8AdditionTarget()
    
    # Components for MXINT8AdditionTarget: "alignment", "raw_sum", "overflow", "normalisation", "full_sum"
    # Components for MXINT8MultiplicationTarget: "renorm_flag", "mant", "exp", "full_product"
    # Components for FP32AdditionTarget: "fp32_alignment", "fp32_raw_sum", "fp32_normalisation", "fp32_full_sum"
    # Components for FP32MultiplicationTarget: "fp32_mantissa", "fp32_exponent"
    
    # Components for for NaiveAdderTarget: "int_add", "fp32_adder"
    # Components for for NaiveMultiplierTarget: "fp32_mul", "int_mul"

    target_component = "full_sum"
 
    # False for a quick post-synthesis estimate (-p)
    # True for a full post-implementation run (-i)
    RUN_IMPLEMENTATION = True
    
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
        if isinstance(target_operation, MXINT8AdditionTarget):
            max_val = 66
        elif isinstance(target_operation, MXINT8MultiplicationTarget):
            max_val = math.sqrt(112)
        elif isinstance(target_operation, (FP32AdditionTarget, FP32MultiplicationTarget)):
            max_val = 1e4

        for _ in range(config.NUM_ITERATIONS):
            f1 = random.uniform(-max_val, max_val)
            f2 = random.uniform(-max_val, max_val)
            synthesis_test_cases.append((f1, f2))

    # ===================================================================

    final_program = synthesis_loop(
        target=target_operation,
        component_name=target_component,
        test_cases=synthesis_test_cases,
        config=config
    )

    if final_program:
        
        op_name = target_operation.__class__.__name__.replace('Target','').lower()
        output_filename = f"solution_{op_name}_{target_component}.smt2"
        

        # Create organized results subdirectories
        smt_dir = os.path.join('results', 'smt2')
        c_dir = os.path.join('results', 'c')
        cpp_dir = os.path.join('results', 'cpp')
        os.makedirs(smt_dir, exist_ok=True)
        os.makedirs(c_dir, exist_ok=True)
        os.makedirs(cpp_dir, exist_ok=True)

        output_path = os.path.join(smt_dir, output_filename)

        with open(output_path, "w") as f:
            f.write(final_program)
        print(f"\n Solution saved to: {output_path}")

        # Run the smt2c translation to get the C-like code
        from src.translate_smt_to_c import run_smt2c_translation
        c_output_path = run_smt2c_translation(output_path, c_dir)

        # Convert the generated C code to HLS-compatible C++
        from src.translate_to_hls_cpp import run_hls_conversion
        run_hls_conversion(c_output_path)

        # Run the conversion from C++ to Verilog using Vitis HLS
        from src.run_vitis_hls import run_vitis_hls
        hls_cpp_path = os.path.join("results", "cpp", f"solution_{op_name}_{target_component}.cpp")
        run_vitis_hls(hls_cpp_path, impl=RUN_IMPLEMENTATION)