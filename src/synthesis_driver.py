import os
import random
import math
import subprocess
import tempfile
from pathlib import Path
from typing import List, Tuple, Dict, Optional, Callable

from .synthesis_targets.addition import AdditionTarget
from .synthesis_targets.multiplication import MultiplicationTarget
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
            print(f"SKIPPED: Constraint from ({f1:.3f}, {f2:.3f}) caused timeout or error.")

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
    target_operation = AdditionTarget()
    #target_operation = MultiplicationTarget()
    
    # Components for AdditionTarget: "alignment", "raw_sum", "overflow"
    # Components for MultiplicationTarget: "renorm_flag", "mant", "exp"
    
    #target_component = "dot_product_2_element"  
    target_component = "overflow"
    
    synthesis_test_cases = []
    if isinstance(target_operation, (AdditionTarget, MultiplicationTarget)):
        max_val = 66 if isinstance(target_operation, AdditionTarget) else math.sqrt(112)
        for _ in range(config.NUM_ITERATIONS):
            f1 = random.uniform(-max_val, max_val)
            f2 = random.uniform(-max_val, max_val)
            synthesis_test_cases.append((f1, f2))
            
    elif isinstance(target_operation, DotProductTarget):
        #
        vec_len = 2 
        max_val = 10 
        for _ in range(config.NUM_ITERATIONS):
            vec1 = [random.uniform(-max_val, max_val) for _ in range(vec_len)]
            vec2 = [random.uniform(-max_val, max_val) for _ in range(vec_len)]
            synthesis_test_cases.append((vec1, vec2))

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