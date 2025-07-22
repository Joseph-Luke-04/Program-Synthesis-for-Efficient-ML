import os
import random
import math
import subprocess
import tempfile
from typing import List, Tuple, Dict, Optional, Callable

from .synthesis_targets.addition import AdditionTarget
from .synthesis_targets.multiplication import MultiplicationTarget

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

    for i, (f1, f2) in enumerate(test_cases):
        print(f"\n--- Iteration {i+1}/{len(test_cases)} ---")
        
        ground_truth_data = target.calculate_ground_truth(f1, f2, config)
        if not ground_truth_data:
            print(f"Could not generate ground truth for floats ({f1:.3f}, {f2:.3f}). Skipping.")
            continue
        

        new_constraint = constraint_generator(ground_truth_data, config)
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
    if current_best_program:
        print("\n--- Final Synthesized Program ---")
        print(current_best_program)
    else:
        print("Could not find a valid program that satisfies any constraints.")
        
    return current_best_program


if __name__ == "__main__":
    config = SynthesisConfig()

    max_val = math.sqrt(112)
    synthesis_test_cases = [(random.uniform(-max_val, max_val), random.uniform(-max_val, max_val)) 
                             for _ in range(config.NUM_ITERATIONS)]

 

    
    # target_operation = AdditionTarget()
    target_operation = MultiplicationTarget()

    
    # Components for AdditionTarget: todo
    # Components for MultiplicationTarget: "renorm_flag", "mantissa", "exponent"
    
    target_component = "renorm_flag"

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
        

        if not os.path.exists('results'):
            os.makedirs('results')
            
        output_path = os.path.join('results', output_filename)

        with open(output_path, "w") as f:
            f.write(final_program)
        print(f"\n Solution saved to: {output_path}")