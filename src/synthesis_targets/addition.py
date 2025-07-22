# src/synthesis_targets/addition.py

from typing import Dict, Optional
import torch
from a_cx_mxint_quant.quantizers import mxint_hardware

def to_smt_bitvec(value: int, bits: int) -> str:
    """Converts an integer to its SMT-LIB two's complement bit-vector literal."""
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

class AdditionTarget:
    """Encapsulates all logic for synthesizing components of MXInt addition."""

    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
        """Calculates all intermediate and final values for an MXInt addition."""
        tensor1 = torch.tensor([[float1]])
        tensor2 = torch.tensor([[float2]])

        # Get quantized values from the hardware oracle
        _, m1_t, e1_t = mxint_hardware(tensor1, config.Q_CONFIG_IN, config.PARALLELISM)
        _, m2_t, e2_t = mxint_hardware(tensor2, config.Q_CONFIG_IN, config.PARALLELISM)
        m1, e1, m2, e2 = int(m1_t.item()), int(e1_t.item()), int(m2_t.item()), int(e2_t.item())

        # Calculate intermediate steps
        target_exponent = max(e1, e2)
        shift_amount = abs(e1 - e2)
        aligned_m1, aligned_m2 = (m1, m2 >> shift_amount) if e1 >= e2 else (m1 >> shift_amount, m2)
        raw_sum_mantissa = aligned_m1 + aligned_m2

        # Get final result from the hardware oracle
        dequant1 = m1_t.float() * (2.0**e1_t.float())
        dequant2 = m2_t.float() * (2.0**e2_t.float())
        sum_dequant = dequant1 + dequant2
        _, final_mant_t, final_exp_t = mxint_hardware(sum_dequant, config.Q_CONFIG_OUT, config.PARALLELISM)

        return {
            "m1": m1, "e1": e1, "m2": m2, "e2": e2,
            "raw_sum_mantissa": raw_sum_mantissa,
            "target_exponent": target_exponent,
            "final_mant": int(final_mant_t.item()),
            "final_exp": int(final_exp_t.item()),
        }

    def gen_final_add_constraint(self, data: Dict, config) -> str:
        """Generates a constraint for the final saturation/rounding step."""
        raw_sum_bv = to_smt_bitvec(data["raw_sum_mantissa"], config.RAW_SUM_MANTISSA_WIDTH)
        target_exp_bv = to_smt_bitvec(data["target_exponent"], config.EXPONENT_WIDTH)
        final_mant_bv = to_smt_bitvec(data["final_mant"], config.MANTISSA_WIDTH)
        final_exp_bv = to_smt_bitvec(data["final_exp"], config.EXPONENT_WIDTH)
        final_result_bv = f"#b{final_mant_bv[2:]}{final_exp_bv[2:]}"
        
        synth_call = f"(finalize_addition {raw_sum_bv} {target_exp_bv})"
        return f"(constraint (= {synth_call} {final_result_bv}))"
    
    def get_components(self) -> Dict:
        return {
            "finalization": {
                "template": "sygus_grammars/add_finalize_template.sl",
                "generator": self.gen_final_add_constraint,
            },
        }