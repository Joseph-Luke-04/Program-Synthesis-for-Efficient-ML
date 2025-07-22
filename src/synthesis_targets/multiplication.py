from typing import Dict, Optional
import torch
from a_cx_mxint_quant.quantizers import mxint_hardware

def to_smt_bitvec(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

class MultiplicationTarget:
    
    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
        """
        Calculates all ground truth values for multiplication.
        """
        tensor1 = torch.tensor([[float1]])
        tensor2 = torch.tensor([[float2]])


        dequant1, m1_t, e1_t = mxint_hardware(tensor1, config.Q_CONFIG_IN, config.PARALLELISM)
        dequant2, m2_t, e2_t = mxint_hardware(tensor2, config.Q_CONFIG_IN, config.PARALLELISM)
        m1, e1, m2, e2 = int(m1_t.item()), int(e1_t.item()), int(m2_t.item()), int(e2_t.item())

        if dequant1.item() == 0.0 or dequant2.item() == 0.0:
            return None

        renorm_flag = 0
        try:
            true_mant1 = abs(dequant1.item()) / (2**e1)
            true_mant2 = abs(dequant2.item()) / (2**e2)
            mant_product = true_mant1 * true_mant2
            if mant_product <= 0.5 and mant_product > 0:
                renorm_flag = 1
        except (ZeroDivisionError, OverflowError):
            renorm_flag = 0

        product_dequant = dequant1 * dequant2
        _, final_mant_t, final_exp_t = mxint_hardware(product_dequant, config.Q_CONFIG_OUT, config.PARALLELISM)

        return {
            "m1": m1, "e1": e1, "m2": m2, "e2": e2,
            "final_mant": int(final_mant_t.item()),
            "final_exp": int(final_exp_t.item()),
            "renorm_flag": renorm_flag  
        }

    def gen_renorm_flag_constraint(self, data: Dict, config) -> str:
        m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
        m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
        flag_bv = to_smt_bitvec(data["renorm_flag"], 1)

        synth_call = f"(mult_renorm_flag {m1_bv} {m2_bv})"
        return f"(constraint (= {synth_call} {flag_bv}))"

    def gen_mantissa_constraint(self, data: Dict, config) -> str:
        m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
        m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
        final_mant_bv = to_smt_bitvec(data["final_mant"], config.MANTISSA_WIDTH)
        
        synth_call = f"(mult_mxint_mant {m1_bv} {m2_bv})"
        return f"(constraint (= {synth_call} {final_mant_bv}))"

    def gen_exponent_constraint(self, data: Dict, config) -> str:
        e1_bv = to_smt_bitvec(data["e1"], config.EXPONENT_WIDTH)
        e2_bv = to_smt_bitvec(data["e2"], config.EXPONENT_WIDTH)
        renorm_flag_bv = to_smt_bitvec(data["renorm_flag"], 1) 
        final_exp_bv = to_smt_bitvec(data["final_exp"], config.EXPONENT_WIDTH)

        synth_call = f"(mult_mxint_exp {e1_bv} {e2_bv} {renorm_flag_bv})"
        return f"(constraint (= {synth_call} {final_exp_bv}))"

    def get_components(self) -> Dict:
    
        return {
            "renorm_flag": {
                "template": "sygus_grammars/mult_renorm_flag_template.sl",
                "generator": self.gen_renorm_flag_constraint,
            },
            "mantissa": {
                "template": "sygus_grammars/mult_mant_template.sl",
                "generator": self.gen_mantissa_constraint,
            },
            "exponent": {
                "template": "sygus_grammars/mult_exp_template.sl",
                "generator": self.gen_exponent_constraint,
            },
        }