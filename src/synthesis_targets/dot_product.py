from typing import Dict, Optional, List
import torch
from a_cx_mxint_quant.quantizers import mxint_hardware

def to_smt_bitvec(value: int, bits: int) -> str:
    """Converts an integer to its SMT-LIB two's complement bit-vector literal."""
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

class DotProductTarget:
    

    def calculate_ground_truth(
    self, 
    vec1_floats: List[float], 
    vec2_floats: List[float], 
    config
    ) -> Optional[Dict]:
        
        vec_len = len(vec1_floats)
        dot_product_parallelism = [1, vec_len]
        
        vec1_tensor = torch.tensor([vec1_floats])
        vec2_tensor = torch.tensor([vec2_floats])

        q_vec1, m1_tensor, e1_tensor = mxint_hardware(vec1_tensor, config.Q_CONFIG_IN, dot_product_parallelism)
        q_vec2, m2_tensor, e2_tensor = mxint_hardware(vec2_tensor, config.Q_CONFIG_IN, dot_product_parallelism)

        dot_product_result = torch.dot(q_vec1.flatten(), q_vec2.flatten())
        
        result_tensor = torch.tensor([[dot_product_result]])
        _, final_mant_t, final_exp_t = mxint_hardware(result_tensor, config.Q_CONFIG_OUT, [1, 1])

        m1s = [int(v) for v in m1_tensor.flatten()]
        e1s = [int(e1_tensor.flatten()[0])] * vec_len
        m2s = [int(v) for v in m2_tensor.flatten()]
        e2s = [int(e2_tensor.flatten()[0])] * vec_len

        return {
            "m1s": m1s, "e1s": e1s,
            "m2s": m2s, "e2s": e2s,
            "final_mant": int(final_mant_t.item()),
            "final_exp": int(final_exp_t.item()),
        }

    def gen_dot_product_2_element_constraint(self, data: Dict, config) -> str:
    
        m1a_bv, m1b_bv = [to_smt_bitvec(v, config.MANTISSA_WIDTH) for v in data['m1s']]
        e1a_bv, e1b_bv = [to_smt_bitvec(v, config.EXPONENT_WIDTH) for v in data['e1s']]
        m2a_bv, m2b_bv = [to_smt_bitvec(v, config.MANTISSA_WIDTH) for v in data['m2s']]
        e2a_bv, e2b_bv = [to_smt_bitvec(v, config.EXPONENT_WIDTH) for v in data['e2s']]
        
        final_mant_bv = to_smt_bitvec(data["final_mant"], config.MANTISSA_WIDTH)
        final_exp_bv = to_smt_bitvec(data["final_exp"], config.EXPONENT_WIDTH)

        oracle_result_bv = f"#b{final_mant_bv[2:]}{final_exp_bv[2:]}"
        
     
        all_args = [m1a_bv, e1a_bv, m1b_bv, e1b_bv, m2a_bv, e2a_bv, m2b_bv, e2b_bv]
        synth_call = f"(dot_product_2_element {' '.join(all_args)})"
        
        return f"(constraint (= {synth_call} {oracle_result_bv}))"
    
    def get_components(self) -> Dict:
        return {
            "dot_product_2_element": {
                "template": "sygus_grammars/dot_product_template.sl",
                "generator": self.gen_dot_product_2_element_constraint,
            }
        }