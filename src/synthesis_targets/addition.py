
from typing import Dict, Optional
import torch
from a_cx_mxint_quant.quantizers import mxint_hardware

def to_smt_bitvec(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

class AdditionTarget:

    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
       
        tensor1 = torch.tensor([[float1]])
        tensor2 = torch.tensor([[float2]])
        
        dequant1, m1_t, e1_t = mxint_hardware(tensor1, config.Q_CONFIG_IN, config.PARALLELISM)
        dequant2, m2_t, e2_t = mxint_hardware(tensor2, config.Q_CONFIG_IN, config.PARALLELISM)
        m1, e1, m2, e2 = int(m1_t.item()), int(e1_t.item()), int(m2_t.item()), int(e2_t.item())

        # Alignment
        target_exponent = max(e1, e2)
        shift_amount = abs(e1 - e2)
        aligned_m1, aligned_m2 = (m1, m2 >> shift_amount) if e1 >= e2 else (m1 >> shift_amount, m2)

        # Raw Sum 
        raw_sum_mantissa = aligned_m1 + aligned_m2

        # Overflow Detection 
        INT4_MAX = (2**(config.MANTISSA_WIDTH - 1)) - 1
        INT4_MIN = -(2**(config.MANTISSA_WIDTH - 1))
        overflow_flag = 1 if (raw_sum_mantissa > INT4_MAX or raw_sum_mantissa < INT4_MIN) else 0

        sum_dequant = dequant1 + dequant2
        _, final_mant_t, final_exp_t = mxint_hardware(sum_dequant, config.Q_CONFIG_OUT, config.PARALLELISM)

        return {
            "m1": m1, "e1": e1, "m2": m2, "e2": e2,
            "aligned_m1": aligned_m1, "aligned_m2": aligned_m2,
            "target_exponent": target_exponent,
            "raw_sum_mantissa": raw_sum_mantissa,
            "overflow_flag": overflow_flag,
            "final_mant": int(final_mant_t.item()),
            "final_exp": int(final_exp_t.item()),
        }
        
    def gen_alignment_constraint(self, data: Dict, config) -> str:
            m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
            e1_bv = to_smt_bitvec(data["e1"], config.EXPONENT_WIDTH)
            m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
            e2_bv = to_smt_bitvec(data["e2"], config.EXPONENT_WIDTH)
            
            target_exp_bv = to_smt_bitvec(data["target_exponent"], config.EXPONENT_WIDTH)
            aligned_m1_bv = to_smt_bitvec(data["aligned_m1"], config.MANTISSA_WIDTH)
            aligned_m2_bv = to_smt_bitvec(data["aligned_m2"], config.MANTISSA_WIDTH)
            
            concatenated_mantissas = f"#b{aligned_m1_bv[2:]}{aligned_m2_bv[2:]}"
            
            exp_constraint = f"(constraint (= (select_exponent {e1_bv} {e2_bv}) {target_exp_bv}))"
            mant_constraint = f"(constraint (= (align_mantissas {m1_bv} {e1_bv} {m2_bv} {e2_bv}) {concatenated_mantissas}))"
            return f"{exp_constraint}\n{mant_constraint}"

    def gen_raw_sum_constraint(self, data: Dict, config) -> str:
        m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
        e1_bv = to_smt_bitvec(data["e1"], config.EXPONENT_WIDTH)
        m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
        e2_bv = to_smt_bitvec(data["e2"], config.EXPONENT_WIDTH)

        raw_sum_bv = to_smt_bitvec(data["raw_sum_mantissa"], config.RAW_SUM_MANTISSA_WIDTH)
        target_exp_bv = to_smt_bitvec(data["target_exponent"], config.EXPONENT_WIDTH)
        concatenated_result = f"#b{raw_sum_bv[2:]}{target_exp_bv[2:]}"

        return f"(constraint (= (add_raw {m1_bv} {e1_bv} {m2_bv} {e2_bv}) {concatenated_result}))"

    def gen_overflow_flag_constraint(self, data: Dict, config) -> str:
        raw_sum_bv = to_smt_bitvec(data["raw_sum_mantissa"], config.RAW_SUM_MANTISSA_WIDTH)
        flag_bv = to_smt_bitvec(data["overflow_flag"], 1)
        return f"(constraint (= (detect_overflow {raw_sum_bv}) {flag_bv}))"
    
    def gen_mant_constraint(self, data: Dict, config) -> str:
        m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
        e1_bv = to_smt_bitvec(data["e1"], config.EXPONENT_WIDTH)
        m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
        e2_bv = to_smt_bitvec(data["e2"], config.EXPONENT_WIDTH)
        final_mant_bv = to_smt_bitvec(data["final_mant"], config.MANTISSA_WIDTH)
        
        synth_call = f"(add_mxint_mant {m1_bv} {e1_bv} {m2_bv} {e2_bv})"
        return f"(constraint (= {synth_call} {final_mant_bv}))"

    def gen_exp_constraint(self, data: Dict, config) -> str:
        m1_bv = to_smt_bitvec(data["m1"], config.MANTISSA_WIDTH)
        e1_bv = to_smt_bitvec(data["e1"], config.EXPONENT_WIDTH)
        m2_bv = to_smt_bitvec(data["m2"], config.MANTISSA_WIDTH)
        e2_bv = to_smt_bitvec(data["e2"], config.EXPONENT_WIDTH)
        final_exp_bv = to_smt_bitvec(data["final_exp"], config.EXPONENT_WIDTH)

        synth_call = f"(add_mxint_exp {m1_bv} {e1_bv} {m2_bv} {e2_bv})"
        return f"(constraint (= {synth_call} {final_exp_bv}))"

    def gen_finalization_constraint(self, data: Dict, config) -> str:
        raw_sum_bv = to_smt_bitvec(data["raw_sum_mantissa"], config.RAW_SUM_MANTISSA_WIDTH)
        target_exp_bv = to_smt_bitvec(data["target_exponent"], config.EXPONENT_WIDTH)
        
        final_mant_bv = to_smt_bitvec(data["final_mant"], config.MANTISSA_WIDTH)
        final_exp_bv = to_smt_bitvec(data["final_exp"], config.EXPONENT_WIDTH)
        final_result_bv = f"#b{final_mant_bv[2:]}{final_exp_bv[2:]}"
        
        return f"(constraint (= (finalize_addition {raw_sum_bv} {target_exp_bv}) {final_result_bv}))"

    def get_components(self) -> Dict:
        
        return {
            "alignment": {
                "template": "sygus_grammars/add_alignment_template.sl",
                "generator": self.gen_alignment_constraint,
            },
            "raw_sum": {
                "template": "sygus_grammars/add_raw_sum_template.sl",
                "generator": self.gen_raw_sum_constraint,
            },
            "overflow": {
                "template": "sygus_grammars/add_detect_overflow_template.sl",
                "generator": self.gen_overflow_flag_constraint,
            },
            #"finalization": {
            #    "template": "sygus_grammars/add_finalize_template.sl",
            #    "generator": self.gen_finalization_constraint,
            #},
        }