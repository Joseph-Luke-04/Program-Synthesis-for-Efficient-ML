from typing import Dict, Optional
import struct
import numpy as np

def to_smt_bitvec(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

def fp32_match_constraint(call_expr: str, expected_expr: str, msb_bits: int) -> str:
    """Build exact or approximate FP32 equality over the top-msb bits."""
    total_bits = 32
    if msb_bits <= 0:
        raise ValueError(f"FP32_OUTPUT_MATCH_MSB_BITS must be in [1, 32], got {msb_bits}.")
    if msb_bits >= total_bits:
        return f"(constraint (= {call_expr} {expected_expr}))"

    low = total_bits - msb_bits
    return (
        f"(constraint (= ((_ extract {total_bits - 1} {low}) {call_expr}) "
        f"((_ extract {total_bits - 1} {low}) {expected_expr})))"
    )

def float_to_components(value: float) -> Dict[str, int]:
    """Convert a float32 value to its sign, exponent, and mantissa components."""
    bits = struct.unpack('<I', struct.pack('<f', value))[0]

    sign = (bits >> 31) & 0x1
    exponent = (bits >> 23) & 0xFF
    mantissa = bits & 0x7FFFFF

    return {
        "sign": sign,
        "exponent": exponent,
        "mantissa": mantissa
    }


class FP32AdditionTarget:

    def get_op_name(self) -> str:
        return "fp32addition"
    
    def get_dependency_map(self) -> Dict[str, list[str]]:
        from src.dependencies import DEPENDENCY_MAP
        return DEPENDENCY_MAP

    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
        if not (np.isfinite(float1) and np.isfinite(float2)):
            return None
        
        c1 = float_to_components(float1)
        c2 = float_to_components(float2)

        # 24-bit mantissas with hidden 1 (ignoring subnormals here)
        m1_full = (1 << 23) | c1["mantissa"]
        m2_full = (1 << 23) | c2["mantissa"]

        # Align exponents
        if c1["exponent"] > c2["exponent"]:
            exp_diff = c1["exponent"] - c2["exponent"]
            aligned_m1 = m1_full
            aligned_m2 = m2_full >> exp_diff
            target_exponent = c1["exponent"]
        else:
            exp_diff = c2["exponent"] - c1["exponent"]
            aligned_m1 = m1_full >> exp_diff
            aligned_m2 = m2_full
            target_exponent = c2["exponent"]

        # Sign-aware add/sub
        if c1["sign"] == c2["sign"]:
            raw_sum_mantissa = aligned_m1 + aligned_m2  # up to 25 bits
            result_sign = c1["sign"]
        else:
            if aligned_m1 >= aligned_m2:
                raw_sum_mantissa = aligned_m1 - aligned_m2
                result_sign = c1["sign"]
            else:
                raw_sum_mantissa = aligned_m2 - aligned_m1
                result_sign = c2["sign"]

        # Normalise: place MSB at bit index 23
        msb_index = raw_sum_mantissa.bit_length() - 1
        norm_shift_amount = msb_index - 23

        if norm_shift_amount > 0:
            # Too wide (carry into bit 24): shift RIGHT, exponent increases
            normalised_mantissa = raw_sum_mantissa >> norm_shift_amount
        else:
            # Too narrow: shift LEFT, exponent decreases
            normalised_mantissa = raw_sum_mantissa << (-norm_shift_amount)

        final_exponent = target_exponent + norm_shift_amount
        final_mantissa = normalised_mantissa & 0x7FFFFF  # keep 23-bit fraction

        # Zero sum case
        if raw_sum_mantissa == 0:
            return {
                "s1": c1["sign"], "e1": c1["exponent"], "m1": c1["mantissa"],
                "s2": c2["sign"], "e2": c2["exponent"], "m2": c2["mantissa"],

                "aligned_m1": 0,
                "aligned_m2": 0,
                "target_exponent": target_exponent,

                "raw_sum_mantissa": 0,
                "raw_sign": 0,

                "final_sign": 0,
                "final_exponent": 0,
                "final_mantissa": 0,
            }
        else:
            return {
                "s1": c1["sign"], "e1": c1["exponent"], "m1": c1["mantissa"],
                "s2": c2["sign"], "e2": c2["exponent"], "m2": c2["mantissa"],

                "aligned_m1": aligned_m1,
                "aligned_m2": aligned_m2,
                "target_exponent": target_exponent,

                "raw_sum_mantissa": raw_sum_mantissa,
                "raw_sign": result_sign,

                "final_sign": result_sign,
                "final_exponent": final_exponent,
                "final_mantissa": final_mantissa,
            }

    
    def gen_alignment_constraint(self, data: Dict, config) -> str:
        # The hardware block will receive the raw 8-bit exponents and 23-bit mantissas.
        e1_bv = to_smt_bitvec(data["e1"], 8)
        m1_bv = to_smt_bitvec(data["m1"], 23)
        e2_bv = to_smt_bitvec(data["e2"], 8)
        m2_bv = to_smt_bitvec(data["m2"], 23)

        aligned_m1_bv = to_smt_bitvec(data["aligned_m1"], 24)
        aligned_m2_bv = to_smt_bitvec(data["aligned_m2"], 24)
        target_exponent_bv = to_smt_bitvec(data["target_exponent"], 8)

        # The function to synthesize will take the original E/M values.
        synth_call = f"(fp32_aligner {e1_bv} {m1_bv} {e2_bv} {m2_bv})"
        # The hardware should output the two aligned mantissas and the chosen exponent.
        # We concatenate them into one wide bitvector for the solver.
        expected_output = f"(concat {aligned_m1_bv} (concat {aligned_m2_bv} {target_exponent_bv}))"
        return f"(constraint (= {synth_call} {expected_output}))"

    def gen_raw_sum_constraint(self, data: Dict, config) -> str:
        # This block takes the original signs and the ALIGNED mantissas from the previous stage.
        s1_bv = to_smt_bitvec(data["s1"], 1)
        aligned_m1_bv = to_smt_bitvec(data["aligned_m1"], 24)
        s2_bv = to_smt_bitvec(data["s2"], 1)
        aligned_m2_bv = to_smt_bitvec(data["aligned_m2"], 24)

        raw_sum_mantissa_bv = to_smt_bitvec(data["raw_sum_mantissa"], 25)
        raw_sign_bv = to_smt_bitvec(data["raw_sign"], 1)

        synth_call = f"(fp32_raw_summer {s1_bv} {aligned_m1_bv} {s2_bv} {aligned_m2_bv})"
        expected_output = f"(concat {raw_sign_bv} {raw_sum_mantissa_bv})"
        return f"(constraint (= {synth_call} {expected_output}))"


    def gen_normalisation_constraint(self, data: Dict, config) -> str:
        # This block takes the results from the previous two stages.
        raw_sum_mantissa_bv = to_smt_bitvec(data["raw_sum_mantissa"], 25)
        raw_sign_bv = to_smt_bitvec(data["raw_sign"], 1)
        target_exponent_bv = to_smt_bitvec(data["target_exponent"], 8)

        # --- EXPECTED OUTPUTS from this hardware block ---
        # The final, packed IEEE 754 components.
        final_sign_bv = to_smt_bitvec(data["final_sign"], 1)
        final_exponent_bv = to_smt_bitvec(data["final_exponent"], 8)
        final_mantissa_bv = to_smt_bitvec(data["final_mantissa"], 23)

        synth_call = f"(fp32_normaliser {raw_sum_mantissa_bv} {raw_sign_bv} {target_exponent_bv})"
        expected_output = f"(concat {final_sign_bv} (concat {final_exponent_bv} {final_mantissa_bv}))"
        return f"(constraint (= {synth_call} {expected_output}))"
    

    def gen_sum_constraint(self, data, config) -> str:
        s1 = to_smt_bitvec(data["s1"], 1); e1 = to_smt_bitvec(data["e1"], 8); m1 = to_smt_bitvec(data["m1"], 23)
        s2 = to_smt_bitvec(data["s2"], 1); e2 = to_smt_bitvec(data["e2"], 8); m2 = to_smt_bitvec(data["m2"], 23)

        final_sign     = to_smt_bitvec(data["final_sign"], 1)
        final_exponent = to_smt_bitvec(data["final_exponent"], 8)
        final_mantissa = to_smt_bitvec(data["final_mantissa"], 23)

        call = f"(fp32_sum {s1} {e1} {m1} {s2} {e2} {m2})"
        expected = f"(concat {final_sign} (concat {final_exponent} {final_mantissa}))"
        msb_bits = getattr(config, "FP32_OUTPUT_MATCH_MSB_BITS", 32)
        return fp32_match_constraint(call, expected, msb_bits)


    def get_components(self) -> Dict:
        
        return {
            "fp32_alignment": {
                "template": "sygus_grammars/addition/FP32/fp32_alignment_template.sl",
                "generator": self.gen_alignment_constraint,
            },
            "fp32_raw_sum": {
                "template": "sygus_grammars/addition/FP32/fp32_raw_sum_template.sl",
                "generator": self.gen_raw_sum_constraint,
            },
            "fp32_normalisation": {
                "template": "sygus_grammars/addition/FP32/fp32_normalisation_template.sl",
                "generator": self.gen_normalisation_constraint,
            },
            "fp32_full_sum": {
                "template": "sygus_grammars/addition/FP32/fp32_full_sum_template.sl",
                "generator": self.gen_sum_constraint,
            },
            "fp32_full_sum_combined": {
                "template": "sygus_grammars/addition/FP32/fp32_full_sum_combined_template.sl",
                "generator": self.gen_sum_constraint,
            },
        }
