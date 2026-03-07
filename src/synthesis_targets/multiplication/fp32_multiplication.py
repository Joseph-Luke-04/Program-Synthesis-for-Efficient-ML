from typing import Dict, Optional
import struct

def to_smt_bitvec(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

def f32_to_u32(x: float) -> int:
    return struct.unpack("<I", struct.pack("<f", float(x)))[0]

def u32_to_f32(u: int) -> float:
    return struct.unpack("<f", struct.pack("<I", u & 0xFFFFFFFF))[0]

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

class FP32MultiplicationTarget:

    def get_op_name(self) -> str:
        return "fp32multiplication"
    
    def get_dependency_map(self) -> Dict[str, list[str]]:
        from src.dependencies import DEPENDENCY_MAP
        return DEPENDENCY_MAP

    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
        a_u = f32_to_u32(float1)
        b_u = f32_to_u32(float2)

        # Unpack components (extraction)
        sa = (a_u >> 31) & 0x1
        sb = (b_u >> 31) & 0x1
        ea = (a_u >> 23) & 0xFF
        eb = (b_u >> 23) & 0xFF
        fa = a_u & ((1 << 23) - 1)
        fb = b_u & ((1 << 23) - 1)

        # Handle special cases
        isNaN_a = (ea == 0xFF) and (fa != 0)
        isNaN_b = (eb == 0xFF) and (fb != 0)
        isInf_a = (ea == 0xFF) and (fa == 0)
        isInf_b = (eb == 0xFF) and (fb == 0)
        isZero_a = (ea == 0) and (fa == 0)
        isZero_b = (eb == 0) and (fb == 0)

        # Skip special cases for now
        if isNaN_a or isNaN_b or isInf_a or isInf_b or isZero_a or isZero_b:
            return None
        
        # Build mantissas (assume normals only for now)
        Ma = (1 << 23) | fa  # 24-bit
        Mb = (1 << 23) | fb  # 24-bit

        # Exponent (unbias)
        Ea = ea - 127
        Eb = eb - 127
        E_sum = Ea + Eb  # still needs renorm adjust

        # Multiply 24x24 -> 48
        Product = Ma * Mb  # up to 48 bits

        # Normalise: product in [1,4). In fixed point, if bit 47 is 1 => >=2.0
        renorm = 1 if (Product >> 47) & 1 else 0
        if renorm:
            P_norm = Product >> 1
            E_norm = E_sum + 1
        else:
            P_norm = Product
            E_norm = E_sum

        # Extract fraction bits (pre-round): we want 23 bits after leading 1.
        # P_norm has leading 1 at bit 46 (if renorm) or bit 46 anyway after above rule.
        # Keep guard/round/sticky
        # Take top 24 bits: [46:23] gives 24 incl hidden; fraction = lower 23 of that.
        top24 = (P_norm >> 23) & ((1 << 24) - 1)
        frac23 = top24 & ((1 << 23) - 1)

        # GRS bits: next bits below frac field
        guard = (P_norm >> 22) & 1
        roundb = (P_norm >> 21) & 1
        sticky = 1 if (P_norm & ((1 << 21) - 1)) != 0 else 0

        # Round-to-nearest-even
        lsb = frac23 & 1
        inc = 1 if (guard and (roundb or sticky or lsb)) else 0
        frac_rounded = frac23 + inc
        carry = 1 if frac_rounded >> 23 else 0
        if carry:
            frac_rounded &= ((1 << 23) - 1)
            E_norm += 1

        # Re-bias exponent
        e_out = E_norm + 127

        # (No underflow/overflow handling yet)
        if not (1 <= e_out <= 254):
            return None

        s_out = sa ^ sb
        out_u = (s_out << 31) | ((e_out & 0xFF) << 23) | (frac_rounded & ((1 << 23) - 1))

        return {
            "a": a_u, "b": b_u,
            "sa": sa, "sb": sb,
            "ea": ea, "eb": eb,
            "fa": fa, "fb": fb,
            "Ma": Ma, "Mb": Mb,
            "E_sum": E_sum,
            "Product": Product,
            "renorm": renorm,
            "P_norm": P_norm,
            "E_norm": E_norm,
            "frac23": frac_rounded,
            "e_out": e_out,
            "s_out": s_out,
            "out": out_u,
        }

    
    def gen_renorm_constraint(self, data: Dict, config) -> str:
        # 24-bit mantissas incl. hidden bit (normals-only)
        Ma_bv = to_smt_bitvec(data["Ma"], 24)
        Mb_bv = to_smt_bitvec(data["Mb"], 24)
        ren_bv = to_smt_bitvec(data["renorm"], 1)

        synth_call = f"(fp32_mult_renorm {Ma_bv} {Mb_bv})"
        return f"(constraint (= {synth_call} {ren_bv}))"

    def gen_exp_constraint(self, data: Dict, config) -> str:
        # Compute round-carry from what ground_truth already stores:
        # E_norm = E_sum + renorm + round_carry  (since you increment E_norm on carry)
        round_carry = 1 if (data["E_norm"] - (data["E_sum"] + data["renorm"])) == 1 else 0

        ea_bv = to_smt_bitvec(data["ea"], 8)
        eb_bv = to_smt_bitvec(data["eb"], 8)
        ren_bv = to_smt_bitvec(data["renorm"], 1)
        car_bv = to_smt_bitvec(round_carry, 1)
        eout_bv = to_smt_bitvec(data["e_out"], 8)

        # exp depends on renorm AND possible mantissa rounding carry
        synth_call = f"(fp32_mult_exp {ea_bv} {eb_bv} {ren_bv} {car_bv})"
        return f"(constraint (= {synth_call} {eout_bv}))"

    def gen_mant_constraint(self, data: Dict, config) -> str:
        Ma_bv = to_smt_bitvec(data["Ma"], 24)
        Mb_bv = to_smt_bitvec(data["Mb"], 24)
        ren_bv = to_smt_bitvec(data["renorm"], 1)
        frac_bv = to_smt_bitvec(data["frac23"], 23)

        synth_call = f"(fp32_mult_mant {Ma_bv} {Mb_bv} {ren_bv})"
        return f"(constraint (= {synth_call} {frac_bv}))"

    def gen_full_product_constraint(self, data: Dict, config) -> str:
        a_bv = to_smt_bitvec(data["a"], 32)
        b_bv = to_smt_bitvec(data["b"], 32)
        out_bv = to_smt_bitvec(data["out"], 32)

        synth_call = f"(fp32_full_mul {a_bv} {b_bv})"
        msb_bits = getattr(config, "FP32_OUTPUT_MATCH_MSB_BITS", 32)
        return fp32_match_constraint(synth_call, out_bv, msb_bits)


    def get_components(self) -> Dict:

        return {
            "renorm": {
                "template": "sygus_grammars/multiplication/FP32/fp32_mult_renorm_template.sl",
                "generator": self.gen_renorm_constraint,
            },
            "exp": {
                "template": "sygus_grammars/multiplication/FP32/fp32_mult_exp_template.sl",
                "generator": self.gen_exp_constraint,
            },
            "mant": {
                "template": "sygus_grammars/multiplication/FP32/fp32_mult_mant_template.sl",
                "generator": self.gen_mant_constraint,
            },
            "full_product": {
                "template": "sygus_grammars/multiplication/FP32/fp32_full_prod_template.sl",
                "generator": self.gen_full_product_constraint,
            },
            # Monolithic full-product grammar (no subcomponent dependencies).
            "full_product_combined": {
                "template": "sygus_grammars/multiplication/FP32/fp32_full_prod_combined_template.sl",
                "generator": self.gen_full_product_constraint,
            },
        }
