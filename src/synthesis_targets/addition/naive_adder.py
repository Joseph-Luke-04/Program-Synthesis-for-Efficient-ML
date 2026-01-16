from typing import Dict, Optional
import struct
import math

def to_smt_bitvec(value: int, bits: int) -> str:
    """Converts an integer to an SMT-LIB bit-vector literal."""
    mask = (1 << bits) - 1
    return f"#b{value & mask:0{bits}b}"

def float_to_fp_bitvecs(f: float) -> Dict[str, int]:
    """Converts a Python float to its IEEE 754 single-precision components."""
    # Pack the float into 4 bytes, then unpack as a 32-bit unsigned integer
    bits = struct.unpack('<I', struct.pack('<f', f))[0]
    
    sign = (bits >> 31) & 0x1
    exponent = (bits >> 23) & 0xFF
    mantissa = bits & 0x7FFFFF
    
    return {"s": sign, "e": exponent, "m": mantissa, "bits": bits}

class NaiveAdderTarget:
    """
    kind='fp32'  -> synthesize (naive_fp32_add s1 e1 m1 s2 e2 m2) : (_ BitVec 32)
    kind='int' -> synthesize (naive_int_add  x  y)              : (_ BitVec 32)
    width is only used for the INT path (defaults to 32).
    """

    def __init__(self, kind:str = "fp32", width:int = 32):
        assert kind in ("fp32", "int")
        self.kind = kind
        self.width = width

    def calculate_ground_truth(self, a, b, config) -> Optional[Dict]:
        """
        The oracle for the naive adder. It takes two floats or ints, adds them, and returns
        the bit-level components of the inputs and the output.
        """
        if self.kind == "fp32":
            if not (math.isfinite(a) and math.isfinite(b)):
                return None
            c = a + b
            if not math.isfinite(c):
                return None
            a_bits = float_to_fp_bitvecs(a)
            b_bits = float_to_fp_bitvecs(b)
            c_bits = float_to_fp_bitvecs(c)

            return {
                "s1": a_bits["s"], "e1": a_bits["e"], "m1": a_bits["m"],
                "s2": b_bits["s"], "e2": b_bits["e"], "m2": b_bits["m"],
                "sum_bits": c_bits["bits"],
            }
        else: #int modular addition
            mask = (1 << self.width) - 1
            x = int(a) & mask
            y = int(b) & mask
            sum_xy = (x + y) & mask
            return {"x": x, "y": y, "sum_bits": sum_xy}

    def gen_constraint(self, data: Dict, config) -> str:
        """Generates a single constraint for the entire 32-bit operation."""
        if self.kind == "fp32":
            s1_bv = to_smt_bitvec(data["s1"], 1)
            e1_bv = to_smt_bitvec(data["e1"], 8)
            m1_bv = to_smt_bitvec(data["m1"], 23)
            
            s2_bv = to_smt_bitvec(data["s2"], 1)
            e2_bv = to_smt_bitvec(data["e2"], 8)
            m2_bv = to_smt_bitvec(data["m2"], 23)
            
            sum_bits_bv = to_smt_bitvec(data["sum_bits"], 32)
            
            # The synthesizer must find a function that takes the 6 input components
            # and produces the final 32-bit float result.
            synth_call = f"(naive_fp32_add {s1_bv} {e1_bv} {m1_bv} {s2_bv} {e2_bv} {m2_bv})"
            return f"(constraint (= {synth_call} {sum_bits_bv}))"
        else: # int
            x_bv = to_smt_bitvec(data["x"], self.width)
            y_bv = to_smt_bitvec(data["y"], self.width)
            sum_bits_bv = to_smt_bitvec(data["sum_bits"], self.width)
            
            synth_call = f"(naive_int_add {x_bv} {y_bv})"
            return f"(constraint (= {synth_call} {sum_bits_bv}))"

    def get_components(self) -> Dict:
        """This target has only one component: the whole adder."""
        if self.kind == "fp32":
            return {
                "fp32_adder": {
                    "template": "sygus_grammars/FP32/fp32_full_add_template.sl",
                    "generator": self.gen_constraint,
                }
            }
        elif self.kind == "int": 
            return {
                "int_add": {
                    "template": f"sygus_grammars/INT/int_full_add_{self.width}_template.sl",
                    "generator": self.gen_constraint,
                }
            }