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

class NaiveMultiplierTarget:
    """
    kind='fp32'  -> synthesize (naive_fp32_mul s1 e1 m1 s2 e2 m2) : (_ BitVec 32)
    kind='int' -> synthesize (naive_int_mul  x  y)              : (_ BitVec 32)
    width is only used for the INT path (defaults to 32).
    """

    def __init__(self, kind:str = "fp32", width:int = 32):
        assert kind in ("fp32", "int")
        self.kind = kind
        self.width = width

    def get_op_name(self) -> str:
        if self.kind == "fp32":
            return "naivefp32multiplier"
        return f"naivemultiplier_int{self.width}"

    def get_dependency_map(self):
        from src.dependencies import DEPENDENCY_MAP
        return DEPENDENCY_MAP

    def calculate_ground_truth(self, a, b, config) -> Optional[Dict]:
        """
        The oracle for the naive multiplier. It takes two floats or ints, multiplies them, and returns
        the bit-level components of the inputs and the output.
        """
        if self.kind == "fp32":
            if not (math.isfinite(a) and math.isfinite(b)):
                return None
            c = a * b
            if not math.isfinite(c):
                return None
            a_bits = float_to_fp_bitvecs(a)
            b_bits = float_to_fp_bitvecs(b)
            c_bits = float_to_fp_bitvecs(c)

            return {
                "s1": a_bits["s"], "e1": a_bits["e"], "m1": a_bits["m"],
                "s2": b_bits["s"], "e2": b_bits["e"], "m2": b_bits["m"],
                "prod_bits": c_bits["bits"],
            }
        else: #int modular multiplication
            mask = (1 << self.width) - 1
            x = int(a) & mask
            y = int(b) & mask
            prod_xy = (x * y) & mask
            return {"x": x, "y": y, "prod_bits": prod_xy}
        
    def gen_constraint(self, data: Dict, config) -> str:
        if self.kind == "fp32":
            s1 = to_smt_bitvec(data["s1"], 1)
            e1 = to_smt_bitvec(data["e1"], 8)
            m1 = to_smt_bitvec(data["m1"], 23)

            s2 = to_smt_bitvec(data["s2"], 1)
            e2 = to_smt_bitvec(data["e2"], 8)
            m2 = to_smt_bitvec(data["m2"], 23)

            prod_bits = to_smt_bitvec(data["prod_bits"], 32)
            return f"(constraint (= (naive_fp32_mul {s1} {e1} {m1} {s2} {e2} {m2}) {prod_bits}))"
        
        elif self.kind == "int":
            x = to_smt_bitvec(data["x"], self.width)
            y = to_smt_bitvec(data["y"], self.width)
            prod_bits = to_smt_bitvec(data["prod_bits"], self.width)

            return f"(constraint (= (naive_int_mul {x} {y}) {prod_bits}))"
    
    def get_components(self) -> Dict:
        if self.kind == "fp32":
            if self.kind == "fp32":
                return {
                    "fp32_mul": {
                        "template": "sygus_grammars/multiplication/FP32/fp32_full_mul_template.sl",
                        "generator": self.gen_constraint,
                    }
                }
        elif self.kind == "int":
            return {
                "int_mul": {
                    "template": f"sygus_grammars/multiplication/INT/int_full_mul_{self.width}_template.sl",
                    "generator": self.gen_constraint,
                }
            }
