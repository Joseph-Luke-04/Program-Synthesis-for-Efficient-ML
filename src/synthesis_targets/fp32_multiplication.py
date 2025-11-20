from typing import Dict, Optional
import struct

def float_to_smt_bitvec(value: float) -> str:
    bits = struct.unpack('!I', struct.pack('!f', value))[0]
    sign = (bits >> 31) & 0x1
    exponent = (bits >> 23) & 0xFF
    mantissa = bits & 0x7FFFFF
    return f"(fp #b{sign:01b} #b{exponent:08b} #b{mantissa:023b})"

class FP32MultiplicationTarget:

    def get_op_name(self) -> str:
        return "fp32multiplication"
    
    def get_dependency_map(self) -> Dict[str, list[str]]:
        from src.dependencies import DEPENDENCY_MAP
        return DEPENDENCY_MAP

    def calculate_ground_truth(self, float1: float, float2: float, config) -> Optional[Dict]:
        product_float = float1 * float2
        return {
            "inputs": [float_to_smt_bitvec(float1), float_to_smt_bitvec(float2)],
            "output": float_to_smt_bitvec(product_float)
        }
    
    def gen_multiplication_constraint(self, data: Dict, config) -> str:
        pass