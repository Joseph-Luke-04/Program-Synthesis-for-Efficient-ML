import torch

from a_cx_mxint_quant.quantizers import mxint_quant_block

WIDTH = 4
EXPONENT_WIDTH = 4
ROUND_BITS = 0

Q_CONFIG = {
    "width": WIDTH,
    "exponent_width": EXPONENT_WIDTH,
    "round_bits": ROUND_BITS,
}

MANTISSA_BITS = WIDTH - 1
EXPONENT_BIAS = 2**(EXPONENT_WIDTH - 1)
EXPONENT_MAX_VAL = 2**EXPONENT_WIDTH - 1 - EXPONENT_BIAS
EXPONENT_MIN_VAL = -EXPONENT_BIAS
MANTISSA_MIN = -(2**MANTISSA_BITS)
MANTISSA_MAX = 2**MANTISSA_BITS - 1



def quantize_to_mxint(x_float: float) -> tuple[int, int]:
    
    x_tensor = torch.tensor([x_float], dtype=torch.float32)

    _, mantissa_tensor, exponent_tensor = mxint_quant_block(x_tensor, **Q_CONFIG)

    mantissa = int(mantissa_tensor.item())
    exponent = int(exponent_tensor.item())

    return mantissa, exponent


def dequantize_from_mxint(m: int, e: int) -> float:
    if m == 0:
        return 0.0
    
    val = m * (2.0**e) / (2.0**(WIDTH - 1))
    return val

def add_mxint_gt(m1: int, e1: int, m2: int, e2: int) -> tuple[int, int]:

    f1 = dequantize_from_mxint(m1, e1)
    f2 = dequantize_from_mxint(m2, e2)

    sum_float = f1 + f2

    m_out, e_out = quantize_to_mxint(sum_float)
    
    return m_out, e_out
