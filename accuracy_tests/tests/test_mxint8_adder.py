import cocotb
from cocotb.triggers import Timer
import random
import numpy as np
import torch

# Helper functions for float quantisation/dequantisation to/from MXINT8
# --- Configuration for MXINT8 (4-bit mantissa, 4-bit exponent) ---
WIDTH = 4
EXPONENT_WIDTH = 4
MANTISSA_MIN = -(2**(WIDTH - 1))
MANTISSA_MAX = (2**(WIDTH - 1)) - 1
EXPONENT_MIN = -(2**(EXPONENT_WIDTH - 1))
EXPONENT_MAX = (2**(EXPONENT_WIDTH - 1)) - 1
SCALE = 1 << (WIDTH - 1)

Q_CONFIG = {
    "width": WIDTH,
    "exponent_width": EXPONENT_WIDTH,
    "round_bits": 0,
}

def dequantize_mxint8(m: int, e: int) -> float:
    """Converts an MXINT8 mantissa and exponent back to a float."""
    if m == 0:
        return 0.0
    # The scaling factor is 2^(width-1), which is 8 for a 4-bit mantissa
    return m * (2.0**e) / SCALE

def quantize_to_mxint8(x_float: float) -> tuple[int, int]:
    """
    Quantizes a float to the MXINT8 format using the project's quantizer.
    This is a simplified version of the mxint_hardware function for scalar values.
    """
    if x_float == 0.0:
        return 0, 0  # Zero is represented by mantissa=0, exponent=0
    
    ax = abs(x_float)
    log2 = float(np.log2(ax))
    e = int(np.ceil(log2))
    # if exactly a power of two, bump exponent so mantissa stays in range
    if ax == 2.0**e:
        e += 1
    e = max(EXPONENT_MIN, min(EXPONENT_MAX, e))
    m = int(np.round(x_float * SCALE / (2.0**e)))
    m = max(MANTISSA_MIN, min(MANTISSA_MAX, m))
    return m, e

def oracle_mxint8_add(m1: int, e1: int, m2: int, e2: int) -> tuple[int, int]:
    """
    The "golden reference" for MXINT8 addition. It dequantizes the inputs,
    performs a high-precision float addition, and re-quantizes the result.
    """
    f1 = dequantize_mxint8(m1, e1)
    f2 = dequantize_mxint8(m2, e2)
    
    sum_float = f1 + f2
    
    return quantize_to_mxint8(sum_float)

# =====================================================================
#                        The Cocotb Testbench
# =====================================================================

@cocotb.test()
async def mxint8_adder_accuracy_test(dut):
    dut._log.info("Starting MXINT8 adder accuracy test")

    # Tie off control signals for the combinational design
    dut.ap_rst.value   = 0
    dut.ap_start.value = 1
    
    num_samples = 1000000
    errors = []
    matches = 0
    
    for _ in range(num_samples):
        # 1. Generate random valid MXINT8 integer inputs
        m1 = random.randint(MANTISSA_MIN, MANTISSA_MAX)
        e1 = random.randint(EXPONENT_MIN, EXPONENT_MAX)
        m2 = random.randint(MANTISSA_MIN, MANTISSA_MAX)
        e2 = random.randint(EXPONENT_MIN, EXPONENT_MAX)
        
        # 2. Calculate the "oracle" result using the reference implementation
        m_oracle, e_oracle = oracle_mxint8_add(m1, e1, m2, e2)
        oracle_float = dequantize_mxint8(m_oracle, e_oracle)
        
        # 3. Drive the DUT (Device Under Test) inputs
        dut.m1.value = m1
        dut.e1.value = e1
        dut.m2.value = m2
        dut.e2.value = e2

        # 4. Wait for the combinational logic to settle
        await Timer(1, unit='ns')

        # 5. Read the DUT output
        # The synthesized adder returns a packed 8-bit vector: {mant_out[3:0], exp_out[3:0]}
        dut_return_val = dut.ap_return.value
        
        # Extract the mantissa and exponent. The mantissa is signed.
        m_dut = dut_return_val[7:4].to_signed()
        e_dut = dut_return_val[3:0].to_signed()
        
        # Convert the DUT's output back to a float for comparison
        dut_float = dequantize_mxint8(m_dut, e_dut)
        matches += int(m_oracle == m_dut and e_oracle == e_dut)
        
        # 6. Compare and store the absolute error
        errors.append(abs(oracle_float - dut_float))

    # 7. Final statistical analysis
    max_error = np.max(errors) if errors else 0
    avg_error = np.mean(errors) if errors else 0
    p99_error = np.percentile(errors, 99) if errors else 0
    
    dut._log.info("--- Test Finished ---")
    dut._log.info(f"Ran {num_samples} test cases.")
    dut._log.info(f"Max Absolute Error: {max_error}")
    dut._log.info(f"Average Absolute Error: {avg_error}")
    dut._log.info(f"99th Percentile Error: {p99_error}")
    
    # Assert that the hardware is reasonably accurate. The threshold here should be
    # based on the expected precision of the MXINT8 format. A small error is expected.
    lsb = (2.0 ** e_oracle) / float(1 << (WIDTH - 1))  # 2^e / 8
    assert abs(dut_float - oracle_float) <= 0.5 * lsb + 1e-6
