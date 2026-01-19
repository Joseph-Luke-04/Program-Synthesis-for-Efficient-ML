import cocotb
from cocotb.triggers import Timer
import random
import numpy as np
import torch
import math
import os
import sys
from pathlib import Path

# Allow imports from the repo root (for a_cx_mxint_quant).
_REPO_ROOT = Path(__file__).resolve().parents[3]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from a_cx_mxint_quant.quantizers import mxint_hardware

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
PARALLELISM = [1, 1]

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
    
    num_samples = 100000
    errors = []
    matches = 0
    tested = 0
    skipped = 0

    # Representable range for MXINT8 addition is roughly +/-112.
    max_val = 112.0
    
    while tested < num_samples:
        # 1. Generate random float inputs and quantize using mxint_hardware
        f1 = random.uniform(-max_val, max_val)
        f2 = random.uniform(-max_val, max_val)

        t1 = torch.tensor([[f1]])
        t2 = torch.tensor([[f2]])

        dequant1, m1_t, e1_t = mxint_hardware(t1, Q_CONFIG, PARALLELISM)
        dequant2, m2_t, e2_t = mxint_hardware(t2, Q_CONFIG, PARALLELISM)

        if dequant1.item() == 0.0 or dequant2.item() == 0.0:
            skipped += 1
            continue

        m1, e1 = int(m1_t.item()), int(e1_t.item())
        m2, e2 = int(m2_t.item()), int(e2_t.item())

        # 2. Oracle: quantize the sum using the same hardware quantizer
        sum_float = dequant1 + dequant2
        _, m_oracle_t, e_oracle_t = mxint_hardware(sum_float, Q_CONFIG, PARALLELISM)
        m_oracle, e_oracle = int(m_oracle_t.item()), int(e_oracle_t.item())
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
        tested += 1

    max_error = np.max(errors) if errors else 0
    avg_error = np.mean(errors) if errors else 0
    p99_error = np.percentile(errors, 99) if errors else 0
    
    dut._log.info("--- Test Finished ---")
    dut._log.info(f"Ran {tested} test cases (skipped {skipped}).")
    if tested > 0:
        exact_pct = 100.0 * (matches / tested)
        dut._log.info(f"Exact Match Accuracy: {exact_pct:.2f}% ({matches}/{tested})")
    dut._log.info(f"Max Absolute Error: {max_error}")
    dut._log.info(f"Average Absolute Error: {avg_error}")
    dut._log.info(f"99th Percentile Error: {p99_error}")
    
    # After you compute max_error, avg_error, p99_error
    FULL_SCALE = (MANTISSA_MAX * (2.0 ** EXPONENT_MAX)) / float(SCALE)  # = 112 for 4/4 format

    # Example smoke thresholds; tune to taste:
    # - avg absolute error should be tiny relative to full-scale
    # - p99 absolute error should still be a small fraction of full-scale
    assert (avg_error / FULL_SCALE) < 0.02 + 1e-12, "Average abs error too large vs full-scale"
    assert (p99_error / FULL_SCALE) < 0.20 + 1e-12, "P99 abs error too large vs full-scale"
