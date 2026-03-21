import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
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
FULL_SCALE = (MANTISSA_MAX * (2.0 ** EXPONENT_MAX)) / float(SCALE)  # = 112 for 4/4 format
ABS_ERR_TOL_FRAC = 0.05

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

def oracle_mxint8_mul(m1: int, e1: int, m2: int, e2: int) -> tuple[int, int]:
    """
    The "golden reference" for MXINT8 multiplication. It dequantizes the inputs,
    performs a high-precision float multiplication, and re-quantizes the result.
    """
    f1 = dequantize_mxint8(m1, e1)
    f2 = dequantize_mxint8(m2, e2)
    
    product_float = f1 * f2
    
    return quantize_to_mxint8(product_float)

# =====================================================================
#                        The Cocotb Testbench
# =====================================================================

async def _run_mxint8_multiplier_accuracy(dut, label: str):
    dut._log.info(f"Starting MXINT8 multiplier accuracy test ({label})")

    has_clk = hasattr(dut, "ap_clk")
    if has_clk:
        # Drive the HLS control interface for a clocked design.
        cocotb.start_soon(Clock(dut.ap_clk, 10, unit="ns").start())
        dut.ap_rst.value = 1
        dut.ap_start.value = 0
        dut.m1.value = 0
        dut.e1.value = 0
        dut.m2.value = 0
        dut.e2.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
        dut.ap_rst.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
    else:
        # Combinational core (ap_ctrl_none): no clock/reset ports.
        if hasattr(dut, "ap_rst"):
            dut.ap_rst.value = 0
        if hasattr(dut, "ap_start"):
            dut.ap_start.value = 1

    num_samples = 100000
    errors_quant = []
    errors_full = []
    tested = 0
    skipped = 0

    # Representable range for MXINT8 multiplication is roughly +/-112.
    max_val = math.sqrt(112)

    while tested < num_samples:
        # 1. Generate random float inputs and quantize using mxint_hardware
        f1 = random.uniform(-max_val, max_val)
        f2 = random.uniform(-max_val, max_val)
        oracle_full = f1 * f2

        t1 = torch.tensor([[f1]])
        t2 = torch.tensor([[f2]])

        dequant1, m1_t, e1_t = mxint_hardware(t1, Q_CONFIG, PARALLELISM)
        dequant2, m2_t, e2_t = mxint_hardware(t2, Q_CONFIG, PARALLELISM)

        if dequant1.item() == 0.0 or dequant2.item() == 0.0:
            skipped += 1
            continue

        m1, e1 = int(m1_t.item()), int(e1_t.item())
        m2, e2 = int(m2_t.item()), int(e2_t.item())

        # Quantized oracle: multiply quantized inputs then re-quantize.
        product_dequant = dequant1 * dequant2
        _, m_or_t, e_or_t = mxint_hardware(product_dequant, Q_CONFIG, PARALLELISM)
        oracle_quant = dequantize_mxint8(int(m_or_t.item()), int(e_or_t.item()))

        # 2. Drive the DUT (Device Under Test) inputs
        dut.m1.value = m1
        dut.e1.value = e1
        dut.m2.value = m2
        dut.e2.value = e2
        if hasattr(dut, "renorm_flag"):
            if label == "v2":
                # V2 solution takes renorm_flag as an explicit input.
                # Flag=1 when |m1*m2| is large enough that the exponent
                # needs adjusting down to compensate for the mantissa shift.
                dut.renorm_flag.value = 1 if abs(m1 * m2) >= 32 else 0
            else:
                # Subcomponents version computes renorm_flag internally
                # via a dedicated sub-circuit; the port value is unused.
                dut.renorm_flag.value = 0

        if has_clk:
            # Start the transaction and wait for ap_done.
            if hasattr(dut, "ap_idle") and hasattr(dut, "ap_ready"):
                while int(dut.ap_idle.value) == 0 and int(dut.ap_ready.value) == 0:
                    await RisingEdge(dut.ap_clk)
            dut.ap_start.value = 1
            await RisingEdge(dut.ap_clk)
            dut.ap_start.value = 0

            if hasattr(dut, "ap_done"):
                done = False
                for _ in range(50):
                    await RisingEdge(dut.ap_clk)
                    if int(dut.ap_done.value) == 1:
                        done = True
                        break
                if not done:
                    raise RuntimeError("Timeout waiting for ap_done from mult_mxint_full_product")
            else:
                await RisingEdge(dut.ap_clk)
        else:
            # Wait for combinational logic to settle.
            await Timer(1, unit="ns")

        # 5. Read the DUT output
        # The synthesized multiplier returns a packed 8-bit vector: {exp_out[3:0], mant_out[3:0]}
        dut_return_val = dut.ap_return.value

        # Extract the exponent (upper nibble) and mantissa (lower nibble). Both are signed.
        e_dut = dut_return_val[7:4].to_signed()
        m_dut = dut_return_val[3:0].to_signed()

        # Convert the DUT's output back to a float for comparison
        dut_float = dequantize_mxint8(m_dut, e_dut)

        # 6. Compare and store absolute error vs both oracles
        errors_full.append(abs(oracle_full - dut_float))
        errors_quant.append(abs(oracle_quant - dut_float))
        tested += 1

    def summarize(errors):
        max_error = np.max(errors) if errors else 0
        avg_error = np.mean(errors) if errors else 0
        p99_error = np.percentile(errors, 99) if errors else 0
        p95_abs = np.percentile(errors, 95) if errors else 0
        pct_within = 100.0 * (np.mean(np.array(errors) <= (FULL_SCALE * ABS_ERR_TOL_FRAC)) if errors else 0.0)
        return max_error, avg_error, p99_error, p95_abs, pct_within

    max_q, avg_q, p99_q, p95_q, pct_q = summarize(errors_quant)
    max_f, avg_f, p99_f, p95_f, pct_f = summarize(errors_full)

    dut._log.info("--- Test Finished ---")
    dut._log.info(f"Ran {tested} test cases (skipped {skipped}).")
    dut._log.info("Quantized oracle:")
    dut._log.info(f"Max Absolute Error: {max_q}")
    dut._log.info(f"Average Absolute Error: {avg_q}")
    dut._log.info(f"99th Percentile Error: {p99_q}")
    dut._log.info(f"95th Percentile Absolute Error: {p95_q}")
    dut._log.info(f"Percent Within {ABS_ERR_TOL_FRAC * 100:.2f}% Full-Scale Error: {pct_q:.2f}%")
    dut._log.info("Full-precision oracle:")
    dut._log.info(f"Max Absolute Error: {max_f}")
    dut._log.info(f"Average Absolute Error: {avg_f}")
    dut._log.info(f"99th Percentile Error: {p99_f}")
    dut._log.info(f"95th Percentile Absolute Error: {p95_f}")
    dut._log.info(f"Percent Within {ABS_ERR_TOL_FRAC * 100:.2f}% Full-Scale Error: {pct_f:.2f}%")

    # Optional dump for downstream plotting (violin charts, etc.).
    dump_path = os.getenv("MXINT8_MUL_DUMP_PATH", "").strip()
    if dump_path:
        try:
            dump_dir = os.path.dirname(dump_path)
            if dump_dir:
                os.makedirs(dump_dir, exist_ok=True)
            np.savez_compressed(
                dump_path,
                abs_err_quant=np.asarray(errors_quant, dtype=np.float32),
                abs_err_full=np.asarray(errors_full, dtype=np.float32),
                full_scale=np.asarray([FULL_SCALE], dtype=np.float32),
                abs_err_tol_frac=np.asarray([ABS_ERR_TOL_FRAC], dtype=np.float32),
            )
            dut._log.info(f"Saved per-sample error dump: {dump_path}")
        except Exception as exc:
            dut._log.warning(f"Failed to dump per-sample errors to {dump_path}: {exc}")

    # No threshold assertions; report metrics only.


def _should_run(label: str) -> bool:
    # Optional filter so you can run a single variant from the same test file.
    # Use: MXINT8_MUL_VARIANT=v2 or MXINT8_MUL_VARIANT=subcomponents
    want = os.getenv("MXINT8_MUL_VARIANT", "").strip().lower()
    if not want:
        return True
    return want == label.lower()


@cocotb.test()
async def mxint8_multiplier_accuracy_subcomponents(dut):
    if not _should_run("subcomponents"):
        dut._log.info("Skipping subcomponents variant (MXINT8_MUL_VARIANT filter).")
        return
    await _run_mxint8_multiplier_accuracy(dut, "subcomponents")


@cocotb.test()
async def mxint8_multiplier_accuracy_v2(dut):
    if not _should_run("v2"):
        dut._log.info("Skipping v2 variant (MXINT8_MUL_VARIANT filter).")
        return
    await _run_mxint8_multiplier_accuracy(dut, "v2")


@cocotb.test()
async def mxint8_multiplier_accuracy_v1(dut):
    if not _should_run("v1"):
        dut._log.info("Skipping v1 variant (MXINT8_MUL_VARIANT filter).")
        return
    await _run_mxint8_multiplier_accuracy(dut, "v1")
