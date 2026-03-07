import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import random 
import struct
import numpy as np
import os

# Helper functions for float quantisation/dequantisation
def float_to_uint32(f): return struct.unpack('<I', struct.pack('<f', float(f)))[0]
def uint32_to_float(u): return struct.unpack('<f', struct.pack('<I', u))[0]

def _is_finite_non_subnormal_u32(u: int) -> bool:
    exp = (u >> 23) & 0xFF
    frac = u & 0x7FFFFF
    if exp == 0xFF:
        return False  # NaN/Inf
    if exp == 0 and frac != 0:
        return False  # subnormal
    return True  # zero or normal finite

def _order_for_ulp(u: int) -> int:
    """Order-preserving map of IEEE754 bits to 32-bit unsigned ints.
       Treats +0 and -0 as the same."""
    u &= 0xFFFFFFFF
    if (u & 0x7FFFFFFF) == 0:   # ±0
        return 0
    if u & 0x80000000:          # negatives
        return (~u + 1) & 0xFFFFFFFF   # two's complement mirrors the order
    else:                       # non-negatives
        return (u | 0x80000000) & 0xFFFFFFFF

def ulp_distance(a_bits, b_bits):
    return abs(_order_for_ulp(a_bits) - _order_for_ulp(b_bits))

# =====================================================================
#                         The Cocotb Testbench
# =====================================================================

async def _run_fp32_adder_accuracy(dut, label: str):
    dut._log.info(f"Starting FP32 adder accuracy test ({label})")

    has_clk = hasattr(dut, "ap_clk")
    if has_clk:
        cocotb.start_soon(Clock(dut.ap_clk, 10, unit="ns").start())
        dut.ap_rst.value = 1
        dut.ap_start.value = 0
        dut.s1.value = 0
        dut.e1.value = 0
        dut.m1.value = 0
        dut.s2.value = 0
        dut.e2.value = 0
        dut.m2.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
        dut.ap_rst.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
    else:
        dut.ap_rst.value = 0
        dut.ap_start.value = 1
    
    num_samples = 100000
    ulps = []
    rel_err_pcts = []
    skipped = 0
    
    for _ in range(num_samples):
        a = random.getrandbits(32)
        b = random.getrandbits(32)
        if not _is_finite_non_subnormal_u32(a) or not _is_finite_non_subnormal_u32(b):
            # keep only finite, non-subnormal operands
            skipped += 1
            continue

        s1, e1, m1 = (a >> 31) & 1, (a >> 23) & 0xFF, a & 0x7FFFFF
        s2, e2, m2 = (b >> 31) & 1, (b >> 23) & 0xFF, b & 0x7FFFFF

        # drive DUT
        dut.s1.value, dut.e1.value, dut.m1.value = s1, e1, m1
        dut.s2.value, dut.e2.value, dut.m2.value = s2, e2, m2

        if has_clk:
            if hasattr(dut, "ap_idle") and hasattr(dut, "ap_ready"):
                while int(dut.ap_idle.value) == 0 and int(dut.ap_ready.value) == 0:
                    await RisingEdge(dut.ap_clk)
            dut.ap_start.value = 1
            await RisingEdge(dut.ap_clk)
            dut.ap_start.value = 0
            if hasattr(dut, "ap_done"):
                done = False
                for _ in range(100):
                    await RisingEdge(dut.ap_clk)
                    if int(dut.ap_done.value) == 1:
                        done = True
                        break
                if not done:
                    raise RuntimeError(f"Timeout waiting for ap_done from fp32_sum ({label})")
            else:
                await RisingEdge(dut.ap_clk)
        else:
            await Timer(1, unit="ns")  # allow combinational logic to settle

        got_bits = int(dut.ap_return.value)

        # IEEE-754 single-precision reference (rounded to nearest-even)
        with np.errstate(over='ignore', invalid='ignore'):
            ref_bits = float_to_uint32(np.float32(uint32_to_float(a)) + np.float32(uint32_to_float(b)))
        if not _is_finite_non_subnormal_u32(ref_bits):
            # keep only finite, non-subnormal oracle outputs
            skipped += 1
            continue

        got_f = np.float32(uint32_to_float(got_bits))
        ref_f = np.float32(uint32_to_float(ref_bits))
        if not np.isfinite(got_f) or not np.isfinite(ref_f):
            rel_pct = float('inf')
        elif ref_f == 0.0:
            rel_pct = 0.0 if got_f == 0.0 else float('inf')
        else:
            rel_pct = abs(float((got_f - ref_f) / ref_f)) * 100.0

        ulps.append(ulp_distance(got_bits, ref_bits))
        rel_err_pcts.append(rel_pct)

    if not ulps:
        raise AssertionError("No samples tested (all skipped?)")

    avg_ulp = float(np.mean(ulps))
    p99_ulp = int(np.percentile(ulps, 99))
    max_ulp = int(np.max(ulps))

    dut._log.info(f"Ran {len(ulps)} cases (skipped {skipped}). "
                  f"ULP avg={avg_ulp:.3f}, p99={p99_ulp}, max={max_ulp}")
    
    N = len(ulps)
    within_5pct = sum(e <= 5.0 for e in rel_err_pcts)
    avg_rel_pct = float(np.mean(rel_err_pcts)) if rel_err_pcts else -1.0
    p99_rel_pct = float(np.percentile(rel_err_pcts, 99)) if rel_err_pcts else -1.0
    dut._log.info(
        f"Within 5% relative error: {within_5pct/N:.2%} "
        f"(avg={avg_rel_pct:.3f}%, p99={p99_rel_pct:.3f}%)"
    )

    exact   = sum(d == 0 for d in ulps)
    within1 = sum(d <= 1 for d in ulps)
    within2 = sum(d <= 2 for d in ulps)
    within4 = sum(d <= 4 for d in ulps)
    dut._log.info(f"Exact {exact/N:.2%}, ≤1 ULP {within1/N:.2%}, ≤2 ULP {within2/N:.2%}, ≤4 ULP {within4/N:.2%}")

    # Set a tolerance you’re comfortable with. Without guard/sticky/round,
    # expect occasional multi-ULP errors.
    assert p99_ulp <= 4, f"99th percentile ULP too high: {p99_ulp}"


def _should_run(label: str) -> bool:
    # Optional filter so you can run a single variant from the same test file.
    # Use: FP32_ADD_VARIANT=combined | subcomponents | flopoco
    want = os.getenv("FP32_ADD_VARIANT", "").strip().lower()
    if not want:
        return True
    return want == label.lower()


@cocotb.test()
async def fp32_adder_accuracy_subcomponents(dut):
    if not _should_run("subcomponents"):
        dut._log.info("Skipping subcomponents variant (FP32_ADD_VARIANT filter).")
        return
    await _run_fp32_adder_accuracy(dut, "subcomponents")


@cocotb.test()
async def fp32_adder_accuracy_combined(dut):
    if not _should_run("combined"):
        dut._log.info("Skipping combined variant (FP32_ADD_VARIANT filter).")
        return
    await _run_fp32_adder_accuracy(dut, "combined")


@cocotb.test()
async def fp32_adder_accuracy_flopoco(dut):
    if not _should_run("flopoco"):
        dut._log.info("Skipping flopoco variant (FP32_ADD_VARIANT filter).")
        return
    await _run_fp32_adder_accuracy(dut, "flopoco")
