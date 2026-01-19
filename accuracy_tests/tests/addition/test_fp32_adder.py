import cocotb
from cocotb.triggers import Timer
import random 
import struct
import numpy as np

# Helper functions for float quantisation/dequantisation
def float_to_uint32(f): return struct.unpack('<I', struct.pack('<f', float(f)))[0]
def uint32_to_float(u): return struct.unpack('<f', struct.pack('<I', u))[0]

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

@cocotb.test()
async def fp32_adder_accuracy_test(dut):
    dut._log.info("Starting FP32 adder accuracy test")

    # combinational IP: tie handshakes
    dut.ap_rst.value   = 0
    dut.ap_start.value = 1
    
    num_samples = 100000
    ulps = []
    skipped = 0
    
    for _ in range(num_samples):
        a = random.getrandbits(32)
        b = random.getrandbits(32)
        if ((a >> 23 ) & 0xFF) == 0xFF or ((b >> 23) & 0xFF) == 0xFF:
            # skip NaNs/Infs
            skipped += 1
            continue

        s1, e1, m1 = (a >> 31) & 1, (a >> 23) & 0xFF, a & 0x7FFFFF
        s2, e2, m2 = (b >> 31) & 1, (b >> 23) & 0xFF, b & 0x7FFFFF

        # drive DUT
        dut.s1.value, dut.e1.value, dut.m1.value = s1, e1, m1
        dut.s2.value, dut.e2.value, dut.m2.value = s2, e2, m2

        await Timer(1, unit='ns')  # allow combinational logic to settle

        got_bits = int(dut.ap_return.value)

        # IEEE-754 single-precision reference (rounded to nearest-even)
        ref_bits = float_to_uint32(np.float32(uint32_to_float(a)) + np.float32(uint32_to_float(b)))

        ulps.append(ulp_distance(got_bits, ref_bits))

    if not ulps:
        raise AssertionError("No samples tested (all skipped?)")

    avg_ulp = float(np.mean(ulps))
    p99_ulp = int(np.percentile(ulps, 99))
    max_ulp = int(np.max(ulps))

    dut._log.info(f"Ran {len(ulps)} cases (skipped {skipped}). "
                  f"ULP avg={avg_ulp:.3f}, p99={p99_ulp}, max={max_ulp}")
    
    N = len(ulps)
    exact   = sum(d == 0 for d in ulps)
    within1 = sum(d <= 1 for d in ulps)
    within2 = sum(d <= 2 for d in ulps)
    within4 = sum(d <= 4 for d in ulps)
    dut._log.info(f"Exact {exact/N:.2%}, ≤1 ULP {within1/N:.2%}, ≤2 ULP {within2/N:.2%}, ≤4 ULP {within4/N:.2%}")

    # Set a tolerance you’re comfortable with. Without guard/sticky/round,
    # expect occasional multi-ULP errors.
    assert p99_ulp <= 4, f"99th percentile ULP too high: {p99_ulp}"