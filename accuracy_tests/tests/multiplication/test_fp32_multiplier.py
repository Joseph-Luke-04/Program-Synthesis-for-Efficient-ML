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


def _sample_normal_u32(rng: random.Random) -> int:
    """Sample a finite normal FP32 bit-pattern uniformly over sign/exp/frac."""
    sign = rng.getrandbits(1)
    exp = rng.randint(1, 254)  # normal exponents only
    frac = rng.getrandbits(23)
    return (sign << 31) | (exp << 23) | frac


def _sample_u32_from_float_range(rng: random.Random, lo: float, hi: float) -> int:
    """Sample a float value in [lo, hi], quantize to FP32, return its uint32 bits."""
    while True:
        u = float_to_uint32(np.float32(rng.uniform(lo, hi)))
        if _is_finite_non_subnormal_u32(u):
            return u


def _sample_operands(rng: random.Random, mode: str) -> tuple[int, int]:
    """Sample two operands. All modes guarantee finite, non-subnormal results."""
    if mode == "bits" or mode == "normal_full":
        return _sample_normal_u32(rng), _sample_normal_u32(rng)
    if mode == "wide":
        return (
            _sample_u32_from_float_range(rng, -1024.0, 1024.0),
            _sample_u32_from_float_range(rng, -1024.0, 1024.0),
        )
    if mode == "small":
        return (
            _sample_u32_from_float_range(rng, 0.0, 1.0),
            _sample_u32_from_float_range(rng, 0.0, 1.0),
        )
    # Fallback to legacy behavior.
    return rng.getrandbits(32), rng.getrandbits(32)

def _directed_cases():
    return [
        (0.5, 0.5),
        (1.0, 1.0),
        (2.0, 0.5),
        (1.5, 2.0),
        (0.25, 4.0),
        (-0.5, 0.5),
    ]

def _order_for_ulp(u: int) -> int:
    """Order-preserving map of IEEE754 bits to 32-bit unsigned ints.
       Treats +0 and -0 as the same."""
    u &= 0xFFFFFFFF
    if (u & 0x7FFFFFFF) == 0:   # ±0
        return 0
    if u & 0x80000000:          # negatives
        # Mirror negatives so adjacent floats remain adjacent in ordered space.
        return (~u) & 0xFFFFFFFF
    else:                       # non-negatives
        return (u | 0x80000000) & 0xFFFFFFFF

def ulp_distance(a_bits, b_bits):
    return abs(_order_for_ulp(a_bits) - _order_for_ulp(b_bits))

# =====================================================================
#                         The Cocotb Testbench
# =====================================================================

async def _run_fp32_multiplier_accuracy(dut, label: str):
    dut._log.info(f"Starting FP32 multiplier accuracy test ({label})")

    has_clk = hasattr(dut, "ap_clk")
    if has_clk:
        cocotb.start_soon(Clock(dut.ap_clk, 10, unit="ns").start())
        dut.ap_rst.value = 1
        dut.ap_start.value = 0
        if hasattr(dut, "a"):
            dut.a.value = 0
        if hasattr(dut, "b"):
            dut.b.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
        dut.ap_rst.value = 0
        for _ in range(2):
            await RisingEdge(dut.ap_clk)
    else:
        if hasattr(dut, "ap_rst"):
            dut.ap_rst.value = 0
        if hasattr(dut, "ap_start"):
            dut.ap_start.value = 1

    num_samples = int(os.getenv("FP32_MUL_RANDOM_SAMPLES", "100000"))
    sample_seed = int(os.getenv("FP32_MUL_SEED", "7"))
    rel_err_threshold_pct = float(os.getenv("FP32_MUL_REL_ERR_PCT", "5"))
    sample_mode = os.getenv("FP32_MUL_MODE", "bits").strip().lower()
    gen_samples = int(os.getenv("FP32_MUL_GEN_SAMPLES", "50000"))
    rng = random.Random(sample_seed)
    valid_modes = {"bits", "normal_full", "wide", "small"}
    if sample_mode not in valid_modes:
        dut._log.warning(f"Unknown FP32_MUL_MODE='{sample_mode}', falling back to 'bits'.")
        sample_mode = "bits"
    dut._log.info(f"Random operand sampler mode: {sample_mode} (seed={sample_seed})")
    if rel_err_threshold_pct <= 0:
        rel_err_threshold_pct = 5.0
    ulps = []
    rel_err_pcts = []
    skipped = 0
    directed_run = 0

    async def _drive_and_measure(a: int, b: int):
        nonlocal skipped

        # Keep only finite, non-subnormal inputs (exclude NaN/Inf/subnormal).
        if not _is_finite_non_subnormal_u32(a) or not _is_finite_non_subnormal_u32(b):
            skipped += 1
            return None, None, None, None

        # drive DUT
        if hasattr(dut, "a") and hasattr(dut, "b"):
            dut.a.value, dut.b.value = a, b
        else:
            # fallback if design exposes s/e/m ports (not expected)
            s1, e1, m1 = (a >> 31) & 1, (a >> 23) & 0xFF, a & 0x7FFFFF
            s2, e2, m2 = (b >> 31) & 1, (b >> 23) & 0xFF, b & 0x7FFFFF
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
                    raise RuntimeError(f"Timeout waiting for ap_done from fp32_full_mul ({label})")
            else:
                await RisingEdge(dut.ap_clk)
        else:
            await Timer(1, unit="ns")

        got_bits = int(dut.ap_return.value)

        # IEEE-754 single-precision reference (rounded to nearest-even)
        ref_bits = float_to_uint32(np.float32(uint32_to_float(a)) * np.float32(uint32_to_float(b)))

        # Keep only finite, non-subnormal oracle outputs.
        if not _is_finite_non_subnormal_u32(ref_bits):
            skipped += 1
            return None, None, None, None

        got_f = np.float32(uint32_to_float(got_bits))
        ref_f = np.float32(uint32_to_float(ref_bits))
        if not np.isfinite(got_f) or not np.isfinite(ref_f):
            rel_pct = float("inf")
        elif ref_f == 0.0:
            rel_pct = 0.0 if got_f == 0.0 else float("inf")
        else:
            rel_pct = abs(float((got_f - ref_f) / ref_f)) * 100.0

        return got_bits, ref_bits, ulp_distance(got_bits, ref_bits), rel_pct

    # Directed sanity vectors first, then random vectors.
    for af, bf in _directed_cases():
        a = float_to_uint32(np.float32(af))
        b = float_to_uint32(np.float32(bf))
        got_bits, ref_bits, d, rel_pct = await _drive_and_measure(a, b)
        if d is None:
            continue
        directed_run += 1
        ulps.append(d)
        rel_err_pcts.append(rel_pct)
        dut._log.info(f"[DIRECTED] a={af} b={bf} got=0x{got_bits:08X} ref=0x{ref_bits:08X} ulp={d}")

    for _ in range(num_samples):
        a, b = _sample_operands(rng, sample_mode)
        _, _, d, rel_pct = await _drive_and_measure(a, b)
        if d is None:
            continue
        ulps.append(d)
        rel_err_pcts.append(rel_pct)

    if not ulps:
        raise AssertionError("No samples tested (all skipped?)")

    avg_ulp = float(np.mean(ulps))
    p99_ulp = int(np.percentile(ulps, 99))
    max_ulp = int(np.max(ulps))

    dut._log.info(f"Directed cases run: {directed_run}")
    dut._log.info(f"Ran {len(ulps)} cases (skipped {skipped}). "
                  f"ULP avg={avg_ulp:.3f}, p99={p99_ulp}, max={max_ulp}")

    N = len(ulps)
    within_rel = sum(e <= rel_err_threshold_pct for e in rel_err_pcts)
    avg_rel_pct = float(np.mean(rel_err_pcts)) if rel_err_pcts else -1.0
    p99_rel_pct = float(np.percentile(rel_err_pcts, 99)) if rel_err_pcts else -1.0
    dut._log.info(
        f"Within {rel_err_threshold_pct:g}% relative error: {within_rel/N:.2%} "
        f"(avg={avg_rel_pct:.3f}%, p99={p99_rel_pct:.3f}%)"
    )

    # Optional dump for downstream plotting (e.g. violin over per-sample relative error).
    dump_path = os.getenv("FP32_MUL_DUMP_PATH", "").strip()
    if dump_path:
        try:
            dump_dir = os.path.dirname(dump_path)
            if dump_dir:
                os.makedirs(dump_dir, exist_ok=True)
            np.savez_compressed(
                dump_path,
                rel_err_pct=np.asarray(rel_err_pcts, dtype=np.float32),
                ulp=np.asarray(ulps, dtype=np.int32),
                sample_mode=np.asarray([sample_mode]),
                rel_err_threshold_pct=np.asarray([rel_err_threshold_pct], dtype=np.float32),
            )
            dut._log.info(f"Saved per-sample error dump: {dump_path}")
        except Exception as exc:
            dut._log.warning(f"Failed to dump per-sample errors to {dump_path}: {exc}")

    exact   = sum(d == 0 for d in ulps)
    within1 = sum(d <= 1 for d in ulps)
    within2 = sum(d <= 2 for d in ulps)
    within4 = sum(d <= 4 for d in ulps)
    dut._log.info(f"Exact {exact/N:.2%}, ≤1 ULP {within1/N:.2%}, ≤2 ULP {within2/N:.2%}, ≤4 ULP {within4/N:.2%}")
    d1 = sum(d == 1 for d in ulps)
    d2 = sum(d == 2 for d in ulps)
    d3 = sum(d == 3 for d in ulps)
    d4 = sum(d == 4 for d in ulps)
    dgt4 = sum(d > 4 for d in ulps)
    dut._log.info(
        f"ULP buckets: ==1 {d1/N:.2%}, ==2 {d2/N:.2%}, ==3 {d3/N:.2%}, ==4 {d4/N:.2%}, >4 {dgt4/N:.2%}"
    )

    # Set a tolerance you're comfortable with. Without full IEEE handling,
    # expect occasional multi-ULP errors.
    assert p99_ulp <= 4, f"99th percentile ULP too high: {p99_ulp}"

    # --- Pass 2: generalisation (full IEEE normal range) ---
    # Skip if the primary mode already covers all normals.
    if sample_mode not in ("bits", "normal_full") and gen_samples > 0:
        gen_ulps = []
        gen_rel = []
        gen_skipped = 0
        gen_rng = random.Random(sample_seed + 1)

        for _ in range(gen_samples):
            a, b = _sample_operands(gen_rng, "normal_full")
            _, _, d, rel_pct = await _drive_and_measure(a, b)
            if d is None:
                gen_skipped += 1
                continue
            gen_ulps.append(d)
            gen_rel.append(rel_pct)

        if gen_ulps:
            gen_N = len(gen_ulps)
            gen_avg_ulp = float(np.mean(gen_ulps))
            gen_p99_ulp = int(np.percentile(gen_ulps, 99))
            gen_max_ulp = int(np.max(gen_ulps))
            dut._log.info(
                f"[GENERALISATION (normal_full)] Ran {gen_N} cases (skipped {gen_skipped}). "
                f"ULP avg={gen_avg_ulp:.3f}, p99={gen_p99_ulp}, max={gen_max_ulp}"
            )
            gen_within_rel = sum(e <= rel_err_threshold_pct for e in gen_rel)
            gen_avg_rel = float(np.mean(gen_rel))
            gen_p99_rel = float(np.percentile(gen_rel, 99))
            dut._log.info(
                f"[GENERALISATION (normal_full)] Within {rel_err_threshold_pct:g}% relative error: "
                f"{gen_within_rel/gen_N:.2%} (avg={gen_avg_rel:.3f}%, p99={gen_p99_rel:.3f}%)"
            )
            gen_exact = sum(d == 0 for d in gen_ulps)
            gen_w1 = sum(d <= 1 for d in gen_ulps)
            gen_w2 = sum(d <= 2 for d in gen_ulps)
            gen_w4 = sum(d <= 4 for d in gen_ulps)
            dut._log.info(
                f"[GENERALISATION (normal_full)] Exact {gen_exact/gen_N:.2%}, "
                f"≤1 ULP {gen_w1/gen_N:.2%}, ≤2 ULP {gen_w2/gen_N:.2%}, ≤4 ULP {gen_w4/gen_N:.2%}"
            )


def _should_run(label: str) -> bool:
    # Optional filter so you can run a single variant from the same test file.
    # Use: FP32_MUL_VARIANT=combined | subcomponents | flopoco
    want = os.getenv("FP32_MUL_VARIANT", "").strip().lower()
    if not want:
        return True
    return want == label.lower()


@cocotb.test()
async def fp32_multiplier_accuracy_subcomponents(dut):
    if not _should_run("subcomponents"):
        dut._log.info("Skipping subcomponents variant (FP32_MUL_VARIANT filter).")
        return
    await _run_fp32_multiplier_accuracy(dut, "subcomponents")


@cocotb.test()
async def fp32_multiplier_accuracy_combined(dut):
    if not _should_run("combined"):
        dut._log.info("Skipping combined variant (FP32_MUL_VARIANT filter).")
        return
    await _run_fp32_multiplier_accuracy(dut, "combined")


@cocotb.test()
async def fp32_multiplier_accuracy_flopoco(dut):
    if not _should_run("flopoco"):
        dut._log.info("Skipping flopoco variant (FP32_MUL_VARIANT filter).")
        return
    await _run_fp32_multiplier_accuracy(dut, "flopoco")
