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
    exp = rng.randint(1, 254)  # normal exponents only (no subnormals, no Inf/NaN)
    frac = rng.getrandbits(23)
    return (sign << 31) | (exp << 23) | frac


def _sample_u32_from_float_range(rng: random.Random, lo: float, hi: float) -> int:
    """Sample a float value in [lo, hi], quantize to FP32, return its uint32 bits.
       Rejects subnormals, NaN, and Inf."""
    while True:
        u = float_to_uint32(np.float32(rng.uniform(lo, hi)))
        if _is_finite_non_subnormal_u32(u):
            return u


def _sample_operands(rng: random.Random, mode: str) -> tuple[int, int]:
    """Sample two operands. All modes guarantee finite, non-subnormal results."""
    if mode == "bits" or mode == "normal_full":
        # Uniform over all normal FP32 bit-patterns (skips subnormals/NaN/Inf).
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
    # Fallback: default range matches synthesis [-1e4, 1e4].
    return (
        _sample_u32_from_float_range(rng, -1e4, 1e4),
        _sample_u32_from_float_range(rng, -1e4, 1e4),
    )


# =====================================================================
#                         The Cocotb Testbench
# =====================================================================

def _report_stats(dut, tag: str, rel_err_pcts: list, exact_matches: int,
                  skipped: int, rel_err_threshold_pct: float):
    """Print accuracy statistics for one sampling pass."""
    if not rel_err_pcts:
        dut._log.warning(f"[{tag}] No samples tested (all skipped?).")
        return

    N = len(rel_err_pcts)
    within_rel = sum(e <= rel_err_threshold_pct for e in rel_err_pcts)
    avg_rel_pct = float(np.mean(rel_err_pcts))
    p99_rel_pct = float(np.percentile(rel_err_pcts, 99))
    dut._log.info(
        f"[{tag}] Ran {N} cases (skipped {skipped}). "
        f"Exact match: {exact_matches/N:.2%}. "
        f"Within {rel_err_threshold_pct:g}% relative error: {within_rel/N:.2%} "
        f"(avg={avg_rel_pct:.3f}%, p99={p99_rel_pct:.3f}%)"
    )


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

    num_samples = int(os.getenv("FP32_ADD_RANDOM_SAMPLES", "100000"))
    sample_seed = int(os.getenv("FP32_ADD_SEED", "7"))
    rel_err_threshold_pct = float(os.getenv("FP32_ADD_REL_ERR_PCT", "5"))
    sample_mode = os.getenv("FP32_ADD_MODE", "default").strip().lower()
    gen_samples = int(os.getenv("FP32_ADD_GEN_SAMPLES", "50000"))
    rng = random.Random(sample_seed)
    valid_modes = {"bits", "normal_full", "wide", "small", "default"}
    if sample_mode not in valid_modes:
        dut._log.warning(f"Unknown FP32_ADD_MODE='{sample_mode}', falling back to 'default'.")
        sample_mode = "default"
    dut._log.info(f"Random operand sampler mode: {sample_mode} (seed={sample_seed})")

    async def _drive_and_measure(a: int, b: int):
        # All samplers already guarantee finite non-subnormal inputs,
        # but guard just in case.
        if not _is_finite_non_subnormal_u32(a) or not _is_finite_non_subnormal_u32(b):
            return None, None, None, None

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
                    raise RuntimeError(f"Timeout waiting for ap_done from fp32_sum ({label})")
            else:
                await RisingEdge(dut.ap_clk)
        else:
            await Timer(1, unit="ns")

        got_bits = int(dut.ap_return.value)

        with np.errstate(over='ignore', invalid='ignore'):
            ref_bits = float_to_uint32(np.float32(uint32_to_float(a)) + np.float32(uint32_to_float(b)))

        # Skip if the *result* is NaN/Inf/subnormal (e.g. overflow from adding large normals).
        if not _is_finite_non_subnormal_u32(ref_bits):
            return None, None, None, None

        got_f = np.float32(uint32_to_float(got_bits))
        ref_f = np.float32(uint32_to_float(ref_bits))
        if not np.isfinite(got_f) or not np.isfinite(ref_f):
            rel_pct = float('inf')
        elif ref_f == 0.0:
            rel_pct = 0.0 if got_f == 0.0 else float('inf')
        else:
            rel_pct = abs(float((got_f - ref_f) / ref_f)) * 100.0

        exact = (got_bits == ref_bits)
        return got_bits, ref_bits, exact, rel_pct

    # --- Pass 1: in-distribution (synthesis range) ---
    rel_err_pcts = []
    exact_matches = 0
    skipped = 0

    for _ in range(num_samples):
        a, b = _sample_operands(rng, sample_mode)
        _, _, ex, rel_pct = await _drive_and_measure(a, b)
        if ex is None:
            skipped += 1
            continue
        if ex:
            exact_matches += 1
        rel_err_pcts.append(rel_pct)

    _report_stats(dut, f"IN-DIST ({sample_mode})", rel_err_pcts, exact_matches,
                  skipped, rel_err_threshold_pct)

    # Optional dump for downstream plotting.
    dump_path = os.getenv("FP32_ADD_DUMP_PATH", "").strip()
    if dump_path:
        try:
            dump_dir = os.path.dirname(dump_path)
            if dump_dir:
                os.makedirs(dump_dir, exist_ok=True)
            np.savez_compressed(
                dump_path,
                rel_err_pct=np.asarray(rel_err_pcts, dtype=np.float32),
                sample_mode=np.asarray([sample_mode]),
                rel_err_threshold_pct=np.asarray([rel_err_threshold_pct], dtype=np.float32),
            )
            dut._log.info(f"Saved per-sample error dump: {dump_path}")
        except Exception as exc:
            dut._log.warning(f"Failed to dump per-sample errors to {dump_path}: {exc}")

    # --- Pass 2: generalisation (full IEEE normal range) ---
    # Skip if the primary mode already covers all normals.
    if sample_mode not in ("bits", "normal_full") and gen_samples > 0:
        gen_rel = []
        gen_exact = 0
        gen_skipped = 0
        gen_rng = random.Random(sample_seed + 1)

        for _ in range(gen_samples):
            a, b = _sample_operands(gen_rng, "normal_full")
            _, _, ex, rel_pct = await _drive_and_measure(a, b)
            if ex is None:
                gen_skipped += 1
                continue
            if ex:
                gen_exact += 1
            gen_rel.append(rel_pct)

        _report_stats(dut, "GENERALISATION (normal_full)", gen_rel, gen_exact,
                      gen_skipped, rel_err_threshold_pct)


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
