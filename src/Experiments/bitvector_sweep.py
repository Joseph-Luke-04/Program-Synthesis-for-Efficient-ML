import argparse
import csv
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from ..run_vitis_hls import run_vitis_hls
except ImportError:
    from run_vitis_hls import run_vitis_hls


@dataclass(frozen=True)
class SweepTarget:
    key: str
    op: str
    dtype: str
    synth_target: str
    synth_component: str
    base_cpp_prefix: str
    top_func: str
    cocotb_module: str
    variant_env: str
    fp32: bool


TARGETS: dict[str, SweepTarget] = {
    "fp32_mul": SweepTarget(
        key="fp32_mul",
        op="Multiplication",
        dtype="FP32",
        synth_target="fp32_mul",
        synth_component="full_product",
        base_cpp_prefix="solution_fp32multiplication_full_product",
        top_func="fp32_full_mul",
        cocotb_module="tests.multiplication.test_fp32_multiplier",
        variant_env="FP32_MUL_VARIANT",
        fp32=True,
    ),
    "fp32_add": SweepTarget(
        key="fp32_add",
        op="Addition",
        dtype="FP32",
        synth_target="fp32_add",
        synth_component="full_sum",
        base_cpp_prefix="solution_fp32addition_full_sum",
        top_func="fp32_sum",
        cocotb_module="tests.addition.test_fp32_adder",
        variant_env="FP32_ADD_VARIANT",
        fp32=True,
    ),
    "mxint8_mul": SweepTarget(
        key="mxint8_mul",
        op="Multiplication",
        dtype="MXINT8",
        synth_target="mxint8_mul",
        synth_component="full_product",
        base_cpp_prefix="solution_mxint8multiplication_full_product",
        top_func="mult_mxint_full_product",
        cocotb_module="tests.multiplication.test_mxint8_multiplier",
        variant_env="MXINT8_MUL_VARIANT",
        fp32=False,
    ),
    "mxint8_add": SweepTarget(
        key="mxint8_add",
        op="Addition",
        dtype="MXINT8",
        synth_target="mxint8_add",
        synth_component="full_sum",
        base_cpp_prefix="solution_mxint8addition_full_sum",
        top_func="add_full_sum",
        cocotb_module="tests.addition.test_mxint8_adder",
        variant_env="MXINT8_ADD_VARIANT",
        fp32=False,
    ),
}

FULL_FP32_EXP_BITS = 8


def parse_int_sweep(spec: str, name: str, min_value: int, max_value: int, default_step: int) -> list[int]:
    text = str(spec).strip()
    if ":" not in text:
        vals = [int(text)]
    else:
        parts = [p.strip() for p in text.split(":")]
        if len(parts) not in {2, 3}:
            raise ValueError(f"Invalid {name} '{spec}'. Use N or START:STOP[:STEP].")
        start = int(parts[0])
        stop = int(parts[1])
        step = int(parts[2]) if len(parts) == 3 else default_step
        if step <= 0:
            raise ValueError("STEP must be > 0.")

        if start >= stop:
            vals = list(range(start, stop - 1, -step))
            if vals[-1] != stop:
                vals.append(stop)
        else:
            vals = list(range(start, stop + 1, step))
            if vals[-1] != stop:
                vals.append(stop)

    for v in vals:
        if v < min_value or v > max_value:
            raise ValueError(f"{name} value {v} out of range [{min_value}, {max_value}].")
    return sorted(set(vals), reverse=True)


def parse_mant_bits(spec: str, fp32: bool) -> list[int]:
    if fp32:
        return parse_int_sweep(spec, "--mant-bits", min_value=1, max_value=24, default_step=1)
    return parse_int_sweep(spec, "--mant-bits", min_value=1, max_value=4, default_step=1)


def _replace_function(code: str, name: str, new_body: str) -> tuple[str, bool]:
    m = re.search(rf"\bap_(?:u)?int<\d+>\s+{name}\s*\([^)]*\)\s*\{{", code)
    if not m:
        return code, False

    start = m.start()
    i = m.end() - 1
    depth = 0
    end = None
    while i < len(code):
        if code[i] == "{":
            depth += 1
        elif code[i] == "}":
            depth -= 1
            if depth == 0:
                end = i + 1
                break
        i += 1
    if end is None:
        return code, False
    return code[:start] + new_body.strip("\n") + "\n" + code[end:], True


def _require_pattern(code: str, pattern: str, desc: str, target: SweepTarget) -> None:
    if not re.search(pattern, code, re.S):
        raise RuntimeError(
            f"Base C++ no longer matches expected {target.key} layout: missing {desc}.\n"
            "This is a safety guard to avoid applying stale truncation rewrites onto a changed synthesis output.\n"
            "Update rewrite rules for the new generated shape, or rerun with --force-rewrite to bypass."
        )


def validate_base_cpp_layout(code: str, target: SweepTarget, force_rewrite: bool) -> None:
    if force_rewrite:
        return

    if target.key == "fp32_mul":
        _require_pattern(
            code,
            r"ap_uint<32>\s+fp32_full_mul\s*\(\s*ap_uint<32>\s+\w+\s*,\s*ap_uint<32>\s+\w+\s*\)",
            "fp32_full_mul(ap_uint<32>, ap_uint<32>) signature",
            target,
        )
        _require_pattern(code, r"\bfp32_mult_renorm\s*\(", "fp32_mult_renorm helper", target)
        _require_pattern(code, r"\bfp32_mult_round_carry\s*\(", "fp32_mult_round_carry helper", target)
        _require_pattern(code, r"\bfp32_mult_exp\s*\(", "fp32_mult_exp helper", target)
        _require_pattern(code, r"\bfp32_mult_mant\s*\(", "fp32_mult_mant helper", target)
    elif target.key == "fp32_add":
        _require_pattern(code, r"\bfp32_aligner\s*\(", "fp32_aligner helper", target)
        _require_pattern(code, r"\bfp32_raw_summer\s*\(", "fp32_raw_summer helper", target)
        _require_pattern(code, r"\bfp32_normaliser\s*\(", "fp32_normaliser helper", target)
        _require_pattern(
            code,
            r"ap_uint<32>\s+fp32_sum\s*\(\s*ap_uint<1>\s+\w+\s*,\s*ap_uint<8>\s+\w+\s*,\s*ap_uint<23>\s+\w+\s*,\s*ap_uint<1>\s+\w+\s*,\s*ap_uint<8>\s+\w+\s*,\s*ap_uint<23>\s+\w+\s*\)",
            "fp32_sum subcomponent signature (s,e,m,s,e,m)",
            target,
        )
    elif target.key == "mxint8_mul":
        _require_pattern(code, r"\bmult_renorm_flag\s*\(", "mult_renorm_flag helper", target)
        _require_pattern(code, r"\bmult_mxint_mant\s*\(", "mult_mxint_mant helper", target)
        _require_pattern(
            code,
            r"ap_uint<8>\s+mult_mxint_full_product\s*\(\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<1>\s+\w+\s*\)",
            "mult_mxint_full_product subcomponent signature",
            target,
        )
    elif target.key == "mxint8_add":
        _require_pattern(code, r"\balign_mantissas\s*\(", "align_mantissas helper", target)
        _require_pattern(
            code,
            r"ap_uint<8>\s+add_full_sum\s*\(\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*,\s*ap_uint<4>\s+\w+\s*\)",
            "add_full_sum subcomponent signature",
            target,
        )


def _render_fp32_mult_renorm(mant_bits: int) -> str:
    drop_m = 24 - mant_bits
    return f"""
ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {{
  ap_uint<{mant_bits}> Ma_eff = (ap_uint<{mant_bits}>)(Ma >> {drop_m});
  ap_uint<{mant_bits}> Mb_eff = (ap_uint<{mant_bits}>)(Mb >> {drop_m});
  ap_uint<{mant_bits + mant_bits}> prod_eff =
      (ap_uint<{mant_bits + mant_bits}>)Ma_eff * (ap_uint<{mant_bits + mant_bits}>)Mb_eff;
  ap_uint<48> prod = ((ap_uint<48>)prod_eff) << {drop_m + drop_m};
  return (ap_uint<1>)prod[47];
}}
"""


def _render_fp32_mult_exp() -> str:
    return f"""
ap_uint<8> fp32_mult_exp(ap_uint<8> ea, ap_uint<8> eb, ap_uint<1> renorm, ap_uint<1> carry) {{
  ap_uint<10> exp10 = (ap_uint<10>)ea + (ap_uint<10>)eb;
  exp10 = (ap_uint<10>)(exp10 - (ap_uint<10>)127);
  exp10 = (ap_uint<10>)(exp10 + (ap_uint<10>)renorm);
  return (ap_uint<8>)exp10;
}}
"""


def _render_fp32_mult_mant(mant_bits: int) -> str:
    drop_m = 24 - mant_bits
    return f"""
ap_uint<23> fp32_mult_mant(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {{
  ap_uint<{mant_bits}> Ma_eff = (ap_uint<{mant_bits}>)(Ma >> {drop_m});
  ap_uint<{mant_bits}> Mb_eff = (ap_uint<{mant_bits}>)(Mb >> {drop_m});
  ap_uint<{mant_bits + mant_bits}> prod_eff =
      (ap_uint<{mant_bits + mant_bits}>)Ma_eff * (ap_uint<{mant_bits + mant_bits}>)Mb_eff;
  ap_uint<48> _let_1 = ((ap_uint<48>)prod_eff) << {drop_m + drop_m};
  ap_uint<48> _let_2 = renorm == 1 ? (ap_uint<48>)_let_1 >> 1 : (ap_uint<48>)_let_1;
  ap_uint<24> top = (ap_uint<24>)_let_2.range(46, 23);
  ap_uint<1> round = (ap_uint<1>)_let_2[22];
  ap_uint<25> rounded25 = (ap_uint<25>)(((ap_uint<25>)top) + (ap_uint<25>)round);
  return (ap_uint<23>)rounded25.range(22, 0);
}}
"""


def _render_fp32_aligner(mant_bits: int) -> str:
    drop_m = 24 - mant_bits
    return f"""
ap_uint<56> fp32_aligner(ap_uint<8> e1, ap_uint<23> m1, ap_uint<8> e2, ap_uint<23> m2) {{
  ap_uint<8> e1_t = e1;
  ap_uint<8> e2_t = e2;

  ap_uint<24> sm1 = (e1 == 0) ? (ap_uint<24>)m1 : (ap_uint<24>)(((ap_uint<24>)1 << 23) | m1);
  ap_uint<24> sm2 = (e2 == 0) ? (ap_uint<24>)m2 : (ap_uint<24>)(((ap_uint<24>)1 << 23) | m2);
  sm1 = (ap_uint<24>)(((ap_uint<24>)(sm1 >> {drop_m})) << {drop_m});
  sm2 = (ap_uint<24>)(((ap_uint<24>)(sm2 >> {drop_m})) << {drop_m});

  ap_uint<8> texp_t = (e1_t >= e2_t) ? e1_t : e2_t;
  ap_uint<8> de_t = (e1_t >= e2_t) ? (ap_uint<8>)(e1_t - e2_t) : (ap_uint<8>)(e2_t - e1_t);
  ap_uint<5> sh = (de_t > (ap_uint<8>)31) ? (ap_uint<5>)31 : (ap_uint<5>)de_t;

  ap_uint<24> am1 = (e1_t >= e2_t) ? sm1 : (ap_uint<24>)(sm1 >> sh);
  ap_uint<24> am2 = (e1_t >= e2_t) ? (ap_uint<24>)(sm2 >> sh) : sm2;
  ap_uint<8> texp = texp_t;

  ap_uint<56> pack = ((ap_uint<56>)am1 << 32) | ((ap_uint<56>)am2 << 8) | (ap_uint<56>)texp;
  return pack;
}}
"""


def _render_fp32_raw_summer(mant_bits: int) -> str:
    drop_m = 24 - mant_bits
    return f"""
ap_uint<26> fp32_raw_summer(ap_uint<1> s1, ap_uint<24> aligned_m1,
                            ap_uint<1> s2, ap_uint<24> aligned_m2) {{
  ap_uint<{mant_bits}> A_t = (ap_uint<{mant_bits}>)(aligned_m1 >> {drop_m});
  ap_uint<{mant_bits}> B_t = (ap_uint<{mant_bits}>)(aligned_m2 >> {drop_m});
  ap_uint<{mant_bits + 1}> A = (ap_uint<{mant_bits + 1}>)A_t;
  ap_uint<{mant_bits + 1}> B = (ap_uint<{mant_bits + 1}>)B_t;

  ap_uint<{mant_bits + 1}> sum_small;
  ap_uint<1> out_sign;

  if (s1 == s2) {{
    sum_small = A + B;
    out_sign = s1;
  }} else {{
    if (A == B) {{
      sum_small = 0;
      out_sign = 0;
    }} else if (A > B) {{
      sum_small = A - B;
      out_sign = s1;
    }} else {{
      sum_small = B - A;
      out_sign = s2;
    }}
  }}

  ap_uint<25> expanded = (ap_uint<25>)((ap_uint<25>)sum_small << {drop_m});
  return ((ap_uint<26>)out_sign << 25) | (ap_uint<26>)expanded;
}}
"""


def _render_fp32_normaliser(mant_bits: int) -> str:
    drop_m = 24 - mant_bits
    return f"""
ap_uint<32> fp32_normaliser(ap_uint<25> raw_sum_mantissa, ap_uint<1> raw_sign, ap_uint<8> target_exponent) {{
  if (raw_sum_mantissa == 0) {{
    return (ap_uint<32>)0;
  }}

  ap_uint<8> exp_t = target_exponent;
  ap_int<11> exp_acc = (ap_int<11>)exp_t;

  ap_uint<25> abs_full = raw_sum_mantissa;
  ap_uint<{mant_bits + 1}> abs_t = (ap_uint<{mant_bits + 1}>)(abs_full >> {drop_m});

  ap_uint<{mant_bits}> norm_small = 0;
  if (abs_t[{mant_bits}] == 1) {{
    norm_small = (ap_uint<{mant_bits}>)(abs_t >> 1);
    exp_acc = exp_acc + (ap_int<11>)1;
  }} else if (abs_t[{mant_bits - 1}] == 1) {{
    norm_small = (ap_uint<{mant_bits}>)abs_t;
  }} else {{
    int msb = -1;
    for (int i = {mant_bits - 2}; i >= 0; --i) {{
      if (abs_t[i]) {{
        msb = i;
        break;
      }}
    }}
    if (msb < 0) {{
      return (ap_uint<32>)0;
    }}
    int lsh = {mant_bits - 1} - msb;
    norm_small = (ap_uint<{mant_bits}>)(abs_t << lsh);
    exp_acc = exp_acc - (ap_int<11>)lsh;
  }}

  ap_uint<24> norm24 = (ap_uint<24>)((ap_uint<24>)norm_small << {drop_m});
  ap_uint<23> frac = (ap_uint<23>)norm24.range(22, 0);
  ap_uint<8> exp_out = (ap_uint<8>)exp_acc;
  ap_uint<1> sign = raw_sign;
  return (ap_uint<32>)(((ap_uint<32>)sign << 31) | ((ap_uint<32>)exp_out << 23) | (ap_uint<32>)frac);
}}
"""


def _render_mxint8_mul(mant_bits: int) -> str:
    drop_m = 4 - mant_bits
    return f"""
ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {{
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> s1_q = (ap_int<4>)((s1 >> {drop_m}) << {drop_m});
  ap_int<4> s2_q = (ap_int<4>)((s2 >> {drop_m}) << {drop_m});

  ap_uint<4> m1_q = (ap_uint<4>)s1_q;
  ap_uint<4> m2_q = (ap_uint<4>)s2_q;

  ap_uint<1> rf = mult_renorm_flag(m1_q, m2_q);
  ap_uint<4> mant = mult_mxint_mant(m1_q, m2_q);
  ap_uint<4> exp = mult_mxint_exp(e1, e2, rf);
  return (ap_uint<8>)((((ap_uint<8>)mant) << 4) | exp);
}}
"""


def _render_mxint8_renorm_flag(mant_bits: int) -> str:
    drop_m = 4 - mant_bits
    return f"""
ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {{
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> s1_q = (ap_int<4>)((s1 >> {drop_m}) << {drop_m});
  ap_int<4> s2_q = (ap_int<4>)((s2 >> {drop_m}) << {drop_m});
  ap_int<8> prod = (ap_int<8>)(s1_q * s2_q);
  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;
  return (abs_p <= (ap_int<8>)32) ? (ap_uint<1>)1 : (ap_uint<1>)0;
}}
"""


def _render_mxint8_mant(mant_bits: int) -> str:
    drop_m = 4 - mant_bits
    return f"""
ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {{
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> s1_q = (ap_int<4>)((s1 >> {drop_m}) << {drop_m});
  ap_int<4> s2_q = (ap_int<4>)((s2 >> {drop_m}) << {drop_m});
  ap_int<8> prod = (ap_int<8>)(s1_q * s2_q);
  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;
  ap_int<8> inter = (abs_p <= (ap_int<8>)32)
                  ? (ap_int<8>)((prod << 1) >> 3)
                  : (ap_int<8>)(prod >> 3);
  return (ap_uint<4>)inter;
}}
"""


def _render_mxint8_add(mant_bits: int) -> str:
    drop_m = 4 - mant_bits
    return f"""
ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {{
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> s1_q = (ap_int<4>)((s1 >> {drop_m}) << {drop_m});
  ap_int<4> s2_q = (ap_int<4>)((s2 >> {drop_m}) << {drop_m});

  ap_uint<4> m1_q = (ap_uint<4>)s1_q;
  ap_uint<4> m2_q = (ap_uint<4>)s2_q;
  ap_uint<9> raw = add_raw(m1_q, e1, m2_q, e2);
  return normalise_addition((ap_uint<5>)raw.range(8, 4), (ap_uint<4>)raw.range(3, 0));
}}
"""


def _render_mxint8_aligner(mant_bits: int) -> str:
    drop_m = 4 - mant_bits
    return f"""
ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {{
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> s1_q = (ap_int<4>)((s1 >> {drop_m}) << {drop_m});
  ap_int<4> s2_q = (ap_int<4>)((s2 >> {drop_m}) << {drop_m});
  ap_int<4> se1 = (ap_int<4>)e1;
  ap_int<4> se2 = (ap_int<4>)e2;
  bool cond = (se1 >= se2);
  ap_uint<4> d = cond ? (ap_uint<4>)(e1 - e2) : (ap_uint<4>)(e2 - e1);
  ap_int<4> a1, a2;
  if (cond) {{
    a1 = s1_q;
    if (d == 0) {{
      a2 = s2_q;
    }} else if (d >= 4) {{
      a2 = (ap_int<4>)0;
    }} else {{
      ap_uint<3> ush = (ap_uint<3>)d;
      a2 = (ap_int<4>)(s2_q >> ush);
    }}
  }} else {{
    a2 = s2_q;
    if (d == 0) {{
      a1 = s1_q;
    }} else if (d >= 4) {{
      a1 = (ap_int<4>)0;
    }} else {{
      ap_uint<3> ush = (ap_uint<3>)d;
      a1 = (ap_int<4>)(s1_q >> ush);
    }}
  }}
  return (ap_uint<8>)((((ap_uint<8>)(ap_uint<4>)a1) << 4) | (ap_uint<4>)a2);
}}
"""


def rewrite_cpp_for_variant(base_code: str, target: SweepTarget, mant_bits: int) -> str:
    code = base_code
    changed = False
    if target.key == "fp32_mul":
        replaced = 0
        repls = [
            ("fp32_mult_renorm", _render_fp32_mult_renorm(mant_bits)),
            ("fp32_mult_exp", _render_fp32_mult_exp()),
            ("fp32_mult_mant", _render_fp32_mult_mant(mant_bits)),
        ]
        for fn, body in repls:
            code, ok = _replace_function(code, fn, body)
            changed = changed or ok
            replaced += 1 if ok else 0
        if replaced != len(repls):
            raise RuntimeError(
                "Could not rewrite all FP32 multiply subcomponent helpers "
                f"(replaced {replaced}/{len(repls)})."
            )
    elif target.key == "fp32_add":
        replaced = 0
        repls = [
            ("fp32_aligner", _render_fp32_aligner(mant_bits)),
            ("fp32_raw_summer", _render_fp32_raw_summer(mant_bits)),
            ("fp32_normaliser", _render_fp32_normaliser(mant_bits)),
        ]
        for fn, body in repls:
            code, ok = _replace_function(code, fn, body)
            changed = changed or ok
            replaced += 1 if ok else 0
        if replaced != len(repls):
            raise RuntimeError(
                "Could not rewrite all FP32 addition subcomponent helpers "
                f"(replaced {replaced}/{len(repls)})."
            )
    elif target.key == "mxint8_mul":
        replaced = 0
        repls = [
            ("mult_renorm_flag", _render_mxint8_renorm_flag(mant_bits)),
            ("mult_mxint_mant", _render_mxint8_mant(mant_bits)),
        ]
        for fn, body in repls:
            code, ok = _replace_function(code, fn, body)
            changed = changed or ok
            replaced += 1 if ok else 0
        if replaced != len(repls):
            raise RuntimeError(
                "Could not rewrite all MXINT8 multiply subcomponent helpers "
                f"(replaced {replaced}/{len(repls)})."
            )
    elif target.key == "mxint8_add":
        code, changed = _replace_function(code, "align_mantissas", _render_mxint8_aligner(mant_bits))
        if not changed:
            raise RuntimeError("Could not rewrite MXINT8 addition helper align_mantissas.")

    if not changed:
        raise RuntimeError(f"No rewrite was applied for target {target.key}.")
    return code


def run_synthesis_for_target(target: SweepTarget, repo_root: Path) -> None:
    env = os.environ.copy()
    env["SYNTH_TARGET"] = target.synth_target
    env["SYNTH_COMPONENT"] = target.synth_component
    env["SYNTH_RUN_IMPL"] = "0"
    subprocess.run([sys.executable, "-m", "src.synthesis_driver"], cwd=repo_root, env=env, check=True)


def find_latest_base_cpp(results_cpp_dir: Path, base_prefix: str) -> Path | None:
    candidates: list[Path] = []
    for p in results_cpp_dir.glob("*.cpp"):
        stem = p.stem
        if stem == base_prefix:
            candidates.append(p)
            continue
        # Never auto-pick combined artefacts when caller asked for subcomponent base.
        if stem.startswith(base_prefix + "_combined"):
            continue
        if stem.startswith(base_prefix + "_"):
            candidates.append(p)

    if not candidates:
        return None
    return max(candidates, key=lambda p: p.stat().st_mtime)


def parse_cocotb_metrics(text: str, target: SweepTarget) -> dict[str, Any]:
    out: dict[str, Any] = {
        "accuracy_source": "cocotb",
        "exact_matches": -1,
        "total_cases": -1,
        "accuracy_exact_match": -1.0,
        "within_rel_pct": -1.0,
        "within_rel_threshold_pct": -1.0,
        "within_5pct_rel": -1.0,
        "ulp_avg": -1.0,
        "ulp_p99": -1,
        "ulp_max": -1,
        "abs_err_avg": -1.0,
        "abs_err_p99": -1.0,
        "abs_err_max": -1.0,
    }

    m_run = re.search(r"Ran\s+(\d+)\s+(?:cases|test cases)\s+\(skipped\s+(\d+)\)", text)
    if m_run:
        out["total_cases"] = int(m_run.group(1))

    if target.fp32:
        m_ulp = re.search(r"ULP avg=([0-9.eE+-]+),\s*p99=(\d+),\s*max=(\d+)", text)
        if m_ulp:
            out["ulp_avg"] = float(m_ulp.group(1))
            out["ulp_p99"] = int(m_ulp.group(2))
            out["ulp_max"] = int(m_ulp.group(3))

        m_exact = re.search(r"Exact\s+([0-9.]+)%", text)
        if m_exact:
            exact_ratio = float(m_exact.group(1)) / 100.0
            out["accuracy_exact_match"] = exact_ratio
            total = out.get("total_cases", -1)
            if isinstance(total, int) and total > 0:
                out["exact_matches"] = int(round(exact_ratio * total))

        m_within_rel = re.search(r"Within\s+([0-9.]+)%\s+relative\s+error:\s+([0-9.]+)%", text)
        if m_within_rel:
            threshold = float(m_within_rel.group(1))
            ratio = float(m_within_rel.group(2)) / 100.0
            out["within_rel_threshold_pct"] = threshold
            out["within_rel_pct"] = ratio
            if abs(threshold - 5.0) < 1e-9:
                out["within_5pct_rel"] = ratio
        return out

    # MXINT8 tests: pick metrics from the "Quantized oracle" section.
    q = re.search(
        r"Quantized oracle:\s*"
        r".*?Max Absolute Error:\s*([0-9.eE+-]+)"
        r".*?Average Absolute Error:\s*([0-9.eE+-]+)"
        r".*?99th Percentile Error:\s*([0-9.eE+-]+)"
        r".*?Percent Within\s+([0-9.]+)%\s+Full-Scale Error:\s*([0-9.]+)%",
        text,
        re.S,
    )
    if q:
        out["abs_err_max"] = float(q.group(1))
        out["abs_err_avg"] = float(q.group(2))
        out["abs_err_p99"] = float(q.group(3))
        out["within_rel_threshold_pct"] = float(q.group(4))
        out["within_rel_pct"] = float(q.group(5)) / 100.0
    return out


def run_cocotb_accuracy(
    repo_root: Path,
    hls_root: Path,
    variant_stem: str,
    target: SweepTarget,
    timeout_seconds: int,
    log_path: Path,
    rel_error_pct: float,
    cocotb_mode: str,
    dump_samples_path: Path | None = None,
) -> dict[str, Any]:
    acc_root = repo_root / "accuracy_tests"
    env = os.environ.copy()
    env["TOPLEVEL_LANG"] = "verilog"
    env[target.variant_env] = "subcomponents"

    if target.key == "fp32_mul":
        env["FP32_MUL_REL_ERR_PCT"] = f"{rel_error_pct}"
        env["FP32_MUL_MODE"] = cocotb_mode
        if dump_samples_path is not None:
            env["FP32_MUL_DUMP_PATH"] = str(dump_samples_path.resolve())
    elif target.key == "fp32_add":
        if dump_samples_path is not None:
            env["FP32_ADD_DUMP_PATH"] = str(dump_samples_path.resolve())
    elif target.key == "mxint8_mul":
        if dump_samples_path is not None:
            env["MXINT8_MUL_DUMP_PATH"] = str(dump_samples_path.resolve())
    elif target.key == "mxint8_add":
        if dump_samples_path is not None:
            env["MXINT8_ADD_DUMP_PATH"] = str(dump_samples_path.resolve())

    mode_tag = re.sub(r"[^a-zA-Z0-9_.-]+", "_", cocotb_mode)
    env["COCOTB_RESULTS_FILE"] = str((log_path.parent / f"{variant_stem}_{mode_tag}_results.xml").resolve())

    cmd = [
        "make",
        f"HLS_BASE={hls_root}",
        f"HLS_SOLN={variant_stem}",
        f"TOPLEVEL={target.top_func}",
        f"MODULE={target.cocotb_module}",
        "TOPLEVEL_LANG=verilog",
    ]

    extras = ""
    if target.key == "fp32_mul":
        extras = (
            f"FP32_MUL_REL_ERR_PCT={env['FP32_MUL_REL_ERR_PCT']} "
            f"FP32_MUL_MODE={env['FP32_MUL_MODE']} "
            + (f"FP32_MUL_DUMP_PATH={env['FP32_MUL_DUMP_PATH']} " if "FP32_MUL_DUMP_PATH" in env else "")
        )
    print(
        "[ACC-CMD] "
        f"{target.variant_env}={env[target.variant_env]} "
        + extras
        + " ".join(cmd)
    )

    try:
        proc = subprocess.run(
            cmd,
            cwd=acc_root,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_seconds if timeout_seconds > 0 else None,
        )
        output = (proc.stdout or "") + ("\n" + proc.stderr if proc.stderr else "")
        log_path.write_text(output)
        metrics = parse_cocotb_metrics(output, target)
        metrics["cocotb_passed"] = proc.returncode == 0
        metrics["cocotb_returncode"] = proc.returncode
        metrics["error_samples_npz"] = str(dump_samples_path) if dump_samples_path is not None else ""
        return metrics
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + ("\n" + exc.stderr if exc.stderr else "")
        log_path.write_text(output + "\n[TIMEOUT]\n")
        metrics = parse_cocotb_metrics(output, target)
        metrics["cocotb_passed"] = False
        metrics["cocotb_returncode"] = -9
        metrics["error_samples_npz"] = str(dump_samples_path) if dump_samples_path is not None else ""
        return metrics


def compute_area_score(row: dict[str, Any], w_lut: float, w_ff: float, w_dsp: float, w_bram: float) -> float:
    lut = row.get("LUTs", -1)
    ff = row.get("FFs", -1)
    dsp = row.get("DSPs", -1)
    bram = row.get("BRAMs", -1)
    if any((not isinstance(v, (int, float)) or v < 0) for v in (lut, ff, dsp, bram)):
        return 1e15
    return float(lut) * w_lut + float(ff) * w_ff + float(dsp) * w_dsp + float(bram) * w_bram


def pick_optuna_accuracy_objective(row: dict[str, Any], target: SweepTarget) -> tuple[float, str]:
    within_rel = row.get("within_rel_pct", -1.0)
    if isinstance(within_rel, (int, float)) and float(within_rel) >= 0.0:
        return float(within_rel), "within_rel_pct"

    exact = row.get("accuracy_exact_match", -1.0)
    if isinstance(exact, (int, float)) and float(exact) >= 0.0:
        return float(exact), "accuracy_exact_match"

    abs_err = row.get("abs_err_avg", -1.0)
    if isinstance(abs_err, (int, float)) and float(abs_err) >= 0.0:
        return -float(abs_err), "neg_abs_err_avg"

    return -1.0, "unknown"


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Unified bitvector truncation sweep/Optuna search for FP32 and MXINT8 subcomponent designs. "
            "FP32 truncates mantissa only (exponent fixed at 8); MXINT8 truncates mantissa only."
        )
    )
    parser.add_argument("--target", choices=list(TARGETS.keys()), required=False)
    parser.add_argument(
        "--all-targets",
        action="store_true",
        help="Run all targets sequentially (fp32_add, fp32_mul, mxint8_add, mxint8_mul).",
    )
    parser.add_argument("--base-cpp", default="", help="Optional explicit base C++ path.")
    parser.add_argument(
        "--force-rewrite",
        action="store_true",
        help="Bypass base-layout safety checks and force function-body rewrites.",
    )
    parser.add_argument("--run-synthesis", action="store_true", help="Regenerate base synthesized C++ first.")
    parser.add_argument("--mant-bits", default="", help="Mantissa bit candidates: N or START:STOP[:STEP].")
    parser.add_argument(
        "--exp-bits",
        default="",
        help="Deprecated for FP32 mantissa-only mode; ignored (exponent fixed at 8).",
    )

    parser.add_argument("--accuracy-source", default="cocotb", choices=["cocotb"], help="Accuracy backend.")
    parser.add_argument("--rel-error-pct", type=float, default=5.0, help="FP32 mul relative-error threshold (%%) for cocotb.")
    parser.add_argument(
        "--cocotb-mode",
        default="bits",
        choices=["bits", "normal_full", "wide", "small"],
        help="FP32 multiplier operand sampler mode in cocotb tests.",
    )
    parser.add_argument("--cocotb-timeout", type=int, default=0, help="Per-variant cocotb timeout seconds.")

    parser.add_argument("--skip-hls", action="store_true", help="Skip HLS and hardware report collection.")
    parser.add_argument(
        "--impl",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Run Vivado implementation after HLS synthesis (default: enabled).",
    )
    parser.add_argument(
        "--show-cpp",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="Print generated C++ per variant.",
    )

    parser.add_argument("--search", default="sweep", choices=["sweep", "optuna"], help="Exhaustive sweep or Optuna search.")
    parser.add_argument("--optuna-trials", type=int, default=24, help="Number of Optuna trials.")
    parser.add_argument(
        "--optuna-sampler",
        default="nsga2",
        choices=["nsga2", "tpe", "random"],
        help="Optuna sampler.",
    )
    parser.add_argument("--optuna-seed", type=int, default=7, help="Seed for Optuna sampler.")
    parser.add_argument("--optuna-study-name", default="bitvector_multiobj", help="Optuna study name.")
    parser.add_argument(
        "--optuna-storage",
        default="",
        help="Optional Optuna storage URL (e.g. sqlite:///results/sweeps/bitvector/optuna.db).",
    )

    parser.add_argument("--area-lut-weight", type=float, default=1.0, help="Area objective LUT weight.")
    parser.add_argument("--area-ff-weight", type=float, default=0.1, help="Area objective FF weight.")
    parser.add_argument("--area-dsp-weight", type=float, default=200.0, help="Area objective DSP weight.")
    parser.add_argument("--area-bram-weight", type=float, default=1000.0, help="Area objective BRAM weight.")

    parser.add_argument("--output-dir", default="", help="Output directory root for this run.")
    parser.add_argument("--min-accuracy", type=float, default=None, help="Optional post-run accuracy threshold.")

    args = parser.parse_args()
    if not args.all_targets and not args.target:
        parser.error("Either --target or --all-targets must be provided.")

    if args.all_targets:
        src_dir = Path(__file__).resolve().parent
        repo_root = src_dir.parent.parent

        # --base-cpp points to one file and is ambiguous for --all-targets.
        if args.base_cpp:
            parser.error("--base-cpp is only supported with a single --target run.")

        ordered_targets = ["fp32_add", "fp32_mul", "mxint8_add", "mxint8_mul"]
        combined_rows: list[dict[str, Any]] = []

        for t_key in ordered_targets:
            t_cfg = TARGETS[t_key]
            cmd = [sys.executable, "-m", "src.Experiments.bitvector_sweep", "--target", t_key]

            if args.run_synthesis:
                cmd.append("--run-synthesis")
            if args.mant_bits:
                cmd += ["--mant-bits", str(args.mant_bits)]
            cmd += ["--accuracy-source", str(args.accuracy_source)]
            cmd += ["--search", str(args.search)]
            cmd += ["--optuna-trials", str(args.optuna_trials)]
            cmd += ["--optuna-sampler", str(args.optuna_sampler)]
            cmd += ["--optuna-seed", str(args.optuna_seed)]
            cmd += ["--optuna-study-name", f"{args.optuna_study_name}_{t_key}"]
            if args.optuna_storage:
                storage = str(args.optuna_storage)
                if storage.startswith("sqlite:///"):
                    storage = storage[:-3] + f"_{t_key}.db"
                cmd += ["--optuna-storage", storage]

            cmd += ["--rel-error-pct", str(args.rel_error_pct)]
            if t_key == "fp32_mul":
                cmd += ["--cocotb-mode", str(args.cocotb_mode)]

            if args.cocotb_timeout:
                cmd += ["--cocotb-timeout", str(args.cocotb_timeout)]
            if args.skip_hls:
                cmd.append("--skip-hls")

            cmd.append("--impl" if args.impl else "--no-impl")
            cmd.append("--show-cpp" if args.show_cpp else "--no-show-cpp")

            cmd += ["--area-lut-weight", str(args.area_lut_weight)]
            cmd += ["--area-ff-weight", str(args.area_ff_weight)]
            cmd += ["--area-dsp-weight", str(args.area_dsp_weight)]
            cmd += ["--area-bram-weight", str(args.area_bram_weight)]

            if args.min_accuracy is not None:
                cmd += ["--min-accuracy", str(args.min_accuracy)]

            if args.output_dir:
                child_out = Path(args.output_dir).resolve() / t_key
                cmd += ["--output-dir", str(child_out)]
            else:
                child_out = (repo_root / "results" / "sweeps" / f"bitvector_{t_key}").resolve()

            print(f"[ALL-TARGETS] Running: {' '.join(cmd)}")
            proc = subprocess.run(cmd, cwd=repo_root)
            if proc.returncode != 0:
                raise RuntimeError(f"--all-targets failed for {t_key} (rc={proc.returncode}).")

            summary_csv = child_out / "summary.csv"
            if summary_csv.exists():
                with open(summary_csv, newline="") as f:
                    for row in csv.DictReader(f):
                        row["run_target"] = t_key
                        combined_rows.append(row)

        combined_root = Path(args.output_dir).resolve() if args.output_dir else (repo_root / "results" / "sweeps" / "bitvector_all").resolve()
        combined_root.mkdir(parents=True, exist_ok=True)
        combined_csv = combined_root / "summary_all_targets.csv"
        combined_json = combined_root / "summary_all_targets.json"
        if combined_rows:
            fields = list(combined_rows[0].keys())
            with open(combined_csv, "w", newline="") as f:
                writer = csv.DictWriter(f, fieldnames=fields)
                writer.writeheader()
                writer.writerows(combined_rows)
            combined_json.write_text(json.dumps(combined_rows, indent=2))
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_csv}")
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_json}")
        else:
            print("[ALL-TARGETS] Completed, but no per-target summary rows were found.")
        return

    target = TARGETS[args.target]

    src_dir = Path(__file__).resolve().parent
    repo_root = src_dir.parent.parent

    mode_tag = (
        re.sub(r"[^a-zA-Z0-9_.-]+", "_", str(args.cocotb_mode).strip().lower())
        if target.key == "fp32_mul"
        else "default"
    )

    output_dir = (
        Path(args.output_dir).resolve()
        if args.output_dir
        else (repo_root / "results" / "sweeps" / f"bitvector_{target.key}").resolve()
    )
    variants_dir = output_dir / "variants_cpp"
    hls_root = output_dir / "hls"
    cocotb_logs_dir = output_dir / "accuracy_logs"
    error_samples_dir = output_dir / "error_samples"

    variants_dir.mkdir(parents=True, exist_ok=True)
    hls_root.mkdir(parents=True, exist_ok=True)
    cocotb_logs_dir.mkdir(parents=True, exist_ok=True)
    error_samples_dir.mkdir(parents=True, exist_ok=True)

    if args.run_synthesis:
        print(f"[INFO] Running synthesis for {target.synth_target}/{target.synth_component}...")
        run_synthesis_for_target(target, repo_root)

    default_base = repo_root / "results" / "cpp" / f"{target.base_cpp_prefix}.cpp"
    if args.base_cpp:
        base_cpp = Path(args.base_cpp).resolve()
    else:
        latest = find_latest_base_cpp(repo_root / "results" / "cpp", target.base_cpp_prefix)
        base_cpp = latest.resolve() if latest else default_base.resolve()

    if not base_cpp.exists():
        raise FileNotFoundError(f"Base C++ file not found: {base_cpp}")

    if target.fp32:
        mant_spec = args.mant_bits if args.mant_bits else "24:1:1"
        mant_bits_list = parse_mant_bits(mant_spec, fp32=True)
        exp_bits_list = [FULL_FP32_EXP_BITS]
        candidates = list(mant_bits_list)
    else:
        mant_spec = args.mant_bits if args.mant_bits else "4:1:1"
        mant_bits_list = parse_mant_bits(mant_spec, fp32=False)
        exp_bits_list = [4]
        candidates = list(mant_bits_list)

    base_code = base_cpp.read_text()
    validate_base_cpp_layout(base_code, target, force_rewrite=bool(args.force_rewrite))

    print(f"[INFO] Target: {target.key} ({target.dtype} {target.op})")
    print(f"[INFO] Base design: {base_cpp}")
    print(f"[INFO] Candidate mantissa bits: {mant_bits_list}")
    if target.fp32:
        if args.exp_bits:
            print("[INFO] Ignoring --exp-bits; exponent bits are fixed at 8.")
        print("[INFO] Exponent bits fixed at 8 (no exponent truncation).")
    print(f"[INFO] Candidate points (mant, exp): {[(m, exp_bits_list[0]) for m in candidates]}")
    print(f"[INFO] Search mode: {args.search}")

    if args.skip_hls and args.search == "optuna":
        raise ValueError("Optuna multi-objective requires area metrics; do not use --skip-hls.")

    rows: list[dict[str, Any]] = []
    old_hls_root = os.environ.get("VITIS_HLS_RESULTS_ROOT")
    os.environ["VITIS_HLS_RESULTS_ROOT"] = str(hls_root)

    def evaluate_candidate(mant_bits: int, eval_label: str = "") -> dict[str, Any]:
        exp_bits = FULL_FP32_EXP_BITS if target.fp32 else 4
        variant_stem = f"{base_cpp.stem}_m{mant_bits}"
        variant_cpp = variants_dir / f"{variant_stem}.cpp"

        variant_code = rewrite_cpp_for_variant(base_code, target, mant_bits)
        variant_cpp.write_text(variant_code)

        prefix = "[EVAL]" if not eval_label else f"[EVAL:{eval_label}]"
        print(
            f"{prefix} mantissa_bits={mant_bits} exponent_bits={exp_bits} variant={variant_cpp}"
        )
        if args.show_cpp:
            print(f"\n--- C++ Variant: {variant_stem} ---\n{variant_code}")

        hw: dict[str, Any] = {"LUTs": -1, "FFs": -1, "DSPs": -1, "BRAMs": -1, "Cycles": -1, "Fmax_MHz": -1}
        if not args.skip_hls:
            hw = run_vitis_hls(str(variant_cpp), top_func=target.top_func, impl=args.impl) or hw

        cocotb_log = cocotb_logs_dir / f"{variant_stem}_{mode_tag}.log"
        sample_dump = error_samples_dir / f"{variant_stem}_{mode_tag}.npz"
        acc = run_cocotb_accuracy(
            repo_root=repo_root,
            hls_root=hls_root,
            variant_stem=variant_stem,
            target=target,
            timeout_seconds=args.cocotb_timeout,
            log_path=cocotb_log,
            rel_error_pct=float(args.rel_error_pct),
            cocotb_mode=str(args.cocotb_mode),
            dump_samples_path=sample_dump,
        )
        print(
            f"[ACC] exact={acc.get('accuracy_exact_match', -1.0):.6f} "
            f"within={acc.get('within_rel_pct', -1.0):.6f} "
            f"ulp_p99={acc.get('ulp_p99', -1)} abs_p99={acc.get('abs_err_p99', -1.0)} "
            f"pass={acc.get('cocotb_passed')} log={cocotb_log}"
        )

        row: dict[str, Any] = {
            "search_mode": args.search,
            "target": target.key,
            "op": target.op,
            "dtype": target.dtype,
            "variant_cpp": str(variant_cpp),
            "mantissa_bits": mant_bits,
            "mantissa_bits_a": mant_bits,
            "mantissa_bits_b": mant_bits,
            "mantissa_bits_effective": mant_bits,
            "exponent_bits": exp_bits,
            "exponent_bits_a": exp_bits,
            "exponent_bits_b": exp_bits,
            "accuracy_source": acc.get("accuracy_source"),
            "cocotb_mode": args.cocotb_mode if target.key == "fp32_mul" else "",
            "exact_matches": acc.get("exact_matches", -1),
            "total_cases": acc.get("total_cases", -1),
            "accuracy_exact_match": acc.get("accuracy_exact_match", -1.0),
            "within_rel_pct": acc.get("within_rel_pct", -1.0),
            "within_rel_threshold_pct": acc.get("within_rel_threshold_pct", -1.0),
            "within_5pct_rel": acc.get("within_5pct_rel", -1.0),
            "ulp_avg": acc.get("ulp_avg", -1.0),
            "ulp_p99": acc.get("ulp_p99", -1),
            "ulp_max": acc.get("ulp_max", -1),
            "abs_err_avg": acc.get("abs_err_avg", -1.0),
            "abs_err_p99": acc.get("abs_err_p99", -1.0),
            "abs_err_max": acc.get("abs_err_max", -1.0),
            "cocotb_passed": acc.get("cocotb_passed"),
            "cocotb_returncode": acc.get("cocotb_returncode"),
            "accuracy_log": str(cocotb_log),
            "error_samples_npz": acc.get("error_samples_npz", ""),
            "LUTs": hw.get("LUTs", -1),
            "FFs": hw.get("FFs", -1),
            "DSPs": hw.get("DSPs", -1),
            "BRAMs": hw.get("BRAMs", -1),
            "Cycles": hw.get("Cycles", -1),
            "Fmax_MHz": hw.get("Fmax_MHz", -1),
        }
        row["area_score"] = compute_area_score(
            row,
            args.area_lut_weight,
            args.area_ff_weight,
            args.area_dsp_weight,
            args.area_bram_weight,
        )
        rows.append(row)
        return row

    try:
        if args.search == "sweep":
            for mant_bits in candidates:
                evaluate_candidate(mant_bits)
        else:
            try:
                import optuna
            except ImportError as exc:
                raise RuntimeError(
                    "Optuna is not installed. Install it (pip install optuna) or use --search sweep."
                ) from exc

            if args.optuna_sampler == "nsga2":
                sampler = optuna.samplers.NSGAIISampler(seed=args.optuna_seed)
            elif args.optuna_sampler == "tpe":
                sampler = optuna.samplers.TPESampler(seed=args.optuna_seed)
            else:
                sampler = optuna.samplers.RandomSampler(seed=args.optuna_seed)

            study = optuna.create_study(
                directions=["maximize", "minimize"],
                sampler=sampler,
                study_name=args.optuna_study_name,
                storage=args.optuna_storage if args.optuna_storage else None,
                load_if_exists=True,
            )

            cache: dict[int, dict[str, Any]] = {}
            labels = [str(m) for m in candidates]

            def objective(trial):
                label = str(trial.suggest_categorical("mantissa_bits", labels))
                m = int(label)
                key = m
                if key in cache:
                    row = cache[key]
                else:
                    row = evaluate_candidate(m, eval_label=f"trial-{trial.number}")
                    cache[key] = row

                acc, acc_metric = pick_optuna_accuracy_objective(row, target)
                area = row["area_score"]
                if not isinstance(acc, (int, float)):
                    acc = -1.0
                if not isinstance(area, (int, float)):
                    area = 1e15

                trial.set_user_attr("variant_cpp", row["variant_cpp"])
                trial.set_user_attr("mantissa_bits", row["mantissa_bits"])
                trial.set_user_attr("exponent_bits", row["exponent_bits"])
                trial.set_user_attr("LUTs", row["LUTs"])
                trial.set_user_attr("DSPs", row["DSPs"])
                trial.set_user_attr("accuracy_metric", acc_metric)
                return float(acc), float(area)

            study.optimize(objective, n_trials=max(1, int(args.optuna_trials)))

            trials_csv = output_dir / "optuna_trials.csv"
            with open(trials_csv, "w", newline="") as f:
                fieldnames = [
                    "trial_number",
                    "state",
                    "value_accuracy",
                    "accuracy_metric",
                    "value_area",
                    "mantissa_bits",
                    "exponent_bits",
                    "LUTs",
                    "DSPs",
                    "variant_cpp",
                ]
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                for t in study.trials:
                    label = t.params.get("bitvector_pair")
                    if label is not None:
                        m = int(str(label))
                        e = FULL_FP32_EXP_BITS if target.fp32 else 4
                    else:
                        m = None
                        e = None
                    vals = t.values if t.values else [None, None]
                    writer.writerow(
                        {
                            "trial_number": t.number,
                            "state": str(t.state),
                            "value_accuracy": vals[0],
                            "accuracy_metric": t.user_attrs.get("accuracy_metric"),
                            "value_area": vals[1],
                            "mantissa_bits": m,
                            "exponent_bits": e,
                            "LUTs": t.user_attrs.get("LUTs"),
                            "DSPs": t.user_attrs.get("DSPs"),
                            "variant_cpp": t.user_attrs.get("variant_cpp"),
                        }
                    )

            pareto_json = output_dir / "optuna_pareto.json"
            pareto_rows = []
            for t in study.best_trials:
                label = t.params.get("bitvector_pair")
                if label is not None:
                    m = int(str(label))
                    e = FULL_FP32_EXP_BITS if target.fp32 else 4
                else:
                    m = None
                    e = None
                vals = t.values if t.values else [None, None]
                pareto_rows.append(
                    {
                        "trial_number": t.number,
                        "value_accuracy": vals[0],
                        "accuracy_metric": t.user_attrs.get("accuracy_metric"),
                        "value_area": vals[1],
                        "mantissa_bits": m,
                        "exponent_bits": e,
                        "variant_cpp": t.user_attrs.get("variant_cpp"),
                        "LUTs": t.user_attrs.get("LUTs"),
                        "DSPs": t.user_attrs.get("DSPs"),
                    }
                )
            pareto_json.write_text(json.dumps(pareto_rows, indent=2))
            print(f"[INFO] Wrote Optuna trials: {trials_csv}")
            print(f"[INFO] Wrote Optuna Pareto set: {pareto_json}")

            valid_pareto = [
                p
                for p in pareto_rows
                if isinstance(p.get("value_accuracy"), (int, float)) and isinstance(p.get("value_area"), (int, float))
            ]
            if valid_pareto:
                best_acc = max(valid_pareto, key=lambda p: (float(p["value_accuracy"]), -float(p["value_area"])))
                best_area = min(valid_pareto, key=lambda p: (float(p["value_area"]), -float(p["value_accuracy"])))

                acc_vals = [float(p["value_accuracy"]) for p in valid_pareto]
                area_vals = [float(p["value_area"]) for p in valid_pareto]
                acc_min, acc_max = min(acc_vals), max(acc_vals)
                area_min, area_max = min(area_vals), max(area_vals)

                def knee_score(p: dict[str, Any]) -> float:
                    acc = float(p["value_accuracy"])
                    area = float(p["value_area"])
                    d_acc = (acc_max - acc) / (acc_max - acc_min) if acc_max > acc_min else 0.0
                    d_area = (area - area_min) / (area_max - area_min) if area_max > area_min else 0.0
                    return (d_acc * d_acc + d_area * d_area) ** 0.5

                best_knee = min(valid_pareto, key=knee_score)

                def describe(p: dict[str, Any]) -> str:
                    return (
                        f"trial={p.get('trial_number')} "
                        f"mantissa_bits={p.get('mantissa_bits')} "
                        f"exponent_bits={p.get('exponent_bits')} "
                        f"accuracy={float(p['value_accuracy']):.6f} "
                        f"area_score={float(p['value_area']):.3f} "
                        f"LUTs={p.get('LUTs')} DSPs={p.get('DSPs')} "
                        f"metric={p.get('accuracy_metric')}"
                    )

                print(f"[OPTUNA-BEST-ACCURACY] {describe(best_acc)}")
                print(f"[OPTUNA-BEST-AREA] {describe(best_area)}")
                print(f"[OPTUNA-BEST-KNEE] {describe(best_knee)}")
    finally:
        if old_hls_root is None:
            os.environ.pop("VITIS_HLS_RESULTS_ROOT", None)
        else:
            os.environ["VITIS_HLS_RESULTS_ROOT"] = old_hls_root

    if not rows:
        raise RuntimeError("No variants were evaluated.")

    summary_csv = output_dir / "summary.csv"
    summary_json = output_dir / "summary.json"
    with open(summary_csv, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    summary_json.write_text(json.dumps(rows, indent=2))

    print(f"[INFO] Wrote summary: {summary_csv}")
    print(f"[INFO] Wrote summary: {summary_json}")

    if args.min_accuracy is not None:
        feasible = [
            r
            for r in rows
            if isinstance(r.get("within_rel_pct"), (int, float))
            and float(r["within_rel_pct"]) >= float(args.min_accuracy)
        ]
        feasible.sort(key=lambda r: (r["area_score"], -float(r.get("within_rel_pct", -1.0))))
        if feasible:
            best = feasible[0]
            print(
                "[BEST-UNDER-THRESHOLD] "
                f"mantissa_bits={best['mantissa_bits']} exponent_bits={best['exponent_bits']} "
                f"within={best['within_rel_pct']:.6f} area_score={best['area_score']:.3f} "
                f"LUTs={best['LUTs']} DSPs={best['DSPs']} Fmax_MHz={best['Fmax_MHz']}"
            )
        else:
            print(f"[BEST-UNDER-THRESHOLD] No variant met min accuracy threshold {args.min_accuracy:.6f}.")


if __name__ == "__main__":
    main()
