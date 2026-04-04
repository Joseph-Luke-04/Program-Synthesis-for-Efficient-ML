import argparse
import csv
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from .bitvector_sweep import (
        compute_area_score,
        parse_cocotb_metrics,
        parse_int_sweep,
        pick_optuna_accuracy_objective,
    )
    from ..run_vitis_hls import parse_reports, _resolve_xilinx_settings
except ImportError:
    from src.Experiments.bitvector_sweep import (
        compute_area_score,
        parse_cocotb_metrics,
        parse_int_sweep,
        pick_optuna_accuracy_objective,
    )
    from run_vitis_hls import parse_reports, _resolve_xilinx_settings


@dataclass(frozen=True)
class FlopocoTarget:
    key: str
    op: str
    dtype: str
    base_solution: str
    wrapper_filename: str
    top_func: str
    cocotb_module: str
    variant_env: str
    fp32: bool
    is_mul: bool


TARGETS: dict[str, FlopocoTarget] = {
    "fp32_add": FlopocoTarget(
        key="fp32_add",
        op="Addition",
        dtype="FP32",
        base_solution="solution_fp32addition_flopoco",
        wrapper_filename="fp32_sum_flopoco.vhd",
        top_func="fp32_sum_flopoco",
        cocotb_module="tests.addition.test_fp32_adder",
        variant_env="FP32_ADD_VARIANT",
        fp32=True,
        is_mul=False,
    ),
    "fp32_mul": FlopocoTarget(
        key="fp32_mul",
        op="Multiplication",
        dtype="FP32",
        base_solution="solution_fp32multiplication_flopoco",
        wrapper_filename="fp32_full_mul_flopoco.vhd",
        top_func="fp32_full_mul_flopoco",
        cocotb_module="tests.multiplication.test_fp32_multiplier",
        variant_env="FP32_MUL_VARIANT",
        fp32=True,
        is_mul=True,
    ),
}

FULL_FP32_EXP_BITS = 8
_FLOPOCO_TARGET_DEFAULT = "Zynq7000"
_FLOPOCO_FREQ_DEFAULT = 250


def parse_mant_bits(spec: str) -> list[int]:
    return parse_int_sweep(spec, "--mant-bits", min_value=2, max_value=24, default_step=1)


def _zeros(width: int) -> str:
    return '"' + ("0" * width) + '"'


def _quantise_expr(signal: str, width: int, keep_msb_bits: int) -> str:
    if keep_msb_bits >= width:
        return signal
    if keep_msb_bits <= 0:
        return "(others => '0')"
    drop = width - keep_msb_bits
    return f"{signal}({width - 1} downto {drop}) & {_zeros(drop)}"


def _run_flopoco_operators(
    flopoco_bin: str,
    flopoco_target: str,
    flopoco_freq: int,
    op_tokens: list[str],
    out_vhd: Path,
) -> None:
    """Invoke FloPoCo to generate one or more chained operators into out_vhd.
    op_tokens: flat list of operator names and key=value params,
    e.g. ['InputIEEE', 'wEIn=8', 'wFIn=23', 'wEOut=8', 'wFOut=4', 'FPAdd', 'wE=8', 'wF=4', ...]"""
    cmd = [flopoco_bin, f"target={flopoco_target}", f"frequency={flopoco_freq}", *op_tokens, f"outputFile={out_vhd}"]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"FloPoCo failed: {' '.join(cmd)}\n{proc.stdout}\n{proc.stderr}")


def _flopoco_entities_by_type(vhd_text: str) -> dict[str, list[str]]:
    """Group entity names in a FloPoCo VHDL file by operator type (InputIEEE/FPAdd/FPMult/OutputIEEE)."""
    all_names: list[str] = re.findall(r"\bentity\s+(\w+)\s+is\b", vhd_text, re.IGNORECASE)
    groups: dict[str, list[str]] = {}
    for op in ("InputIEEE", "FPAdd", "FPMult", "OutputIEEE"):
        matches = [n for n in all_names if n.lower().startswith(op.lower())]
        if matches:
            groups[op] = matches
    return groups


def _flopoco_pipeline_depth(vhd_text: str, entity_name: str) -> int:
    """Parse '-- Pipeline depth: N cycles' from the FloPoCo header block before entity_name.
    Takes the LAST match in the window — the one immediately before the entity declaration."""
    idx = vhd_text.lower().find(f"entity {entity_name.lower()} is")
    if idx == -1:
        return 0
    block = vhd_text[max(0, idx - 3000):idx]
    matches = re.findall(r"--\s*Pipeline depth:\s*(\d+)\s+cycle", block, re.IGNORECASE)
    return int(matches[-1]) if matches else 0


def _entity_has_port(vhd_text: str, entity_name: str, port_name: str) -> bool:
    """Return True if entity_name's port list contains port_name (case-insensitive)."""
    m = re.search(
        rf"entity\s+{re.escape(entity_name)}\s+is\s+.*?port\s*\((.*?)\)\s*;",
        vhd_text,
        re.IGNORECASE | re.DOTALL,
    )
    if not m:
        return False
    return re.search(rf"\b{re.escape(port_name)}\b", m.group(1), re.IGNORECASE) is not None


def _done_pipe_signals(depth: int) -> tuple[str, str, str]:
    """Return (signal_decl, process_snippet, ap_done_line) for a shift-register delay of `depth` cycles.
    Always uses at least 1 register so ap_done fires one cycle after ap_start (never combinational)."""
    depth = max(depth, 1)
    hi = depth - 1
    sig = f"    signal done_pipe : std_logic_vector({hi} downto 0) := (others => '0');"
    shift_stmt = (
        f"                done_pipe(0) <= ap_start;"
        if depth == 1
        else f"                done_pipe <= done_pipe({hi - 1} downto 0) & ap_start;"
    )
    proc = f"""\
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                done_pipe <= (others => '0');
            else
{shift_stmt}
            end if;
        end if;
    end process;"""
    return sig, proc, f"    ap_done <= done_pipe({hi});"


def render_fp32_add_chained_wrapper(
    frac_bits: int, in_entity: str, core_entity: str, out_entity: str,
    pipeline_depth: int, core_has_clk: bool,
) -> str:
    """FP32 I/O wrapper: InputIEEE(8,23→8,frac) → FPAdd(8,frac) → OutputIEEE(8,frac→8,23)."""
    fp_hi = 2 + 1 + FULL_FP32_EXP_BITS + frac_bits - 1  # (11 + frac_bits - 1) downto 0
    sig_decl, proc_snip, ap_done_line = _done_pipe_signals(pipeline_depth)
    core_clk_port = "        clk : in  std_logic;\n        " if core_has_clk else ""
    core_clk_map = "clk => ap_clk, " if core_has_clk else ""
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_sum_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        s1        : in  std_logic_vector(0 downto 0);
        e1        : in  std_logic_vector(7 downto 0);
        m1        : in  std_logic_vector(22 downto 0);
        s2        : in  std_logic_vector(0 downto 0);
        e2        : in  std_logic_vector(7 downto 0);
        m2        : in  std_logic_vector(22 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_sum_flopoco is
    -- InputIEEE(8,23→8,{frac_bits}): IEEE FP32 → FloPoCo FP, combinational
    component {in_entity} is
        port ( clk : in  std_logic;
               X : in  std_logic_vector(31 downto 0);
               R : out std_logic_vector({fp_hi} downto 0) );
    end component;
    -- FPAdd(8,{frac_bits}): reduced-precision adder, {pipeline_depth} pipeline stage(s)
    component {core_entity} is
        port ( {core_clk_port}X : in  std_logic_vector({fp_hi} downto 0);
               Y : in  std_logic_vector({fp_hi} downto 0);
               R : out std_logic_vector({fp_hi} downto 0) );
    end component;
    -- OutputIEEE(8,{frac_bits}→8,23): FloPoCo FP → IEEE FP32, combinational
    component {out_entity} is
        port ( clk : in  std_logic;
               X : in  std_logic_vector({fp_hi} downto 0);
               R : out std_logic_vector(31 downto 0) );
    end component;

    signal x_pack : std_logic_vector(31 downto 0);
    signal y_pack : std_logic_vector(31 downto 0);
    signal fp_x   : std_logic_vector({fp_hi} downto 0);
    signal fp_y   : std_logic_vector({fp_hi} downto 0);
    signal fp_r   : std_logic_vector({fp_hi} downto 0);
{sig_decl}
begin
    x_pack   <= s1(0) & e1 & m1;
    y_pack   <= s2(0) & e2 & m2;
    ap_idle  <= '1';
    ap_ready <= '1';
{ap_done_line}

{proc_snip}
    u_in_x : {in_entity}   port map (clk => ap_clk, X => x_pack, R => fp_x);
    u_in_y : {in_entity}   port map (clk => ap_clk, X => y_pack, R => fp_y);
    u_core : {core_entity} port map ({core_clk_map}X => fp_x, Y => fp_y, R => fp_r);
    u_out  : {out_entity}  port map (clk => ap_clk, X => fp_r,   R => ap_return);
end architecture;
"""


def render_fp32_mul_chained_wrapper(
    frac_bits: int, in_entity: str, core_entity: str, out_entity: str,
    pipeline_depth: int, core_has_clk: bool,
) -> str:
    """FP32 I/O wrapper: InputIEEE(8,23→8,frac) → FPMult(8,frac) → OutputIEEE(8,frac→8,23) → output_reg.
    An output register is added after OutputIEEE so that the combinational OutputIEEE path becomes
    register-to-register (clock-constrained), making Fmax directly comparable to fp32_add."""
    fp_hi = 2 + 1 + FULL_FP32_EXP_BITS + frac_bits - 1
    # +1 for the output register after OutputIEEE
    sig_decl, proc_snip, ap_done_line = _done_pipe_signals(pipeline_depth + 1)
    core_clk_port = "        clk : in  std_logic;\n        " if core_has_clk else ""
    core_clk_map = "clk => ap_clk, " if core_has_clk else ""
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_full_mul_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        a         : in  std_logic_vector(31 downto 0);
        b         : in  std_logic_vector(31 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_full_mul_flopoco is
    -- InputIEEE(8,23→8,{frac_bits}): IEEE FP32 → FloPoCo FP, combinational
    component {in_entity} is
        port ( clk : in  std_logic;
               X : in  std_logic_vector(31 downto 0);
               R : out std_logic_vector({fp_hi} downto 0) );
    end component;
    -- FPMult(8,{frac_bits}): reduced-precision multiplier, {pipeline_depth} pipeline stage(s)
    component {core_entity} is
        port ( {core_clk_port}X : in  std_logic_vector({fp_hi} downto 0);
               Y : in  std_logic_vector({fp_hi} downto 0);
               R : out std_logic_vector({fp_hi} downto 0) );
    end component;
    -- OutputIEEE(8,{frac_bits}→8,23): FloPoCo FP → IEEE FP32, combinational
    component {out_entity} is
        port ( clk : in  std_logic;
               X : in  std_logic_vector({fp_hi} downto 0);
               R : out std_logic_vector(31 downto 0) );
    end component;

    signal fp_a      : std_logic_vector({fp_hi} downto 0);
    signal fp_b      : std_logic_vector({fp_hi} downto 0);
    signal fp_r      : std_logic_vector({fp_hi} downto 0);
    signal ieee_r    : std_logic_vector(31 downto 0);
{sig_decl}
begin
    ap_idle  <= '1';
    ap_ready <= '1';
{ap_done_line}

{proc_snip}
    -- Output register: captures ieee_r so OutputIEEE is a register-to-register path (Fmax-constrained)
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                ap_return <= (others => '0');
            else
                ap_return <= ieee_r;
            end if;
        end if;
    end process;
    u_in_a : {in_entity}   port map (clk => ap_clk, X => a,    R => fp_a);
    u_in_b : {in_entity}   port map (clk => ap_clk, X => b,    R => fp_b);
    u_core : {core_entity} port map ({core_clk_map}X => fp_a, Y => fp_b, R => fp_r);
    u_out  : {out_entity}  port map (clk => ap_clk, X => fp_r, R => ieee_r);
end architecture;
"""


def render_fp32_add_wrapper(mant_bits: int) -> str:
    frac_bits = max(0, mant_bits - 1)
    e1_expr = "e1"
    e2_expr = "e2"
    m1_expr = _quantise_expr("m1", width=23, keep_msb_bits=frac_bits)
    m2_expr = _quantise_expr("m2", width=23, keep_msb_bits=frac_bits)
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_sum_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        s1        : in  std_logic_vector(0 downto 0);
        e1        : in  std_logic_vector(7 downto 0);
        m1        : in  std_logic_vector(22 downto 0);
        s2        : in  std_logic_vector(0 downto 0);
        e2        : in  std_logic_vector(7 downto 0);
        m2        : in  std_logic_vector(22 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_sum_flopoco is
    component fp32_add_flopoco is
        port (
            clk : in  std_logic;
            X   : in  std_logic_vector(31 downto 0);
            Y   : in  std_logic_vector(31 downto 0);
            R   : out std_logic_vector(31 downto 0)
        );
    end component;

    signal e1_q      : std_logic_vector(7 downto 0);
    signal e2_q      : std_logic_vector(7 downto 0);
    signal m1_q      : std_logic_vector(22 downto 0);
    signal m2_q      : std_logic_vector(22 downto 0);
    signal x_pack    : std_logic_vector(31 downto 0);
    signal y_pack    : std_logic_vector(31 downto 0);
    signal r_pack    : std_logic_vector(31 downto 0);
    signal done_pipe : std_logic_vector(7 downto 0) := (others => '0');
begin
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                done_pipe <= (others => '0');
            else
                done_pipe <= done_pipe(6 downto 0) & ap_start;
            end if;
        end if;
    end process;

    e1_q <= {e1_expr};
    e2_q <= {e2_expr};
    m1_q <= {m1_expr};
    m2_q <= {m2_expr};
    x_pack <= s1 & e1_q & m1_q;
    y_pack <= s2 & e2_q & m2_q;

    ap_done   <= done_pipe(7);
    ap_idle   <= '1';
    ap_ready  <= '1';
    ap_return <= r_pack;

    u_fp32_add_flopoco : fp32_add_flopoco
        port map (
            clk => ap_clk,
            X   => x_pack,
            Y   => y_pack,
            R   => r_pack
        );
end architecture;
"""


def render_fp32_mul_wrapper(mant_bits: int) -> str:
    frac_bits = max(0, mant_bits - 1)
    ea_expr = "ea_in"
    eb_expr = "eb_in"
    ma_expr = _quantise_expr("ma_in", width=23, keep_msb_bits=frac_bits)
    mb_expr = _quantise_expr("mb_in", width=23, keep_msb_bits=frac_bits)
    return f"""library ieee;
use ieee.std_logic_1164.all;

entity fp32_full_mul_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        a         : in  std_logic_vector(31 downto 0);
        b         : in  std_logic_vector(31 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_full_mul_flopoco is
    component fp32_fma_flopoco is
        port (
            clk      : in  std_logic;
            A        : in  std_logic_vector(31 downto 0);
            B        : in  std_logic_vector(31 downto 0);
            C        : in  std_logic_vector(31 downto 0);
            negateAB : in  std_logic;
            negateC  : in  std_logic;
            RndMode  : in  std_logic_vector(1 downto 0);
            R        : out std_logic_vector(31 downto 0)
        );
    end component;

    signal ea_in    : std_logic_vector(7 downto 0);
    signal eb_in    : std_logic_vector(7 downto 0);
    signal ma_in    : std_logic_vector(22 downto 0);
    signal mb_in    : std_logic_vector(22 downto 0);
    signal ea_q     : std_logic_vector(7 downto 0);
    signal eb_q     : std_logic_vector(7 downto 0);
    signal ma_q     : std_logic_vector(22 downto 0);
    signal mb_q     : std_logic_vector(22 downto 0);
    signal a_q      : std_logic_vector(31 downto 0);
    signal b_q      : std_logic_vector(31 downto 0);
    signal donepipe : std_logic_vector(4 downto 0) := (others => '0');
begin
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                donepipe <= (others => '0');
            else
                donepipe <= donepipe(3 downto 0) & ap_start;
            end if;
        end if;
    end process;

    ea_in <= a(30 downto 23);
    eb_in <= b(30 downto 23);
    ma_in <= a(22 downto 0);
    mb_in <= b(22 downto 0);
    ea_q <= {ea_expr};
    eb_q <= {eb_expr};
    ma_q <= {ma_expr};
    mb_q <= {mb_expr};
    a_q <= a(31) & ea_q & ma_q;
    b_q <= b(31) & eb_q & mb_q;

    ap_done  <= donepipe(4);
    ap_idle  <= '1';
    ap_ready <= '1';

    u_fp32_fma_flopoco : fp32_fma_flopoco
        port map (
            clk      => ap_clk,
            A        => a_q,
            B        => b_q,
            C        => (others => '0'),
            negateAB => '0',
            negateC  => '0',
            RndMode  => "00",
            R        => ap_return
        );
end architecture;
"""


def render_wrapper(target: FlopocoTarget, mant_bits: int) -> str:
    if target.key == "fp32_add":
        return render_fp32_add_wrapper(mant_bits)
    if target.key == "fp32_mul":
        return render_fp32_mul_wrapper(mant_bits)
    raise ValueError(f"Unsupported target: {target.key}")


def create_vivado_tcl_for_rtl(top_func: str, output_dir: Path) -> Path:
    tcl_path = output_dir / "vivado.tcl"
    rtl_dir = output_dir / "verilog_out"
    clk_period_ns = float(os.environ.get("VIVADO_CLK_PERIOD_NS", "5.000"))
    tcl = f"""
    set vhdl_files [concat [glob -nocomplain {{{rtl_dir}/*.vhd}}] [glob -nocomplain {{{rtl_dir}/*.vhdl}}]]
    set v_files    [glob -nocomplain {{{rtl_dir}/*.v}}]
    set sv_files   [glob -nocomplain {{{rtl_dir}/*.sv}}]

    if {{[llength $vhdl_files] == 0 && [llength $v_files] == 0 && [llength $sv_files] == 0}} {{
      puts "ERROR: No RTL sources found in {rtl_dir}"
      exit 1
    }}

    if {{[llength $vhdl_files] > 0}} {{ foreach f $vhdl_files {{ read_vhdl $f }} }}
    if {{[llength $v_files] > 0}}    {{ read_verilog $v_files }}
    foreach f $sv_files {{ read_verilog -sv $f }}

    synth_design -top {top_func} -part xc7z020clg400-1
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      create_clock -name ap_clk -period {clk_period_ns:.3f} [get_ports ap_clk]
    }}
    opt_design
    place_design
    route_design
    report_utilization    -file {output_dir}/utilization.rpt
    report_timing_summary -file {output_dir}/timing.rpt
    if {{[llength [get_ports -quiet ap_clk]]}} {{
      report_timing -delay_type max -max_paths 1 -nworst 1 -file {output_dir}/timing_detail.rpt
    }}
    """
    tcl_path.write_text(tcl.strip() + "\n")
    return tcl_path


def run_vivado_rtl_impl(output_dir: Path, top_func: str, impl: bool) -> dict[str, Any]:
    if impl:
        tcl_path = create_vivado_tcl_for_rtl(top_func, output_dir)
        vivado_settings = _resolve_xilinx_settings("Vivado")
        cmd = f"source {vivado_settings} && cd {output_dir} && vivado -mode batch -source {tcl_path} > vivado.log 2>&1"
        proc = subprocess.run(["bash", "-lc", cmd], capture_output=True, text=True)
        if proc.returncode != 0:
            print(f"[WARN] Vivado impl failed for {output_dir.name}. Check {output_dir / 'vivado.log'}")
    return parse_reports(output_dir, top_func, output_dir.name, run_impl=impl)


def stage_variant(
    target: FlopocoTarget,
    base_rtl_dir: Path,
    variants_root: Path,
    variant_soln: str,
    wrapper_text: str,
) -> tuple[Path, Path]:
    variant_dir = variants_root / variant_soln
    rtl_out = variant_dir / "verilog_out"
    if variant_dir.exists():
        shutil.rmtree(variant_dir)
    rtl_out.mkdir(parents=True, exist_ok=True)

    copied = 0
    for ext in ("*.vhd", "*.vhdl", "*.v", "*.sv"):
        for src in base_rtl_dir.glob(ext):
            shutil.copy2(src, rtl_out / src.name)
            copied += 1
    if copied == 0:
        raise FileNotFoundError(f"No RTL files found in base dir: {base_rtl_dir}")

    wrapper_path = rtl_out / target.wrapper_filename
    wrapper_with_header = f"-- AUTO-GENERATED FLOPOCO WRAPPER variant={variant_soln}\n" + wrapper_text
    wrapper_path.write_text(wrapper_with_header)
    return variant_dir, wrapper_path


def generate_flopoco_variant(
    target: FlopocoTarget,
    mant_bits: int,
    variant_dir: Path,
    flopoco_bin: str,
    flopoco_target: str,
    flopoco_freq: int,
    correctly_rounded: bool,
) -> tuple[Path, Path]:
    """Generate a reduced-precision FloPoCo variant with FP32 I/O:
    InputIEEE(8,23→8,k) → FPAdd|FPMult(8,k) → OutputIEEE(8,k→8,23)
    where k = max(1, mant_bits - 1) is the FloPoCo fraction width (wF)."""
    rtl_out = variant_dir / "verilog_out"
    if variant_dir.exists():
        shutil.rmtree(variant_dir)
    rtl_out.mkdir(parents=True, exist_ok=True)

    frac_bits = max(1, mant_bits - 1)
    core_op = "FPMult" if target.is_mul else "FPAdd"

    if target.is_mul:
        cr = "1" if correctly_rounded else "0"
        op_tokens = [
            "InputIEEE",  f"wEIn=8", f"wFIn=23", f"wEOut=8", f"wFOut={frac_bits}",
            "FPMult",     f"wE=8",   f"wF={frac_bits}", f"correctlyRounded={cr}",
            "OutputIEEE", f"wEIn=8", f"wFIn={frac_bits}", f"wEOut=8", f"wFOut=23",
        ]
    else:
        op_tokens = [
            "InputIEEE",  f"wEIn=8", f"wFIn=23", f"wEOut=8", f"wFOut={frac_bits}",
            "FPAdd",      f"wE=8",   f"wF={frac_bits}",
            "OutputIEEE", f"wEIn=8", f"wFIn={frac_bits}", f"wEOut=8", f"wFOut=23",
        ]

    core_vhd = rtl_out / f"flopoco_core_wF{frac_bits}.vhd"
    _run_flopoco_operators(flopoco_bin, flopoco_target, flopoco_freq, op_tokens, core_vhd)

    vhd_text = core_vhd.read_text()
    groups = _flopoco_entities_by_type(vhd_text)
    missing = [k for k in ("InputIEEE", core_op, "OutputIEEE") if k not in groups]
    if missing:
        raise RuntimeError(
            f"FloPoCo VHDL missing operator types {missing}. Found: {list(groups.keys())} in {core_vhd}"
        )

    in_entity   = groups["InputIEEE"][-1]
    core_entity = groups[core_op][-1]
    out_entity  = groups["OutputIEEE"][-1]
    depth_in   = _flopoco_pipeline_depth(vhd_text, in_entity)
    depth_core = _flopoco_pipeline_depth(vhd_text, core_entity)
    depth_out  = _flopoco_pipeline_depth(vhd_text, out_entity)
    depth      = depth_in + depth_core + depth_out
    core_has_clk = _entity_has_port(vhd_text, core_entity, "clk")
    print(
        f"[FLOPOCO] wF={frac_bits} entities: {in_entity}(d={depth_in}) → "
        f"{core_entity}(d={depth_core}, clk={core_has_clk}) → {out_entity}(d={depth_out})"
    )

    if target.is_mul:
        wrapper_text = render_fp32_mul_chained_wrapper(
            frac_bits, in_entity, core_entity, out_entity, depth, core_has_clk
        )
    else:
        wrapper_text = render_fp32_add_chained_wrapper(
            frac_bits, in_entity, core_entity, out_entity, depth, core_has_clk
        )

    wrapper_path = rtl_out / target.wrapper_filename
    wrapper_path.write_text(
        f"-- AUTO-GENERATED: reduced-precision FloPoCo wF={frac_bits} "
        f"({in_entity} → {core_entity} → {out_entity}, depth={depth})\n"
        + wrapper_text
    )
    meta = {
        "fraction_bits": frac_bits,
        "input_entity": in_entity,
        "core_entity": core_entity,
        "output_entity": out_entity,
        "pipeline_depth_total": depth,
    }
    return variant_dir, wrapper_path, meta


def run_cocotb_accuracy(
    repo_root: Path,
    rtl_root: Path,
    variant_soln: str,
    target: FlopocoTarget,
    timeout_seconds: int,
    log_path: Path,
    rel_error_pct: float,
    cocotb_mode: str,
    dump_samples_path: Path | None = None,
) -> dict[str, Any]:
    acc_root = repo_root / "accuracy_tests"
    rtl_dir = (rtl_root / variant_soln / "verilog_out").resolve()
    wrapper_path = rtl_dir / target.wrapper_filename
    if not rtl_dir.exists():
        raise FileNotFoundError(f"Variant RTL dir not found for cocotb: {rtl_dir}")
    if not wrapper_path.exists():
        raise FileNotFoundError(f"Variant wrapper VHDL not found for cocotb: {wrapper_path}")

    env = os.environ.copy()
    # Ensure the venv's bin/ is on PATH so cocotb-config is found by make
    py_bin = str(Path(sys.executable).parent.resolve())
    env["PATH"] = py_bin + os.pathsep + env.get("PATH", "")
    env["PYTHON"] = sys.executable
    env["SIM"] = "ghdl"
    env["TOPLEVEL_LANG"] = "vhdl"
    env["GHDL_ARGS"] = "-fsynopsys -fexplicit"
    env["GHDL_ELABORATE_ARGS"] = "-fsynopsys -fexplicit"
    env[target.variant_env] = "flopoco"
    env["COCOTB_RESULTS_FILE"] = str((log_path.parent / f"{variant_soln}_results.xml").resolve())

    if target.is_mul:
        env["FP32_MUL_REL_ERR_PCT"] = f"{rel_error_pct}"
        env["FP32_MUL_MODE"] = cocotb_mode
        if dump_samples_path is not None:
            env["FP32_MUL_DUMP_PATH"] = str(dump_samples_path.resolve())
    else:
        env["FP32_ADD_REL_ERR_PCT"] = f"{rel_error_pct}"
        env["FP32_ADD_MODE"] = cocotb_mode
        if dump_samples_path is not None:
            env["FP32_ADD_DUMP_PATH"] = str(dump_samples_path.resolve())

    cmd = [
        "make",
        f"HLS_BASE={rtl_root}",
        f"HLS_SOLN={variant_soln}",
        f"TOPLEVEL={target.top_func}",
        f"MODULE={target.cocotb_module}",
        f"SIM_BUILD={(acc_root / 'sim_build' / f'{target.top_func}_{variant_soln}_{hashlib.md5(str(rtl_root.resolve()).encode()).hexdigest()[:8]}').resolve()}",
        "TOPLEVEL_LANG=vhdl",
    ]

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


def run_one_target(args: argparse.Namespace, target: FlopocoTarget) -> None:
    src_dir = Path(__file__).resolve().parent
    repo_root = src_dir.parent.parent
    base_rtl_dir = (
        Path(args.base_rtl).resolve()
        if args.base_rtl
        else (repo_root / "results" / "FLOPOCO" / target.base_solution / "verilog_out").resolve()
    )
    flopoco_bin = getattr(args, "flopoco_bin", "")
    if flopoco_bin and not Path(flopoco_bin).exists() and shutil.which(flopoco_bin) is None:
        raise FileNotFoundError(f"FloPoCo binary not found: {flopoco_bin}")
    if not flopoco_bin and not base_rtl_dir.exists():
        raise FileNotFoundError(f"Base FLOPOCO RTL dir not found: {base_rtl_dir}")

    mode_tag = re.sub(r"[^a-zA-Z0-9_.-]+", "_", str(args.cocotb_mode).strip().lower())
    out_root = (
        Path(args.output_dir).resolve()
        if args.output_dir
        else (repo_root / "results" / "sweeps" / f"flopoco_bitvector_{target.key}").resolve()
    )
    # Each mode gets its own subdir so parallel runs never collide and results
    # are always written to the same canonical location regardless of run order.
    if mode_tag:
        out_root = out_root / mode_tag
    variants_root = out_root / "rtl_variants"
    logs_dir = out_root / "accuracy_logs"
    error_samples_dir = out_root / "error_samples"
    variants_root.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)
    error_samples_dir.mkdir(parents=True, exist_ok=True)

    mant_spec = args.mant_bits if args.mant_bits else "24:2:1"
    mant_bits_list = parse_mant_bits(mant_spec)
    candidates = mant_bits_list

    print(f"[INFO] Target: {target.key} ({target.dtype} {target.op})")
    if flopoco_bin:
        print(f"[INFO] FloPoCo binary: {flopoco_bin}")
        print(f"[INFO] FloPoCo target: {args.flopoco_target} @ {args.flopoco_freq} MHz")
    else:
        print(f"[INFO] Base RTL: {base_rtl_dir}")
    if args.exp_bits:
        print("[INFO] Ignoring --exp-bits in mantissa-only mode.")
    pair_labels = ", ".join(f"{m}x{m}" for m in candidates)
    print(f"[INFO] Candidate mantissa pairs: {pair_labels}")
    print(f"[INFO] Search mode: {args.search}")
    if args.search == "optuna" and not args.impl:
        raise ValueError("Optuna multi-objective requires area metrics; use --impl.")

    rows: list[dict[str, Any]] = []

    def evaluate_candidate(mant_bits: int, eval_label: str = "") -> dict[str, Any]:
        gen_mode = "regen" if flopoco_bin else "wrap"
        cr_tag = "_cr" if (flopoco_bin and target.is_mul and getattr(args, "correctly_rounded", False)) else ""
        variant_soln = f"{target.base_solution}_{gen_mode}_m{mant_bits}{cr_tag}"
        flopoco_meta: dict[str, Any] = {}
        if flopoco_bin:
            variant_dir, wrapper_path, flopoco_meta = generate_flopoco_variant(
                target=target,
                mant_bits=mant_bits,
                variant_dir=variants_root / variant_soln,
                flopoco_bin=flopoco_bin,
                flopoco_target=args.flopoco_target,
                flopoco_freq=args.flopoco_freq,
                correctly_rounded=getattr(args, "correctly_rounded", False),
            )
        else:
            wrapper_text = render_wrapper(target, mant_bits)
            variant_dir, wrapper_path = stage_variant(
                target=target,
                base_rtl_dir=base_rtl_dir,
                variants_root=variants_root,
                variant_soln=variant_soln,
                wrapper_text=wrapper_text,
            )
        prefix = "[EVAL]" if not eval_label else f"[EVAL:{eval_label}]"
        variant_rtl_dir = variant_dir / "verilog_out"
        print(
            f"{prefix} mantissa_bits={mant_bits} "
            f"rtl_dir={variant_rtl_dir} wrapper={wrapper_path}"
        )

        hw = run_vivado_rtl_impl(variant_dir, top_func=target.top_func, impl=args.impl)
        cocotb_log = logs_dir / f"{variant_soln}_{mode_tag}.log"
        sample_dump = error_samples_dir / f"{variant_soln}_{mode_tag}.npz"
        acc = run_cocotb_accuracy(
            repo_root=repo_root,
            rtl_root=variants_root,
            variant_soln=variant_soln,
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
            f"ulp_p99={acc.get('ulp_p99', -1)} pass={acc.get('cocotb_passed')} "
            f"log={cocotb_log}"
        )

        row: dict[str, Any] = {
            "search_mode": args.search,
            "generation_mode": "regen_core" if flopoco_bin else "wrapper_trunc",
            "correctly_rounded": bool(getattr(args, "correctly_rounded", False)) if (flopoco_bin and target.is_mul) else None,
            "flopoco_target_device": args.flopoco_target if flopoco_bin else "",
            "flopoco_target_freq_mhz": args.flopoco_freq if flopoco_bin else "",
            "target": target.key,
            "op": target.op,
            "dtype": target.dtype,
            "variant_solution": variant_soln,
            "variant_wrapper_vhdl": str(wrapper_path),
            "mantissa_bits": mant_bits,
            "fraction_bits": flopoco_meta.get("fraction_bits", mant_bits - 1),
            "exponent_bits": FULL_FP32_EXP_BITS,
            "pipeline_depth_total": flopoco_meta.get("pipeline_depth_total", ""),
            "input_entity": flopoco_meta.get("input_entity", ""),
            "core_entity": flopoco_meta.get("core_entity", ""),
            "output_entity": flopoco_meta.get("output_entity", ""),
            "accuracy_source": acc.get("accuracy_source"),
            "cocotb_mode": args.cocotb_mode,
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
            "Latency_ns": hw.get("Latency_ns", -1),
        }
        row["area_score"] = compute_area_score(
            row,
            args.area_lut_weight,
            args.area_ff_weight,
            args.area_dsp_weight,
            args.area_bram_weight,
        )
        _luts = row.get("LUTs", -1)
        _lat  = row.get("Latency_ns", -1)
        row["adp_lut_ns"] = round(_luts * _lat, 3) if _luts > 0 and _lat > 0 else -1
        print(
            f"[AREA] LUTs={row['LUTs']} FFs={row['FFs']} DSPs={row['DSPs']} BRAMs={row['BRAMs']} "
            f"area_score={row['area_score']:.3f}"
        )
        print(f"[PERF] Cycles={row['Cycles']} Fmax_MHz={row['Fmax_MHz']} Latency_ns={row['Latency_ns']} "
              f"ADP={row['adp_lut_ns']}")
        rows.append(row)
        return row

    if args.search == "sweep":
        for m in candidates:
            evaluate_candidate(m)
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
            # accuracy max, area min, cycles min, Fmax max
            directions=["maximize", "minimize", "minimize", "maximize"],
            sampler=sampler,
            study_name=args.optuna_study_name,
            storage=args.optuna_storage if args.optuna_storage else None,
            load_if_exists=True,
        )
        labels = [str(m) for m in candidates]
        cache: dict[int, dict[str, Any]] = {}

        def objective(trial):
            label = str(trial.suggest_categorical("mantissa_bits", labels))
            m = int(label)
            key = m
            row = cache.get(key)
            if row is None:
                row = evaluate_candidate(m, eval_label=f"trial-{trial.number}")
                cache[key] = row

            acc, acc_metric = pick_optuna_accuracy_objective(row, target)
            area = row["area_score"]
            cycles = row.get("Cycles", -1)
            fmax = row.get("Fmax_MHz", -1)
            cycles_obj = float(cycles) if isinstance(cycles, (int, float)) and float(cycles) >= 0 else 1e15
            fmax_obj = float(fmax) if isinstance(fmax, (int, float)) and float(fmax) > 0 else -1e15

            trial.set_user_attr("variant_solution", row["variant_solution"])
            trial.set_user_attr("mantissa_bits", row["mantissa_bits"])
            trial.set_user_attr("exponent_bits", row["exponent_bits"])
            trial.set_user_attr("LUTs", row["LUTs"])
            trial.set_user_attr("DSPs", row["DSPs"])
            trial.set_user_attr("Cycles", row["Cycles"])
            trial.set_user_attr("Fmax_MHz", row["Fmax_MHz"])
            trial.set_user_attr("accuracy_metric", acc_metric)
            return float(acc), float(area), float(cycles_obj), float(fmax_obj)

        study.optimize(objective, n_trials=max(1, int(args.optuna_trials)))

    if not rows:
        raise RuntimeError("No variants were evaluated.")

    summary_csv = out_root / "summary.csv"
    summary_json = out_root / "summary.json"
    write_header = not summary_csv.exists() or summary_csv.stat().st_size == 0
    with open(summary_csv, "a", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        if write_header:
            writer.writeheader()
        writer.writerows(rows)
    # json: accumulate all rows from csv for a complete snapshot
    all_rows = list(csv.DictReader(open(summary_csv, newline="")))
    summary_json.write_text(json.dumps(all_rows, indent=2))
    print(f"[INFO] Wrote summary: {summary_csv}")
    print(f"[INFO] Wrote summary: {summary_json}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Mantissa sweep/Optuna search for FLOPOCO FP32 add/mul. "
            "Two modes: (1) wrapper-level input truncation against a pre-built full-precision core "
            "(default, requires base RTL); (2) reduced-precision core regeneration via "
            "InputIEEE(8,23→8,k) → FPAdd/FPMult(8,k) → OutputIEEE(8,k→8,23) "
            "(requires --flopoco-bin). Exponent fixed at 8 throughout."
        )
    )
    parser.add_argument("--target", choices=list(TARGETS.keys()), required=False)
    parser.add_argument("--all-targets", action="store_true", help="Run both fp32_add and fp32_mul.")
    parser.add_argument("--base-rtl", default="", help="Optional explicit base FLOPOCO verilog_out dir.")
    parser.add_argument("--mant-bits", default="", help="Mantissa bit candidates: N or START:STOP[:STEP].")
    parser.add_argument(
        "--exp-bits",
        default="",
        help="Deprecated for FP32 mantissa-only mode; ignored (exponent fixed at 8).",
    )
    parser.add_argument("--cocotb-timeout", type=int, default=0, help="Per-variant cocotb timeout seconds.")
    parser.add_argument("--rel-error-pct", type=float, default=5.0, help="FP32 mul relative-error threshold (%%).")
    parser.add_argument(
        "--cocotb-mode",
        default="bits",
        choices=["bits", "normal_full", "wide", "small"],
        help="FP32 multiplier operand sampler mode in cocotb tests.",
    )
    parser.add_argument(
        "--impl",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Run Vivado implementation per variant (default: enabled).",
    )
    parser.add_argument("--search", default="sweep", choices=["sweep", "optuna"], help="Exhaustive sweep or Optuna.")
    parser.add_argument("--optuna-trials", type=int, default=24, help="Number of Optuna trials.")
    parser.add_argument("--optuna-sampler", default="nsga2", choices=["nsga2", "tpe", "random"], help="Optuna sampler.")
    parser.add_argument("--optuna-seed", type=int, default=7, help="Seed for Optuna sampler.")
    parser.add_argument("--optuna-study-name", default="flopoco_bitvector_multiobj", help="Optuna study name.")
    parser.add_argument("--optuna-storage", default="", help="Optional Optuna storage URL.")
    parser.add_argument("--area-lut-weight", type=float, default=1.0, help="Area objective LUT weight.")
    parser.add_argument("--area-ff-weight", type=float, default=0.1, help="Area objective FF weight.")
    parser.add_argument("--area-dsp-weight", type=float, default=200.0, help="Area objective DSP weight.")
    parser.add_argument("--area-bram-weight", type=float, default=1000.0, help="Area objective BRAM weight.")
    parser.add_argument("--output-dir", default="", help="Output directory root for this run.")
    parser.add_argument(
        "--flopoco-bin",
        default="",
        help=(
            "Path to flopoco binary. When set, generates a genuinely reduced-precision core via "
            "InputIEEE(8,23→8,k) → FPAdd/FPMult(8,k) → OutputIEEE(8,k→8,23) "
            "where k=mant_bits-1, instead of wrapper-level input masking."
        ),
    )
    parser.add_argument(
        "--flopoco-target", default=_FLOPOCO_TARGET_DEFAULT,
        help="FloPoCo target device (default: %(default)s).",
    )
    parser.add_argument(
        "--flopoco-freq", type=int, default=_FLOPOCO_FREQ_DEFAULT,
        help="FloPoCo target frequency in MHz (default: %(default)s).",
    )
    parser.add_argument(
        "--correctly-rounded", action="store_true", default=False,
        help="Use correctlyRounded=1 for FPMult (only with --flopoco-bin; default: faithful rounding).",
    )
    args = parser.parse_args()

    if not args.all_targets and not args.target:
        parser.error("Either --target or --all-targets must be provided.")
    if args.all_targets and args.base_rtl:
        parser.error("--base-rtl is only supported with a single --target run.")

    if args.all_targets:
        repo_root = Path(__file__).resolve().parent.parent.parent
        combined_rows: list[dict[str, Any]] = []
        for key in ("fp32_add", "fp32_mul"):
            cmd = [sys.executable, "-m", "src.Experiments.flopoco_bitvector_sweep", "--target", key]
            if args.mant_bits:
                cmd += ["--mant-bits", str(args.mant_bits)]
            if args.cocotb_timeout:
                cmd += ["--cocotb-timeout", str(args.cocotb_timeout)]
            cmd += ["--cocotb-mode", str(args.cocotb_mode)]
            if key == "fp32_mul":
                cmd += ["--rel-error-pct", str(args.rel_error_pct)]
            cmd += ["--search", str(args.search)]
            cmd += ["--optuna-trials", str(args.optuna_trials)]
            cmd += ["--optuna-sampler", str(args.optuna_sampler)]
            cmd += ["--optuna-seed", str(args.optuna_seed)]
            cmd += ["--optuna-study-name", f"{args.optuna_study_name}_{key}"]
            if args.optuna_storage:
                storage = str(args.optuna_storage)
                if storage.startswith("sqlite:///"):
                    storage = storage[:-3] + f"_{key}.db"
                cmd += ["--optuna-storage", storage]
            cmd += ["--impl" if args.impl else "--no-impl"]
            if args.flopoco_bin:
                cmd += [
                    "--flopoco-bin", args.flopoco_bin,
                    "--flopoco-target", args.flopoco_target,
                    "--flopoco-freq", str(args.flopoco_freq),
                ]
            if args.correctly_rounded:
                cmd += ["--correctly-rounded"]
            cmd += ["--area-lut-weight", str(args.area_lut_weight)]
            cmd += ["--area-ff-weight", str(args.area_ff_weight)]
            cmd += ["--area-dsp-weight", str(args.area_dsp_weight)]
            cmd += ["--area-bram-weight", str(args.area_bram_weight)]
            child_out = Path(args.output_dir).resolve() / key if args.output_dir else (
                repo_root / "results" / "sweeps" / f"flopoco_bitvector_{key}"
            )
            cmd += ["--output-dir", str(child_out)]

            print(f"[ALL-TARGETS] Running: {' '.join(cmd)}")
            proc = subprocess.run(cmd, cwd=repo_root)
            if proc.returncode != 0:
                raise RuntimeError(f"--all-targets failed for {key} (rc={proc.returncode}).")

            summary_csv = child_out / "summary.csv"
            if summary_csv.exists():
                with open(summary_csv, newline="") as f:
                    for row in csv.DictReader(f):
                        row["run_target"] = key
                        combined_rows.append(row)

        out_root = Path(args.output_dir).resolve() if args.output_dir else (
            repo_root / "results" / "sweeps" / "flopoco_bitvector_all"
        )
        out_root.mkdir(parents=True, exist_ok=True)
        if combined_rows:
            combined_csv = out_root / "summary_all_targets.csv"
            combined_json = out_root / "summary_all_targets.json"
            with open(combined_csv, "w", newline="") as f:
                writer = csv.DictWriter(f, fieldnames=list(combined_rows[0].keys()))
                writer.writeheader()
                writer.writerows(combined_rows)
            combined_json.write_text(json.dumps(combined_rows, indent=2))
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_csv}")
            print(f"[ALL-TARGETS] Wrote combined summary: {combined_json}")
        return

    run_one_target(args, TARGETS[args.target])


if __name__ == "__main__":
    main()
