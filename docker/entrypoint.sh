#!/usr/bin/env bash
set -euo pipefail

export PYTHONUNBUFFERED="${PYTHONUNBUFFERED:-1}"
export MPLBACKEND="${MPLBACKEND:-Agg}"
export PYTHONPATH="/workspace${PYTHONPATH:+:$PYTHONPATH}"
export SMT2C_BIN="${SMT2C_BIN:-/opt/smt2c/src/smt2c}"

if [[ -z "${VITIS_SETTINGS_SH:-}" ]]; then
  for candidate in \
    /home/tools/Xilinx/2025.1/2025.1/Vitis/settings64.sh \
    /home/tools/Xilinx/2025.1/Vitis/settings64.sh \
    /tools/Xilinx/2025.1/Vitis/settings64.sh
  do
    if [[ -f "$candidate" ]]; then
      export VITIS_SETTINGS_SH="$candidate"
      break
    fi
  done
fi

if [[ -z "${VIVADO_SETTINGS_SH:-}" ]]; then
  for candidate in \
    /home/tools/Xilinx/2025.1/2025.1/Vivado/settings64.sh \
    /home/tools/Xilinx/2025.1/Vivado/settings64.sh \
    /tools/Xilinx/2025.1/Vivado/settings64.sh
  do
    if [[ -f "$candidate" ]]; then
      export VIVADO_SETTINGS_SH="$candidate"
      break
    fi
  done
fi

exec "$@"
