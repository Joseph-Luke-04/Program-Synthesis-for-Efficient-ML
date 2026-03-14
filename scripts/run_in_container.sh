#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image_tag="${IMAGE_TAG:-prog-synth:latest}"
engine="${CONTAINER_ENGINE:-}"
xilinx_root="${XILINX_ROOT:-/home/tools/Xilinx}"
host_cvc5_bin="${HOST_CVC5_BIN:-}"

if [[ -z "$engine" ]]; then
  if command -v podman >/dev/null 2>&1; then
    engine="podman"
  elif command -v docker >/dev/null 2>&1; then
    engine="docker"
  else
    echo "Neither podman nor docker is available on PATH." >&2
    exit 1
  fi
fi

if [[ -z "$host_cvc5_bin" ]] && command -v cvc5 >/dev/null 2>&1; then
  host_cvc5_bin="$(command -v cvc5)"
fi

if ! "$engine" image exists "$image_tag" >/dev/null 2>&1; then
  echo "Container image '$image_tag' does not exist locally. Build it first." >&2
  exit 1
fi

runtime_args=(--rm -it -w /workspace --entrypoint /usr/local/bin/container-entrypoint.sh)
if [[ "$engine" == "podman" ]]; then
  runtime_args+=(--userns keep-id)
else
  runtime_args+=(--user "$(id -u):$(id -g)")
fi

runtime_args+=(
  -e HOME=/tmp
  -e VITIS_SETTINGS_SH="${VITIS_SETTINGS_SH:-/home/tools/Xilinx/2025.1/2025.1/Vitis/settings64.sh}"
  -e VIVADO_SETTINGS_SH="${VIVADO_SETTINGS_SH:-/home/tools/Xilinx/2025.1/2025.1/Vivado/settings64.sh}"
  -e VITIS_HLS_RESULTS_ROOT="${VITIS_HLS_RESULTS_ROOT:-/workspace/results/HLS}"
  -v "${repo_root}:/workspace"
)

if [[ -d "$xilinx_root" ]]; then
  runtime_args+=(-v "${xilinx_root}:${xilinx_root}:ro")
fi

if [[ -n "$host_cvc5_bin" ]]; then
  host_cvc5_dir="$(dirname "$host_cvc5_bin")"
  runtime_args+=(
    -e HOST_CVC5_DIR="$host_cvc5_dir"
    -v "${host_cvc5_dir}:${host_cvc5_dir}:ro"
  )
fi

if [[ $# -eq 0 ]]; then
  set -- bash
fi

exec "$engine" run "${runtime_args[@]}" "$image_tag" "$@"
