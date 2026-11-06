#!/usr/bin/env bash
# Build iceStickMac8 (hardware/ice40/obend_ice40_mac8.sv) on the fabric of hardware/fabulous/fabric.csv
# with FABulous's own flow: `run_fab` generates the fabric and its metadata (.FABulous/), and
# `compile_design` runs Yosys synth_fabulous, nextpnr-generic and bit_gen. The pin map is
# top_wrapper.v (`obend fabric wrapper`). Pinned to the FABulous commit below.
#   hardware/fabulous/flow.sh [WORKDIR]     -> WORKDIR/mac8/user_design/obend_ice40_mac8.bin
set -euo pipefail
FAB_COMMIT=ba85d81            # FABulous v2.2.0-57 (CLI 2.2.1), github.com/FPGA-Research/FABulous
FAB_HOME="${FAB_HOME:-/Users/ember/tools/FABulous}"
OSS="${OSS_CAD_SUITE:-/Users/ember/tools/oss-cad-suite/bin}"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../.." && pwd)"
WORK="${1:-$(mktemp -d "${TMPDIR:-/tmp}/obend-fabulous.XXXXXX")}"
export PATH="${FAB_HOME}/.venv/bin:${OSS}:${PATH}"

have="$(git -C "${FAB_HOME}" rev-parse --short=7 HEAD)"
[[ "${have}" == "${FAB_COMMIT}" ]] || { echo "[FAIL] ${FAB_HOME} is at ${have}, expected ${FAB_COMMIT}" >&2; exit 2; }

P="${WORK}/mac8"
rm -rf "${P}"
mkdir -p "${WORK}"
(cd "${WORK}" && FABulous create-project mac8 >/dev/null)
cp "${HERE}/fabric.csv" "${P}/fabric.csv"
cp "${HERE}/top_wrapper.v" "${P}/user_design/top_wrapper.v"
cp "${ROOT}/hardware/ice40/obend_ice40_mac8.sv" "${P}/user_design/"
FABulous -p "${P}" run "run_fab; compile_design user_design/obend_ice40_mac8.sv" > "${WORK}/flow.log" 2>&1 \
  || { tail -30 "${WORK}/flow.log" >&2; echo "[FAIL] FABulous flow" >&2; exit 1; }
grep -A3 "Device utilisation" "${P}/user_design/obend_ice40_mac8_npnr_log.txt" | sed -n 2,3p
echo "${P}/user_design/obend_ice40_mac8.bin"
