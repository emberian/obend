#!/usr/bin/env bash
# Rung 5 groundwork: generate FABulous's standard demo fabric and take one user design through its
# own flow (Yosys synth_fabulous, nextpnr-generic, bit_gen) to a bitstream. Pinned to the commit
# below; the Lean model of the fabric (Obend.Hardware.Fabulous) and verify_fabric.sh are not here yet.
#   hardware/fabulous/flow.sh [DESIGN.v] [WORKDIR]
set -euo pipefail
FAB_COMMIT=ba85d81            # FABulous v2.2.0-57 (CLI 2.2.1), github.com/FPGA-Research/FABulous
FAB_HOME="${FAB_HOME:-/Users/ember/tools/FABulous}"
OSS="${OSS_CAD_SUITE:-/Users/ember/tools/oss-cad-suite/bin}"
WORK="${2:-${TMPDIR:-/tmp}/obend-fabulous}"
export PATH="${FAB_HOME}/.venv/bin:${OSS}:${PATH}"

have="$(git -C "${FAB_HOME}" rev-parse --short=7 HEAD)"
[[ "${have}" == "${FAB_COMMIT}" ]] || { echo "[FAIL] ${FAB_HOME} is at ${have}, expected ${FAB_COMMIT}" >&2; exit 2; }

mkdir -p "${WORK}"
if [[ ! -d "${WORK}/demo" ]]; then
  (cd "${WORK}" && FABulous create-project demo >/dev/null)
fi
DESIGN="${1:-${WORK}/demo/user_design/sequential_16bit_en.v}"
[[ "$(dirname "${DESIGN}")" -ef "${WORK}/demo/user_design" ]] || cp "${DESIGN}" "${WORK}/demo/user_design/"
base="$(basename "${DESIGN}")"
FABulous -p "${WORK}/demo" run "run_fab; compile_design user_design/${base}"
ls -la "${WORK}/demo/user_design/${base%.v}.bin" "${WORK}/demo/.FABulous/bitStreamSpec.csv"
