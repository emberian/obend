#!/usr/bin/env bash
# apps/fidget-cam/verilator/verify_fidget_cam.sh
#
# 1. the committed .sv is byte-identical to what `obend-emit-sv fidget` writes from the Lean
#    definition (`fidgetImpellerVoxelCamRtlModule`); hand edits fail here;
# 2. LEC: Yosys's reading of the .sv against Lean's model of the same RtlModule
#    (`hardware/lec/lec.sh`, `fidget_impeller_voxel_cam_lec.smt2` from `obend-emit-sv fidget --lec`);
#    a planted one-bit mutation must be caught with a counterexample;
# 3. `obend check` / `obend run` on the four-module package;
# 4. the posted program is written by Lean (`obend-emit-sv fidget-ngc`, `impeller5AxisNgc`);
# 5. Verilator builds the emitted RTL and the harness scans the part, writes the STL, and re-checks
#    the program's waypoints on the hardware (`fidget_voxel_tb.cpp`).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
APP_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${APP_DIR}/../.." && pwd)"
OBEND_BIN="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
EMIT_SV="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR_BIN="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
TMP="${TMPDIR:-/tmp}"

if [[ ! -x "${EMIT_SV}" ]]; then
  echo "[FAIL] ${EMIT_SV} is not built (lake build obend-emit-sv); nothing here can be shown to be emitter output" >&2
  exit 1
fi

echo "=== [1/5] byte equality with obend-emit-sv ==="
for pair in "fidget:fidget_impeller_voxel_cam.sv"; do
  target="${pair%%:*}"; file="${pair#*:}"
  "${EMIT_SV}" "${target}" --out "${TMP}/obend_emit_${file}" >/dev/null
  if ! cmp -s "${TMP}/obend_emit_${file}" "${SCRIPT_DIR}/${file}"; then
    echo "[FAIL] ${file} differs from \`obend-emit-sv ${target}\` (regenerate; do not hand-edit)" >&2
    diff "${TMP}/obend_emit_${file}" "${SCRIPT_DIR}/${file}" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${file}: identical"
done

echo "=== [2/5] LEC: the emitted .sv against Lean's model of fidgetImpellerVoxelCamRtlModule ==="
"${REPO_ROOT}/hardware/lec/lec.sh" fidget "${SCRIPT_DIR}/fidget_impeller_voxel_cam.sv" \
  "${SCRIPT_DIR}/fidget_impeller_voxel_cam_lec.smt2" --no-eqy "a 64-bit variable multiply; gate-level SAT equivalence of it does not terminate"

mkdir -p "${APP_DIR}/build"

if [[ -x "${OBEND_BIN}" ]]; then
  echo "=== [3/5] obend check / run on apps/fidget-cam/package.json ==="
  (
    cd "${REPO_ROOT}"
    "${OBEND_BIN}" check --package apps/fidget-cam/package.json
    "${OBEND_BIN}" run --package apps/fidget-cam/package.json
  )
else
  echo "=== [3/5] skipped: ${OBEND_BIN} not built ==="
fi

echo "=== [4/5] posted program from Lean (impeller5AxisNgc) ==="
"${EMIT_SV}" fidget-ngc --out "${APP_DIR}/build/impeller_5axis.ngc"
test -s "${APP_DIR}/build/impeller_5axis.ngc"

echo "=== [5/5] Verilator: scan, STL, waypoint re-check ==="
"${VERILATOR_BIN}" --cc --exe --build --trace -Wall -Wno-DECLFILENAME -Wno-UNUSED \
  -CFLAGS "-std=c++17 -O2" -j 2 \
  -Mdir "${SCRIPT_DIR}/obj_dir" \
  "${SCRIPT_DIR}/fidget_impeller_voxel_cam.sv" \
  "${SCRIPT_DIR}/fidget_voxel_tb.cpp" \
  -o Vfidget_impeller_voxel_cam >/dev/null
(
  cd "${SCRIPT_DIR}"
  ./obj_dir/Vfidget_impeller_voxel_cam "${APP_DIR}/build/impeller_5axis.ngc" "${APP_DIR}/build/impeller_part.stl"
)
test -s "${APP_DIR}/build/impeller_part.stl"
cp -f "${SCRIPT_DIR}/fidget_cam_trace.vcd" "${APP_DIR}/build/fidget_cam_trace.vcd"
echo "[PASS] apps/fidget-cam"
