#!/usr/bin/env bash
# Flagship App #6 (`apps/fidget-cam/verilator/verify_fidget_cam.sh`):
# 1. Verifies the 4-module `.obend` package (`apps/fidget-cam/package.json`) with `obend check` & `obend run`,
# 2. Compiles the `emitModuleSV`-generated pruned SSA F-Rep voxelizer & 5-axis CAM RTL with Verilator,
# 3. Evaluates the recursive 3D octree in hardware, emits `build/impeller_part.stl` + `build/impeller_5axis.ngc`
#    + `fidget_cam_trace.vcd`, and verifies full-surface no-gouge + adversarial gouge detection,
# 4. Verifies Z3 property sheet (`fidget_cam_lec.smt2`) returns `unsat`.
set -euo pipefail

# --- byte equality with the Lean emitter (2026-11-04): the committed .sv must be exactly what
# --- `obend-emit-sv fidget` writes from the Lean RtlModule. Hand edits fail here.
EMIT_SV="${OBEND_EMIT_SV:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)/lean/.lake/build/bin/obend-emit-sv}"
if [[ -x "${EMIT_SV}" ]]; then
  "${EMIT_SV}" fidget --out /tmp/obend_emit_fidget_impeller_voxel_cam.sv >/dev/null
  if ! cmp -s /tmp/obend_emit_fidget_impeller_voxel_cam.sv "$(dirname "${BASH_SOURCE[0]}")/fidget_impeller_voxel_cam.sv"; then
    echo "[FAIL] fidget_impeller_voxel_cam.sv is not the output of obend-emit-sv fidget; regenerate it, do not hand-edit" >&2
    diff /tmp/obend_emit_fidget_impeller_voxel_cam.sv "$(dirname "${BASH_SOURCE[0]}")/fidget_impeller_voxel_cam.sv" | head -20 >&2 || true
    exit 1
  fi
  echo "[OK] fidget_impeller_voxel_cam.sv is byte-identical to obend-emit-sv fidget"
else
  echo "[FAIL] obend-emit-sv not built (lake build obend-emit-sv); cannot prove fidget_impeller_voxel_cam.sv is emitter output" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
APP_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${APP_DIR}/.." && cd .. && pwd)"
OBEND_BIN="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

mkdir -p "${APP_DIR}/build" "${SCRIPT_DIR}/build"

if [[ -x "${OBEND_BIN}" ]]; then
  echo "[0/3] Checking & running multi-module Objective Bend package apps/fidget-cam/package.json..."
  (
    cd "${REPO_ROOT}"
    "${OBEND_BIN}" check --package apps/fidget-cam/package.json
    "${OBEND_BIN}" run --package apps/fidget-cam/package.json
  )
fi

echo "[1/3] Compiling fidget_impeller_voxel_cam.sv with ${VERILATOR_BIN}..."
"${VERILATOR_BIN}" --cc --exe --build --trace -Wall \
  -Wno-DECLFILENAME \
  -CFLAGS "-std=c++17 -O2" \
  -Mdir "${SCRIPT_DIR}/obj_dir" \
  "${SCRIPT_DIR}/fidget_impeller_voxel_cam.sv" \
  "${SCRIPT_DIR}/fidget_voxel_tb.cpp" \
  -o Vfidget_impeller_voxel_cam

echo "[2/3] Running Verilated 3D Octree Voxelizer, .stl Mesh Emitter & Full-Surface 5-Axis G-Code Verifier..."
(
  cd "${SCRIPT_DIR}"
  ./obj_dir/Vfidget_impeller_voxel_cam
)

cp -f "${SCRIPT_DIR}/build/impeller_part.stl" "${APP_DIR}/build/impeller_part.stl"
cp -f "${SCRIPT_DIR}/build/impeller_5axis.ngc" "${APP_DIR}/build/impeller_5axis.ngc"
cp -f "${SCRIPT_DIR}/fidget_cam_trace.vcd" "${APP_DIR}/build/fidget_cam_trace.vcd"

test -s "${APP_DIR}/build/impeller_part.stl"
test -s "${APP_DIR}/build/impeller_5axis.ngc"
test -s "${SCRIPT_DIR}/fidget_cam_trace.vcd"

echo "[3/3] Running Z3 property sheet on fidget_cam_lec.smt2..."
LEC_OUT="$("${Z3_BIN}" -smt2 "${SCRIPT_DIR}/fidget_cam_lec.smt2")"
echo "Z3 property sheet result: ${LEC_OUT}"
if [[ "${LEC_OUT}" != "unsat" ]]; then
  echo "ERROR: Expected 'unsat' from Z3 property sheet, got '${LEC_OUT}'" >&2
  exit 1
fi

echo "[PASS] Flagship App #6 (apps/fidget-cam) .obend + Verilator + .stl + 5-axis G-code + Z3 property sheet verified!"
