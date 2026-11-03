#!/usr/bin/env bash
# Flagship App #6 (`apps/fidget-cam/verilator/verify_fidget_cam.sh`):
# Compiles the pruned SSA F-Rep voxelizer & 5-axis CAM hardware pipeline with Verilator,
# evaluates the 3D octree in hardware, emits `build/impeller_part.stl` + `build/impeller_5axis.ngc`
# + `fidget_cam_trace.vcd`, and verifies Z3 SMT2 LEC returns `unsat`.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
APP_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

mkdir -p "${APP_DIR}/build" "${SCRIPT_DIR}/build"

echo "[1/3] Compiling fidget_impeller_voxel_cam.sv with ${VERILATOR_BIN}..."
"${VERILATOR_BIN}" --cc --exe --build --trace -Wall \
  -Wno-DECLFILENAME \
  -CFLAGS "-std=c++17 -O2" \
  -Mdir "${SCRIPT_DIR}/obj_dir" \
  "${SCRIPT_DIR}/fidget_impeller_voxel_cam.sv" \
  "${SCRIPT_DIR}/fidget_voxel_tb.cpp" \
  -o Vfidget_impeller_voxel_cam

echo "[2/3] Running Verilated 3D Octree Voxelizer, .stl Mesh Emitter & 5-Axis G-Code Verifier..."
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

echo "[3/3] Running Z3 QF_BV LEC on fidget_cam_lec.smt2..."
LEC_OUT="$("${Z3_BIN}" -smt2 "${SCRIPT_DIR}/fidget_cam_lec.smt2")"
echo "Z3 LEC result: ${LEC_OUT}"
if [[ "${LEC_OUT}" != "unsat" ]]; then
  echo "ERROR: Expected 'unsat' from Z3 LEC, got '${LEC_OUT}'" >&2
  exit 1
fi

echo "[PASS] Flagship App #6 (apps/fidget-cam) Verilator + .stl + 5-axis G-code + Z3 LEC verified!"
