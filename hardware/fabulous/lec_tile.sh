#!/usr/bin/env bash
# hardware/fabulous/lec_tile.sh PROJECT_DIR
#
# The LUT4AB tile model (`Obend.Hardware.Fabulous.Tile`) against the RTL FABulous generated for it.
# For each of the switch matrix (`lut4ab-sm`), the LUT4 cell (`lut4c`) and the MUX8LUT (`mux8lut`):
#   1. `hardware/lec/lec.sh`: the emitted SV against Lean's model of the RtlModule, with its own
#      planted output mutation (the standard LEC of every emitted module);
#   2. Yosys reads FABulous's Verilog (`PROJECT/Tile/LUT4AB/*.v`, the primitives of
#      `PROJECT/Fabric/models_pack.v`; the switch matrix through `tile/LUT4AB_switch_matrix_lec.v`,
#      which only splits `ConfigBits` into 64-bit words), and z3 must answer unsat against the same Lean
#      half: every output and next register of FABulous's RTL equals Lean's model, for every input,
#      configuration and register state.
# Then the planted fault: the Lean half of the switch matrix with one table entry changed
# (`obend fabric tile-mutant`: two inputs of one multiplexer exchanged) must answer sat.
set -euo pipefail
PROJ="$(cd "$1" && pwd)"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../.." && pwd)"
EMIT="${OBEND_EMIT_SV:-${ROOT}/lean/.lake/build/bin/obend-emit-sv}"
OBEND="${OBEND:-${ROOT}/lean/.lake/build/bin/obend}"
OSS_CAD="${OSS_CAD:-/Users/ember/tools/oss-cad-suite}"
YOSYS="${YOSYS_BIN:-${OSS_CAD}/bin/yosys}"
Z3="${Z3_BIN:-$(command -v z3 || echo /opt/homebrew/bin/z3)}"
W="$(mktemp -d "${TMPDIR:-/tmp}/lec-tile.XXXXXX")"
trap 'rm -rf "${W}"' EXIT
T="${PROJ}/Tile/LUT4AB"
PRIMS="${PROJ}/Fabric/models_pack.v"

fab_smt2() {  # $1 = top, $2 = out, rest = files
  local top="$1" out="$2"; shift 2
  "${YOSYS}" -q -p "read_verilog -sv $*; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 ${out}"
}
z3_on() {  # $1 = yosys smt2, $2 = lean half -> first line of z3's answer
  { cat "$1"; sed '/^; --- counterexample/,$d' "$2"; } | "${Z3}" -T:"${LEC_SECS:-300}" -in 2>&1 | head -1
}

for spec in "lut4ab-sm:LUT4AB_switch_matrix_lec:${HERE}/tile/LUT4AB_switch_matrix_lec.v ${T}/LUT4AB_switch_matrix.v" \
            "lut4c:LUT4c_frame_config_dffesr:${T}/LUT4c_frame_config_dffesr.v" \
            "mux8lut:MUX8LUT_frame_config_mux:${T}/MUX8LUT_frame_config_mux.v"; do
  target="${spec%%:*}"; rest="${spec#*:}"; top="${rest%%:*}"; files="${rest#*:}"
  sv="${HERE}/tile/${top}.sv"
  lec="${sv%.sv}_lec.smt2"
  echo "=== ${target}: ${top} ==="
  "${EMIT}" "${target}" --out "${W}/${target}.sv" >/dev/null
  cmp "${W}/${target}.sv" "${sv}"
  echo "  $(basename "${sv}"): identical to obend-emit-sv ${target}"
  "${ROOT}/hardware/lec/lec.sh" "${target}" "${sv}" "${lec}" --no-eqy "the FABulous LEC below is the gate here"
  # shellcheck disable=SC2086
  fab_smt2 "${top}" "${W}/${target}.fab.smt2" ${files} "${PRIMS}"
  verdict="$(z3_on "${W}/${target}.fab.smt2" "${lec}")"
  if [[ "${verdict}" != "unsat" ]]; then
    echo "[FAIL] LEC ${top}: z3 says ${verdict}; FABulous's RTL is not shown equal to Lean's model" >&2; exit 1
  fi
  echo "  LEC ${top}: unsat (FABulous's generated RTL == Lean's model of the RtlModule)"
done

echo "=== planted fault: one switch-matrix table entry changed ==="
"${OBEND}" fabric tile-mutant --out "${W}/mutant_lec.smt2"
verdict="$(z3_on "${W}/lut4ab-sm.fab.smt2" "${W}/mutant_lec.smt2")"
if [[ "${verdict}" != "sat" ]]; then
  echo "[FAIL] the mutant switch-matrix model was not refused (z3: ${verdict})" >&2; exit 1
fi
echo "  LEC LUT4AB_switch_matrix_lec against the mutant model: sat, as it must be"
echo "[PASS] tile LEC"
