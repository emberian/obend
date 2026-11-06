#!/usr/bin/env bash
# hardware/fabulous: the FABulous bitstream for iceStickMac8, read back and checked against Lean.
#   [1/6] `obend fabric wrapper` regenerates top_wrapper.v byte for byte
#   [2/6] FABulous's flow (flow.sh, pinned) rebuilds obend_ice40_mac8.bin byte for byte
#   [3/6] `obend fabric extract` reads it back to Mac8Net.lean byte for byte, and
#         `obend fabric check` accepts it: it is the mac8Net that mac8_fabric_realizes_module is about
#   [4/6] a bitstream with one truth-table bit of a used LUT flipped, and one with a select bit of a
#         switch-matrix multiplexer on a used route flipped, are refused, naming tile and bit
#   [5/6] FABulous's fabric RTL, configured with the bitstream through its self-write port, simulated
#         by Icarus, shows mac_out as `moduleRun iceStickMac8` computes it on every cycle after reset
#   [6/6] the LUT4AB tile model is read from the regenerated RTL byte for byte and LEC'd against it
#         (lec_tile.sh), with a planted change to the switch-matrix table refused
# Needs: lake build obend (lean/), FABulous at FAB_HOME, oss-cad-suite at OSS_CAD_SUITE.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../.." && pwd)"
OBEND="${OBEND:-${ROOT}/lean/.lake/build/bin/obend}"
OSS="${OSS_CAD_SUITE:-/Users/ember/tools/oss-cad-suite/bin}"
CYCLES="${CYCLES:-200}"
W="$(mktemp -d "${TMPDIR:-/tmp}/verify-fabric.XXXXXX")"
trap 'rm -rf "${W}"' EXIT
export PATH="${OSS}:${PATH}"

echo "=== [1/6] top_wrapper.v == obend fabric wrapper ==="
"${OBEND}" fabric wrapper --out "${W}/top_wrapper.v"
cmp "${W}/top_wrapper.v" "${HERE}/top_wrapper.v"
echo "identical"

echo "=== [2/6] FABulous flow rebuilds the committed bitstream ==="
BIN="$("${HERE}/flow.sh" "${W}" | tail -1)"
P="${W}/mac8"
cmp "${BIN}" "${HERE}/obend_ice40_mac8.bin"
echo "identical ($(wc -c < "${BIN}" | tr -d ' ') bytes)"

echo "=== [3/6] read back: Mac8Net.lean and obend fabric check ==="
"${OBEND}" fabric extract --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin" \
  --source hardware/fabulous/obend_ice40_mac8.bin --out "${W}/Mac8Net.lean"
cmp "${W}/Mac8Net.lean" "${ROOT}/lean/Obend/Hardware/Fabulous/Mac8Net.lean"
echo "Mac8Net.lean identical"
"${OBEND}" fabric check --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin"

echo "=== [4/6] a flipped bit is refused ==="
SITE="$(grep -m1 -o '"X[0-9]*Y[0-9]*\.[A-H]"' "${ROOT}/lean/Obend/Hardware/Fabulous/Mac8Net.lean" | tr -d '"')"
"${OBEND}" fabric flip --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin" --feature "${SITE}.INIT[3]" --out "${W}/flipped.bin"
if "${OBEND}" fabric check --project "${P}" --bin "${W}/flipped.bin" --golden "${HERE}/obend_ice40_mac8.bin" 2> "${W}/refusal.txt"; then
  echo "[FAIL] the flipped bitstream was accepted"; exit 1
fi
cat "${W}/refusal.txt"
grep -q "tile ${SITE%%.*} bit " "${W}/refusal.txt" || { echo "[FAIL] the refusal does not name the tile and bit"; exit 1; }
# and a routing bit: a select bit of the switch-matrix multiplexer feeding input I0 of a LUT that reads it
RSITE="$(grep -m1 -oE '#16, \((\.pin|\.ff|\.gate) [0-9]+\), .*"X[0-9]+Y[0-9]+\.[A-H]"' "${ROOT}/lean/Obend/Hardware/Fabulous/Mac8Net.lean" \
  | grep -oE '"X[0-9]+Y[0-9]+\.[A-H]"' | tr -d '"')"
NODE="${RSITE%%.*}.L${RSITE##*.}_I0"
"${OBEND}" fabric flip --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin" --node "${NODE}" --out "${W}/flipped_route.bin"
if "${OBEND}" fabric check --project "${P}" --bin "${W}/flipped_route.bin" --golden "${HERE}/obend_ice40_mac8.bin" 2> "${W}/refusal_route.txt"; then
  echo "[FAIL] the bitstream with a routing bit flipped was accepted"; exit 1
fi
cat "${W}/refusal_route.txt"
grep -q "tile ${NODE%%.*} bit " "${W}/refusal_route.txt" || { echo "[FAIL] the routing refusal does not name the tile and bit"; exit 1; }

echo "=== [5/6] FABulous fabric simulation vs Lean (${CYCLES} cycles) ==="
"${OBEND}" fabric vectors --cycles "${CYCLES}" --out "${W}/vec.hex"
od -An -tx1 -v "${HERE}/obend_ice40_mac8.bin" | tr -s ' ' '\n' | grep -v '^$' > "${W}/bit.hex"
iverilog -g2012 -s mac8_fabric_tb -o "${W}/tb.vvp" "${P}"/Test/build/fabric_files/*.v "${HERE}/mac8_fabric_tb.v"
vvp -n "${W}/tb.vvp" +bitstream_hex="${W}/bit.hex" +bitbytes="$(wc -c < "${HERE}/obend_ice40_mac8.bin" | tr -d ' ')" \
  +vectors="${W}/vec.hex" +cycles="${CYCLES}" | tee "${W}/sim.log" | grep -v "^VCD"
grep -q "mismatches=0" "${W}/sim.log" || { echo "[FAIL] fabric simulation"; exit 1; }

echo "=== [6/6] the tile model against FABulous's tile RTL ==="
"${OBEND}" fabric tile --project "${P}" --out-lean "${W}/LUT4ABSwitchMatrix.lean" --out-harness "${W}/LUT4AB_switch_matrix_lec.v"
cmp "${W}/LUT4ABSwitchMatrix.lean" "${ROOT}/lean/Obend/Hardware/Fabulous/LUT4ABSwitchMatrix.lean"
cmp "${W}/LUT4AB_switch_matrix_lec.v" "${HERE}/tile/LUT4AB_switch_matrix_lec.v"
echo "LUT4ABSwitchMatrix.lean and the LEC harness identical"
"${HERE}/lec_tile.sh" "${P}"

echo "[PASS] hardware/fabulous"
