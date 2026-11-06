#!/usr/bin/env bash
# hardware/fabulous: the FABulous bitstream for iceStickMac8, read back and checked against Lean.
#   [1/5] `obend fabric wrapper` regenerates top_wrapper.v byte for byte
#   [2/5] FABulous's flow (flow.sh, pinned) rebuilds obend_ice40_mac8.bin byte for byte
#   [3/5] `obend fabric extract` reads it back to Mac8Net.lean byte for byte, and
#         `obend fabric check` accepts it: it is the mac8Net that mac8_fabric_realizes_module is about
#   [4/5] a bitstream with one configuration bit of a used LUT flipped is refused, naming tile and bit
#   [5/5] FABulous's fabric RTL, configured with the bitstream through its self-write port, simulated
#         by Icarus, shows mac_out as `moduleRun iceStickMac8` computes it on every cycle after reset
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

echo "=== [1/5] top_wrapper.v == obend fabric wrapper ==="
"${OBEND}" fabric wrapper --out "${W}/top_wrapper.v"
cmp "${W}/top_wrapper.v" "${HERE}/top_wrapper.v"
echo "identical"

echo "=== [2/5] FABulous flow rebuilds the committed bitstream ==="
BIN="$("${HERE}/flow.sh" "${W}" | tail -1)"
P="${W}/mac8"
cmp "${BIN}" "${HERE}/obend_ice40_mac8.bin"
echo "identical ($(wc -c < "${BIN}" | tr -d ' ') bytes)"

echo "=== [3/5] read back: Mac8Net.lean and obend fabric check ==="
"${OBEND}" fabric extract --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin" \
  --source hardware/fabulous/obend_ice40_mac8.bin --out "${W}/Mac8Net.lean"
cmp "${W}/Mac8Net.lean" "${ROOT}/lean/Obend/Hardware/Fabulous/Mac8Net.lean"
echo "Mac8Net.lean identical"
"${OBEND}" fabric check --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin"

echo "=== [4/5] a flipped bit is refused ==="
SITE="$(grep -m1 -o '"X[0-9]*Y[0-9]*\.[A-H]"' "${ROOT}/lean/Obend/Hardware/Fabulous/Mac8Net.lean" | tr -d '"')"
"${OBEND}" fabric flip --project "${P}" --bin "${HERE}/obend_ice40_mac8.bin" --feature "${SITE}.INIT[3]" --out "${W}/flipped.bin"
if "${OBEND}" fabric check --project "${P}" --bin "${W}/flipped.bin" --golden "${HERE}/obend_ice40_mac8.bin" 2> "${W}/refusal.txt"; then
  echo "[FAIL] the flipped bitstream was accepted"; exit 1
fi
cat "${W}/refusal.txt"
grep -q "tile ${SITE%%.*} bit " "${W}/refusal.txt" || { echo "[FAIL] the refusal does not name the tile and bit"; exit 1; }

echo "=== [5/5] FABulous fabric simulation vs Lean (${CYCLES} cycles) ==="
"${OBEND}" fabric vectors --cycles "${CYCLES}" --out "${W}/vec.hex"
od -An -tx1 -v "${HERE}/obend_ice40_mac8.bin" | tr -s ' ' '\n' | grep -v '^$' > "${W}/bit.hex"
iverilog -g2012 -s mac8_fabric_tb -o "${W}/tb.vvp" "${P}"/Test/build/fabric_files/*.v "${HERE}/mac8_fabric_tb.v"
vvp -n "${W}/tb.vvp" +bitstream_hex="${W}/bit.hex" +bitbytes="$(wc -c < "${HERE}/obend_ice40_mac8.bin" | tr -d ' ')" \
  +vectors="${W}/vec.hex" +cycles="${CYCLES}" | tee "${W}/sim.log" | grep -v "^VCD"
grep -q "mismatches=0" "${W}/sim.log" || { echo "[FAIL] fabric simulation"; exit 1; }

echo "[PASS] hardware/fabulous"
