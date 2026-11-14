#!/usr/bin/env bash
# apps/sdr-ft8/verilator/verify_sdr_ft8.sh
# The receive chain (emitted from Obend.Apps.SdrFt8Rx) on a real FT8 recording.
# 1. sdr_nco_mix.sv, sdr_cic3_r64.sv and sdr_ft8_disc.sv are byte-identical to what `obend-emit-sv`
#    writes from sdrNcoModule, sdrCicModule and sdrFt8DiscModule; hand edits fail here;
# 2. LEC: Yosys's reading of each against Lean's model of its RtlModule (hardware/lec/lec.sh);
# 3. verilator -Wall lint and build of sdr_ft8_rx_top.sv (wiring only) with sdr_ft8_rx_tb.cpp;
# 4. the WSJT-X sample recording ../recording/ft8_target.txt names (downloaded once, sha256 checked)
#    through the RTL: every decimated CIC output equal to the exact CIC output of
#    Obend.Hardware.Cic.cicOut_eq_movingSum, and the 79 tone decisions equal to the reference decode's
#    message's 79 channel tones.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
EMIT_SV="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR_BIN="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
TMP="${TMPDIR:-/tmp}"
REC_DIR="${SCRIPT_DIR}/../recording"
cd "${SCRIPT_DIR}"

if [[ ! -x "${EMIT_SV}" ]]; then
  echo "[FAIL] ${EMIT_SV} is not built (lake build obend-emit-sv)" >&2
  exit 1
fi

echo "=== [1/4] byte equality with obend-emit-sv ==="
for pair in "sdr-nco:sdr_nco_mix.sv" "sdr-cic:sdr_cic3_r64.sv" "sdr-disc:sdr_ft8_disc.sv"; do
  target="${pair%%:*}"; file="${pair#*:}"
  "${EMIT_SV}" "${target}" --out "${TMP}/obend_emit_${file}" >/dev/null
  if ! cmp -s "${TMP}/obend_emit_${file}" "${file}"; then
    echo "[FAIL] ${file} differs from \`obend-emit-sv ${target}\` (regenerate; do not hand-edit)" >&2
    diff "${TMP}/obend_emit_${file}" "${file}" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${file}: identical"
done

echo "=== [2/4] LEC: each emitted .sv against Lean's model of its RtlModule ==="
"${REPO_ROOT}/hardware/lec/lec.sh" sdr-cic sdr_cic3_r64.sv sdr_cic3_r64_lec.smt2
"${REPO_ROOT}/hardware/lec/lec.sh" sdr-nco sdr_nco_mix.sv sdr_nco_mix_lec.smt2 --no-eqy \
  "64-bit variable multiplies; gate-level SAT equivalence of them does not terminate"
"${REPO_ROOT}/hardware/lec/lec.sh" sdr-disc sdr_ft8_disc.sv sdr_ft8_disc_lec.smt2 --no-eqy \
  "64-bit variable multiplies; gate-level SAT equivalence of them does not terminate"

echo "=== [3/4] verilator -Wall lint + build of the receive chain ==="
"${VERILATOR_BIN}" -Wall --lint-only --top-module sdr_ft8_rx_top sdr_ft8_rx_top.sv sdr_nco_mix.sv sdr_cic3_r64.sv sdr_ft8_disc.sv
rm -rf obj_dir/rx
"${VERILATOR_BIN}" -Wall --cc --exe --build -j 4 -CFLAGS "-std=c++17 -O2" --top-module sdr_ft8_rx_top \
  --Mdir obj_dir/rx sdr_ft8_rx_top.sv sdr_nco_mix.sv sdr_cic3_r64.sv sdr_ft8_disc.sv sdr_ft8_rx_tb.cpp \
  -o Vsdr_ft8_rx >/dev/null

echo "=== [4/4] a real FT8 recording through the RTL ==="
url="$(sed -n 's/^url //p' "${REC_DIR}/ft8_target.txt")"
sum="$(sed -n 's/^sha256 //p' "${REC_DIR}/ft8_target.txt")"
wav="${REC_DIR}/$(basename "${url}")"
if [[ ! -s "${wav}" ]]; then
  curl -fsSL -o "${wav}.part" "${url}" && mv "${wav}.part" "${wav}"
fi
got="$( (command -v sha256sum >/dev/null && sha256sum "${wav}" || shasum -a 256 "${wav}") | cut -d' ' -f1)"
if [[ "${got}" != "${sum}" ]]; then
  echo "[FAIL] ${wav}: sha256 ${got}, expected ${sum}" >&2
  exit 1
fi
./obj_dir/rx/Vsdr_ft8_rx "${wav}" "${REC_DIR}/ft8_target.txt"
echo "[PASS] apps/sdr-ft8"
