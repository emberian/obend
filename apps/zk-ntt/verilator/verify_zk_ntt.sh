#!/usr/bin/env bash
# apps/zk-ntt/verilator/verify_zk_ntt.sh
# 1. the committed .sv and the Lean golden are byte-identical to what `obend-emit-sv` writes from
#    Obend.Apps.ZkNtt (`zkNttCoprocRtlModule`, `zkSumcheckGolden`); hand edits fail here;
# 2. LEC: Yosys's reading of the .sv against Lean's model of the same RtlModule
#    (`hardware/lec/lec.sh`, `zk_ntt_coproc_lec.smt2` from `obend-emit-sv zk --lec`); a planted
#    one-bit mutation must be caught with a counterexample;
# 3. verilator -Wall lint and build with zk_ntt_tb.cpp;
# 4. boundary vectors, a 256-point NTT/INTT (2048 butterflies), and the 8-round sumcheck whose
#    challenges come from the hardware transcript, all against the __uint128_t reference and the
#    Lean golden.
# The hand-typed zk_ntt_lec.smt2 and the hand-written zk_ntt_coproc.sv were retired on 2026-11-04.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
EMIT_SV="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR_BIN="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
TMP="${TMPDIR:-/tmp}"
cd "${SCRIPT_DIR}"

if [[ ! -x "${EMIT_SV}" ]]; then
  echo "[FAIL] ${EMIT_SV} is not built (lake build obend-emit-sv)" >&2
  exit 1
fi

echo "=== [0/4] native checks the Lean module names ==="
"${EMIT_SV}" check-zk

echo "=== [1/4] byte equality with obend-emit-sv ==="
for pair in "zk:zk_ntt_coproc.sv" "golden-zk:zk_ntt_golden.txt"; do
  target="${pair%%:*}"; file="${pair#*:}"
  "${EMIT_SV}" "${target}" --out "${TMP}/obend_emit_${file}" >/dev/null
  if ! cmp -s "${TMP}/obend_emit_${file}" "${file}"; then
    echo "[FAIL] ${file} differs from \`obend-emit-sv ${target}\` (regenerate; do not hand-edit)" >&2
    diff "${TMP}/obend_emit_${file}" "${file}" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${file}: identical"
done

echo "=== [2/4] LEC: the emitted .sv against Lean's model of zkNttCoprocRtlModule ==="
"${REPO_ROOT}/hardware/lec/lec.sh" zk zk_ntt_coproc.sv zk_ntt_coproc_lec.smt2 --no-eqy \
  "a 64-bit variable multiply; gate-level SAT equivalence of it does not terminate"

echo "=== [3/4] verilator -Wall lint + build ==="
"${VERILATOR_BIN}" -Wall --lint-only zk_ntt_coproc.sv
rm -rf obj_dir zk_ntt_trace.vcd
"${VERILATOR_BIN}" -Wall --cc --exe --build --trace -O2 -j 2 zk_ntt_coproc.sv zk_ntt_tb.cpp -o Vzk_ntt_coproc >/dev/null

echo "=== [4/4] boundary vectors, NTT/INTT, sumcheck with the hardware transcript vs the Lean golden ==="
./obj_dir/Vzk_ntt_coproc zk_ntt_trace.vcd zk_ntt_golden.txt
test -s zk_ntt_trace.vcd
echo "[PASS] apps/zk-ntt"
