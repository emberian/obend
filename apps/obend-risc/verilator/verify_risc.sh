#!/usr/bin/env bash
# apps/obend-risc/verilator/verify_risc.sh
# 1. the committed .sv and the Lean golden are byte-identical to what `obend-emit-sv` writes from
#    Obend.Apps.ObendRisc (`obendRiscCpuRtlModule`, `runRiscFirmwareSocCycles 21`); hand edits fail here;
# 2. LEC: Yosys's reading of the .sv against Lean's model of the same RtlModule
#    (`hardware/lec/lec.sh`, `obend_risc_cpu_lec.smt2` from `obend-emit-sv risc --lec`); a planted
#    one-bit mutation must be caught with a counterexample;
# 3. verilator -Wall lint and build of the emitted core with risc_soc_tb.cpp;
# 4. Phase A: firmware/test_prog.hex for 21 cycles, every register and dmem word against the Lean golden;
#    Phase B: the ISA torture program (negative immediates, SLT/SLTU/SRAI, S-type, backward BNE,
#    ECALL/MRET, JAL/JALR, BLTU/BGEU/BLT/BGE, x16..x31).
# The hand-typed risc_lec.smt2 was retired on 2026-11-04: it described the 15-register core.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
EMIT_SV="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR="${VERILATOR:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
TMP="${TMPDIR:-/tmp}"
cd "${SCRIPT_DIR}"

if [[ ! -x "${EMIT_SV}" ]]; then
  echo "[FAIL] ${EMIT_SV} is not built (lake build obend-emit-sv)" >&2
  exit 1
fi

echo "=== [0/4] native checks the Lean module names ==="
"${EMIT_SV}" check-risc

echo "=== [1/4] byte equality with obend-emit-sv ==="
for pair in "risc:obend_risc_cpu.sv" "golden-risc:risc_golden.txt"; do
  target="${pair%%:*}"; file="${pair#*:}"
  "${EMIT_SV}" "${target}" --out "${TMP}/obend_emit_${file}" >/dev/null
  if ! cmp -s "${TMP}/obend_emit_${file}" "${file}"; then
    echo "[FAIL] ${file} differs from \`obend-emit-sv ${target}\` (regenerate; do not hand-edit)" >&2
    diff "${TMP}/obend_emit_${file}" "${file}" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${file}: identical"
done

echo "=== [2/4] LEC: the emitted .sv against Lean's model of obendRiscCpuRtlModule ==="
"${REPO_ROOT}/hardware/lec/lec.sh" risc obend_risc_cpu.sv obend_risc_cpu_lec.smt2 --no-eqy \
  "a 64-bit variable multiply; gate-level SAT equivalence of it does not terminate"

echo "=== [3/4] verilator -Wall lint + build ==="
"${VERILATOR}" -Wall --lint-only obend_risc_cpu.sv
rm -rf obj_dir obend_risc_trace.vcd
"${VERILATOR}" -Wall --cc --exe --build --trace -j 2 obend_risc_cpu.sv risc_soc_tb.cpp -o Vobend_risc_cpu >/dev/null

echo "=== [4/4] firmware vs Lean golden, then the ISA torture program ==="
./obj_dir/Vobend_risc_cpu ../firmware/test_prog.hex obend_risc_trace.vcd risc_golden.txt
test -s obend_risc_trace.vcd
echo "[PASS] apps/obend-risc"
