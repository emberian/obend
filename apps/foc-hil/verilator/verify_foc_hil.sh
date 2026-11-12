#!/usr/bin/env bash
# apps/foc-hil/verilator/verify_foc_hil.sh
# End-to-end verification of the emitted salient IPM FOC + 6-level SiC FCML controller
# (`Obend.Apps.FocHil.focHilSequentialRtlModule`):
# 1. foc_drive_top.sv is byte-identical to `obend-emit-sv foc-hil`;
# 2. Yosys + Z3 LEC (`hardware/lec/lec.sh`) proves foc_drive_top.sv equivalent to Lean's RtlModule
#    model (`foc_drive_top_lec.smt2`) across all inputs and register states, and catches a planted
#    output bit-flip mutation;
# 3. Z3 QF_BV safety barrier property sheet (`foc_drive_props.smt2`);
# 4. Verilator `-Wall` lint + build + 500,000-step (50 ms, dt = 100 ns) RK4 closed-loop FOC HIL
#    co-simulation (250 A torque step, FCML active balancing, live ICAP DPR hot-swap, 155 C 1-cycle
#    gate-kill dominating dpr_isolate_en=1, and write-once fault latch).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
EMIT_SV="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR_BIN="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
Z3_BIN="${Z3_BIN:-$(command -v z3 || echo /opt/homebrew/bin/z3)}"
TMP="${TMPDIR:-/tmp}"
cd "${SCRIPT_DIR}"

if [[ ! -x "${EMIT_SV}" ]]; then
  echo "[FAIL] ${EMIT_SV} is not built (lake build obend-emit-sv)" >&2
  exit 1
fi

echo "=== [1/4] byte equality with obend-emit-sv foc-hil ==="
"${EMIT_SV}" foc-hil --out "${TMP}/obend_emit_foc_drive_top.sv" >/dev/null
if ! cmp -s "${TMP}/obend_emit_foc_drive_top.sv" foc_drive_top.sv; then
  echo "[FAIL] foc_drive_top.sv differs from \`obend-emit-sv foc-hil\` (regenerate; do not hand-edit)" >&2
  diff "${TMP}/obend_emit_foc_drive_top.sv" foc_drive_top.sv | head -20 >&2 || true
  exit 1
fi
echo "  foc_drive_top.sv: identical"

echo "=== [2/4] LEC: emitted foc_drive_top.sv against Lean's RtlModule model ==="
"${REPO_ROOT}/hardware/lec/lec.sh" foc-hil foc_drive_top.sv foc_drive_top_lec.smt2 --no-eqy \
  "64-bit Q32 multiplies in decoupling feedforward; gate-level SAT equivalence of them does not terminate"

echo "=== [3/4] Z3 QF_BV safety barrier property sheet (foc_drive_props.smt2) ==="
Z3_OUT="$("${Z3_BIN}" -smt2 foc_drive_props.smt2)"
if [[ "${Z3_OUT}" != "unsat" ]]; then
  echo "[FAIL] Expected 'unsat' from Z3 property sheet check, got '${Z3_OUT}'" >&2
  exit 1
fi
echo "  foc_drive_props.smt2: unsat"

echo "=== [4/4] Verilator -Wall lint + 500,000-step (50 ms, dt = 100 ns) RK4 FOC HIL ==="
"${VERILATOR_BIN}" -Wall --lint-only --top-module foc_drive_top foc_drive_top.sv
rm -rf obj_dir
"${VERILATOR_BIN}" -Wall --cc --exe --build --trace -j 4 \
    -CFLAGS "-std=c++17 -O3 -Wall" \
    --top-module foc_drive_top \
    foc_drive_top.sv foc_hil_tb.cpp \
    -o Vfoc_drive_top >/dev/null
./obj_dir/Vfoc_drive_top

if [[ ! -s "foc_hil_trace.vcd" ]]; then
  echo "[FAIL] foc_hil_trace.vcd was not generated or is empty" >&2
  exit 1
fi
VCD_BYTES="$(wc -c < foc_hil_trace.vcd | tr -d ' ')"
echo "  Verified VCD waveform trace: foc_hil_trace.vcd (${VCD_BYTES} bytes)"
echo "[PASS] apps/foc-hil"
