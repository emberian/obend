#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}"

VERILATOR="${VERILATOR:-/opt/homebrew/bin/verilator}"
Z3="${Z3:-/opt/homebrew/bin/z3}"

echo "=== [1/4] Strict Verilator -Wall lint check on obend_risc_cpu.sv ==="
"${VERILATOR}" -Wall --lint-only obend_risc_cpu.sv

echo "=== [2/4] Clean & compile obend_risc_cpu.sv + risc_soc_tb.cpp via Verilator ==="
rm -rf obj_dir obend_risc_trace.vcd
"${VERILATOR}" -Wall --cc --exe --build --trace -j 0 \
  obend_risc_cpu.sv risc_soc_tb.cpp \
  -o Vobend_risc_cpu

echo "=== [3/4] Execute cycle-accurate RISC SoC simulation (randReset(2) + VCD trace + ISA torture) ==="
./obj_dir/Vobend_risc_cpu ../firmware/test_prog.hex obend_risc_trace.vcd

if [[ ! -s "obend_risc_trace.vcd" ]]; then
  echo "[FATAL] Expected non-empty VCD waveform obend_risc_trace.vcd" >&2
  exit 1
fi
echo "[OK] Generated waveform trace: $(wc -c < obend_risc_trace.vcd) bytes -> ${SCRIPT_DIR}/obend_risc_trace.vcd"

echo "=== [4/4] Run Z3 QF_BV Logical Equivalence & Non-Interference Check (risc_lec.smt2) ==="
LEC_OUT="$("${Z3}" -smt2 risc_lec.smt2)"
echo "Z3 output: ${LEC_OUT}"
if [[ "${LEC_OUT}" != "unsat" ]]; then
  echo "[FATAL] Expected 'unsat' from Z3 LEC check, got '${LEC_OUT}'" >&2
  exit 1
fi
echo "[PASS] All Verilator -Wall, Firmware, ISA Torture & Z3 QF_BV LEC checks succeeded!"
