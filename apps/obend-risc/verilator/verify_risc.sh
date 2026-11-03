#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

echo "=== [1/3] Compiling obend_risc_cpu.sv + risc_soc_tb.cpp with Verilator ==="
"$VERILATOR_BIN" --cc --exe --build --trace -Wno-fatal \
  -O2 obend_risc_cpu.sv risc_soc_tb.cpp -o Vobend_risc_cpu

echo "=== [2/3] Running Verilator cycle-accurate simulation & dumping obend_risc_trace.vcd ==="
./obj_dir/Vobend_risc_cpu ../firmware/test_prog.hex obend_risc_trace.vcd

if [[ ! -s obend_risc_trace.vcd ]]; then
  echo "[FAIL] obend_risc_trace.vcd was not generated or is empty"
  exit 1
fi
echo "[OK] obend_risc_trace.vcd generated ($(wc -c < obend_risc_trace.vcd) bytes)"

echo "=== [3/3] Running Z3 SMT2 Logical Equivalence & Non-Interference Check (risc_lec.smt2) ==="
Z3_OUT="$("$Z3_BIN" -smt2 risc_lec.smt2)"
echo "Z3 output: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
  echo "[FAIL] Expected unsat from z3 -smt2 risc_lec.smt2, got: $Z3_OUT"
  exit 1
fi

echo "=== [PASS] Flagship App #1 (obend-risc) Verilator + VCD + Z3 SMT2 LEC verified! ==="
