#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

echo "=== [1/3] Compiling zk_ntt_coproc.sv + zk_ntt_tb.cpp with Verilator ==="
"$VERILATOR_BIN" --cc --exe --build --trace -Wno-fatal \
  -O2 zk_ntt_coproc.sv zk_ntt_tb.cpp -o Vzk_ntt_coproc

echo "=== [2/3] Running Verilator 256-pt Goldilocks NTT + 8-round Sumcheck & dumping zk_ntt_trace.vcd ==="
./obj_dir/Vzk_ntt_coproc zk_ntt_trace.vcd

if [[ ! -s zk_ntt_trace.vcd ]]; then
  echo "[FAIL] zk_ntt_trace.vcd was not generated or is empty"
  exit 1
fi
echo "[OK] zk_ntt_trace.vcd generated ($(wc -c < zk_ntt_trace.vcd) bytes)"

echo "=== [3/3] Running Z3 SMT2 Logical Equivalence Check (zk_ntt_lec.smt2) ==="
Z3_OUT="$("$Z3_BIN" -smt2 zk_ntt_lec.smt2)"
echo "Z3 output: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
  echo "[FAIL] Expected unsat from z3 -smt2 zk_ntt_lec.smt2, got: $Z3_OUT"
  exit 1
fi

echo "=== [PASS] Flagship App #4 (zk-ntt) Verilator + VCD + Z3 SMT2 LEC verified! ==="
