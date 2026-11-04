#!/usr/bin/env bash
set -euo pipefail

# --- NOTE (2026-11-04): the .sv in this directory is HAND-WRITTEN reference RTL, not emitter output;
# --- the .smt2 is a hand-written property sheet, not an LEC. Both headers say so.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

echo "=== [1/4] Strict Verilator -Wall lint check on zk_ntt_coproc.sv ==="
"$VERILATOR_BIN" -Wall --lint-only zk_ntt_coproc.sv

echo "=== [2/4] Clean build of zk_ntt_coproc.sv + zk_ntt_tb.cpp with Verilator -Wall ==="
rm -rf obj_dir zk_ntt_trace.vcd
"$VERILATOR_BIN" -Wall --cc --exe --build --trace \
  -O2 zk_ntt_coproc.sv zk_ntt_tb.cpp -o Vzk_ntt_coproc

echo "=== [3/4] Running Verilator 256-pt Goldilocks NTT + II=1 Pipeline + 8-round Sumcheck & dumping zk_ntt_trace.vcd ==="
./obj_dir/Vzk_ntt_coproc zk_ntt_trace.vcd

if [[ ! -s zk_ntt_trace.vcd ]]; then
  echo "[FAIL] zk_ntt_trace.vcd was not generated or is empty"
  exit 1
fi
echo "[OK] zk_ntt_trace.vcd generated ($(wc -c < zk_ntt_trace.vcd) bytes)"

echo "=== [4/4] Running Z3 SMT2 hand-written property sheet (not an LEC) (zk_ntt_lec.smt2) ==="
Z3_OUT="$("$Z3_BIN" -smt2 zk_ntt_lec.smt2)"
echo "Z3 output: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
  echo "[FAIL] Expected unsat from z3 -smt2 zk_ntt_lec.smt2, got: $Z3_OUT"
  exit 1
fi

echo "=== [PASS] Flagship App #4 (zk-ntt) Verilator -Wall + VCD + Z3 property sheet verified! ==="
