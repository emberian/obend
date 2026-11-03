#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$SCRIPT_DIR"

OBEND_BIN="$REPO_ROOT/target/debug/obend"
if [[ -x "$OBEND_BIN" ]]; then
  echo "[0/3] Checking & running apps/sovereign-drex/package.json via obend CLI..."
  "$OBEND_BIN" check --package "$REPO_ROOT/apps/sovereign-drex/package.json" >/dev/null
  RUN_VAL="$("$OBEND_BIN" run --package "$REPO_ROOT/apps/sovereign-drex/package.json")"
  echo "obend run --package apps/sovereign-drex/package.json => $RUN_VAL"
fi

rm -rf obj_dir sovereign_drex_trace.vcd

echo "[1/3] Compiling sovereign_drex_batch_top.sv with /opt/homebrew/bin/verilator..."
/opt/homebrew/bin/verilator --cc --exe --build -j 0 \
  --trace -Wall -Wno-DECLFILENAME -Wno-UNUSED \
  sovereign_drex_batch_top.sv drex_batch_tb.cpp \
  -o Vsovereign_drex_batch_top

echo "[2/3] Running Verilated 4-Validator Sovereign DReX + K-CARRY + WAL Simulation..."
./obj_dir/Vsovereign_drex_batch_top

test -s "sovereign_drex_trace.vcd"

echo "[3/3] Running Z3 QF_BV LEC on sovereign_drex_lec.smt2..."
LEC_OUT="$(/opt/homebrew/bin/z3 -smt2 sovereign_drex_lec.smt2)"
echo "Z3 LEC result: $LEC_OUT"
if [[ "$LEC_OUT" != "unsat" ]]; then
  echo "ERROR: Expected unsat from Z3 LEC, got: $LEC_OUT" >&2
  exit 1
fi

echo "[PASS] Flagship App #7 (apps/sovereign-drex) obend CLI + Verilator + K-CARRY + Z3 LEC verified!"
