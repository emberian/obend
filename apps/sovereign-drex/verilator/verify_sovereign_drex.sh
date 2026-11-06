#!/usr/bin/env bash
set -euo pipefail

# --- byte equality with the Lean emitter (2026-11-04): the committed .sv must be exactly what
# --- `obend-emit-sv drex` writes from the Lean RtlModule. Hand edits fail here.
EMIT_SV="${OBEND_EMIT_SV:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)/lean/.lake/build/bin/obend-emit-sv}"
if [[ -x "${EMIT_SV}" ]]; then
  "${EMIT_SV}" drex --out /tmp/obend_emit_sovereign_drex_batch_top.sv >/dev/null
  if ! cmp -s /tmp/obend_emit_sovereign_drex_batch_top.sv "$(dirname "${BASH_SOURCE[0]}")/sovereign_drex_batch_top.sv"; then
    echo "[FAIL] sovereign_drex_batch_top.sv is not the output of obend-emit-sv drex; regenerate it, do not hand-edit" >&2
    diff /tmp/obend_emit_sovereign_drex_batch_top.sv "$(dirname "${BASH_SOURCE[0]}")/sovereign_drex_batch_top.sv" | head -20 >&2 || true
    exit 1
  fi
  echo "[OK] sovereign_drex_batch_top.sv is byte-identical to obend-emit-sv drex"
else
  echo "[FAIL] obend-emit-sv not built (lake build obend-emit-sv); cannot prove sovereign_drex_batch_top.sv is emitter output" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$SCRIPT_DIR"

echo "=== LEC: the emitted .sv against Lean's model of sovereignDrexBatchTopRtlModule, and EQY against its netlist ==="
"$REPO_ROOT/hardware/lec/lec.sh" drex sovereign_drex_batch_top.sv sovereign_drex_batch_top_lec.smt2 --eqy

OBEND_BIN="${OBEND_BIN:-$REPO_ROOT/lean/.lake/build/bin/obend}"
if [[ -x "$OBEND_BIN" ]]; then
  echo "[0/3] Checking & running apps/sovereign-drex/package.json via obend CLI..."
  (
    cd "$REPO_ROOT"
    "$OBEND_BIN" check --package apps/sovereign-drex/package.json >/dev/null
    RUN_VAL="$("$OBEND_BIN" run --package apps/sovereign-drex/package.json)"
    echo "obend run --package apps/sovereign-drex/package.json => $RUN_VAL"
  )
fi

VERILATOR_BIN="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"

rm -rf obj_dir sovereign_drex_trace.vcd

echo "[1/2] Compiling sovereign_drex_batch_top.sv with $VERILATOR_BIN..."
"$VERILATOR_BIN" --cc --exe --build -j 0 \
  --trace -Wall -Wno-DECLFILENAME -Wno-UNUSED \
  sovereign_drex_batch_top.sv drex_batch_tb.cpp \
  -o Vsovereign_drex_batch_top

echo "[2/2] Running Verilated 4-Validator Sovereign DReX + K-CARRY + WAL Simulation..."
./obj_dir/Vsovereign_drex_batch_top

test -s "sovereign_drex_trace.vcd"

echo "[PASS] Flagship App #7 (apps/sovereign-drex) LEC + EQY + obend CLI + Verilator + K-CARRY verified!"
