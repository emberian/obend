#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

echo "=== [1/3] Running Z3 QF_BV Logic Equivalence & Safety Barrier Check (foc_drive_lec.smt2) ==="
Z3_OUT="$("$Z3_BIN" -smt2 foc_drive_lec.smt2)"
echo "Z3 output: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
    echo "ERROR: Expected 'unsat' from Z3 LEC check, got '$Z3_OUT'" >&2
    exit 1
fi
echo "Z3 LEC & Safety Barrier Check PASSED (unsat)."

echo "=== [2/3] Compiling foc_drive_top.sv + foc_hil_tb.cpp with Verilator ==="
"$VERILATOR_BIN" --cc --exe --build --trace -j 4 \
    -CFLAGS "-std=c++17 -O3" \
    foc_drive_top.sv foc_hil_tb.cpp \
    -o Vfoc_drive_top

echo "=== [3/3] Executing 500,000-Step (50 ms, dt = 100 ns) RK4 + Verilator FOC HIL Simulation ==="
./obj_dir/Vfoc_drive_top

if [[ ! -s "foc_hil_trace.vcd" ]]; then
    echo "ERROR: foc_hil_trace.vcd was not generated or is empty!" >&2
    exit 1
fi
VCD_BYTES="$(wc -c < foc_hil_trace.vcd | tr -d ' ')"
echo "Verified VCD waveform trace: foc_hil_trace.vcd (${VCD_BYTES} bytes)"
echo "=== Flagship App #2 (apps/foc-hil) Verilator HIL + Z3 LEC Suite PASSED ==="
