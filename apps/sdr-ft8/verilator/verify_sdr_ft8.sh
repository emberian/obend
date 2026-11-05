#!/usr/bin/env bash
set -euo pipefail

# --- NOTE (2026-11-04): the .sv in this directory is HAND-WRITTEN reference RTL, not emitter output;
# --- the .smt2 is a hand-written property sheet, not an LEC. Both headers say so.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR_BIN="${VERILATOR_BIN:-/opt/homebrew/bin/verilator}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

echo "=== [1/3] Running Z3 QF_BV hand-written property sheet (not an LEC) (sdr_ft8_props.smt2) ==="
Z3_OUT="$("$Z3_BIN" -smt2 sdr_ft8_props.smt2)"
echo "Z3 output: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
    echo "ERROR: Expected 'unsat' from Z3 property sheet check, got '$Z3_OUT'" >&2
    exit 1
fi
echo "Z3 property sheet & Tayloe Image-Cancellation Check PASSED (unsat)."

echo "=== [2/3] Compiling sdr_ft8_top.sv + sdr_ft8_tb.cpp with Verilator ==="
"$VERILATOR_BIN" --cc --exe --build --trace -j 4 \
    -CFLAGS "-std=c++17 -O3" \
    sdr_ft8_top.sv sdr_ft8_tb.cpp \
    -o Vsdr_ft8_top

echo "=== [3/3] Executing 16,384-Sample (79-Symbol FT8 + +40 dB Image Interferer) SDR Co-Simulation ==="
./obj_dir/Vsdr_ft8_top

if [[ ! -s "sdr_ft8_trace.vcd" ]]; then
    echo "ERROR: sdr_ft8_trace.vcd was not generated or is empty!" >&2
    exit 1
fi
VCD_BYTES="$(wc -c < sdr_ft8_trace.vcd | tr -d ' ')"
echo "Verified VCD waveform trace: sdr_ft8_trace.vcd (${VCD_BYTES} bytes)"
echo "=== Flagship App #3 (apps/sdr-ft8) Verilator SDR + Z3 property sheet Suite PASSED ==="
