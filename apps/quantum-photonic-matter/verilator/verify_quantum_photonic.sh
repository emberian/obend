#!/usr/bin/env bash
# Flagship App #8 (`apps/quantum-photonic-matter/verilator/verify_quantum_photonic.sh`):
# End-to-end Verilator cycle-accurate simulation + Z3 `QF_BV` LEC verification.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

VERILATOR="${VERILATOR:-/opt/homebrew/bin/verilator}"
Z3="${Z3:-/opt/homebrew/bin/z3}"

echo "=== [1/3] Compiling quantum_photonic_coproc_top.sv with Verilator ==="
"$VERILATOR" -Wall --cc --exe --build --trace \
  -O2 \
  quantum_photonic_coproc_top.sv \
  quantum_photonic_tb.cpp \
  -o Vquantum_photonic_coproc_top

echo "=== [2/3] Running cycle-accurate Krawtchouk PST + Faddeev-LeVerrier + Majorana simulation ==="
./obj_dir/Vquantum_photonic_coproc_top

if [[ ! -s "quantum_photonic_trace.vcd" ]]; then
  echo "ERROR: missing or empty VCD trace quantum_photonic_trace.vcd" >&2
  exit 1
fi
echo "Verified VCD trace: quantum_photonic_trace.vcd ($(wc -c < quantum_photonic_trace.vcd) bytes)"

echo "=== [3/3] Proving 64-bit QF_BV RTL/Spec + Crosstalk + Braiding Equivalence in Z3 ==="
Z3_OUT="$("$Z3" quantum_photonic_lec.smt2)"
echo "Z3 LEC result: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
  echo "ERROR: Z3 LEC failed (expected unsat, got '$Z3_OUT')" >&2
  exit 1
fi

echo "=== SUCCESS: Flagship App #8 (quantum-photonic-matter) Verilator + Z3 LEC verified ==="
