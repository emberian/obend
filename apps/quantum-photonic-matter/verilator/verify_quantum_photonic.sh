#!/usr/bin/env bash
# Flagship App #8 (`apps/quantum-photonic-matter/verilator/verify_quantum_photonic.sh`):
# End-to-end obend CLI package check/run + Verilator cycle-accurate simulation + Z3 `QF_BV` LEC.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$SCRIPT_DIR"

OBEND_BIN="${OBEND_BIN:-$REPO_ROOT/lean/.lake/build/bin/obend}"
VERILATOR="${VERILATOR:-/opt/homebrew/bin/verilator}"
Z3="${Z3:-/opt/homebrew/bin/z3}"

if [[ -x "$OBEND_BIN" ]]; then
  echo "=== [0/3] Checking & running apps/quantum-photonic-matter/package.json + stdlib via obend CLI ==="
  (
    cd "$REPO_ROOT"
    "$OBEND_BIN" check stdlib/physical/QuantumPhotonicMatter.obend >/dev/null
    "$OBEND_BIN" check --package apps/quantum-photonic-matter/package.json >/dev/null
    RUN_VAL="$("$OBEND_BIN" run --package apps/quantum-photonic-matter/package.json)"
    echo "obend run --package apps/quantum-photonic-matter/package.json => $RUN_VAL"
  )
fi

rm -rf obj_dir quantum_photonic_trace.vcd

echo "=== [1/3] Compiling quantum_photonic_coproc_top.sv with Verilator ==="
"$VERILATOR" -Wall -Wno-DECLFILENAME -Wno-UNUSED --cc --exe --build --trace \
  -O2 \
  quantum_photonic_coproc_top.sv \
  quantum_photonic_tb.cpp \
  -o Vquantum_photonic_coproc_top

echo "=== [2/3] Running cycle-accurate Krawtchouk PST + Faddeev-LeVerrier + 3-Stage Majorana simulation ==="
./obj_dir/Vquantum_photonic_coproc_top

if [[ ! -s "quantum_photonic_trace.vcd" ]]; then
  echo "ERROR: missing or empty VCD trace quantum_photonic_trace.vcd" >&2
  exit 1
fi
echo "Verified VCD trace: quantum_photonic_trace.vcd ($(wc -c < quantum_photonic_trace.vcd) bytes)"

echo "=== [3/3] Proving 64-bit QF_BV RTL/Spec + Crosstalk + 3-Stage Braiding Equivalence in Z3 ==="
Z3_OUT="$("$Z3" quantum_photonic_lec.smt2)"
echo "Z3 LEC result: $Z3_OUT"
if [[ "$Z3_OUT" != "unsat" ]]; then
  echo "ERROR: Z3 LEC failed (expected unsat, got '$Z3_OUT')" >&2
  exit 1
fi

echo "=== SUCCESS: Flagship App #8 (quantum-photonic-matter) obend CLI + Verilator + Z3 LEC verified ==="
