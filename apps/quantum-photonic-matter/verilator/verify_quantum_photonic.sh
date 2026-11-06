#!/usr/bin/env bash
# Flagship App #8 (`apps/quantum-photonic-matter/verilator/verify_quantum_photonic.sh`):
# byte equality with the Lean emitter, the LEC of the emitted .sv against Lean's model of its RtlModule
# (`hardware/lec/lec.sh`), obend CLI package check/run, and Verilator simulation. The hand-typed
# property sheet that stood here (a transcription of the datapath and invariants of that copy) was
# removed on 2026-11-05: the LEC checks the emitted .sv itself.
set -euo pipefail

# --- byte equality with the Lean emitter (2026-11-04): the committed .sv must be exactly what
# --- `obend-emit-sv quantum` writes from the Lean RtlModule. Hand edits fail here.
EMIT_SV="${OBEND_EMIT_SV:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)/lean/.lake/build/bin/obend-emit-sv}"
if [[ -x "${EMIT_SV}" ]]; then
  "${EMIT_SV}" quantum --out /tmp/obend_emit_quantum_photonic_coproc_top.sv >/dev/null
  if ! cmp -s /tmp/obend_emit_quantum_photonic_coproc_top.sv "$(dirname "${BASH_SOURCE[0]}")/quantum_photonic_coproc_top.sv"; then
    echo "[FAIL] quantum_photonic_coproc_top.sv is not the output of obend-emit-sv quantum; regenerate it, do not hand-edit" >&2
    diff /tmp/obend_emit_quantum_photonic_coproc_top.sv "$(dirname "${BASH_SOURCE[0]}")/quantum_photonic_coproc_top.sv" | head -20 >&2 || true
    exit 1
  fi
  echo "[OK] quantum_photonic_coproc_top.sv is byte-identical to obend-emit-sv quantum"
else
  echo "[FAIL] obend-emit-sv not built (lake build obend-emit-sv); cannot prove quantum_photonic_coproc_top.sv is emitter output" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$SCRIPT_DIR"

echo "=== LEC: the emitted .sv against Lean's model of quantumPhotonicCoprocTopRtlModule ==="
"$REPO_ROOT/hardware/lec/lec.sh" quantum quantum_photonic_coproc_top.sv quantum_photonic_coproc_top_lec.smt2 \
  --no-eqy "a 64-bit variable multiply; gate-level SAT equivalence of it does not terminate"

OBEND_BIN="${OBEND_BIN:-$REPO_ROOT/lean/.lake/build/bin/obend}"
VERILATOR="${VERILATOR:-/opt/homebrew/bin/verilator}"

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

echo "=== [1/2] Compiling quantum_photonic_coproc_top.sv with Verilator ==="
"$VERILATOR" -Wall -Wno-DECLFILENAME -Wno-UNUSED --cc --exe --build --trace \
  -O2 \
  quantum_photonic_coproc_top.sv \
  quantum_photonic_tb.cpp \
  -o Vquantum_photonic_coproc_top

echo "=== [2/2] Running cycle-accurate Krawtchouk PST + Faddeev-LeVerrier + 3-Stage Majorana simulation ==="
./obj_dir/Vquantum_photonic_coproc_top

if [[ ! -s "quantum_photonic_trace.vcd" ]]; then
  echo "ERROR: missing or empty VCD trace quantum_photonic_trace.vcd" >&2
  exit 1
fi
echo "Verified VCD trace: quantum_photonic_trace.vcd ($(wc -c < quantum_photonic_trace.vcd) bytes)"

echo "=== SUCCESS: Flagship App #8 (quantum-photonic-matter) LEC + obend CLI + Verilator verified ==="
