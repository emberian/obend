#!/usr/bin/env bash
# Flagship App #5: the one silicon_elab_top.
#  1. regenerate silicon_elab_top.sv and silicon_elab_golden.txt from Lean and require byte equality,
#  2. verilator -Wall lint,
#  3. run the harness against the Lean-generated golden.
set -euo pipefail
export PATH="/opt/homebrew/bin:/usr/local/bin:$PATH"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
V="${SCRIPT_DIR}/verilator"
OBEND="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
EMIT="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"

echo "=== [1/3] byte equality with the Lean emitter ==="
"${OBEND}" hardware emit-silicon-sv --out /tmp/obend_silicon_elab_top.sv >/dev/null
cmp /tmp/obend_silicon_elab_top.sv "${V}/silicon_elab_top.sv" || { echo "[FAIL] silicon_elab_top.sv is not the emitter output; regenerate, do not hand-edit" >&2; exit 1; }
"${EMIT}" golden-silicon-kernel --out /tmp/obend_silicon_elab_golden.txt >/dev/null
cmp /tmp/obend_silicon_elab_golden.txt "${V}/silicon_elab_golden.txt" || { echo "[FAIL] silicon_elab_golden.txt is stale; regenerate with obend-emit-sv golden-silicon-kernel" >&2; exit 1; }
echo "  silicon_elab_top.sv and silicon_elab_golden.txt reproduce from Lean"

echo "=== [2/3] verilator -Wall lint ==="
(cd "${V}" && verilator --lint-only -Wall -Wno-DECLFILENAME --top-module silicon_elab_top silicon_elab_top.sv)

echo "=== [3/3] harness against the Lean golden ==="
(cd "${V}" && make clean >/dev/null && make run && make clean >/dev/null)
echo "[PASS] apps/silicon-kernel-verilator"
