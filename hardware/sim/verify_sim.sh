#!/usr/bin/env bash
# hardware/sim: regenerate the four emitted modules from Lean, require byte equality with the
# committed files, prove each equivalent to Lean's model of its RtlModule (`hardware/lec/lec.sh`:
# Yosys `write_smt2` of the .sv + `*_lec.smt2` from `obend-emit-sv --lec`, z3 unsat; a planted
# one-bit mutation must come back sat; EQY against the synthesized netlist where it terminates),
# then run the Verilator harness and `obend verilate` (Lean model vs Verilated SV).
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OBEND="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
EMIT="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
VERILATOR="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
cd "${SCRIPT_DIR}"

echo "=== [1/4] byte equality: committed .sv == obend-emit-sv output ==="
for pair in "mac2:obend_retimed_mac2.sv" "tcad:cleanroom_tcad_stack.sv" \
            "stator:lc_drives_userspace_stator.sv" "mill:cnc_5axis_userspace_mill.sv" \
            "width-probe:obend_width_probe.sv"; do
  target="${pair%%:*}"; file="${pair#*:}"
  "${EMIT}" "${target}" --out "/tmp/obend_emit_${file}" >/dev/null
  if ! cmp -s "/tmp/obend_emit_${file}" "${file}"; then
    echo "[FAIL] ${file} differs from \`obend-emit-sv ${target}\` (regenerate; do not hand-edit)" >&2
    diff "/tmp/obend_emit_${file}" "${file}" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${file}: identical"
done

echo "=== [2/4] LEC: Yosys's reading of each .sv against Lean's model of its RtlModule ==="
LEC="${REPO_ROOT}/hardware/lec/lec.sh"
"${LEC}" tcad cleanroom_tcad_stack.sv cleanroom_tcad_stack_lec.smt2 --eqy
"${LEC}" mill cnc_5axis_userspace_mill.sv cnc_5axis_userspace_mill_lec.smt2 --eqy
"${LEC}" stator lc_drives_userspace_stator.sv lc_drives_userspace_stator_lec.smt2 --eqy
"${LEC}" mac2 obend_retimed_mac2.sv obend_retimed_mac2_lec.smt2 --no-eqy \
  "a 64x64 variable multiply; gate-level SAT equivalence of it does not terminate"
"${LEC}" width-probe obend_width_probe.sv obend_width_probe_lec.smt2 --eqy

echo "=== [3/4] Verilator -Wall lint + harness ==="
"${VERILATOR}" --lint-only -Wall -Wno-DECLFILENAME -Wno-UNUSED --top-module tb_top tb_top.sv
# Widths and two clock domains: the emitted probe lints clean under -Wall on its own.
"${VERILATOR}" --lint-only -Wall --top-module obend_width_probe obend_width_probe.sv
rm -rf obj_dir
"${VERILATOR}" -Wall -Wno-DECLFILENAME -Wno-UNUSED --cc --exe --build --trace -j 0 \
  --top-module tb_top tb_top.sv sim_main.cpp -o Vtb_top >/dev/null
./obj_dir/Vtb_top

echo "=== [4/4] obend verilate: Lean model vs Verilated emitted SV (16 vectors x 4 cycles) ==="
for top in cleanroom_tcad_stack lc_drives_userspace_stator cnc_5axis_userspace_mill obend_width_probe; do
  (cd "${REPO_ROOT}" && "${OBEND}" verilate --top "${top}" --work-dir hardware/sim/obj_dir/verilate)
done

echo "[PASS] hardware/sim"
