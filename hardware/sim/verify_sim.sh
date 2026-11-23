#!/usr/bin/env bash
# hardware/sim: regenerate all 6 emitted SystemVerilog modules and their Yosys LEC miters from Lean,
# require byte-identical equality (`diff -u`), prove each equivalent to Lean's `RtlModule` semantics
# (`hardware/lec/lec.sh`: Yosys `read_verilog -sv; proc; flatten; write_smt2` + Z3/Bitwuzla `QF_BV`
# miter `unsat`, plus planted 1-bit output mutation `sat`, plus EQY gate-level equivalence where SAT
# terminates), then run both the multi-cycle domain-specific C++ Verilator co-simulation (`tb_top.sv`
# + `sim_main.cpp`) and `VerilateRunner` continuous-trace differential harnesses against Lean's
# `runModuleTrace` / `evalModuleOutputsW`.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OBEND="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
EMIT="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
if [[ -n "${VERILATOR_BIN:-}" && -x "${VERILATOR_BIN}" ]]; then
  VERILATOR="${VERILATOR_BIN}"
  unset VERILATOR_BIN
else
  if ! command -v verilator >/dev/null 2>&1 || ! verilator --version >/dev/null 2>&1; then
    if [[ -d /tmp/verilator-ok/usr_root/usr/share/verilator ]]; then
      export VERILATOR_ROOT=/tmp/verilator-ok/usr_root/usr/share/verilator
      export VERILATOR_BIN=../../bin/verilator_bin
      export PATH="/tmp/verilator-ok/bin:${PATH}"
    fi
  fi
  VERILATOR="$(command -v verilator || echo /opt/homebrew/bin/verilator)"
fi
cd "${SCRIPT_DIR}"

PAIRS=(
  "risc64:obend_pipelined_risc64.sv:obend_pipelined_risc64_lec.smt2"
  "goldilocks-bfly4:obend_goldilocks_bfly4.sv:obend_goldilocks_bfly4_lec.smt2"
  "gf2-64-karatsuba:obend_gf2_64_karatsuba.sv:obend_gf2_64_karatsuba_lec.smt2"
  "ospc-tile0:obend_ospc_tile0.sv:obend_ospc_tile0_lec.smt2"
  "mac2:obend_retimed_mac2.sv:obend_retimed_mac2_lec.smt2"
  "width-probe:obend_width_probe.sv:obend_width_probe_lec.smt2"
)

WORK_TMP="$(mktemp -d "${TMPDIR:-/tmp}/obend-verify-sim.XXXXXX")"
trap 'rm -rf "${WORK_TMP}" "${SCRIPT_DIR}/obj_dir" "${SCRIPT_DIR}/sim_wave.vcd"' EXIT

echo "=== [1/4] byte equality: committed .sv & *_lec.smt2 == obend-emit-sv output ==="
for entry in "${PAIRS[@]}"; do
  IFS=":" read -r target sv_file lec_file <<< "${entry}"
  "${EMIT}" "${target}" --out "${WORK_TMP}/${sv_file}" >/dev/null
  diff -u "${WORK_TMP}/${sv_file}" "${sv_file}"
  "${EMIT}" "${target}" --lec --out "${WORK_TMP}/${lec_file}" >/dev/null
  diff -u "${WORK_TMP}/${lec_file}" "${lec_file}"
  echo "  ${sv_file} + ${lec_file}: byte-identical"
done

echo "=== [2/4] LEC: Yosys write_smt2 + Z3/Bitwuzla QF_BV against Lean RtlModule ==="
LEC="${REPO_ROOT}/hardware/lec/lec.sh"
EQY_BIN_CHECK="${EQY_BIN:-$([[ -x "${HOME}/tools/oss-cad-suite/bin/eqy" ]] && echo "${HOME}/tools/oss-cad-suite/bin/eqy" || command -v eqy || true)}"
EQY_FLAG=(--no-eqy "eqy binary not installed on host; QF_BV Yosys+Z3 miter & mutation verified")
if [[ -n "${EQY_BIN_CHECK}" && -x "${EQY_BIN_CHECK}" ]]; then
  EQY_FLAG=(--eqy)
fi

"${LEC}" risc64 obend_pipelined_risc64.sv obend_pipelined_risc64_lec.smt2 "${EQY_FLAG[@]}"
"${LEC}" goldilocks-bfly4 obend_goldilocks_bfly4.sv obend_goldilocks_bfly4_lec.smt2 --no-eqy \
  "four 32x32->64 multipliers in Stage 1; gate-level SAT equivalence does not terminate"
"${LEC}" gf2-64-karatsuba obend_gf2_64_karatsuba.sv obend_gf2_64_karatsuba_lec.smt2 "${EQY_FLAG[@]}"
"${LEC}" ospc-tile0 obend_ospc_tile0.sv obend_ospc_tile0_lec.smt2 "${EQY_FLAG[@]}"
"${LEC}" mac2 obend_retimed_mac2.sv obend_retimed_mac2_lec.smt2 --no-eqy \
  "a 64x64 variable multiply; gate-level SAT equivalence of it does not terminate"
"${LEC}" width-probe obend_width_probe.sv obend_width_probe_lec.smt2 "${EQY_FLAG[@]}"

echo "=== [3/4] Verilator -Wall lint + multi-cycle RISC64 / Goldilocks / GF(2^64) / OSPC co-sim ==="
"${VERILATOR}" --lint-only -Wall -Wno-DECLFILENAME -Wno-UNUSED --top-module tb_top tb_top.sv
"${VERILATOR}" --lint-only -Wall --top-module obend_width_probe obend_width_probe.sv
"${VERILATOR}" --lint-only -Wall --top-module obend_ospc_tile0 obend_ospc_tile0.sv
rm -rf obj_dir
"${VERILATOR}" -Wall -Wno-DECLFILENAME -Wno-UNUSED --cc --exe --build --trace -j 4 \
  -CFLAGS "-std=c++17 -O2" --top-module tb_top tb_top.sv sim_main.cpp -o Vtb_top >/dev/null
./obj_dir/Vtb_top

echo "=== [4/4] Lean runModuleTrace / evalModuleOutputsW vs Verilated SV (16 vectors x 6 continuous cycles) ==="
for entry in "${PAIRS[@]}"; do
  IFS=":" read -r target sv_file _ <<< "${entry}"
  top="$(sed -n 's/^module \([A-Za-z_][A-Za-z0-9_]*\).*/\1/p' "${sv_file}" | head -1)"
  tb_cpp="${WORK_TMP}/${target}_tb.cpp"
  mdir="obj_dir/diff_${target}"
  "${EMIT}" "${target}" --tb --vectors 16 --cycles 6 --out "${tb_cpp}" >/dev/null
  "${VERILATOR}" --cc --exe --build -j 4 -CFLAGS "-std=c++17 -O2" --top-module "${top}" \
    -sv -Wno-UNUSED -Wno-DECLFILENAME -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND \
    --x-assign unique --x-initial unique --Mdir "${mdir}" -o "sim_${target}" \
    "${sv_file}" "${tb_cpp}" >/dev/null
  "./${mdir}/sim_${target}"
done
for top in obend_retimed_mac2 obend_width_probe; do
  (cd "${REPO_ROOT}" && "${OBEND}" verilate --top "${top}" --work-dir hardware/sim/obj_dir/verilate)
done

echo "[PASS] hardware/sim"
