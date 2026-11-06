#!/usr/bin/env bash
# hardware/gpu/square: one hypergraph through two devices (Obend.Hardware.Square). Every graph of
# `squareGraphs` (Obend.Hardware.SquareGraphs) is lowered twice, to a combinational RtlModule and to
# the GPU program of ../graphs/<graph>/; `rtl_eq_gpu` (scalar graphs) and `rtl_eq_gpu_array` (array
# graphs) say the two denote one evaluation. This gate runs both legs outside Lean on the same vectors
# and requires three parties to agree: Verilator on the emitted SystemVerilog, the card, and the model.
#
#   verify_square.sh                 the gate, per graph:
#     [1] bytes: sv/<top>.sv == `obend-emit-sv square-<graph>` (the LEC half is compared by lec.sh)
#     [2] models: `obend-emit-sv square-<graph> --expected` (evalModuleOutputs of the RtlModule, the
#         HDL semantics) == ../graphs/<graph>/expected.tsv (evalGraphArr, the array model), byte for byte
#     [3] LEC: hardware/lec/lec.sh (Yosys's reading of the .sv against Lean's model of the RtlModule,
#         z3 unsat; its planted bit flip sat); EQY against Yosys's synthesis for the graphs in EQY_GRAPHS
#     [4] Verilator: the harness `obend-emit-sv square-<graph> --tb` (emitVerilatorHarnessCpp over the
#         graph's vectors against evalModuleOutputs) built on the committed .sv, mismatches=0
#     [5] the card: obend-gpu-run ../graphs/<graph> (every vector against expected.tsv)
#     [6] teeth: an operator swapped in a copy of the .sv (`+` to `-`, else `*` to `+`) must make the
#         Verilator harness report mismatches and the LEC answer sat (lec.sh fails)
#   verify_square.sh --graph NAME    one graph
#   verify_square.sh --stage N       one stage (1-6) of every graph
#
# Tools: obend-emit-sv (`lake build obend-emit-sv` in lean/), obend-gpu-run (`cargo build --release`
# in ../runner/), verilator, and the OSS CAD Suite yosys/eqy/z3 that hardware/lec/lec.sh finds. The
# device is chosen as ../verify_gpu.sh chooses it (GPU_ADAPTER, GPU_ICD).
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
GPU_DIR="${SCRIPT_DIR}/.."
EMIT="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
RUN="${OBEND_GPU_RUN:-${GPU_DIR}/runner/target/release/obend-gpu-run}"
VERILATOR="${VERILATOR_BIN:-$(command -v verilator || echo /opt/homebrew/bin/verilator)}"
LEC="${REPO_ROOT}/hardware/lec/lec.sh"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_square.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
RADEON_ICD=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json

# The graphs whose gate-level equivalence (EQY, SAT against the synthesized netlist) terminates: those
# without a 64-bit variable multiply. The rest run the LEC only, as hardware/sim does for mac2.
EQY_GRAPHS="${EQY_GRAPHS:-tree512}"

for t in "${EMIT}" "${RUN}" "${VERILATOR}"; do
  [[ -x "${t}" ]] || { echo "[FAIL] ${t} missing" >&2; exit 1; }
done
if [[ "$(uname -s)" == Linux && -r "${RADEON_ICD}" && "${GPU_ICD:-radv}" != any ]]; then
  export VK_ICD_FILENAMES="${RADEON_ICD}"
fi
ADAPTER_ARGS=()
[[ -n "${GPU_ADAPTER:-}" ]] && ADAPTER_ARGS=(--adapter "${GPU_ADAPTER}")

ONLY=""; STAGE=""
while (( $# > 0 )); do
  case "$1" in
    --graph) ONLY="${2:?--graph NAME}"; shift 2 ;;
    --stage) STAGE="${2:?--stage N}"; shift 2 ;;
    *) echo "usage: verify_square.sh [--graph NAME] [--stage N]" >&2; exit 2 ;;
  esac
done
run_stage() { [[ -z "${STAGE}" || "${STAGE}" == "$1" ]]; }

mapfile -t GRAPHS < <("${EMIT}" list | cut -f1 | awk '/^square-/ { sub(/^square-/, ""); print }')
if [[ -n "${ONLY}" ]]; then GRAPHS=("${ONLY}"); fi

# verilate TOP SV TB MDIR : build and run the harness; sets MISMATCHES (or fails the build)
verilate() {
  local top="$1" sv="$2" tb="$3" mdir="$4"
  "${VERILATOR}" --cc --exe --build --top-module "${top}" -sv \
    -Wno-UNUSED -Wno-DECLFILENAME -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND \
    --x-assign unique --x-initial unique --Mdir "${mdir}" -o "sim_${top}" "${sv}" "${tb}" \
    > "${mdir}.build.log" 2>&1 || { echo "[FAIL] verilator build of ${sv}:" >&2; tail -20 "${mdir}.build.log" >&2; exit 1; }
  set +e
  SIM_OUT="$("${mdir}/sim_${top}" 2>&1)"
  set -e
  MISMATCHES="$(sed -n 's/.*mismatches=\([0-9]*\).*/\1/p' <<< "${SIM_OUT}" | head -1)"
  [[ -n "${MISMATCHES}" ]] || { echo "[FAIL] ${top}: the harness printed no summary:" >&2; echo "${SIM_OUT}" | tail -5 >&2; exit 1; }
}

for g in "${GRAPHS[@]}"; do
  top="sq_${g//-/_}"
  sv="${SCRIPT_DIR}/sv/${top}.sv"
  lec="${SCRIPT_DIR}/sv/${top}_lec.smt2"
  echo "=== ${g} (${top}) ==="
  mkdir -p "${WORK}/${g}"

  if run_stage 1; then
    "${EMIT}" "square-${g}" --out "${WORK}/${g}/${top}.sv" >/dev/null
    if ! cmp -s "${WORK}/${g}/${top}.sv" "${sv}"; then
      echo "[FAIL] sv/${top}.sv differs from \`obend-emit-sv square-${g}\` (regenerate; do not hand-edit)" >&2
      diff "${WORK}/${g}/${top}.sv" "${sv}" | head -20 >&2 || true
      exit 1
    fi
    echo "  [1] sv/${top}.sv: identical to obend-emit-sv square-${g}"
  fi

  if run_stage 2; then
    "${EMIT}" "square-${g}" --expected --out "${WORK}/${g}/expected.tsv" >/dev/null
    if ! cmp -s "${WORK}/${g}/expected.tsv" "${GPU_DIR}/graphs/${g}/expected.tsv"; then
      echo "[FAIL] ${g}: the HDL model (evalModuleOutputs) and the array model (expected.tsv) differ:" >&2
      diff "${WORK}/${g}/expected.tsv" "${GPU_DIR}/graphs/${g}/expected.tsv" | head -10 >&2 || true
      exit 1
    fi
    echo "  [2] HDL model == array model on $(wc -l < "${GPU_DIR}/graphs/${g}/expected.tsv" | tr -d ' ') vectors (expected.tsv byte for byte)"
  fi

  if run_stage 3; then
    if [[ " ${EQY_GRAPHS} " == *" ${g} "* ]]; then
      "${LEC}" "square-${g}" "${sv}" "${lec}" --eqy | sed 's/^/  [3]/'
    else
      "${LEC}" "square-${g}" "${sv}" "${lec}" --no-eqy "a 64-bit variable multiply; gate-level SAT equivalence does not terminate" | sed 's/^/  [3]/'
    fi
  fi

  if run_stage 4 || run_stage 6; then
    "${EMIT}" "square-${g}" --tb --out "${WORK}/${g}/tb.cpp" >/dev/null
  fi

  if run_stage 4; then
    verilate "${top}" "${sv}" "${WORK}/${g}/tb.cpp" "${WORK}/${g}/obj"
    if [[ "${MISMATCHES}" != 0 ]]; then
      echo "[FAIL] ${g}: Verilator disagrees with evalModuleOutputs on ${MISMATCHES} ports:" >&2
      echo "${SIM_OUT}" | head -10 >&2
      exit 1
    fi
    echo "  [4] Verilator: $(grep -o 'vectors=[0-9]*' <<< "${SIM_OUT}"), mismatches=0 against evalModuleOutputs"
  fi

  if run_stage 5; then
    set +e
    RUN_OUT="$("${RUN}" "${GPU_DIR}/graphs/${g}" "${ADAPTER_ARGS[@]}" 2>"${WORK}/${g}/run.err")"
    RUN_RC=$?
    set -e
    if (( RUN_RC != 0 )); then
      echo "[FAIL] ${g} on the device: $(cat "${WORK}/${g}/run.err")" >&2
      echo "${RUN_OUT}" | head -5 >&2
      exit 1
    fi
    echo "  [5] the card: $(echo "${RUN_OUT}" | tail -1)"
  fi

  if run_stage 6; then
    # the first binary operator of the always_comb block, swapped, on a copy (never the committed file)
    perl -pe 'if (!$d && / = .*\S.* [+] / && s/ \+ / - /) { $d = 1 }' "${sv}" > "${WORK}/${g}/${top}.swap.sv"
    if cmp -s "${sv}" "${WORK}/${g}/${top}.swap.sv"; then
      perl -pe 'if (!$d && s/ \* / + /) { $d = 1 }' "${sv}" > "${WORK}/${g}/${top}.swap.sv"
    fi
    if cmp -s "${sv}" "${WORK}/${g}/${top}.swap.sv"; then
      perl -pe 'if (!$d && s/ - / + /) { $d = 1 }' "${sv}" > "${WORK}/${g}/${top}.swap.sv"
    fi
    swapped="$(diff "${sv}" "${WORK}/${g}/${top}.swap.sv" | sed -n 's/^> *//p' | head -1 || true)"
    [[ -n "${swapped}" ]] || { echo "[FAIL] ${g}: no operator to swap in ${sv}" >&2; exit 1; }
    verilate "${top}" "${WORK}/${g}/${top}.swap.sv" "${WORK}/${g}/tb.cpp" "${WORK}/${g}/obj_swap"
    if [[ "${MISMATCHES}" == 0 ]]; then
      echo "[FAIL] ${g}: the swapped operator \`${swapped}\` went unnoticed by the Verilator harness" >&2
      exit 1
    fi
    set +e
    LEC_OUT="$("${LEC}" "square-${g}" "${WORK}/${g}/${top}.swap.sv" "${lec}" --no-eqy "tooth" 2>&1)"
    LEC_RC=$?
    set -e
    if (( LEC_RC == 0 )) || ! grep -q "z3 says" <<< "${LEC_OUT}"; then
      echo "[FAIL] ${g}: the swapped operator \`${swapped}\` was not caught by the LEC:" >&2
      echo "${LEC_OUT}" | tail -5 >&2
      exit 1
    fi
    echo "  [6] swapped \`${swapped}\`: Verilator mismatches=${MISMATCHES}, LEC $(grep -o 'z3 says [a-z]*' <<< "${LEC_OUT}" | head -1), as they must"
  fi
done
echo "[PASS] hardware/gpu/square${STAGE:+ (stage ${STAGE})}${ONLY:+ (${ONLY})}"
