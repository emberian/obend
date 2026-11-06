#!/usr/bin/env bash
# hardware/gpu: rung G1 of review/GPU-PROGRAM-20261105.md. StrictOpenHypergraphs lowered to compute
# shaders, one dispatch per wavefront stage (Obend.Hardware.Gpu), run on a GPU through wgpu against
# Obend.Hardware.Gpu.runProgram.
#
#   verify_gpu.sh                 the gate: [1] byte equality of every committed plan, shader and
#                                 expected.tsv with obend-emit-gpu (a graph committed as graphs/<g>.sha256
#                                 instead of a directory is regenerated and its digests compared; the
#                                 65536-point NTT's plan is too large to commit), [2] every vector of every
#                                 graph agrees on the device, with the dispatch time per vector printed and
#                                 not gated, [3] each planted shader rule makes at least one graph's
#                                 comparison fail, [4] with Mesa's RADV, the final ISA of every stage is
#                                 extracted under isa/ with its machine code and resource usage
#                                 (isa_extract.py: one program per stage, at least one 64-bit store)
#   verify_gpu.sh --plant NAME    only the comparison, on shaders emitted with the planted rule NAME
#                                 (addAsSub, swapMux); it fails, and says where
#   verify_gpu.sh --stage N       only stage N of the gate (1-4)
#   verify_gpu.sh --digest NAME   write graphs/NAME.sha256 from a fresh emission (for a graph kept as a digest)
#
# The device: GPU_ADAPTER (a substring of the adapter's name or driver, e.g. radv, "6750", Apple) picks
# it; unset, the first non-CPU adapter wgpu finds. On Linux, if Mesa's radeon ICD is installed it is
# selected (VK_ICD_FILENAMES) unless GPU_ICD=any, so that stage 4 can read RADV's shader dump; the
# AMDVLK driver on the same card runs the same shaders but dumps nothing. The device must offer 64-bit
# integers in shaders (wgpu SHADER_INT64); hbox's RX 6750 XT and Apple silicon do.
#
# Build: `lake build obend-emit-gpu` in lean/; `cargo build --release` in hardware/gpu/runner/.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
EMIT="${OBEND_EMIT_GPU:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-gpu}"
RUN="${OBEND_GPU_RUN:-${SCRIPT_DIR}/runner/target/release/obend-gpu-run}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_gpu.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
RADEON_ICD=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json

[[ -x "${EMIT}" ]] || { echo "[FAIL] ${EMIT} missing: run \`lake build obend-emit-gpu\` in lean/" >&2; exit 1; }
[[ -x "${RUN}" ]] || { echo "[FAIL] ${RUN} missing: run \`cargo build --release\` in hardware/gpu/runner/" >&2; exit 1; }

if [[ "$(uname -s)" == Linux && -r "${RADEON_ICD}" && "${GPU_ICD:-radv}" != any ]]; then
  export VK_ICD_FILENAMES="${RADEON_ICD}"
fi
ADAPTER_ARGS=()
[[ -n "${GPU_ADAPTER:-}" ]] && ADAPTER_ARGS=(--adapter "${GPU_ADAPTER}")

mapfile -t GRAPHS < <("${EMIT}" list)
if command -v sha256sum >/dev/null 2>&1; then SHA=(sha256sum); else SHA=(shasum -a 256); fi

# graph_dir NAME : the committed directory, or a fresh emission under WORK for a graph kept as a digest
graph_dir() {
  if [[ -d "${SCRIPT_DIR}/graphs/$1" ]]; then
    echo "${SCRIPT_DIR}/graphs/$1"
  else
    [[ -d "${WORK}/emit/$1" ]] || "${EMIT}" "$1" --out "${WORK}/emit/$1" >/dev/null
    echo "${WORK}/emit/$1"
  fi
}

if [[ "${1:-}" == "--digest" ]]; then
  g="${2:?--digest NAME}"
  "${EMIT}" "${g}" --out "${WORK}/digest/${g}" | sed 's/^/  /'
  (cd "${WORK}/digest/${g}" && "${SHA[@]}" expected.tsv plan.json stage_*.wgsl) > "${SCRIPT_DIR}/graphs/${g}.sha256"
  echo "[PASS] wrote graphs/${g}.sha256"
  exit 0
fi

# run_graph DIR : the device against expected.tsv; output in RUN_OUT, status in RUN_RC
run_graph() {
  set +e
  RUN_OUT="$("${RUN}" "$1" "${ADAPTER_ARGS[@]}" 2>"${WORK}/run.err")"
  RUN_RC=$?
  set -e
}

if [[ "${1:-}" == "--plant" ]]; then
  plant="${2:?--plant NAME}"
  "${EMIT}" all --out "${WORK}/plant" --plant "${plant}" >/dev/null
  caught=0
  for g in "${GRAPHS[@]}"; do
    run_graph "${WORK}/plant/${g}"
    if (( RUN_RC != 0 )); then
      echo "  ${g}: caught"; echo "${RUN_OUT}" | sed 's/^/    /' | head -4
      caught=$((caught + 1))
    fi
  done
  if (( caught > 0 )); then
    echo "[FAIL] planted ${plant}: ${caught} of ${#GRAPHS[@]} graphs disagree with runProgram" >&2
    exit 1
  fi
  echo "[PASS] planted ${plant} went unnoticed (the comparison has no teeth here)"
  exit 0
fi

STAGE=""
if [[ "${1:-}" == "--stage" ]]; then STAGE="${2:?--stage N}"; fi
run_stage() { [[ -z "${STAGE}" || "${STAGE}" == "$1" ]]; }

if run_stage 1; then
echo "=== [1/4] byte equality: committed plan, shaders and expected.tsv == obend-emit-gpu ==="
"${EMIT}" all --out "${WORK}/emit" | sed 's/^/  /'
for g in "${GRAPHS[@]}"; do
  if [[ -d "${SCRIPT_DIR}/graphs/${g}" ]]; then
    if ! diff -r "${WORK}/emit/${g}" "${SCRIPT_DIR}/graphs/${g}" >"${WORK}/diff.txt"; then
      echo "[FAIL] graphs/${g} differs from \`obend-emit-gpu ${g}\` (regenerate; do not hand-edit)" >&2
      head -20 "${WORK}/diff.txt" >&2
      exit 1
    fi
  elif [[ -f "${SCRIPT_DIR}/graphs/${g}.sha256" ]]; then
    if ! (cd "${WORK}/emit/${g}" && "${SHA[@]}" -c --quiet "${SCRIPT_DIR}/graphs/${g}.sha256" >"${WORK}/diff.txt" 2>&1); then
      echo "[FAIL] graphs/${g}.sha256 differs from \`obend-emit-gpu ${g}\` (verify_gpu.sh --digest ${g}; do not hand-edit)" >&2
      head -20 "${WORK}/diff.txt" >&2
      exit 1
    fi
    echo "  ${g}: digests identical (kept as graphs/${g}.sha256)"
  else
    echo "[FAIL] graphs/${g}: neither a directory nor a digest is committed" >&2
    exit 1
  fi
done
echo "  ${#GRAPHS[@]} graphs identical"
fi

if run_stage 2; then
echo "=== [2/4] the device against runProgram ==="
for g in "${GRAPHS[@]}"; do
  run_graph "$(graph_dir "${g}")"
  echo "${RUN_OUT}" | sed 's/^/  /'
  if (( RUN_RC != 0 )); then
    echo "[FAIL] ${g}: $(cat "${WORK}/run.err")" >&2
    exit 1
  fi
done
fi

if run_stage 3; then
echo "=== [3/4] teeth: each planted rule must make some graph's comparison fail ==="
for plant in addAsSub swapMux; do
  "${EMIT}" all --out "${WORK}/plant-${plant}" --plant "${plant}" >/dev/null
  caught=""
  for g in "${GRAPHS[@]}"; do
    run_graph "${WORK}/plant-${plant}/${g}"
    if (( RUN_RC != 0 )); then caught="${caught} ${g}"; fi
  done
  if [[ -z "${caught}" ]]; then
    echo "[FAIL] planted ${plant} went unnoticed on every graph: the comparison has no teeth" >&2
    exit 1
  fi
  echo "  ${plant}: caught on${caught}"
done
fi

if run_stage 4; then
echo "=== [4/4] the ISA: RADV's final assembly and resource usage of every stage, under isa/ ==="
probe="$("${RUN}" --list-adapters 2>/dev/null | grep -i "driver=radv" || true)"
if [[ "$(uname -s)" != Linux || -z "${probe}" ]]; then
  echo "  skipped: no RADV adapter here (the dump is Mesa's); the shaders ran on: $("${RUN}" --list-adapters 2>/dev/null | head -1)"
else
  mkdir -p "${SCRIPT_DIR}/isa"
  adapter="$(echo "${probe}" | head -1 | sed 's/ type=.*//')"
  for g in "${GRAPHS[@]}"; do
    dir="$(graph_dir "${g}")"
    RADV_DEBUG=shaders,shaderstats "${RUN}" "${dir}" --adapter radv >/dev/null 2>"${WORK}/isa-${g}.txt" || {
      echo "[FAIL] ${g} under RADV_DEBUG=shaders" >&2; exit 1; }
    echo "  ${g}:"
    python3 -I "${SCRIPT_DIR}/isa_extract.py" "${WORK}/isa-${g}.txt" "${dir}/plan.json" \
      "${SCRIPT_DIR}/isa/${g}.txt" "${adapter}" || exit 1
  done
fi
fi
echo "[PASS] hardware/gpu${STAGE:+ (stage ${STAGE})}"
