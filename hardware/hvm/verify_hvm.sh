#!/usr/bin/env bash
# hardware/hvm: rung 2 of HARDWARE.md. A Leaf book lowered to an HVM2 net (Obend.Hardware.Hvm), run by
# HVM2 itself, against evalBookAt.
#
#   verify_hvm.sh                 the gate: [1] byte equality of the committed .hvm with obend-emit-hvm,
#                                 [2] the refused book is refused, [3] every vector agrees under `hvm run`
#                                 (Rust) and `hvm run-c` (C) with evalBookAt (as a literal and run on the
#                                 demand machine) and with the Lean model's own run, [4] each planted rule
#                                 makes at least one vector disagree (else the comparison has no teeth)
#   verify_hvm.sh --plant NAME    only the comparison, on nets emitted with the planted rule NAME
#                                 (swapSwitch, addAsSub); it fails, and says where
#
# HVM2: `cargo install hvm` (2.0.22) or HVM_BIN. The CUDA runtime (`hvm run-cu`) needs an NVIDIA GPU;
# none of our machines has one, so this gate runs the Rust and C runtimes.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
EMIT="${OBEND_EMIT_HVM:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-hvm}"
HVM="${HVM_BIN:-$(command -v hvm || echo "${HOME}/tools/hvm/bin/hvm")}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_hvm.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
BOOK=arith

[[ -x "${EMIT}" ]] || { echo "[FAIL] ${EMIT} missing: run \`lake build obend-emit-hvm\` in lean/" >&2; exit 1; }
[[ -x "${HVM}" ]] || { echo "[FAIL] no hvm binary (cargo install hvm, or set HVM_BIN)" >&2; exit 1; }

# compare DIR RUNNER... : prints one line per disagreeing vector, returns the count in MISMATCHES
compare() {
  local dir="$1"; shift
  MISMATCHES=0; CHECKED=0
  while IFS=$'\t' read -r file member x sort lit machine model; do
    for runner in "$@"; do
      got="$("${HVM}" "${runner}" "${dir}/${file}" 2>&1 | sed -n 's/^Result: //p')"
      CHECKED=$((CHECKED + 1))
      if [[ "${got}" != "${machine}" || "${model}" != "${machine}" || ( "${lit}" != "-" && "${lit}" != "${machine}" ) ]]; then
        echo "  ${runner} ${member}(${x}) [${sort}]: hvm=${got:-<no result>} evalBookAt=${lit} machine=${machine} model=${model}"
        MISMATCHES=$((MISMATCHES + 1))
      fi
    done
  done < "${dir}/expected.tsv"
}

if [[ "${1:-}" == "--plant" ]]; then
  plant="${2:?--plant NAME}"
  "${EMIT}" "${BOOK}" --vectors "${WORK}/plant" --plant "${plant}"
  compare "${WORK}/plant" run
  if (( MISMATCHES > 0 )); then
    echo "[FAIL] planted ${plant}: ${MISMATCHES} of ${CHECKED} runs disagree with evalBookAt" >&2
    exit 1
  fi
  echo "[PASS] planted ${plant} went unnoticed (the comparison has no teeth here)"
  exit 0
fi

echo "=== [1/4] byte equality: committed ${BOOK}.hvm == obend-emit-hvm ${BOOK} ==="
"${EMIT}" "${BOOK}" --out "${WORK}/${BOOK}.hvm"
if ! cmp -s "${WORK}/${BOOK}.hvm" "${SCRIPT_DIR}/${BOOK}.hvm"; then
  echo "[FAIL] ${BOOK}.hvm differs from \`obend-emit-hvm ${BOOK}\` (regenerate; do not hand-edit)" >&2
  diff "${WORK}/${BOOK}.hvm" "${SCRIPT_DIR}/${BOOK}.hvm" | head -20 >&2 || true
  exit 1
fi
echo "  ${BOOK}.hvm: identical"
"${HVM}" run "${SCRIPT_DIR}/${BOOK}.hvm" | sed -n 's/^/  /p' | head -1

echo "=== [2/4] the refused book is refused by name ==="
set +e; out="$("${EMIT}" refused)"; rc=$?; set -e
[[ ${rc} -eq 3 && "${out}" == refused:* ]] || { echo "[FAIL] book 'refused' was not refused (rc=${rc}): ${out}" >&2; exit 1; }
echo "  ${out}"

echo "=== [3/4] hvm run / hvm run-c against evalBookAt and the model ==="
"${EMIT}" "${BOOK}" --vectors "${WORK}/vec" | sed 's/^/  /'
compare "${WORK}/vec" run run-c
if (( MISMATCHES > 0 )); then
  echo "[FAIL] ${MISMATCHES} of ${CHECKED} runs disagree" >&2
  exit 1
fi
echo "  ${CHECKED} runs agree ($(wc -l < "${WORK}/vec/expected.tsv" | tr -d ' ') vectors x {run, run-c})"

echo "=== [4/4] teeth: each planted rule must make the comparison fail ==="
for plant in swapSwitch addAsSub; do
  "${EMIT}" "${BOOK}" --vectors "${WORK}/plant-${plant}" --plant "${plant}" >/dev/null
  compare "${WORK}/plant-${plant}" run >/dev/null
  if (( MISMATCHES == 0 )); then
    echo "[FAIL] planted ${plant} went unnoticed: the comparison has no teeth" >&2
    exit 1
  fi
  echo "  ${plant}: ${MISMATCHES} of ${CHECKED} runs disagree (caught)"
done
echo "[PASS] hardware/hvm"
