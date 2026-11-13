#!/usr/bin/env bash
# hardware/hvm: rung 2 of HARDWARE.md. Leaf books lowered to HVM2 nets (Obend.Hardware.Hvm), run by HVM2
# itself, against evalBookAt.
#
#   verify_hvm.sh                 the gate: [1] byte equality of each committed .hvm with obend-emit-hvm,
#                                 [2] the refused book is refused, [3] every vector of every book agrees
#                                 under `hvm run` (Rust) and `hvm run-c` (C) with the slots evalBookAt shows
#                                 (each probe run on the demand machine) and with the Lean model's own run,
#                                 [4] each planted rule makes at least one vector of each book disagree
#   verify_hvm.sh --plant NAME    tooth check on nets emitted with the planted rule NAME
#                                 (swapSwitch, addAsSub); passes (exit 0) iff every book catches it
#   verify_hvm.sh --stage N       only stage N of the gate (1-4)
#
# Every `hvm` run is bounded: 120 s for the real books (a timeout fails the gate), 30 s for a planted
# net (a planted rule on a recursive book can diverge; a timeout counts as a disagreement, i.e. caught).
#
# HVM2: `cargo install hvm` (2.0.22) or HVM_BIN. The CUDA runtime (`hvm run-cu`) needs an NVIDIA GPU;
# none of our machines has one, so this gate runs the Rust and C runtimes.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
EMIT="${OBEND_EMIT_HVM:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-hvm}"
HVM="${HVM_BIN:-$(command -v hvm || echo "${HOME}/tools/hvm/bin/hvm")}"
TIMEOUT="${TIMEOUT_BIN:-$(command -v timeout || command -v gtimeout || echo timeout)}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_hvm.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
BOOKS=(arith rec data)

STAGE=""
if [[ $# -gt 0 && "${1:-}" != "--plant" ]]; then
  if [[ "${1:-}" == "--stage" && $# -eq 2 ]]; then
    case "$2" in
      1|2|3|4) STAGE="$2" ;;
      *) echo "[FAIL] unknown --stage '$2' (expected 1, 2, 3, or 4)" >&2; exit 2 ;;
    esac
  else
    echo "[FAIL] usage: verify_hvm.sh [--plant NAME | --stage 1|2|3|4]" >&2
    exit 2
  fi
fi
if [[ "${1:-}" == "--plant" ]]; then
  [[ $# -eq 2 && -n "${2:-}" ]] || { echo "[FAIL] usage: verify_hvm.sh --plant NAME" >&2; exit 2; }
fi

[[ -x "${EMIT}" ]] || { echo "[FAIL] ${EMIT} missing: run \`lake build obend-emit-hvm\` in lean/" >&2; exit 1; }
[[ -x "${HVM}" ]] || { echo "[FAIL] no hvm binary (cargo install hvm, or set HVM_BIN)" >&2; exit 1; }

# compare SECS DIR RUNNER... : one line per disagreeing run (a run past SECS seconds disagrees);
# the count in MISMATCHES, the runs in CHECKED
compare() {
  local secs="$1" dir="$2"; shift 2
  MISMATCHES=0; CHECKED=0
  while IFS=$'\t' read -r file member args expected model; do
    for runner in "$@"; do
      got="$("${TIMEOUT}" "${secs}" "${HVM}" "${runner}" "${dir}/${file}" 2>&1 | sed -n 's/^Result: //p' || true)"
      CHECKED=$((CHECKED + 1))
      if [[ "${got}" != "${expected}" || "${model}" != "${expected}" ]]; then
        echo "  ${runner} ${member}(${args}): hvm=${got:-<no result>} evalBookAt=${expected} model=${model}"
        MISMATCHES=$((MISMATCHES + 1))
        [[ -n "${FIRST_ONLY:-}" ]] && return 0
      fi
    done
  done < "${dir}/expected.tsv"
  return 0
}

if [[ "${1:-}" == "--plant" ]]; then
  [[ $# -eq 2 && -n "${2:-}" ]] || { echo "[FAIL] usage: verify_hvm.sh --plant NAME" >&2; exit 2; }
  plant="$2"
  total=0
  missed=0
  for book in "${BOOKS[@]}"; do
    "${EMIT}" "${book}" --vectors "${WORK}/${book}" --plant "${plant}"
    compare 30 "${WORK}/${book}" run
    if (( MISMATCHES == 0 )); then
      echo "[FAIL] planted ${plant} went unnoticed on ${book}: the comparison has no teeth" >&2
      missed=$((missed + 1))
    fi
    total=$((total + MISMATCHES))
  done
  if (( missed > 0 || total == 0 )); then
    exit 1
  fi
  echo "[PASS] planted ${plant} caught across all ${#BOOKS[@]} books (${total} disagreeing runs)"
  exit 0
fi

run_stage() { [[ -z "${STAGE}" || "${STAGE}" == "$1" ]]; }

if run_stage 1; then
echo "=== [1/4] byte equality: committed .hvm == obend-emit-hvm ==="
for book in "${BOOKS[@]}"; do
  "${EMIT}" "${book}" --out "${WORK}/${book}.hvm"
  if ! cmp -s "${WORK}/${book}.hvm" "${SCRIPT_DIR}/${book}.hvm"; then
    echo "[FAIL] ${book}.hvm differs from \`obend-emit-hvm ${book}\` (regenerate; do not hand-edit)" >&2
    diff "${WORK}/${book}.hvm" "${SCRIPT_DIR}/${book}.hvm" | head -20 >&2 || true
    exit 1
  fi
  echo "  ${book}.hvm: identical; $("${TIMEOUT}" 120 "${HVM}" run "${SCRIPT_DIR}/${book}.hvm" | head -1)"
done
fi

if run_stage 2; then
echo "=== [2/4] the refused book is refused by name ==="
set +e; out="$("${EMIT}" refused)"; rc=$?; set -e
[[ ${rc} -eq 3 && "${out}" == refused:* ]] || { echo "[FAIL] book 'refused' was not refused (rc=${rc}): ${out}" >&2; exit 1; }
echo "  ${out}"
fi

if run_stage 3; then
echo "=== [3/4] hvm run / hvm run-c against evalBookAt and the model ==="
for book in "${BOOKS[@]}"; do
  "${EMIT}" "${book}" --vectors "${WORK}/vec-${book}" | sed 's/^/  /'
  compare 120 "${WORK}/vec-${book}" run run-c
  if (( MISMATCHES > 0 )); then
    echo "[FAIL] ${book}: ${MISMATCHES} of ${CHECKED} runs disagree" >&2
    exit 1
  fi
  echo "  ${book}: ${CHECKED} runs agree ($(wc -l < "${WORK}/vec-${book}/expected.tsv" | tr -d ' ') vectors x {run, run-c})"
done
fi

if run_stage 4; then
echo "=== [4/4] teeth: each planted rule must make each book's comparison fail ==="
for plant in swapSwitch addAsSub; do
  for book in "${BOOKS[@]}"; do
    "${EMIT}" "${book}" --vectors "${WORK}/plant-${plant}-${book}" --plant "${plant}" >/dev/null
    FIRST_ONLY=1 compare 30 "${WORK}/plant-${plant}-${book}" run >/dev/null
    if (( MISMATCHES == 0 )); then
      echo "[FAIL] planted ${plant} went unnoticed on ${book}: the comparison has no teeth" >&2
      exit 1
    fi
    echo "  ${plant} on ${book}: caught at run ${CHECKED} (stops at the first disagreement)"
  done
done
fi
echo "[PASS] hardware/hvm${STAGE:+ (stage ${STAGE})}"
