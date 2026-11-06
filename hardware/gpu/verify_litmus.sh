#!/usr/bin/env bash
# hardware/gpu: rung G4 of review/GPU-PROGRAM-20261105.md. The scoped memory model of our GPUs
# (Obend.Hardware.Gpu.Memory) against the Vulkan model as Dartagnan executes it and against the devices.
#
#   verify_litmus.sh                the gate: [1] the Dartagnan litmus files under litmus/dartagnan/ are the
#                                   checker's, byte for byte, and Dartagnan's verdict under cat/vulkan.cat
#                                   (regenerated when Dartagnan is installed, else the committed
#                                   verdicts.tsv) equals the checker's on every shape and outcome; [2] every
#                                   outcome class a device showed (litmus/results/*.tsv) is allowed by the
#                                   checker, and every allowed weak class is observed on some device or
#                                   recorded in results/STRONGER.tsv; [3] every planted axiom change makes
#                                   [2] fail; [4] the section functor restricts along scope inclusion on
#                                   every shape (obend-litmus-check restrict)
#   verify_litmus.sh --plant NAME   only [2], with the checker's axioms planted (dropCoherence,
#                                   dropBarrierSync, sequential); it fails, and says where
#   verify_litmus.sh --stage N      only stage N (1-4)
#
# Running the suite on a device is not part of the gate (the tables are committed with their seed and
# budget): `obend-gpu-litmus litmus --out litmus/results/<device>-<driver>.tsv` in runner/ (see litmus/README.md).
# Dartagnan: DAT3M_HOME, or ~/tools/dartagnan, holding dartagnan.jar, libs/, cat/ and compilation.yml
# (github.com/hernanponcedeleon/Dat3M, `mvn clean install -DskipTests`); needs a JRE 17+.
#
# Build: `lake build obend-litmus-check` in lean/.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
CHECK="${OBEND_LITMUS_CHECK:-${REPO_ROOT}/lean/.lake/build/bin/obend-litmus-check}"
LITMUS="${SCRIPT_DIR}/litmus"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_litmus.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
DAT3M="${DAT3M_HOME:-${HOME}/tools/dartagnan}"

[[ -x "${CHECK}" ]] || { echo "[FAIL] ${CHECK} missing: run \`lake build obend-litmus-check\` in lean/" >&2; exit 1; }

"${CHECK}" table > "${WORK}/table.tsv"

if [[ "${1:-}" == "--plant" ]]; then
  plant="${2:?--plant NAME}"
  "${CHECK}" table --plant "${plant}" > "${WORK}/planted.tsv"
  if python3 -I "${LITMUS}/gate.py" devices "${WORK}/planted.tsv" "${LITMUS}/results" 2>"${WORK}/why.txt"; then
    echo "[PASS] planted ${plant} went unnoticed (the device tables have no teeth here)"
    exit 0
  fi
  echo "[FAIL] planted ${plant}:" >&2
  cat "${WORK}/why.txt" >&2
  exit 1
fi

STAGE=""
if [[ "${1:-}" == "--stage" ]]; then STAGE="${2:?--stage N}"; fi
run_stage() { [[ -z "${STAGE}" || "${STAGE}" == "$1" ]]; }

if run_stage 1; then
echo "=== [1/4] the referent: Dartagnan under cat/vulkan.cat agrees with the checker on every shape and outcome ==="
"${CHECK}" dartagnan --out "${WORK}/dartagnan" | sed 's/^/  /'
for f in "${WORK}"/dartagnan/*.litmus; do
  b="$(basename "${f}")"
  if ! cmp -s "${f}" "${LITMUS}/dartagnan/${b}"; then
    echo "[FAIL] litmus/dartagnan/${b} differs from the checker's (regenerate; do not hand-edit)" >&2
    diff "${f}" "${LITMUS}/dartagnan/${b}" | head -10 >&2 || true
    exit 1
  fi
done
for f in "${LITMUS}"/dartagnan/*.litmus; do
  b="$(basename "${f}")"
  [[ -f "${WORK}/dartagnan/${b}" ]] || { echo "[FAIL] litmus/dartagnan/${b} is not the checker's" >&2; exit 1; }
done
if [[ -f "${DAT3M}/dartagnan.jar" ]] && command -v java >/dev/null; then
  echo "  running Dartagnan ($(java -version 2>&1 | head -1 | tr -d '"'))"
  : > "${WORK}/verdicts.tsv"
  for f in "${LITMUS}"/dartagnan/*.litmus; do
    r="$(cd "${DAT3M}" && DAT3M_HOME="${DAT3M}" java -jar dartagnan.jar cat/vulkan.cat "${f}" 2>&1 | grep -E '^Result:' | awk '{print $2}')"
    printf '%s\t%s\n' "$(basename "${f}")" "${r:-ERROR}" >> "${WORK}/verdicts.tsv"
  done
  if ! cmp -s "${WORK}/verdicts.tsv" "${LITMUS}/dartagnan/verdicts.tsv"; then
    echo "[FAIL] Dartagnan's verdicts differ from the committed litmus/dartagnan/verdicts.tsv:" >&2
    diff "${WORK}/verdicts.tsv" "${LITMUS}/dartagnan/verdicts.tsv" | head -20 >&2 || true
    exit 1
  fi
  echo "  verdicts regenerated and identical to the committed table"
else
  echo "  Dartagnan not installed here (DAT3M_HOME or ~/tools/dartagnan): the committed verdicts.tsv stands in"
fi
if ! python3 -I "${LITMUS}/gate.py" dartagnan "${WORK}/table.tsv" "${WORK}/dartagnan/index.tsv" "${LITMUS}/dartagnan/verdicts.tsv"; then
  echo "[FAIL] the checker and Dartagnan disagree" >&2
  exit 1
fi
echo "  $(($(wc -l < "${WORK}/dartagnan/index.tsv") - 1)) outcomes: Dartagnan and the checker agree on every one"
fi

if run_stage 2; then
echo "=== [2/4] the devices: observed classes allowed; allowed weak classes observed or recorded stronger ==="
if ! python3 -I "${LITMUS}/gate.py" devices "${WORK}/table.tsv" "${LITMUS}/results"; then
  echo "[FAIL] the device tables and the checker disagree" >&2
  exit 1
fi
for t in "${LITMUS}"/results/*.tsv; do
  [[ "$(basename "${t}")" == STRONGER.tsv ]] && continue
  echo "  $(basename "${t}" .tsv): $(grep -v '^#' "${t}" | awk -F'\t' 'NR>1 && $7!="0" && $7!="-" {printf "%s ", $1}' | sed 's/ $//')"
done
fi

if run_stage 3; then
echo "=== [3/4] teeth: each planted axiom change must make stage 2 fail ==="
for plant in dropCoherence dropBarrierSync sequential; do
  "${CHECK}" table --plant "${plant}" > "${WORK}/planted-${plant}.tsv"
  if python3 -I "${LITMUS}/gate.py" devices "${WORK}/planted-${plant}.tsv" "${LITMUS}/results" 2>"${WORK}/why-${plant}.txt"; then
    echo "[FAIL] planted ${plant} went unnoticed: the device tables have no teeth" >&2
    exit 1
  fi
  echo "  ${plant}: caught ($(head -1 "${WORK}/why-${plant}.txt" | sed 's/^ *//'))"
done
fi

if run_stage 4; then
echo "=== [4/4] sections restrict along scope inclusion on every shape ==="
"${CHECK}" restrict || { echo "[FAIL] a device witness does not restrict to a consistent section" >&2; exit 1; }
fi
echo "[PASS] hardware/gpu/litmus${STAGE:+ (stage ${STAGE})}"
