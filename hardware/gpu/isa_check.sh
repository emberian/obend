#!/usr/bin/env bash
# hardware/gpu/isa_check.sh: rung G2 of review/GPU-PROGRAM-20261105.md. RADV's final RDNA2 machine code
# (hardware/gpu/isa/<graph>.txt, from verify_gpu.sh stage 4) read by Lean with a decoder generated from
# AMD's machine-readable ISA (hardware/gpu/rdna2/) and run on the wave model (Obend.Hardware.Gpu.Rdna2).
#
#   isa_check.sh              the gate: [1] the generated Lean data modules are byte-identical to the
#                             generator's output from the committed XML; [2] on every instruction of every
#                             dump, the Lean decoder's text equals `llvm-mc --disassemble` (LLVM 19,
#                             gfx1031, wave64); [3] every bit of every instruction's machine code, flipped,
#                             changes the decoding or fails it, unless the bit lies in no field the
#                             specification names; [4] every graph's dumped programs, run on the model from
#                             each vector's inputs, give expected.tsv, and a planted bit flip in one store
#                             is caught
#   isa_check.sh --stage N    only stage N (1-4)
#
# Needs llvm-mc (LLVM_MC, default /usr/lib/llvm-19/bin/llvm-mc; hbox) and `lake build obend-rdna2` in lean/.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
RDNA2="${OBEND_RDNA2:-${REPO_ROOT}/lean/.lake/build/bin/obend-rdna2}"
LLVM_MC="${LLVM_MC:-/usr/lib/llvm-19/bin/llvm-mc}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/isa_check.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
STAGE=""
if [[ "${1:-}" == "--stage" ]]; then STAGE="${2:?--stage N}"; fi
run_stage() { [[ -z "${STAGE}" || "${STAGE}" == "$1" ]]; }
[[ -x "${RDNA2}" ]] || { echo "[FAIL] ${RDNA2} missing: run \`lake build obend-rdna2\` in lean/" >&2; exit 1; }
mapfile -t DUMPS < <(ls "${SCRIPT_DIR}"/isa/*.txt)

if run_stage 1; then
echo "=== [1/4] the generated modules == gen_encodings.py on the committed XML ==="
mkdir -p "${WORK}/gen"
python3 -I "${SCRIPT_DIR}/rdna2/gen_encodings.py" "${SCRIPT_DIR}/rdna2/amdgpu_isa_rdna2.xml" "${WORK}/gen" | sed 's/^/  /'
for f in Encodings.lean Insts.lean; do
  cmp "${WORK}/gen/${f}" "${REPO_ROOT}/lean/Obend/Hardware/Gpu/Rdna2/${f}" || { echo "[FAIL] ${f} differs from the generator's output" >&2; exit 1; }
done
diff -r "${WORK}/gen/Insts" "${REPO_ROOT}/lean/Obend/Hardware/Gpu/Rdna2/Insts" >/dev/null || { echo "[FAIL] Insts/ differs from the generator's output" >&2; exit 1; }
echo "  identical"
fi

if run_stage 2; then
echo "=== [2/4] the decoder against llvm-mc on every instruction of every dump ==="
[[ -x "${LLVM_MC}" ]] || { echo "[FAIL] ${LLVM_MC} missing (LLVM 19 with the amdgcn target)" >&2; exit 1; }
total=0
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  python3 -I "${SCRIPT_DIR}/isa_words.py" "${d}" > "${WORK}/${g}.bytes"
  n=$(wc -l < "${WORK}/${g}.bytes")
  "${LLVM_MC}" --disassemble -triple=amdgcn-amd-amdhsa -mcpu=gfx1031 -mattr=+wavefrontsize64 < "${WORK}/${g}.bytes" 2>"${WORK}/${g}.mcerr" \
    | grep -v '^\s*\.' | sed 's/^\s*//' > "${WORK}/${g}.llvm"
  if [[ -s "${WORK}/${g}.mcerr" ]]; then echo "[FAIL] llvm-mc on ${g}:" >&2; head -3 "${WORK}/${g}.mcerr" >&2; exit 1; fi
  "${RDNA2}" decode "${d}" > "${WORK}/${g}.lean"
  if ! diff "${WORK}/${g}.llvm" "${WORK}/${g}.lean" > "${WORK}/${g}.diff"; then
    echo "[FAIL] ${g}: the Lean decoder and llvm-mc disagree (llvm <, lean >):" >&2
    head -12 "${WORK}/${g}.diff" >&2
    exit 1
  fi
  [[ "$(wc -l < "${WORK}/${g}.lean")" == "${n}" ]] || { echo "[FAIL] ${g}: ${n} instructions, $(wc -l < "${WORK}/${g}.lean") decoded lines" >&2; exit 1; }
  echo "  ${g}: ${n} instructions agree"
  total=$((total + n))
done
echo "  every instruction of every dump agrees"
fi

if run_stage 3; then
echo "=== [3/4] teeth: every bit of every instruction's machine code, flipped ==="
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  printf '  %s: ' "${g}"
  "${RDNA2}" flip "${d}" || exit 1
done
fi

if run_stage 4; then
echo "=== [4/4] the model: every graph's programs on every vector; a planted store flip caught ==="
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  "${RDNA2}" run "${SCRIPT_DIR}/graphs/${g}" | sed 's/^/  /' || exit 1
done
for g in diamond optic-mul optic-bilinear optic-linearmac; do
  # the first buffer_store of stage 0: VDATA's low bit (bit 40 of the instruction) names another register
  k=$(grep -n "" "${SCRIPT_DIR}/isa/${g}.txt" | sed -n '/## stage 0/,/## stage 1/p' | grep -c $'^\t\|^[0-9]*:\t' || true)
  idx=$(awk '/^## stage 0/{s=1; i=-1; next} /^## stage 1/{exit} s && /^\t/{i++; if ($0 ~ /buffer_store/) {print i; exit}}' "${SCRIPT_DIR}/isa/${g}.txt")
  "${RDNA2}" run "${SCRIPT_DIR}/graphs/${g}" --flip "0:${idx}:40" | sed 's/^/  /' || { echo "[FAIL] ${g}: a flipped store went unnoticed" >&2; exit 1; }
done
fi
echo "[PASS] hardware/gpu/isa_check.sh${STAGE:+ (stage ${STAGE})}"
