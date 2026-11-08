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
#                             is caught; [5] gem5's Vega execute() bodies (rdna2/gem5_ref.cpp), on random
#                             register states, agree with the model's step on every twin instruction;
#                             [6] every stage's s_waitcnts are sufficient (Obend.Hardware.Gpu.Rdna2.Waitcnt:
#                             no load destination touched before a wait that covers it), and a dump with
#                             a vector (or scalar-only) load wait replaced by s_nop 0 is refused; [7] the
#                             certificate (Obend.Hardware.Gpu.Rdna2.Certified): the residual library
#                             Residuals.lean is byte-identical to `obend-rdna2 reslib` over every dump, every
#                             graph's dump is certified for every input (certifyNamed, the pinned check, with
#                             its time and peak memory), and a planted bit flip in a store is refused
#   isa_check.sh --stage N    only stage N (1-7)
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
EMIT="${OBEND_EMIT_GPU:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-gpu}"

# graph_dir NAME : committed directory, or a graph kept as a digest. OBEND_GPU_ARTIFACTS
# may name a read-only emission cache; every cached use checks the committed digest.
# Unset it to emit digest-backed graphs freshly under WORK.
graph_dir() {
  if [[ -d "${SCRIPT_DIR}/graphs/$1" ]]; then
    echo "${SCRIPT_DIR}/graphs/$1"
  elif [[ -n "${OBEND_GPU_ARTIFACTS:-}" ]]; then
    if ! (cd "${OBEND_GPU_ARTIFACTS}/$1" && sha256sum -c "${SCRIPT_DIR}/graphs/$1.sha256" >/dev/null); then
      echo "[FAIL] $1: cached artifacts do not match graphs/$1.sha256" >&2
      return 1
    fi
    echo "${OBEND_GPU_ARTIFACTS}/$1"
  else
    [[ -d "${WORK}/emit/$1" ]] || "${EMIT}" "$1" --out "${WORK}/emit/$1" >/dev/null || return 1
    echo "${WORK}/emit/$1"
  fi
}

if run_stage 1; then
echo "=== [1/7] the generated modules == gen_encodings.py on the committed XML ==="
mkdir -p "${WORK}/gen"
python3 -I "${SCRIPT_DIR}/rdna2/gen_encodings.py" "${SCRIPT_DIR}/rdna2/amdgpu_isa_rdna2.xml" "${WORK}/gen" | sed 's/^/  /'
for f in Encodings.lean Insts.lean; do
  cmp "${WORK}/gen/${f}" "${REPO_ROOT}/lean/Obend/Hardware/Gpu/Rdna2/${f}" || { echo "[FAIL] ${f} differs from the generator's output" >&2; exit 1; }
done
diff -r "${WORK}/gen/Insts" "${REPO_ROOT}/lean/Obend/Hardware/Gpu/Rdna2/Insts" >/dev/null || { echo "[FAIL] Insts/ differs from the generator's output" >&2; exit 1; }
echo "  identical"
fi

if run_stage 2; then
echo "=== [2/7] the decoder against llvm-mc on every instruction of every dump ==="
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
echo "=== [3/7] teeth: every bit of every instruction's machine code, flipped ==="
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  printf '  %s: ' "${g}"
  "${RDNA2}" flip "${d}" || exit 1
done
fi

if run_stage 4; then
echo "=== [4/7] the model: every graph's programs on every vector; a planted store flip caught ==="
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  dir="$(graph_dir "${g}")" || exit 1
  "${RDNA2}" run "${dir}" --isa "${d}" | sed 's/^/  /' || exit 1
done
# Keep the original store teeth and exercise each emitted SOAC's fold stage as well.
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  case "${g}" in diamond|optic-mul|optic-bilinear|optic-linearmac|soac-*) ;; *) continue ;; esac
  # Prefer a store after stage 0 for SOACs, so this changes a fold result rather than its input map.
  specs=$(awk -v graph="${g}" '
    /^## stage / {stage=$3; i=-1; next}
    /^\t/ {i++; if ($0 ~ /buffer_store/) {
      here=stage ":" i ":40";
      if (graph ~ /^soac-/ && stage > 0) fold=fold here "\n";
      else other=other here "\n";
    }}
    END {printf "%s%s", fold, other}' "${d}")
  if [[ -z "${specs}" ]]; then
    echo "  ${g}: no buffer store in the dump; no store mutation applies"
    continue
  fi
  dir="$(graph_dir "${g}")" || exit 1
  caught=""
  # A zero identity can make a register substitution observationally identical. Try the
  # remaining stores, still requiring one changed result for every graph with stores.
  while IFS= read -r spec; do
    if "${RDNA2}" run "${dir}" --isa "${d}" --flip "${spec}" >"${WORK}/store-plant.log" 2>&1; then
      sed 's/^/  /' "${WORK}/store-plant.log"
      caught=1
      break
    fi
  done <<< "${specs}"
  [[ -n "${caught}" ]] || { echo "[FAIL] ${g}: all store mutations went unnoticed" >&2; exit 1; }
done
# Embedded descriptors are executable data. An empty segment can leave a particular
# word unobserved, so try each word until a changed value or checked address is observed.
for d in "${DUMPS[@]}"; do
  if ! grep -q '^\.data ' "${d}"; then continue; fi
  g="$(basename "${d}" .txt)"
  dir="$(graph_dir "${g}")" || exit 1
  planted="${WORK}/${g}.pool-flip.txt"
  python3 -I - "${d}" >"${WORK}/pool-words" <<'PYPOOLWORDS'
import pathlib, sys
stage = None
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    if line.startswith("## stage "):
        stage = int(line.split()[2])
    elif line.startswith(".data "):
        words = line.split()
        for index in range(len(words) - 2):
            print(f"{stage}:{int(words[1]) + 4 * index}")
PYPOOLWORDS
  caught=""
  while IFS= read -r spec; do
    python3 -I - "${d}" "${planted}" "${spec}" <<'PYPOOL'
import pathlib, sys
lines = pathlib.Path(sys.argv[1]).read_text().splitlines()
target_stage, target_offset = map(int, sys.argv[3].split(":"))
stage = None
for i, line in enumerate(lines):
    if line.startswith("## stage "):
        stage = int(line.split()[2])
    elif stage == target_stage and line.startswith(".data "):
        words = line.split()
        offset = target_offset - int(words[1])
        if 0 <= offset < 4 * (len(words) - 2) and offset % 4 == 0:
            index = 2 + offset // 4
            words[index] = f"{int(words[index], 16) ^ 1:08x}"
            lines[i] = " ".join(words)
            break
else:
    raise SystemExit("no constant-data word at " + sys.argv[3])
pathlib.Path(sys.argv[2]).write_text("\n".join(lines) + "\n")
PYPOOL
    if "${RDNA2}" run "${dir}" --isa "${planted}" >"${WORK}/pool-plant.log" 2>&1; then
      continue
    fi
    # A parser error is not evidence that the pool's contents reach execution.
    if ! grep -Eq 'the model gives|load .*outside the memory' "${WORK}/pool-plant.log"; then
      cat "${WORK}/pool-plant.log" >&2
      echo "[FAIL] ${g}: pool corruption did not reach a value or address comparison" >&2; exit 1
    fi
    echo "  ${g}: corrupted embedded descriptor caught at stage ${spec%%:*}, byte offset ${spec#*:}"
    sed 's/^/    /' "${WORK}/pool-plant.log"
    caught=1
    break
  done <"${WORK}/pool-words"
  if [[ -z "${caught}" ]]; then
    # Mesa may retain a wholly unused pool after unrolling. Removing all data must
    # still replay correctly before classifying the pool as unread on these vectors.
    sed '/^\.data /d' "${d}" >"${WORK}/${g}.no-pool.txt"
    if ! "${RDNA2}" run "${dir}" --isa "${WORK}/${g}.no-pool.txt" >"${WORK}/pool-removed.log" 2>&1; then
      cat "${WORK}/pool-removed.log" >&2
      echo "[FAIL] ${g}: pool is read but all descriptor mutations went unnoticed" >&2; exit 1
    fi
    echo "  ${g}: retained pool unread on this vector suite (complete removal still replays); no pool negative applies"
  fi
done

fi
if run_stage 5; then
echo "=== [5/7] the model against gem5's Vega bodies on random register states ==="
python3 -I "${SCRIPT_DIR}/rdna2/gem5_ref.py" "${WORK}/gem5_vectors.tsv" --llvm-mc "${LLVM_MC}" | sed 's/^/  /'
cmp "${WORK}/gem5_vectors.tsv" "${SCRIPT_DIR}/rdna2/gem5_vectors.tsv" || { echo "[FAIL] rdna2/gem5_vectors.tsv differs from gem5_ref.py's output (regenerate; do not hand-edit)" >&2; exit 1; }
"${RDNA2}" gem5 "${SCRIPT_DIR}/rdna2/gem5_vectors.tsv" | sed 's/^/  /' || exit 1
fi
if run_stage 6; then
echo "=== [6/7] the waits: every load awaited before its destination is touched; a removed wait refused ==="
for d in "${DUMPS[@]}"; do
  "${RDNA2}" waitcnt "${d}" | sed 's/^/  /' || exit 1
done
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  # Empty folds may have no loads at all, or only scalar descriptor loads. Search every
  # stage, preferring the vector-load wait, and retain a scalar-wait negative when needed.
  spec=$(awk '
    /^## stage / {stage=$3; i=-1; next}
    /^\t/ {i++;
      if ($0 ~ /s_waitcnt vmcnt/ && vm == "") vm=stage ":" i;
      if ($0 ~ /s_waitcnt.*lgkmcnt/ && sm == "") sm=stage ":" i;
    }
    END {if (vm != "") print vm; else if (sm != "") print sm}' "${d}")
  if [[ -z "${spec}" ]]; then
    if grep -Eq '^[[:space:]]+(buffer_load|global_load|flat_load|ds_read|s_load|s_buffer_load)' "${d}"; then
      echo "[FAIL] ${g}: loads exist but there is no wait to mutate" >&2; exit 1
    fi
    echo "  ${g}: no loads in the dump; no load-wait mutation applies"
    continue
  fi
  "${RDNA2}" waitcnt "${d}" --nop "${spec}" | sed 's/^/  /' || {
    echo "[FAIL] ${g}: a removed wait went unnoticed" >&2; exit 1; }
done
fi
if run_stage 7; then
echo "=== [7/7] the certificate: every graph's machine code computes the graph for every input ==="
pairs=()
for d in "${DUMPS[@]}"; do pairs+=("$(basename "${d}" .txt)=${d}"); done
"${RDNA2}" reslib Obend.Hardware.Gpu.Rdna2.Residuals r "${pairs[@]}" > "${WORK}/Residuals.lean" 2> "${WORK}/reslib.log" \
  || { cat "${WORK}/reslib.log" >&2; exit 1; }
cmp "${WORK}/Residuals.lean" "${REPO_ROOT}/lean/Obend/Hardware/Gpu/Rdna2/Residuals.lean" \
  || { echo "[FAIL] Residuals.lean differs from obend-rdna2 reslib over the dumps (regenerate; do not hand-edit)" >&2; exit 1; }
echo "  Residuals.lean == obend-rdna2 reslib over every dump"
for d in "${DUMPS[@]}"; do
  g="$(basename "${d}" .txt)"
  /usr/bin/time -f "%e %M" -o "${WORK}/time" "${RDNA2}" cert "${g}" "${d}" > "${WORK}/cert.out" || { cat "${WORK}/cert.out"; exit 1; }
  read -r secs kb < "${WORK}/time"
  echo "  $(cat "${WORK}/cert.out"); ${secs} s, $((kb / 1024)) MB peak"
done
for g in diamond glmul-4 ntt-16 adjoint-square-bilinear; do
  # the first buffer_store of stage 0: VDATA's low bit (bit 40 of the instruction) names another register
  idx=$(awk '/^## stage 0/{s=1; i=-1; next} /^## stage 1/{exit} s && /^\t/{i++; if ($0 ~ /buffer_store/) {print i; exit}}' "${SCRIPT_DIR}/isa/${g}.txt")
  "${RDNA2}" cert "${g}" "${SCRIPT_DIR}/isa/${g}.txt" --flip "0:${idx}:40" | sed 's/^/  /' || { echo "[FAIL] ${g}: a flipped store was certified" >&2; exit 1; }
done
fi
echo "[PASS] hardware/gpu/isa_check.sh${STAGE:+ (stage ${STAGE})}"
