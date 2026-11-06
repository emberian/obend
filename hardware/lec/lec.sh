#!/usr/bin/env bash
# hardware/lec/lec.sh <emit-target> <X.sv> <X_lec.smt2> [--eqy | --no-eqy <reason>]
#
# The LEC step every verify_*.sh runs after byte equality and before Verilator. X.sv is the
# emitter's output for <emit-target> (the caller has already compared its bytes).
#
#  1. `obend-emit-sv <target> --lec` regenerates the Lean half of the miter (Lean's model of the
#     RtlModule, `Obend.Hardware.YosysLec.emitYosysLecSmt2`); it must equal X_lec.smt2 byte for byte.
#  2. LEC: Yosys reads X.sv (`proc`, `write_smt2`), the Lean half is appended, and z3 must answer
#     unsat (bit-precise, or, when that does not finish, with multiplication uninterpreted; see
#     `decide`): every output and every next register value of the module Yosys read agrees with
#     Lean's model, for every input and register state.
#  3. The same query on a copy of X.sv with bit 0 of one output flipped must answer
#     sat; the counterexample is printed.
#  4. With --eqy: EQY proves gold X.sv equivalent to gate X.gl.v, the gate-level netlist `synth`
#     makes of it, and fails on the mutated copy against the same gate netlist.
#
# Tools: yosys and z3 from PATH or the YosysHQ OSS CAD Suite (OSS_CAD, default
# /Users/ember/tools/oss-cad-suite); eqy from the suite.
set -euo pipefail

target="$1"; shift
sv="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"; lec="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"; shift 2
mode="${1:---no-eqy}"; reason="${2:-}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
EMIT="${OBEND_EMIT_SV:-${REPO_ROOT}/lean/.lake/build/bin/obend-emit-sv}"
OSS_CAD="${OSS_CAD:-/Users/ember/tools/oss-cad-suite}"
YOSYS="${YOSYS_BIN:-${OSS_CAD}/bin/yosys}"
EQY="${EQY_BIN:-${OSS_CAD}/bin/eqy}"
Z3="${Z3_BIN:-$(command -v z3 || echo /opt/homebrew/bin/z3)}"
for t in "${EMIT}" "${YOSYS}" "${Z3}"; do
  [[ -x "${t}" ]] || { echo "[FAIL] lec: ${t} not found (lake build obend-emit-sv; OSS CAD Suite under ${OSS_CAD})" >&2; exit 1; }
done

top="$(sed -n 's/^module \([A-Za-z_][A-Za-z0-9_]*\).*/\1/p' "${sv}" | head -1)"
work="$(mktemp -d "${TMPDIR:-/tmp}/obend-lec-${top}.XXXXXX")"
trap 'rm -rf "${work}"' EXIT

# 1. the Lean half reproduces from Lean
"${EMIT}" "${target}" --lec --out "${work}/${top}_lec.smt2" >/dev/null
if ! cmp -s "${work}/${top}_lec.smt2" "${lec}"; then
  echo "[FAIL] $(basename "${lec}") differs from \`obend-emit-sv ${target} --lec\` (regenerate; do not hand-edit)" >&2
  diff "${work}/${top}_lec.smt2" "${lec}" | head -20 >&2 || true
  exit 1
fi
echo "  $(basename "${lec}"): identical to obend-emit-sv ${target} --lec"

# Yosys's reading: the SystemVerilog frontend and `proc`, nothing that optimizes. `prep` would also
# run `wreduce` and `opt_expr`, which narrow multiplies and fold masks into slices; equivalent, but it
# moves the reading away from the text and defeats the multiplication abstraction below. The output
# wire of every flip-flop is kept, so a register no output reads still has its next value compared.
yosys_smt2() {  # $1 = .sv, $2 = out .smt2
  "${YOSYS}" -q -p "read_verilog -sv $1; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 $2"
}

# One query, decided twice if need be. First as written, with a time limit (LEC_SECS, default 60).
# If z3 does not answer in time, again with every multiplication uninterpreted: each `bvmul` of
# width W, in both halves, becomes the same free function |lec_mul_W|. An `unsat` there is a proof
# for every interpretation of multiplication, so for the real one; z3 then needs only to see that the
# two sides multiply equal operands, not to bit-blast two multipliers. A `sat` there is reported as
# undecided, never as a pass; so is a timeout of this second query, which has no limit unless
# LEC_ABS_SECS is set (the square gate's tooth sets it). Sets `verdict` (unsat, sat, undecided or z3's own words), `answer` (z3's
# whole output) and `how`; `$3` = 1 keeps the counterexample query.
decide() {  # $1 = yosys .smt2, $2 = lean half, $3 = with get-value (0/1)
  local lean="${work}/lean.smt2"
  if [[ "$3" == 1 ]]; then cp "$2" "${lean}"; else sed '/^; --- counterexample/,$d' "$2" > "${lean}"; fi
  answer="$(cat "$1" "${lean}" | "${Z3}" -T:"${LEC_SECS:-60}" -in 2>&1 || true)"
  how="bit-precise"; verdict="$(head -1 <<< "${answer}")"
  if [[ "${verdict}" == "unsat" || "${verdict}" == "sat" ]]; then return; fi
  perl -pe 's/^(\(define-fun \S+ \(\(state \S+\)\) \(_ BitVec (\d+)\) )\(bvmul /$1(|lec_mul_$2| /' "$1" > "${work}/abs.yosys.smt2"
  perl -pe 's/\(bvmul \(\(_ sign_extend 64\)/(|lec_mul_128| ((_ sign_extend 64)/g; s/\(bvmul /(|lec_mul_64| /g' "${lean}" > "${work}/abs.lean.smt2"
  answer="$( { grep -ohE 'lec_mul_[0-9]+' "${work}/abs.yosys.smt2" "${work}/abs.lean.smt2" | sort -u \
               | sed -E 's/lec_mul_([0-9]+)/(declare-fun |&| ((_ BitVec \1) (_ BitVec \1)) (_ BitVec \1))/'
             cat "${work}/abs.yosys.smt2" "${work}/abs.lean.smt2"; } | "${Z3}" ${LEC_ABS_SECS:+-T:"${LEC_ABS_SECS}"} -in 2>&1 || true)"
  how="multiplication uninterpreted"; verdict="$(head -1 <<< "${answer}")"
  if [[ "${verdict}" == "sat" || "${verdict}" == "timeout" || "${verdict}" == "unknown" ]]; then verdict="undecided"; fi
}

# 2. LEC of the emitted SV against Lean's model
yosys_smt2 "${sv}" "${work}/${top}.yosys.smt2"
decide "${work}/${top}.yosys.smt2" "${lec}" 0
if [[ "${verdict}" != "unsat" ]]; then
  echo "[FAIL] LEC ${top}: z3 says ${verdict} (${how}); Yosys's reading of $(basename "${sv}") is not shown equal to Lean's model" >&2
  decide "${work}/${top}.yosys.smt2" "${lec}" 1
  tail -n +2 <<< "${answer}" >&2
  exit 1
fi
echo "  LEC ${top}: unsat, ${how} (Yosys's reading of $(basename "${sv}") == Lean's model of the RtlModule)"

# 3. planted mutation: flip bit 0 of the first output's value in the always_comb block, on a copy
#    (never the committed file). An output, not a register: synthesis deletes a register no output
#    reads, so EQY could not see a mutation there; the LEC sees both.
awk '!done && /^    [A-Za-z_][A-Za-z0-9_]* = .*;$/ && !/^    w_[0-9]+ = / {
       sub(/ = /, " = 64'"'"'d1 ^ ("); sub(/;$/, ");"); done = 1 }
     { print }' "${sv}" > "${work}/${top}.mut.sv"
mutline="$(diff "${sv}" "${work}/${top}.mut.sv" | sed -n 's/^> *//p' | head -1 || true)"
[[ -n "${mutline}" ]] || { echo "[FAIL] lec: no line of ${sv} to mutate" >&2; exit 1; }
yosys_smt2 "${work}/${top}.mut.sv" "${work}/${top}.mut.yosys.smt2"
decide "${work}/${top}.mut.yosys.smt2" "${lec}" 1
if [[ "${verdict}" != "sat" && "${verdict}" != "undecided" ]]; then
  echo "[FAIL] LEC ${top}: the planted mutation \`${mutline}\` was not caught (z3: ${verdict}, ${how})" >&2
  exit 1
fi
echo "  mutation \`${mutline}\`: ${verdict}, as it must be (${how}); counterexample (false = the obligation that fails):"
cex="$(tail -n +2 <<< "${answer}" | tr -s ' \n' ' ')"
failing="$(grep -oE '\(\|lec_[a-z]+_[A-Za-z0-9_]+\| false\) \(\|rtl_[a-z]+_[A-Za-z0-9_]+\| [^)]*\) \(\|spec_[a-z]+_[A-Za-z0-9_]+\| [^)]*\)' <<< "${cex}" || true)"
if [[ -n "${failing}" ]]; then sed 's/^/    /' <<< "${failing}"; else echo "    ${cex}"; fi

# 4. EQY: the emitted SV against the gate-level netlist Yosys synthesizes from it
if [[ "${mode}" == "--no-eqy" ]]; then
  echo "  EQY ${top}: not run (${reason:-no reason given})"
  exit 0
fi
[[ -x "${EQY}" ]] || { echo "[FAIL] lec: ${EQY} not found" >&2; exit 1; }
"${YOSYS}" -q -p "read_verilog -sv ${sv}; synth -top ${top}; write_verilog -noattr ${work}/${top}.gl.v"
eqy_cfg() {  # $1 = gold .sv, $2 = cfg path
  cat > "$2" <<CFG
[gold]
read_verilog -sv $1
prep -top ${top}
# match only ports and flip-flop outputs: synthesis rewrites and shares the combinational wires
rename -hide t:\$dff %co x:* %% w:* %D

[gate]
read_verilog ${work}/${top}.gl.v
prep -top ${top}

[partition *]
amend *

[strategy sby]
use sby
depth 2
engine smtbmc bitwuzla
CFG
}
eqy_cfg "${sv}" "${work}/gold.eqy"
if ! (cd "${work}" && "${EQY}" -j "${EQY_JOBS:-4}" -d gold -f gold.eqy > gold.log 2>&1); then
  echo "[FAIL] EQY ${top}: $(basename "${sv}") is not equivalent to its synthesized netlist:" >&2
  grep -E "Failed|ERROR|Error" "${work}/gold.log" | head -20 >&2
  exit 1
fi
echo "  EQY ${top}: gold $(basename "${sv}") == gate ${top}.gl.v ($(grep -c 'Proved equivalence' "${work}/gold.log") partitions)"
eqy_cfg "${work}/${top}.mut.sv" "${work}/mut.eqy"
if (cd "${work}" && "${EQY}" -j "${EQY_JOBS:-4}" -d mut -f mut.eqy > mut.log 2>&1); then
  echo "[FAIL] EQY ${top}: the planted mutation \`${mutline}\` was proved equivalent to the original netlist" >&2
  exit 1
fi
echo "  EQY mutation \`${mutline}\`: not equivalent, as it must be:"
grep -E "Failed to prove|could not|Assert failed" "${work}/mut.log" | head -3 | sed 's/^/    /'
