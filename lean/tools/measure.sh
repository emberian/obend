#!/bin/bash
# Step-4 measurement (2026-10-30): after a green build, (1) a private proof edit in Adequacy, (2) a
# definitional change in Term; record which modules rebuild and the wall time of each `lake build`.
# Run from lean/ as `tools/measure.sh`. Reverts both edits. One measurement (docs/MEASURE-20261030.log), not a harness.
set -u
export LEAN_NUM_THREADS=2
LOG=docs/MEASURE-$(date +%Y%m%d).log
: > $LOG
t() { local s=$(date +%s); "$@" > /tmp/obend-measure.out 2>&1; local e=$(date +%s); echo "wall ${e}-${s} = $((e-s))s" >> $LOG; grep -E "^✔|^✖|Build completed|error" /tmp/obend-measure.out | sed 's/ (.*//' >> $LOG; }
echo "== 0. baseline: lake build with nothing changed" >> $LOG; t lake build
echo "== 1. private proof edit: a trivial private theorem appended to Obend/Core/Proofs/Adequacy.lean" >> $LOG
cp Obend/Core/Proofs/Adequacy.lean /tmp/Adequacy.bak
printf '\n-- measurement edit (reverted)\ntheorem measurement_private_tooth : (1 : Nat) + 1 = 2 := rfl\n' >> Obend/Core/Proofs/Adequacy.lean
t lake build
cp /tmp/Adequacy.bak Obend/Core/Proofs/Adequacy.lean
echo "== 2. definitional change: an exposed public def appended to Obend/Core/Term.lean (inside its exposed section)" >> $LOG
cp Obend/Core/Term.lean /tmp/Term.bak
python3 - <<'PY'
p='Obend/Core/Term.lean'; s=open(p).read()
i=s.rindex('\nend Obend.Core.Term')
s=s[:i]+'\n/-- measurement edit (reverted) -/\ndef measurementScalar : Term → Bool\n  | .nat _ | .boolean _ | .label _ => true\n  | _ => false\n'+s[i:]
open(p,'w').write(s)
PY
t lake build
cp /tmp/Term.bak Obend/Core/Term.lean
echo "== 3. restore: lake build after reverting both" >> $LOG; t lake build
echo done >> $LOG
