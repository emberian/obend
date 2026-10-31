#!/bin/bash
# The one-edit measurement (REPORT-20261030 §4; repeated 2026-11-01 after the tiers and the splits, and
# again after the expose confinement): after a green tier-1 build, (1) a private proof edit in
# Adequacy's largest piece, (2) an exposed def appended to Term, (3) a body edit of `checkExtension`,
# a definition of Check that is not exposed; record the rebuilt modules and the wall time of each
# tier-1 `lake build`.
# Run from lean/ as `tools/measure.sh`. Reverts both edits. One measurement, not a harness.
set -u
export LEAN_NUM_THREADS=2
LOG=docs/MEASURE-$(date +%Y%m%d).log
PIECE=Obend/Core/Proofs/Adequacy/Safety.lean
WORK=$(mktemp -d)
: > $LOG
t() { echo "load $(uptime | sed 's/.*averages: //')" >> $LOG; local s=$(date +%s); "$@" > $WORK/out 2>&1; local e=$(date +%s); echo "wall $((e-s))s" >> $LOG; grep -E "^(✔|⚠|✖)|Build completed|^error" $WORK/out | sed -E 's/^(.) \[[0-9]+\/[0-9]+\] /\1 /' >> $LOG; }
echo "== 0. baseline: lake build with nothing changed" >> $LOG; t lake build
echo "== 1. private proof edit: a trivial private theorem appended to $PIECE" >> $LOG
cp $PIECE $WORK/piece.bak
printf '\n-- measurement edit (reverted)\ntheorem measurement_private_tooth : (1 : Nat) + 1 = 2 := rfl\n' >> $PIECE
t lake build
cp $WORK/piece.bak $PIECE
echo "== 2. definitional change: an @[expose] def appended to Obend/Core/Term.lean" >> $LOG
cp Obend/Core/Term.lean $WORK/Term.bak
python3 - <<'PY'
p='Obend/Core/Term.lean'; s=open(p).read()
i=s.rindex('\nend Obend.Core.Term')
s=s[:i]+'\n/-- measurement edit (reverted) -/\n@[expose] def measurementScalar : Term → Bool\n  | .nat _ | .boolean _ | .label _ => true\n  | _ => false\n'+s[i:]
open(p,'w').write(s)
PY
t lake build
cp $WORK/Term.bak Obend/Core/Term.lean
t lake build
echo "== 3. body edit of an unexposed definition: checkExtension in Obend/Core/Check.lean (fuel + 0)" >> $LOG
cp Obend/Core/Check.lean $WORK/Check.bak
python3 - <<'PY'
p='Obend/Core/Check.lean'; s=open(p).read()
old='  let result ← check source context fuel\n  if ht : result.type = family.functionType futureSelf then'
assert s.count(old)==1
open(p,'w').write(s.replace(old,old.replace('context fuel','context (fuel + 0)')))
PY
t lake build
cp $WORK/Check.bak Obend/Core/Check.lean
echo "== 4. restore: lake build after reverting all three" >> $LOG; t lake build
rm -r $WORK
echo done >> $LOG
