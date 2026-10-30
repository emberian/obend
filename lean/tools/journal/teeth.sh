#!/bin/bash
# Teeth for the journal (brief item 4). Run from lean/ on a green tree; exits non-zero on a failed tooth.
#   (a) change a definition body a theorem's proof unfolds but its statement never mentions
#       (`Obend.Slot.Protocol.Coin.answer`, reached only by the proof of `Coin.no_foresight`): the
#       journal lists `no_foresight` under PROOF-CITED and nowhere else.
#   (b) swap the order of two independent declarations (`dead_eq_nil_iff`, `mem_dead_iff` in
#       `Obend/Slot.lean`): the journal flags nothing.
# Each edit is applied and inverted by exact text, so the files are as they were when this exits.
# The teeth live in the `Obend.Slot` subtree: only its modules are built and exported (`--only`), so a
# red module elsewhere in the tree (another lane's proof in progress) does not stop them.
set -u
export LEAN_NUM_THREADS=2
OUT=${OUT:?set OUT to a scratch directory for the logs}
mkdir -p "$OUT"
J=tools/journal
PROT=Obend/Slot/Protocol.lean
SLOT=Obend/Slot.lean

A_OLD='  | .revealed, () => some (.ret c)'
A_NEW='  | .revealed, () => id (some (.ret c))'
B_FIRST='theorem dead_eq_nil_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    S.dead holds c = [] ↔ ∀ f ∈ S.supports c, holds f = true := by
  simp [Slot.dead, List.filter_eq_nil_iff]
'
B_SECOND='theorem mem_dead_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) (f : Fact) :
    f ∈ S.dead holds c ↔ f ∈ S.supports c ∧ holds f = false := by
  simp [Slot.dead, List.mem_filter]
'

replace_once() {  # file old new: exactly one occurrence, or fail
  python3 - "$1" "$2" "$3" <<'PY'
import sys
p, old, new = sys.argv[1:4]
s = open(p).read()
assert s.count(old) == 1, (p, s.count(old))
open(p, 'w').write(s.replace(old, new))
PY
}
restore() {
  grep -qF "$A_NEW" "$PROT" && replace_once "$PROT" "$A_NEW" "$A_OLD"
  grep -qF "$(printf '%s' "$B_SECOND" | head -1)" "$SLOT" && python3 - "$SLOT" "$B_FIRST" "$B_SECOND" <<'PY'
import sys
p, first, second = sys.argv[1:4]
s = open(p).read()
if s.count(second + '\n' + first) == 1:
    open(p, 'w').write(s.replace(second + '\n' + first, first + '\n' + second))
PY
  rm -f "$J"/env-teeth-*.jsonl
}
trap restore EXIT

fail=0
check() {  # $1 description, $2 condition exit code
  if [ "$2" -eq 0 ]; then echo "PASS: $1"; else echo "FAIL: $1"; fail=1; fi
}
section() {  # $1 report file, $2 section title: the names listed under it (indented one level, not `dead:` lines)
  awk -v t="$2" '
    /^[^ ]/ { on = ($0 ~ "^" t " \\(") }
    on && /^  [^ ]/ { print $0 }' "$1" | sed 's/^  //'
}

SLOT_TARGETS="+Obend.Slot +Obend.Slot.Protocol +Obend.Slot.Calculus +Obend.Slot.Core4 +Obend.Slot.Proofs.ProtocolTyping +Obend.Slot.Proofs.Protocol +Obend.Slot.Proofs.Negotiation journal"
build() { lake build $SLOT_TARGETS > "$1" 2>&1; }
export_only() { lake env .lake/build/bin/journal export --only Obend.Slot --out "$1"; }

echo "== Slot subtree green, export before"
build "$OUT/teeth-build-0.log" || { echo "Slot subtree not green; see $OUT/teeth-build-0.log"; exit 1; }
export_only "$J/env-teeth-before.jsonl" > "$OUT/teeth-export-0.log" 2>&1 || { echo "export failed; see $OUT/teeth-export-0.log"; exit 1; }

echo "== (a) body of Coin.answer changed (id inserted), statement intact"
replace_once "$PROT" "$A_OLD" "$A_NEW" || exit 1
build "$OUT/teeth-build-a.log" || { echo "build (a) failed; see $OUT/teeth-build-a.log"; exit 1; }
export_only "$J/env-teeth-a.jsonl" > "$OUT/teeth-export-a.log" 2>&1 || exit 1
replace_once "$PROT" "$A_NEW" "$A_OLD" || exit 1
lake env .lake/build/bin/journal diff "$J/env-teeth-before.jsonl" "$J/env-teeth-a.jsonl" 2>/dev/null | sed -n '/^journal:/,$p' > "$OUT/teeth-a.txt"
T=Obend.Slot.Protocol.Coin.no_foresight
section "$OUT/teeth-a.txt" "PROOF-CITED" | grep -qxF "$T"; check "(a) $T under PROOF-CITED" $?
for s in "STATEMENT-CITED" "revised theorems (own statement meaning changed)" "reproved (supports hold, proof hash differs)" "added theorems" "removed theorems"; do
  section "$OUT/teeth-a.txt" "$s" | grep -qxF "$T"; [ $? -ne 0 ]; check "(a) $T not under $s" $?
done
grep -q 'Obend.Slot.Protocol.Coin.answer  meaning changed' "$OUT/teeth-a.txt"; check "(a) Coin.answer is a withdrawn support" $?
echo "--- (a) report:"; cat "$OUT/teeth-a.txt"

echo "== (b) dead_eq_nil_iff and mem_dead_iff swapped"
replace_once "$SLOT" "$B_FIRST
$B_SECOND" "$B_SECOND
$B_FIRST" || exit 1
build "$OUT/teeth-build-b.log" || { echo "build (b) failed; see $OUT/teeth-build-b.log"; exit 1; }
export_only "$J/env-teeth-b.jsonl" > "$OUT/teeth-export-b.log" 2>&1 || exit 1
replace_once "$SLOT" "$B_SECOND
$B_FIRST" "$B_FIRST
$B_SECOND" || exit 1
lake env .lake/build/bin/journal diff "$J/env-teeth-before.jsonl" "$J/env-teeth-b.jsonl" 2>/dev/null | sed -n '/^journal:/,$p' > "$OUT/teeth-b.txt"
for s in "withdrawn supports" "revised theorems (own statement meaning changed)" "STATEMENT-CITED" "PROOF-CITED" "reproved (supports hold, proof hash differs)" "added theorems" "removed theorems"; do
  grep -qF "$s (0)" "$OUT/teeth-b.txt"; check "(b) $s (0)" $?
done
echo "--- (b) report:"; cat "$OUT/teeth-b.txt"

echo "== restored; rebuilding the subtree as it was"
build "$OUT/teeth-build-restore.log"; echo "restore build exit $?"
exit $fail
