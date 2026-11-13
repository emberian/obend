#!/bin/bash
# Teeth for the journal (brief item 4). Run from lean/ on a green tree; exits non-zero on a failed tooth.
#   (a) change a definition body a theorem's proof unfolds but its statement never mentions
#       (`Obend.Slot.Protocol.Coin.answer`, reached only by the proof of `Coin.no_foresight`): the
#       journal lists `no_foresight` under PROOF-CITED and nowhere else.
#   (b) swap the order of two independent declarations (`dead_eq_nil_iff`, `mem_dead_iff` in
#       `Obend/Slot.lean`): the journal flags nothing.
#   (c) Kimi's seven-row graph (`tools/journal/ClosureTooth.lean`): the kernel, by `decide`, finds the
#       pre-2026-10-30 closure missing `Z` (refuting the completeness statement) and the current one
#       complete. Runs first: it needs only `Journal.Journal` built, no export.
# Each edit is applied and inverted by exact text, so the files are as they were when this exits.
# The teeth live in the `Obend.Slot` subtree: only its modules are built and exported (`--only`), so a
# red module elsewhere in the tree (another lane's proof in progress) does not stop them.
set -euo pipefail
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
  set +e
  if grep -qF "$A_NEW" "$PROT"; then
    replace_once "$PROT" "$A_NEW" "$A_OLD"
  fi
  if grep -qF "$(printf '%s' "$B_SECOND" | head -1)" "$SLOT"; then
    python3 - "$SLOT" "$B_FIRST" "$B_SECOND" <<'PY'
import sys
p, first, second = sys.argv[1:4]
s = open(p).read()
if s.count(second + '\n' + first) == 1:
    open(p, 'w').write(s.replace(second + '\n' + first, first + '\n' + second))
PY
  fi
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
diff_journal() {
  local raw="$1" out="$2"
  shift 2
  lake env .lake/build/bin/journal diff "$@" > "$raw" 2>/dev/null
  sed -n '/^journal:/,$p' "$raw" > "$out"
  [ -s "$out" ]
}

echo "== (c) closure completeness on Kimi's seven-row graph"
lake build Journal.Journal > "$OUT/teeth-build-c.log" 2>&1 || { echo "Journal.Journal not green; see $OUT/teeth-build-c.log"; exit 1; }
rc=0; lake env lean "$J/ClosureTooth.lean" > "$OUT/teeth-c.log" 2>&1 || rc=$?
check "(c) old closure refuted, new closure complete (ClosureTooth.lean)" "$rc"

echo "== Slot subtree green, export before"
build "$OUT/teeth-build-0.log" || { echo "Slot subtree not green; see $OUT/teeth-build-0.log"; exit 1; }
export_only "$J/env-teeth-before.jsonl" > "$OUT/teeth-export-0.log" 2>&1 || { echo "export failed; see $OUT/teeth-export-0.log"; exit 1; }

echo "== (a) body of Coin.answer changed (id inserted), statement intact"
replace_once "$PROT" "$A_OLD" "$A_NEW" || exit 1
build "$OUT/teeth-build-a.log" || { echo "build (a) failed; see $OUT/teeth-build-a.log"; exit 1; }
export_only "$J/env-teeth-a.jsonl" > "$OUT/teeth-export-a.log" 2>&1 || exit 1
replace_once "$PROT" "$A_NEW" "$A_OLD" || exit 1
diff_journal "$OUT/teeth-a.raw" "$OUT/teeth-a.txt" "$J/env-teeth-before.jsonl" "$J/env-teeth-a.jsonl" || { echo "journal diff (a) failed"; exit 1; }
T=Obend.Slot.Protocol.Coin.no_foresight
rc=0; { section "$OUT/teeth-a.txt" "PROOF-CITED" | grep -qxF "$T"; } || rc=$?
check "(a) $T under PROOF-CITED" "$rc"
for s in "STATEMENT-CITED" "revised theorems (own statement meaning changed)" "reproved (supports hold, proof hash differs)" "added theorems" "removed theorems"; do
  rc=0; { ! (section "$OUT/teeth-a.txt" "$s" | grep -qxF "$T"); } || rc=$?
  check "(a) $T not under $s" "$rc"
done
rc=0; grep -q 'Obend.Slot.Protocol.Coin.answer  meaning changed' "$OUT/teeth-a.txt" || rc=$?
check "(a) Coin.answer is a withdrawn support" "$rc"
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
diff_journal "$OUT/teeth-b.raw" "$OUT/teeth-b.txt" "$J/env-teeth-before.jsonl" "$J/env-teeth-b.jsonl" || { echo "journal diff (b) failed"; exit 1; }
for s in "withdrawn supports" "revised theorems (own statement meaning changed)" "STATEMENT-CITED" "PROOF-CITED" "reproved (supports hold, proof hash differs)" "added theorems" "removed theorems"; do
  rc=0; grep -qF "$s (0)" "$OUT/teeth-b.txt" || rc=$?
  check "(b) $s (0)" "$rc"
done
echo "--- (b) report:"; cat "$OUT/teeth-b.txt"

echo "== restored; rebuilding the subtree as it was"
restore_rc=0; build "$OUT/teeth-build-restore.log" || restore_rc=$?
echo "restore build exit $restore_rc"
check "restore build green" "$restore_rc"
if [ "$restore_rc" -ne 0 ]; then
  cat "$OUT/teeth-build-restore.log" >&2
fi
exit $fail
