#!/bin/bash
# The one experiment (brief item 3, 2026-10-30): the two edits REPORT-20261030 §4 made, each exported
# before and after, the journal run on each pair, next to the modules Lake rebuilt. Run from lean/.
# Edits are appended behind a marker and removed by the marker, so a concurrent edit to the same file
# by another lane survives. One run; the record is EXPERIMENT-20261030.md, written by hand from
# $OUT. Not a harness.
set -u
export LEAN_NUM_THREADS=2
OUT=${OUT:?set OUT to a scratch directory for the logs}
mkdir -p "$OUT"
J=tools/journal
ADEQ=Obend/Core/Proofs/Adequacy.lean
TERM_=Obend/Core/Term.lean
MARK='-- journal experiment edit (removed by experiment.sh)'

# remove the marker and the edit after it: up to the namespace end when the edit sits inside one,
# else to the end of the file
strip_marker() {
  python3 - "$1" "$MARK" <<'PY'
import sys
p, mark = sys.argv[1], sys.argv[2]
s = open(p).read()
i = s.find('\n' + mark)
if i >= 0:
    j = s.find('\nend Obend.Core.Term', i)
    open(p, 'w').write(s[:i] + (s[j:] if j >= 0 else ''))
PY
}
restore() { strip_marker "$ADEQ"; strip_marker "$TERM_"; }
trap restore EXIT

build() {  # $1: label. Records the modules Lake built (not replayed), by name.
  lake build > "$OUT/build-$1.log" 2>&1
  echo "build $1: exit $?" | tee -a "$OUT/summary.txt"
  grep -oE '(Built|Building) [A-Za-z0-9.]+' "$OUT/build-$1.log" | awk '{print $2}' | sort -u > "$OUT/rebuilt-$1.txt"
  echo "  rebuilt ($(wc -l < "$OUT/rebuilt-$1.txt" | tr -d ' ')): $(tr '\n' ' ' < "$OUT/rebuilt-$1.txt")" | tee -a "$OUT/summary.txt"
}
export_as() { lake exe journal export --out "$J/env-$1.jsonl" 2>&1 | grep -E 'rows from' | tee -a "$OUT/summary.txt"; }
journal() { lake exe journal diff "$J/env-$1.jsonl" "$J/env-$2.jsonl" 2>&1 | sed -n '/^journal:/,$p' | tee "$OUT/journal-$1-$2.txt"; }
tree_state() { echo "tree $1: $(git rev-parse --short HEAD) $(git status --porcelain -- Obend Obend.lean | tr '\n' ' ')" | tee -a "$OUT/summary.txt"; }

: > "$OUT/summary.txt"
echo "== 0. green tree, export before" | tee -a "$OUT/summary.txt"
tree_state 0
build 0
export_as exp-before

echo "== 1. a private trivial theorem appended to $ADEQ" | tee -a "$OUT/summary.txt"
printf '\n%s\ntheorem measurement_private_tooth : (1 : Nat) + 1 = 2 := rfl\n' "$MARK" >> "$ADEQ"
build 1
export_as exp-after1
strip_marker "$ADEQ"
tree_state 1
journal exp-before exp-after1

echo "== 2. an exposed def appended to $TERM_ (inside its exposed section, before the namespace end)" | tee -a "$OUT/summary.txt"
python3 - "$TERM_" "$MARK" <<'PY'
import sys
p, mark = sys.argv[1], sys.argv[2]
s = open(p).read()
i = s.rindex('\nend Obend.Core.Term')
edit = '\n' + mark + '\n/-- measurement edit (removed) -/\ndef measurementScalar : Term → Bool\n  | .nat _ | .boolean _ | .label _ => true\n  | _ => false\n'
open(p, 'w').write(s[:i] + edit + s[i:])
PY
build 2
export_as exp-after2
strip_marker "$TERM_"
tree_state 2
journal exp-before exp-after2

echo "== 3. both removed; the tree rebuilt" | tee -a "$OUT/summary.txt"
build 3
export_as exp-after3
journal exp-before exp-after3
rm -f "$J"/env-exp-*.jsonl
echo done | tee -a "$OUT/summary.txt"
