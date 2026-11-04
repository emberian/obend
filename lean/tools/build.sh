#!/bin/sh
# The tier build with its time budget (review/DECISIONS-20261031.md, 2026-11-04: no build step takes
# an hour). `tools/build.sh tier1` is `lake build`; `tools/build.sh tier2` is
# `lake build Obend.Census Teeth Tests`. Each module Lake elaborates is read back from Lake's own
# timing line (`✔ [n/N] Built Obend.Foo (12s)`), and the build fails when a module of tier 1 took
# more than 60 s or a module of tier 2 more than 600 s, even if Lake itself succeeded. A module Lake
# replays (unchanged, no timing) carries its last measurement, not a new one, so a full measurement
# is a build from a clean .lake on a box (bb2, hbox). The timings are wall time under whatever
# parallelism Lake had (LEAN_NUM_THREADS, the box's load); the budget is of the build as run.
# Run from lean/. The log is kept at .lake/build/<tier>.log; the ten slowest modules are printed.
# `tools/build.sh --parse LOG tier1` applies the budget to a log already on disk.
set -u
# `tools/build.sh --parse LOG tier1|tier2` only reads an existing log back (the same parser, no build).
parse_only=""
if [ "${1:-}" = "--parse" ]; then parse_only="$2"; shift 2; fi
tier="${1:-tier1}"; shift 2>/dev/null
case "$tier" in
  tier1) budget=60;  targets="" ;;
  tier2) budget=600; targets="Obend.Census Teeth Tests" ;;
  *) echo "usage: tools/build.sh [--parse LOG] tier1|tier2 [lake args]" >&2; exit 2 ;;
esac
if [ -n "$parse_only" ]; then
  log="$parse_only"; lake_status=0
else
  mkdir -p .lake/build
  log=".lake/build/$tier.log"
  # shellcheck disable=SC2086
  lake build $targets "$@" 2>&1 | tee "$log"
  lake_status=$?
fi
# Lake prints durations as 123ms, 1.2s, 12s, 3m 4s, 1h 2m. Reduce each `Built <Module> (<dur>)` line to
# seconds; `:c.o`/`:o` and other facet lines are not module elaborations and are skipped. The line's
# first field is Lake's status glyph (✔, ⚠, ℹ, ✖), matched as "anything but a space" so the parser
# does not depend on the awk's view of multibyte characters.
over=$(awk -v budget="$budget" '
  /^[^ ]+ \[[0-9]+\/[0-9]+\] Built [A-Za-z0-9_.]+ \(/ {
    mod = $4; if (mod ~ /:/) next
    s = $0; sub(/.*\(/, "", s); sub(/\)[^)]*$/, "", s)
    secs = 0; n = split(s, parts, " ")
    for (i = 1; i <= n; i++) {
      p = parts[i]
      if (p ~ /ms$/) { sub(/ms$/, "", p); secs += p / 1000 }
      else if (p ~ /h$/) { sub(/h$/, "", p); secs += p * 3600 }
      else if (p ~ /m$/) { sub(/m$/, "", p); secs += p * 60 }
      else if (p ~ /s$/) { sub(/s$/, "", p); secs += p }
    }
    printf "%.1f %s\n", secs, mod
  }' "$log" | sort -rn)
echo "build.sh: slowest modules of this $tier build (budget ${budget}s per module):"
echo "$over" | head -10 | sed 's/^/  /'
offenders=$(echo "$over" | awk -v budget="$budget" '$1 > budget')
if [ "$lake_status" -ne 0 ]; then
  echo "build.sh: $tier FAILED (lake exit $lake_status); log at $log"; exit "$lake_status"
fi
if [ -n "$offenders" ]; then
  echo "build.sh: $tier is over budget; these modules took more than ${budget}s each:"
  echo "$offenders" | sed 's/^/  /'
  echo "build.sh: split the module, move the fixture to tier 2 (Obend/Teeth/), or make the thing faster; raising the budget is a ledger decision"
  exit 3
fi
echo "build.sh: $tier green, every elaborated module within ${budget}s"
