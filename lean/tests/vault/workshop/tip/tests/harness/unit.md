---
command: "tools/accept/harness.sh"
---
# harness: the suite, offline, and the help

`tools/accept/harness.sh WORKTREE` from this workshop: runs `python3 -m unittest discover -s tests -v`
with `HOME` an empty directory and no `KAGI_API_KEY` or `SCRY_API_KEY` (a live call cannot succeed),
then `python3 research.py --help`, `python3 research.py kagi --help` and
`python3 research.py scry --help`. Passing: every step exits 0 and the suite ran at least one test of
each of Kagi and Scry. Proves [[jobs/harness]].
