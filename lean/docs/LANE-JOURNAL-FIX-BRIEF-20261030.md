# Lane Journal-fix: the closure under-approximates its own dependencies

A hostile review found a correctness bug in `lean/Journal/Journal.lean`: `closure` (line 99) starts
with fuel `E.size + seeds.length + 1` and decrements it on every stack pop, including pops of names
already in `seen`, so a convergent acyclic graph can run out of fuel before every reachable row is
visited. Concrete case: `R` cites `[A,B,C,D,Z]`, each of `A..D` cites only `X`, `X` and `Z` cite
nothing; seven rows, fuel nine; the walk visits `R, A, X, B, X, C, X, D, X` and returns with `Z` on
the stack, so a change to `Z` reads as `.unaffected`. The full review is
`/Users/ember/dev/obend/review/KIMI-REVIEW-20261030.md`, section "The journal closure omits reachable
dependencies" and item 1 of its ranking.

Read: that section, `lean/Journal/README.md`, `lean/Journal/Journal.lean`, `lean/Journal/Export.lean`,
`lean/tools/journal/EXPERIMENT-20261030.md` and `teeth.sh`, and `lean/docs/REPORT-JOURNAL-20261030.md`.
Build with `cd /Users/ember/dev/obend/lean && LEAN_NUM_THREADS=2 lake build Journal journal 2>&1 | tee build.log`
(by name: other lanes have uncommitted red files elsewhere in the tree).

Do, as one or two commits:

1. Replace the fuel scheme with a worklist whose termination measure is the number of unvisited
   rows (or bound the fuel by the total citation-list length), so termination is structural and
   the walk visits every reachable row.
2. Prove closure completeness: every finite meaning-edge path from a seed ends in a row that is in
   the computed support set. State it so a `decide` tooth on Kimi's seven-row graph refutes the old
   definition and passes the new one; keep that graph as a test in `tools/journal/teeth.sh`.
3. In `README.md` and the module docstring, say plainly that equal 64-bit non-cryptographic hashes
   are evidence of equal meaning, not equality, and what that means for `holdsIn`.
4. Append a dated section to `lean/docs/REPORT-JOURNAL-20261030.md`: what was wrong, what changed,
   the theorem, the tooth, and anything you would still not trust.

You own `lean/Journal/**`, `lean/tools/journal/**` and that report. Commit named files on `dev`
with `git -c commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`;
`git fetch` and rebase only if the tree is clean, otherwise commit and push directly as the paper
lane did. No sorry, no axiom.

Ember's safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x
<bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID
file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file,
no kill: tell me instead." On disk: when a disk is low, stop writing to it, tell Ember, wait.

Reply with the commit hash, the completeness theorem's statement, and whether the seven-row tooth
refutes the old closure.
