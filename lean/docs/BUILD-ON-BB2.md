# Building on dregg-build2 (from 2026-10-31)

The Mac is for editing and single-file checks; whole-tree builds run on dregg-build2 (`ssh bb2`, user
`build`) or hbox. Read `~/swarm/MACHINES.md` and `RULES.md` first.

A lane's loop:

1. Edit in your Mac worktree as before. Commit named files on your lane branch (unsigned is fine).
2. Push the branch to the box: `git push bb2 <branch>` (the Mac has `bb2` as a remote pointing at
   `~/obend/repo`; the box has no GitHub write key, so `dev` is still pushed from the Mac).
3. Build there, one build per tree, under the cgroup:
   ```
   ssh bb2 'cd ~/obend/repo && git checkout -q <branch> && cd lean && \
     SWARM_MEM_MAX=48G LEAN_NUM_THREADS=4 swarm-build lake build 2>&1 | tail -3'
   ```
   Tier 2: the same with `lake build Obend.Census Teeth`. The cohorts and tests run there too
   (`python3 tests/run-obend-source.py`, `run-receipts.py`, `run-workspace.py`, `run-logic.py`).
   For a detached build, write the PID file in its own step:
   ```
   ssh bb2 'cd ~/obend/repo/lean && nohup swarm-build lake build > ~/obend/logs/NAME.log 2>&1 &
            echo $! > ~/obend/logs/NAME.pid'
   ```
   A single ssh one-liner with `… & echo $! > pid` loses `$!`; put the `echo` on its own line.
4. When green: rebase onto `origin/dev` on the Mac, push `dev` from the Mac (the pre-push hook builds
   both tiers locally; pass `--no-verify` only when the identical commit was green on the box and say so).

Cold tier 1 on the box is about 70 s sharing with minidregg's lanes; hbox is about 50 s and preferred
when up (`~/obend/repo` there as well, user `hbox`).
