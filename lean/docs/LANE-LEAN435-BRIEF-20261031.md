# Lane Lean 4.35: bump the toolchain

Goal: `lean/` builds green at Lean v4.35.0 (the latest stable; elan has it installed) with every
theorem, pin and cohort unchanged. A probe build of current `dev` at 4.35 already exists in the
worktree `/private/tmp/claude-501/-Users-ember-dev-obend/33ee7e81-25a8-4000-aaf3-942ad7ef028b/scratchpad/lean435/lean`
with its log in `build.log` there; read that log first. Five independent failures, each with a
cause I read:

- `Obend/AssertAxioms.lean:40`: `Lean.ofReduceBool` and `Lean.trustCompiler` no longer exist by
  those names in `Init`; find what 4.35 calls the compiled-evaluation axioms (look at how
  `native_decide` in `~/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Elab/Tactic/Decide.lean`
  records its axiom) and keep the census's meaning: the standard three, plus the compiled-trust
  set reported separately.
- `Obend/Tactic/Tooth.lean:157`: `Environment.addDeclCore`'s signature changed (the heartbeat
  `USize` argument); read the 4.35 signature and call it as it is now, keeping `doCheck := true`.
- `Obend/Slot/Protocol.lean:586-588`: `simp` no longer closes `x ∈ [a, b]` membership goals;
  `decide` or `simp [List.mem_cons]` does.
- `Obend/Core/LegacyAgreement.lean:290`: `simpa` expected `1 ≤ n` and got `0 < n`; a
  normal-form change, `Nat.succ_le_of_lt`/`omega` closes it.
- `Obend/Core/Proofs/Adequacy.lean:1186` and whatever `Law/Proofs/Std` and `FiniteBisimulation`
  report once their imports build: the same simp-normal-form class. Read each error; fix the proof,
  never the statement.

Do it in the main checkout: set `lean/lean-toolchain` to `leanprover/lean4:v4.35.0`, let Lake
regenerate the manifest, fix each error in place, full `LEAN_NUM_THREADS=2 lake build 2>&1 | tee
lean/build.log` (177 jobs at 4.30), then `python3 lean/tests/run-obend-source.py` for Mini's cohorts,
and `lake exe journal` before and after (`lean/Journal/README.md`) so the report shows nothing
changed meaning. One commit, named files, on `dev`, `git -c commit.gpgsign=false commit -F -` with
trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, push. Append a short section to
`lean/docs/REPORT-EQUIREC-20261031.md` or start `REPORT-LEAN435-20261031.md`: each fix, and any
4.35 change that affected a statement (there should be none). Remove the probe worktree when done
(`git worktree remove --force <path>`); it is this session's.

No sorry, no axiom, no weakened statement. The source trees under `~/dev` other than `obend` are
read-only. Ember's safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`,
no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID
in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No
PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait.

Reply with the commit hash and each fix in one line.
