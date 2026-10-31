# Study and spike: `≈b` for the lazy heap, and whether Iris-Lean is the tool

`METATHEORY.md` §2 row one: `mix` is associative up to a behavioural equivalence `≈b` nobody has
defined, and the candidate tool is a step-indexed logical relation over the demand machine's heap in
Iris-Lean, with Moran–Sands' improvement theory as the cost-sensitive equivalence a priced kernel
wants. Study it and build the smallest honest spike.

Read `METATHEORY.md` §2, `DESIGN.md` §1–2, `review/PRIOR-ART-20261030.md` §5 and §7, then the
machine: `lean/Obend/Core/Machine.lean`, `MachineFast.lean`, `Core/Proofs/{Forcing,Collect,Settle}*.lean`
(what is already proved about update frames, blackholing, sharing), `Core/Term.lean` (`mix`, `fix`,
`Steps`, `Evaluates`). Papers in `~/paperbin`: `launchbury1993-natural-semantics-lazy-evaluation`,
`breitner2014-adequacy-of-launchburys-natural-semantics` (the Isabelle mechanization and what it
cost), `sestoft1997-deriving-a-lazy-abstract-machine`, `hackett-hutton2019-call-by-need-is-clairvoyant-call-by-value`,
`appel-mcallester2001-indexed-model-recursive-types`, `ahmed2006-step-indexed-syntactic-logical-relations`,
`iris-in-lean2026`, `jung2018-iris-from-the-ground-up`. Moran–Sands 1999 is not in paperbin (no open
copy); `$ANNAS_SECRET_KEY` is available if you want to try Anna's Archive for it.

Deliver: (1) `/Users/ember/dev/obend/review/EQUIV-PLAN-20261031.md`: the three candidate definitions
of `≈b` (completed-run equality on observable results; clairvoyant call-by-value cost equivalence;
a step-indexed relation over machine configurations with heap), what each proves about `mix`
associativity and the `keep(7, fix(identity))` / `{good=7, bad=self.bad}.good` tests, which is
compatible with the world's resource pricing, and whether Iris-Lean at its current state (check
`leanprover-community/iris-lean`'s toolchain and whether its adequacy layer has landed) is usable
from a Lean 4.35 `module` tree at all. (2) The spike, in a new library `lean/Obend/Equiv/` (new
files only): the weakest of the three definitions that is strong enough to state `mix` associativity,
the theorem `mix_assoc` for it over Core4's reference `Steps` (both associations reduce to
`c self (b self (a self super))` in a few β steps, so this may need no heap), and the clairvoyant
cost statement if it fits in the time. Say in the plan what the heap-indexed version would need
that the spike does not have.

Conventions: own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/equiv dev`),
Lean v4.35.0, every file a `module`, no `#assert_axioms` lines, no sorry, no axiom, named-file commits
on `dev` with `git -c commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Claude Opus
<noreply@anthropic.com>`, rebase before pushing; other lanes are live under `Obend/Core/Proofs`,
`Obend/Spec`, `Obend/Doc`, `Obend/Slot`, `Obend/Run`, `Obend/Law`. Ember: "Never kill by pattern. No
`pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is
stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo
$! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell
Ember, wait. Reply with the commit range, which definition the spike uses, and whether Iris-Lean is usable.
