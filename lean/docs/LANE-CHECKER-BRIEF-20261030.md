# Lane Checker: align the procedure with declarative typing

Goal: a type checker for Core4 that is complete for a fragment we can state, with the proof, so
the kernel's admission judge and the metatheory's `PartialTyping` stop disagreeing. The problem
statement is `/Users/ember/dev/obend/review/CHECKER-COMPLETENESS-REPORT-20261030.md`; the design
we are following, with the parts we checked against the code, is
`/Users/ember/dev/obend/review/ARGON-RESPONSE-20261030.md`. Read both first, then
`lean/README.md` and `lean/docs/REPORT-20261030.md` §2 (the module discipline), then the code:
`lean/Obend/Core/Check.lean` (`Assumptions` at :10, `sameType` at :91, `PartialTyping` at :183,
`infer` at :348, `Checked`/`check` at :614), `Obend/Core/Ty.lean`, `Core/Proofs/Substitution.lean`,
`Core/Proofs/CheckCompletenessObstruction.lean` (the three counterexamples you are retiring),
`Obend/Slot/Calculus.lean` and `Obend/Slot/Core4.lean` (`Decides`, `Covered`, `Recognized`).
The precedents named in the response are worth an hour before writing: Dunfield–Krishnaswami's
survey and Lennon-Bertrand's bidirectional CIC are the two that match our obstructions exactly.

Follow the five-step order at the end of the response file, one commit each. Some specifics:

- Step 1 touches the relation's `sameType`, so every theorem that cites it is in the journal's
  repair set: run `lake exe journal` before and after (`lean/Journal/README.md`) and put the exact
  set in your report. Prove `Equivalence (sameType assumptions)`; if the relation needs to change
  shape to make that true (hereditary unfolding, visited set), change it and say so. Rigid
  variables stay nominal; `lookup` through a rigid variable's bound stays directional.
- Step 2 is small and should land on its own so the cascade is visible: `correct_lambda_annotation_
  still_incomplete` must stop being provable, and you replace it with a positive theorem that the
  example now checks.
- Step 3 builds `Obend/Core/Bidirectional.lean` beside `Check.lean`: `infer` and `checkAgainst`,
  returning `Except CheckRefusal Checked` with the constructors the response lists (each carrying a
  path), uses synthesized inline, native `checkAgainst` clauses, conversion only at the mode switch.
  Soundness is by construction as now (the certificate's `derivation` field).
- Step 4: `checkCovered`/`synthCovered` as decidable functions on `AnnotatedTerm`; the theorem
  `PartialTyping Ψ Γ t A u → checkCovered t → ∃ c, checkAgainst t A Γ = ok c ∧ UsesLE c.uses u`;
  then `annotateFromDerivation` and the full corollary. Each with a `#tooth` (the command exists in
  `Obend/Tactic`) showing the fragment boundary bites.
- Step 5: the Core4 `Decides` instance moves to the new checker; `Recognized` is deleted; the slot
  theorems rebuild. Full `lake build` green, every pin intact.

Build: `cd /Users/ember/dev/obend/lean && LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`
(about two minutes at 121 jobs). Write `lean/docs/REPORT-CHECKER-20261030.md` in the style of
`REPORT-20261030.md`: what landed, the journal's repair sets, decisions with critique and
meta-critique, and anything from Argon's design you found wrong when you got to the code.

You own `Obend/Core/Check.lean`, `Obend/Core/Ty.lean`, the new `Bidirectional.lean`, proofs under
`Core/Proofs/` that your changes force, `Obend/Slot/Core4.lean`, and your report. No other lane is
live. Commits: named files on `dev`, `git -c commit.gpgsign=false commit -F -` with trailer
`Co-Authored-By: Claude Opus <noreply@anthropic.com>`, push after each step. No sorry, no axiom, no
weakened statement; a theorem that could be vacuous keeps its tooth. The source trees under
`~/dev/minidregg`, `~/dev/nanodregg`, `~/dev/bend` are read-only.

Ember's safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x
<bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID
file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file,
no kill: tell me instead." On disk: when a disk is low, stop writing to it, tell Ember, wait.

Reply with the commit range, which of the five steps are fully proved, the repair set sizes from
the journal for steps 1 and 2, and the one decision for Ember.
