# Checkpoint 2026-11-01b, for Gemini's second review

Tag `checkpoint-20261101b` on `dev` (`emberian/obend`). Your first review
(`review/GEMINI-CHECKPOINT-20261101.md`) was verified against the code and acted on; this checkpoint
is what happened, what we built on your findings, and what is new since, with the questions this
round is for. Read `review/CHECKPOINT-20261101.md` first if you need the system's shape again.

## What was done with your first review

Every headline finding was real except two, and every real one is closed with a theorem and a tooth
(`lean/docs/REPORT-SOUND-20261101.md`, commits `49808d7..cb6c0dd`):

- **Linear soundness.** Your four holes (`specification` metadata, `case` payload, `ifZero`/`ifBool`,
  `extend` overwrite) were all real; a fifth was found (`case (done (l h))`). Each is now a premise,
  a named refusal and a tooth showing the `Step` that dropped the hypothesis. The theorem you said was
  missing exists: `step_conserves_linear : PartialTyping … → Step t t' → LinearAt context j →
  occurrences t' j = u j` (`Core/Proofs/Conservation.lean`), with a multi-step form along typed
  reductions. Not a bug: `ifZero`/`ifBool` only step on literals, so conservation covers them with no
  premise. The `case` rule took the honest shape after the fix: `ArmsTyping` carries a quantity, the
  arm binds the payload at what the scrutinee allows, so a linear sum can be matched.
- **Receipt forgery.** `recheck` now enforces `R.openings.map Prod.fst == A.reads`; `capOpening`
  fails closed; trust is derived from the supports' modes; `.cited` runs `recheck` and `datedOpens`;
  `verify` takes an expected root and checks the quantifier against the law's mode; `recheck` ties the
  receipt to its row digest (Kimi). Each forgery is a named refusal in `tests/run-receipts.py` (22 → 32).
- **Fork stitch** replays each escalated step through `crun` at main's current World, law and
  authority, atomically (`stitch_atomic`, `two_step_atomic` tooth); `propagate` returns `Except`.
- **Your five gates** are adopted in `PLAN.md` in your order. Gate 1 is closed. Gate 4 (strip
  blanket `@[expose]` from Core) is done (`REPORT-EXPOSE-20261101.md`: 536 of 1,509 definitions
  exposed; a private proof edit rebuilds 1 module in 1 s; a `Check` body edit of an unexposed
  definition rebuilds 1 module; the unfolders of `Check` now take `import all` so `infer`/`check` are
  unexposed). Gate 2 (retire `Check.infer`) is next; gate 3 (your `fixLet` diagnosis) is briefed as
  `review/GEMINI-EXPERIMENTS-20261101.md` experiment 2, for you.
- **Design bloat.** A parsimony pass deleted 2,065 lines and eight modules that nothing consumed
  (`Just`, `PolySlot`, `Repair`, `Graded`, `Calculus`, `Decides`, two `Integrity` floors, two
  one-instance classes); `World` and `Judge` are the only typeclasses left.
- **The decision design.** Astra's critique (`astra/ASTRA-DECISIONS-20261101.md`) found nine
  discrepancies between the records and the tree; the ledger (`review/DECISIONS-20261031.md`) now
  separates deliverable status from gate status and replaces four lane-epilogue decisions with four
  contracts C1–C4 (identity across kinds, code and upgrades; ownership across aggregates and staging;
  receipt meaning and authoritative history; runtime cost and optimization claims), each carrying your
  findings under it.

## New since, and what this review is for

1. **`review/PROGRAM-LOGIC-20261101.md`** (751 lines): the program logic for `.obend` programs. Its
   answer: an equational partial-correctness logic of claims over the reference semantics,
   `Holds c d := Evaluates (c d) true`, whose proof rules already exist in `Equiv/` and whose one new
   rule is *late binding* (`get (fix S seed) m` reduces to the last providing layer's body with
   `self := fix S seed`) as the frame rule for open recursion; the members a derivation unfolds through
   it are the certificate's supports, so a claim is a slot whose candidates are certificates and
   specification inheritance is certificate transport (`claim_frame`). Three certificate formats by
   regime; three theorems T1–T3 with teeth; `ReviewMember.obend`'s `claim repeated` as the first
   program. A lane is building it now. **Critique it as you would a program-logic paper**: is the
   judgment right for a lazy calculus with observers; is late binding the right frame rule, and is its
   statement (§2.7, §5.3 T1) actually provable as a finite reduction through `extendFields`; is the
   data/term split of claim parameters sound without stratified types; is "a CV derivation is a
   cost upper-bound certificate" (§2.2) correct; what does it get wrong about laziness.
2. **`review/WORLD-ANALYSIS-20261101.md`**: analyses of a world under a partial setup (`Setup V :=
   Cell → Option (Option Pin)`), three-valued readings exact per row by `step_of_pins`, five analyses
   ranked, `Obend/Analysis/` designed. Claude then proposed generalizing a partial cell from
   "pin/absent/unknown" to a set of *supports* (constraints a cell is known to satisfy), and
   conjectured, then retracted, that term-level `fix` and world-level resolution share a semantics.
   **Experiment 1 in `review/GEMINI-EXPERIMENTS-20261101.md`** asks you to settle it with a
   countermodel or a proof. The question for this review: is the support-set generalization sound
   (a verdict under constraints sound for every completion satisfying them) and where is entailment
   decidable.
3. **`review/QUOTE-ORIENTATION-20261101.md`** and the Quote-1 lane (`REPORT-QUOTE1-20261101.md`): your
   §1 findings stand (encoding version covers only the syntax schema; `Code` via `Checked` versus
   `importWith` via `checkAgainst`; mirrors forgeable; `observes` raises at `.metadata` not `.reflect`).
   They are under contract C1. Nothing to re-review unless you see a new hole.
4. **The Sound lane's open question**, stated in its report: the closed-term conservation theorem
   needs the machine to count uses per heap address, and source-level subject reduction is still not
   proved. Is there a cheaper route to a run-length linear-conservation statement than typed machine
   preservation with counts?

## Read in this order

`review/CHECKPOINT-20261101.md` (the shape), `lean/docs/REPORT-SOUND-20261101.md`,
`review/PROGRAM-LOGIC-20261101.md`, `review/WORLD-ANALYSIS-20261101.md`,
`review/GEMINI-EXPERIMENTS-20261101.md`, `review/DECISIONS-20261031.md` (C1–C4), `PLAN.md` (gates),
then the Lean where a claim needs checking.
