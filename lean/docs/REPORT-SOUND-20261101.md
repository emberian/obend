# Report: lane Sound — linear holes closed, conservation proved, receipts and the stitch made honest (Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-SOUND-BRIEF-20261101.md`, from Gemini's checkpoint review
(`review/GEMINI-CHECKPOINT-20261101.md`, items 1–3) and, mid-lane, three findings of Kimi's code
reviews (`review/KIMI-CODE-A-20261101.md`, `-B`). Item 1 in worktree `scratchpad/kinds` (branch
`lane-sound`); item 2 and Kimi's receipt/vault findings in `scratchpad/build`; item 3 in
`scratchpad/runner2` (sub-agents of this lane). Commits on `dev`: `802d85e` (receipts), `f12e474`
(stitch), `a550bad` (Kimi: receipts and vault), then this lane's `Sound (1)`, `Sound (2)` and this report.

**Builds.** Start, at `49808d7`: tier 1 282 jobs, tier 2 303 jobs, green (warm). End, after rebasing
onto `a550bad`: tier 1 283 jobs, tier 2 304 jobs, green; census 35,462 constants, 27 on compiler trust,
none on `sorryAx` or a declared axiom. **Controls** (start → end): cohorts probes 30/30, tutorial
71/71, preview 161 with 0 failures → unchanged; receipts 22/22 → 32/32 (ten new forgery tests, all
refused by name); workspaces 30/30 → 30/30; the vault walkthrough 26 → 26.

## 1. Linear soundness (`Core/Check.lean`, `Core/Bidirectional.lean`)

Each hole was confirmed first: the fixture below was accepted by the bidirectional checker at
`linear` on the tree at `9d75d59` (and by the fuel checker for the first two), and one or two `Step`s
from its body lose the use of the hypothesis (`*_drops_in_*_step` in `Teeth/Core/LinearTeeth`, a
`Step` and the `occurrences` before and after).

| hole | fixture body (`h : Nat`) | the drop | rule added | refusal |
|---|---|---|---|---|
| specification | `{meta = h; λx. x} 3` | `applySpecification` discards the metadata | `linearFree context mu` | `linearMetadata path index` |
| extend | `{a = h} with {a = 0}` | `extendRecord` overwrites the field | `linearFree context targetUses` | `linearOverwritten path index` |
| case | `case l h of l x. 0` | `caseInject` binds the payload `unrestricted`; `x + x` copies it | `linearFree context su` (scrutinee) | `linearScrutinee path index` |
| done (fifth, found here) | `case (done (l h)) of l x. done 0` | `done` steps to its value, then the plain `case` drops it (two steps) | `linearFree context uses` at `done` | `linearReturned path index` |

Each refusal is a `#tooth` by mutating the fixture's quantity to `affine` (accepted there: dropping is
within "at most once"). Both checkers (`Check.infer`, `Bidirectional.elaborate`) check the premises.

**Not a hole: `ifZero` and `ifBool`.** Their scrutinee is *eliminated*: the test is the one use of the
hypothesis. `Step.zero`/`successor`/`ifTrue`/`ifFalse` fire only at a literal, which holds no
hypothesis, and the predecessor `ifZero` binds `unrestricted` is a fresh literal, not the scrutinee's
contents. `λ(h : linear Nat). ifZero h 0 (p. p + p)` is accepted (`ifZero_scrutinee_accepted`), and
`step_conserves_linear` covers both rules with no new premise. Gemini's ⊕-reading (the predecessor
inherits linearity) would matter for a type whose values carry custody; `Nat` and `Bool` do not.

**Metatheory re-established (all green).** Weakening (`source_insert_binding`), closed substitution
(`infer_msubst`, `partialTyping_msubst` in `Substitution/Transport`, `Msubst`, `TypedSubstitution`;
`check_msubst`, `checked_msubst`, `calculus_typed_msubst` unchanged in statement), templates
(`Templates`), the machine's preservation (`Preservation/Base/Focus`, `Cases/Activities`, `Cases/Pairs`:
the machine needs no new premise), completeness: `completes_specification`, `completes_extend`,
`completes_case`, `completes_done` take the premise (revised); `complete`, `full_annotated`,
`annotated_complete` unchanged; `prepare_checks` unchanged (its private `motive_case` takes the
premise); Law typing (`chk_case`, via `linearFree_noLinear`); `SpecificationClosure`
(`compose_wrapper_typed`: its context is all `unrestricted`).

**Linear resource conservation** (`Core/Proofs/Conservation.lean`, new, tier 1):

```lean
public theorem step_conserves_linear {a : Assumptions} {context : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a context t T u) (valid : validContext a.shareableVariables context = true)
    {t' : Term} (step : Step t t') {j : Nat} (lin : LinearAt context j) :
    (occurrences context.length t').getD j 0 = u.getD j 0
```

A `Step` from a term that checks in `context` uses every `linear` hypothesis of `context` exactly as
often as the term did (`u` is that count, `uses_determined`): none dropped, none copied. The context is
the custody the term holds; `Step` has no discharge (a `perform` does not step; the kernel's resume is
the explicit discharge). The substitution case is `subst_counts`: through `t.substitute σ` with `σ`
putting `A` at `d`, hypothesis `j` counts `u[skipAt d j] + u[d] · uses(A)[j]`, exactly at every `linear`
`j`, because at each join both branches agree on a `linear` hypothesis and either the substituted
binder is `linear` (so they agree on it too) or `A` uses no `linear` hypothesis. Beta uses `fits`
(a `linear` binder is used once) and `argumentAllowed`; `caseInject` uses the new scrutinee premise and
`arms_find`; `mix` and `fix` use their reusable captures.

**What it does not say (stated, not proved).** `steps_conserve_linear` extends it along a reduction
*every term of which checks*: source subject reduction is not proved in the tree (the proved
preservation is the machine's, `typed_stepRaw_preserved`, which does not track counts). The closed-term
version the brief asks for needs exactly that: over a closed term the context is empty, and the custody
lives in heap cells after `beta`, so "live linear positions" are machine addresses. That version needs
the machine to carry per-address use counts; it is not done.

**Refusals that name their own clause** (Kimi review A, while in these rules). `overuse` said
`affineBinderOverused` for every quantity: it is now `binderOverused path index quantity count`
(`linear_overuse_named`, `erased_use_named`). `argumentRefusal` follows `argumentAllowed`'s clauses in
order: `activityMisplaced`, `linearArgumentDropped`, `notShareable` (the type), `capturesNotShareable`
(the captures) — it said `notShareable` for all (`unrestricted_argument_captures_named`,
`activity_argument_named`). `checkFields`' empty-field mismatch had expected and actual reversed
(`empty_fields_mismatch_ordered`).

**Deviations.**
- `CheckTeeth.shadowed_shareable_member_accepted` pinned acceptance of a `linear` hypothesis hidden in a
  shadowed field of a `case` scrutinee: that program drops it in two steps. The control is now
  `affine` (revised); `shadowed_linear_member_refused` is new.
- `CoerceProbes`: the `linear → linear` sum codomain coercion matches its `linear` component and is now
  refused `.checker (.linearScrutinee _ 0)` (accepted before): a `linear` sum, like a `linear` record
  (Linear round 2), is consumed whole.
- Cohorts, receipts, workspaces, walkthrough: no change from item 1.

**The decision for Ember.** The `case` rule taken is the brief's first option, `linearFree` of the
scrutinee: sound, and the same shape as the projections, but it makes a `linear` sum uneliminable
(the coercion deviation above). The quantity-preserving rule (the arm binds the payload at `linear`
when the scrutinee uses a `linear` hypothesis, and must use it once) is the honest elimination; it
changes `ArmsTyping`'s shape (a quantity index) through the machine typing, completeness and
preparation. `step_conserves_linear` already handles a `linear` substituted binder, so it would carry
over. Also open: affine *copying* through `case` (`case l h of l x. x + x` with `h : affine`) is still
accepted; the source semantics copies, the machine shares one thunk, so it is harmless there.

## Journal (`lake exe journal`, `49808d7` → end, the base moved by the three sub-lane commits)

160 revised, 1,220 STATEMENT-CITED, 0 PROOF-CITED, 417 added, 178 removed, 16,289 unaffected.
This lane's revised statements: `completes_specification`, `completes_extend`, `completes_case`,
`completes_done`, `motive_case` (private), `CheckTeeth.shadowed_shareable_member_accepted`, and the
equations of `elaborate`, `checkFields`, `CheckRefusal`'s `DecidableEq` (new constructors).
`check_msubst`, `checked_msubst`, `full_annotated`, `prepare_checks` are STATEMENT-CITED (they mention
`PartialTyping`) and rebuilt green with unchanged statements. The `Receipt.*`, `Run.Fork.*`,
`Vault.Store.*` revisions are items 2, 3 and Kimi's below.

## 2. Receipts (`Receipt.lean`, `Receipt/Export.lean`), commit `802d85e` (49808d7..802d85e), worktree scratchpad/build

Files: `Obend/Receipt.lean`, `Obend/Receipt/Export.lean`, `Obend/Receipt/Negotiation.lean`, `Obend/Receipt/Cli.lean`, the usage line in `Obend/Main.lean`, `tests/run-receipts.py`.

- **(a) Coverage computed.** `recheck` requires `R.openings.map Prod.fst == A.reads (w', rest) r` (takes `[DecidableEq Fact]`). There was no theorem named `dated_sound`; the gap was that `dated_verdict` covered only receipts built by `issue`. New `dated_sound`: for any receipt R, if `recheck` passes at the stranger's view `w'`, R's dated root is the root of world `w`'s view, and `datedOpens` and `matched` pass, then the row judged at `w` has R's verdict and post root, or the hash collides (from `recheck_covers` (new), `openings_checked`, `Admission.step_of_reads`). `verifyWorld` refuses `openings: the receipt does not open exactly what the row reads` before `recheck`.
- **(b)** `capOpening`: `| none => false`.
- **(c) Trust derived.** There is no `R.supports`; the per-support list is `R.trust`, and the verifier no longer reads its trust from it. New `ceiling ran claimed`, `ran` what the verifier itself checked (`identitySupports`; `worldSupports = trust4`). It refuses a support it ran with no entry (so `[]` is never `checked`), a `checked` claim no check stands behind, and any unrun support not `attested` with a principal. Theorems `ceiling_checked`, `ceiling_empty`.
- **(d) Cited dial re-checks.** `accepts` takes a `Stranger` (naming, hash, reading, view, supports run); `.cited` runs `recheck`, `datedOpens`, `matched` and `ceiling` over the prefix's accumulator, skipping only certificate re-execution; `.bit` alone trusts the producer's bit. New `accepts_cited_sound`.
- **(e) Expected root and quantifier.** `verify j prev root`, `obend verify R [--prev P] [--root N]`; a world-transition is refused without a root (`root: no expected root given…`) or when `R.dated` differs (`root: the receipt is dated at a view whose root is not the expected root`); a world-transition predecessor is refused (no root for it). New `checkQuantifier`: identity receipts `forAll`, transitions `existsRun`, else `quantifier: the law establishes …, the receipt says …`. `negotiationReceipt` takes `shift` (`--shift-clock N`), issuing honestly at the clock-moved view (Astra's probe).

Revised: `recheck_sound` (new instance argument); `recheck_issued` (adds `hr : A.reads (w', a.2) r = A.reads a r`; new `recheck_issued_self` with no premise; `row4_recheck` discharges `hr` by `rfl`); `dial_invariant` (stated for a stranger with `Naming.ofReading`, a view agreeing with the openings and reads, a ceiling-passing support list; cited case via `issue_checks`). Kept unchanged: `receipt_sufficient`, `openings_checked`, `dated_verdict`, `issue_checks`, `overall_none_checked`, `chain_binds`, `receipt4_checks`, `receipt4_dated_verdict`, `pins_sufficient`, `issueLast`.

Forgeries refused by name (`tests/run-receipts.py`):

| forgery | refusal |
|---|---|
| capability opening and its proof omitted | `openings: the receipt does not open exactly` |
| empty support list | `trust: the support legal-fold has no entry` |
| clock-shifted receipt against the run's root | `root: the receipt is dated` |
| quantifier relabelled to `planForAll` | `quantifier: the law establishes existsRun` |
| extra `checked` support nothing runs | `trust: the support oracle claims checked` |
| world-transition verified without `--root` | `root: no expected root` |

The clock-shifted receipt verifies against its own root: the root check is what refuses it.

Controls: receipts 22/22 → 31/31; cohorts 30/30, 71/71, 161/0; workspaces 30/30; walkthrough 26; unchanged. Deviations: the `move_root` tamper is now refused first by the root check; a second case verifies it against its own moved root so `dated: an opening proof does not open` is still exercised. Honest verify calls pass `--root`, taken from the first honest receipt (the test stands in for the authority).

Not bugs: all four findings real. Nuance: the CLI's cited path (`verifyWorld`) already ran `recheck`, `datedOpens`, `matched`; only the abstract `accepts` trusted `R.verdict.isOk` at `.cited`. `dated_sound` did not exist; the missing coverage premise sat in the issued-only `dated_verdict`.

## 3. Fork stitch (`Run/Fork.lean`), commit `f12e474` (802d85e..f12e474), worktree scratchpad/runner2

**The hole, verified.** `stitchRows` committed each escalated `(i, t)` through `ledgerStep L d (.commit i t)` alone: no `crun`, so no protocol state, law or decision citations, selection control or authority judged the row; a refused row left the rows before it committed. `forkStep (.defer i t)` recorded only a token, so nothing the runner could judge.

**What landed.**
- `Fork Tok M E` and `FRow.defer (e : E)` carry an abstract escalated row, unjudged in the fork (`forkStep` takes `tokOf : E → Option Tok` for the `ownToken` refusal). `fork_owns_no_shared`, `fork_spend_notMine` kept (restated over `E`).
- Generic stitch: `replay (step : St → E → Except R St)` runs escalated rows in order; a refusal is a conflict section `(e, r)` that moves nothing; `accepted`; `settle main tentative conflicts` returns the replay only when `conflicts = []`; `stitch step main F = ((settle …, union main.2 F.grown), conflicts)`.
- Joint instance: `Deferred ι S := ι × (Σ i, S.Op i)`, `jstep L base sp au k J e := jrun L base sp au k J (.dispatch e.1 e.2)`, `jstitch := stitch (jstep …)`: each escalated dispatch is judged by runner `i`'s `crun` at main's current World (protocol, law, citations, selection control, authority), then by the ledger's commit row, exactly as a live dispatch.
- `stitch_atomic`:
  ```lean
  theorem stitch_atomic (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
      ((stitch step main F).2 = [] ∧ accepted step main.1 F.escalated = F.escalated ∧
          (stitch step main F).1.1 = (replay step main.1 F.escalated).1) ∨
        ((stitch step main F).2 ≠ [] ∧ (stitch step main F).1.1 = main.1)
  ```
- Kept: `stitch_union`, `stitch_union_comm` (unchanged), `stitch_accounts` (every escalated row is accepted or has a conflict), `stitch_exclusive` (over `jstitch`, via `jstep_exclusive`), `stitch_double_spend` (over `jstitch`: a grant `g` in main's ledger while the fork was offline makes the fork's escalated dispatch consuming `g.tok` a conflict `.taken g.tok g.winner g.epoch`; now takes `JReachable` of main and the runner being at that call). Revised: `stitch_is_commit` is now `JReachable … main.1 → JReachable … (jstitch … main F).1.1` (the former ledger-fold statement is `joint_ledger_fold` applied to it). New helpers: `replay_keeps`, `stitch_keeps`, `replay_append`, `accepted_all`, `jstep_ledger`, `jstep_exclusive`, `jstep_grants`.
- `propagate` returns `Except`: `.ok (propagated L d cs)` when `L.allowed prev d`, `.error (.ledger .notAllowed)` otherwise; `jrun` maps it. `crun_propagated`, `propagate_allowed` (`Proofs/Shared.lean`); `propagate_ok` kept over `propagated`. `jreachable_inv`, `jreachable_fold`, `jrun_height_mono`, `jrun_toks` (`Proofs/Durable.lean`) repaired; the `coupled_after_commit` tooth now mutates `propagate` to `.ok cs`.

**Teeth** (`ForkExample.lean`, tier 2, all bite): `fork_refuses`; `bob_offline_conflict` by mutating `sharedLive` (the former tooth no longer bites: Bob's runner's shared mask refuses him first); `runner_judges_escalation` (stitched into `J₀` where Bob never reserved, his escalated commitment is refused by his own runner and nothing is granted; the tooth is the former stitch, `ledgerStep` alone, which grants it); `two_step_atomic` (Bob escalates his commitment twice into a main where both reserved and nobody committed; the first would commit, the second is refused; the stitch returns one conflict, `grants = []`, Bob's log length unchanged; the tooth is `settle` returning the tentative state). `bob_offline_wins`, `conflict_general` kept.

**Controls.** Tier 1 282, tier 2 303 green; census 35,174 constants, 27 on compiler trust, none on sorryAx or an axiom. Cohorts 30/30, 71/71, 161/0; receipts 31/31 (after the receipts commit); workspaces 30/30; walkthrough 26/26. No deviations.

**Not a bug / caveats.** `propagate` did not swallow errors in any reachable state: `propagate_ok` proved every coupled runner accepts the world event for an allowed move, and `jrun` called it only after `ledgerStep` succeeded (`ledgerStep_allowed`); the `.error _ => cs i` arm was dead code, now a refusal by name. "Bypasses the law judge and citations" is right insofar as `crun` is where those live; `jrun`'s dispatch arm is unchanged, the stitch now goes through it. The old `stitch_double_spend` held unconditionally because the ledger alone judged; the new one needs the runner at the escalated call (otherwise the runner's own refusal is the conflict, which `stitch_accounts` covers).

## 4. Kimi's review findings in receipts and vault, commit `a550bad` (618da4b..a550bad), worktree scratchpad/build

**(1) Receipt replayed against another row** (`Receipt.lean`). `recheck` first checks `N.rowDigest r == R.row`. `recheck_sound` (revised, extended) concludes `N.rowDigest r = R.row ∧ N.root rest = R.pre ∧ verdict ∧ post`; `recheck_covers`, `recheck_issued`, `recheck_issued_self`, `dated_sound` re-established with unchanged statements (the new conjunct is `rfl` for issued receipts). New test: the disclosed `rowData` replaced by `dispatch commit p1`, refused `row: the disclosed row is not the receipt's`. Not a CLI bug: `verifyWorld` already compared `naming.rowDigest row` with `R.row`; the gap was in the abstract `recheck`, `recheck_sound` and `accepts`.

**(2) A kind change judged by the old laws** (`Vault/Store.lean`, `commit`). New `lawsKept old new := lawLines old == lawLines new && kindLine old == kindLine new` replaces the law-line comparison; retargeting `kind:` goes through the adoption branch (needs `relaw`, judged by `newLaws`); the write branch judges by `newLaws`, equal to the old by `lawsFor_of_kept`, so `oldLaws` is gone. Refusal: "refused: changing a law line or the page's kind is the owner's (… has no relaw grant on …)". New: `lawsFor_of_kept`, `kindChain_of_kept`, `commit_kind_needs_relaw`. Tooth: `#tooth lawsFor_of_kept by mutation lawsKept := fun old new => lawLines old == lawLines new` bites. The kind line, not the chain, is compared: the chain is a function of page name and kind line, and the laws read the kind line through `kindLaws`' `named`.

**(3) Section 0 aliasing section 1** (`Store.lean`, `selectIn`). New `sectionAt G k := if 1 ≤ k then (sections G)[k - 1]? else none`; `sectionAt_zero`, `select_section_zero_refused`; tooth by mutating `sectionAt` to the unguarded form bites.

Controls: receipts 32/32 (one new); cohorts 30/30, 71/71, 161/0; workspaces 30/30; walkthrough 26; tier 1 282, tier 2 303; census 35,194 constants, 27 on compiler trust, none on sorryAx or an axiom. No deviations.

## 5. Round 2: the arm binds the payload at the scrutinee's quantity (decided 11-01)

The coordinator took the alternative named in §1: matching passes the payload to the selected arm as
an argument, so the arms bind it at a quantity the scrutinee allows, and a `linear` sum is matched.
This replaces round 1's `linearFree` scrutinee premise and its `done` premise.

**The rule** (`Core/Check.lean`). `ArmsTyping` gains a quantity index `q`; each arm binds
`⟨payload, q⟩`, with `validContext [⟨payload, q⟩]` (a shareable payload type when `unrestricted`,
replacing the old unconditional shareability premise) and `q.fits (bu.headD 0)` (exactly once when
`linear`). `case` and `effectCase` require `caseAllowed q context su`:
`(q == .linear || linearFree context su) && (q != .unrestricted || reusableCaptures … su)`, the quantity
clauses of `argumentAllowed`. A `linear` scrutinee therefore binds a `linear` payload used once; one
with `affine` captures binds at most `affine`; `unrestricted` needs reusable captures. `done` has no
premise again: `case (done (l h)) of l x. done 0` is refused at the arm, whose payload is `linear`.

**The checkers.** The bidirectional checker takes `q` from the case annotation's `parameter` when the
case is annotated, and otherwise computes `caseQuantity` (`linear` if the scrutinee uses a `linear`
hypothesis, else `unrestricted` if its captures are reusable and every arm's payload is shareable
(`armsShareable`), else `affine`), the most permissive quantity `caseAllowed` admits (`caseQuantity_allowed`).
`ArmsAgainst` records the quantity its arms were checked at, so the `caseAllowed` premise is checked on
the answer (a dependency on the computed quantity broke the completeness rewriting otherwise).
Refusals: an arm that does not use its `linear` payload is `linearScrutinee path` (the arm's path; the
constructor lost its index); an annotation whose quantity the scrutinee does not allow is
`linearArgumentDropped path index q` or `capturesNotShareable path` (`caseRefusal`). `linearReturned`
is gone. Preparation (`Elab/Prepare.lean`) computes the same `caseQuantity` from
`occurrences context.length scrutinee` and prepares the arms in that context. The legacy fuel checker
`Check.infer` binds every payload `unrestricted` (so it accepts only scrutinees with reusable captures):
a quantity computed from the uses would move under substitution, and `infer_msubst`/`infer_instantiate`
are proofs about that executable function.

**Metatheory (all green, tier 1 283 jobs, tier 2 304).** Weakening (`case_allowed_insert`), closed
substitution (`caseAllowed_append_zero`, `caseAllowed_of_le`; the arm's `fits` through `UsesMasked.headD`),
templates (`Discharges.caseAllowed_instantiate`, `validBinder_instantiate`), the machine
(`MachineTyping.FrameTyping.case`/`effectCase` carry `q`; `typed_case_preserved` binds the payload
cell at `q`, its non-computation from the heap's address type instead of shareability), bidirectional
completeness (`completes_case`/`effectCase` annotate the case node with the derivation's `q`;
`arms_cons_complete` takes `fits`), preparation (`ArmsMotive` is quantified over a checker quantity
`q'` that refines the derivation's, `ArmRefines`, arm by arm `QuantityRefines`; `caseQuantity_refines`
and `armsShareable_of_unrestricted` show the computed quantity refines any derivation's), Law typing
(`chk_case`: a clean context computes `unrestricted`). `complete`, `full_annotated`, `prepare_checks`,
`check_msubst`, `checked_msubst` and `step_conserves_linear` keep their statements (STATEMENT-CITED in
the journal, rebuilt green). In `step_conserves_linear`'s `caseInject` case the binder is now `q`, and
`fits_once` with `caseAllowed` gives the argument's count once, as in beta.

**Revised** (journal, `08bc950` → round 2): `completes_case`, `completes_effectCase`, `completes_done`,
`arms_cons_complete`, `arms_nil_complete`, `arms_typing_find`, `arms_uses_length`, `stack_effect_case`,
`infer_transport`, and the private `arms_find`, `arms_row_closed`, `arms_typing_absent`,
`stack_case_value`, `infer_msubst`, `Discharges.infer_instantiate`, `armsMotive_cons/nil`,
`membersAgree_of`, `members_of_variant`, `motive_case`, `motive_effectCase`, `checkArms_ok` (Law); plus
`CheckTeeth.shadowed_shareable_member_accepted`.

**Teeth** (`LinearTeeth`). `case_scrutinee_refused`: `λh. case l h of l x. 0` at `linear` is
`linearScrutinee [0, 1, 0]` (`#tooth` to `affine` bites); `case_scrutinee_refused_unannotated` (the
checker computes `linear` itself); `linear_sum_matched`: `λh. case l h of l x. x` is accepted at
`linear`; `linear_scrutinee_unrestricted_payload_refused`: annotating the payload `unrestricted` is
`linearArgumentDropped [0] 0 .unrestricted`; `done_value_refused` is now the arm's `linearScrutinee
[0, 1, 0]`. The one- and two-step drop witnesses are unchanged.

**Deviations.** `CoerceProbes`: the `linear → linear` sum codomain coercion checks again (round 1
refused it). `CheckTeeth.shadowed_shareable_member_accepted`'s hypothesis is now `unrestricted` (the
legacy checker needs reusable scrutinee captures; `shadowed_linear_member_refused` stays refused).
Controls unchanged: cohorts 30/30, 71/71, 161/0; receipts 32/32; workspaces 30/30; walkthrough 26.
Census after rebasing onto `39932d9` (the Expose lane's per-definition `@[expose]` in `Check` and `Ty`, kept; `caseAllowed` and `caseQuantity` exposed): 35,625 constants, 27 on compiler trust, none on `sorryAx` or a declared axiom.

**What remains.** `Check.infer` is stricter than the relation (only reusable scrutinee captures); it is
the checker Gemini's review says to retire. `affine` copying through `case` is closed by the same rule
(an `affine` scrutinee binds an `affine` payload).

## 6. Pass 3: source subject reduction (Gemini's second review §6)

Brief: `scratchpad/sound/SUBJECT-REDUCTION-BRIEF.md`. Worktree `scratchpad/kinds`, branch `lane-sound`
on `2e70070`. Two new tier-1 modules beside `Conservation`, theorems only: `Core/Proofs/SubjectReduction/Substitution.lean`
(typed open substitution, 646 lines) and `Core/Proofs/SubjectReduction.lean` (inversions, the step
theorem, the chain, the custody corollary, 914 lines); both in the census. No rule, checker or
executable changed. `steps_conserve_linear`'s docstring now points at its discharged form.

**Typed open substitution** (`subst_typed`, private). The induction of `subst_counts`, producing a
derivation: if `σ` puts `A` at `d` (`SubstAt`), `A` checks in `Γ.eraseIdx d` at the binder's type and
uses its hypotheses as an argument to that binder may (`TSub`: `linear` binder or `linearFree`;
`unrestricted` binder only with reusable captures), and `Image d ua u` is safe in `Γ.eraseIdx d`
(`Budget`), then `t.substitute σ` checks in `Γ.eraseIdx d` at the same type with uses pointwise
`≤ Image d ua u` (equal at `linear` positions by `subst_counts`). Every premise transports:
`linearFree`, `reusableCaptures`, `argumentAllowed`, `caseAllowed`, `reusableAllowed` from `≤ Image`
and the binder's quantity condition; `safeUses` of inner binders from the budget (it passes under a
binder as `ub[0] :: Image`, from the binder's own `safeUses`); `fits` from `≤` plus equality at a
`linear` binder; `branchesAgree` from equality at `linear` positions. All cases proved, none isolated.

**The step theorem** (`Core/Proofs/SubjectReduction.lean`):

```lean
public theorem step_preserves_typing {a : Assumptions} {Γ : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) {t' : Term} (step : Step t t') :
    ∃ T' u', PartialTyping a Γ t' T' u' ∧ safeUses Γ u' = true ∧ Below Γ u' u ∧
      (∀ j, LinearAt Γ j → u'.getD j 0 = u.getD j 0) ∧
      (sameType a T' T = true ∨ RowRefines a T' T ∨
        (t = .done t' ∧ ∃ P R, sameType a (.computation P R T') T = true))
```

`Below Γ x y`: `x[j] ≤ y[j]` at every position not `unrestricted`. `RowRefines a T' T`: both finite
rows, and every `T.lookup` is answered by `T'.lookup` with a `sameType` member. Every rule is
proved; the redexes: `beta` and `caseInject` by `subst_typed` (the budget from `safe`: the binder is
used at most once unless `unrestricted`, in which case the argument's captures are reusable), the
arm's payload type transported to the injection's through `variant_components` and lookup
transport; `successor` the same with a literal; `field` through lookup transport and the first
field found; `applySpecification`, `reflect`/`metadata`/`project` through `*_components`; `fix`
builds `app (app spec (fix spec inh)) inh` from its own derivation (reusable captures, so
`Below` everywhere); `mix` is `reusable_mix_body`; `primitive` types its literal. Congruences: a
`done` that steps under `effectCase`'s scrutinee turns it into a plain `case` (the arms already
return the activity); under any other frame it is refuted (`isComputation`).

**What resisted, and is stated instead: `extendRecord` does not preserve the type up to
`sameType`.** The brief's statement (`∃ u', PartialTyping a Γ t' T u'` except at a root `done`) is
false: `extendRecord_changes_type` proves that `{a = h} with {a = 0}`, `h` an `affine` custody
handle, checks at `{a : ℕ, a : custody 0}`, steps to `{a = 0}`, and no type of `{a = 0}` is
`sameType` to the old one (`TypeGraph.equivalent_shareable`: the old type is not shareable, every
type of the reduct is). `overlay` keeps a shadowed member, and canonical rows forget it only when it
is shareable (`Ty.insertCanonical`), so the old type remembers what the new record dropped. The
machine never meets this: its record values are typed by lookup (`ValueTyping.record`), not by
row structure. So the theorem's second disjunct is `RowRefines`, which is exactly what the
frames that can hold a record need (`get` looks up, `extend` needs a finite row and lifts it through
`overlay`: `overlay_refines`), and is refuted under every other frame (`finiteRow_nonrow`). This
needs no change to the rules; whether `extendRecord` should be type-preserving (e.g. an `extend`
that requires shareable shadowed members, or `overlay` that drops them) is a language decision.

**The chain** (no typing premise on intermediate terms):

```lean
public theorem steps_conserve_linear' {a : Assumptions} {Γ : Context} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) (steps : Steps t t') {j : Nat} (lin : LinearAt Γ j) :
    (occurrences Γ.length t').getD j 0 = (occurrences Γ.length t).getD j 0
```

from `steps_preserve_typing` (every term along the reduction checks, within budget, with the initial
`linear` counts).

**Closed programs over custody handles** (`custodyContext k`: handle `n` is `⟨.custody n, .linear⟩` at
index `n`):

```lean
public theorem custody_conserved {a : Assumptions} {k : Nat} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a (custodyContext k) t T u) (safe : safeUses (custodyContext k) u = true)
    (steps : Steps t t') {j : Nat} (hj : j < k) :
    (occurrences k t').getD j 0 = u.getD j 0
```

**Builds and controls.** On `2e70070`: tier 1 285 jobs, tier 2 306, green; census 36,242 constants, 27
on compiler trust, none on `sorryAx` or a declared axiom. After rebasing onto `c67f197`: tier 1 290,
tier 2 314, census 37,299 constants, 27 on compiler trust, none on `sorryAx` or an axiom. Cohorts 30/30, 71/71, 161/0; receipts 32/32; workspaces
30/30; walkthrough 26: unchanged. Added public: `step_preserves_typing`, `steps_preserve_typing`,
`steps_conserve_linear'`, `custody_conserved`, `extendRecord_changes_type`, `RowRefines`, `Below`,
`Retyped`, `custodyContext`. Revised: none (one docstring).
