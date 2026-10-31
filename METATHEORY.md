# The mechanized metatheory: what is proved, what remains, and the tools

Revised 2026-11-01. §1 (the meaning/procedure/budget split) and §6 (checker alignment) are landed and
kept as the record of why; §2 is the live table; §3 and §4 are the extension and tactic disciplines.

Draft 1, 2026-10-30, after lanes A and B. Companion to `DESIGN.md` and `SHIP.md`. Ember's ask:
"a kickass mechanized metatheory for this whole thing and hook up custom tactics, program
logics/iris-lean (if called for)", and D12 "more parametric/somehow compositional."

## 1. D12, resolved by separating meaning from procedure

Lane A found that the slot's judge at Core4 is `check` at a fixed fuel and that judge is not closed
under substitution: `check_msubst` holds at fuel `n + m`, so a filling that passes the judge can
yield a filled term the same judge refuses for depth. That is step-indexing wearing a type
checker's clothes, and the fix is the one every step-indexed development makes:

- **Meaning is fuel-free.** `PartialTyping Ψ t A` (the derivation `Checked` already carries) is the
  typing judgment. The substitution lemma is stated there: `checked_msubst` proves it by induction on
  typing evidence. Checker soundness alone cannot prove it: some semantic derivations are
  never recognized by the checker.
- **The procedure is graded.** `check : Fuel → Ctx → Tm → Ty → Option Checked` with `check_mono`
  (lane A proved it) and conditional completeness on the recognized fragment.
  `CheckCompletenessObstruction` pins counterexamples even with complete lambda annotations;
  `Recognized` explicitly records eventual algorithmic success and is not claimed decidable. Generalize the index to any ordered commutative
  monoid `R` with a typeclass `Graded R`: fuel is one instance; the machine's ticks, heap and
  extraction budget are others. The law reads `grade (msubst σ t) ≤ grade t + Σ grade σ`, and the
  arithmetic of `n + m` becomes the monoid law, stated once.
- **The budget is declared.** `slotOf` takes a `Budget R`; the toy World supplies it from
  its view. Admission names a failed invocation `uncovered`, and Integrity's resolver diagnostic
  connects that name to an actual failed candidate with live ordinary supports. The generic Slot
  retains its existing refusal API. A budget is not semantic typing, and `uncovered` does not
  assert that more fuel alone can repair the term. Recording grants as audited World facts is
  a subsequent integration, not a claim of this implementation.

So `Obend.Slot.Calculus` split into `Calculus` (with `Typed : Ctx → Tm → Ty → Prop`, `msubst`, and
the substitution law on `Typed`) and `Decides R` (the graded procedure with soundness, monotonicity
and completeness-at-some-grade under an explicit coverage premise). (2026-11-01, lane Parsimony: each
class had one instance and `Graded` had one, `Nat`, so `Typed` and the substitution law are Core4's
own definitions, the procedure is the `Judge` instance `bidirectional`, and grades are `Nat`;
`REPORT-PARSIMONY-20261101.md`.) The slot's theorems quantify over `Typed`; admission quantifies
over the grade the world granted. Nothing about fuel appears in a statement about meaning again.

## 2. The remaining theorems, and the tool each wants (revised 2026-11-01)

| theorem | status | tool |
|---|---|---|
| `mix_assoc` under `≈b` (completed-run equality) | PROVED, `Obend/Equiv` (needed `Ahead`, reduction under binders; the "few β steps" premise was false) | parallel reduction, determinism |
| `≈c`: cost equivalence with explicit constants; ticks within a constant of clairvoyant call-by-value cost | OPEN; `review/EQUIV-PLAN-20261031.md` definition 2; `mix_assoc` differs by at most 7 ticks on the machine | Hackett–Hutton over Core4's binding sites; no heap |
| the heap-indexed relation (sharing identity, effects under update frames, space) | OPEN; Iris-Lean is usable from this tree (4.35, modules, adequacy landed) but has no binary logic or time credits | Iris-Lean, only when a statement needs it |
| source-to-machine completeness of the demand machine (`Representation`) | PARTLY: `coreRepresentation` inhabited for closed sources (`Core/Proofs/Completeness`); administrative progress open | induction over `Chain` |
| checker completeness | PROVED on the stated fragment (`complete`), full annotated completeness (`full_annotated`), executable preparation on the alias-free fragment (`prepare_checks`) | bidirectional checker, finite bisimulation |
| law inheritance, `keeps`, machine-judges-relation | PROVED (`package_never_widens`, `judgeEffective_names`, `chain_keeps`, `judge_sound`/`judge_complete`, `legal_law_admitted`) | Core4 terms, machine probe |
| C4 `linearize` correct on general graphs | OPEN; proved on trees (`c3_tree_is_chain`), checked elsewhere (`precedence`, refused `unordered`) | structural rewrite of `linearize`, then monotonicity and local precedence proved |
| B4/B4′: `Integrity.contextual`, `repair_sound`, `incumbentTransition` | PROVED over every `World`; `repair_of_contextual` shows B4′ was a corollary | the slot calculus |
| shared-World exclusion | PROVED (`joint_reachable_ticket_exclusive`, `joint_once`, `loser_refused_names_winner_and_epoch`); projection by each runner's reachability, not yet the generic `project_run` | the audited fold |
| Doc pushout universal property | PROVED (`merge_isPushout`, `pushout_unique`, `no_cocone`, `files_no_pushout`) | thin category, join |
| leaf refinement: a Core4 run equals BendTT's `Eval` of the emitted book | OPEN; toolchain decision (BendTT at 4.34) pending | interaction-tree simulation through the runner's adapter |
| `quote`: observer ladder, `rewrite_sound_below`, erasure and preservation | OPEN; gated on `review/QUOTE-ORIENTATION-20261101.md` | typed represented syntax first; CMTT substitution; two-level staging results |
| judgment class soundness per format; one foreign certificate format | IN PROGRESS (Judge lane) | `Decides` generalized; LRAT or PBLean |

## 3. The extension problem, and what keeps it from being a rewrite

Every `cases`/`induction` over `Term` (24 constructors) gains a case when CARD 9 (B) adds
`hole n σ`, and again when Leaf adds whatever it adds. Three layers of defence, cheapest first:

1. **Generic traversals once.** `rename`, `substitute`, `uses`, `scoped`, the `Yields` frames and
   their congruence lemmas are all one traversal shape; a `TermF` functor view with a `Traverse`
   class derives them, so a new constructor is one instance clause and the generic lemmas hold.
   This is "Meta-theory à la carte" (Delaware et al. 2013) in the amount Lean makes cheap, not the
   full feature-algebra apparatus.
2. **A case-generating tactic.** `obend_cases t with simp_set`: run the module's simp set and
   `grind` on every constructor, leave only the arms that fail. On the 1514 theorems, a new
   constructor then costs exactly the arms that mention it.
3. **The journal watches.** Lane B's obligation journal reports the exact repair set by name
   (statement-cited vs proof-cited); the `hole n σ` exercise is the first thing it should watch.

## 4. Custom tactics and commands worth having

- `obend_cases` (above). (`fuel_lift`, which raised a judgment's grade through `Graded`, was built,
  lost its last use, and was deleted on 2026-11-01.)
- `#tooth T by mutation`: a command that applies a stated mutation to a definition in a scratch
  environment and checks the theorem `T` *fails*; the trees do this by hand today with planted
  files. A green that cannot red is not evidence; this makes the red mechanical.
- the axiom check is one census, `#assert_axioms_tree` in `Obend/Census.lean` (exists; the
  per-theorem lists are gone); `lake check` with independent kernels once the toolchain moves; `decide +kernel` in place of `native_decide` where it is fast enough, so fewer
  compiled-trust pins.
- `grind` configurations per module (`Core.Proofs.Preservation`, `Collect`) for the arithmetic and
  row lemmas; Aesop as a Mathlib-free dependency only if `grind` falls short.

## 5. Order

The order is kept in `PLAN.md`.

## 6. Checker alignment (added 2026-10-30, after Gemini Argon's analysis)

The procedure is provably incomplete for `PartialTyping` (`Core/Proofs/CheckCompletenessObstruction.lean`).
The plan, checked against the code in `review/ARGON-RESPONSE-20261030.md`: separate transparent
aliases from rigid bounds and make `sameType` a hereditary, visited-set-bounded equivalence; put
`sameType` plus `conversion` at every join in the existing checker; build a bidirectional checker
beside it with uses synthesized inline and refusals that name the rule and the path; define
`Covered := checkCovered` syntactically and prove direct completeness on it plus full completeness
through `annotateFromDerivation`; swap the Core4 `Decides` instance. §1's correction: usage
accounting is already a synthesized output and stays inside the checker; no solver pass. Solvers
belong only in the member-side elaborator that finds annotations, never in admission.
