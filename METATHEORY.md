# The mechanized metatheory: what finished looks like, and the compositional shape

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

So `Obend.Slot.Calculus` splits into `Calculus` (with `Typed : Ctx → Tm → Ty → Prop`, `msubst`, and
the substitution law on `Typed`) and `Decides R` (the graded procedure with soundness, monotonicity
and completeness-at-some-grade under an explicit coverage premise). The slot's theorems quantify over `Typed`; admission quantifies
over the grade the world granted. Nothing about fuel appears in a statement about meaning again.

## 2. The remaining theorems, and the tool each wants

| theorem | tool | reference | why that tool |
|---|---|---|---|
| `mix` associative up to `≈b`; `≈b` itself | a step-indexed logical relation over the lazy heap, in **Iris-Lean** | Moran–Sands, *Improvement in a lazy context* (1999); Hackett–Hutton, *Call-by-need is clairvoyant call-by-value* (2019); Iris-Lean core ported, adequacy layer in progress (arXiv 2609.24252, PR #394) | the demand machine has update frames, blackholes and cyclic heaps; the Representation docstring already says "cyclic heaps require a graph logical relation"; Iris's later modality is the standard way to hide the step arithmetic, and improvement theory is the cost-sensitive equivalence we want, since `≈b` on completed runs is too weak for a resource-priced world |
| surface semantics (LT3), C4 ordered-presentation invariance | the lowering as the definition, proofs by induction on the AST; **proof by reflection** (`decide`) for C4 and the contract algebra | `OBJECTIVE-BEND-FRONTEND.md`; fareoo `ltuo-objective-bend` §5 | finite combinatorics; the 4000 seeded vectors become one decidable statement |
| bounded completeness; `prototype` provenance | ordinary induction over `Steps`/`MachineSteps` | `OBJECTIVE-BEND.md` §Open | nothing new |
| Law inheritance (`effective_law_eval`, `inherited_never_widens`, `c3_tree_is_chain`), `keeps` | ports of nano's and the Faré audit's statements over Core4 laws | nano LANG-20/92; `AUDIT.md` §1 | well-specified already |
| B4/B4′ at a real kernel | the `World` class lane A built, instantiated by minidregg's and nano's histories | DESIGN-CTX §2.4 | the class exists; the instances are the trees' own theorems (`receive_congr`, `stale_behind_forever`, `ObjectHistory`) |
| Leaf refinement: a Core4 run equals BendTT's `Eval` of the emitted book | **interaction-tree simulation** (Core4's `Interaction` is already itree-shaped) against `bendtt.lean`'s big-step `Eval`; **Pyrosome** for the modular compilation structure | Xia et al., *Interaction Trees* (2020); *Pyrosome: Verified Compilation for Modular Metatheory* (2025); `bendtt.lean` (4043 lines, Lean 4.34) | the one theorem that needs another tree's semantics; forces the toolchain decision (4.30 → 4.34, or vendor BendTT) |
| Doc: pushout universal property for the patch representation | definitions, then one universal-property proof | Mimram–Di Giusto (2013) | new but small |

Iris-Lean is called for in exactly one row, the first, and it is the row that gives the thesis its
teeth: it is where "laziness is a semantic choice" becomes a proved cost-sensitive equivalence over
a shared heap rather than a slogan. It is not called for in Core typing, Spec, Law or Slot.

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

- `obend_cases` (above) and `fuel_lift` (apply `check_mono` / `Graded` monotonicity to raise a
  judgment's grade to a common bound, so no proof mentions `n + m` by hand).
- `#tooth T by mutation`: a command that applies a stated mutation to a definition in a scratch
  environment and checks the theorem `T` *fails*; the trees do this by hand today with planted
  files. A green that cannot red is not evidence; this makes the red mechanical.
- `#pin` is `#assert_axioms` (exists); `lake check` with independent kernels for the pins once the
  toolchain moves; `decide +kernel` in place of `native_decide` where it is fast enough, so fewer
  compiled-trust pins.
- `grind` configurations per module (`Core.Proofs.Preservation`, `Collect`) for the arithmetic and
  row lemmas; Aesop as a Mathlib-free dependency only if `grind` falls short.

## 5. Order

1. Landed: meaning/procedure/budget split, fuel-free semantic substitution, generic traversal
   laws used by existing metatheory, and `obend_cases`/`fuel_lift`/`#tooth` used in the library.
   D12 is closed at meaning; procedural completeness is explicitly conditional, with pinned
   obstructions to the stronger claim. See `astra/ASTRA-IMPL-REPORT-20261030.md`.
2. Landed: the `hole-exercise` branch, merged after the whole exercise and its pins passed.
   The before/after journal comparison and actual proof repairs are recorded separately in
   `astra/HOLE-REPAIR-SET-20261030.md`. The corrected journal closure is used for the comparison.
3. `Obend.Spec` is landed by lane C. Law and inheritance are the concurrent active lane;
   B4/B4′ already have the toy World, with production history instances still to integrate.
4. Decide the checker coverage design: align procedure with declarative typing, or state an
   independently characterized checking fragment. More fuel cannot fix the proved obstructions.
5. `≈b` via Iris-Lean, as its own lane with its own toolchain decision.
6. Leaf refinement against `bendtt.lean`.

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
