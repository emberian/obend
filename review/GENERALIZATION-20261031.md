# What the studies generalize to

Claude, 2026-10-31, after reading in full: `review/GENERATED-20261031.md`, `astra/ASTRA-EFFECT-LAWS-20261031.md`,
`review/ALGEBRAIC-SUBTYPING-20261031.md`, `review/SYNTHESIS-20261031.md` (and its refutation in
`REPORT-JUST-20261031.md`), `review/EQUIV-PLAN-20261031.md`, `astra/ASTRA-SELECTION-20261031.md`,
`astra/ASTRA-EVAL-20261031.md`. Written for Ember. Not a plan of experiments: the generalizations
below are modules, and the one already in flight is being built as a module.

## 0. Two corrections first

**Oracle7.** The effect-laws brief pointed Astra at veri7vn's `logic` provider because it is the one
Oracle7 artefact a node can re-check (a stable model under the Gelfond–Lifschitz reduct). Ember's
picture, Oracle7 judging plain-language propositions, is a different thing and the design already has
the honest place for it: Astra's third trust mode, a *named attestation* (`analyst says φ`, signed,
under delegation, withdrawable by revision), where the theorem concludes that an authorized live
assessment was relied on, never that φ holds. That is the hybrid-intelligence seam and it is not
built; nothing in it requires the model checker. We should stop saying "Oracle7" when we mean the
reduct checker, and say "attestation" when we mean the language model.

**Experiments.** Three studies ended with "the one-day experiment". Those are retracted as gates.
Each is restated below as the module it was testing.

## 1. What the studies agree on

Read together, the seven documents converge on four findings and one destination.

1. **The library is set-level on purpose, and admission is a fold.** Every equation the admitter
   needs is definitional (GENERATED §0); `Legal`, the law judge, `checkAt`, `Doc.apply`, the journal's
   closure and `obend open` are each a fold over rows with an accumulator and witnessed oracle reads,
   and a row's verdict depends only on the pins of the facts it reads (`holds_congr`, `read_congr`).
   The semiring of justifications was the wrong generalization of this (the proofs did not shorten,
   `REPORT-JUST` §3); the fold is the right one, because it is already true of every module and
   decides what a receipt is.
2. **A judge is a certificate checker over a declared domain.** The checker is bidirectional and
   total with a work grade; the law judge is a machine probe with `judge_sound`/`judge_complete`; the
   coercion emitter re-runs the checker; Astra's four designs each name the object judged (a plan and
   its continuation, a joint transition system, a set of traces, a stable model) and the certificate
   a node re-checks. The meaning/procedure/budget split of `Decides` is the pattern, and it is the
   project's trust rule: search belongs to the producer, checking to every node.
3. **Every reference across a boundary is an intention, and an intention is a slot whose candidates
   are pins.** Package parents (built: `stale_iff_blocked`), cites (built: identity and byte cites),
   kinds (pending the nominal decision), leaf proofs (`leafProof`, designed), attestations and
   stable-model evidence (Astra D), a chooser's office (SlotRun's tenure). The two structures of the
   synthesis meet only here, and the Extends and Vault lanes built the first two instances without
   sharing a definition.
4. **Knowledge is dated and distributed; coordination needs a shared step.** `read_congr` is
   distributed knowledge over pin-holders unfolded; a receipt certifies "usable at v"; Halpern–Moses
   is the reason several runners need an atomic shared commit before any joint property is a theorem
   (GENERATED §3, Astra B). The quantifier shape of a claim (`∃M ∃run`, `∃plan ∀M ∀r`, `∃policy ∀M ∀r`,
   `∀M ∃plan`) is part of what a receipt must say (Astra §6).

The destination all three Astra studies and the epistemic reading point at: a system that can say
what it thinks might happen, what survives every declared alternative, which observation would change
its recommendation, and what has already left the machine and cannot be undone.

## 2. The generalizations, as modules

**G1. `Obend/Fold.lean`: the audited fold.** A structure `Admission Row Acc Fact` with `step : Acc →
Row → Except Clause Acc`, `reads : Acc → Row → List Fact`, and the law `step_of_pins` (two
accumulators differing only in the world agree on a row whose reads have equal pins). Theorems once:
`receipt_sufficient` (a stranger holding the accumulator's roots and the cited openings recomputes the
verdict), composition (the product of two folds over interleaved rows with a shared component, which
is the shared-World layer), projection (a component's own rows recover its own fold), and the cost
accumulator as a second, tropical, component (ticks, `checkWork`, heap). Instances: `Legal`
(`legal_iff_fold`), the law judge, `Doc.apply`, the journal closure, `Vault.open`. This is what the
Shared lane is now building the composition layer on, and what `legal_iff_fold` was the spike of.

**G2. `Obend/Judge.lean`: the judgment-domain class.** Generalize `Decides` from typing to every
judge: `Judge Obj Cert R` with a deterministic `check : R → Obj → Cert → Verdict`, `sound`,
`complete` on a stated fragment, monotone in the grade, with a refusal naming the clause and path.
Instances today: the bidirectional checker, the law machine probe, `coerce`, the protocol envelope
(`HasProt`), C4's checked linearization; designed: the product invariant for a two-run hyperlaw, the
reduct checker for a stable model, the attestation verifier. A registry of these is Astra's §7 made a
typeclass, and it is what lets a kernel accept a certificate it did not search for.

**G3. `Obend/Intention.lean`: references as slots.** One structure for a named reference resolved
against a World: candidates are pins, the chooser is the name's owner, the support is "the record
names v at p", staleness is the blocked read. Instances: package parents (re-based onto it from
`Spec/Ecosystem`), cites (from `Doc/Section`), kind references, leaf proofs, attestations. With it,
`resolve` on a specification DAG, `recite` on a document and `renew` on a lease are one repair action.

**G4. `Obend/Receipt.lean`: the receipt type.** The inventory found none (GENERATED §0): a receipt is
`{pre post : Root; row; law : Digest; pins : List (Cell × Option Pin); verdict; quantifier :
Shape; trust : checked | attested; dated : View}` with the dial (full log, cited openings, one bit)
as three projections and `receipt_sufficient` from G1 as its theorem. Refusals are receipts whose
verdict names the clause and, where one exists, what would pass; Astra's `Refusal` outcomes
(`noAdmissible | awaitingChoice | preferenceKept | candidateRejected | staleEvidence | executionFrozen`)
are its verdict constructors.

**G5. Laws over declared domains.** With G2 in place, `law` gains a domain keyword: `law L on write`
(today), `law L on plan P` (A: envelope and monitor over the yielded tree, judged at install and
rechecked at dispatch through the adapter), `world law L for W` (B: the joint invariant, judged at the
shared commit), `hyperlaw L on P` (C: a product invariant over admitted traces, judged at install),
and a support that is an attestation or a checked model (D). Each is an instance of G2 with its
certificate, and each refusal is a G4 receipt. B is being built now; A is the next, because the
protocol typing already carries its judgment; C and D wait for B's shared step, for the reason in §1.4.

## 3. What this costs and what it refuses

Additive in `Core` (nothing changes), a redefinition under kept statements in `Run` (Legal as a fold
instance), `Spec/Ecosystem` and `Doc/Section` (intentions), and new modules otherwise. The journal
measures the cascade as before. Refused, with the studies' reasons: the semiring as construction
(kept as provenance for explanations); HoTT beyond pages and the tree; circuits in the TCB (the fold
is the shape a circuit would take, which is why G1 is worth having, and the charters still say no);
epistemic logic as the logic of joint invariants (it is the logic of receipts and of why B precedes C);
Oracle7's reduct checker as anything but one certificate format among several.

## 4. Order

Shared (G1's composition, in flight) → G1 stated as the structure with Legal, the law judge and
`Vault.open` as instances → G4 with the dial → G3 re-basing Extends and Vault's references → G2 with
the five existing judges → G5's `law … on plan` → the attestation support (the hybrid seam, D's third
mode) → C's two-run fragment. The template elaborator by Simple-sub (ALGEBRAIC §6) and `≈b` by
clairvoyant cost (EQUIV §5.2) run beside these; they touch neither the fold nor the judge class.
