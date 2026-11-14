module
/-
# Obend.Spec.Proofs.FrontEndAdequacy — what the front end's acceptance buys, on the ELABORATOR's term

`Obend.Spec.FrontEnd.Accepted l` is the front end checking its own output: the packet it rendered
decodes (with the checker's decoder) to exactly the erasure of the elaborator's annotated term
(`packetTerm`, proved by `Obend.Spec.Proofs.TermWire.decode_json`), and the proof-producing checker
accepted it closed. Composed with the Core4 metatheory this gives, for every program the front end
accepts:

* `accepted_typed`: the erased elaborator term is closed and has the checker's typing derivation;
* `accepted_never_refused`: the bounded demand machine never refuses it, at any tick, heap or stack
  budget (it finishes, yields, suspends or blackholes);
* `accepted_execution_semantics`: a finished bounded run of it extracts THE deep source evaluation
  of that term (`deepEvaluates_unique`): a Data deep-evaluates the term exactly when it is the
  extracted Data, under every policy and budget.

The compiled surface `.obend` acceptance vector (`accept_inhabited`) lives in Tier-2A
`tests/extracted/SpecLawVectorsTest.lean`. Statements as in minidregg
`Compiler/ObjectiveBendFrontEndAdequacy.lean` (commit 092027a2); `Accepted.sound` is in
`Obend.Spec.Proofs.TermWire` with `packetTerm`, which it cites.
-/
public import Obend.Spec.FrontEnd
public import Obend.Core.Proofs.Preservation
public import Obend.Core.Proofs.DataSoundness
public import Obend.Core.MachineTyping
public section
namespace Obend.Spec.Proofs.FrontEndAdequacy
open Obend.Spec.FrontEnd
open Obend.Core.Check
open Obend.Core.Machine
open Obend.Core.Proofs.DataSoundness
set_option autoImplicit false

theorem accepted_typed (l : Lowering) (a : Accepted l) :
    l.term.erase = .ok a.erased ∧
    PartialTyping a.source.assumptions [] a.erased a.typed.type a.typed.uses ∧
    Obend.Core.Invariant.Scoped 0 a.erased := by
  have derivation := a.typed.derivation
  have term : a.source.erase = a.erased := by rw [a.sourceExact]; rfl
  rw [term] at derivation
  exact ⟨a.erasure, derivation, Obend.Core.MachineTyping.source_scoped derivation⟩

theorem accepted_never_refused (l : Lowering) (a : Accepted l) (limits : Limits) (ticks : Nat)
    (reason : Refusal) (retained : State) :
    runBounded limits ticks (initial a.erased) ≠ .refused reason retained := by
  have := Obend.Core.Proofs.Preservation.checked_runBounded_no_refusal
    a.source a.typed limits ticks reason retained
  have term : a.source.erase = a.erased := by rw [a.sourceExact]; rfl
  rwa [term] at this

theorem accepted_execution_semantics (l : Lowering) (a : Accepted l) {policy : State → Bool}
    {limits : Limits} {budget : Obend.Core.Data.Budget}
    (execution : Obend.Core.Data.ExecutionWith policy limits budget a.erased) :
    runBounded limits budget.ticks (initial a.erased) = .finished execution.value execution.state ∧
      ∀ data, DeepEvaluates a.erased data ↔ data = execution.extraction.result.value :=
  execution_source_semantics (accepted_typed l a).2.2 execution

end Obend.Spec.Proofs.FrontEndAdequacy

end
