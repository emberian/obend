module
/-
# `Obend.Teeth.Extracted.DocVaultSlotTeeth` — Slot, Doc & Vault Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (51 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Core.Bidirectional
import all Obend.Core.Check
import all Obend.Core.Data
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraphHead
import all Obend.Digest.HashBytes
import all Obend.Doc.Backlinks
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Elab.Work
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Genealogy
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Run
import all Obend.Law.Syntax
import all Obend.Logic.Receipt
import all Obend.Reasons
import all Obend.Run.Core4
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Protocol
import all Obend.Slot.World
import all Obend.Spec.Law
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Vault.Affordance
import all Obend.Vault.Branch
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
import all Obend.Vault.Store
import all Obend.Vault.SwarmLedgerSeams

public section
end

namespace Obend.Teeth.Extracted.DocVaultSlotTeeth
/-! ## Extracted from `Obend.Slot` (3 teeth) -/
section Obend_Slot
open Obend.Slot
open Obend.Slot.Protocol

#tooth read_usable_supports by mutation Slot.read := fun _ _ _ => .empty

#tooth permanent_blocked_forever by mutation Slot.read := fun _ _ _ => .empty

#tooth read_of_usable by mutation Slot.read := fun _ _ _ => .empty

end Obend_Slot

/-! ## Extracted from `Obend.Slot.Core4` (2 teeth) -/
section Obend_Slot_Core4
open Obend.Slot.Core4
open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty Context Binding)
open Obend.Core.Check (AnnotatedTerm Annotations Checked)
open Obend.Core.Ty (LambdaAnnotation)
open Obend.Core.Invariant (Scoped)
open Obend.Core.Proofs.Substitution (fillingAt annotationsAt fillTerm msubst fillTerm_zero)

#tooth extend_filling_admitted by mutation judge := fun _ _ _ _ => false

#tooth extend_filling_budget_refused by mutation judge := fun _ Ψ t A =>
  (Obend.Core.Bidirectional.checkAgainst t Ψ A).toBool

end Obend_Slot_Core4

/-! ## Extracted from `Obend.Slot.Integrity` (7 teeth) -/
section Obend_Slot_Integrity
open Obend.Slot
open World

#tooth slotFiller_integrity by mutation Slot.advance := fun _ _ _ _ => .error []

#tooth select_reuse by mutation Slot.alternatives := fun _ _ _ => []

#tooth toy_repair by mutation toyOrder := []

#tooth toy_advance by mutation toyOrder := []

#tooth not_integrity_credulousHoles by mutation Integrity.contextual := fun {_ _ _} [_] _ => True

#tooth not_transition_churn by mutation churn := slotAdvance

#tooth not_transition_sticky by mutation sticky := slotAdvance

end Obend_Slot_Integrity

/-! ## Extracted from `Obend.Slot.World` (2 teeth) -/
section Obend_Slot_World
open Obend.Slot Obend.Slot.World Obend.Slot.World.Returning

#tooth stale_behind_forever by mutation World.Collides := fun {_ _} [_] _ _ _ => False

#tooth stale_dead_forever by mutation World.PinnedAt := fun {_ _} [_] _ _ => True

end Obend_Slot_World

/-! ## Extracted from `Obend.Doc.Backlinks` (5 teeth) -/
section Obend_Doc_Backlinks
open Obend.Doc Obend.Doc.Teeth
open Obend.Slot Obend.Digest.HashBytes
open Obend.Doc.Teeth (toy)

#tooth mem_backlinks by mutation Graph.citesOf := fun _ _ _ => []

#tooth post_correct by mutation Index.post := fun I _ _ => I

#tooth usable_unmoved by mutation citeFacts := fun _ => [.present 2]

#tooth impactedBacklinksFuel_mono by mutation impactedBacklinksFuel := fun fuel _ k =>
  if fuel == 0 then [k] else []

#tooth impactedBacklinksFuel_fixedPoint_sound by mutation impactStep := fun _ _ => []

end Obend_Doc_Backlinks

/-! ## Extracted from `Obend.Doc.Merge` (4 teeth) -/
section Obend_Doc_Merge
open Obend.Doc Obend.Doc.Graph Obend.Doc.Teeth

#tooth Graph.merge_isPushout by mutation Graph.merge := fun A _ => A

#tooth Teeth.files_no_pushout by mutation Graph.File := fun _ => True

#tooth mergeCell3_commutative by mutation mergeCell3 := fun _ vL _ => .merged vL

#tooth mergeCell3_disjoint_edits_succeed by mutation mergeCell3 := fun base _ _ => .merged base

end Obend_Doc_Merge

/-! ## Extracted from `Obend.Doc.Patch` (4 teeth) -/
section Obend_Doc_Patch
open Obend.Doc Obend.Doc.Op Obend.Doc.Graph Obend.Doc.Patch Obend.Doc.Teeth

-- Forgetting the deletions makes the theorem claim a delete leaves the atom alive.
#tooth isDead_apply_forward by mutation deletes := fun _ => []

#tooth apply_compose by mutation Patch.compose := fun p _ => p

#tooth apply_invert by mutation Patch.invert := fun p => p

#tooth apply_frame by mutation Op.touches := fun _ => []

end Obend_Doc_Patch

/-! ## Extracted from `Obend.Doc.Render` (1 teeth) -/
section Obend_Doc_Render
open Obend.Doc Obend.Doc.Teeth
open Obend.Digest.HashBytes
open Obend.Doc.Teeth (toy)

#tooth renderAt_fresh by mutation viewAtom := fun _ _ _ _ => ""

end Obend_Doc_Render

/-! ## Extracted from `Obend.Doc.Section` (6 teeth) -/
section Obend_Doc_Section
open Obend.Doc Obend.Doc.Graph Obend.Doc.Teeth
open Obend.Slot Obend.Digest.HashBytes

#tooth pinned_cite_stays by mutation citeFacts := fun c => [.current c]

#tooth following_cite_behind by mutation citeFacts := fun c => [.verifies c]

#tooth section_alternatives by mutation posted := fun _ _ _ => []

#tooth identity_cite_stays by mutation citeFacts := fun c => [.current c]

#tooth following_cite_stays by mutation quoted := fun _ _ => none

#tooth recite_holds by mutation recite := fun _ _ c => c

end Obend_Doc_Section

/-! ## Extracted from `Obend.Vault.Branch` (2 teeth) -/
section Obend_Vault_Branch
open Obend.Vault.Branch Obend.Vault.Branch.Authority
open Obend.Vault
open Obend.Vault.Rehydration (Sturdyref)
open Obend.Vault.Affordance (Auth fireGate)
open Obend.Spec.Law (LawExpr Facts)
open Obend.Core.Data (Data)
open Obend.Doc (Graph AtomId)
open Obend.Spec.Law (fieldOf fieldLabel firstScalarField firstField LawRef)

#tooth settled_at_tip by mutation authRefusal := fun _ _ _ => none

#tooth tip_lands_iff_store_lands by mutation judgeWrite := fun c _ => .ok c.vault

end Obend_Vault_Branch

/-! ## Extracted from `Obend.Vault.Hyperedge` (3 teeth) -/
section Obend_Vault_Hyperedge
open Obend.Vault
open Obend.Law
open Obend.Core.Data
open Obend.Core.Term

#tooth unreported_state_inflation_refused by mutation
  checkDeltaMatchesStateBalances := fun _ _ => true

#tooth stateBoundTurn_conserves_actual_state_balances by mutation
  checkTurnStateBalancesBound := fun _ _ => true

#tooth deriveHalfEdgesFromState_matches by mutation
  deriveHalfEdgesFromState := fun _ _ => []

end Obend_Vault_Hyperedge

/-! ## Extracted from `Obend.Vault.Log` (1 teeth) -/
section Obend_Vault_Log
open Obend.Vault.Log
open Obend.Vault.Rehydration (WitnessReceipt wellLinked genesisSentinel)

-- Reading without the link check recovers records that do not follow one another.
#tooth parseFrom_sound by mutation parseOne := fun Hb prev bs =>
  match takeN 136 bs with
  | none => .error .torn
  | some (h, rest) =>
    if h.take 4 ≠ magic then .error .magic else
    let len := unbe ((h.drop 4).take 4)
    match takeN (len + 32) rest with
    | none => .error .torn
    | some (body, rest') =>
      let rc := fieldsOf ((h.drop 4).drop 4)
      let payload := body.take len
      if rc.effectsHash ≠ dig Hb payload then .error .digest
      else if unbe (body.drop len) ≠ Hr Hb rc then .error .seal
      else let _ := prev; .ok (⟨rc, payload⟩, rest')

end Obend_Vault_Log

/-! ## Extracted from `Obend.Vault.Store` (7 teeth) -/
section Obend_Vault_Store
open Obend.Vault
open Obend.Doc Obend.Doc.Graph Obend.Digest.HashBytes
open Obend.Spec.Law (LawExpr Facts)

-- Comparing the law lines alone lets a write retarget its kind and be judged by the old kind's laws.
#tooth lawsFor_of_kept by mutation lawsKept := fun old new => lawLines old == lawLines new

#tooth open_idem by mutation writesFor := fun _ _ => []

#tooth open_idem by mutation quiet := fun _ _ => false

#tooth select_section_zero_refused by mutation Obend.Vault.sectionAt := fun G k => (sections G)[k - 1]?

#tooth mergePage_pushout by mutation mergePage := fun A _ => some A

#tooth select_needs_grant by mutation Actor.may := fun _ _ _ => true

#tooth post_needs_grant by mutation Actor.may := fun _ _ _ => true

end Obend_Vault_Store

/-! ## Extracted from `Obend.Vault.SwarmLedgerSeams` (4 teeth) -/
section Obend_Vault_SwarmLedgerSeams
open Obend.Vault.SwarmLedgerSeams
open Obend.Core.Term (Term Value Step Steps Evaluates)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Spec.Law (LawRef LawExpr Facts scalarOf firstScalarField fieldOf firstField fieldLabel)
open Obend.Judge

-- Mutation witness: collapsing typed link roles back to untyped `links.map (·.target)` breaks isolation.
#tooth write_in_disjoint_role_preserves_role_law by mutation
  targetsInRole := fun _ links => links.map (·.target)

-- Mutation witness: ignoring telemetry observations in `ingestTelemetryObservation` is caught immediately.
#tooth telemetry_defeats_lane_dispatch_without_refusing_fact by mutation
  ingestTelemetryObservation := fun s _ => .ok s

-- Mutation witness: waving through succession in `checkDoctrineSuccession` allows floor loosening and is caught.
#tooth vaultDoctrine_refuses_loosening by mutation
  checkDoctrineSuccession := fun _ _ _ => true

-- Mutation witness: dropping the `allLawsHold` soundness guard in `synthesizePassingDelta` is caught.
#tooth synthesizePassingDelta_sound by mutation
  allLawsHold := fun _ _ _ _ _ => true

end Obend_Vault_SwarmLedgerSeams
end Obend.Teeth.Extracted.DocVaultSlotTeeth
