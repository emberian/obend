module
/-
# `Obend.Teeth.Extracted.CoreTeeth` — Core, Equiv, FFI, Ledger, Logic, Reasons, Kind, Law & Spec Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (21 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Analysis.Format
import all Obend.Analysis.Hybrid
import all Obend.Analysis.SosLyapunov
import all Obend.Consensus.SimplexTrace
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Check
import all Obend.Core.Checkpoint
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Packet
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraphHead
import all Obend.Digest.Cshake256
import all Obend.Digest.HashBytes
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Doc.WorkbookEngine
import all Obend.Elab.AutoCert
import all Obend.Elab.Gate
import all Obend.Elab.Work
import all Obend.Elab.Workbook
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Clairvoyant
import all Obend.Equiv.Simulation
import all Obend.FFI.Bridge
import all Obend.FFI.BridgeTypes
import all Obend.Fold
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Judge
import all Obend.Intention
import all Obend.Judge
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Certified
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Genealogy
import all Obend.Judge.Identity
import all Obend.Judge.Instances
import all Obend.Judge.Lrat
import all Obend.Judge.Netting
import all Obend.Judge.RealAnalysis
import all Obend.Judge.TranscriptPolicy
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
import all Obend.Leaf.UpTo
import all Obend.Ledger.Book
import all Obend.Ledger.Commit
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Lower.Judge
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Transport
import all Obend.Reasons
import all Obend.Reasons.UnifiedEquilibrium
import all Obend.Receipt.Merkle
import all Obend.Run.Core4
import all Obend.Run.Fork
import all Obend.Run.HyperLaw
import all Obend.Run.Proofs.Shared
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.Annotated
import all Obend.Spec.C4
import all Obend.Spec.Capture
import all Obend.Spec.CrossPackage
import all Obend.Spec.DataWire
import all Obend.Spec.Ecosystem
import all Obend.Spec.Elaborate
import all Obend.Spec.FrontEnd
import all Obend.Spec.Identity
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.PackageLaw
import all Obend.Spec.Parse
import all Obend.Spec.Preview
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.Ecosystem
import all Obend.Spec.Proofs.PackageLaw
import all Obend.Spec.Sha256
import all Obend.Spec.Syntax
import all Obend.Spec.Types
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Vault.ChunkedWorld
import all Obend.Vault.Form
import all Obend.Vault.FormCheckCache
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Json
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.Merge
import all Obend.Vault.Replay
import all Obend.Vault.Retention
import all Obend.Vault.Store
import all Obend.Vault.Transport

public section
end

namespace Obend.Teeth.Extracted.CoreTeeth
/-! ## Extracted from `Obend.Core.Code` (1 teeth) -/
section Obend_Core_Code
open Obend.Core.Code
open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag Shape encode decode decode_encode)
open Obend.Core.Data (Data)
open Obend.Digest.HashBytes (Hash Collision ofBE be ofBE_lt)
open Obend.Core.Digest (digestWith deployed Admissible admissible_of_lt binds_or_collides lengthHash)
open Obend.Core.Ty (Ty Quantity Reuse LambdaAnnotation Context Binding)
open Obend.Core.Check (Assumptions AnnotatedTerm Checked PartialTyping HoleDecl)
open Obend.Core.Bidirectional (CheckRefusal checkAgainst checkAgainst_sound)
open Obend.Elab.Work (checkWork)
open Obend.Core.Proofs.BidirectionalCompleteness (AnnotationTree treeAnnotations)

#tooth quote_roundtrip by mutation tagData := lossyTagData

end Obend_Core_Code

/-! ## Extracted from `Obend.Equiv.Clairvoyant` (1 teeth) -/
section Obend_Equiv_Clairvoyant
open Obend.Equiv
open Obend.Core.Term

private def deadLetBindBroken (deadExpr _body : Term) : Term := deadExpr

#tooth Obend.Equiv.clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper by mutation
  Obend.Equiv.deadLetBind := deadLetBindBroken

end Obend_Equiv_Clairvoyant

/-! ## Extracted from `Obend.FFI.Bridge` (1 teeth) -/
section Obend_FFI_Bridge
open Obend.FFI
open Lean (Json toJson)
open Obend.Core
open Obend.Core.Data (Data)
open Obend.Vault
open Obend.Doc
open Obend.Receipt.Merkle
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

#tooth turnCommitCore_unproposed_tid_refused by mutation
  turnCommitCore := fun s _ => (s, 0)

end Obend_FFI_Bridge

/-! ## Extracted from `Obend.Ledger.Register` (1 teeth) -/
section Obend_Ledger_Register
open Obend.Ledger

-- Tooth: a register that never finds a document's live posting does not keep "posted once".
#tooth step_once by mutation Reg.liveOf := fun _ _ => none

end Obend_Ledger_Register

/-! ## Extracted from `Obend.Logic.Obligation` (3 teeth) -/
section Obend_Logic_Obligation
open Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Lean (Json toJson)

/-- Mutated `ClaimObj.withLhs` that replaces the whole claim with `lhs'` without equation binders. -/
private def withLhsBroken (o : ClaimObj) (lhs' : Term) : ClaimObj :=
  { o with claim := lhs' }

/-- Mutated `verifyByBisimRefinement` that unconditionally accepts without running `claimCheck`. -/
private def verifyByBisimRefinementBroken (_k : Nat) (_baseObj : ClaimObj) (_baseSteps : List RStep) (_lhs' : Term) :
    Judge.Verdict ClaimClause :=
  .ok

#tooth Obend.Logic.claimMeaning_of_bEquiv by mutation
  Obend.Logic.ClaimObj.withLhs := withLhsBroken

#tooth Obend.Logic.verifyByBisimRefinement_sound by mutation
  Obend.Logic.verifyByBisimRefinement := verifyByBisimRefinementBroken

#tooth Obend.Logic.obligationCheck_refuses_false_external_claim by mutation
  Obend.Logic.externalClaimBound := fun _ _ _ => true

end Obend_Logic_Obligation

/-! ## Extracted from `Obend.Reasons.UnifiedEquilibrium` (2 teeth) -/
section Obend_Reasons_UnifiedEquilibrium
open Obend.Reasons.UnifiedEquilibrium
open Obend

-- Mutation witnesses: breaking `checkGLStable` or `checkSameSet` is immediately caught by the kernel.
#tooth oddLoop_refused_by_judge by mutation checkGLStable := fun _ _ => true

#tooth checkGLStable_sound by mutation checkSameSet := fun _ _ => true

end Obend_Reasons_UnifiedEquilibrium

/-! ## Extracted from `Obend.Kind.Proofs` (4 teeth) -/
section Obend_Kind_Proofs
open Obend.Kind
open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Law (Admits)

#tooth dispatch_sound by mutation dispatch := fun _ _ _ _ => .ok none

#tooth effectiveOf_ok by mutation effectiveOf := fun _ _ => .ok lawAdmit

#tooth create_carries by mutation create := fun _ k n l => .ok ⟨n, ⟨k, 0, []⟩, l, .natural 0⟩

-- A pin of the kind's own version alone (the pre-2026-11-01 pin) stays current when an ancestor moves.
#tooth stale_tooth by mutation KindPin.lineage := fun p => [⟨p.name, p.version⟩]

end Obend_Kind_Proofs

/-! ## Extracted from `Obend.Law.Proofs.Inherit` (2 teeth) -/
section Obend_Law_Proofs_Inherit
open Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)

#tooth precedence_local by mutation Obend.Spec.C4.cleanAll := fun _ ls => some (ls.map fun _ => [])

#tooth precedence_monotone by mutation Obend.Spec.C4.cleanAll := fun _ ls => some (ls.map fun _ => [])

end Obend_Law_Proofs_Inherit

/-! ## Extracted from `Obend.Spec.CrossPackage` (2 teeth) -/
section Obend_Spec_CrossPackage
open Obend.Spec.CrossPackage Obend.Spec.CrossPackage.CrossPackageLink
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Slot
open Obend.Slot.World

/-- Mutated `rebindEquivPin` that leaves the stale pin untouched instead of re-pinning to `linkComposition C L`. -/
private def rebindEquivPinBroken {C : Composition} {L : Layer} {m : String}
    (_cert : EquivOverrideCert C L m) (p : LeafPin) : LeafPin :=
  p

/-- Mutated `compContext` that drops `F` and returns `C` unchanged. -/
private def compContextBroken (C _F : Term) : Term :=
  C

#tooth Obend.Spec.CrossPackage.crossPackage_bEquiv_override_preserves_semantics by mutation
  Obend.Spec.CrossPackage.compContext := compContextBroken

#tooth Obend.Spec.CrossPackage.crossPackage_bEquiv_rebinds_slot_usable by mutation
  Obend.Spec.CrossPackage.rebindEquivPin := rebindEquivPinBroken

end Obend_Spec_CrossPackage

/-! ## Extracted from `Obend.Spec.Proofs.Ecosystem` (3 teeth) -/
section Obend_Spec_Proofs_Ecosystem
open Obend.Spec.Ecosystem
open Obend.Slot

#tooth turn_pins_every_root by mutation covered := fun _ _ _ _ => none

#tooth admit_refuses_moved by mutation admit := fun _ _ => .diverged

#tooth stale_iff_blocked by mutation holds := fun _ _ => true

end Obend_Spec_Proofs_Ecosystem

/-! ## Extracted from `Obend.Spec.Proofs.PackageLaw` (1 teeth) -/
section Obend_Spec_Proofs_PackageLaw
open Obend.Spec.PackageLaw
open Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data)

#tooth package_law_eval by mutation packageClauses := fun _ _ => []

end Obend_Spec_Proofs_PackageLaw
end Obend.Teeth.Extracted.CoreTeeth
