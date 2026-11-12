module
/-
# SlotReceiptIntentionRevivalTest — Cross-Organ Synthesis & `#tooth` Mutation Suite (`W7-Revival3`)

Exercises and mutation-tests the upgraded 7-organ stack:
1. **`Obend.Intention` & `Obend.Kind` & `Obend.Slot.Budget`**:
   - Compositional `Intention.product`, `Intention.resolveBatch_sound`, `Intention.resolveBatch_refuses_exact`,
     and `Intention.dedupSupports`.
   - Author ≠ Integrator `OpenSlotInterface`, `SlotCandidate`, `auditCandidateLocal`, `checkCandidateLocal_sound`,
     `intentionRealizerSupportSheaf`, `negotiateSlots_converges_and_conserves_budget`,
     `negotiateSlots_complete_no_deadlock`, and strict shared-resource subadditivity
     (`sumResourceCosts_dedup_lt_of_shared`).
2. **`Obend.Equiv.Clairvoyant` & `Obend.Equiv.Cost`**:
   - `clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper`, `checkSlotCostContract_sound`,
     and exact Clairvoyant budget boundary vs. overrun refutation.
3. **`Obend.Receipt.Merkle` & `Obend.Fold.Collapse`**:
   - Domain-separated (`0x00`/`0x01`/`0x02` + `spanSize`/`startIdx`) 256-bit `cSHAKE256` salted
     blinded Merkle multiproofs (`verifyBlindedMultiproof256_complete`, `extractMultiproofCollision`,
     `blindedMultiproof_redaction_nonleakage`) and horizon-compressed multiproofs
     (`verifyCollapsedHorizonMultiproof256_complete`, `extractCollapsedHorizonCollision`,
     `collapsedHorizon_redaction_nonleakage`).
   - Adversarial rejections on duplicate leaf indices (`[0, 0]`), unsorted indices (`[2, 1]`),
     out-of-bounds indices (`[0, 4]`), and tampered leaf payloads.
4. **`Obend.Reasons` & `Obend.Reasons.DialecticalBlame`**:
   - Stratified unique Gelfond–Lifschitz equilibrium (`dialecticalAudit_stratified`,
     `dialecticalAudit_unique_equilibrium`), constructive `Type`-valued `PSum` blame extraction
     (`diagnoseDialecticalBlame_inl_sound`, `diagnoseDialecticalBlame_inr_sound`), and cycle-safe
     termination on odd negative self-loops (`p ← not p`) and 2-party mutual-defeat cycles
     (`a ← not b`, `b ← not a`).
5. **21 Universal `#tooth` Mutation Kills & `0 sorryAx` / `0 Classical.choice` Extractor Verification**.
-/

public import Obend.Intention
public import Obend.Kind
public import Obend.Slot.Budget
public import Obend.Equiv.Clairvoyant
public import Obend.Equiv.Cost
public import Obend.Receipt.Merkle
public import Obend.Fold.Collapse
public import Obend.Reasons
public import Obend.Reasons.UnifiedEquilibrium
public import Obend.Reasons.DialecticalBlame
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Intention
import all Obend.Slot.Budget
import all Obend.Equiv.Clairvoyant
import all Obend.Equiv.Cost
import all Obend.Receipt.Merkle
import all Obend.Fold.Collapse
import all Obend.Reasons
import all Obend.Reasons.DialecticalBlame

public section

namespace Obend.Tests.Metasystem.SlotReceiptIntentionRevivalTest

open Obend
open Obend.Core.Term
open Obend.Equiv
open Obend.Slot.Budget
open Obend.Receipt.Merkle
open Obend.Fold.Collapse
open Obend.Reasons
open Obend.Reasons.UnifiedEquilibrium
open Obend.Reasons.DialecticalBlame

set_option autoImplicit false

/-! ## 1. Cross-Organ 5-Pillar End-to-End Synthesis -/

def revivalKinds : Obend.Kind.Kinds :=
  ⟨[{ name := "Codec", version := 1, layout := [], init := .natural 0,
      law := .boolean true, parents := [] },
    { name := "Transport", version := 1, layout := [], init := .natural 0,
      law := .boolean true, parents := [] }]⟩

def revivalIntention : Obend.Intention Unit String String Unit String where
  ref := id
  supports := fun _ => [()]
  holds := fun _ _ => true
  resolve := fun _ r => .ok r
  resolve_ref := fun _ _ _ h => by cases h; rfl
  resolve_holds := fun _ _ _ _ _ _ => rfl

def codecIface : OpenSlotInterface :=
  { slotId := "codec"
    expectedKind := "Codec"
    intentionRef := "codec@^1"
    budget := ⟨2⟩
    fuel := 4
    specTerm := .nat 42
    peerDeps := [("transport", "wire")] }

def transportIface : OpenSlotInterface :=
  { slotId := "transport"
    expectedKind := "Transport"
    intentionRef := "transport@^1"
    budget := ⟨2⟩
    fuel := 4
    specTerm := .nat 99
    peerDeps := [("codec", "wire")] }

/-- Top-ranked candidate incompatible on `"wire"` (`"v2"` vs `"v1"`): pruned by arc-consistency. -/
def codecCandV2 : SlotCandidate String :=
  { candId := "codec-v2"
    slotId := "codec"
    kindPin := ⟨"Codec", 1, []⟩
    intentionPin := "codec@^1"
    implTerm := .nat 42
    gluingTags := [("wire", "v2")]
    sharedResourceIds := ["keccak-lut"] }

/-- Over-budget candidate (`(λ x => x) ((λ y => y) 42)` takes 3 steps > budget 2): rejected locally. -/
def codecCandOverBudget : SlotCandidate String :=
  { candId := "codec-slow"
    slotId := "codec"
    kindPin := ⟨"Codec", 1, []⟩
    intentionPin := "codec@^1"
    implTerm := .app (.lam (.bound 0)) (.app (.lam (.bound 0)) (.nat 42))
    gluingTags := [("wire", "v1")]
    sharedResourceIds := ["keccak-lut"] }

/-- Dead-let bound candidate (`deadLetBind (10+20) 42` skips `10+20` at Clairvoyant cost 2 ≤ budget 2). -/
def codecCandV1 : SlotCandidate String :=
  { candId := "codec-v1"
    slotId := "codec"
    kindPin := ⟨"Codec", 1, []⟩
    intentionPin := "codec@^1"
    implTerm := deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)
    gluingTags := [("wire", "v1")]
    sharedResourceIds := ["keccak-lut"] }

def transportCandV1 : SlotCandidate String :=
  { candId := "transport-v1"
    slotId := "transport"
    kindPin := ⟨"Transport", 1, []⟩
    intentionPin := "transport@^1"
    implTerm := .app (.lam (.nat 99)) (.binary .add (.nat 1) (.nat 2))
    gluingTags := [("wire", "v1")]
    sharedResourceIds := ["keccak-lut"] }

@[expose] def sampleLeaves256 : List SaltedLeaf256 :=
  [ ⟨0x10111213#256, [0xAA, 0x01]⟩
  , ⟨0x20212223#256, [0xBB, 0x02]⟩
  , ⟨0x30313233#256, [0xCC, 0x03]⟩
  , ⟨0x40414243#256, [0xDD, 0x04]⟩ ]

/-- End-to-end 5-organ synthesis:
1. `negotiateSlots` prunes `codecCandOverBudget` locally and `codecCandV2` by arc-consistency,
   selecting `[codecCandV1, transportCandV1]` in 1 round and conserving Clairvoyant budget.
2. Shared `"keccak-lut"` resource cost is strictly subadditive (`glued < unglued`).
3. 256-bit `cSHAKE256` blinded multiproof over `[0, 3]` verifies and redacts middle leaves `[1, 2]`.
4. `diagnoseDialecticalBlame` certifies admissibility (`.inl cert`) with `"admissible:realization"`
   `.supported` in the unique GL stable equilibrium of `buildDialecticalAuditBase`. -/
theorem endToEnd_schelling_slot_receipt_equilibrium_certified :
    let proposals :=
      [ ⟨codecIface, [codecCandOverBudget, codecCandV2, codecCandV1]⟩
      , ⟨transportIface, [transportCandV1]⟩ ]
    let costOf : String → Nat := fun r => if r == "keccak-lut" then 10 else 1
    let proof := buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0, 3]
    let root := saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256
    ∃ realizer cert,
      negotiateSlots revivalKinds revivalIntention () proposals = .ok realizer ∧
      realizer.bindings = [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] ∧
      gluedSharedResourceCost costOf realizer.bindings <
        ungluedResourceCost costOf realizer.bindings ∧
      verifyBlindedMultiproof256 cshakeMultiproofHash proof root = true ∧
      diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        realizer.bindings proof root = .inl cert ∧
      status (buildDialecticalAuditBase revivalKinds revivalIntention () cshakeMultiproofHash
        realizer.bindings proof root) realizationAdmissibleAtom = .supported := by
  dsimp only
  have hVer := verifyBlindedMultiproof256_complete cshakeMultiproofHash sampleLeaves256 [0, 3] (by decide)
  have hAudOver :
      checkCandidateLocal revivalKinds revivalIntention () codecIface codecCandOverBudget = false := by
    simp (config := { decide := true }) [checkCandidateLocal, auditCandidateLocal,
      checkSlotCostContract, sameObservedLiteral, codecIface, codecCandOverBudget]
  have hAudV2 :
      checkCandidateLocal revivalKinds revivalIntention () codecIface codecCandV2 = true := by
    simp (config := { decide := true }) [checkCandidateLocal, auditCandidateLocal,
      checkSlotCostContract, sameObservedLiteral, codecIface]
  have hAudC : auditCandidateLocal revivalKinds revivalIntention () codecIface codecCandV1 = none := by
    simp (config := { decide := true }) [auditCandidateLocal, checkSlotCostContract,
      sameObservedLiteral, codecIface, codecCandV1]
  have hAudT : auditCandidateLocal revivalKinds revivalIntention () transportIface transportCandV1 = none := by
    simp (config := { decide := true }) [auditCandidateLocal, checkSlotCostContract,
      sameObservedLiteral, transportIface, transportCandV1]
  have hCheckC :
      checkCandidateLocal revivalKinds revivalIntention () codecIface codecCandV1 = true := by
    simp [checkCandidateLocal, hAudC]
  have hCheckT :
      checkCandidateLocal revivalKinds revivalIntention () transportIface transportCandV1 = true := by
    simp [checkCandidateLocal, hAudT]
  have hNeg :
      negotiateSlots revivalKinds revivalIntention ()
        [ ⟨codecIface, [codecCandOverBudget, codecCandV2, codecCandV1]⟩
        , ⟨transportIface, [transportCandV1]⟩ ] =
      .ok ⟨[⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩], 1⟩ := by
    simp (config := { decide := true }) [negotiateSlots, buildLocalDomains, domainCard,
      pruneDomainsLoop, pruneOneRound, pruneOneRoundAux, findEmptyDomain,
      searchConsistentWith, searchConsistentWith.tryCands,
      hAudOver, hAudV2, hCheckC, hCheckT]
  have hSlotsOk :
      findFirstFailingSlotAux revivalKinds revivalIntention () 0
        [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] = none := by
    simp [findFirstFailingSlotAux, hAudC, hAudT]
  have hGraphOk : slotGraphWellFormed [codecIface, transportIface] = true := by
    decide
  have hGluePair : gluingCompatible codecIface codecCandV1 transportIface transportCandV1 = true := by
    decide
  have hGlueOk :
      findFirstGluingConflict
        [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] = none := by
    simp [findFirstGluingConflict, findIncompatiblePeer, hGluePair]
  have hNonEmpty :
      verifyNonEmptyBlindedMultiproof256 cshakeMultiproofHash
        (buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0, 3])
        (saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256) = true := by
    unfold verifyNonEmptyBlindedMultiproof256
    rw [buildBlindedMultiproof256_queriedIndices, hVer]
    rfl
  have hInl :
      diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩]
        (buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0, 3])
        (saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256) =
      .inl { supportedAtoms :=
               (buildDialecticalAuditState revivalKinds revivalIntention () cshakeMultiproofHash
                 [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩]
                 (buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0, 3])
                 (saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256)).kept.1
             slotCount := 2
             totalDeclaredBudget := 4 } := by
    unfold diagnoseDialecticalBlame
    have hMapIf :
        ([⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] : List (BoundSlot String)).map (·.iface) =
          [codecIface, transportIface] := rfl
    have hBud : totalDeclaredSlotBudget [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] = 4 := rfl
    rw [hSlotsOk, hMapIf, hGraphOk, hGlueOk, hNonEmpty, hBud]
    rfl
  refine ⟨⟨[⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩], 1⟩, _,
    hNeg, rfl, ?_, hVer, hInl, (diagnoseDialecticalBlame_inl_sound hInl).2.2.2.2.2.1⟩
  exact gluedSharedResourceCost_lt_of_shared_bindings
    (fun r => if r == "keccak-lut" then 10 else 1)
    ⟨codecIface, codecCandV1⟩ ⟨transportIface, transportCandV1⟩ []
    (r₀ := "keccak-lut") (by decide) (by decide) (by decide)

/-! ## 2. Adversarial Edge Cases: Multiproof Forgery, Dependency Closure, Cyclic Defeat Graphs & Cost Boundaries -/

/-- Duplicate, unsorted, empty-query, out-of-bounds, and malformed-span multiproofs are all rejected. -/
theorem multiproof_adversarial_indices_rejected (H : Obend.Digest.HashBytes.Hash) :
    let root := saltedTreeRoot256 H sampleLeaves256
    let pDup := buildBlindedMultiproof256 H sampleLeaves256 [0, 0]
    let pUnsorted := buildBlindedMultiproof256 H sampleLeaves256 [2, 1]
    let pOob := buildBlindedMultiproof256 H sampleLeaves256 [0, 4]
    let pZeroQuery : BlindedMultiproof256 := { treeSize := 4, queriedIndices := [], tree := .blinded root }
    let pMismatchSpan : BlindedMultiproof256 :=
      { treeSize := 4, queriedIndices := [1, 2], tree := .openedLeaf 1 0x20212223#256 [0xFF] }
    verifyBlindedMultiproof256 H pDup root = false ∧
    verifyBlindedMultiproof256 H pUnsorted root = false ∧
    verifyBlindedMultiproof256 H pOob root = false ∧
    verifyNonEmptyBlindedMultiproof256 H pZeroQuery root = false ∧
    verifyBlindedMultiproof256 H pMismatchSpan root = false := by
  dsimp only
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · have hBad : strictlyAscendingInBounds sampleLeaves256.length [0, 0] = false := by decide
    simp [verifyBlindedMultiproof256, hBad]
  · have hBad : strictlyAscendingInBounds sampleLeaves256.length [2, 1] = false := by decide
    simp [verifyBlindedMultiproof256, hBad]
  · have hBad : strictlyAscendingInBounds sampleLeaves256.length [0, 4] = false := by decide
    simp [verifyBlindedMultiproof256, hBad]
  · simp [verifyBlindedMultiproof256, evalBlindedNode256]

/-- **Shape-Preserving Merkle Payload Forgery Forces Constructive Collision Extraction**:
Tampering ONLY leaf `0`'s payload (`[0xFF, 0x99]` vs `[0xAA, 0x01]`) while preserving exact tree
geometry and `queriedIndices = [0, 3]` cannot take `.inl` in `extractMultiproofCollision`: if any
hash `H` accepts the forgery against `saltedTreeRoot256 H sampleLeaves256`, `extractMultiproofCollision`
constructively extracts a `ScopedCollision256 H` witness (`col.msg₁ ≠ col.msg₂` with equal 256-bit digests)! -/
@[expose] def forgedSampleProof256 (H : Obend.Digest.HashBytes.Hash) : BlindedMultiproof256 :=
  { treeSize := 4
    queriedIndices := [0, 3]
    tree :=
      .branch
        (.branch
          (.openedLeaf 0 0x10111213#256 [0xFF, 0x99])
          (.blinded (saltedSubtreeRoot256 H 1 [⟨0x20212223#256, [0xBB, 0x02]⟩])))
        (.branch
          (.blinded (saltedSubtreeRoot256 H 2 [⟨0x30313233#256, [0xCC, 0x03]⟩]))
          (.openedLeaf 3 0x40414243#256 [0xDD, 0x04])) }

theorem shape_preserving_merkle_forgery_forces_collision
    (H : Obend.Digest.HashBytes.Hash)
    (hVer : verifyBlindedMultiproof256 H (forgedSampleProof256 H)
      (saltedTreeRoot256 H sampleLeaves256) = true) :
    ∃ col : ScopedCollision256 H
        (multiproofScopePreimages H sampleLeaves256 (forgedSampleProof256 H)),
      extractMultiproofCollision H sampleLeaves256 (forgedSampleProof256 H) rfl hVer = .inr col ∧
      col.msg₁ ≠ col.msg₂ ∧
      hashBytes256 H col.msg₁ = hashBytes256 H col.msg₂ := by
  cases hExt : extractMultiproofCollision H sampleLeaves256 (forgedSampleProof256 H) rfl hVer with
  | inr col => exact ⟨col, rfl, col.ne, col.eq256⟩
  | inl ok =>
    exfalso
    obtain ⟨opened, hEval, _, hAgree⟩ := ok
    have hSyn := evalBlindedNode256_syntacticOpened _ _ _ _ _ hEval
    have hMem0 : (0, (⟨0x10111213#256, [0xFF, 0x99]⟩ : SaltedLeaf256)) ∈ opened := by
      rw [← hSyn]
      simp [forgedSampleProof256, BlindedNode256.syntacticOpenedLeaves]
    have hBad := hAgree 0 ⟨0x10111213#256, [0xFF, 0x99]⟩ hMem0
    simp [sampleLeaves256] at hBad

/-- Concrete inhabitedness witness for `shape_preserving_merkle_forgery_forces_collision` under a
constant 32-byte colliding hash: `extractMultiproofCollision` constructively computes `.inr col`! -/
theorem shape_preserving_merkle_forgery_inhabited :
    let constHash32 : Obend.Digest.HashBytes.Hash := fun _ => List.replicate 32 0
    ∃ hVer : verifyBlindedMultiproof256 constHash32 (forgedSampleProof256 constHash32)
        (saltedTreeRoot256 constHash32 sampleLeaves256) = true,
      ∃ col,
        extractMultiproofCollision constHash32 sampleLeaves256
          (forgedSampleProof256 constHash32) rfl hVer = .inr col ∧
        col.msg₁ ≠ col.msg₂ := by
  dsimp only
  let cH : Obend.Digest.HashBytes.Hash := fun _ => List.replicate 32 0
  have hHash : ∀ m, hashBytes256 cH m = 0#256 := fun _ => by
    unfold hashBytes256; dsimp only [cH]; decide
  have h0 : sampleLeaves256.length ≠ 0 := by decide
  have h1 : sampleLeaves256.length ≠ 1 := by decide
  have hRoot : saltedTreeRoot256 cH sampleLeaves256 = 0#256 := by
    rw [saltedTreeRoot256, saltedSubtreeRoot256]
    simp only [h0, h1, ↓reduceIte]
    exact hHash _
  have hEv : evalBlindedNode256 cH (forgedSampleProof256 cH).tree 4 0 =
      some (0#256, [(0, ⟨0x10111213#256, [0xFF, 0x99]⟩), (3, ⟨0x40414243#256, [0xDD, 0x04]⟩)]) := by
    unfold forgedSampleProof256
    dsimp only [evalBlindedNode256]
    simp only [hHash]
    rfl
  have hSz : (forgedSampleProof256 cH).treeSize = 4 := rfl
  have hQi : (forgedSampleProof256 cH).queriedIndices = [0, 3] := rfl
  have hAsc : strictlyAscendingInBounds 4 [0, 3] = true := by decide
  have hVer : verifyBlindedMultiproof256 cH (forgedSampleProof256 cH)
      (saltedTreeRoot256 cH sampleLeaves256) = true := by
    unfold verifyBlindedMultiproof256
    rw [hSz, hQi, hAsc, hEv, hRoot]
    decide
  obtain ⟨col, hEq, hNe, _⟩ := shape_preserving_merkle_forgery_forces_collision cH hVer
  exact ⟨hVer, col, hEq, hNe⟩

/-- **Dependency Closure & Self-Edge Validation Regression**:
1. Dangling peer `("missing", "wire")` is refused with `.malformedSlotGraph` in `negotiateSlots`
   and `.slotGraphMalformed` in `diagnoseDialecticalBlame`.
2. Self-dependency `("codec", "wire")` without local `"wire"` tag is refused locally with
   `some (.missingSelfGluingTag "codec")`.
3. Self-dependency `("codec", "wire")` WITH local `"wire" = "v1"` tag passes `negotiateSlots` and
   satisfies `realizerGraphValid_dependency_closure`. -/
theorem slot_dependency_closure_and_self_edge_regression :
    let danglingIface : OpenSlotInterface := { codecIface with peerDeps := [("missing", "wire")] }
    let selfIface : OpenSlotInterface := { codecIface with peerDeps := [("codec", "wire")] }
    let noTagCand : SlotCandidate String := { codecCandV1 with gluingTags := [] }
    let proof := buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0]
    let root := saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256
    negotiateSlots revivalKinds revivalIntention () [⟨danglingIface, [codecCandV1]⟩] =
      .error (.malformedSlotGraph ["codec"]) ∧
    (match diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        [⟨danglingIface, codecCandV1⟩] proof root with
     | .inr (.slotGraphMalformed ["codec"] _ _) => true
     | _ => false) = true ∧
    auditCandidateLocal revivalKinds revivalIntention () selfIface noTagCand =
      some (.missingSelfGluingTag "codec") ∧
    realizerGraphValid [⟨selfIface, codecCandV1⟩] = true := by
  dsimp only
  let dIf : OpenSlotInterface := { codecIface with peerDeps := [("missing", "wire")] }
  have hId : dIf.slotId = "codec" := rfl
  have hBad : slotGraphWellFormed [dIf] = false := by decide
  refine ⟨?_, ?_, ?_, by decide⟩
  · change negotiateSlots revivalKinds revivalIntention () [⟨dIf, [codecCandV1]⟩] = _
    simp [negotiateSlots, hBad, hId]
  · change (match diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        [⟨dIf, codecCandV1⟩] _ _ with
      | .inr (.slotGraphMalformed ["codec"] _ _) => true
      | _ => false) = true
    have hAud : auditCandidateLocal revivalKinds revivalIntention () dIf codecCandV1 = none := by
      simp (config := { decide := true }) [dIf, auditCandidateLocal, checkSlotCostContract,
        sameObservedLiteral, codecIface, codecCandV1]
    unfold diagnoseDialecticalBlame
    simp [findFirstFailingSlotAux, hAud, hBad, hId]
  · decide

/-- Cyclic `Reasons` defeat graphs (odd self-defeat `p ← not p`, 2-party mutual defeat
`a ← not b`, `b ← not a`, AND ungrounded positive 3-cycle `a ← b`, `b ← c`, `c ← a`) terminate
cleanly with blame, while adding a grounded fallback explanation (`a ← fact_ok`) restores
`.supported` / `.inl cert` **independently of rule order**! -/
theorem cyclic_reasons_defeat_graphs_terminate_with_blame :
    let bOdd : Base := { explanations := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] }
    let bEven : Base :=
      { explanations :=
          [ { name := "ab", concl := "a", pos := [], neg := ["b"] }
          , { name := "ba", concl := "b", pos := [], neg := ["a"] } ] }
    let rAB : Rule := { name := "r_ab", concl := "a", pos := ["b"], neg := [] }
    let rBC : Rule := { name := "r_bc", concl := "b", pos := ["c"], neg := [] }
    let rCA : Rule := { name := "r_ca", concl := "c", pos := ["a"], neg := [] }
    let rGood : Rule := { name := "r_good", concl := "a", pos := ["fact_ok"], neg := [] }
    let obsOk : Reasons.Observation := { name := "fact_ok", text := "grounded", source := "test" }
    let bPos3Cycle : Base := { explanations := [rAB, rBC, rCA] }
    let bFallback1 : Base := { observations := [obsOk], explanations := [rAB, rBC, rCA, rGood] }
    let bFallback2 : Base := { observations := [obsOk], explanations := [rGood, rAB, rBC, rCA] }
    let proof := buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0]
    let root := saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256
    let bs := [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩]
    diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
      bs proof root bOdd (some "p") =
      .inr (.policyJustificationDefeated "p" .undefined (.cyclicDependency "p" ["p"])) ∧
    diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
      bs proof root bEven (some "a") =
      .inr (.policyJustificationDefeated "a" .undefined
        (.contestedByUndefined "ab" "b" (.cyclicDependency "a" ["b", "a"]))) ∧
    status bPos3Cycle "a" = .unsupported ∧
    traceUnsupportedRoot { base := bPos3Cycle, kept := judge bPos3Cycle } "a" =
      .missingPremise "r_ab" "b"
        (.missingPremise "r_bc" "c"
          (.cyclicDependency "a" ["c", "b", "a"])) ∧
    status bFallback1 "a" = .supported ∧
    status bFallback2 "a" = .supported ∧
    (match diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        bs proof root bFallback1 (some "a") with
     | .inl _ => true | .inr _ => false) = true ∧
    (match diagnoseDialecticalBlame revivalKinds revivalIntention () cshakeMultiproofHash
        bs proof root bFallback2 (some "a") with
     | .inl _ => true | .inr _ => false) = true := by
  dsimp only
  have hVer := verifyBlindedMultiproof256_complete cshakeMultiproofHash sampleLeaves256 [0] (by decide)
  have hAudC : auditCandidateLocal revivalKinds revivalIntention () codecIface codecCandV1 = none := by
    simp (config := { decide := true }) [auditCandidateLocal, checkSlotCostContract,
      sameObservedLiteral, codecIface, codecCandV1]
  have hAudT : auditCandidateLocal revivalKinds revivalIntention () transportIface transportCandV1 = none := by
    simp (config := { decide := true }) [auditCandidateLocal, checkSlotCostContract,
      sameObservedLiteral, transportIface, transportCandV1]
  have hSlotsOk :
      findFirstFailingSlotAux revivalKinds revivalIntention () 0
        [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] = none := by
    simp [findFirstFailingSlotAux, hAudC, hAudT]
  have hGraphOk : slotGraphWellFormed [codecIface, transportIface] = true := by
    decide
  have hGluePair : gluingCompatible codecIface codecCandV1 transportIface transportCandV1 = true := by
    decide
  have hGlueOk :
      findFirstGluingConflict
        [⟨codecIface, codecCandV1⟩, ⟨transportIface, transportCandV1⟩] = none := by
    simp [findFirstGluingConflict, findIncompatiblePeer, hGluePair]
  have hNonEmpty :
      verifyNonEmptyBlindedMultiproof256 cshakeMultiproofHash
        (buildBlindedMultiproof256 cshakeMultiproofHash sampleLeaves256 [0])
        (saltedTreeRoot256 cshakeMultiproofHash sampleLeaves256) = true := by
    unfold verifyNonEmptyBlindedMultiproof256
    rw [buildBlindedMultiproof256_queriedIndices, hVer]
    rfl
  have hOdd :
      ({ base := { explanations := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] }
         kept := judge { explanations := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] } } : State).status "p" =
        .undefined := by decide
  have hOddTrace :
      traceUnsupportedRoot
        { base := { explanations := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] }
          kept := judge { explanations := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] } } "p" =
        .cyclicDependency "p" ["p"] := by decide
  have hEven :
      ({ base := { explanations := [{ name := "ab", concl := "a", pos := [], neg := ["b"] },
                                    { name := "ba", concl := "b", pos := [], neg := ["a"] }] }
         kept := judge { explanations := [{ name := "ab", concl := "a", pos := [], neg := ["b"] },
                                          { name := "ba", concl := "b", pos := [], neg := ["a"] }] } } : State).status "a" =
        .undefined := by decide
  have hEvenTrace :
      traceUnsupportedRoot
        { base := { explanations := [{ name := "ab", concl := "a", pos := [], neg := ["b"] },
                                     { name := "ba", concl := "b", pos := [], neg := ["a"] }] }
          kept := judge { explanations := [{ name := "ab", concl := "a", pos := [], neg := ["b"] },
                                           { name := "ba", concl := "b", pos := [], neg := ["a"] }] } } "a" =
        .contestedByUndefined "ab" "b" (.cyclicDependency "a" ["b", "a"]) := by decide
  have hFb1 :
      ({ base := { observations := [{ name := "fact_ok", text := "grounded", source := "test" }]
                   explanations := [{ name := "r_ab", concl := "a", pos := ["b"], neg := [] },
                                    { name := "r_bc", concl := "b", pos := ["c"], neg := [] },
                                    { name := "r_ca", concl := "c", pos := ["a"], neg := [] },
                                    { name := "r_good", concl := "a", pos := ["fact_ok"], neg := [] }] }
         kept := judge { observations := [{ name := "fact_ok", text := "grounded", source := "test" }]
                         explanations := [{ name := "r_ab", concl := "a", pos := ["b"], neg := [] },
                                          { name := "r_bc", concl := "b", pos := ["c"], neg := [] },
                                          { name := "r_ca", concl := "c", pos := ["a"], neg := [] },
                                          { name := "r_good", concl := "a", pos := ["fact_ok"], neg := [] }] } } : State).status "a" =
        .supported := by decide
  have hFb2 :
      ({ base := { observations := [{ name := "fact_ok", text := "grounded", source := "test" }]
                   explanations := [{ name := "r_good", concl := "a", pos := ["fact_ok"], neg := [] },
                                    { name := "r_ab", concl := "a", pos := ["b"], neg := [] },
                                    { name := "r_bc", concl := "b", pos := ["c"], neg := [] },
                                    { name := "r_ca", concl := "c", pos := ["a"], neg := [] }] }
         kept := judge { observations := [{ name := "fact_ok", text := "grounded", source := "test" }]
                         explanations := [{ name := "r_good", concl := "a", pos := ["fact_ok"], neg := [] },
                                          { name := "r_ab", concl := "a", pos := ["b"], neg := [] },
                                          { name := "r_bc", concl := "b", pos := ["c"], neg := [] },
                                          { name := "r_ca", concl := "c", pos := ["a"], neg := [] }] } } : State).status "a" =
        .supported := by decide
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · unfold diagnoseDialecticalBlame
    simp [hSlotsOk, hGraphOk, hGlueOk, hNonEmpty, hOdd, hOddTrace]
  · unfold diagnoseDialecticalBlame
    simp [hSlotsOk, hGraphOk, hGlueOk, hNonEmpty, hEven, hEvenTrace]
  · unfold diagnoseDialecticalBlame
    simp [hSlotsOk, hGraphOk, hGlueOk, hNonEmpty, hFb1]
  · unfold diagnoseDialecticalBlame
    simp [hSlotsOk, hGraphOk, hGlueOk, hNonEmpty, hFb2]

/-- Clairvoyant cost boundary sharpness: `(λ x => 99) (1 + 2)` costs exactly `2` via `Skip` + `β`
(passing budget `2`), whereas reducing the budget by 1 (`budget := 1`) immediately fails
`checkSlotCostContract` and triggers `.costOrObservationContractFailed 1` in `diagnoseDialecticalBlame`. -/
theorem clairvoyant_cost_boundary_sharp :
    let tightIface := { transportIface with budget := ⟨2⟩ }
    let tooTightIface := { transportIface with budget := ⟨1⟩ }
    checkCandidateLocal revivalKinds revivalIntention () tightIface transportCandV1 = true ∧
    auditCandidateLocal revivalKinds revivalIntention () tooTightIface transportCandV1 =
      some (.costOrObservationContractFailed 1) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simp (config := { decide := true }) [checkCandidateLocal, auditCandidateLocal,
      checkSlotCostContract, sameObservedLiteral, transportIface, transportCandV1]
  · simp (config := { decide := true }) [auditCandidateLocal, checkSlotCostContract,
      sameObservedLiteral, transportIface, transportCandV1]

/-! ## 3. 21 Universal `#tooth` Mutation Kills Across All Upgraded Organs -/

-- 1–3: Equiv.Cost & Equiv.Clairvoyant
#tooth Obend.Equiv.checkSlotCostContract_sound by
  mutation Obend.Equiv.checkSlotCostContract := fun _ _ _ _ => true

#tooth Obend.Equiv.checkSlotCostContract_sound by
  mutation Obend.Equiv.sameObservedLiteral := fun _ _ => true

#tooth Obend.Equiv.clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper by
  mutation Obend.Equiv.deadLetBind := fun _ body => body

-- 4–5: Intention
#tooth Obend.Intention.resolveBatch_sound by
  mutation Obend.Intention.resolveBatch := fun _ _ _ => .ok []

#tooth Obend.Intention.mem_dedupSupports_iff by
  mutation Obend.Intention.dedupSupports := fun _ => []

-- 6–11: Slot.Budget & Kind & Dependency Closure
#tooth Obend.Slot.Budget.checkCandidateLocal_sound by
  mutation Obend.Slot.Budget.checkCandidateLocal := fun _ _ _ _ _ => true

#tooth Obend.Slot.Budget.checkCandidateLocal_sound by
  mutation Obend.Slot.Budget.auditCandidateLocal := fun _ _ _ _ _ => none

#tooth Obend.Slot.Budget.negotiateSlots_converges_and_conserves_budget by
  mutation Obend.Slot.Budget.negotiateSlots := fun _ _ _ _ => .ok ⟨[], 0⟩

#tooth Obend.Slot.Budget.negotiateSlots_complete_no_deadlock by
  mutation Obend.Slot.Budget.negotiateSlots := fun _ _ _ _ => .error (.cyclicGluingConflict 0 [])

#tooth Obend.Slot.Budget.sumResourceCosts_dedup_lt_of_shared by
  mutation Obend.Slot.Budget.sumResourceCosts := fun _ _ => 0

#tooth Obend.Slot.Budget.realizerGraphValid_dependency_closure by
  mutation Obend.Slot.Budget.realizerGraphValid := fun _ => true

-- 12–16: Receipt.Merkle (completeness + domain separation + spanSize/startIdx framing!)
#tooth Obend.Receipt.Merkle.verifyBlindedMultiproof256_complete by
  mutation Obend.Receipt.Merkle.verifyBlindedMultiproof256 := fun _ _ _ => false

#tooth Obend.Receipt.Merkle.verifyBlindedMultiproof256_complete by
  mutation Obend.Receipt.Merkle.evalBlindedNode256 := fun _ _ _ _ => none

#tooth Obend.Receipt.Merkle.internalPreimage256_injective by
  mutation Obend.Receipt.Merkle.internalPreimage256 :=
    fun _ startIdx left right =>
      encodeFields [[0x01], leb128 startIdx, bytesOfDigest256 left, bytesOfDigest256 right]

#tooth Obend.Receipt.Merkle.internalPreimage256_injective by
  mutation Obend.Receipt.Merkle.internalPreimage256 :=
    fun spanSize _ left right =>
      encodeFields [[0x01], leb128 spanSize, bytesOfDigest256 left, bytesOfDigest256 right]

#tooth Obend.Receipt.Merkle.leaf_ne_internal_preimage256 by
  mutation Obend.Receipt.Merkle.leafPreimage256 :=
    fun idx salt payload =>
      encodeFields [[0x01], leb128 idx, bytesOfDigest256 salt, payload]

-- 17–18: Fold.Collapse
#tooth Obend.Fold.Collapse.verifyCollapsedHorizonMultiproof256_complete by
  mutation Obend.Fold.Collapse.verifyCollapsedHorizonMultiproof256 := fun _ _ _ _ => false

#tooth Obend.Fold.Collapse.collapsedHorizon_redaction_nonleakage by
  mutation Obend.Fold.Collapse.buildCollapsedHorizonMultiproof256 :=
    fun _ _ _ _ _ q => ⟨0, q, .empty⟩

-- 19–21: Reasons & Reasons.DialecticalBlame
#tooth Obend.Reasons.traceUnsupportedRoot_sound by
  mutation Obend.Reasons.traceUnsupportedRoot := fun _ x => .unexplained x

#tooth Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame_inl_sound by
  mutation Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame :=
    fun _ _ _ _ _ _ _ _ _ => .inl ⟨[], 0, 0⟩

#tooth Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame_inr_sound by
  mutation Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame :=
    fun _ _ _ _ _ _ _ _ _ =>
      .inr (.invalidReceiptMultiproof 0 0 "receipt_multiproof_invalid" .alreadySupported)

/-! ## 4. Constructive Extractor & Apex Theorem Axiom Audits (`0 sorryAx`, `0 Classical.choice` in Extractors) -/

#print axioms Obend.Intention.resolveBatch_sound
#print axioms Obend.Slot.Budget.negotiateSlots
#print axioms Obend.Slot.Budget.negotiateSlots_converges_and_conserves_budget
#print axioms Obend.Slot.Budget.negotiateSlots_complete_no_deadlock
#print axioms Obend.Receipt.Merkle.verifyBlindedMultiproof256_complete
#print axioms Obend.Receipt.Merkle.extractMultiproofCollision
#print axioms Obend.Receipt.Merkle.blindedMultiproof_redaction_nonleakage
#print axioms Obend.Fold.Collapse.verifyCollapsedHorizonMultiproof256_complete
#print axioms Obend.Fold.Collapse.extractCollapsedHorizonCollision
#print axioms Obend.Reasons.traceUnsupportedRoot_sound
#print axioms Obend.Reasons.DialecticalBlame.dialecticalAudit_unique_equilibrium
#print axioms Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame
#print axioms Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame_inl_sound
#print axioms Obend.Reasons.DialecticalBlame.diagnoseDialecticalBlame_inr_sound
#print axioms endToEnd_schelling_slot_receipt_equilibrium_certified

end Obend.Tests.Metasystem.SlotReceiptIntentionRevivalTest

end
