module
/-
# Obend.Metatheory.LiveEvolutionAndLink — Polarity-Graded Live Evolution, History Refactoring & Blame

Completes Obend's General Metatheory of Distributed, Decentralized Houyhnhnm Computation:
1. **Polarity-Graded Exhaustive Linear `SchemaMorphism`**:
   - Source-field linearity (`(dispositions.map srcName).Nodup`), target uniqueness, and fused
     `Cubical2LTT.AdapterChain`s (`fuseAdapters`).
   - Injective, destination-checked sum-tag mapping (`checkSumExhaustive`) refusing wildcard
     catch-all masking AND multi-tag catch-all collapse.
   - **Asymmetric Row Variance**: `.positiveData` rows covariantly preserve `unknownFields` and their
     256-bit `unknownFieldsDigest`, whereas `.negativeAuthority` rows forbid field drops and
     contravariantly transport every `mustUnderstand = true` caveat into a `mustUnderstand = true`
     caveat in `dstCaveats`.
2. **Demand-Driven `IncoherenceObligation` Holes (`Core.Term.hole`)**:
   - Dynamic relevance dichotomy (`incoherence_relevance_dichotomy`) across taken vs. untaken branches,
     attributing the exact `obligationId` even after multi-step machine branching.
3. **`ValidHistoryRefactoring` (`ActualHistory ↠ EffectiveHistory`)**:
   - Coalescing internal causal cones preserves `QuiescentValid`, global nullifier `Nodup`, and
     exact macro-boundary pins.
4. **External-Context `SlotBinding` + `SuperRefines` + `SubadditiveBlame`**:
   - Verifies untrusted `SlotSubmission`s against caller-owned `SlotContext` (`author ≠ integrator`,
     `interfaceDigest = expectedInterfaceDigest`, `claimObj.layer = slotId`, and `superClaimCheck = .ok`),
     localizes cut faults without blaming compliant peers, and proves blame subadditivity.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Core.Cubical2LTT
public import Obend.Vault.CheckedCarry
public import Obend.Logic.Obligation
import all Obend.Logic.Obligation
public import Obend.Metatheory.StratifiedCut

public section

namespace Obend.Metatheory.LiveEvolutionAndLink

open Obend.Digest
open Obend.Core.Term
open Obend.Core.Machine (State Limits)
open Obend.Core.Cubical2LTT (AdapterOp AdapterChain evalChain chainGrade fuseAdapters fuseAdapters_sound)
open Obend.Category (CompositeGrade GradeMonoid)
open Obend.Vault.CheckedCarry (DropReason)
open Obend.Logic (ClaimObj RStep superClaimCheck superClaim_sound T3_super_claim_frame superSupports SuperSupport)
open Obend.Polis.HouyhnhnmMonitor (PinInterposition VirtualizedCell stepVirtualizedCell MonitorBlame)
open Obend.Metatheory.PinsAndQuiescence
open Obend.Metatheory.SponsorAndMigration (machineGuestRunner runBoundedTrackingHole pendingHoleId?
  subsetCaps subsetCaps_refl subsetCaps_trans)

set_option autoImplicit false

/-! ## 1. Polarity-Graded Exhaustive Linear `SchemaMorphism` -/

/-- Polarity of a schema row across decentralized bidirectional lenses:
    - `positiveData`: display/payload record (covariant unknown-field passthrough + 256-bit digest),
    - `negativeAuthority`: capability/caveat record (contravariant fail-closed `mustUnderstand` transport,
      forbidding field drops). -/
inductive RowPolarity where
  | positiveData
  | negativeAuthority
  deriving DecidableEq, Repr

inductive FieldDisposition where
  | mapped (srcField targetField : String) (chain : AdapterChain)
  | dropped (srcField : String) (reason : DropReason)

@[expose] def FieldDisposition.srcName : FieldDisposition → String
  | .mapped s _ _ => s
  | .dropped s _ => s

@[expose] def FieldDisposition.isDropped : FieldDisposition → Bool
  | .mapped _ _ _ => false
  | .dropped _ _ => true

/-- Sum-type tag mapping enforcing injectivity and destination-tag membership (preventing both
    explicit `hasWildcardCatchAll` and implicit many-to-one catch-all tag collapse). -/
structure SumSchemaMap where
  srcTags             : List String
  dstTags             : List String
  explicitArmPairs    : List (String × String)
  hasWildcardCatchAll : Bool
  deriving DecidableEq, Repr

@[expose] def checkSumExhaustive (sm : SumSchemaMap) : Bool :=
  !sm.hasWildcardCatchAll &&
  decide (sm.explicitArmPairs.map Prod.fst).Nodup &&
  decide (sm.explicitArmPairs.map Prod.snd).Nodup &&
  sm.explicitArmPairs.all (fun p => sm.dstTags.contains p.2) &&
  sm.srcTags.all (fun tag => sm.explicitArmPairs.any (fun p => p.1 == tag))

/-- Security caveat carried in a `.negativeAuthority` row. -/
structure AuthorityCaveat where
  caveatId       : String
  mustUnderstand : Bool
  deriving DecidableEq, Repr

/-- Explicit caveat migration entry mapping `srcCaveatId` to a mandatory caveat in `dstCaveats`. -/
structure CaveatTranslation where
  srcCaveatId : String
  dstCaveatId : String
  attenuates  : Bool
  deriving DecidableEq, Repr

/-- Complete polarized linear schema morphism specification. -/
structure SchemaMorphism where
  polarity           : RowPolarity
  srcFields          : List String
  dispositions       : List FieldDisposition
  retireAllowlist    : List String
  sumMap             : SumSchemaMap
  srcCaveats         : List AuthorityCaveat
  dstCaveats         : List AuthorityCaveat
  caveatTranslations : List CaveatTranslation

inductive SchemaRefusal where
  | unmappedSourceField (field : String)
  | duplicateOrExtraneousSourceField
  | unauthorizedFieldDrop (field : String)
  | duplicateTargetField
  | wildcardCatchAllForbidden
  | nonExhaustiveOrCollapsedSumTag
  | negativeAuthorityDropForbidden
  | droppedMandatoryCaveat (caveatId : String)
  deriving DecidableEq, Repr

@[expose] def keptTargetFields (ds : List FieldDisposition) : List String :=
  ds.filterMap fun d =>
    match d with
    | .mapped _ tgt _ => some tgt
    | .dropped _ _ => none

@[expose] def checkFieldDispositions (retireAllowlist : List String) : List FieldDisposition → Option SchemaRefusal
  | [] => none
  | .mapped _ _ _ :: rest => checkFieldDispositions retireAllowlist rest
  | .dropped s r :: rest =>
      if retireAllowlist.contains s && decide (r.contractName != "") then
        checkFieldDispositions retireAllowlist rest
      else
        some (.unauthorizedFieldDrop s)

/-- Contravariant caveat check: every `mustUnderstand = true` caveat in `srcCaveats` must map via an
    `attenuates = true` entry to an active `mustUnderstand = true` caveat present in `dstCaveats`! -/
@[expose] def checkMandatoryCaveats (trans : List CaveatTranslation) (dstCaveats : List AuthorityCaveat) :
    List AuthorityCaveat → Option SchemaRefusal
  | [] => none
  | c :: rest =>
      if c.mustUnderstand then
        if trans.any (fun t =>
            t.srcCaveatId == c.caveatId && t.attenuates &&
            dstCaveats.any (fun dc => dc.caveatId == t.dstCaveatId && dc.mustUnderstand)) then
          checkMandatoryCaveats trans dstCaveats rest
        else
          some (.droppedMandatoryCaveat c.caveatId)
      else
        checkMandatoryCaveats trans dstCaveats rest

/-- Executable linear & polarity-graded schema morphism verifier. -/
@[expose] def checkSchemaMorphism (M : SchemaMorphism) : Except SchemaRefusal Unit := do
  let srcDispNames := M.dispositions.map FieldDisposition.srcName
  match M.srcFields.find? (fun f => !srcDispNames.contains f) with
  | some missing => throw (.unmappedSourceField missing)
  | none => pure ()
  if !(decide srcDispNames.Nodup && srcDispNames.all (fun f => M.srcFields.contains f)) then
    throw .duplicateOrExtraneousSourceField
  match checkFieldDispositions M.retireAllowlist M.dispositions with
  | some err => throw err
  | none => pure ()
  if !decide (keptTargetFields M.dispositions).Nodup then
    throw .duplicateTargetField
  if M.sumMap.hasWildcardCatchAll then
    throw .wildcardCatchAllForbidden
  if !checkSumExhaustive M.sumMap then
    throw .nonExhaustiveOrCollapsedSumTag
  match M.polarity with
  | .positiveData => pure ()
  | .negativeAuthority =>
      if M.dispositions.any FieldDisposition.isDropped then
        throw .negativeAuthorityDropForbidden
      match checkMandatoryCaveats M.caveatTranslations M.dstCaveats M.srcCaveats with
      | some err => throw err
      | none => pure ()

/-- Wildcard sum catch-all (`hasWildcardCatchAll = true`) is unconditionally refused. -/
theorem schemaMorphism_bans_wildcard_sum (M : SchemaMorphism)
    (hWild : M.sumMap.hasWildcardCatchAll = true) :
    ∀ u, checkSchemaMorphism M ≠ .ok u := by
  intro u hOk
  unfold checkSchemaMorphism at hOk; dsimp only at hOk
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  cases hOk

private theorem checkMandatoryCaveats_sound {trans : List CaveatTranslation}
    {dsts : List AuthorityCaveat} :
    ∀ {cs : List AuthorityCaveat},
      checkMandatoryCaveats trans dsts cs = none →
      ∀ c ∈ cs, c.mustUnderstand = true →
        trans.any (fun t =>
          t.srcCaveatId == c.caveatId && t.attenuates &&
          dsts.any (fun dc => dc.caveatId == t.dstCaveatId && dc.mustUnderstand)) = true
  | [], _, _, hc, _ => absurd hc List.not_mem_nil
  | c₀ :: rest, hNone, c, hcMem, hMust => by
    unfold checkMandatoryCaveats at hNone
    rcases List.mem_cons.1 hcMem with rfl | hInRest
    · simp only [hMust, ite_true] at hNone
      split at hNone
      · rename_i hAny; exact hAny
      · cases hNone
    · by_cases hm₀ : c₀.mustUnderstand = true
      · simp only [hm₀, ite_true] at hNone
        split at hNone
        · exact checkMandatoryCaveats_sound hNone c hInRest hMust
        · cases hNone
      · simp only [hm₀, Bool.false_eq_true, ite_false] at hNone
        exact checkMandatoryCaveats_sound hNone c hInRest hMust

/-- **Contravariant Authority Safety & Linearity (`schemaMorphism_blocks_confused_deputy_caveat_drop`)**:
    In any accepted `.negativeAuthority` `SchemaMorphism`:
    1. Source dispositions are strictly linear (`Nodup`) and zero fields are dropped,
    2. Sum arms are injective (`(explicitArmPairs.map Prod.snd).Nodup`, blocking catch-all tag collapse), and
    3. Every `mustUnderstand = true` caveat in `srcCaveats` maps to a genuine `mustUnderstand = true`
       caveat present in `dstCaveats` via an `attenuates = true` translation! -/
theorem schemaMorphism_blocks_confused_deputy_caveat_drop (M : SchemaMorphism)
    (hNeg : M.polarity = .negativeAuthority)
    (hOk : checkSchemaMorphism M = .ok ()) :
    (M.dispositions.map FieldDisposition.srcName).Nodup ∧
    (M.sumMap.explicitArmPairs.map Prod.snd).Nodup ∧
    (∀ d ∈ M.dispositions, d.isDropped = false) ∧
    (∀ c ∈ M.srcCaveats, c.mustUnderstand = true →
      ∃ t ∈ M.caveatTranslations, ∃ dc ∈ M.dstCaveats,
        t.srcCaveatId = c.caveatId ∧ t.dstCaveatId = dc.caveatId ∧
        t.attenuates = true ∧ dc.mustUnderstand = true) := by
  unfold checkSchemaMorphism at hOk; dsimp only at hOk
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  rename_i hLin
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  split at hOk; · cases hOk
  rename_i hSumEx
  rw [hNeg] at hOk; dsimp only at hOk
  split at hOk; · cases hOk
  rename_i hNoDrop
  cases hCav : checkMandatoryCaveats M.caveatTranslations M.dstCaveats M.srcCaveats with
  | some _ => rw [hCav] at hOk; cases hOk
  | none =>
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hLin
    simp only [Bool.not_eq_true', Bool.not_eq_false, checkSumExhaustive, Bool.and_eq_true,
      decide_eq_true_eq] at hSumEx
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hNoDrop
    refine ⟨hLin.1, hSumEx.1.1.2, hNoDrop, fun c hc hMust => ?_⟩
    have hAny := checkMandatoryCaveats_sound hCav c hc hMust
    obtain ⟨t, htMem, htPred⟩ := List.any_eq_true.1 hAny
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at htPred
    obtain ⟨⟨hSrcEq, hAtt⟩, dc, hdcMem, hdcEq, hdcMust⟩ := htPred
    exact ⟨t, htMem, dc, hdcMem, hSrcEq, hdcEq.symm, hAtt, hdcMust⟩

/-- Domain-tagged 256-bit commitment over unknown positive-row fields. -/
def unknownFieldsDigest (ufs : List (String × List UInt8)) : Digest256 :=
  let bytes := ufs.foldr (fun (k, v) acc => k.toUTF8.toList ++ (0 :: v) ++ acc) []
  BitVec.ofNat 256 (HashBytes.ofBE (Cshake256.cshake256Bytes
    "Obend.Metatheory.UnknownRow.v1".toUTF8.toList bytes))

/-- Positive-polarity row carrying known fields AND lossless unknown-field passthrough payload. -/
structure PositiveDataRow where
  knownFields   : List (String × Int)
  unknownFields : List (String × List UInt8)
  deriving DecidableEq, Repr

@[expose] def translatePositiveRow (ds : List FieldDisposition) (row : PositiveDataRow) : PositiveDataRow where
  knownFields := ds.filterMap fun d =>
    match d with
    | .dropped _ _ => none
    | .mapped src tgt chain =>
        (row.knownFields.lookup src).map fun v => (tgt, evalChain (fuseAdapters chain) v)
  unknownFields := row.unknownFields

/-- **Covariant Unknown-Field Roundtrip & Cast-Fusion Soundness (`positiveData_passthrough_and_fusion_sound`)**:
    `translatePositiveRow` preserves all `unknownFields` (every unknown key/payload looks up identically
    before and after translation) and their 256-bit `unknownFieldsDigest`, while fusing `AdapterChain`s. -/
theorem positiveData_passthrough_and_fusion_sound (ds : List FieldDisposition) (row : PositiveDataRow) :
    (translatePositiveRow ds row).unknownFields = row.unknownFields ∧
    unknownFieldsDigest (translatePositiveRow ds row).unknownFields = unknownFieldsDigest row.unknownFields ∧
    (∀ unkKey, (translatePositiveRow ds row).unknownFields.lookup unkKey = row.unknownFields.lookup unkKey) ∧
    ∀ src tgt (chain : AdapterChain) (v : Int),
      evalChain (fuseAdapters chain) v = evalChain chain v ∧
      chainGrade (fuseAdapters chain) ≤ chainGrade chain ∧
      (row.knownFields.lookup src = some v →
        FieldDisposition.mapped src tgt chain ∈ ds →
        (tgt, evalChain chain v) ∈ (translatePositiveRow ds row).knownFields) := by
  refine ⟨rfl, rfl, fun _ => rfl, fun src tgt chain v => ?_⟩
  obtain ⟨hEq, hGr⟩ := fuseAdapters_sound chain v
  refine ⟨hEq, hGr, fun hLk hMem => ?_⟩
  simp only [translatePositiveRow, List.mem_filterMap]
  exact ⟨.mapped src tgt chain, hMem, by simp [hLk, hEq]⟩

/-! ## 2. Demand-Driven `IncoherenceObligation` Holes (`Core.Term.hole`) -/

inductive EdgeCoherence where
  | cohered (adaptedBody : Term)
  | incoherent (obligationId : Nat) (srcSchemaVer dstSchemaVer : Nat)
  deriving Repr

@[expose] def compileEvolutionEdge : EdgeCoherence → Term
  | .cohered body => body
  | .incoherent oid _ _ => .hole oid []

/-- **Relevance-Gated Live Execution Dichotomy (`incoherence_relevance_dichotomy`)**:
    For `prog(takeCohered) = .ifBool (.boolean takeCohered) (.nat v) (compileEvolutionEdge (.incoherent oid sv dv))`:
    1. When `takeCohered = true`, `prog true` evaluates cleanly to `.nat v` despite the untaken incoherent hole.
    2. When `takeCohered = false`, running `prog false` on `Machine.State` steps through `.ifBool` and
       traps cleanly to `VirtualizedCell` with the **exact** `MonitorBlame.incoherentHoleTrap oid`
       and zero committed world side-effects! -/
theorem incoherence_relevance_dichotomy (oid sv dv v : Nat)
    (limits : Limits) (pol : Term → PinInterposition)
    (cell : VirtualizedCell State) (extraTicks : Nat)
    (hStackLim : 1 ≤ limits.stack)
    (hGuest : cell.guest = Obend.Core.Machine.initial
      (.ifBool (.boolean false) (.nat v) (compileEvolutionEdge (.incoherent oid sv dv))))
    (hTicks : cell.tickSlice = extraTicks + 4) :
    Evaluates (.ifBool (.boolean true) (.nat v) (compileEvolutionEdge (.incoherent oid sv dv))) (.nat v) ∧
    (let next := stepVirtualizedCell (machineGuestRunner limits) pol cell
     next.blameLog = .incoherentHoleTrap oid :: cell.blameLog ∧
     next.committedEffects = cell.committedEffects) := by
  refine ⟨⟨.next (.ifTrue _ _) (.refl _), .natural v⟩, ?_⟩
  let s0 := Obend.Core.Machine.initial (.ifBool (.boolean false) (.nat v) (.hole oid []))
  let s1 : State := ⟨#[], .evaluate (.boolean false) [], [.ifBool (.nat v) (.hole oid []) []]⟩
  let s2 : State := ⟨#[], .returned (.boolean false), [.ifBool (.nat v) (.hole oid []) []]⟩
  let s3 : State := ⟨#[], .evaluate (.hole oid []) [], []⟩
  let s4 : State := ⟨#[], .refused .unresolvedHole, []⟩
  have hs0 : Obend.Core.Machine.step limits s0 = .suspended .ticks s1 := by
    simp [s0, s1, Obend.Core.Machine.step, Obend.Core.Machine.initial, Obend.Core.Machine.stepRaw, hStackLim]
  have hs1 : Obend.Core.Machine.step limits s1 = .suspended .ticks s2 := by
    simp [s1, s2, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw, hStackLim]
  have hs2 : Obend.Core.Machine.step limits s2 = .suspended .ticks s3 := by
    simp [s2, s3, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw]
  have hs3 : Obend.Core.Machine.step limits s3 = .suspended .ticks s4 := by
    simp [s3, s4, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw]
  have hTail : runBoundedTrackingHole limits extraTicks (some oid) s4 =
      (some oid, .refused .unresolvedHole s4) := by
    cases extraTicks <;> simp [runBoundedTrackingHole, pendingHoleId?, Option.or, Obend.Core.Machine.step, s4]
  have hEqT : extraTicks + 4 = (((extraTicks + 1) + 1) + 1) + 1 := by omega
  have hTrack : runBoundedTrackingHole limits (extraTicks + 4) none s0 =
      (some oid, .refused .unresolvedHole s4) := by
    rw [hEqT]
    simp [runBoundedTrackingHole, s0, s1, s2, s3, pendingHoleId?, Option.or, hs0, hs1, hs2, hs3, hTail]
  have hSlice : (machineGuestRunner limits).runSlice cell.tickSlice cell.guest = .refusedHole oid s4 := by
    simp [machineGuestRunner, hGuest, hTicks, compileEvolutionEdge, s0, hTrack]
  simp [stepVirtualizedCell, hSlice]

/-! ## 3. `ValidHistoryRefactoring` (`ActualHistory ↠ EffectiveHistory` Preserving `foldHorizon`) -/

structure ValidHistoryRefactoring where
  sliceId         : Digest256
  actualEvents    : List OpenEvent
  actualMacro     : OpenEvent
  actualParts     : List (List BoundaryPins)
  effectiveParts  : List (List BoundaryPins)
  hCone           : ValidHorizonCone sliceId actualEvents actualMacro
  hActualFlat     : actualParts.flatten = actualEvents.map OpenEvent.boundary
  hEffectiveFlat  : effectiveParts.flatten = actualEvents.map OpenEvent.boundary
  hDisjoint       : PairwiseHorizonDisjoint (actualEvents.map OpenEvent.boundary)

/-- **History Refactoring Soundness (`refactorHistory_preserves_quiescence_and_boundary`)**:
    Preserves `QuiescentValid`, global nullifier `Nodup`, and exact folded macro-boundaries. -/
theorem refactorHistory_preserves_quiescence_and_boundary (R : ValidHistoryRefactoring) :
    foldHorizon R.sliceId R.actualEvents = some R.actualMacro ∧
    QuiescentValid R.actualMacro ∧
    (pinNullifiers (R.actualEvents.flatMap OpenEvent.inPins)).Nodup ∧
    foldHorizonBoundaries (R.effectiveParts.map foldHorizonBoundaries) =
      foldHorizonBoundaries (R.actualParts.map foldHorizonBoundaries) := by
  have ⟨hConeFn, hPartFn⟩ := foldHorizon_quiescent_and_observer_invariant R.sliceId
  obtain ⟨hFold, hQuiesc, hNodup⟩ := hConeFn R.hCone
  have hActDisj : PairwiseHorizonDisjoint R.actualParts.flatten := by rw [R.hActualFlat]; exact R.hDisjoint
  have hEffDisj : PairwiseHorizonDisjoint R.effectiveParts.flatten := by rw [R.hEffectiveFlat]; exact R.hDisjoint
  refine ⟨hFold, hQuiesc, hNodup, ?_⟩
  rw [hPartFn R.effectiveParts hEffDisj, R.hEffectiveFlat, ← R.hActualFlat, ← hPartFn R.actualParts hActDisj]

/-! ## 4. External-Context Schelling `SlotBinding`, `SuperRefines` & `SubadditiveBlame` -/

/-- Caller-owned slot requirements (NOT supplied by the component author!). -/
structure SlotContext where
  slotId                  : Nat
  integratorPrincipal     : Digest256
  expectedInterfaceDigest : Digest256
  deriving DecidableEq, Repr

/-- Component author's untrusted slot submission. -/
structure SlotSubmission where
  authorPrincipal : Digest256
  interfaceDigest : Digest256
  claimFuel       : Nat
  claimObj        : ClaimObj
  certSteps       : List RStep

/-- Verify an untrusted `SlotSubmission` against caller-owned `SlotContext`. -/
@[expose] def verifySlotBinding (ctx : SlotContext) (sub : SlotSubmission) : Bool :=
  (sub.authorPrincipal != 0#256) &&
  (ctx.integratorPrincipal != 0#256) &&
  (sub.authorPrincipal != ctx.integratorPrincipal) &&
  (sub.interfaceDigest == ctx.expectedInterfaceDigest) &&
  (sub.claimObj.layer == ctx.slotId) &&
  (match superClaimCheck sub.claimFuel sub.claimObj sub.certSteps with
   | .ok => true
   | _ => false)

theorem verifySlotBinding_refuses_self_dealing (ctx : SlotContext) (sub : SlotSubmission)
    (hSame : sub.authorPrincipal = ctx.integratorPrincipal) :
    verifySlotBinding ctx sub = false := by
  simp [verifySlotBinding, hSame]

theorem verifySlotBinding_complete (author integrator digest : Digest256)
    (hAuth : author ≠ 0#256) (hInt : integrator ≠ 0#256) (hDisj : author ≠ integrator) :
    verifySlotBinding ⟨Obend.Logic.verticalLimitClaimObj.layer, integrator, digest⟩
      ⟨author, digest, 10, Obend.Logic.verticalLimitClaimObj, Obend.Logic.verticalLimitSteps⟩ = true := by
  unfold verifySlotBinding
  simp [bne_iff_ne, hAuth, hInt, hDisj, Obend.Logic.verticalLimit_superClaim_accepted.1]

/-- **`verifySlotBinding_sound` + Vertical `T3_super_claim_frame` Transport**. -/
theorem verifySlotBinding_sound (ctx : SlotContext) (sub : SlotSubmission)
    (hOk : verifySlotBinding ctx sub = true) :
    sub.authorPrincipal ≠ 0#256 ∧
    ctx.integratorPrincipal ≠ 0#256 ∧
    sub.authorPrincipal ≠ ctx.integratorPrincipal ∧
    sub.interfaceDigest = ctx.expectedInterfaceDigest ∧
    sub.claimObj.layer = ctx.slotId ∧
    Obend.Logic.claimMeaning sub.claimObj ∧
    (∀ (C' : Obend.Logic.Composition) (j' : Nat),
      (∀ sp ∈ superSupports sub.claimObj sub.certSteps, SuperSupport.holds C' sub.claimObj.arity j' sp = true) →
      ({ sub.claimObj with comp := C', layer := j' } : ClaimObj).wellFormed = true →
      superClaimCheck sub.claimFuel { sub.claimObj with comp := C', layer := j' } sub.certSteps = .ok) := by
  unfold verifySlotBinding at hOk
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hOk
  obtain ⟨⟨⟨⟨⟨hAuthNz, hIntNz⟩, hDisj⟩, hDig⟩, hLay⟩, hSupMatch⟩ := hOk
  have hSupOk : superClaimCheck sub.claimFuel sub.claimObj sub.certSteps = .ok := by
    cases hS : superClaimCheck sub.claimFuel sub.claimObj sub.certSteps <;> simp [hS] at hSupMatch
    rfl
  exact ⟨hAuthNz, hIntNz, hDisj, hDig, hLay, superClaim_sound hSupOk,
    fun C' j' hHolds hWf => (T3_super_claim_frame hSupOk hHolds hWf).1⟩

@[expose] def localizeCutFault (senderId receiverId : Nat)
    (senderPinValid receiverAcceptedPost : Bool) : List Nat :=
  if !senderPinValid then [senderId]
  else if !receiverAcceptedPost then [receiverId]
  else []

theorem localizeCutFault_never_blames_compliant (senderId receiverId : Nat)
    (senderPinValid receiverAcceptedPost : Bool) :
    (senderPinValid = true → senderId ≠ receiverId →
      senderId ∉ localizeCutFault senderId receiverId senderPinValid receiverAcceptedPost) ∧
    (receiverAcceptedPost = true → senderId ≠ receiverId →
      receiverId ∉ localizeCutFault senderId receiverId senderPinValid receiverAcceptedPost) := by
  refine ⟨fun hS hNe => ?_, fun hR hNe => ?_⟩
  · cases receiverAcceptedPost <;> simp [localizeCutFault, hS, hNe]
  · cases senderPinValid <;> simp [localizeCutFault, hR, Ne.symm hNe]

def dedupNats : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let r := dedupNats xs
      if r.contains x then r else x :: r

@[expose] def blameSet (isFaulty : Nat → Bool) (S : List Nat) : Nat :=
  (dedupNats (S.filter isFaulty)).length

private theorem mem_dedupNats_iff :
    ∀ {xs : List Nat} {a : Nat}, a ∈ dedupNats xs ↔ a ∈ xs
  | [], _ => Iff.rfl
  | x :: xs, a => by
    simp only [dedupNats]
    cases hContains : (dedupNats xs).contains x
    · simp only [Bool.false_eq_true, ite_false, List.mem_cons, mem_dedupNats_iff]
    · simp only [ite_true, mem_dedupNats_iff, List.mem_cons]
      have hxIn : x ∈ xs := mem_dedupNats_iff.1 (List.contains_iff_mem.1 hContains)
      exact ⟨fun h => .inr h, fun h => by rcases h with rfl | hr; exact hxIn; exact hr⟩

private theorem nodup_dedupNats :
    ∀ (xs : List Nat), (dedupNats xs).Nodup
  | [] => List.Pairwise.nil
  | x :: xs => by
    simp only [dedupNats]
    cases hContains : (dedupNats xs).contains x
    · simp only [Bool.false_eq_true, ite_false, List.nodup_cons]
      refine ⟨fun hMem => ?_, nodup_dedupNats xs⟩
      have hc : (dedupNats xs).contains x = true := List.contains_iff_mem.2 hMem
      rw [hContains] at hc; cases hc
    · simp only [ite_true]; exact nodup_dedupNats xs

private theorem length_le_of_nodup_subset :
    ∀ {xs ys : List Nat}, xs.Nodup → (∀ a ∈ xs, a ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hNodup, hSub => by
    rw [List.nodup_cons] at hNodup
    obtain ⟨hxNotInXs, hNodupXs⟩ := hNodup
    have hxInYs : x ∈ ys := hSub x List.mem_cons_self
    have hSubErase : ∀ a ∈ xs, a ∈ ys.erase x := by
      intro a ha
      have haNe : a ≠ x := fun hEq => hxNotInXs (hEq ▸ ha)
      exact (List.mem_erase_of_ne haNe).2 (hSub a (List.mem_cons_of_mem x ha))
    have hRec := length_le_of_nodup_subset hNodupXs hSubErase
    have hPos : 0 < ys.length := List.length_pos_of_mem hxInYs
    have hErase : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hxInYs
    simp only [List.length_cons]
    omega

/-- **Subadditive Blame Law (`subadditive_blame`)**. -/
theorem subadditive_blame (isFaulty : Nat → Bool) :
    blameSet isFaulty [] = 0 ∧
    (∀ (A B : List Nat), (∀ x ∈ A, x ∈ B) → blameSet isFaulty A ≤ blameSet isFaulty B) ∧
    (∀ (A B : List Nat), blameSet isFaulty (A ++ B) ≤ blameSet isFaulty A + blameSet isFaulty B) := by
  refine ⟨rfl, fun A B hSub => ?_, fun A B => ?_⟩
  · unfold blameSet
    apply length_le_of_nodup_subset (nodup_dedupNats _)
    intro x hx; rw [mem_dedupNats_iff, List.mem_filter] at hx ⊢
    exact ⟨hSub x hx.1, hx.2⟩
  · unfold blameSet
    have hLenAppend : (dedupNats (A.filter isFaulty) ++ dedupNats (B.filter isFaulty)).length =
        (dedupNats (A.filter isFaulty)).length + (dedupNats (B.filter isFaulty)).length := List.length_append
    rw [← hLenAppend]
    apply length_le_of_nodup_subset (nodup_dedupNats _)
    intro x hx
    rw [mem_dedupNats_iff, List.mem_filter, List.mem_append] at hx
    rw [List.mem_append, mem_dedupNats_iff, mem_dedupNats_iff, List.mem_filter, List.mem_filter]
    rcases hx.1 with hA | hB
    · exact .inl ⟨hA, hx.2⟩
    · exact .inr ⟨hB, hx.2⟩

/-- Multi-epoch live evolution trace threading capability attenuation AND chaining each epoch's
    `dstCaveats` into the next epoch's `srcCaveats` (`M.srcCaveats = cavs₀ ∧ M.dstCaveats = cavs₁`)! -/
inductive ValidEvolutionTrace :
    List Nat → List AuthorityCaveat →
    List (SchemaMorphism × SlotContext × SlotSubmission) →
    List Nat → List AuthorityCaveat → Prop where
  | nil (caps : List Nat) (cavs : List AuthorityCaveat) :
      ValidEvolutionTrace caps cavs [] caps cavs
  | step {caps₀ caps₁ caps₂ : List Nat} {cavs₀ cavs₁ cavs₂ : List AuthorityCaveat}
      {M : SchemaMorphism} {ctx : SlotContext} {sub : SlotSubmission}
      {rest : List (SchemaMorphism × SlotContext × SlotSubmission)} :
      subsetCaps caps₁ caps₀ = true →
      M.polarity = .negativeAuthority →
      M.srcCaveats = cavs₀ →
      M.dstCaveats = cavs₁ →
      checkSchemaMorphism M = .ok () →
      verifySlotBinding ctx sub = true →
      ValidEvolutionTrace caps₁ cavs₁ rest caps₂ cavs₂ →
      ValidEvolutionTrace caps₀ cavs₀ ((M, ctx, sub) :: rest) caps₂ cavs₂

/-- **Transitive Multi-Epoch Authority & Caveat Preservation (`validEvolutionTrace_preserves_authority_and_caveats`)**:
    Across any $N$-epoch `ValidEvolutionTrace`:
    1. Capabilities remain monotonically confined (`subsetCaps finalCaps initCaps = true`),
    2. If `initCaveats` contained ANY `mustUnderstand = true` caveat, `finalCaveats` is guaranteed to
       retain an active `mustUnderstand = true` caveat (multi-epoch upgrades can NEVER silently shed
       mandatory caveats by resetting `srcCaveats := []`!), and
    3. Every epoch satisfies `authorPrincipal ≠ integratorPrincipal`, `claimObj.layer = slotId`,
       and `claimMeaning`. -/
theorem validEvolutionTrace_preserves_authority_and_caveats
    {initCaps finalCaps : List Nat} {initCavs finalCavs : List AuthorityCaveat}
    {epochs : List (SchemaMorphism × SlotContext × SlotSubmission)}
    (hTr : ValidEvolutionTrace initCaps initCavs epochs finalCaps finalCavs) :
    subsetCaps finalCaps initCaps = true ∧
    ((∃ c ∈ initCavs, c.mustUnderstand = true) → (∃ dc ∈ finalCavs, dc.mustUnderstand = true)) ∧
    ∀ e ∈ epochs,
      e.2.2.authorPrincipal ≠ e.2.1.integratorPrincipal ∧
      e.2.2.claimObj.layer = e.2.1.slotId ∧
      Obend.Logic.claimMeaning e.2.2.claimObj := by
  induction hTr with
  | nil cs cv =>
    exact ⟨subsetCaps_refl cs, id, fun _ he => absurd he List.not_mem_nil⟩
  | @step _ _ _ _ _ _ M ctx sub _ hSub hPol hSrcEq hDstEq hSchema hSlot _ ih =>
    have hCavStep := schemaMorphism_blocks_confused_deputy_caveat_drop M hPol hSchema
    refine ⟨subsetCaps_trans ih.1 hSub, fun ⟨c₀, hc₀, hMust₀⟩ => ?_, fun e he => ?_⟩
    · rw [← hSrcEq] at hc₀
      obtain ⟨_, _, dc₁, hdc₁, _, _, _, hMust₁⟩ := hCavStep.2.2.2 c₀ hc₀ hMust₀
      rw [hDstEq] at hdc₁
      exact ih.2.1 ⟨dc₁, hdc₁, hMust₁⟩
    · rcases List.mem_cons.1 he with rfl | hInRest
      · have hSnd := verifySlotBinding_sound ctx sub hSlot
        exact ⟨hSnd.2.2.1, hSnd.2.2.2.2.1, hSnd.2.2.2.2.2.1⟩
      · exact ih.2.2 e hInRest

end Obend.Metatheory.LiveEvolutionAndLink
end
