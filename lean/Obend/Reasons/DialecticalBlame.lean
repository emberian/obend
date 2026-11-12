module
/-
# Obend.Reasons.DialecticalBlame — Constructive Dialectical Blame Certificates for Schelling Slots, Clairvoyant Cost Contracts, & Blinded Receipts

Welds `Obend.Reasons` (well-founded justification & cycle-safe defeat chains),
`Obend.Reasons.UnifiedEquilibrium` (stratified total well-founded models & unique Gelfond–Lifschitz
stable equilibria), `Obend.Slot.Budget` (`OpenSlotInterface`, `SlotCandidate`, `BoundSlot`,
`LocalSlotFailure`, `auditCandidateLocal`, `checkCandidateLocal`, `allPairsGluingCompatible`,
`negotiateSlots`), `Obend.Equiv.Cost` (`CostAtMost`, Clairvoyant budget contracts), and
`Obend.Receipt.Merkle` (`BlindedMultiproof256`, `verifyBlindedMultiproof256`).

Given a candidate tuple of bound Schelling slots, a 256-bit salted blinded Merkle receipt multiproof,
and an optional governance `Reasons.Base` (which may contain arbitrary cyclic positive or negative
defeat graphs), this module:
1. Compiles the multi-organ audit evidence into a stratified `Obend.Reasons.Base`
   (`buildDialecticalAuditBase`) whose program `P` satisfies `IsAuditStratified`
   (`dialecticalAudit_stratified`), implies `UnifiedEquilibrium.IsTotalWF P`
   (`auditStratified_implies_totalWF`), and therefore possesses a unique Gelfond–Lifschitz stable
   model accepted by `UnifiedEquilibrium.unifiedEquilibriumJudge` (`dialecticalAudit_unique_equilibrium`).
2. Computes a constructive `Type`-valued `PSum` verdict (`diagnoseDialecticalBlame` — `0 Classical.choice`)
   returning either:
   - `.inl AdmissibleRealizationCert`: certifying that every slot satisfies its nominal `Kind` C4
     lineage, `Intention` / `SupportSheaf` usability, and Clairvoyant `Equiv.Cost.CostAtMost` ceiling,
     all pairwise gluing overlaps hold, the 256-bit blinded Merkle multiproof verifies, and
     `"admissible:realization"` is `.supported` in `Reasons.wf`; or
   - `.inr DialecticalBlameCert`: constructively pinpointing the exact offending slot binding,
     pairwise gluing conflict, invalid receipt multiproof, or defeated/cyclic governance policy atom
     together with its `Reasons` defeat status and cycle-safe `Reasons.BlockerChain`.
-/
public import Obend.Reasons
public import Obend.Reasons.UnifiedEquilibrium
public import Obend.Slot.Budget
public import Obend.Receipt.Merkle
public import Obend.Digest.HashBytes
public section

namespace Obend.Reasons.DialecticalBlame

open Obend
open Obend.Digest.HashBytes (Hash)
open Obend.Reasons
open Obend.Reasons.UnifiedEquilibrium
open Obend.Slot.Budget
open Obend.Receipt.Merkle

set_option autoImplicit false

/-! ## 1. Canonical Dialectical Audit Atoms & Stratified Justification Base -/

/-- Target conclusion atom certifying that the entire multi-slot realization and receipt stand. -/
abbrev realizationAdmissibleAtom : String := "admissible:realization"

/-- Positive evidence atom for bound slot at index `idx` with identifier `slotId`. -/
abbrev slotVerifiedAtom (idx : Nat) (slotId : String) : String :=
  "slot_ok:" ++ toString idx ++ ":" ++ slotId

/-- Negative defeater atom for bound slot at index `idx` with identifier `slotId`. -/
abbrev slotViolationAtom (idx : Nat) (slotId : String) : String :=
  "slot_violation:" ++ toString idx ++ ":" ++ slotId

/-- Positive evidence atom for pairwise SupportSheaf gluing compatibility. -/
abbrev gluingVerifiedAtom : String := "gluing_ok"

/-- Negative defeater atom for pairwise SupportSheaf gluing conflict. -/
abbrev gluingConflictAtom : String := "gluing_conflict"

/-- Positive evidence atom for 256-bit salted blinded Merkle receipt verification. -/
abbrev receiptVerifiedAtom : String := "receipt_multiproof_ok"

/-- Negative defeater atom for invalid 256-bit salted blinded Merkle receipt multiproof. -/
abbrev receiptInvalidAtom : String := "receipt_multiproof_invalid"

theorem slotVerifiedAtom_ne_admissible (idx : Nat) (slotId : String) :
    slotVerifiedAtom idx slotId ≠ realizationAdmissibleAtom := by
  intro h
  have h0 := congrArg (fun s => s.toList.head?) h
  simp [slotVerifiedAtom, realizationAdmissibleAtom, String.toList_append] at h0

theorem slotViolationAtom_ne_admissible (idx : Nat) (slotId : String) :
    slotViolationAtom idx slotId ≠ realizationAdmissibleAtom := by
  intro h
  have h0 := congrArg (fun s => s.toList.head?) h
  simp [slotViolationAtom, realizationAdmissibleAtom, String.toList_append] at h0

theorem slotViolationAtom_ne_slotVerified (i j : Nat) (s₁ s₂ : String) :
    slotViolationAtom i s₁ ≠ slotVerifiedAtom j s₂ := by
  intro h
  have h0 := congrArg (fun s => s.toList.take 6) h
  simp [slotViolationAtom, slotVerifiedAtom, String.toList_append] at h0

theorem gluingVerified_ne_admissible : gluingVerifiedAtom ≠ realizationAdmissibleAtom := by decide
theorem gluingConflict_ne_admissible : gluingConflictAtom ≠ realizationAdmissibleAtom := by decide
theorem receiptVerified_ne_admissible : receiptVerifiedAtom ≠ realizationAdmissibleAtom := by decide
theorem receiptInvalid_ne_admissible : receiptInvalidAtom ≠ realizationAdmissibleAtom := by decide

/-- Build indexed local slot observations from actual `auditCandidateLocal` ground truth. -/
def buildSlotObservationsAux {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    Nat → List (BoundSlot Pin) → List Observation
  | _, [] => []
  | idx, b :: rest =>
    let obs : Observation :=
      match auditCandidateLocal ks I w b.iface b.cand with
      | none =>
        { name := slotVerifiedAtom idx b.iface.slotId
          text := "verified candidate " ++ b.cand.candId
          source := "Obend.Slot.Budget.auditCandidateLocal" }
      | some _ =>
        { name := slotViolationAtom idx b.iface.slotId
          text := "contract failed on candidate " ++ b.cand.candId
          source := "Obend.Slot.Budget.auditCandidateLocal" }
    obs :: buildSlotObservationsAux ks I w (idx + 1) rest

/-- Positive premises required by `admitRealizationRule` for slots starting at `idx`. -/
def slotPositiveAtoms {Pin : Type} : Nat → List (BoundSlot Pin) → List String
  | _, [] => []
  | idx, b :: rest => slotVerifiedAtom idx b.iface.slotId :: slotPositiveAtoms (idx + 1) rest

/-- Negative defeater atoms attached to `admitRealizationRule` for slots starting at `idx`. -/
def slotNegativeAtoms {Pin : Type} : Nat → List (BoundSlot Pin) → List String
  | _, [] => []
  | idx, b :: rest => slotViolationAtom idx b.iface.slotId :: slotNegativeAtoms (idx + 1) rest

/-- Top-level dialectical rule concluding `realizationAdmissibleAtom` iff all slot, gluing, and
receipt checks hold and no violation defeater is supported. -/
@[expose] def admitRealizationRule {Pin : Type} (bindings : List (BoundSlot Pin)) : Rule :=
  { name := "admit_realization"
    concl := realizationAdmissibleAtom
    pos := slotPositiveAtoms 0 bindings ++ [gluingVerifiedAtom, receiptVerifiedAtom]
    neg := slotNegativeAtoms 0 bindings ++ [gluingConflictAtom, receiptInvalidAtom] }

/-- Non-vacuous receipt verification check: requires at least one opened leaf index
(`!proof.queriedIndices.isEmpty`) AND valid 256-bit salted blinded multiproof verification,
preventing vacuous zero-opening `.blinded root` proofs from certifying a realization. -/
@[expose] def verifyNonEmptyBlindedMultiproof256 (H : Hash) (proof : BlindedMultiproof256)
    (expectedRoot : Digest256) : Bool :=
  !proof.queriedIndices.isEmpty && verifyBlindedMultiproof256 H proof expectedRoot

/-- Compile multi-organ slot, gluing, and blinded multiproof checks into a `Reasons.Base`. -/
@[expose] def buildDialecticalAuditBase {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) : Base :=
  let slotObs := buildSlotObservationsAux ks I w 0 bindings
  let glueObs : Observation :=
    if slotGraphWellFormed (bindings.map (·.iface)) && allPairsGluingCompatible bindings then
      { name := gluingVerifiedAtom, text := "slot graph closed & all pairs gluing-compatible", source := "Slot.SupportSheaf" }
    else
      { name := gluingConflictAtom, text := "malformed slot graph or gluing overlap mismatch", source := "Slot.SupportSheaf" }
  let recObs : Observation :=
    if verifyNonEmptyBlindedMultiproof256 H proof expectedRoot then
      { name := receiptVerifiedAtom, text := "256-bit blinded multiproof valid", source := "Receipt.Merkle" }
    else
      { name := receiptInvalidAtom, text := "256-bit blinded multiproof invalid", source := "Receipt.Merkle" }
  { observations := slotObs ++ [glueObs, recObs]
    explanations := [admitRealizationRule bindings]
    actions := [{ name := "commit_realization", because := realizationAdmissibleAtom }] }

/-- Consistent `Reasons.State` paired with `buildDialecticalAuditBase`. -/
@[expose] def buildDialecticalAuditState {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) : State :=
  let b := buildDialecticalAuditBase ks I w H bindings proof expectedRoot
  { base := b, kept := judge b }

theorem buildDialecticalAuditState_consistent {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) :
    (buildDialecticalAuditState ks I w H bindings proof expectedRoot).Consistent :=
  ⟨Same.refl _, Same.refl _⟩

/-! ## 2. Syntactic Stratification & Unique Gelfond–Lifschitz Equilibrium -/

/-- Two-level stratification ranking all evidence/defeater atoms at stratum `0` and
`realizationAdmissibleAtom` at stratum `1`. -/
@[expose] def dialecticalStratum (atom : String) : Nat :=
  if atom == realizationAdmissibleAtom then 1 else 0

theorem slotPositiveAtoms_stratum_zero {Pin : Type} :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)) (p : String),
      p ∈ slotPositiveAtoms idx bs → dialecticalStratum p = 0
  | _, [], _, hp => nomatch hp
  | idx, b :: rest, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hpTail
    · have hne : (slotVerifiedAtom idx b.iface.slotId == realizationAdmissibleAtom) = false :=
        beq_false_of_ne (slotVerifiedAtom_ne_admissible idx b.iface.slotId)
      simp [dialecticalStratum, hne]
    · exact slotPositiveAtoms_stratum_zero (idx + 1) rest p hpTail

theorem slotNegativeAtoms_stratum_zero {Pin : Type} :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)) (d : String),
      d ∈ slotNegativeAtoms idx bs → dialecticalStratum d = 0
  | _, [], _, hd => nomatch hd
  | idx, b :: rest, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hdTail
    · have hne : (slotViolationAtom idx b.iface.slotId == realizationAdmissibleAtom) = false :=
        beq_false_of_ne (slotViolationAtom_ne_admissible idx b.iface.slotId)
      simp [dialecticalStratum, hne]
    · exact slotNegativeAtoms_stratum_zero (idx + 1) rest d hdTail

/-- Syntactic stratification of a `Reasons.Program` by `stratum : String → Nat`: every positive
premise has stratum `≤` the rule's conclusion, and every negated defeater has stratum `<` it. -/
def IsAuditStratified (P : Program) (stratum : String → Nat) : Prop :=
  ∀ r ∈ P.rules,
    (∀ p ∈ r.pos, stratum p ≤ stratum r.concl) ∧
    (∀ d ∈ r.neg, stratum d < stratum r.concl)

private theorem auditStage_supported_of_lower_strata {P : Program} {stratum : String → Nat}
    (hstrat : IsAuditStratified P stratum) {k : Nat}
    (ihStrata : ∀ y, stratum y < k → y ∈ (wf P).2 → y ∈ (wf P).1) :
    ∀ n x, stratum x ≤ k → x ∈ stage P (wf P).1 n → x ∈ (wf P).1
  | 0, _, _, hx => by simp [stage] at hx
  | n + 1, x, hxk, hx => by
    rcases mem_T.1 hx with hfact | ⟨r, hr, hfire, rfl⟩
    · exact facts_mem_wf_supported P hfact
    · obtain ⟨hpos_le, hneg_lt⟩ := hstrat r hr
      obtain ⟨hpos_in, hneg_out⟩ := fires_iff.1 hfire
      have hfireU : fires (wf P).2 (gamma P (wf P).2) r = true := by
        refine fires_iff.2 ⟨fun p hp => ?_, fun d hd hdU => ?_⟩
        · have hp_le : stratum p ≤ k := Nat.le_trans (hpos_le p hp) hxk
          have hp1 : p ∈ (wf P).1 :=
            auditStage_supported_of_lower_strata hstrat ihStrata n p hp_le (hpos_in p hp)
          exact (rounds_fix P p).2 hp1
        · have hd_lt : stratum d < k := Nat.lt_of_lt_of_le (hneg_lt d hd) hxk
          exact hneg_out d hd (ihStrata d hd_lt hdU)
      have hT : r.concl ∈ T P (wf P).2 (gamma P (wf P).2) :=
        mem_T.2 (Or.inr ⟨r, hr, hfireU, rfl⟩)
      have hG : r.concl ∈ gamma P (wf P).2 :=
        (gamma_fix P (wf P).2 r.concl).1 hT
      exact (rounds_fix P r.concl).1 hG

/-- Every `IsAuditStratified` program has a 2-valued total well-founded model (`IsTotalWF P`). -/
theorem auditStratified_implies_totalWF {P : Program} {stratum : String → Nat}
    (hstrat : IsAuditStratified P stratum) : IsTotalWF P := by
  have h_le : ∀ k x, stratum x ≤ k → x ∈ (wf P).2 → x ∈ (wf P).1 := by
    intro k
    induction k with
    | zero =>
      intro x hxk hx2
      exact auditStage_supported_of_lower_strata hstrat (fun _ hy => by omega) (bound P) x hxk hx2
    | succ k ih =>
      intro x hxk hx2
      exact auditStage_supported_of_lower_strata hstrat (fun y hy => ih y (by omega)) (bound P) x hxk hx2
  have hSame : Same (wf P).1 (wf P).2 := fun x =>
    ⟨supported_possible P x, fun hx2 => h_le (stratum x) x (Nat.le_refl _) hx2⟩
  exact checkTotalWF_sound ((checkSameSet_iff (wf P).1 (wf P).2).2 hSame)

private theorem auditRule_eq {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) :
    (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.rules =
      [admitRealizationRule bindings] := by
  change [{ admitRealizationRule bindings with neg := (admitRealizationRule bindings).neg ++ [] }] =
    [admitRealizationRule bindings]
  rw [List.append_nil]

/-- Every `buildDialecticalAuditBase` program is syntactically stratified by `dialecticalStratum`. -/
theorem dialecticalAudit_stratified {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) :
    IsAuditStratified
      (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program
      dialecticalStratum := by
  intro r hr
  rw [auditRule_eq, List.mem_singleton] at hr
  subst hr
  have hConcl : dialecticalStratum (admitRealizationRule bindings).concl = 1 := by
    simp [admitRealizationRule, dialecticalStratum]
  rw [hConcl]
  refine ⟨fun p hp => ?_, fun d hd => ?_⟩
  · simp only [admitRealizationRule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hpSlot | (rfl | rfl)
    · rw [slotPositiveAtoms_stratum_zero 0 bindings p hpSlot]; omega
    · decide
    · decide
  · simp only [admitRealizationRule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hdSlot | (rfl | rfl)
    · rw [slotNegativeAtoms_stratum_zero 0 bindings d hdSlot]; omega
    · decide
    · decide

/-- Because `buildDialecticalAuditBase` is stratified, its well-founded model is 2-valued (`IsTotalWF`),
forms the **unique** Gelfond–Lifschitz stable model of the audit program, and is accepted by
`UnifiedEquilibrium.unifiedEquilibriumJudge` at every grade. -/
theorem dialecticalAudit_unique_equilibrium {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) (grade : Nat) :
    let P := (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program
    IsTotalWF P ∧
    IsGLStableModel P (wf P).1 ∧
    unifiedEquilibriumJudge.check grade P (wf P).1 = .ok ∧
    ∀ M, IsGLStableModel P M → Same M (wf P).1 := by
  intro P
  have hStrat := dialecticalAudit_stratified ks I w H bindings proof expectedRoot
  have hTot : IsTotalWF P := auditStratified_implies_totalWF hStrat
  obtain ⟨hGL, hUniq⟩ := totalWF_unique_glStable hTot
  have hJudge : unifiedEquilibriumJudge.check grade P (wf P).1 = .ok := by
    show (if checkGLStable P (wf P).1 then Judge.Verdict.ok else _) = Judge.Verdict.ok
    rw [checkGLStable_complete hGL]
    rfl
  exact ⟨hTot, hGL, hJudge, hUniq⟩

/-! ## 3. Constructive Pinpointing Helpers & Support/Defeat Lemmas -/

theorem buildSlotObservations_names_no_admissible {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)),
      realizationAdmissibleAtom ∉ (buildSlotObservationsAux ks I w idx bs).map (·.name)
  | _, [] => by simp [buildSlotObservationsAux]
  | idx, b :: rest => by
    simp only [buildSlotObservationsAux, List.map_cons, List.mem_cons]
    rintro (hHead | hTail)
    · cases hAud : auditCandidateLocal ks I w b.iface b.cand <;> simp only [hAud] at hHead
      · exact slotVerifiedAtom_ne_admissible idx b.iface.slotId hHead.symm
      · exact slotViolationAtom_ne_admissible idx b.iface.slotId hHead.symm
    · exact buildSlotObservations_names_no_admissible ks I w (idx + 1) rest hTail

theorem admissible_not_in_audit_facts {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) :
    realizationAdmissibleAtom ∉
      (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts := by
  simp only [buildDialecticalAuditBase, Base.held, List.filter_nil, List.append_nil,
    List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro (hSlot | hGlue | hRec)
  · exact buildSlotObservations_names_no_admissible ks I w 0 bindings hSlot
  · split at hGlue
    · exact gluingVerified_ne_admissible hGlue.symm
    · exact gluingConflict_ne_admissible hGlue.symm
  · split at hRec
    · exact receiptVerified_ne_admissible hRec.symm
    · exact receiptInvalid_ne_admissible hRec.symm

/-- Whenever any defeater atom `d ∈ (admitRealizationRule bindings).neg` is observed in
`bAudit.program.facts`, `d` is `.supported` and `realizationAdmissibleAtom` is `.unsupported`. -/
theorem defeat_observation_forces_admissible_unsupported {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256)
    {d : String}
    (hdFact : d ∈ (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts)
    (hdNeg : d ∈ (admitRealizationRule bindings).neg) :
    let bAudit := buildDialecticalAuditBase ks I w H bindings proof expectedRoot
    status bAudit d = .supported ∧
    status bAudit realizationAdmissibleAtom = .unsupported := by
  intro bAudit
  have hdSup : status bAudit d = .supported := (supported_iff bAudit d).2 (Or.inl hdFact)
  have hdMem1 : d ∈ (judge bAudit).1 := (status_supported_iff bAudit d).1 hdSup
  refine ⟨hdSup, ?_⟩
  rw [status_unsupported_iff, judge]
  intro hMem2
  rcases mem_gamma.1 hMem2 with hFactAdm | ⟨r, hr, _, _, hNoNeg⟩
  · exact admissible_not_in_audit_facts ks I w H bindings proof expectedRoot hFactAdm
  · change r ∈ (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.rules at hr
    rw [auditRule_eq, List.mem_singleton] at hr
    subst hr
    exact hNoNeg d hdNeg hdMem1

/-- Find the first bound slot failing `auditCandidateLocal`, returning `(idx, boundSlot, failure)`. -/
def findFirstFailingSlotAux {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    Nat → List (BoundSlot Pin) → Option (Nat × BoundSlot Pin × LocalSlotFailure)
  | _, [] => none
  | idx, b :: rest =>
    match auditCandidateLocal ks I w b.iface b.cand with
    | some failure => some (idx, b, failure)
    | none => findFirstFailingSlotAux ks I w (idx + 1) rest

theorem findFirstFailingSlotAux_none_iff {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)),
      findFirstFailingSlotAux ks I w idx bs = none ↔
        ∀ b ∈ bs, checkCandidateLocal ks I w b.iface b.cand = true
  | _, [] => by simp [findFirstFailingSlotAux]
  | idx, b :: rest => by
    simp only [findFirstFailingSlotAux]
    cases hAud : auditCandidateLocal ks I w b.iface b.cand with
    | some failure =>
      simp only [reduceCtorEq, false_iff]
      intro hall
      have hb := hall b List.mem_cons_self
      simp [checkCandidateLocal, hAud] at hb
    | none =>
      rw [findFirstFailingSlotAux_none_iff ks I w (idx + 1) rest]
      constructor
      · intro hRest b' hb'
        rcases List.mem_cons.1 hb' with rfl | hb'Tail
        · simp [checkCandidateLocal, hAud]
        · exact hRest b' hb'Tail
      · intro hall b' hb'Tail
        exact hall b' (List.mem_cons_of_mem _ hb'Tail)

private theorem findFirstFailingSlotAux_eq_some {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin))
      {outIdx : Nat} {b : BoundSlot Pin} {failure : LocalSlotFailure},
      findFirstFailingSlotAux ks I w idx bs = some (outIdx, b, failure) →
      idx ≤ outIdx ∧
      bs[outIdx - idx]? = some b ∧
      b ∈ bs ∧
      auditCandidateLocal ks I w b.iface b.cand = some failure ∧
      checkCandidateLocal ks I w b.iface b.cand = false ∧
      slotViolationAtom outIdx b.iface.slotId ∈
        (buildSlotObservationsAux ks I w idx bs).map (·.name) ∧
      slotViolationAtom outIdx b.iface.slotId ∈ slotNegativeAtoms idx bs
  | _, [], _, _, _, h => by simp [findFirstFailingSlotAux] at h
  | idx, hd :: rest, outIdx, b, failure, h => by
    simp only [findFirstFailingSlotAux] at h
    cases hAud : auditCandidateLocal ks I w hd.iface hd.cand <;> rw [hAud] at h
    · obtain ⟨hLe, hGet, hMem, hFail, hCheck, hObs, hNeg⟩ :=
        findFirstFailingSlotAux_eq_some ks I w (idx + 1) rest h
      have hSub : outIdx - idx = (outIdx - (idx + 1)) + 1 := by omega
      refine ⟨by omega, ?_, List.mem_cons_of_mem _ hMem, hFail, hCheck, ?_, ?_⟩
      · rw [hSub, List.getElem?_cons_succ]
        exact hGet
      · simp only [buildSlotObservationsAux, hAud, List.map_cons, List.mem_cons]
        exact Or.inr hObs
      · simp only [slotNegativeAtoms, List.mem_cons]
        exact Or.inr hNeg
    · rename_i failHd
      cases h
      refine ⟨Nat.le_refl _, by simp, List.mem_cons_self, hAud,
        by simp [checkCandidateLocal, hAud], ?_, ?_⟩
      · simp [buildSlotObservationsAux, hAud]
      · simp [slotNegativeAtoms]

/-- Find a concrete pair of bound slots violating `gluingCompatible` against `b`. -/
def findIncompatiblePeer {Pin : Type} (b : BoundSlot Pin) :
    List (BoundSlot Pin) → Option (BoundSlot Pin)
  | [] => none
  | b' :: rest =>
    if gluingCompatible b.iface b.cand b'.iface b'.cand then
      findIncompatiblePeer b rest
    else
      some b'

/-- Find the first incompatible pair `(b₁, b₂)` when `allPairsGluingCompatible` fails. -/
def findFirstGluingConflict {Pin : Type} :
    List (BoundSlot Pin) → Option (BoundSlot Pin × BoundSlot Pin)
  | [] => none
  | b :: rest =>
    match findIncompatiblePeer b rest with
    | some b' => some (b, b')
    | none => findFirstGluingConflict rest

theorem findIncompatiblePeer_none_iff {Pin : Type} (b : BoundSlot Pin) :
    ∀ (bs : List (BoundSlot Pin)),
      findIncompatiblePeer b bs = none ↔
        ∀ b' ∈ bs, gluingCompatible b.iface b.cand b'.iface b'.cand = true
  | [] => by simp [findIncompatiblePeer]
  | b' :: rest => by
    simp only [findIncompatiblePeer]
    by_cases hGlue : gluingCompatible b.iface b.cand b'.iface b'.cand = true
    · simp only [hGlue, ↓reduceIte, findIncompatiblePeer_none_iff b rest, List.mem_cons,
        forall_eq_or_imp, true_and]
    · simp only [Bool.not_eq_true] at hGlue
      simp only [hGlue, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h
        cases h
      · intro hall
        have h0 := hall b' List.mem_cons_self
        rw [hGlue] at h0
        cases h0

private theorem findIncompatiblePeer_eq_some {Pin : Type} (b : BoundSlot Pin) :
    ∀ (bs : List (BoundSlot Pin)) {b' : BoundSlot Pin},
      findIncompatiblePeer b bs = some b' →
      b' ∈ bs ∧ gluingCompatible b.iface b.cand b'.iface b'.cand = false
  | [], _, h => by simp [findIncompatiblePeer] at h
  | hd :: rest, b', h => by
    simp only [findIncompatiblePeer] at h
    by_cases hGlue : gluingCompatible b.iface b.cand hd.iface hd.cand = true
    · simp only [hGlue, ↓reduceIte] at h
      obtain ⟨hm, hf⟩ := findIncompatiblePeer_eq_some b rest h
      exact ⟨List.mem_cons_of_mem _ hm, hf⟩
    · simp only [Bool.not_eq_true] at hGlue
      simp only [hGlue, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, hGlue⟩

theorem findFirstGluingConflict_none_iff {Pin : Type} :
    ∀ (bs : List (BoundSlot Pin)),
      findFirstGluingConflict bs = none ↔ allPairsGluingCompatible bs = true
  | [] => by simp [findFirstGluingConflict, allPairsGluingCompatible]
  | b :: rest => by
    simp only [findFirstGluingConflict, allPairsGluingCompatible]
    cases hPeer : findIncompatiblePeer b rest with
    | some b' =>
      obtain ⟨hm, hf⟩ := findIncompatiblePeer_eq_some b rest hPeer
      simp only [reduceCtorEq, false_iff, Bool.and_eq_true, compatWithAll, List.all_eq_true, not_and]
      intro hHead
      have := hHead b' hm
      rw [hf] at this
      cases this
    | none =>
      have hFwd := (findIncompatiblePeer_none_iff b rest).1 hPeer
      have hHead : compatWithAll b rest = true := List.all_eq_true.2 hFwd
      rw [findFirstGluingConflict_none_iff rest]
      simp [hHead]

private theorem findFirstGluingConflict_eq_some {Pin : Type} :
    ∀ (bs : List (BoundSlot Pin)) {b₁ b₂ : BoundSlot Pin},
      findFirstGluingConflict bs = some (b₁, b₂) →
      b₁ ∈ bs ∧ b₂ ∈ bs ∧ gluingCompatible b₁.iface b₁.cand b₂.iface b₂.cand = false
  | [], _, _, h => by simp [findFirstGluingConflict] at h
  | b :: rest, b₁, b₂, h => by
    simp only [findFirstGluingConflict] at h
    cases hPeer : findIncompatiblePeer b rest <;> rw [hPeer] at h
    · obtain ⟨hm1, hm2, hf⟩ := findFirstGluingConflict_eq_some rest h
      exact ⟨List.mem_cons_of_mem _ hm1, List.mem_cons_of_mem _ hm2, hf⟩
    · rename_i b'
      cases h
      obtain ⟨hm, hf⟩ := findIncompatiblePeer_eq_some b rest hPeer
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hm, hf⟩

/-! ### All-Green Support Lemma for `realizationAdmissibleAtom` -/

theorem slotPositiveAtoms_in_obs_of_all_ok {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)),
      (∀ b ∈ bs, checkCandidateLocal ks I w b.iface b.cand = true) →
      ∀ p ∈ slotPositiveAtoms idx bs,
        p ∈ (buildSlotObservationsAux ks I w idx bs).map (·.name)
  | _, [], _, _, hp => nomatch hp
  | idx, b :: rest, hall, p, hp => by
    have hbOk := hall b List.mem_cons_self
    have hAud : auditCandidateLocal ks I w b.iface b.cand = none :=
      Option.isNone_iff_eq_none.1 hbOk
    simp only [slotPositiveAtoms, List.mem_cons] at hp
    simp only [buildSlotObservationsAux, hAud, List.map_cons, List.mem_cons]
    rcases hp with rfl | hpTail
    · exact Or.inl rfl
    · exact Or.inr (slotPositiveAtoms_in_obs_of_all_ok ks I w (idx + 1) rest
        (fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')) p hpTail)

theorem no_slotNegative_in_obs_of_all_ok {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)),
      (∀ b ∈ bs, checkCandidateLocal ks I w b.iface b.cand = true) →
      ∀ (j : Nat) (s : String),
        slotViolationAtom j s ∉ (buildSlotObservationsAux ks I w idx bs).map (·.name)
  | _, [], _, _, _ => by simp [buildSlotObservationsAux]
  | idx, b :: rest, hall, j, s => by
    have hbOk := hall b List.mem_cons_self
    have hAud : auditCandidateLocal ks I w b.iface b.cand = none :=
      Option.isNone_iff_eq_none.1 hbOk
    simp only [buildSlotObservationsAux, hAud, List.map_cons, List.mem_cons]
    rintro (hEq | hTail)
    · exact slotViolationAtom_ne_slotVerified j idx s b.iface.slotId hEq
    · exact no_slotNegative_in_obs_of_all_ok ks I w (idx + 1) rest
        (fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')) j s hTail

theorem slotNegative_mem_shape {Pin : Type} :
    ∀ (idx : Nat) (bs : List (BoundSlot Pin)) {d : String},
      d ∈ slotNegativeAtoms idx bs → ∃ j s, d = slotViolationAtom j s
  | _, [], _, hd => nomatch hd
  | idx, b :: rest, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hdTail
    · exact ⟨idx, b.iface.slotId, rfl⟩
    · exact slotNegative_mem_shape (idx + 1) rest hdTail

theorem all_checks_support_admissible {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256)
    (hSlots : ∀ b ∈ bindings, checkCandidateLocal ks I w b.iface b.cand = true)
    (hGraph : slotGraphWellFormed (bindings.map (·.iface)) = true)
    (hGlue : allPairsGluingCompatible bindings = true)
    (hRec : verifyNonEmptyBlindedMultiproof256 H proof expectedRoot = true) :
    status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
      realizationAdmissibleAtom = .supported := by
  rw [supported_iff]
  refine Or.inr ⟨admitRealizationRule bindings, ?_, rfl, ?_, ?_⟩
  · simp [buildDialecticalAuditBase, Base.rule]
  · intro p hp
    rw [supported_iff]
    left
    simp only [buildDialecticalAuditBase, hGraph, hGlue, Bool.and_self, hRec,
      ↓reduceIte, Base.held, List.filter_nil, List.append_nil, List.map_append, List.mem_append,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    simp only [admitRealizationRule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hpSlot | (rfl | rfl)
    · exact Or.inl (slotPositiveAtoms_in_obs_of_all_ok ks I w 0 bindings hSlots p hpSlot)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro d hd
    rw [status_unsupported_iff, judge]
    intro hdMem
    rcases mem_gamma.1 hdMem with hdFact | ⟨r, hr, hConcl, _, _⟩
    · simp only [buildDialecticalAuditBase, hGraph, hGlue, Bool.and_self,
        hRec, ↓reduceIte, Base.held, List.filter_nil, List.append_nil, List.map_append,
        List.mem_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hdFact
      simp only [admitRealizationRule, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hd
      rcases hd with hdSlot | (rfl | rfl)
      · obtain ⟨j, s, rfl⟩ := slotNegative_mem_shape 0 bindings hdSlot
        rcases hdFact with hInSlotObs | hEqGlue | hEqRec
        · exact no_slotNegative_in_obs_of_all_ok ks I w 0 bindings hSlots j s hInSlotObs
        · have h0 := congrArg (fun str => str.toList.head?) hEqGlue
          simp [slotViolationAtom, gluingVerifiedAtom, String.toList_append] at h0
        · have h0 := congrArg (fun str => str.toList.head?) hEqRec
          simp [slotViolationAtom, receiptVerifiedAtom, String.toList_append] at h0
      · rcases hdFact with hInSlotObs | hEqGlue | hEqRec
        · have : ∀ idx (bs : List (BoundSlot Pin)),
              gluingConflictAtom ∉ (buildSlotObservationsAux ks I w idx bs).map (·.name) := by
            intro idx bs
            induction bs generalizing idx with
            | nil => simp [buildSlotObservationsAux]
            | cons hdB tlB ih =>
              simp only [buildSlotObservationsAux, List.map_cons, List.mem_cons]
              rintro (h1 | h2)
              · cases hAud : auditCandidateLocal ks I w hdB.iface hdB.cand <;>
                  { simp only [hAud] at h1
                    have h0 := congrArg (fun str => str.toList.head?) h1
                    simp [slotVerifiedAtom, slotViolationAtom, gluingConflictAtom,
                      String.toList_append] at h0 }
              · exact ih (idx + 1) h2
          exact this 0 bindings hInSlotObs
        · exact absurd hEqGlue (by decide)
        · exact absurd hEqRec (by decide)
      · rcases hdFact with hInSlotObs | hEqGlue | hEqRec
        · have : ∀ idx (bs : List (BoundSlot Pin)),
              receiptInvalidAtom ∉ (buildSlotObservationsAux ks I w idx bs).map (·.name) := by
            intro idx bs
            induction bs generalizing idx with
            | nil => simp [buildSlotObservationsAux]
            | cons hdB tlB ih =>
              simp only [buildSlotObservationsAux, List.map_cons, List.mem_cons]
              rintro (h1 | h2)
              · cases hAud : auditCandidateLocal ks I w hdB.iface hdB.cand <;>
                  { simp only [hAud] at h1
                    have h0 := congrArg (fun str => str.toList.head?) h1
                    simp [slotVerifiedAtom, slotViolationAtom, receiptInvalidAtom,
                      String.toList_append] at h0 }
              · exact ih (idx + 1) h2
          exact this 0 bindings hInSlotObs
        · exact absurd hEqGlue (by decide)
        · exact absurd hEqRec (by decide)
    · simp only [buildDialecticalAuditBase, Base.rule, List.filter_nil,
        List.map_nil, List.append_nil, List.map_singleton, List.mem_singleton] at hr
      subst hr
      simp only [admitRealizationRule, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hd hConcl
      rcases hd with hdSlot | (rfl | rfl)
      · obtain ⟨j, s, rfl⟩ := slotNegative_mem_shape 0 bindings hdSlot
        exact slotViolationAtom_ne_admissible j s hConcl.symm
      · exact gluingConflict_ne_admissible hConcl.symm
      · exact receiptInvalid_ne_admissible hConcl.symm

/-! ## 4. Constructive `PSum` Dialectical Blame Extractor (`0 Classical.choice`) -/

/-- Certified admissibility summary produced when all slot, gluing, receipt, and policy checks hold. -/
structure AdmissibleRealizationCert where
  supportedAtoms : List String
  slotCount : Nat
  totalDeclaredBudget : Nat
  deriving DecidableEq, Repr

/-- Constructive dialectical blame certificate pinpointing the exact offending slot, malformed
slot dependency graph, gluing pair, receipt multiproof, or defeated/cyclic governance policy target. -/
inductive DialecticalBlameCert where
  | slotContractViolation
      (slotIndex : Nat)
      (slotId : String)
      (candId : String)
      (failure : LocalSlotFailure)
      (defeatAtom : String)
      (blocker : BlockerChain)
  | slotGraphMalformed
      (slotIds : List String)
      (defeatAtom : String)
      (blocker : BlockerChain)
  | gluingIncompatiblePair
      (slotA : String) (candA : String)
      (slotB : String) (candB : String)
      (defeatAtom : String)
      (blocker : BlockerChain)
  | invalidReceiptMultiproof
      (queriedCount : Nat)
      (treeSize : Nat)
      (defeatAtom : String)
      (blocker : BlockerChain)
  | policyJustificationDefeated
      (targetAtom : String)
      (targetStatus : Status)
      (blocker : BlockerChain)
  deriving DecidableEq, Repr

/-- Justification equivalence on `buildDialecticalAuditState`: `justify realizationAdmissibleAtom`
succeeds iff `realizationAdmissibleAtom` is `.supported` in `buildDialecticalAuditBase`. -/
theorem auditState_justify_admissible_iff {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256) :
    (buildDialecticalAuditState ks I w H bindings proof expectedRoot).justify
      realizationAdmissibleAtom = .ok () ↔
    status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
      realizationAdmissibleAtom = .supported := by
  rw [justify_ok_iff,
      State.status_eq (buildDialecticalAuditState_consistent ks I w H bindings proof expectedRoot)]
  rfl

/-- **Constructive `Type`-Valued Dialectical Blame Extractor (`diagnoseDialecticalBlame`)**:
Zero `Classical.choice`. Evaluates local slot contracts (`Kind` C4 lineage, `Intention` / `SupportSheaf`
usability, Clairvoyant `Equiv.Cost` budget), slot-graph dependency closure (`slotGraphWellFormed`),
pairwise gluing, non-empty 256-bit salted blinded Merkle receipt multiproof verification, and optional
governance `Reasons.Base` justification (including cyclic defeat graphs via `traceUnsupportedRoot`). -/
@[expose] def diagnoseDialecticalBlame {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (H : Hash) (bindings : List (BoundSlot Pin))
    (proof : BlindedMultiproof256) (expectedRoot : Digest256)
    (policyBase : Base := {}) (policyTarget : Option String := none) :
    PSum AdmissibleRealizationCert DialecticalBlameCert :=
  let sAudit := buildDialecticalAuditState ks I w H bindings proof expectedRoot
  match findFirstFailingSlotAux ks I w 0 bindings with
  | some (idx, b, failure) =>
    .inr (.slotContractViolation idx b.iface.slotId b.cand.candId failure
      (slotViolationAtom idx b.iface.slotId)
      (traceUnsupportedRoot sAudit realizationAdmissibleAtom))
  | none =>
    if !slotGraphWellFormed (bindings.map (·.iface)) then
      .inr (.slotGraphMalformed (bindings.map (·.iface.slotId))
        gluingConflictAtom
        (traceUnsupportedRoot sAudit realizationAdmissibleAtom))
    else
      match findFirstGluingConflict bindings with
      | some (b₁, b₂) =>
        .inr (.gluingIncompatiblePair b₁.iface.slotId b₁.cand.candId b₂.iface.slotId b₂.cand.candId
          gluingConflictAtom
          (traceUnsupportedRoot sAudit realizationAdmissibleAtom))
      | none =>
        if verifyNonEmptyBlindedMultiproof256 H proof expectedRoot then
          match policyTarget with
          | none =>
            .inl { supportedAtoms := sAudit.kept.1
                   slotCount := bindings.length
                   totalDeclaredBudget := totalDeclaredSlotBudget bindings }
          | some target =>
            let sPol : State := { base := policyBase, kept := judge policyBase }
            if sPol.status target == .supported then
              .inl { supportedAtoms := sAudit.kept.1
                     slotCount := bindings.length
                     totalDeclaredBudget := totalDeclaredSlotBudget bindings }
            else
              .inr (.policyJustificationDefeated target (sPol.status target)
                (traceUnsupportedRoot sPol target))
        else
          .inr (.invalidReceiptMultiproof proof.queriedIndices.length proof.treeSize
            receiptInvalidAtom
            (traceUnsupportedRoot sAudit realizationAdmissibleAtom))

/-- Inhabitedness witness for `diagnoseDialecticalBlame` (`.inl` certified realization branch). -/
theorem diagnoseDialecticalBlame_inl_inhabited :
    let ks : Obend.Kind.Kinds :=
      ⟨[{ name := "Codec", version := 1, layout := [], init := .natural 0,
          law := .boolean true, parents := [] }]⟩
    let I₀ : Obend.Intention Unit String String Unit String :=
      { ref := id
        supports := fun _ => [()]
        holds := fun _ _ => true
        resolve := fun _ r => .ok r
        resolve_ref := fun _ _ _ h => by cases h; rfl
        resolve_holds := fun _ _ _ _ _ _ => rfl }
    let iface : OpenSlotInterface :=
      { slotId := "s0", expectedKind := "Codec", intentionRef := "codec@^1",
        budget := ⟨2⟩, fuel := 1, specTerm := .nat 7 }
    let cand : SlotCandidate String :=
      { candId := "c0", slotId := "s0", kindPin := ⟨"Codec", 1, []⟩,
        intentionPin := "codec@^1", implTerm := .nat 7 }
    let proof : BlindedMultiproof256 :=
      { treeSize := 1, queriedIndices := [0], tree := .openedLeaf 0 0#256 [0x42] }
    let root := saltedTreeRoot256 cshakeMultiproofHash [⟨0#256, [0x42]⟩]
    ∃ cert, diagnoseDialecticalBlame ks I₀ () cshakeMultiproofHash
      [⟨iface, cand⟩] proof root = .inl cert := by
  intro ks I₀ iface cand proof root
  have hVer := verifyBlindedMultiproof256_inhabited cshakeMultiproofHash
  have hAudOk : auditCandidateLocal ks I₀ () iface cand = none := by
    decide
  have hGraphOk : slotGraphWellFormed [iface] = true := by
    decide
  have hEq :
      diagnoseDialecticalBlame ks I₀ () cshakeMultiproofHash [⟨iface, cand⟩] proof root =
        .inl ⟨(buildDialecticalAuditState ks I₀ () cshakeMultiproofHash [⟨iface, cand⟩] proof root).kept.1,
          1, totalDeclaredSlotBudget [⟨iface, cand⟩]⟩ := by
    unfold diagnoseDialecticalBlame verifyNonEmptyBlindedMultiproof256
    simp [findFirstFailingSlotAux, hAudOk, hGraphOk, findFirstGluingConflict, findIncompatiblePeer,
      proof, root, hVer]
  exact ⟨_, hEq⟩

/-- Inhabitedness witness for `diagnoseDialecticalBlame` (`.inr` blame extraction branch on Clairvoyant
budget overrun: `implTerm = (λ x. x) ((λ y. y) 7)` takes 3 Clairvoyant steps against budget `2`!). -/
theorem diagnoseDialecticalBlame_inr_inhabited :
    let ks : Obend.Kind.Kinds :=
      ⟨[{ name := "Codec", version := 1, layout := [], init := .natural 0,
          law := .boolean true, parents := [] }]⟩
    let I₀ : Obend.Intention Unit String String Unit String :=
      { ref := id
        supports := fun _ => [()]
        holds := fun _ _ => true
        resolve := fun _ r => .ok r
        resolve_ref := fun _ _ _ h => by cases h; rfl
        resolve_holds := fun _ _ _ _ _ _ => rfl }
    let iface : OpenSlotInterface :=
      { slotId := "s0", expectedKind := "Codec", intentionRef := "codec@^1",
        budget := ⟨2⟩, fuel := 4, specTerm := .nat 7 }
    let overBudgetCand : SlotCandidate String :=
      { candId := "c_expensive", slotId := "s0", kindPin := ⟨"Codec", 1, []⟩,
        intentionPin := "codec@^1",
        implTerm := .app (.lam (.bound 0)) (.app (.lam (.bound 0)) (.nat 7)) }
    let proof : BlindedMultiproof256 :=
      { treeSize := 1, queriedIndices := [0], tree := .openedLeaf 0 0#256 [0x42] }
    let root := saltedTreeRoot256 cshakeMultiproofHash [⟨0#256, [0x42]⟩]
    ∃ blame, diagnoseDialecticalBlame ks I₀ () cshakeMultiproofHash
      [⟨iface, overBudgetCand⟩] proof root = .inr blame ∧
      match blame with
      | .slotContractViolation 0 "s0" "c_expensive" (.costOrObservationContractFailed 2) _ _ => True
      | _ => False := by
  intro ks I₀ iface overBudgetCand proof root
  have hAudFail :
      auditCandidateLocal ks I₀ () iface overBudgetCand =
        some (.costOrObservationContractFailed 2) := by
    simp (config := { decide := true }) [auditCandidateLocal, Obend.Equiv.checkSlotCostContract,
      Obend.Equiv.sameObservedLiteral, ks, I₀, iface, overBudgetCand]
  have hEq :
      diagnoseDialecticalBlame ks I₀ () cshakeMultiproofHash [⟨iface, overBudgetCand⟩] proof root =
        .inr (.slotContractViolation 0 "s0" "c_expensive" (.costOrObservationContractFailed 2)
          (slotViolationAtom 0 "s0")
          (traceUnsupportedRoot
            (buildDialecticalAuditState ks I₀ () cshakeMultiproofHash [⟨iface, overBudgetCand⟩] proof root)
            realizationAdmissibleAtom)) := by
    unfold diagnoseDialecticalBlame
    simp [findFirstFailingSlotAux, hAudFail, iface, overBudgetCand]
  exact ⟨_, hEq, trivial⟩

/-- **Admissibility Soundness (`diagnoseDialecticalBlame_inl_sound`)**:
Whenever `diagnoseDialecticalBlame` returns `.inl cert`:
1. Every bound slot passes `checkCandidateLocal`, certifying live C4 `Kind` precedence, `SupportSheaf`
   usability, and Clairvoyant `Equiv.Cost.CostAtMost b.cand.implTerm b.iface.budget.grade`.
2. `realizerGraphValid bindings = true` (pairwise-distinct `slotId`s, closed `peerDeps`, self-edges,
   and `allPairsGluingCompatible bindings = true`).
3. `proof.queriedIndices ≠ []` and `verifyBlindedMultiproof256 H proof expectedRoot = true`.
4. `realizationAdmissibleAtom` is `.supported` in `buildDialecticalAuditBase`, whose well-founded
   model is accepted as the unique GL equilibrium by `unifiedEquilibriumJudge`.
5. `cert.slotCount = bindings.length`, `cert.totalDeclaredBudget = totalDeclaredSlotBudget bindings`,
   and any requested governance `policyTarget` is `.supported` in `policyBase`. -/
theorem diagnoseDialecticalBlame_inl_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {H : Hash} {bindings : List (BoundSlot Pin)}
    {proof : BlindedMultiproof256} {expectedRoot : Digest256}
    {policyBase : Base} {policyTarget : Option String}
    {cert : AdmissibleRealizationCert}
    (h : diagnoseDialecticalBlame ks I w H bindings proof expectedRoot policyBase policyTarget = .inl cert) :
    let bAudit := buildDialecticalAuditBase ks I w H bindings proof expectedRoot
    (∀ b ∈ bindings, checkCandidateLocal ks I w b.iface b.cand = true ∧
      Obend.Equiv.CostAtMost b.cand.implTerm b.iface.budget.grade) ∧
    realizerGraphValid bindings = true ∧
    allPairsGluingCompatible bindings = true ∧
    proof.queriedIndices ≠ [] ∧
    verifyBlindedMultiproof256 H proof expectedRoot = true ∧
    status bAudit realizationAdmissibleAtom = .supported ∧
    unifiedEquilibriumJudge.check 0 bAudit.program (wf bAudit.program).1 = .ok ∧
    cert.slotCount = bindings.length ∧
    cert.totalDeclaredBudget = totalDeclaredSlotBudget bindings ∧
    (∀ t, policyTarget = some t → status policyBase t = .supported) := by
  unfold diagnoseDialecticalBlame at h
  cases hSlot : findFirstFailingSlotAux ks I w 0 bindings <;> rw [hSlot] at h
  · have hAllLocal := (findFirstFailingSlotAux_none_iff ks I w 0 bindings).1 hSlot
    by_cases hBadGraph : (!slotGraphWellFormed (bindings.map (·.iface))) = true
    · simp [hBadGraph] at h
    · simp only [hBadGraph, Bool.false_eq_true, ↓reduceIte] at h
      have hGraph : slotGraphWellFormed (bindings.map (·.iface)) = true := by
        cases hg : slotGraphWellFormed (bindings.map (·.iface))
        · simp [hg] at hBadGraph
        · rfl
      cases hGlueOpt : findFirstGluingConflict bindings <;> rw [hGlueOpt] at h
      · have hAllGlue := (findFirstGluingConflict_none_iff bindings).1 hGlueOpt
        have hSelfAll :
            (bindings.all fun b => directedGluingCompatible b.iface b.cand b.iface b.cand) = true :=
          List.all_eq_true.2 fun b hb => (checkCandidateLocal_self_gluing_sound (hAllLocal b hb)).2
        have hFullGraph : realizerGraphValid bindings = true := by
          simp [realizerGraphValid, hGraph, hSelfAll, hAllGlue]
        by_cases hRec : verifyNonEmptyBlindedMultiproof256 H proof expectedRoot = true
        · simp only [hRec, ↓reduceIte] at h
          have hRecParts : proof.queriedIndices ≠ [] ∧ verifyBlindedMultiproof256 H proof expectedRoot = true := by
            unfold verifyNonEmptyBlindedMultiproof256 at hRec
            simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hRec
            exact hRec
          have hSupAdm := all_checks_support_admissible ks I w H bindings proof expectedRoot
            hAllLocal hGraph hAllGlue hRec
          have hEqJudge := (dialecticalAudit_unique_equilibrium ks I w H bindings proof expectedRoot 0).2.2.1
          have hSlotsAndCost :
              ∀ b ∈ bindings, checkCandidateLocal ks I w b.iface b.cand = true ∧
                Obend.Equiv.CostAtMost b.cand.implTerm b.iface.budget.grade := by
            intro b hb
            have hLoc := hAllLocal b hb
            obtain ⟨_, _, _, hCost⟩ := (checkCandidateLocal_sound hLoc).2.2.2.2.2.2
            exact ⟨hLoc, hCost.2.2.2⟩
          cases policyTarget with
          | none =>
            simp only [PSum.inl.injEq] at h
            subst h
            exact ⟨hSlotsAndCost, hFullGraph, hAllGlue, hRecParts.1, hRecParts.2, hSupAdm, hEqJudge,
              rfl, rfl, fun _ ht => nomatch ht⟩
          | some t =>
            dsimp only at h
            by_cases hPol : ({ base := policyBase, kept := judge policyBase } : State).status t = .supported
            · have hBeq : (({ base := policyBase, kept := judge policyBase } : State).status t == .supported) = true :=
                beq_iff_eq.2 hPol
              simp only [hBeq, ↓reduceIte, PSum.inl.injEq] at h
              subst h
              refine ⟨hSlotsAndCost, hFullGraph, hAllGlue, hRecParts.1, hRecParts.2, hSupAdm, hEqJudge,
                rfl, rfl, fun t' ht' => ?_⟩
              cases ht'
              exact hPol
            · have hne : (({ base := policyBase, kept := judge policyBase } : State).status t == .supported) = false :=
                beq_false_of_ne hPol
              simp [hne] at h
        · simp [hRec] at h
      · cases h
  · cases h

/-- **Dialectical Blame Soundness (`diagnoseDialecticalBlame_inr_sound`)**:
Whenever `diagnoseDialecticalBlame` returns `.inr blame`, the certificate constructively pinpoints
a genuine contract violation (at exact index `bindings[slotIndex]? = some b`), malformed slot
dependency graph, gluing conflict, invalid/empty 256-bit multiproof, or defeated/cyclic governance
policy target, and in the first four cases `realizationAdmissibleAtom` is `.unsupported` in
`buildDialecticalAuditBase` with its defeater atom `.supported`. -/
theorem diagnoseDialecticalBlame_inr_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {H : Hash} {bindings : List (BoundSlot Pin)}
    {proof : BlindedMultiproof256} {expectedRoot : Digest256}
    {policyBase : Base} {policyTarget : Option String}
    {blame : DialecticalBlameCert}
    (h : diagnoseDialecticalBlame ks I w H bindings proof expectedRoot policyBase policyTarget = .inr blame) :
    let bAudit := buildDialecticalAuditBase ks I w H bindings proof expectedRoot
    match blame with
    | .slotContractViolation slotIndex slotId candId failure defeatAtom blocker =>
      (∃ b, bindings[slotIndex]? = some b ∧ b ∈ bindings ∧
        b.iface.slotId = slotId ∧ b.cand.candId = candId ∧
        defeatAtom = slotViolationAtom slotIndex slotId ∧
        auditCandidateLocal ks I w b.iface b.cand = some failure ∧
        checkCandidateLocal ks I w b.iface b.cand = false) ∧
      status bAudit defeatAtom = .supported ∧
      status bAudit realizationAdmissibleAtom = .unsupported ∧
      blocker ≠ .alreadySupported
    | .slotGraphMalformed slotIds defeatAtom blocker =>
      slotIds = bindings.map (·.iface.slotId) ∧
      slotGraphWellFormed (bindings.map (·.iface)) = false ∧
      status bAudit defeatAtom = .supported ∧
      status bAudit realizationAdmissibleAtom = .unsupported ∧
      blocker ≠ .alreadySupported
    | .gluingIncompatiblePair slotA candA slotB candB defeatAtom blocker =>
      (∃ b₁ ∈ bindings, ∃ b₂ ∈ bindings,
        b₁.iface.slotId = slotA ∧ b₁.cand.candId = candA ∧
        b₂.iface.slotId = slotB ∧ b₂.cand.candId = candB ∧
        gluingCompatible b₁.iface b₁.cand b₂.iface b₂.cand = false) ∧
      status bAudit defeatAtom = .supported ∧
      status bAudit realizationAdmissibleAtom = .unsupported ∧
      blocker ≠ .alreadySupported
    | .invalidReceiptMultiproof _ _ defeatAtom blocker =>
      verifyNonEmptyBlindedMultiproof256 H proof expectedRoot = false ∧
      status bAudit defeatAtom = .supported ∧
      status bAudit realizationAdmissibleAtom = .unsupported ∧
      blocker ≠ .alreadySupported
    | .policyJustificationDefeated targetAtom st blocker =>
      policyTarget = some targetAtom ∧
      status policyBase targetAtom = st ∧
      st ≠ .supported ∧
      blocker ≠ .alreadySupported := by
  unfold diagnoseDialecticalBlame at h
  cases hSlot : findFirstFailingSlotAux ks I w 0 bindings <;> rw [hSlot] at h
  · by_cases hBadGraph : (!slotGraphWellFormed (bindings.map (·.iface))) = true
    · simp only [hBadGraph, ↓reduceIte, PSum.inr.injEq] at h
      subst h
      have hGraphFalse : slotGraphWellFormed (bindings.map (·.iface)) = false := by
        cases hg : slotGraphWellFormed (bindings.map (·.iface))
        · rfl
        · simp [hg] at hBadGraph
      have hdFact :
          gluingConflictAtom ∈
            (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts := by
        simp [buildDialecticalAuditBase, hGraphFalse]
      have hdNeg : gluingConflictAtom ∈ (admitRealizationRule bindings).neg := by
        simp [admitRealizationRule]
      obtain ⟨hdSup, hAdmUnsup⟩ :=
        defeat_observation_forces_admissible_unsupported ks I w H bindings proof expectedRoot
          hdFact hdNeg
      refine ⟨rfl, hGraphFalse, hdSup, hAdmUnsup, ?_⟩
      intro hBlk
      have hEqSup := (traceUnsupportedRoot_eq_alreadySupported_iff
        (buildDialecticalAuditState ks I w H bindings proof expectedRoot)
        realizationAdmissibleAtom).1 hBlk
      change status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
        realizationAdmissibleAtom = .supported at hEqSup
      rw [hAdmUnsup] at hEqSup
      cases hEqSup
    · simp only [hBadGraph, Bool.false_eq_true, ↓reduceIte] at h
      cases hGlueOpt : findFirstGluingConflict bindings <;> rw [hGlueOpt] at h
      · by_cases hRec : verifyNonEmptyBlindedMultiproof256 H proof expectedRoot = true
        · simp only [hRec, ↓reduceIte] at h
          cases policyTarget with
          | none => cases h
          | some t =>
            dsimp only at h
            by_cases hPol : ({ base := policyBase, kept := judge policyBase } : State).status t = .supported
            · simp [hPol] at h
            · have hne : (({ base := policyBase, kept := judge policyBase } : State).status t == .supported) = false :=
                beq_false_of_ne hPol
              simp only [hne, Bool.false_eq_true, ↓reduceIte, PSum.inr.injEq] at h
              subst h
              refine ⟨rfl, rfl, hPol, ?_⟩
              intro hBlk
              exact hPol ((traceUnsupportedRoot_eq_alreadySupported_iff _ t).1 hBlk)
        · simp only [Bool.not_eq_true] at hRec
          simp only [hRec, Bool.false_eq_true, ↓reduceIte, PSum.inr.injEq] at h
          subst h
          have hdFact :
              receiptInvalidAtom ∈
                (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts := by
            simp [buildDialecticalAuditBase, hRec]
          have hdNeg : receiptInvalidAtom ∈ (admitRealizationRule bindings).neg := by
            simp [admitRealizationRule]
          obtain ⟨hdSup, hAdmUnsup⟩ :=
            defeat_observation_forces_admissible_unsupported ks I w H bindings proof expectedRoot
              hdFact hdNeg
          refine ⟨hRec, hdSup, hAdmUnsup, ?_⟩
          intro hBlk
          have hEqSup := (traceUnsupportedRoot_eq_alreadySupported_iff
            (buildDialecticalAuditState ks I w H bindings proof expectedRoot)
            realizationAdmissibleAtom).1 hBlk
          change status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
            realizationAdmissibleAtom = .supported at hEqSup
          rw [hAdmUnsup] at hEqSup
          cases hEqSup
      · rename_i pair
        rcases pair with ⟨b₁, b₂⟩
        simp only [PSum.inr.injEq] at h
        subst h
        obtain ⟨hm1, hm2, hIncompat⟩ := findFirstGluingConflict_eq_some bindings hGlueOpt
        have hNotAllGlue : allPairsGluingCompatible bindings = false := by
          cases hAll : allPairsGluingCompatible bindings
          · rfl
          · rw [(findFirstGluingConflict_none_iff bindings).2 hAll] at hGlueOpt
            cases hGlueOpt
        have hdFact :
            gluingConflictAtom ∈
              (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts := by
          simp [buildDialecticalAuditBase, hNotAllGlue]
        have hdNeg : gluingConflictAtom ∈ (admitRealizationRule bindings).neg := by
          simp [admitRealizationRule]
        obtain ⟨hdSup, hAdmUnsup⟩ :=
          defeat_observation_forces_admissible_unsupported ks I w H bindings proof expectedRoot
            hdFact hdNeg
        refine ⟨⟨b₁, hm1, b₂, hm2, rfl, rfl, rfl, rfl, hIncompat⟩, hdSup, hAdmUnsup, ?_⟩
        intro hBlk
        have hEqSup := (traceUnsupportedRoot_eq_alreadySupported_iff
          (buildDialecticalAuditState ks I w H bindings proof expectedRoot)
          realizationAdmissibleAtom).1 hBlk
        change status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
          realizationAdmissibleAtom = .supported at hEqSup
        rw [hAdmUnsup] at hEqSup
        cases hEqSup
  · rename_i triple
    rcases triple with ⟨idx, b, failure⟩
    simp only [PSum.inr.injEq] at h
    subst h
    obtain ⟨_, hGet, hm, hAud, hCheck, hInSlotObs, hInNeg⟩ :=
      findFirstFailingSlotAux_eq_some ks I w 0 bindings hSlot
    rw [Nat.sub_zero] at hGet
    have hdFact :
        slotViolationAtom idx b.iface.slotId ∈
          (buildDialecticalAuditBase ks I w H bindings proof expectedRoot).program.facts := by
      simp only [buildDialecticalAuditBase, Base.held, List.filter_nil,
        List.append_nil, List.map_append, List.mem_append]
      exact Or.inl hInSlotObs
    have hdNeg : slotViolationAtom idx b.iface.slotId ∈ (admitRealizationRule bindings).neg := by
      simp only [admitRealizationRule, List.mem_append]
      exact Or.inl hInNeg
    obtain ⟨hdSup, hAdmUnsup⟩ :=
      defeat_observation_forces_admissible_unsupported ks I w H bindings proof expectedRoot
        hdFact hdNeg
    refine ⟨⟨b, hGet, hm, rfl, rfl, rfl, hAud, hCheck⟩, hdSup, hAdmUnsup, ?_⟩
    intro hBlk
    have hEqSup := (traceUnsupportedRoot_eq_alreadySupported_iff
      (buildDialecticalAuditState ks I w H bindings proof expectedRoot)
      realizationAdmissibleAtom).1 hBlk
    change status (buildDialecticalAuditBase ks I w H bindings proof expectedRoot)
      realizationAdmissibleAtom = .supported at hEqSup
    rw [hAdmUnsup] at hEqSup
    cases hEqSup

end Obend.Reasons.DialecticalBlame

end
