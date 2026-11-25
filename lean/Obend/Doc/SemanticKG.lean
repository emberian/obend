module
/-
# Obend.Doc.SemanticKG — Public Spine & Multi-Turn Verifiable Semantic KG World Evolution

Public umbrella spine for the 4-stage Verifiable Semantic Knowledge Graph (`Obend.SemanticKG`) and
verified multi-turn stateful world evolution:
1. **Public Spine**: Re-exports `Databank` (Stage 1), `SpanParse` (Stage 2), `HypergraphChase`
   (Stage 3), and `SemanticCert` (Stage 4).
2. **Multi-Turn Stateful World Evolution (`KgWorldState`, `KgTurn`, `stepKgTurn`, `runKgTrace`)**:
   - Models document insertion (`insertDoc`), irrevocable document revocation (`revokeDoc`),
     monotone redaction tightening (`tightenRedaction`), capability attenuation (`attenuateCap`),
     and mandate budget consumption (`consumeMandate`).
   - Proves open-world anti-narrowing completeness **`skip_implies_contract_violation`**:
     `stepKgTurn st turn = none ↔ ¬ KgTurnContract st turn`.
   - Proves multi-turn preservation & revocation soundness **`semanticKg_multi_turn_update_sound`**:
     across arbitrary `turns : List KgTurn`, preserves `WfKgWorldState` (including
     `redaction_cannot_splice_tokens` on every active chunk), monotonically grows `revokedDocIds`
     with zero revoked chunks remaining in `stₙ.db`, monotonically attenuates `capRights`,
     monotonically depletes `mandateBudget`, and invalidates both Merkle chunk inclusion proofs
     (`verifyDatabankChunkInclusion_binding`) and full-databank commitments (`databankCommit256_binding`
     up to 2-preimage `CollisionAmong deployed`) for any revoked `docId`.
   - Proves constructive non-vacuity **`runKgTrace_inhabited`** across all 5 turn constructors.
-/
public import Obend.SemanticKG.Databank
public import Obend.SemanticKG.SpanParse
public import Obend.SemanticKG.HypergraphChase
public import Obend.SemanticKG.WireQuery
import all Obend.SemanticKG.Databank
import all Obend.Polis.EvidencedOcap

public section
namespace Obend.Doc.SemanticKG

open Obend.SemanticKG
open Obend.Core.Digest
open Obend.Digest.HashBytes
open Obend.Judge
open Obend.Judge.Commit (cshakeHasher)

set_option autoImplicit false

/-! ## §1. Multi-Turn KG World State & Well-Formedness Invariant -/

/-- Persistent multi-turn world state of a verifiable Semantic Knowledge Graph. -/
structure KgWorldState where
  db                : SemanticDatabank
  revokedDocIds     : Array Nat
  redactionPolicies : List (Nat × RedactionSlicePolicy)
  capRights         : UInt64
  mandateBudget     : Nat
  deriving DecidableEq

/-- Look up the active redaction policy bound to `docId`. -/
def lookupRedactionPolicy (pols : List (Nat × RedactionSlicePolicy)) (docId : Nat) :
    Option RedactionSlicePolicy :=
  (pols.find? (fun p => p.1 == docId)).map Prod.snd

/-- Pairwise distinctness check on document IDs. -/
def nodupDocIds : List Nat → Bool
  | [] => true
  | x :: xs => (!xs.contains x) && nodupDocIds xs

/-- Set or replace the redaction policy associated with `docId` without leaving stale shadows. -/
def setRedactionPolicy (pols : List (Nat × RedactionSlicePolicy))
    (docId : Nat) (pol : RedactionSlicePolicy) : List (Nat × RedactionSlicePolicy) :=
  (docId, pol) :: pols.filter (fun p => p.1 != docId)

/-- Full world-state invariant:
    1. `WfDatabank st.db` (width bounds + per-chunk 256-bit digest integrity),
    2. Active chunk `docId`s are pairwise distinct,
    3. Every active chunk has `docId ∉ st.revokedDocIds` and a delimiter-confined redaction policy. -/
def WfKgWorldState (st : KgWorldState) : Bool :=
  WfDatabank st.db &&
  nodupDocIds (st.db.chunks.toList.map (·.docId)) &&
  st.db.chunks.all fun c =>
    (!st.revokedDocIds.contains c.docId) &&
    match lookupRedactionPolicy st.redactionPolicies c.docId with
    | some pol => checkRedactionDelimiterConfined c.rawBytes pol
    | none => false

private theorem nodupDocIds_iff_nodup : ∀ xs : List Nat, nodupDocIds xs = true ↔ xs.Nodup
  | [] => by simp [nodupDocIds]
  | x :: xs => by
    have hnot : xs.contains x = false ↔ x ∉ xs := by cases h : xs.contains x <;> simp_all
    simp only [nodupDocIds, Bool.and_eq_true, Bool.not_eq_true', hnot,
      nodupDocIds_iff_nodup xs, List.nodup_cons]

private theorem lookupRedactionPolicy_set_self (pols : List (Nat × RedactionSlicePolicy))
    (docId : Nat) (pol : RedactionSlicePolicy) :
    lookupRedactionPolicy (setRedactionPolicy pols docId pol) docId = some pol := by
  simp [lookupRedactionPolicy, setRedactionPolicy]

private theorem lookupRedactionPolicy_set_ne (pols : List (Nat × RedactionSlicePolicy))
    {d₁ d₂ : Nat} (hne : d₂ ≠ d₁) (pol : RedactionSlicePolicy) :
    lookupRedactionPolicy (setRedactionPolicy pols d₁ pol) d₂ =
      lookupRedactionPolicy pols d₂ := by
  unfold lookupRedactionPolicy setRedactionPolicy
  have hHead : (d₁ == d₂) = false := beq_false_of_ne hne.symm
  simp only [List.find?_cons, hHead]
  congr 1
  induction pols with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.filter_cons]
    by_cases hp1 : p.1 = d₁
    · have hNe1 : (p.1 != d₁) = false := bne_eq_false_iff_eq.mpr hp1
      have hNe2 : (p.1 == d₂) = false := beq_false_of_ne (hp1 ▸ hne.symm)
      simp only [hNe1, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hNe2, ih]
    · have hNe1 : (p.1 != d₁) = true := bne_iff_ne.mpr hp1
      simp only [hNe1, ↓reduceIte, List.find?_cons]
      cases (p.1 == d₂)
      · exact ih
      · rfl

private theorem nodup_append_singleton {xs : List Nat} {x : Nat}
    (hNd : xs.Nodup) (hNot : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hNd
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih hNd.2 (fun hm => hNot (.tail _ hm))⟩
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hNd.1 h1
    · exact hNot (List.mem_singleton.mp h2 ▸ .head _)

private theorem nodup_map_filter_chunks (cs : List DocChunkEntry) (p : DocChunkEntry → Bool)
    (hNd : (cs.map (·.docId)).Nodup) :
    ((cs.filter p).map (·.docId)).Nodup := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    simp only [List.filter_cons]
    cases hpc : p c
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih hNd.2
    · simp only [↓reduceIte, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih hNd.2⟩
      obtain ⟨c', hc', hIdEq⟩ := List.mem_map.mp hm
      exact hNd.1 (hIdEq ▸ List.mem_map_of_mem (List.mem_filter.mp hc').1)

private theorem chunk_eq_of_docId_eq {cs : List DocChunkEntry}
    (hNd : (cs.map (·.docId)).Nodup) {c₁ c₂ : DocChunkEntry}
    (h₁ : c₁ ∈ cs) (h₂ : c₂ ∈ cs) (hEq : c₁.docId = c₂.docId) : c₁ = c₂ := by
  induction cs with
  | nil => cases h₁
  | cons c rest ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp h₁ with rfl | h₁'
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · rfl
      · exact False.elim (hNd.1 (hEq ▸ List.mem_map_of_mem h₂'))
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · exact False.elim (hNd.1 (hEq.symm ▸ List.mem_map_of_mem h₁'))
      · exact ih hNd.2 h₁' h₂'

/-! ## §2. Multi-Turn `KgTurn`, Declarative Contract, Operational Step & Completeness -/

/-- State-evolution turns over a persistent `KgWorldState`. -/
inductive KgTurn where
  | insertDoc (chunk : DocChunkEntry) (pol : RedactionSlicePolicy)
  | revokeDoc (docId : Nat)
  | tightenRedaction (docId : Nat) (newPol : RedactionSlicePolicy)
  | attenuateCap (mask : UInt64)
  | consumeMandate (cost : Nat)
  deriving DecidableEq

/-- Byte-level disclosure tightening check: every byte disclosed by `newPol` was disclosed by `oldPol`. -/
def checkRedactionTighter (docSize : Nat) (oldPol newPol : RedactionSlicePolicy) : Bool :=
  (List.range docSize).all fun pos => !isDisclosedAt newPol pos || isDisclosedAt oldPol pos

private theorem checkRedactionTighter_iff (docSize : Nat) (oldPol newPol : RedactionSlicePolicy) :
    checkRedactionTighter docSize oldPol newPol = true ↔
      ∀ pos, pos < docSize → isDisclosedAt newPol pos = true → isDisclosedAt oldPol pos = true := by
  simp only [checkRedactionTighter, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro h pos hlt hNew
    rcases h pos hlt with hF | hOld
    · rw [hNew] at hF; cases hF
    · exact hOld
  · intro h pos hlt
    cases hNew : isDisclosedAt newPol pos
    · exact Or.inl rfl
    · exact Or.inr (h pos hlt hNew)

/-- Declarative per-turn admission contract (used for open-world anti-narrowing completeness). -/
def KgTurnContract (st : KgWorldState) : KgTurn → Prop
  | .insertDoc chunk pol =>
    WfDocChunk chunk = true ∧
    st.db.chunks.size + 1 < 18446744073709551616 ∧
    chunk.docId ∉ st.revokedDocIds.toList ∧
    chunk.docId ∉ st.db.chunks.toList.map (·.docId) ∧
    checkRedactionDelimiterConfined chunk.rawBytes pol = true
  | .revokeDoc docId =>
    docId ∉ st.revokedDocIds.toList
  | .tightenRedaction docId newPol =>
    ∃ c, st.db.chunks.toList.find? (fun x => x.docId == docId) = some c ∧
      ∃ oldPol, lookupRedactionPolicy st.redactionPolicies docId = some oldPol ∧
        checkRedactionDelimiterConfined c.rawBytes newPol = true ∧
        ∀ pos, pos < c.rawBytes.size →
          isDisclosedAt newPol pos = true → isDisclosedAt oldPol pos = true
  | .attenuateCap _ => True
  | .consumeMandate cost =>
    0 < cost ∧ cost ≤ st.mandateBudget

/-- Operational single-turn state transition over `KgWorldState`. -/
def stepKgTurn (st : KgWorldState) : KgTurn → Option KgWorldState
  | .insertDoc chunk pol =>
    if WfDocChunk chunk &&
       decide (st.db.chunks.size + 1 < 18446744073709551616) &&
       !st.revokedDocIds.contains chunk.docId &&
       !(st.db.chunks.toList.map (·.docId)).contains chunk.docId &&
       checkRedactionDelimiterConfined chunk.rawBytes pol then
      some {
        st with
        db := { st.db with chunks := st.db.chunks.push chunk }
        redactionPolicies := setRedactionPolicy st.redactionPolicies chunk.docId pol
      }
    else none
  | .revokeDoc docId =>
    if !st.revokedDocIds.contains docId then
      some {
        st with
        db := { st.db with chunks := st.db.chunks.filter (fun c => c.docId != docId) }
        revokedDocIds := st.revokedDocIds.push docId
      }
    else none
  | .tightenRedaction docId newPol =>
    match st.db.chunks.toList.find? (fun c => c.docId == docId),
          lookupRedactionPolicy st.redactionPolicies docId with
    | some c, some oldPol =>
      if checkRedactionDelimiterConfined c.rawBytes newPol &&
         checkRedactionTighter c.rawBytes.size oldPol newPol then
        some {
          st with
          redactionPolicies := setRedactionPolicy st.redactionPolicies docId newPol
        }
      else none
    | _, _ => none
  | .attenuateCap mask =>
    some { st with capRights := st.capRights &&& mask }
  | .consumeMandate cost =>
    if decide (0 < cost) && decide (cost ≤ st.mandateBudget) then
      some { st with mandateBudget := st.mandateBudget - cost }
    else none

/-- Execute a multi-turn sequence of KG updates starting from `st`. -/
def runKgTrace (st : KgWorldState) : List KgTurn → Option KgWorldState
  | [] => some st
  | turn :: rest =>
    match stepKgTurn st turn with
    | none => none
    | some st' => runKgTrace st' rest

private theorem stepKgTurn_isSome_iff (st : KgWorldState) (turn : KgTurn) :
    (∃ st', stepKgTurn st turn = some st') ↔ KgTurnContract st turn := by
  cases turn with
  | insertDoc chunk pol =>
    unfold stepKgTurn KgTurnContract
    have hRev : (!st.revokedDocIds.contains chunk.docId) = true ↔
        chunk.docId ∉ st.revokedDocIds.toList := by
      simp [Array.mem_toList_iff]
    have hAct : (!(st.db.chunks.toList.map (·.docId)).contains chunk.docId) = true ↔
        chunk.docId ∉ st.db.chunks.toList.map (·.docId) := by
      simp
    by_cases hCond : (WfDocChunk chunk &&
        decide (st.db.chunks.size + 1 < 18446744073709551616) &&
        !st.revokedDocIds.contains chunk.docId &&
        !(st.db.chunks.toList.map (·.docId)).contains chunk.docId &&
        checkRedactionDelimiterConfined chunk.rawBytes pol) = true
    · simp only [hCond, ↓reduceIte, Option.some.injEq, exists_eq', true_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, hRev, hAct] at hCond
      exact ⟨hCond.1.1.1.1, hCond.1.1.1.2, hCond.1.1.2, hCond.1.2, hCond.2⟩
    · simp only [hCond, ↓reduceIte, reduceCtorEq, exists_false, false_iff]
      rintro ⟨h1, h2, h3, h4, h5⟩
      apply hCond
      simp only [Bool.and_eq_true, decide_eq_true_eq, hRev, hAct]
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  | revokeDoc docId =>
    unfold stepKgTurn KgTurnContract
    have hRev : (!st.revokedDocIds.contains docId) = true ↔ docId ∉ st.revokedDocIds.toList := by
      simp [Array.mem_toList_iff]
    by_cases hCond : (!st.revokedDocIds.contains docId) = true
    · simp only [hCond, ↓reduceIte, Option.some.injEq, exists_eq', true_iff]
      exact hRev.mp hCond
    · simp only [hCond, ↓reduceIte, reduceCtorEq, exists_false, false_iff]
      exact mt hRev.mpr hCond
  | tightenRedaction docId newPol =>
    simp only [stepKgTurn, KgTurnContract]
    cases hFind : st.db.chunks.toList.find? (fun c => c.docId == docId) with
    | none =>
      constructor
      · rintro ⟨_, h⟩; cases h
      · rintro ⟨_, h, _⟩; cases h
    | some c =>
      cases hPol : lookupRedactionPolicy st.redactionPolicies docId with
      | none =>
        constructor
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨_, _, _, hp, _⟩; cases hp
      | some oldPol =>
        by_cases hCond : (checkRedactionDelimiterConfined c.rawBytes newPol &&
            checkRedactionTighter c.rawBytes.size oldPol newPol) = true
        · simp only [hCond, ↓reduceIte]
          simp only [Bool.and_eq_true, checkRedactionTighter_iff] at hCond
          exact ⟨fun _ => ⟨c, rfl, oldPol, rfl, hCond.1, hCond.2⟩, fun _ => ⟨_, rfl⟩⟩
        · simp only [hCond, Bool.false_eq_true, ↓reduceIte]
          constructor
          · rintro ⟨_, h⟩; cases h
          · rintro ⟨c', hc', oldPol', hp', hConf, hTight⟩
            injection hc' with hcEq; subst hcEq
            injection hp' with hpEq; subst hpEq
            exact False.elim (hCond (by simp only [Bool.and_eq_true, checkRedactionTighter_iff]; exact ⟨hConf, hTight⟩))
  | attenuateCap mask =>
    simp [stepKgTurn, KgTurnContract]
  | consumeMandate cost =>
    unfold stepKgTurn KgTurnContract
    by_cases hCond : (decide (0 < cost) && decide (cost ≤ st.mandateBudget)) = true
    · simp only [hCond, ↓reduceIte, Option.some.injEq, exists_eq', true_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      exact hCond
    · simp only [hCond, ↓reduceIte, reduceCtorEq, exists_false, false_iff]
      rintro ⟨h1, h2⟩
      exact hCond (by simp [h1, h2])

/-- **Open-World Anti-Narrowing Completeness (`skip_implies_contract_violation`)**:
    `stepKgTurn st turn` rejects (`none`) if and only if `turn` genuinely violates `KgTurnContract st turn`. -/
theorem skip_implies_contract_violation (st : KgWorldState) (turn : KgTurn) :
    stepKgTurn st turn = none ↔ ¬ KgTurnContract st turn := by
  rw [← stepKgTurn_isSome_iff st turn]
  cases stepKgTurn st turn with
  | none => simp
  | some st' => simp

/-! ## §3. Single-Turn & Multi-Turn Preservation, Monotonicity & Revocation Invalidation -/

private theorem stepKgTurn_preserves {st st' : KgWorldState} {turn : KgTurn}
    (hWf : WfKgWorldState st = true)
    (hStep : stepKgTurn st turn = some st') :
    WfKgWorldState st' = true ∧
    (∀ id ∈ st.revokedDocIds.toList, id ∈ st'.revokedDocIds.toList) ∧
    Obend.Polis.subMask st'.capRights st.capRights = true ∧
    st'.mandateBudget ≤ st.mandateBudget := by
  have hWfUnpack := hWf
  simp only [WfKgWorldState, WfDatabank, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true_iff_forall_mem, nodupDocIds_iff_nodup] at hWfUnpack
  obtain ⟨⟨⟨hSz, hChunksWf⟩, hNd⟩, hChunkPol⟩ := hWfUnpack
  cases turn with
  | insertDoc chunk pol =>
    simp only [stepKgTurn] at hStep
    split at hStep
    · rename_i hCond
      injection hStep with hEq; subst hEq
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hCond
      obtain ⟨⟨⟨⟨hWfC, hSz'⟩, hNotRev⟩, hNotAct⟩, hConf⟩ := hCond
      have hNotRev' : chunk.docId ∉ st.revokedDocIds := fun hm => by
        have ht := Array.contains_iff_mem.mpr hm; rw [ht] at hNotRev; cases hNotRev
      have hNotAct' : chunk.docId ∉ st.db.chunks.toList.map (·.docId) := fun hm => by
        have ht := List.contains_iff_mem.mpr hm; rw [ht] at hNotAct; cases hNotAct
      refine ⟨?_, fun _ h => h, Obend.Polis.subMask_refl _, Nat.le_refl _⟩
      simp only [WfKgWorldState, WfDatabank, Bool.and_eq_true, decide_eq_true_eq,
        Array.all_eq_true_iff_forall_mem, nodupDocIds_iff_nodup]
      simp only [Array.size_push, Array.toList_push, List.map_append, List.map_singleton]
      refine ⟨⟨⟨hSz', fun c hc => ?_⟩, nodup_append_singleton hNd hNotAct'⟩, fun c hc => ?_⟩
      · rcases Array.mem_push.mp hc with hcOld | rfl
        · exact hChunksWf c hcOld
        · exact hWfC
      · rcases Array.mem_push.mp hc with hcOld | rfl
        · have hOld := hChunkPol c hcOld
          have hNe : c.docId ≠ chunk.docId := fun hId =>
            hNotAct' (hId ▸ List.mem_map_of_mem (Array.mem_toList_iff.mpr hcOld))
          rw [lookupRedactionPolicy_set_ne _ hNe pol]
          exact hOld
        · rw [lookupRedactionPolicy_set_self]
          exact ⟨by simpa [Array.contains_iff_mem] using hNotRev', hConf⟩
    · cases hStep
  | revokeDoc docId =>
    simp only [stepKgTurn] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      refine ⟨?_, fun id hid => by
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        exact Or.inl hid, Obend.Polis.subMask_refl _, Nat.le_refl _⟩
      simp only [WfKgWorldState, WfDatabank, Bool.and_eq_true, decide_eq_true_eq,
        Array.all_eq_true_iff_forall_mem, nodupDocIds_iff_nodup]
      have hFiltSz : (st.db.chunks.filter (fun c => c.docId != docId)).size ≤ st.db.chunks.size :=
        Array.size_filter_le
      refine ⟨⟨⟨by omega, fun c hc => ?_⟩, ?_⟩, fun c hc => ?_⟩
      · exact hChunksWf c (Array.mem_filter.mp hc).1
      · rw [Array.toList_filter]
        exact nodup_map_filter_chunks st.db.chunks.toList _ hNd
      · have hMemOld : c ∈ st.db.chunks := (Array.mem_filter.mp hc).1
        have hNeId : c.docId ≠ docId := bne_iff_ne.mp (Array.mem_filter.mp hc).2
        have hOld := hChunkPol c hMemOld
        refine ⟨?_, hOld.2⟩
        simp only [Bool.not_eq_true'] at hOld ⊢
        have hNotOld : c.docId ∉ st.revokedDocIds := fun hm => by
          have ht := Array.contains_iff_mem.mpr hm; rw [ht] at hOld; cases hOld.1
        cases hCont : (st.revokedDocIds.push docId).contains c.docId with
        | false => rfl
        | true =>
          rcases Array.mem_push.mp (Array.contains_iff_mem.mp hCont) with hm | heq
          · exact False.elim (hNotOld hm)
          · exact False.elim (hNeId heq)
    · cases hStep
  | tightenRedaction docId newPol =>
    simp only [stepKgTurn] at hStep
    cases hFind : st.db.chunks.toList.find? (fun c => c.docId == docId) with
    | none => simp [hFind] at hStep
    | some c =>
      cases hOldPol : lookupRedactionPolicy st.redactionPolicies docId with
      | none => simp [hFind, hOldPol] at hStep
      | some oldPol =>
        simp only [hFind, hOldPol] at hStep
        split at hStep
        · rename_i hCond
          injection hStep with hEq; subst hEq
          simp only [Bool.and_eq_true] at hCond
          have hcMem : c ∈ st.db.chunks.toList := List.mem_of_find?_eq_some hFind
          have hcId : c.docId = docId := by simpa [beq_iff_eq] using List.find?_some hFind
          refine ⟨?_, fun _ h => h, Obend.Polis.subMask_refl _, Nat.le_refl _⟩
          simp only [WfKgWorldState, WfDatabank, Bool.and_eq_true, decide_eq_true_eq,
            Array.all_eq_true_iff_forall_mem, nodupDocIds_iff_nodup]
          refine ⟨⟨⟨hSz, hChunksWf⟩, hNd⟩, fun x hx => ?_⟩
          have hOld := hChunkPol x hx
          by_cases hxId : x.docId = docId
          · have hxEq : x = c :=
              chunk_eq_of_docId_eq hNd (Array.mem_toList_iff.mpr hx) hcMem (hxId.trans hcId.symm)
            subst hxEq
            rw [hcId] at hOld ⊢
            rw [lookupRedactionPolicy_set_self]
            exact ⟨hOld.1, hCond.1⟩
          · rw [lookupRedactionPolicy_set_ne _ hxId newPol]
            exact hOld
        · cases hStep
  | attenuateCap mask =>
    simp only [stepKgTurn, Option.some.injEq] at hStep
    subst hStep
    exact ⟨hWf, fun _ h => h, Obend.Polis.subMask_and_left st.capRights mask, Nat.le_refl _⟩
  | consumeMandate cost =>
    simp only [stepKgTurn] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      exact ⟨hWf, fun _ h => h, Obend.Polis.subMask_refl _, Nat.sub_le _ _⟩
    · cases hStep

private theorem wfKgWorldState_redaction_and_disjoint {st : KgWorldState}
    (hWf : WfKgWorldState st = true) :
    WfDatabankBounds st.db = true ∧
    (∀ c ∈ st.db.chunks, c.docId ∉ st.revokedDocIds.toList) ∧
    (∀ c ∈ st.db.chunks, ∃ pol,
      lookupRedactionPolicy st.redactionPolicies c.docId = some pol ∧
      checkRedactionDelimiterConfined c.rawBytes pol = true ∧
      (∀ tok : TokenSpan, IsMaximalTokenSpan (applyRedactionPolicy c.rawBytes pol) tok = true →
        (∃ sp ∈ pol.disclosedSpans.toList, sp.1 ≤ tok.start ∧ tok.stop ≤ sp.2) ∧
        VpaJson.jsonStateAt (applyRedactionPolicy c.rawBytes pol) tok.start =
          VpaJson.jsonStateAt c.rawBytes tok.start ∧
        IsMaximalTokenSpan c.rawBytes tok = true)) := by
  simp only [WfKgWorldState, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hWf
  obtain ⟨⟨hWfDb, _⟩, hPer⟩ := hWf
  have hBnd : WfDatabankBounds st.db = true := by
    simp only [WfDatabank, WfDatabankBounds, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hWfDb ⊢
    exact ⟨hWfDb.1, fun c hc => (Bool.and_eq_true_iff.mp (hWfDb.2 c hc)).1⟩
  refine ⟨hBnd, fun c hc hRev => ?_, fun c hc => ?_⟩
  · have hC := (hPer c hc).1
    have hMem : c.docId ∈ st.revokedDocIds := Array.mem_toList_iff.mp hRev
    rw [Array.contains_iff_mem.mpr hMem] at hC; cases hC
  · have hC := (hPer c hc).2
    cases hPol : lookupRedactionPolicy st.redactionPolicies c.docId with
    | none => rw [hPol] at hC; cases hC
    | some pol =>
      rw [hPol] at hC
      exact ⟨pol, rfl, hC, (redaction_cannot_splice_tokens hC).2.2⟩

/-- **Multi-Turn Semantic KG Evolution & Revocation Soundness (`semanticKg_multi_turn_update_sound`)**:
    Across arbitrary multi-turn traces `runKgTrace st₀ turns = some stₙ` starting from `WfKgWorldState st₀`:
    (a) `WfKgWorldState stₙ = true` and `redaction_cannot_splice_tokens` holds on every active chunk;
    (b) `revokedDocIds` grows monotonically and zero active chunks in `stₙ.db` carry a revoked `docId`;
    (c) `capRights` attenuates monotonically (`Obend.Polis.subMask stₙ.capRights st₀.capRights = true`);
    (d) `mandateBudget` depletes monotonically (`stₙ.mandateBudget ≤ st₀.mandateBudget`);
    (e) Any Merkle chunk inclusion proof against `databankChunkMerkleRoot stₙ.db` for a revoked `docId`
        yields a `cshakeHasher` collision (via `verifyDatabankChunkInclusion_binding`), AND any
        well-formed databank `dbOld` still holding a revoked chunk with `databankCommit256 dbOld =
        databankCommit256 stₙ.db` yields an explicit 2-preimage `CollisionAmong deployed`. -/
theorem semanticKg_multi_turn_update_sound
    {st₀ stₙ : KgWorldState} {turns : List KgTurn}
    (hWf₀ : WfKgWorldState st₀ = true)
    (hTrace : runKgTrace st₀ turns = some stₙ) :
    WfKgWorldState stₙ = true ∧
    (∀ c ∈ stₙ.db.chunks, ∃ pol,
      lookupRedactionPolicy stₙ.redactionPolicies c.docId = some pol ∧
      checkRedactionDelimiterConfined c.rawBytes pol = true ∧
      (∀ tok : TokenSpan, IsMaximalTokenSpan (applyRedactionPolicy c.rawBytes pol) tok = true →
        (∃ sp ∈ pol.disclosedSpans.toList, sp.1 ≤ tok.start ∧ tok.stop ≤ sp.2) ∧
        VpaJson.jsonStateAt (applyRedactionPolicy c.rawBytes pol) tok.start =
          VpaJson.jsonStateAt c.rawBytes tok.start ∧
        IsMaximalTokenSpan c.rawBytes tok = true)) ∧
    (∀ id ∈ st₀.revokedDocIds.toList, id ∈ stₙ.revokedDocIds.toList) ∧
    (∀ c ∈ stₙ.db.chunks, c.docId ∉ stₙ.revokedDocIds.toList) ∧
    Obend.Polis.subMask stₙ.capRights st₀.capRights = true ∧
    stₙ.mandateBudget ≤ st₀.mandateBudget ∧
    (∀ (chunk : DocChunkEntry) (prf : VpaJson.SpanProof),
      verifyDatabankChunkInclusion (databankChunkMerkleRoot stₙ.db) chunk prf = true →
      chunk.docId ∈ stₙ.revokedDocIds.toList →
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
        cshakeHasher.hash databankChunkSpanTag m₁ = cshakeHasher.hash databankChunkSpanTag m₂) ∧
    (∀ (dbOld : SemanticDatabank),
      WfDatabankBounds dbOld = true →
      (∃ c ∈ dbOld.chunks, c.docId ∈ stₙ.revokedDocIds.toList) →
      databankCommit256 dbOld = databankCommit256 stₙ.db →
      CollisionAmong deployed
        (fun m => m = databankPreimage dbOld ∨ m = databankPreimage stₙ.db)) := by
  have hInv : ∀ (ts : List KgTurn) (s₀ s₁ : KgWorldState),
      WfKgWorldState s₀ = true → runKgTrace s₀ ts = some s₁ →
      WfKgWorldState s₁ = true ∧
      (∀ id ∈ s₀.revokedDocIds.toList, id ∈ s₁.revokedDocIds.toList) ∧
      Obend.Polis.subMask s₁.capRights s₀.capRights = true ∧
      s₁.mandateBudget ≤ s₀.mandateBudget := by
    intro ts
    induction ts with
    | nil =>
      intro s₀ s₁ hW hR
      simp only [runKgTrace, Option.some.injEq] at hR; subst hR
      exact ⟨hW, fun _ h => h, Obend.Polis.subMask_refl _, Nat.le_refl _⟩
    | cons t rest ih =>
      intro s₀ s₁ hW hR
      unfold runKgTrace at hR
      cases hS : stepKgTurn s₀ t with
      | none => rw [hS] at hR; cases hR
      | some sm =>
        rw [hS] at hR
        obtain ⟨hWm, hRev1, hCap1, hBud1⟩ := stepKgTurn_preserves hW hS
        obtain ⟨hW1, hRev2, hCap2, hBud2⟩ := ih sm s₁ hWm hR
        exact ⟨hW1, fun id hid => hRev2 id (hRev1 id hid),
          Obend.Polis.subMask_trans hCap2 hCap1, Nat.le_trans hBud2 hBud1⟩
  obtain ⟨hWfₙ, hRevMono, hCapMono, hBudMono⟩ := hInv turns st₀ stₙ hWf₀ hTrace
  obtain ⟨hBndₙ, hNoRevₙ, hRedₙ⟩ := wfKgWorldState_redaction_and_disjoint hWfₙ
  refine ⟨hWfₙ, hRedₙ, hRevMono, hNoRevₙ, hCapMono, hBudMono, ?_, ?_⟩
  · intro chunk prf hIncl hRev
    rcases verifyDatabankChunkInclusion_binding hBndₙ hIncl with hGet | hCol
    · exact False.elim (hNoRevₙ chunk (Array.mem_of_getElem? hGet) hRev)
    · exact hCol
  · intro dbOld hBndOld ⟨c, hcOld, hcRev⟩ hCommitEq
    rcases databankCommit256_binding hBndOld hBndₙ hCommitEq with hDbEq | hCol
    · rw [hDbEq] at hcOld
      exact False.elim (hNoRevₙ c hcOld hcRev)
    · exact hCol

/-- Constructive multi-turn non-vacuity witness executing all 5 turn kinds:
    `insertDoc → tightenRedaction → attenuateCap → consumeMandate → revokeDoc`. -/
theorem runKgTrace_inhabited (worldRoot : DatabankRoot256) :
    let doc := "{\"k\":\"a\",\"s\":\"secret\"}".toByteArray
    let chunk := mkDocChunk 1 0 doc
    let pol1 : RedactionSlicePolicy := ⟨22, #[(0, 22)]⟩
    let pol2 : RedactionSlicePolicy := ⟨22, #[(0, 14), (20, 22)]⟩
    let st₀ : KgWorldState := {
      db := ⟨worldRoot, #[]⟩
      revokedDocIds := #[]
      redactionPolicies := []
      capRights := 0xff
      mandateBudget := 10
    }
    let turns : List KgTurn := [
      .insertDoc chunk pol1,
      .tightenRedaction 1 pol2,
      .attenuateCap 0x0f,
      .consumeMandate 3,
      .revokeDoc 1
    ]
    WfKgWorldState st₀ = true ∧
    ∃ stₙ : KgWorldState,
      runKgTrace st₀ turns = some stₙ ∧
      stₙ.db.chunks = #[] ∧
      stₙ.revokedDocIds = #[1] ∧
      stₙ.capRights = 0x0f ∧
      stₙ.mandateBudget = 7 := by
  intro doc chunk pol1 pol2 st₀ turns
  have hWf₀ : WfKgWorldState st₀ = true := by
    simp [WfKgWorldState, WfDatabank, nodupDocIds, st₀]
  have hWfChunk : WfDocChunk chunk = true :=
    wfDocChunk_mkDocChunk (by decide) (by decide) (by decide)
  have hConf1 : checkRedactionDelimiterConfined doc pol1 = true := by
    have hSz : doc.size = 22 := by decide
    have hElid : elidedGaps pol1 = [] := by decide
    simp [checkRedactionDelimiterConfined, pol1, hSz, hElid, checkSortedDisjointSpansFrom]
  have hConf2 : checkRedactionDelimiterConfined doc pol2 = true :=
    (checkRedactionDelimiterConfined_inhabited ()).2.2.1
  have hTight : checkRedactionTighter doc.size pol1 pol2 = true := by decide +kernel
  have hChunkBytes : chunk.rawBytes = doc := rfl
  have hChunkId : chunk.docId = 1 := rfl
  let st₁ : KgWorldState := ⟨⟨worldRoot, #[chunk]⟩, #[], [(1, pol1)], 0xff, 10⟩
  let st₂ : KgWorldState := ⟨⟨worldRoot, #[chunk]⟩, #[], [(1, pol2)], 0xff, 10⟩
  let st₃ : KgWorldState := ⟨⟨worldRoot, #[chunk]⟩, #[], [(1, pol2)], 0x0f, 10⟩
  let st₄ : KgWorldState := ⟨⟨worldRoot, #[chunk]⟩, #[], [(1, pol2)], 0x0f, 7⟩
  let st₅ : KgWorldState := ⟨⟨worldRoot, #[]⟩, #[1], [(1, pol2)], 0x0f, 7⟩
  refine ⟨hWf₀, st₅, ?_, rfl, rfl, rfl, rfl⟩
  have hStep1 : stepKgTurn st₀ (.insertDoc chunk pol1) = some st₁ := by
    simp [stepKgTurn, hWfChunk, hChunkBytes, hConf1, setRedactionPolicy, st₀, st₁, hChunkId]
  have hStep2 : stepKgTurn st₁ (.tightenRedaction 1 pol2) = some st₂ := by
    have hFind : st₁.db.chunks.toList.find? (fun c => c.docId == 1) = some chunk := by
      simp [st₁, hChunkId]
    have hLook : lookupRedactionPolicy st₁.redactionPolicies 1 = some pol1 := by
      simp [lookupRedactionPolicy, st₁]
    simp [stepKgTurn, hFind, hLook, hChunkBytes, hConf2, hTight, setRedactionPolicy, st₁, st₂]
  have hStep3 : stepKgTurn st₂ (.attenuateCap 0x0f) = some st₃ := by
    have hAnd : ((0xff : UInt64) &&& (0x0f : UInt64)) = 0x0f := by decide
    simp [stepKgTurn, st₂, st₃, hAnd]
  have hStep4 : stepKgTurn st₃ (.consumeMandate 3) = some st₄ := by
    simp [stepKgTurn, st₃, st₄]
  have hStep5 : stepKgTurn st₄ (.revokeDoc 1) = some st₅ := by
    simp [stepKgTurn, st₄, st₅, hChunkId]
  dsimp only [turns]
  simp only [runKgTrace, hStep1, hStep2, hStep3, hStep4, hStep5]

end Obend.Doc.SemanticKG
end
