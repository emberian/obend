module
/-
# Obend.SemanticKG.HypergraphChase — Provenance Hypergraphs, Guarded Skolem Chase, RMFA, Ranked WFS, Evidenced Ocap & Core Quotient
Stage 3 of the 4-stage Verifiable Semantic Knowledge Graph (`Obend.SemanticKG`):
1. **4-Point Goldilocks Provenance Semiring (`ProvVec d`, `ProvVec4`)**
2. **Attributed Knowledge Hypergraph (`AKHGSpec` ↔ `AKHGExec`, `akhgExec_simulates_spec`)**
3. **Injective `Term ↔ SymId` Interning & $O(|R| \cdot |M| \log |M|)$ Guarded TGD Saturation (`checkGuardedSaturationFast_eq_spec`)**
4. **RMFA / EDB-Guarded Rank Witness (`RmfaRankWitness`, `rmfa_chase_terminates_bounded`, `rmfa_strictly_subsumes_weaklyAcyclic`)**
5. **$O(|P|)$ Ranked GL & VGRS Fixpoint Wrappers (`checkGlFixpointLinear_iff_least_model`, `checkVgrsFixpointLinear_iff_wfs`)**
6. **Evidenced Ocap Query Guard (`evidenced_kg_query_guard_sound`) & Choice-Free Core BCQ Quotient Lift (`core_quotient_bcq_lift_sound`)**
-/
public import Obend.SemanticKG.Databank
public import Obend.SemanticKG.ColtJoin
public import Obend.SemanticKG.SlottedEGraph
public import Obend.SemanticKG.SpanParse
public import Obend.SymbolicZk.SemiringDatalog
public import Obend.SymbolicZk.SkolemChaseCore
public import Obend.SymbolicZk.RankedFixpointArith
public import Obend.Polis.EvidencedOcap
public import Obend.Repair.QuotAssembly
import all Obend.SymbolicZk.SemiringDatalog
import all Obend.SymbolicZk.SkolemChaseCore
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.Polis.EvidencedOcap
import all Obend.Repair.QuotAssembly

public section
namespace Obend.SemanticKG
open Obend.SymbolicZk
open Obend.SymbolicZk.Datalog (ProvenanceSemiringOps LawfulProvenanceSemiring ProvenanceHom)
open Obend.SymbolicZk.SkolemChaseCore
set_option autoImplicit false

/-- Table of Core4 terms for a relational body. Equations name input rows. The two sides must
share a free-slot interface in the same formal order. An incompatible or dangling equation
rejects the batch. The output columns are input row and congruence class of its full application. -/
def coreCongruenceRelation (terms : Array Obend.Core.Term.Term)
    (equations : Array (Nat × Nat)) : Option Colt.Relation := do
  let (roots, graph) := (terms.mapM (fun t => Slotted.insertCore t)).run {}
  let eqs ← equations.mapM fun (lhs, rhs) => do
    let a ← roots[lhs]?
    let b ← roots[rhs]?
    guard (a.slots == b.slots)
    return (a.id, b.id)
  let reps := graph.close eqs
  let mut applications : Std.HashMap (Slotted.Applied Nat) Nat := {}
  let mut classes := #[]
  for root in roots do
    let key := { root with id := ← reps[root.id]? }
    let c := applications[key]?.getD applications.size
    applications := applications.insert key c
    classes := classes.push c
  return ⟨[Array.range terms.size, classes], terms.size⟩

/-! ## §1. 4-Point Goldilocks Provenance Semiring (`ProvVec d`, `ProvVec4`) -/
structure ProvVec (d : Nat) where
  limbs : Vector Obend.Crypto.Goldilocks d
  deriving DecidableEq, Repr
abbrev ProvVec4 := ProvVec 4
instance instProvenanceSemiringOpsProvVec (d : Nat) :
    Datalog.ProvenanceSemiringOps (ProvVec d) where
  zero := ⟨Vector.replicate d Datalog.ProvenanceSemiringOps.zero⟩
  one  := ⟨Vector.replicate d Datalog.ProvenanceSemiringOps.one⟩
  add a b := ⟨Vector.ofFn fun i => Datalog.ProvenanceSemiringOps.add a.limbs[i.val] b.limbs[i.val]⟩
  mul a b := ⟨Vector.ofFn fun i => Datalog.ProvenanceSemiringOps.mul a.limbs[i.val] b.limbs[i.val]⟩
theorem provVec_ext {d : Nat} {a b : ProvVec d}
    (h : ∀ (i : Nat) (hi : i < d), a.limbs[i]'hi = b.limbs[i]'hi) : a = b := by
  cases a; cases b; congr 1; exact Vector.ext h
instance instLawfulProvenanceSemiringProvVec (d : Nat) :
    Datalog.LawfulProvenanceSemiring (ProvVec d) where
  add_assoc a b c := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.add, Vector.getElem_ofFn]; exact LawfulProvenanceSemiring.add_assoc _ _ _
  add_comm a b := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.add, Vector.getElem_ofFn]; exact LawfulProvenanceSemiring.add_comm _ _
  zero_add a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.zero, ProvenanceSemiringOps.add, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.zero_add _
  add_zero a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.zero, ProvenanceSemiringOps.add, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.add_zero _
  mul_assoc a b c := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.mul, Vector.getElem_ofFn]; exact LawfulProvenanceSemiring.mul_assoc _ _ _
  mul_comm a b := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.mul, Vector.getElem_ofFn]; exact LawfulProvenanceSemiring.mul_comm _ _
  one_mul a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.one, ProvenanceSemiringOps.mul, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.one_mul _
  mul_one a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.one, ProvenanceSemiringOps.mul, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.mul_one _
  left_distrib a b c := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.add, ProvenanceSemiringOps.mul, Vector.getElem_ofFn]
    exact LawfulProvenanceSemiring.left_distrib _ _ _
  zero_mul a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.zero, ProvenanceSemiringOps.mul, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.zero_mul _
  mul_zero a := provVec_ext fun i hi => by
    simp only [ProvenanceSemiringOps.zero, ProvenanceSemiringOps.mul, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact LawfulProvenanceSemiring.mul_zero _
def evalProvVec {V : Type} {d : Nat} (envs : Fin d → V → Obend.Crypto.Goldilocks)
    (e : Datalog.ProvExpr V) : ProvVec d :=
  ⟨Vector.ofFn fun i => Datalog.evalProvGoldilocks (envs i) e⟩
theorem evalProvenancePoly_hom {V : Type} (d : Nat) (envs : Fin d → V → Obend.Crypto.Goldilocks) :
    Datalog.ProvenanceHom (evalProvVec envs) where
  map_zero := provVec_ext fun _ _ => by simp [evalProvVec, ProvenanceSemiringOps.zero, Datalog.evalProvGoldilocks]
  map_one  := provVec_ext fun _ _ => by simp [evalProvVec, ProvenanceSemiringOps.one, Datalog.evalProvGoldilocks]
  map_add _ _ := provVec_ext fun _ _ => by simp [evalProvVec, ProvenanceSemiringOps.add, Datalog.evalProvGoldilocks]
  map_mul _ _ := provVec_ext fun _ _ => by simp [evalProvVec, ProvenanceSemiringOps.mul, Datalog.evalProvGoldilocks]
theorem provVecProj_hom (d : Nat) (i : Fin d) :
    Datalog.ProvenanceHom (fun (v : ProvVec d) => v.limbs[i]) where
  map_zero := by simp [ProvenanceSemiringOps.zero]
  map_one  := by simp [ProvenanceSemiringOps.one]
  map_add _ _ := by simp [ProvenanceSemiringOps.add]
  map_mul _ _ := by simp [ProvenanceSemiringOps.mul]

/-! ## §2. Attributed Knowledge Hypergraph (`AKHGSpec` ↔ `AKHGExec`) -/
def spanAtomToGroundTuple (a : SpanBoundAtom) : Datalog.GroundTuple :=
  { rel := a.predSym.toNat, args := a.args.map UInt32.toNat }
def spanAtomToBaseChaseAtom (a : SpanBoundAtom) : Atom Term :=
  { rel := a.predSym.toNat, args := a.args.toList.map (fun id => .const id.toNat) }
theorem spanAtomToBaseChaseAtom_isBase (a : SpanBoundAtom) :
    isBaseAtom (spanAtomToBaseChaseAtom a) = true := by
  simp [isBaseAtom, spanAtomToBaseChaseAtom, isBaseTerm]
abbrev AKHGSpec (K : Type) := List (Datalog.GroundTuple × K)
structure AKHGExec (K : Type) where
  table : Datalog.SortedKTable K
def buildAkhgExec {K : Type} [Datalog.LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (Datalog.GroundTuple × K)) : AKHGExec K := ⟨Datalog.buildSorted es⟩
theorem buildAkhgExec_wf {K : Type} [Datalog.LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (Datalog.GroundTuple × K)) : (buildAkhgExec es).table.WF := Datalog.buildSorted_wf es
theorem akhgExec_simulates_spec {K : Type} [Datalog.LawfulProvenanceSemiring K] [DecidableEq K]
    (es : Array (Datalog.GroundTuple × K)) (q : Datalog.GroundTuple) :
    Datalog.lookupFast (buildAkhgExec es).table q = Datalog.sumRows q es.toList := by
  have hwf := Datalog.buildSorted_wf es
  change Datalog.lookupFast (Datalog.buildSorted es) q = _
  rw [Datalog.lookupFast_eq_spec _ hwf]; unfold Datalog.lookupSpec
  rw [Datalog.lookupList_sum _ ((Datalog.table_wf_iff _).mp hwf), Datalog.buildSorted_sum]

/-! ## §3. Injective `Term ↔ SymId` Interning & $O(|R| \cdot |M| \log |M|)$ Guarded TGD Saturation -/
structure SymInternTable where
  terms : Array Term
  deriving DecidableEq, Repr
def nodupTerms : List Term → Bool
  | [] => true
  | t :: ts => (!ts.contains t) && nodupTerms ts
def SymInternTable.WF (tbl : SymInternTable) : Bool := nodupTerms tbl.terms.toList
def decodeSym (tbl : SymInternTable) (id : Datalog.SymId) : Option Term := tbl.terms[id]?
private def internTermGo (ts : Array Term) (t : Term) (idx : Nat) : Option Datalog.SymId :=
  if h : idx < ts.size then if ts[idx]'h = t then some idx else internTermGo ts t (idx + 1) else none
termination_by ts.size - idx
def internTerm (tbl : SymInternTable) (t : Term) : Option Datalog.SymId := internTermGo tbl.terms t 0
private theorem nodupTerms_iff_nodup : ∀ xs : List Term, nodupTerms xs = true ↔ xs.Nodup
  | [] => by simp [nodupTerms]
  | x :: xs => by
    have hnot : xs.contains x = false ↔ x ∉ xs := by cases h : xs.contains x <;> simp_all
    simp only [nodupTerms, Bool.and_eq_true, Bool.not_eq_true', hnot, nodupTerms_iff_nodup xs, List.nodup_cons]
private theorem internTermGo_some (ts : Array Term) (t : Term) :
    ∀ (idx id : Nat), internTermGo ts t idx = some id → ∃ h : id < ts.size, ts[id]'h = t ∧ idx ≤ id := by
  intro idx id hEq
  induction fuel : ts.size - idx using Nat.strongRecOn generalizing idx with
  | ind fuel ih =>
    unfold internTermGo at hEq; split at hEq
    · rename_i hlt; split at hEq
      · rename_i hteq; injection hEq with hid; subst hid; exact ⟨hlt, hteq, Nat.le_refl _⟩
      · obtain ⟨h, hteq, hle⟩ := ih (ts.size - (idx + 1)) (by omega) (idx + 1) hEq rfl; exact ⟨h, hteq, by omega⟩
    · cases hEq
theorem decodeSym_of_internTerm {tbl : SymInternTable} {t : Term} {id : Datalog.SymId}
    (h : internTerm tbl t = some id) : decodeSym tbl id = some t := by
  obtain ⟨hlt, hteq, _⟩ := internTermGo_some tbl.terms t 0 id h
  simp [decodeSym, Array.getElem?_eq_some_getElem tbl.terms id hlt, hteq]
theorem internTerm_injective {tbl : SymInternTable} {t₁ t₂ : Term} {id : Datalog.SymId}
    (h₁ : internTerm tbl t₁ = some id) (h₂ : internTerm tbl t₂ = some id) : t₁ = t₂ := by
  have hd₁ := decodeSym_of_internTerm h₁; have hd₂ := decodeSym_of_internTerm h₂
  rw [hd₁] at hd₂; exact Option.some.inj hd₂
private theorem internTermGo_of_getElem (ts : Array Term) (t : Term) (hNd : ts.toList.Nodup)
    {id : Nat} (hid : id < ts.size) (ht : ts[id]'hid = t) :
    ∀ (idx : Nat), idx ≤ id → (∀ j (hj : j < ts.size), j < idx → ts[j]'hj ≠ t) → internTermGo ts t idx = some id := by
  intro idx hle hprev
  induction fuel : ts.size - idx using Nat.strongRecOn generalizing idx with
  | ind fuel ih =>
    unfold internTermGo; have hlt : idx < ts.size := by omega
    rw [dite_eq_left hlt]
    by_cases heq : ts[idx]'hlt = t
    · rw [ite_eq_left heq]
      by_cases hlt' : idx < id
      · exact False.elim (((List.pairwise_iff_getElem.mp hNd) idx id (by simpa using hlt)
          (by simpa using hid) hlt') (by simpa [Array.getElem_toList, heq] using ht.symm))
      · have hidxEq : idx = id := by omega
        rw [hidxEq]
    · rw [ite_eq_right heq]; have hne : idx ≠ id := fun h => heq (h ▸ ht)
      exact ih (ts.size - (idx + 1)) (by omega) (idx + 1) (by omega)
        (fun j hj hjlt => if hj' : j = idx then hj' ▸ heq else hprev j hj (by omega)) rfl
theorem internTerm_of_decodeSym {tbl : SymInternTable} (hWf : tbl.WF = true)
    {id : Datalog.SymId} {t : Term} (h : decodeSym tbl id = some t) : internTerm tbl t = some id := by
  unfold decodeSym at h
  by_cases hid : id < tbl.terms.size
  · rw [Array.getElem?_eq_some_getElem tbl.terms id hid] at h; injection h with hteq
    exact internTermGo_of_getElem tbl.terms t ((nodupTerms_iff_nodup _).mp hWf) hid hteq 0 (Nat.zero_le _)
      (fun _ _ hj => by omega)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hid)] at h; cases h
def decodeSyms (tbl : SymInternTable) : List Datalog.SymId → Option (List Term)
  | [] => some []
  | id :: rest => match decodeSym tbl id, decodeSyms tbl rest with | some t, some ts => some (t :: ts) | _, _ => none
def internTerms (tbl : SymInternTable) : List Term → Option (List Datalog.SymId)
  | [] => some []
  | t :: rest => match internTerm tbl t, internTerms tbl rest with | some id, some ids => some (id :: ids) | _, _ => none
def decodeTuple (tbl : SymInternTable) (gt : Datalog.GroundTuple) : Option (Atom Term) :=
  match decodeSyms tbl gt.args.toList with | some ts => some { rel := gt.rel, args := ts } | none => none
def internAtom (tbl : SymInternTable) (a : Atom Term) : Option Datalog.GroundTuple :=
  match internTerms tbl a.args with | some ids => some { rel := a.rel, args := ids.toArray } | none => none
def decodeSortedFactSet {K : Type} [Datalog.ProvenanceSemiringOps K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) : FactSet :=
  M.entries.toList.filterMap fun e => decodeTuple tbl e.1
def tableSymsInBounds {K : Type} (tbl : SymInternTable) (M : Datalog.SortedKTable K) : Bool :=
  M.entries.all fun e => e.1.args.all (· < tbl.terms.size)
private theorem decodeSyms_of_internTerms (tbl : SymInternTable) :
    ∀ {ts : List Term} {ids : List Datalog.SymId}, internTerms tbl ts = some ids → decodeSyms tbl ids = some ts
  | [], _, h => by simp only [internTerms, Option.some.injEq] at h; subst h; rfl
  | t :: rest, _, h => by
    simp only [internTerms] at h
    cases h1 : internTerm tbl t <;> simp only [h1] at h
    · cases h
    · cases h2 : internTerms tbl rest <;> simp only [h2] at h
      · cases h
      · injection h with hids; subst hids; simp only [decodeSyms, decodeSym_of_internTerm h1, decodeSyms_of_internTerms tbl h2]
private theorem internTerms_of_decodeSyms {tbl : SymInternTable} (hWf : tbl.WF = true) :
    ∀ {ids : List Datalog.SymId} {ts : List Term}, decodeSyms tbl ids = some ts → internTerms tbl ts = some ids
  | [], _, h => by simp only [decodeSyms, Option.some.injEq] at h; subst h; rfl
  | id :: rest, _, h => by
    simp only [decodeSyms] at h
    cases h1 : decodeSym tbl id <;> simp only [h1] at h
    · cases h
    · cases h2 : decodeSyms tbl rest <;> simp only [h2] at h
      · cases h
      · injection h with hts; subst hts; simp only [internTerms, internTerm_of_decodeSym hWf h1, internTerms_of_decodeSyms hWf h2]
private theorem decodeSyms_some_of_inBounds (tbl : SymInternTable) :
    ∀ ids : List Datalog.SymId, (∀ id ∈ ids, id < tbl.terms.size) → ∃ ts, decodeSyms tbl ids = some ts
  | [], _ => ⟨[], rfl⟩
  | id :: rest, hB => by
    have h1 := hB id (.head _)
    obtain ⟨ts, hts⟩ := decodeSyms_some_of_inBounds tbl rest (fun x hx => hB x (.tail _ hx))
    exact ⟨tbl.terms[id]'h1 :: ts, by simp only [decodeSyms, decodeSym, Array.getElem?_eq_some_getElem tbl.terms id h1, hts]⟩
private theorem decodeTuple_some_of_inBounds {K : Type} {tbl : SymInternTable} {M : Datalog.SortedKTable K}
    (hBounds : tableSymsInBounds tbl M = true) {e : Datalog.GroundTuple × K} (he : e ∈ M.entries) :
    ∃ a, decodeTuple tbl e.1 = some a := by
  have hArgs : ∀ id ∈ e.1.args.toList, id < tbl.terms.size := fun id hid =>
    of_decide_eq_true ((Array.all_eq_true_iff_forall_mem.mp ((Array.all_eq_true_iff_forall_mem.mp hBounds) e he))
      id (Array.mem_toList_iff.mp hid))
  obtain ⟨ts, hts⟩ := decodeSyms_some_of_inBounds tbl e.1.args.toList hArgs
  exact ⟨{ rel := e.1.rel, args := ts }, by simp [decodeTuple, hts]⟩
private theorem decodeTuple_of_internAtom (tbl : SymInternTable) {a : Atom Term} {gt : Datalog.GroundTuple}
    (h : internAtom tbl a = some gt) : decodeTuple tbl gt = some a := by
  simp only [internAtom] at h; cases h1 : internTerms tbl a.args <;> simp only [h1] at h
  · cases h
  · injection h with hgt; subst hgt; cases a; simp only [decodeTuple, decodeSyms_of_internTerms tbl h1]
private theorem internAtom_of_decodeTuple {tbl : SymInternTable} (hWf : tbl.WF = true)
    {gt : Datalog.GroundTuple} {a : Atom Term} (h : decodeTuple tbl gt = some a) : internAtom tbl a = some gt := by
  simp only [decodeTuple] at h; cases h1 : decodeSyms tbl gt.args.toList <;> simp only [h1] at h
  · cases h
  · injection h with ha; subst ha; cases gt; simp only [internAtom, internTerms_of_decodeSyms hWf h1, Array.toArray_toList]
def lowerBoundRelGo {K : Type} (es : Array (Datalog.GroundTuple × K)) (rel : Datalog.RelId) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < es.size then
        if es[mid].1.rel < rel then lowerBoundRelGo es rel fuel (mid + 1) hi else lowerBoundRelGo es rel fuel lo mid
      else lo
    else lo
def lowerBoundRel {K : Type} (M : Datalog.SortedKTable K) (rel : Datalog.RelId) : Nat :=
  lowerBoundRelGo M.entries rel (M.entries.size + 1) 0 M.entries.size
def upperBoundRel {K : Type} (M : Datalog.SortedKTable K) (rel : Datalog.RelId) : Nat := lowerBoundRel M (rel + 1)
private theorem rel_le_of_tupleLt {a b : Datalog.GroundTuple} (h : Datalog.TupleLt a b) : a.rel ≤ b.rel := by
  unfold Datalog.TupleLt Datalog.tupleCmp compareLex compareOn at h
  cases hc : compare a.rel b.rel with
  | lt => exact Nat.le_of_lt (Nat.compare_eq_lt.mp hc)
  | eq => exact Nat.le_of_eq (Nat.compare_eq_eq.mp hc)
  | gt => simp [hc] at h
private theorem entries_rel_mono {K : Type} [Datalog.ProvenanceSemiringOps K] {M : Datalog.SortedKTable K}
    (hM : M.WF) {i j : Nat} (hi : i < M.entries.size) (hj : j < M.entries.size) (hle : i ≤ j) :
    M.entries[i].1.rel ≤ M.entries[j].1.rel := by
  by_cases hlt : i < j
  · exact rel_le_of_tupleLt (hM.1 ⟨i, hi⟩ ⟨j, hj⟩ hlt)
  · have heq : i = j := by omega
    subst heq; exact Nat.le_refl _
private theorem lowerBoundRelGo_spec {K : Type} [Datalog.ProvenanceSemiringOps K]
    {M : Datalog.SortedKTable K} (hM : M.WF) (rel : Datalog.RelId) :
    ∀ (fuel lo hi : Nat), lo ≤ hi → hi ≤ M.entries.size → hi - lo < fuel →
      (∀ i (hi' : i < M.entries.size), i < lo → M.entries[i].1.rel < rel) →
      (∀ i (hi' : i < M.entries.size), hi ≤ i → rel ≤ M.entries[i].1.rel) →
      let k := lowerBoundRelGo M.entries rel fuel lo hi
      k ≤ M.entries.size ∧
      (∀ i (hi' : i < M.entries.size), i < k → M.entries[i].1.rel < rel) ∧
      (∀ i (hi' : i < M.entries.size), k ≤ i → rel ≤ M.entries[i].1.rel)
  | 0, _, _, _, _, hfuel, _, _ => by omega
  | fuel + 1, lo, hi, hlohi, hhi, hfuel, hLo, hHi => by
    simp only [lowerBoundRelGo]
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt]; have hmid : (lo + hi) / 2 < M.entries.size := by omega
      rw [dite_eq_left hmid]
      by_cases hrel : M.entries[(lo + hi) / 2].1.rel < rel
      · rw [ite_eq_left hrel]
        exact lowerBoundRelGo_spec hM rel fuel ((lo + hi) / 2 + 1) hi (by omega) hhi (by omega)
          (fun i hi' hilt => Nat.lt_of_le_of_lt (entries_rel_mono hM hi' hmid (by omega)) hrel) hHi
      · rw [ite_eq_right hrel]
        exact lowerBoundRelGo_spec hM rel fuel lo ((lo + hi) / 2) (by omega) (by omega) (by omega) hLo
          (fun i hi' hige => Nat.le_trans (Nat.le_of_not_lt hrel) (entries_rel_mono hM hmid hi' hige))
    · rw [ite_eq_right hlt]; have heq : lo = hi := by omega
      subst heq; exact ⟨hhi, hLo, hHi⟩
theorem mem_rel_slice_iff {K : Type} [Datalog.ProvenanceSemiringOps K] {M : Datalog.SortedKTable K}
    (hM : M.WF) (rel : Datalog.RelId) {i : Nat} (hi : i < M.entries.size) :
    M.entries[i].1.rel = rel ↔ lowerBoundRel M rel ≤ i ∧ i < upperBoundRel M rel := by
  have hLo := lowerBoundRelGo_spec hM rel (M.entries.size + 1) 0 M.entries.size
    (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
  have hHi := lowerBoundRelGo_spec hM (rel + 1) (M.entries.size + 1) 0 M.entries.size
    (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
  dsimp only at hLo hHi; unfold upperBoundRel lowerBoundRel
  constructor
  · intro heq; refine ⟨?_, ?_⟩
    · by_cases hlt : i < lowerBoundRelGo M.entries rel (M.entries.size + 1) 0 M.entries.size
      · have h1 := hLo.2.1 i hi hlt; rw [heq] at h1; exact False.elim (Nat.lt_irrefl _ h1)
      · omega
    · by_cases hge : lowerBoundRelGo M.entries (rel + 1) (M.entries.size + 1) 0 M.entries.size ≤ i
      · have h2 := hHi.2.2 i hi hge; rw [heq] at h2; exact False.elim (Nat.not_succ_le_self _ h2)
      · omega
  · rintro ⟨h1, h2⟩; exact Nat.le_antisymm (Nat.le_of_lt_succ (hHi.2.1 i hi h2)) (hLo.2.2 i hi h1)
private theorem upperBoundRel_le_size {K : Type} [Datalog.ProvenanceSemiringOps K]
    {M : Datalog.SortedKTable K} (hM : M.WF) (rel : Datalog.RelId) : upperBoundRel M rel ≤ M.entries.size :=
  (lowerBoundRelGo_spec hM (rel + 1) (M.entries.size + 1) 0 M.entries.size
    (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)).1
def IsGuardedRule (r : TgdRule) : Bool :=
  WfRule r && match r.body with
  | [] => false
  | g :: _ => (varsOfPatAtoms r.body).all (fun v => (varsOfPatAtom g).contains v) &&
    match r.head with | [] => true | h0 :: _ => r.existVars.all fun y => (varsOfPatAtom h0).contains y
def checkAtomInTableFast {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (a : Atom Term) : Bool :=
  match internAtom tbl a with | none => false | some gt => Datalog.lookupFast M gt != ProvenanceSemiringOps.zero
def checkPatAtomInTableFast {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (σ : Subst Term) (pa : PatAtom) : Bool :=
  match evalPatAtom Term.const σ pa with | none => false | some a => checkAtomInTableFast tbl M a
private def allInRange (lo hi : Nat) (p : Nat → Bool) : Bool :=
  if lo < hi then p lo && allInRange (lo + 1) hi p else true
termination_by hi - lo
private def anyInRange (lo hi : Nat) (p : Nat → Bool) : Bool :=
  if lo < hi then p lo || anyInRange (lo + 1) hi p else false
termination_by hi - lo
private theorem allInRange_eq_true (lo hi : Nat) (p : Nat → Bool) :
    allInRange lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  induction fuel : hi - lo using Nat.strongRecOn generalizing lo with
  | ind fuel ih =>
    unfold allInRange
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt, Bool.and_eq_true, ih (hi - (lo + 1)) (by omega) (lo + 1) rfl]
      exact ⟨fun ⟨h0, hr⟩ i h1 h2 => if he : i = lo then he ▸ h0 else hr i (by omega) h2,
        fun hall => ⟨hall lo (Nat.le_refl _) hlt, fun i h1 h2 => hall i (by omega) h2⟩⟩
    · rw [ite_eq_right hlt]; exact ⟨fun _ _ h1 h2 => by omega, fun _ => rfl⟩
private theorem anyInRange_eq_true (lo hi : Nat) (p : Nat → Bool) :
    anyInRange lo hi p = true ↔ ∃ i, lo ≤ i ∧ i < hi ∧ p i = true := by
  induction fuel : hi - lo using Nat.strongRecOn generalizing lo with
  | ind fuel ih =>
    unfold anyInRange
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt, Bool.or_eq_true, ih (hi - (lo + 1)) (by omega) (lo + 1) rfl]
      exact ⟨fun h => h.elim (fun h0 => ⟨lo, Nat.le_refl _, hlt, h0⟩) (fun ⟨i, h1, h2, hp⟩ => ⟨i, by omega, h2, hp⟩),
        fun ⟨i, h1, h2, hp⟩ => if he : i = lo then Or.inl (he ▸ hp) else Or.inr ⟨i, by omega, h2, hp⟩⟩
    · rw [ite_eq_right hlt]; exact ⟨(fun h => nomatch h), fun ⟨_, h1, h2, _⟩ => by omega⟩
def checkGuardedHeadFast {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (r : TgdRule) (σ : Subst Term) : Bool :=
  let σF := frontierSubst r.frontierVars σ
  match r.head with
  | [] => true
  | h0 :: restHead =>
    anyInRange (lowerBoundRel M h0.rel) (upperBoundRel M h0.rel) fun j =>
      match M.entries[j]? with
      | none => false
      | some e => match decodeTuple tbl e.1 with
        | none => false
        | some ha => match matchPatAtom Term.const σF h0 ha with
          | none => false
          | some σ₁ => restHead.all (checkPatAtomInTableFast tbl M σ₁)
def checkGuardedRuleFast {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (r : TgdRule) : Bool :=
  match r.body with
  | [] => false
  | g :: restBody =>
    allInRange (lowerBoundRel M g.rel) (upperBoundRel M g.rel) fun i =>
      match M.entries[i]? with
      | none => false
      | some e => match decodeTuple tbl e.1 with
        | none => false
        | some a => match matchPatAtom Term.const [] g a with
          | none => true
          | some σ₀ => if restBody.all (checkPatAtomInTableFast tbl M σ₀) then checkGuardedHeadFast tbl M r σ₀ else true
def checkGuardedSaturationFast {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (rules : Array TgdRule) : Bool :=
  rules.all (checkGuardedRuleFast tbl M)
private theorem rel_eq_of_matchPatAtom {σ σ' : Subst Term} {pa : PatAtom} {a : Atom Term}
    (hm : matchPatAtom Term.const σ pa a = some σ') : a.rel = pa.rel := by
  unfold matchPatAtom at hm; split at hm
  · rename_i hr; exact hr.symm
  · cases hm
private theorem checkAtomInTableFast_eq_true_iff {K : Type} [Datalog.ProvenanceSemiringOps K]
    [DecidableEq K] {tbl : SymInternTable} {M : Datalog.SortedKTable K} (hTbl : tbl.WF = true)
    (hM : M.WF) (a : Atom Term) : checkAtomInTableFast tbl M a = true ↔ a ∈ decodeSortedFactSet tbl M := by
  unfold checkAtomInTableFast decodeSortedFactSet; constructor
  · intro h; cases hInt : internAtom tbl a with
    | none => simp [hInt] at h
    | some gt =>
      rw [hInt] at h
      have hNe : Datalog.lookupFast M gt ≠ ProvenanceSemiringOps.zero := by simpa [bne_iff_ne] using h
      cases hs : Datalog.search M.entries gt (M.entries.size + 1) 0 M.entries.size with
      | none => simp [Datalog.lookupFast, hs] at hNe
      | some i =>
        obtain ⟨hi, hiEq⟩ := Datalog.search_some M.entries gt _ _ _ _ hs
        rw [List.mem_filterMap]; exact ⟨M.entries[i], Array.getElem_mem_toList hi, hiEq ▸ decodeTuple_of_internAtom tbl hInt⟩
  · intro hMem; rw [List.mem_filterMap] at hMem; obtain ⟨e, heMem, hDec⟩ := hMem
    rw [internAtom_of_decodeTuple hTbl hDec]
    obtain ⟨i, hi, heEq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp heMem)
    have hNe : Datalog.lookupFast M e.1 ≠ ProvenanceSemiringOps.zero := fun hZ =>
      Datalog.absent_of_lookupFast M hM e.1 hZ ⟨i, hi⟩ (congrArg Prod.fst heEq)
    simpa [bne_iff_ne] using hNe
private theorem matchPatTerm_eq_self_of_eval (σ σ' : Subst Term) (pt : PatTerm) (d d' : Term)
    (hev : evalPatTerm Term.const σ pt = some d) (hm : matchPatTerm Term.const σ pt d' = some σ') :
    d' = d ∧ σ' = σ := by
  cases pt with
  | const _ =>
    simp only [evalPatTerm, Option.some.injEq] at hev; simp only [matchPatTerm] at hm; split at hm
    · rename_i hc; injection hm with hσ; exact ⟨hc.symm.trans hev, hσ.symm⟩
    · cases hm
  | var _ =>
    simp only [evalPatTerm] at hev; simp only [matchPatTerm, hev] at hm; split at hm
    · rename_i hd; injection hm with hσ; exact ⟨hd.symm, hσ.symm⟩
    · cases hm
private theorem matchPatArgs_eq_self_of_eval (σ σ' : Subst Term) :
    ∀ (pts : List PatTerm) (ds ds' : List Term),
      evalPatArgs Term.const σ pts = some ds → matchPatArgs Term.const σ pts ds' = some σ' → ds' = ds ∧ σ' = σ
  | [], _, [], hev, hm => by injection hev with hds; injection hm with hσ; exact ⟨hds, hσ.symm⟩
  | [], _, _ :: _, _, hm => by cases hm
  | _ :: _, _, [], _, hm => by cases hm
  | pt :: rest, _, d' :: restD', hev, hm => by
    simp only [evalPatArgs] at hev
    cases h1 : evalPatTerm Term.const σ pt with
    | none => simp [h1] at hev
    | some d => cases h2 : evalPatArgs Term.const σ rest with
      | none => simp [h1, h2] at hev
      | some restD =>
        simp only [h1, h2, Option.some.injEq] at hev; subst hev; simp only [matchPatArgs] at hm
        cases hm1 : matchPatTerm Term.const σ pt d' with
        | none => simp [hm1] at hm
        | some σ₁ =>
          simp only [hm1] at hm
          obtain ⟨hdEq, hσ1⟩ := matchPatTerm_eq_self_of_eval σ σ₁ pt d d' h1 hm1
          subst d'; subst σ₁
          obtain ⟨hrEq, hσ'⟩ := matchPatArgs_eq_self_of_eval σ σ' rest restD restD' h2 hm
          exact ⟨congrArg (d :: ·) hrEq, hσ'⟩
private theorem matchPatAtom_eq_self_of_eval (σ σ' : Subst Term) (pa : PatAtom) (b a : Atom Term)
    (hev : evalPatAtom Term.const σ pa = some b) (hm : matchPatAtom Term.const σ pa a = some σ') : a = b ∧ σ' = σ := by
  simp only [evalPatAtom] at hev; cases hargs : evalPatArgs Term.const σ pa.args with
  | none => simp [hargs] at hev
  | some ds =>
    simp only [hargs, Option.some.injEq] at hev; subst hev; simp only [matchPatAtom] at hm; split at hm
    · rename_i hrel; obtain ⟨haEq, hσEq⟩ := matchPatArgs_eq_self_of_eval σ σ' pa.args ds a.args hargs hm
      cases a; simp only at hrel haEq; subst hrel; subst haEq; exact ⟨rfl, hσEq⟩
    · cases hm
private theorem matchPatArgs_self_of_eval (σ : Subst Term) :
    ∀ (pts : List PatTerm) (ds : List Term), evalPatArgs Term.const σ pts = some ds → matchPatArgs Term.const σ pts ds = some σ
  | [], _, hev => by injection hev with hds; subst hds; rfl
  | pt :: rest, _, hev => by
    simp only [evalPatArgs] at hev; cases h1 : evalPatTerm Term.const σ pt with
    | none => simp [h1] at hev
    | some d => cases h2 : evalPatArgs Term.const σ rest with
      | none => simp [h1, h2] at hev
      | some restD =>
        simp only [h1, h2, Option.some.injEq] at hev; subst hev
        have hm1 : matchPatTerm Term.const σ pt d = some σ := by
          cases pt with
          | const _ => simp only [evalPatTerm, Option.some.injEq] at h1; simp [matchPatTerm, h1]
          | var _ => simp only [evalPatTerm] at h1; simp [matchPatTerm, h1]
        simp [matchPatArgs, hm1, matchPatArgs_self_of_eval σ rest restD h2]
private theorem matchPatAtom_self_of_eval (σ : Subst Term) (pa : PatAtom) (b : Atom Term)
    (hev : evalPatAtom Term.const σ pa = some b) : matchPatAtom Term.const σ pa b = some σ := by
  simp only [evalPatAtom] at hev; cases hargs : evalPatArgs Term.const σ pa.args with
  | none => simp [hargs] at hev
  | some ds => simp only [hargs, Option.some.injEq] at hev; subst hev; simp [matchPatAtom, matchPatArgs_self_of_eval σ pa.args ds hargs]
private theorem evalPatArgs_some_of_all_bound (σ : Subst Term) :
    ∀ (pts : List PatTerm),
      (∀ v ∈ pts.filterMap (fun pt => match pt with | .var u => some u | .const _ => none),
        ∃ d, lookupSubst σ v = some d) → ∃ ds, evalPatArgs Term.const σ pts = some ds
  | [], _ => ⟨[], rfl⟩
  | pt :: rest, hB => by
    have h1 : ∃ d, evalPatTerm Term.const σ pt = some d := by
      cases pt with | const c => exact ⟨.const c, rfl⟩ | var v => exact hB v (by simp)
    obtain ⟨d, hd⟩ := h1; obtain ⟨ds, hds⟩ := evalPatArgs_some_of_all_bound σ rest (fun v hv => hB v (by cases pt <;> simp [hv]))
    exact ⟨d :: ds, by simp [evalPatArgs, hd, hds]⟩
private theorem ground_matchPatAtoms_iff {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    {tbl : SymInternTable} {M : Datalog.SortedKTable K} (hTbl : tbl.WF = true) (hM : M.WF) (σ : Subst Term) :
    ∀ (pas : List PatAtom),
      (∀ v ∈ varsOfPatAtoms pas, ∃ d, lookupSubst σ v = some d) →
      (∀ σ' ∈ matchPatAtoms Term.const σ pas (decodeSortedFactSet tbl M), σ' = σ) ∧
      ((!(matchPatAtoms Term.const σ pas (decodeSortedFactSet tbl M)).isEmpty) = true ↔
        pas.all (checkPatAtomInTableFast tbl M σ) = true)
  | [], _ => ⟨fun _ h => List.mem_singleton.mp h, by simp [matchPatAtoms]⟩
  | pa :: rest, hB => by
    obtain ⟨ds, hds⟩ := evalPatArgs_some_of_all_bound σ pa.args (fun v hv => hB v (List.mem_flatMap.mpr ⟨pa, .head _, hv⟩))
    have hevB : evalPatAtom Term.const σ pa = some { rel := pa.rel, args := ds } := by simp [evalPatAtom, hds]
    let b : Atom Term := { rel := pa.rel, args := ds }
    have hBrest : ∀ v ∈ varsOfPatAtoms rest, ∃ d, lookupSubst σ v = some d := fun v hv => by
      obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.mp hv; exact hB v (List.mem_flatMap.mpr ⟨p, .tail _ hp, hvp⟩)
    obtain ⟨ihEq, ihNE⟩ := ground_matchPatAtoms_iff hTbl hM σ rest hBrest
    refine ⟨?_, ?_⟩
    · intro σ' hMem; simp only [matchPatAtoms, List.mem_flatMap] at hMem; obtain ⟨a, _, hmRest⟩ := hMem
      cases hm1 : matchPatAtom Term.const σ pa a with
      | none => simp [hm1] at hmRest
      | some σ₁ =>
        simp only [hm1] at hmRest
        obtain ⟨_, hσ1⟩ := matchPatAtom_eq_self_of_eval σ σ₁ pa b a hevB hm1; subst σ₁; exact ihEq σ' hmRest
    · simp only [List.all_cons, Bool.and_eq_true]
      have hCheckPa : checkPatAtomInTableFast tbl M σ pa = true ↔ b ∈ decodeSortedFactSet tbl M := by
        simp [checkPatAtomInTableFast, hevB, b, checkAtomInTableFast_eq_true_iff hTbl hM]
      constructor
      · intro hNE; cases hMs : matchPatAtoms Term.const σ (pa :: rest) (decodeSortedFactSet tbl M) with
        | nil => simp [hMs] at hNE
        | cons σ' _ =>
          have hMem : σ' ∈ matchPatAtoms Term.const σ (pa :: rest) (decodeSortedFactSet tbl M) := hMs ▸ .head _
          simp only [matchPatAtoms, List.mem_flatMap] at hMem; obtain ⟨a, haMem, hmRest⟩ := hMem
          cases hm1 : matchPatAtom Term.const σ pa a with
          | none => simp [hm1] at hmRest
          | some σ₁ =>
            simp only [hm1] at hmRest
            obtain ⟨hab, hσ1⟩ := matchPatAtom_eq_self_of_eval σ σ₁ pa b a hevB hm1; subst a; subst σ₁
            refine ⟨hCheckPa.mpr haMem, ihNE.mp ?_⟩
            cases hRs : matchPatAtoms Term.const σ rest (decodeSortedFactSet tbl M) with
            | nil => rw [hRs] at hmRest; cases hmRest
            | cons _ _ => rfl
      · rintro ⟨hPaOk, hRestOk⟩; have hbMem := hCheckPa.mp hPaOk; have hRestNE := ihNE.mpr hRestOk
        cases hRs : matchPatAtoms Term.const σ rest (decodeSortedFactSet tbl M) with
        | nil => simp [hRs] at hRestNE
        | cons σ' _ =>
          have hσ'In : σ' ∈ matchPatAtoms Term.const σ (pa :: rest) (decodeSortedFactSet tbl M) := by
            simp only [matchPatAtoms, List.mem_flatMap]
            exact ⟨b, hbMem, by simp only [matchPatAtom_self_of_eval σ pa b hevB, hRs]; exact .head _⟩
          cases hMs : matchPatAtoms Term.const σ (pa :: rest) (decodeSortedFactSet tbl M) with
          | nil => rw [hMs] at hσ'In; cases hσ'In
          | cons _ _ => rfl
private theorem mem_decode_rel_iff {K : Type} [Datalog.ProvenanceSemiringOps K]
    {tbl : SymInternTable} {M : Datalog.SortedKTable K} (hM : M.WF) (rel : Datalog.RelId)
    (a : Atom Term) (hRel : a.rel = rel) :
    a ∈ decodeSortedFactSet tbl M ↔
      ∃ idx, lowerBoundRel M rel ≤ idx ∧ idx < upperBoundRel M rel ∧
        ∃ e, M.entries[idx]? = some e ∧ decodeTuple tbl e.1 = some a := by
  constructor
  · intro haMem; rw [decodeSortedFactSet, List.mem_filterMap] at haMem; obtain ⟨e, heMem, hDec⟩ := haMem
    obtain ⟨idx, hidx, heEq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp heMem)
    have heRel : M.entries[idx].1.rel = rel := by
      have hDRel : e.1.rel = a.rel := by
        unfold decodeTuple at hDec; cases hs : decodeSyms tbl e.1.args.toList <;> simp [hs] at hDec; rw [← hDec]
      rw [heEq, hDRel, hRel]
    obtain ⟨hLo, hHi⟩ := (mem_rel_slice_iff hM rel hidx).mp heRel
    exact ⟨idx, hLo, hHi, e, by rw [Array.getElem?_eq_some_getElem M.entries idx hidx, heEq], hDec⟩
  · rintro ⟨idx, _, hHi, e, hGet, hDec⟩
    have hidx : idx < M.entries.size := Nat.lt_of_lt_of_le hHi (upperBoundRel_le_size hM rel)
    have heEq : M.entries[idx] = e := by rw [Array.getElem?_eq_some_getElem M.entries idx hidx] at hGet; exact Option.some.inj hGet
    rw [decodeSortedFactSet, List.mem_filterMap]; exact ⟨e, heEq ▸ Array.getElem_mem_toList hidx, hDec⟩
private theorem bound_of_matchPatAtom (σ σ' : Subst Term) (pa : PatAtom) (a : Atom Term)
    (hm : matchPatAtom Term.const σ pa a = some σ') : ∀ v ∈ varsOfPatAtom pa, ∃ d, lookupSubst σ' v = some d := by
  have ⟨_, hev⟩ := matchPatAtom_sound Term.const σ σ' pa a hm
  intro v hv; unfold evalPatAtom at hev; cases hargs : evalPatArgs Term.const σ' pa.args <;> simp only [hargs] at hev
  · cases hev
  · exact SkolemChaseCore.bound_of_mem_varsOfPatArgs Term.const σ' pa.args _ v hv hargs
private theorem checkGuardedHeadFast_iff {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    {tbl : SymInternTable} {M : Datalog.SortedKTable K} (hTbl : tbl.WF = true) (hM : M.WF)
    {r : TgdRule} (hG : IsGuardedRule r = true) {σ : Subst Term}
    (hFrontB : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ x = some d) :
    checkGuardedHeadFast tbl M r σ = true ↔ isSatisfied Term.const r σ (decodeSortedFactSet tbl M) = true := by
  have hWf := (Bool.and_eq_true_iff.mp hG).1
  have hHeadVars : ∀ v ∈ varsOfPatAtoms r.head, v ∈ r.frontierVars ∨ v ∈ r.existVars := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hWf; exact hWf.2
  obtain ⟨tTuple, hExt⟩ := SkolemChaseCore.extractFrontierTuple_some_of_all_bound r.frontierVars σ hFrontB
  have hσFBound : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst (frontierSubst r.frontierVars σ) x = some d := fun x hx => by
    obtain ⟨d, hd⟩ := hFrontB x hx
    exact ⟨d, by simp only [frontierSubst, hExt]; rw [lookupSubst_zip_of_extract r.frontierVars σ tTuple hExt x hx]; exact hd⟩
  cases hHead : r.head with
  | nil => simp [checkGuardedHeadFast, isSatisfied, hHead, matchPatAtoms]
  | cons h0 restHead =>
    have hExistInH0 : ∀ y ∈ r.existVars, y ∈ varsOfPatAtom h0 := by
      simp only [IsGuardedRule, Bool.and_eq_true] at hG
      cases hBody : r.body with
      | nil => simp [hBody] at hG
      | cons g _ => simp only [hBody, hHead, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hG; exact hG.2.2
    have mkB1 : ∀ ha σ₁, matchPatAtom Term.const (frontierSubst r.frontierVars σ) h0 ha = some σ₁ →
        ∀ v ∈ varsOfPatAtoms restHead, ∃ d, lookupSubst σ₁ v = some d := fun ha σ₁ hm0 v hv => by
      have hExt1 := (matchPatAtom_sound Term.const _ σ₁ h0 ha hm0).1
      rcases hHeadVars v (by rw [hHead]; exact List.mem_append_right _ hv) with hvf | hve
      · obtain ⟨d, hd⟩ := hσFBound v hvf; exact ⟨d, hExt1 v d hd⟩
      · exact bound_of_matchPatAtom _ σ₁ h0 ha hm0 v (hExistInH0 v hve)
    simp only [checkGuardedHeadFast, hHead, anyInRange_eq_true]; constructor
    · rintro ⟨j, hLo, hHi, hjOk⟩
      cases hGet : M.entries[j]? with
      | none => simp [hGet] at hjOk
      | some e =>
        simp only [hGet] at hjOk; cases hDec : decodeTuple tbl e.1 with
        | none => simp [hDec] at hjOk
        | some ha =>
          simp only [hDec] at hjOk; cases hm0 : matchPatAtom Term.const (frontierSubst r.frontierVars σ) h0 ha with
          | none => simp [hm0] at hjOk
          | some σ₁ =>
            simp only [hm0] at hjOk
            have haMem := (mem_decode_rel_iff hM h0.rel ha (rel_eq_of_matchPatAtom hm0)).mpr ⟨j, hLo, hHi, e, hGet, hDec⟩
            have hRestNE := (ground_matchPatAtoms_iff hTbl hM σ₁ restHead (mkB1 ha σ₁ hm0)).2.mpr hjOk
            cases hRs : matchPatAtoms Term.const σ₁ restHead (decodeSortedFactSet tbl M) with
            | nil => simp [hRs] at hRestNE
            | cons τ' _ =>
              have hτ'In : τ' ∈ matchPatAtoms Term.const (frontierSubst r.frontierVars σ) (h0 :: restHead)
                  (decodeSortedFactSet tbl M) := by
                simp only [matchPatAtoms, List.mem_flatMap]; exact ⟨ha, haMem, by simp only [hm0, hRs]; exact .head _⟩
              unfold isSatisfied; rw [hHead]
              cases hMs : matchPatAtoms Term.const (frontierSubst r.frontierVars σ) (h0 :: restHead)
                  (decodeSortedFactSet tbl M) with
              | nil => rw [hMs] at hτ'In; cases hτ'In
              | cons _ _ => rfl
    · intro hSat; unfold isSatisfied at hSat; rw [hHead] at hSat
      cases hMs : matchPatAtoms Term.const (frontierSubst r.frontierVars σ) (h0 :: restHead)
          (decodeSortedFactSet tbl M) with
      | nil => simp [hMs] at hSat
      | cons τ' _ =>
        have hτ'In : τ' ∈ matchPatAtoms Term.const (frontierSubst r.frontierVars σ) (h0 :: restHead)
            (decodeSortedFactSet tbl M) := hMs ▸ .head _
        simp only [matchPatAtoms, List.mem_flatMap] at hτ'In; obtain ⟨ha, haMem, hmRest⟩ := hτ'In
        cases hm0 : matchPatAtom Term.const (frontierSubst r.frontierVars σ) h0 ha with
        | none => simp [hm0] at hmRest
        | some σ₁ =>
          simp only [hm0] at hmRest
          obtain ⟨j, hLo, hHi, e, hGet, hDec⟩ := (mem_decode_rel_iff hM h0.rel ha (rel_eq_of_matchPatAtom hm0)).mp haMem
          refine ⟨j, hLo, hHi, ?_⟩; simp only [hGet, hDec, hm0]
          refine (ground_matchPatAtoms_iff hTbl hM σ₁ restHead (mkB1 ha σ₁ hm0)).2.mp ?_
          cases hRs : matchPatAtoms Term.const σ₁ restHead (decodeSortedFactSet tbl M) with
          | nil => rw [hRs] at hmRest; cases hmRest
          | cons _ _ => rfl
private theorem checkGuardedRuleFast_eq_spec {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    {tbl : SymInternTable} {M : Datalog.SortedKTable K} (hTbl : tbl.WF = true) (hM : M.WF)
    (hBounds : tableSymsInBounds tbl M = true) {r : TgdRule} (hG : IsGuardedRule r = true) :
    checkGuardedRuleFast tbl M r = ruleSatisfiedSpec r (decodeSortedFactSet tbl M) := by
  apply Bool.eq_iff_iff.mpr
  have hWf := (Bool.and_eq_true_iff.mp hG).1
  have hFrontInBody : ∀ x ∈ r.frontierVars, x ∈ varsOfPatAtoms r.body := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hWf; exact hWf.1.2
  cases hBody : r.body with
  | nil => simp [IsGuardedRule, hBody] at hG
  | cons g restBody =>
    have hBodyInG : ∀ v ∈ varsOfPatAtoms r.body, v ∈ varsOfPatAtom g := by
      have hG' := hG; simp only [IsGuardedRule, hBody, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hG'
      exact fun v hv => hG'.2.1 v (by rwa [← hBody])
    rw [checkGuardedRuleFast, hBody, allInRange_eq_true, ruleSatisfiedSpec, hBody, List.all_eq_true]
    constructor
    · intro hFast σ hσMem; simp only [matchPatAtoms, List.mem_flatMap] at hσMem; obtain ⟨a, haMem, hmRest⟩ := hσMem
      cases hmG : matchPatAtom Term.const [] g a with
      | none => simp [hmG] at hmRest
      | some σ₀ =>
        simp only [hmG] at hmRest
        have hBrest : ∀ v ∈ varsOfPatAtoms restBody, ∃ d, lookupSubst σ₀ v = some d := fun v hv =>
          bound_of_matchPatAtom [] σ₀ g a hmG v (hBodyInG v (by rw [hBody]; exact List.mem_append_right _ hv))
        obtain ⟨hEqσ, hRestIff⟩ := ground_matchPatAtoms_iff hTbl hM σ₀ restBody hBrest
        have hσEq : σ = σ₀ := hEqσ σ hmRest; subst σ
        have hRestOk : restBody.all (checkPatAtomInTableFast tbl M σ₀) = true := by
          apply hRestIff.mp
          cases hRs : matchPatAtoms Term.const σ₀ restBody (decodeSortedFactSet tbl M) with
          | nil => rw [hRs] at hmRest; cases hmRest
          | cons _ _ => rfl
        obtain ⟨idx, hLo, hHi, e, hGet, hDec⟩ := (mem_decode_rel_iff hM g.rel a (rel_eq_of_matchPatAtom hmG)).mp haMem
        have hIdxOk := hFast idx hLo hHi
        simp only [hGet, hDec, hmG, hRestOk, ↓reduceIte] at hIdxOk
        have hFrontB : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ₀ x = some d :=
          fun x hx => bound_of_matchPatAtom [] σ₀ g a hmG x (hBodyInG x (hFrontInBody x hx))
        exact (checkGuardedHeadFast_iff hTbl hM hG hFrontB).mp hIdxOk
    · intro hSpec idx hLo hHi
      have hidx : idx < M.entries.size := Nat.lt_of_lt_of_le hHi (upperBoundRel_le_size hM g.rel)
      have hGet : M.entries[idx]? = some M.entries[idx] := Array.getElem?_eq_some_getElem M.entries idx hidx
      obtain ⟨a, hDec⟩ := decodeTuple_some_of_inBounds hBounds (Array.getElem_mem hidx)
      simp only [hGet, hDec]
      cases hmG : matchPatAtom Term.const [] g a with
      | none => rfl
      | some σ₀ =>
        dsimp only
        by_cases hRestOk : restBody.all (checkPatAtomInTableFast tbl M σ₀) = true
        · rw [ite_eq_left hRestOk]
          have hBrest : ∀ v ∈ varsOfPatAtoms restBody, ∃ d, lookupSubst σ₀ v = some d := fun v hv =>
            bound_of_matchPatAtom [] σ₀ g a hmG v (hBodyInG v (by rw [hBody]; exact List.mem_append_right _ hv))
          have hRestNE := (ground_matchPatAtoms_iff hTbl hM σ₀ restBody hBrest).2.mpr hRestOk
          cases hRs : matchPatAtoms Term.const σ₀ restBody (decodeSortedFactSet tbl M) with
          | nil => simp [hRs] at hRestNE
          | cons σ' _ =>
            have hσ'In : σ' ∈ matchPatAtoms Term.const σ₀ restBody (decodeSortedFactSet tbl M) := hRs ▸ .head _
            have hσ'Eq : σ' = σ₀ := (ground_matchPatAtoms_iff hTbl hM σ₀ restBody hBrest).1 σ' hσ'In; subst σ'
            have haMem := (mem_decode_rel_iff hM g.rel a (rel_eq_of_matchPatAtom hmG)).mpr ⟨idx, hLo, hHi, M.entries[idx], hGet, hDec⟩
            have hσ₀Mem : σ₀ ∈ matchPatAtoms Term.const [] (g :: restBody) (decodeSortedFactSet tbl M) := by
              simp only [matchPatAtoms, List.mem_flatMap]; exact ⟨a, haMem, by simp only [hmG]; exact hσ'In⟩
            have hFrontB : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ₀ x = some d :=
              fun x hx => bound_of_matchPatAtom [] σ₀ g a hmG x (hBodyInG x (hFrontInBody x hx))
            exact (checkGuardedHeadFast_iff hTbl hM hG hFrontB).mpr (hSpec σ₀ hσ₀Mem)
        · rw [ite_eq_right hRestOk]
/-- **Indexed Guarded Saturation Equivalence (`checkGuardedSaturationFast_eq_spec`)**. -/
theorem checkGuardedSaturationFast_eq_spec {K : Type} [Datalog.ProvenanceSemiringOps K] [DecidableEq K]
    (tbl : SymInternTable) (M : Datalog.SortedKTable K) (rules : Array TgdRule)
    (hTbl : tbl.WF = true) (hM : M.WF) (hBounds : tableSymsInBounds tbl M = true)
    (hGuarded : rules.all IsGuardedRule = true) :
    checkGuardedSaturationFast tbl M rules = allRulesSatisfied rules.toList (decodeSortedFactSet tbl M) := by
  simp only [checkGuardedSaturationFast, allRulesSatisfied, ← Array.all_toList]
  have hAllG : ∀ r ∈ rules.toList, IsGuardedRule r = true := fun r hr =>
    Array.all_eq_true_iff_forall_mem.mp hGuarded r (Array.mem_toList_iff.mp hr)
  generalize rules.toList = rs at hAllG ⊢
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.all_cons]
    rw [checkGuardedRuleFast_eq_spec hTbl hM hBounds (hAllG r (.head _)), ih (fun r' hr' => hAllG r' (.tail _ hr'))]
theorem checkGuardedSaturationFast_inhabited (c : Nat) :
    let tbl : SymInternTable := ⟨#[.const c]⟩
    let M : Datalog.SortedKTable Bool := ⟨#[(⟨0, #[0]⟩, true), (⟨1, #[0]⟩, true)]⟩
    let r : TgdRule := { id := 1, frontierVars := [0], existVars := [], body := [⟨0, [.var 0]⟩], head := [⟨1, [.var 0]⟩] }
    tbl.WF = true ∧ M.WF ∧ tableSymsInBounds tbl M = true ∧
    IsGuardedRule r = true ∧ checkGuardedSaturationFast tbl M #[r] = true := by
  intro tbl M r
  have hM : M.WF := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hiLt : i.val < 2 := i.isLt; have hjLt : j.val < 2 := j.isLt
      have hi : i.val = 0 := by omega
      have hj : j.val = 1 := by omega
      simp [M, hi, hj, Datalog.TupleLt, Datalog.tupleCmp, compareLex, compareOn, Nat.compare_eq_lt]
    · have hiLt : i.val < 2 := i.isLt
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with h0 | h0 <;> simp [M, h0, ProvenanceSemiringOps.zero]
  have hTbl : tbl.WF = true := by simp [tbl, SymInternTable.WF, nodupTerms]
  have hBnd : tableSymsInBounds tbl M = true := by simp [tableSymsInBounds, tbl, M]
  have hG : IsGuardedRule r = true := by decide
  refine ⟨hTbl, hM, hBnd, hG, ?_⟩
  rw [checkGuardedSaturationFast_eq_spec tbl M #[r] hTbl hM hBnd (by simp [hG])]
  simp [M, decodeSortedFactSet, decodeTuple, decodeSyms, decodeSym, tbl, r,
    allRulesSatisfied, ruleSatisfiedSpec, matchPatAtoms, matchPatAtom, matchPatArgs,
    matchPatTerm, isSatisfied, frontierSubst, extractFrontierTuple, lookupSubst]

/-! ## §4. RMFA / EDB-Guarded Rank Witness (`RmfaRankWitness`, `rmfa_chase_terminates_bounded`) -/
def isEdbOnlyRel (rules : List TgdRule) (rel : Nat) : Bool :=
  rules.all fun r => r.head.all fun pa => pa.rel != rel
def isEdbGuardedVar (rules : List TgdRule) (r : TgdRule) (v : VarId) : Bool :=
  r.body.any fun pa => isEdbOnlyRel rules pa.rel && (varsOfPatAtom pa).contains v
structure RmfaRankWitness where
  posRanks : PosRankMap
  deriving DecidableEq, Repr
def maxRmfaRank (w : RmfaRankWitness) : Nat := maxRankOf w.posRanks
def checkRmfaRankRule (rules : List TgdRule) (w : RmfaRankWitness) (r : TgdRule) : Bool :=
  r.frontierVars.all (fun x => !(varPositionsIn x r.body).isEmpty) &&
  r.head.all fun pa =>
    (enumFrom 0 pa.args).all fun (j, pt) =>
      let headRank := rankOf w.posRanks { rel := pa.rel, pos := j }
      match pt with
      | .const _ => true
      | .var v =>
        if r.frontierVars.contains v then
          if isEdbGuardedVar rules r v then true
          else (varPositionsIn v r.body).all fun pB => decide (rankOf w.posRanks pB ≤ headRank)
        else if r.existVars.contains v then
          decide (1 ≤ headRank) &&
          r.frontierVars.all fun x =>
            if isEdbGuardedVar rules r x then true
            else (varPositionsIn x r.body).all fun pB => decide (rankOf w.posRanks pB + 1 ≤ headRank)
        else false
def checkRmfaRankWitness (w : RmfaRankWitness) (rules : List TgdRule) : Bool :=
  rules.all (checkRmfaRankRule rules w)
theorem weaklyAcyclic_implies_rmfaRankWitness (rk : PosRankMap) (rules : List TgdRule)
    (hWA : checkWeaklyAcyclic rk rules = true) : checkRmfaRankWitness ⟨rk⟩ rules = true := by
  simp only [checkWeaklyAcyclic, checkRmfaRankWitness, List.all_eq_true] at hWA ⊢
  intro r hr; have hR := hWA r hr
  simp only [checkWeaklyAcyclicRule, checkRmfaRankRule, Bool.and_eq_true, List.all_eq_true] at hR ⊢
  refine ⟨hR.1, fun pa hpa ⟨j, pt⟩ hjp => ?_⟩
  have hP := hR.2 pa hpa (j, pt) hjp
  cases pt with
  | const _ => exact hP
  | var v =>
    dsimp only at hP ⊢
    cases hvf : r.frontierVars.contains v
    · rw [hvf] at hP; simp only [Bool.false_eq_true, ↓reduceIte] at hP ⊢
      cases hve : r.existVars.contains v
      · rw [hve] at hP; simp only [Bool.false_eq_true, ↓reduceIte] at hP
      · rw [hve] at hP; simp only [↓reduceIte, Bool.and_eq_true, List.all_eq_true] at hP ⊢
        exact ⟨hP.1, fun x hx => by
          by_cases hed : isEdbGuardedVar rules r x = true
          · simp [hed]
          · simp only [hed, Bool.false_eq_true, ↓reduceIte, List.all_eq_true]; exact hP.2 x hx⟩
    · rw [hvf] at hP; simp only [↓reduceIte] at hP ⊢
      by_cases hed : isEdbGuardedVar rules r v = true
      · simp [hed]
      · simp only [hed, Bool.false_eq_true, ↓reduceIte]; exact hP
private theorem edb_var_skolemDepth_zero (rules : List TgdRule) (σ : Subst Term)
    (body : List PatAtom) (bodyAtoms : FactSet) (hevBody : evalPatAtoms Term.const σ body = some bodyAtoms)
    (hEdbBase : ∀ a ∈ bodyAtoms, isEdbOnlyRel rules a.rel = true → isBaseAtom a = true)
    (v : VarId) (ba : PatAtom) (hbaMem : ba ∈ body) (hEdbRel : isEdbOnlyRel rules ba.rel = true)
    (hvInBa : v ∈ varsOfPatAtom ba) (d : Term) (hlook : lookupSubst σ v = some d) : skolemDepth d = 0 := by
  have hexAtom : ∃ a ∈ bodyAtoms, evalPatAtom Term.const σ ba = some a := by
    induction body generalizing bodyAtoms with
    | nil => cases hbaMem
    | cons p₀ rest ih =>
      simp only [evalPatAtoms] at hevBody
      cases h1 : evalPatAtom Term.const σ p₀ <;> simp only [h1] at hevBody
      · cases hevBody
      · cases h2 : evalPatAtoms Term.const σ rest <;> simp only [h2] at hevBody
        · cases hevBody
        · injection hevBody with hga; subst hga; cases hbaMem with
          | head => exact ⟨_, .head _, h1⟩
          | tail _ hRest =>
            obtain ⟨a, ha, heva⟩ := ih _ h2 (fun b hb => hEdbBase b (.tail _ hb)) hRest
            exact ⟨a, .tail _ ha, heva⟩
  obtain ⟨a, haMem, heva⟩ := hexAtom; simp only [evalPatAtom] at heva
  cases hargs : evalPatArgs Term.const σ ba.args <;> simp only [hargs] at heva
  · cases heva
  · injection heva with haEq; subst haEq; rename_i aArgs
    have hBaseA : isBaseAtom { rel := ba.rel, args := aArgs } = true := hEdbBase _ haMem hEdbRel
    have aux : ∀ (pts : List PatTerm) (ds : List Term), evalPatArgs Term.const σ pts = some ds →
        v ∈ pts.filterMap (fun pt => match pt with | .var u => some u | .const _ => none) → d ∈ ds := by
      intro pts; induction pts with
      | nil => intro _ _ hv; cases hv
      | cons pt rest ih =>
        intro ds hEv hv; simp only [evalPatArgs] at hEv
        cases h1 : evalPatTerm Term.const σ pt <;> simp only [h1] at hEv
        · cases hEv
        · cases h2 : evalPatArgs Term.const σ rest <;> simp only [h2] at hEv
          · cases hEv
          · injection hEv with hds; subst hds; cases pt with
            | const _ => exact .tail _ (ih _ h2 (by simpa using hv))
            | var _ =>
              simp only [List.filterMap_cons, List.mem_cons] at hv
              rcases hv with rfl | hvRest
              · simp only [evalPatTerm, hlook, Option.some.injEq] at h1; subst h1; exact .head _
              · exact .tail _ (ih _ h2 hvRest)
    have hBaseD := (List.all_eq_true.mp hBaseA) d (aux ba.args aArgs hargs hvInBa)
    cases d with | const _ => rfl | skolem _ _ _ => cases hBaseD
private theorem rmfa_var_depth_bound (w : RmfaRankWitness) (rules : List TgdRule) (r : TgdRule)
    (σ : Subst Term) (bodyAtoms : FactSet) (hevBody : evalPatAtoms Term.const σ r.body = some bodyAtoms)
    (hBodyRk : ∀ b ∈ bodyAtoms, AtomPosRanked w.posRanks b)
    (hBodyEdb : ∀ b ∈ bodyAtoms, isEdbOnlyRel rules b.rel = true → isBaseAtom b = true)
    (v : VarId) (hPosNE : (!(varPositionsIn v r.body).isEmpty) = true)
    (d : Term) (hlook : lookupSubst σ v = some d) (delta bound : Nat) (hDelta : delta ≤ bound)
    (hCheck : (if isEdbGuardedVar rules r v then true
      else (varPositionsIn v r.body).all fun pB => decide (rankOf w.posRanks pB + delta ≤ bound)) = true) :
    skolemDepth d + delta ≤ bound := by
  by_cases hed : isEdbGuardedVar rules r v = true
  · simp only [isEdbGuardedVar, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hed
    obtain ⟨ba, hbaMem, hEdbBa, hvInBa⟩ := hed
    have hZ := edb_var_skolemDepth_zero rules σ r.body bodyAtoms hevBody hBodyEdb v ba hbaMem hEdbBa hvInBa d hlook
    omega
  · simp only [hed, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hCheck
    cases hPosList : varPositionsIn v r.body with
    | nil => simp [hPosList] at hPosNE
    | cons pB _ =>
      have hpBMem : pB ∈ varPositionsIn v r.body := hPosList ▸ .head _
      exact Nat.le_trans (Nat.add_le_add_right
        (SkolemChaseCore.body_var_depth_le_posRank w.posRanks σ r.body bodyAtoms hevBody hBodyRk v pB hpBMem d hlook) delta)
        (hCheck pB hpBMem)
/-- **RMFA Bounded Chase Termination (`rmfa_chase_terminates_bounded`)**. -/
theorem rmfa_chase_terminates_bounded (w : RmfaRankWitness) (rules : List TgdRule) (fuel : Nat) (I : FactSet)
    (hRmfa : checkRmfaRankWitness w rules = true) (hBaseI : IsBaseFactSet I = true) :
    ∀ a ∈ runBoundedChase rules fuel I, ∀ t ∈ a.args, skolemDepth t ≤ maxRmfaRank w := by
  let Inv : Atom Term → Prop :=
    fun a => AtomPosRanked w.posRanks a ∧ (isEdbOnlyRel rules a.rel = true → isBaseAtom a = true)
  have hRunInv : ∀ a ∈ runBoundedChase rules fuel I, Inv a := by
    refine SkolemChaseCore.runBoundedChase_invariant Inv rules ?_ fuel I ?_
    · intro r hrMem σ bodyAtoms headAtoms tTuple hevBody hBodyInv hExt hInst
      have hRuleR := (List.all_eq_true.mp hRmfa) r hrMem
      simp only [checkRmfaRankRule, Bool.and_eq_true, List.all_eq_true] at hRuleR
      obtain ⟨hFrontNE, hHeadR⟩ := hRuleR
      let σSkolem := buildHeadSubst r.frontierVars tTuple r.existVars (fun y => Term.skolem r.id y tTuple)
      have hHeadEach : ∀ (pas : List PatAtom) (as : FactSet), (∀ pa ∈ pas, pa ∈ r.head) →
          evalPatAtoms Term.const σSkolem pas = some as → ∀ a ∈ as, Inv a := by
        intro pas; induction pas with
        | nil => intro as _ hev a ha; injection hev with has; subst has; cases ha
        | cons pa restP ihP =>
          intro as hSubP hevP a ha; simp only [evalPatAtoms] at hevP
          cases h1 : evalPatAtom Term.const σSkolem pa <;> simp only [h1] at hevP
          · cases hevP
          · cases h2 : evalPatAtoms Term.const σSkolem restP <;> simp only [h2] at hevP
            · cases hevP
            · injection hevP with hasEq; subst hasEq; cases ha with
              | tail _ haRest => exact ihP _ (fun p hp => hSubP p (.tail _ hp)) h2 a haRest
              | head =>
                simp only [evalPatAtom] at h1
                cases hargs : evalPatArgs Term.const σSkolem pa.args <;> simp only [hargs] at h1
                · cases h1
                · injection h1 with haMk; subst haMk; rename_i aArgs
                  refine ⟨?_, fun hEdb => by
                    simp only [isEdbOnlyRel, List.all_eq_true] at hEdb
                    have hNe := hEdb r hrMem pa (hSubP pa (.head _)); simp at hNe⟩
                  intro j t hjtMem
                  obtain ⟨hL, _⟩ := SkolemChaseCore.evalPatArgs_enumFrom_correspondence σSkolem pa.args aArgs 0 hargs
                  obtain ⟨pt, hptMem, hevPt⟩ := hL j t hjtMem
                  have hpaClause := hHeadR pa (hSubP pa (.head _)) (j, pt) hptMem
                  cases pt with
                  | const _ => simp only [evalPatTerm, Option.some.injEq] at hevPt; subst hevPt; simp [skolemDepth]
                  | var v =>
                    dsimp only at hpaClause
                    cases hvFront : r.frontierVars.contains v
                    · rw [hvFront] at hpaClause; simp only [Bool.false_eq_true, ↓reduceIte] at hpaClause
                      cases hvExist : r.existVars.contains v
                      · rw [hvExist] at hpaClause; simp only [Bool.false_eq_true, ↓reduceIte] at hpaClause
                      · rw [hvExist] at hpaClause; simp only [↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hpaClause
                        obtain ⟨hOneLe, hSpec⟩ := hpaClause
                        have hvNotFront : v ∉ r.frontierVars := fun hm => by rw [List.contains_iff_mem.mpr hm] at hvFront; cases hvFront
                        have hLookSkolem : lookupSubst σSkolem v = some (Term.skolem r.id v tTuple) := by
                          simp only [σSkolem, buildHeadSubst]
                          rw [SkolemChaseCore.lookupSubst_append_of_left_none _ _ v
                            (SkolemChaseCore.lookupSubst_zip_none_of_not_mem r.frontierVars tTuple hvNotFront)]
                          exact SkolemChaseCore.lookupSubst_map_mkExist r.existVars _ (List.contains_iff_mem.mp hvExist)
                        simp only [evalPatTerm, hLookSkolem, Option.some.injEq] at hevPt; subst hevPt; simp only [skolemDepth]
                        apply SkolemChaseCore.skolemDepthList_add_one_le tTuple _ hOneLe
                        intro tArg htArg
                        obtain ⟨x, hxFront, hlx⟩ := SkolemChaseCore.mem_extractFrontierTuple_imp_var r.frontierVars σ tTuple hExt htArg
                        exact rmfa_var_depth_bound w rules r σ bodyAtoms hevBody (fun b hb => (hBodyInv b hb).1)
                          (fun b hb => (hBodyInv b hb).2) x (hFrontNE x hxFront) tArg hlx 1 _ hOneLe (hSpec x hxFront)
                    · rw [hvFront] at hpaClause; simp only [↓reduceIte] at hpaClause
                      have hvInFront := List.contains_iff_mem.mp hvFront
                      have hLookFront : lookupSubst σSkolem v = lookupSubst σ v :=
                        SkolemChaseCore.lookupSubst_buildHeadSubst_frontier r.frontierVars tTuple r.existVars
                          (fun y => Term.skolem r.id y tTuple) σ hExt hvInFront
                      simp only [evalPatTerm] at hevPt; rw [hLookFront] at hevPt
                      have hCheck0 : (if isEdbGuardedVar rules r v then true else
                          (varPositionsIn v r.body).all fun pB => decide (rankOf w.posRanks pB + 0 ≤ rankOf w.posRanks { rel := pa.rel, pos := j })) = true := by
                        simpa using hpaClause
                      simpa using rmfa_var_depth_bound w rules r σ bodyAtoms hevBody (fun b hb => (hBodyInv b hb).1)
                        (fun b hb => (hBodyInv b hb).2) v (hFrontNE v hvInFront) t hevPt 0 _ (Nat.zero_le _) hCheck0
      exact hHeadEach r.head headAtoms (fun p hp => hp) hInst
    · intro a ha; have hBaseA := (List.all_eq_true.mp hBaseI) a ha
      exact ⟨SkolemChaseCore.atomPosRanked_of_isBaseAtom w.posRanks a hBaseA, fun _ => hBaseA⟩
  intro a ha t ht; obtain ⟨idx, hIdxMem⟩ := SkolemChaseCore.mem_enumFrom_of_mem a.args 0 t ht
  exact Nat.le_trans ((hRunInv a ha).1 idx t hIdxMem) (SkolemChaseCore.rankOf_le_maxRankOf w.posRanks { rel := a.rel, pos := idx })
private theorem relPos_beq_eq_decide (p q : RelPos) : (p == q) = decide (p = q) := by
  rcases p with ⟨r1, p1⟩; rcases q with ⟨r2, p2⟩
  change (r1 == r2 && p1 == p2) = decide ({ rel := r1, pos := p1 : RelPos } = { rel := r2, pos := p2 })
  by_cases h1 : r1 = r2 <;> by_cases h2 : p1 = p2 <;> simp [h1, h2]
/-- **Strict Separation (`rmfa_strictly_subsumes_weaklyAcyclic`)**. -/
theorem rmfa_strictly_subsumes_weaklyAcyclic (relP relR relB : Nat)
    (hPR : relP ≠ relR) (hPB : relP ≠ relB) (hRB : relR ≠ relB) :
    let rules : List TgdRule := [
      { id := 1, frontierVars := [0], existVars := [1], body := [⟨relP, [.var 0]⟩], head := [⟨relR, [.var 0, .var 1]⟩] },
      { id := 2, frontierVars := [1], existVars := [], body := [⟨relR, [.var 0, .var 1]⟩, ⟨relB, [.var 1]⟩], head := [⟨relP, [.var 1]⟩] }
    ]
    (∀ rk : PosRankMap, checkWeaklyAcyclic rk rules = false) ∧
    (∃ w : RmfaRankWitness, checkRmfaRankWitness w rules = true ∧ maxRmfaRank w = 1) := by
  intro rules; constructor
  · intro rk; cases hWA : checkWeaklyAcyclic rk rules with
    | false => rfl
    | true =>
      exfalso; simp only [checkWeaklyAcyclic, List.all_eq_true] at hWA
      have h1 := hWA _ List.mem_cons_self; have h2 := hWA _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [checkWeaklyAcyclicRule, Bool.and_eq_true, List.all_eq_true] at h1 h2
      have h1y := h1.2 ⟨relR, [.var 0, .var 1]⟩ List.mem_cons_self (1, .var 1) (List.mem_cons_of_mem _ List.mem_cons_self)
      have h2y := h2.2 ⟨relP, [.var 1]⟩ List.mem_cons_self (0, .var 1) List.mem_cons_self
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq,
        show (1 : Nat) ≠ 0 by decide, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h1y h2y
      have hLt1 : rankOf rk ⟨relP, 0⟩ + 1 ≤ rankOf rk ⟨relR, 1⟩ :=
        h1y.2 0 List.mem_cons_self ⟨relP, 0⟩ (by simp [varPositionsIn, enumFrom])
      have hLe2 : rankOf rk ⟨relR, 1⟩ ≤ rankOf rk ⟨relP, 0⟩ :=
        h2y ⟨relR, 1⟩ (by simp [varPositionsIn, enumFrom])
      omega
  · refine ⟨⟨[(⟨relP, 0⟩, 0), (⟨relR, 0⟩, 0), (⟨relR, 1⟩, 1)]⟩, ?_, rfl⟩
    have hEdbB : isEdbOnlyRel rules relB = true := by simp [isEdbOnlyRel, rules, bne_iff_ne, hRB, hPB]
    have hGuardedY : isEdbGuardedVar rules
        { id := 2, frontierVars := [1], existVars := [], body := [⟨relR, [.var 0, .var 1]⟩, ⟨relB, [.var 1]⟩], head := [⟨relP, [.var 1]⟩] } 1 = true := by
      simp [isEdbGuardedVar, varsOfPatAtom, hEdbB]
    have hRankR0 : rankOf [(⟨relP, 0⟩, 0), (⟨relR, 0⟩, 0), (⟨relR, 1⟩, 1)] ⟨relR, 0⟩ = 0 := by simp [rankOf, relPos_beq_eq_decide, hPR]
    have hRankR1 : rankOf [(⟨relP, 0⟩, 0), (⟨relR, 0⟩, 0), (⟨relR, 1⟩, 1)] ⟨relR, 1⟩ = 1 := by simp [rankOf, relPos_beq_eq_decide, hPR]
    have hRankP0 : rankOf [(⟨relP, 0⟩, 0), (⟨relR, 0⟩, 0), (⟨relR, 1⟩, 1)] ⟨relP, 0⟩ = 0 := by simp [rankOf, relPos_beq_eq_decide]
    simp [checkRmfaRankWitness, checkRmfaRankRule, rules, varPositionsIn, enumFrom, hGuardedY, hRankR0, hRankR1, hRankP0]

/-! ## §5. $O(|P|)$ Ranked GL & VGRS Fixpoint Wrappers (`Obend.SymbolicZk.Ranked`) -/
structure GlFixpointCert where
  rank    : Array Nat
  support : Array Nat
  deriving DecidableEq, Repr, Inhabited
def checkGlFixpointLinear (p : Ranked.ArithProgram) (m : Array Bool) (cert : GlFixpointCert) : Bool :=
  Ranked.checkRankedGLStable p m cert.rank cert.support
theorem checkGlFixpointLinear_iff_least_model (p : Ranked.ArithProgram) (m : Array Bool)
    (hWf : Ranked.WFProgram p = true) (hm : m.size = p.numAtoms) :
    (∃ cert : GlFixpointCert, checkGlFixpointLinear p m cert = true) ↔
      Obend.Reasons.UnifiedEquilibrium.IsGLStableModel (Ranked.toReasonsProgram p) (Ranked.decodeBits m) :=
  ⟨fun ⟨_, hOk⟩ => Ranked.checkRankedGLStable_sound hOk, fun hM =>
    let ⟨r, s, hOk⟩ := Ranked.checkRankedGamma_complete p m m hWf hm hm hM; ⟨⟨r, s⟩, hOk⟩⟩
theorem checkGlFixpointLinear_inhabited (r0 : Nat) :
    let _ := r0
    checkGlFixpointLinear ⟨1, #[⟨0, #[], #[]⟩]⟩ #[true] ⟨#[0], #[0]⟩ = true := by
  simp only [checkGlFixpointLinear, Ranked.checkRankedGLStable, Ranked.checkRankedGamma,
    Ranked.WFProgram, Ranked.checkClosure, Ranked.firesFast, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp [Ranked.checkSupport, Ranked.rankAt, Ranked.bit, Array.mem_range]
def checkVgrsFixpointLinear (p : Ranked.ArithProgram) (t u : Array Bool) (cert : Ranked.ArrayCert) : Bool :=
  Ranked.checkRankedWFS p t u cert
theorem checkVgrsFixpointLinear_iff_wfs (p : Ranked.ArithProgram) (t u : Array Bool)
    (hWf : Ranked.WFProgram p = true) (ht : t.size = p.numAtoms) (hu : u.size = p.numAtoms) :
    (∃ cert : Ranked.ArrayCert, checkVgrsFixpointLinear p t u cert = true) ↔
      Obend.Reasons.Same (Ranked.decodeBits t) (Obend.Reasons.wf (Ranked.toReasonsProgram p)).1 ∧
      Obend.Reasons.Same (Ranked.decodeBits u) (Obend.Reasons.wf (Ranked.toReasonsProgram p)).2 :=
  ⟨fun ⟨_, hOk⟩ => Ranked.checkRankedWFS_sound hOk, Ranked.checkRankedWFS_complete p t u hWf ht hu⟩
theorem checkVgrsFixpointLinear_inhabited (r0 : Nat) :
    let _ := r0
    checkVgrsFixpointLinear ⟨0, #[]⟩ #[] #[] ⟨#[], #[], #[], #[], #[], #[]⟩ = true := by
  simp [checkVgrsFixpointLinear, Ranked.checkRankedWFS, Ranked.WFProgram, Ranked.checkClosure, Array.range_eq_range']

/-! ## §6. Evidenced Ocap Query Guard (`Obend.Polis`) & Choice-Free Core BCQ Quotient Lift (`Obend.Repair`) -/
structure KgQueryPolicy where
  query      : ConjunctiveQuery
  needRights : UInt64
  caveat     : Obend.Polis.Caveat
  deriving DecidableEq, Repr
def checkKgQueryGuard (pol : KgQueryPolicy) (rights mask : UInt64)
    (ρ : Nat → Obend.Polis.KleenePred3) : Bool :=
  Obend.Polis.subMask pol.needRights (rights &&& mask) &&
  Obend.Polis.KleenePred3.accepts (pol.caveat.eval ρ)
theorem evidenced_kg_query_guard_sound (pol : KgQueryPolicy) (rights mask : UInt64)
    (ρ ρ' : Nat → Obend.Polis.KleenePred3) (hGuard : checkKgQueryGuard pol rights mask ρ = true)
    (hRef : ∀ v, Obend.Polis.KleenePred3.Refines (ρ v) (ρ' v)) :
    (Obend.Polis.realizabilityFrame Obend.Polis.capPCA).Leads
      (Obend.Polis.holdsCap rights)
      ((Obend.Polis.realizabilityFrame Obend.Polis.capPCA).seq (.attenuate mask) (.guard pol.needRights))
      (fun c => c = .k) ∧
    Obend.Polis.subMask (rights &&& mask) rights = true ∧
    Obend.Polis.subMask pol.needRights rights = true ∧
    Obend.Polis.KleenePred3.Refines (pol.caveat.eval ρ) (pol.caveat.eval ρ') ∧
    Obend.Polis.KleenePred3.accepts (pol.caveat.eval ρ') = true := by
  simp only [checkKgQueryGuard, Bool.and_eq_true] at hGuard
  obtain ⟨hSubEff, hAcc⟩ := hGuard
  obtain ⟨hAttLeads, hAttSub⟩ := Obend.Polis.attenuate_leads rights mask
  have hGuardLeads : (Obend.Polis.realizabilityFrame Obend.Polis.capPCA).Leads
      (Obend.Polis.holdsCap (rights &&& mask)) (.guard pol.needRights) (fun c => c = .k) :=
    fun _ ha => ⟨.k, ha ▸ Obend.Polis.CapApp.guardGrant hSubEff, rfl⟩
  exact ⟨(Obend.Polis.realizabilityFrame Obend.Polis.capPCA).leads_trans hAttLeads hGuardLeads,
    hAttSub, Obend.Polis.subMask_trans hSubEff hAttSub,
    Obend.Polis.Caveat.eval_refines hRef pol.caveat, Obend.Polis.Caveat.accepts_stable hRef pol.caveat hAcc⟩
theorem checkKgQueryGuard_inhabited (q : ConjunctiveQuery) (rights : UInt64) :
    checkKgQueryGuard ⟨q, rights, .const true⟩ rights rights (fun _ => .unbound3) = true := by
  simp [checkKgQueryGuard, Obend.Polis.subMask_refl, Obend.Polis.Caveat.eval, Obend.Polis.KleenePred3.accepts]
inductive KgAsmVal where
  | factSet (M : FactSet)
  | boolVal (b : Bool)
  deriving DecidableEq, Repr
inductive KgAsmCode where
  | id
  | comp (g f : KgAsmCode)
  | evalBcq (q : ConjunctiveQuery)
  deriving DecidableEq, Repr
@[expose] def KgAsmCode.eval : KgAsmCode → KgAsmVal → Option KgAsmVal
  | .id, v => some v
  | .comp g f, v => match eval f v with | some u => eval g u | none => none
  | .evalBcq q, .factSet M => some (.boolVal (evalBCQ q M))
  | .evalBcq _, .boolVal _ => none
instance instCodeTrackerKgAsm : Obend.Repair.CodeTracker KgAsmCode KgAsmVal where
  eval := KgAsmCode.eval
  idCode := .id
  compCode := .comp
  eval_id _ := rfl
  eval_comp g f v u w hf hg := by dsimp only [KgAsmCode.eval]; rw [hf]; exact hg
def CoreHomEquiv (M₁ M₂ : FactSet) : Prop :=
  (∃ f : Term → Term, (∀ c, f (.const c) = .const c) ∧ (∀ a ∈ M₁, mapAtom f a ∈ M₂)) ∧
  (∃ g : Term → Term, (∀ c, g (.const c) = .const c) ∧ (∀ a ∈ M₂, mapAtom g a ∈ M₁))
theorem coreHomEquiv_of_retraction {cert : RetractionCert} {M C : FactSet}
    (hRet : checkRetractionCore cert M C = true) : CoreHomEquiv M C := by
  obtain ⟨hCsubM, hMtoC, _, _⟩ := checkRetractionCore_sound cert M C hRet
  exact ⟨⟨applyRetraction cert, fun _ => rfl, hMtoC⟩, ⟨id, fun _ => rfl, fun a ha => by rw [mapAtom_id]; exact hCsubM a ha⟩⟩
theorem evalBCQ_eq_of_coreHomEquiv {M₁ M₂ : FactSet} (hEq : CoreHomEquiv M₁ M₂) (q : ConjunctiveQuery) :
    evalBCQ q M₁ = evalBCQ q M₂ := by
  obtain ⟨⟨f, hfC, hfHom⟩, ⟨g, hgC, hgHom⟩⟩ := hEq
  cases h1 : evalBCQ q M₁ <;> cases h2 : evalBCQ q M₂
  · rfl
  · have hT := SkolemChaseCore.evalBCQ_mono_of_hom g hgC M₂ M₁ hgHom q h2; rw [h1] at hT; cases hT
  · have hT := SkolemChaseCore.evalBCQ_mono_of_hom f hfC M₁ M₂ hfHom q h1; rw [h2] at hT; cases hT
  · rfl
@[expose] def factSetAssembly : Obend.Repair.Assembly KgAsmCode KgAsmVal FactSet where
  Realizes v M := v = .factSet M
  realized M := ⟨.factSet M, rfl⟩
@[expose] def boolAssembly : Obend.Repair.Assembly KgAsmCode KgAsmVal Bool where
  Realizes v b := v = .boolVal b
  realized b := ⟨.boolVal b, rfl⟩
@[expose] def bcqEvalAsmHom (q : ConjunctiveQuery) : Obend.Repair.AsmHom factSetAssembly boolAssembly where
  specFun M := evalBCQ q M
  tracker := .evalBcq q
  tracks M v hv := by subst hv; exact ⟨.boolVal (evalBCQ q M), rfl, rfl⟩
@[expose] def coreEffectiveQuotient : Obend.Repair.EffectiveQuotient factSetAssembly CoreHomEquiv :=
  Obend.Repair.EffectiveQuotient.ofId factSetAssembly CoreHomEquiv
@[expose] def coreQuotientBcqHom (q : ConjunctiveQuery) :
    Obend.Repair.AsmHom (Obend.Repair.EffectiveQuotient.quotAssembly factSetAssembly CoreHomEquiv) boolAssembly :=
  coreEffectiveQuotient.liftHom (bcqEvalAsmHom q) (fun _ _ hEq => evalBCQ_eq_of_coreHomEquiv hEq q)
theorem coreQuotientBcqHom_tracker_reduces_rfl (q : ConjunctiveQuery) (M : FactSet) :
    KgAsmCode.eval (coreQuotientBcqHom q).tracker (.factSet M) = some (.boolVal (evalBCQ q M)) := rfl
theorem core_quotient_bcq_lift_sound (cert : RetractionCert) (M C : FactSet) (q : ConjunctiveQuery)
    (hRet : checkRetractionCore cert M C = true) :
    Quot.mk CoreHomEquiv M = Quot.mk CoreHomEquiv C ∧
    (coreQuotientBcqHom q).specFun (Quot.mk CoreHomEquiv M) = evalBCQ q M ∧
    (coreQuotientBcqHom q).specFun (Quot.mk CoreHomEquiv M) =
      (coreQuotientBcqHom q).specFun (Quot.mk CoreHomEquiv C) ∧
    KgAsmCode.eval (coreQuotientBcqHom q).tracker (.factSet M) = some (.boolVal (evalBCQ q C)) := by
  have hEq := coreHomEquiv_of_retraction hRet
  have hQ : Quot.mk CoreHomEquiv M = Quot.mk CoreHomEquiv C := Quot.sound hEq
  refine ⟨hQ, rfl, congrArg (coreQuotientBcqHom q).specFun hQ, ?_⟩
  rw [coreQuotientBcqHom_tracker_reduces_rfl, evalBCQ_eq_of_coreHomEquiv hEq q]

end Obend.SemanticKG
end
