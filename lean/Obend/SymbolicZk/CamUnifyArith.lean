module
public import Obend.Lower.ExprCAM
public import Obend.Tactic.Tooth
public import Std

public section
set_option autoImplicit false
namespace Obend.SymbolicZk.Cam
open Obend.Lower.ExprCAM Obend.Lower Obend.Lower.Inductive Obend.Lower.LeanKernel

/-- The committed representation contains only hardware words. A ternary `letE` uses
an auxiliary pair node for its value/body; both encoded edges must be checked. -/
structure CamDagPool where
  words : Array CamWord64
  sigma : Array (Option Nat)
  deriving Inhabited

@[expose] def heightAt (tau : Array Nat) (u : Nat) : Nat := tau[u]?.getD 0

/-- Child handles for the binary hardware encoding. Tag 7's right child is the
auxiliary pair node, not a projection that discards the third AST child. -/
@[expose] def childHandles (w : CamWord64) : Array Nat :=
  let f := unpackCamWord64 w
  if f.tag.toNat = 4 ∨ f.tag.toNat = 5 ∨ f.tag.toNat = 6 ∨ f.tag.toNat = 7 then
    #[f.left.toNat, f.right.toNat]
  else if f.tag.toNat = 9 then #[f.left.toNat] else #[]

@[expose] def Child (p : CamDagPool) (u v : Nat) : Prop :=
  ∃ w, p.words[u]? = some w ∧ v ∈ childHandles w

@[expose] def Assigned (p : CamDagPool) (u v : Nat) : Prop :=
  p.sigma[u]? = some (some v)

/-- Every path represented here contains at least one constructor edge. Pure alias
cycles are deliberately separate: they do not describe an infinite constructor term. -/
inductive AliasPath (p : CamDagPool) : Nat → Nat → Prop where
  | refl (u) : AliasPath p u u
  | step {u v w} : Assigned p u v → AliasPath p v w → AliasPath p u w

inductive SubstDependsOn (p : CamDagPool) : Nat → Nat → Prop where
  | child {u v} : Child p u v → SubstDependsOn p u v
  | aliasLeft {u v w} : Assigned p u v → SubstDependsOn p v w → SubstDependsOn p u w
  | aliasRight {u v w} : SubstDependsOn p u v → Assigned p v w → SubstDependsOn p u w
  | trans {u v w} : SubstDependsOn p u v → SubstDependsOn p v w → SubstDependsOn p u w

@[expose] def strictHeight (a b : Nat) : Bool := decide (b < a)

/-- O(nodes + encoded edges), with direct array reads. Assignments are accepted only
at metavariable nodes. Rank values are ordinary integers, not field residues. -/
def checkTopologicalUnifyExec (p : CamDagPool) (tau : Array Nat) : Bool :=
  tau.size == p.words.size && p.sigma.size == p.words.size &&
  (Array.range p.words.size).all fun u =>
    (childHandles p.words[u]!).all (fun v =>
      v < p.words.size && strictHeight (heightAt tau u) (heightAt tau v)) &&
    match p.sigma[u]?.getD none with
    | none => true
    | some v => (unpackCamWord64 p.words[u]!).tag.toNat == 10 &&
        v < p.words.size && heightAt tau u == heightAt tau v

private theorem checked_edges {p : CamDagPool} {tau : Array Nat}
    (h : checkTopologicalUnifyExec p tau = true) :
    (∀ u v, Child p u v → heightAt tau v < heightAt tau u) ∧
    (∀ u v, Assigned p u v → heightAt tau u = heightAt tau v) := by
  simp only [checkTopologicalUnifyExec, Bool.and_eq_true, beq_iff_eq] at h
  have rows := Array.all_eq_true_iff_forall_mem.mp h.2
  constructor
  · intro u v hc
    obtain ⟨w, hw, hv⟩ := hc
    have hu : u < p.words.size := (Array.getElem?_eq_some_iff.mp hw).1
    have he : p.words[u]! = w := by
      rw [getElem!_pos p.words u hu]
      exact (Array.getElem?_eq_some_iff.mp hw).2
    have row := rows u (by simpa using hu)
    have ch := (Bool.and_eq_true_iff.mp row).1
    rw [he] at ch
    have hh := (Array.all_eq_true_iff_forall_mem.mp ch) v hv
    simpa [strictHeight] using (Bool.and_eq_true_iff.mp hh).2
  · intro u v hs
    have hu : u < p.words.size := by
      have := (Array.getElem?_eq_some_iff.mp hs).1
      omega
    have row := rows u (by simpa using hu)
    have ass := (Bool.and_eq_true_iff.mp row).2
    simp only [Assigned] at hs
    simp only [hs, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at ass
    exact ass.2

theorem topologicalHeight_forbids_cyclic_mvar {p : CamDagPool} {tau : Array Nat}
    (h : checkTopologicalUnifyExec p tau = true) : ∀ u, ¬ SubstDependsOn p u u := by
  obtain ⟨hc, hs⟩ := checked_edges h
  have descent : ∀ {u v}, SubstDependsOn p u v → heightAt tau v < heightAt tau u := by
    intro u v hv
    induction hv with
    | child he => exact hc _ _ he
    | aliasLeft he _ ih => rw [hs _ _ he]; exact ih
    | aliasRight _ he ih => rw [← hs _ _ he]; exact ih
    | trans _ _ h₁ h₂ => exact Nat.lt_trans h₂ h₁
  exact fun u hu => Nat.lt_irrefl (heightAt tau u) (descent hu)

#tooth topologicalHeight_forbids_cyclic_mvar by mutation strictHeight := fun a b => decide (b ≤ a)

/-- The finite graph's edges, oriented toward dependencies. -/
def DagEdge (p : CamDagPool) (v u : Nat) : Prop := Child p u v ∨ Assigned p u v

/-- Shape and bounds are independent of the height witness. -/
structure CamDagWF (p : CamDagPool) : Prop where
  sigmaSize : p.sigma.size = p.words.size
  childBound : ∀ u v, Child p u v → v < p.words.size
  assigned : ∀ u v, Assigned p u v → v < p.words.size ∧
    ∃ w, p.words[u]? = some w ∧ (unpackCamWord64 w).tag.toNat = 10

def maxHeights {A : Type} (f : A → Nat) : List A → Nat
  | [] => 0
  | a :: as => max (f a + 1) (maxHeights f as)

private theorem lt_maxHeights {A : Type} (f : A → Nat) (xs : List A) (a : A)
    (ha : a ∈ xs) : f a < maxHeights f xs := by
  induction xs with
  | nil => cases ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih ha) (Nat.le_max_right _ _)

noncomputable def dagHeight (p : CamDagPool) (hwf : WellFounded (DagEdge p)) : Nat → Nat :=
  hwf.fix fun u rec =>
    match hs : p.sigma[u]? with
    | some (some v) => rec v (Or.inr hs)
    | _ => match hw : p.words[u]? with
      | none => 0
      | some w => maxHeights (fun v : {v // v ∈ (childHandles w).toList} =>
          rec v.val (Or.inl ⟨w, hw, by simpa using v.property⟩)) (childHandles w).toList.attach

private theorem dagHeight_assigned (p : CamDagPool) (hwf : WellFounded (DagEdge p))
    (u v : Nat) (hs : Assigned p u v) : dagHeight p hwf u = dagHeight p hwf v := by
  rw [dagHeight, WellFounded.fix_eq]
  simp only [Assigned] at hs
  split <;> simp_all
  subst_vars
  rfl

private theorem dagHeight_child (p : CamDagPool) (hw : CamDagWF p)
    (hwf : WellFounded (DagEdge p)) (u v : Nat) (hc : Child p u v) :
    dagHeight p hwf v < dagHeight p hwf u := by
  obtain ⟨w, hword, hmem⟩ := hc
  have noAssign : ∀ a, ¬ Assigned p u a := by
    intro a ha
    obtain ⟨_, w', hw', ht⟩ := hw.assigned u a ha
    have he : w' = w := Option.some.inj (hw'.symm.trans hword)
    subst w'
    have hempty : childHandles w = #[] := by simp [childHandles, ht]
    simp [hempty] at hmem
  conv => rhs; rw [dagHeight, WellFounded.fix_eq]
  split
  · rename_i a hs
    exact False.elim (noAssign a hs)
  · split
    · rename_i he
      simp_all
    · rename_i w' he
      have hew : w' = w := Option.some.inj (he.symm.trans hword)
      subst w'
      exact lt_maxHeights (fun x : {x // x ∈ (childHandles w).toList} => dagHeight p hwf x.val)
        (childHandles w).toList.attach ⟨v, by simpa using hmem⟩ (by simp)

/-- On a finite well-formed DAG, well-foundedness of dependency edges is the acyclicity
hypothesis. Alias edges receive equal heights; constructor edges receive strict heights. -/
theorem topologicalHeight_complete (p : CamDagPool) (hw : CamDagWF p)
    (acyclic : WellFounded (DagEdge p)) :
    ∃ tau, checkTopologicalUnifyExec p tau = true := by
  let tau := Array.ofFn (fun i : Fin p.words.size => dagHeight p acyclic i.val)
  have hv (u : Nat) (hu : u < p.words.size) : heightAt tau u = dagHeight p acyclic u := by
    simp [tau, heightAt, hu]
  refine ⟨tau, ?_⟩
  simp only [checkTopologicalUnifyExec, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨by simp [tau], hw.sigmaSize⟩, ?_⟩
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro u hu
  have hub : u < p.words.size := by simpa using hu
  have hword : p.words[u]? = some p.words[u]! := by simp [getElem!_pos, hub]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro v hmem
    have hc : Child p u v := ⟨p.words[u]!, hword, hmem⟩
    have hb := hw.childBound u v hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, strictHeight, hv u hub, hv v hb]
    exact ⟨hb, dagHeight_child p hw acyclic u v hc⟩
  · cases hs : p.sigma[u]? with
    | none => rfl
    | some opt =>
      cases opt with
      | none => rfl
      | some v =>
        have ha : Assigned p u v := hs
        obtain ⟨hb, w, he, ht⟩ := hw.assigned u v ha
        have hew : w = p.words[u]! := Option.some.inj (he.symm.trans hword)
        subst w
        simp only [Option.getD_some, ht, beq_self_eq_true, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hv u hub, hv v hb]
        exact ⟨hb, dagHeight_assigned p acyclic u v ha⟩

/-- Bit 59 is meaningful only when tied to the packed expression summary. -/
theorem camWord64_bit59_closed_bypass (e : KExpr) (leftH rightH : Nat) (w : CamWord64)
    (hw : w = packCamWord64 (mkExprCamFields e leftH rightH))
    (hbit : w.getLsbD 59 = false) :
    KExpr.hasLooseBVar e = false ∧
      (∀ arg, KExpr.instantiateAt 0 arg e = e) ∧
      (∀ delta, KExpr.liftLooseBVars 0 delta e = e) := by
  have he := congrArg CamNodeFields.looseBVar (unpack_pack_camWord64 (mkExprCamFields e leftH rightH))
  have hc : KExpr.hasLooseBVar e = false := by
    rw [hw] at hbit
    exact he.symm.trans hbit
  exact ⟨hc, fun arg => instantiateAt_of_hasLooseBVarAt_false e 0 arg hc,
    fun delta => liftLooseBVars_of_hasLooseBVarAt_false e 0 delta hc⟩

example : checkTopologicalUnifyExec ⟨#[], #[]⟩ #[] = true := by
  simp [checkTopologicalUnifyExec, Array.range_eq_range']

/-- Adjacent comparisons suffice for strict ordering; no quadratic pairwise check. -/
@[expose] def checkStrictKeys (keys : Array Nat) : Bool :=
  (Array.range (keys.size - 1)).all fun i => keys[i]! < keys[i + 1]!

theorem checkStrictKeys_order {keys : Array Nat} (h : checkStrictKeys keys = true)
    (i j : Nat) (hi : i < keys.size) (hj : j < keys.size) (hij : i < j) :
    keys[i] < keys[j] := by
  have adj : ∀ k, k + 1 < keys.size → keys[k]! < keys[k + 1]! := by
    intro k hk
    have hh := (Array.all_eq_true_iff_forall_mem.mp h) k (by simp; omega)
    exact of_decide_eq_true hh
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := adj j hj
    simp only [getElem!_pos keys j (by omega), getElem!_pos keys (j + 1) hj] at hstep
    by_cases he : i = j
    · subst i; exact hstep
    · exact Nat.lt_trans (ih (by omega) (by omega)) hstep

theorem checkStrictKeys_nodup {keys : Array Nat} (h : checkStrictKeys keys = true) :
    keys.toList.Nodup := by
  apply List.Pairwise.imp (fun hlt => Nat.ne_of_lt hlt)
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  exact checkStrictKeys_order h i j (by simpa using hi) (by simpa using hj) hij

/-- The numeric key is the lexicographic `(tag,left,right)` key: 4+16+16 bits. -/
@[expose] def camKey (w : CamWord64) : Nat :=
  let f := unpackCamWord64 w
  f.tag.toNat * 4294967296 + f.left.toNat * 65536 + f.right.toNat

/-- An inverse permutation is supplied alongside π, allowing an O(n) coverage check. -/
structure InternCert where
  order : Array Nat
  inverse : Array Nat
  deriving Inhabited

def checkCanonicalCamPool (pool : Array CamWord64) (c : InternCert) : Bool :=
  c.order.size == pool.size && c.inverse.size == pool.size &&
  (Array.range pool.size).all (fun h =>
    c.inverse[h]! < c.order.size && c.order[c.inverse[h]!]! == h) &&
  c.order.all (· < pool.size) &&
  checkStrictKeys (c.order.map (fun h => camKey pool[h]!))

theorem checkCanonicalCamPool_sound {pool : Array CamWord64} {c : InternCert}
    (h : checkCanonicalCamPool pool c = true) (u v : Nat)
    (hu : u < pool.size) (hv : v < pool.size)
    (he : camKey pool[u] = camKey pool[v]) : u = v := by
  simp only [checkCanonicalCamPool, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  have rows := Array.all_eq_true_iff_forall_mem.mp h.2.2.1
  have ru := rows u (by simpa using hu)
  have rv := rows v (by simpa using hv)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ru rv
  let keys := c.order.map (fun h => camKey pool[h]!)
  have huk : c.inverse[u]! < keys.size := by simpa [keys] using ru.1
  have hvk : c.inverse[v]! < keys.size := by simpa [keys] using rv.1
  have ku : keys[c.inverse[u]!] = camKey pool[u] := by
    simp [keys, Array.getElem_map, ← getElem!_pos c.order (c.inverse[u]!) ru.1, ru.2, getElem!_pos pool u hu]
  have kv : keys[c.inverse[v]!] = camKey pool[v] := by
    simp [keys, Array.getElem_map, ← getElem!_pos c.order (c.inverse[v]!) rv.1, rv.2, getElem!_pos pool v hv]
  have heq : c.inverse[u]! = c.inverse[v]! := by
    by_cases hlt : c.inverse[u]! < c.inverse[v]!
    · have hh := checkStrictKeys_order h.2.2.2.2 _ _ (by simpa using ru.1) (by simpa using rv.1) hlt
      rw [ku, kv, he] at hh
      exact False.elim (Nat.lt_irrefl _ hh)
    · by_cases hgt : c.inverse[v]! < c.inverse[u]!
      · have hh := checkStrictKeys_order h.2.2.2.2 _ _ (by simpa using rv.1) (by simpa using ru.1) hgt
        rw [ku, kv, he] at hh
        exact False.elim (Nat.lt_irrefl _ hh)
      · omega
  exact ru.2.symm.trans ((congrArg (fun i => c.order[i]!) heq).trans rv.2)

example : checkCanonicalCamPool #[] ⟨#[], #[]⟩ = true := by
  simp [checkCanonicalCamPool, checkStrictKeys, Array.range_eq_range']

/-- Congruence over the binary encoded DAG, relative to authenticated input equalities. -/
inductive CamCongruence (pool : Array CamWord64) (seeds : Array (Nat × Nat)) : Nat → Nat → Prop where
  | refl (u) : CamCongruence pool seeds u u
  | seed {u v} : (u,v) ∈ seeds → CamCongruence pool seeds u v
  | symm {u v} : CamCongruence pool seeds u v → CamCongruence pool seeds v u
  | trans {u v w} : CamCongruence pool seeds u v → CamCongruence pool seeds v w → CamCongruence pool seeds u w
  | node {u v a b} : pool[u]? = some a → pool[v]? = some b →
      (unpackCamWord64 a).tag = (unpackCamWord64 b).tag →
      4 ≤ (unpackCamWord64 a).tag.toNat → (unpackCamWord64 a).tag.toNat ≤ 7 →
      CamCongruence pool seeds (unpackCamWord64 a).left.toNat (unpackCamWord64 b).left.toNat →
      CamCongruence pool seeds (unpackCamWord64 a).right.toNat (unpackCamWord64 b).right.toNat →
      CamCongruence pool seeds u v

inductive CongruenceReason where
  | refl | seed (i : Nat) | symm (i : Nat) | trans (i j : Nat) | node (i j : Nat)
  deriving Repr, Inhabited

structure CongruenceRow where
  lhs : Nat
  rhs : Nat
  reason : CongruenceReason
  deriving Repr, Inhabited

@[expose] def edgeAt (rows : Array CongruenceRow) (i : Nat) : Option (Nat × Nat) :=
  rows[i]?.map (fun r => (r.lhs,r.rhs))

/-- Two child-equality references justify a constructor edge. The proof DAG's references
strictly precede their consumer, independently of the union-find forest's ranks. -/
@[expose] def checkCongruenceRow (pool : Array CamWord64) (seeds : Array (Nat × Nat))
    (rows : Array CongruenceRow) (i : Nat) (r : CongruenceRow) : Bool :=
  match r.reason with
  | .refl => r.lhs == r.rhs
  | .seed k => seeds[k]? == some (r.lhs,r.rhs)
  | .symm k => k < i && edgeAt rows k == some (r.rhs,r.lhs)
  | .trans j k => j < i && k < i &&
      match edgeAt rows j, edgeAt rows k with
      | some a, some b => a.1 == r.lhs && a.2 == b.1 && b.2 == r.rhs
      | _, _ => false
  | .node j k => j < i && k < i &&
      match pool[r.lhs]?, pool[r.rhs]? with
      | some a, some b =>
        let x := unpackCamWord64 a
        let y := unpackCamWord64 b
        x.tag == y.tag && 4 ≤ x.tag.toNat && x.tag.toNat ≤ 7 &&
          edgeAt rows j == some (x.left.toNat,y.left.toNat) &&
          edgeAt rows k == some (x.right.toNat,y.right.toNat)
      | _, _ => false

def checkCongruenceProofs (pool : Array CamWord64) (seeds : Array (Nat × Nat))
    (rows : Array CongruenceRow) : Bool :=
  (Array.range rows.size).all (fun i => checkCongruenceRow pool seeds rows i rows[i]!)

theorem checkCongruenceProofs_sound {pool : Array CamWord64} {seeds : Array (Nat × Nat)}
    {rows : Array CongruenceRow} (h : checkCongruenceProofs pool seeds rows = true)
    (i : Nat) (hi : i < rows.size) : CamCongruence pool seeds rows[i].lhs rows[i].rhs := by
  have checked := Array.all_eq_true_iff_forall_mem.mp h
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have prior : ∀ k, k < i → ∀ a b, edgeAt rows k = some (a,b) → CamCongruence pool seeds a b := by
      intro k hk a b he
      unfold edgeAt at he
      cases hr : rows[k]? with
      | none => simp [hr] at he
      | some r =>
        have hkb := (Array.getElem?_eq_some_iff.mp hr).1
        have hkr := (Array.getElem?_eq_some_iff.mp hr).2
        have hh := ih k hk hkb
        rw [hkr] at hh
        have hep : (r.lhs,r.rhs) = (a,b) := by simpa [hr] using he
        cases hep
        exact hh
    have row := checked i (by simpa using hi)
    rw [getElem!_pos rows i hi] at row
    unfold checkCongruenceRow at row
    split at row
    · have he : rows[i].lhs = rows[i].rhs := by simpa using row
      rw [he]; exact .refl _
    · exact .seed (Array.mem_of_getElem? (by simpa using row))
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at row
      exact .symm (prior _ row.1 _ _ row.2)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at row
      obtain ⟨⟨hj,hk⟩, he⟩ := row
      split at he
      · rename_i a b ha hb
        simp only [Bool.and_eq_true, beq_iff_eq] at he
        have h₁ := prior _ hj a.1 a.2 ha
        have h₂ := prior _ hk b.1 b.2 hb
        rw [he.1.1, he.1.2] at h₁
        rw [he.2] at h₂
        exact .trans h₁ h₂
      · cases he
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at row
      obtain ⟨⟨hj,hk⟩, he⟩ := row
      split at he
      · rename_i a b ha hb
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
        exact .node ha hb he.1.1.1.1 he.1.1.1.2 he.1.1.2
          (prior _ hj _ _ he.1.2) (prior _ hk _ _ he.2)
      · cases he

example : checkCongruenceProofs #[] #[(0,1)] #[⟨0,1,.seed 0⟩] = true := by
  simp only [checkCongruenceProofs, Array.all_eq_true_iff_forall_mem]
  simp [Array.mem_range, checkCongruenceRow]

/-- Equivalence generated by authenticated equality edges. Congruence-generation
must justify its input edges; the forest verifier does not invent equality axioms. -/
inductive ForestEquivalent (edges : Array (Nat × Nat)) : Nat → Nat → Prop where
  | refl (u) : ForestEquivalent edges u u
  | edge {u v} : (u, v) ∈ edges → ForestEquivalent edges u v
  | symm {u v} : ForestEquivalent edges u v → ForestEquivalent edges v u
  | trans {u v w} : ForestEquivalent edges u v → ForestEquivalent edges v w → ForestEquivalent edges u w

structure ProofForest where
  parent : Array Nat
  forestRank : Array Nat
  rep : Array Nat
  edgeIndex : Array Nat
  deriving Inhabited

/-- Every nonroot uses one authenticated edge and strictly descends. -/
def checkProofForestExec (edges : Array (Nat × Nat)) (c : ProofForest) : Bool :=
  c.forestRank.size == c.parent.size && c.rep.size == c.parent.size &&
  c.edgeIndex.size == c.parent.size &&
  (Array.range c.parent.size).all fun u =>
    let v := heightAt c.parent u
    if v == u then heightAt c.rep u == u else
      v < c.parent.size && strictHeight (heightAt c.forestRank u) (heightAt c.forestRank v) &&
      heightAt c.rep u == heightAt c.rep v &&
      (edges[heightAt c.edgeIndex u]? == some (u,v) || edges[heightAt c.edgeIndex u]? == some (v,u))

theorem checkProofForestExec_sound {edges : Array (Nat × Nat)} {c : ProofForest}
    (h : checkProofForestExec edges c = true) (u : Nat) (hu : u < c.parent.size) :
    ForestEquivalent edges u (heightAt c.rep u) := by
  simp only [checkProofForestExec, Bool.and_eq_true] at h
  have rows := Array.all_eq_true_iff_forall_mem.mp h.2
  have aux : ∀ n u, heightAt c.forestRank u = n → u < c.parent.size →
      ForestEquivalent edges u (heightAt c.rep u) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u hn hu
      have row := rows u (by simpa using hu)
      split at row
      · have hr : heightAt c.rep u = u := by simpa using row
        rw [hr]; exact .refl u
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, strictHeight,
          decide_eq_true_eq] at row
        obtain ⟨⟨⟨hv, hlt⟩, hr⟩, hedge⟩ := row
        have step : ForestEquivalent edges u (heightAt c.parent u) := by
          rcases hedge with he | he
          · exact .edge (Array.mem_of_getElem? he)
          · exact .symm (.edge (Array.mem_of_getElem? he))
        rw [hr]
        exact .trans step (ih _ (by omega) _ rfl hv)
  exact aux _ u rfl hu

example : checkProofForestExec #[(0,1)] ⟨#[1,1], #[1,0], #[1,1], #[0,0]⟩ = true := by
  simp only [checkProofForestExec, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp [heightAt, strictHeight, Array.mem_range]
  intro u hu
  have : u = 0 ∨ u = 1 := by omega
  rcases this with rfl | rfl <;> decide

#tooth checkProofForestExec_sound by mutation strictHeight := fun a b => decide (b ≤ a)

/-- Composition: the ranked forest transports only equalities justified by the
checked congruence proof DAG, whose leaves refer to the committed seed table. -/
theorem checkedForest_congruence_sound {pool : Array CamWord64} {seeds : Array (Nat × Nat)}
    {rows : Array CongruenceRow} {c : ProofForest}
    (hp : checkCongruenceProofs pool seeds rows = true)
    (hf : checkProofForestExec (rows.map (fun r => (r.lhs,r.rhs))) c = true)
    (u : Nat) (hu : u < c.parent.size) : CamCongruence pool seeds u (heightAt c.rep u) := by
  have lift : ∀ a b, ForestEquivalent (rows.map (fun r => (r.lhs,r.rhs))) a b → CamCongruence pool seeds a b := by
    intro a b forest
    induction forest with
    | refl u => exact .refl u
    | edge he =>
      obtain ⟨r, hr, he⟩ := Array.mem_map.mp he
      obtain ⟨i, hi, hrow⟩ := Array.mem_iff_getElem.mp hr
      have h := checkCongruenceProofs_sound hp i hi
      rw [hrow] at h
      cases he
      exact h
    | symm _ ih => exact .symm ih
    | trans _ _ h₁ h₂ => exact .trans h₁ h₂
  exact lift _ _ (checkProofForestExec_sound hf u hu)

structure LinearCell where
  cellId : Nat
  birthStep : Nat
  payload : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

structure Consumption where
  cell : LinearCell
  consumeStep : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

structure LinMem where
  initCells : Array LinearCell
  producedCells : Array LinearCell
  consumedCells : Array Consumption
  finalCells : Array LinearCell
  deriving Inhabited

@[expose] def births (m : LinMem) : Array LinearCell := m.initCells ++ m.producedCells
@[expose] def exits (m : LinMem) : Array LinearCell := m.consumedCells.map Consumption.cell ++ m.finalCells
@[expose] def sortCells (a : Array LinearCell) : Array LinearCell :=
  a.mergeSort (fun x y => x.cellId ≤ y.cellId)
@[expose] def bornBefore (c : Consumption) : Bool := c.cell.birthStep < c.consumeStep

/-- Sorting is O(n log n); equality, freshness, and causality are linear passes.
Birth timestamps must additionally be bound to producer events by the transition relation. -/
def checkLinMemExec (m : LinMem) : Bool :=
  let allocated := sortCells (births m)
  let retired := sortCells (exits m)
  decide (allocated = retired) && checkStrictKeys (allocated.map LinearCell.cellId) &&
    m.consumedCells.all bornBefore

/-- Exact multiset balance plus distinct occurrence IDs: every allocation is used exactly
once on the RHS, either consumed or final. Payload and birth time are part of equality. -/
theorem linmem_sound {m : LinMem} (h : checkLinMemExec m = true) :
    (births m).toList.Perm (exits m).toList ∧
    ((births m).toList.map LinearCell.cellId).Nodup ∧
    ((exits m).toList.map LinearCell.cellId).Nodup ∧
    (∀ c ∈ m.consumedCells, c.cell ∈ births m ∧ c.cell.birthStep < c.consumeStep) := by
  simp only [checkLinMemExec, Bool.and_eq_true, decide_eq_true_eq] at h
  have bp : (sortCells (births m)).toList.Perm (births m).toList := by
    simpa [sortCells, Array.perm_iff_toList_perm] using (Array.mergeSort_perm (xs := (births m)))
  have ep : (sortCells (exits m)).toList.Perm (exits m).toList := by
    simpa [sortCells, Array.perm_iff_toList_perm] using (Array.mergeSort_perm (xs := (exits m)))
  have balance := bp.symm.trans (h.1.1 ▸ ep)
  have hn := checkStrictKeys_nodup h.1.2
  have bn : ((births m).toList.map LinearCell.cellId).Nodup :=
    (bp.map LinearCell.cellId).nodup_iff.mp (by simpa using hn)
  refine ⟨balance, bn, (balance.map LinearCell.cellId).nodup_iff.mp bn, ?_⟩
  intro c hc
  have he : c.cell ∈ (exits m).toList := by
    simp only [exits, Array.toList_append, List.mem_append, Array.toList_map]
    exact Or.inl (List.mem_map.mpr ⟨c, by simpa using hc, rfl⟩)
  refine ⟨by simpa using balance.mem_iff.mpr he, ?_⟩
  exact of_decide_eq_true ((Array.all_eq_true_iff_forall_mem.mp h.2) c hc)

theorem linmem_allocation_unique {m : LinMem} (h : checkLinMemExec m = true)
    (i j : Fin (births m).size) (he : (births m)[i.val].cellId = (births m)[j.val].cellId) : i = j := by
  have hn := (linmem_sound h).2.1
  have he' : ((births m).toList.map LinearCell.cellId)[i.val] =
      ((births m).toList.map LinearCell.cellId)[j.val] := by simpa using he
  exact Fin.ext (hn.getElem_inj.mp he')

theorem linmem_consumed_once {m : LinMem} (h : checkLinMemExec m = true)
    (i j : Fin m.consumedCells.size)
    (he : m.consumedCells[i.val].cell.cellId = m.consumedCells[j.val].cell.cellId) : i = j := by
  have hn := (linmem_sound h).2.2.1
  simp only [exits, Array.toList_append, Array.toList_map, List.map_append, List.map_map] at hn
  have hc := (List.nodup_append.mp hn).1
  apply Fin.ext
  apply (hc.getElem_inj (hi := by simp) (hj := by simp)).mp
  simpa using he

theorem linmem_consumed_not_final {m : LinMem} (h : checkLinMemExec m = true)
    (c : Consumption) (hc : c ∈ m.consumedCells) (f : LinearCell) (hf : f ∈ m.finalCells) :
    c.cell.cellId ≠ f.cellId := by
  have hn := (linmem_sound h).2.2.1
  simp only [exits, Array.toList_append, Array.toList_map, List.map_append, List.map_map] at hn
  exact (List.nodup_append.mp hn).2.2 c.cell.cellId
    (List.mem_map.mpr ⟨c, by simpa using hc, rfl⟩) f.cellId
    (List.mem_map.mpr ⟨f, by simpa using hf, rfl⟩)

/-- A circulating pair cannot allocate each resource after consuming the other. -/
theorem ghostCycle_rejected_by_linMem (m : LinMem) (g h : Consumption)
    (hg : g ∈ m.consumedCells) (hh : h ∈ m.consumedCells)
    (gh : g.cell.birthStep = h.consumeStep) (hg' : h.cell.birthStep = g.consumeStep) :
    checkLinMemExec m = false := by
  cases hc : checkLinMemExec m
  · rfl
  · obtain ⟨_, _, _, causal⟩ := linmem_sound hc
    have gtime := (causal g hg).2
    have htime := (causal h hh).2
    omega

#tooth linmem_sound by mutation bornBefore := fun _ => true
#tooth ghostCycle_rejected_by_linMem by mutation bornBefore := fun _ => true

example : checkLinMemExec ⟨#[⟨7, 0, 42⟩], #[], #[⟨⟨7, 0, 42⟩, 1⟩], #[]⟩ = true := by
  simp [checkLinMemExec, births, exits, sortCells, checkStrictKeys, bornBefore, Array.range_eq_range']

end Obend.SymbolicZk.Cam
