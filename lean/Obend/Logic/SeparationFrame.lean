module
/-
# Obend.Logic.SeparationFrame — Constructive PCM Separation Logic, `HeapExec` Frame Rule & `AuthCamera`

1. `LawfulPCM`, `SepProp`, `∗`, `-∗` (`sep_wand_adj`), `sepAll`, and `FPU` (`fpu_refl`, `fpu_trans`, `fpu_frame`).
2. Strictly-sorted `HeapExec Val`, `disjointMerge_spec_iff`, and `hoare_sep_frame` (`transferCells_framed`).
3. Epistemic `AuthCamera` (`ConservedValue` $\sum \delta = 0$, `grow_authority_fpu`, `spend_nullifier_fpu`,
   and refutation `uncoordinated_forget_nullifier_not_fpu`).
-/

public section
namespace Obend.Logic
set_option autoImplicit false
universe u v

/-! ## 1. Constructive Partial Commutative Monoids (`LawfulPCM`) and `FPU` -/

/-- Constructive Partial Commutative Monoid (PCM / Resource Algebra). -/
class LawfulPCM (M : Type u) where
  /-- Partial resource composition (`none` when resources conflict). -/
  op? : M → M → Option M
  /-- Identity / empty resource. -/
  one : M
  /-- Commutativity of partial composition. -/
  op_comm : ∀ a b : M, op? a b = op? b a
  /-- Associativity of partial composition (`(a • b) • c = a • (b • c)` in `Option`). -/
  op_assoc : ∀ a b c : M,
    (op? a b).bind (fun ab => op? ab c) = (op? b c).bind (fun bc => op? a bc)
  /-- Left unit law (`one • a = some a`). -/
  one_op : ∀ a : M, op? one a = some a

/-- Generic helper deriving `Option.bind` associativity from commutativity + right-reassociation. -/
theorem option_op_assoc_of_comm_forward {M : Type u} (op : M → M → Option M)
    (hcomm : ∀ x y : M, op x y = op y x)
    (hforward : ∀ {x y z xy xyz : M}, op x y = some xy → op xy z = some xyz →
      ∃ yz : M, op y z = some yz ∧ op x yz = some xyz)
    (a b c : M) :
    (op a b).bind (fun ab => op ab c) = (op b c).bind (fun bc => op a bc) := by
  cases hl : (op a b).bind (fun ab => op ab c) with
  | some abc =>
    rcases Option.bind_eq_some_iff.1 hl with ⟨ab, hab, habc⟩
    obtain ⟨bc, hbc, ha_bc⟩ := hforward hab habc
    rw [hbc]; dsimp only [Option.bind]; exact ha_bc.symm
  | none =>
    cases hr : (op b c).bind (fun bc => op a bc) with
    | none => rfl
    | some abc =>
      rcases Option.bind_eq_some_iff.1 hr with ⟨bc, hbc, ha_bc⟩
      have hcb : op c b = some bc := by rw [hcomm]; exact hbc
      have hbc_a : op bc a = some abc := by rw [hcomm]; exact ha_bc
      obtain ⟨ba, hba, hc_ba⟩ := hforward hcb hbc_a
      have hab : op a b = some ba := by rw [hcomm]; exact hba
      have hab_c : op ba c = some abc := by rw [hcomm]; exact hc_ba
      rw [hab] at hl; dsimp only [Option.bind] at hl; rw [hab_c] at hl
      cases hl

namespace LawfulPCM
variable {M : Type u} [LawfulPCM M]

theorem op_one (a : M) : op? a (one : M) = some a := by rw [op_comm, one_op]

theorem op_assoc_right {a b c ab abc : M}
    (hab : op? a b = some ab) (habc : op? ab c = some abc) :
    ∃ bc : M, op? b c = some bc ∧ op? a bc = some abc := by
  have hassoc := op_assoc a b c
  rw [hab] at hassoc; dsimp only [Option.bind] at hassoc; rw [habc] at hassoc
  cases hbc : op? b c with
  | none => rw [hbc] at hassoc; cases hassoc
  | some bc => rw [hbc] at hassoc; dsimp only [Option.bind] at hassoc; exact ⟨bc, rfl, hassoc.symm⟩

theorem op_assoc_left {a b c bc abc : M}
    (hbc : op? b c = some bc) (habc : op? a bc = some abc) :
    ∃ ab : M, op? a b = some ab ∧ op? ab c = some abc := by
  have hassoc := op_assoc a b c
  rw [hbc] at hassoc; dsimp only [Option.bind] at hassoc; rw [habc] at hassoc
  cases hab : op? a b with
  | none => rw [hab] at hassoc; cases hassoc
  | some ab => rw [hab] at hassoc; dsimp only [Option.bind] at hassoc; exact ⟨ab, rfl, hassoc⟩

/-- Compatibility predicate: `a` and `b` have a defined composition. -/
@[expose] def Compat (a b : M) : Prop := (op? a b).isSome = true
theorem compat_symm {a b : M} (h : Compat a b) : Compat b a := by unfold Compat at h ⊢; rw [op_comm]; exact h
theorem compat_one_right (a : M) : Compat a one := by simp [Compat, op_one]
theorem compat_one_left (a : M) : Compat one a := by simp [Compat, one_op]
end LawfulPCM

/-- **Frame-Preserving Update (`FPU a B`)**: every resource `frame` compatible with `a` remains
    compatible with at least one target resource `b` satisfying `B b`. -/
@[expose] def FPU {M : Type u} [LawfulPCM M] (a : M) (B : M → Prop) : Prop :=
  ∀ frame : M, (LawfulPCM.op? a frame).isSome = true →
    ∃ b : M, B b ∧ (LawfulPCM.op? b frame).isSome = true
@[expose] def FPUDet {M : Type u} [LawfulPCM M] (a b : M) : Prop := FPU a (fun x => x = b)
theorem fpuDet_iff {M : Type u} [LawfulPCM M] {a b : M} :
    FPUDet a b ↔ ∀ frame : M, (LawfulPCM.op? a frame).isSome = true →
      (LawfulPCM.op? b frame).isSome = true :=
  ⟨fun h frame hf => by obtain ⟨b', rfl, hb'⟩ := h frame hf; exact hb',
   fun h frame hf => ⟨b, rfl, h frame hf⟩⟩
theorem fpu_refl {M : Type u} [LawfulPCM M] (a : M) {B : M → Prop} (ha : B a) : FPU a B :=
  fun _ hf => ⟨a, ha, hf⟩

theorem fpu_trans {M : Type u} [LawfulPCM M] {a : M} {B C : M → Prop}
    (h₁ : FPU a B) (h₂ : ∀ b, B b → FPU b C) : FPU a C := by
  intro frame hf
  obtain ⟨b, hB, hbf⟩ := h₁ frame hf
  exact h₂ b hB frame hbf

/-- Local framing of `FPU` across PCM composition `a • r = some ar`. -/
theorem fpu_frame {M : Type u} [LawfulPCM M] {a r ar : M} {B : M → Prop}
    (hfpu : FPU a B) (har : LawfulPCM.op? a r = some ar) :
    FPU ar (fun br => ∃ b, B b ∧ LawfulPCM.op? b r = some br) := by
  intro frame hcompat
  rcases Option.isSome_iff_exists.1 hcompat with ⟨all, hall⟩
  obtain ⟨rf, hrf, harf⟩ := LawfulPCM.op_assoc_right har hall
  obtain ⟨b, hB, hb_rf⟩ := hfpu rf (by rw [harf]; rfl)
  rcases Option.isSome_iff_exists.1 hb_rf with ⟨all', hall'⟩
  obtain ⟨br, hbr, hbr_f⟩ := LawfulPCM.op_assoc_left hrf hall'
  exact ⟨br, ⟨b, hB, hbr⟩, by rw [hbr_f]; rfl⟩

/-! ## 2. Spatial Assertions (`SepProp`, `∗`, `-∗`, `⊢ₛ`, `sep_wand_adj`, `sepAll`) -/

abbrev SepProp (M : Type u) : Type u := M → Prop
@[expose] def sepEntails {M : Type u} (P Q : SepProp M) : Prop := ∀ m : M, P m → Q m
@[expose] def sepEmp {M : Type u} [LawfulPCM M] : SepProp M := fun m => m = LawfulPCM.one
@[expose] def sepPure {M : Type u} (φ : Prop) : SepProp M := fun _ => φ
@[expose] def sepConj {M : Type u} [LawfulPCM M] (P Q : SepProp M) : SepProp M :=
  fun m => ∃ m₁ m₂ : M, LawfulPCM.op? m₁ m₂ = some m ∧ P m₁ ∧ Q m₂
@[expose] def sepWand {M : Type u} [LawfulPCM M] (P Q : SepProp M) : SepProp M :=
  fun m => ∀ m' m_all : M, LawfulPCM.op? m m' = some m_all → P m' → Q m_all

infix:50 " ⊢ₛ " => sepEntails
infixr:70 " ∗ " => sepConj
infixr:60 " -∗ " => sepWand

section SepAlgebra
variable {M : Type u}
theorem sepEntails_refl (P : SepProp M) : P ⊢ₛ P := fun _ h => h
theorem sepEntails_trans {P Q R : SepProp M} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun m hp => h₂ m (h₁ m hp)
theorem sepEntails_antisymm {P Q : SepProp M} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ P) : P = Q :=
  funext fun m => propext ⟨h₁ m, h₂ m⟩
theorem sepEntails_congr {P P' Q Q' : SepProp M}
    (hP : P = P') (hQ : Q = Q') (h : P' ⊢ₛ Q') : P ⊢ₛ Q := by subst hP; subst hQ; exact h

variable [LawfulPCM M]
theorem sep_congr_eq {P P' Q Q' : SepProp M} (hP : P = P') (hQ : Q = Q') :
    (P ∗ Q) = (P' ∗ Q') := by subst hP; subst hQ; rfl

theorem sep_comm (P Q : SepProp M) : (P ∗ Q) = (Q ∗ P) := by
  apply sepEntails_antisymm
  · rintro m ⟨m₁, m₂, hop, hp, hq⟩; rw [LawfulPCM.op_comm] at hop; exact ⟨m₂, m₁, hop, hq, hp⟩
  · rintro m ⟨m₂, m₁, hop, hq, hp⟩; rw [LawfulPCM.op_comm] at hop; exact ⟨m₁, m₂, hop, hp, hq⟩

theorem sep_assoc (P Q R : SepProp M) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  apply sepEntails_antisymm
  · rintro m ⟨ab, c, habc, ⟨a, b, hab, hp, hq⟩, hr⟩
    obtain ⟨bc, hbc, ha_bc⟩ := LawfulPCM.op_assoc_right hab habc
    exact ⟨a, bc, ha_bc, hp, ⟨b, c, hbc, hq, hr⟩⟩
  · rintro m ⟨a, bc, ha_bc, hp, ⟨b, c, hbc, hq, hr⟩⟩
    obtain ⟨ab, hab, hab_c⟩ := LawfulPCM.op_assoc_left hbc ha_bc
    exact ⟨ab, c, hab_c, ⟨a, b, hab, hp, hq⟩, hr⟩

@[simp] theorem emp_sep (P : SepProp M) : (sepEmp ∗ P) = P := by
  apply sepEntails_antisymm
  · rintro m ⟨m₁, m₂, hop, rfl, hp⟩; rw [LawfulPCM.one_op] at hop; cases hop; exact hp
  · exact fun m hp => ⟨LawfulPCM.one, m, LawfulPCM.one_op m, rfl, hp⟩
@[simp] theorem sep_emp (P : SepProp M) : (P ∗ sepEmp) = P := by rw [sep_comm, emp_sep]
theorem sep_mono {P₁ P₂ Q₁ Q₂ : SepProp M}
    (hP : P₁ ⊢ₛ P₂) (hQ : Q₁ ⊢ₛ Q₂) : (P₁ ∗ Q₁) ⊢ₛ (P₂ ∗ Q₂) := by
  rintro m ⟨m₁, m₂, hop, hp, hq⟩; exact ⟨m₁, m₂, hop, hP m₁ hp, hQ m₂ hq⟩

/-- **`sep_wand_adj`**: Residual / monoidal-closed adjunction `(P ∗ Q ⊢ₛ R) ↔ (P ⊢ₛ Q -∗ R)`. -/
theorem sep_wand_adj {P Q R : SepProp M} : ((P ∗ Q) ⊢ₛ R) ↔ (P ⊢ₛ (Q -∗ R)) :=
  ⟨fun h m₁ hp m₂ m_all hop hq => h m_all ⟨m₁, m₂, hop, hp, hq⟩,
   fun h m ⟨m₁, m₂, hop, hp, hq⟩ => h m₁ hp m₂ m hop hq⟩
theorem wand_elim_left {P Q : SepProp M} : ((P -∗ Q) ∗ P) ⊢ₛ Q := sep_wand_adj.2 (sepEntails_refl (P -∗ Q))
theorem wand_elim_right {P Q : SepProp M} : (P ∗ (P -∗ Q)) ⊢ₛ Q := by rw [sep_comm]; exact wand_elim_left

/-- Right-associated spatial list product used by the `by sep_cancel` normalizer. -/
@[expose] def sepAll : List (SepProp M) → SepProp M
  | [] => sepEmp
  | P :: Ps => P ∗ sepAll Ps
theorem sepAll_nil : (sepEmp : SepProp M) = sepAll [] := rfl
theorem sepAll_singleton_eq (P : SepProp M) : P = sepAll [P] := (sep_emp P).symm
theorem sepAll_append (xs ys : List (SepProp M)) : (sepAll xs ∗ sepAll ys) = sepAll (xs ++ ys) := by
  induction xs with
  | nil => simp [sepAll]
  | cons P rest ih => simp only [sepAll, List.cons_append]; rw [sep_assoc, ih]
theorem sepAll_extract (P : SepProp M) (before after : List (SepProp M)) :
    sepAll (before ++ P :: after) = (P ∗ sepAll (before ++ after)) := by
  induction before with
  | nil => rfl
  | cons Q rest ih => simp only [List.cons_append, sepAll]; rw [ih, ← sep_assoc, sep_comm Q P, sep_assoc]
theorem sepCancel_match {P : SepProp M} {before after rRest : List (SepProp M)}
    (h : sepAll (before ++ after) ⊢ₛ sepAll rRest) :
    sepAll (before ++ P :: after) ⊢ₛ (P ∗ sepAll rRest) := by
  rw [sepAll_extract]; exact sep_mono (sepEntails_refl P) h
end SepAlgebra

/-! ## 3. Disjoint Cell Heaps (`HeapExec` = Sorted `Array (Nat × Val)`) & `hoare_sep_frame` -/

abbrev HeapSpec (Val : Type u) : Type u := Nat → Option Val

@[expose] def specDisjoint {Val : Type u} (f g : HeapSpec Val) : Prop :=
  ∀ k : Nat, f k = none ∨ g k = none

@[expose] def specMerge {Val : Type u} (f g : HeapSpec Val) : HeapSpec Val :=
  fun k => match f k with | some v => some v | none => g k

theorem specDisjoint_symm {Val : Type u} {f g : HeapSpec Val}
    (h : specDisjoint f g) : specDisjoint g f := fun k => (h k).symm

theorem specMerge_comm_of_disjoint {Val : Type u} {f g : HeapSpec Val}
    (h : specDisjoint f g) : specMerge f g = specMerge g f := by
  funext k
  rcases h k with hf | hg
  · simp [specMerge, hf]; cases g k <;> rfl
  · simp [specMerge, hg]; cases f k <;> rfl

@[expose] def lookupEntries {Val : Type u} : List (Nat × Val) → Nat → Option Val
  | [], _ => none
  | (k, v) :: rest, q => if q == k then some v else lookupEntries rest q

theorem lookupEntries_none_of_forall_gt {Val : Type u} {l : List (Nat × Val)} {q : Nat}
    (hgt : ∀ p ∈ l, q < p.1) : lookupEntries l q = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    have hlt : q < k := hgt (k, v) List.mem_cons_self
    have hne : (q == k) = false := beq_false_of_ne (by omega)
    simp only [lookupEntries, hne]
    exact ih (fun p hp => hgt p (List.mem_cons_of_mem _ hp))

theorem sorted_entries_ext {Val : Type u} :
    ∀ {l₁ l₂ : List (Nat × Val)},
      List.Pairwise (fun a b => a.1 < b.1) l₁ →
      List.Pairwise (fun a b => a.1 < b.1) l₂ →
      (∀ q : Nat, lookupEntries l₁ q = lookupEntries l₂ q) →
      l₁ = l₂
  | [], [], _, _, _ => rfl
  | (k, _) :: _, [], _, _, heq => by have h := heq k; simp [lookupEntries] at h
  | [], (k, _) :: _, _, _, heq => by have h := heq k; simp [lookupEntries] at h
  | (k₁, v₁) :: t₁, (k₂, v₂) :: t₂, .cons hgt₁ hs₁, .cons hgt₂ hs₂, heq => by
    by_cases hlt₁ : k₁ < k₂
    · have hk₁ := heq k₁
      have hnone : lookupEntries ((k₂, v₂) :: t₂) k₁ = none :=
        lookupEntries_none_of_forall_gt fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hm; exact hlt₁; exact Nat.lt_trans hlt₁ (hgt₂ p hm)
      rw [hnone] at hk₁; simp [lookupEntries] at hk₁
    · by_cases hlt₂ : k₂ < k₁
      · have hk₂ := heq k₂
        have hnone : lookupEntries ((k₁, v₁) :: t₁) k₂ = none :=
          lookupEntries_none_of_forall_gt fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hm; exact hlt₂; exact Nat.lt_trans hlt₂ (hgt₁ p hm)
        rw [hnone] at hk₂; simp [lookupEntries] at hk₂
      · have hkeq : k₁ = k₂ := by omega
        subst hkeq
        have hveq : v₁ = v₂ := by simpa [lookupEntries] using heq k₁
        subst hveq
        have htail : ∀ q : Nat, lookupEntries t₁ q = lookupEntries t₂ q := fun q => by
          by_cases hq : q = k₁
          · subst hq; rw [lookupEntries_none_of_forall_gt hgt₁, lookupEntries_none_of_forall_gt hgt₂]
          · simpa [lookupEntries, beq_false_of_ne hq] using heq q
        rw [sorted_entries_ext hs₁ hs₂ htail]

/-- Linear-time two-pointer disjoint merge on strictly sorted `(Nat × Val)` lists. -/
@[expose] def mergeSortedEntries {Val : Type u} :
    List (Nat × Val) → List (Nat × Val) → Option (List (Nat × Val))
  | [], ys => some ys
  | (k₁, v₁) :: xs, [] => some ((k₁, v₁) :: xs)
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
    if k₁ < k₂ then (mergeSortedEntries xs ((k₂, v₂) :: ys)).map ((k₁, v₁) :: ·)
    else if k₂ < k₁ then (mergeSortedEntries ((k₁, v₁) :: xs) ys).map ((k₂, v₂) :: ·)
    else none
termination_by xs ys => xs.length + ys.length

theorem mergeSortedEntries_mem {Val : Type u} :
    ∀ {xs ys zs : List (Nat × Val)} {p : Nat × Val},
      mergeSortedEntries xs ys = some zs → p ∈ zs → p ∈ xs ∨ p ∈ ys
  | [], _, _, _, hm, hp => by simp [mergeSortedEntries] at hm; subst hm; exact Or.inr hp
  | (_, _) :: _, [], _, _, hm, hp => by simp [mergeSortedEntries] at hm; subst hm; exact Or.inl hp
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys, _, p, hm, hp => by
    simp only [mergeSortedEntries] at hm
    split at hm
    · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
      rcases List.mem_cons.1 hp with rfl | hmem
      · exact Or.inl List.mem_cons_self
      · exact (mergeSortedEntries_mem hrest hmem).imp (List.mem_cons_of_mem _) id
    · split at hm
      · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
        rcases List.mem_cons.1 hp with rfl | hmem
        · exact Or.inr List.mem_cons_self
        · exact (mergeSortedEntries_mem hrest hmem).imp id (List.mem_cons_of_mem _)
      · cases hm
termination_by xs ys _ _ _ _ => xs.length + ys.length

theorem mergeSortedEntries_sorted {Val : Type u} :
    ∀ {xs ys zs : List (Nat × Val)},
      List.Pairwise (fun a b => a.1 < b.1) xs →
      List.Pairwise (fun a b => a.1 < b.1) ys →
      mergeSortedEntries xs ys = some zs →
      List.Pairwise (fun a b => a.1 < b.1) zs
  | [], _, _, _, hys, hm => by simp [mergeSortedEntries] at hm; subst hm; exact hys
  | (_, _) :: _, [], _, hxs, _, hm => by simp [mergeSortedEntries] at hm; subst hm; exact hxs
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys, _, .cons hgx hsx, .cons hgy hsy, hm => by
    simp only [mergeSortedEntries] at hm
    split at hm
    · rename_i hlt
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
      refine .cons (fun p hp => ?_) (mergeSortedEntries_sorted hsx (.cons hgy hsy) hrest)
      rcases mergeSortedEntries_mem hrest hp with hx | hy
      · exact hgx p hx
      · rcases List.mem_cons.1 hy with rfl | hy'; exact hlt; exact Nat.lt_trans hlt (hgy p hy')
    · split at hm
      · rename_i hlt₂
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
        refine .cons (fun p hp => ?_) (mergeSortedEntries_sorted (.cons hgx hsx) hsy hrest)
        rcases mergeSortedEntries_mem hrest hp with hx | hy
        · rcases List.mem_cons.1 hx with rfl | hx'; exact hlt₂; exact Nat.lt_trans hlt₂ (hgx p hx')
        · exact hgy p hy
      · cases hm
termination_by xs ys _ _ _ _ => xs.length + ys.length

theorem mergeSortedEntries_sound {Val : Type u} :
    ∀ {xs ys zs : List (Nat × Val)},
      List.Pairwise (fun a b => a.1 < b.1) xs →
      List.Pairwise (fun a b => a.1 < b.1) ys →
      mergeSortedEntries xs ys = some zs →
      specDisjoint (lookupEntries xs) (lookupEntries ys) ∧
        ∀ q : Nat, lookupEntries zs q = specMerge (lookupEntries xs) (lookupEntries ys) q
  | [], _, _, _, _, hm => by
    simp [mergeSortedEntries] at hm; subst hm; exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | (k₁, v₁) :: xs, [], _, _, _, hm => by
    simp [mergeSortedEntries] at hm; subst hm
    refine ⟨fun _ => Or.inr rfl, fun q => ?_⟩
    unfold specMerge; cases lookupEntries ((k₁, v₁) :: xs) q <;> rfl
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys, _, .cons hgx hsx, .cons hgy hsy, hm => by
    simp only [mergeSortedEntries] at hm
    split at hm
    · rename_i hlt
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
      obtain ⟨hdisj, hlk⟩ := mergeSortedEntries_sound hsx (.cons hgy hsy) hrest
      have hy_k₁ : lookupEntries ((k₂, v₂) :: ys) k₁ = none :=
        lookupEntries_none_of_forall_gt fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp'; exact hlt; exact Nat.lt_trans hlt (hgy p hp')
      refine ⟨fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = k₁
        · subst hq; exact Or.inr hy_k₁
        · simpa [lookupEntries, beq_false_of_ne hq] using hdisj q
      · by_cases hq : q = k₁
        · subst hq; simp [lookupEntries, specMerge]
        · simpa [lookupEntries, specMerge, beq_false_of_ne hq] using hlk q
    · split at hm
      · rename_i hlt₂
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hm
        obtain ⟨hdisj, hlk⟩ := mergeSortedEntries_sound (.cons hgx hsx) hsy hrest
        have hx_k₂ : lookupEntries ((k₁, v₁) :: xs) k₂ = none :=
          lookupEntries_none_of_forall_gt fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp'; exact hlt₂; exact Nat.lt_trans hlt₂ (hgx p hp')
        refine ⟨fun q => ?_, fun q => ?_⟩
        · by_cases hq : q = k₂
          · subst hq; exact Or.inl hx_k₂
          · simpa [lookupEntries, beq_false_of_ne hq] using hdisj q
        · by_cases hq : q = k₂
          · subst hq; unfold specMerge; rw [hx_k₂]; simp [lookupEntries]
          · have hne : (q == k₂) = false := beq_false_of_ne hq
            have h1 : lookupEntries ((k₂, v₂) :: rest) q = lookupEntries rest q := by simp [lookupEntries, hne]
            rw [h1, hlk q]; unfold specMerge
            cases lookupEntries ((k₁, v₁) :: xs) q
            · simp [lookupEntries, hne]
            · rfl
      · cases hm
termination_by xs ys _ _ _ _ => xs.length + ys.length

theorem mergeSortedEntries_complete {Val : Type u} :
    ∀ {xs ys : List (Nat × Val)},
      List.Pairwise (fun a b => a.1 < b.1) xs →
      List.Pairwise (fun a b => a.1 < b.1) ys →
      specDisjoint (lookupEntries xs) (lookupEntries ys) →
      (mergeSortedEntries xs ys).isSome = true
  | [], _, _, _, _ => by simp [mergeSortedEntries]
  | (_, _) :: _, [], _, _, _ => by simp [mergeSortedEntries]
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys, .cons hgx hsx, .cons hgy hsy, hdisj => by
    simp only [mergeSortedEntries]
    by_cases hlt₁ : k₁ < k₂
    · simp only [hlt₁, ite_true]
      have hsub : specDisjoint (lookupEntries xs) (lookupEntries ((k₂, v₂) :: ys)) := fun q => by
        by_cases hq : q = k₁
        · subst hq; exact Or.inl (lookupEntries_none_of_forall_gt hgx)
        · simpa [lookupEntries, beq_false_of_ne hq] using hdisj q
      rcases Option.isSome_iff_exists.1 (mergeSortedEntries_complete hsx (.cons hgy hsy) hsub) with ⟨_, hrec⟩
      simp [hrec]
    · simp only [hlt₁, ite_false]
      by_cases hlt₂ : k₂ < k₁
      · simp only [hlt₂, ite_true]
        have hsub : specDisjoint (lookupEntries ((k₁, v₁) :: xs)) (lookupEntries ys) := fun q => by
          by_cases hq : q = k₂
          · subst hq; exact Or.inr (lookupEntries_none_of_forall_gt hgy)
          · simpa [lookupEntries, beq_false_of_ne hq] using hdisj q
        rcases Option.isSome_iff_exists.1 (mergeSortedEntries_complete (.cons hgx hsx) hsy hsub) with ⟨_, hrec⟩
        simp [hrec]
      · have hkeq : k₁ = k₂ := by omega
        subst hkeq; have hk := hdisj k₁; simp [lookupEntries] at hk
termination_by xs ys _ _ _ => xs.length + ys.length

/-- Executable cell heap backed by a strictly key-sorted `Array (Nat × Val)`. -/
structure HeapExec (Val : Type u) where
  entries : Array (Nat × Val)
  sorted : List.Pairwise (fun a b => a.1 < b.1) entries.toList

namespace HeapExec

variable {Val : Type u}

@[expose] def toSpec (h : HeapExec Val) : HeapSpec Val := lookupEntries h.entries.toList

/-- Canonical extensionality: two sorted `HeapExec` arrays with the same `toSpec` are equal! -/
theorem ext {h₁ h₂ : HeapExec Val} (heq : ∀ k, h₁.toSpec k = h₂.toSpec k) : h₁ = h₂ := by
  cases h₁ with | mk a₁ s₁ =>
  cases h₂ with | mk a₂ s₂ =>
  have harr : a₁ = a₂ := Array.ext' (sorted_entries_ext s₁ s₂ heq)
  subst harr; rfl

@[expose] def empty : HeapExec Val := ⟨#[], .nil⟩

@[simp] theorem empty_toSpec (k : Nat) : (empty : HeapExec Val).toSpec k = none := rfl

@[expose] def singleton (k : Nat) (v : Val) : HeapExec Val :=
  ⟨#[(k, v)], .cons (fun _ hp => by cases hp) .nil⟩

theorem singleton_toSpec (k q : Nat) (v : Val) :
    (singleton k v).toSpec q = if q == k then some v else none := rfl

@[expose] def disjointMerge (h₁ h₂ : HeapExec Val) : Option (HeapExec Val) :=
  match hm : mergeSortedEntries h₁.entries.toList h₂.entries.toList with
  | none => none
  | some zs => some ⟨Array.mk zs, mergeSortedEntries_sorted h₁.sorted h₂.sorted hm⟩

/-- **`Spec ↔ Exec` Disjoint Merge Theorem (`disjointMerge_spec_iff`)**. -/
theorem disjointMerge_spec_iff {h₁ h₂ h : HeapExec Val} :
    disjointMerge h₁ h₂ = some h ↔
      specDisjoint h₁.toSpec h₂.toSpec ∧ h.toSpec = specMerge h₁.toSpec h₂.toSpec := by
  constructor
  · intro hm
    unfold disjointMerge at hm; split at hm; · cases hm
    rename_i zs hzs; simp only [Option.some.injEq] at hm; subst hm
    obtain ⟨hdisj, hlk⟩ := mergeSortedEntries_sound h₁.sorted h₂.sorted hzs
    exact ⟨hdisj, funext hlk⟩
  · rintro ⟨hdisj, hspec⟩
    rcases Option.isSome_iff_exists.1 (mergeSortedEntries_complete h₁.sorted h₂.sorted hdisj) with ⟨zs, hzs⟩
    obtain ⟨_, hlk⟩ := mergeSortedEntries_sound h₁.sorted h₂.sorted hzs
    have heq : (⟨Array.mk zs, mergeSortedEntries_sorted h₁.sorted h₂.sorted hzs⟩ : HeapExec Val) = h :=
      ext fun k => by change lookupEntries zs k = h.toSpec k; rw [hlk k, hspec]; rfl
    unfold disjointMerge; split
    · rename_i hnone; rw [hzs] at hnone; cases hnone
    · rename_i zs' hzs'; rw [hzs] at hzs'; cases hzs'; simp [heq]

theorem disjointMerge_isSome_iff {h₁ h₂ : HeapExec Val} :
    (disjointMerge h₁ h₂).isSome = true ↔ specDisjoint h₁.toSpec h₂.toSpec :=
  ⟨fun hs => by rcases Option.isSome_iff_exists.1 hs with ⟨h, hh⟩; exact (disjointMerge_spec_iff.1 hh).1,
   fun hdisj => by
     rcases Option.isSome_iff_exists.1 (mergeSortedEntries_complete h₁.sorted h₂.sorted hdisj) with ⟨zs, hzs⟩
     unfold disjointMerge; split
     · rename_i hnone; rw [hzs] at hnone; cases hnone
     · rfl⟩

theorem disjointMerge_comm (h₁ h₂ : HeapExec Val) : disjointMerge h₁ h₂ = disjointMerge h₂ h₁ := by
  cases hm₁ : disjointMerge h₁ h₂ with
  | none =>
    cases hm₂ : disjointMerge h₂ h₁ with
    | none => rfl
    | some h =>
      have his := disjointMerge_isSome_iff.2 (specDisjoint_symm (disjointMerge_spec_iff.1 hm₂).1)
      rw [hm₁] at his; cases his
  | some h =>
    obtain ⟨hdisj, hspec⟩ := disjointMerge_spec_iff.1 hm₁
    symm
    exact disjointMerge_spec_iff.2 ⟨specDisjoint_symm hdisj, by rw [hspec, specMerge_comm_of_disjoint hdisj]⟩

instance instLawfulPCMHeapExec : LawfulPCM (HeapExec Val) where
  op? := disjointMerge
  one := empty
  one_op h := disjointMerge_spec_iff.2 ⟨fun _ => Or.inl rfl, rfl⟩
  op_comm := disjointMerge_comm
  op_assoc := option_op_assoc_of_comm_forward disjointMerge disjointMerge_comm
    fun {x y z xy xyz} hab habc => by
      obtain ⟨hd_ab, hs_ab⟩ := disjointMerge_spec_iff.1 hab
      obtain ⟨hd_abc, hs_abc⟩ := disjointMerge_spec_iff.1 habc
      have hd_bc : specDisjoint y.toSpec z.toSpec := fun k => by
        rcases hd_abc k with hab_n | hc_n
        · rw [hs_ab] at hab_n; unfold specMerge at hab_n
          cases ha : x.toSpec k <;> rw [ha] at hab_n
          · exact Or.inl hab_n
          · cases hab_n
        · exact Or.inr hc_n
      rcases Option.isSome_iff_exists.1 (disjointMerge_isSome_iff.2 hd_bc) with ⟨bc, hbc⟩
      obtain ⟨_, hs_bc⟩ := disjointMerge_spec_iff.1 hbc
      refine ⟨bc, hbc, disjointMerge_spec_iff.2 ⟨fun k => ?_, funext fun k => ?_⟩⟩
      · cases ha : x.toSpec k with
        | none => exact Or.inl rfl
        | some v =>
          have hb_n : y.toSpec k = none := by
            rcases hd_ab k with h1 | h2
            · rw [ha] at h1; cases h1
            · exact h2
          have hc_n : z.toSpec k = none := by
            rcases hd_abc k with h1 | h2
            · rw [hs_ab] at h1; simp [specMerge, ha] at h1
            · exact h2
          right; rw [hs_bc]; simp [specMerge, hb_n, hc_n]
      · rw [hs_abc, hs_ab, hs_bc]
        unfold specMerge
        cases x.toSpec k <;> cases y.toSpec k <;> rfl

end HeapExec

/-- Points-to spatial assertion `ptsTo k v` (`k ↦ₕ v`). -/
@[expose] def ptsTo {Val : Type u} (k : Nat) (v : Val) : SepProp (HeapExec Val) :=
  fun h => h = HeapExec.singleton k v

infix:75 " ↦ₕ " => ptsTo

theorem ptsTo_sep_disjoint {Val : Type u} {k₁ k₂ : Nat} {v₁ v₂ : Val} {h : HeapExec Val}
    (hsep : ((k₁ ↦ₕ v₁) ∗ (k₂ ↦ₕ v₂)) h) : k₁ ≠ k₂ := by
  rcases hsep with ⟨h₁, h₂, hm, rfl, rfl⟩
  intro heq; subst heq
  have hk := (HeapExec.disjointMerge_spec_iff.1 hm).1 k₁
  simp [HeapExec.singleton_toSpec] at hk

abbrev HeapOp (Val : Type u) (α : Type v) : Type (max u v) :=
  HeapExec Val → Option (α × HeapExec Val)

@[expose] def IsLocalOp {Val : Type u} {α : Type v} (op : HeapOp Val α) : Prop :=
  ∀ (h₁ h_frame h h₁' : HeapExec Val) (res : α),
    op h₁ = some (res, h₁') →
    LawfulPCM.op? h₁ h_frame = some h →
    ∃ h' : HeapExec Val, LawfulPCM.op? h₁' h_frame = some h' ∧ op h = some (res, h')

@[expose] def HoareSep {Val : Type u} {α : Type v}
    (P : SepProp (HeapExec Val)) (op : HeapOp Val α) (Q : α → SepProp (HeapExec Val)) : Prop :=
  ∀ h : HeapExec Val, P h → ∃ (res : α) (h' : HeapExec Val), op h = some (res, h') ∧ Q res h'

/-- **`hoare_sep_frame` (Local Separation Frame Rule)**: `{P} op {Q} → {P ∗ R} op {Q ∗ R}`. -/
theorem hoare_sep_frame {Val : Type u} {α : Type v}
    {P : SepProp (HeapExec Val)} {op : HeapOp Val α} {Q : α → SepProp (HeapExec Val)}
    (R : SepProp (HeapExec Val))
    (hLocal : IsLocalOp op)
    (hTriple : HoareSep P op Q) :
    HoareSep (P ∗ R) op (fun res => Q res ∗ R) := by
  rintro h ⟨h₁, h₂, hmerge, hP, hR⟩
  obtain ⟨res, h₁', hop₁, hQ⟩ := hTriple h₁ hP
  obtain ⟨h', hmerge', hop⟩ := hLocal h₁ h₂ h h₁' res hop₁ hmerge
  exact ⟨res, h', hop, ⟨h₁', h₂, hmerge', hQ, hR⟩⟩

theorem hoare_sep_conseq_frame {Val : Type u} {α : Type v}
    {P P_sub R : SepProp (HeapExec Val)} {op : HeapOp Val α}
    {Q_sub Q : α → SepProp (HeapExec Val)}
    (hLocal : IsLocalOp op)
    (hSub : HoareSep P_sub op Q_sub)
    (hPre : P ⊢ₛ (P_sub ∗ R))
    (hPost : ∀ res : α, (Q_sub res ∗ R) ⊢ₛ Q res) :
    HoareSep P op Q := by
  intro h hp
  obtain ⟨res, h', hop, hQR⟩ := hoare_sep_frame R hLocal hSub h (hPre h hp)
  exact ⟨res, h', hop, hPost res h' hQR⟩

/-! ### Concrete Local Heap Operations (`readCell`, `writeCell`, 2-Cell `transferCells`) -/

@[expose] def updateExistingEntries {Val : Type u} (k : Nat) (v : Val) :
    List (Nat × Val) → Option (List (Nat × Val))
  | [] => none
  | (k', v') :: rest =>
    if k == k' then some ((k', v) :: rest)
    else (updateExistingEntries k v rest).map ((k', v') :: ·)

theorem updateExistingEntries_keys {Val : Type u} {k : Nat} {v : Val} :
    ∀ {xs ys : List (Nat × Val)},
      updateExistingEntries k v xs = some ys → xs.map Prod.fst = ys.map Prod.fst
  | [], _, h => by cases h
  | _ :: _, _, h => by
    simp only [updateExistingEntries] at h; split at h
    · cases h; rfl
    · obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 h; simp [updateExistingEntries_keys htl]

theorem pairwise_of_keys_eq {Val : Type u} :
    ∀ {xs ys : List (Nat × Val)},
      xs.map Prod.fst = ys.map Prod.fst →
      List.Pairwise (fun a b => a.1 < b.1) xs →
      List.Pairwise (fun a b => a.1 < b.1) ys
  | [], [], _, _ => .nil
  | _ :: _, [], heq, _ => by cases heq
  | [], _ :: _, heq, _ => by cases heq
  | (_, _) :: _, (_, _) :: ty, heq, .cons hgt hs => by
    simp only [List.map_cons, List.cons.injEq] at heq
    obtain ⟨hkhd, htk⟩ := heq
    refine .cons (fun p hp => ?_) (pairwise_of_keys_eq htk hs)
    have hmem : p.1 ∈ ty.map Prod.fst := List.mem_map_of_mem hp
    rw [← htk] at hmem
    rcases List.mem_map.1 hmem with ⟨q, hq, hqk⟩
    dsimp only at hkhd ⊢
    rw [← hkhd, ← hqk]; exact hgt q hq

theorem updateExistingEntries_lookup {Val : Type u} {k : Nat} {v : Val} :
    ∀ {xs ys : List (Nat × Val)},
      List.Pairwise (fun a b => a.1 < b.1) xs →
      updateExistingEntries k v xs = some ys →
      (∃ old : Val, lookupEntries xs k = some old) ∧
        ∀ q : Nat, lookupEntries ys q = if q == k then some v else lookupEntries xs q
  | [], _, _, h => by cases h
  | (k', v') :: rest, _, .cons _ hs, h => by
    simp only [updateExistingEntries] at h; split at h
    · rename_i heq
      have hkeq : k = k' := eq_of_beq heq; subst hkeq; cases h
      exact ⟨⟨v', by simp [lookupEntries]⟩, fun q => by by_cases hq : q == k <;> simp [lookupEntries, hq]⟩
    · rename_i hne
      obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨⟨old, hold⟩, hlk⟩ := updateExistingEntries_lookup hs htl
      refine ⟨⟨old, by simp [lookupEntries, hne, hold]⟩, fun q => ?_⟩
      by_cases hqk' : q == k'
      · have heq' : q = k' := eq_of_beq hqk'; subst heq'
        have hqk_f : (q == k) = false := by
          cases hqk : q == k
          · rfl
          · simp [(eq_of_beq hqk).symm] at hne
        simp [lookupEntries, hqk_f]
      · simp [lookupEntries, hqk', hlk q]

theorem updateExistingEntries_complete {Val : Type u} {k : Nat} {v old : Val} :
    ∀ {xs : List (Nat × Val)},
      lookupEntries xs k = some old → (updateExistingEntries k v xs).isSome = true
  | [], h => by cases h
  | (k', _) :: rest, h => by
    simp only [lookupEntries] at h; simp only [updateExistingEntries]
    by_cases hkk' : k == k'
    · simp [hkk']
    · simp only [hkk', Bool.false_eq_true, ↓reduceIte] at h ⊢
      rcases Option.isSome_iff_exists.1 (updateExistingEntries_complete (v := v) h) with ⟨_, hrec⟩
      simp [hrec]

@[expose] def readCell {Val : Type u} (k : Nat) : HeapOp Val Val :=
  fun h => (h.toSpec k).map (fun v => (v, h))

@[expose] def writeCell {Val : Type u} (k : Nat) (v : Val) : HeapOp Val Unit :=
  fun h =>
    match hm : updateExistingEntries k v h.entries.toList with
    | none => none
    | some ys => some ((), ⟨Array.mk ys, pairwise_of_keys_eq (updateExistingEntries_keys hm) h.sorted⟩)

@[expose] def transferCells (src dst amount : Nat) : HeapOp Nat Unit :=
  fun h => do
    let (balSrc, _) ← readCell src h
    let (balDst, _) ← readCell dst h
    if src != dst && decide (amount ≤ balSrc) then
      let (_, h₁) ← writeCell src (balSrc - amount) h
      writeCell dst (balDst + amount) h₁
    else none

theorem readCell_local {Val : Type u} (k : Nat) : IsLocalOp (readCell (Val := Val) k) := by
  intro h₁ hf h h₁' res hop hmerge
  simp only [readCell, Option.map_eq_some_iff] at hop
  obtain ⟨v, hv, hpair⟩ := hop; cases hpair
  obtain ⟨_, hspec⟩ := HeapExec.disjointMerge_spec_iff.1 hmerge
  exact ⟨h, hmerge, by simp [readCell, hspec, specMerge, hv]⟩

theorem writeCell_spec_iff {Val : Type u} {k : Nat} {v : Val} {h h' : HeapExec Val} :
    writeCell k v h = some ((), h') ↔
      (∃ old : Val, h.toSpec k = some old) ∧
        ∀ q : Nat, h'.toSpec q = if q == k then some v else h.toSpec q := by
  constructor
  · intro hw; unfold writeCell at hw; split at hw; · cases hw
    rename_i ys hys; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hw; subst hw
    exact updateExistingEntries_lookup h.sorted hys
  · rintro ⟨⟨old, hold⟩, hspec⟩
    rcases Option.isSome_iff_exists.1 (updateExistingEntries_complete (v := v) hold) with ⟨ys, hys⟩
    obtain ⟨_, hlk⟩ := updateExistingEntries_lookup h.sorted hys
    have heq : (⟨Array.mk ys, pairwise_of_keys_eq (updateExistingEntries_keys hys) h.sorted⟩ : HeapExec Val) = h' :=
      HeapExec.ext fun q => by change lookupEntries ys q = h'.toSpec q; rw [hlk q, hspec q]; rfl
    unfold writeCell; split
    · rename_i hnone; rw [hys] at hnone; cases hnone
    · rename_i ys' hys'; rw [hys] at hys'; cases hys'; simp [heq]

theorem writeCell_local {Val : Type u} (k : Nat) (v : Val) : IsLocalOp (writeCell k v) := by
  rintro h₁ hf h h₁' ⟨⟩ hw hmerge
  obtain ⟨⟨old, hold⟩, hspec₁'⟩ := writeCell_spec_iff.1 hw
  obtain ⟨hdisj, hspec_h⟩ := HeapExec.disjointMerge_spec_iff.1 hmerge
  have hf_k : hf.toSpec k = none := by
    rcases hdisj k with hk₁ | hkf
    · rw [hold] at hk₁; cases hk₁
    · exact hkf
  have hdisj' : specDisjoint h₁'.toSpec hf.toSpec := fun q => by
    by_cases hqk : q == k
    · rw [eq_of_beq hqk]; exact Or.inr hf_k
    · rw [hspec₁' q]; simp [hqk]; exact hdisj q
  rcases Option.isSome_iff_exists.1 (HeapExec.disjointMerge_isSome_iff.2 hdisj') with ⟨h', hm'⟩
  obtain ⟨_, hspec_h'⟩ := HeapExec.disjointMerge_spec_iff.1 hm'
  refine ⟨h', hm', writeCell_spec_iff.2 ⟨⟨old, by simp [hspec_h, specMerge, hold]⟩, fun q => ?_⟩⟩
  rw [hspec_h', hspec_h]
  by_cases hqk : q == k
  · have hqeq : q = k := eq_of_beq hqk; subst hqeq; simp [specMerge, hspec₁']
  · simp [specMerge, hspec₁' q, hqk]

theorem transferCells_local (src dst amount : Nat) : IsLocalOp (transferCells src dst amount) := by
  rintro h₁ hf h h₁' ⟨⟩ htr hmerge
  unfold transferCells at htr
  cases hrSrc : readCell src h₁ with
  | none => simp [hrSrc] at htr
  | some pSrc =>
    obtain ⟨bSrc, s₁⟩ := pSrc
    have hs₁ : s₁ = h₁ := by simp only [readCell, Option.map_eq_some_iff] at hrSrc; obtain ⟨_, _, hp⟩ := hrSrc; exact (Prod.mk.inj hp).2.symm
    rw [hs₁] at hrSrc
    rw [hrSrc] at htr; dsimp only [bind, Option.bind] at htr
    cases hrDst : readCell dst h₁ with
    | none => simp [hrDst] at htr
    | some pDst =>
      obtain ⟨bDst, s₂⟩ := pDst
      have hs₂ : s₂ = h₁ := by simp only [readCell, Option.map_eq_some_iff] at hrDst; obtain ⟨_, _, hp⟩ := hrDst; exact (Prod.mk.inj hp).2.symm
      rw [hs₂] at hrDst
      rw [hrDst] at htr; dsimp only [bind, Option.bind] at htr
      split at htr
      · rename_i hcond
        cases hw₁ : writeCell src (bSrc - amount) h₁ with
        | none => simp [hw₁] at htr
        | some pMid =>
          obtain ⟨⟨⟩, hMid₁⟩ := pMid
          rw [hw₁] at htr; dsimp only [bind, Option.bind] at htr
          obtain ⟨_, hmSrc, hrSrc_h⟩ := readCell_local src h₁ hf h h₁ bSrc hrSrc hmerge
          obtain ⟨_, hmDst, hrDst_h⟩ := readCell_local dst h₁ hf h h₁ bDst hrDst hmerge
          rw [hmerge] at hmSrc hmDst; cases hmSrc; cases hmDst
          obtain ⟨hMid, hmMid, hw₁_h⟩ := writeCell_local src (bSrc - amount) h₁ hf h hMid₁ () hw₁ hmerge
          obtain ⟨h', hm', hw₂_h⟩ := writeCell_local dst (bDst + amount) hMid₁ hf hMid h₁' () htr hmMid
          simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hcond
          exact ⟨h', hm', by simp [transferCells, hrSrc_h, hrDst_h, hcond.1, hcond.2, hw₁_h, hw₂_h]⟩
      · cases htr

/-- Verified 2-cell specification of `transferCells` on `src ↦ₕ b₁ ∗ dst ↦ₕ b₂`. -/
theorem transferCells_spec (src dst amount b₁ b₂ : Nat) (hle : amount ≤ b₁) :
    HoareSep ((src ↦ₕ b₁) ∗ (dst ↦ₕ b₂))
      (transferCells src dst amount)
      (fun _ => (src ↦ₕ (b₁ - amount)) ∗ (dst ↦ₕ (b₂ + amount))) := by
  intro h hpre
  have hne : src ≠ dst := ptsTo_sep_disjoint hpre
  rcases hpre with ⟨h₁, h₂, hm, rfl, rfl⟩
  obtain ⟨_, hspec_h⟩ := HeapExec.disjointMerge_spec_iff.1 hm
  have hne_beq : (src == dst) = false := beq_false_of_ne hne
  have hne_sym : (dst == src) = false := beq_false_of_ne hne.symm
  have hrSrc : readCell src h = some (b₁, h) := by simp [readCell, hspec_h, specMerge, HeapExec.singleton_toSpec]
  have hrDst : readCell dst h = some (b₂, h) := by simp [readCell, hspec_h, specMerge, HeapExec.singleton_toSpec, hne_sym]
  have mkDisj (v₁ v₂ : Nat) : specDisjoint (HeapExec.singleton src v₁).toSpec (HeapExec.singleton dst v₂).toSpec := fun q => by
    by_cases hq : q == src
    · rw [eq_of_beq hq]; exact Or.inr (by simp [HeapExec.singleton_toSpec, hne_beq])
    · exact Or.inl (by simp [HeapExec.singleton_toSpec, hq])
  rcases Option.isSome_iff_exists.1 (HeapExec.disjointMerge_isSome_iff.2 (mkDisj (b₁ - amount) b₂)) with ⟨hMid, hmMid⟩
  rcases Option.isSome_iff_exists.1 (HeapExec.disjointMerge_isSome_iff.2 (mkDisj (b₁ - amount) (b₂ + amount))) with ⟨h', hm'⟩
  obtain ⟨_, hspec_mid⟩ := HeapExec.disjointMerge_spec_iff.1 hmMid
  obtain ⟨_, hspec_h'⟩ := HeapExec.disjointMerge_spec_iff.1 hm'
  have hw₁ : writeCell src (b₁ - amount) h = some ((), hMid) :=
    writeCell_spec_iff.2 ⟨⟨b₁, by simp [hspec_h, specMerge, HeapExec.singleton_toSpec]⟩, fun q => by
      rw [hspec_mid, hspec_h]; by_cases hq : q == src <;> simp [specMerge, HeapExec.singleton_toSpec, hq]⟩
  have hw₂ : writeCell dst (b₂ + amount) hMid = some ((), h') :=
    writeCell_spec_iff.2 ⟨⟨b₂, by simp [hspec_mid, specMerge, HeapExec.singleton_toSpec, hne_sym]⟩, fun q => by
      rw [hspec_h', hspec_mid]
      by_cases hq : q == dst
      · have hqeq : q = dst := eq_of_beq hq; subst hqeq; simp [specMerge, HeapExec.singleton_toSpec, hne_sym]
      · simp [specMerge, HeapExec.singleton_toSpec, hq]⟩
  exact ⟨(), h', by simp [transferCells, hrSrc, hrDst, hne, hle, hw₁, hw₂], ⟨_, _, hm', rfl, rfl⟩⟩

/-- **2-Cell Transfer Lifted to an Arbitrary $N$-Cell World (`transferCells_framed`)**. -/
theorem transferCells_framed (src dst amount b₁ b₂ : Nat) (hle : amount ≤ b₁)
    (R : SepProp (HeapExec Nat)) :
    HoareSep (((src ↦ₕ b₁) ∗ (dst ↦ₕ b₂)) ∗ R)
      (transferCells src dst amount)
      (fun _ => ((src ↦ₕ (b₁ - amount)) ∗ (dst ↦ₕ (b₂ + amount))) ∗ R) :=
  hoare_sep_frame R (transferCells_local src dst amount) (transferCells_spec src dst amount b₁ b₂ hle)

/-! ## 4. Breadstuffs's Epistemic Authoritative Camera (`AuthCamera`) -/

/-! ### 4.1 Canonical `NullifierSet` (Strictly Sorted `List Nat`) -/

theorem sorted_nat_ext :
    ∀ {l₁ l₂ : List Nat},
      List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
      (∀ x : Nat, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | a :: _, [], _, _, h => by cases (h a).1 List.mem_cons_self
  | [], b :: _, _, _, h => by cases (h b).2 List.mem_cons_self
  | a :: t₁, b :: t₂, .cons ha hs₁, .cons hb hs₂, h => by
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with rfl | hm₂; · rfl
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with rfl | hm₁; · rfl
      exact False.elim (Nat.lt_irrefl a (Nat.lt_trans (ha b hm₁) (hb a hm₂)))
    subst hab
    have htail : ∀ x : Nat, x ∈ t₁ ↔ x ∈ t₂ := fun x =>
      ⟨fun hx₁ => by
         have hxa : x ≠ a := by have := ha x hx₁; omega
         rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem a hx₁)) with rfl | hx₂
         · exact False.elim (hxa rfl)
         · exact hx₂,
       fun hx₂ => by
         have hxa : x ≠ a := by have := hb x hx₂; omega
         rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem a hx₂)) with rfl | hx₁
         · exact False.elim (hxa rfl)
         · exact hx₁⟩
    rw [sorted_nat_ext hs₁ hs₂ htail]

@[expose] def insertSortedNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if y < x then y :: insertSortedNat x ys
    else y :: ys

theorem mem_insertSortedNat (x q : Nat) : ∀ (ys : List Nat),
    q ∈ insertSortedNat x ys ↔ q = x ∨ q ∈ ys
  | [] => by simp [insertSortedNat]
  | y :: ys => by
    simp only [insertSortedNat]
    by_cases hxy : x < y
    · simp [hxy]
    · by_cases hyx : y < x
      · simp [hxy, hyx, mem_insertSortedNat x q ys]; exact ⟨by rintro (rfl | rfl | h); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr h), by rintro (rfl | rfl | h); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr h)⟩
      · have heq : x = y := by omega
        subst heq; simp [hxy]

theorem pairwise_insertSortedNat (x : Nat) : ∀ {ys : List Nat},
    List.Pairwise (· < ·) ys → List.Pairwise (· < ·) (insertSortedNat x ys)
  | [], _ => .cons (fun _ h => by cases h) .nil
  | y :: ys, .cons hy hys => by
    simp only [insertSortedNat]
    by_cases hxy : x < y
    · simp only [hxy, ↓reduceIte]
      refine .cons (fun q hq => ?_) (.cons hy hys)
      rcases List.mem_cons.1 hq with rfl | hm; exact hxy; exact Nat.lt_trans hxy (hy q hm)
    · by_cases hyx : y < x
      · simp only [hxy, hyx, ↓reduceIte]
        refine .cons (fun q hq => ?_) (pairwise_insertSortedNat x hys)
        rcases (mem_insertSortedNat x q ys).1 hq with rfl | hm; exact hyx; exact hy q hm
      · simp [hxy, hyx, List.Pairwise.cons hy hys]

@[expose] def unionSortedNats (xs ys : List Nat) : List Nat :=
  xs.foldr insertSortedNat ys

theorem mem_unionSortedNats : ∀ (xs ys : List Nat) (q : Nat),
    q ∈ unionSortedNats xs ys ↔ q ∈ xs ∨ q ∈ ys
  | [], ys, q => by simp [unionSortedNats]
  | a :: xs, ys, q => by
    change q ∈ insertSortedNat a (unionSortedNats xs ys) ↔ _
    rw [mem_insertSortedNat, mem_unionSortedNats xs ys q, List.mem_cons, or_assoc]

theorem pairwise_unionSortedNats : ∀ {xs ys : List Nat},
    List.Pairwise (· < ·) xs → List.Pairwise (· < ·) ys →
    List.Pairwise (· < ·) (unionSortedNats xs ys)
  | [], _, _, hys => hys
  | _ :: _, _, .cons _ hsx, hys => pairwise_insertSortedNat _ (pairwise_unionSortedNats hsx hys)

/-- Canonical finite set of spent `Nat` nullifiers. -/
structure NullifierSet where
  items : List Nat
  sorted : List.Pairwise (· < ·) items

namespace NullifierSet

@[expose] def empty : NullifierSet := ⟨[], .nil⟩
@[expose] def singleton (nf : Nat) : NullifierSet := ⟨[nf], .cons (fun _ h => by cases h) .nil⟩
@[expose] def union (s₁ s₂ : NullifierSet) : NullifierSet :=
  ⟨unionSortedNats s₁.items s₂.items, pairwise_unionSortedNats s₁.sorted s₂.sorted⟩
@[expose] def insert (nf : Nat) (s : NullifierSet) : NullifierSet := union (singleton nf) s
@[expose] def erase (nf : Nat) (s : NullifierSet) : NullifierSet :=
  ⟨s.items.filter (· != nf), List.Pairwise.filter _ s.sorted⟩
@[expose] def subsetB (s₁ s₂ : NullifierSet) : Bool := s₁.items.all (fun x => s₂.items.contains x)

theorem ext {s₁ s₂ : NullifierSet} (h : ∀ x, x ∈ s₁.items ↔ x ∈ s₂.items) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact sorted_nat_ext ‹_› ‹_› h

theorem subsetB_iff {s₁ s₂ : NullifierSet} :
    s₁.subsetB s₂ = true ↔ ∀ x ∈ s₁.items, x ∈ s₂.items := by
  simp [subsetB, List.all_eq_true]

theorem union_comm (s₁ s₂ : NullifierSet) : union s₁ s₂ = union s₂ s₁ := by
  apply ext; intro x; simp [union, mem_unionSortedNats, Or.comm]

theorem union_assoc (s₁ s₂ s₃ : NullifierSet) :
    union (union s₁ s₂) s₃ = union s₁ (union s₂ s₃) := by
  apply ext; intro x; simp [union, mem_unionSortedNats, or_assoc]

@[simp] theorem empty_union (s : NullifierSet) : union empty s = s := by
  apply ext; intro x; simp [empty, union, mem_unionSortedNats]

@[simp] theorem union_empty (s : NullifierSet) : union s empty = s := by rw [union_comm, empty_union]

theorem mem_insert {nf x : Nat} {s : NullifierSet} :
    x ∈ (s.insert nf).items ↔ x = nf ∨ x ∈ s.items := by
  simp [insert, singleton, union, mem_unionSortedNats]

theorem not_mem_erase (nf : Nat) (s : NullifierSet) : nf ∉ (s.erase nf).items := by simp [erase]

end NullifierSet

/-! ### 4.2 Conserved Multi-Account Linear `Value` ($\sum \delta = 0$) -/

@[expose] def NonZeroSorted (xs : List (Nat × Int)) : Prop :=
  List.Pairwise (fun a b => a.1 < b.1) xs ∧ ∀ p ∈ xs, p.2 ≠ 0

@[expose] def deltaAt : List (Nat × Int) → Nat → Int
  | [], _ => 0
  | (k, d) :: rest, q => if q == k then d else deltaAt rest q

@[expose] def sumDeltas : List (Nat × Int) → Int
  | [] => 0
  | (_, d) :: rest => d + sumDeltas rest

theorem deltaAt_zero_of_forall_gt {l : List (Nat × Int)} {q : Nat}
    (hgt : ∀ p ∈ l, q < p.1) : deltaAt l q = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, d⟩ := hd
    have hlt : q < (k, d).1 := hgt (k, d) List.mem_cons_self
    dsimp only at hlt
    have hne : (q == k) = false := beq_false_of_ne (by omega)
    simp only [deltaAt, hne, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun p hp => hgt p (List.mem_cons_of_mem _ hp))

theorem nonZeroSorted_ext :
    ∀ {l₁ l₂ : List (Nat × Int)},
      NonZeroSorted l₁ → NonZeroSorted l₂ →
      (∀ q : Nat, deltaAt l₁ q = deltaAt l₂ q) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | (k, d) :: _, [], ⟨_, hnz⟩, _, heq => by
    have hk := heq k; simp only [deltaAt, beq_self_eq_true, ↓reduceIte] at hk
    exact False.elim (hnz (k, d) List.mem_cons_self hk)
  | [], (k, d) :: _, _, ⟨_, hnz⟩, heq => by
    have hk := heq k; simp only [deltaAt, beq_self_eq_true, ↓reduceIte] at hk
    exact False.elim (hnz (k, d) List.mem_cons_self hk.symm)
  | (k₁, d₁) :: t₁, (k₂, d₂) :: t₂, ⟨.cons hgt₁ hs₁, hnz₁⟩, ⟨.cons hgt₂ hs₂, hnz₂⟩, heq => by
    by_cases hlt₁ : k₁ < k₂
    · have hk₁ := heq k₁
      have hz : deltaAt ((k₂, d₂) :: t₂) k₁ = 0 :=
        deltaAt_zero_of_forall_gt fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp'; exact hlt₁; exact Nat.lt_trans hlt₁ (hgt₂ p hp')
      rw [hz] at hk₁; simp only [deltaAt, beq_self_eq_true, ↓reduceIte] at hk₁
      exact False.elim (hnz₁ (k₁, d₁) List.mem_cons_self hk₁)
    · by_cases hlt₂ : k₂ < k₁
      · have hk₂ := heq k₂
        have hz : deltaAt ((k₁, d₁) :: t₁) k₂ = 0 :=
          deltaAt_zero_of_forall_gt fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp'; exact hlt₂; exact Nat.lt_trans hlt₂ (hgt₁ p hp')
        rw [hz] at hk₂; simp only [deltaAt, beq_self_eq_true, ↓reduceIte] at hk₂
        exact False.elim (hnz₂ (k₂, d₂) List.mem_cons_self hk₂.symm)
      · have hkeq : k₁ = k₂ := by omega
        subst hkeq
        have hdeq : d₁ = d₂ := by simpa [deltaAt] using heq k₁
        subst hdeq
        have htail : ∀ q : Nat, deltaAt t₁ q = deltaAt t₂ q := fun q => by
          by_cases hq : q = k₁
          · subst hq; rw [deltaAt_zero_of_forall_gt hgt₁, deltaAt_zero_of_forall_gt hgt₂]
          · simpa [deltaAt, beq_false_of_ne hq] using heq q
        rw [nonZeroSorted_ext ⟨hs₁, fun p hp => hnz₁ p (List.mem_cons_of_mem _ hp)⟩
          ⟨hs₂, fun p hp => hnz₂ p (List.mem_cons_of_mem _ hp)⟩ htail]

/-- Insert/accumulate signed delta `d` at account `k` into a `NonZeroSorted` list. -/
@[expose] def addAccountDelta (k : Nat) (d : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => if d == 0 then [] else [(k, d)]
  | (k', d') :: xs =>
    if k < k' then if d == 0 then (k', d') :: xs else (k, d) :: (k', d') :: xs
    else if k' < k then (k', d') :: addAccountDelta k d xs
    else if d + d' == 0 then xs else (k', d + d') :: xs

theorem addAccountDelta_keys {k : Nat} {d : Int} :
    ∀ {xs : List (Nat × Int)} {p : Nat × Int},
      p ∈ addAccountDelta k d xs → p.1 = k ∨ ∃ d₀, (p.1, d₀) ∈ xs
  | [], p, hp => by
    simp only [addAccountDelta] at hp; split at hp; · cases hp
    simp only [List.mem_singleton] at hp; subst hp; exact Or.inl rfl
  | (k', d') :: xs, p, hp => by
    simp only [addAccountDelta] at hp
    split at hp
    · split at hp
      · exact Or.inr ⟨p.2, hp⟩
      · rcases List.mem_cons.1 hp with rfl | hm; exact Or.inl rfl; exact Or.inr ⟨p.2, hm⟩
    · split at hp
      · rcases List.mem_cons.1 hp with rfl | hm
        · exact Or.inr ⟨d', List.mem_cons_self⟩
        · exact (addAccountDelta_keys hm).imp id fun ⟨d₀, h₀⟩ => ⟨d₀, List.mem_cons_of_mem _ h₀⟩
      · split at hp
        · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hp⟩
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact Or.inr ⟨d', List.mem_cons_self⟩
          · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hm⟩

theorem addAccountDelta_nonZeroSorted (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs → NonZeroSorted (addAccountDelta k d xs)
  | [], _ => by
    simp only [addAccountDelta]
    by_cases hd : d == 0
    · simp [hd, NonZeroSorted]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, NonZeroSorted]
      refine ⟨.cons (fun _ h => by cases h) .nil, fun p hp => ?_⟩
      simp only [List.mem_singleton] at hp; subst hp
      exact fun hz => absurd (beq_iff_eq.2 hz) hd
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩ => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [addAccountDelta]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d == 0
      · simp [hd]; exact ⟨.cons hgt hs, hnz⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        refine ⟨.cons (fun p hp => ?_) (.cons hgt hs), fun p hp => ?_⟩
        · rcases List.mem_cons.1 hp with rfl | hm; exact hlt; exact Nat.lt_trans hlt (hgt p hm)
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (beq_iff_eq.2 hz) hd
          · exact hnz p hm
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte]
        obtain ⟨hs_rec, hnz_rec⟩ := addAccountDelta_nonZeroSorted k d htail
        refine ⟨.cons (fun p hp => ?_) hs_rec, fun p hp => ?_⟩
        · rcases addAccountDelta_keys hp with hpk | ⟨d₀, h₀⟩
          · rw [hpk]; exact hgt'
          · exact hgt (p.1, d₀) h₀
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact hnz (k', d') List.mem_cons_self
          · exact hnz_rec p hm
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' == 0
        · simp [hsum]; exact htail
        · simp only [hsum, Bool.false_eq_true, ↓reduceIte]
          refine ⟨.cons hgt hs, fun p hp => ?_⟩
          rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (beq_iff_eq.2 hz) hsum
          · exact htail.2 p hm

theorem deltaAt_addAccountDelta (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs →
      ∀ q : Nat, deltaAt (addAccountDelta k d xs) q = (if q == k then d else 0) + deltaAt xs q
  | [], _, q => by
    simp only [addAccountDelta]
    by_cases hd : d == 0
    · rw [eq_of_beq hd]; simp [deltaAt]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, deltaAt]; by_cases hqk : q == k <;> simp [hqk]
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩, q => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [addAccountDelta]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d == 0
      · simp only [hd, ↓reduceIte]; rw [eq_of_beq hd]; simp
      · simp only [hd, Bool.false_eq_true, ↓reduceIte, deltaAt]
        by_cases hqk : q == k
        · have hqeq : q = k := eq_of_beq hqk
          have hqk' : (q == k') = false := beq_false_of_ne (by omega)
          have hz : deltaAt xs q = 0 := deltaAt_zero_of_forall_gt fun p hp => by
            have := hgt p hp; omega
          simp [hqk, hqk', hz]
        · simp [hqk]
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, deltaAt]
        by_cases hqk' : q == k'
        · have hqk_f : (q == k) = false := beq_false_of_ne (by have := eq_of_beq hqk'; omega)
          simp [hqk', hqk_f]
        · simp [hqk', deltaAt_addAccountDelta k d htail q]
      · have hkeq : k = k' := by omega
        subst hkeq; simp only [hlt, ↓reduceIte]
        by_cases hsum : d + d' == 0
        · simp only [hsum, ↓reduceIte]
          have hz : d + d' = 0 := eq_of_beq hsum
          by_cases hqk : q == k
          · have hqeq : q = k := eq_of_beq hqk; subst hqeq
            simp [deltaAt, deltaAt_zero_of_forall_gt hgt]; omega
          · simp [deltaAt, hqk]
        · simp only [hsum, Bool.false_eq_true, ↓reduceIte, deltaAt]
          by_cases hqk : q == k <;> simp [hqk]

theorem sumDeltas_addAccountDelta (k : Nat) (d : Int) :
    ∀ (xs : List (Nat × Int)), sumDeltas (addAccountDelta k d xs) = d + sumDeltas xs
  | [] => by
    simp only [addAccountDelta]
    by_cases hd : d == 0
    · simp [eq_of_beq hd, sumDeltas]
    · simp [hd, sumDeltas]
  | (k', d') :: xs => by
    simp only [addAccountDelta]
    by_cases hlt : k < k'
    · by_cases hd : d == 0 <;> simp [hlt, hd, sumDeltas]; have := eq_of_beq hd; omega
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, sumDeltas, sumDeltas_addAccountDelta k d xs]; omega
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' == 0
        · have := eq_of_beq hsum; simp only [hsum, ↓reduceIte, sumDeltas]; omega
        · simp only [hsum, Bool.false_eq_true, ↓reduceIte, sumDeltas]; omega

/-- Canonical sparse addition of two `NonZeroSorted` account-delta lists. -/
@[expose] def addDeltaLists (xs ys : List (Nat × Int)) : List (Nat × Int) :=
  xs.foldr (fun p acc => addAccountDelta p.1 p.2 acc) ys

theorem addDeltaLists_nonZeroSorted :
    ∀ {xs ys : List (Nat × Int)},
      NonZeroSorted xs → NonZeroSorted ys → NonZeroSorted (addDeltaLists xs ys)
  | [], _, _, hys => hys
  | (k, d) :: _xs, _, ⟨.cons _ hsx, hnzx⟩, hys =>
    addAccountDelta_nonZeroSorted k d
      (addDeltaLists_nonZeroSorted ⟨hsx, fun p hp => hnzx p (List.mem_cons_of_mem _ hp)⟩ hys)

theorem deltaAt_addDeltaLists :
    ∀ {xs ys : List (Nat × Int)},
      NonZeroSorted xs → NonZeroSorted ys →
      ∀ q : Nat, deltaAt (addDeltaLists xs ys) q = deltaAt xs q + deltaAt ys q
  | [], _, _, _, q => by simp [addDeltaLists, deltaAt]
  | (k, d) :: xs, ys, ⟨.cons hgx hsx, hnzx⟩, hys, q => by
    have htx : NonZeroSorted xs := ⟨hsx, fun p hp => hnzx p (List.mem_cons_of_mem _ hp)⟩
    have ih := deltaAt_addDeltaLists htx hys q
    dsimp only [addDeltaLists, List.foldr_cons]
    change deltaAt (addAccountDelta k d (addDeltaLists xs ys)) q = _
    rw [deltaAt_addAccountDelta k d (addDeltaLists_nonZeroSorted htx hys) q, ih]
    by_cases hqk : q == k
    · have hqeq : q = k := eq_of_beq hqk; subst hqeq
      simp [deltaAt, deltaAt_zero_of_forall_gt hgx]
    · simp [deltaAt, hqk]

theorem sumDeltas_addDeltaLists :
    ∀ (xs ys : List (Nat × Int)), sumDeltas (addDeltaLists xs ys) = sumDeltas xs + sumDeltas ys
  | [], _ => by simp [addDeltaLists, sumDeltas]
  | (k, d) :: xs, ys => by
    have ih := sumDeltas_addDeltaLists xs ys
    dsimp only [addDeltaLists, List.foldr_cons]
    change sumDeltas (addAccountDelta k d (addDeltaLists xs ys)) = d + sumDeltas xs + sumDeltas ys
    rw [sumDeltas_addAccountDelta, ih]
    omega

/-- Conserved linear `Value` vector ($\sum \delta = 0$) over accounts. -/
structure ConservedValue where
  entries : List (Nat × Int)
  wf : NonZeroSorted entries
  conserved : sumDeltas entries = 0

namespace ConservedValue

@[expose] def zero : ConservedValue := ⟨[], ⟨.nil, fun _ h => by cases h⟩, rfl⟩

@[expose] def add (v₁ v₂ : ConservedValue) : ConservedValue where
  entries := addDeltaLists v₁.entries v₂.entries
  wf := addDeltaLists_nonZeroSorted v₁.wf v₂.wf
  conserved := by rw [sumDeltas_addDeltaLists, v₁.conserved, v₂.conserved]; rfl

/-- Construct a conserved 2-account transfer `(-amount)` from `src` and `(+amount)` to `dst`
    satisfying $\sum \delta = (-amount) + amount = 0$! -/
@[expose] def transfer (src dst : Nat) (amount : Int) : ConservedValue where
  entries := addAccountDelta src (-amount) (addAccountDelta dst amount [])
  wf := addAccountDelta_nonZeroSorted src (-amount)
    (addAccountDelta_nonZeroSorted dst amount ⟨.nil, fun _ h => by cases h⟩)
  conserved := by simp [sumDeltas_addAccountDelta, sumDeltas]; omega

theorem transfer_deltaAt (src dst : Nat) (amount : Int) (q : Nat) :
    deltaAt (transfer src dst amount).entries q =
      (if q == src then -amount else 0) + (if q == dst then amount else 0) := by
  have hwf1 := addAccountDelta_nonZeroSorted dst amount ⟨.nil, fun _ h => by cases h⟩
  simp only [transfer, deltaAt_addAccountDelta src (-amount) hwf1 q,
    deltaAt_addAccountDelta dst amount ⟨.nil, fun _ h => by cases h⟩ q, deltaAt, Int.add_zero]

theorem ext {v₁ v₂ : ConservedValue} (h : ∀ q, deltaAt v₁.entries q = deltaAt v₂.entries q) :
    v₁ = v₂ := by
  cases v₁; cases v₂; simp only [mk.injEq]; exact nonZeroSorted_ext ‹_› ‹_› h

theorem add_comm (v₁ v₂ : ConservedValue) : add v₁ v₂ = add v₂ v₁ :=
  ext fun q => by
    change deltaAt (addDeltaLists v₁.entries v₂.entries) q =
      deltaAt (addDeltaLists v₂.entries v₁.entries) q
    rw [deltaAt_addDeltaLists v₁.wf v₂.wf, deltaAt_addDeltaLists v₂.wf v₁.wf]
    omega

theorem add_assoc (v₁ v₂ v₃ : ConservedValue) :
    add (add v₁ v₂) v₃ = add v₁ (add v₂ v₃) :=
  ext fun q => by
    have h12 := (add v₁ v₂).wf
    have h23 := (add v₂ v₃).wf
    change deltaAt (addDeltaLists (add v₁ v₂).entries v₃.entries) q =
      deltaAt (addDeltaLists v₁.entries (add v₂ v₃).entries) q
    rw [deltaAt_addDeltaLists h12 v₃.wf, deltaAt_addDeltaLists v₁.wf h23]
    change deltaAt (addDeltaLists v₁.entries v₂.entries) q + deltaAt v₃.entries q =
      deltaAt v₁.entries q + deltaAt (addDeltaLists v₂.entries v₃.entries) q
    rw [deltaAt_addDeltaLists v₁.wf v₂.wf, deltaAt_addDeltaLists v₂.wf v₃.wf]
    omega

@[simp] theorem zero_add (v : ConservedValue) : add zero v = v := ext fun _ => rfl

@[simp] theorem add_zero (v : ConservedValue) : add v zero = v := by rw [add_comm, zero_add]

end ConservedValue

/-! ### 4.3 Authoritative Epistemic Camera (`AuthCamera`) & FPU / Refutation Theorems -/

structure AuthWorld where
  authority : Nat
  nullifiers : NullifierSet

/-- **Breadstuffs's Epistemic Authoritative Camera (`AuthCamera`)**. -/
structure AuthCamera where
  auth? : Option AuthWorld
  fragAuthority : Nat
  fragNullifiers : NullifierSet
  value : ConservedValue
  coherent : ∀ w : AuthWorld, auth? = some w →
    fragAuthority ≤ w.authority ∧ fragNullifiers.subsetB w.nullifiers = true

namespace AuthCamera

theorem ext {a b : AuthCamera}
    (hAuth : a.auth? = b.auth?) (hFA : a.fragAuthority = b.fragAuthority)
    (hFN : a.fragNullifiers = b.fragNullifiers) (hVal : a.value = b.value) : a = b := by
  cases a; cases b; simp only [mk.injEq] at *; exact ⟨hAuth, hFA, hFN, hVal⟩

@[expose] def empty : AuthCamera := ⟨none, 0, .empty, .zero, fun _ h => by cases h⟩

@[expose] def mkAuth (authority : Nat) (nullifiers : NullifierSet)
    (val : ConservedValue := .zero) : AuthCamera where
  auth? := some ⟨authority, nullifiers⟩
  fragAuthority := authority
  fragNullifiers := nullifiers
  value := val
  coherent w hw := by cases hw; exact ⟨Nat.le_refl _, NullifierSet.subsetB_iff.2 (fun _ hx => hx)⟩

@[expose] def mkFrag (fragAuthority : Nat) (fragNullifiers : NullifierSet)
    (val : ConservedValue := .zero) : AuthCamera :=
  ⟨none, fragAuthority, fragNullifiers, val, fun _ h => by cases h⟩

private theorem union_subsetB {s₁ s₂ w : NullifierSet}
    (h₁ : s₁.subsetB w = true) (h₂ : s₂.subsetB w = true) :
    (s₁.union s₂).subsetB w = true :=
  NullifierSet.subsetB_iff.2 fun x hx => by
    rcases (mem_unionSortedNats s₁.items s₂.items x).1 hx with hx₁ | hx₂
    · exact NullifierSet.subsetB_iff.1 h₁ x hx₁
    · exact NullifierSet.subsetB_iff.1 h₂ x hx₂

private theorem subsetB_of_union_left {s₁ s₂ w : NullifierSet}
    (h : (s₁.union s₂).subsetB w = true) : s₁.subsetB w = true :=
  NullifierSet.subsetB_iff.2 fun x hx =>
    NullifierSet.subsetB_iff.1 h x ((mem_unionSortedNats s₁.items s₂.items x).2 (Or.inl hx))

private theorem subsetB_of_union_right {s₁ s₂ w : NullifierSet}
    (h : (s₁.union s₂).subsetB w = true) : s₂.subsetB w = true :=
  NullifierSet.subsetB_iff.2 fun x hx =>
    NullifierSet.subsetB_iff.1 h x ((mem_unionSortedNats s₁.items s₂.items x).2 (Or.inr hx))

@[expose] def composeWithWorld? (w : AuthWorld) (fa : Nat) (fn : NullifierSet)
    (val : ConservedValue) : Option AuthCamera :=
  if h : decide (fa ≤ w.authority) && fn.subsetB w.nullifiers then
    some ⟨some w, fa, fn, val, fun _ hw => by
      cases hw; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1, h.2⟩⟩
  else none

@[expose] def compose? (a b : AuthCamera) : Option AuthCamera :=
  let fa := max a.fragAuthority b.fragAuthority
  let fn := a.fragNullifiers.union b.fragNullifiers
  let val := a.value.add b.value
  match a.auth?, b.auth? with
  | none, none => some ⟨none, fa, fn, val, fun _ h => by cases h⟩
  | some w, none => composeWithWorld? w fa fn val
  | none, some w => composeWithWorld? w fa fn val
  | some _, some _ => none

private theorem composeWithWorld?_eq_some_iff {w : AuthWorld} {fa : Nat}
    {fn : NullifierSet} {val : ConservedValue} {c : AuthCamera} :
    composeWithWorld? w fa fn val = some c ↔
      fa ≤ w.authority ∧ fn.subsetB w.nullifiers = true ∧
      c.auth? = some w ∧ c.fragAuthority = fa ∧ c.fragNullifiers = fn ∧ c.value = val := by
  unfold composeWithWorld?
  split <;> rename_i h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fun hs => by cases hs; exact ⟨h.1, h.2, rfl, rfl, rfl, rfl⟩,
           fun ⟨_, _, hc1, hc2, hc3, hc4⟩ => congrArg some (ext hc1.symm hc2.symm hc3.symm hc4.symm)⟩
  · exact ⟨fun hs => (by cases hs), fun ⟨h1, h2, _⟩ => absurd (by simp [h1, h2]) h⟩

theorem compose?_eq_some_iff {a b c : AuthCamera} :
    compose? a b = some c ↔
      c.fragAuthority = max a.fragAuthority b.fragAuthority ∧
      c.fragNullifiers = a.fragNullifiers.union b.fragNullifiers ∧
      c.value = a.value.add b.value ∧
      ((a.auth? = none ∧ b.auth? = none ∧ c.auth? = none) ∨
       (∃ w, a.auth? = some w ∧ b.auth? = none ∧ c.auth? = some w ∧
          b.fragAuthority ≤ w.authority ∧ b.fragNullifiers.subsetB w.nullifiers = true) ∨
       (∃ w, a.auth? = none ∧ b.auth? = some w ∧ c.auth? = some w ∧
          a.fragAuthority ≤ w.authority ∧ a.fragNullifiers.subsetB w.nullifiers = true)) := by
  cases hA : a.auth? <;> cases hB : b.auth?
  · simp only [compose?, hA, hB, Option.some.injEq, reduceCtorEq, false_and, exists_false, true_and, or_false]
    exact ⟨fun h => by subst h; exact ⟨rfl, rfl, rfl, rfl⟩,
           fun ⟨h1, h2, h3, h4⟩ => ext h4.symm h1.symm h2.symm h3.symm⟩
  · rename_i w
    obtain ⟨hb₁, hb₂⟩ := b.coherent w hB
    have hL : compose? a b = composeWithWorld? w (max a.fragAuthority b.fragAuthority)
        (a.fragNullifiers.union b.fragNullifiers) (a.value.add b.value) := by simp [compose?, hA, hB]
    rw [hL, composeWithWorld?_eq_some_iff]
    constructor
    · rintro ⟨hfa, hfn, hcA, hcFA, hcFN, hcV⟩
      exact ⟨hcFA, hcFN, hcV, Or.inr (Or.inr ⟨w, rfl, rfl, hcA, by omega, subsetB_of_union_left hfn⟩)⟩
    · rintro ⟨hcFA, hcFN, hcV, ⟨_, hbad, _⟩ | ⟨_, hbad, _⟩ | ⟨w', _, hw', hcA, ha₁, ha₂⟩⟩
      · cases hbad
      · cases hbad
      · cases hw'; exact ⟨by omega, union_subsetB ha₂ hb₂, hcA, hcFA, hcFN, hcV⟩
  · rename_i w
    obtain ⟨ha₁, ha₂⟩ := a.coherent w hA
    have hL : compose? a b = composeWithWorld? w (max a.fragAuthority b.fragAuthority)
        (a.fragNullifiers.union b.fragNullifiers) (a.value.add b.value) := by simp [compose?, hA, hB]
    rw [hL, composeWithWorld?_eq_some_iff]
    constructor
    · rintro ⟨hfa, hfn, hcA, hcFA, hcFN, hcV⟩
      exact ⟨hcFA, hcFN, hcV, Or.inr (Or.inl ⟨w, rfl, rfl, hcA, by omega, subsetB_of_union_right hfn⟩)⟩
    · rintro ⟨hcFA, hcFN, hcV, ⟨hbad, _⟩ | ⟨w', hw', _, hcA, hb₁, hb₂⟩ | ⟨_, hbad, _⟩⟩
      · cases hbad
      · cases hw'; exact ⟨by omega, union_subsetB ha₂ hb₂, hcA, hcFA, hcFN, hcV⟩
      · cases hbad
  · have hL : compose? a b = none := by simp [compose?, hA, hB]
    rw [hL]
    constructor
    · intro h; cases h
    · rintro ⟨_, _, _, ⟨hbad, _⟩ | ⟨_, _, hbad, _⟩ | ⟨_, hbad, _⟩⟩ <;> cases hbad

theorem compose?_symm {a b c : AuthCamera} (hab : compose? a b = some c) : compose? b a = some c := by
  obtain ⟨hFA, hFN, hVal, hCases⟩ := compose?_eq_some_iff.1 hab
  apply compose?_eq_some_iff.2
  refine ⟨by omega, by rw [hFN, NullifierSet.union_comm], by rw [hVal, ConservedValue.add_comm], ?_⟩
  rcases hCases with ⟨hA, hB, hC⟩ | ⟨w, hA, hB, hC, h1, h2⟩ | ⟨w, hA, hB, hC, h1, h2⟩
  · exact Or.inl ⟨hB, hA, hC⟩
  · exact Or.inr (Or.inr ⟨w, hB, hA, hC, h1, h2⟩)
  · exact Or.inr (Or.inl ⟨w, hB, hA, hC, h1, h2⟩)

theorem compose?_comm (a b : AuthCamera) : compose? a b = compose? b a := by
  cases hab : compose? a b with
  | none =>
    cases hba : compose? b a with
    | none => rfl
    | some c => rw [compose?_symm hba] at hab; cases hab
  | some c => exact (compose?_symm hab).symm

instance instLawfulPCMAuthCamera : LawfulPCM AuthCamera where
  op? := compose?
  one := empty
  one_op a := by
    apply compose?_eq_some_iff.2
    refine ⟨by change a.fragAuthority = max 0 a.fragAuthority; omega,
      (NullifierSet.empty_union _).symm, (ConservedValue.zero_add _).symm, ?_⟩
    cases hA : a.auth? with
    | none => exact Or.inl ⟨rfl, rfl, rfl⟩
    | some w => exact Or.inr (Or.inr ⟨w, rfl, rfl, rfl, Nat.zero_le _,
        NullifierSet.subsetB_iff.2 (fun _ h => by cases h)⟩)
  op_comm := compose?_comm
  op_assoc := option_op_assoc_of_comm_forward compose? compose?_comm fun {x y z xy xyz} hxy hxyz => by
    obtain ⟨hFA₁, hFN₁, hVal₁, hC₁⟩ := compose?_eq_some_iff.1 hxy
    obtain ⟨hFA₂, hFN₂, hVal₂, hC₂⟩ := compose?_eq_some_iff.1 hxyz
    have hFA_assoc : xyz.fragAuthority = max x.fragAuthority (max y.fragAuthority z.fragAuthority) := by
      omega
    have hFN_assoc : xyz.fragNullifiers = x.fragNullifiers.union (y.fragNullifiers.union z.fragNullifiers) := by
      rw [hFN₂, hFN₁, NullifierSet.union_assoc]
    have hV_assoc : xyz.value = x.value.add (y.value.add z.value) := by
      rw [hVal₂, hVal₁, ConservedValue.add_assoc]
    rcases hC₁ with ⟨hxN, hyN, hxyN⟩ | ⟨w, hxS, hyN, hxyS, hyA, hySub⟩ | ⟨w, hxN, hyS, hxyS, hxA, hxSub⟩
    · rcases hC₂ with ⟨_, hzN, hxyzN⟩ | ⟨_, hbad, _, _, _, _⟩ | ⟨w, _, hzS, hxyzS, hxyA, hxySub⟩
      · refine ⟨⟨none, max y.fragAuthority z.fragAuthority, _, _, fun _ h => by cases h⟩,
          compose?_eq_some_iff.2 ⟨rfl, rfl, rfl, Or.inl ⟨hyN, hzN, rfl⟩⟩,
          compose?_eq_some_iff.2 ⟨hFA_assoc, hFN_assoc, hV_assoc, Or.inl ⟨hxN, rfl, hxyzN⟩⟩⟩
      · rw [hxyN] at hbad; cases hbad
      · rw [hFA₁] at hxyA; rw [hFN₁] at hxySub
        have hyA : y.fragAuthority ≤ w.authority := by omega
        have hxA : x.fragAuthority ≤ w.authority := by omega
        have hySub := subsetB_of_union_right hxySub
        have hxSub := subsetB_of_union_left hxySub
        obtain ⟨hzA, hzSub⟩ := z.coherent w hzS
        refine ⟨⟨some w, max y.fragAuthority z.fragAuthority, _, _, fun _ hw' => by cases hw'; exact ⟨by omega, union_subsetB hySub hzSub⟩⟩,
          compose?_eq_some_iff.2 ⟨rfl, rfl, rfl, Or.inr (Or.inr ⟨w, hyN, hzS, rfl, hyA, hySub⟩)⟩,
          compose?_eq_some_iff.2 ⟨hFA_assoc, hFN_assoc, hV_assoc, Or.inr (Or.inr ⟨w, hxN, rfl, hxyzS, hxA, hxSub⟩)⟩⟩
    · rcases hC₂ with ⟨hbad, _, _⟩ | ⟨_, hxyS', hzN, hxyzS, hzA, hzSub⟩ | ⟨_, hbad, _, _, _, _⟩
      · rw [hxyS] at hbad; cases hbad
      · rw [hxyS] at hxyS'; cases hxyS'
        refine ⟨⟨none, max y.fragAuthority z.fragAuthority, _, _, fun _ h => by cases h⟩,
          compose?_eq_some_iff.2 ⟨rfl, rfl, rfl, Or.inl ⟨hyN, hzN, rfl⟩⟩,
          compose?_eq_some_iff.2 ⟨hFA_assoc, hFN_assoc, hV_assoc,
            Or.inr (Or.inl ⟨w, hxS, rfl, hxyzS, by dsimp only; omega, union_subsetB hySub hzSub⟩)⟩⟩
      · rw [hxyS] at hbad; cases hbad
    · rcases hC₂ with ⟨hbad, _, _⟩ | ⟨_, hxyS', hzN, hxyzS, hzA, hzSub⟩ | ⟨_, hbad, _, _, _, _⟩
      · rw [hxyS] at hbad; cases hbad
      · rw [hxyS] at hxyS'; cases hxyS'
        obtain ⟨hyA, hySub⟩ := y.coherent w hyS
        refine ⟨⟨some w, max y.fragAuthority z.fragAuthority, _, _, fun _ hw' => by cases hw'; exact ⟨by omega, union_subsetB hySub hzSub⟩⟩,
          compose?_eq_some_iff.2 ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨w, hyS, hzN, rfl, hzA, hzSub⟩)⟩,
          compose?_eq_some_iff.2 ⟨hFA_assoc, hFN_assoc, hV_assoc, Or.inr (Or.inr ⟨w, hxN, rfl, hxyzS, hxA, hxSub⟩)⟩⟩
      · rw [hxyS] at hbad; cases hbad

theorem grow_authority_fpu {k k' : Nat} (hle : k ≤ k')
    (nfs : NullifierSet) (val val' : ConservedValue) :
    FPUDet (mkAuth k nfs val) (mkAuth k' nfs val') := by
  apply fpuDet_iff.2; intro frame hcompat
  rcases Option.isSome_iff_exists.1 hcompat with ⟨_, hm⟩
  obtain ⟨_, _, _, hCases⟩ := compose?_eq_some_iff.1 hm
  rcases hCases with ⟨hbad, _, _⟩ | ⟨w, hA, hfN, _, hfA, hfSub⟩ | ⟨_, hbad, _, _, _, _⟩
  · cases hbad
  · simp only [mkAuth, Option.some.injEq] at hA; subst hA
    have hfA' : frame.fragAuthority ≤ k' := Nat.le_trans hfA hle
    let target : AuthCamera :=
      ⟨some ⟨k', nfs⟩, max k' frame.fragAuthority, nfs.union frame.fragNullifiers,
       val'.add frame.value, fun _ hw => by
         cases hw; exact ⟨by dsimp only; omega,
           union_subsetB (NullifierSet.subsetB_iff.2 fun _ hx => hx) hfSub⟩⟩
    exact Option.isSome_iff_exists.2 ⟨target,
      compose?_eq_some_iff.2 ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨⟨k', nfs⟩, rfl, hfN, rfl, hfA', hfSub⟩)⟩⟩
  · cases hbad

theorem spend_nullifier_fpu (k : Nat) (nfs : NullifierSet) (nf : Nat)
    (val tx : ConservedValue) :
    FPU (mkAuth k nfs val)
      (fun b => ∃ authNext : AuthCamera,
        authNext = mkAuth k (nfs.insert nf) val ∧
        LawfulPCM.op? authNext (mkFrag k (.singleton nf) tx) = some b) := by
  intro frame hcompat
  rcases Option.isSome_iff_exists.1 hcompat with ⟨_, hm⟩
  obtain ⟨_, _, _, hCases⟩ := compose?_eq_some_iff.1 hm
  rcases hCases with ⟨hbad, _, _⟩ | ⟨w, hA, hfN, _, hfA, hfSub⟩ | ⟨_, hbad, _, _, _, _⟩
  · cases hbad
  · simp only [mkAuth, Option.some.injEq] at hA; subst hA
    have hFragSub : (NullifierSet.singleton nf).subsetB (nfs.insert nf) = true :=
      NullifierSet.subsetB_iff.2 fun x hx => by
        simp only [NullifierSet.singleton, List.mem_singleton] at hx; subst hx
        exact NullifierSet.mem_insert.2 (Or.inl rfl)
    have hSelfSub : (nfs.insert nf).subsetB (nfs.insert nf) = true :=
      NullifierSet.subsetB_iff.2 fun _ hx => hx
    have hfAk : frame.fragAuthority ≤ k := hfA
    let b : AuthCamera :=
      ⟨some ⟨k, nfs.insert nf⟩, k, (nfs.insert nf).union (.singleton nf),
       val.add tx, fun _ hw => by cases hw; exact ⟨Nat.le_refl k, union_subsetB hSelfSub hFragSub⟩⟩
    have hbMint : compose? (mkAuth k (nfs.insert nf) val) (mkFrag k (.singleton nf) tx) = some b :=
      compose?_eq_some_iff.2 ⟨(Nat.max_self k).symm, rfl, rfl,
        Or.inr (Or.inl ⟨⟨k, nfs.insert nf⟩, rfl, rfl, rfl, Nat.le_refl k, hFragSub⟩)⟩
    have hfSub' : frame.fragNullifiers.subsetB (nfs.insert nf) = true :=
      NullifierSet.subsetB_iff.2 fun x hx =>
        NullifierSet.mem_insert.2 (Or.inr (NullifierSet.subsetB_iff.1 hfSub x hx))
    let bFramed : AuthCamera :=
      ⟨some ⟨k, nfs.insert nf⟩, max k frame.fragAuthority,
       b.fragNullifiers.union frame.fragNullifiers, b.value.add frame.value,
       fun _ hw => by
         cases hw; exact ⟨Nat.max_le.2 ⟨Nat.le_refl k, hfAk⟩,
           union_subsetB (union_subsetB hSelfSub hFragSub) hfSub'⟩⟩
    have hFrameOk : compose? b frame = some bFramed :=
      compose?_eq_some_iff.2 ⟨rfl, rfl, rfl,
        Or.inr (Or.inl ⟨⟨k, nfs.insert nf⟩, rfl, hfN, rfl, hfAk, hfSub'⟩)⟩
    exact ⟨b, ⟨mkAuth k (nfs.insert nf) val, rfl, hbMint⟩, Option.isSome_iff_exists.2 ⟨bFramed, hFrameOk⟩⟩
  · cases hbad

theorem uncoordinated_forget_nullifier_not_fpu (k : Nat) (nfs : NullifierSet) (nf : Nat)
    (val val' : ConservedValue) :
    ¬ FPUDet (mkAuth k (nfs.insert nf) val) (mkAuth k (nfs.erase nf) val') := by
  intro hfpu
  let observerReceipt : AuthCamera := mkFrag 0 (.singleton nf) .zero
  have hSubBefore : (NullifierSet.singleton nf).subsetB (nfs.insert nf) = true :=
    NullifierSet.subsetB_iff.2 fun x hx => by
      simp only [NullifierSet.singleton, List.mem_singleton] at hx; subst hx
      exact NullifierSet.mem_insert.2 (Or.inl rfl)
  have hSelfSub : (nfs.insert nf).subsetB (nfs.insert nf) = true :=
    NullifierSet.subsetB_iff.2 fun _ hx => hx
  let beforeAll : AuthCamera :=
    ⟨some ⟨k, nfs.insert nf⟩, max k 0, (nfs.insert nf).union (.singleton nf),
     val.add .zero, fun _ hw => by cases hw; exact ⟨by dsimp only; omega, union_subsetB hSelfSub hSubBefore⟩⟩
  have hBeforeOk : compose? (mkAuth k (nfs.insert nf) val) observerReceipt = some beforeAll :=
    compose?_eq_some_iff.2 ⟨rfl, rfl, rfl,
      Or.inr (Or.inl ⟨⟨k, nfs.insert nf⟩, rfl, rfl, rfl, Nat.zero_le k, hSubBefore⟩)⟩
  have hCompatBefore : (LawfulPCM.op? (mkAuth k (nfs.insert nf) val) observerReceipt).isSome = true :=
    Option.isSome_iff_exists.2 ⟨beforeAll, hBeforeOk⟩
  rcases Option.isSome_iff_exists.1 ((fpuDet_iff.1 hfpu) observerReceipt hCompatBefore) with ⟨_, hbad⟩
  obtain ⟨_, _, _, hCases⟩ := compose?_eq_some_iff.1 hbad
  rcases hCases with ⟨h1, _, _⟩ | ⟨_, hA, _, _, _, hSubAfter⟩ | ⟨_, h1, _, _, _, _⟩
  · cases h1
  · simp only [mkAuth, Option.some.injEq] at hA; subst hA
    have hMemSingle : nf ∈ (NullifierSet.singleton nf).items := List.mem_cons_self
    exact NullifierSet.not_mem_erase nf nfs
      (NullifierSet.subsetB_iff.1 hSubAfter nf hMemSingle)
  · cases h1

end AuthCamera

end Obend.Logic
end
