module
/-
# Obend.Paco.GPaco — Parameterized and Generalized Parameterized Coinduction

Quarried and upgraded from `breadstuffs` (`Dregg2/Paco/{Basic,GPaco,Companion,UpTo/*}`),
self-contained in pure Lean 4 (`Init` only, zero Mathlib dependencies, zero custom axioms).

## Summary of Constructions & Theorems

1. **Relational Lattice & Greatest Fixed Points (`Rel`, `MonoRel`, `MonoRel.gfp`)**:
   - Binary relations `Rel α := α → α → Prop` with subset order `≤`, union `⊔`, intersection `⊓`,
     `⊥`, `⊤`, and Knaster–Tarski `MonoRel.gfp`.
2. **Parameterized Coinduction (`paco`, `upaco` — Hur, Neis, Dreyer, Vafeiadis, POPL 2013)**:
   - `paco F r x y := ∃ R, (∀ a b, R a b → F (R ⊔ r) a b) ∧ R x y`
   - Monotonicity (`paco_mon`), fixed-point unfolding/folding (`paco_unfold`, `paco_fold`,
     `paco_fixed`), initialization (`paco_init`), accumulation (`paco_acc`, `paco_acc_upaco`),
     and soundness into `F.gfp` (`paco_final`).
3. **Generalized Parameterized Coinduction (`gpaco`, `gupaco` — Zakowski, Yoon, He, Hur, Zdancewic, CPP 2020)**:
   - `gpaco F r g := paco F (r ⊔ g) ⊔ r` with available base `r` and guarded hypothesis `g`
     released into `gupaco F r g := gpaco F r g ⊔ g` after one `F` step (`gpaco_unfold`, `gpaco_step`).
   - Constructive coinduction with base (`gpaco_coind`), guard accumulation (`gpaco_acc`), and
     finality (`gpaco_init`, `gpaco_final`).
4. **Up-To Closures & Companion (`rclo`, `gpaco_clo`, `cpn`, `Companion`)**:
   - Reflexive-transitive closure `rclo`, compatible closures (`Compatible`, `WCompatible`),
     full `gpaco_clo F clo r rg`, incremental absorption (`gpaco_clo_gupaco`), soundness into
     `F.gfp` (`gpaco_clo_final`, `gpaco_clo_sound`), and the greatest compatible closure
     `companion F` (`Companion`, `companion_compat`, `companion_step`, `companion_gupaco_eq`).
-/

public section

namespace Obend.Paco

set_option autoImplicit false

universe u

/-! ## 1. Binary Relations and Complete-Lattice Operations -/

/-- Binary relations over `α`. -/
abbrev Rel (α : Type u) : Type u := α → α → Prop

namespace Rel

variable {α : Type u}

/-- Empty relation `⊥`. -/
@[expose] def bot : Rel α := fun _ _ => False

/-- Full relation `⊤`. -/
@[expose] def top : Rel α := fun _ _ => True

/-- Relational union `R ⊔ S`. -/
@[expose] def union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y

/-- Relational intersection `R ⊓ S`. -/
@[expose] def inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y

/-- Relational inclusion `R ≤ S`. -/
@[expose] def le (R S : Rel α) : Prop := ∀ x y, R x y → S x y

instance : Max (Rel α) := ⟨union⟩
instance : Min (Rel α) := ⟨inter⟩
instance : LE (Rel α) := ⟨le⟩

end Rel

notation "⊥" => Rel.bot
notation "⊤" => Rel.top
infixl:65 " ⊔ " => Rel.union
infixl:70 " ⊓ " => Rel.inter

namespace Rel

variable {α : Type u}

theorem le_refl (R : Rel α) : R ≤ R := fun _ _ h => h

theorem le_trans {R S T : Rel α} (hRS : R ≤ S) (hST : S ≤ T) : R ≤ T :=
  fun x y hR => hST x y (hRS x y hR)

instance instTransLeRel : @Trans (Rel α) (Rel α) (Rel α) (· ≤ ·) (· ≤ ·) (· ≤ ·) :=
  ⟨le_trans⟩

theorem le_antisymm {R S : Rel α} (hRS : R ≤ S) (hSR : S ≤ R) : R = S :=
  funext fun x => funext fun y => propext ⟨hRS x y, hSR x y⟩

theorem bot_le (R : Rel α) : (⊥ : Rel α) ≤ R :=
  fun _ _ h => False.elim h

theorem le_top (R : Rel α) : R ≤ (⊤ : Rel α) :=
  fun _ _ _ => True.intro

theorem le_sup_left {R S : Rel α} : R ≤ R ⊔ S :=
  fun _ _ h => Or.inl h

theorem le_sup_right {R S : Rel α} : S ≤ R ⊔ S :=
  fun _ _ h => Or.inr h

theorem sup_le {R S T : Rel α} (hRT : R ≤ T) (hST : S ≤ T) : R ⊔ S ≤ T :=
  fun x y h => h.elim (hRT x y) (hST x y)

theorem sup_le_sup {R₁ R₂ S₁ S₂ : Rel α} (h₁ : R₁ ≤ R₂) (h₂ : S₁ ≤ S₂) :
    R₁ ⊔ S₁ ≤ R₂ ⊔ S₂ :=
  sup_le (le_trans h₁ le_sup_left) (le_trans h₂ le_sup_right)

theorem sup_le_sup_left {S₁ S₂ : Rel α} (h : S₁ ≤ S₂) (R : Rel α) :
    R ⊔ S₁ ≤ R ⊔ S₂ :=
  sup_le_sup (le_refl R) h

theorem sup_le_sup_right {R₁ R₂ : Rel α} (h : R₁ ≤ R₂) (S : Rel α) :
    R₁ ⊔ S ≤ R₂ ⊔ S :=
  sup_le_sup h (le_refl S)

theorem inf_le_left {R S : Rel α} : R ⊓ S ≤ R :=
  fun _ _ h => h.1

theorem inf_le_right {R S : Rel α} : R ⊓ S ≤ S :=
  fun _ _ h => h.2

theorem le_inf {R S T : Rel α} (hRS : R ≤ S) (hRT : R ≤ T) : R ≤ S ⊓ T :=
  fun x y h => ⟨hRS x y h, hRT x y h⟩

@[simp] theorem sup_bot (R : Rel α) : R ⊔ ⊥ = R :=
  le_antisymm (sup_le (le_refl R) (bot_le R)) le_sup_left

@[simp] theorem bot_sup (R : Rel α) : ⊥ ⊔ R = R :=
  le_antisymm (sup_le (bot_le R) (le_refl R)) le_sup_right

@[simp] theorem sup_idem (R : Rel α) : R ⊔ R = R :=
  le_antisymm (sup_le (le_refl R) (le_refl R)) le_sup_left

theorem sup_comm (R S : Rel α) : R ⊔ S = S ⊔ R :=
  le_antisymm (sup_le le_sup_right le_sup_left) (sup_le le_sup_right le_sup_left)

theorem sup_assoc (R S T : Rel α) : (R ⊔ S) ⊔ T = R ⊔ (S ⊔ T) :=
  le_antisymm
    (sup_le (sup_le le_sup_left (le_trans le_sup_left le_sup_right))
      (le_trans le_sup_right le_sup_right))
    (sup_le (le_trans le_sup_left le_sup_left)
      (sup_le (le_trans le_sup_right le_sup_left) le_sup_right))

end Rel

/-! ## 2. Monotone Relational Endofunctors and Knaster–Tarski `gfp` -/

/-- A relational operator `F` is monotone when `R ≤ S → F R ≤ F S`. -/
@[expose] def Monotone2 {α : Type u} (F : Rel α → Rel α) : Prop :=
  ∀ R S, R ≤ S → F R ≤ F S

/-- Bundled monotone relational endofunctor on `Rel α`. -/
structure MonoRel (α : Type u) where
  F : Rel α → Rel α
  mono : Monotone2 F

namespace MonoRel

variable {α : Type u}

instance : CoeFun (MonoRel α) (fun _ => Rel α → Rel α) := ⟨MonoRel.F⟩

theorem mono' (F : MonoRel α) {R S : Rel α} (h : R ≤ S) : F R ≤ F S :=
  F.mono R S h

/-- Greatest fixed point of `F` (Knaster–Tarski union of all post-fixpoints). -/
@[expose] def gfp (F : MonoRel α) : Rel α :=
  fun x y => ∃ R : Rel α, (∀ a b, R a b → F R a b) ∧ R x y

/-- Standard coinduction into `F.gfp`: every post-fixpoint is below `F.gfp`. -/
theorem le_gfp (F : MonoRel α) {R : Rel α} (hpost : R ≤ F R) : R ≤ F.gfp :=
  fun _ _ hxy => ⟨R, hpost, hxy⟩

/-- `F.gfp` is a post-fixpoint of `F` (unfolding). -/
theorem gfp_unfold (F : MonoRel α) : F.gfp ≤ F F.gfp := by
  intro x y ⟨R, hpost, hxy⟩
  exact F.mono' (le_gfp F hpost) x y (hpost x y hxy)

/-- `F.gfp` is a pre-fixpoint of `F` (folding). -/
theorem gfp_fold (F : MonoRel α) : F F.gfp ≤ F.gfp := by
  apply le_gfp F
  exact F.mono' (gfp_unfold F)

/-- Fixed-point equation `F.gfp = F F.gfp`. -/
theorem gfp_fixed (F : MonoRel α) : F.gfp = F F.gfp :=
  Rel.le_antisymm (gfp_unfold F) (gfp_fold F)

end MonoRel

/-! ## 3. Hur-et-al. Parameterized Coinduction (`paco`, `upaco`) -/

section PacoCore

variable {α : Type u}

/-- Parameterized greatest fixed point `paco F r := gfp (λ R. F (R ⊔ r))`. -/
@[expose] def paco (F : MonoRel α) (r : Rel α) : Rel α :=
  fun x y => ∃ R : Rel α, (∀ a b, R a b → F (R ⊔ r) a b) ∧ R x y

/-- Usable coinductive hypothesis `upaco F r := paco F r ⊔ r`. -/
@[expose] def upaco (F : MonoRel α) (r : Rel α) : Rel α :=
  paco F r ⊔ r

theorem paco_coind (F : MonoRel α) (R r : Rel α) {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ r) a b) (hxy : R x y) : paco F r x y :=
  ⟨R, hpost, hxy⟩

theorem paco_coind_le (F : MonoRel α) (r R : Rel α)
    (hpost : R ≤ F (R ⊔ r)) : R ≤ paco F r :=
  fun _ _ hxy => ⟨R, hpost, hxy⟩

/-- Monotonicity of `paco` in its parameter `r`. -/
theorem paco_mon (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    paco F r ≤ paco F s := by
  intro x y ⟨R, hpost, hxy⟩
  refine ⟨R, fun a b hab => ?_, hxy⟩
  exact F.mono' (Rel.sup_le_sup_left hrs R) a b (hpost a b hab)

/-- Joint monotonicity of `paco` in both the endofunctor `F` and parameter `r`. -/
theorem paco_mon_gen {F G : MonoRel α} {r s : Rel α}
    (hFG : ∀ R, F R ≤ G R) (hrs : r ≤ s) :
    paco F r ≤ paco G s := by
  intro x y ⟨R, hpost, hxy⟩
  refine ⟨R, fun a b hab => ?_, hxy⟩
  exact hFG (R ⊔ s) a b (F.mono' (Rel.sup_le_sup_left hrs R) a b (hpost a b hab))

/-- Monotonicity of `upaco` in its parameter `r`. -/
theorem upaco_mon (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    upaco F r ≤ upaco F s :=
  Rel.sup_le_sup (paco_mon F hrs) hrs

/-- Unfold `paco`: `paco F r ≤ F (upaco F r)`. -/
theorem paco_unfold (F : MonoRel α) (r : Rel α) :
    paco F r ≤ F (upaco F r) := by
  intro x y ⟨R, hpost, hxy⟩
  have hle : R ⊔ r ≤ upaco F r :=
    Rel.sup_le_sup_right (paco_coind_le F r R hpost) r
  exact F.mono' hle x y (hpost x y hxy)

/-- Fold `paco`: `F (upaco F r) ≤ paco F r`. -/
theorem paco_fold (F : MonoRel α) (r : Rel α) :
    F (upaco F r) ≤ paco F r := by
  apply paco_coind_le F r (F (upaco F r))
  have hle : upaco F r ≤ F (upaco F r) ⊔ r :=
    Rel.sup_le_sup_right (paco_unfold F r) r
  exact F.mono' hle

/-- Fixed-point equation `paco F r = F (upaco F r)`. -/
theorem paco_fixed (F : MonoRel α) (r : Rel α) :
    paco F r = F (upaco F r) :=
  Rel.le_antisymm (paco_unfold F r) (paco_fold F r)

/-- Initialization law: at `⊥`, `paco F ⊥` is `F.gfp`. -/
theorem paco_init (F : MonoRel α) : paco F ⊥ = F.gfp := by
  apply Rel.le_antisymm
  · intro x y ⟨R, hpost, hxy⟩
    refine ⟨R, fun a b hab => ?_, hxy⟩
    have h := hpost a b hab
    rw [Rel.sup_bot] at h
    exact h
  · intro x y ⟨R, hpost, hxy⟩
    refine ⟨R, fun a b hab => ?_, hxy⟩
    rw [Rel.sup_bot]
    exact hpost a b hab

/-- Accumulation law (Hur et al.): `paco F (upaco F r) ≤ paco F r`. -/
theorem paco_acc_upaco (F : MonoRel α) (r : Rel α) :
    paco F (upaco F r) ≤ paco F r := by
  intro x y ⟨R, hpost, hxy⟩
  refine ⟨R ⊔ paco F r, fun a b hab => ?_, Or.inl hxy⟩
  cases hab with
  | inl hR =>
    have hle : R ⊔ upaco F r ≤ (R ⊔ paco F r) ⊔ r := by
      intro u v huv
      cases huv with
      | inl hRu => exact Or.inl (Or.inl hRu)
      | inr hup =>
        cases hup with
        | inl hp => exact Or.inl (Or.inr hp)
        | inr hr => exact Or.inr hr
    exact F.mono' hle a b (hpost a b hR)
  | inr hp =>
    have hle : upaco F r ≤ (R ⊔ paco F r) ⊔ r := by
      intro u v huv
      cases huv with
      | inl hp' => exact Or.inl (Or.inr hp')
      | inr hr => exact Or.inr hr
    exact F.mono' hle a b (paco_unfold F r a b hp)

/-- Accumulation law: `paco F (paco F r) ≤ paco F r`. -/
theorem paco_acc (F : MonoRel α) (r : Rel α) :
    paco F (paco F r) ≤ paco F r :=
  Rel.le_trans (paco_mon F Rel.le_sup_left) (paco_acc_upaco F r)

/-- Idempotence of `upaco`: `upaco F (upaco F r) = upaco F r`. -/
theorem upaco_idem (F : MonoRel α) (r : Rel α) :
    upaco F (upaco F r) = upaco F r := by
  apply Rel.le_antisymm
  · exact Rel.sup_le (Rel.le_trans (paco_acc_upaco F r) Rel.le_sup_left) (Rel.le_refl _)
  · exact Rel.le_sup_right

/-- Soundness of `paco` into `F.gfp` whenever the parameter `r ≤ F.gfp`. -/
theorem paco_final (F : MonoRel α) (r : Rel α) (hr : r ≤ F.gfp) :
    paco F r ≤ F.gfp := by
  calc paco F r
      ≤ paco F F.gfp := paco_mon F hr
    _ = paco F (paco F ⊥) := by rw [paco_init]
    _ ≤ paco F ⊥ := paco_acc F ⊥
    _ = F.gfp := paco_init F

end PacoCore

/-! ## 4. Generalized Parameterized Coinduction (`gpaco`, `gupaco` — CPP 2020) -/

section GPacoCore

variable {α : Type u}

/-- Generalized parameterized coinduction with available base `r` and guarded hypothesis `g`:
`gpaco F r g := paco F (r ⊔ g) ⊔ r`. -/
@[expose] def gpaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  paco F (r ⊔ g) ⊔ r

/-- Usable hypothesis after unfolding one `F` step:
`gupaco F r g := gpaco F r g ⊔ g = upaco F (r ⊔ g)`. -/
@[expose] def gupaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  gpaco F r g ⊔ g

theorem gupaco_eq_upaco (F : MonoRel α) (r g : Rel α) :
    gupaco F r g = upaco F (r ⊔ g) := by
  apply Rel.le_antisymm
  · intro x y h
    rcases h with (hp | hr) | hg
    · exact Or.inl hp
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hg)
  · intro x y h
    rcases h with hp | (hr | hg)
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hg

@[simp] theorem gpaco_bot_g (F : MonoRel α) (r : Rel α) :
    gpaco F r ⊥ = upaco F r := by
  simp only [gpaco, Rel.sup_bot, upaco]

@[simp] theorem gpaco_bot_r (F : MonoRel α) (g : Rel α) :
    gpaco F ⊥ g = paco F g := by
  simp only [gpaco, Rel.bot_sup, Rel.sup_bot]

@[simp] theorem gpaco_diag (F : MonoRel α) (r : Rel α) :
    gpaco F r r = upaco F r := by
  simp only [gpaco, Rel.sup_idem, upaco]

/-- Initialization law: `gpaco F ⊥ ⊥ = F.gfp`. -/
theorem gpaco_init (F : MonoRel α) : gpaco F ⊥ ⊥ = F.gfp := by
  rw [gpaco_bot_r, paco_init]

theorem r_le_gpaco (F : MonoRel α) (r g : Rel α) : r ≤ gpaco F r g :=
  Rel.le_sup_right

theorem paco_le_gpaco (F : MonoRel α) (r g : Rel α) :
    paco F (r ⊔ g) ≤ gpaco F r g :=
  Rel.le_sup_left

theorem gpaco_le_gupaco (F : MonoRel α) (r g : Rel α) :
    gpaco F r g ≤ gupaco F r g :=
  Rel.le_sup_left

theorem g_le_gupaco (F : MonoRel α) (r g : Rel α) : g ≤ gupaco F r g :=
  Rel.le_sup_right

theorem gpaco_mon_r (F : MonoRel α) (g : Rel α) {r r' : Rel α} (hr : r ≤ r') :
    gpaco F r g ≤ gpaco F r' g :=
  Rel.sup_le_sup (paco_mon F (Rel.sup_le_sup_right hr g)) hr

theorem gpaco_mon_g (F : MonoRel α) (r : Rel α) {g g' : Rel α} (hg : g ≤ g') :
    gpaco F r g ≤ gpaco F r g' :=
  Rel.sup_le_sup_right (paco_mon F (Rel.sup_le_sup_left hg r)) r

/-- Joint monotonicity of `gpaco` in `r` and `g`. -/
theorem gpaco_mon (F : MonoRel α) {r r' g g' : Rel α}
    (hr : r ≤ r') (hg : g ≤ g') : gpaco F r g ≤ gpaco F r' g' :=
  Rel.le_trans (gpaco_mon_r F g hr) (gpaco_mon_g F r' hg)

/-- Joint monotonicity of `gupaco` in `r` and `g`. -/
theorem gupaco_mon (F : MonoRel α) {r r' g g' : Rel α}
    (hr : r ≤ r') (hg : g ≤ g') : gupaco F r g ≤ gupaco F r' g' :=
  Rel.sup_le_sup (gpaco_mon F hr hg) hg

/-- Unfold `gpaco`: releases the guard `g` into `gupaco F r g`. -/
theorem gpaco_unfold (F : MonoRel α) (r g : Rel α) :
    gpaco F r g ≤ F (gupaco F r g) ⊔ r := by
  intro x y hxy
  cases hxy with
  | inl hpaco =>
    left
    rw [gupaco_eq_upaco]
    exact paco_unfold F (r ⊔ g) x y hpaco
  | inr hr =>
    exact Or.inr hr

/-- Fold `F (gupaco F r g)` into `gpaco F r g`. -/
theorem gpaco_fold (F : MonoRel α) (r g : Rel α) :
    F (gupaco F r g) ≤ gpaco F r g := by
  intro x y hxy
  left
  rw [gupaco_eq_upaco] at hxy
  exact paco_fold F (r ⊔ g) x y hxy

/-- Fixed-point unfolding equation `gpaco F r g = F (gupaco F r g) ⊔ r`. -/
theorem gpaco_step (F : MonoRel α) (r g : Rel α) :
    gpaco F r g = F (gupaco F r g) ⊔ r :=
  Rel.le_antisymm (gpaco_unfold F r g) (Rel.sup_le (gpaco_fold F r g) (r_le_gpaco F r g))

/-- Guard accumulation law: `gpaco F r (gupaco F r g) ≤ gpaco F r g`. -/
theorem gpaco_acc (F : MonoRel α) (r g : Rel α) :
    gpaco F r (gupaco F r g) ≤ gpaco F r g := by
  intro x y hxy
  cases hxy with
  | inl hpaco =>
    left
    have hle : r ⊔ gupaco F r g ≤ upaco F (r ⊔ g) := by
      intro a b hab
      rcases hab with hr | hgu
      · exact Or.inr (Or.inl hr)
      · rw [gupaco_eq_upaco] at hgu
        exact hgu
    exact paco_acc_upaco F (r ⊔ g) x y (paco_mon F hle x y hpaco)
  | inr hr =>
    exact Or.inr hr

/-- Constructive coinduction for `gpaco` (no `Classical.choice` needed!):
if `R` steps into `F (R ⊔ gupaco F r g)` or lands in the base `r`, then `R ≤ gpaco F r g`. -/
theorem gpaco_coind (F : MonoRel α) (R r g : Rel α) {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b)
    (hxy : R x y) : gpaco F r g x y := by
  cases hpost x y hxy with
  | inr hr => exact Or.inr hr
  | inl hFxy =>
    left
    let R' : Rel α := fun a b => R a b ∧ F (R ⊔ gupaco F r g) a b
    refine paco_coind F (R' ⊔ paco F (r ⊔ g)) (r ⊔ g) (fun a b hab => ?_) (Or.inl ⟨hxy, hFxy⟩)
    cases hab with
    | inl hR' =>
      have hle : R ⊔ gupaco F r g ≤ (R' ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
        intro u v huv
        cases huv with
        | inl hRuv =>
          cases hpost u v hRuv with
          | inl hFuv => exact Or.inl (Or.inl ⟨hRuv, hFuv⟩)
          | inr hruv => exact Or.inr (Or.inl hruv)
        | inr hgu =>
          rw [gupaco_eq_upaco] at hgu
          cases hgu with
          | inl hp => exact Or.inl (Or.inr hp)
          | inr hrg => exact Or.inr hrg
      exact F.mono' hle a b hR'.2
    | inr hp =>
      have hle : upaco F (r ⊔ g) ≤ (R' ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
        intro u v huv
        cases huv with
        | inl hp' => exact Or.inl (Or.inr hp')
        | inr hrg => exact Or.inr hrg
      exact F.mono' hle a b (paco_unfold F (r ⊔ g) a b hp)

/-- Finality of `gpaco` into `F.gfp` whenever `r ≤ F.gfp` and `g ≤ F.gfp`. -/
theorem gpaco_final (F : MonoRel α) (r g : Rel α)
    (hr : r ≤ F.gfp) (hg : g ≤ F.gfp) : gpaco F r g ≤ F.gfp :=
  Rel.sup_le (paco_final F (r ⊔ g) (Rel.sup_le hr hg)) hr

end GPacoCore

/-! ## 5. Up-To Closures (`rclo`, `Compatible`, `WCompatible`, `gpaco_clo`) -/

section UpToClosure

variable {α : Type u}

/-- Reflexive-transitive closure of `R` under a relational closure operator `clo`. -/
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base {x y : α} (h : R x y) : rclo clo R x y
  | clo {x y : α} (R' : Rel α) (hR' : R' ≤ rclo clo R) (h : clo R' x y) : rclo clo R x y

namespace rclo

variable {clo : Rel α → Rel α} {R S : Rel α}

theorem base_le : R ≤ rclo clo R :=
  fun _ _ h => .base h

theorem clo_base : clo R ≤ rclo clo R :=
  fun _ _ h => .clo R base_le h

theorem mono (hRS : R ≤ S) : rclo clo R ≤ rclo clo S := by
  intro x y h
  induction h with
  | base hr => exact .base (hRS _ _ hr)
  | clo R' _ hclo ih => exact .clo R' ih hclo

theorem mono_clo {clo₁ clo₂ : Rel α → Rel α} (h : ∀ X, clo₁ X ≤ clo₂ X) :
    rclo clo₁ R ≤ rclo clo₂ R := by
  intro x y hxy
  induction hxy with
  | base hr => exact .base hr
  | clo R' _ hclo ih => exact .clo R' ih (h R' _ _ hclo)

theorem clo_rclo : clo (rclo clo R) ≤ rclo clo R :=
  fun _ _ h => .clo (rclo clo R) (Rel.le_refl _) h

theorem rclo_rclo : rclo clo (rclo clo R) ≤ rclo clo R := by
  intro x y h
  induction h with
  | base hr => exact hr
  | clo R' _ hclo ih => exact .clo R' ih hclo

theorem rclo_smallest {R S : Rel α} (hRS : R ≤ S) (hclo : ∀ R', R' ≤ S → clo R' ≤ S) :
    rclo clo R ≤ S := by
  intro x y h
  induction h with
  | base hr => exact hRS _ _ hr
  | clo R' _ hcloR' ih => exact hclo R' ih _ _ hcloR'

theorem rclo_id (R : Rel α) : rclo id R = R :=
  Rel.le_antisymm (rclo_smallest (Rel.le_refl R) (fun _ h => h)) base_le

end rclo

/-- Monotonicity of a closure operator (`CloMono`). -/
abbrev CloMono (clo : Rel α → Rel α) : Prop := Monotone2 clo

/-- Compatibility of a closure operator `clo` with `F`: `clo (F R) ≤ F (clo R)`. -/
@[expose] def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)

theorem cloMono_id : CloMono (id : Rel α → Rel α) :=
  fun _ _ h => h

theorem compatible_id (F : MonoRel α) : Compatible F id :=
  fun _ => Rel.le_refl _

theorem compatible_comp (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h_mono₁ : CloMono clo₁) (h_compat₁ : Compatible F clo₁) (h_compat₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂) := by
  intro R
  calc clo₁ (clo₂ (F R))
      ≤ clo₁ (F (clo₂ R)) := h_mono₁ _ _ (h_compat₂ R)
    _ ≤ F (clo₁ (clo₂ R)) := h_compat₁ (clo₂ R)

/-- If `clo` is monotone and compatible with `F`, then `rclo clo` is compatible with `F`. -/
theorem rclo_compatible (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    Compatible F (rclo clo) := by
  intro R x y h
  induction h with
  | base hFR => exact F.mono' rclo.base_le _ _ hFR
  | clo R' _ hclo ih =>
    have h1 : clo R' ≤ clo (F (rclo clo R)) := h_mono R' _ ih
    have h2 : clo (F (rclo clo R)) ≤ F (clo (rclo clo R)) := h_compat (rclo clo R)
    have h3 : F (clo (rclo clo R)) ≤ F (rclo clo R) := F.mono' rclo.clo_rclo
    exact h3 _ _ (h2 _ _ (h1 _ _ hclo))

/-- Modified generator `F ∘ rclo clo` for `gpaco_clo`. -/
@[expose] def composeRclo (F : MonoRel α) (clo : Rel α → Rel α) : MonoRel α where
  F := F ∘ rclo clo
  mono := fun _ _ hRS => F.mono' (rclo.mono hRS)

theorem composeRclo_id (F : MonoRel α) : composeRclo F id = F := by
  cases F with
  | mk f hf =>
    simp only [composeRclo]
    congr 1
    funext R
    simp only [Function.comp_apply, rclo.rclo_id]

/-- Full `gpaco` with up-to closure `clo`, accumulator `r`, and guard `rg` (Coq `gpacoN`). -/
@[expose] def gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) : Rel α :=
  rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r)

/-- Symmetric up-to hypothesis `gupaco_clo F clo r := gpaco_clo F clo r r`. -/
@[expose] def gupaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r : Rel α) : Rel α :=
  gpaco_clo F clo r r

/-- Weak compatibility of `clo` with `F`: `clo (F R) ≤ F (gupaco_clo F clo R)`. -/
@[expose] def WCompatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (gupaco_clo F clo R)

theorem r_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    r ≤ gpaco_clo F clo r rg :=
  fun _ _ hr => rclo.base (Or.inr hr)

theorem paco_le_gpaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    paco (composeRclo F clo) (rg ⊔ r) ≤ gpaco_clo F clo r rg :=
  fun _ _ hp => rclo.base (Or.inl hp)

theorem clo_le_gupaco_clo (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    clo R ≤ gupaco_clo F clo R :=
  fun _ _ hclo => rclo.clo R (fun _ _ hR => rclo.base (Or.inr hR)) hclo

theorem gpaco_clo_mon (F : MonoRel α) (clo : Rel α → Rel α)
    {r r' rg rg' : Rel α} (hr : r ≤ r') (hrg : rg ≤ rg') :
    gpaco_clo F clo r rg ≤ gpaco_clo F clo r' rg' :=
  rclo.mono (Rel.sup_le_sup (paco_mon (composeRclo F clo) (Rel.sup_le_sup hrg hr)) hr)

/-- Unfolding law for `gpaco_clo`. -/
theorem gpaco_clo_unfold (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    gpaco_clo F clo r rg ≤
      rclo clo (F (rclo clo (upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r) :=
  rclo.mono (Rel.sup_le_sup_right (paco_unfold (composeRclo F clo) (rg ⊔ r)) r)

/-- Full coinduction principle for `gpaco_clo` (`gpacoN_cofix`). -/
theorem gpaco_clo_coind (F : MonoRel α) (clo : Rel α → Rel α) (r rg l : Rel α)
    (h_obg : ∀ rr, rg ≤ rr → l ≤ rr → l ≤ gpaco_clo F clo r rr) :
    l ≤ gpaco_clo F clo r rg := by
  have hIN : l ≤ gpaco_clo F clo r (rg ⊔ l) := h_obg (rg ⊔ l) Rel.le_sup_left Rel.le_sup_right
  intro x y hlxy
  have hgp := hIN x y hlxy
  have h_inner : paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ r ≤
      rclo clo (paco (composeRclo F clo) (rg ⊔ r) ⊔ r) := by
    apply Rel.sup_le
    · intro a b hpaco
      apply rclo.base
      left
      refine paco_coind (composeRclo F clo)
        (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) (rg ⊔ r) (fun u v huv => ?_) hpaco
      have hunf := paco_unfold (composeRclo F clo) ((rg ⊔ l) ⊔ r) u v huv
      have hrclo : rclo clo (upaco (composeRclo F clo) ((rg ⊔ l) ⊔ r)) ≤
          rclo clo (paco (composeRclo F clo) ((rg ⊔ l) ⊔ r) ⊔ (rg ⊔ r)) := by
        intro x' y' hup
        induction hup with
        | base hbase =>
          rcases hbase with hp | ((hrg | hl') | hr')
          · exact rclo.base (Or.inl hp)
          · exact rclo.base (Or.inr (Or.inl hrg))
          · exact rclo.mono (Rel.sup_le_sup_left Rel.le_sup_right _) _ _ (hIN _ _ hl')
          · exact rclo.base (Or.inr (Or.inr hr'))
        | clo R' _ hcloR' ih => exact rclo.clo R' ih hcloR'
      exact F.mono' hrclo u v hunf
    · exact fun _ _ hr => rclo.base (Or.inr hr)
  exact rclo.rclo_rclo x y (rclo.mono h_inner x y hgp)

/-- Constructive one-step cofix rule for `gpaco_clo` (no `Classical.choice`). -/
theorem gpaco_clo_cofix (F : MonoRel α) (clo : Rel α → Rel α) (r rg R : Rel α) {x y : α}
    (hR : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r)
    (hxy : R x y) : gpaco_clo F clo r rg x y := by
  apply rclo.base
  cases hR x y hxy with
  | inr hr => exact Or.inr hr
  | inl hF =>
    left
    let R' : Rel α := fun a b => R a b ∧ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) a b
    refine paco_coind (composeRclo F clo)
      (R' ⊔ paco (composeRclo F clo) (rg ⊔ r)) (rg ⊔ r) (fun a b hab => ?_) (Or.inl ⟨hxy, hF⟩)
    cases hab with
    | inl hR' =>
      refine F.mono' (rclo.mono fun u v huv => ?_) a b hR'.2
      cases huv with
      | inl hRuv =>
        cases hR u v hRuv with
        | inl hFuv => exact Or.inl (Or.inl ⟨hRuv, hFuv⟩)
        | inr hruv => exact Or.inr (Or.inr hruv)
      | inr hup =>
        cases hup with
        | inl hp => exact Or.inl (Or.inr hp)
        | inr hrg => exact Or.inr hrg
    | inr hpaco =>
      have hunf := paco_unfold (composeRclo F clo) (rg ⊔ r) a b hpaco
      refine F.mono' (rclo.mono fun u v huv => ?_) a b hunf
      cases huv with
      | inl hp => exact Or.inl (Or.inr hp)
      | inr hrg => exact Or.inr hrg

/-- Accumulation / absorption law for `gpaco_clo`:
`gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg`. -/
theorem gpaco_clo_gupaco (F : MonoRel α) (clo : Rel α → Rel α) (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg := by
  let G := gpaco_clo F clo r rg
  let P := composeRclo F clo
  apply gpaco_clo_coind F clo r rg (gupaco_clo F clo G)
  intro rr hINC hCIH x y hgup
  induction hgup with
  | base hbase =>
    cases hbase with
    | inl hpaco =>
      have hG_le_rr : G ≤ rr := fun a b hG => hCIH a b (rclo.base (Or.inr hG))
      have hGG : G ⊔ G ≤ rr ⊔ r :=
        Rel.sup_le (Rel.le_trans hG_le_rr Rel.le_sup_left) (Rel.le_trans hG_le_rr Rel.le_sup_left)
      exact rclo.base (Or.inl (paco_mon P hGG _ _ hpaco))
    | inr hG =>
      have h_le : paco P (rg ⊔ r) ⊔ r ≤ paco P (rr ⊔ r) ⊔ r :=
        Rel.sup_le_sup_right (paco_mon P (Rel.sup_le_sup_right hINC r)) r
      exact rclo.mono h_le _ _ hG
  | clo R' _ hcloR' ih =>
    exact rclo.clo R' ih hcloR'

theorem gfp_closed_clo (F : MonoRel α) (clo : Rel α → Rel α)
    (h_compat : Compatible F clo) : clo F.gfp ≤ F.gfp := by
  intro x y hclo
  have hpost : clo F.gfp ⊔ F.gfp ≤ F (clo F.gfp ⊔ F.gfp) := by
    apply Rel.sup_le
    · calc clo F.gfp
          = clo (F F.gfp) := congrArg clo F.gfp_fixed
        _ ≤ F (clo F.gfp) := h_compat F.gfp
        _ ≤ F (clo F.gfp ⊔ F.gfp) := F.mono' Rel.le_sup_left
    · calc F.gfp
          = F F.gfp := F.gfp_fixed
        _ ≤ F (clo F.gfp ⊔ F.gfp) := F.mono' Rel.le_sup_right
  exact MonoRel.le_gfp F hpost x y (Or.inl hclo)

theorem gfp_closed_rclo (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    rclo clo F.gfp ≤ F.gfp := by
  intro x y h
  induction h with
  | base hr => exact hr
  | clo R' _ hcloR' ih =>
    exact gfp_closed_clo F clo h_compat _ _ (h_mono R' _ ih _ _ hcloR')

theorem gfp_compose_rclo_le (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    (composeRclo F clo).gfp ≤ F.gfp := by
  let G := composeRclo F clo
  let R := G.gfp
  have hR_eq : R = F (rclo clo R) := G.gfp_fixed
  have h_idem : rclo clo (rclo clo R) = rclo clo R :=
    Rel.le_antisymm rclo.rclo_rclo rclo.base_le
  have hrclo_post_G : rclo clo R ≤ G (rclo clo R) := by
    change rclo clo R ≤ F (rclo clo (rclo clo R))
    rw [h_idem]
    have h1 : rclo clo R ≤ rclo clo (F (rclo clo R)) := by
      rw [← hR_eq]
      exact Rel.le_refl _
    have h2 : rclo clo (F (rclo clo R)) ≤ F (rclo clo (rclo clo R)) :=
      rclo_compatible F h_mono h_compat (rclo clo R)
    rw [h_idem] at h2
    exact Rel.le_trans h1 h2
  have hrclo_le_R : rclo clo R ≤ R := MonoRel.le_gfp G hrclo_post_G
  have hR_post_F : R ≤ F R := by
    calc R
        = F (rclo clo R) := hR_eq
      _ ≤ F R := F.mono' hrclo_le_R
  exact MonoRel.le_gfp F hR_post_F

/-- Soundness / finality of `gpaco_clo` into `F.gfp` for any monotone compatible closure `clo`. -/
theorem gpaco_clo_final (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) (hr : r ≤ F.gfp) (hrg : rg ≤ F.gfp) :
    gpaco_clo F clo r rg ≤ F.gfp := by
  let G := composeRclo F clo
  have hgfp_le_G : F.gfp ≤ G.gfp := by
    apply MonoRel.le_gfp G
    calc F.gfp
        = F F.gfp := F.gfp_fixed
      _ ≤ F (rclo clo F.gfp) := F.mono' rclo.base_le
  have hinner : paco G (rg ⊔ r) ⊔ r ≤ F.gfp := by
    apply Rel.sup_le _ hr
    have hparam : rg ⊔ r ≤ G.gfp :=
      Rel.sup_le (Rel.le_trans hrg hgfp_le_G) (Rel.le_trans hr hgfp_le_G)
    exact Rel.le_trans (paco_final G (rg ⊔ r) hparam) (gfp_compose_rclo_le F clo h_mono h_compat)
  exact Rel.le_trans (rclo.mono hinner) (gfp_closed_rclo F clo h_mono h_compat)

/-- Initialization law for `gpaco_clo`: at `⊥, ⊥`, a compatible monotone closure yields `F.gfp`. -/
theorem gpaco_clo_init (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    gpaco_clo F clo ⊥ ⊥ = F.gfp := by
  apply Rel.le_antisymm
  · exact gpaco_clo_final F clo h_mono h_compat ⊥ ⊥ (Rel.bot_le _) (Rel.bot_le _)
  · intro x y hgfp
    apply rclo.base
    left
    rw [Rel.sup_bot, paco_init]
    have hgfp_le_G : F.gfp ≤ (composeRclo F clo).gfp := by
      apply MonoRel.le_gfp (composeRclo F clo)
      calc F.gfp
          = F F.gfp := F.gfp_fixed
        _ ≤ F (rclo clo F.gfp) := F.mono' rclo.base_le
    exact hgfp_le_G x y hgfp

/-- Pointwise soundness of coinduction up-to `clo`: `gpaco_clo F clo ⊥ ⊥ x y → F.gfp x y`. -/
theorem gpaco_clo_sound (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo) {x y : α}
    (h : gpaco_clo F clo ⊥ ⊥ x y) : F.gfp x y :=
  gpaco_clo_final F clo h_mono h_compat ⊥ ⊥ (Rel.bot_le _) (Rel.bot_le _) x y h

end UpToClosure

/-! ## 6. The Companion (`cpn`, `Companion`, `companion`) -/

section CompanionTheory

variable {α : Type u}

/-- Greatest compatible monotone closure operator `cpn F` (Pous / Hur et al. / Zakowski et al.). -/
inductive cpn (F : MonoRel α) (R : Rel α) : Rel α where
  | intro {x y : α} (clo : Rel α → Rel α) (h_mono : CloMono clo)
      (h_compat : Compatible F clo) (h_clo : clo R x y) : cpn F R x y

/-- Packaged companion interface for a monotone relational endofunctor `F`. -/
structure Companion (F : MonoRel α) where
  C : Rel α → Rel α
  mono : CloMono C
  compat : Compatible F C
  extensive : ∀ R, R ≤ C R

/-- Canonical companion operator `companion F := cpn F`. -/
@[expose] def companion (F : MonoRel α) : Rel α → Rel α := cpn F

theorem companion_mono (F : MonoRel α) : CloMono (companion F) := by
  intro R S hRS x y ⟨clo, h_mono, h_compat, h_clo⟩
  exact ⟨clo, h_mono, h_compat, h_mono R S hRS x y h_clo⟩

theorem companion_greatest (F : MonoRel α) {clo : Rel α → Rel α} {R : Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ companion F R :=
  fun _ _ h => ⟨clo, h_mono, h_compat, h⟩

theorem companion_extensive (F : MonoRel α) (R : Rel α) : R ≤ companion F R :=
  companion_greatest F cloMono_id (compatible_id F)

theorem companion_compat (F : MonoRel α) : Compatible F (companion F) := by
  intro R x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h1 : clo (F R) ≤ F (clo R) := h_compat R
  have h2 : F (clo R) ≤ F (companion F R) := F.mono' (companion_greatest F h_mono h_compat)
  exact h2 x y (h1 x y h_clo)

/-- Packaged canonical companion `cpnCompanion F`. -/
def cpnCompanion (F : MonoRel α) : Companion F where
  C := companion F
  mono := companion_mono F
  compat := companion_compat F
  extensive := companion_extensive F

theorem companion_idem (F : MonoRel α) (R : Rel α) :
    companion F (companion F R) ≤ companion F R := by
  intro x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h_cmono : CloMono (clo ∘ companion F) :=
    fun X Y hXY => h_mono _ _ (companion_mono F X Y hXY)
  have h_ccompat : Compatible F (clo ∘ companion F) :=
    compatible_comp F h_mono h_compat (companion_compat F)
  exact companion_greatest F h_cmono h_ccompat x y h_clo

/-- `F` steps are absorbed by the companion (`cpn_step`): `F (companion F R) ≤ companion F R`. -/
theorem companion_step (F : MonoRel α) (R : Rel α) :
    F (companion F R) ≤ companion F R := by
  let clo : Rel α → Rel α := fun X => F (companion F X)
  have h_mono : CloMono clo := fun X Y hXY => F.mono' (companion_mono F X Y hXY)
  have h_compat : Compatible F clo := fun X => F.mono' (companion_compat F X)
  exact companion_greatest F h_mono h_compat

theorem companion_wcompat (F : MonoRel α) : WCompatible F (companion F) := by
  intro R x y h
  exact F.mono' (clo_le_gupaco_clo F (companion F) R) x y (companion_compat F R x y h)

theorem wcompat_compat_gupaco (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_wcompat : WCompatible F clo) :
    Compatible F (gupaco_clo F clo) := by
  intro R
  let P := composeRclo F clo
  have h_FR_le_paco : F R ≤ paco P (R ⊔ R) := by
    apply paco_coind_le P (R ⊔ R) (F R)
    exact F.mono' (fun _ _ hr => rclo.base (Or.inr (Or.inl hr)))
  have h_FR_le_gupaco : F R ≤ gupaco_clo F clo R :=
    fun x y hFR => rclo.base (Or.inl (h_FR_le_paco x y hFR))
  have h_idemp : ∀ X, gupaco_clo F clo (gupaco_clo F clo X) ≤ gupaco_clo F clo X :=
    fun X => gpaco_clo_gupaco F clo X X
  have h_paco_FR_le : paco P (F R ⊔ F R) ≤ gupaco_clo F clo R := fun x y hp =>
    h_idemp R x y (rclo.base (Or.inl (paco_mon P (Rel.sup_le_sup h_FR_le_gupaco h_FR_le_gupaco) x y hp)))
  intro x y hgup
  induction hgup with
  | base hbase =>
    cases hbase with
    | inl hpaco =>
      have hunf := paco_unfold P (F R ⊔ F R) _ _ hpaco
      have h_in : paco P (F R ⊔ F R) ⊔ (F R ⊔ F R) ≤ gupaco_clo F clo R :=
        Rel.sup_le h_paco_FR_le (Rel.sup_le h_FR_le_gupaco h_FR_le_gupaco)
      have h_rclo : rclo clo (paco P (F R ⊔ F R) ⊔ (F R ⊔ F R)) ≤ gupaco_clo F clo R :=
        fun a b hr => rclo.rclo_rclo a b (rclo.mono h_in a b hr)
      exact F.mono' h_rclo _ _ hunf
    | inr hFR =>
      exact F.mono' (r_le_gpaco_clo F clo R R) _ _ hFR
  | clo R' _ hcloR' ih =>
    have h1 := h_mono R' _ ih _ _ hcloR'
    exact F.mono' (h_idemp R) _ _ (h_wcompat (gupaco_clo F clo R) _ _ h1)

/-- `gupaco_clo` with the companion absorbs into `companion F`. -/
theorem companion_gupaco (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R ≤ companion F R := by
  have h_mono : CloMono (gupaco_clo F (companion F)) :=
    fun _ _ hXY => gpaco_clo_mon F (companion F) hXY hXY
  have h_compat : Compatible F (gupaco_clo F (companion F)) :=
    wcompat_compat_gupaco F (companion_mono F) (companion_wcompat F)
  exact companion_greatest F h_mono h_compat

/-- Fixed-point identity `gupaco_clo F (companion F) R = companion F R`. -/
theorem companion_gupaco_eq (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R = companion F R := by
  apply Rel.le_antisymm
  · exact companion_gupaco F R
  · intro x y hcpn
    exact rclo.mono Rel.le_sup_right x y (rclo.clo_base x y hcpn)

/-- Soundness of coinduction up-to the companion into `F.gfp`. -/
theorem gpaco_clo_companion_sound (F : MonoRel α) {x y : α}
    (h : gpaco_clo F (companion F) ⊥ ⊥ x y) : F.gfp x y :=
  gpaco_clo_sound F (companion F) (companion_mono F) (companion_compat F) h

end CompanionTheory

/-! ## 7. Concrete Inhabited Witness & Refutation Teeth (`orbitBisimF`) -/

/-- Concrete deterministic transition system on `Nat`:
`0 ↔ 2` oscillate with label `true`, while `1` self-loops with label `false`. -/
def orbitStep : Nat → Nat
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | n + 3 => n + 3

/-- Observable label at each state of `orbitStep`. -/
def orbitLabel : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | _ => false

/-- Bisimulation generator on `orbitStep`: states agree on `orbitLabel` and their successors
stand in `R`. -/
def orbitBisimF : MonoRel Nat where
  F R x y := orbitLabel x = orbitLabel y ∧ R (orbitStep x) (orbitStep y)
  mono _ _ hRS _ _ h := ⟨h.1, hRS _ _ h.2⟩

/-- Symmetric closure on `Rel Nat`, used as an up-to closure for `orbitBisimF`. -/
def symClo (R : Rel Nat) : Rel Nat := fun x y => R x y ∨ R y x

theorem symClo_mono : CloMono symClo := by
  intro R S hRS x y h
  rcases h with hxy | hyx
  · exact Or.inl (hRS x y hxy)
  · exact Or.inr (hRS y x hyx)

theorem symClo_compat_orbit : Compatible orbitBisimF symClo := by
  intro R x y h
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨hl, Or.inl hr⟩
  · exact ⟨hl.symm, Or.inr hr⟩

/-- Single-pair seed `(0, 2)` — without `(2, 0)`! Up-to `symClo` closes the cycle in one step. -/
def zeroTwoSeed : Rel Nat := fun x y => x = 0 ∧ y = 2

/-- **Inhabited witness (`gpaco_clo` + `symClo`)**: `gpaco_clo orbitBisimF symClo ⊥ ⊥ 0 2` holds
from the singleton seed `zeroTwoSeed` because `(0, 2)` steps to `(2, 0) ∈ symClo zeroTwoSeed`. -/
theorem orbit_zero_two_clo_inhabited : gpaco_clo orbitBisimF symClo ⊥ ⊥ 0 2 := by
  refine gpaco_clo_cofix orbitBisimF symClo ⊥ ⊥ zeroTwoSeed (fun a b hab => ?_) ⟨rfl, rfl⟩
  rcases hab with ⟨rfl, rfl⟩
  left
  refine ⟨rfl, ?_⟩
  exact rclo.clo zeroTwoSeed (fun u v huv => rclo.base (Or.inl huv)) (Or.inr ⟨rfl, rfl⟩)

/-- **Inhabited witness (`gpaco_clo` + `companion`)**: `0` and `2` are related up-to the canonical
companion `companion orbitBisimF`. -/
theorem orbit_companion_zero_two_inhabited :
    gpaco_clo orbitBisimF (companion orbitBisimF) ⊥ ⊥ 0 2 := by
  refine gpaco_clo_cofix orbitBisimF (companion orbitBisimF) ⊥ ⊥ zeroTwoSeed
    (fun a b hab => ?_) ⟨rfl, rfl⟩
  rcases hab with ⟨rfl, rfl⟩
  left
  refine ⟨rfl, ?_⟩
  apply rclo.clo zeroTwoSeed (fun u v huv => rclo.base (Or.inl huv))
  exact companion_greatest orbitBisimF symClo_mono symClo_compat_orbit 2 0 (Or.inr ⟨rfl, rfl⟩)

/-- **Derived bisimulation witness**: `orbitBisimF.gfp 0 2` via `gpaco_clo_sound`. -/
theorem orbit_zero_two_bisim_witness : orbitBisimF.gfp 0 2 :=
  gpaco_clo_sound orbitBisimF symClo symClo_mono symClo_compat_orbit orbit_zero_two_clo_inhabited

/-- **Refutation 1**: states `0` and `1` have distinct labels and are NOT bisimilar. -/
theorem orbit_zero_one_not_bisim : ¬ orbitBisimF.gfp 0 1 := by
  intro h
  have hunf := orbitBisimF.gfp_unfold 0 1 h
  exact Bool.noConfusion hunf.1

/-- **Refutation 2 (Guardedness tooth)**: placing a false pair `(0, 1)` into the *guarded*
slot `g` of `gpaco orbitBisimF ⊥ g` does NOT make `(0, 1)` provable, because `g` is only
released after a productive `orbitBisimF` step (which immediately checks `orbitLabel 0 = orbitLabel 1`). -/
theorem gpaco_guard_not_immediate :
    ¬ gpaco orbitBisimF ⊥ (fun x y => x = 0 ∧ y = 1) 0 1 := by
  intro h
  have hunf := gpaco_unfold orbitBisimF ⊥ (fun x y => x = 0 ∧ y = 1) 0 1 h
  rcases hunf with ⟨hl, _⟩ | hbot
  · exact Bool.noConfusion hl
  · exact hbot

end Obend.Paco

end
