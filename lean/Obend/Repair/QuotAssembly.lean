module
/-
# Obend.Repair.QuotAssembly — realizability `Asm(P)` escape hatch for stuck-free quotients

Clean, self-contained pure Lean 4 mechanization of the Realizability Assembly (`Asm(P)`) cover
descent pattern (`AssemblyRegularCoverage.coverDesc`):

- `CodeTracker Code Val`: combinatory/bytecode tracker substrate with canonical identity `idCode`
  and composition `compCode` whose evaluator `eval : Code → Val → Option Val` computes directly in
  Lean's reduction kernel (`rfl`).
- `Assembly Code Val X` & `AsmHom X Y`: pairs semantic specification elements `x : X` with
  non-empty computational realizers `Realizes v x`, while morphisms carry BOTH a specification
  function `specFun : α → β` AND an explicit computational `tracker : Code` that computes directly
  on raw codes.
- `EffectiveQuotient X R`: lifts any `R`-respecting morphism `h : AsmHom X Z` across `Quot.mk R`
  so that:
  1. `lifted.specFun` factors cleanly through `Quot.lift`,
  2. `lifted.tracker := compCode h.tracker q.canonCode` is **100% choice-free and `Quot.sound`-free**,
     reducing to canonical values by `rfl` in the Lean kernel even across distinct equivalent
     representatives `a₁ ≠ a₂` (`R a₁ a₂`), where naive `Eq.rec (Quot.sound hab)` gets stuck!
-/
public section
namespace Obend.Repair
set_option autoImplicit false

universe u v w w₁ w₂

/-! ## 1. Computational Code/Tracker Substrate (`CodeTracker`) -/

/-- A computational code/realizer algebra whose `eval` runs canonically on raw values `Val`. -/
class CodeTracker (Code : Type u) (Val : Type v) where
  eval : Code → Val → Option Val
  idCode : Code
  compCode : Code → Code → Code
  eval_id : ∀ v : Val, eval idCode v = some v
  eval_comp : ∀ (g f : Code) (v u w : Val),
    eval f v = some u → eval g u = some w → eval (compCode g f) v = some w

/-! ## 2. Realizability Assemblies (`Assembly`) & Tracked Morphisms (`AsmHom`) -/

/-- An assembly over `[CodeTracker Code Val]` equips carrier `X` with a non-empty realizer
    relation `Realizes : Val → X → Prop`. -/
structure Assembly (Code : Type u) (Val : Type v) [CodeTracker Code Val] (X : Type w) where
  Realizes : Val → X → Prop
  realized : ∀ x : X, ∃ v : Val, Realizes v x

/-- A tracked assembly morphism `AsmHom X Y`: carries the extensional specification map
    `specFun : α → β` AND a computational `tracker : Code` computing directly on raw realizers. -/
structure AsmHom {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} {β : Type w₂}
    (X : Assembly Code Val α) (Y : Assembly Code Val β) where
  specFun : α → β
  tracker : Code
  tracks : ∀ (x : α) (v : Val),
    X.Realizes v x → ∃ w : Val, T.eval tracker v = some w ∧ Y.Realizes w (specFun x)

namespace AsmHom

/-- Identity assembly morphism tracked by `CodeTracker.idCode`. -/
@[expose] def id {Code : Type u} {Val : Type v} [T : CodeTracker Code Val] {α : Type w}
    (X : Assembly Code Val α) : AsmHom X X where
  specFun x := x
  tracker := T.idCode
  tracks _ v hv := ⟨v, T.eval_id v, hv⟩

/-- Composition of assembly morphisms tracked by `CodeTracker.compCode g.tracker f.tracker`. -/
@[expose] def comp {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w} {β : Type w₁} {γ : Type w₂}
    {X : Assembly Code Val α} {Y : Assembly Code Val β} {Z : Assembly Code Val γ}
    (g : AsmHom Y Z) (f : AsmHom X Y) : AsmHom X Z where
  specFun x := g.specFun (f.specFun x)
  tracker := T.compCode g.tracker f.tracker
  tracks x v hv := by
    obtain ⟨u, hfu, hu⟩ := f.tracks x v hv
    obtain ⟨w, hgw, hw⟩ := g.tracks (f.specFun x) u hu
    exact ⟨w, T.eval_comp g.tracker f.tracker v u w hfu hgw, hw⟩

end AsmHom

/-! ## 3. Choice-Free, `Quot.sound`-Free Effective Quotients (`EffectiveQuotient`) -/

/-- An effective quotient over `X : Assembly Code Val α` and relation `R : α → α → Prop`,
    equipped with a computational normalizer/lift code `canonCode : Code` producing valid
    representative realizers (defaulting to `idCode` when every `X`-realizer already realizes its
    equivalence class). -/
structure EffectiveQuotient {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} (X : Assembly Code Val α) (R : α → α → Prop) where
  canonCode : Code
  canon_tracks : ∀ (a : α) (v : Val),
    X.Realizes v a →
      ∃ (a' : α) (v' : Val),
        Quot.mk R a' = Quot.mk R a ∧ T.eval canonCode v = some v' ∧ X.Realizes v' a'

namespace EffectiveQuotient

/-- Default `EffectiveQuotient` with `canonCode := idCode` (zero normalization overhead). -/
@[expose] def ofId {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} (X : Assembly Code Val α) (R : α → α → Prop) :
    EffectiveQuotient X R where
  canonCode := T.idCode
  canon_tracks a v hv := ⟨a, v, rfl, T.eval_id v, hv⟩

/-- Quotient assembly on `Quot R`: `v` realizes `q : Quot R` iff `v` realizes some representative
    `a : α` with `Quot.mk R a = q`. Uses `Quot.ind` (targeting `Prop`) with zero `Classical.choice`
    and zero `Quot.sound`. -/
@[expose] def quotAssembly {Code : Type u} {Val : Type v} [CodeTracker Code Val]
    {α : Type w₁} (X : Assembly Code Val α) (R : α → α → Prop) :
    Assembly Code Val (Quot R) where
  Realizes v q := ∃ a : α, Quot.mk R a = q ∧ X.Realizes v a
  realized :=
    Quot.ind fun a =>
      let ⟨v, hv⟩ := X.realized a
      ⟨v, a, rfl, hv⟩

/-- Canonical quotient projection `Quot.mk R : AsmHom X (quotAssembly X R)`. -/
@[expose] def mkHom {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} (X : Assembly Code Val α) (R : α → α → Prop) :
    AsmHom X (quotAssembly X R) where
  specFun := Quot.mk R
  tracker := T.idCode
  tracks a v hv := ⟨v, T.eval_id v, ⟨a, rfl, hv⟩⟩

/-- **Choice-Free, `Quot.sound`-Free Quotient Lift (`liftHom`).**
    Lifts `h : AsmHom X Z` across `Quot.mk R`:
    - `specFun` is `Quot.lift h.specFun hResp` (computes judgmentally on `Quot.mk R a`),
    - `tracker` is `T.compCode h.tracker Q.canonCode` (pure `Code` data: zero `Classical.choice`,
      zero `Quot.sound`, reduces by `rfl` in the Lean kernel!). -/
@[expose] def liftHom {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} {γ : Type w₂}
    {X : Assembly Code Val α} {R : α → α → Prop}
    (Q : EffectiveQuotient X R)
    {Z : Assembly Code Val γ}
    (h : AsmHom X Z)
    (hResp : ∀ a₁ a₂ : α, R a₁ a₂ → h.specFun a₁ = h.specFun a₂) :
    AsmHom (quotAssembly X R) Z where
  specFun := Quot.lift h.specFun hResp
  tracker := T.compCode h.tracker Q.canonCode
  tracks := by
    rintro q v ⟨a, rfl, hva⟩
    obtain ⟨a', v', hQuotEq, hCanonEval, hva'⟩ := Q.canon_tracks a v hva
    obtain ⟨w, hhEval, hwz⟩ := h.tracks a' v' hva'
    have hSpecEq : h.specFun a' = Quot.lift h.specFun hResp (Quot.mk R a) := by
      change Quot.lift h.specFun hResp (Quot.mk R a') = Quot.lift h.specFun hResp (Quot.mk R a)
      exact congrArg (Quot.lift h.specFun hResp) hQuotEq
    exact ⟨w, T.eval_comp h.tracker Q.canonCode v v' w hCanonEval hhEval, hSpecEq ▸ hwz⟩

@[simp] theorem liftHom_tracker {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
    {α : Type w₁} {γ : Type w₂}
    {X : Assembly Code Val α} {R : α → α → Prop}
    (Q : EffectiveQuotient X R) {Z : Assembly Code Val γ}
    (h : AsmHom X Z) (hResp : ∀ a₁ a₂ : α, R a₁ a₂ → h.specFun a₁ = h.specFun a₂) :
    (Q.liftHom h hResp).tracker = T.compCode h.tracker Q.canonCode := rfl

@[simp] theorem liftHom_spec_mk {Code : Type u} {Val : Type v} [CodeTracker Code Val]
    {α : Type w₁} {γ : Type w₂}
    {X : Assembly Code Val α} {R : α → α → Prop}
    (Q : EffectiveQuotient X R) {Z : Assembly Code Val γ}
    (h : AsmHom X Z) (hResp : ∀ a₁ a₂ : α, R a₁ a₂ → h.specFun a₁ = h.specFun a₂) (a : α) :
    (Q.liftHom h hResp).specFun (Quot.mk R a) = h.specFun a := rfl

end EffectiveQuotient

/-! ## 4. Concrete Kernel-Reducible Bytecode Tracker (`CanonCode` / `CanonVal`) & Modular Quotient -/

/-- First-order canonical value domain for kernel-reducible realizers. -/
inductive CanonVal : Type where
  | nat : Nat → CanonVal
  | pair : CanonVal → CanonVal → CanonVal
  deriving @[expose] DecidableEq, Repr

/-- First-order combinator/bytecode instructions whose evaluator reduces by `rfl` in the Lean kernel. -/
inductive CanonCode : Type where
  | id : CanonCode
  | comp : CanonCode → CanonCode → CanonCode
  | addConst : Nat → CanonCode
  | mulConst : Nat → CanonCode
  | modCanon : Nat → CanonCode
  | fst : CanonCode
  | snd : CanonCode
  | fork : CanonCode → CanonCode → CanonCode
  deriving @[expose] DecidableEq, Repr

namespace CanonCode

@[expose] def eval : CanonCode → CanonVal → Option CanonVal
  | .id, v => some v
  | .comp g f, v =>
      match eval f v with
      | some u => eval g u
      | none => none
  | .addConst k, .nat n => some (.nat (n + k))
  | .addConst _, .pair _ _ => none
  | .mulConst k, .nat n => some (.nat (n * k))
  | .mulConst _, .pair _ _ => none
  | .modCanon m, .nat n => some (.nat (n % (m + 1)))
  | .modCanon _, .pair _ _ => none
  | .fst, .pair a _ => some a
  | .fst, .nat _ => none
  | .snd, .pair _ b => some b
  | .snd, .nat _ => none
  | .fork f g, v =>
      match eval f v, eval g v with
      | some a, some b => some (.pair a b)
      | _, _ => none

instance instCodeTracker : CodeTracker CanonCode CanonVal where
  eval := eval
  idCode := .id
  compCode := .comp
  eval_id _ := rfl
  eval_comp g f v u w hf hg := by
    dsimp only [eval]
    rw [hf]
    dsimp only
    exact hg

end CanonCode

/-- Standard `Nat` assembly realized by `CanonVal.nat n`. -/
@[expose] def natAssembly : Assembly CanonCode CanonVal Nat where
  Realizes v n := v = .nat n
  realized n := ⟨.nat n, rfl⟩

/-- Congruence modulo `m + 1` on `Nat`. -/
@[expose] def ModRel (m : Nat) (a b : Nat) : Prop :=
  a % (m + 1) = b % (m + 1)

/-- Effective quotient for `Nat / ModRel m` using `CanonCode.modCanon m` to canonicalize raw
    representatives into `0 .. m` before downstream computation. -/
@[expose] def modEffectiveQuotient (m : Nat) : EffectiveQuotient natAssembly (ModRel m) where
  canonCode := .modCanon m
  canon_tracks a v hv := by
    subst hv
    refine ⟨a % (m + 1), .nat (a % (m + 1)), ?_, rfl, rfl⟩
    apply Quot.sound
    change (a % (m + 1)) % (m + 1) = a % (m + 1)
    exact Nat.mod_eq_of_lt (Nat.mod_lt a (Nat.succ_pos m))

/--Residue-class map `(x ↦ (2 * x) % (m + 1))` lifted across `Quot (ModRel m)` with a canonical
   kernel-reducible tracker `.comp (.modCanon m) (.comp (.mulConst 2) (.modCanon m))`. -/
@[expose] def doubleModRawHom (m : Nat) : AsmHom natAssembly natAssembly where
  specFun x := (x * 2) % (m + 1)
  tracker := .comp (.modCanon m) (.mulConst 2)
  tracks x v hv := by
    subst hv
    exact ⟨.nat ((x * 2) % (m + 1)), rfl, rfl⟩

@[expose] def doubleModQuotHom (m : Nat) :
    AsmHom (EffectiveQuotient.quotAssembly natAssembly (ModRel m)) natAssembly :=
  (modEffectiveQuotient m).liftHom (doubleModRawHom m) (by
    intro a₁ a₂ hmod
    dsimp only [doubleModRawHom, ModRel] at hmod ⊢
    rw [Nat.mul_mod, hmod, ← Nat.mul_mod])

/-- Kernel `rfl` reduction witness: on raw representative `17` (`17 ≡ 2 mod 5`), the lifted
    quotient morphism's tracker normalizes `17 → 2 → 4 → 4` purely by kernel reduction (`rfl`)! -/
theorem doubleModQuotHom_tracker_reduces_rfl (k : Nat) :
    CanonCode.eval (doubleModQuotHom 4).tracker (.nat (5 * k + 2)) =
      some (.nat (((5 * k + 2) % 5 * 2) % 5)) := rfl

end Obend.Repair
end
