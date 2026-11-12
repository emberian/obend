module
/-
# Obend.Repair.AlgConfig — polynomial algebras, initiality & scar-free algebraic proof repair

Lean 4 mechanization of Plante–Paul–Viola–Kavvos–Ringer (`arXiv:2610.36669v1` §2–3):

- `PolyF A B X := (a : A) × (B a → X)` with functorial action `PolyF.map`.
- `PAlg`, `PAlgHom`, and homotopy-initial `InitPAlg` (`fold`, `fold_beta`, `fold_eta`, and
  contractibility of `PAlgHom init.alg γ`).
- `AlgConfig A B C D := InitPAlg A B C × InitPAlg A B D`:
  - Induced `AlgEquiv A B C D` (`forward_backward`, `backward_forward`, `constr_ok`, and
    uniqueness `forwardHom_unique`).
  - **Proposition 3.15 (`repair_by_instantiation`)**: `cfg.foldC γ x = cfg.foldD γ (cfg.forward x)`.
  - **Total-Space Dependent Elimination & Repair (`InitPAlg.elim`, `elim_repair_ok`,
    `InitPAlg.elimProp`, `elimProp_repair_ok`)**: derives dependent induction over `P : D → Type w`
    and `P : D → Prop` from `InitPAlg` via total-space sections without univalence.
- Concrete scar-free case study: `UnaryNat ↔ BinNat` (`zero | pos (one | bit0 | bit1)`), repairing
  both operations (`unaryIsZero → binIsZero`, `unaryAdd → binAdd`) and an inductive theorem
  (`unary_add_zero → bin_add_zero`) with zero residual dependency on `UnaryNat`.
-/
public section
namespace Obend.Repair
set_option autoImplicit false

universe u v w w₁ w₂

/-! ## 1. Polynomial Endofunctors (`PolyF`) and `P`-Algebras -/

/-- Polynomial endofunctor `P_{A, B}(X) := (a : A) × (B a → X)`. -/
abbrev PolyF (A : Type u) (B : A → Type v) (X : Type w) : Type (max u v w) :=
  (a : A) × (B a → X)

namespace PolyF

/-- Functorial action of `PolyF A B` on `f : X → Y`. -/
@[expose] def map {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    (f : X → Y) : PolyF A B X → PolyF A B Y
  | ⟨a, k⟩ => ⟨a, fun b => f (k b)⟩

@[simp] theorem map_id {A : Type u} {B : A → Type v} {X : Type w} (t : PolyF A B X) :
    PolyF.map (fun x => x) t = t := by
  cases t; rfl

theorem map_comp {A : Type u} {B : A → Type v} {X : Type w} {Y : Type w₁} {Z : Type w₂}
    (g : Y → Z) (f : X → Y) (t : PolyF A B X) :
    PolyF.map g (PolyF.map f t) = PolyF.map (fun x => g (f x)) t := by
  cases t; rfl

end PolyF

/-- An algebra `PolyF A B X → X` for polynomial `(A, B)` on carrier `X`. -/
structure PAlg (A : Type u) (B : A → Type v) (X : Type w) where
  op : PolyF A B X → X

/-- Homomorphism between `PAlg`s `(X, α) → (Y, β)`. -/
structure PAlgHom {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    (α : PAlg A B X) (β : PAlg A B Y) where
  toFun : X → Y
  hom_comm : ∀ t : PolyF A B X, toFun (α.op t) = β.op (PolyF.map toFun t)

namespace PAlgHom

theorem ext {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    {α : PAlg A B X} {β : PAlg A B Y} {f g : PAlgHom α β}
    (h : ∀ x : X, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  have hfun : _ = _ := funext h
  subst hfun
  rfl

@[expose] def id {A : Type u} {B : A → Type v} {X : Type w} (α : PAlg A B X) : PAlgHom α α where
  toFun x := x
  hom_comm t := by simp [PolyF.map_id]

@[expose] def comp {A : Type u} {B : A → Type v} {X : Type w} {Y : Type w₁} {Z : Type w₂}
    {α : PAlg A B X} {β : PAlg A B Y} {γ : PAlg A B Z}
    (g : PAlgHom β γ) (f : PAlgHom α β) : PAlgHom α γ where
  toFun x := g.toFun (f.toFun x)
  hom_comm t := by
    rw [f.hom_comm, g.hom_comm, PolyF.map_comp]

end PAlgHom

/-! ## 2. Homotopy-Initial `P`-Algebras (`InitPAlg`) & Total-Space Dependent Elimination -/

/-- Homotopy-initial `P`-algebra structure on carrier `C : Type w`: unique `fold` into any
    `Y : Type w` algebra with computation law `fold_beta` and uniqueness law `fold_eta`. -/
structure InitPAlg (A : Type u) (B : A → Type v) (C : Type w) where
  alg : PAlg A B C
  fold : ∀ {Y : Type w}, PAlg A B Y → C → Y
  fold_beta : ∀ {Y : Type w} (γ : PAlg A B Y) (t : PolyF A B C),
    fold γ (alg.op t) = γ.op (PolyF.map (fold γ) t)
  fold_eta : ∀ {Y : Type w} (γ : PAlg A B Y) (h : C → Y),
    (∀ t : PolyF A B C, h (alg.op t) = γ.op (PolyF.map h t)) →
    ∀ x : C, h x = fold γ x

namespace InitPAlg

/-- Canonical `PAlgHom` out of an initial algebra. -/
@[expose] def foldHom {A : Type u} {B : A → Type v} {C Y : Type w}
    (I : InitPAlg A B C) (γ : PAlg A B Y) : PAlgHom I.alg γ where
  toFun := I.fold γ
  hom_comm := I.fold_beta γ

/-- Contractibility of `PAlgHom I.alg γ` (Plante et al. Definition 3.7): every algebra
    homomorphism out of `I.alg` equals `I.foldHom γ`. -/
theorem hom_unique {A : Type u} {B : A → Type v} {C Y : Type w}
    (I : InitPAlg A B C) (γ : PAlg A B Y) (f : PAlgHom I.alg γ) :
    f = I.foldHom γ :=
  PAlgHom.ext (I.fold_eta γ f.toFun f.hom_comm)

/-- Folding `I.alg` into itself yields the identity map. -/
theorem fold_self {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (x : C) :
    I.fold I.alg x = x :=
  (I.fold_eta I.alg (fun c => c) (fun t => by simp [PolyF.map_id]) x).symm

/-- Total-space `P`-algebra on `(x : C) × P x` for `Type w`-valued dependent motives. -/
@[expose] def totalAlg {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩)) :
    PAlg A B ((x : C) × P x) where
  op := fun ⟨a, tk⟩ =>
    ⟨I.alg.op ⟨a, fun b => (tk b).1⟩,
     cases a (fun b => (tk b).1) (fun b => (tk b).2)⟩

/-- Total-space section `C → (x : C) × P x` induced by `I.fold`. -/
@[expose] def totalFold {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩)) :
    C → (x : C) × P x :=
  I.fold (I.totalAlg P cases)

/-- First projection of `totalFold` is the identity on `C` by initiality. -/
theorem totalFold_fst {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) :
    (I.totalFold P cases x).1 = x := by
  have hfst : ∀ c : C, (I.totalFold P cases c).1 = I.fold I.alg c := by
    apply I.fold_eta I.alg (fun c => (I.totalFold P cases c).1)
    intro ⟨a, k⟩
    exact congrArg Sigma.fst (I.fold_beta (I.totalAlg P cases) ⟨a, k⟩)
  rw [hfst x, I.fold_self x]

/-- Dependent eliminator for `P : C → Type w` derived solely from `InitPAlg` via the total-space section. -/
@[expose] def elim {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) : P x :=
  I.totalFold_fst P cases x ▸ (I.totalFold P cases x).2

/-- Subtype `P`-algebra on `{ x : C // P x }` for `Prop`-valued dependent motives. -/
@[expose] def subtypeAlg {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Prop)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩)) :
    PAlg A B { x : C // P x } where
  op := fun ⟨a, tk⟩ =>
    ⟨I.alg.op ⟨a, fun b => (tk b).1⟩,
     cases a (fun b => (tk b).1) (fun b => (tk b).2)⟩

/-- Dependent `Prop` induction principle derived from `InitPAlg` via `{ x : C // P x }`. -/
theorem elimProp {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Prop)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) : P x := by
  let sect := I.fold (I.subtypeAlg P cases)
  have hfst : ∀ c : C, (sect c).1 = c := by
    intro c
    have h₁ := I.fold_eta I.alg (fun z => (sect z).1)
      (fun ⟨a, k⟩ => congrArg Subtype.val (I.fold_beta (I.subtypeAlg P cases) ⟨a, k⟩)) c
    exact h₁.trans (I.fold_self c)
  exact hfst x ▸ (sect x).2

end InitPAlg

/-! ## 3. Algebra Equivalences & Configurations (`AlgConfig`) -/

/-- Explicit isomorphism of `P`-algebras on `C` and `D`. -/
structure AlgEquiv (A : Type u) (B : A → Type v) (C D : Type w) where
  algC : PAlg A B C
  algD : PAlg A B D
  forwardHom : PAlgHom algC algD
  backwardHom : PAlgHom algD algC
  backward_forward : ∀ x : C, backwardHom.toFun (forwardHom.toFun x) = x
  forward_backward : ∀ y : D, forwardHom.toFun (backwardHom.toFun y) = y

/-- An algebra configuration between carriers `C` and `D` (Plante et al. Definition 3.13):
    a pair of initial `P`-algebra structures for a shared polynomial `(A, B)`. -/
abbrev AlgConfig (A : Type u) (B : A → Type v) (C D : Type w) :=
  InitPAlg A B C × InitPAlg A B D

namespace AlgConfig

abbrev initC {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : InitPAlg A B C :=
  cfg.1

abbrev initD {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : InitPAlg A B D :=
  cfg.2

abbrev algC {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : PAlg A B C :=
  cfg.1.alg

abbrev algD {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : PAlg A B D :=
  cfg.2.alg

abbrev foldC {A : Type u} {B : A → Type v} {C D Y : Type w}
    (cfg : AlgConfig A B C D) (γ : PAlg A B Y) : C → Y :=
  cfg.1.fold γ

abbrev foldD {A : Type u} {B : A → Type v} {C D Y : Type w}
    (cfg : AlgConfig A B C D) (γ : PAlg A B Y) : D → Y :=
  cfg.2.fold γ

/-- Induced forward repair map `φ : C → D`. -/
@[expose] def forward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : C → D :=
  cfg.foldC cfg.algD

/-- Induced backward repair map `ψ : D → C`. -/
@[expose] def backward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : D → C :=
  cfg.foldD cfg.algC

/-- **Constructor Coherence (`constr_ok`, Proposition 2.3(1)).**
    `cfg.forward` commutes with the polynomial constructors of `C` and `D`. -/
theorem constr_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (t : PolyF A B C) :
    cfg.forward (cfg.algC.op t) = cfg.algD.op (PolyF.map cfg.forward t) :=
  cfg.1.fold_beta cfg.algD t

theorem backward_constr_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (t : PolyF A B D) :
    cfg.backward (cfg.algD.op t) = cfg.algC.op (PolyF.map cfg.backward t) :=
  cfg.2.fold_beta cfg.algC t

/-- **Proposition 3.15 (`repair_by_instantiation`).**
    Any `P`-algebra fold over `C` equals the *same* defining algebra `γ` folded over `D` after
    `cfg.forward` (`foldC γ x = foldD γ (forward x)`), justifying scar-free repair by re-instantiating
    `γ` at `D`. -/
theorem repair_by_instantiation {A : Type u} {B : A → Type v} {C D Y : Type w}
    (cfg : AlgConfig A B C D) (γ : PAlg A B Y) (x : C) :
    cfg.foldC γ x = cfg.foldD γ (cfg.forward x) := by
  symm
  apply cfg.1.fold_eta γ (fun c => cfg.foldD γ (cfg.forward c))
  intro t
  rw [cfg.constr_ok]
  dsimp only [foldD, algD]
  rw [cfg.2.fold_beta γ, PolyF.map_comp]

theorem backward_forward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (x : C) :
    cfg.backward (cfg.forward x) = x := by
  have h := cfg.repair_by_instantiation cfg.algC x
  change cfg.foldC cfg.algC x = cfg.backward (cfg.forward x) at h
  rw [← h]
  exact cfg.1.fold_self x

theorem forward_backward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (y : D) :
    cfg.forward (cfg.backward y) = y := by
  let symCfg : AlgConfig A B D C := (cfg.2, cfg.1)
  exact symCfg.backward_forward y

/-- Every `AlgConfig` canonically induces a unique `AlgEquiv A B C D` (Theorem 3.11). -/
@[expose] def toAlgEquiv {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) : AlgEquiv A B C D where
  algC := cfg.algC
  algD := cfg.algD
  forwardHom := cfg.1.foldHom cfg.algD
  backwardHom := cfg.2.foldHom cfg.algC
  backward_forward := cfg.backward_forward
  forward_backward := cfg.forward_backward

theorem forwardHom_unique {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (f : PAlgHom cfg.algC cfg.algD) :
    f = cfg.toAlgEquiv.forwardHom :=
  cfg.1.hom_unique cfg.algD f

/-! ## 4. Total-Space Dependent Elimination Repair (`elim_repair_ok`) -/

private theorem sigma_cast_symm {D : Type w} (P : D → Type w) {d₁ d₂ : D}
    (h : d₁ = d₂) (v : P d₂) :
    (⟨d₁, h.symm ▸ v⟩ : (y : D) × P y) = ⟨d₂, v⟩ := by
  cases h
  rfl

private theorem elim_eq_of_sigma_eq {C D : Type w} (φ : C → D) (P : D → Type w)
    {x : C} {sc : (c : C) × P (φ c)} {sd : (d : D) × P d}
    (hPair : (⟨φ sc.1, sc.2⟩ : (d : D) × P d) = sd)
    (hc : sc.1 = x) (hd : sd.1 = φ x) :
    (hc ▸ sc.2 : P (φ x)) = (hd ▸ sd.2 : P (φ x)) := by
  rcases sc with ⟨c₀, pc⟩
  rcases sd with ⟨d₀, pd⟩
  dsimp only at hPair hc hd ⊢
  subst hc
  cases hPair
  cases hd
  rfl

/-- Transport `D`-side induction cases along `cfg.forward` and `cfg.constr_ok` (Plante et al. `φ* casesD`). -/
@[expose] def pullbackCases {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (P : D → Type w)
    (casesD : (a : A) → (k : B a → D) → ((b : B a) → P (k b)) → P (cfg.algD.op ⟨a, k⟩)) :
    (a : A) → (k : B a → C) → ((b : B a) → P (cfg.forward (k b))) →
      P (cfg.forward (cfg.algC.op ⟨a, k⟩)) :=
  fun a k ih =>
    (cfg.constr_ok ⟨a, k⟩).symm ▸ casesD a (fun b => cfg.forward (k b)) ih

/-- **Total-Space Dependent Elimination Repair (`elim_repair_ok`, Proposition 2.3(3)).**
    Dependent elimination over `C` at motive `P ∘ cfg.forward` with transported cases
    `cfg.pullbackCases P casesD` equals native `D`-side dependent elimination at `cfg.forward x`—without
    univalence! -/
theorem elim_repair_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (P : D → Type w)
    (casesD : (a : A) → (k : B a → D) → ((b : B a) → P (k b)) → P (cfg.algD.op ⟨a, k⟩))
    (x : C) :
    cfg.initC.elim (fun c => P (cfg.forward c)) (cfg.pullbackCases P casesD) x =
      cfg.initD.elim P casesD (cfg.forward x) := by
  let casesC := cfg.pullbackCases P casesD
  let liftSigma : ((c : C) × P (cfg.forward c)) → ((d : D) × P d) :=
    fun ⟨c, pc⟩ => ⟨cfg.forward c, pc⟩
  have hPair :
      liftSigma (cfg.initC.totalFold (fun c => P (cfg.forward c)) casesC x) =
        cfg.initD.totalFold P casesD (cfg.forward x) := by
    have h₁ :
        liftSigma (cfg.initC.totalFold (fun c => P (cfg.forward c)) casesC x) =
          cfg.foldC (cfg.initD.totalAlg P casesD) x := by
      apply cfg.initC.fold_eta (cfg.initD.totalAlg P casesD)
        (fun c => liftSigma (cfg.initC.totalFold (fun z => P (cfg.forward z)) casesC c))
      intro ⟨a, k⟩
      dsimp only [InitPAlg.totalFold]
      rw [cfg.initC.fold_beta]
      dsimp only [InitPAlg.totalAlg, liftSigma, PolyF.map, casesC, pullbackCases]
      exact sigma_cast_symm P
        (cfg.constr_ok ⟨a, fun b => (cfg.initC.totalFold (fun z => P (cfg.forward z)) casesC (k b)).1⟩)
        (casesD a _ _)
    exact h₁.trans (cfg.repair_by_instantiation (cfg.initD.totalAlg P casesD) x)
  exact elim_eq_of_sigma_eq cfg.forward P hPair
    (cfg.initC.totalFold_fst (fun c => P (cfg.forward c)) casesC x)
    (cfg.initD.totalFold_fst P casesD (cfg.forward x))

/-- Transport `Prop`-valued dependent elimination across `AlgConfig`: in Lean 4, both proofs
    inhabit `P (cfg.forward x) : Prop` and agree unconditionally. -/
theorem elimProp_repair_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (P : D → Prop)
    (casesD : (a : A) → (k : B a → D) → ((b : B a) → P (k b)) → P (cfg.algD.op ⟨a, k⟩))
    (x : C) :
    cfg.initC.elimProp (fun c => P (cfg.forward c))
      (fun a k ih => (cfg.constr_ok ⟨a, k⟩).symm ▸ casesD a (fun b => cfg.forward (k b)) ih) x =
      cfg.initD.elimProp P casesD (cfg.forward x) :=
  Subsingleton.elim _ _

end AlgConfig

/-! ## 5. Concrete Scar-Free Case Study: `UnaryNat ↔ BinNat` (`1 + X`) -/

/-- Peano shape family `Bool`: `false` for `zero`, `true` for `succ`. -/
abbrev PeanoPos : Bool → Type
  | false => PEmpty
  | true => PUnit

/-- Build a Peano `PAlg Bool PeanoPos X` from `zeroVal : X` and `succFn : X → X`. -/
@[expose] def mkPeanoAlg {X : Type} (zeroVal : X) (succFn : X → X) : PAlg Bool PeanoPos X where
  op := fun
    | ⟨false, _⟩ => zeroVal
    | ⟨true, k⟩ => succFn (k PUnit.unit)

/-- Retired unary natural numbers (`zero | succ`). -/
inductive UnaryNat : Type where
  | zero : UnaryNat
  | succ : UnaryNat → UnaryNat
  deriving @[expose] DecidableEq, Repr

namespace UnaryNat

@[expose] def fold {Y : Type} (γ : PAlg Bool PeanoPos Y) : UnaryNat → Y
  | .zero => γ.op ⟨false, PEmpty.elim⟩
  | .succ n => γ.op ⟨true, fun _ => fold γ n⟩

@[expose] def initPAlg : InitPAlg Bool PeanoPos UnaryNat where
  alg := mkPeanoAlg .zero .succ
  fold := fold
  fold_beta γ t := by
    rcases t with ⟨b, k⟩
    cases b with
    | false =>
      change γ.op ⟨false, PEmpty.elim⟩ = γ.op ⟨false, fun e => fold γ (k e)⟩
      apply congrArg γ.op
      apply congrArg (Sigma.mk false)
      funext e
      cases e
    | true =>
      rfl
  fold_eta γ h hcomm x := by
    induction x with
    | zero =>
      have hz := hcomm ⟨false, PEmpty.elim⟩
      dsimp only [mkPeanoAlg, PolyF.map, fold] at hz ⊢
      rw [hz]
      apply congrArg γ.op
      apply congrArg (Sigma.mk false)
      funext e
      cases e
    | succ n ih =>
      have hs := hcomm ⟨true, fun _ => n⟩
      dsimp only [mkPeanoAlg, PolyF.map, fold] at hs ⊢
      rw [hs]
      apply congrArg γ.op
      apply congrArg (Sigma.mk true)
      funext u
      cases u
      exact ih

end UnaryNat

/-- Strictly positive binary numbers (`1 | 2p | 2p + 1`). -/
inductive BinPos : Type where
  | one : BinPos
  | bit0 : BinPos → BinPos
  | bit1 : BinPos → BinPos
  deriving @[expose] DecidableEq, Repr

/-- Binary natural numbers (`0 | pos p`). Built with zero dependency on `UnaryNat` so repaired
    `BinNat` definitions and proofs are 100% scar-free. -/
inductive BinNat : Type where
  | zero : BinNat
  | pos : BinPos → BinNat
  deriving @[expose] DecidableEq, Repr

namespace BinPos

@[expose] def succ : BinPos → BinPos
  | .one => .bit0 .one
  | .bit0 p => .bit1 p
  | .bit1 p => .bit0 p.succ

/-- Apply `s : Y → Y` exactly `p` times to `acc : Y` by structural recursion on `BinPos`. -/
@[expose] def iter {Y : Type} (s : Y → Y) : BinPos → Y → Y
  | .one, acc => s acc
  | .bit0 p, acc => iter s p (iter s p acc)
  | .bit1 p, acc => s (iter s p (iter s p acc))

theorem iter_comm_step {Y : Type} (s : Y → Y) (p : BinPos) (acc : Y) :
    iter s p (s acc) = s (iter s p acc) := by
  induction p generalizing acc with
  | one => rfl
  | bit0 q ih =>
    simp only [iter]
    rw [ih, ih]
  | bit1 q ih =>
    simp only [iter]
    rw [ih, ih]

theorem iter_succ {Y : Type} (s : Y → Y) (p : BinPos) (acc : Y) :
    iter s p.succ acc = s (iter s p acc) := by
  induction p generalizing acc with
  | one => rfl
  | bit0 q _ => rfl
  | bit1 q ih =>
    simp only [succ, iter]
    rw [ih, ih, iter_comm_step]

end BinPos

namespace BinNat

@[expose] def succ : BinNat → BinNat
  | .zero => .pos .one
  | .pos p => .pos p.succ

@[expose] def double : BinNat → BinNat
  | .zero => .zero
  | .pos p => .pos (.bit0 p)

theorem double_succ (b : BinNat) : b.succ.double = b.double.succ.succ := by
  cases b <;> rfl

theorem double_iter_succ (p : BinPos) (b : BinNat) :
    (BinPos.iter BinNat.succ p b).double =
      BinPos.iter BinNat.succ p (BinPos.iter BinNat.succ p b.double) := by
  induction p generalizing b with
  | one =>
    exact double_succ b
  | bit0 q ih =>
    simp only [BinPos.iter]
    rw [ih (BinPos.iter BinNat.succ q b), ih b]
  | bit1 q ih =>
    simp only [BinPos.iter]
    rw [double_succ, ih (BinPos.iter BinNat.succ q b), ih b,
        BinPos.iter_comm_step BinNat.succ q, BinPos.iter_comm_step BinNat.succ q]

theorem iter_succ_zero (p : BinPos) :
    BinPos.iter BinNat.succ p .zero = .pos p := by
  induction p with
  | one => rfl
  | bit0 q ih =>
    simp only [BinPos.iter]
    have hd := (double_iter_succ q .zero).symm
    dsimp only [double] at hd
    rw [hd, ih]
  | bit1 q ih =>
    simp only [BinPos.iter]
    have hd := (double_iter_succ q .zero).symm
    dsimp only [double] at hd
    rw [hd, ih]
    rfl

@[expose] def fold {Y : Type} (γ : PAlg Bool PeanoPos Y) : BinNat → Y
  | .zero => γ.op ⟨false, PEmpty.elim⟩
  | .pos p =>
      BinPos.iter (fun y => γ.op ⟨true, fun _ => y⟩) p (γ.op ⟨false, PEmpty.elim⟩)

theorem fold_succ {Y : Type} (γ : PAlg Bool PeanoPos Y) (b : BinNat) :
    fold γ b.succ = γ.op ⟨true, fun _ => fold γ b⟩ := by
  cases b with
  | zero => rfl
  | pos p =>
    exact BinPos.iter_succ (fun y => γ.op ⟨true, fun _ => y⟩) p (γ.op ⟨false, PEmpty.elim⟩)

private theorem iter_preserves_eq {Y : Type} (s : Y → Y) (h : BinNat → Y)
    (hs : ∀ b : BinNat, h b.succ = s (h b)) (p : BinPos) (b : BinNat) :
    h (BinPos.iter BinNat.succ p b) = BinPos.iter s p (h b) := by
  induction p generalizing b with
  | one => exact hs b
  | bit0 q ih =>
    simp only [BinPos.iter]
    rw [ih (BinPos.iter BinNat.succ q b), ih b]
  | bit1 q ih =>
    simp only [BinPos.iter]
    rw [hs, ih (BinPos.iter BinNat.succ q b), ih b]

/-- Homotopy-initial Peano `P`-algebra on `BinNat`, proved with zero reference to `UnaryNat` or `Nat`. -/
@[expose] def initPAlg : InitPAlg Bool PeanoPos BinNat where
  alg := mkPeanoAlg .zero .succ
  fold := fold
  fold_beta γ t := by
    rcases t with ⟨b, k⟩
    cases b with
    | false =>
      change γ.op ⟨false, PEmpty.elim⟩ = γ.op ⟨false, fun e => fold γ (k e)⟩
      apply congrArg γ.op
      apply congrArg (Sigma.mk false)
      funext e
      cases e
    | true =>
      exact fold_succ γ (k PUnit.unit)
  fold_eta γ h hcomm x := by
    have hz : h .zero = γ.op ⟨false, PEmpty.elim⟩ := by
      have h0 := hcomm ⟨false, PEmpty.elim⟩
      dsimp only [mkPeanoAlg, PolyF.map] at h0
      rw [h0]
      apply congrArg γ.op
      apply congrArg (Sigma.mk false)
      funext e
      cases e
    let stepY : _ → _ := fun y => γ.op ⟨true, fun _ => y⟩
    have hs : ∀ b : BinNat, h b.succ = stepY (h b) := by
      intro b
      have h1 := hcomm ⟨true, fun _ => b⟩
      dsimp only [mkPeanoAlg, PolyF.map, stepY] at h1 ⊢
      rw [h1]
    cases x with
    | zero => exact hz
    | pos p =>
      change h (.pos p) = BinPos.iter stepY p (γ.op ⟨false, PEmpty.elim⟩)
      rw [← iter_succ_zero p, iter_preserves_eq stepY h hs p .zero, hz]

end BinNat

/-- Canonical algebra configuration between `UnaryNat` and `BinNat`. -/
@[expose] def unaryBinConfig : AlgConfig Bool PeanoPos UnaryNat BinNat :=
  (UnaryNat.initPAlg, BinNat.initPAlg)

/-- Carrier-free `isZero` defining algebra. -/
@[expose] def peanoIsZeroAlg : PAlg Bool PeanoPos Bool :=
  mkPeanoAlg true (fun _ => false)

/-- Carrier-free Peano addition defined solely against an abstract `InitPAlg Bool PeanoPos X`. -/
@[expose] def peanoAdd {X : Type} (I : InitPAlg Bool PeanoPos X) (x y : X) : X :=
  I.fold (mkPeanoAlg y (fun acc => I.alg.op ⟨true, fun _ => acc⟩)) x

/-- Carrier-free proof of right zero identity `x + 0 = x` over any `InitPAlg Bool PeanoPos X`. -/
theorem peano_add_zero {X : Type} (I : InitPAlg Bool PeanoPos X) (x : X) :
    peanoAdd I x (I.alg.op ⟨false, PEmpty.elim⟩) = x := by
  let zeroX : X := I.alg.op ⟨false, PEmpty.elim⟩
  let addZeroAlg : PAlg Bool PeanoPos X := mkPeanoAlg zeroX (fun acc => I.alg.op ⟨true, fun _ => acc⟩)
  apply I.elimProp (fun c => I.fold addZeroAlg c = c)
  intro shape k ih
  cases shape with
  | false =>
    rw [I.fold_beta addZeroAlg ⟨false, k⟩]
    change I.alg.op ⟨false, PEmpty.elim⟩ = I.alg.op ⟨false, k⟩
    apply congrArg I.alg.op
    apply congrArg (Sigma.mk false)
    funext e
    cases e
  | true =>
    rw [I.fold_beta addZeroAlg ⟨true, k⟩]
    have ihUnit : I.fold addZeroAlg (k PUnit.unit) = k PUnit.unit := ih PUnit.unit
    change I.alg.op ⟨true, fun _ => I.fold addZeroAlg (k PUnit.unit)⟩ = I.alg.op ⟨true, k⟩
    rw [ihUnit]

/-- Source `UnaryNat` operations and theorem. -/
@[expose] def unaryIsZero : UnaryNat → Bool := UnaryNat.initPAlg.fold peanoIsZeroAlg
@[expose] def unaryAdd : UnaryNat → UnaryNat → UnaryNat := peanoAdd UnaryNat.initPAlg

theorem unary_add_zero (n : UnaryNat) : unaryAdd n .zero = n :=
  peano_add_zero UnaryNat.initPAlg n

/-- Scar-free repaired `BinNat` operations and theorem: instantiated directly at `BinNat.initPAlg`
    with zero dependency on `UnaryNat`. -/
@[expose] def binIsZero : BinNat → Bool := BinNat.initPAlg.fold peanoIsZeroAlg
@[expose] def binAdd : BinNat → BinNat → BinNat := peanoAdd BinNat.initPAlg

theorem bin_add_zero (b : BinNat) : binAdd b .zero = b :=
  peano_add_zero BinNat.initPAlg b

/-- Repair coherence between `unaryIsZero` and `binIsZero` via Proposition 3.15 (`repair_by_instantiation`). -/
theorem unary_bin_isZero_coherence (n : UnaryNat) :
    unaryIsZero n = binIsZero (unaryBinConfig.forward n) :=
  unaryBinConfig.repair_by_instantiation peanoIsZeroAlg n

/-- Repair coherence between `unaryAdd` and `binAdd` across `unaryBinConfig.forward`. -/
theorem unary_bin_add_coherence (m n : UnaryNat) :
    unaryBinConfig.forward (unaryAdd m n) =
      binAdd (unaryBinConfig.forward m) (unaryBinConfig.forward n) := by
  let zB := unaryBinConfig.forward n
  let stepAlgB : PAlg Bool PeanoPos BinNat := mkPeanoAlg zB BinNat.succ
  let stepAlgU : PAlg Bool PeanoPos UnaryNat := mkPeanoAlg n UnaryNat.succ
  have hLhs :
      unaryBinConfig.forward (UnaryNat.initPAlg.fold stepAlgU m) =
        UnaryNat.initPAlg.fold stepAlgB m := by
    apply UnaryNat.initPAlg.fold_eta stepAlgB (fun x => unaryBinConfig.forward (UnaryNat.initPAlg.fold stepAlgU x))
    intro ⟨shape, k⟩
    rw [UnaryNat.initPAlg.fold_beta]
    cases shape with
    | false =>
      dsimp only [stepAlgU, stepAlgB, mkPeanoAlg, PolyF.map, zB]
    | true =>
      dsimp only [stepAlgU, stepAlgB, mkPeanoAlg, PolyF.map]
      exact unaryBinConfig.constr_ok ⟨true, fun _ => UnaryNat.initPAlg.fold stepAlgU (k PUnit.unit)⟩
  exact hLhs.trans (unaryBinConfig.repair_by_instantiation stepAlgB m)

end Obend.Repair
end
