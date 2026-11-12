module
/-
# Obend.Repair.CoalgConfig — polynomial coalgebras, `paco` coinduction & scar-free coalgebraic repair

Lean 4 mechanization of Plante–Paul–Viola–Kavvos–Ringer (`arXiv:2610.36669v1` §4) fused with
Hur-et-al. parameterized coinduction (`paco` / `gpaco`):

- `PCoalg A B X`, `PCoalgHom`, and `Bisim A B γ R` (one-step `BisimStep` functor).
- Parameterized Coinduction (`paco` & `gpaco`):
  - `paco_mon`, `paco_unfold`, `paco_fold`, `paco_acc`, `paco_mult`, `paco_coind`, and
    `paco_bot_isBisim` (incremental bisimulation proofs without restarting the witness!).
- `FinalPCoalg A B C` (`corec`, `corec_out`, `corec_shape`, `corec_pos`, `corec_uniq`) with
  Rutten's span coinduction principle `FinalPCoalg.coind` and `FinalPCoalg.paco_eq` derived
  without cubical or univalence axioms.
- `CoalgConfig A B C D := FinalPCoalg A B C × FinalPCoalg A B D`:
  - Induced `CoalgEquiv A B C D` (`forward_backward`, `backward_forward`).
  - **Proposition 4.19 (`destr_ok`, `iota_ok`, `corec_ok`, and `coind_ok`)**: `coind_ok` holds
    unconditionally in Lean 4 via constructive bisimulation pushforward `pushRel_isBisim` and
    `Prop` proof irrelevance (`congrArg cfg.forward (coindC r) = coindD (pushRel_step r)`).
- Concrete scar-free case study: scalar stream `SeqStream α` (`Nat → α`) ↔ 2-wide packed SIMD word
  stream `Simd2Stream α` (`Nat → α × α`), repairing `consVia` and the stream decomposition proof
  `stream_eta_via` with zero dependency on `SeqStream`.
-/
public import Obend.Repair.AlgConfig
public section
namespace Obend.Repair
set_option autoImplicit false

universe u v w w₁ w₂

/-! ## 1. Polynomial Coalgebras (`PCoalg`), Homomorphisms & Bisimulations -/

/-- A coalgebra `X → PolyF A B X` for polynomial `(A, B)` on carrier `X`. -/
structure PCoalg (A : Type u) (B : A → Type v) (X : Type w) where
  out : X → PolyF A B X

namespace PCoalg

/-- Shape observation `X → A`. -/
@[expose] def shape {A : Type u} {B : A → Type v} {X : Type w} (γ : PCoalg A B X) (x : X) : A :=
  (γ.out x).1

/-- Position/transition observation `(x : X) → B (γ.shape x) → X`. -/
@[expose] def pos {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) (x : X) : B (γ.shape x) → X :=
  (γ.out x).2

theorem out_eq_mk {A : Type u} {B : A → Type v} {X : Type w} (γ : PCoalg A B X) (x : X) :
    γ.out x = ⟨γ.shape x, γ.pos x⟩ := by
  rcases h : γ.out x with ⟨a, k⟩
  dsimp only [shape, pos]
  rw [h]

end PCoalg

/-- Homomorphism between `PCoalg`s `(X, γ) → (Y, δ)`. -/
structure PCoalgHom {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    (γ : PCoalg A B X) (δ : PCoalg A B Y) where
  toFun : X → Y
  hom_comm : ∀ x : X, PolyF.map toFun (γ.out x) = δ.out (toFun x)

namespace PCoalgHom

theorem ext {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    {γ : PCoalg A B X} {δ : PCoalg A B Y} {f g : PCoalgHom γ δ}
    (h : ∀ x : X, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  have hfun : _ = _ := funext h
  subst hfun
  rfl

@[expose] def id {A : Type u} {B : A → Type v} {X : Type w} (γ : PCoalg A B X) : PCoalgHom γ γ where
  toFun x := x
  hom_comm x := PolyF.map_id (γ.out x)

@[expose] def comp {A : Type u} {B : A → Type v} {X : Type w} {Y : Type w₁} {Z : Type w₂}
    {γ : PCoalg A B X} {δ : PCoalg A B Y} {ε : PCoalg A B Z}
    (g : PCoalgHom δ ε) (f : PCoalgHom γ δ) : PCoalgHom γ ε where
  toFun x := g.toFun (f.toFun x)
  hom_comm x := by
    rw [← PolyF.map_comp, f.hom_comm, g.hom_comm]

theorem shape_comm {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    {γ : PCoalg A B X} {δ : PCoalg A B Y} (f : PCoalgHom γ δ) (x : X) :
    δ.shape (f.toFun x) = γ.shape x :=
  (congrArg Sigma.fst (f.hom_comm x)).symm

end PCoalgHom

/-- One-step polynomial bisimulation operator (Plante et al. Definition 4.9):
    `x` and `y` have equal shapes `hShape : γ.shape x = γ.shape y` and `R`-related child positions. -/
@[expose] def BisimStep {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) (R : X → X → Prop) (x y : X) : Prop :=
  ∃ hShape : γ.shape x = γ.shape y,
    ∀ b : B (γ.shape x), R (γ.pos x b) (γ.pos y (hShape ▸ b))

/-- `R` is a coalgebraic bisimulation on `(X, γ)` when `R ≤ BisimStep γ R`. -/
@[expose] def Bisim (A : Type u) (B : A → Type v) {X : Type w}
    (γ : PCoalg A B X) (R : X → X → Prop) : Prop :=
  ∀ {x y : X}, R x y → BisimStep γ R x y

theorem BisimStep.mono {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) {R S : X → X → Prop}
    (hRS : ∀ x y, R x y → S x y) {x y : X} (h : BisimStep γ R x y) :
    BisimStep γ S x y := by
  obtain ⟨hShape, hPos⟩ := h
  exact ⟨hShape, fun b => hRS _ _ (hPos b)⟩

/-! ## 2. Parameterized Coinduction (`paco` & `gpaco`) -/

/-- Inclusion ordering on binary relations `R ≤ S`. -/
@[expose] def RelLe {X : Type w} (R S : X → X → Prop) : Prop :=
  ∀ x y : X, R x y → S x y

/-- Pointwise union of binary relations `R ⊔ S`. -/
@[expose] def RelUnion {X : Type w} (R S : X → X → Prop) (x y : X) : Prop :=
  R x y ∨ S x y

/-- Empty binary relation `⊥`. -/
@[expose] def RelBot (X : Type w) : X → X → Prop :=
  fun _ _ => False

/-- A monotone binary-relation transformer on `X`. -/
structure MonoRel (X : Type w) where
  fn : (X → X → Prop) → (X → X → Prop)
  mono : ∀ {R S : X → X → Prop}, RelLe R S → RelLe (fn R) (fn S)

/-- Canonical `MonoRel` for `BisimStep γ`. -/
@[expose] def BisimStep.toMonoRel {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) : MonoRel X where
  fn := BisimStep γ
  mono hRS _ _ h := BisimStep.mono γ hRS h

/-- Parameterized greatest fixed point `paco F r := ν R. F (R ∪ r)` (Hur et al., POPL 2013). -/
@[expose] def paco {X : Type w} (F : MonoRel X) (r : X → X → Prop) (x y : X) : Prop :=
  ∃ R : X → X → Prop,
    (∀ u v : X, R u v → F.fn (RelUnion R r) u v) ∧ R x y

/-- Usable coinductive hypothesis `upaco F r := paco F r ∪ r`. -/
@[expose] def upaco {X : Type w} (F : MonoRel X) (r : X → X → Prop) : X → X → Prop :=
  RelUnion (paco F r) r

/-- Monotonicity of `paco` in its parameter `r`. -/
theorem paco_mon {X : Type w} (F : MonoRel X) {r s : X → X → Prop} (hrs : RelLe r s) :
    RelLe (paco F r) (paco F s) := by
  rintro x y ⟨R, hPost, hrxy⟩
  refine ⟨R, ?_, hrxy⟩
  intro u v hruv
  exact F.mono
    (fun a b h => match h with
      | .inl hR => .inl hR
      | .inr hr => .inr (hrs a b hr))
    u v (hPost u v hruv)

/-- **Coinduction Rule (`paco_coind`).** Any `R` post-fixed modulo `r` embeds into `paco F r`. -/
theorem paco_coind {X : Type w} (F : MonoRel X) {R r : X → X → Prop}
    (hPost : ∀ x y : X, R x y → F.fn (RelUnion R r) x y) :
    RelLe R (paco F r) :=
  fun _ _ hR => ⟨R, hPost, hR⟩

/-- Unfold `paco F r` one step into `F (upaco F r)`. -/
theorem paco_unfold {X : Type w} (F : MonoRel X) (r : X → X → Prop) :
    RelLe (paco F r) (F.fn (upaco F r)) := by
  rintro x y ⟨R, hPost, hR⟩
  exact F.mono
    (fun a b h => match h with
      | .inl ha => .inl ⟨R, hPost, ha⟩
      | .inr hb => .inr hb)
    x y (hPost x y hR)

/-- Fold `F (upaco F r)` into `paco F r`. -/
theorem paco_fold {X : Type w} (F : MonoRel X) (r : X → X → Prop) :
    RelLe (F.fn (upaco F r)) (paco F r) := by
  intro x y hf
  refine ⟨F.fn (upaco F r), ?_, hf⟩
  intro u v huv
  exact F.mono
    (fun a b h => match h with
      | .inl hp => .inl (paco_unfold F r a b hp)
      | .inr hr => .inr hr)
    u v huv

/-- **Accumulation / Mult Rule (`paco_mult`).** Facts proved in `paco F (upaco F r)` collapse
    back into `paco F r`, enabling incremental lemma-by-lemma coinductive proofs. -/
theorem paco_mult {X : Type w} (F : MonoRel X) (r : X → X → Prop) :
    RelLe (paco F (upaco F r)) (paco F r) := by
  rintro x y ⟨R, hPost, hR⟩
  refine ⟨RelUnion R (paco F r), ?_, .inl hR⟩
  intro u v huv
  cases huv with
  | inl hRu =>
    exact F.mono
      (fun a b h => match h with
        | .inl ha => .inl (.inl ha)
        | .inr (.inl hp) => .inl (.inr hp)
        | .inr (.inr hr) => .inr hr)
      u v (hPost u v hRu)
  | inr hPaco =>
    exact F.mono
      (fun a b h => match h with
        | .inl hp => .inl (.inr hp)
        | .inr hr => .inr hr)
      u v (paco_unfold F r u v hPaco)

/-- **Direct Accumulation (`paco_acc`).** `paco F (paco F r) ≤ paco F r`. -/
theorem paco_acc {X : Type w} (F : MonoRel X) (r : X → X → Prop) :
    RelLe (paco F (paco F r)) (paco F r) :=
  fun x y h =>
    paco_mult F r x y (paco_mon F (fun _ _ hp => .inl hp) x y h)

/-- Guarded parameterized coinduction (`gpaco F r g := paco F (r ∪ g) ∪ r`, CPP 2020). -/
@[expose] def gpaco {X : Type w} (F : MonoRel X) (r g : X → X → Prop) : X → X → Prop :=
  RelUnion (paco F (RelUnion r g)) r

/-- Unfolding `gpaco` releases the guarded hypothesis `g` into `upaco F (r ∪ g)`. -/
theorem gpaco_unfold {X : Type w} (F : MonoRel X) (r g : X → X → Prop) :
    RelLe (gpaco F r g) (RelUnion (F.fn (upaco F (RelUnion r g))) r) := by
  intro x y h
  cases h with
  | inl hp => exact .inl (paco_unfold F (RelUnion r g) x y hp)
  | inr hr => exact .inr hr

/-- At empty parameter `RelBot`, `paco (BisimStep.toMonoRel γ) RelBot` is a genuine `Bisim`. -/
theorem paco_bot_isBisim {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) :
    Bisim A B γ (paco (BisimStep.toMonoRel γ) (RelBot X)) := by
  intro x y hp
  have hunf := paco_unfold (BisimStep.toMonoRel γ) (RelBot X) x y hp
  exact BisimStep.mono γ
    (fun a b h => match h with
      | .inl hPaco => hPaco
      | .inr hBot => False.elim hBot)
    hunf

/-! ## 3. Final `P`-Coalgebras (`FinalPCoalg`) & Derived Coinduction -/

/-- Final `P`-coalgebra structure on carrier `C : Type w`: unique `corec` out of any `E : Type w`
    coalgebra with computation rule `corec_out` and uniqueness rule `corec_uniq`. -/
structure FinalPCoalg (A : Type u) (B : A → Type v) (C : Type w) where
  coalg : PCoalg A B C
  corec : ∀ {E : Type w}, PCoalg A B E → E → C
  corec_out : ∀ {E : Type w} (δ : PCoalg A B E) (e : E),
    coalg.out (corec δ e) = PolyF.map (corec δ) (δ.out e)
  corec_uniq : ∀ {E : Type w} (δ : PCoalg A B E) (h : E → C),
    (∀ e : E, coalg.out (h e) = PolyF.map h (δ.out e)) →
    ∀ e : E, h e = corec δ e

namespace FinalPCoalg

/-- Shape β-rule `β_s` (Plante et al. Figure 1). -/
theorem corec_shape {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) (e : E) :
    F.coalg.shape (F.corec δ e) = δ.shape e :=
  congrArg Sigma.fst (F.corec_out δ e)

private theorem polyF_snd_of_eq {A : Type u} {B : A → Type v} {E C : Type w}
    (f : E → C) {p : PolyF A B C} {q : PolyF A B E}
    (h : p = PolyF.map f q) (b : B p.1) :
    p.2 b = f (q.2 (congrArg Sigma.fst h ▸ b)) := by
  cases q with
  | mk a k =>
    cases p with
    | mk a' k' =>
      dsimp only [PolyF.map] at h
      injection h with ha hk
      subst ha
      have hkEq : k' = fun x => f (k x) := eq_of_heq hk
      dsimp only
      rw [hkEq]

private theorem polyF_mk_cast {A : Type u} {B : A → Type v} {C : Type w}
    (p q : PolyF A B C) (h : p.1 = q.1) :
    q = ⟨p.1, fun b => q.2 (h ▸ b)⟩ := by
  cases p with
  | mk ap _ =>
    cases q with
    | mk aq _ =>
      dsimp only at h
      subst h
      rfl

/-- Dependent position β-rule `β_p` over `corec_shape` (Plante et al. Figure 1). -/
theorem corec_pos {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) (e : E)
    (b : B (F.coalg.shape (F.corec δ e))) :
    F.coalg.pos (F.corec δ e) b = F.corec δ (δ.pos e (F.corec_shape δ e ▸ b)) :=
  polyF_snd_of_eq (F.corec δ) (F.corec_out δ e) b

/-- Canonical `PCoalgHom` into a final coalgebra. -/
@[expose] def corecHom {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) : PCoalgHom δ F.coalg where
  toFun := F.corec δ
  hom_comm e := (F.corec_out δ e).symm

theorem hom_unique {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) (f : PCoalgHom δ F.coalg) :
    f = F.corecHom δ :=
  PCoalgHom.ext (F.corec_uniq δ f.toFun (fun e => (f.hom_comm e).symm))

theorem corec_self {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) (c : C) :
    F.corec F.coalg c = c :=
  (F.corec_uniq F.coalg (fun x => x) (fun x => (PolyF.map_id (F.coalg.out x)).symm) c).symm

/-- **Rutten's Coinduction Principle (`coind`, Proposition 4.10).**
    Derived purely from `FinalPCoalg` via the span coalgebra `{ p : C × C // R p.1 p.2 }`
    without cubical path types or univalence! -/
theorem coind {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) (R : C → C → Prop)
    (hBisim : Bisim A B F.coalg R) {x y : C} (hxy : R x y) :
    x = y := by
  let Span := { p : C × C // R p.1 p.2 }
  let spanCoalg : PCoalg A B Span :=
    { out := fun ⟨⟨u, v⟩, huv⟩ =>
        let hStep := hBisim huv
        -- `Classical.choose` is NOT needed if we extract from `Prop`?! Wait: `Span` is in `Type w`,
        -- whereas `BisimStep` is `∃ hShape : shape u = shape v, ∀ b, R ...`!
        -- Notice `hShape : F.coalg.shape u = F.coalg.shape v` is an `Eq` in `Prop`, AND `R` is in `Prop`!!
        -- Wait: to project `hShape` out of `∃ hShape, ...` without `Classical.choice`, `∃` eliminates into `Prop`!
        -- Let's check! `F.coalg.shape u` IS ALREADY IN `Type u`, we DON'T choose `a : A`—the first field of
        -- `spanCoalg.out` IS `F.coalg.shape u`!! And inside the subtype `{ p : C × C // R p.1 p.2 }`,
        -- what is the second component of the pair `(pos u b, pos v (hShape ▸ b))`?!
        -- In Lean 4, `hShape : F.coalg.shape u = F.coalg.shape v` is `Prop` (proof-irrelevant!), so if we know
        -- `Nonempty (F.coalg.shape u = F.coalg.shape v)` (which is `F.coalg.shape u = F.coalg.shape v : Prop` itself!!),
        -- we can project `hStep.1 : F.coalg.shape u = F.coalg.shape v` DIRECTLY FROM A CONJUNCTION `∧` or `PSigma`
        -- with ZERO `Classical.choice`!
        ⟨F.coalg.shape u, fun b =>
          have hShape : F.coalg.shape u = F.coalg.shape v :=
            let ⟨hs, _⟩ := hStep; hs
          have hChild : R (F.coalg.pos u b) (F.coalg.pos v (hShape ▸ b)) :=
            let ⟨hs, hp⟩ := hStep
            have heq : hs = hShape := Subsingleton.elim hs hShape
            heq ▸ hp b
          ⟨(F.coalg.pos u b, F.coalg.pos v (hShape ▸ b)), hChild⟩⟩ }
  have hFst : ∀ s : Span, s.1.1 = F.corec spanCoalg s := by
    apply F.corec_uniq spanCoalg (fun s => s.1.1)
    rintro ⟨⟨u, v⟩, huv⟩
    exact F.coalg.out_eq_mk u
  have hSnd : ∀ s : Span, s.1.2 = F.corec spanCoalg s := by
    apply F.corec_uniq spanCoalg (fun s => s.1.2)
    rintro ⟨⟨u, v⟩, huv⟩
    have hShape : F.coalg.shape u = F.coalg.shape v :=
      let ⟨hs, _⟩ := hBisim huv; hs
    exact polyF_mk_cast (F.coalg.out u) (F.coalg.out v) hShape
  exact (hFst ⟨(x, y), hxy⟩).trans (hSnd ⟨(x, y), hxy⟩).symm

/-- `paco` equality corollary: any pair in `paco (BisimStep.toMonoRel F.coalg) RelBot` is equal. -/
theorem paco_eq {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) {x y : C}
    (hp : paco (BisimStep.toMonoRel F.coalg) (RelBot C) x y) :
    x = y :=
  F.coind _ (paco_bot_isBisim F.coalg) hp

end FinalPCoalg

/-! ## 4. Coalgebra Configurations (`CoalgConfig`) & Proposition 4.19 -/

/-- Explicit isomorphism of `P`-coalgebras on `C` and `D`. -/
structure CoalgEquiv (A : Type u) (B : A → Type v) (C D : Type w) where
  coalgC : PCoalg A B C
  coalgD : PCoalg A B D
  forwardHom : PCoalgHom coalgC coalgD
  backwardHom : PCoalgHom coalgD coalgC
  backward_forward : ∀ c : C, backwardHom.toFun (forwardHom.toFun c) = c
  forward_backward : ∀ d : D, forwardHom.toFun (backwardHom.toFun d) = d

/-- A coalgebra configuration between carriers `C` and `D` (Plante et al. Definition 4.12). -/
abbrev CoalgConfig (A : Type u) (B : A → Type v) (C D : Type w) :=
  FinalPCoalg A B C × FinalPCoalg A B D

namespace CoalgConfig

abbrev finalC {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : FinalPCoalg A B C :=
  cfg.1

abbrev finalD {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : FinalPCoalg A B D :=
  cfg.2

abbrev coalgC {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : PCoalg A B C :=
  cfg.1.coalg

abbrev coalgD {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : PCoalg A B D :=
  cfg.2.coalg

abbrev corecC {A : Type u} {B : A → Type v} {C D E : Type w}
    (cfg : CoalgConfig A B C D) (δ : PCoalg A B E) : E → C :=
  cfg.1.corec δ

abbrev corecD {A : Type u} {B : A → Type v} {C D E : Type w}
    (cfg : CoalgConfig A B C D) (δ : PCoalg A B E) : E → D :=
  cfg.2.corec δ

/-- Forward coalgebraic repair map `φ := corecD coalgC : C → D`. -/
@[expose] def forward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : C → D :=
  cfg.2.corec cfg.1.coalg

/-- Backward coalgebraic repair map `ψ := corecC coalgD : D → C`. -/
@[expose] def backward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : D → C :=
  cfg.1.corec cfg.2.coalg

/-- **Proposition 4.19(1) (`destr_ok`).** Destructors commute with `cfg.forward`. -/
theorem destr_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) :
    cfg.coalgD.out (cfg.forward c) = PolyF.map cfg.forward (cfg.coalgC.out c) :=
  cfg.2.corec_out cfg.1.coalg c

theorem destr_shape_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) :
    cfg.coalgD.shape (cfg.forward c) = cfg.coalgC.shape c :=
  cfg.2.corec_shape cfg.1.coalg c

/-- **Proposition 4.19(2) (`iota_ok`).** Corecursors compute under their respective destructors. -/
theorem iota_ok {A : Type u} {B : A → Type v} {C D E : Type w}
    (cfg : CoalgConfig A B C D) (δ : PCoalg A B E) (e : E) :
    cfg.coalgC.out (cfg.corecC δ e) = PolyF.map (cfg.corecC δ) (δ.out e) ∧
      cfg.coalgD.out (cfg.corecD δ e) = PolyF.map (cfg.corecD δ) (δ.out e) :=
  ⟨cfg.1.corec_out δ e, cfg.2.corec_out δ e⟩

/-- **Proposition 4.19(3) (`corec_ok`).** Dual of `repair_by_instantiation`: corecursing into `C`
    followed by `cfg.forward` equals corecursing the same seed coalgebra `δ` directly into `D`. -/
theorem corec_ok {A : Type u} {B : A → Type v} {C D E : Type w}
    (cfg : CoalgConfig A B C D) (δ : PCoalg A B E) (e : E) :
    cfg.forward (cfg.corecC δ e) = cfg.corecD δ e := by
  apply cfg.2.corec_uniq δ (fun x => cfg.forward (cfg.corecC δ x))
  intro x
  change cfg.coalgD.out (cfg.forward (cfg.corecC δ x)) =
    PolyF.map (fun x => cfg.forward (cfg.corecC δ x)) (δ.out x)
  rw [cfg.destr_ok]
  dsimp only [coalgC, corecC]
  rw [cfg.1.corec_out, PolyF.map_comp]

theorem backward_forward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) :
    cfg.backward (cfg.forward c) = c := by
  let symCfg : CoalgConfig A B D C := (cfg.2, cfg.1)
  exact (symCfg.corec_ok cfg.1.coalg c).trans (cfg.1.corec_self c)

theorem forward_backward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (d : D) :
    cfg.forward (cfg.backward d) = d :=
  (cfg.corec_ok cfg.2.coalg d).trans (cfg.2.corec_self d)

@[expose] def toCoalgEquiv {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) : CoalgEquiv A B C D where
  coalgC := cfg.coalgC
  coalgD := cfg.coalgD
  forwardHom := cfg.2.corecHom cfg.1.coalg
  backwardHom := cfg.1.corecHom cfg.2.coalg
  backward_forward := cfg.backward_forward
  forward_backward := cfg.forward_backward

/-- Pushforward relation `φ_* R` on `D` induced by a relation `R` on `C`. -/
@[expose] def pushRel {C D : Type w} (φ : C → D) (R : C → C → Prop) (d₁ d₂ : D) : Prop :=
  ∃ c₁ c₂ : C, φ c₁ = d₁ ∧ φ c₂ = d₂ ∧ R c₁ c₂

theorem pushRel_step {C D : Type w} (φ : C → D) (R : C → C → Prop) {x y : C} (r : R x y) :
    pushRel φ R (φ x) (φ y) :=
  ⟨x, y, rfl, rfl, r⟩

private theorem cast_trans_eq {A : Type u} {B : A → Type v}
    {a₁ a₂ a₃ a₄ : A} (h₁₂ : a₁ = a₂) (h₂₄ : a₂ = a₄) (h₁₃ : a₁ = a₃) (h₃₄ : a₃ = a₄)
    (b : B a₁) :
    h₃₄ ▸ (h₁₃ ▸ b) = h₂₄ ▸ (h₁₂ ▸ b) := by
  subst h₁₂
  subst h₂₄
  subst h₁₃
  have h : h₃₄ = rfl := Subsingleton.elim _ _
  rw [h]

/-- Constructive transport of a `C`-bisimulation to a `D`-bisimulation along `cfg.forward`. -/
theorem pushRel_isBisim {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (R : C → C → Prop) (hB : Bisim A B cfg.coalgC R) :
    Bisim A B cfg.coalgD (pushRel cfg.forward R) := by
  rintro d₁ d₂ ⟨c₁, c₂, rfl, rfl, hrc⟩
  obtain ⟨hShapeC, hPosC⟩ := hB hrc
  have hs₁ := cfg.destr_shape_ok c₁
  have hs₂ := cfg.destr_shape_ok c₂
  have hShapeD : cfg.coalgD.shape (cfg.forward c₁) = cfg.coalgD.shape (cfg.forward c₂) :=
    hs₁.trans (hShapeC.trans hs₂.symm)
  refine ⟨hShapeD, fun b => ?_⟩
  let b₁ : B (cfg.coalgC.shape c₁) := hs₁ ▸ b
  have hp₁ : cfg.coalgD.pos (cfg.forward c₁) b = cfg.forward (cfg.coalgC.pos c₁ b₁) :=
    cfg.2.corec_pos cfg.1.coalg c₁ b
  have hp₂ :
      cfg.coalgD.pos (cfg.forward c₂) (hShapeD ▸ b) =
        cfg.forward (cfg.coalgC.pos c₂ (hs₂ ▸ (hShapeD ▸ b))) :=
    cfg.2.corec_pos cfg.1.coalg c₂ (hShapeD ▸ b)
  have hbEq : (hs₂ ▸ (hShapeD ▸ b)) = (hShapeC ▸ b₁) :=
    cast_trans_eq hs₁ hShapeC hShapeD hs₂ b
  refine ⟨cfg.coalgC.pos c₁ b₁, cfg.coalgC.pos c₂ (hShapeC ▸ b₁), hp₁.symm, ?_, hPosC b₁⟩
  rw [hp₂, hbEq]

/-- **Proposition 4.19(4) (`coind_ok`).**
    Coinduction on `C` pushed along `cfg.forward` equals coinduction on `D` applied to the
    transported `D`-bisimulation `pushRel cfg.forward R`—holding unconditionally in Lean 4! -/
theorem coind_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (R : C → C → Prop) (hB : Bisim A B cfg.coalgC R)
    {x y : C} (r : R x y) :
    congrArg cfg.forward (cfg.1.coind R hB r) =
      cfg.2.coind (pushRel cfg.forward R) (cfg.pushRel_isBisim R hB) (pushRel_step cfg.forward R r) :=
  Subsingleton.elim _ _

end CoalgConfig

/-! ## 5. Concrete Scar-Free Case Study: `SeqStream α ↔ Simd2Stream α` -/

/-- Stream polynomial position family (`B _ = PUnit`). -/
abbrev StreamPos {α : Type u} : α → Type
  | _ => PUnit

/-- Retired scalar stream `Nat → α`. -/
structure SeqStream (α : Type u) where
  atStep : Nat → α

namespace SeqStream

@[expose] def hd {α : Type u} (s : SeqStream α) : α := s.atStep 0
@[expose] def tl {α : Type u} (s : SeqStream α) : SeqStream α := ⟨fun n => s.atStep (n + 1)⟩

@[expose] def coalg (α : Type u) : PCoalg α StreamPos (SeqStream α) where
  out s := ⟨s.hd, fun _ => s.tl⟩

@[expose] def iterStep {α : Type u} {E : Type u} (δ : PCoalg α StreamPos E) : Nat → E → E
  | 0, e => e
  | n + 1, e => iterStep δ n (δ.pos e PUnit.unit)

@[expose] def corec {α : Type u} {E : Type u} (δ : PCoalg α StreamPos E) (e : E) : SeqStream α where
  atStep n := δ.shape (iterStep δ n e)

private theorem iterStep_succ_right {α : Type u} {E : Type u}
    (δ : PCoalg α StreamPos E) (n : Nat) (e : E) :
    iterStep δ (n + 1) e = iterStep δ n (δ.pos e PUnit.unit) := rfl

@[expose] def finalPCoalg (α : Type u) : FinalPCoalg α StreamPos (SeqStream α) where
  coalg := coalg α
  corec := corec
  corec_out δ e := by
    dsimp only [coalg, PolyF.map, hd, tl, corec]
    rfl
  corec_uniq {E} δ h hcomm e := by
    have hAt : ∀ (n : Nat) (x : E), (h x).atStep n = δ.shape (iterStep δ n x) := by
      intro n
      induction n with
      | zero =>
        intro x
        exact congrArg Sigma.fst (hcomm x)
      | succ k ih =>
        intro x
        have hc := hcomm x
        dsimp only [coalg, PolyF.map, hd, tl] at hc
        injection hc with _ hk
        have htl : (fun n => (h x).atStep (n + 1)) = (h (δ.pos x PUnit.unit)).atStep := by
          have hseq : SeqStream.mk (fun n => (h x).atStep (n + 1)) = h (δ.pos x PUnit.unit) :=
            congrFun hk PUnit.unit
          exact congrArg SeqStream.atStep hseq
        exact (congrFun htl k).trans (ih (δ.pos x PUnit.unit))
    cases he : h e with
    | mk fn =>
      apply congrArg SeqStream.mk
      funext n
      have hn := hAt n e
      rw [he] at hn
      exact hn

end SeqStream

/-- Target 2-wide SIMD word stream storing `(s_{2k}, s_{2k+1})` per lane with zero reference to `SeqStream`. -/
structure Simd2Stream (α : Type u) where
  wordAt : Nat → α × α

namespace Simd2Stream

@[expose] def hd {α : Type u} (w : Simd2Stream α) : α :=
  (w.wordAt 0).1

@[expose] def tl {α : Type u} (w : Simd2Stream α) : Simd2Stream α where
  wordAt k := ((w.wordAt k).2, (w.wordAt (k + 1)).1)

@[expose] def coalg (α : Type u) : PCoalg α StreamPos (Simd2Stream α) where
  out w := ⟨w.hd, fun _ => w.tl⟩

@[expose] def stepN {α : Type u} {E : Type u} (δ : PCoalg α StreamPos E) : Nat → E → E
  | 0, e => e
  | n + 1, e => stepN δ n (δ.pos e PUnit.unit)

@[expose] def corec {α : Type u} {E : Type u} (δ : PCoalg α StreamPos E) (e : E) : Simd2Stream α where
  wordAt k :=
    (δ.shape (stepN δ (2 * k) e), δ.shape (stepN δ (2 * k + 1) e))

@[expose] def finalPCoalg (α : Type u) : FinalPCoalg α StreamPos (Simd2Stream α) where
  coalg := coalg α
  corec := corec
  corec_out _ _ := rfl
  corec_uniq {E} δ h hcomm e := by
    have hHd : ∀ x : E, (h x).wordAt 0 = (δ.shape x, (h (δ.pos x PUnit.unit)).hd) := by
      intro x
      have hc := hcomm x
      dsimp only [coalg, PolyF.map, hd, tl] at hc
      injection hc with hfst hk
      have htl : Simd2Stream.mk (fun k => (((h x).wordAt k).2, ((h x).wordAt (k + 1)).1)) =
          h (δ.pos x PUnit.unit) :=
        congrFun hk PUnit.unit
      have h0 : ((h x).wordAt 0).2 = ((h (δ.pos x PUnit.unit)).wordAt 0).1 :=
        congrArg (fun s => (s.wordAt 0).1) htl
      cases hw0 : (h x).wordAt 0 with
      | mk a₀ a₁ =>
        rw [hw0] at hfst h0
        dsimp only at hfst h0
        rw [hfst, h0]
        rfl
    have hShift : ∀ (k : Nat) (x : E),
        (h x).wordAt (k + 1) =
          (((h (δ.pos x PUnit.unit)).wordAt k).2, ((h (δ.pos x PUnit.unit)).wordAt (k + 1)).1) := by
      intro k x
      have hc := hcomm x
      dsimp only [coalg, PolyF.map, hd, tl] at hc
      injection hc with _ hk
      have htl : Simd2Stream.mk (fun j => (((h x).wordAt j).2, ((h x).wordAt (j + 1)).1)) =
          h (δ.pos x PUnit.unit) :=
        congrFun hk PUnit.unit
      have hj₀ : ((h x).wordAt (k + 1)).1 = ((h (δ.pos x PUnit.unit)).wordAt k).2 :=
        congrArg (fun s => (s.wordAt k).2) htl
      have hj₁ : ((h x).wordAt (k + 1)).2 = ((h (δ.pos x PUnit.unit)).wordAt (k + 1)).1 :=
        congrArg (fun s => (s.wordAt (k + 1)).1) htl
      cases hwk : (h x).wordAt (k + 1) with
      | mk b₀ b₁ =>
        rw [hwk] at hj₀ hj₁
        dsimp only at hj₀ hj₁
        rw [hj₀, hj₁]
    have hWord : ∀ (k : Nat) (x : E),
        (h x).wordAt k = (δ.shape (stepN δ (2 * k) x), δ.shape (stepN δ (2 * k + 1) x)) := by
      intro k
      induction k with
      | zero =>
        intro x
        rw [hHd x]
        have hNext := congrArg Prod.fst (hHd (δ.pos x PUnit.unit))
        dsimp only [hd] at hNext ⊢
        rw [hNext]
        rfl
      | succ j ih =>
        intro x
        let x₁ := δ.pos x PUnit.unit
        let x₂ := δ.pos x₁ PUnit.unit
        have hx₁ := hShift j x
        have hx₂ := hShift j x₁
        have hFst : ((h x₁).wordAt j).2 = δ.shape (stepN δ (2 * j + 1) x₁) :=
          congrArg Prod.snd (ih x₁)
        have hSnd : ((h x₁).wordAt (j + 1)).1 = ((h x₂).wordAt j).2 :=
          congrArg Prod.fst hx₂
        have hSnd' : ((h x₂).wordAt j).2 = δ.shape (stepN δ (2 * j + 1) x₂) :=
          congrArg Prod.snd (ih x₂)
        have e₁ : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
        rw [hx₁, hFst, hSnd, hSnd', e₁]
        rfl
    cases he : h e with
    | mk fn =>
      apply congrArg Simd2Stream.mk
      funext k
      have hk := hWord k e
      rw [he] at hk
      exact hk

end Simd2Stream

/-- Coalgebra configuration between scalar `SeqStream α` and 2-wide `Simd2Stream α`. -/
@[expose] def seqSimd2StreamConfig (α : Type u) : CoalgConfig α StreamPos (SeqStream α) (Simd2Stream α) :=
  (SeqStream.finalPCoalg α, Simd2Stream.finalPCoalg α)

/-- Carrier-free stream `cons` seed coalgebra over `Sum (α × S) S` (Plante et al. Example 4.13). -/
@[expose] def streamConsSeed {α : Type u} {S : Type u} (coalgS : PCoalg α StreamPos S) :
    PCoalg α StreamPos (Sum (α × S) S) where
  out
    | .inl (a, s) => ⟨a, fun _ => .inr s⟩
    | .inr s => ⟨coalgS.shape s, fun b => .inr (coalgS.pos s b)⟩

/-- Carrier-free `consVia` defined purely against an abstract `FinalPCoalg α StreamPos S`. -/
@[expose] def streamConsVia {α : Type u} {S : Type u} (F : FinalPCoalg α StreamPos S) (a : α) (s : S) : S :=
  F.corec (streamConsSeed F.coalg) (.inl (a, s))

/-- Carrier-free coinductive decomposition theorem `cons (shape s) (pos s ()) = s` proved once via
    `paco` and `FinalPCoalg.paco_eq`! -/
theorem stream_eta_via {α : Type u} {S : Type u} (F : FinalPCoalg α StreamPos S) (s : S) :
    streamConsVia F (F.coalg.shape s) (F.coalg.pos s PUnit.unit) = s := by
  let seed := streamConsSeed F.coalg
  have hTail : ∀ t : S, F.corec seed (.inr t) = t := by
    intro t
    have hCorec : F.corec seed (.inr t) = F.corec F.coalg t := by
      apply F.corec_uniq F.coalg (fun z => F.corec seed (.inr z)) ?_ t
      intro z
      rw [F.corec_out seed (.inr z), F.coalg.out_eq_mk z]
      rfl
    exact hCorec.trans (F.corec_self t)
  apply F.paco_eq
  let R : S → S → Prop := fun x y =>
    (x = streamConsVia F (F.coalg.shape y) (F.coalg.pos y PUnit.unit)) ∨ x = y
  apply paco_coind (BisimStep.toMonoRel F.coalg) (R := R) ?_ _ _ (.inl rfl)
  intro u v huv
  cases huv with
  | inl hCons =>
    subst hCons
    have hs : F.coalg.shape (streamConsVia F (F.coalg.shape v) (F.coalg.pos v PUnit.unit)) =
        F.coalg.shape v :=
      F.corec_shape seed (.inl (F.coalg.shape v, F.coalg.pos v PUnit.unit))
    refine ⟨hs, fun b => .inl (.inr ?_)⟩
    cases b
    have hp := F.corec_pos seed (.inl (F.coalg.shape v, F.coalg.pos v PUnit.unit)) PUnit.unit
    dsimp only [streamConsVia]
    rw [hp]
    exact hTail (F.coalg.pos v PUnit.unit)
  | inr hEq =>
    subst hEq
    exact ⟨rfl, fun b => .inl (.inr rfl)⟩

/-- Scar-free repaired `Simd2Stream` `cons` and decomposition proof—zero mention of `SeqStream`! -/
@[expose] def simd2Cons {α : Type u} : α → Simd2Stream α → Simd2Stream α :=
  streamConsVia (Simd2Stream.finalPCoalg α)

theorem simd2_eta {α : Type u} (w : Simd2Stream α) :
    simd2Cons w.hd w.tl = w :=
  stream_eta_via (Simd2Stream.finalPCoalg α) w

end Obend.Repair
end
