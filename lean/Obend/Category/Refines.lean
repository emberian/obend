module
/-
# Obend.Category.Refines — quantitative forward/stutter simulation and Galois refinement

Compositional refinement infrastructure parameterized over an ordered additive grade monoid
`GradeMonoid ε`:

- `GradeMonoid ε`: ordered commutative additive monoid instantiated for `Unit` (exact zero-slack
  refinement), `Nat` (step/cycle slack), `Int` (signed drift/exergy slack), `RatSlack` (exact
  rational bounds `num / (denPred + 1)`), and product grades `ε₁ × ε₂`.
- `ObsMetric V ε`: `GradeMonoid`-valued Lawvere hemimetric on observable outputs `V`, closed under
  cartesian products `V₁ × V₂`.
- `StepSystem S Act V`: relational transition coalgebra with observable readout `observe : S → V`.
- `Simulates C A R δ`: quantitative forward simulation bounding observation defect by `δ : ε` and
  preserving labeled transitions, with compositional combinators `Simulates.refl`,
  `Simulates.trans` (errors add `δ₁ + δ₂`), `Simulates.prod` (lockstep product),
  `Simulates.indepProd` (interleaved sum-action product), and `Simulates.trace_safety`
  (arbitrary-length trace invariant & quantitative error pullback).
- `StutterSimulates C A R K δ`: bounded `1 ≤ k ≤ K` stutter simulation closed under reflexivity,
  single-step lifting, and transitive composition (`K₁ * K₂` horizon, `δ₁ + δ₂` defect).
- `GaloisRefinement`: monotone Galois connection `α ⊣ γ` between concrete and abstract state
  predicates induced canonically by any simulation relation `R`.
-/
public section
namespace Obend.Category
set_option autoImplicit false

universe u v w u₁ u₂ v₁ v₂

/-! ## 1. Ordered Additive Grade Monoids -/

/-- An ordered commutative additive monoid of refinement defects or resource grades.
    Does not assume `0 ≤ a` so signed quantities (such as `Int` exergy) are admitted alongside
    non-negative slack grades (`Unit`, `Nat`, `RatSlack`). -/
class GradeMonoid (ε : Type u) extends Zero ε, Add ε, LE ε where
  add_zero : ∀ a : ε, a + 0 = a
  zero_add : ∀ a : ε, 0 + a = a
  add_assoc : ∀ a b c : ε, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : ε, a + b = b + a
  le_refl : ∀ a : ε, a ≤ a
  le_trans : ∀ {a b c : ε}, a ≤ b → b ≤ c → a ≤ c
  add_mono : ∀ {a₁ a₂ b₁ b₂ : ε}, a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + b₁ ≤ a₂ + b₂

namespace GradeMonoid

/-- Scalar `N`-fold grade accumulation (`N • g`), matching right-nested sequential loops. -/
@[expose] def nsmul {ε : Type u} [GradeMonoid ε] : Nat → ε → ε
  | 0, _ => 0
  | n + 1, g => g + nsmul n g

@[simp] theorem nsmul_zero {ε : Type u} [GradeMonoid ε] (g : ε) :
    nsmul 0 g = (0 : ε) := rfl

@[simp] theorem nsmul_succ {ε : Type u} [GradeMonoid ε] (n : Nat) (g : ε) :
    nsmul (n + 1) g = g + nsmul n g := rfl

theorem nsmul_one {ε : Type u} [GradeMonoid ε] (g : ε) :
    nsmul 1 g = g := by
  simp [nsmul, GradeMonoid.add_zero]

theorem nsmul_add {ε : Type u} [GradeMonoid ε] (m n : Nat) (g : ε) :
    nsmul (m + n) g = nsmul m g + nsmul n g := by
  induction m with
  | zero => simp [GradeMonoid.zero_add]
  | succ m ih =>
    rw [Nat.succ_add, nsmul_succ, nsmul_succ, ih, GradeMonoid.add_assoc]

theorem nsmul_mono {ε : Type u} [GradeMonoid ε] (n : Nat) {g₁ g₂ : ε} (h : g₁ ≤ g₂) :
    nsmul n g₁ ≤ nsmul n g₂ := by
  induction n with
  | zero => exact GradeMonoid.le_refl 0
  | succ k ih => exact GradeMonoid.add_mono h ih

end GradeMonoid

instance : Zero Unit where
  zero := ()

instance : Add Unit where
  add _ _ := ()

instance instGradeMonoidUnit : GradeMonoid Unit where
  le _ _ := True
  add_zero _ := rfl
  zero_add _ := rfl
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  le_refl _ := trivial
  le_trans _ _ := trivial
  add_mono _ _ := trivial

instance instGradeMonoidNat : GradeMonoid Nat where
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  le_refl := Nat.le_refl
  le_trans h₁ h₂ := Nat.le_trans h₁ h₂
  add_mono h₁ h₂ := Nat.add_le_add h₁ h₂

instance instGradeMonoidInt : GradeMonoid Int where
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  le_refl := Int.le_refl
  le_trans h₁ h₂ := Int.le_trans h₁ h₂
  add_mono h₁ h₂ := Int.add_le_add h₁ h₂

instance instGradeMonoidProd {ε₁ : Type u₁} {ε₂ : Type u₂}
    [GradeMonoid ε₁] [GradeMonoid ε₂] : GradeMonoid (ε₁ × ε₂) where
  zero := (0, 0)
  add x y := (x.1 + y.1, x.2 + y.2)
  le x y := x.1 ≤ y.1 ∧ x.2 ≤ y.2
  add_zero x := Prod.ext (GradeMonoid.add_zero x.1) (GradeMonoid.add_zero x.2)
  zero_add x := Prod.ext (GradeMonoid.zero_add x.1) (GradeMonoid.zero_add x.2)
  add_assoc x y z := Prod.ext (GradeMonoid.add_assoc x.1 y.1 z.1) (GradeMonoid.add_assoc x.2 y.2 z.2)
  add_comm x y := Prod.ext (GradeMonoid.add_comm x.1 y.1) (GradeMonoid.add_comm x.2 y.2)
  le_refl x := ⟨GradeMonoid.le_refl x.1, GradeMonoid.le_refl x.2⟩
  le_trans h₁ h₂ := ⟨GradeMonoid.le_trans h₁.1 h₂.1, GradeMonoid.le_trans h₁.2 h₂.2⟩
  add_mono h₁ h₂ := ⟨GradeMonoid.add_mono h₁.1 h₂.1, GradeMonoid.add_mono h₁.2 h₂.2⟩

/-- Exact rational slack bound representing `num / (denPred + 1)` with strictly positive
    denominator `denPred + 1`. Unreduced cross-multiplication makes `+` strictly associative
    and commutative on the nose without quotient axioms. -/
structure RatSlack where
  num : Int
  denPred : Nat
  deriving @[expose] DecidableEq, Repr

namespace RatSlack

/-- Strictly positive integer denominator `denPred + 1`. -/
@[expose] def denInt (q : RatSlack) : Int :=
  ((q.denPred + 1 : Nat) : Int)

theorem denInt_pos (q : RatSlack) : 0 < q.denInt := by
  unfold denInt
  omega

instance : Zero RatSlack where
  zero := ⟨0, 0⟩

instance : Add RatSlack where
  add a b :=
    { num := a.num * b.denInt + b.num * a.denInt
      denPred := (a.denPred + 1) * (b.denPred + 1) - 1 }

instance : LE RatSlack where
  le a b := a.num * b.denInt ≤ b.num * a.denInt

instance (a b : RatSlack) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.num * b.denInt ≤ b.num * a.denInt))

theorem add_denInt (a b : RatSlack) : (a + b).denInt = a.denInt * b.denInt := by
  change (((a.denPred + 1) * (b.denPred + 1) - 1 + 1 : Nat) : Int) =
    ((a.denPred + 1 : Nat) : Int) * ((b.denPred + 1 : Nat) : Int)
  have hpos : 1 ≤ (a.denPred + 1) * (b.denPred + 1) :=
    Nat.mul_le_mul (Nat.succ_pos a.denPred) (Nat.succ_pos b.denPred)
  rw [Nat.sub_add_cancel hpos, Int.natCast_mul]

private theorem int_ring_add_assoc (na nb nc da db dc : Int) :
    (na * db + nb * da) * dc + nc * (da * db) =
      na * (db * dc) + (nb * dc + nc * db) * da := by
  rw [Int.add_mul, Int.add_mul, Int.mul_assoc na db dc]
  have e₁ : nb * da * dc = nb * dc * da := by
    rw [Int.mul_assoc, Int.mul_comm da dc, ← Int.mul_assoc]
  have e₂ : nc * (da * db) = nc * db * da := by
    rw [Int.mul_comm da db, ← Int.mul_assoc]
  rw [e₁, e₂, Int.add_assoc]

private theorem int_ring_lhs_mono (na₁ nb₁ da₁ db₁ da₂ db₂ : Int) :
    (na₁ * db₁ + nb₁ * da₁) * (da₂ * db₂) =
      na₁ * da₂ * (db₁ * db₂) + nb₁ * db₂ * (da₁ * da₂) := by
  rw [Int.add_mul]
  congr 1
  · rw [Int.mul_assoc, ← Int.mul_assoc db₁ da₂ db₂, Int.mul_comm db₁ da₂,
        Int.mul_assoc, ← Int.mul_assoc]
  · rw [Int.mul_assoc, ← Int.mul_assoc da₁ da₂ db₂, Int.mul_comm (da₁ * da₂) db₂,
        ← Int.mul_assoc]

private theorem int_ring_rhs_mono (na₂ nb₂ da₁ db₁ da₂ db₂ : Int) :
    (na₂ * db₂ + nb₂ * da₂) * (da₁ * db₁) =
      na₂ * da₁ * (db₁ * db₂) + nb₂ * db₁ * (da₁ * da₂) := by
  rw [Int.add_mul]
  congr 1
  · rw [Int.mul_assoc, ← Int.mul_assoc db₂ da₁ db₁, Int.mul_comm db₂ da₁,
        Int.mul_assoc da₁ db₂ db₁, Int.mul_comm db₂ db₁, ← Int.mul_assoc]
  · rw [Int.mul_assoc, ← Int.mul_assoc da₂ da₁ db₁, Int.mul_comm da₂ da₁,
        Int.mul_comm (da₁ * da₂) db₁, ← Int.mul_assoc]

instance instGradeMonoid : GradeMonoid RatSlack where
  add_zero a := by
    cases a with
    | mk n d =>
      have hn : n * (0 : RatSlack).denInt + 0 * (⟨n, d⟩ : RatSlack).denInt = n := by
        change n * 1 + 0 * ((d + 1 : Nat) : Int) = n
        omega
      have hd : (d + 1) * (0 + 1) - 1 = d := by omega
      change RatSlack.mk (n * (0 : RatSlack).denInt + 0 * (⟨n, d⟩ : RatSlack).denInt)
        ((d + 1) * (0 + 1) - 1) = RatSlack.mk n d
      rw [hn, hd]
  zero_add a := by
    cases a with
    | mk n d =>
      have hn : 0 * (⟨n, d⟩ : RatSlack).denInt + n * (0 : RatSlack).denInt = n := by
        change 0 * ((d + 1 : Nat) : Int) + n * 1 = n
        omega
      have hd : (0 + 1) * (d + 1) - 1 = d := by omega
      change RatSlack.mk (0 * (⟨n, d⟩ : RatSlack).denInt + n * (0 : RatSlack).denInt)
        ((0 + 1) * (d + 1) - 1) = RatSlack.mk n d
      rw [hn, hd]
  add_assoc a b c := by
    have hd : ((a + b) + c).denPred = (a + (b + c)).denPred := by
      have h1 : 1 ≤ (a.denPred + 1) * (b.denPred + 1) :=
        Nat.mul_le_mul (Nat.succ_pos _) (Nat.succ_pos _)
      have h2 : 1 ≤ (b.denPred + 1) * (c.denPred + 1) :=
        Nat.mul_le_mul (Nat.succ_pos _) (Nat.succ_pos _)
      change (((a.denPred + 1) * (b.denPred + 1) - 1 + 1) * (c.denPred + 1) - 1) =
        ((a.denPred + 1) * ((b.denPred + 1) * (c.denPred + 1) - 1 + 1) - 1)
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, Nat.mul_assoc]
    have hn : ((a + b) + c).num = (a + (b + c)).num := by
      change (a + b).num * c.denInt + c.num * (a + b).denInt =
        a.num * (b + c).denInt + (b + c).num * a.denInt
      rw [add_denInt, add_denInt]
      exact int_ring_add_assoc a.num b.num c.num a.denInt b.denInt c.denInt
    cases h_lhs : (a + b) + c
    cases h_rhs : a + (b + c)
    rw [h_lhs, h_rhs] at hd hn
    cases hd
    cases hn
    rfl
  add_comm a b := by
    have hd : (a + b).denPred = (b + a).denPred := by
      change (a.denPred + 1) * (b.denPred + 1) - 1 = (b.denPred + 1) * (a.denPred + 1) - 1
      rw [Nat.mul_comm]
    have hn : (a + b).num = (b + a).num := by
      change a.num * b.denInt + b.num * a.denInt = b.num * a.denInt + a.num * b.denInt
      rw [Int.add_comm]
    cases h_lhs : a + b
    cases h_rhs : b + a
    rw [h_lhs, h_rhs] at hd hn
    cases hd
    cases hn
    rfl
  le_refl a := Int.le_refl (a.num * a.denInt)
  le_trans {a b c} hab hbc := by
    change a.num * c.denInt ≤ c.num * a.denInt
    have hbpos : 0 < b.denInt := denInt_pos b
    have hcpos : 0 ≤ c.denInt := Int.le_of_lt (denInt_pos c)
    have hapos : 0 ≤ a.denInt := Int.le_of_lt (denInt_pos a)
    have h₁ : (a.num * b.denInt) * c.denInt ≤ (b.num * a.denInt) * c.denInt :=
      Int.mul_le_mul_of_nonneg_right hab hcpos
    have h₂ : (b.num * c.denInt) * a.denInt ≤ (c.num * b.denInt) * a.denInt :=
      Int.mul_le_mul_of_nonneg_right hbc hapos
    have e₁ : (a.num * c.denInt) * b.denInt = (a.num * b.denInt) * c.denInt := by
      rw [Int.mul_assoc, Int.mul_comm c.denInt b.denInt, ← Int.mul_assoc]
    have e₂ : (b.num * a.denInt) * c.denInt = (b.num * c.denInt) * a.denInt := by
      rw [Int.mul_assoc, Int.mul_comm a.denInt c.denInt, ← Int.mul_assoc]
    have e₃ : (c.num * b.denInt) * a.denInt = (c.num * a.denInt) * b.denInt := by
      rw [Int.mul_assoc, Int.mul_comm b.denInt a.denInt, ← Int.mul_assoc]
    have h₃ : (a.num * c.denInt) * b.denInt ≤ (c.num * a.denInt) * b.denInt := by
      rw [e₁, ← e₃]
      exact Int.le_trans h₁ (e₂ ▸ h₂)
    exact Int.le_of_mul_le_mul_right h₃ hbpos
  add_mono {a₁ a₂ b₁ b₂} ha hb := by
    change (a₁.num * b₁.denInt + b₁.num * a₁.denInt) * (a₂ + b₂).denInt ≤
      (a₂.num * b₂.denInt + b₂.num * a₂.denInt) * (a₁ + b₁).denInt
    rw [add_denInt, add_denInt,
        int_ring_lhs_mono a₁.num b₁.num a₁.denInt b₁.denInt a₂.denInt b₂.denInt,
        int_ring_rhs_mono a₂.num b₂.num a₁.denInt b₁.denInt a₂.denInt b₂.denInt]
    have hd_b1b2 : 0 ≤ b₁.denInt * b₂.denInt :=
      Int.mul_nonneg (Int.le_of_lt (denInt_pos b₁)) (Int.le_of_lt (denInt_pos b₂))
    have hd_a1a2 : 0 ≤ a₁.denInt * a₂.denInt :=
      Int.mul_nonneg (Int.le_of_lt (denInt_pos a₁)) (Int.le_of_lt (denInt_pos a₂))
    exact Int.add_le_add
      (Int.mul_le_mul_of_nonneg_right ha hd_b1b2)
      (Int.mul_le_mul_of_nonneg_right hb hd_a1a2)

end RatSlack

/-! ## 2. GradeMonoid-Valued Observation Metrics -/

/-- A Lawvere hemimetric / quantitative defect measure on observations `V` valued in `ε`. -/
class ObsMetric (V : Type w) (ε : Type u) [GradeMonoid ε] where
  dist : V → V → ε
  dist_self : ∀ v : V, dist v v ≤ 0
  dist_triangle : ∀ u v w : V, dist u w ≤ dist u v + dist v w

instance instObsMetricUnit {ε : Type u} [GradeMonoid ε] : ObsMetric Unit ε where
  dist _ _ := 0
  dist_self _ := GradeMonoid.le_refl 0
  dist_triangle _ _ _ := by
    rw [GradeMonoid.add_zero]
    exact GradeMonoid.le_refl 0

instance instObsMetricNat : ObsMetric Nat Nat where
  dist a b := if a ≤ b then b - a else a - b
  dist_self v := by simp
  dist_triangle u v w := by
    by_cases huv : u ≤ v <;> by_cases hvw : v ≤ w <;> by_cases huw : u ≤ w <;>
      simp [huv, hvw, huw] <;> omega

instance instObsMetricInt : ObsMetric Int Int where
  dist a b := Int.ofNat (a - b).natAbs
  dist_self v := by simp
  dist_triangle u v w := by
    have hsub : u - w = (u - v) + (v - w) := by omega
    have htri : (u - w).natAbs ≤ (u - v).natAbs + (v - w).natAbs := by
      rw [hsub]
      exact Int.natAbs_add_le (u - v) (v - w)
    exact Int.ofNat_le.mpr htri

instance instObsMetricProd {V₁ : Type v₁} {V₂ : Type v₂} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V₁ ε] [ObsMetric V₂ ε] : ObsMetric (V₁ × V₂) ε where
  dist x y := ObsMetric.dist (ε := ε) x.1 y.1 + ObsMetric.dist (ε := ε) x.2 y.2
  dist_self v := by
    have h := GradeMonoid.add_mono (ObsMetric.dist_self (ε := ε) v.1) (ObsMetric.dist_self (ε := ε) v.2)
    rw [GradeMonoid.add_zero] at h
    exact h
  dist_triangle u v w := by
    let d1uv : ε := ObsMetric.dist (ε := ε) u.1 v.1
    let d1vw : ε := ObsMetric.dist (ε := ε) v.1 w.1
    let d2uv : ε := ObsMetric.dist (ε := ε) u.2 v.2
    let d2vw : ε := ObsMetric.dist (ε := ε) v.2 w.2
    have h₁ : ObsMetric.dist (ε := ε) u.1 w.1 ≤ d1uv + d1vw :=
      ObsMetric.dist_triangle (ε := ε) u.1 v.1 w.1
    have h₂ : ObsMetric.dist (ε := ε) u.2 w.2 ≤ d2uv + d2vw :=
      ObsMetric.dist_triangle (ε := ε) u.2 v.2 w.2
    have hsum := GradeMonoid.add_mono h₁ h₂
    have rearrange : (d1uv + d1vw) + (d2uv + d2vw) = (d1uv + d2uv) + (d1vw + d2vw) := by
      rw [GradeMonoid.add_assoc, ← GradeMonoid.add_assoc d1vw d2uv d2vw,
          GradeMonoid.add_comm d1vw d2uv, GradeMonoid.add_assoc d2uv d1vw d2vw,
          ← GradeMonoid.add_assoc]
    rw [rearrange] at hsum
    exact hsum

/-! ## 3. Transition Coalgebras (`StepSystem`) and Quantitative Forward Simulation -/

/-- Relational labeled transition system with observable state output `observe : S → V`. -/
structure StepSystem (S : Type u) (Act : Type v) (V : Type w) where
  step : S → Act → S → Prop
  observe : S → V

namespace StepSystem

/-- Build a deterministic transition system from `next : S → Act → S` and `observe : S → V`. -/
@[expose] def ofDet {S : Type u} {Act : Type v} {V : Type w}
    (next : S → Act → S) (observe : S → V) : StepSystem S Act V where
  step s a s' := s' = next s a
  observe := observe

/-- Lockstep product of two subsystems over paired actions `Act₁ × Act₂` and paired observations. -/
@[expose] def prod {S₁ : Type u₁} {S₂ : Type u₂} {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w}
    (sys₁ : StepSystem S₁ Act₁ V₁) (sys₂ : StepSystem S₂ Act₂ V₂) :
    StepSystem (S₁ × S₂) (Act₁ × Act₂) (V₁ × V₂) where
  step s a s' := sys₁.step s.1 a.1 s'.1 ∧ sys₂.step s.2 a.2 s'.2
  observe s := (sys₁.observe s.1, sys₂.observe s.2)

/-- Independent interleaved product of two subsystems over `Sum Act₁ Act₂`:
    a left action steps `sys₁` leaving `S₂` unchanged, and a right action steps `sys₂` leaving `S₁` unchanged. -/
@[expose] def indepProd {S₁ : Type u₁} {S₂ : Type u₂} {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w}
    (sys₁ : StepSystem S₁ Act₁ V₁) (sys₂ : StepSystem S₂ Act₂ V₂) :
    StepSystem (S₁ × S₂) (Sum Act₁ Act₂) (V₁ × V₂) where
  step s act s' :=
    match act with
    | .inl a₁ => sys₁.step s.1 a₁ s'.1 ∧ s'.2 = s.2
    | .inr a₂ => s'.1 = s.1 ∧ sys₂.step s.2 a₂ s'.2
  observe s := (sys₁.observe s.1, sys₂.observe s.2)

end StepSystem

/-- Relational composition `(R₁ ; R₂) x z ↔ ∃ y, R₁ x y ∧ R₂ y z`. -/
@[expose] def RelComp {α : Type u₁} {β : Type u₂} {γ : Type u}
    (R₁ : α → β → Prop) (R₂ : β → γ → Prop) (x : α) (z : γ) : Prop :=
  ∃ y : β, R₁ x y ∧ R₂ y z

/-- Product relation `(R₁ × R₂) (x₁, x₂) (y₁, y₂) ↔ R₁ x₁ y₁ ∧ R₂ x₂ y₂`. -/
@[expose] def RelProd {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    (R₁ : α₁ → β₁ → Prop) (R₂ : α₂ → β₂ → Prop) (x : α₁ × α₂) (y : β₁ × β₂) : Prop :=
  R₁ x.1 y.1 ∧ R₂ x.2 y.2

/-- Quantitative forward simulation from concrete `C` to abstract `A` along relation `R`
    within observation defect `δ : ε`. -/
structure Simulates {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    (C : StepSystem S₁ Act V) (A : StepSystem S₂ Act V)
    (R : S₁ → S₂ → Prop) (δ : ε) : Prop where
  obs_bound : ∀ {s₁ : S₁} {s₂ : S₂},
    R s₁ s₂ → ObsMetric.dist (C.observe s₁) (A.observe s₂) ≤ δ
  step_sim : ∀ {s₁ s₁' : S₁} {s₂ : S₂} {a : Act},
    R s₁ s₂ → C.step s₁ a s₁' → ∃ s₂' : S₂, A.step s₂ a s₂' ∧ R s₁' s₂'

/-- Finite multi-step labeled trace execution on a `StepSystem`. -/
inductive StepTrace {S : Type u} {Act : Type v} {V : Type w}
    (sys : StepSystem S Act V) : S → List Act → S → Prop where
  | nil (s : S) : StepTrace sys s [] s
  | cons {s₁ s₂ s₃ : S} {a : Act} {as : List Act} :
      sys.step s₁ a s₂ → StepTrace sys s₂ as s₃ → StepTrace sys s₁ (a :: as) s₃

namespace Simulates

/-- Reflexive zero-error simulation (`δ = 0`). -/
theorem refl {S : Type u₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε] (sys : StepSystem S Act V) :
    Simulates sys sys Eq (0 : ε) where
  obs_bound h := by
    subst h
    exact ObsMetric.dist_self (sys.observe _)
  step_sim h hstep := by
    subst h
    exact ⟨_, hstep, rfl⟩

/-- Relax the quantitative error bound along `δ ≤ δ'`. -/
theorem weaken_err {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {A : StepSystem S₂ Act V} {R : S₁ → S₂ → Prop} {δ δ' : ε}
    (hsim : Simulates C A R δ) (hle : δ ≤ δ') :
    Simulates C A R δ' where
  obs_bound hr := GradeMonoid.le_trans (hsim.obs_bound hr) hle
  step_sim hr hs := hsim.step_sim hr hs

/-- Transitive vertical composition of simulations: quantitative defects add (`δ₁ + δ₂`). -/
theorem trans {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type v₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {M : StepSystem S₂ Act V} {A : StepSystem S₃ Act V}
    {R₁ : S₁ → S₂ → Prop} {R₂ : S₂ → S₃ → Prop} {δ₁ δ₂ : ε}
    (h₁ : Simulates C M R₁ δ₁) (h₂ : Simulates M A R₂ δ₂) :
    Simulates C A (RelComp R₁ R₂) (δ₁ + δ₂) where
  obs_bound := by
    rintro s₁ s₃ ⟨s₂, hr₁, hr₂⟩
    exact GradeMonoid.le_trans
      (ObsMetric.dist_triangle (C.observe s₁) (M.observe s₂) (A.observe s₃))
      (GradeMonoid.add_mono (h₁.obs_bound hr₁) (h₂.obs_bound hr₂))
  step_sim := by
    rintro s₁ s₁' s₃ a ⟨s₂, hr₁, hr₂⟩ hc
    obtain ⟨s₂', hm, hr₁'⟩ := h₁.step_sim hr₁ hc
    obtain ⟨s₃', ha, hr₂'⟩ := h₂.step_sim hr₂ hm
    exact ⟨s₃', ha, ⟨s₂', hr₁', hr₂'⟩⟩

/-- Lockstep horizontal product of subsystem simulations (`δ₁ + δ₂` under product metric). -/
theorem prod {S₁ T₁ : Type u₁} {S₂ T₂ : Type u₂}
    {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V₁ ε] [ObsMetric V₂ ε]
    {C₁ : StepSystem S₁ Act₁ V₁} {A₁ : StepSystem S₂ Act₁ V₁}
    {C₂ : StepSystem T₁ Act₂ V₂} {A₂ : StepSystem T₂ Act₂ V₂}
    {R₁ : S₁ → S₂ → Prop} {R₂ : T₁ → T₂ → Prop} {δ₁ δ₂ : ε}
    (h₁ : Simulates C₁ A₁ R₁ δ₁) (h₂ : Simulates C₂ A₂ R₂ δ₂) :
    Simulates (C₁.prod C₂) (A₁.prod A₂) (RelProd R₁ R₂) (δ₁ + δ₂) where
  obs_bound := by
    intro sPair aPair hr
    exact GradeMonoid.add_mono (h₁.obs_bound hr.1) (h₂.obs_bound hr.2)
  step_sim := by
    rintro ⟨s₁, t₁⟩ ⟨s₁', t₁'⟩ ⟨s₂, t₂⟩ ⟨a₁, a₂⟩ ⟨hr₁, hr₂⟩ ⟨hs₁, hs₂⟩
    obtain ⟨s₂', ha₁, hr₁'⟩ := h₁.step_sim hr₁ hs₁
    obtain ⟨t₂', ha₂, hr₂'⟩ := h₂.step_sim hr₂ hs₂
    exact ⟨(s₂', t₂'), ⟨ha₁, ha₂⟩, ⟨hr₁', hr₂'⟩⟩

/-- Independent interleaved horizontal product of subsystem simulations over `Sum Act₁ Act₂`. -/
theorem indepProd {S₁ T₁ : Type u₁} {S₂ T₂ : Type u₂}
    {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V₁ ε] [ObsMetric V₂ ε]
    {C₁ : StepSystem S₁ Act₁ V₁} {A₁ : StepSystem S₂ Act₁ V₁}
    {C₂ : StepSystem T₁ Act₂ V₂} {A₂ : StepSystem T₂ Act₂ V₂}
    {R₁ : S₁ → S₂ → Prop} {R₂ : T₁ → T₂ → Prop} {δ₁ δ₂ : ε}
    (h₁ : Simulates C₁ A₁ R₁ δ₁) (h₂ : Simulates C₂ A₂ R₂ δ₂) :
    Simulates (C₁.indepProd C₂) (A₁.indepProd A₂) (RelProd R₁ R₂) (δ₁ + δ₂) where
  obs_bound := by
    intro sPair aPair hr
    exact GradeMonoid.add_mono (h₁.obs_bound hr.1) (h₂.obs_bound hr.2)
  step_sim := by
    rintro ⟨s₁, t₁⟩ ⟨s₁', t₁'⟩ ⟨s₂, t₂⟩ act ⟨hr₁, hr₂⟩ hstep
    cases act with
    | inl a₁ =>
      obtain ⟨hs₁, rfl⟩ := hstep
      obtain ⟨s₂', ha₁, hr₁'⟩ := h₁.step_sim hr₁ hs₁
      exact ⟨(s₂', t₂), ⟨ha₁, rfl⟩, ⟨hr₁', hr₂⟩⟩
    | inr a₂ =>
      obtain ⟨rfl, hs₂⟩ := hstep
      obtain ⟨t₂', ha₂, hr₂'⟩ := h₂.step_sim hr₂ hs₂
      exact ⟨(s₂, t₂'), ⟨rfl, ha₂⟩, ⟨hr₁, hr₂'⟩⟩

/-- Reflexivity with slack relaxation, used by compositional proof search. -/
theorem refl_of_le {S : Type u₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    (sys : StepSystem S Act V) {δ : ε} (h : (0 : ε) ≤ δ) :
    Simulates sys sys Eq δ :=
  (Simulates.refl sys).weaken_err h

/-- Transitivity with slack relaxation, used by compositional proof search. -/
theorem trans_of_le {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type v₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {M : StepSystem S₂ Act V} {A : StepSystem S₃ Act V}
    {R₁ : S₁ → S₂ → Prop} {R₂ : S₂ → S₃ → Prop} {δ₁ δ₂ δ : ε}
    (h₁ : Simulates C M R₁ δ₁) (h₂ : Simulates M A R₂ δ₂) (hle : δ₁ + δ₂ ≤ δ) :
    Simulates C A (RelComp R₁ R₂) δ :=
  (h₁.trans h₂).weaken_err hle

/-- Lockstep product with slack relaxation, used by compositional proof search. -/
theorem prod_of_le {S₁ T₁ : Type u₁} {S₂ T₂ : Type u₂}
    {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V₁ ε] [ObsMetric V₂ ε]
    {C₁ : StepSystem S₁ Act₁ V₁} {A₁ : StepSystem S₂ Act₁ V₁}
    {C₂ : StepSystem T₁ Act₂ V₂} {A₂ : StepSystem T₂ Act₂ V₂}
    {R₁ : S₁ → S₂ → Prop} {R₂ : T₁ → T₂ → Prop} {δ₁ δ₂ δ : ε}
    (h₁ : Simulates C₁ A₁ R₁ δ₁) (h₂ : Simulates C₂ A₂ R₂ δ₂) (hle : δ₁ + δ₂ ≤ δ) :
    Simulates (C₁.prod C₂) (A₁.prod A₂) (RelProd R₁ R₂) δ :=
  (h₁.prod h₂).weaken_err hle

/-- **Arbitrary-Length Trace Safety & Defect Pullback.**
    Any inductive safety invariant `Inv` of abstract system `A` pulls back along `R` across
    arbitrary-length concrete traces `StepTrace C s₁ tr s₁'`, preserving `Inv` on a matching
    abstract trajectory while maintaining the quantitative observation bound `≤ δ` at the endpoint. -/
theorem trace_safety {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {A : StepSystem S₂ Act V}
    {R : S₁ → S₂ → Prop} {δ : ε}
    (hsim : Simulates C A R δ)
    {Inv : S₂ → Prop}
    (hInvStep : ∀ {s₂ s₂' : S₂} {a : Act}, Inv s₂ → A.step s₂ a s₂' → Inv s₂')
    {s₁ s₁' : S₁} {s₂ : S₂} {tr : List Act}
    (hRel₀ : R s₁ s₂) (hInv₀ : Inv s₂) (hTrace : StepTrace C s₁ tr s₁') :
    ∃ s₂' : S₂,
      StepTrace A s₂ tr s₂' ∧
      Inv s₂' ∧
      R s₁' s₂' ∧
      ObsMetric.dist (C.observe s₁') (A.observe s₂') ≤ δ := by
  induction hTrace generalizing s₂ with
  | nil s =>
    exact ⟨s₂, .nil s₂, hInv₀, hRel₀, hsim.obs_bound hRel₀⟩
  | cons hc hrest ih =>
    obtain ⟨s₂Mid, haStep, hRelMid⟩ := hsim.step_sim hRel₀ hc
    have hInvMid : Inv s₂Mid := hInvStep hInv₀ haStep
    obtain ⟨s₂', haRest, hInv', hRel', hDist'⟩ := ih hRelMid hInvMid
    exact ⟨s₂', .cons haStep haRest, hInv', hRel', hDist'⟩

end Simulates

/-! ## 4. Bounded Stutter Simulation (`1 ≤ k ≤ K` Concrete Steps per Abstract Step) -/

/-- Exact `k`-step transition under repeated action `a` (concrete micro-steps implementing macro-step `a`). -/
inductive StepCount {S : Type u} {Act : Type v} {V : Type w}
    (sys : StepSystem S Act V) (a : Act) : Nat → S → S → Prop where
  | zero (s : S) : StepCount sys a 0 s s
  | succ {k : Nat} {s₁ s₂ s₃ : S} :
      sys.step s₁ a s₂ → StepCount sys a k s₂ s₃ → StepCount sys a (k + 1) s₁ s₃

theorem StepCount.append {S : Type u} {Act : Type v} {V : Type w}
    {sys : StepSystem S Act V} {a : Act} {j k : Nat} {s₁ s₂ s₃ : S}
    (h₁ : StepCount sys a j s₁ s₂) (h₂ : StepCount sys a k s₂ s₃) :
    StepCount sys a (j + k) s₁ s₃ := by
  induction h₁ with
  | zero _ =>
    rw [Nat.zero_add]
    exact h₂
  | succ hs hrest ih =>
    rw [Nat.succ_add]
    exact .succ hs (ih h₂)

/-- Bounded stutter simulation: every abstract macro-step of `A` (or inversely, concrete macro-step
    matched by `1 ≤ k ≤ K` micro-steps) is realized by `1 ≤ k ≤ K` micro-steps of `C` preserving `R`
    and quantitative defect `≤ δ`. -/
structure StutterSimulates {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    (C : StepSystem S₁ Act V) (A : StepSystem S₂ Act V)
    (R : S₁ → S₂ → Prop) (K : Nat) (δ : ε) : Prop where
  horizon_pos : 1 ≤ K
  obs_bound : ∀ {s₁ : S₁} {s₂ : S₂},
    R s₁ s₂ → ObsMetric.dist (C.observe s₁) (A.observe s₂) ≤ δ
  stutter_step : ∀ {s₁ : S₁} {s₂ s₂' : S₂} {a : Act},
    R s₁ s₂ → A.step s₂ a s₂' →
      ∃ (k : Nat) (s₁' : S₁), 1 ≤ k ∧ k ≤ K ∧ StepCount C a k s₁ s₁' ∧ R s₁' s₂'

namespace StutterSimulates

/-- Reflexive 1-step stutter simulation. -/
theorem refl {S : Type u₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε] (sys : StepSystem S Act V) :
    StutterSimulates sys sys Eq 1 (0 : ε) where
  horizon_pos := Nat.le_refl 1
  obs_bound h := by
    subst h
    exact ObsMetric.dist_self (sys.observe _)
  stutter_step h hs := by
    subst h
    exact ⟨1, _, Nat.le_refl 1, Nat.le_refl 1, .succ hs (.zero _), rfl⟩

/-- Helper: lift `k` micro-steps along a `StutterSimulates` relation into `k'` micro-steps bounded by `k * K`. -/
theorem lift_stepCount {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {M : StepSystem S₂ Act V}
    {R : S₁ → S₂ → Prop} {K : Nat} {δ : ε}
    (hsim : StutterSimulates C M R K δ)
    {a : Act} {k : Nat} {m m' : S₂} {s₁ : S₁}
    (hRel : R s₁ m) (hSteps : StepCount M a k m m') (hkPos : 1 ≤ k) :
    ∃ (j : Nat) (s₁' : S₁), 1 ≤ j ∧ j ≤ k * K ∧ StepCount C a j s₁ s₁' ∧ R s₁' m' := by
  induction hSteps generalizing s₁ with
  | zero _ => omega
  | @succ k₀ m₁ m₂ m₃ hmStep hmRest ih =>
    obtain ⟨j₁, s₁Mid, hj₁Pos, hj₁Bound, hc₁, hRelMid⟩ := hsim.stutter_step hRel hmStep
    cases k₀ with
    | zero =>
      cases hmRest with
      | zero _ =>
        refine ⟨j₁, s₁Mid, hj₁Pos, ?_, hc₁, hRelMid⟩
        simpa [Nat.one_mul] using hj₁Bound
    | succ k' =>
      obtain ⟨j₂, s₁', _, hj₂Bound, hc₂, hRel'⟩ := ih hRelMid (Nat.succ_pos k')
      refine ⟨j₁ + j₂, s₁', by omega, ?_, hc₁.append hc₂, hRel'⟩
      have hmul : (k' + 1 + 1) * K = K + (k' + 1) * K := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hmul]
      exact Nat.add_le_add hj₁Bound hj₂Bound

/-- Transitive composition of stutter simulations: stutter bounds multiply (`K₁ * K₂`) and
    observation defects add (`δ₁ + δ₂`). -/
theorem trans {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type v₁} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {M : StepSystem S₂ Act V} {A : StepSystem S₃ Act V}
    {R₁ : S₁ → S₂ → Prop} {R₂ : S₂ → S₃ → Prop} {K₁ K₂ : Nat} {δ₁ δ₂ : ε}
    (h₁ : StutterSimulates C M R₁ K₁ δ₁) (h₂ : StutterSimulates M A R₂ K₂ δ₂) :
    StutterSimulates C A (RelComp R₁ R₂) (K₁ * K₂) (δ₁ + δ₂) where
  horizon_pos := Nat.mul_le_mul h₁.horizon_pos h₂.horizon_pos
  obs_bound := by
    rintro s₁ s₃ ⟨s₂, hr₁, hr₂⟩
    exact GradeMonoid.le_trans
      (ObsMetric.dist_triangle (C.observe s₁) (M.observe s₂) (A.observe s₃))
      (GradeMonoid.add_mono (h₁.obs_bound hr₁) (h₂.obs_bound hr₂))
  stutter_step := by
    rintro s₁ s₃ s₃' a ⟨s₂, hr₁, hr₂⟩ haStep
    obtain ⟨k₂, s₂', hk₂Pos, hk₂Bound, hmSteps, hr₂'⟩ := h₂.stutter_step hr₂ haStep
    obtain ⟨k₁, s₁', hk₁Pos, hk₁Bound, hcSteps, hr₁'⟩ := h₁.lift_stepCount hr₁ hmSteps hk₂Pos
    have hProdBound : k₂ * K₁ ≤ K₁ * K₂ := by
      rw [Nat.mul_comm K₁ K₂]
      exact Nat.mul_le_mul_right K₁ hk₂Bound
    exact ⟨k₁, s₁', hk₁Pos, Nat.le_trans hk₁Bound hProdBound, hcSteps, ⟨s₂', hr₁', hr₂'⟩⟩

end StutterSimulates

/-! ## 5. Galois Refinement Hierarchy on State Predicates -/

/-- Predicate entailment ordering `P ≤ Q ↔ ∀ s, P s → Q s`. -/
@[expose] def PredLe {S : Type u} (P Q : S → Prop) : Prop :=
  ∀ s : S, P s → Q s

/-- A monotone Galois connection `α ⊣ γ` between concrete state predicates `S₁ → Prop`
    and abstract state predicates `S₂ → Prop`. -/
structure GaloisRefinement (S₁ : Type u₁) (S₂ : Type u₂) where
  alpha : (S₁ → Prop) → (S₂ → Prop)
  gamma : (S₂ → Prop) → (S₁ → Prop)
  adj : ∀ (P : S₁ → Prop) (Q : S₂ → Prop), PredLe (alpha P) Q ↔ PredLe P (gamma Q)

namespace GaloisRefinement

theorem mono_alpha {S₁ : Type u₁} {S₂ : Type u₂} (G : GaloisRefinement S₁ S₂)
    {P₁ P₂ : S₁ → Prop} (h : PredLe P₁ P₂) : PredLe (G.alpha P₁) (G.alpha P₂) := by
  rw [G.adj]
  intro s₁ hp₁
  exact (G.adj P₂ (G.alpha P₂)).1 (fun _ hx => hx) s₁ (h s₁ hp₁)

theorem mono_gamma {S₁ : Type u₁} {S₂ : Type u₂} (G : GaloisRefinement S₁ S₂)
    {Q₁ Q₂ : S₂ → Prop} (h : PredLe Q₁ Q₂) : PredLe (G.gamma Q₁) (G.gamma Q₂) := by
  rw [← G.adj]
  intro s₂ hα
  exact h s₂ ((G.adj (G.gamma Q₁) Q₁).2 (fun _ hx => hx) s₂ hα)

/-- Canonical Galois connection induced by any refinement relation `R : S₁ → S₂ → Prop`:
    `α(P)(s₂) := ∃ s₁, R s₁ s₂ ∧ P s₁` and `γ(Q)(s₁) := ∀ s₂, R s₁ s₂ → Q s₂`. -/
@[expose] def ofRel {S₁ : Type u₁} {S₂ : Type u₂} (R : S₁ → S₂ → Prop) : GaloisRefinement S₁ S₂ where
  alpha P s₂ := ∃ s₁ : S₁, R s₁ s₂ ∧ P s₁
  gamma Q s₁ := ∀ s₂ : S₂, R s₁ s₂ → Q s₂
  adj P Q := by
    constructor
    · intro h s₁ hp s₂ hr
      exact h s₂ ⟨s₁, hr, hp⟩
    · rintro h s₂ ⟨s₁, hr, hp⟩
      exact h s₁ hp s₂ hr

/-- Forward simulation induces backward step preservation of `γ(Inv)` whenever `R` is total
    or along any concrete step whose target stays `R`-related: if `A` preserves `Inv` from `s₂`
    and `Simulates C A R δ` holds, any concrete step from `R`-related `s₁` lands in a state
    related to an `Inv`-satisfying abstract state within error `δ`. -/
theorem sim_preserves_galois {S₁ : Type u₁} {S₂ : Type u₂} {Act : Type v} {V : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V ε]
    {C : StepSystem S₁ Act V} {A : StepSystem S₂ Act V} {R : S₁ → S₂ → Prop} {δ : ε}
    (hsim : Simulates C A R δ)
    {Inv : S₂ → Prop}
    (hInv : ∀ {s₂ s₂' : S₂} {a : Act}, Inv s₂ → A.step s₂ a s₂' → Inv s₂')
    {s₁ s₁' : S₁} {s₂ : S₂} {a : Act}
    (hAlpha : (ofRel R).alpha (fun x => x = s₁) s₂)
    (hInv₀ : Inv s₂)
    (hc : C.step s₁ a s₁') :
    ∃ s₂' : S₂, (ofRel R).alpha (fun x => x = s₁') s₂' ∧ Inv s₂' ∧
      ObsMetric.dist (C.observe s₁') (A.observe s₂') ≤ δ := by
  obtain ⟨_, hr, rfl⟩ := hAlpha
  obtain ⟨s₂', ha, hr'⟩ := hsim.step_sim hr hc
  exact ⟨s₂', ⟨s₁', hr', rfl⟩, hInv hInv₀ ha, hsim.obs_bound hr'⟩

end GaloisRefinement

end Obend.Category
end
