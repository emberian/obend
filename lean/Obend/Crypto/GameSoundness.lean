module
/- # Obend.Crypto.GameSoundness — Constructive Game-Based Cryptographic Foundation
0-axiom, `0 Classical.choice`, exact-rational game-based security layer (`RatProb`/`RatSlack`, `FinDist`,
`tvDist`, coupling/smudging, `FiniteGame`, `CryptoPackage`/`Converter`, `LazyRO` birthday bound & witness
extractor, Minkowski vacuity refutation vs uniform-CRS `MSISGame`/`MLWEGame`, `ZKProtocol` & `TranscriptTree`). -/
public import Obend.Category.Refines
public import Obend.Judge.Computational
public import Obend.Crypto.Transcript
import all Obend.Category.Refines
import all Obend.Judge.Computational
import all Obend.Crypto.Transcript
public section
namespace Obend.Crypto.GameSoundness
open Obend.Category
open Obend.Judge.Computational
set_option autoImplicit false
/-! ## 1. Exact Non-Negative Rational Bounds (`RatProb`) & `RatSlack` Bridge -/
structure RatProb where
  num : Nat
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr
@[expose] def RatProb.zero : RatProb := ⟨0, 1, Nat.zero_lt_one⟩
@[expose] def RatProb.one : RatProb := ⟨1, 1, Nat.zero_lt_one⟩
@[expose] def RatProb.le (p q : RatProb) : Prop := p.num * q.den ≤ q.num * p.den
@[expose] def RatProb.eqv (p q : RatProb) : Prop := p.num * q.den = q.num * p.den
def RatProb.add (p q : RatProb) : RatProb := ⟨p.num * q.den + q.num * p.den, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩
def RatProb.mul (p q : RatProb) : RatProb := ⟨p.num * q.num, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩
def RatProb.absDiff (p q : RatProb) : RatProb := ⟨((p.num : Int) * (q.den : Int) - (q.num : Int) * (p.den : Int)).natAbs, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩
@[expose] def RatProb.toRatSlack (p : RatProb) : RatSlack := ⟨(p.num : Int), p.den - 1⟩
theorem RatProb.toRatSlack_denInt (p : RatProb) : p.toRatSlack.denInt = (p.den : Int) := by change ((p.den - 1 + 1 : Nat) : Int) = (p.den : Int); have := p.den_pos; omega
theorem RatProb.toRatSlack_le_iff (p q : RatProb) : (p.toRatSlack ≤ q.toRatSlack) ↔ RatProb.le p q := by
  change p.toRatSlack.num * q.toRatSlack.denInt ≤ q.toRatSlack.num * p.toRatSlack.denInt ↔ _; rw [toRatSlack_denInt, toRatSlack_denInt]
  change (p.num : Int) * (q.den : Int) ≤ (q.num : Int) * (p.den : Int) ↔ p.num * q.den ≤ q.num * p.den; rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_le
theorem RatProb.toRatSlack_add (p q : RatProb) : (p.add q).toRatSlack = p.toRatSlack + q.toRatSlack := by
  have hp := p.den_pos; have hq := q.den_pos
  change RatSlack.mk (((p.num * q.den + q.num * p.den : Nat) : Int)) (p.den * q.den - 1) = RatSlack.mk ((p.num : Int) * q.toRatSlack.denInt + (q.num : Int) * p.toRatSlack.denInt) ((p.den - 1 + 1) * (q.den - 1 + 1) - 1)
  rw [toRatSlack_denInt, toRatSlack_denInt, Nat.sub_add_cancel hp, Nat.sub_add_cancel hq, Int.natCast_add, Int.natCast_mul, Int.natCast_mul]
theorem RatProb.eqv_refl (p : RatProb) : RatProb.eqv p p := rfl
theorem RatProb.eqv_symm {p q : RatProb} (h : RatProb.eqv p q) : RatProb.eqv q p := h.symm
theorem RatProb.eqv_trans {p q r : RatProb} (hpq : RatProb.eqv p q) (hqr : RatProb.eqv q r) : RatProb.eqv p r := by
  unfold RatProb.eqv at *; refine Nat.eq_of_mul_eq_mul_right q.den_pos ?_
  calc (p.num * r.den) * q.den = (p.num * q.den) * r.den := by ac_rfl
    _ = (q.num * p.den) * r.den := by rw [hpq]
    _ = (q.num * r.den) * p.den := by ac_rfl
    _ = (r.num * q.den) * p.den := by rw [hqr]
    _ = (r.num * p.den) * q.den := by ac_rfl
theorem RatProb.le_refl (p : RatProb) : RatProb.le p p := Nat.le_refl _
theorem RatProb.le_of_eqv {p q : RatProb} (h : RatProb.eqv p q) : RatProb.le p q := Nat.le_of_eq h
theorem RatProb.eqv_of_le_antisymm {p q : RatProb} (h1 : RatProb.le p q) (h2 : RatProb.le q p) : RatProb.eqv p q := Nat.le_antisymm h1 h2
theorem RatProb.le_trans {p q r : RatProb} (hpq : RatProb.le p q) (hqr : RatProb.le q r) : RatProb.le p r := by rw [← toRatSlack_le_iff] at *; exact GradeMonoid.le_trans hpq hqr
theorem RatProb.le_congr {p₁ p₂ q₁ q₂ : RatProb} (hp : RatProb.eqv p₁ p₂) (hq : RatProb.eqv q₁ q₂) (h : RatProb.le p₁ q₁) : RatProb.le p₂ q₂ :=
  RatProb.le_trans (RatProb.le_of_eqv (RatProb.eqv_symm hp)) (RatProb.le_trans h (RatProb.le_of_eqv hq))
theorem RatProb.add_le_add {a₁ a₂ b₁ b₂ : RatProb} (ha : RatProb.le a₁ a₂) (hb : RatProb.le b₁ b₂) : RatProb.le (RatProb.add a₁ b₁) (RatProb.add a₂ b₂) := by
  rw [← toRatSlack_le_iff, toRatSlack_add, toRatSlack_add]; exact GradeMonoid.add_mono ((toRatSlack_le_iff _ _).2 ha) ((toRatSlack_le_iff _ _).2 hb)
theorem RatProb.absDiff_symm (p q : RatProb) : RatProb.eqv (RatProb.absDiff p q) (RatProb.absDiff q p) := by
  unfold RatProb.eqv RatProb.absDiff; dsimp only; have hSub : (q.num : Int) * p.den - (p.num : Int) * q.den = -((p.num : Int) * q.den - (q.num : Int) * p.den) := (by omega)
  rw [hSub, Int.natAbs_neg, Nat.mul_comm p.den q.den]
theorem RatProb.absDiff_eqv_congr {p₁ p₂ q₁ q₂ : RatProb} (hp : RatProb.eqv p₁ p₂) (hq : RatProb.eqv q₁ q₂) : RatProb.eqv (RatProb.absDiff p₁ q₁) (RatProb.absDiff p₂ q₂) := by
  unfold RatProb.eqv RatProb.absDiff at *; dsimp only; have hpI : (p₁.num : Int) * p₂.den = (p₂.num : Int) * p₁.den := (by rw [← Int.natCast_mul, ← Int.natCast_mul, hp])
  have hqI : (q₁.num : Int) * q₂.den = (q₂.num : Int) * q₁.den := (by rw [← Int.natCast_mul, ← Int.natCast_mul, hq])
  have t1 : ((p₁.num : Int) * q₁.den) * (p₂.den * q₂.den) = ((p₂.num : Int) * q₂.den) * (p₁.den * q₁.den) := by
    calc ((p₁.num : Int) * q₁.den) * (p₂.den * q₂.den) = ((p₁.num : Int) * p₂.den) * (q₁.den * q₂.den) := by ac_rfl
      _ = ((p₂.num : Int) * p₁.den) * (q₁.den * q₂.den) := by rw [hpI]
      _ = ((p₂.num : Int) * q₂.den) * (p₁.den * q₁.den) := by ac_rfl
  have t2 : ((q₁.num : Int) * p₁.den) * (p₂.den * q₂.den) = ((q₂.num : Int) * p₂.den) * (p₁.den * q₁.den) := by
    calc ((q₁.num : Int) * p₁.den) * (p₂.den * q₂.den) = ((q₁.num : Int) * q₂.den) * (p₁.den * p₂.den) := by ac_rfl
      _ = ((q₂.num : Int) * q₁.den) * (p₁.den * p₂.den) := by rw [hqI]
      _ = ((q₂.num : Int) * p₂.den) * (p₁.den * q₁.den) := by ac_rfl
  have hCross : ((p₁.num : Int) * q₁.den - (q₁.num : Int) * p₁.den) * ((p₂.den * q₂.den : Nat) : Int) = ((p₂.num : Int) * q₂.den - (q₂.num : Int) * p₂.den) * ((p₁.den * q₁.den : Nat) : Int) := by
    rw [Int.natCast_mul, Int.natCast_mul, Int.sub_mul, Int.sub_mul, t1, t2]
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hCross
theorem RatProb.absDiff_triangle (p q r : RatProb) : RatProb.le (RatProb.absDiff p r) (RatProb.add (RatProb.absDiff p q) (RatProb.absDiff q r)) := by
  unfold RatProb.le RatProb.add RatProb.absDiff; dsimp only; let dPR : Int := (p.num : Int) * r.den - (r.num : Int) * p.den; let dPQ : Int := (p.num : Int) * q.den - (q.num : Int) * p.den
  let dQR : Int := (q.num : Int) * r.den - (r.num : Int) * q.den
  have hSplit : dPR * q.den = dPQ * r.den + dQR * p.den := by
    dsimp [dPR, dPQ, dQR]; rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]; have e1 : (p.num : Int) * r.den * q.den = (p.num : Int) * q.den * r.den := (by ac_rfl)
    have e2 : (q.num : Int) * p.den * r.den = (q.num : Int) * r.den * p.den := (by ac_rfl); have e3 : (r.num : Int) * p.den * q.den = (r.num : Int) * q.den * p.den := (by ac_rfl); rw [e1, e2, e3]; omega
  have hTri : (dPR * q.den).natAbs ≤ (dPQ * r.den).natAbs + (dQR * p.den).natAbs := (by rw [hSplit]; exact Int.natAbs_add_le _ _); simp only [Int.natAbs_mul, Int.natAbs_natCast] at hTri
  calc dPR.natAbs * (p.den * q.den * (q.den * r.den)) = (dPR.natAbs * q.den) * (p.den * q.den * r.den) := by ac_rfl
    _ ≤ (dPQ.natAbs * r.den + dQR.natAbs * p.den) * (p.den * q.den * r.den) := Nat.mul_le_mul_right _ hTri
    _ = (dPQ.natAbs * (q.den * r.den) + dQR.natAbs * (p.den * q.den)) * (p.den * r.den) := by rw [Nat.add_mul, Nat.add_mul]; congr 1 <;> ac_rfl
/-! ## 2. Constructive Discrete Distributions (`FinDist α`) & Coupling Bad-Event Bound -/
def weightSum {α : Type} : List (α × Nat) → Nat
  | [] => 0
  | (_, w) :: xs => w + weightSum xs
def eventMass {α : Type} (p : α → Bool) : List (α × Nat) → Nat
  | [] => 0
  | (a, w) :: xs => (if p a then w else 0) + eventMass p xs
def massOf {α : Type} [DecidableEq α] (x : α) (xs : List (α × Nat)) : Nat := eventMass (· == x) xs
structure FinDist (α : Type) where
  support : List (α × Nat)
  total_pos : 0 < weightSum support
theorem FinDist.ext_support {α : Type} {d₁ d₂ : FinDist α} (h : d₁.support = d₂.support) : d₁ = d₂ := by
  cases d₁; cases d₂; cases h; rfl
def FinDist.totalWeight {α : Type} (d : FinDist α) : Nat := weightSum d.support
def FinDist.probEvent {α : Type} (d : FinDist α) (p : α → Bool) : RatProb := ⟨eventMass p d.support, d.totalWeight, d.total_pos⟩
def FinDist.probOf {α : Type} [DecidableEq α] (d : FinDist α) (x : α) : RatProb := d.probEvent (· == x)
def expectMass {α : Type} (f : α → Nat) : List (α × Nat) → Nat
  | [] => 0
  | (a, w) :: xs => f a * w + expectMass f xs
def FinDist.expectNat {α : Type} (d : FinDist α) (f : α → Nat) : RatProb := ⟨expectMass f d.support, d.totalWeight, d.total_pos⟩
@[expose] def FinDist.Equiv {α : Type} (d₁ d₂ : FinDist α) : Prop := ∀ p : α → Bool, RatProb.eqv (d₁.probEvent p) (d₂.probEvent p)
theorem weightSum_append {α : Type} (xs ys : List (α × Nat)) : weightSum (xs ++ ys) = weightSum xs + weightSum ys := by
  induction xs with | nil => simp [weightSum] | cons _ _ ih => simp [weightSum, ih, Nat.add_assoc]
theorem eventMass_append {α : Type} (p : α → Bool) (xs ys : List (α × Nat)) : eventMass p (xs ++ ys) = eventMass p xs + eventMass p ys := by
  induction xs with | nil => simp [eventMass] | cons _ _ ih => simp [eventMass, ih, Nat.add_assoc]
theorem eventMass_le_weightSum {α : Type} (p : α → Bool) (xs : List (α × Nat)) : eventMass p xs ≤ weightSum xs := by
  induction xs with | nil => exact Nat.le_refl 0 | cons _ _ ih => simp only [eventMass, weightSum]; split <;> omega
theorem eventMass_compl {α : Type} (p : α → Bool) (xs : List (α × Nat)) : eventMass p xs + eventMass (fun a => !p a) xs = weightSum xs := by
  induction xs with
  | nil => rfl
  | cons hd _ ih =>
    rcases hd with ⟨a, _⟩; simp only [eventMass, weightSum]
    by_cases h : p a = true <;> simp [h] <;> omega
def scaleSupport {α : Type} (c : Nat) : List (α × Nat) → List (α × Nat)
  | [] => []
  | (a, w) :: xs => (a, c * w) :: scaleSupport c xs
theorem weightSum_scaleSupport {α : Type} (c : Nat) (xs : List (α × Nat)) : weightSum (scaleSupport c xs) = c * weightSum xs := by
  induction xs with | nil => simp [scaleSupport, weightSum] | cons _ _ ih => simp [scaleSupport, weightSum, ih, Nat.mul_add]
theorem eventMass_scaleSupport {α : Type} (p : α → Bool) (c : Nat) (xs : List (α × Nat)) : eventMass p (scaleSupport c xs) = c * eventMass p xs := by
  induction xs with
  | nil => simp [scaleSupport, eventMass] | cons hd _ ih => rcases hd with ⟨a, _⟩; simp only [scaleSupport, eventMass, ih, Nat.mul_add]; cases p a <;> simp
def FinDist.pure {α : Type} (x : α) : FinDist α := ⟨[(x, 1)], by simp [weightSum]⟩
theorem FinDist.weightSum_map {α β : Type} (f : α → β) (xs : List (α × Nat)) : weightSum (xs.map (fun x => (f x.1, x.2))) = weightSum xs := by
  induction xs with | nil => rfl | cons _ _ ih => simp [weightSum, ih]
theorem FinDist.eventMass_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List (α × Nat)) : eventMass p (xs.map (fun x => (f x.1, x.2))) = eventMass (p ∘ f) xs := by
  induction xs with | nil => rfl | cons _ _ ih => simp [eventMass, ih]
def FinDist.map {α β : Type} (f : α → β) (d : FinDist α) : FinDist β where
  support := d.support.map (fun x => (f x.1, x.2))
  total_pos := by rw [FinDist.weightSum_map]; exact d.total_pos
theorem FinDist.probEvent_map {α β : Type} (f : α → β) (d : FinDist α) (p : β → Bool) : (d.map f).probEvent p = d.probEvent (p ∘ f) := by
  unfold FinDist.probEvent FinDist.map FinDist.totalWeight; dsimp only; congr 1; exact FinDist.eventMass_map f p d.support; exact FinDist.weightSum_map f d.support
def bindRaw {α β : Type} : List (α × Nat) → (α → FinDist β) → List (β × Nat) × Nat
  | [], _ => ([], 1)
  | (a, w) :: rest, k =>
    let (outRest, denRest) := bindRaw rest k; let da := k a; let ta := da.totalWeight
    (scaleSupport (w * denRest) da.support ++ scaleSupport ta outRest, ta * denRest)
theorem bindRaw_den_pos {α β : Type} (xs : List (α × Nat)) (k : α → FinDist β) : 0 < (bindRaw xs k).2 := by
  induction xs with | nil => exact Nat.zero_lt_one | cons hd _ ih => exact Nat.mul_pos (k hd.1).total_pos ih
theorem bindRaw_weightSum {α β : Type} (xs : List (α × Nat)) (k : α → FinDist β) : weightSum (bindRaw xs k).1 = weightSum xs * (bindRaw xs k).2 := by
  induction xs with
  | nil => simp [bindRaw, weightSum]
  | cons hd _ ih =>
    rcases hd with ⟨a, w⟩
    simp only [bindRaw, weightSum, weightSum_append, weightSum_scaleSupport, ih, FinDist.totalWeight]; rw [Nat.add_mul]; congr 1 <;> ac_rfl
def FinDist.bind {α β : Type} (d : FinDist α) (k : α → FinDist β) : FinDist β where
  support := (bindRaw d.support k).1
  total_pos := by rw [bindRaw_weightSum]; exact Nat.mul_pos d.total_pos (bindRaw_den_pos d.support k)
def FinDist.prod {α β : Type} (d₁ : FinDist α) (d₂ : FinDist β) : FinDist (α × β) := d₁.bind (fun a => d₂.map (fun b => (a, b)))
theorem length_pos_of_ne_nil {α : Type} {xs : List α} (h : xs ≠ []) : 0 < xs.length := by
  cases xs with | nil => exact False.elim (h rfl) | cons _ _ => simp
private theorem range_ne_nil {n : Nat} (h : 0 < n) : List.range n ≠ [] := by intro he; have := congrArg List.length he; simp at this; omega
def FinDist.uniform {α : Type} (xs : List α) (hne : xs ≠ []) : FinDist α where
  support := xs.map (fun x => (x, 1))
  total_pos := by cases xs with | nil => exact False.elim (hne rfl) | cons _ _ => simp [weightSum]; omega
theorem uniform_weightSum {α : Type} (xs : List α) : weightSum (xs.map (fun x => (x, 1))) = xs.length := by
  induction xs with | nil => rfl | cons _ _ ih => simp [weightSum, ih]; omega
theorem uniform_eventMass {α : Type} (p : α → Bool) (xs : List α) : eventMass p (xs.map (fun x => (x, 1))) = (xs.filter p).length := by
  induction xs with
  | nil => rfl | cons x _ ih => simp only [List.map_cons, eventMass, List.filter, ih]; cases p x <;> simp <;> omega
theorem bind_map_eq {α β γ : Type} (d : FinDist α) (f : α → β) (k : β → FinDist γ) : (d.map f).bind k = d.bind (fun a => k (f a)) := by
  apply FinDist.ext_support
  have aux : ∀ (xs : List (α × Nat)), bindRaw (xs.map (fun x => (f x.1, x.2))) k = bindRaw xs (fun a => k (f a)) := by
    intro xs; induction xs with | nil => rfl | cons hd _ ih => rcases hd with ⟨_, _⟩; simp [bindRaw, ih]
  exact congrArg Prod.fst (aux d.support)
theorem bind_map_equiv {α β γ : Type} (d : FinDist α) (f : α → β) (k : β → FinDist γ) : FinDist.Equiv ((d.map f).bind k) (d.bind (fun a => k (f a))) := by rw [bind_map_eq]; exact fun _ => rfl
theorem probEvent_bind_mono {α β₁ β₂ : Type} (d : FinDist α) (k₁ : α → FinDist β₁) (k₂ : α → FinDist β₂) (p₁ : β₁ → Bool) (p₂ : β₂ → Bool)
    (hPt : ∀ a w, (a, w) ∈ d.support → RatProb.le ((k₁ a).probEvent p₁) ((k₂ a).probEvent p₂)) :
    RatProb.le ((d.bind k₁).probEvent p₁) ((d.bind k₂).probEvent p₂) := by
  unfold RatProb.le FinDist.probEvent FinDist.bind FinDist.totalWeight; dsimp only; rw [bindRaw_weightSum, bindRaw_weightSum]
  have aux : ∀ (xs : List (α × Nat)), (∀ a w, (a, w) ∈ xs → RatProb.le ((k₁ a).probEvent p₁) ((k₂ a).probEvent p₂)) →
      eventMass p₁ (bindRaw xs k₁).1 * (bindRaw xs k₂).2 ≤ eventMass p₂ (bindRaw xs k₂).1 * (bindRaw xs k₁).2 := by
    intro xs; induction xs with
    | nil => intros; simp [bindRaw, eventMass]
    | cons hd rest ih =>
      rcases hd with ⟨a, w⟩; intro hSub
      have hPa := hSub a w List.mem_cons_self; unfold RatProb.le FinDist.probEvent FinDist.totalWeight at hPa; dsimp only at hPa; have ihR := ih (fun a' w' hm => hSub a' w' (List.mem_cons_of_mem _ hm))
      simp only [bindRaw, eventMass_append, eventMass_scaleSupport, FinDist.totalWeight]; rw [Nat.add_mul, Nat.add_mul]; apply Nat.add_le_add
      · calc (w * (bindRaw rest k₁).2 * eventMass p₁ (k₁ a).support) * (weightSum (k₂ a).support * (bindRaw rest k₂).2)
          _ = (eventMass p₁ (k₁ a).support * weightSum (k₂ a).support) * (w * (bindRaw rest k₁).2 * (bindRaw rest k₂).2) := by ac_rfl
          _ ≤ (eventMass p₂ (k₂ a).support * weightSum (k₁ a).support) * (w * (bindRaw rest k₁).2 * (bindRaw rest k₂).2) := Nat.mul_le_mul_right _ hPa
          _ = (w * (bindRaw rest k₂).2 * eventMass p₂ (k₂ a).support) * (weightSum (k₁ a).support * (bindRaw rest k₁).2) := by ac_rfl
      · calc (weightSum (k₁ a).support * eventMass p₁ (bindRaw rest k₁).1) * (weightSum (k₂ a).support * (bindRaw rest k₂).2)
          _ = (eventMass p₁ (bindRaw rest k₁).1 * (bindRaw rest k₂).2) * (weightSum (k₁ a).support * weightSum (k₂ a).support) := by ac_rfl
          _ ≤ (eventMass p₂ (bindRaw rest k₂).1 * (bindRaw rest k₁).2) * (weightSum (k₁ a).support * weightSum (k₂ a).support) := Nat.mul_le_mul_right _ ihR
          _ = (weightSum (k₂ a).support * eventMass p₂ (bindRaw rest k₂).1) * (weightSum (k₁ a).support * (bindRaw rest k₁).2) := by ac_rfl
  calc eventMass p₁ (bindRaw d.support k₁).1 * (weightSum d.support * (bindRaw d.support k₂).2)
    _ = (eventMass p₁ (bindRaw d.support k₁).1 * (bindRaw d.support k₂).2) * weightSum d.support := by ac_rfl
    _ ≤ (eventMass p₂ (bindRaw d.support k₂).1 * (bindRaw d.support k₁).2) * weightSum d.support := Nat.mul_le_mul_right _ (aux d.support hPt)
    _ = eventMass p₂ (bindRaw d.support k₂).1 * (weightSum d.support * (bindRaw d.support k₁).2) := by ac_rfl
theorem bind_congr_equiv {α β : Type} (d : FinDist α) (k₁ k₂ : α → FinDist β) (hPt : ∀ a, FinDist.Equiv (k₁ a) (k₂ a)) : FinDist.Equiv (d.bind k₁) (d.bind k₂) :=
  fun p => RatProb.eqv_of_le_antisymm
    (probEvent_bind_mono d k₁ k₂ p p (fun a _ _ => RatProb.le_of_eqv (hPt a p)))
    (probEvent_bind_mono d k₂ k₁ p p (fun a _ _ => RatProb.le_of_eqv (RatProb.eqv_symm (hPt a p))))
theorem FinDist.bind_pure_left {α β : Type} (x : α) (k : α → FinDist β) : FinDist.Equiv (FinDist.bind (FinDist.pure x) k) (k x) := by
  intro p; unfold FinDist.bind FinDist.pure FinDist.probEvent FinDist.totalWeight RatProb.eqv; simp [bindRaw, scaleSupport, eventMass_scaleSupport, weightSum_scaleSupport]
theorem FinDist.bind_pure_right {α : Type} (d : FinDist α) : FinDist.Equiv (FinDist.bind d FinDist.pure) d := by
  intro p
  have aux : ∀ (xs : List (α × Nat)), (bindRaw xs FinDist.pure).2 = 1 ∧ eventMass p (bindRaw xs FinDist.pure).1 = eventMass p xs := by
    intro xs; induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons hd _ ih =>
      rcases hd with ⟨a, w⟩; obtain ⟨hD, hE⟩ := ih
      simp only [bindRaw, FinDist.pure, FinDist.totalWeight, weightSum, Nat.add_zero, hD, Nat.mul_one, scaleSupport, List.singleton_append, eventMass, eventMass_scaleSupport, Nat.one_mul, hE]
      exact ⟨by trivial, by trivial⟩
  obtain ⟨hD, hE⟩ := aux d.support; unfold FinDist.probEvent FinDist.totalWeight RatProb.eqv; dsimp only [FinDist.bind]; rw [bindRaw_weightSum, hD, hE, Nat.mul_one]
theorem FinDist.bind_assoc {α β γ : Type} (d : FinDist α) (f : α → FinDist β) (g : β → FinDist γ) : FinDist.Equiv ((d.bind f).bind g) (d.bind (fun a => (f a).bind g)) := by
  intro p
  have sc : ∀ (c : Nat) (ys : List (β × Nat)), eventMass p (bindRaw (scaleSupport c ys) g).1 = c * eventMass p (bindRaw ys g).1 ∧ (bindRaw (scaleSupport c ys) g).2 = (bindRaw ys g).2 := by
    intro c ys; induction ys with
    | nil => simp [scaleSupport, bindRaw, eventMass]
    | cons hd _ ih =>
      rcases hd with ⟨b, u⟩; obtain ⟨ihE, ihD⟩ := ih
      simp only [scaleSupport, bindRaw, ihD, eventMass_append, eventMass_scaleSupport, ihE]
      exact ⟨by rw [Nat.mul_add]; congr 1 <;> ac_rfl, by trivial⟩
  have ap : ∀ (ys₁ ys₂ : List (β × Nat)), (bindRaw (ys₁ ++ ys₂) g).2 = (bindRaw ys₁ g).2 * (bindRaw ys₂ g).2 ∧ eventMass p (bindRaw (ys₁ ++ ys₂) g).1 =
        eventMass p (bindRaw ys₁ g).1 * (bindRaw ys₂ g).2 + eventMass p (bindRaw ys₂ g).1 * (bindRaw ys₁ g).2 := by
    intro ys₁ ys₂; induction ys₁ with
    | nil => simp [bindRaw, eventMass]
    | cons hd ys₁ ih =>
      rcases hd with ⟨b, u⟩; obtain ⟨ihD, ihE⟩ := ih
      simp only [List.cons_append, bindRaw, ihD, eventMass_append, eventMass_scaleSupport, ihE]
      refine ⟨by ac_rfl, ?_⟩; rw [Nat.mul_add, Nat.add_mul]
      have e1 : u * ((bindRaw ys₁ g).2 * (bindRaw ys₂ g).2) * eventMass p (g b).support = u * (bindRaw ys₁ g).2 * eventMass p (g b).support * (bindRaw ys₂ g).2 := (by ac_rfl)
      have e2 : (g b).totalWeight * (eventMass p (bindRaw ys₁ g).1 * (bindRaw ys₂ g).2) = (g b).totalWeight * eventMass p (bindRaw ys₁ g).1 * (bindRaw ys₂ g).2 := (by ac_rfl)
      have e3 : (g b).totalWeight * (eventMass p (bindRaw ys₂ g).1 * (bindRaw ys₁ g).2) = eventMass p (bindRaw ys₂ g).1 * ((g b).totalWeight * (bindRaw ys₁ g).2) := (by ac_rfl); rw [e1, e2, e3]; omega
  have cross : ∀ (xs : List (α × Nat)), eventMass p (bindRaw (bindRaw xs f).1 g).1 * (bindRaw xs (fun a => (f a).bind g)).2 =
      eventMass p (bindRaw xs (fun a => (f a).bind g)).1 * ((bindRaw xs f).2 * (bindRaw (bindRaw xs f).1 g).2) := by
    intro xs; induction xs with
    | nil => simp [bindRaw, eventMass]
    | cons hd rest ih =>
      rcases hd with ⟨a, w⟩; simp only [bindRaw]
      obtain ⟨hAd, hAe⟩ := ap (scaleSupport (w * (bindRaw rest f).2) (f a).support)
        (scaleSupport (f a).totalWeight (bindRaw rest f).1)
      obtain ⟨hSe1, hSd1⟩ := sc (w * (bindRaw rest f).2) (f a).support; obtain ⟨hSe2, hSd2⟩ := sc (f a).totalWeight (bindRaw rest f).1; have hSup : ((f a).bind g).support = (bindRaw (f a).support g).1 := rfl
      have hTot : ((f a).bind g).totalWeight = weightSum (f a).support * (bindRaw (f a).support g).2 := bindRaw_weightSum (f a).support g
      rw [hAd, hAe, hSd1, hSd2, hSe1, hSe2, hSup, hTot]; simp only [eventMass_append, eventMass_scaleSupport, FinDist.totalWeight]
      let eA := eventMass p (bindRaw (f a).support g).1; let dA := (bindRaw (f a).support g).2; let tA := weightSum (f a).support; let dR := (bindRaw rest f).2
      let eLR := eventMass p (bindRaw (bindRaw rest f).1 g).1; let dLR := (bindRaw (bindRaw rest f).1 g).2; let eRR := eventMass p (bindRaw rest (fun x => (f x).bind g)).1
      let dRR := (bindRaw rest (fun x => (f x).bind g)).2; have ih' : eLR * dRR = eRR * (dR * dLR) := ih; rw [Nat.add_mul, Nat.add_mul]
      have l1 : (w * dR * eA * dLR) * (tA * dA * dRR) = (w * dRR * eA) * (tA * dR * (dA * dLR)) := (by ac_rfl); have l2 : (tA * eLR * dA) * (tA * dA * dRR) = (tA * tA * dA * dA) * (eLR * dRR) := (by ac_rfl)
      have l3 : (tA * tA * dA * dA) * (eRR * (dR * dLR)) = (tA * dA * eRR) * (tA * dR * (dA * dLR)) := (by ac_rfl); rw [l1, l2, ih', l3]
  unfold FinDist.probEvent FinDist.totalWeight RatProb.eqv; change eventMass p (bindRaw (bindRaw d.support f).1 g).1 *
      weightSum (bindRaw d.support (fun a => (f a).bind g)).1 =
    eventMass p (bindRaw d.support (fun a => (f a).bind g)).1 *
      weightSum (bindRaw (bindRaw d.support f).1 g).1
  rw [bindRaw_weightSum, bindRaw_weightSum, bindRaw_weightSum]; have hC := cross d.support
  calc eventMass p (bindRaw (bindRaw d.support f).1 g).1 * (weightSum d.support * (bindRaw d.support (fun a => (f a).bind g)).2)
    _ = weightSum d.support * (eventMass p (bindRaw (bindRaw d.support f).1 g).1 * (bindRaw d.support (fun a => (f a).bind g)).2) := by ac_rfl
    _ = weightSum d.support * (eventMass p (bindRaw d.support (fun a => (f a).bind g)).1 * ((bindRaw d.support f).2 * (bindRaw (bindRaw d.support f).1 g).2)) := by rw [hC]
    _ = eventMass p (bindRaw d.support (fun a => (f a).bind g)).1 * (weightSum d.support * (bindRaw d.support f).2 * (bindRaw (bindRaw d.support f).1 g).2) := by ac_rfl
/-! ### Exact Total Variation / Statistical Distance (`tvDist`) & Coupling Lemma -/
def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => let r := dedupList xs; if x ∈ r then r else x :: r
theorem mem_dedupList {α : Type} [DecidableEq α] {x : α} {xs : List α} : x ∈ dedupList xs ↔ x ∈ xs := by
  induction xs with
  | nil => exact Iff.rfl
  | cons _ _ ih =>
    simp only [dedupList, List.mem_cons]; split
    · rename_i hIn; exact ⟨fun h => .inr (ih.1 h), fun h => h.elim (fun hxy => hxy ▸ hIn) (fun hm => ih.2 hm)⟩
    · simp only [List.mem_cons]; exact ⟨fun h => h.elim .inl (fun hm => .inr (ih.1 hm)), fun h => h.elim .inl (fun hm => .inr (ih.2 hm))⟩
theorem nodup_dedupList {α : Type} [DecidableEq α] (xs : List α) : (dedupList xs).Nodup := by
  induction xs with | nil => exact .nil | cons _ _ ih => simp only [dedupList]; split; exact ih; rename_i hNot; exact .cons (fun _ hy hxy => hNot (hxy ▸ hy)) ih
def sumOver {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + sumOver f xs
private theorem sumOver_zero {α : Type} (ys : List α) : sumOver (fun _ => 0) ys = 0 := by
  induction ys with | nil => rfl | cons _ _ ih => simp [sumOver, ih]
private theorem sumOver_mul_right {α : Type} (f : α → Nat) (c : Nat) (S : List α) : sumOver f S * c = sumOver (fun x => f x * c) S := by
  induction S with | nil => simp [sumOver] | cons _ _ ih => simp [sumOver, Nat.add_mul, ih]
private theorem sumOver_add_point {α : Type} [DecidableEq α] (a : α) (w : Nat) (p : α → Bool) (S : List α) (hNd : S.Nodup) (hMem : a ∈ S) :
    sumOver (fun x => if p x then (if a == x then w else 0) else 0) S = if p a then w else 0 := by
  induction S with
  | nil => cases hMem
  | cons x rest ih =>
    rcases hNd with _ | ⟨hNot, hNdR⟩; rcases List.mem_cons.1 hMem with rfl | hTail
    · have hR0 : ∀ (ys : List α), (∀ y ∈ ys, a ≠ y) →
          sumOver (fun y => if p y then (if a == y then w else 0) else 0) ys = 0 := by
        intro ys; induction ys with
        | nil => intros; rfl
        | cons y ys ihY =>
          intro hz; simp only [sumOver, beq_eq_false_iff_ne.2 (hz y List.mem_cons_self), Bool.false_eq_true, ↓reduceIte, ite_self, Nat.zero_add]; exact ihY (fun z hz' => hz z (List.mem_cons_of_mem _ hz'))
      simp only [sumOver, beq_self_eq_true, ↓reduceIte, hR0 rest (fun y hy h => hNot y hy h), Nat.add_zero]
    · simp only [sumOver, beq_eq_false_iff_ne.2 (fun h => hNot a hTail h.symm), Bool.false_eq_true, ↓reduceIte, ite_self, Nat.zero_add]; exact ih hNdR hTail
theorem eventMass_eq_sumOver {α : Type} [DecidableEq α] (p : α → Bool) (S : List α) (hNodup : S.Nodup) (xs : List (α × Nat)) (hSub : ∀ a ∈ xs.map Prod.fst, a ∈ S) :
    eventMass p xs = sumOver (fun x => if p x then massOf x xs else 0) S := by
  induction xs with
  | nil =>
    have hEq : (fun x : α => if p x then massOf x [] else 0) = (fun _ => 0) := (by funext _; simp [massOf, eventMass]); simp [eventMass, hEq, sumOver_zero]
  | cons hd rest ih =>
    rcases hd with ⟨a, w⟩
    have hMass : ∀ x, massOf x ((a, w) :: rest) = (if a == x then w else 0) + massOf x rest := fun _ => rfl
    have hSplit : ∀ (ys : List α), sumOver (fun x => if p x then massOf x ((a, w) :: rest) else 0) ys = sumOver (fun x => if p x then (if a == x then w else 0) else 0) ys +
        sumOver (fun x => if p x then massOf x rest else 0) ys := by
      intro ys; induction ys with
      | nil => rfl | cons y _ ihY => dsimp only [sumOver]; rw [ihY, hMass y]; cases p y <;> simp <;> omega
    rw [hSplit S, sumOver_add_point a w p S hNodup (hSub a List.mem_cons_self), ← ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx))]; rfl
def optEvent {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) (x : α) : Bool := decide (massOf x d₂.support * d₁.totalWeight < massOf x d₁.support * d₂.totalWeight)
def tvDist {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) : RatProb :=
  let S := dedupList (d₁.support.map Prod.fst ++ d₂.support.map Prod.fst)
  ⟨sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) S,
   d₁.totalWeight * d₂.totalWeight, Nat.mul_pos d₁.total_pos d₂.total_pos⟩
theorem absDiff_probEvent_le_tvDist {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) (p : α → Bool) : RatProb.le (RatProb.absDiff (d₁.probEvent p) (d₂.probEvent p)) (tvDist d₁ d₂) := by
  unfold RatProb.le RatProb.absDiff tvDist FinDist.probEvent; dsimp only; apply Nat.mul_le_mul_right; let S := dedupList (d₁.support.map Prod.fst ++ d₂.support.map Prod.fst)
  change ((eventMass p d₁.support : Int) * d₂.totalWeight - (eventMass p d₂.support : Int) * d₁.totalWeight).natAbs ≤ sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) S
  have fwd : ∀ (q : α → Bool), eventMass q d₁.support * d₂.totalWeight - eventMass q d₂.support * d₁.totalWeight ≤
      sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) S := by
    intro q; rw [eventMass_eq_sumOver q S (nodup_dedupList _) d₁.support (fun a ha => mem_dedupList.2 (List.mem_append_left _ ha)),
        eventMass_eq_sumOver q S (nodup_dedupList _) d₂.support (fun a ha => mem_dedupList.2 (List.mem_append_right _ ha)),
        sumOver_mul_right, sumOver_mul_right]
    have aux : ∀ (ys : List α), sumOver (fun x => (if q x then massOf x d₁.support else 0) * d₂.totalWeight) ys - sumOver (fun x => (if q x then massOf x d₂.support else 0) * d₁.totalWeight) ys ≤
        sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) ys := by
      intro ys; induction ys with
      | nil => exact Nat.zero_le _ | cons x _ ih => dsimp only [sumOver]; cases q x <;> simp <;> omega
    exact aux S
  have hPos := fwd p; have hNeg := fwd (fun x => !p x)
  have hc₁ : eventMass (fun x => !p x) d₁.support * d₂.totalWeight + eventMass p d₁.support * d₂.totalWeight = d₁.totalWeight * d₂.totalWeight := by rw [← Nat.add_mul, Nat.add_comm, eventMass_compl]; rfl
  have hc₂ : eventMass (fun x => !p x) d₂.support * d₁.totalWeight + eventMass p d₂.support * d₁.totalWeight = d₂.totalWeight * d₁.totalWeight := by rw [← Nat.add_mul, Nat.add_comm, eventMass_compl]; rfl
  have hComm : d₁.totalWeight * d₂.totalWeight = d₂.totalWeight * d₁.totalWeight := Nat.mul_comm _ _; omega
theorem tvDist_eq_optEvent {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) : RatProb.eqv (tvDist d₁ d₂) (RatProb.absDiff (d₁.probEvent (optEvent d₁ d₂)) (d₂.probEvent (optEvent d₁ d₂))) := by
  apply RatProb.eqv_of_le_antisymm _ (absDiff_probEvent_le_tvDist d₁ d₂ (optEvent d₁ d₂))
  unfold RatProb.le tvDist RatProb.absDiff FinDist.probEvent; dsimp only; apply Nat.mul_le_mul_right; let S := dedupList (d₁.support.map Prod.fst ++ d₂.support.map Prod.fst)
  change sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) S ≤ ((eventMass (optEvent d₁ d₂) d₁.support : Int) * d₂.totalWeight -
     (eventMass (optEvent d₁ d₂) d₂.support : Int) * d₁.totalWeight).natAbs
  rw [eventMass_eq_sumOver (optEvent d₁ d₂) S (nodup_dedupList _) d₁.support (fun a ha => mem_dedupList.2 (List.mem_append_left _ ha)),
      eventMass_eq_sumOver (optEvent d₁ d₂) S (nodup_dedupList _) d₂.support (fun a ha => mem_dedupList.2 (List.mem_append_right _ ha))]
  have h1 := sumOver_mul_right (fun x => if optEvent d₁ d₂ x then massOf x d₁.support else 0) d₂.totalWeight S
  have h2 := sumOver_mul_right (fun x => if optEvent d₁ d₂ x then massOf x d₂.support else 0) d₁.totalWeight S
  have hExact : ∀ (ys : List α), sumOver (fun x => (if optEvent d₁ d₂ x then massOf x d₂.support else 0) * d₁.totalWeight) ys ≤
        sumOver (fun x => (if optEvent d₁ d₂ x then massOf x d₁.support else 0) * d₂.totalWeight) ys ∧
      sumOver (fun x => massOf x d₁.support * d₂.totalWeight - massOf x d₂.support * d₁.totalWeight) ys =
        sumOver (fun x => (if optEvent d₁ d₂ x then massOf x d₁.support else 0) * d₂.totalWeight) ys -
        sumOver (fun x => (if optEvent d₁ d₂ x then massOf x d₂.support else 0) * d₁.totalWeight) ys := by
    intro ys; induction ys with
    | nil => exact ⟨Nat.le_refl 0, rfl⟩
    | cons x _ ih =>
      obtain ⟨ihLe, ihEq⟩ := ih; simp only [sumOver]
      by_cases hLt : massOf x d₂.support * d₁.totalWeight < massOf x d₁.support * d₂.totalWeight
      · simp only [show optEvent d₁ d₂ x = true from decide_eq_true hLt, ↓reduceIte]; exact ⟨by omega, by omega⟩
      · simp only [show optEvent d₁ d₂ x = false from decide_eq_false hLt, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
        exact ⟨ihLe, by omega⟩
  obtain ⟨hLe, hEq⟩ := hExact S; rw [← h1, ← h2] at hLe hEq; omega
theorem tvDist_self_zero {α : Type} [DecidableEq α] (d : FinDist α) : (tvDist d d).num = 0 := by
  unfold tvDist; dsimp only; have hEq : (fun x => massOf x d.support * d.totalWeight - massOf x d.support * d.totalWeight) = (fun _ => 0) := (by funext _; simp); rw [hEq, sumOver_zero]
theorem tvDist_symm {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) : RatProb.eqv (tvDist d₁ d₂) (tvDist d₂ d₁) := RatProb.eqv_of_le_antisymm
    (RatProb.le_congr (RatProb.eqv_symm (tvDist_eq_optEvent d₁ d₂)) (RatProb.eqv_refl _)
      (RatProb.le_congr (RatProb.absDiff_symm _ _) (RatProb.eqv_refl _) (absDiff_probEvent_le_tvDist d₂ d₁ (optEvent d₁ d₂))))
    (RatProb.le_congr (RatProb.eqv_symm (tvDist_eq_optEvent d₂ d₁)) (RatProb.eqv_refl _)
      (RatProb.le_congr (RatProb.absDiff_symm _ _) (RatProb.eqv_refl _) (absDiff_probEvent_le_tvDist d₁ d₂ (optEvent d₂ d₁))))
theorem tvDist_triangle {α : Type} [DecidableEq α] (d₁ d₂ d₃ : FinDist α) : RatProb.le (tvDist d₁ d₃) (RatProb.add (tvDist d₁ d₂) (tvDist d₂ d₃)) :=
  let E := optEvent d₁ d₃
  RatProb.le_congr (RatProb.eqv_symm (tvDist_eq_optEvent d₁ d₃)) (RatProb.eqv_refl _)
    (RatProb.le_trans (RatProb.absDiff_triangle (d₁.probEvent E) (d₂.probEvent E) (d₃.probEvent E))
      (RatProb.add_le_add (absDiff_probEvent_le_tvDist d₁ d₂ E) (absDiff_probEvent_le_tvDist d₂ d₃ E)))
instance instObsMetricFinDist {α : Type} [DecidableEq α] : ObsMetric (FinDist α) RatSlack where
  dist d₁ d₂ := (tvDist d₁ d₂).toRatSlack
  dist_self d := by change (tvDist d d).toRatSlack.num * (0 : RatSlack).denInt ≤ 0 * (tvDist d d).toRatSlack.denInt; simp [RatProb.toRatSlack, tvDist_self_zero]
  dist_triangle d₁ d₂ d₃ := by rw [← RatProb.toRatSlack_add, RatProb.toRatSlack_le_iff]; exact tvDist_triangle d₁ d₂ d₃
theorem tvDist_map_le {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (d₁ d₂ : FinDist α) : RatProb.le (tvDist (d₁.map f) (d₂.map f)) (tvDist d₁ d₂) := by
  have hOpt := tvDist_eq_optEvent (d₁.map f) (d₂.map f); rw [FinDist.probEvent_map, FinDist.probEvent_map] at hOpt
  exact RatProb.le_congr (RatProb.eqv_symm hOpt) (RatProb.eqv_refl _) (absDiff_probEvent_le_tvDist d₁ d₂ (optEvent (d₁.map f) (d₂.map f) ∘ f))
theorem tvDist_of_equiv {α : Type} [DecidableEq α] {d₁ d₂ e₁ e₂ : FinDist α} (h₁ : FinDist.Equiv d₁ e₁) (h₂ : FinDist.Equiv d₂ e₂) : RatProb.eqv (tvDist d₁ d₂) (tvDist e₁ e₂) :=
  RatProb.eqv_of_le_antisymm (RatProb.le_congr (RatProb.eqv_symm (RatProb.eqv_trans (tvDist_eq_optEvent d₁ d₂)
      (RatProb.absDiff_eqv_congr (h₁ (optEvent d₁ d₂)) (h₂ (optEvent d₁ d₂))))) (RatProb.eqv_refl _) (absDiff_probEvent_le_tvDist e₁ e₂ (optEvent d₁ d₂)))
    (RatProb.le_congr (RatProb.eqv_symm (RatProb.eqv_trans (tvDist_eq_optEvent e₁ e₂)
      (RatProb.absDiff_eqv_congr (RatProb.eqv_symm (h₁ (optEvent e₁ e₂))) (RatProb.eqv_symm (h₂ (optEvent e₁ e₂))))))
      (RatProb.eqv_refl _) (absDiff_probEvent_le_tvDist d₁ d₂ (optEvent e₁ e₂)))
/-- **Fundamental Coupling / Bad-Event Lemma (`tvDist_le_of_bad_event`)**: If `bad = false` forces `x = y` on every positive-weight atom of `c`, then $\Delta(\pi_1(c), \pi_2(c)) \le \Pr_c[\text{Bad}]$. -/
theorem tvDist_le_of_bad_event {α : Type} [DecidableEq α] (c : FinDist ((α × α) × Bool)) (hAgree : ∀ x y b w, (((x, y), b), w) ∈ c.support → 0 < w → b = false → x = y) :
    RatProb.le (tvDist (c.map (fun p => p.1.1)) (c.map (fun p => p.1.2))) (c.probEvent Prod.snd) := by
  let E := optEvent (c.map (fun p => p.1.1)) (c.map (fun p => p.1.2)); have hOpt := tvDist_eq_optEvent (c.map (fun p => p.1.1)) (c.map (fun p => p.1.2))
  rw [FinDist.probEvent_map, FinDist.probEvent_map] at hOpt
  refine RatProb.le_congr (RatProb.eqv_symm hOpt) (RatProb.eqv_refl _) ?_
  unfold RatProb.le RatProb.absDiff FinDist.probEvent; dsimp only; change ((eventMass (E ∘ fun p => p.1.1) c.support : Int) * c.totalWeight -
          (eventMass (E ∘ fun p => p.1.2) c.support : Int) * c.totalWeight).natAbs * c.totalWeight ≤
    eventMass Prod.snd c.support * (c.totalWeight * c.totalWeight)
  have aux : ∀ (xs : List (((α × α) × Bool) × Nat)), (∀ x y b w, (((x, y), b), w) ∈ xs → 0 < w → b = false → x = y) →
      ((eventMass (E ∘ fun p => p.1.1) xs : Int) - (eventMass (E ∘ fun p => p.1.2) xs : Int)).natAbs ≤
        eventMass Prod.snd xs := by
    intro xs; induction xs with
    | nil => intros; exact Nat.zero_le 0
    | cons hd rest ih =>
      rcases hd with ⟨⟨⟨x, y⟩, b⟩, w⟩; intro hAg
      have ihR := ih (fun x' y' b' w' hm => hAg x' y' b' w' (List.mem_cons_of_mem _ hm)); simp only [eventMass, Function.comp_def] at ihR ⊢; rcases b with _ | _
      · by_cases hw : 0 < w
        · have hxy := hAg x y false w List.mem_cons_self hw rfl; subst hxy; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]; omega
        · have hw0 : w = 0 := by omega
          subst hw0; simp only [ite_self, Nat.zero_add]; omega
      · by_cases hex : E x = true <;> by_cases hey : E y = true <;> simp [hex, hey] <;> omega
  rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
  calc _ * c.totalWeight * c.totalWeight ≤ eventMass Prod.snd c.support * c.totalWeight * c.totalWeight := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (aux c.support hAgree))
    _ = eventMass Prod.snd c.support * (c.totalWeight * c.totalWeight) := by ac_rfl
theorem tvDist_bind_le_of_pointwise {α β : Type} [DecidableEq β] (d : FinDist α) (k₁ k₂ : α → FinDist β) (ε : RatProb) (hPt : ∀ a, RatProb.le (tvDist (k₁ a) (k₂ a)) ε) :
    RatProb.le (tvDist (d.bind k₁) (d.bind k₂)) ε := by
  let E := optEvent (d.bind k₁) (d.bind k₂)
  have hEv : ∀ a, RatProb.le (RatProb.absDiff ((k₁ a).probEvent E) ((k₂ a).probEvent E)) ε := fun a => RatProb.le_trans (absDiff_probEvent_le_tvDist (k₁ a) (k₂ a) E) (hPt a)
  refine RatProb.le_congr (RatProb.eqv_symm (tvDist_eq_optEvent (d.bind k₁) (d.bind k₂))) (RatProb.eqv_refl _) ?_
  unfold RatProb.le RatProb.absDiff FinDist.probEvent; dsimp only; change ((eventMass E (bindRaw d.support k₁).1 : Int) * (d.bind k₂).totalWeight -
          (eventMass E (bindRaw d.support k₂).1 : Int) * (d.bind k₁).totalWeight).natAbs * ε.den ≤
    ε.num * ((d.bind k₁).totalWeight * (d.bind k₂).totalWeight)
  rw [show (d.bind k₁).totalWeight = weightSum d.support * (bindRaw d.support k₁).2 from bindRaw_weightSum d.support k₁,
      show (d.bind k₂).totalWeight = weightSum d.support * (bindRaw d.support k₂).2 from bindRaw_weightSum d.support k₂]
  have aux : ∀ (zs : List (α × Nat)), ((eventMass E (bindRaw zs k₁).1 : Int) * ((bindRaw zs k₂).2 : Int) - (eventMass E (bindRaw zs k₂).1 : Int) * ((bindRaw zs k₁).2 : Int)).natAbs * ε.den ≤
      ε.num * (weightSum zs * (bindRaw zs k₁).2 * (bindRaw zs k₂).2) := by
    intro zs; induction zs with
    | nil => simp [bindRaw, eventMass, weightSum]
    | cons hd zs ih =>
      rcases hd with ⟨a, u⟩; have hPa := hEv a
      unfold RatProb.le RatProb.absDiff FinDist.probEvent at hPa; dsimp only at hPa; simp only [bindRaw, eventMass_append, eventMass_scaleSupport, weightSum]
      let A1 := eventMass E (k₁ a).support; let A2 := eventMass E (k₂ a).support; let B1 := eventMass E (bindRaw zs k₁).1; let B2 := eventMass E (bindRaw zs k₂).1
      let D1 := (bindRaw zs k₁).2; let D2 := (bindRaw zs k₂).2; let T1 := (k₁ a).totalWeight; let T2 := (k₂ a).totalWeight
      have hDec : ((u * D1 * A1 + T1 * B1 : Nat) : Int) * ((T2 * D2 : Nat) : Int) - ((u * D2 * A2 + T2 * B2 : Nat) : Int) * ((T1 * D1 : Nat) : Int) =
          ((u * D1 * D2 : Nat) : Int) * ((A1 : Int) * T2 - (A2 : Int) * T1) +
          ((T1 * T2 : Nat) : Int) * ((B1 : Int) * D2 - (B2 : Int) * D1) := by
        simp only [Int.natCast_add, Int.natCast_mul, Int.add_mul, Int.mul_sub]; have e1 : (u : Int) * D1 * A1 * (T2 * D2) = (u : Int) * D1 * D2 * (A1 * T2) := (by ac_rfl)
        have e2 : (u : Int) * D2 * A2 * (T1 * D1) = (u : Int) * D1 * D2 * (A2 * T1) := (by ac_rfl); have e3 : (T1 : Int) * B1 * (T2 * D2) = (T1 : Int) * T2 * (B1 * D2) := (by ac_rfl)
        have e4 : (T2 : Int) * B2 * (T1 * D1) = (T1 : Int) * T2 * (B2 * D1) := (by ac_rfl); rw [e1, e2, e3, e4]; omega
      have hTri := Int.natAbs_add_le (((u * D1 * D2 : Nat) : Int) * ((A1 : Int) * T2 - (A2 : Int) * T1))
        (((T1 * T2 : Nat) : Int) * ((B1 : Int) * D2 - (B2 : Int) * D1))
      rw [← hDec] at hTri; simp only [Int.natAbs_mul, Int.natAbs_natCast] at hTri; have hMul := Nat.mul_le_mul_right ε.den hTri; rw [Nat.add_mul] at hMul
      have h1 : u * D1 * D2 * ((A1 : Int) * T2 - (A2 : Int) * T1).natAbs * ε.den ≤ ε.num * (u * (T1 * D1) * (T2 * D2)) := by
        calc u * D1 * D2 * ((A1 : Int) * T2 - (A2 : Int) * T1).natAbs * ε.den = (((A1 : Int) * T2 - (A2 : Int) * T1).natAbs * ε.den) * (u * D1 * D2) := by ac_rfl
          _ ≤ (ε.num * (T1 * T2)) * (u * D1 * D2) := Nat.mul_le_mul_right _ hPa
          _ = ε.num * (u * (T1 * D1) * (T2 * D2)) := by ac_rfl
      have h2 : T1 * T2 * ((B1 : Int) * D2 - (B2 : Int) * D1).natAbs * ε.den ≤ ε.num * (weightSum zs * (T1 * D1) * (T2 * D2)) := by
        calc T1 * T2 * ((B1 : Int) * D2 - (B2 : Int) * D1).natAbs * ε.den = (((B1 : Int) * D2 - (B2 : Int) * D1).natAbs * ε.den) * (T1 * T2) := by ac_rfl
          _ ≤ (ε.num * (weightSum zs * D1 * D2)) * (T1 * T2) := Nat.mul_le_mul_right _ ih
          _ = ε.num * (weightSum zs * (T1 * D1) * (T2 * D2)) := by ac_rfl
      have hRhs : ε.num * (u * (T1 * D1) * (T2 * D2)) + ε.num * (weightSum zs * (T1 * D1) * (T2 * D2)) =
          ε.num * ((u + weightSum zs) * (T1 * D1) * (T2 * D2)) := by rw [← Nat.mul_add]; congr 1; rw [Nat.add_mul, Nat.add_mul]
      exact hRhs ▸ Nat.le_trans hMul (Nat.add_le_add h1 h2)
  have hFac : (eventMass E (bindRaw d.support k₁).1 : Int) * ((weightSum d.support * (bindRaw d.support k₂).2 : Nat) : Int) -
      (eventMass E (bindRaw d.support k₂).1 : Int) * ((weightSum d.support * (bindRaw d.support k₁).2 : Nat) : Int) =
      (weightSum d.support : Int) * ((eventMass E (bindRaw d.support k₁).1 : Int) * ((bindRaw d.support k₂).2 : Int) -
         (eventMass E (bindRaw d.support k₂).1 : Int) * ((bindRaw d.support k₁).2 : Int)) := by
    rw [Int.natCast_mul, Int.natCast_mul, Int.mul_sub]; congr 1 <;> ac_rfl
  rw [hFac, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_assoc]
  calc weightSum d.support * (_ * ε.den)
    _ ≤ weightSum d.support * (ε.num * (weightSum d.support * (bindRaw d.support k₁).2 * (bindRaw d.support k₂).2)) := Nat.mul_le_mul_left _ (aux d.support)
    _ = ε.num * (weightSum d.support * (bindRaw d.support k₁).2 * (weightSum d.support * (bindRaw d.support k₂).2)) := by ac_rfl
private theorem prod_comm_equiv {α β : Type} (d₁ : FinDist α) (d₂ : FinDist β) : FinDist.Equiv (FinDist.prod d₁ d₂) ((FinDist.prod d₂ d₁).map (fun p => (p.2, p.1))) := by
  intro p; rw [FinDist.probEvent_map]
  have constBind : ∀ {γ δ : Type} (u : FinDist γ) (v : FinDist δ) (q : (γ × δ) → Bool), (bindRaw u.support (fun a => v.map (fun b => (a, b)))).2 = v.totalWeight ^ u.support.length ∧
      eventMass q (bindRaw u.support (fun a => v.map (fun b => (a, b)))).1 =
        (v.totalWeight ^ (u.support.length - 1)) * expectMass (fun a => eventMass (fun b => q (a, b)) v.support) u.support := by
    intro γ δ u v q; have aux : ∀ (ys : List (γ × Nat)), ys ≠ [] → (bindRaw ys (fun a => v.map (fun b => (a, b)))).2 = v.totalWeight ^ ys.length ∧ eventMass q (bindRaw ys (fun a => v.map (fun b => (a, b)))).1 =
          (v.totalWeight ^ (ys.length - 1)) * expectMass (fun a => eventMass (fun b => q (a, b)) v.support) ys := by
      intro ys; induction ys with
      | nil => intro hne; exact False.elim (hne rfl)
      | cons hd tl ih =>
        rcases hd with ⟨a, w⟩; intro _
        have hWMap : (v.map (fun b => (a, b))).totalWeight = v.totalWeight := FinDist.weightSum_map _ _
        have hEMap : eventMass q (v.map (fun b => (a, b))).support = eventMass (fun b => q (a, b)) v.support := FinDist.eventMass_map _ _ _
        by_cases hTl : tl = []
        · subst hTl
          simp only [bindRaw, scaleSupport, List.append_nil, List.length_singleton, Nat.sub_self, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, eventMass_scaleSupport, expectMass, Nat.add_zero]
          exact ⟨hWMap, by rw [hEMap]; exact Nat.mul_comm _ _⟩
        · obtain ⟨ihD, ihE⟩ := ih hTl; have hLenTl : 1 ≤ tl.length := length_pos_of_ne_nil hTl
          have hPowTl : v.totalWeight ^ tl.length = v.totalWeight * v.totalWeight ^ (tl.length - 1) := (by conv => lhs; rw [← Nat.sub_add_cancel hLenTl, Nat.pow_succ]; rw [Nat.mul_comm])
          simp only [List.length_cons, Nat.add_sub_cancel, bindRaw, hWMap, ihD, eventMass_append, eventMass_scaleSupport, hEMap, ihE, expectMass]
          refine ⟨by rw [Nat.pow_succ]; ac_rfl, ?_⟩
          rw [hPowTl, Nat.mul_add]; congr 1 <;> ac_rfl
    exact aux u.support (fun h => by have hp := u.total_pos; rw [h] at hp; simp [weightSum] at hp)
  obtain ⟨hD1, hE1⟩ := constBind d₁ d₂ p; obtain ⟨hD2, hE2⟩ := constBind d₂ d₁ (p ∘ fun q => (q.2, q.1))
  have hFub : ∀ (ys : List (α × Nat)) (zs : List (β × Nat)), expectMass (fun a => eventMass (fun b => p (a, b)) zs) ys = expectMass (fun b => eventMass (fun a => p (a, b)) ys) zs := by
    intro ys zs; induction ys with
    | nil =>
      have hz0 : ∀ (l : List (β × Nat)), expectMass (fun _ => 0) l = 0 := by
        intro l; induction l with | nil => rfl | cons _ _ ihL => simp [expectMass, ihL]
      simpa [expectMass, eventMass] using (hz0 zs).symm
    | cons hd ys ih =>
      rcases hd with ⟨a, w⟩
      have hAdd : ∀ (l : List (β × Nat)), expectMass (fun b => (if p (a, b) then w else 0) + eventMass (fun a' => p (a', b)) ys) l =
          eventMass (fun b => p (a, b)) l * w + expectMass (fun b => eventMass (fun a' => p (a', b)) ys) l := by
        intro l; induction l with
        | nil => simp [expectMass, eventMass]
        | cons hdl _ ihL =>
          rcases hdl with ⟨b, u⟩; simp only [expectMass, eventMass, ihL, Nat.add_mul]
          by_cases hpab : p (a, b) = true <;> simp [hpab, Nat.mul_comm w u] <;> omega
      simp [expectMass, eventMass, ih, hAdd zs]
  unfold FinDist.prod FinDist.probEvent RatProb.eqv; change eventMass p (bindRaw d₁.support (fun a => d₂.map (fun b => (a, b)))).1 *
      (d₂.bind (fun a => d₁.map (fun b => (a, b)))).totalWeight =
    eventMass (p ∘ fun q => (q.2, q.1)) (bindRaw d₂.support (fun a => d₁.map (fun b => (a, b)))).1 *
      (d₁.bind (fun a => d₂.map (fun b => (a, b)))).totalWeight
  rw [show (d₁.bind (fun a => d₂.map (fun b => (a, b)))).totalWeight = d₁.totalWeight * (bindRaw d₁.support (fun a => d₂.map (fun b => (a, b)))).2 from bindRaw_weightSum _ _,
      show (d₂.bind (fun a => d₁.map (fun b => (a, b)))).totalWeight = d₂.totalWeight * (bindRaw d₂.support (fun a => d₁.map (fun b => (a, b)))).2 from bindRaw_weightSum _ _,
      hD1, hD2, hE1, hE2]
  dsimp only [Function.comp_def]; rw [hFub d₁.support d₂.support]
  have hne1 : 1 ≤ d₁.support.length := by
    cases h : d₁.support with | nil => have hp := d₁.total_pos; rw [h] at hp; simp [weightSum] at hp | cons _ _ => simp
  have hne2 : 1 ≤ d₂.support.length := by
    cases h : d₂.support with | nil => have hp := d₂.total_pos; rw [h] at hp; simp [weightSum] at hp | cons _ _ => simp
  have hp1 : d₂.totalWeight ^ d₁.support.length = d₂.totalWeight * d₂.totalWeight ^ (d₁.support.length - 1) := (by conv => lhs; rw [← Nat.sub_add_cancel hne1, Nat.pow_succ]; rw [Nat.mul_comm])
  have hp2 : d₁.totalWeight ^ d₂.support.length = d₁.totalWeight * d₁.totalWeight ^ (d₂.support.length - 1) := (by conv => lhs; rw [← Nat.sub_add_cancel hne2, Nat.pow_succ]; rw [Nat.mul_comm])
  rw [hp1, hp2]; ac_rfl
theorem tvDist_prod_le {α β : Type} [DecidableEq α] [DecidableEq β] (d₁ e₁ : FinDist α) (d₂ e₂ : FinDist β) :
    RatProb.le (tvDist (FinDist.prod d₁ d₂) (FinDist.prod e₁ e₂)) (RatProb.add (tvDist d₁ e₁) (tvDist d₂ e₂)) := by
  have rightFor : ∀ {γ δ : Type} [DecidableEq γ] [DecidableEq δ] (u : FinDist γ) (v₁ v₂ : FinDist δ), RatProb.le (tvDist (FinDist.prod u v₁) (FinDist.prod u v₂)) (tvDist v₁ v₂) :=
    fun u v₁ v₂ => tvDist_bind_le_of_pointwise u (fun a => v₁.map (fun b => (a, b)))
      (fun a => v₂.map (fun b => (a, b))) (tvDist v₁ v₂) (fun a => tvDist_map_le (fun b => (a, b)) v₁ v₂)
  have leftStep : RatProb.le (tvDist (FinDist.prod d₁ d₂) (FinDist.prod e₁ d₂)) (tvDist d₁ e₁) :=
    RatProb.le_congr (RatProb.eqv_symm (tvDist_of_equiv (prod_comm_equiv d₁ d₂) (prod_comm_equiv e₁ d₂))) (RatProb.eqv_refl (tvDist d₁ e₁))
      (RatProb.le_trans (tvDist_map_le (fun p : β × α => (p.2, p.1)) (FinDist.prod d₂ d₁) (FinDist.prod d₂ e₁)) (rightFor d₂ d₁ e₁))
  exact RatProb.le_trans (tvDist_triangle (FinDist.prod d₁ d₂) (FinDist.prod e₁ d₂) (FinDist.prod e₁ e₂)) (RatProb.add_le_add leftStep (rightFor e₁ d₂ e₂))
private theorem eventMass_const {β : Type} (b : Bool) (zs : List (β × Nat)) : eventMass (fun _ => b) zs = (if b then 1 else 0) * weightSum zs := by
  induction zs with | nil => simp [eventMass, weightSum] | cons _ _ ih => simp only [eventMass, weightSum, ih]; cases b <;> simp
theorem prod_fst_equiv {α β : Type} (d₁ : FinDist α) (d₂ : FinDist β) : FinDist.Equiv ((FinDist.prod d₁ d₂).map Prod.fst) d₁ := by
  intro p; rw [FinDist.probEvent_map]; unfold FinDist.prod
  have hPt : ∀ a, RatProb.eqv ((d₂.map (fun b => (a, b))).probEvent (p ∘ Prod.fst)) ((FinDist.pure a).probEvent p) := by
    intro a; rw [FinDist.probEvent_map]; unfold FinDist.pure FinDist.probEvent FinDist.totalWeight RatProb.eqv; dsimp only [Function.comp_def]; rw [eventMass_const (p a) d₂.support]; simp [eventMass, weightSum]
  exact RatProb.eqv_trans (RatProb.eqv_of_le_antisymm
      (probEvent_bind_mono d₁ _ FinDist.pure (p ∘ Prod.fst) p (fun a _ _ => RatProb.le_of_eqv (hPt a)))
      (probEvent_bind_mono d₁ FinDist.pure _ p (p ∘ Prod.fst) (fun a _ _ => RatProb.le_of_eqv (RatProb.eqv_symm (hPt a)))))
    (FinDist.bind_pure_right d₁ p)
theorem prod_snd_equiv {α β : Type} (d₁ : FinDist α) (d₂ : FinDist β) : FinDist.Equiv ((FinDist.prod d₁ d₂).map Prod.snd) d₂ := by
  intro p; rw [FinDist.probEvent_map]; have h1 := prod_comm_equiv d₁ d₂ (p ∘ Prod.snd); rw [FinDist.probEvent_map] at h1; have h2 := prod_fst_equiv d₂ d₁ p; rw [FinDist.probEvent_map] at h2
  exact RatProb.eqv_trans h1 h2
theorem tvDist_le_one {α : Type} [DecidableEq α] (d₁ d₂ : FinDist α) : RatProb.le (tvDist d₁ d₂) RatProb.one := by
  refine RatProb.le_congr (RatProb.eqv_symm (tvDist_eq_optEvent d₁ d₂)) (RatProb.eqv_refl RatProb.one) ?_
  unfold RatProb.le RatProb.absDiff FinDist.probEvent RatProb.one FinDist.totalWeight; dsimp only; have h1 := Nat.mul_le_mul_right (weightSum d₂.support) (eventMass_le_weightSum (optEvent d₁ d₂) d₁.support)
  have h2 := Nat.mul_le_mul_right (weightSum d₁.support) (eventMass_le_weightSum (optEvent d₁ d₂) d₂.support)
  have hComm : weightSum d₂.support * weightSum d₁.support = weightSum d₁.support * weightSum d₂.support := Nat.mul_comm _ _; omega
/-! ### Uniform Interval Smudging / Rejection Distance Bound -/
def uniformIntervalDist (B : Nat) : FinDist Int :=
  FinDist.map (fun i : Nat => (i : Int) - (B : Int)) (FinDist.uniform (List.range (2 * B + 1)) (by simp))
private theorem list_range_add (a b : Nat) : List.range (a + b) = List.range a ++ (List.range b).map (a + ·) := by
  induction b with | zero => simp | succ b ih => rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
private def cycShift (N k i : Nat) : Nat := if i < N - k then i + k else i - (N - k)
private theorem uniform_cycShift_equiv (N k : Nat) (hN : 0 < N) (hk : k ≤ N) : FinDist.Equiv (FinDist.map (cycShift N k) (FinDist.uniform (List.range N) (range_ne_nil hN)))
      (FinDist.uniform (List.range N) (range_ne_nil hN)) := by
  intro p; rw [FinDist.probEvent_map]; unfold FinDist.uniform FinDist.probEvent FinDist.totalWeight RatProb.eqv; dsimp only
  rw [uniform_weightSum, uniform_eventMass, uniform_eventMass]; apply congrArg (· * (List.range N).length)
  have hSp1 : List.range N = List.range (N - k) ++ (List.range k).map ((N - k) + ·) := by simpa [show (N - k) + k = N by omega] using list_range_add (N - k) k
  have hSp2 : List.range N = List.range k ++ (List.range (N - k)).map (k + ·) := by simpa [show k + (N - k) = N by omega] using list_range_add k (N - k)
  have hM1 : ∀ (m : Nat), m ≤ N - k → ((List.range m).filter (p ∘ cycShift N k)).length = (((List.range m).map (k + ·)).filter p).length := by
    intro m; induction m with
    | zero => intros; rfl
    | succ m ih =>
      intro hm
      have hCyc : cycShift N k m = k + m := by unfold cycShift; rw [ite_eq_left_iff.2 (fun h => False.elim (h (by omega)))]; omega
      rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append, List.filter_append, List.length_append, List.length_append, ih (by omega)]
      congr 1; simp only [List.filter, Function.comp_def, hCyc]; cases p (k + m) <;> rfl
  have hM2 : ∀ (m : Nat), (((List.range m).map ((N - k) + ·)).filter (p ∘ cycShift N k)).length = ((List.range m).filter p).length := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      have hCyc : cycShift N k ((N - k) + m) = m := by unfold cycShift; rw [ite_eq_right_iff.2 (fun h => False.elim ((by omega : ¬ (N - k + m < N - k)) h))]; omega
      rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append, List.filter_append, List.length_append, List.length_append, ih]
      congr 1; simp only [List.filter, Function.comp_def, hCyc]; cases p m <;> rfl
  conv => lhs; rw [hSp1]
  conv => rhs; rw [hSp2]
  rw [List.filter_append, List.filter_append, List.length_append, List.length_append, hM1 (N - k) (Nat.le_refl _), hM2 k, Nat.add_comm]
/-- **Exact Statistical Smudging Lemma (`uniformShift_tvDist_le`)**: Shifting $u \leftarrow U([-B, B])$ by $e \in \mathbb{Z}$ incurs `tvDist` $\le |e| / (2B + 1)$. -/
theorem uniformShift_tvDist_le (e : Int) (B : Nat) : RatProb.le (tvDist ((uniformIntervalDist B).map (fun u => e + u)) (uniformIntervalDist B)) ⟨e.natAbs, 2 * B + 1, by omega⟩ := by
  let N := 2 * B + 1; have hN : 0 < N := by omega
  by_cases hk : e.natAbs ≤ N
  · let base : FinDist Nat := FinDist.uniform (List.range N) (range_ne_nil hN); let k := e.natAbs; let shiftAmt := if 0 ≤ e then k else N - k
    let badPred : Nat → Bool := fun i => if 0 ≤ e then decide (N - k ≤ i) else decide (i < k); let c := base.map (fun i : Nat =>
      (((e + ((i : Int) - (B : Int)), (((cycShift N shiftAmt i : Nat) : Int) - (B : Int))), badPred i)))
    have hCoup := tvDist_le_of_bad_event c (by
      intro x y b w hMem _ hb
      rcases List.mem_map.1 hMem with ⟨⟨i, _⟩, hIn, hEq⟩
      rcases List.mem_map.1 hIn with ⟨j, hjR, hP0⟩; injection hP0 with hjE _; subst hjE
      have _ : j < N := List.mem_range.1 hjR; injection hEq with hPair _; injection hPair with hXY hBad; injection hXY with hx hy; subst hx hy; dsimp only [badPred, shiftAmt] at hBad ⊢
      by_cases hNonneg : 0 ≤ e
      · simp only [hNonneg, ↓reduceIte] at hBad ⊢; have hLt : j < N - k := (by have := of_decide_eq_false (hBad.trans hb); omega); have hek : e = (k : Int) := (Int.natAbs_of_nonneg hNonneg).symm
        unfold cycShift; simp only [hLt, ↓reduceIte, hek]; omega
      · simp only [hNonneg, ↓reduceIte] at hBad ⊢; have _ : k ≤ j := (by have := of_decide_eq_false (hBad.trans hb); omega); have hek : e = -(k : Int) := (by omega)
        have hNotLt : ¬ (j < N - (N - k)) := (by omega); unfold cycShift; simp only [hNotLt, ↓reduceIte, hek]; omega)
    have hM1 : c.map (fun p => p.1.1) = (uniformIntervalDist B).map (fun u => e + u) := by dsimp only [c, base, uniformIntervalDist, FinDist.map, FinDist.uniform, N]; simp [List.map_map, Function.comp_def]
    have hM2 : FinDist.Equiv (c.map (fun p => p.1.2)) (uniformIntervalDist B) := by
      intro p; have hSA : shiftAmt ≤ N := by dsimp [shiftAmt]; split <;> omega
      have hS := uniform_cycShift_equiv N shiftAmt hN hSA (p ∘ fun j : Nat => (j : Int) - (B : Int)); dsimp only [c, base, uniformIntervalDist, N]
      rw [FinDist.probEvent_map, FinDist.probEvent_map, FinDist.probEvent_map]; rw [FinDist.probEvent_map] at hS; exact hS
    have hBad : RatProb.le (c.probEvent Prod.snd) ⟨k, N, hN⟩ := by
      rw [FinDist.probEvent_map]; unfold base FinDist.uniform FinDist.probEvent FinDist.totalWeight RatProb.le; dsimp only [Function.comp_def]; rw [uniform_weightSum, uniform_eventMass, List.length_range]
      apply Nat.mul_le_mul_right
      by_cases hNonneg : 0 ≤ e
      · have hEqF : (fun x : Nat => badPred x) = (fun i => decide (N - k ≤ i)) := by funext i; dsimp [badPred]; simp [hNonneg]
        rw [hEqF, show List.range N = List.range (N - k) ++ (List.range k).map ((N - k) + ·) by simpa [show (N - k) + k = N by omega] using list_range_add (N - k) k, List.filter_append]
        have hZ : ∀ (m : Nat), m ≤ N - k → (List.range m).filter (fun i => decide (N - k ≤ i)) = [] := by
          intro m; induction m with
          | zero => intros; rfl
          | succ m ih =>
            intro hm; rw [List.range_succ, List.filter_append, ih (by omega), List.nil_append]; have hf : decide (N - k ≤ m) = false := decide_eq_false (by omega); dsimp only [List.filter]; rw [hf]
        rw [hZ (N - k) (Nat.le_refl _), List.nil_append]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      · have hEqF : (fun x : Nat => badPred x) = (fun i => decide (i < k)) := by funext i; dsimp [badPred]; simp [hNonneg]
        rw [hEqF, show List.range N = List.range k ++ (List.range (N - k)).map (k + ·) by simpa [show k + (N - k) = N by omega] using list_range_add k (N - k), List.filter_append]
        have hZ : ∀ (m : Nat), ((List.range m).map (k + ·)).filter (fun i => decide (i < k)) = [] := by
          intro m; induction m with
          | zero => rfl
          | succ m ih => rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append, ih, List.filter]; simp [decide_eq_false (by omega : ¬ (k + m < k))]
        rw [hZ (N - k), List.append_nil]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    rw [hM1] at hCoup; exact RatProb.le_trans (RatProb.le_congr (tvDist_of_equiv (fun _ => RatProb.eqv_refl _) hM2) (RatProb.eqv_refl _) hCoup) hBad
  · exact RatProb.le_trans (tvDist_le_one _ _) (by unfold RatProb.le RatProb.one; dsimp; omega)
def uniformVecDist (B : Nat) : Nat → FinDist (List Int)
  | 0 => FinDist.pure []
  | m + 1 => (FinDist.prod (uniformIntervalDist B) (uniformVecDist B m)).map (fun q => q.1 :: q.2)
theorem uniformVecShift_tvDist_le (B E : Nat) (v : List Int) (hBnd : ∀ x ∈ v, x.natAbs ≤ E) : RatProb.le
      (tvDist ((uniformVecDist B v.length).map (fun us => List.zipWith (· + ·) v us)) (uniformVecDist B v.length))
      ⟨v.length * E, 2 * B + 1, by omega⟩ := by
  induction v with
  | nil =>
    unfold uniformVecDist FinDist.map FinDist.pure; simp only [List.length_nil, Nat.zero_mul]; have h0 := tvDist_self_zero (FinDist.pure ([] : List Int))
    change RatProb.le (tvDist (FinDist.pure []) (FinDist.pure [])) _; unfold RatProb.le; rw [h0]; simp
  | cons x xs ih =>
    have hx : x.natAbs ≤ E := hBnd x List.mem_cons_self; have ihX := ih (fun y hy => hBnd y (List.mem_cons_of_mem _ hy)); let dHead := (uniformIntervalDist B).map (fun u => x + u)
    let dTail := (uniformVecDist B xs.length).map (fun us => List.zipWith (· + ·) xs us); let consFn : Int × List Int → List Int := fun q => q.1 :: q.2
    have hProdEq : FinDist.Equiv ((uniformVecDist B (x :: xs).length).map (fun us => List.zipWith (· + ·) (x :: xs) us)) ((FinDist.prod dHead dTail).map consFn) := by
      intro p; simp only [List.length_cons, uniformVecDist, FinDist.probEvent_map]; unfold FinDist.prod dHead; rw [bind_map_eq]
      have hPt : ∀ a, (((uniformVecDist B xs.length).map (fun b => (a, b))).probEvent ((p ∘ fun us => List.zipWith (· + ·) (x :: xs) us) ∘ consFn)) =
          ((dTail.map (fun b' => (x + a, b'))).probEvent (p ∘ consFn)) := fun a => by
        dsimp only [dTail]; rw [FinDist.probEvent_map, FinDist.probEvent_map, FinDist.probEvent_map]; rfl
      exact RatProb.eqv_of_le_antisymm
        (probEvent_bind_mono _ _ _ _ _ (fun a _ _ => by rw [hPt a]; exact RatProb.le_refl _))
        (probEvent_bind_mono _ _ _ _ _ (fun a _ _ => by rw [hPt a]; exact RatProb.le_refl _))
    have hHeadBnd : RatProb.le (tvDist dHead (uniformIntervalDist B)) ⟨E, 2 * B + 1, by omega⟩ :=
      RatProb.le_trans (uniformShift_tvDist_le x B) (by unfold RatProb.le; dsimp; exact Nat.mul_le_mul_right _ hx)
    have hComb : RatProb.le (RatProb.add ⟨E, 2 * B + 1, by omega⟩ ⟨xs.length * E, 2 * B + 1, by omega⟩) ⟨(x :: xs).length * E, 2 * B + 1, by omega⟩ := by
      unfold RatProb.le RatProb.add; dsimp only [List.length_cons]; rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.add_comm (xs.length * E * _)]
      apply Nat.le_of_eq; congr 1 <;> ac_rfl
    exact RatProb.le_congr (RatProb.eqv_symm (tvDist_of_equiv hProdEq (fun _ => RatProb.eqv_refl _))) (RatProb.eqv_refl _)
      (RatProb.le_trans (tvDist_map_le consFn (FinDist.prod dHead dTail) (FinDist.prod (uniformIntervalDist B) (uniformVecDist B xs.length)))
        (RatProb.le_trans (tvDist_prod_le dHead (uniformIntervalDist B) dTail (uniformVecDist B xs.length)) (RatProb.le_trans (RatProb.add_le_add hHeadBnd ihX) hComb)))
/-! ## 3. Coin-Counting Games, Stateful Packages & Maurer Resource Converters -/
private theorem nodup_append_disjoint {α : Type} {xs ys : List α} (hx : xs.Nodup) (hy : ys.Nodup) (hDisj : ∀ a, a ∈ xs → a ∈ ys → False) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x _ ih =>
    rcases hx with _ | ⟨hNotX, hxR⟩
    refine .cons (fun b hb hxb => ?_) (ih hxR (fun a ha => hDisj a (List.mem_cons_of_mem _ ha)))
    rcases List.mem_append.1 hb with hbX | hbY
    · exact hNotX b hbX hxb
    · exact hDisj x List.mem_cons_self (hxb ▸ hbY)
def bitVecEnum : (n : Nat) → List (BitVec n)
  | 0 => [0#0]
  | n + 1 => (bitVecEnum n).map (BitVec.cons false) ++ (bitVecEnum n).map (BitVec.cons true)
theorem bitVecEnum_length (n : Nat) : (bitVecEnum n).length = 2 ^ n := by
  induction n with | zero => rfl | succ n ih => simp [bitVecEnum, ih, Nat.pow_succ]; omega
theorem bitVecEnum_ne_nil (n : Nat) : bitVecEnum n ≠ [] := by intro h; have hL := bitVecEnum_length n; rw [h] at hL; have : 0 < 2 ^ n := Nat.pow_pos (by decide); simp at hL; omega
private theorem bitVec_cons_inj {n : Nat} {b₁ b₂ : Bool} {v₁ v₂ : BitVec n} (h : BitVec.cons b₁ v₁ = BitVec.cons b₂ v₂) : b₁ = b₂ ∧ v₁ = v₂ := by
  have hMsb := congrArg BitVec.msb h; simp only [BitVec.msb_cons] at hMsb; subst hMsb
  exact ⟨rfl, by simpa [BitVec.setWidth_cons] using congrArg (BitVec.setWidth n) h⟩
theorem bitVecEnum_nodup (n : Nat) : (bitVecEnum n).Nodup := by
  induction n with
  | zero => simp [bitVecEnum]
  | succ n ih =>
    simp only [bitVecEnum]
    have hMap : ∀ (b : Bool) (xs : List (BitVec n)), xs.Nodup → (xs.map (BitVec.cons b)).Nodup := by
      intro b xs; induction xs with
      | nil => intros; exact .nil
      | cons _ _ ihX =>
        intro hNd; rcases hNd with _ | ⟨hNot, hNdR⟩
        refine .cons (fun y hy hEq => ?_) (ihX hNdR)
        rcases List.mem_map.1 hy with ⟨x', hx', rfl⟩; exact hNot x' hx' (bitVec_cons_inj hEq).2
    refine nodup_append_disjoint (hMap false _ ih) (hMap true _ ih) (fun _ hu1 hu2 => ?_)
    rcases List.mem_map.1 hu1 with ⟨_, _, rfl⟩; rcases List.mem_map.1 hu2 with ⟨_, _, hEq⟩
    cases (bitVec_cons_inj hEq.symm).1
structure FiniteGame (coinBits : Nat) where
  win : BitVec coinBits → Bool
def FiniteGame.toFinDist {b : Nat} (G : FiniteGame b) : FinDist Bool := (FinDist.uniform (bitVecEnum b) (bitVecEnum_ne_nil b)).map G.win
def FiniteGame.winCount {b : Nat} (G : FiniteGame b) : Nat := ((bitVecEnum b).filter G.win).length
theorem FiniteGame.probWin_eq {b : Nat} (G : FiniteGame b) : G.toFinDist.probEvent id = ⟨G.winCount, 2 ^ b, Nat.pow_pos (by decide)⟩ := by
  unfold toFinDist winCount; rw [FinDist.probEvent_map]; unfold FinDist.uniform FinDist.probEvent FinDist.totalWeight
  dsimp only [Function.comp_def]; simp [uniform_eventMass, uniform_weightSum, bitVecEnum_length]
structure CryptoPackage (State Q R : Type) where
  init : State
  step : State → Q → FinDist (R × State)
def CryptoPackage.toDistStepSystem {State Q R : Type} (pkg : CryptoPackage State Q R) : StepSystem (FinDist (Option R × State)) Q (FinDist (Option R)) := StepSystem.ofDet
    (fun d q => d.bind (fun (_, st) => (pkg.step st q).map (fun (r, st') => (some r, st'))))
    (fun d => d.map Prod.fst)
inductive QueryProg (Q R Out : Type) : Nat → Type where
  | ret : ∀ {q : Nat}, Out → QueryProg Q R Out q
  | query : ∀ {q : Nat}, Q → (R → QueryProg Q R Out q) → QueryProg Q R Out (q + 1)
def runProg {State Q R Out : Type} (pkg : CryptoPackage State Q R) : ∀ {q : Nat}, QueryProg Q R Out q → State → FinDist (Out × State)
  | _, .ret out, st => FinDist.pure (out, st)
  | _, .query x k, st => (pkg.step st x).bind (fun (r, st') => runProg pkg (k r) st')
def evalGame {State Q R Out : Type} (pkg : CryptoPackage State Q R) {q : Nat} (adv : QueryProg Q R Out q) : FinDist Out := (runProg pkg adv pkg.init).map Prod.fst
def gameAdv {S₀ S₁ Q R : Type} (G₀ : CryptoPackage S₀ Q R) (G₁ : CryptoPackage S₁ Q R) {q : Nat} (adv : QueryProg Q R Bool q) : RatProb :=
  RatProb.absDiff ((evalGame G₀ adv).probEvent id) ((evalGame G₁ adv).probEvent id)
theorem adv_triangle {S₀ S₁ S₂ Q R : Type} (G₀ : CryptoPackage S₀ Q R) (G₁ : CryptoPackage S₁ Q R) (G₂ : CryptoPackage S₂ Q R) {q : Nat} (adv : QueryProg Q R Bool q) :
    RatProb.le (gameAdv G₀ G₂ adv) (RatProb.add (gameAdv G₀ G₁ adv) (gameAdv G₁ G₂ adv)) :=
  RatProb.absDiff_triangle _ _ _
theorem gameAdv_le_tvDist {S₀ S₁ Q R : Type} (G₀ : CryptoPackage S₀ Q R) (G₁ : CryptoPackage S₁ Q R) {q : Nat} (adv : QueryProg Q R Bool q) :
    RatProb.le (gameAdv G₀ G₁ adv) (tvDist (evalGame G₀ adv) (evalGame G₁ adv)) :=
  absDiff_probEvent_le_tvDist _ _ id
structure Converter (CState Q₁ R₁ Q₀ R₀ : Type) where
  init : CState
  onQuery : CState → Q₁ → Q₀ × (R₀ → R₁ × CState)
def attachConverter {CState State Q₁ R₁ Q₀ R₀ : Type} (conv : Converter CState Q₁ R₁ Q₀ R₀) (pkg : CryptoPackage State Q₀ R₀) : CryptoPackage (CState × State) Q₁ R₁ where
  init := (conv.init, pkg.init)
  step := fun (cst, st) q₁ =>
    let (q₀, post) := conv.onQuery cst q₁
    (pkg.step st q₀).map (fun (r₀, st') => let (r₁, cst') := post r₀; (r₁, (cst', st')))
def pullbackAdv {CState Q₁ R₁ Q₀ R₀ Out : Type} (conv : Converter CState Q₁ R₁ Q₀ R₀) : ∀ {q : Nat}, CState → QueryProg Q₁ R₁ Out q → QueryProg Q₀ R₀ Out q
  | _, _, .ret out => .ret out
  | _, cst, .query q₁ k =>
    let (q₀, post) := conv.onQuery cst q₁
    .query q₀ (fun r₀ => let (r₁, cst') := post r₀; pullbackAdv conv cst' (k r₁))
private theorem runProg_attachConverter_equiv {CState State Q₁ R₁ Q₀ R₀ Out : Type} (conv : Converter CState Q₁ R₁ Q₀ R₀) (pkg : CryptoPackage State Q₀ R₀) :
    ∀ {q : Nat} (adv : QueryProg Q₁ R₁ Out q) (cst : CState) (st : State),
      FinDist.Equiv ((runProg (attachConverter conv pkg) adv (cst, st)).map Prod.fst)
        ((runProg pkg (pullbackAdv conv cst adv) st).map Prod.fst)
  | _, .ret _, _, _ => fun _ => RatProb.eqv_refl _
  | _, .query q₁ k, cst, st => by
    intro p; rw [FinDist.probEvent_map, FinDist.probEvent_map]; let stepRes := conv.onQuery cst q₁; let fMap : R₀ × State → R₁ × CState × State := fun rs => let rc := stepRes.2 rs.1; (rc.1, (rc.2, rs.2))
    have hL : runProg (attachConverter conv pkg) (.query q₁ k) (cst, st) = ((pkg.step st stepRes.1).map fMap).bind (fun rcs => runProg (attachConverter conv pkg) (k rcs.1) rcs.2) := rfl
    have hR : runProg pkg (pullbackAdv conv cst (.query q₁ k)) st = (pkg.step st stepRes.1).bind (fun rs => let rc := stepRes.2 rs.1; runProg pkg (pullbackAdv conv rc.2 (k rc.1)) rs.2) := rfl
    rw [hL, hR, bind_map_eq]
    have hSub : ∀ (rs : R₀ × State), ((runProg (attachConverter conv pkg) (k (stepRes.2 rs.1).1) ((stepRes.2 rs.1).2, rs.2)).probEvent (p ∘ Prod.fst)).eqv
        ((runProg pkg (pullbackAdv conv (stepRes.2 rs.1).2 (k (stepRes.2 rs.1).1)) rs.2).probEvent (p ∘ Prod.fst)) := by
      intro rs
      have ih := runProg_attachConverter_equiv conv pkg (k (stepRes.2 rs.1).1) (stepRes.2 rs.1).2 rs.2 p; rw [FinDist.probEvent_map, FinDist.probEvent_map] at ih; exact ih
    exact RatProb.eqv_of_le_antisymm (probEvent_bind_mono _ _ _ _ _ (fun rs _ _ => RatProb.le_of_eqv (hSub rs))) (probEvent_bind_mono _ _ _ _ _ (fun rs _ _ => RatProb.le_of_eqv (RatProb.eqv_symm (hSub rs))))
theorem adv_compose_converter {CState S₀ S₁ Q₁ R₁ Q₀ R₀ : Type} (conv : Converter CState Q₁ R₁ Q₀ R₀) (G₀ : CryptoPackage S₀ Q₀ R₀) (G₁ : CryptoPackage S₁ Q₀ R₀)
    {q : Nat} (adv : QueryProg Q₁ R₁ Bool q) :
    RatProb.eqv (gameAdv (attachConverter conv G₀) (attachConverter conv G₁) adv) (gameAdv G₀ G₁ (pullbackAdv conv conv.init adv)) :=
  RatProb.absDiff_eqv_congr (runProg_attachConverter_equiv conv G₀ adv conv.init G₀.init id)
    (runProg_attachConverter_equiv conv G₁ adv conv.init G₁.init id)
/-! ## 4. Stateful Lazy Random Oracle (`LazyRO`), Birthday Bound & Straight-Line Extractor -/
abbrev ROLog (In Out : Type) := List (In × Out)
abbrev ROLog256 := ROLog ByteArray (BitVec 256)
def roLookup {In Out : Type} [DecidableEq In] (x : In) : ROLog In Out → Option Out
  | [] => none
  | (k, v) :: rest => if k == x then some v else roLookup x rest
def lazyROPackage {In Out : Type} [DecidableEq In] (dom : List Out) (hne : dom ≠ []) : CryptoPackage (ROLog In Out) In Out where
  init := []
  step := fun log x =>
    match roLookup x log with
    | some y => FinDist.pure (y, log)
    | none => (FinDist.uniform dom hne).map (fun y => (y, (x, y) :: log))
def lazyRO256 : CryptoPackage ROLog256 ByteArray (BitVec 256) := lazyROPackage (bitVecEnum 256) (bitVecEnum_ne_nil 256)
def hasLogCollision {In Out : Type} [DecidableEq In] [DecidableEq Out] : ROLog In Out → Bool
  | [] => false
  | (x, y) :: rest => rest.any (fun (x', y') => (x != x') && (y == y')) || hasLogCollision rest
theorem hasLogCollision_iff {In Out : Type} [DecidableEq In] [DecidableEq Out] (log : ROLog In Out) : hasLogCollision log = true ↔ ∃ p₁ ∈ log, ∃ p₂ ∈ log, p₁.1 ≠ p₂.1 ∧ p₁.2 = p₂.2 := by
  induction log with
  | nil => simp [hasLogCollision]
  | cons hd rest ih =>
    rcases hd with ⟨x, y⟩
    simp only [hasLogCollision, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ih, List.mem_cons]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨p₂, hM, hN, hE⟩ | ⟨p₁, hp₁, p₂, hp₂, hN, hE⟩
      · exact ⟨(x, y), .inl rfl, p₂, .inr hM, hN, hE⟩
      · exact ⟨p₁, .inr hp₁, p₂, .inr hp₂, hN, hE⟩
    · rcases h with ⟨p₁, hp₁, p₂, hp₂, hN, hE⟩
      rcases hp₁ with rfl | hp₁ <;> rcases hp₂ with rfl | hp₂
      · exact False.elim (hN rfl)
      · exact .inl ⟨p₂, hp₂, hN, hE⟩
      · exact .inl ⟨p₁, hp₁, Ne.symm hN, hE.symm⟩
      · exact .inr ⟨p₁, hp₁, p₂, hp₂, hN, hE⟩
private theorem filter_mem_length_le_of_nodup {Out : Type} [DecidableEq Out] {dom : List Out} (hNodup : dom.Nodup) (ys : List Out) : (dom.filter (fun y => ys.any (· == y))).length ≤ ys.length := by
  induction ys with
  | nil => simp
  | cons y₀ rest ih =>
    have hCnt : ∀ (xs : List Out), xs.Nodup → (xs.filter (· == y₀)).length ≤ 1 := by
      intro xs; induction xs with
      | nil => intros; exact Nat.zero_le 1
      | cons x xs ihX =>
        intro hNd; rcases hNd with _ | ⟨hNot, hNdR⟩; simp only [List.filter]
        by_cases hxy : x = y₀
        · subst hxy
          have hZ : (xs.filter (· == x)).length = 0 := by rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro z hz; simp [beq_iff_eq]; exact fun hzx => hNot z hz hzx.symm
          simp [hZ]
        · simp [beq_eq_false_iff_ne.2 hxy, ihX hNdR]
    have hSub : ∀ (xs : List Out), (xs.filter (fun y => (y₀ == y) || rest.any (· == y))).length ≤ (xs.filter (· == y₀)).length + (xs.filter (fun y => rest.any (· == y))).length := by
      intro xs; induction xs with
      | nil => exact Nat.zero_le 0
      | cons x xs ihS =>
        simp only [List.filter]; by_cases hx : x = y₀
        · subst hx; simp only [beq_self_eq_true, Bool.true_or]
          cases rest.any (· == x) <;> simp at ihS ⊢ <;> omega
        · simp only [beq_eq_false_iff_ne.2 (Ne.symm hx), beq_eq_false_iff_ne.2 hx, Bool.false_or]
          cases rest.any (· == x) <;> simp at ihS ⊢ <;> omega
    have := hSub dom; have := hCnt dom hNodup; simp only [List.any_cons, List.length_cons]; omega
private theorem even_choose_two_step (q : Nat) : 2 * q + q * (q - 1) = (q + 1) * q := by
  cases q with | zero => rfl | succ m => simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
private theorem lazyRO_collision_step_bound {In Out α : Type} [DecidableEq In] [DecidableEq Out] (dom : List Out) (hne : dom ≠ []) (hNodup : dom.Nodup) :
    ∀ {q : Nat} (adv : QueryProg In Out α q) (log : ROLog In Out) (L : Nat), log.length ≤ L →
      RatProb.le ((runProg (lazyROPackage dom hne) adv log).probEvent (fun (_, lf) => hasLogCollision lf)) (if hasLogCollision log then RatProb.one
         else ⟨2 * q * L + q * (q - 1), 2 * dom.length, Nat.mul_pos (by decide) (length_pos_of_ne_nil hne)⟩)
  | _, .ret _, log, _, _ => by
    simp only [runProg, FinDist.pure, FinDist.probEvent, FinDist.totalWeight, eventMass, weightSum, Nat.add_zero]
    cases hasLogCollision log <;> simp [RatProb.le, RatProb.one]
  | q + 1, .query x k, log, L, hLen => by
    by_cases hC0 : hasLogCollision log = true
    · simp only [hC0, ↓reduceIte]; unfold RatProb.le FinDist.probEvent RatProb.one; dsimp [FinDist.totalWeight]; simpa using eventMass_le_weightSum _ _
    · have hCF : hasLogCollision log = false := Bool.eq_false_iff.2 hC0; simp only [hC0, Bool.false_eq_true, ↓reduceIte, runProg]
      cases hLook : roLookup x log with
      | some y =>
        simp only [lazyROPackage, hLook]; have hEqv := FinDist.bind_pure_left (y, log)
          (fun (r, st') => runProg (lazyROPackage dom hne) (k r) st') (fun (_, lf) => hasLogCollision lf)
        have ih := lazyRO_collision_step_bound dom hne hNodup (k y) log L hLen; simp only [hCF, Bool.false_eq_true, ↓reduceIte] at ih
        have hMono : 2 * q * L + q * (q - 1) ≤ 2 * (q + 1) * L + (q + 1) * q := by have := even_choose_two_step q; have : 2 * q * L ≤ 2 * (q + 1) * L := Nat.mul_le_mul_right L (by omega); omega
        exact RatProb.le_congr (RatProb.eqv_symm hEqv) (RatProb.eqv_refl _)
          (RatProb.le_trans ih (by unfold RatProb.le; dsimp; exact Nat.mul_le_mul_right _ hMono))
      | none =>
        simp only [lazyROPackage, hLook]; let M := dom.length; let remNum := 2 * q * (L + 1) + q * (q - 1)
        have hHit : (dom.filter (fun y => hasLogCollision ((x, y) :: log))).length ≤ L := by
          have hImp : ∀ y, hasLogCollision ((x, y) :: log) = true → (log.map Prod.snd).any (· == y) = true := by
            intro y hy; simp only [hasLogCollision, hCF, Bool.or_false, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hy
            rcases hy with ⟨⟨_, _⟩, hMem, _, rfl⟩; exact List.any_eq_true.2 ⟨y, List.mem_map_of_mem hMem, beq_self_eq_true y⟩
          have hSubF : ∀ (xs : List Out), (xs.filter (fun y => hasLogCollision ((x, y) :: log))).length ≤ (xs.filter (fun y => (log.map Prod.snd).any (· == y))).length := by
            intro xs; induction xs with
            | nil => exact Nat.zero_le 0
            | cons z zs ihZ =>
              dsimp only [List.filter]; by_cases hCz : hasLogCollision ((x, z) :: log) = true
              · rw [hCz, hImp z hCz]; dsimp; omega
              · rw [Bool.eq_false_iff.2 hCz]
                cases hAz : (log.map Prod.snd).any (· == z) <;> dsimp <;> omega
          exact Nat.le_trans (hSubF dom)
            (Nat.le_trans (filter_mem_length_le_of_nodup hNodup (log.map Prod.snd)) (by simpa using hLen))
        rw [bind_map_eq]; unfold RatProb.le FinDist.probEvent FinDist.bind FinDist.uniform FinDist.totalWeight; dsimp only; rw [bindRaw_weightSum, uniform_weightSum]
        let fK : Out → FinDist (α × ROLog In Out) := fun z => runProg (lazyROPackage dom hne) (k z) ((x, z) :: log)
        have auxU : ∀ (ys : List Out), eventMass (fun (_, lf) => hasLogCollision lf) (bindRaw (ys.map (fun y => (y, 1))) fK).1 * (2 * M) ≤
            ((ys.filter (fun y => hasLogCollision ((x, y) :: log))).length * (2 * M) + ys.length * remNum) *
            (bindRaw (ys.map (fun y => (y, 1))) fK).2 := by
          intro ys; induction ys with
          | nil => simp [bindRaw, eventMass]
          | cons y ys ihY =>
            have hBr := lazyRO_collision_step_bound dom hne hNodup (k y) ((x, y) :: log) (L + 1) (by simp; omega)
            simp only [List.map_cons, bindRaw, Nat.one_mul, eventMass_append, eventMass_scaleSupport, FinDist.totalWeight, List.length_cons, List.filter]
            let dy := fK y; let Ey := eventMass (fun (_, lf) => hasLogCollision lf) dy.support; let Ty := weightSum dy.support
            let B := eventMass (fun (_, lf) => hasLogCollision lf) (bindRaw (ys.map (fun z => (z, 1))) fK).1; let D := (bindRaw (ys.map (fun z => (z, 1))) fK).2
            let cy := (ys.filter (fun z => hasLogCollision ((x, z) :: log))).length
            cases hCy : hasLogCollision ((x, y) :: log)
            · simp only [hCy, Bool.false_eq_true, ↓reduceIte] at hBr; unfold RatProb.le FinDist.probEvent FinDist.totalWeight at hBr; dsimp only at hBr
              have hStep : (D * Ey + Ty * B) * (2 * M) ≤ D * (remNum * Ty) + Ty * ((cy * (2 * M) + ys.length * remNum) * D) := by
                rw [Nat.add_mul]; apply Nat.add_le_add
                · calc D * Ey * (2 * M) = D * (Ey * (2 * M)) := by ac_rfl
                    _ ≤ D * (remNum * Ty) := Nat.mul_le_mul_left D hBr
                · calc Ty * B * (2 * M) = Ty * (B * (2 * M)) := by ac_rfl
                    _ ≤ Ty * ((cy * (2 * M) + ys.length * remNum) * D) := Nat.mul_le_mul_left Ty ihY
              have hEqR : ∀ R, D * (R * Ty) + Ty * ((cy * (2 * M) + ys.length * R) * D) = (cy * (2 * M) + (ys.length + 1) * R) * (Ty * D) := fun _ => by simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; ac_rfl
              exact hEqR remNum ▸ hStep
            · simp only [List.length_cons]
              have hStep : (D * Ey + Ty * B) * (2 * M) ≤ D * Ty * (2 * M) + Ty * ((cy * (2 * M) + ys.length * remNum) * D) := by
                rw [Nat.add_mul]; apply Nat.add_le_add
                · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D (eventMass_le_weightSum _ _))
                · calc Ty * B * (2 * M) = Ty * (B * (2 * M)) := by ac_rfl
                    _ ≤ Ty * ((cy * (2 * M) + ys.length * remNum) * D) := Nat.mul_le_mul_left Ty ihY
              have hLeR : ∀ R, D * Ty * (2 * M) + Ty * ((cy * (2 * M) + ys.length * R) * D) ≤ ((cy + 1) * (2 * M) + (ys.length + 1) * R) * (Ty * D) := fun R => by
                have hId : ((cy + 1) * (2 * M) + (ys.length + 1) * R) * (Ty * D) = (D * Ty * (2 * M) + Ty * ((cy * (2 * M) + ys.length * R) * D)) + R * (Ty * D) := by
                  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]; ac_rfl
                rw [hId]; exact Nat.le_add_right _ _
              exact Nat.le_trans hStep (hLeR remNum)
        have hDom := auxU dom; let Ddom := (bindRaw (dom.map (fun y => (y, 1))) fK).2
        have hCoef : (dom.filter (fun y => hasLogCollision ((x, y) :: log))).length * (2 * M) + M * remNum ≤ (2 * (q + 1) * L + (q + 1) * q) * M := by
          calc (dom.filter (fun y => hasLogCollision ((x, y) :: log))).length * (2 * M) + M * remNum
            _ ≤ L * (2 * M) + M * (2 * q * (L + 1) + q * (q - 1)) := Nat.add_le_add_right (Nat.mul_le_mul_right (2 * M) hHit) _
            _ = (2 * L + 2 * q * L + (2 * q + q * (q - 1))) * M := by simp only [Nat.mul_add, Nat.add_mul]; ac_rfl
            _ = (2 * (q + 1) * L + (q + 1) * q) * M := by rw [even_choose_two_step q]; congr 1; have : 2 * (q + 1) * L = 2 * L + 2 * q * L := (by rw [Nat.mul_add, Nat.add_mul]; ac_rfl); omega
        exact Nat.le_trans hDom (by
          calc _ ≤ ((2 * (q + 1) * L + (q + 1) * q) * M) * Ddom := Nat.mul_le_mul_right Ddom hCoef
            _ = (2 * (q + 1) * L + (q + 1) * q) * (M * Ddom) := by ac_rfl)
theorem lazyRO_collision_prob_le_birthday_dom {In Out α : Type} [DecidableEq In] [DecidableEq Out] (dom : List Out) (hne : dom ≠ []) (hNodup : dom.Nodup) {q : Nat} (adv : QueryProg In Out α q) :
    RatProb.le ((runProg (lazyROPackage dom hne) adv []).probEvent (fun (_, lf) => hasLogCollision lf))
      ⟨q * (q - 1), 2 * dom.length, Nat.mul_pos (by decide) (length_pos_of_ne_nil hne)⟩ := by
  simpa [hasLogCollision] using lazyRO_collision_step_bound dom hne hNodup adv [] 0 (Nat.le_refl 0)
/-- **Constructive Birthday Collision Bound (`lazyRO_collision_prob_le_birthday`)**: Any $q$-query adaptive adversary against `lazyRO256` produces distinct inputs with equal 256-bit digest in its query log with probability $\le \frac{q(q-1)}{2 \cdot 2^{256}}$. -/
theorem lazyRO_collision_prob_le_birthday {α : Type} {q : Nat} (adv : QueryProg ByteArray (BitVec 256) α q) : RatProb.le ((runProg lazyRO256 adv []).probEvent (fun (_, lf) => hasLogCollision lf))
      ⟨q * (q - 1), 2 * (2 ^ 256), Nat.mul_pos (by decide) (Nat.pow_pos (by decide))⟩ := by
  simpa only [lazyRO256, bitVecEnum_length] using
    lazyRO_collision_prob_le_birthday_dom (bitVecEnum 256) (bitVecEnum_ne_nil 256) (bitVecEnum_nodup 256) adv
def extractFromROLog {In Out W : Type} [DecidableEq Out] (decode : In → Option W) (targetDigest : Out) : ROLog In Out → Option (In × W)
  | [] => none
  | (x, y) :: rest =>
    if y == targetDigest then
      match decode x with | some w => some (x, w) | none => extractFromROLog decode targetDigest rest
    else extractFromROLog decode targetDigest rest
theorem extractFromROLog_sound {In Out W : Type} [DecidableEq Out] (decode : In → Option W) (target : Out) (log : ROLog In Out) {x : In} {w : W}
    (hExt : extractFromROLog decode target log = some (x, w)) :
    (x, target) ∈ log ∧ decode x = some w := by
  induction log with
  | nil => cases hExt
  | cons hd rest ih =>
    rcases hd with ⟨x₀, y₀⟩; simp only [extractFromROLog] at hExt
    by_cases hy : y₀ = target
    · subst hy; simp only [beq_self_eq_true, ↓reduceIte] at hExt
      cases hDec : decode x₀ with
      | some w₀ => rw [hDec] at hExt; injection hExt with hP; injection hP with hx hw; subst hx hw; exact ⟨List.mem_cons_self, hDec⟩
      | none => rw [hDec] at hExt; obtain ⟨hM, hD⟩ := ih hExt; exact ⟨List.mem_cons_of_mem _ hM, hD⟩
    · simp only [beq_eq_false_iff_ne.2 hy, Bool.false_eq_true, ↓reduceIte] at hExt; obtain ⟨hM, hD⟩ := ih hExt; exact ⟨List.mem_cons_of_mem _ hM, hD⟩
theorem extractFromROLog_complete_of_no_collision {In Out W : Type} [DecidableEq In] [DecidableEq Out]
    (decode : In → Option W) (target : Out) (log : ROLog In Out) (hNoColl : hasLogCollision log = false)
    {x : In} {w : W} (hMem : (x, target) ∈ log) (hDec : decode x = some w) :
    extractFromROLog decode target log = some (x, w) := by
  induction log with
  | nil => cases hMem
  | cons hd rest ih =>
    rcases hd with ⟨x₀, y₀⟩; simp only [hasLogCollision, Bool.or_eq_false_iff] at hNoColl
    obtain ⟨hNoHead, hNoRest⟩ := hNoColl
    rcases List.mem_cons.1 hMem with hEq | hTail
    · injection hEq with hx hy; subst hx hy; simp [extractFromROLog, hDec]
    · by_cases hy : y₀ = target
      · subst hy
        have hxEq : x₀ = x :=
          if hx : x₀ = x then hx else False.elim (by
            have hAny : rest.any (fun (x', y') => (x₀ != x') && (y₀ == y')) = true :=
              List.any_eq_true.2 ⟨(x, y₀), hTail, by simp [bne_iff_ne, hx]⟩
            rw [hNoHead] at hAny; cases hAny)
        subst hxEq; simp [extractFromROLog, hDec]
      · simp [extractFromROLog, beq_eq_false_iff_ne.2 hy, ih hNoRest hTail]
/-! ## 5. Compressing `MSISGame` & `MLWEGame` (Killing Pigeonhole / Minkowski Vacuity) -/
def findMatch {α β : Type} [DecidableEq β] (f : α → β) (y : β) : List α → Option α
  | [] => none
  | x :: xs => if f x == y then some x else findMatch f y xs
private theorem findMatch_some {α β : Type} [DecidableEq β] {f : α → β} {y : β} {xs : List α} {x' : α} (h : findMatch f y xs = some x') : x' ∈ xs ∧ f x' = y := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    simp only [findMatch] at h; by_cases hfx : f x = y
    · simp only [beq_iff_eq.2 hfx, ↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨List.mem_cons_self, hfx⟩
    · simp only [beq_eq_false_iff_ne.2 hfx, Bool.false_eq_true, ↓reduceIte] at h; obtain ⟨hm, he⟩ := ih h; exact ⟨List.mem_cons_of_mem _ hm, he⟩
private theorem findMatch_none {α β : Type} [DecidableEq β] {f : α → β} {y : β} {xs : List α} (h : findMatch f y xs = none) : ∀ x' ∈ xs, f x' ≠ y := by
  induction xs with
  | nil => intro _ hm; cases hm
  | cons x rest ih =>
    simp only [findMatch] at h; by_cases hfx : f x = y
    · simp [beq_iff_eq.2 hfx] at h
    · simp only [beq_eq_false_iff_ne.2 hfx, Bool.false_eq_true, ↓reduceIte] at h
      intro x' hm; rcases List.mem_cons.1 hm with rfl | ht; exact hfx; exact ih h x' ht
def findCollisionAux {α β : Type} [DecidableEq β] (f : α → β) : List α → List α → Option (α × α)
  | [], _ => none
  | x :: xs, seen =>
    match findMatch f (f x) seen with
    | some x' => some (x', x)
    | none => findCollisionAux f xs (x :: seen)
def findCollision {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) : Option (α × α) := findCollisionAux f xs []
private theorem nodup_length_le_of_subset {β : Type} [DecidableEq β] {L cod : List β} (hNd : L.Nodup) (hSub : ∀ y ∈ L, y ∈ cod) : L.length ≤ cod.length := by
  have hFilt : L.filter (fun y => cod.any (· == y)) = L := List.filter_eq_self.2 (fun y hy => List.any_eq_true.2 ⟨y, hSub y hy, beq_self_eq_true y⟩)
  have hBnd := filter_mem_length_le_of_nodup hNd cod; rwa [hFilt] at hBnd
private theorem findCollisionAux_spec {α β : Type} [DecidableEq β] (f : α → β) (xs seen : List α) (hNdX : xs.Nodup) (hDisj : ∀ z ∈ xs, z ∉ seen) (hNdSeen : (seen.map f).Nodup) :
    match findCollisionAux f xs seen with
    | some (a₁, a₂) => a₁ ∈ seen ++ xs ∧ a₂ ∈ xs ∧ a₁ ≠ a₂ ∧ f a₁ = f a₂
    | none => ∃ L : List β, L.Nodup ∧ L.length = xs.length + seen.length ∧ ∀ y ∈ L, ∃ z ∈ seen ++ xs, f z = y := by
  induction xs generalizing seen with
  | nil =>
    dsimp [findCollisionAux]
    exact ⟨seen.map f, hNdSeen, by simp, fun y hy => by
      rcases List.mem_map.1 hy with ⟨z, hz, rfl⟩; exact ⟨z, by simp [hz], rfl⟩⟩
  | cons x rest ih =>
    rcases hNdX with _ | ⟨hNotRest, hNdRest⟩; dsimp only [findCollisionAux]
    cases hM : findMatch f (f x) seen with
    | some x' =>
      obtain ⟨hxSeen, hfx⟩ := findMatch_some hM
      refine ⟨List.mem_append_left _ hxSeen, List.mem_cons_self, fun hEq => ?_, hfx⟩
      subst hEq; exact hDisj x' List.mem_cons_self hxSeen
    | none =>
      have hNo := findMatch_none hM
      have hNdSeen' : ((x :: seen).map f).Nodup := by
        refine .cons (fun y hy hEq => ?_) hNdSeen
        rcases List.mem_map.1 hy with ⟨x', hx', rfl⟩; exact hNo x' hx' hEq.symm
      have hDisj' : ∀ z ∈ rest, z ∉ x :: seen := by
        intro z hz hIn; rcases List.mem_cons.1 hIn with rfl | hs
        · exact hNotRest z hz rfl
        · exact hDisj z (List.mem_cons_of_mem _ hz) hs
      have step := ih (x :: seen) hNdRest hDisj' hNdSeen'
      cases hRec : findCollisionAux f rest (x :: seen) with
      | some p =>
        rcases p with ⟨a₁, a₂⟩; rw [hRec] at step; obtain ⟨ha₁, ha₂, hNe, hEqF⟩ := step
        have ha₁' : a₁ ∈ seen ++ (x :: rest) := by
          rcases List.mem_append.1 ha₁ with hs | hr
          · rcases List.mem_cons.1 hs with rfl | hs'
            · exact List.mem_append_right _ List.mem_cons_self
            · exact List.mem_append_left _ hs'
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
        exact ⟨ha₁', List.mem_cons_of_mem _ ha₂, hNe, hEqF⟩
      | none =>
        rw [hRec] at step; obtain ⟨L, hLNd, hLLen, hLSub⟩ := step
        refine ⟨L, hLNd, by simp at hLLen ⊢; omega, fun y hy => ?_⟩
        obtain ⟨z, hz, rfl⟩ := hLSub y hy
        rcases List.mem_append.1 hz with hs | hr
        · rcases List.mem_cons.1 hs with rfl | hs'
          · exact ⟨z, List.mem_append_right _ List.mem_cons_self, rfl⟩
          · exact ⟨z, List.mem_append_left _ hs', rfl⟩
        · exact ⟨z, List.mem_append_right _ (List.mem_cons_of_mem _ hr), rfl⟩
/-- **Constructive `0 Classical.choice` Pigeonhole Collision Extractor**: Whenever `cod.length < xs.length` and `xs.Nodup`, `findCollision f xs` deterministically extracts `a₁ ≠ a₂` in `xs` with `f a₁ = f a₂`. -/
def pigeonholeCollision {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) (cod : List β) (hNd : xs.Nodup) (hMap : ∀ x ∈ xs, f x ∈ cod) (hGt : cod.length < xs.length) :
    { p : α × α // p.1 ∈ xs ∧ p.2 ∈ xs ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2 } :=
  have hSpec := findCollisionAux_spec f xs [] hNd (fun _ _ h => by cases h) .nil
  match hC : findCollision f xs with
  | some (a₁, a₂) => ⟨(a₁, a₂), by change findCollisionAux f xs [] = some (a₁, a₂) at hC; rw [hC] at hSpec; simpa using hSpec⟩
  | none => False.elim (by
      change findCollisionAux f xs [] = none at hC; rw [hC] at hSpec; obtain ⟨L, hLNd, hLLen, hLSub⟩ := hSpec
      have hLe := nodup_length_le_of_subset hLNd (fun y hy => by obtain ⟨z, hz, rfl⟩ := hLSub y hy; exact hMap z (by simpa using hz))
      simp at hLLen; omega)
def dotInt : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dotInt xs ys
  | _, _ => 0
def vecLinComb (a b : Int) (u v : List Int) : List Int := List.zipWith (fun x y => a * x + b * y) u v
theorem dotInt_vecLinComb (a b : Int) (row u v : List Int) (huv : u.length = v.length) : dotInt row (vecLinComb a b u v) = a * dotInt row u + b * dotInt row v := by
  induction row generalizing u v with
  | nil => simp [dotInt]
  | cons r rs ih =>
    cases u with
    | nil => cases v with | nil => simp [vecLinComb, dotInt] | cons _ _ => simp at huv
    | cons x xs =>
      cases v with
      | nil => simp at huv
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at huv; change r * (a * x + b * y) + dotInt rs (vecLinComb a b xs ys) =
          a * (r * x + dotInt rs xs) + b * (r * y + dotInt rs ys)
        rw [ih xs ys huv, Int.mul_add, Int.mul_add, Int.mul_add]; have e1 : r * (a * x) = a * (r * x) := (by ac_rfl); have e2 : r * (b * y) = b * (r * y) := (by ac_rfl); rw [e1, e2]; omega
private def prependAll {α : Type} : List α → List (List α) → List (List α)
  | [], _ => []
  | d :: ds, vs => vs.map (d :: ·) ++ prependAll ds vs
private theorem map_cons_nodup {α : Type} (d : α) {vs : List (List α)} (hNdV : vs.Nodup) : (vs.map (d :: ·)).Nodup := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    rcases hNdV with _ | ⟨hNot, hRest⟩
    refine .cons (fun w hw hEq => ?_) (ih hRest)
    rcases List.mem_map.1 hw with ⟨v', hv', rfl⟩; injection hEq with _ hvEq; exact hNot v' hv' hvEq
private theorem prependAll_mem_decomp {α : Type} (ds : List α) (vs : List (List α)) : ∀ w ∈ prependAll ds vs, ∃ d' ∈ ds, ∃ v' ∈ vs, w = d' :: v' := by
  induction ds with
  | nil => intro _ hm; cases hm
  | cons d ds ih =>
    intro w hm; rcases List.mem_append.1 hm with hL | hR
    · rcases List.mem_map.1 hL with ⟨v', hv', rfl⟩; exact ⟨d, List.mem_cons_self, v', hv', rfl⟩
    · obtain ⟨d', hd', v', hv', rfl⟩ := ih w hR; exact ⟨d', List.mem_cons_of_mem _ hd', v', hv', rfl⟩
private theorem prependAll_spec {α : Type} (ds : List α) (vs : List (List α)) (k : Nat) (hNdD : ds.Nodup) (hNdV : vs.Nodup) (hLenV : ∀ v ∈ vs, v.length = k) :
    (prependAll ds vs).length = ds.length * vs.length ∧
    (prependAll ds vs).Nodup ∧
    (∀ w ∈ prependAll ds vs, w.length = k + 1 ∧ ∀ x ∈ w, x ∈ ds ∨ ∃ v ∈ vs, x ∈ v) := by
  induction ds with
  | nil => simp [prependAll]
  | cons d ds ih =>
    rcases hNdD with _ | ⟨hNotD, hNdDs⟩
    obtain ⟨ihLen, ihNd, ihMem⟩ := ih hNdDs; simp only [prependAll]
    refine ⟨by simp [ihLen, Nat.add_mul]; omega,
      nodup_append_disjoint (map_cons_nodup d hNdV) ihNd (fun w hw1 hw2 => ?_), fun w hw => ?_⟩
    · rcases List.mem_map.1 hw1 with ⟨_, _, rfl⟩
      obtain ⟨d', hd', _, _, hEq⟩ := prependAll_mem_decomp ds vs _ hw2; injection hEq with hdEq _; exact hNotD d' hd' hdEq
    · rcases List.mem_append.1 hw with hL | hR
      · rcases List.mem_map.1 hL with ⟨v, hv, rfl⟩
        refine ⟨by simp [hLenV v hv], fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hxv; exact .inl List.mem_cons_self; exact .inr ⟨v, hv, hxv⟩
      · obtain ⟨hL', hM'⟩ := ihMem w hR; exact ⟨hL', fun x hx => (hM' x hx).elim (fun hd' => .inl (List.mem_cons_of_mem _ hd')) .inr⟩
def nonnegShortVecs (B : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | m + 1 => prependAll ((List.range (B + 1)).map (fun n : Nat => (n : Int))) (nonnegShortVecs B m)
def modSynVecs (q : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => prependAll ((List.range q).map (fun n : Nat => (n : Int))) (modSynVecs q n)
private theorem range_map_natCast_nodup (K : Nat) : ((List.range K).map (fun n : Nat => (n : Int))).Nodup := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine nodup_append_disjoint ih (by simp) (fun _ h1 h2 => ?_)
    rcases List.mem_map.1 h1 with ⟨j, hj, rfl⟩
    simp only [List.mem_singleton] at h2; have : j < K := List.mem_range.1 hj; omega
private theorem nonnegShortVecs_spec (B m : Nat) : (nonnegShortVecs B m).length = (B + 1) ^ m ∧ (nonnegShortVecs B m).Nodup ∧
    (∀ v ∈ nonnegShortVecs B m, v.length = m ∧ ∀ x ∈ v, 0 ≤ x ∧ x ≤ (B : Int)) := by
  induction m with
  | zero => simp [nonnegShortVecs]
  | succ m ih =>
    obtain ⟨ihLen, ihNd, ihMem⟩ := ih; obtain ⟨pLen, pNd, pMem⟩ := prependAll_spec ((List.range (B + 1)).map (fun n : Nat => (n : Int)))
      (nonnegShortVecs B m) m (range_map_natCast_nodup (B + 1)) ihNd (fun v hv => (ihMem v hv).1)
    refine ⟨by simp [nonnegShortVecs, pLen, ihLen, Nat.pow_succ, Nat.mul_comm], pNd, fun w hw => ?_⟩
    obtain ⟨hwLen, hwX⟩ := pMem w hw
    refine ⟨hwLen, fun x hx => ?_⟩
    rcases hwX x hx with hHead | ⟨v, hv, hxv⟩
    · rcases List.mem_map.1 hHead with ⟨k, hk, rfl⟩
      have := List.mem_range.1 hk; exact ⟨Int.natCast_nonneg k, by omega⟩
    · exact (ihMem v hv).2 x hxv
private theorem modSynVecs_mem (q : Nat) (_ : 0 < q) : ∀ (ys : List Int), (∀ y ∈ ys, 0 ≤ y ∧ y < (q : Int)) → ys ∈ modSynVecs q ys.length := by
  intro ys; induction ys with
  | nil => intros; simp [modSynVecs]
  | cons y ys ih =>
    intro hB; obtain ⟨hy0, hyq⟩ := hB y List.mem_cons_self; have ihYs := ih (fun z hz => hB z (List.mem_cons_of_mem _ hz)); have hyNat : ((y.toNat : Nat) : Int) = y := Int.toNat_of_nonneg hy0
    have hyLt : y.toNat < q := (by omega)
    have hInPre : ∀ (ds : List Int) (vs : List (List Int)), y ∈ ds → ys ∈ vs → (y :: ys) ∈ prependAll ds vs := by
      intro ds vs; induction ds with
      | nil => intro hm; cases hm
      | cons d ds ihD =>
        intro hd hvs; simp only [prependAll, List.mem_append]
        rcases List.mem_cons.1 hd with rfl | hds; exact .inl (List.mem_map_of_mem hvs); exact .inr (ihD hds hvs)
    exact hInPre _ _ (List.mem_map.2 ⟨y.toNat, List.mem_range.2 hyLt, hyNat⟩) ihYs
private theorem modSynVecs_length (q n : Nat) : (modSynVecs q n).length = q ^ n := by
  induction n with
  | zero => simp [modSynVecs]
  | succ n ih =>
    have hNd : ∀ k, (modSynVecs q k).Nodup ∧ ∀ v ∈ modSynVecs q k, v.length = k := by
      intro k; induction k with
      | zero => simp [modSynVecs]
      | succ k ihK =>
        obtain ⟨_, pNd, pMem⟩ := prependAll_spec ((List.range q).map (fun n : Nat => (n : Int))) (modSynVecs q k) k
          (range_map_natCast_nodup q) ihK.1 ihK.2
        exact ⟨pNd, fun w hw => (pMem w hw).1⟩
    obtain ⟨pLen, _, _⟩ := prependAll_spec ((List.range q).map (fun n : Nat => (n : Int))) (modSynVecs q n) n
      (range_map_natCast_nodup q) (hNd n).1 (hNd n).2
    simp [modSynVecs, pLen, ih, Nat.pow_succ, Nat.mul_comm]
def ajtaiSyndrome (q : Nat) (A : List (List Int)) (v : List Int) : List Int := A.map (fun row => dotInt row v % (q : Int))
private theorem vecSub_nonzero_of_ne {u v : List Int} (hLen : u.length = v.length) (hNe : u ≠ v) : ∃ x ∈ vecLinComb 1 (-1) u v, x ≠ 0 := by
  induction u generalizing v with
  | nil => cases v with | nil => exact False.elim (hNe rfl) | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      by_cases hab : a = b
      · subst hab
        obtain ⟨x, hx, hxz⟩ := ih (by simpa using hLen) (fun h => hNe (congrArg (a :: ·) h)); exact ⟨x, List.mem_cons_of_mem _ hx, hxz⟩
      · exact ⟨1 * a + (-1) * b, List.mem_cons_self, by omega⟩
/-- **Constructive Minkowski / Pigeonhole Short-Kernel Extractor (`pigeonhole_short_kernel_construct`)**: Whenever `(B + 1) ^ cols > q ^ rows`, EVERY $n \times m$ matrix $A$ over $\mathbb{Z}_q$ constructively admits a non-zero kernel vector $u \neq 0$ with $\|u\|_\infty \le B$ and $A u \equiv 0 \pmod q$! -/
def pigeonhole_short_kernel_construct (rows cols q B : Nat) (hq : 0 < q) (A : List (List Int)) (hRows : A.length = rows) (_ : ∀ row ∈ A, row.length = cols) (hCompressing : q ^ rows < (B + 1) ^ cols) :
    { u : List Int // u.length = cols ∧ (∃ x ∈ u, x ≠ 0) ∧ (∀ x ∈ u, x.natAbs ≤ B) ∧
        ∀ row ∈ A, dotInt row u % (q : Int) = 0 } :=
  let ⟨hLenDom, hNdDom, hMemDom⟩ := nonnegShortVecs_spec B cols
  let coll := pigeonholeCollision (ajtaiSyndrome q A) (nonnegShortVecs B cols) (modSynVecs q rows) hNdDom
    (fun v _ => by
      have hSynLen : (ajtaiSyndrome q A v).length = rows := (by simp [ajtaiSyndrome, hRows]); rw [← hSynLen]
      exact modSynVecs_mem q hq _ (fun y hy => by
        rcases List.mem_map.1 hy with ⟨_, _, rfl⟩; exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩))
    (by rw [modSynVecs_length, hLenDom]; exact hCompressing)
  let v₁ := coll.1.1; let v₂ := coll.1.2; let ⟨hv₁, hv₂, hNe, hSynEq⟩ := coll.2; let u := vecLinComb 1 (-1) v₁ v₂
  ⟨u, by
    obtain ⟨hL1, hB1⟩ := hMemDom v₁ hv₁; obtain ⟨hL2, hB2⟩ := hMemDom v₂ hv₂; have huLen : u.length = cols := (by unfold u vecLinComb; rw [List.length_zipWith, hL1, hL2, Nat.min_self])
    refine ⟨huLen, vecSub_nonzero_of_ne (hL1.trans hL2.symm) hNe, ?_, ?_⟩
    · have auxB : ∀ (l₁ l₂ : List Int), (∀ a ∈ l₁, 0 ≤ a ∧ a ≤ (B : Int)) →
          (∀ b ∈ l₂, 0 ≤ b ∧ b ≤ (B : Int)) → ∀ z ∈ vecLinComb 1 (-1) l₁ l₂, z.natAbs ≤ B := by
        intro l₁; induction l₁ with
        | nil => intro _ _ _ _ hz; simp [vecLinComb] at hz
        | cons a l₁ ihL =>
          intro l₂ haL hbL z hz; cases l₂ with
          | nil => simp [vecLinComb] at hz
          | cons b l₂ =>
            dsimp only [vecLinComb, List.zipWith] at hz
            rcases List.mem_cons.1 hz with rfl | hTail
            · obtain ⟨_, _⟩ := haL a List.mem_cons_self; obtain ⟨_, _⟩ := hbL b List.mem_cons_self; omega
            · exact ihL l₂ (fun a' hm => haL a' (List.mem_cons_of_mem _ hm)) (fun b' hm => hbL b' (List.mem_cons_of_mem _ hm)) z hTail
      exact auxB v₁ v₂ hB1 hB2
    · intro row hRow; have hMapEq : ∀ (rs : List (List Int)), rs.map (fun r => dotInt r v₁ % (q : Int)) =
          rs.map (fun r => dotInt r v₂ % (q : Int)) → row ∈ rs → dotInt row v₁ % (q : Int) = dotInt row v₂ % (q : Int) := by
        intro rs; induction rs with
        | nil => intro _ hm; cases hm
        | cons r rs ihR =>
          intro hE hm; injection hE with hHd hTl; rcases List.mem_cons.1 hm with rfl | hTr; exact hHd; exact ihR hTl hTr
      have hCong := hMapEq A hSynEq hRow; rw [dotInt_vecLinComb 1 (-1) row v₁ v₂ (hL1.trans hL2.symm)]; have hSub : 1 * dotInt row v₁ + (-1) * dotInt row v₂ = dotInt row v₁ - dotInt row v₂ := (by omega)
      rw [hSub, Int.sub_emod, hCong, Int.sub_self, Int.zero_emod]⟩
theorem pigeonhole_short_kernel_exists (rows cols q B : Nat) (hq : 0 < q) (A : List (List Int)) (hRows : A.length = rows) (hCols : ∀ row ∈ A, row.length = cols)
    (hCompressing : q ^ rows < (B + 1) ^ cols) :
    ∃ u : List Int, u.length = cols ∧ (∃ x ∈ u, x ≠ 0) ∧ (∀ x ∈ u, x.natAbs ≤ B) ∧
      ∀ row ∈ A, dotInt row u % (q : Int) = 0 :=
  let ⟨u, hu⟩ := pigeonhole_short_kernel_construct rows cols q B hq A hRows hCols hCompressing
  ⟨u, hu⟩
def UnbrokenMSIS (cols q B : Nat) (A : List (List Int)) : Prop := ¬ ∃ u : List Int, u.length = cols ∧ (∃ x ∈ u, x ≠ 0) ∧ (∀ x ∈ u, x.natAbs ≤ B) ∧ ∀ row ∈ A, dotInt row u % (q : Int) = 0
theorem unbroken_sis_false_when_compressing (rows cols q B : Nat) (hq : 0 < q) (A : List (List Int)) (hRows : A.length = rows) (hCols : ∀ row ∈ A, row.length = cols)
    (hCompressing : q ^ rows < (B + 1) ^ cols) :
    UnbrokenMSIS cols q B A → False :=
  fun hUnb => hUnb (pigeonhole_short_kernel_exists rows cols q B hq A hRows hCols hCompressing)
/-! ### Uniform-CRS Distributional `MSISGame` & Exact Advantage-Preserving Binding Reduction -/
structure MSISParams where
  rows : Nat
  cols : Nat
  q : Nat
  beta : Nat
  rows_pos : 0 < rows
  cols_pos : 0 < cols
  q_pos : 0 < q
  beta_lt_q : beta < q
def uniformModDist (q : Nat) (hq : 0 < q) : FinDist Int := (FinDist.uniform (List.range q) (range_ne_nil hq)).map (fun n : Nat => (n : Int))
def uniformModVecDist (q : Nat) (hq : 0 < q) : Nat → FinDist (List Int) | 0 => FinDist.pure [] | m + 1 => (FinDist.prod (uniformModDist q hq) (uniformModVecDist q hq m)).map (fun p => p.1 :: p.2)
def uniformMatDist (P : MSISParams) : FinDist (List (List Int)) :=
  let rowD := uniformModVecDist P.q P.q_pos P.cols; let rec go : Nat → FinDist (List (List Int)) | 0 => FinDist.pure [] | r + 1 => (FinDist.prod rowD (go r)).map (fun p => p.1 :: p.2)
  go P.rows
def isMSISWin (P : MSISParams) (A : List (List Int)) (u : List Int) : Bool :=
  (u.length == P.cols) && u.any (· != 0) && u.all (fun x => decide (x.natAbs ≤ P.beta)) && A.all (fun row => decide (dotInt row u % (P.q : Int) == 0))
theorem msis_rejects_mod_wraparound (P : MSISParams) (A : List (List Int)) :
    isMSISWin P A ((P.q : Int) :: List.replicate (P.cols - 1) 0) = false := by
  have := P.beta_lt_q; simp [isMSISWin]; omega
def msisAdvantage (P : MSISParams) (adv : List (List Int) → FinDist (List Int)) : RatProb := ((uniformMatDist P).bind (fun A => (adv A).map (fun u => isMSISWin P A u))).probEvent id
theorem msis_unit_row_hit_prob (q cols : Nat) (hq : 0 < q) (hc : 0 < cols) : RatProb.eqv ((uniformModVecDist q hq cols).probEvent
        (fun row => decide (dotInt row (1 :: List.replicate (cols - 1) 0) % (q : Int) == 0)))
      ⟨1, q, hq⟩ := by
  cases cols with
  | zero => omega
  | succ m =>
    have dotZero : ∀ (rs : List Int) (k : Nat), dotInt rs (List.replicate k 0) = 0 := by
      intro rs; induction rs with
      | nil => intros; rfl | cons _ rs ih => intro k; cases k with | zero => rfl | succ k => simp [List.replicate, dotInt, ih k]
    let pRow : List Int → Bool := fun row => decide (dotInt row (1 :: List.replicate m 0) % (q : Int) == 0)
    have hEqEv : pRow ∘ (fun p : Int × List Int => p.1 :: p.2) = (fun x : Int => decide (x % (q : Int) == 0)) ∘ Prod.fst := (by funext ⟨x, xs⟩; simp [pRow, dotInt, dotZero])
    simp only [Nat.add_sub_cancel, uniformModVecDist]; change RatProb.eqv (((FinDist.prod (uniformModDist q hq) (uniformModVecDist q hq m)).map
        (fun p => p.1 :: p.2)).probEvent pRow) ⟨1, q, hq⟩
    rw [FinDist.probEvent_map, hEqEv, ← FinDist.probEvent_map]; apply RatProb.eqv_trans (prod_fst_equiv (uniformModDist q hq) (uniformModVecDist q hq m) (fun x => decide (x % (q : Int) == 0)))
    unfold uniformModDist; rw [FinDist.probEvent_map]; unfold FinDist.uniform FinDist.probEvent FinDist.totalWeight RatProb.eqv
    dsimp only [Function.comp_def]; rw [uniform_weightSum, uniform_eventMass, List.length_range]
    have hFilt : (List.range q).filter (fun n : Nat => decide ((n : Int) % (q : Int) == 0)) = [0] := by
      cases q with
      | zero => omega
      | succ q' =>
        have hTail : ∀ (k : Nat), k ≤ q' → ((List.range k).map (1 + ·)).filter (fun n : Nat => decide ((n : Int) % ((q' + 1 : Nat) : Int) == 0)) = [] := by
          intro k; induction k with
          | zero => intros; rfl
          | succ k ih =>
            intro hk; rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append, ih (by omega), List.nil_append]
            have hMod : ((1 + k : Nat) : Int) % ((q' + 1 : Nat) : Int) = ((1 + k : Nat) : Int) :=
              Int.emod_eq_of_lt (by omega) (by omega)
            have hf : decide ((((1 + k : Nat) : Int) % ((q' + 1 : Nat) : Int) == 0) = true) = false :=
              decide_eq_false (by rw [hMod]; simp [beq_iff_eq]; omega)
            dsimp only [List.filter]; rw [hf]
        have hSp := list_range_add 1 q'; simp only [Nat.add_comm 1 q'] at hSp; rw [hSp, List.filter_append, hTail q' (Nat.le_refl _), List.append_nil]; rfl
    rw [hFilt]; simp
def isValidDoubleOpening (P : MSISParams) (bOpen : Nat) (A : List (List Int)) (pair : List Int × List Int) : Bool :=
  let (w₁, w₂) := pair
  (w₁.length == P.cols) && (w₂.length == P.cols) && (w₁ != w₂) &&
    w₁.all (fun x => decide (x.natAbs ≤ bOpen)) &&
    w₂.all (fun x => decide (x.natAbs ≤ bOpen)) &&
    (ajtaiSyndrome P.q A w₁ == ajtaiSyndrome P.q A w₂)
def bindBreakProb (P : MSISParams) (bOpen : Nat) (adv : List (List Int) → FinDist (List Int × List Int)) : RatProb :=
  ((uniformMatDist P).bind (fun A => (adv A).map (isValidDoubleOpening P bOpen A))).probEvent id
def reduceBindToMSIS (adv : List (List Int) → FinDist (List Int × List Int)) : List (List Int) → FinDist (List Int) := fun A => (adv A).map (fun (w₁, w₂) => vecLinComb 1 (-1) w₁ w₂)
/-- **Exact Advantage-Preserving Compressing Ajtai Binding Reduction (`binding_advantage_le_msis_advantage`)**: In the uniform-CRS game (including compressing parameters `cols > 4 * rows`), ANY double-opening adversary `adv` yields an explicit `MSISGame` solver `reduceBindToMSIS adv` with factor-1 advantage. -/
theorem binding_advantage_le_msis_advantage (P : MSISParams) (bOpen : Nat) (hBeta : 2 * bOpen ≤ P.beta) (adv : List (List Int) → FinDist (List Int × List Int)) :
    RatProb.le (bindBreakProb P bOpen adv) (msisAdvantage P (reduceBindToMSIS adv)) := by
  unfold bindBreakProb msisAdvantage reduceBindToMSIS
  refine probEvent_bind_mono (uniformMatDist P) _ _ id id (fun A _ _ => ?_)
  rw [FinDist.probEvent_map, FinDist.probEvent_map, FinDist.probEvent_map]; unfold RatProb.le FinDist.probEvent; apply Nat.mul_le_mul_right
  have ptImp : ∀ (pair : List Int × List Int), isValidDoubleOpening P bOpen A pair = true → isMSISWin P A (vecLinComb 1 (-1) pair.1 pair.2) = true := by
    intro ⟨w₁, w₂⟩ hV; simp only [isValidDoubleOpening, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true, decide_eq_true_eq] at hV
    rcases hV with ⟨⟨⟨⟨⟨hL1, hL2⟩, hNe⟩, hB1⟩, hB2⟩, hSyn⟩
    simp only [isMSISWin, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
    have hVLen : (vecLinComb 1 (-1) w₁ w₂).length = P.cols := (by unfold vecLinComb; rw [List.length_zipWith, hL1, hL2, Nat.min_self])
    refine ⟨⟨⟨hVLen, vecSub_nonzero_of_ne (hL1.trans hL2.symm) hNe⟩, ?_⟩, ?_⟩
    · have auxNorm : ∀ (l₁ l₂ : List Int), (∀ a ∈ l₁, a.natAbs ≤ bOpen) → (∀ b ∈ l₂, b.natAbs ≤ bOpen) →
          ∀ z ∈ vecLinComb 1 (-1) l₁ l₂, z.natAbs ≤ P.beta := by
        intro l₁; induction l₁ with
        | nil => intro _ _ _ _ hz; simp [vecLinComb] at hz
        | cons a l₁ ih =>
          intro l₂ ha hb z hz; cases l₂ with
          | nil => simp [vecLinComb] at hz
          | cons b l₂ =>
            dsimp only [vecLinComb, List.zipWith] at hz
            rcases List.mem_cons.1 hz with rfl | hTl
            · have := ha a List.mem_cons_self; have := hb b List.mem_cons_self; omega
            · exact ih l₂ (fun a' hm => ha a' (List.mem_cons_of_mem _ hm)) (fun b' hm => hb b' (List.mem_cons_of_mem _ hm)) z hTl
      exact auxNorm w₁ w₂ hB1 hB2
    · intro row hRow; have hMapEq : ∀ (rs : List (List Int)), rs.map (fun r => dotInt r w₁ % (P.q : Int)) =
          rs.map (fun r => dotInt r w₂ % (P.q : Int)) → row ∈ rs → dotInt row w₁ % (P.q : Int) = dotInt row w₂ % (P.q : Int) := by
        intro rs; induction rs with
        | nil => intro _ hm; cases hm
        | cons r rs ihR =>
          intro hE hm; injection hE with hHd hTl; rcases List.mem_cons.1 hm with rfl | hTr; exact hHd; exact ihR hTl hTr
      have hCong := hMapEq A hSyn hRow; rw [dotInt_vecLinComb 1 (-1) row w₁ w₂ (hL1.trans hL2.symm)]; have hSub : 1 * dotInt row w₁ + (-1) * dotInt row w₂ = dotInt row w₁ - dotInt row w₂ := (by omega)
      rw [hSub, Int.sub_emod, hCong, Int.sub_self, Int.zero_emod]
  have monoMass : ∀ (xs : List ((List Int × List Int) × Nat)), eventMass (isValidDoubleOpening P bOpen A) xs ≤ eventMass (fun p => isMSISWin P A (vecLinComb 1 (-1) p.1 p.2)) xs := by
    intro xs; induction xs with
    | nil => exact Nat.le_refl 0
    | cons hd _ ih =>
      rcases hd with ⟨pair, u⟩; dsimp only [eventMass]
      by_cases hV : isValidDoubleOpening P bOpen A pair = true
      · simp only [hV, ptImp pair hV, ↓reduceIte]; omega
      · simp only [Bool.eq_false_iff.2 hV, Bool.false_eq_true, ↓reduceIte]
        by_cases hw : isMSISWin P A (vecLinComb 1 (-1) pair.1 pair.2) = true <;> simp [hw] <;> omega
  exact monoMass (adv A).support
structure MLWEParams where
  samples : Nat
  secretDim : Nat
  q : Nat
  errBound : Nat
  q_pos : 0 < q
  err_lt_q : errBound < q
def mlweRealDist (P : MLWEParams) : FinDist (List (List Int) × List Int) :=
  let matP : MSISParams := ⟨P.samples + 1, P.secretDim + 1, P.q, P.errBound, by omega, by omega, P.q_pos, P.err_lt_q⟩
  (FinDist.prod (uniformMatDist matP) (FinDist.prod (uniformVecDist P.errBound (P.secretDim + 1)) (uniformVecDist P.errBound (P.samples + 1)))).map
    (fun (A, s, e) => (A, List.zipWith (fun a ei => (a + ei) % (P.q : Int)) (ajtaiSyndrome P.q A s) e))
def mlweIdealDist (P : MLWEParams) : FinDist (List (List Int) × List Int) :=
  let matP : MSISParams := ⟨P.samples + 1, P.secretDim + 1, P.q, P.errBound, by omega, by omega, P.q_pos, P.err_lt_q⟩
  FinDist.prod (uniformMatDist matP) (uniformModVecDist P.q P.q_pos (P.samples + 1))
def mlweAdv (P : MLWEParams) (D : (List (List Int) × List Int) → Bool) : RatProb := RatProb.absDiff ((mlweRealDist P).probEvent D) ((mlweIdealDist P).probEvent D)
/-! ## 6. Simulator-Based Zero-Knowledge (`ZKProtocol`) & `TranscriptTree` Extractor -/
structure ZKProtocol (Stmt Wit View Leak : Type) where
  Rel : Stmt → Wit → Prop
  leakage : Stmt → Wit → Leak
  realView : Stmt → Wit → FinDist View
structure ZKSimulator (Stmt Leak View : Type) where
  simView : Stmt → Leak → FinDist View
def StatZKWithLeakage {Stmt Wit View Leak : Type} [DecidableEq View] (prot : ZKProtocol Stmt Wit View Leak) (Sim : ZKSimulator Stmt Leak View) (ε : RatProb) : Prop :=
  ∀ x w, prot.Rel x w → RatProb.le (tvDist (prot.realView x w) (Sim.simView x (prot.leakage x w))) ε
abbrev StatisticalZK {Stmt Wit View : Type} [DecidableEq View] (prot : ZKProtocol Stmt Wit View Unit) (Sim : ZKSimulator Stmt Unit View) (ε : RatProb) : Prop := StatZKWithLeakage prot Sim ε
theorem statZK_distinguisher_bound {Stmt Wit View Leak : Type} [DecidableEq View] {prot : ZKProtocol Stmt Wit View Leak} {Sim : ZKSimulator Stmt Leak View} {ε : RatProb}
    (hZK : StatZKWithLeakage prot Sim ε) (D : View → Bool) {x : Stmt} {w : Wit} (hRel : prot.Rel x w) :
    RatProb.le (RatProb.absDiff ((prot.realView x w).probEvent D) ((Sim.simView x (prot.leakage x w)).probEvent D)) ε :=
  RatProb.le_trans (absDiff_probEvent_le_tvDist _ _ D) (hZK x w hRel)
theorem dual_zk_of_both_zk {Stmt Wit V₁ V₂ : Type} [DecidableEq V₁] [DecidableEq V₂] (prot₁ : ZKProtocol Stmt Wit V₁ Unit) (prot₂ : ZKProtocol Stmt Wit V₂ Unit)
    (Sim₁ : ZKSimulator Stmt Unit V₁) (Sim₂ : ZKSimulator Stmt Unit V₂)
    (ε₁ ε₂ : RatProb) (hRelImp : ∀ x w, prot₁.Rel x w → prot₂.Rel x w)
    (hZK₁ : StatisticalZK prot₁ Sim₁ ε₁) (hZK₂ : StatisticalZK prot₂ Sim₂ ε₂) :
    StatisticalZK
      ⟨prot₁.Rel, fun _ _ => (), fun x w => FinDist.prod (prot₁.realView x w) (prot₂.realView x w)⟩
      ⟨fun x u => FinDist.prod (Sim₁.simView x u) (Sim₂.simView x u)⟩
      (RatProb.add ε₁ ε₂) :=
  fun x w hR => RatProb.le_trans
    (tvDist_prod_le (prot₁.realView x w) (Sim₁.simView x ()) (prot₂.realView x w) (Sim₂.simView x ())) (RatProb.add_le_add (hZK₁ x w hR) (hZK₂ x w (hRelImp x w hR)))
/-- $\land$-Composition of Privacy (`dual_zk_requires_both_hiding`): Dual-spine zero-knowledge requires **BOTH** spines to be hiding! -/
theorem dual_zk_requires_both_hiding {Stmt Wit V₁ V₂ : Type} [DecidableEq V₁] [DecidableEq V₂] (Rel : Stmt → Wit → Prop) (real₁ : Stmt → Wit → FinDist V₁) (real₂ : Stmt → Wit → FinDist V₂)
    (Sim : ZKSimulator Stmt Unit (V₁ × V₂)) (ε : RatProb)
    (hDual : StatisticalZK ⟨Rel, fun _ _ => (), fun x w => FinDist.prod (real₁ x w) (real₂ x w)⟩ Sim ε) :
    StatisticalZK ⟨Rel, fun _ _ => (), real₁⟩ ⟨fun x u => (Sim.simView x u).map Prod.fst⟩ ε ∧
    StatisticalZK ⟨Rel, fun _ _ => (), real₂⟩ ⟨fun x u => (Sim.simView x u).map Prod.snd⟩ ε := by
  refine ⟨fun x w hR => ?_, fun x w hR => ?_⟩
  · exact RatProb.le_congr
      (tvDist_of_equiv (prod_fst_equiv (real₁ x w) (real₂ x w)) (fun _ => RatProb.eqv_refl _)) (RatProb.eqv_refl ε)
      (RatProb.le_trans (tvDist_map_le Prod.fst (FinDist.prod (real₁ x w) (real₂ x w)) (Sim.simView x ())) (hDual x w hR))
  · exact RatProb.le_congr
      (tvDist_of_equiv (prod_snd_equiv (real₁ x w) (real₂ x w)) (fun _ => RatProb.eqv_refl _)) (RatProb.eqv_refl ε)
      (RatProb.le_trans (tvDist_map_le Prod.snd (FinDist.prod (real₁ x w) (real₂ x w)) (Sim.simView x ())) (hDual x w hR))
/-- **Refutation of Cleartext-Opening Cosplay (`cleartext_opening_destroys_dual_zk`)**: Pairing ANY hiding commitment view `real₁` with an unmasked cleartext opening `FinDist.pure (proj w)` forces $\varepsilon \ge 1/2$ against EVERY zero-leakage simulator whenever `proj w₀ ≠ proj w₁`! -/
theorem cleartext_opening_destroys_dual_zk {Stmt Wit V₁ WProj : Type} [DecidableEq V₁] [DecidableEq WProj] (Rel : Stmt → Wit → Prop) (real₁ : Stmt → Wit → FinDist V₁) (proj : Wit → WProj)
    (Sim : ZKSimulator Stmt Unit (V₁ × WProj)) (ε : RatProb)
    (hDual : StatisticalZK
      ⟨Rel, fun _ _ => (), fun x w => FinDist.prod (real₁ x w) (FinDist.pure (proj w))⟩ Sim ε)
    {x : Stmt} {w₀ w₁ : Wit} (hR₀ : Rel x w₀) (hR₁ : Rel x w₁) (hDiff : proj w₀ ≠ proj w₁) :
    RatProb.le ⟨1, 2, by decide⟩ ε := by
  obtain ⟨_, hZK₂⟩ := dual_zk_requires_both_hiding Rel real₁ (fun _ w => FinDist.pure (proj w)) Sim ε hDual
  let D : WProj → Bool := (· == proj w₀)
  have hB₀ := statZK_distinguisher_bound hZK₂ D hR₀; have hB₁' := RatProb.le_congr (RatProb.absDiff_symm _ _) (RatProb.eqv_refl ε) (statZK_distinguisher_bound hZK₂ D hR₁)
  have hP₀ : (FinDist.pure (proj w₀)).probEvent D = RatProb.one := (by simp [D, FinDist.pure, FinDist.probEvent, FinDist.totalWeight, eventMass, weightSum, RatProb.one])
  have hP₁ : (FinDist.pure (proj w₁)).probEvent D = RatProb.zero := by simp [D, FinDist.pure, FinDist.probEvent, FinDist.totalWeight, eventMass, weightSum, beq_eq_false_iff_ne.2 (Ne.symm hDiff), RatProb.zero]
  have hTri := RatProb.le_trans
    (RatProb.absDiff_triangle ((FinDist.pure (proj w₀)).probEvent D) ((Sim.simView x ()).map Prod.snd |>.probEvent D) ((FinDist.pure (proj w₁)).probEvent D))
    (RatProb.add_le_add hB₀ hB₁')
  rw [hP₀, hP₁, show RatProb.absDiff RatProb.one RatProb.zero = RatProb.one by decide] at hTri
  unfold RatProb.le RatProb.add RatProb.one at hTri; dsimp only at hTri
  have hMul : (1 * ε.den) * ε.den ≤ (ε.num * 2) * ε.den := by
    calc (1 * ε.den) * ε.den = 1 * (ε.den * ε.den) := by ac_rfl
      _ ≤ (ε.num * ε.den + ε.num * ε.den) * 1 := hTri
      _ = (ε.num * 2) * ε.den := by simp only [Nat.mul_one, ← Nat.add_mul]; congr 1; omega
  exact Nat.le_of_mul_le_mul_right hMul ε.den_pos
/-! ### Multi-Round Special-Soundness Tree Extractor (`TranscriptTree`, `extractFromForkingTree`) -/
inductive TranscriptTree : Nat → Type where
  | leaf : (cm : List Int) → (wit : List Int) → TranscriptTree 0
  | fork2 : {d : Nat} → (cm cmAux : List Int) → (c₀ c₁ : Int) →
      TranscriptTree d → TranscriptTree d → TranscriptTree (d + 1)
def TranscriptTree.rootCm : {d : Nat} → TranscriptTree d → List Int | 0, .leaf cm _ => cm | _ + 1, .fork2 cm _ _ _ _ _ => cm
def slackAtDepth (bChal : Nat) : Nat → Nat | 0 => 1 | d + 1 => 2 * bChal * slackAtDepth bChal d * slackAtDepth bChal d
def normAtDepth (bChal : Nat) : Nat → Nat → Nat | 0, b₀ => b₀ | d + 1, b₀ => 2 * bChal * slackAtDepth bChal d * normAtDepth bChal d b₀
def ValidForkingTree (q cols bChal b₀ : Nat) (A : List (List Int)) : {d : Nat} → TranscriptTree d → Prop
  | 0, .leaf cm wit =>
    cm.length = A.length ∧ wit.length = cols ∧ (∀ x ∈ wit, x.natAbs ≤ b₀) ∧ ∀ p ∈ List.zip A cm, (dotInt p.1 wit - p.2) % (q : Int) = 0
  | _ + 1, .fork2 cm cmAux c₀ c₁ t₀ t₁ =>
    cm.length = A.length ∧ cmAux.length = A.length ∧
      c₀ ≠ c₁ ∧ Nat.Coprime (c₀ - c₁).natAbs q ∧ c₀.natAbs ≤ bChal ∧ c₁.natAbs ≤ bChal ∧
      t₀.rootCm = vecLinComb 1 c₀ cm cmAux ∧ t₁.rootCm = vecLinComb 1 c₁ cm cmAux ∧
      ValidForkingTree q cols bChal b₀ A t₀ ∧ ValidForkingTree q cols bChal b₀ A t₁
/-- Explicit non-trivial depth-1 `.fork2` inhabitedness witness for `ValidForkingTree` (with coprime modular slack). -/
theorem validForkingTree_inhabited (b₀ : Nat) (hb : 1 ≤ b₀) : ∃ (A : List (List Int)) (tr : TranscriptTree 1), ValidForkingTree 17 2 1 b₀ A tr := by
  refine ⟨[[1, 1]], .fork2 [2] [0] 0 1 (.leaf [2] [1, 1]) (.leaf [2] [1, 1]), ?_⟩
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, rfl, rfl, ?_, ?_⟩ <;>
    exact ⟨rfl, rfl, by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simpa using hb, by intro p hp; simp at hp; rcases hp with rfl; decide⟩
def extractFromForkingTree : {d : Nat} → TranscriptTree d → List Int × Int
  | 0, .leaf _ wit => (wit, 1)
  | _ + 1, .fork2 _ _ c₀ c₁ t₀ t₁ =>
    let (u₀, δ₀) := extractFromForkingTree t₀; let (u₁, δ₁) := extractFromForkingTree t₁
    (vecLinComb (-c₁ * δ₁) (c₀ * δ₀) u₀ u₁, δ₀ * δ₁ * (c₀ - c₁))
private theorem fork_elim_identity (c₀ c₁ δ₀ δ₁ x₀ x₁ ci ai : Int) : (-c₁ * δ₁) * x₀ + (c₀ * δ₀) * x₁ - (δ₀ * δ₁ * (c₀ - c₁)) * ci =
      (-c₁ * δ₁) * (x₀ - δ₀ * (ci + c₀ * ai)) + (c₀ * δ₀) * (x₁ - δ₁ * (ci + c₁ * ai)) := by
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add]; have e1 : (-c₁ * δ₁) * (δ₀ * ci) = -(c₁ * δ₀ * δ₁ * ci) := (by rw [Int.neg_mul, Int.neg_mul]; congr 1; ac_rfl)
  have e2 : (c₀ * δ₀) * (δ₁ * ci) = c₀ * δ₀ * δ₁ * ci := (by ac_rfl); have e3 : (-c₁ * δ₁) * (δ₀ * (c₀ * ai)) = -(c₀ * c₁ * δ₀ * δ₁ * ai) := (by rw [Int.neg_mul, Int.neg_mul]; congr 1; ac_rfl)
  have e4 : (c₀ * δ₀) * (δ₁ * (c₁ * ai)) = c₀ * c₁ * δ₀ * δ₁ * ai := (by ac_rfl); have e5 : δ₀ * δ₁ * c₀ * ci = c₀ * δ₀ * δ₁ * ci := (by ac_rfl); have e6 : δ₀ * δ₁ * c₁ * ci = c₁ * δ₀ * δ₁ * ci := (by ac_rfl)
  rw [e1, e2, e3, e4, e5, e6]; omega
theorem extractFromForkingTree_sound (q cols bChal b₀ : Nat) (A : List (List Int)) (hCols : ∀ row ∈ A, row.length = cols) : ∀ {d : Nat} (tr : TranscriptTree d), ValidForkingTree q cols bChal b₀ A tr →
      let (w, δ) := extractFromForkingTree tr
      w.length = cols ∧ δ ≠ 0 ∧ δ.natAbs ≤ slackAtDepth bChal d ∧
      (∀ x ∈ w, x.natAbs ≤ normAtDepth bChal d b₀) ∧
      (∀ p ∈ List.zip A tr.rootCm, (dotInt p.1 w - δ * p.2) % (q : Int) = 0) ∧ Nat.Coprime δ.natAbs q
  | 0, .leaf cm wit, hV => by
    obtain ⟨_, hLen, hBnd, hRel⟩ := hV
    exact ⟨hLen, by decide, Nat.le_refl 1, hBnd, fun p hp => by simpa [TranscriptTree.rootCm] using hRel p hp, Nat.coprime_one_left q⟩
  | d + 1, .fork2 cm cmAux c₀ c₁ t₀ t₁, hV => by
    obtain ⟨hCmL, hAuxL, hcNe, hcCop, hc0B, hc1B, hRoot0, hRoot1, hV0, hV1⟩ := hV; obtain ⟨hu0L, hδ0Ne, hδ0B, hu0B, hRel0, hδ0Cop⟩ := extractFromForkingTree_sound q cols bChal b₀ A hCols t₀ hV0
    obtain ⟨hu1L, hδ1Ne, hδ1B, hu1B, hRel1, hδ1Cop⟩ := extractFromForkingTree_sound q cols bChal b₀ A hCols t₁ hV1; let u₀ := (extractFromForkingTree t₀).1; let δ₀ := (extractFromForkingTree t₀).2
    let u₁ := (extractFromForkingTree t₁).1; let δ₁ := (extractFromForkingTree t₁).2; dsimp only [extractFromForkingTree, TranscriptTree.rootCm]; have hcSubNe : c₀ - c₁ ≠ 0 := (by omega)
    have hcSubB : (c₀ - c₁).natAbs ≤ 2 * bChal := (by omega); have hWLen : (vecLinComb (-c₁ * δ₁) (c₀ * δ₀) u₀ u₁).length = cols := (by unfold vecLinComb; rw [List.length_zipWith, hu0L, hu1L, Nat.min_self])
    refine ⟨hWLen, Int.mul_ne_zero (Int.mul_ne_zero hδ0Ne hδ1Ne) hcSubNe, ?_, ?_, ?_, ?_⟩
    · change (δ₀ * δ₁ * (c₀ - c₁)).natAbs ≤ slackAtDepth bChal (d + 1); simp only [Int.natAbs_mul, slackAtDepth]
      calc δ₀.natAbs * δ₁.natAbs * (c₀ - c₁).natAbs ≤ (slackAtDepth bChal d * slackAtDepth bChal d) * (2 * bChal) := Nat.mul_le_mul (Nat.mul_le_mul hδ0B hδ1B) hcSubB
        _ = 2 * bChal * slackAtDepth bChal d * slackAtDepth bChal d := by ac_rfl
    · have auxW : ∀ (l₀ l₁ : List Int), (∀ a ∈ l₀, a.natAbs ≤ normAtDepth bChal d b₀) →
          (∀ b ∈ l₁, b.natAbs ≤ normAtDepth bChal d b₀) →
          ∀ z ∈ vecLinComb (-c₁ * δ₁) (c₀ * δ₀) l₀ l₁, z.natAbs ≤ normAtDepth bChal (d + 1) b₀ := by
        intro l₀; induction l₀ with
        | nil => intro _ _ _ _ hz; simp [vecLinComb] at hz
        | cons a l₀ ih =>
          intro l₁ ha hb z hz; cases l₁ with
          | nil => simp [vecLinComb] at hz
          | cons b l₁ =>
            dsimp only [vecLinComb, List.zipWith] at hz
            rcases List.mem_cons.1 hz with rfl | hTl
            · have ha0 := ha a List.mem_cons_self; have hb0 := hb b List.mem_cons_self; have hTri := Int.natAbs_add_le ((-c₁ * δ₁) * a) ((c₀ * δ₀) * b); simp only [Int.natAbs_mul, Int.natAbs_neg] at hTri
              have t1 : c₁.natAbs * δ₁.natAbs * a.natAbs ≤ bChal * slackAtDepth bChal d * normAtDepth bChal d b₀ := Nat.mul_le_mul (Nat.mul_le_mul hc1B hδ1B) ha0
              have t2 : c₀.natAbs * δ₀.natAbs * b.natAbs ≤ bChal * slackAtDepth bChal d * normAtDepth bChal d b₀ := Nat.mul_le_mul (Nat.mul_le_mul hc0B hδ0B) hb0; simp only [normAtDepth]
              calc ((-c₁ * δ₁) * a + (c₀ * δ₀) * b).natAbs
                _ ≤ bChal * slackAtDepth bChal d * normAtDepth bChal d b₀ + bChal * slackAtDepth bChal d * normAtDepth bChal d b₀ := Nat.le_trans hTri (Nat.add_le_add t1 t2)
                _ = 2 * bChal * slackAtDepth bChal d * normAtDepth bChal d b₀ := by rw [← Nat.two_mul]; ac_rfl
            · exact ih l₁ (fun a' hm => ha a' (List.mem_cons_of_mem _ hm)) (fun b' hm => hb b' (List.mem_cons_of_mem _ hm)) z hTl
      exact auxW u₀ u₁ hu0B hu1B
    · rw [hRoot0] at hRel0; rw [hRoot1] at hRel1; have zipRel : ∀ (rs : List (List Int)) (cs as : List Int), cs.length = rs.length → as.length = rs.length →
          (∀ p ∈ List.zip rs (vecLinComb 1 c₀ cs as), (dotInt p.1 u₀ - δ₀ * p.2) % (q : Int) = 0) →
          (∀ p ∈ List.zip rs (vecLinComb 1 c₁ cs as), (dotInt p.1 u₁ - δ₁ * p.2) % (q : Int) = 0) →
          ∀ p ∈ List.zip rs cs, (dotInt p.1 (vecLinComb (-c₁ * δ₁) (c₀ * δ₀) u₀ u₁) - (δ₀ * δ₁ * (c₀ - c₁)) * p.2) % (q : Int) = 0 := by
        intro rs; induction rs with
        | nil => intro _ _ _ _ _ _ _ hp; cases hp
        | cons r rs ih =>
          intro cs as hCL hAL hZ0 hZ1 p hp
          cases cs with
          | nil => simp at hCL
          | cons ci cs =>
            cases as with
            | nil => simp at hAL
            | cons ai as =>
              rcases List.mem_cons.1 hp with rfl | hTail
              · have hr0 := hZ0 (r, 1 * ci + c₀ * ai) List.mem_cons_self; have hr1 := hZ1 (r, 1 * ci + c₁ * ai) List.mem_cons_self; dsimp only at hr0 hr1 ⊢; rw [Int.one_mul] at hr0 hr1
                rw [dotInt_vecLinComb (-c₁ * δ₁) (c₀ * δ₀) r u₀ u₁ (hu0L.trans hu1L.symm), fork_elim_identity c₀ c₁ δ₀ δ₁ (dotInt r u₀) (dotInt r u₁) ci ai,
                    Int.add_emod, Int.mul_emod (-c₁ * δ₁), hr0, Int.mul_zero, Int.zero_emod, Int.mul_emod (c₀ * δ₀), hr1, Int.mul_zero, Int.zero_emod]; rfl
              · exact ih cs as (by simpa using hCL) (by simpa using hAL) (fun p' hp' => hZ0 p' (List.mem_cons_of_mem _ hp')) (fun p' hp' => hZ1 p' (List.mem_cons_of_mem _ hp')) p hTail
      exact zipRel A cm cmAux hCmL hAuxL hRel0 hRel1
    · change Nat.Coprime (δ₀ * δ₁ * (c₀ - c₁)).natAbs q; simp only [Int.natAbs_mul]; exact (hδ0Cop.mul_left hδ1Cop).mul_left hcCop
theorem extractFromForkingTree_slack_mod_ne_zero (q cols bChal b₀ : Nat) (hq : 1 < q) (A : List (List Int)) (hCols : ∀ row ∈ A, row.length = cols)
    {d : Nat} (tr : TranscriptTree d) (hV : ValidForkingTree q cols bChal b₀ A tr) : (extractFromForkingTree tr).2 % (q : Int) ≠ 0 := by
  intro hMod; have hCop := (extractFromForkingTree_sound q cols bChal b₀ A hCols tr hV).2.2.2.2.2; let δ := (extractFromForkingTree tr).2
  have hDiv : (q : Int) * (δ / (q : Int)) = δ := by have hE := Int.mul_ediv_add_emod δ (q : Int); dsimp [δ] at hE ⊢; rw [hMod, Int.add_zero] at hE; exact hE
  have hAbs : q * (δ / (q : Int)).natAbs = δ.natAbs := by have := congrArg Int.natAbs hDiv; simpa [Int.natAbs_mul] using this
  have hDvd : q ∣ Nat.gcd δ.natAbs q := Nat.dvd_gcd ⟨(δ / (q : Int)).natAbs, hAbs.symm⟩ (Nat.dvd_refl q)
  rw [hCop.gcd_eq_one] at hDvd; have := Nat.le_of_dvd (by decide) hDvd; omega
theorem extractFromForkingTree_within_sisBeta (q cols bChal b₀ sisBetaBound : Nat) (A : List (List Int)) (hCols : ∀ row ∈ A, row.length = cols)
    {d : Nat} (tr : TranscriptTree d) (hV : ValidForkingTree q cols bChal b₀ A tr)
    (hGate : normAtDepth bChal d b₀ < sisBetaBound) :
    ∀ x ∈ (extractFromForkingTree tr).1, x.natAbs < sisBetaBound :=
  fun x hx => Nat.lt_of_le_of_lt ((extractFromForkingTree_sound q cols bChal b₀ A hCols tr hV).2.2.2.1 x hx) hGate
end Obend.Crypto.GameSoundness
end
