module
/-
# Obend.Judge.Clearing — drex-clearing@1 certified primal-dual LP clearing judge

Verifies market clearing prices, surplus non-negativity, capacity bounds,
dual feasibility, and duality gap ≤ ε in O(N) operations.
Soundness theorem: any certified triple certifies ε-optimality over ALL feasible allocations.
-/

public import Obend.Judge.Class
public import Obend.Ledger.Book
public import Obend.Ledger.Seat

@[expose] public section
namespace Obend.Judge

open Obend.Ledger
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Market, Orders & Certificate -/

structure Market where
  currency : AssetId
  goods : AssetId
  epsilon : Nat
  deriving DecidableEq, Repr

inductive Side where
  | bid
  | ask
  deriving DecidableEq, Repr

structure Order where
  account : AccountId
  side : Side
  qty : Nat
  total : Nat
  deriving DecidableEq, Repr

def Order.crosses (price : Nat) (order : Order) : Bool :=
  match order.side with
  | .bid => decide (price * order.qty ≤ order.total)
  | .ask => decide (order.total ≤ price * order.qty)

structure Certificate where
  price : Nat
  potentials : Int × Int
  slacks : List Int
  deriving DecidableEq, Repr

structure ClearingQuery where
  market : Market
  orders : List Order
  transfers : List ResourcePosting
  deriving DecidableEq, Repr

/-! ## Order Book Analysis: Crossing Pairs & Price Validity -/

def isOrderAccount (orders : List Order) (account : AccountId) : Bool :=
  orders.any fun order => order.account == account

/-- The best (highest limit price) bid with positive quantity.
    b₁ has higher limit than b₂ iff b₂.total * b₁.qty < b₁.total * b₂.qty. -/
def highestBid? (orders : List Order) : Option Order :=
  let bids := orders.filter (fun o => o.side == .bid && o.qty > 0)
  match bids with
  | [] => none
  | b :: bs => some (bs.foldl (fun best b =>
      if best.total * b.qty < b.total * best.qty then b else best) b)

/-- The best (lowest limit price) ask with positive quantity.
    a₁ has lower limit than a₂ iff a₁.total * a₂.qty < a₂.total * a₁.qty. -/
def lowestAsk? (orders : List Order) : Option Order :=
  let asks := orders.filter (fun o => o.side == .ask && o.qty > 0)
  match asks with
  | [] => none
  | a :: as => some (as.foldl (fun best a =>
      if a.total * best.qty < best.total * a.qty then a else best) a)

/-- A crossing pair exists iff the highest bid can trade with the lowest ask. -/
def hasCrossingPair (orders : List Order) : Bool :=
  match highestBid? orders, lowestAsk? orders with
  | some bMax, some aMin => aMin.total * bMax.qty ≤ bMax.total * aMin.qty
  | _, _ => false

/-- Price validity: when crossed orders exist, the proposed price must lie within
    the crossing interval [lowest ask, highest bid] (i.e. cross both endpoints). -/
def priceInCrossingInterval (orders : List Order) (price : Nat) : Bool :=
  match highestBid? orders, lowestAsk? orders with
  | some bMax, some aMin =>
    if aMin.total * bMax.qty ≤ bMax.total * aMin.qty then
      aMin.crosses price && bMax.crosses price
    else true
  | _, _ => true

/-! ## Net Flow & Order Fills -/

def netFlow (transfers : List ResourcePosting) (account : AccountId) (asset : AssetId) : Int :=
  (transfers.map fun t =>
    (if t.destination = account ∧ t.asset = asset then (t.amount : Int) else 0) -
    (if t.source = account ∧ t.asset = asset then (t.amount : Int) else 0)).sum

def Order.fill (m : Market) (transfers : List ResourcePosting) (o : Order) : Int :=
  match o.side with
  | .bid => netFlow transfers o.account m.goods
  | .ask => - netFlow transfers o.account m.goods

def Order.paid (m : Market) (transfers : List ResourcePosting) (o : Order) : Int :=
  match o.side with
  | .bid => - netFlow transfers o.account m.currency
  | .ask => netFlow transfers o.account m.currency

/-! ## Refusals & O(N) Judge Verification -/

inductive ClearingRefusal where
  | marketMalformed
  | foreignAsset (posting : ResourcePosting)
  | notAnOrder (posting : ResourcePosting)
  | invalidPrice (price : Nat)
  | slackCount (orders slacks : Nat)
  | notUniform (account : AccountId)
  | nonConserving (diff : Int)
  | capacityExceeded (account : AccountId) (fill cap : Int)
  | negativeFill (account : AccountId) (fill : Int)
  | negativeSlack (account : AccountId) (slack : Int)
  | dualInfeasible (account : AccountId) (side : Side) (slack req : Int)
  | unservedCrossing
  | uncertified (gap : Int) (epsilon : Nat)
  deriving DecidableEq, Repr

def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f i.castSucc) + f (Fin.last n)

def judge (m : Market) (orders : List Order) (transfers : List ResourcePosting) (c : Certificate) :
    Except ClearingRefusal Unit :=
  if m.currency = m.goods then .error .marketMalformed
  else match transfers.find? (fun t => t.asset ≠ m.currency && t.asset ≠ m.goods) with
  | some t => .error (.foreignAsset t)
  | none =>
    match transfers.find? (fun t => !isOrderAccount orders t.source || !isOrderAccount orders t.destination) with
    | some t => .error (.notAnOrder t)
    | none =>
      if !priceInCrossingInterval orders c.price then
        .error (.invalidPrice c.price)
      else if c.slacks.length ≠ orders.length then
        .error (.slackCount orders.length c.slacks.length)
      else
        match orders.find? (fun o => o.paid m transfers ≠ (c.price : Int) * o.fill m transfers) with
        | some o => .error (.notUniform o.account)
        | none =>
          if finSum orders.length (fun i =>
              match (orders.get i).side with
              | .bid => (orders.get i).fill m transfers
              | .ask => - (orders.get i).fill m transfers) ≠ 0 then
            .error (.nonConserving (finSum orders.length (fun i =>
              match (orders.get i).side with
              | .bid => (orders.get i).fill m transfers
              | .ask => - (orders.get i).fill m transfers)))
          else
            match (List.finRange orders.length).find? (fun i =>
                let f := (orders.get i).fill m transfers
                let cap := if (orders.get i).crosses c.price then ((orders.get i).qty : Int) else 0
                f < 0 || cap < f) with
            | some i =>
                let o := orders.get i
                let f := o.fill m transfers
                let cap := if o.crosses c.price then (o.qty : Int) else 0
                .error (if f < 0 then .negativeFill o.account f else .capacityExceeded o.account f cap)
            | none =>
              match (List.finRange orders.length).find? (fun i =>
                  let s := c.slacks.getD i.val 0
                  let o := orders.get i
                  let dualDiff := c.potentials.2 - c.potentials.1
                  s < 0 ||
                  match o.side with
                  | .bid => dualDiff + s < 1
                  | .ask => -dualDiff + s < 1) with
              | some i =>
                  let o := orders.get i
                  let s := c.slacks.getD i.val 0
                  .error (if s < 0 then .negativeSlack o.account s else .dualInfeasible o.account o.side s 1)
              | none =>
                let objVol := finSum orders.length (fun i => (orders.get i).fill m transfers)
                let dualCap := finSum orders.length (fun i =>
                  let cap := if (orders.get i).crosses c.price then ((orders.get i).qty : Int) else 0
                  let s := c.slacks.getD i.val 0
                  cap * s)
                let gap := dualCap - objVol
                if gap ≤ (m.epsilon : Int) then
                  if objVol == 0 && hasCrossingPair orders then
                    .error .unservedCrossing
                  else .ok ()
                else .error (.uncertified gap m.epsilon)

/-! ## Soundness: Weak Duality & ε-Optimality (Full Machine-Checked Proofs) -/

theorem finSum_add (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [finSum]
    rw [ih]
    omega

theorem finSum_mul_const (n : Nat) (k : Int) (f : Fin n → Int) :
    finSum n (fun i => k * f i) = k * finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum]
    rw [ih, Int.mul_add]

theorem finSum_le (n : Nat) (f g : Fin n → Int) (hle : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ m ih =>
    simp only [finSum]
    have ih_app := ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => hle i.castSucc)
    have hlast := hle (Fin.last m)
    omega

theorem le_mul_of_one_le {x y : Int} (hx : 0 ≤ x) (hy : 1 ≤ y) : x ≤ y * x := by
  have h1 : 0 ≤ y - 1 := by omega
  have h2 : 0 ≤ (y - 1) * x := Int.mul_nonneg h1 hx
  have h3 : (y - 1) * x = y * x - x := by rw [Int.sub_mul, Int.one_mul]
  omega

theorem mul_le_mul_of_nonneg {s f c : Int} (hs : 0 ≤ s) (hfc : f ≤ c) : s * f ≤ c * s := by
  have h1 : 0 ≤ c - f := by omega
  have h2 : 0 ≤ s * (c - f) := Int.mul_nonneg hs h1
  have h3 : s * (c - f) = s * c - s * f := by rw [Int.mul_sub]
  have h4 : s * c = c * s := Int.mul_comm s c
  omega

/-- Weak duality theorem: dual value bounds every feasible circulation (0 axioms, 0 sorries). -/
theorem weak_duality (n : Nat) (A : Fin n → Int) (c : Fin n → Int) (s : Fin n → Int)
    (f' : Fin n → Int) (diff : Int)
    (hprim_cons : finSum n (fun i => A i * f' i) = 0)
    (hprim_nonneg : ∀ i, 0 ≤ f' i)
    (hprim_cap : ∀ i, f' i ≤ c i)
    (hdual_nonneg : ∀ i, 0 ≤ s i)
    (hdual_feas : ∀ i, 1 ≤ diff * A i + s i) :
    finSum n f' ≤ finSum n (fun i => c i * s i) := by
  have h1 : finSum n f' ≤ finSum n (fun i => (diff * A i + s i) * f' i) := by
    apply finSum_le
    intro i
    exact le_mul_of_one_le (hprim_nonneg i) (hdual_feas i)
  have hsplit : (fun i => (diff * A i + s i) * f' i) =
      (fun i => diff * (A i * f' i) + s i * f' i) := by
    funext i
    rw [Int.add_mul, Int.mul_assoc]
  rw [hsplit, finSum_add, finSum_mul_const, hprim_cons, Int.mul_zero, Int.zero_add] at h1
  have h2 : finSum n (fun i => s i * f' i) ≤ finSum n (fun i => c i * s i) := by
    apply finSum_le
    intro i
    exact mul_le_mul_of_nonneg (hdual_nonneg i) (hprim_cap i)
  exact Int.le_trans h1 h2

/-- Duality gap certifying ε-optimality over all candidate allocations (0 axioms, 0 sorries). -/
theorem certifies_epsilon_optimal (n : Nat) (A : Fin n → Int) (c : Fin n → Int) (s : Fin n → Int)
    (f f' : Fin n → Int) (diff : Int) (eps : Nat)
    (hgap : finSum n (fun i => c i * s i) - finSum n f ≤ (eps : Int))
    (hprim_cons : finSum n (fun i => A i * f' i) = 0)
    (hprim_nonneg : ∀ i, 0 ≤ f' i)
    (hprim_cap : ∀ i, f' i ≤ c i)
    (hdual_nonneg : ∀ i, 0 ≤ s i)
    (hdual_feas : ∀ i, 1 ≤ diff * A i + s i) :
    finSum n f' ≤ finSum n f + (eps : Int) := by
  have hwd := weak_duality n A c s f' diff hprim_cons hprim_nonneg hprim_cap hdual_nonneg hdual_feas
  omega

theorem not_or_of_decide {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (decide p || decide q) = true) :
    ¬ p ∧ ¬ q := by
  have hfalse : (decide p || decide q) = false := by
    cases hbool : (decide p || decide q)
    · rfl
    · contradiction
  rw [Bool.or_eq_false_iff] at hfalse
  rw [decide_eq_false_iff_not, decide_eq_false_iff_not] at hfalse
  exact hfalse

/-- Bridge theorem: any clearing accepted by `judge` certifies ε-optimality
    over all candidate circulations in the order book LP (0 axioms, 0 sorries). -/
theorem judge_certifies_epsilon_optimal (m : Market) (orders : List Order)
    (transfers : List ResourcePosting) (c : Certificate)
    (h_judge : judge m orders transfers c = .ok ()) :
    let n := orders.length
    let A : Fin n → Int := fun i => match (orders.get i).side with | .bid => 1 | .ask => -1
    let cap : Fin n → Int := fun i => if (orders.get i).crosses c.price then ((orders.get i).qty : Int) else 0
    let s : Fin n → Int := fun i => c.slacks.getD i.val 0
    let f : Fin n → Int := fun i => (orders.get i).fill m transfers
    let diff := c.potentials.2 - c.potentials.1
    ∀ (f' : Fin n → Int),
      finSum n (fun i => A i * f' i) = 0 →
      (∀ i, 0 ≤ f' i) →
      (∀ i, f' i ≤ cap i) →
      finSum n f' ≤ finSum n f + (m.epsilon : Int) := by
  unfold judge at h_judge
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  split at h_judge <;> try contradiction
  rename_i h_dual_none
  dsimp only at h_judge
  split at h_judge
  · rename_i h_gap
    split at h_judge
    · contradiction
    · intro n A cap s f diff f' hf'_cons hf'_nonneg hf'_cap
      refine certifies_epsilon_optimal n A cap s f f' diff m.epsilon h_gap hf'_cons hf'_nonneg hf'_cap ?_ ?_
      · intro i
        have hmem : i ∈ List.finRange orders.length := List.mem_finRange i
        have hnone := List.find?_eq_none.mp h_dual_none i hmem
        dsimp at hnone
        revert hnone
        cases (orders.get i).side <;> intro hnone
        · have ⟨hneg, _⟩ := not_or_of_decide hnone
          dsimp [s]
          omega
        · have ⟨hneg, _⟩ := not_or_of_decide hnone
          dsimp [s]
          omega
      · intro i
        have hmem : i ∈ List.finRange orders.length := List.mem_finRange i
        have hnone := List.find?_eq_none.mp h_dual_none i hmem
        dsimp at hnone
        revert hnone
        cases h_side : orders[i.val].side <;> intro hnone
        · have ⟨_, hfeas⟩ := not_or_of_decide hnone
          dsimp [diff, A, s]
          rw [h_side]
          dsimp
          omega
        · have ⟨_, hfeas⟩ := not_or_of_decide hnone
          dsimp [diff, A, s]
          rw [h_side]
          dsimp
          omega
  · contradiction

/-- Full Judge instance registration for Obend runtime. -/
instance drexClearingJudge : Judge ClearingQuery Certificate where
  Clause := ClearingRefusal
  Meaning q c := judge q.market q.orders q.transfers c = .ok ()
  check _ q c :=
    match judge q.market q.orders q.transfers c with
    | .ok () => .ok
    | .error r => .refused r []
  sound := by
    intro r q c h
    split at h
    · rename_i hu
      exact hu
    · contradiction
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c, judge q.market q.orders q.transfers c = .ok ()
  complete := by
    intro o _ ⟨c, hc⟩
    refine ⟨c, 0, ?_⟩
    simp [hc]
  mono := by intro _ _ _ _ _ _; rfl

end Obend.Judge
