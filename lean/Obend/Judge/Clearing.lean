module
/-
# Obend.Judge.Clearing — drex-clearing@1 certified primal-dual LP clearing judge

Verifies market clearing prices, surplus non-negativity, capacity bounds,
dual feasibility, and duality gap ≤ ε in O(N) operations.
Soundness theorem: any certified triple certifies ε-optimality over ALL feasible allocations.

What `judge` decides is stated without it: `CertifiedClearing` is the clearing LP's primal-dual
conditions on a batch and a certificate, as propositions over fills, capacities and slacks, and
`judge_ok_iff` is the theorem that `judge` accepts exactly those. `AdmissibleClearingBatch` (some
certificate satisfies them) is the judge's completeness fragment. A batch in which two orders share
an account is refuted, not merely refused (`judge_duplicateAccount`): no certificate can mean it.

The bodies are sealed (`LAW-M1`): `Order.crosses` and `judge` are exposed, for the downstream
modules that reduce them; everything else is used through its theorems.
-/

public import Obend.Judge.Class
public import Obend.Ledger.Book
public import Obend.Ledger.Seat
import Obend.Tactic.Tooth

public section
namespace Obend.Judge

open Obend.Ledger
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Market, Orders & Certificate -/

structure Market where
  currency : AssetId
  goods : AssetId
  epsilon : Nat
  deriving @[expose] DecidableEq, Repr

inductive Side where
  | bid
  | ask
  deriving @[expose] DecidableEq, Repr

structure Order where
  account : AccountId
  side : Side
  qty : Nat
  total : Nat
  deriving @[expose] DecidableEq, Repr

@[expose] def Order.crosses (price : Nat) (order : Order) : Bool :=
  match order.side with
  | .bid => decide (price * order.qty ≤ order.total)
  | .ask => decide (order.total ≤ price * order.qty)

structure Certificate where
  price : Nat
  potentials : Int × Int
  slacks : List Int
  deriving @[expose] DecidableEq, Repr

structure ClearingQuery where
  market : Market
  orders : List Order
  transfers : List ResourcePosting
  deriving @[expose] DecidableEq, Repr

/-! ## Order Book Analysis: Crossing Pairs & Price Validity -/

def isOrderAccount (orders : List Order) (account : AccountId) : Bool :=
  orders.any fun order => order.account == account

/-- The first account two orders share, if any. Fills are read off the account's net flow
(`Order.fill`), so a batch with two orders from one account would let them share one fill;
`judge` refuses such a batch (`duplicateAccount`, `judge_ok_accounts_nodup`). -/
def firstDuplicateAccount? : List Order → Option AccountId
  | [] => none
  | o :: rest =>
    if rest.any (fun o' => o'.account == o.account) then some o.account
    else firstDuplicateAccount? rest

theorem firstDuplicateAccount?_none_iff :
    ∀ (os : List Order), firstDuplicateAccount? os = none ↔ (os.map (·.account)).Nodup
  | [] => by simp [firstDuplicateAccount?]
  | o :: rest => by
    simp only [firstDuplicateAccount?, List.map_cons, List.nodup_cons, List.mem_map]
    constructor
    · intro h
      split at h
      · cases h
      · rename_i hany
        refine ⟨?_, (firstDuplicateAccount?_none_iff rest).1 h⟩
        rintro ⟨o', ho', he⟩
        apply hany
        exact List.any_eq_true.2 ⟨o', ho', by simp [he]⟩
    · rintro ⟨hnot, hnd⟩
      split
      · rename_i hany
        obtain ⟨o', ho', he⟩ := List.any_eq_true.1 hany
        exact absurd ⟨o', ho', by simpa using he⟩ hnot
      · exact (firstDuplicateAccount?_none_iff rest).2 hnd

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

/-- A crossing pair exists at an integer tick iff the highest bid can trade with the lowest ask
    at some integer price (`ceil(aMin.total / aMin.qty) ≤ floor(bMax.total / bMax.qty)`). -/
def hasCrossingPair (orders : List Order) : Bool :=
  match highestBid? orders, lowestAsk? orders with
  | some bMax, some aMin =>
    let askUnit := (aMin.total + aMin.qty - 1) / aMin.qty
    let bidUnit := bMax.total / bMax.qty
    aMin.total * bMax.qty ≤ bMax.total * aMin.qty && askUnit ≤ bidUnit
  | _, _ => false

/-- Price validity: when integer-crossing orders exist, the proposed price must lie within
    the crossing interval [lowest ask, highest bid] (i.e. cross both endpoints). -/
def priceInCrossingInterval (orders : List Order) (price : Nat) : Bool :=
  match highestBid? orders, lowestAsk? orders with
  | some bMax, some aMin =>
    let askUnit := (aMin.total + aMin.qty - 1) / aMin.qty
    let bidUnit := bMax.total / bMax.qty
    if aMin.total * bMax.qty ≤ bMax.total * aMin.qty && askUnit ≤ bidUnit then
      aMin.crosses price && bMax.crosses price
    else true
  | _, _ => true

/-! ## Net Flow & Order Fills

A fill is read off the ACCOUNT's net flow in the goods asset, so it is an order's fill only when
the account placed one order in the batch. `judge` enforces that (`judge_ok_accounts_nodup`). -/

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
  | duplicateAccount (account : AccountId)
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
  deriving @[expose] DecidableEq, Repr

def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f i.castSucc) + f (Fin.last n)

@[expose] def judge (m : Market) (orders : List Order) (transfers : List ResourcePosting) (c : Certificate) :
    Except ClearingRefusal Unit :=
  if m.currency = m.goods then .error .marketMalformed
  else match transfers.find? (fun t => t.asset ≠ m.currency && t.asset ≠ m.goods) with
  | some t => .error (.foreignAsset t)
  | none =>
    match transfers.find? (fun t => !isOrderAccount orders t.source || !isOrderAccount orders t.destination) with
    | some t => .error (.notAnOrder t)
    | none =>
      match firstDuplicateAccount? orders with
      | some a => .error (.duplicateAccount a)
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

/-- **One order per account**: an accepted batch names every account once, so every
`Order.fill` is that order's fill and not a sum over the account's orders. -/
theorem judge_ok_accounts_nodup (m : Market) (orders : List Order) (transfers : List ResourcePosting)
    (c : Certificate) (h : judge m orders transfers c = .ok ()) :
    (orders.map (·.account)).Nodup := by
  unfold judge at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · contradiction
  · rename_i hdup
    exact (firstDuplicateAccount?_none_iff orders).1 hdup

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

/-- Declarative primal-dual LP clearing specification:
    1. Distinct order accounts (`(q.orders.map Order.account).Nodup`), and
    2. Certified fills are ε-optimal over EVERY feasible circulation `f'` on the order book. -/
def ClearingSemanticMeaning (q : ClearingQuery) (c : Certificate) : Prop :=
  (q.orders.map (·.account)).Nodup ∧
  let n := q.orders.length
  let A : Fin n → Int := fun i => match (q.orders.get i).side with | .bid => 1 | .ask => -1
  let cap : Fin n → Int := fun i => if (q.orders.get i).crosses c.price then ((q.orders.get i).qty : Int) else 0
  let f : Fin n → Int := fun i => (q.orders.get i).fill q.market q.transfers
  ∀ (f' : Fin n → Int),
    finSum n (fun i => A i * f' i) = 0 →
    (∀ i, 0 ≤ f' i) →
    (∀ i, f' i ≤ cap i) →
    finSum n f' ≤ finSum n f + (q.market.epsilon : Int)

/-! ## What `judge` decides, stated without it

The clearing LP over a batch: maximize the matched volume `Σ fᵢ` subject to conservation
`Σ Aᵢ fᵢ = 0` and capacities `0 ≤ fᵢ ≤ capᵢ` (an order's quantity when it is willing at the price,
nothing otherwise). Its dual has one potential spread and a slack per order, `sᵢ ≥ 0` with
`Aᵢ · spread + sᵢ ≥ 1`. A certificate names a price, the spread and the slacks. -/

/-- A limit order is willing to trade at `price`: a bid pays at most its limit, an ask receives at
least its limit. -/
def Order.WillingAt (price : Nat) (o : Order) : Prop :=
  match o.side with
  | .bid => price * o.qty ≤ o.total
  | .ask => o.total ≤ price * o.qty

/-- What an order can trade at `price`: its whole quantity when it is willing, nothing otherwise. -/
def Order.capacityAt (price : Nat) (o : Order) : Int :=
  match o.side with
  | .bid => if price * o.qty ≤ o.total then (o.qty : Int) else 0
  | .ask => if o.total ≤ price * o.qty then (o.qty : Int) else 0

theorem Order.crosses_iff (price : Nat) (o : Order) : o.crosses price = true ↔ o.WillingAt price := by
  unfold Order.crosses Order.WillingAt
  cases o.side <;> simp

theorem Order.capacityAt_eq (price : Nat) (o : Order) :
    o.capacityAt price = if o.crosses price then (o.qty : Int) else 0 := by
  unfold Order.crosses Order.capacityAt
  cases o.side <;> simp

/-- A positive-quantity bid in `orders` whose unit limit is at least every other positive-quantity
bid's unit limit in `orders`. -/
def IsBestBid (orders : List Order) (bMax : Order) : Prop :=
  bMax ∈ orders ∧ bMax.side = .bid ∧ 0 < bMax.qty ∧
    ∀ b ∈ orders, b.side = .bid → 0 < b.qty → b.total * bMax.qty ≤ bMax.total * b.qty

/-- A positive-quantity ask in `orders` whose unit limit is at most every other positive-quantity
ask's unit limit in `orders`. -/
def IsBestAsk (orders : List Order) (aMin : Order) : Prop :=
  aMin ∈ orders ∧ aMin.side = .ask ∧ 0 < aMin.qty ∧
    ∀ a ∈ orders, a.side = .ask → 0 < a.qty → aMin.total * a.qty ≤ a.total * aMin.qty

/-- The best bid and the best ask cross at an integer tick: the ask's limit is at most the bid's,
and the ask's unit limit rounded up is at most the bid's rounded down. -/
def IntegerCrossing (bMax aMin : Order) : Prop :=
  aMin.total * bMax.qty ≤ bMax.total * aMin.qty ∧
    (aMin.total + aMin.qty - 1) / aMin.qty ≤ bMax.total / bMax.qty

/-- The book has a best bid and a best ask that cross at an integer tick. -/
def CrossingBook (orders : List Order) : Prop :=
  ∃ bMax aMin, IsBestBid orders bMax ∧ IsBestAsk orders aMin ∧ IntegerCrossing bMax aMin

/-- **The clearing LP's primal-dual conditions** on a batch and a certificate. In order: the market
has two assets and every posting moves one of them between accounts that placed orders, one order
an account; the price lies in the crossing interval when the book crosses; the postings settle
every order at that one price; the fills (read off the postings) conserve goods and respect each
order's capacity at the price; the slacks are dual feasible; the duality gap is at most `ε`; and a
crossing book is not left wholly unserved. -/
def CertifiedClearing (m : Market) (orders : List Order) (transfers : List ResourcePosting)
    (c : Certificate) : Prop :=
  m.currency ≠ m.goods ∧
  (∀ t ∈ transfers, t.asset = m.currency ∨ t.asset = m.goods) ∧
  (∀ t ∈ transfers, (∃ o ∈ orders, o.account = t.source) ∧ ∃ o ∈ orders, o.account = t.destination) ∧
  (orders.map (·.account)).Nodup ∧
  (∀ bMax aMin, IsBestBid orders bMax → IsBestAsk orders aMin →
    IntegerCrossing bMax aMin → aMin.WillingAt c.price ∧ bMax.WillingAt c.price) ∧
  c.slacks.length = orders.length ∧
  (∀ o ∈ orders, o.paid m transfers = (c.price : Int) * o.fill m transfers) ∧
  finSum orders.length (fun i =>
    match (orders.get i).side with
    | .bid => (orders.get i).fill m transfers
    | .ask => - (orders.get i).fill m transfers) = 0 ∧
  (∀ i : Fin orders.length, 0 ≤ (orders.get i).fill m transfers ∧
    (orders.get i).fill m transfers ≤ (orders.get i).capacityAt c.price) ∧
  (∀ i : Fin orders.length, 0 ≤ c.slacks.getD i.val 0 ∧
    1 ≤ (match (orders.get i).side with
      | .bid => c.potentials.2 - c.potentials.1
      | .ask => - (c.potentials.2 - c.potentials.1)) + c.slacks.getD i.val 0) ∧
  finSum orders.length (fun i => (orders.get i).capacityAt c.price * c.slacks.getD i.val 0) -
      finSum orders.length (fun i => (orders.get i).fill m transfers) ≤ (m.epsilon : Int) ∧
  (finSum orders.length (fun i => (orders.get i).fill m transfers) = 0 → ¬ CrossingBook orders)

/-- **The completeness fragment**: some price, potential spread and slacks satisfy the clearing
LP's primal-dual conditions on the batch. -/
def AdmissibleClearingBatch (q : ClearingQuery) : Prop :=
  ∃ c : Certificate, CertifiedClearing q.market q.orders q.transfers c

/-! ### Best-bid / best-ask scan characterization & unit-limit invariance -/

private theorem unit_le_trans {y cur next : Order} (hcur : 0 < cur.qty)
    (h1 : y.total * cur.qty ≤ cur.total * y.qty)
    (h2 : cur.total * next.qty ≤ next.total * cur.qty) :
    y.total * next.qty ≤ next.total * y.qty := by
  apply Nat.le_of_mul_le_mul_right _ hcur
  calc
    y.total * next.qty * cur.qty = y.total * cur.qty * next.qty := by
      rw [Nat.mul_right_comm]
    _ ≤ cur.total * y.qty * next.qty := Nat.mul_le_mul_right next.qty h1
    _ = cur.total * next.qty * y.qty := by
      rw [Nat.mul_right_comm]
    _ ≤ next.total * cur.qty * y.qty := Nat.mul_le_mul_right y.qty h2
    _ = next.total * y.qty * cur.qty := by
      rw [Nat.mul_right_comm]

private theorem foldl_bestBid_spec (bs : List Order) (init : Order)
    (hInit : 0 < init.qty)
    (hBs : ∀ b ∈ bs, 0 < b.qty) :
    let res := bs.foldl (fun best b => if best.total * b.qty < b.total * best.qty then b else best) init
    (res = init ∨ res ∈ bs) ∧
    0 < res.qty ∧
    init.total * res.qty ≤ res.total * init.qty ∧
    ∀ b ∈ bs, b.total * res.qty ≤ res.total * b.qty := by
  induction bs generalizing init with
  | nil =>
    exact ⟨.inl rfl, hInit, Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
    have hxPos : 0 < x.qty := hBs x (.head _)
    have hxsPos : ∀ b ∈ xs, 0 < b.qty := fun b hb => hBs b (.tail _ hb)
    let next := if init.total * x.qty < x.total * init.qty then x else init
    have hNextPos : 0 < next.qty := by
      dsimp [next]; split <;> assumption
    have hInitNext : init.total * next.qty ≤ next.total * init.qty := by
      dsimp [next]; split
      · rename_i hlt; exact Nat.le_of_lt hlt
      · exact Nat.le_refl _
    have hxNext : x.total * next.qty ≤ next.total * x.qty := by
      dsimp [next]; split
      · exact Nat.le_refl _
      · rename_i hge; omega
    obtain ⟨hMem, hResPos, hNextRes, hXsRes⟩ := ih next hNextPos hxsPos
    refine ⟨?_, hResPos, unit_le_trans hNextPos hInitNext hNextRes, ?_⟩
    · rcases hMem with hEq | hIn
      · dsimp only [List.foldl]
        rw [hEq]
        dsimp [next]; split
        · exact .inr (.head _)
        · exact .inl rfl
      · dsimp only [List.foldl]
        exact .inr (.tail _ hIn)
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact unit_le_trans hNextPos hxNext hNextRes
      · exact hXsRes b hb'

private theorem foldl_bestAsk_spec (as : List Order) (init : Order)
    (hInit : 0 < init.qty)
    (hAs : ∀ a ∈ as, 0 < a.qty) :
    let res := as.foldl (fun best a => if a.total * best.qty < best.total * a.qty then a else best) init
    (res = init ∨ res ∈ as) ∧
    0 < res.qty ∧
    res.total * init.qty ≤ init.total * res.qty ∧
    ∀ a ∈ as, res.total * a.qty ≤ a.total * res.qty := by
  induction as generalizing init with
  | nil =>
    exact ⟨.inl rfl, hInit, Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
    have hxPos : 0 < x.qty := hAs x (.head _)
    have hxsPos : ∀ a ∈ xs, 0 < a.qty := fun a ha => hAs a (.tail _ ha)
    let next := if x.total * init.qty < init.total * x.qty then x else init
    have hNextPos : 0 < next.qty := by
      dsimp [next]; split <;> assumption
    have hNextInit : next.total * init.qty ≤ init.total * next.qty := by
      dsimp [next]; split
      · rename_i hlt; exact Nat.le_of_lt hlt
      · exact Nat.le_refl _
    have hNextX : next.total * x.qty ≤ x.total * next.qty := by
      dsimp [next]; split
      · exact Nat.le_refl _
      · rename_i hge; omega
    obtain ⟨hMem, hResPos, hResNext, hResXs⟩ := ih next hNextPos hxsPos
    refine ⟨?_, hResPos, unit_le_trans hNextPos hResNext hNextInit, ?_⟩
    · rcases hMem with hEq | hIn
      · dsimp only [List.foldl]
        rw [hEq]
        dsimp [next]; split
        · exact .inr (.head _)
        · exact .inl rfl
      · dsimp only [List.foldl]
        exact .inr (.tail _ hIn)
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact unit_le_trans hNextPos hResNext hNextX
      · exact hResXs a ha'

theorem highestBid?_some_isBestBid {orders : List Order} {bMax : Order}
    (h : highestBid? orders = some bMax) : IsBestBid orders bMax := by
  unfold highestBid? at h
  dsimp only at h
  cases hFilt : orders.filter (fun o => o.side == .bid && o.qty > 0) with
  | nil => rw [hFilt] at h; cases h
  | cons b bs =>
    rw [hFilt, Option.some.injEq] at h
    have hMemFilt : ∀ x ∈ b :: bs, x ∈ orders ∧ x.side = .bid ∧ 0 < x.qty := by
      intro x hx
      rw [← hFilt, List.mem_filter] at hx
      obtain ⟨hIn, hPred⟩ := hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hPred
      exact ⟨hIn, hPred.1, hPred.2⟩
    obtain ⟨hbIn, hbSide, hbPos⟩ := hMemFilt b (.head _)
    have hbsPos : ∀ x ∈ bs, 0 < x.qty := fun x hx => (hMemFilt x (.tail _ hx)).2.2
    obtain ⟨hResMem, hResPos, hInitLe, hBsLe⟩ := foldl_bestBid_spec bs b hbPos hbsPos
    rw [h] at hResMem hResPos hInitLe hBsLe
    have hBMaxMem : bMax ∈ b :: bs := by
      rcases hResMem with rfl | hIn
      · exact .head _
      · exact .tail _ hIn
    obtain ⟨hInOrders, hSide, _⟩ := hMemFilt bMax hBMaxMem
    refine ⟨hInOrders, hSide, hResPos, ?_⟩
    intro o ho hoSide hoPos
    have hoFilt : o ∈ b :: bs := by
      rw [← hFilt, List.mem_filter]
      exact ⟨ho, by simp [hoSide, hoPos]⟩
    rcases List.mem_cons.mp hoFilt with rfl | hoBs
    · exact hInitLe
    · exact hBsLe o hoBs

theorem highestBid?_none_not_isBestBid {orders : List Order}
    (h : highestBid? orders = none) {bMax : Order} (hb : IsBestBid orders bMax) : False := by
  unfold highestBid? at h
  dsimp only at h
  obtain ⟨hIn, hSide, hPos, _⟩ := hb
  have hMemFilt : bMax ∈ orders.filter (fun o => o.side == .bid && o.qty > 0) := by
    rw [List.mem_filter]
    exact ⟨hIn, by simp [hSide, hPos]⟩
  cases hFilt : orders.filter (fun o => o.side == .bid && o.qty > 0) with
  | nil => rw [hFilt] at hMemFilt; cases hMemFilt
  | cons b bs => rw [hFilt] at h; cases h

theorem lowestAsk?_some_isBestAsk {orders : List Order} {aMin : Order}
    (h : lowestAsk? orders = some aMin) : IsBestAsk orders aMin := by
  unfold lowestAsk? at h
  dsimp only at h
  cases hFilt : orders.filter (fun o => o.side == .ask && o.qty > 0) with
  | nil => rw [hFilt] at h; cases h
  | cons a as =>
    rw [hFilt, Option.some.injEq] at h
    have hMemFilt : ∀ x ∈ a :: as, x ∈ orders ∧ x.side = .ask ∧ 0 < x.qty := by
      intro x hx
      rw [← hFilt, List.mem_filter] at hx
      obtain ⟨hIn, hPred⟩ := hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hPred
      exact ⟨hIn, hPred.1, hPred.2⟩
    obtain ⟨haIn, haSide, haPos⟩ := hMemFilt a (.head _)
    have hasPos : ∀ x ∈ as, 0 < x.qty := fun x hx => (hMemFilt x (.tail _ hx)).2.2
    obtain ⟨hResMem, hResPos, hInitLe, hAsLe⟩ := foldl_bestAsk_spec as a haPos hasPos
    rw [h] at hResMem hResPos hInitLe hAsLe
    have hAMinMem : aMin ∈ a :: as := by
      rcases hResMem with rfl | hIn
      · exact .head _
      · exact .tail _ hIn
    obtain ⟨hInOrders, hSide, _⟩ := hMemFilt aMin hAMinMem
    refine ⟨hInOrders, hSide, hResPos, ?_⟩
    intro o ho hoSide hoPos
    have hoFilt : o ∈ a :: as := by
      rw [← hFilt, List.mem_filter]
      exact ⟨ho, by simp [hoSide, hoPos]⟩
    rcases List.mem_cons.mp hoFilt with rfl | hoAs
    · exact hInitLe
    · exact hAsLe o hoAs

theorem lowestAsk?_none_not_isBestAsk {orders : List Order}
    (h : lowestAsk? orders = none) {aMin : Order} (ha : IsBestAsk orders aMin) : False := by
  unfold lowestAsk? at h
  dsimp only at h
  obtain ⟨hIn, hSide, hPos, _⟩ := ha
  have hMemFilt : aMin ∈ orders.filter (fun o => o.side == .ask && o.qty > 0) := by
    rw [List.mem_filter]
    exact ⟨hIn, by simp [hSide, hPos]⟩
  cases hFilt : orders.filter (fun o => o.side == .ask && o.qty > 0) with
  | nil => rw [hFilt] at hMemFilt; cases hMemFilt
  | cons a as => rw [hFilt] at h; cases h

private theorem nat_floor_eq_of_cross_eq {t1 q1 t2 q2 : Nat}
    (hq1 : 0 < q1) (hq2 : 0 < q2) (hEq : t1 * q2 = t2 * q1) :
    t1 / q1 = t2 / q2 := by
  have hle : ∀ {a b c d : Nat}, 0 < b → 0 < d → a * d = c * b → a / b ≤ c / d := by
    intro a b c d hb hd heq
    rw [Nat.le_div_iff_mul_le hd]
    apply Nat.le_of_mul_le_mul_right _ hb
    calc
      a / b * d * b = a / b * b * d := by rw [Nat.mul_right_comm]
      _ ≤ a * d := Nat.mul_le_mul_right d (Nat.div_mul_le_self a b)
      _ = c * b := heq
  exact Nat.le_antisymm (hle hq1 hq2 hEq) (hle hq2 hq1 hEq.symm)

private theorem ceil_div_le_iff {t q k : Nat} (hq : 0 < q) :
    (t + q - 1) / q ≤ k ↔ t ≤ k * q := by
  have hlt : (t + q - 1) / q ≤ k ↔ (t + q - 1) / q < k + 1 := by omega
  rw [hlt, Nat.div_lt_iff_lt_mul hq, Nat.succ_mul]
  omega

private theorem nat_ceil_eq_of_cross_eq {t1 q1 t2 q2 : Nat}
    (hq1 : 0 < q1) (hq2 : 0 < q2) (hEq : t1 * q2 = t2 * q1) :
    (t1 + q1 - 1) / q1 = (t2 + q2 - 1) / q2 := by
  have hle : ∀ {a b c d : Nat}, 0 < b → 0 < d → a * d = c * b →
      (a + b - 1) / b ≤ (c + d - 1) / d := by
    intro a b c d hb hd heq
    rw [ceil_div_le_iff hb]
    have hc : c ≤ ((c + d - 1) / d) * d := (ceil_div_le_iff hd).mp (Nat.le_refl _)
    apply Nat.le_of_mul_le_mul_right _ hd
    calc
      a * d = c * b := heq
      _ ≤ ((c + d - 1) / d) * d * b := Nat.mul_le_mul_right b hc
      _ = ((c + d - 1) / d) * b * d := by rw [Nat.mul_right_comm]
  exact Nat.le_antisymm (hle hq1 hq2 hEq) (hle hq2 hq1 hEq.symm)

private theorem integerCrossing_congr {b1 b2 a1 a2 : Order}
    (hb1 : 0 < b1.qty) (hb2 : 0 < b2.qty) (ha1 : 0 < a1.qty) (ha2 : 0 < a2.qty)
    (hbEq : b1.total * b2.qty = b2.total * b1.qty)
    (haEq : a1.total * a2.qty = a2.total * a1.qty) :
    IntegerCrossing b1 a1 ↔ IntegerCrossing b2 a2 := by
  have hCrossImp : ∀ {x1 x2 y1 y2 : Order},
      0 < x1.qty → 0 < y1.qty →
      x1.total * x2.qty = x2.total * x1.qty →
      y1.total * y2.qty = y2.total * y1.qty →
      y1.total * x1.qty ≤ x1.total * y1.qty →
      y2.total * x2.qty ≤ x2.total * y2.qty := by
    intro x1 x2 y1 y2 hx1 hy1 hxEq hyEq hle
    apply Nat.le_of_mul_le_mul_right _ hx1
    apply Nat.le_of_mul_le_mul_right _ hy1
    calc
      y2.total * x2.qty * x1.qty * y1.qty = (y2.total * y1.qty) * (x2.qty * x1.qty) := by
        rw [Nat.mul_right_comm (y2.total * x2.qty) x1.qty y1.qty,
          Nat.mul_right_comm y2.total x2.qty y1.qty, Nat.mul_assoc]
      _ = (y1.total * y2.qty) * (x2.qty * x1.qty) := by rw [hyEq]
      _ = (y1.total * x1.qty) * (y2.qty * x2.qty) := by
        rw [Nat.mul_comm x2.qty x1.qty, ← Nat.mul_assoc,
          Nat.mul_right_comm y1.total y2.qty x1.qty, Nat.mul_assoc]
      _ ≤ (x1.total * y1.qty) * (y2.qty * x2.qty) := Nat.mul_le_mul_right _ hle
      _ = (x1.total * x2.qty) * (y1.qty * y2.qty) := by
        rw [Nat.mul_comm y2.qty x2.qty, ← Nat.mul_assoc,
          Nat.mul_right_comm x1.total y1.qty x2.qty, Nat.mul_assoc]
      _ = (x2.total * x1.qty) * (y1.qty * y2.qty) := by rw [hxEq]
      _ = x2.total * y2.qty * x1.qty * y1.qty := by
        rw [Nat.mul_comm y1.qty y2.qty, ← Nat.mul_assoc,
          Nat.mul_right_comm x2.total x1.qty y2.qty]
  unfold IntegerCrossing
  rw [nat_ceil_eq_of_cross_eq ha1 ha2 haEq, nat_floor_eq_of_cross_eq hb1 hb2 hbEq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨hCrossImp hb1 ha1 hbEq haEq h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨hCrossImp hb2 ha2 hbEq.symm haEq.symm h1, h2⟩⟩

private theorem willingAt_bid_congr {price : Nat} {b1 b2 : Order}
    (hs1 : b1.side = .bid) (hs2 : b2.side = .bid)
    (hb1 : 0 < b1.qty) (hbEq : b1.total * b2.qty = b2.total * b1.qty)
    (hw : b1.WillingAt price) : b2.WillingAt price := by
  unfold Order.WillingAt at hw ⊢
  rw [hs1] at hw
  rw [hs2]
  apply Nat.le_of_mul_le_mul_right _ hb1
  calc
    price * b2.qty * b1.qty = price * b1.qty * b2.qty := by rw [Nat.mul_right_comm]
    _ ≤ b1.total * b2.qty := Nat.mul_le_mul_right _ hw
    _ = b2.total * b1.qty := hbEq

private theorem willingAt_ask_congr {price : Nat} {a1 a2 : Order}
    (hs1 : a1.side = .ask) (hs2 : a2.side = .ask)
    (ha1 : 0 < a1.qty) (haEq : a1.total * a2.qty = a2.total * a1.qty)
    (hw : a1.WillingAt price) : a2.WillingAt price := by
  unfold Order.WillingAt at hw ⊢
  rw [hs1] at hw
  rw [hs2]
  apply Nat.le_of_mul_le_mul_right _ ha1
  calc
    a2.total * a1.qty = a1.total * a2.qty := haEq.symm
    _ ≤ price * a1.qty * a2.qty := Nat.mul_le_mul_right _ hw
    _ = price * a2.qty * a1.qty := by rw [Nat.mul_right_comm]

/-! ### Each scan of `judge` is its clause -/

theorem isOrderAccount_iff (orders : List Order) (account : AccountId) :
    isOrderAccount orders account = true ↔ ∃ o ∈ orders, o.account = account := by
  simp [isOrderAccount]

theorem foreign_none_iff (m : Market) (transfers : List ResourcePosting) :
    transfers.find? (fun t => t.asset ≠ m.currency && t.asset ≠ m.goods) = none ↔
      ∀ t ∈ transfers, t.asset = m.currency ∨ t.asset = m.goods := by
  rw [List.find?_eq_none]
  constructor
  · intro h t ht
    have h' := h t ht
    by_cases h1 : t.asset = m.currency
    · exact .inl h1
    · by_cases h2 : t.asset = m.goods
      · exact .inr h2
      · simp [h1, h2] at h'
  · intro h t ht
    rcases h t ht with h1 | h2
    · simp [h1]
    · simp [h2]

theorem notAnOrder_none_iff (orders : List Order) (transfers : List ResourcePosting) :
    transfers.find? (fun t => !isOrderAccount orders t.source || !isOrderAccount orders t.destination) = none ↔
      ∀ t ∈ transfers, (∃ o ∈ orders, o.account = t.source) ∧ ∃ o ∈ orders, o.account = t.destination := by
  rw [List.find?_eq_none]
  constructor
  · intro h t ht
    have h' := h t ht
    cases hs : isOrderAccount orders t.source <;> cases hd : isOrderAccount orders t.destination <;>
      simp [hs, hd] at h'
    exact ⟨(isOrderAccount_iff _ _).1 hs, (isOrderAccount_iff _ _).1 hd⟩
  · intro h t ht
    obtain ⟨hs, hd⟩ := h t ht
    simp [(isOrderAccount_iff _ _).2 hs, (isOrderAccount_iff _ _).2 hd]

private theorem isBestBid_unit_eq {orders : List Order} {b1 b2 : Order}
    (hb1 : IsBestBid orders b1) (hb2 : IsBestBid orders b2) :
    b1.total * b2.qty = b2.total * b1.qty :=
  Nat.le_antisymm (hb2.2.2.2 b1 hb1.1 hb1.2.1 hb1.2.2.1) (hb1.2.2.2 b2 hb2.1 hb2.2.1 hb2.2.2.1)

private theorem isBestAsk_unit_eq {orders : List Order} {a1 a2 : Order}
    (ha1 : IsBestAsk orders a1) (ha2 : IsBestAsk orders a2) :
    a1.total * a2.qty = a2.total * a1.qty :=
  Nat.le_antisymm (ha1.2.2.2 a2 ha2.1 ha2.2.1 ha2.2.2.1) (ha2.2.2.2 a1 ha1.1 ha1.2.1 ha1.2.2.1)

theorem priceInCrossingInterval_iff (orders : List Order) (price : Nat) :
    priceInCrossingInterval orders price = true ↔
      ∀ bMax aMin, IsBestBid orders bMax → IsBestAsk orders aMin →
        IntegerCrossing bMax aMin → aMin.WillingAt price ∧ bMax.WillingAt price := by
  unfold priceInCrossingInterval
  cases hBid : highestBid? orders with
  | none =>
    simp only [true_iff]
    intro bMax _ hb _ _
    exact (highestBid?_none_not_isBestBid hBid hb).elim
  | some b =>
    cases hAsk : lowestAsk? orders with
    | none =>
      simp only [true_iff]
      intro _ aMin _ ha _
      exact (lowestAsk?_none_not_isBestAsk hAsk ha).elim
    | some a =>
      have hbBest : IsBestBid orders b := highestBid?_some_isBestBid hBid
      have haBest : IsBestAsk orders a := lowestAsk?_some_isBestAsk hAsk
      dsimp only
      constructor
      · intro h bMax aMin hb ha hx
        have hbEq := isBestBid_unit_eq hbBest hb
        have haEq := isBestAsk_unit_eq haBest ha
        have hxa : IntegerCrossing b a :=
          (integerCrossing_congr hbBest.2.2.1 hb.2.2.1 haBest.2.2.1 ha.2.2.1 hbEq haEq).mpr hx
        split at h
        · simp only [Bool.and_eq_true] at h
          have haW : a.WillingAt price := (Order.crosses_iff price a).mp h.1
          have hbW : b.WillingAt price := (Order.crosses_iff price b).mp h.2
          exact ⟨willingAt_ask_congr haBest.2.1 ha.2.1 haBest.2.2.1 haEq haW,
            willingAt_bid_congr hbBest.2.1 hb.2.1 hbBest.2.2.1 hbEq hbW⟩
        · rename_i hNotCond
          exfalso
          apply hNotCond
          simp [hxa.1, hxa.2]
      · intro h
        split
        · rename_i hCond
          have hxa : IntegerCrossing b a := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
            exact hCond
          obtain ⟨haW, hbW⟩ := h b a hbBest haBest hxa
          simp [(Order.crosses_iff price a).mpr haW, (Order.crosses_iff price b).mpr hbW]
        · rfl

theorem hasCrossingPair_iff (orders : List Order) : hasCrossingPair orders = true ↔ CrossingBook orders := by
  unfold hasCrossingPair CrossingBook
  cases hBid : highestBid? orders with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨bMax, _, hb, _, _⟩
    exact highestBid?_none_not_isBestBid hBid hb
  | some b =>
    cases hAsk : lowestAsk? orders with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨_, aMin, _, ha, _⟩
      exact lowestAsk?_none_not_isBestAsk hAsk ha
    | some a =>
      have hbBest : IsBestBid orders b := highestBid?_some_isBestBid hBid
      have haBest : IsBestAsk orders a := lowestAsk?_some_isBestAsk hAsk
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro hx
        exact ⟨b, a, hbBest, haBest, hx⟩
      · rintro ⟨bMax, aMin, hb, ha, hx⟩
        have hbEq := isBestBid_unit_eq hbBest hb
        have haEq := isBestAsk_unit_eq haBest ha
        exact (integerCrossing_congr hbBest.2.2.1 hb.2.2.1 haBest.2.2.1 ha.2.2.1 hbEq haEq).mpr hx

theorem uniform_none_iff (m : Market) (orders : List Order) (transfers : List ResourcePosting) (price : Nat) :
    orders.find? (fun o => o.paid m transfers ≠ (price : Int) * o.fill m transfers) = none ↔
      ∀ o ∈ orders, o.paid m transfers = (price : Int) * o.fill m transfers := by
  rw [List.find?_eq_none]
  constructor
  · intro h o ho
    have h' := h o ho
    simpa using h'
  · intro h o ho
    simp [h o ho]

theorem primal_none_iff (m : Market) (orders : List Order) (transfers : List ResourcePosting) (price : Nat) :
    (List.finRange orders.length).find? (fun i =>
        let f := (orders.get i).fill m transfers
        let cap := if (orders.get i).crosses price then ((orders.get i).qty : Int) else 0
        f < 0 || cap < f) = none ↔
      ∀ i : Fin orders.length, 0 ≤ (orders.get i).fill m transfers ∧
        (orders.get i).fill m transfers ≤ (orders.get i).capacityAt price := by
  rw [List.find?_eq_none]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := not_or_of_decide (h i (List.mem_finRange i))
    rw [Order.capacityAt_eq]
    exact ⟨Int.not_lt.1 h1, Int.not_lt.1 h2⟩
  · intro h i _
    obtain ⟨h1, h2⟩ := h i
    rw [Order.capacityAt_eq] at h2
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt]
    exact ⟨h1, h2⟩

theorem dual_none_iff (orders : List Order) (c : Certificate) :
    (List.finRange orders.length).find? (fun i =>
        let s := c.slacks.getD i.val 0
        let o := orders.get i
        let dualDiff := c.potentials.2 - c.potentials.1
        s < 0 ||
        match o.side with
        | .bid => dualDiff + s < 1
        | .ask => -dualDiff + s < 1) = none ↔
      ∀ i : Fin orders.length, 0 ≤ c.slacks.getD i.val 0 ∧
        1 ≤ (match (orders.get i).side with
          | .bid => c.potentials.2 - c.potentials.1
          | .ask => - (c.potentials.2 - c.potentials.1)) + c.slacks.getD i.val 0 := by
  rw [List.find?_eq_none]
  constructor
  · intro h i
    have hi := h i (List.mem_finRange i)
    dsimp only at hi
    revert hi
    cases (orders.get i).side with
    | bid =>
      intro hi
      obtain ⟨h1, h2⟩ := not_or_of_decide hi
      refine ⟨Int.not_lt.1 h1, ?_⟩
      show 1 ≤ c.potentials.2 - c.potentials.1 + c.slacks.getD i.val 0
      omega
    | ask =>
      intro hi
      obtain ⟨h1, h2⟩ := not_or_of_decide hi
      refine ⟨Int.not_lt.1 h1, ?_⟩
      show 1 ≤ - (c.potentials.2 - c.potentials.1) + c.slacks.getD i.val 0
      omega
  · intro h i _
    obtain ⟨h1, h2⟩ := h i
    dsimp only
    revert h2
    cases (orders.get i).side with
    | bid =>
      intro h2
      have h2' : 1 ≤ c.potentials.2 - c.potentials.1 + c.slacks.getD i.val 0 := h2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    | ask =>
      intro h2
      have h2' : 1 ≤ - (c.potentials.2 - c.potentials.1) + c.slacks.getD i.val 0 := h2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega

theorem error_ne_ok {P : Prop} {r : ClearingRefusal} (h : ¬ P) :
    (Except.error r : Except ClearingRefusal Unit) = .ok () ↔ P :=
  ⟨fun e => (by cases e), fun p => absurd p h⟩

/-- **`judge` accepts exactly the clearing LP's primal-dual conditions.** Each refusal is the
failure of one clause of `CertifiedClearing`, and an acceptance is all of them. -/
theorem judge_ok_iff (m : Market) (orders : List Order) (transfers : List ResourcePosting) (c : Certificate) :
    judge m orders transfers c = .ok () ↔ CertifiedClearing m orders transfers c := by
  unfold judge
  split
  · rename_i hm
    exact error_ne_ok fun hP => hP.1 hm
  rename_i hm
  split
  · rename_i t ht
    refine error_ne_ok fun hP => ?_
    have h := ht.symm.trans ((foreign_none_iff m transfers).2 hP.2.1)
    cases h
  rename_i hforeign
  split
  · rename_i t ht
    refine error_ne_ok fun hP => ?_
    have h := ht.symm.trans ((notAnOrder_none_iff orders transfers).2 hP.2.2.1)
    cases h
  rename_i hparty
  split
  · rename_i a ha
    refine error_ne_ok fun hP => ?_
    have h := ha.symm.trans ((firstDuplicateAccount?_none_iff orders).2 hP.2.2.2.1)
    cases h
  rename_i hdup
  split
  · rename_i hprice
    refine error_ne_ok fun hP => ?_
    rw [(priceInCrossingInterval_iff orders c.price).2 hP.2.2.2.2.1] at hprice
    cases hprice
  rename_i hprice
  split
  · rename_i hlen
    exact error_ne_ok fun hP => hlen hP.2.2.2.2.2.1
  rename_i hlen
  split
  · rename_i o ho
    refine error_ne_ok fun hP => ?_
    have h := ho.symm.trans ((uniform_none_iff m orders transfers c.price).2 hP.2.2.2.2.2.2.1)
    cases h
  rename_i huniform
  split
  · rename_i hcons
    exact error_ne_ok fun hP => hcons hP.2.2.2.2.2.2.2.1
  rename_i hcons
  split
  · rename_i i hi
    refine error_ne_ok fun hP => ?_
    have h := hi.symm.trans ((primal_none_iff m orders transfers c.price).2 hP.2.2.2.2.2.2.2.2.1)
    cases h
  rename_i hprimal
  split
  · rename_i i hi
    refine error_ne_ok fun hP => ?_
    have h := hi.symm.trans ((dual_none_iff orders c).2 hP.2.2.2.2.2.2.2.2.2.1)
    cases h
  rename_i hdual
  have hcap : (fun i : Fin orders.length =>
      (if (orders.get i).crosses c.price then ((orders.get i).qty : Int) else 0) * c.slacks.getD i.val 0) =
      fun i => (orders.get i).capacityAt c.price * c.slacks.getD i.val 0 := by
    funext i; rw [Order.capacityAt_eq]
  dsimp only
  rw [hcap]
  split
  · rename_i hgap
    split
    · rename_i hunserved
      refine error_ne_ok fun hP => ?_
      simp only [Bool.and_eq_true, beq_iff_eq] at hunserved
      exact hP.2.2.2.2.2.2.2.2.2.2.2 hunserved.1 ((hasCrossingPair_iff orders).1 hunserved.2)
    · rename_i hserved
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      refine ⟨hm, (foreign_none_iff m transfers).1 hforeign, (notAnOrder_none_iff orders transfers).1 hparty,
        (firstDuplicateAccount?_none_iff orders).1 hdup, ?_, Decidable.not_not.1 hlen,
        (uniform_none_iff m orders transfers c.price).1 huniform, Decidable.not_not.1 hcons,
        (primal_none_iff m orders transfers c.price).1 hprimal, (dual_none_iff orders c).1 hdual, hgap, ?_⟩
      · apply (priceInCrossingInterval_iff orders c.price).1
        cases hp : priceInCrossingInterval orders c.price
        · simp [hp] at hprice
        · rfl
      · intro hzero hcross
        apply hserved
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨hzero, (hasCrossingPair_iff orders).2 hcross⟩
  · rename_i hgap
    exact error_ne_ok fun hP => hgap hP.2.2.2.2.2.2.2.2.2.2.1

/-- **A batch is admissible exactly when `judge` accepts it under some certificate.** -/
theorem admissibleClearingBatch_iff_judge_ok (q : ClearingQuery) :
    AdmissibleClearingBatch q ↔ ∃ c, judge q.market q.orders q.transfers c = .ok () :=
  ⟨fun ⟨c, hc⟩ => ⟨c, (judge_ok_iff _ _ _ c).2 hc⟩, fun ⟨c, hc⟩ => ⟨c, (judge_ok_iff _ _ _ c).1 hc⟩⟩

/-- **Two orders from one account refute the batch**: `judge` reports `duplicateAccount` only when
the batch names an account twice, and then no certificate can mean it (`ClearingSemanticMeaning`
reads each fill off its account's net flow). -/
theorem judge_duplicateAccount {m : Market} {orders : List Order} {transfers : List ResourcePosting}
    {c : Certificate} {a : AccountId} (h : judge m orders transfers c = .error (.duplicateAccount a)) :
    ¬ (orders.map (·.account)).Nodup := by
  intro hnd
  have hdup := (firstDuplicateAccount?_none_iff orders).2 hnd
  unfold judge at h
  rw [hdup] at h
  dsimp only at h
  repeat' split at h
  all_goals cases h

/-- Full Judge instance registration for Obend runtime. -/
instance drexClearingJudge : Judge ClearingQuery Certificate where
  Clause := ClearingRefusal
  Meaning := ClearingSemanticMeaning
  check _ q c :=
    match judge q.market q.orders q.transfers c with
    | .ok () => .ok
    | .error r => .refused r []
  sound := by
    intro _ q c h
    split at h
    · rename_i hu
      exact ⟨judge_ok_accounts_nodup q.market q.orders q.transfers c hu,
        judge_certifies_epsilon_optimal q.market q.orders q.transfers c hu⟩
    · contradiction
  refutes
    | .duplicateAccount _ => true
    | _ => false
  refuted := by
    intro _ q c k p h hk c' hm
    obtain ⟨hnd, _⟩ := hm
    split at h
    · cases h
    · rename_i hr
      cases h
      cases k <;> first | exact judge_duplicateAccount hr hnd | cases hk
  Fragment := AdmissibleClearingBatch
  complete := by
    intro q hq _
    obtain ⟨c, hc⟩ := (admissibleClearingBatch_iff_judge_ok q).1 hq
    refine ⟨c, 0, ?_⟩
    simp [hc]
  mono := by intro _ _ _ _ _ _; rfl

/-! ## Witnesses and teeth -/

/-- One bid and one ask at the same limit, settled at it: one unit of goods for ten of currency. -/
def matchedPair : ClearingQuery where
  market := { currency := 0, goods := 1, epsilon := 0 }
  orders := [⟨1, .bid, 1, 10⟩, ⟨2, .ask, 1, 10⟩]
  transfers := [⟨2, 1, 1, 1⟩, ⟨1, 2, 0, 10⟩]

/-- Its certificate: price ten, no potential spread, unit slacks (the gap is zero). -/
def matchedPairCert : Certificate := ⟨10, (0, 0), [1, 1]⟩

/-- A bid and an ask placed by one account, with nothing settled. -/
def sharedAccount : ClearingQuery where
  market := { currency := 0, goods := 1, epsilon := 0 }
  orders := [⟨1, .bid, 1, 10⟩, ⟨1, .ask, 1, 10⟩]
  transfers := []

example : CertifiedClearing matchedPair.market matchedPair.orders matchedPair.transfers matchedPairCert :=
  (judge_ok_iff _ _ _ _).1 (by rfl)

example : AdmissibleClearingBatch matchedPair :=
  (admissibleClearingBatch_iff_judge_ok _).2 ⟨matchedPairCert, by rfl⟩

example : drexClearingJudge.check 0 matchedPair matchedPairCert = .ok := by rfl

example (c : Certificate) : ¬ ClearingSemanticMeaning sharedAccount c :=
  drexClearingJudge.refuted (r := 0) (c := matchedPairCert) (k := .duplicateAccount 1) (p := []) (by rfl) rfl c

#tooth judge_ok_iff by mutation judge := fun _ _ _ _ => .ok ()
#tooth judge_duplicateAccount by mutation judge := fun _ _ _ _ => .error (.duplicateAccount 0)
#tooth judge_ok_iff by mutation Order.capacityAt := fun _ o => (o.qty : Int)
#tooth judge_ok_iff by mutation highestBid? := fun _ => none
#tooth judge_ok_iff by mutation lowestAsk? := fun _ => none

end Obend.Judge
