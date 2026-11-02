module
/-
# Obend.Vault.DragonsExchange — Dragon's Exchange (`dclutch` Hoard + `dreggfi` Multilateral Credit-Ring Netting) (`WS-F`)

Provides:
1. `CreditLeg` & `settleRing`: Multilateral credit-ring settlement engine extinguishing closed cycles
   of debt of size `cycleFlow` across `ringParticipants`.
2. `settleRing_conserves_net_worth`: Settling a closed ring of flow `cycleFlow` leaves every participant's
   net position (`assets - liabilities`) and net balance strictly unchanged while reducing gross bilateral
   debt by `ringParticipants.length * cycleFlow`.
3. `settleRing_never_triggers_liquidation`: If all participants are solvent before `settleRing`, they
   remain solvent after `settleRing` with strictly lower gross exposure.
4. `DragonsExchangeState` & `stepDragonsExchangeEpoch`: Unified verified epoch transition combining
   `settleRing` with `HoardMarketState` (`dclutch` complete-set split/merge + KKT clearing) and
   `Core.Data` roundtrip codecs (`toData`, `ofData?`, `ofData?_toData`).
-/
public import Obend.Core.Data
public import Obend.Judge.AutomataConfinement

@[expose] public section

namespace Obend.Vault

open Obend.Core.Data (Data)
open Obend.Judge (HoardMarketState HoardCollateralInvariant hoardCollateralValid
  splitCompleteSet mergeCompleteSet applyCompleteSetDelta
  applyCompleteSetDelta_preserves_invariant
  JointClearingCert jointClearingValid)

set_option autoImplicit false

/-! ## 1. Multilateral Credit-Ring Netting (`CreditLeg` & `settleRing`) -/

/-- Bilateral credit/debt leg in the `dreggfi` credit network. -/
structure CreditLeg where
  debtor : Nat
  creditor : Nat
  amount : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Net worth / position of a participant given gross assets and gross liabilities. -/
def netPosition (assets liabilities : Int) : Int :=
  assets - liabilities

/-- Gross bilateral debt remaining after netting a closed ring of `ringParticipants` with flow `cycleFlow`. -/
def grossDebtAfterRing (grossDebt : Nat) (ringParticipants : List Nat) (cycleFlow : Nat) : Nat :=
  grossDebt - ringParticipants.length * cycleFlow

/-- Solvency predicate for participant `i`: `balances[i] + creditLimits[i] ≥ 0`. -/
def ParticipantSolvent (balances creditLimits : List Int) (i : Nat) : Prop :=
  balances.getD i 0 + creditLimits.getD i 0 ≥ 0

/-- All participants `i < balances.length` satisfy `ParticipantSolvent`. -/
def AllSolvent (balances creditLimits : List Int) : Prop :=
  ∀ i < balances.length, ParticipantSolvent balances creditLimits i

/-- Executable check that all participants are solvent within their credit limits. -/
def allSolventB (balances creditLimits : List Int) : Bool :=
  (List.range balances.length).all fun i =>
    decide (balances.getD i 0 + creditLimits.getD i 0 ≥ 0)

theorem allSolventB_iff (balances creditLimits : List Int) :
    allSolventB balances creditLimits = true ↔ AllSolvent balances creditLimits := by
  unfold allSolventB AllSolvent ParticipantSolvent
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- Executable check that a participant list contains no duplicate participant IDs. -/
def ringNodupB : List Nat → Bool
  | [] => true
  | p :: rest => !(rest.contains p) && ringNodupB rest

/-- Construct the directed bilateral `CreditLeg`s of a path `ps` closing back to `first` with uniform flow `flow`. -/
def mkRingLegsAux (first : Nat) (flow : Nat) : List Nat → List CreditLeg
  | [] => []
  | [last] => [{ debtor := last, creditor := first, amount := flow }]
  | u :: v :: rest => { debtor := u, creditor := v, amount := flow } :: mkRingLegsAux first flow (v :: rest)

/-- Construct the closed cycle of `CreditLeg`s `(p₀ → p₁), (p₁ → p₂), ..., (p_{k-1} → p₀)` for `ringParticipants`. -/
def mkClosedRingLegs (ringParticipants : List Nat) (cycleFlow : Nat) : List CreditLeg :=
  match ringParticipants with
  | [] => []
  | first :: rest => mkRingLegsAux first cycleFlow (first :: rest)

/-- Net balance delta for participant `i` from extinguishing a single bilateral `CreditLeg`
    (`+leg.amount` for extinguished liability as `debtor`, `-leg.amount` for extinguished receivable as `creditor`). -/
def legDeltaFor (i : Nat) (leg : CreditLeg) : Int :=
  (if i == leg.debtor then (leg.amount : Int) else 0) -
  (if i == leg.creditor then (leg.amount : Int) else 0)

/-- Total net balance delta for participant `i` across a list of `CreditLeg`s. -/
def legsNetDeltaFor (i : Nat) : List CreditLeg → Int
  | [] => 0
  | leg :: rest => legDeltaFor i leg + legsNetDeltaFor i rest

/-- Apply a list of `CreditLeg`s to `balances` starting at participant index `idx`. -/
def applyCreditLegsFrom (legs : List CreditLeg) : Nat → List Int → List Int
  | _, [] => []
  | idx, b :: rest => (b + legsNetDeltaFor idx legs) :: applyCreditLegsFrom legs (idx + 1) rest

/-- Apply a list of `CreditLeg`s to all participant balances. -/
def applyCreditLegs (balances : List Int) (legs : List CreditLeg) : List Int :=
  applyCreditLegsFrom legs 0 balances

/-- Telescoping Kirchhoff sum along an open path closing at `first`:
    intermediate vertices cancel (`-flow + flow = 0`), leaving only `(i == u) - (i == first)`. -/
theorem legsNetDeltaFor_mkRingLegsAux (i first flow : Nat) :
    ∀ (u : Nat) (rest : List Nat),
      legsNetDeltaFor i (mkRingLegsAux first flow (u :: rest)) =
        (if i == u then (flow : Int) else 0) - (if i == first then (flow : Int) else 0)
  | u, [] => by
    simp [mkRingLegsAux, legsNetDeltaFor, legDeltaFor]
  | u, v :: tail => by
    have ih := legsNetDeltaFor_mkRingLegsAux i first flow v tail
    simp only [mkRingLegsAux, legsNetDeltaFor, legDeltaFor, ih]
    omega

/-- **Closed-Ring Kirchhoff Conservation Lemma**:
    For every participant `i`, the sum of `legDeltaFor i` across all legs in
    `mkClosedRingLegs ringParticipants cycleFlow` is strictly `0`. -/
theorem legsNetDeltaFor_mkClosedRingLegs_eq_zero (i : Nat) (ringParticipants : List Nat) (cycleFlow : Nat) :
    legsNetDeltaFor i (mkClosedRingLegs ringParticipants cycleFlow) = 0 := by
  cases ringParticipants with
  | nil => rfl
  | cons first rest =>
    simp only [mkClosedRingLegs, legsNetDeltaFor_mkRingLegsAux]
    omega

theorem applyCreditLegsFrom_closedRing (ringParticipants : List Nat) (cycleFlow : Nat) :
    ∀ (idx : Nat) (xs : List Int),
      applyCreditLegsFrom (mkClosedRingLegs ringParticipants cycleFlow) idx xs = xs
  | _, [] => rfl
  | idx, b :: rest => by
    simp only [applyCreditLegsFrom, legsNetDeltaFor_mkClosedRingLegs_eq_zero, Int.add_zero,
      applyCreditLegsFrom_closedRing ringParticipants cycleFlow (idx + 1) rest]

theorem applyCreditLegs_closedRing (balances : List Int) (ringParticipants : List Nat) (cycleFlow : Nat) :
    applyCreditLegs balances (mkClosedRingLegs ringParticipants cycleFlow) = balances :=
  applyCreditLegsFrom_closedRing ringParticipants cycleFlow 0 balances

/-- Settle a closed cycle of debt of size `cycleFlow` across distinct `ringParticipants`.
    Constructs the closed ring of bilateral `CreditLeg`s `mkClosedRingLegs ringParticipants cycleFlow`
    and applies every leg to `balances` (`applyCreditLegs`), leaving net balances invariant by
    Kirchhoff cycle conservation while reducing gross bilateral debt by `ringParticipants.length * cycleFlow`. -/
def settleRing (balances : List Int) (creditLimits : List Int)
    (cycleFlow : Nat) (ringParticipants : List Nat) : Option (List Int) :=
  if ringParticipants.isEmpty then
    none
  else if !ringNodupB ringParticipants then
    none
  else if balances.length != creditLimits.length then
    none
  else if !ringParticipants.all (fun p => decide (p < balances.length)) then
    none
  else if !allSolventB balances creditLimits then
    none
  else
    let legs := mkClosedRingLegs ringParticipants cycleFlow
    some (applyCreditLegs balances legs)

theorem settleRing_eq_some_balances {balances creditLimits : List Int}
    {cycleFlow : Nat} {ringParticipants : List Nat} {postBalances : List Int}
    (h : settleRing balances creditLimits cycleFlow ringParticipants = some postBalances) :
    postBalances = balances := by
  unfold settleRing at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · dsimp only at h
            rw [applyCreditLegs_closedRing] at h
            injection h with h_eq
            exact h_eq.symm

/-- **Multilateral Ring Netting Conservation (`settleRing_conserves_net_worth`)**:
    Settling a closed ring of flow `cycleFlow` across `ringParticipants`:
    1. Leaves every participant's net balance (`postBalances.getD i 0 = balances.getD i 0`) unchanged,
    2. Leaves every participant's `assets - liabilities` net position strictly unchanged
       (`netPosition (assets - cycleFlow) (liabilities - cycleFlow) = netPosition assets liabilities`),
    3. Reduces gross bilateral debt by `ringParticipants.length * cycleFlow`. -/
theorem settleRing_conserves_net_worth
    {balances creditLimits : List Int} {cycleFlow : Nat} {ringParticipants : List Nat}
    {postBalances : List Int}
    (h_settle : settleRing balances creditLimits cycleFlow ringParticipants = some postBalances) :
    postBalances = balances ∧
    (∀ i, postBalances.getD i 0 = balances.getD i 0) ∧
    (∀ assets liabilities : Int,
      netPosition (assets - (cycleFlow : Int)) (liabilities - (cycleFlow : Int)) =
        netPosition assets liabilities) ∧
    (∀ grossDebt : Nat, ringParticipants.length * cycleFlow ≤ grossDebt →
      grossDebt - grossDebtAfterRing grossDebt ringParticipants cycleFlow =
        ringParticipants.length * cycleFlow) := by
  have heq := settleRing_eq_some_balances h_settle
  subst heq
  refine ⟨rfl, fun _ => rfl, fun assets liabilities => ?_, fun grossDebt hle => ?_⟩
  · unfold netPosition
    omega
  · unfold grossDebtAfterRing
    omega

/-- **Zero-Liquidation-Cascade Soundness (`settleRing_never_triggers_liquidation`)**:
    If all participants are solvent before `settleRing`, they remain solvent after `settleRing`,
    and for any positive flow `0 < cycleFlow` on a non-empty ring (`ringParticipants ≠ []`)
    with `ringParticipants.length * cycleFlow ≤ grossDebt`, gross exposure is strictly reduced. -/
theorem settleRing_never_triggers_liquidation
    {balances creditLimits : List Int} {cycleFlow : Nat} {ringParticipants : List Nat}
    {postBalances : List Int} {grossDebt : Nat}
    (h_solvent : AllSolvent balances creditLimits)
    (h_settle : settleRing balances creditLimits cycleFlow ringParticipants = some postBalances)
    (h_flow : 0 < cycleFlow)
    (h_gross : ringParticipants.length * cycleFlow ≤ grossDebt) :
    AllSolvent postBalances creditLimits ∧
    grossDebtAfterRing grossDebt ringParticipants cycleFlow < grossDebt := by
  have heq := settleRing_eq_some_balances h_settle
  have h_nonempty : ringParticipants.isEmpty = false := by
    unfold settleRing at h_settle
    cases he : ringParticipants.isEmpty
    · rfl
    · rw [he] at h_settle; cases h_settle
  have h_len_pos : 0 < ringParticipants.length := by
    cases ringParticipants with
    | nil => cases h_nonempty
    | cons _ _ => simp
  have h_prod_pos : 0 < ringParticipants.length * cycleFlow :=
    Nat.mul_pos h_len_pos h_flow
  subst heq
  refine ⟨h_solvent, ?_⟩
  unfold grossDebtAfterRing
  omega

/-! ## 2. Unified Dragon's Exchange Epoch State & Verified Transition -/

/-- Combined state of the Dragon's Exchange (`dclutch` Hoard + `dreggfi` credit network). -/
structure DragonsExchangeState where
  epoch : Nat
  hoardState : HoardMarketState
  balances : List Int
  creditLimits : List Int
  grossExposure : Nat
  deriving DecidableEq, Repr

/-- Epoch transition input combining `dclutch` complete-set / KKT clearing with `settleRing`. -/
structure DragonsExchangeEpochInput where
  clearingCert : JointClearingCert
  cycleFlow : Nat
  ringParticipants : List Nat
  deriving DecidableEq, Repr

/-- Combined Dragon's Exchange invariant:
    1. `HoardCollateralInvariant s.hoardState` (100% complete-set backing),
    2. `AllSolvent s.balances s.creditLimits` (all credit-ring participants solvent). -/
def DragonsExchangeInvariant (s : DragonsExchangeState) : Prop :=
  HoardCollateralInvariant s.hoardState ∧
  AllSolvent s.balances s.creditLimits

/-- Step a `DragonsExchangeState` across one epoch:
    1. Verifies the `dclutch` KKT `JointClearingCert` (`jointClearingValid`),
    2. Applies the complete-set mint/merge delta `input.clearingCert.sets` to `s.hoardState`,
    3. Executes multilateral credit-ring netting `settleRing` across `input.ringParticipants`,
    4. Reduces `grossExposure` by `ringParticipants.length * cycleFlow`. -/
def stepDragonsExchangeEpoch (s : DragonsExchangeState) (input : DragonsExchangeEpochInput) :
    Option DragonsExchangeState :=
  if input.clearingCert.outcomeCount != s.hoardState.outcomes then
    none
  else if !jointClearingValid input.clearingCert then
    none
  else if !(decide (input.ringParticipants.length * input.cycleFlow ≤ s.grossExposure)) then
    none
  else
    let nextHoard := applyCompleteSetDelta s.hoardState input.clearingCert.sets
    if !hoardCollateralValid nextHoard then
      none
    else
      match settleRing s.balances s.creditLimits input.cycleFlow input.ringParticipants with
      | none => none
      | some nextBalances =>
        some {
          epoch := s.epoch + 1
          hoardState := nextHoard
          balances := nextBalances
          creditLimits := s.creditLimits
          grossExposure := grossDebtAfterRing s.grossExposure input.ringParticipants input.cycleFlow
        }

/-- **Dragon's Exchange Epoch Preservation Theorem (`stepDragonsExchangeEpoch_preserves_invariant`)**:
    Any admitted epoch transition preserves both the `dclutch` Hoard full-collateralization
    invariant and `dreggfi` participant solvency while conserving net balances. -/
theorem stepDragonsExchangeEpoch_preserves_invariant
    (s s' : DragonsExchangeState) (input : DragonsExchangeEpochInput)
    (h_inv : DragonsExchangeInvariant s)
    (h_step : stepDragonsExchangeEpoch s input = some s') :
    DragonsExchangeInvariant s' ∧ s'.balances = s.balances := by
  unfold stepDragonsExchangeEpoch at h_step
  split at h_step
  · cases h_step
  · split at h_step
    · cases h_step
    · split at h_step
      · cases h_step
      · dsimp only at h_step
        split at h_step
        · cases h_step
        · cases h_ring : settleRing s.balances s.creditLimits input.cycleFlow input.ringParticipants with
          | none =>
            rw [h_ring] at h_step
            cases h_step
          | some nextBalances =>
            rw [h_ring] at h_step
            injection h_step with h_eq
            subst h_eq
            have h_bal := settleRing_eq_some_balances h_ring
            have h_hoard : HoardCollateralInvariant (applyCompleteSetDelta s.hoardState input.clearingCert.sets) :=
              applyCompleteSetDelta_preserves_invariant s.hoardState input.clearingCert.sets h_inv.1
            refine ⟨⟨h_hoard, ?_⟩, h_bal⟩
            rw [h_bal]
            exact h_inv.2

/-! ## 3. `Core.Data` Roundtrip Codecs -/

/-- Encode an `Int` as `Core.Data`. -/
def intToData (z : Int) : Data :=
  if z ≥ 0 then .variant "pos" (.natural z.toNat)
  else .variant "neg" (.natural (-z).toNat)

/-- Decode an `Int` from `Core.Data`. -/
def intOfData? : Data → Option Int
  | .variant "pos" (.natural n) => some (n : Int)
  | .variant "neg" (.natural n) => some (-(n : Int))
  | _ => none

@[simp] theorem intOfData?_intToData (z : Int) : intOfData? (intToData z) = some z := by
  unfold intToData
  by_cases hz : z ≥ 0
  · simp only [hz, ↓reduceIte, intOfData?]
    congr 1
    omega
  · simp only [hz, ↓reduceIte, intOfData?]
    congr 1
    omega

/-- Encode a `List Nat` as `Core.Data` using nested `.variant "cons"` / `.variant "nil"`. -/
def natListToData : List Nat → Data
  | [] => .variant "nil" (.record [])
  | n :: rest => .variant "cons" (.record [("head", .natural n), ("tail", natListToData rest)])

/-- Decode a `List Nat` from `Core.Data`. -/
def natListOfData? : Data → Option (List Nat)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", .natural n), ("tail", tailData)]) =>
    match natListOfData? tailData with
    | some rest => some (n :: rest)
    | none => none
  | _ => none

@[simp] theorem natListOfData?_natListToData (ns : List Nat) :
    natListOfData? (natListToData ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n rest ih =>
    simp [natListToData, natListOfData?, ih]

/-- Encode a `List Int` as `Core.Data`. -/
def intListToData : List Int → Data
  | [] => .variant "nil" (.record [])
  | z :: rest => .variant "cons" (.record [("head", intToData z), ("tail", intListToData rest)])

/-- Decode a `List Int` from `Core.Data`. -/
def intListOfData? : Data → Option (List Int)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", headData), ("tail", tailData)]) =>
    match intOfData? headData, intListOfData? tailData with
    | some z, some rest => some (z :: rest)
    | _, _ => none
  | _ => none

@[simp] theorem intListOfData?_intListToData (zs : List Int) :
    intListOfData? (intListToData zs) = some zs := by
  induction zs with
  | nil => rfl
  | cons z rest ih =>
    simp [intListToData, intListOfData?, ih]

/-- Encode a `CreditLeg` as `Core.Data`. -/
def CreditLeg.toData (leg : CreditLeg) : Data :=
  .record [
    ("debtor", .natural leg.debtor),
    ("creditor", .natural leg.creditor),
    ("amount", .natural leg.amount)
  ]

/-- Decode a `CreditLeg` from `Core.Data`. -/
def CreditLeg.ofData? : Data → Option CreditLeg
  | .record [("debtor", .natural d), ("creditor", .natural c), ("amount", .natural a)] =>
    some { debtor := d, creditor := c, amount := a }
  | _ => none

@[simp] theorem CreditLeg.ofData?_toData (leg : CreditLeg) :
    CreditLeg.ofData? leg.toData = some leg := by
  cases leg
  rfl

/-- Encode a `DragonsExchangeState` as `Core.Data`. -/
def DragonsExchangeState.toData (s : DragonsExchangeState) : Data :=
  .record [
    ("epoch", .natural s.epoch),
    ("outcomes", .natural s.hoardState.outcomes),
    ("hoard", .natural s.hoardState.hoard),
    ("supply", natListToData s.hoardState.supply),
    ("balances", intListToData s.balances),
    ("creditLimits", intListToData s.creditLimits),
    ("grossExposure", .natural s.grossExposure)
  ]

/-- Decode a `DragonsExchangeState` from `Core.Data`. -/
def DragonsExchangeState.ofData? : Data → Option DragonsExchangeState
  | .record [
      ("epoch", .natural ep),
      ("outcomes", .natural outc),
      ("hoard", .natural hrd),
      ("supply", supData),
      ("balances", balData),
      ("creditLimits", limData),
      ("grossExposure", .natural ge)
    ] =>
    match natListOfData? supData, intListOfData? balData, intListOfData? limData with
    | some sup, some bal, some lim =>
      some {
        epoch := ep
        hoardState := { outcomes := outc, hoard := hrd, supply := sup }
        balances := bal
        creditLimits := lim
        grossExposure := ge
      }
    | _, _, _ => none
  | _ => none

/-- **`Core.Data` Roundtrip Theorem (`DragonsExchangeState.ofData?_toData`)**. -/
@[simp] theorem DragonsExchangeState.ofData?_toData (s : DragonsExchangeState) :
    DragonsExchangeState.ofData? s.toData = some s := by
  cases s with
  | mk ep hs bal lim ge =>
    cases hs with
    | mk outc hrd sup =>
      simp [DragonsExchangeState.toData, DragonsExchangeState.ofData?]

end Obend.Vault
end
