module
/-
# Obend.Vault.Escrow — House Capacities as C4 Kinds: SealedEscrow and PrepaidLease

Absorbs `breadstuffs/Dregg2/Deos/SealedEscrow.lean` and `breadstuffs/Dregg2/Deos/PrepaidLease.lean`
into Obend's C4 Kind system, conserved resource Book (`Obend.Ledger.Book`), and multi-cell turns (`Obend.Vault.Hyperedge`).
-/
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Kind
public import Obend.Ledger.Book
public import Obend.Vault.Hyperedge
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
public import Obend.Spec.Law
public import Obend.Spec.LawCompile

@[expose] public section

namespace Obend.Vault.Escrow

open Obend.Core.Data
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Kind
open Obend.Ledger
open Obend.Vault
open Obend.Law
open Obend.Spec.Law
open Obend.Spec.LawCompile (compile reqOf Fits)

set_option autoImplicit false

/-! ## 1. Coordinates and Common Types -/

inductive Side where
  | A
  | B
deriving DecidableEq, Repr

def Side.other : Side → Side
  | .A => .B
  | .B => .A

inductive LegStatus where
  | empty
  | deposited
  | consumed
deriving DecidableEq, Repr

def upd {α : Type} (f : Side → α) (s : Side) (v : α) : Side → α :=
  fun t => if t == s then v else f t

@[simp] theorem upd_same {α : Type} (f : Side → α) (s : Side) (v : α) :
    upd f s v s = v := by
  cases s <;> rfl

@[simp] theorem upd_ne {α : Type} (f : Side → α) (s : Side) (v : α) {t : Side} (h : t ≠ s) :
    upd f s v t = f t := by
  cases s <;> cases t <;> first | exact absurd rfl h | rfl

theorem upd_pair_sum (f : Side → Nat) (s : Side) (v : Nat) :
    upd f s v Side.A + upd f s v Side.B = (f Side.A + f Side.B) - f s + v := by
  cases s <;> dsimp [upd] <;> omega

/-! ## 2. SealedEscrow Value Ledger & State Machine -/

structure EscrowTerms where
  sideA_account : AccountId
  sideA_asset   : AssetId
  sideA_amount  : Nat
  sideB_account : AccountId
  sideB_asset   : AssetId
  sideB_amount  : Nat
  timeout       : Epoch
deriving DecidableEq, Repr

structure EscrowState where
  status : Side → LegStatus
  amount : Side → Nat
  recv   : Side → Nat
  paid   : Side → Nat

def openedEscrow : EscrowState where
  status := fun _ => .empty
  amount := fun _ => 0
  recv   := fun _ => 0
  paid   := fun _ => 0

def entered (st : EscrowState) (s : Side) : Nat :=
  match st.status s with
  | .empty => 0
  | _ => st.amount s

def locked (st : EscrowState) (s : Side) : Nat :=
  match st.status s with
  | .deposited => st.amount s
  | _ => 0

def enteredTotal (st : EscrowState) : Nat := entered st Side.A + entered st Side.B
def lockedTotal (st : EscrowState) : Nat := locked st Side.A + locked st Side.B
def paidTotal (st : EscrowState) : Nat := st.paid Side.A + st.paid Side.B
def recvTotal (st : EscrowState) : Nat := st.recv Side.A + st.recv Side.B

def Ready (st : EscrowState) : Prop :=
  st.status Side.A = .deposited ∧ st.status Side.B = .deposited

def ClaimOk (st : EscrowState) (own take : Side) (ownAmt claimedValue lockedAmt : Nat) : Prop :=
  st.status own = .deposited ∧
  st.amount own = ownAmt ∧
  st.status take = .deposited ∧
  st.amount take = lockedAmt ∧
  claimedValue ≤ lockedAmt

inductive EscrowOp : EscrowState → EscrowState → Prop where
  | deposit (st : EscrowState) (s : Side) (amt : Nat) (hempty : st.status s = .empty) :
      EscrowOp st { status := upd st.status s .deposited,
                    amount := upd st.amount s amt,
                    recv   := st.recv,
                    paid   := st.paid }
  | settle (st : EscrowState) (hA : st.status Side.A = .deposited) (hB : st.status Side.B = .deposited) :
      EscrowOp st { status := fun _ => .consumed,
                    amount := st.amount,
                    recv   := fun p => st.recv p + st.amount p.other,
                    paid   := fun s => st.paid s + st.amount s }
  | reclaim (st : EscrowState) (s : Side) (hdep : st.status s = .deposited) :
      EscrowOp st { status := upd st.status s .consumed,
                    amount := st.amount,
                    recv   := upd st.recv s (st.recv s + st.amount s),
                    paid   := upd st.paid s (st.paid s + st.amount s) }

inductive EscrowReachable : EscrowState → Prop where
  | genesis : EscrowReachable openedEscrow
  | step (st st' : EscrowState) (hr : EscrowReachable st) (hop : EscrowOp st st') : EscrowReachable st'

structure EscrowInv (st : EscrowState) : Prop where
  cons : ∀ s, st.paid s + locked st s = entered st s
  balance : recvTotal st = paidTotal st
  participate : ∀ s, st.status s = .empty → st.recv s = 0

theorem opened_inv : EscrowInv openedEscrow := by
  refine ⟨?_, ?_, ?_⟩
  · intro s; cases s <;> rfl
  · rfl
  · intro s _; rfl

theorem Op_preserves {st st' : EscrowState} (hop : EscrowOp st st') (ih : EscrowInv st) : EscrowInv st' := by
  cases hop with
  | deposit s amt hempty =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases s <;> cases t
        · have hpre := ih.cons .A
          unfold locked entered at hpre ⊢
          rw [hempty] at hpre
          dsimp [upd] at hpre ⊢
          omega
        · exact ih.cons .B
        · exact ih.cons .A
        · have hpre := ih.cons .B
          unfold locked entered at hpre ⊢
          rw [hempty] at hpre
          dsimp [upd] at hpre ⊢
          omega
      · exact ih.balance
      · intro t ht
        cases s <;> cases t
        · dsimp [upd] at ht; cases ht
        · exact ih.participate .B ht
        · exact ih.participate .A ht
        · dsimp [upd] at ht; cases ht
  | settle hA hB =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases t
        · have hc := ih.cons .A
          unfold locked entered at hc ⊢
          rw [hA] at hc
          dsimp at hc ⊢
          omega
        · have hc := ih.cons .B
          unfold locked entered at hc ⊢
          rw [hB] at hc
          dsimp at hc ⊢
          omega
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        dsimp [Side.other]
        omega
      · intro t ht; cases t <;> cases ht
  | reclaim s hdep =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        cases s <;> cases t
        · have hc := ih.cons .A
          unfold locked entered at hc ⊢
          rw [hdep] at hc
          dsimp [upd] at hc ⊢
          omega
        · exact ih.cons .B
        · exact ih.cons .A
        · have hc := ih.cons .B
          unfold locked entered at hc ⊢
          rw [hdep] at hc
          dsimp [upd] at hc ⊢
          omega
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        cases s <;> dsimp [upd] <;> omega
      · intro t ht
        cases s <;> cases t
        · dsimp [upd] at ht; cases ht
        · exact ih.participate .B ht
        · exact ih.participate .A ht
        · dsimp [upd] at ht; cases ht

theorem reachable_inv (st : EscrowState) (h : EscrowReachable st) : EscrowInv st := by
  induction h with
  | genesis => exact opened_inv
  | step s s' _ hop ih => exact Op_preserves hop ih

/-- **THE ECONOMIC NO-THEFT WORLD PROPERTY**:
    Per-leg conservation holds, and uncommitted parties receive nothing. -/
theorem sealedescrow_no_theft (st : EscrowState) (h : EscrowReachable st) :
    (∀ s, st.paid s + locked st s = entered st s) ∧
    (∀ s, st.status s = .empty → st.recv s = 0) :=
  ⟨(reachable_inv st h).cons, (reachable_inv st h).participate⟩

theorem no_phantom_extraction (st : EscrowState) (h : EscrowReachable st) (s : Side)
    (hempty : st.status s = .empty) : st.paid s = 0 := by
  have hc := (reachable_inv st h).cons s
  unfold locked entered at hc
  rw [hempty] at hc
  exact hc

theorem escrow_solvent (st : EscrowState) (h : EscrowReachable st) :
    recvTotal st ≤ enteredTotal st := by
  have inv := reachable_inv st h
  have hbal := inv.balance
  have hcA := inv.cons Side.A
  have hcB := inv.cons Side.B
  unfold recvTotal paidTotal enteredTotal at *
  omega

theorem halfopen_theft_unreachable (st : EscrowState) (h : EscrowReachable st)
    (hempty : st.status Side.A = .empty) (hclaim : 0 < st.recv Side.A) : False := by
  have hp := (reachable_inv st h).participate Side.A hempty
  omega

theorem phantom_extraction_unreachable (st : EscrowState) (h : EscrowReachable st)
    (hempty : st.status Side.A = .empty) (hextract : 0 < st.paid Side.A) : False := by
  have hz := no_phantom_extraction st h Side.A hempty
  omega

/-! ## 3. PrepaidLease Fused Meter-Draw Engine -/

structure LeaseTerms where
  rent    : Nat
  period  : Nat
  start   : Nat
  count   : Nat
  budget  : Nat
  lessor  : AccountId
  lessee  : AccountId
  asset   : AssetId
deriving DecidableEq, Repr

structure LeaseState where
  nextDue         : Nat
  dischargedCount : Nat
  remaining       : Nat
  drawn           : Nat
deriving DecidableEq, Repr

def LeaseTerms.wf (t : LeaseTerms) : Prop := 0 < t.rent ∧ 0 < t.period

def cursorAt (t : LeaseTerms) (k : Nat) : Nat := t.start + k * t.period
def dueBlock (t : LeaseTerms) (k : Nat) : Nat := t.start + k * t.period
def expectedPeriod (t : LeaseTerms) (nextDue : Nat) : Nat := (nextDue - t.start) / t.period

def periodsDueBy (t : LeaseTerms) (clock : Nat) : Nat :=
  if clock < t.start then 0
  else
    let due := (clock - t.start) / t.period + 1
    if 0 < t.count ∧ t.count < due then t.count else due

def openLease (t : LeaseTerms) : LeaseState where
  nextDue         := t.start
  dischargedCount := 0
  remaining       := t.budget
  drawn           := 0

/-- **THE FUSED DISCHARGE OPERATION**:
    Atomically advances the meter, bumps count, draws rent, and records drawn total. -/
def advance (t : LeaseTerms) (st : LeaseState) : LeaseState where
  nextDue         := st.nextDue + t.period
  dischargedCount := st.dischargedCount + 1
  remaining       := st.remaining - t.rent
  drawn           := st.drawn + t.rent

def DischargeOk (t : LeaseTerms) (st : LeaseState) (clock : Nat) (amount : Nat) (periodIdx : Nat) : Prop :=
  (t.count = 0 ∨ expectedPeriod t st.nextDue < t.count) ∧
  periodIdx = expectedPeriod t st.nextDue ∧
  dueBlock t (expectedPeriod t st.nextDue) ≤ clock ∧
  amount = t.rent ∧
  t.rent ≤ st.remaining

def remainingAfter (budget rent : Nat) : Nat → Nat
  | 0 => budget
  | n + 1 => remainingAfter budget rent n - rent

def drawnAfter (rent : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => drawnAfter rent n + rent

theorem budget_never_overdrawn (budget rent n : Nat) (h : n * rent ≤ budget) :
    remainingAfter budget rent n = budget - n * rent := by
  induction n with
  | zero => simp [remainingAfter]
  | succ k ih =>
      simp only [remainingAfter]
      rw [Nat.succ_mul] at h ⊢
      have hk : k * rent ≤ budget := by omega
      rw [ih hk]
      omega

theorem drawn_eq_count_rent (rent n : Nat) :
    drawnAfter rent n = n * rent := by
  induction n with
  | zero => simp [drawnAfter]
  | succ k ih =>
      simp only [drawnAfter, ih]
      rw [Nat.succ_mul]

theorem remaining_plus_drawn_conserved (budget rent n : Nat) (h : n * rent ≤ budget) :
    remainingAfter budget rent n + drawnAfter rent n = budget := by
  rw [budget_never_overdrawn budget rent n h, drawn_eq_count_rent]
  omega

theorem cursor_strict_mono (t : LeaseTerms) (hwf : t.wf) {j k : Nat} (hjk : j < k) :
    cursorAt t j < cursorAt t k := by
  unfold cursorAt
  have hp : 0 < t.period := hwf.2
  have : j * t.period < k * t.period := Nat.mul_lt_mul_of_pos_right hjk hp
  omega

theorem advance_strictly_increases (t : LeaseTerms) (hwf : t.wf) (st : LeaseState) :
    st.nextDue < (advance t st).nextDue := by
  dsimp [advance]
  have hp := hwf.2
  omega

theorem advance_draws_exactly_rent (t : LeaseTerms) (st : LeaseState) :
    (advance t st).remaining = st.remaining - t.rent := rfl

theorem advance_meters_period (t : LeaseTerms) (st : LeaseState) :
    (advance t st).nextDue = st.nextDue + t.period := rfl

theorem expectedPeriod_open (t : LeaseTerms) : expectedPeriod t t.start = 0 := by
  unfold expectedPeriod
  simp

theorem expectedPeriod_advance (t : LeaseTerms) (hwf : t.wf) (k : Nat) :
    expectedPeriod t (t.start + (k + 1) * t.period) = expectedPeriod t (t.start + k * t.period) + 1 := by
  unfold expectedPeriod
  have hp : 0 < t.period := hwf.2
  have h1 : t.start + (k + 1) * t.period - t.start = (k + 1) * t.period := by omega
  have h0 : t.start + k * t.period - t.start = k * t.period := by omega
  rw [h1, h0]
  rw [Nat.mul_comm (k + 1) t.period, Nat.mul_div_right (k + 1) hp]
  rw [Nat.mul_comm k t.period, Nat.mul_div_right k hp]

theorem replay_rejected (t : LeaseTerms) (hwf : t.wf) (st : LeaseState) (clock : Nat)
    (k : Nat) (hcur : st.nextDue = cursorAt t k) :
    ¬ DischargeOk t (advance t st) clock t.rent (expectedPeriod t st.nextDue) := by
  intro hok
  have hexp := hok.2.1
  dsimp [advance] at hexp
  unfold cursorAt at hcur
  rw [hcur] at hexp
  have hadv : t.start + k * t.period + t.period = t.start + (k + 1) * t.period := by
    rw [Nat.succ_mul]
    omega
  rw [hadv] at hexp
  rw [expectedPeriod_advance t hwf k] at hexp
  omega

theorem insufficient_budget_rejected (t : LeaseTerms) (st : LeaseState) (clock amt pidx : Nat)
    (hshort : st.remaining < t.rent) :
    ¬ DischargeOk t st clock amt pidx := by
  intro hok
  have hcov := hok.2.2.2.2
  omega

/-! ## 4. C4 Nominal Kind Registration, Non-Trivial Laws & Verified CellContracts -/

/-- Legacy alias retained only for backward compatibility; `escrowKindCell` and
    `prepaidLeaseKindCell` now enforce `escrowLaw` and `prepaidLeaseLaw`. -/
def trivialLaw : LawExpr := .eqR .turn .turn

/-- Enforced law combinators for C4 Vault Kinds. -/
def monotone (field : String) : LawExpr := .monotone field
def writeOnce (field : String) : LawExpr := .writeOnce field
def inRange (field : String) (values : List Int) : LawExpr := .inC (.field field) values
def leField (left right : String) (offset : Int := 0) : LawExpr := .leROff (.field left) (.field right) offset

/-- Non-trivial enforced `LawExpr` for `escrowKindCell`:
    `monotone "settled" && inRange "statusA" [0, 1, 2] && inRange "statusB" [0, 1, 2]`. -/
def escrowLaw : LawExpr :=
  .and (monotone "settled")
    (.and (inRange "statusA" [0, 1, 2]) (inRange "statusB" [0, 1, 2]))

/-- Non-trivial enforced `LawExpr` for `prepaidLeaseKindCell`:
    `monotone "dischargedCount" && monotone "drawn" && leField "drawn" "budget" 0 && writeOnce "budget" && writeOnce "rent"`. -/
def prepaidLeaseLaw : LawExpr :=
  .and (monotone "dischargedCount")
    (.and (monotone "drawn")
      (.and (leField "drawn" "budget" 0)
        (.and (writeOnce "budget") (writeOnce "rent"))))

def escrowKindCell : KindCell LawExpr where
  name := "escrow"
  version := 1
  layout := ["termsDigest", "sideA_account", "sideA_asset", "sideA_amount", "sideA_status",
             "sideB_account", "sideB_asset", "sideB_amount", "sideB_status", "timeout",
             "settled", "statusA", "statusB"]
  init := .record [
    ("termsDigest", .natural 0),
    ("sideA_amount", .natural 0),
    ("sideB_amount", .natural 0),
    ("timeout", .natural 0),
    ("settled", .natural 0),
    ("statusA", .natural 0),
    ("statusB", .natural 0)
  ]
  law := escrowLaw
  parents := []

def prepaidLeaseKindCell : KindCell LawExpr where
  name := "prepaidLease"
  version := 1
  layout := ["termsDigest", "rent", "period", "start", "count", "budget",
             "nextDue", "dischargedCount", "remaining", "drawn", "lessor", "lessee", "asset"]
  init := .record [
    ("termsDigest", .natural 0),
    ("rent", .natural 0),
    ("period", .natural 0),
    ("start", .natural 0),
    ("count", .natural 0),
    ("budget", .natural 0),
    ("nextDue", .natural 0),
    ("dischargedCount", .natural 0),
    ("remaining", .natural 0),
    ("drawn", .natural 0)
  ]
  law := prepaidLeaseLaw
  parents := ["escrow"]

/-! ### 4.1 Data Encodings & State Types for Escrow and PrepaidLease -/

def LegStatus.toNat : LegStatus → Nat
  | .empty => 0
  | .deposited => 1
  | .consumed => 2

def escrowSettledTag (st : EscrowState) : Nat :=
  if st.status .A == .consumed && st.status .B == .consumed then 1 else 0

def escrowStateToData (st : EscrowState) : Data :=
  .record [
    ("settled", .natural (escrowSettledTag st)),
    ("statusA", .natural (st.status .A).toNat),
    ("statusB", .natural (st.status .B).toNat),
    ("sideA_amount", .natural (st.amount .A)),
    ("sideB_amount", .natural (st.amount .B)),
    ("paidA", .natural (st.paid .A)),
    ("paidB", .natural (st.paid .B)),
    ("recvA", .natural (st.recv .A)),
    ("recvB", .natural (st.recv .B))
  ]

def escrowStateTy : Ty :=
  .field "settled" .natural
    (.field "statusA" .natural
      (.field "statusB" .natural
        (.field "sideA_amount" .natural
          (.field "sideB_amount" .natural
            (.field "paidA" .natural
              (.field "paidB" .natural
                (.field "recvA" .natural
                  (.field "recvB" .natural .emptyRow))))))))

def leaseStateToData (t : LeaseTerms) (st : LeaseState) : Data :=
  .record [
    ("rent", .natural t.rent),
    ("period", .natural t.period),
    ("start", .natural t.start),
    ("count", .natural t.count),
    ("budget", .natural t.budget),
    ("nextDue", .natural st.nextDue),
    ("dischargedCount", .natural st.dischargedCount),
    ("remaining", .natural st.remaining),
    ("drawn", .natural st.drawn)
  ]

def leaseStateTy : Ty :=
  .field "rent" .natural
    (.field "period" .natural
      (.field "start" .natural
        (.field "count" .natural
          (.field "budget" .natural
            (.field "nextDue" .natural
              (.field "dischargedCount" .natural
                (.field "remaining" .natural
                  (.field "drawn" .natural .emptyRow))))))))

@[simp] theorem escrowStateToData_fits (st : EscrowState) :
    Fits escrowStateTy escrowLaw (escrowStateToData st) = true := rfl

@[simp] theorem leaseStateToData_fits (t : LeaseTerms) (st : LeaseState) :
    Fits leaseStateTy prepaidLeaseLaw (leaseStateToData t st) = true := rfl

@[simp] theorem escrowStateToData_field_settled (st : EscrowState) :
    fieldOf "settled" (escrowStateToData st) = some (Int.ofNat (escrowSettledTag st)) := rfl

@[simp] theorem escrowStateToData_field_statusA (st : EscrowState) :
    fieldOf "statusA" (escrowStateToData st) = some (Int.ofNat (st.status .A).toNat) := rfl

@[simp] theorem escrowStateToData_field_statusB (st : EscrowState) :
    fieldOf "statusB" (escrowStateToData st) = some (Int.ofNat (st.status .B).toNat) := rfl

@[simp] theorem leaseStateToData_field_rent (t : LeaseTerms) (st : LeaseState) :
    fieldOf "rent" (leaseStateToData t st) = some (Int.ofNat t.rent) := rfl

@[simp] theorem leaseStateToData_field_budget (t : LeaseTerms) (st : LeaseState) :
    fieldOf "budget" (leaseStateToData t st) = some (Int.ofNat t.budget) := rfl

@[simp] theorem leaseStateToData_field_dischargedCount (t : LeaseTerms) (st : LeaseState) :
    fieldOf "dischargedCount" (leaseStateToData t st) = some (Int.ofNat st.dischargedCount) := rfl

@[simp] theorem leaseStateToData_field_drawn (t : LeaseTerms) (st : LeaseState) :
    fieldOf "drawn" (leaseStateToData t st) = some (Int.ofNat st.drawn) := rfl

/-! ### 4.2 Inductive CellContract Construction (`escrowCellContract` & `prepaidLeaseCellContract`) -/

def cellTopInv : Term := .lam trueT

example : closedB cellTopInv = true := by decide +kernel

theorem holds_cellTopInv (d : Data) : Holds cellTopInv d := by
  unfold Holds cellTopInv
  refine evaluates_step (.beta trueT d.term) ?_
  have hinst : instantiate trueT d.term = .boolean true := by
    unfold instantiate
    exact subst_trueT _
  rw [hinst]
  exact evaluates_self (.boolean true)

def inRange012T (x : Term) : Term :=
  .ifBool (eqNat x (natT 0)) trueT
    (.ifBool (eqNat x (natT 1)) trueT
      (.ifBool (eqNat x (natT 2)) trueT falseT))

/-- Non-trivial single-state invariant for `SealedEscrow` enforcing valid leg status tags in `{0, 1, 2}`. -/
def escrowInvariant : Term :=
  .lam (andT (inRange012T (.get (.bound 0) "statusA"))
             (inRange012T (.get (.bound 0) "statusB")))

theorem escrowInvariant_closed : closedB escrowInvariant = true := by decide +kernel

/-- Non-trivial single-state invariant for `PrepaidLease` enforcing `drawn ≤ budget` and `remaining ≤ budget`. -/
def prepaidLeaseInvariant : Term :=
  .lam (andT (leNat (.get (.bound 0) "drawn") (.get (.bound 0) "budget"))
             (leNat (.get (.bound 0) "remaining") (.get (.bound 0) "budget")))

theorem prepaidLeaseInvariant_closed : closedB prepaidLeaseInvariant = true := by decide +kernel

/-- Constructive `CellContract` builder backed by a closed `invariant` (`closedB invariant = true`)
    and a Core4 `stepBody` (`0 Classical.choice`).
    The executable `law` guards `stepBody` with `.app invariant (.bound 1)` on the post-state `new`,
    establishing both `inductive_preserves` (`Holds invariant new`) and `step_sound`
    (`Admits (law3 stepBody) old new req`). -/
def mkGuardedStepCellContract (invariant : Term) (hI : closedB invariant = true)
    (why : String) (stepBody : Term) : CellContract where
  law := law3 (guard (.app invariant (.bound 1)) why stepBody)
  invariant := invariant
  stepRel := law3 stepBody
  inductive_preserves := by
    intro old new req _ hadm
    obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
    unfold Obend.Law.guard at hw
    simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
    obtain ⟨bb, hc, hr⟩ := ifBool_inv hw
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
      have hval := evaluates_value (.inject _ _) hr
      injection hval with htag _
      exact absurd htag (by decide)
    · exact hc
  step_sound := by
    intro old new req _ hadm
    obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
    unfold Obend.Law.guard at hw
    simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
    obtain ⟨bb, _, hr⟩ := ifBool_inv hw
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
      have hval := evaluates_value (.inject _ _) hr
      injection hval with htag _
      exact absurd htag (by decide)
    · simp only [↓reduceIte] at hr
      exact (admits_iff stepBody old new req).2 ⟨w, hr⟩

/-- Constructive `CellContract` builder backed by a Core4 `stepBody` and `cellTopInv` (`0 Classical.choice`). -/
def mkDirectStepCellContract (stepBody : Term) : CellContract where
  law := law3 stepBody
  invariant := cellTopInv
  stepRel := law3 stepBody
  inductive_preserves := fun _ new _ _ _ => holds_cellTopInv new
  step_sound := fun _ _ _ _ hadm => hadm

def escrowCondT : Term :=
  andT (leNat (.get (.bound 2) "settled") (.get (.bound 1) "settled"))
    (andT (inRange012T (.get (.bound 1) "statusA"))
      (andT (inRange012T (.get (.bound 1) "statusB"))
        (andT (leNat (.get (.bound 2) "paidA") (.get (.bound 1) "paidA"))
              (leNat (.get (.bound 2) "paidB") (.get (.bound 1) "paidB")))))

def escrowStepBody : Term := guard escrowCondT "escrowLaw" okT

def writeOnceNatT (oldV newV : Term) : Term :=
  .ifBool (eqNat oldV (natT 0)) trueT (eqNat newV oldV)

def prepaidLeaseCondT : Term :=
  andT (leNat (.get (.bound 2) "dischargedCount") (.get (.bound 1) "dischargedCount"))
    (andT (leNat (.get (.bound 2) "drawn") (.get (.bound 1) "drawn"))
      (andT (leNat (.get (.bound 1) "drawn") (.get (.bound 1) "budget"))
        (andT (writeOnceNatT (.get (.bound 2) "budget") (.get (.bound 1) "budget"))
          (andT (writeOnceNatT (.get (.bound 2) "rent") (.get (.bound 1) "rent"))
            (andT (leNat (.get (.bound 1) "remaining") (.get (.bound 2) "remaining"))
                  (leNat (.get (.bound 1) "remaining") (.get (.bound 1) "budget")))))))

def prepaidLeaseStepBody : Term := guard prepaidLeaseCondT "prepaidLeaseLaw" okT

/-- Proof-carrying inductive `CellContract` for `SealedEscrow` with non-trivial `escrowInvariant` (`0 Classical.choice`). -/
def escrowCellContract : CellContract :=
  mkGuardedStepCellContract escrowInvariant escrowInvariant_closed "escrowLaw" escrowStepBody

/-- Proof-carrying inductive `CellContract` for `PrepaidLease` with non-trivial `prepaidLeaseInvariant` (`0 Classical.choice`). -/
def prepaidLeaseCellContract : CellContract :=
  mkGuardedStepCellContract prepaidLeaseInvariant prepaidLeaseInvariant_closed "prepaidLeaseLaw" prepaidLeaseStepBody

/-! ### 4.3 Constructive Core4 Evaluation & Machine-Checked Bridge/Refusal Theorems -/

theorem guardedLaw_admits_of_holds_and_step {invariant : Term} (hI : closedB invariant = true)
    {why : String} {stepBody : Term} {old new req : Data}
    (hinv : Holds invariant new)
    (hstep : Admits (law3 stepBody) old new req) :
    Admits (law3 (guard (.app invariant (.bound 1)) why stepBody)) old new req := by
  obtain ⟨w, hw⟩ := (admits_iff stepBody old new req).1 hstep
  refine (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).2 ⟨w, ?_⟩
  unfold Obend.Law.guard
  simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv]
  refine evaluates_ifBool hinv ?_
  exact hw

theorem guardedLaw_admits_imp_stepRel {invariant : Term} (hI : closedB invariant = true)
    {why : String} {stepBody : Term} {old new req : Data}
    (hadm : Admits (law3 (guard (.app invariant (.bound 1)) why stepBody)) old new req) :
    Admits (law3 stepBody) old new req := by
  obtain ⟨w, hw⟩ := (admits_iff (guard (.app invariant (.bound 1)) why stepBody) old new req).1 hadm
  unfold Obend.Law.guard at hw
  simp only [subst_ifBool, subst_app, subst_bound, closedB_subst hI, lawEnv] at hw
  obtain ⟨bb, _, hr⟩ := ifBool_inv hw
  cases bb
  · simp only [Bool.false_eq_true, ↓reduceIte, refusedT, subst_inject, Term.substitute] at hr
    have hval := evaluates_value (.inject _ _) hr
    injection hval with htag _
    exact absurd htag (by decide)
  · simp only [↓reduceIte] at hr
    exact (admits_iff stepBody old new req).2 ⟨w, hr⟩

theorem steps_binaryLeft {p : Primitive} {l l' r : Term} (h : Steps l l') :
    Steps (.binary p l r) (.binary p l' r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft _ _ s) ih

theorem steps_binaryRight {p : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary p l r) (.binary p l r') := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight _ _ hl s) ih

theorem ev_leNat {l r : Term} {a b : Nat} (hl : Evaluates l (.nat a)) (hr : Evaluates r (.nat b)) :
    Evaluates (leNat l r) (.boolean (decide (a ≤ b))) := by
  unfold leNat
  refine evaluates_steps (steps_binaryLeft hl.1) ?_
  refine evaluates_steps (steps_binaryRight (.natural a) hr.1) ?_
  exact evaluates_step (.primitive .lessEqual (.nat a) (.nat b) (.boolean (decide (a ≤ b))) (.natural a) (.natural b) rfl)
    (evaluates_self (.boolean _))

theorem ev_eqNat {l r : Term} {a b : Nat} (hl : Evaluates l (.nat a)) (hr : Evaluates r (.nat b)) :
    Evaluates (eqNat l r) (.boolean (a == b)) := by
  unfold eqNat
  refine evaluates_steps (steps_binaryLeft hl.1) ?_
  refine evaluates_steps (steps_binaryRight (.natural a) hr.1) ?_
  exact evaluates_step (.primitive .equal (.nat a) (.nat b) (.boolean (a == b)) (.natural a) (.natural b) rfl)
    (evaluates_self (.boolean _))

theorem ev_andT {a b : Term} {ba bb : Bool} (ha : Evaluates a (.boolean ba)) (hb : Evaluates b (.boolean bb)) :
    Evaluates (andT a b) (.boolean (ba && bb)) := by
  unfold andT
  refine evaluates_ifBool ha ?_
  cases ba
  · exact evaluates_self (.boolean false)
  · exact hb

theorem ev_orT {a b : Term} {ba bb : Bool} (ha : Evaluates a (.boolean ba)) (hb : Evaluates b (.boolean bb)) :
    Evaluates (.ifBool a trueT b) (.boolean (ba || bb)) := by
  refine evaluates_ifBool ha ?_
  cases ba
  · exact hb
  · exact evaluates_self (.boolean true)

theorem ev_get_nat {fs : List (String × Term)} {f : String} {m : Nat}
    (hf : fs.find? (fun field => field.1 == f) = some (f, .nat m)) :
    Evaluates (.get (.record fs) f) (.nat m) :=
  evaluates_step (.field fs f (.nat m) hf) (evaluates_self (.natural m))

theorem ev_inRange012T {x : Term} {m : Nat} (hx : Evaluates x (.nat m)) :
    Evaluates (inRange012T x) (.boolean ((m == 0) || ((m == 1) || (m == 2)))) := by
  unfold inRange012T
  refine ev_orT (ev_eqNat hx (evaluates_self (.natural 0))) ?_
  refine ev_orT (ev_eqNat hx (evaluates_self (.natural 1))) ?_
  refine evaluates_ifBool (ev_eqNat hx (evaluates_self (.natural 2))) ?_
  cases (m == 2) <;> exact evaluates_self (.boolean _)

theorem ev_writeOnceNatT {oldV newV : Term} {o n : Nat}
    (ho : Evaluates oldV (.nat o)) (hn : Evaluates newV (.nat n)) :
    Evaluates (writeOnceNatT oldV newV) (.boolean ((o == 0) || (n == o))) := by
  unfold writeOnceNatT
  exact ev_orT (ev_eqNat ho (evaluates_self (.natural 0))) (ev_eqNat hn ho)

def verdictOfBool (why : String) (b : Bool) : Term :=
  if b then okT else refusedT why

theorem ev_guard_okT {c : Term} {why : String} {b : Bool} (hc : Evaluates c (.boolean b)) :
    Evaluates (guard c why okT) (verdictOfBool why b) := by
  unfold Obend.Law.guard verdictOfBool
  refine evaluates_ifBool hc ?_
  cases b <;> exact evaluates_self (.inject _ _)

theorem verdictOfBool_iff {B : Term} {o n rq : Data} {why : String} {b : Bool}
    (h : Evaluates (B.substitute (lawEnv o.term n.term rq.term)) (verdictOfBool why b)) :
    (Admits (law3 B) o n rq ↔ b = true) ∧ (Refuses (law3 B) o n rq why ↔ b = false) := by
  cases b
  · refine ⟨⟨fun hadm => ?_, fun h => by cases h⟩,
            ⟨fun _ => rfl, fun _ => (refuses_iff B o n rq why).2 h⟩⟩
    obtain ⟨w, hw⟩ := (admits_iff B o n rq).1 hadm
    have heq := evaluates_unique h hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  · refine ⟨⟨fun _ => rfl, fun _ => (admits_iff B o n rq).2 ⟨_, h⟩⟩,
            ⟨fun href => ?_, fun h => by cases h⟩⟩
    have hw := (refuses_iff B o n rq why).1 href
    have heq := evaluates_unique h hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)

def escrowVerdictBool (st st' : EscrowState) : Bool :=
  decide (escrowSettledTag st ≤ escrowSettledTag st') &&
    (((st'.status .A).toNat == 0 || ((st'.status .A).toNat == 1 || (st'.status .A).toNat == 2)) &&
     (((st'.status .B).toNat == 0 || ((st'.status .B).toNat == 1 || (st'.status .B).toNat == 2)) &&
      (decide (st.paid .A ≤ st'.paid .A) && decide (st.paid .B ≤ st'.paid .B))))

theorem escrowStepBody_eval (st st' : EscrowState) (rq : Data) :
    Evaluates (escrowStepBody.substitute (lawEnv (escrowStateToData st).term (escrowStateToData st').term rq.term))
      (verdictOfBool "escrowLaw" (escrowVerdictBool st st')) := by
  unfold escrowStepBody escrowCondT inRange012T
  simp only [subst_guard, subst_okT, subst_andT, subst_leNat, subst_ifBool, subst_eqNat,
    subst_natT, subst_trueT, subst_falseT, subst_get, subst_bound]
  refine ev_guard_okT ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_inRange012T (ev_get_nat rfl)) ?_
  refine ev_andT (ev_inRange012T (ev_get_nat rfl)) ?_
  exact ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
                (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))

def prepaidLeaseVerdictBool (t : LeaseTerms) (st st' : LeaseState) : Bool :=
  decide (st.dischargedCount ≤ st'.dischargedCount) &&
    (decide (st.drawn ≤ st'.drawn) &&
      (decide (st'.drawn ≤ t.budget) &&
        (((t.budget == 0) || (t.budget == t.budget)) &&
         (((t.rent == 0) || (t.rent == t.rent)) &&
          (decide (st'.remaining ≤ st.remaining) && decide (st'.remaining ≤ t.budget))))))

theorem prepaidLeaseStepBody_eval (t : LeaseTerms) (st st' : LeaseState) (rq : Data) :
    Evaluates (prepaidLeaseStepBody.substitute (lawEnv (leaseStateToData t st).term (leaseStateToData t st').term rq.term))
      (verdictOfBool "prepaidLeaseLaw" (prepaidLeaseVerdictBool t st st')) := by
  unfold prepaidLeaseStepBody prepaidLeaseCondT writeOnceNatT
  simp only [subst_guard, subst_okT, subst_andT, subst_leNat, subst_ifBool, subst_eqNat,
    subst_natT, subst_trueT, subst_get, subst_bound]
  refine ev_guard_okT ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_writeOnceNatT (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  refine ev_andT (ev_writeOnceNatT (ev_get_nat rfl) (ev_get_nat rfl)) ?_
  exact ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
                (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))

theorem legStatus_in_range (s : LegStatus) :
    ([0, 1, 2] : List Int).contains (Int.ofNat s.toNat) = true := by
  cases s <;> decide

theorem legStatus_inRange012 (s : LegStatus) :
    (s.toNat == 0 || (s.toNat == 1 || s.toNat == 2)) = true := by
  cases s <;> decide

theorem holds_escrowInvariant (st : EscrowState) :
    Holds escrowInvariant (escrowStateToData st) := by
  unfold Holds escrowInvariant
  refine evaluates_step (.beta _ (escrowStateToData st).term) ?_
  unfold instantiate
  simp only [subst_andT, subst_ifBool, subst_eqNat, subst_natT, subst_trueT, subst_falseT,
    subst_get, subst_bound, inRange012T]
  have hev : Evaluates
      (andT (inRange012T (.get (escrowStateToData st).term "statusA"))
            (inRange012T (.get (escrowStateToData st).term "statusB")))
      (.boolean (((st.status .A).toNat == 0 || ((st.status .A).toNat == 1 || (st.status .A).toNat == 2)) &&
                 ((st.status .B).toNat == 0 || ((st.status .B).toNat == 1 || (st.status .B).toNat == 2)))) :=
    ev_andT (ev_inRange012T (ev_get_nat rfl)) (ev_inRange012T (ev_get_nat rfl))
  rw [legStatus_inRange012 (st.status .A), legStatus_inRange012 (st.status .B), Bool.and_self] at hev
  exact hev

theorem holds_prepaidLeaseInvariant (t : LeaseTerms) (st : LeaseState)
    (hdrawn : st.drawn ≤ t.budget) (hrem : st.remaining ≤ t.budget) :
    Holds prepaidLeaseInvariant (leaseStateToData t st) := by
  unfold Holds prepaidLeaseInvariant
  refine evaluates_step (.beta _ (leaseStateToData t st).term) ?_
  unfold instantiate
  simp only [subst_andT, subst_leNat, subst_get, subst_bound]
  have h1 : decide (st.drawn ≤ t.budget) = true := decide_eq_true hdrawn
  have h2 : decide (st.remaining ≤ t.budget) = true := decide_eq_true hrem
  have hev : Evaluates
      (andT (leNat (.get (leaseStateToData t st).term "drawn") (.get (leaseStateToData t st).term "budget"))
            (leNat (.get (leaseStateToData t st).term "remaining") (.get (leaseStateToData t st).term "budget")))
      (.boolean (decide (st.drawn ≤ t.budget) && decide (st.remaining ≤ t.budget))) :=
    ev_andT (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl)) (ev_leNat (ev_get_nat rfl) (ev_get_nat rfl))
  rw [h1, h2, Bool.and_self] at hev
  exact hev

theorem escrowSettledTag_eq_zero_of_not_consumed {st : EscrowState} {s : Side}
    (h : st.status s ≠ .consumed) : escrowSettledTag st = 0 := by
  unfold escrowSettledTag
  cases s
  · have hA : (st.status .A == .consumed) = false := beq_false_of_ne h
    simp [hA]
  · have hB : (st.status .B == .consumed) = false := beq_false_of_ne h
    simp [hB]

/-- Every valid `EscrowOp` transition satisfies the non-trivial `escrowLaw`. -/
theorem escrowOp_satisfies_escrowLaw (facts : Facts) {st st' : EscrowState}
    (hop : EscrowOp st st') :
    escrowLaw.denote facts (some (escrowStateToData st)) (escrowStateToData st') = true := by
  have hzero : escrowSettledTag st = 0 := by
    cases hop with
    | deposit s amt hempty =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hempty]; decide)
    | settle hA _ =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hA]; decide)
    | reclaim s hdep =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hdep]; decide)
  have hA := legStatus_in_range (st'.status .A)
  have hB := legStatus_in_range (st'.status .B)
  have hle : decide ((Int.ofNat (escrowSettledTag st) : Int) ≤ Int.ofNat (escrowSettledTag st')) = true :=
    decide_eq_true (by rw [hzero]; simp only [Int.ofNat_eq_natCast]; omega)
  simp only [escrowLaw, monotone, inRange, LawExpr.denote, LawRef.read,
    Option.bind_some, escrowStateToData_field_settled, escrowStateToData_field_statusA,
    escrowStateToData_field_statusB, hle, hA, hB, Bool.and_self]

/-- Every valid `EscrowOp` transition is admitted by `escrowCellContract` (both `law` and `stepRel`)
    and preserves `escrowCellContract.invariant` (`0 Classical.choice`). -/
theorem escrowOp_admitted_by_contract (facts : Facts) {st st' : EscrowState}
    (hop : EscrowOp st st') (ag pr : String) (nb vu : Nat) :
    Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) ∧
    Admits escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) ∧
    Holds escrowCellContract.invariant (escrowStateToData st') := by
  have hzero : escrowSettledTag st = 0 := by
    cases hop with
    | deposit s amt hempty =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hempty]; decide)
    | settle hA _ =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hA]; decide)
    | reclaim s hdep =>
        exact escrowSettledTag_eq_zero_of_not_consumed (by rw [hdep]; decide)
  have hpaidA : decide (st.paid .A ≤ st'.paid .A) = true := by
    cases hop with
    | deposit _ _ _ => exact decide_eq_true (Nat.le_refl _)
    | settle _ _ => exact decide_eq_true (Nat.le_add_right _ _)
    | reclaim s _ =>
      apply decide_eq_true
      cases s <;> dsimp [upd] <;> omega
  have hpaidB : decide (st.paid .B ≤ st'.paid .B) = true := by
    cases hop with
    | deposit _ _ _ => exact decide_eq_true (Nat.le_refl _)
    | settle _ _ => exact decide_eq_true (Nat.le_add_right _ _)
    | reclaim s _ =>
      apply decide_eq_true
      cases s <;> dsimp [upd] <;> omega
  have hle : decide (escrowSettledTag st ≤ escrowSettledTag st') = true :=
    decide_eq_true (by rw [hzero]; omega)
  have hv : escrowVerdictBool st st' = true := by
    simp only [escrowVerdictBool, hle, legStatus_inRange012, hpaidA, hpaidB, Bool.and_self]
  have hstep : Admits escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
    (verdictOfBool_iff (escrowStepBody_eval st st' _)).1.2 hv
  have hinv : Holds escrowCellContract.invariant (escrowStateToData st') :=
    holds_escrowInvariant st'
  have hlaw : Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) :=
    guardedLaw_admits_of_holds_and_step escrowInvariant_closed hinv hstep
  exact ⟨hlaw, hstep, hinv⟩

/-- Every valid `PrepaidLease` `advance` transition (under `DischargeOk` and budget conservation
    `st.remaining + st.drawn ≤ t.budget`) satisfies the non-trivial `prepaidLeaseLaw`. -/
theorem lease_advance_satisfies_prepaidLeaseLaw (facts : Facts) (t : LeaseTerms) (st : LeaseState)
    (clock amt pidx : Nat) (hok : DischargeOk t st clock amt pidx)
    (hcons : st.remaining + st.drawn ≤ t.budget) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st))
      (leaseStateToData t (advance t st)) = true := by
  have hrent : t.rent ≤ st.remaining := hok.2.2.2.2
  have h1 : decide ((Int.ofNat st.dischargedCount : Int) ≤ Int.ofNat (advance t st).dischargedCount) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h2 : decide ((Int.ofNat st.drawn : Int) ≤ Int.ofNat (advance t st).drawn) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h3 : decide ((Int.ofNat (advance t st).drawn : Int) ≤ Int.ofNat t.budget + 0) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h4 : decide (fieldOf "budget" (leaseStateToData t (advance t st)) = some (Int.ofNat t.budget)) = true :=
    decide_eq_true rfl
  have h5 : decide (fieldOf "rent" (leaseStateToData t (advance t st)) = some (Int.ofNat t.rent)) = true :=
    decide_eq_true rfl
  change ((match fieldOf "dischargedCount" (leaseStateToData t st),
                 fieldOf "dischargedCount" (leaseStateToData t (advance t st)) with
           | some v0, some v1 => decide (v0 ≤ v1) | _, _ => false) &&
          ((match fieldOf "drawn" (leaseStateToData t st),
                  fieldOf "drawn" (leaseStateToData t (advance t st)) with
            | some v0, some v1 => decide (v0 ≤ v1) | _, _ => false) &&
           ((match fieldOf "drawn" (leaseStateToData t (advance t st)),
                   fieldOf "budget" (leaseStateToData t (advance t st)) with
             | some v0, some v1 => decide (v0 ≤ v1 + 0) | _, _ => false) &&
            (((Int.ofNat t.budget == 0) ||
              decide (fieldOf "budget" (leaseStateToData t (advance t st)) = some (Int.ofNat t.budget))) &&
             ((Int.ofNat t.rent == 0) ||
              decide (fieldOf "rent" (leaseStateToData t (advance t st)) = some (Int.ofNat t.rent))))))) = true
  rw [leaseStateToData_field_dischargedCount, leaseStateToData_field_dischargedCount,
      leaseStateToData_field_drawn, leaseStateToData_field_drawn,
      h4, h5]
  rw [leaseStateToData_field_budget]
  dsimp only
  simp only [h1, h2, h3, Bool.or_true, Bool.and_self]

/-- Every valid `PrepaidLease` `advance` transition is admitted by `prepaidLeaseCellContract`
    and preserves `prepaidLeaseCellContract.invariant` (`0 Classical.choice`). -/
theorem lease_advance_admitted_by_contract (facts : Facts) (t : LeaseTerms) (st : LeaseState)
    (clock amt pidx : Nat) (hok : DischargeOk t st clock amt pidx)
    (hcons : st.remaining + st.drawn ≤ t.budget)
    (ag pr : String) (nb vu : Nat) :
    Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t (advance t st))
      (reqOf ag pr nb vu writeO facts) ∧
    Admits prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t (advance t st))
      (reqOf ag pr nb vu writeO facts) ∧
    Holds prepaidLeaseCellContract.invariant (leaseStateToData t (advance t st)) := by
  have hrent : t.rent ≤ st.remaining := hok.2.2.2.2
  have h1 : decide (st.dischargedCount ≤ (advance t st).dischargedCount) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h2 : decide (st.drawn ≤ (advance t st).drawn) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h3 : decide ((advance t st).drawn ≤ t.budget) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h4 : decide ((advance t st).remaining ≤ st.remaining) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have h5 : decide ((advance t st).remaining ≤ t.budget) = true :=
    decide_eq_true (by dsimp [advance]; omega)
  have hv : prepaidLeaseVerdictBool t st (advance t st) = true := by
    simp only [prepaidLeaseVerdictBool, h1, h2, h3, h4, h5, beq_self_eq_true, Bool.or_true, Bool.and_self]
  have hstep : Admits prepaidLeaseCellContract.stepRel (leaseStateToData t st)
      (leaseStateToData t (advance t st)) (reqOf ag pr nb vu writeO facts) :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st (advance t st) _)).1.2 hv
  have hinv : Holds prepaidLeaseCellContract.invariant (leaseStateToData t (advance t st)) :=
    holds_prepaidLeaseInvariant t (advance t st) (by dsimp [advance]; omega) (by dsimp [advance]; omega)
  have hlaw : Admits prepaidLeaseCellContract.law (leaseStateToData t st)
      (leaseStateToData t (advance t st)) (reqOf ag pr nb vu writeO facts) :=
    guardedLaw_admits_of_holds_and_step prepaidLeaseInvariant_closed hinv hstep
  exact ⟨hlaw, hstep, hinv⟩

/-- Constructive `CellContract` refusal of overdrawing `t.budget < st'.drawn` (`0 Classical.choice`). -/
theorem lease_overdraw_contract_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hover : t.budget < st'.drawn) (ag pr : String) (nb vu : Nat) :
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (st'.drawn ≤ t.budget) = false :=
    decide_eq_false (by omega)
  have hv : prepaidLeaseVerdictBool t st st' = false := by
    simp only [prepaidLeaseVerdictBool, hnotleNat, Bool.false_and, Bool.and_false]
  have href : Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st st' _)).2.2 hv
  have hnotadm : ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel prepaidLeaseInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- **Refusal Tooth 1 (Overdrawing `drawn > budget`)**:
    Any transition to a lease state `st'` with `t.budget < st'.drawn` is refused by `prepaidLeaseLaw`
    and rejected by `prepaidLeaseCellContract`. -/
theorem lease_overdraw_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hover : t.budget < st'.drawn) (ag pr : String) (nb vu : Nat) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotle : decide ((Int.ofNat st'.drawn : Int) ≤ Int.ofNat t.budget + 0) = false :=
    decide_eq_false (by simp only [Int.ofNat_eq_natCast]; omega)
  have hden : prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false := by
    simp only [prepaidLeaseLaw, monotone, leField, writeOnce, LawExpr.denote, LawRef.read,
      Option.bind_some, leaseStateToData_field_dischargedCount, leaseStateToData_field_drawn,
      leaseStateToData_field_budget, leaseStateToData_field_rent,
      hnotle, Bool.false_and, Bool.and_false]
  exact ⟨hden, lease_overdraw_contract_refused facts t st st' hover ag pr nb vu⟩

/-- Constructive `CellContract` refusal of decreasing `dischargedCount` (`0 Classical.choice`). -/
theorem lease_rollback_contract_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hdec : st'.dischargedCount < st.dischargedCount) (ag pr : String) (nb vu : Nat) :
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (st.dischargedCount ≤ st'.dischargedCount) = false :=
    decide_eq_false (by omega)
  have hv : prepaidLeaseVerdictBool t st st' = false := by
    simp only [prepaidLeaseVerdictBool, hnotleNat, Bool.false_and]
  have href : Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" :=
    (verdictOfBool_iff (prepaidLeaseStepBody_eval t st st' _)).2.2 hv
  have hnotadm : ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel prepaidLeaseInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- **Refusal Tooth 2 (Decreasing `dischargedCount` / Replay Rollback)**:
    Any transition to a lease state `st'` with `st'.dischargedCount < st.dischargedCount` is refused
    by `prepaidLeaseLaw` and rejected by `prepaidLeaseCellContract`. -/
theorem lease_rollback_dischargedCount_refused (facts : Facts) (t : LeaseTerms) (st st' : LeaseState)
    (hdec : st'.dischargedCount < st.dischargedCount) (ag pr : String) (nb vu : Nat) :
    prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData t st) (leaseStateToData t st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotle : decide ((Int.ofNat st.dischargedCount : Int) ≤ Int.ofNat st'.dischargedCount) = false :=
    decide_eq_false (by simp only [Int.ofNat_eq_natCast]; omega)
  have hden : prepaidLeaseLaw.denote facts (some (leaseStateToData t st)) (leaseStateToData t st') = false := by
    simp only [prepaidLeaseLaw, monotone, leField, writeOnce, LawExpr.denote, LawRef.read,
      Option.bind_some, leaseStateToData_field_dischargedCount, hnotle, Bool.false_and]
  exact ⟨hden, lease_rollback_contract_refused facts t st st' hdec ag pr nb vu⟩

/-- Constructive `CellContract` refusal of rolling back `settled` from 1 to 0 (`0 Classical.choice`). -/
theorem escrow_rollback_contract_refused (facts : Facts) (st st' : EscrowState)
    (hset : escrowSettledTag st = 1) (hunset : escrowSettledTag st' = 0)
    (ag pr : String) (nb vu : Nat) :
    Refuses escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) "escrowLaw" ∧
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotleNat : decide (escrowSettledTag st ≤ escrowSettledTag st') = false :=
    decide_eq_false (by rw [hset, hunset]; decide)
  have hv : escrowVerdictBool st st' = false := by
    simp only [escrowVerdictBool, hnotleNat, Bool.false_and]
  have href : Refuses escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) "escrowLaw" :=
    (verdictOfBool_iff (escrowStepBody_eval st st' _)).2.2 hv
  have hnotadm : ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) := by
    intro hadm
    obtain ⟨w, hw⟩ := guardedLaw_admits_imp_stepRel escrowInvariant_closed hadm
    have heq := evaluates_unique href hw
    injection heq with hlbl _
    exact absurd hlbl (by decide)
  exact ⟨href, hnotadm⟩

/-- **Refusal Tooth 3 (Escrow `settled` Rollback)**:
    Rolling back a settled escrow (`settled = 1`) to an unsettled state (`settled = 0`) is refused
    by `escrowLaw` and rejected by `escrowCellContract`. -/
theorem escrow_unsettled_rollback_refused (facts : Facts) (st st' : EscrowState)
    (hset : escrowSettledTag st = 1) (hunset : escrowSettledTag st' = 0)
    (ag pr : String) (nb vu : Nat) :
    escrowLaw.denote facts (some (escrowStateToData st)) (escrowStateToData st') = false ∧
    Refuses escrowCellContract.stepRel (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) "escrowLaw" ∧
    ¬ Admits escrowCellContract.law (escrowStateToData st) (escrowStateToData st')
      (reqOf ag pr nb vu writeO facts) := by
  have hnotle : decide ((Int.ofNat (escrowSettledTag st) : Int) ≤ Int.ofNat (escrowSettledTag st')) = false :=
    decide_eq_false (by rw [hset, hunset]; decide)
  have hden : escrowLaw.denote facts (some (escrowStateToData st)) (escrowStateToData st') = false := by
    simp only [escrowLaw, monotone, inRange, LawExpr.denote, LawRef.read,
      Option.bind_some, escrowStateToData_field_settled, hnotle, Bool.false_and]
  exact ⟨hden, escrow_rollback_contract_refused facts st st' hset hunset ag pr nb vu⟩

/-! ## 5. Coordination with Obend.Ledger.Book & VaultTurn -/

def escrowDepositPosting (escrowAcc : AccountId) (terms : EscrowTerms) (s : Side) : ResourcePosting :=
  match s with
  | .A => ⟨terms.sideA_account, escrowAcc, terms.sideA_asset, terms.sideA_amount⟩
  | .B => ⟨terms.sideB_account, escrowAcc, terms.sideB_asset, terms.sideB_amount⟩

def escrowSettlePostings (escrowAcc : AccountId) (terms : EscrowTerms) : List ResourcePosting :=
  [ ⟨escrowAcc, terms.sideA_account, terms.sideB_asset, terms.sideB_amount⟩,
    ⟨escrowAcc, terms.sideB_account, terms.sideA_asset, terms.sideA_amount⟩ ]

def escrowReclaimPosting (escrowAcc : AccountId) (terms : EscrowTerms) (s : Side) : ResourcePosting :=
  match s with
  | .A => ⟨escrowAcc, terms.sideA_account, terms.sideA_asset, terms.sideA_amount⟩
  | .B => ⟨escrowAcc, terms.sideB_account, terms.sideB_asset, terms.sideB_amount⟩

def leaseAdvancePosting (escrowAcc : AccountId) (terms : LeaseTerms) : ResourcePosting :=
  ⟨escrowAcc, terms.lessor, terms.asset, terms.rent⟩

theorem escrow_settle_conserves_book (b : Book) (escrowAcc : AccountId) (terms : EscrowTerms)
    (hesc : escrowAcc ∈ b.accounts) (hA : terms.sideA_account ∈ b.accounts) (hB : terms.sideB_account ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    ((escrowSettlePostings escrowAcc terms).foldl Book.applyPosting b).totalAsset ast = b.totalAsset ast := by
  simp only [escrowSettlePostings, List.foldl_cons, List.foldl_nil]
  let pB : ResourcePosting := ⟨escrowAcc, terms.sideA_account, terms.sideB_asset, terms.sideB_amount⟩
  let pA : ResourcePosting := ⟨escrowAcc, terms.sideB_account, terms.sideA_asset, terms.sideA_amount⟩
  have h1 : ((b.applyPosting pB).applyPosting pA).totalAsset ast = (b.applyPosting pB).totalAsset ast := by
    exact Book.applyPosting_conserves (b.applyPosting pB) pA hesc hB hnodup ast
  have h2 : (b.applyPosting pB).totalAsset ast = b.totalAsset ast := by
    exact Book.applyPosting_conserves b pB hesc hA hnodup ast
  exact h1.trans h2

theorem lease_advance_conserves_book (b : Book) (escrowAcc : AccountId) (terms : LeaseTerms)
    (hesc : escrowAcc ∈ b.accounts) (hlessor : terms.lessor ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.applyPosting (leaseAdvancePosting escrowAcc terms)).totalAsset ast = b.totalAsset ast := by
  exact Book.applyPosting_conserves b (leaseAdvancePosting escrowAcc terms) hesc hlessor hnodup ast

end Obend.Vault.Escrow

end
