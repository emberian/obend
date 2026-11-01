module
/-
# Obend.Vault.Escrow — House Capacities as C4 Kinds: SealedEscrow and PrepaidLease

Absorbs `breadstuffs/Dregg2/Deos/SealedEscrow.lean` and `breadstuffs/Dregg2/Deos/PrepaidLease.lean`
into Obend's C4 Kind system, conserved resource Book (`Obend.Ledger.Book`), and multi-cell turns (`Obend.Vault.Hyperedge`).
-/
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Kind
public import Obend.Ledger.Book
public import Obend.Vault.Hyperedge
public import Obend.Law.Contract
public import Obend.Spec.Law

@[expose] public section

namespace Obend.Vault.Escrow

open Obend.Core.Data
open Obend.Core.Term
open Obend.Kind
open Obend.Ledger
open Obend.Vault
open Obend.Spec.Law

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
  fun t => if t = s then v else f t

@[simp] theorem upd_same {α : Type} (f : Side → α) (s : Side) (v : α) :
    upd f s v s = v := by
  simp [upd]

@[simp] theorem upd_ne {α : Type} (f : Side → α) (s : Side) (v : α) {t : Side} (h : t ≠ s) :
    upd f s v t = f t := by
  simp [upd, h]

theorem upd_pair_sum (f : Side → Nat) (s : Side) (v : Nat) :
    upd f s v Side.A + upd f s v Side.B = (f Side.A + f Side.B) - f s + v := by
  cases s <;> simp [upd] <;> omega

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
  if st.status s = .empty then 0 else st.amount s

def locked (st : EscrowState) (s : Side) : Nat :=
  if st.status s = .deposited then st.amount s else 0

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
        by_cases h : t = s
        · subst h
          unfold locked entered
          simp [upd_same]
          have hpre := ih.cons t
          unfold locked entered at hpre
          simp [hempty] at hpre
          omega
        · unfold locked entered
          simp [upd_ne _ _ _ h]
          have hpre := ih.cons t
          unfold locked entered at hpre
          exact hpre
      · exact ih.balance
      · intro t
        by_cases h : t = s
        · subst h; simp [upd_same]
        · simp [upd_ne _ _ _ h]; exact ih.participate t
  | settle hA hB =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        unfold locked entered
        cases t
        · simp
          have hc := ih.cons Side.A
          unfold locked entered at hc
          simp [hA] at hc
          omega
        · simp
          have hc := ih.cons Side.B
          unfold locked entered at hc
          simp [hB] at hc
          omega
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        simp [Side.other]
        omega
      · intro t _; cases t <;> contradiction
  | reclaim s hdep =>
      refine ⟨?_, ?_, ?_⟩
      · intro t
        by_cases h : t = s
        · subst h
          unfold locked entered
          simp [upd_same]
          have hc := ih.cons t
          unfold locked entered at hc
          simp [hdep] at hc
          omega
        · unfold locked entered
          simp [upd_ne _ _ _ h]
          have hc := ih.cons t
          unfold locked entered at hc
          exact hc
      · unfold recvTotal paidTotal
        have hb := ih.balance
        unfold recvTotal paidTotal at hb
        cases s <;> simp [upd] <;> omega
      · intro t
        by_cases h : t = s
        · subst h; simp [upd_same]
        · simp [upd_ne _ _ _ h]; exact ih.participate t

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
  simp [hempty] at hc
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

/-! ## 4. C4 Nominal Kind Registration -/

def trivialLaw : LawExpr := .eqR .turn .turn

def escrowKindCell : KindCell LawExpr where
  name := "escrow"
  version := 1
  layout := ["termsDigest", "sideA_account", "sideA_asset", "sideA_amount", "sideA_status",
             "sideB_account", "sideB_asset", "sideB_amount", "sideB_status", "timeout"]
  init := .record [
    ("termsDigest", .natural 0),
    ("sideA_amount", .natural 0),
    ("sideB_amount", .natural 0),
    ("timeout", .natural 0)
  ]
  law := trivialLaw
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
  law := trivialLaw
  parents := ["escrow"]

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
