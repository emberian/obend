module
/-
# Obend.Ledger.Book — conserved multi-asset balance ledger with credit floors

Multi-asset balance ledger with credit floors, account coordinates, and operations:
* `transfer`: moves value between accounts
* `mint`: moves value out of the asset's issuer well (negative supply)
* `burn`: returns value to that issuer well
* `fee`: moves value to an explicit collector
* `lease`: prepays `rate * epochs` to a lessor and installs the lease record
* `setFloor`: zero-value posting from issuer well installing credit floor
* `sweep`: moves demurrage/idle balance to commons or issuer well
* `hold`: reserves balance in escrow
* `release`: unreserves balance from escrow

Theorems:
* `applyPosting_conserves`: every posting preserves the per-asset total.
* `Operation.apply_conserves`: all 9 operations share one per-asset conservation theorem.
* `Batch.conservation`: batch execution of registrations, operations, and deregistrations conserves every asset.
-/

@[expose] public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## Account, Asset & Lease Coordinates -/

abbrev AccountId := Nat
abbrev AssetId := Nat
abbrev LeaseId := Nat
abbrev Epoch := Nat

/-- The floor of the protected coordinate space: kernel-held and seat account ids. -/
def protectedBase : Nat := 2 ^ 256

/-- The durable semantic content installed by a prepaid lease. -/
structure LeaseRecord where
  holder : AccountId
  lessor : AccountId
  asset : AssetId
  prepaid : Nat
  startsAt : Epoch
  expiresAt : Epoch
  deriving DecidableEq, Repr

/-- The conserved normal form: exactly one debit and one equal credit. -/
structure ResourcePosting where
  source : AccountId
  destination : AccountId
  asset : AssetId
  amount : Nat
  deriving DecidableEq, Repr

abbrev Book.Posting := ResourcePosting

/-- A signed multi-asset balance ledger with credit floors. -/
structure Book where
  accounts : List AccountId
  balances : AccountId → AssetId → Int
  leaseRecords : LeaseId → Option LeaseRecord
  floors : AccountId → AssetId → Nat

def Book.balance (b : Book) (a : AccountId) (ast : AssetId) : Int :=
  b.balances a ast

def Book.floor (b : Book) (a : AccountId) (ast : AssetId) : Nat :=
  b.floors a ast

def Book.leases (b : Book) (id : LeaseId) : Option LeaseRecord :=
  b.leaseRecords id

def Book.empty : Book where
  accounts := []
  balances := fun _ _ => 0
  leaseRecords := fun _ => none
  floors := fun _ _ => 0

/-- The conserved total for one asset across all registered accounts. -/
def Book.totalAsset (b : Book) (ast : AssetId) : Int :=
  (b.accounts.map (fun a => b.balance a ast)).sum

/-! ## Posting Execution & Invariant Preservation -/

def Book.applyPosting (b : Book) (p : ResourcePosting) : Book where
  accounts := b.accounts
  balances := fun a ast =>
    let cur := b.balances a ast
    if ast = p.asset then
      cur - (if a = p.source then (p.amount : Int) else 0)
          + (if a = p.destination then (p.amount : Int) else 0)
    else cur
  leaseRecords := b.leaseRecords
  floors := b.floors

@[simp] theorem Book.applyPosting_accounts (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).accounts = b.accounts := rfl

@[simp] theorem Book.applyPosting_floors (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).floors = b.floors := rfl

@[simp] theorem Book.applyPosting_leases (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).leaseRecords = b.leaseRecords := rfl

/-! ## Elementary Indicator Summation Lemmas -/

theorem sum_zero_of_forall_zero {α : Type} (l : List α) (f : α → Int) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx : f x = 0 := h x (List.Mem.head xs)
    have hxs : (xs.map f).sum = 0 := ih (fun y hy => h y (List.Mem.tail x hy))
    omega

theorem sum_single_indicator (l : List AccountId) (target : AccountId) (v : Int)
    (hmem : target ∈ l) (hnodup : l.Nodup) :
    (l.map fun a => if a = target then v else 0).sum = v := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    simp only [List.map_cons, List.sum_cons]
    if hxt : x = target then
      have hzero : ∀ a ∈ xs, (if a = target then v else 0) = 0 := by
        intro a ha
        have hne : a ≠ target := by
          intro he; subst he; subst hxt; exact hnodup.1 ha
        simp [hne]
      have hrest : (xs.map (fun a => if a = target then v else 0)).sum = 0 :=
        sum_zero_of_forall_zero xs _ hzero
      simp [hxt, hrest]
    else
      have hin : target ∈ xs := by
        cases hmem with
        | head => contradiction
        | tail _ h => exact h
      have hih := ih hin hnodup.2
      simp [hxt, hih]

theorem sum_map_add_sub (l : List AccountId) (f : AccountId → Int) (src dst : AccountId) (amt : Int) :
    (l.map fun a => f a - (if a = src then amt else 0) + (if a = dst then amt else 0)).sum =
    (l.map f).sum - (l.map fun a => if a = src then amt else 0).sum +
      (l.map fun a => if a = dst then amt else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    omega

/-- Every posting preserves the per-asset total. -/
theorem Book.applyPosting_conserves (b : Book) (p : ResourcePosting)
    (hsrc : p.source ∈ b.accounts) (hdst : p.destination ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.applyPosting p).totalAsset ast = b.totalAsset ast := by
  unfold Book.totalAsset Book.applyPosting Book.balance
  dsimp only
  by_cases heq : ast = p.asset
  · subst heq
    simp only [ite_true]
    rw [sum_map_add_sub b.accounts (fun a => b.balances a p.asset) p.source p.destination (p.amount : Int)]
    rw [sum_single_indicator b.accounts p.source (p.amount : Int) hsrc hnodup]
    rw [sum_single_indicator b.accounts p.destination (p.amount : Int) hdst hnodup]
    omega
  · simp only [heq, ite_false]

/-! ## The Nine Ledger Operations -/

inductive Operation where
  | transfer (source destination : AccountId) (asset : AssetId) (amount : Nat)
  | mint (asset : AssetId) (destination : AccountId) (amount : Nat)
  | burn (source : AccountId) (asset : AssetId) (amount : Nat)
  | fee (payer collector : AccountId) (asset : AssetId) (amount : Nat)
  | lease (leaseId : LeaseId) (holder lessor : AccountId) (asset : AssetId)
      (rate epochs : Nat) (startsAt : Epoch)
  | setFloor (asset : AssetId) (account : AccountId) (floor : Nat)
  | sweep (holder commons : AccountId) (asset : AssetId) (permille epochs amount : Nat)
  | hold (holder escrow : AccountId) (asset : AssetId) (amount : Nat)
  | release (escrow destination : AccountId) (asset : AssetId) (amount : Nat)
  deriving DecidableEq, Repr

def Operation.posting : Operation → ResourcePosting
  | .transfer s d a amt => ⟨s, d, a, amt⟩
  | .mint a d amt => ⟨a, d, a, amt⟩
  | .burn s a amt => ⟨s, a, a, amt⟩
  | .fee p c a amt => ⟨p, c, a, amt⟩
  | .lease _ h l a rate ep _ => ⟨h, l, a, rate * ep⟩
  | .setFloor a acc _ => ⟨a, acc, a, 0⟩
  | .sweep h c a _ _ amt => ⟨h, c, a, amt⟩
  | .hold h e a amt => ⟨h, e, a, amt⟩
  | .release e d a amt => ⟨e, d, a, amt⟩

def retained (permille : Nat) (balance : Nat) : Nat → Nat
  | 0 => balance
  | epochs + 1 =>
      let kept := retained permille balance epochs
      kept - kept * permille / 1000

def recycle (balance : Int) (permille epochs : Nat) : Nat :=
  balance.toNat - retained permille balance.toNat epochs

def Operation.WellFormed (b : Book) : Operation → Prop
  | .lease id _ _ _ _ epochs _ => 0 < epochs ∧ b.leases id = none
  | .setFloor a acc floor => -(Int.ofNat floor) ≤ b.balance acc a
  | .sweep h _ a permille epochs amt => amt = recycle (b.balance h a) permille epochs
  | _ => True

structure Admission (b : Book) (op : Operation) : Prop where
  sourcePresent : op.posting.source ∈ b.accounts
  destinationPresent : op.posting.destination ∈ b.accounts
  sourceWithinFloor :
    (op.posting.amount : Int) ≤ b.balance op.posting.source op.posting.asset +
      (b.floor op.posting.source op.posting.asset : Int)
  wellFormed : op.WellFormed b

def Operation.apply (op : Operation) (b : Book) : Book :=
  let paid := b.applyPosting op.posting
  match op with
  | .lease id h l a rate epochs startsAt =>
      { paid with leaseRecords := fun i =>
          if i = id then some ⟨h, l, a, rate * epochs, startsAt, startsAt + epochs⟩
          else paid.leaseRecords i }
  | .setFloor a acc floor =>
      { paid with floors := fun acc' a' =>
          if acc' = acc ∧ a' = a then floor
          else paid.floors acc' a' }
  | _ => paid

@[simp] theorem Operation.apply_accounts (op : Operation) (b : Book) :
    (op.apply b).accounts = b.accounts := by
  cases op <;> rfl

theorem Operation.apply_total_eq_posting (op : Operation) (b : Book) (ast : AssetId) :
    (op.apply b).totalAsset ast = (b.applyPosting op.posting).totalAsset ast := by
  cases op <;> rfl

/-- Common conservation theorem across all 9 operations. -/
theorem Operation.apply_conserves (op : Operation) (b : Book)
    (hsrc : op.posting.source ∈ b.accounts) (hdst : op.posting.destination ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (op.apply b).totalAsset ast = b.totalAsset ast := by
  rw [Operation.apply_total_eq_posting]
  exact b.applyPosting_conserves op.posting hsrc hdst hnodup ast

/-! ## Atomic Batch Execution -/

def Book.registerAccount (b : Book) (acc : AccountId) : Book :=
  { b with accounts := acc :: b.accounts }

def RegistrationAdmission (b : Book) (acc : AccountId) : Prop :=
  acc ∉ b.accounts ∧ (∀ a, b.balance acc a = 0) ∧ (∀ a, b.floor acc a = 0)

theorem Book.registerAccount_conserves (b : Book) (acc : AccountId)
    (adm : RegistrationAdmission b acc) (ast : AssetId) :
    (b.registerAccount acc).totalAsset ast = b.totalAsset ast := by
  unfold Book.totalAsset Book.registerAccount Book.balance
  simp only [List.map_cons, List.sum_cons]
  have h0 : b.balances acc ast = 0 := adm.2.1 ast
  rw [h0]
  omega

def registerAccounts (b : Book) : List AccountId → Book
  | [] => b
  | acc :: rest => registerAccounts (b.registerAccount acc) rest

def RegistrationsAdmitted (b : Book) : List AccountId → Prop
  | [] => True
  | acc :: rest => RegistrationAdmission b acc ∧ RegistrationsAdmitted (b.registerAccount acc) rest

def Book.deregisterAccount (b : Book) (acc : AccountId) : Book :=
  { b with accounts := b.accounts.erase acc }

def DeregistrationAdmission (b : Book) (acc : AccountId) : Prop :=
  protectedBase ≤ acc ∧ acc ∈ b.accounts ∧
    (∀ a, b.balance acc a = 0) ∧ (∀ a, b.floor acc a = 0)

theorem sum_erase_zero (l : List AccountId) (acc : AccountId) (f : AccountId → Int)
    (hmem : acc ∈ l) (hnodup : l.Nodup) (hzero : f acc = 0) :
    ((l.erase acc).map f).sum = (l.map f).sum := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    simp only [List.erase_cons]
    split
    · rename_i hxacc
      have hx : x = acc := beq_iff_eq.mp hxacc
      subst hx
      simp only [List.map_cons, List.sum_cons]
      rw [hzero]
      omega
    · rename_i hxacc
      have hx : x ≠ acc := by
        intro h
        subst h
        simp at hxacc
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact False.elim (hx rfl)
      · rw [ih hin hnodup.2]

theorem Book.deregisterAccount_conserves (b : Book) (acc : AccountId)
    (adm : DeregistrationAdmission b acc) (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.deregisterAccount acc).totalAsset ast = b.totalAsset ast := by
  unfold Book.totalAsset Book.deregisterAccount Book.balance
  exact sum_erase_zero b.accounts acc (fun a => b.balances a ast) adm.2.1 hnodup (adm.2.2.1 ast)

def deregisterAccounts (b : Book) : List AccountId → Book
  | [] => b
  | acc :: rest => deregisterAccounts (b.deregisterAccount acc) rest

def DeregistrationsAdmitted (b : Book) : List AccountId → Prop
  | [] => True
  | acc :: rest => DeregistrationAdmission b acc ∧ DeregistrationsAdmitted (b.deregisterAccount acc) rest

def applyOperations (b : Book) : List Operation → Book
  | [] => b
  | op :: rest => applyOperations (op.apply b) rest

def OperationsAdmitted (b : Book) : List Operation → Prop
  | [] => True
  | op :: rest => Admission b op ∧ OperationsAdmitted (op.apply b) rest

structure Batch where
  registrations : List AccountId
  operations : List Operation
  deregistrations : List AccountId
  deriving DecidableEq, Repr

def Batch.apply (batch : Batch) (b : Book) : Book :=
  deregisterAccounts
    (applyOperations (registerAccounts b batch.registrations) batch.operations)
    batch.deregistrations

def Batch.Admission (b : Book) (batch : Batch) : Prop :=
  RegistrationsAdmitted b batch.registrations ∧
    OperationsAdmitted (registerAccounts b batch.registrations) batch.operations ∧
    DeregistrationsAdmitted
      (applyOperations (registerAccounts b batch.registrations) batch.operations)
      batch.deregistrations

theorem registerAccounts_nodup {b : Book} (hnodup : b.accounts.Nodup) :
    ∀ {accs : List AccountId}, RegistrationsAdmitted b accs →
      (registerAccounts b accs).accounts.Nodup
  | [], _ => hnodup
  | acc :: rest, ⟨adm, radm⟩ => by
    have h1 : (b.registerAccount acc).accounts.Nodup := List.nodup_cons.mpr ⟨adm.1, hnodup⟩
    exact registerAccounts_nodup h1 radm

theorem applyOperations_nodup {b : Book} (hnodup : b.accounts.Nodup) :
    ∀ (ops : List Operation), (applyOperations b ops).accounts.Nodup
  | [] => hnodup
  | op :: rest => by
    have h1 : (op.apply b).accounts.Nodup := by rw [op.apply_accounts]; exact hnodup
    exact applyOperations_nodup h1 rest

theorem registerAccounts_conserves (b : Book) (accs : List AccountId)
    (adm : RegistrationsAdmitted b accs) (ast : AssetId) :
    (registerAccounts b accs).totalAsset ast = b.totalAsset ast := by
  induction accs generalizing b with
  | nil => rfl
  | cons acc rest ih =>
    exact (ih (b.registerAccount acc) adm.2).trans (b.registerAccount_conserves acc adm.1 ast)

theorem applyOperations_conserves (b : Book) (ops : List Operation)
    (hnodup : b.accounts.Nodup) (adm : OperationsAdmitted b ops) (ast : AssetId) :
    (applyOperations b ops).totalAsset ast = b.totalAsset ast := by
  induction ops generalizing b with
  | nil => rfl
  | cons op rest ih =>
    have hop := op.apply_conserves b adm.1.sourcePresent adm.1.destinationPresent hnodup ast
    have h1 : (op.apply b).accounts.Nodup := by rw [op.apply_accounts]; exact hnodup
    exact (ih (op.apply b) h1 adm.2).trans hop

theorem deregisterAccounts_conserves (b : Book) (accs : List AccountId)
    (hnodup : b.accounts.Nodup) (adm : DeregistrationsAdmitted b accs) (ast : AssetId) :
    (deregisterAccounts b accs).totalAsset ast = b.totalAsset ast := by
  induction accs generalizing b with
  | nil => rfl
  | cons acc rest ih =>
    have hdec : (b.deregisterAccount acc).accounts.Nodup := List.Nodup.erase acc hnodup
    exact (ih (b.deregisterAccount acc) hdec adm.2).trans (b.deregisterAccount_conserves acc adm.1 hnodup ast)

/-- Universal batch conservation law. -/
theorem Batch.conservation (b : Book) (batch : Batch)
    (adm : batch.Admission b) (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (batch.apply b).totalAsset ast = b.totalAsset ast := by
  unfold Batch.apply
  have hreg_nodup := registerAccounts_nodup hnodup adm.1
  have hops_nodup := applyOperations_nodup hreg_nodup batch.operations
  have hdereg := deregisterAccounts_conserves _ batch.deregistrations hops_nodup adm.2.2 ast
  have hops := applyOperations_conserves _ batch.operations hreg_nodup adm.2.1 ast
  have hreg := registerAccounts_conserves b batch.registrations adm.1 ast
  exact hdereg.trans (hops.trans hreg)

end Obend.Ledger
