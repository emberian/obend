module
/-
# Obend.Ledger.Book — Finite-Support Multi-Asset Resource Ledger Bridged to `Floors` & `Register`

Replaces function-closure internals (`AccountId → AssetId → Int`) with the closure-free
finite-support resource kernel from `Obend.Ledger.Floors` and `Obend.Ledger.Register`:

1. **Finite-Support `Book` (`DecidableEq`, `Repr`, Zero Closures)**:
   - Backed by `FinMap (AccountId × AssetId)` (`entries : List ((AccountId × AssetId) × Int)`),
     `leaseMap : List (LeaseId × LeaseRecord)`, and `floorMap : List ((AccountId × AssetId) × Nat)`.
   - Exposes `Book.heldAssets (b : Book) (acc : AccountId) : List AssetId`, computing the exact
     duplicate-free finite support `{ ast | b.balance acc ast ≠ 0 }` executably!
2. **Elimination of `AssetId`/`AccountId` Issuer-Well Collision**:
   - `mint`, `burn`, and `setFloor` route issuer supply through `issuerWellAccount asset`
     (`2 * protectedBase + asset`), strictly disjoint from ordinary user accounts (`< protectedBase`)
     and protected seat/escrow accounts (`[protectedBase, 2 * protectedBase)`).
3. **Direct `Register.Movement` Bridge**:
   - `ResourcePosting.toMovements` compiles any `ResourcePosting` to balanced `Register.Movement` pairs.
-/
public import Obend.Ledger.Floors

@[expose] public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## Lease & Posting Records -/

/-- The durable semantic content installed by a prepaid lease. -/
structure LeaseRecord where
  holder   : AccountId
  lessor   : AccountId
  asset    : AssetId
  prepaid  : Nat
  startsAt : Epoch
  expiresAt : Epoch
  deriving DecidableEq, Repr

/-- Conserved normal-form posting: one debit on `source` and one equal credit on `destination`. -/
structure ResourcePosting where
  source      : AccountId
  destination : AccountId
  asset       : AssetId
  amount      : Nat
  deriving DecidableEq, Repr

abbrev Book.Posting := ResourcePosting

/-- Compile a `ResourcePosting` to balanced `Register.Movement` lines on `Obend.Ledger.Register`. -/
def ResourcePosting.toMovements (p : ResourcePosting) : List Movement :=
  let acctStr (acc : AccountId) :=
    "acct:" ++ String.ofList (natBitChars acc) ++ ":ast:" ++ String.ofList (natBitChars p.asset)
  transferMovements (acctStr p.source) (acctStr p.destination) p.amount

theorem ResourcePosting.toMovements_balanced (p : ResourcePosting) :
    (p.toMovements.map (·.debit)).sum = (p.toMovements.map (·.credit)).sum :=
  transferMovements_balanced _ _ _

/-! ## Finite-Support `Book` (Closure-Free) -/

/-- Closure-free signed multi-asset balance ledger with finite support and credit floors. -/
structure Book where
  accounts     : List AccountId := []
  balances     : FinMap (AccountId × AssetId) := FinMap.empty
  leaseRecords : List (LeaseId × LeaseRecord) := []
  floors       : List ((AccountId × AssetId) × Nat) := []
  deriving DecidableEq, Repr

def Book.balance (b : Book) (a : AccountId) (ast : AssetId) : Int :=
  b.balances.get (a, ast)

def Book.floor (b : Book) (a : AccountId) (ast : AssetId) : Nat :=
  (b.floors.lookup (a, ast)).getD 0

def Book.leases (b : Book) (id : LeaseId) : Option LeaseRecord :=
  b.leaseRecords.lookup id

def Book.empty : Book := {}

@[simp] theorem Book.balance_empty (a : AccountId) (ast : AssetId) :
    Book.empty.balance a ast = 0 := rfl

/-- Update a single `(account, asset)` balance in `b` (useful for initializing test books cleanly). -/
def Book.setBalance (b : Book) (a : AccountId) (ast : AssetId) (val : Int) : Book :=
  { b with balances := b.balances.set (a, ast) val }

@[simp] theorem Book.balance_setBalance (b : Book) (a a' : AccountId) (ast ast' : AssetId) (val : Int) :
    (b.setBalance a ast val).balance a' ast' =
      if a' = a ∧ ast' = ast then val else b.balance a' ast' := by
  unfold Book.setBalance Book.balance
  simp [FinMap.get_set, Prod.mk.injEq]

/-- Exact finite duplicate-free list of all assets in which `acc` currently holds a nonzero balance. -/
def Book.heldAssets (b : Book) (acc : AccountId) : List AssetId :=
  (dedupLocal ((b.balances.entries.filter (fun p => p.1.1 == acc)).map (fun p => p.1.2))).filter
    (fun ast => b.balance acc ast != 0)

theorem Book.heldAssets_nodup (b : Book) (acc : AccountId) :
    (b.heldAssets acc).Nodup := by
  unfold Book.heldAssets
  exact nodup_filter_local _ (nodup_dedupLocal _)

theorem Book.balance_zero_of_not_in_entries (b : Book) (acc : AccountId) (ast : AssetId)
    (hnot : (acc, ast) ∉ b.balances.entries.map Prod.fst) :
    b.balance acc ast = 0 :=
  FinMap.get_eq_zero_of_not_mem_fst b.balances (acc, ast) hnot

theorem Book.mem_heldAssets_iff (b : Book) (acc : AccountId) (ast : AssetId) :
    ast ∈ b.heldAssets acc ↔ b.balance acc ast ≠ 0 := by
  unfold Book.heldAssets
  rw [List.mem_filter, mem_dedupLocal, bne_iff_ne]
  constructor
  · exact fun h => h.2
  · intro hne
    refine ⟨?_, hne⟩
    have hmem_fst : (acc, ast) ∈ b.balances.entries.map Prod.fst :=
      Classical.byContradiction fun hnot => hne (b.balance_zero_of_not_in_entries acc ast hnot)
    rcases List.mem_map.mp hmem_fst with ⟨⟨⟨a0, ast0⟩, v⟩, hp, heq⟩
    cases heq
    exact List.mem_map.mpr ⟨((acc, ast), v), List.mem_filter.mpr ⟨hp, beq_self_eq_true acc⟩, rfl⟩

theorem Book.balance_eq_zero_of_not_mem_heldAssets (b : Book) (acc : AccountId) {ast : AssetId}
    (hnot : ast ∉ b.heldAssets acc) :
    b.balance acc ast = 0 :=
  Classical.byContradiction fun hne => hnot ((b.mem_heldAssets_iff acc ast).mpr hne)

/-- Conserved total for one asset across all registered accounts in `b.accounts`. -/
def Book.totalAsset (b : Book) (ast : AssetId) : Int :=
  (b.accounts.map (fun a => b.balance a ast)).sum

/-- Global algebraic sum of `ast` across the entire `FinMap` (independent of `b.accounts`). -/
def Book.globalAssetSum (b : Book) (ast : AssetId) : Int :=
  ((b.balances.entries.filter (fun p => p.1.2 == ast)).map Prod.snd).sum

/-! ## Posting Execution & Invariant Preservation -/

def Book.applyPosting (b : Book) (p : ResourcePosting) : Book where
  accounts := b.accounts
  balances :=
    (b.balances.addDelta (p.source, p.asset) (-(p.amount : Int))).addDelta
      (p.destination, p.asset) (p.amount : Int)
  leaseRecords := b.leaseRecords
  floors := b.floors

@[simp] theorem Book.applyPosting_accounts (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).accounts = b.accounts := rfl

@[simp] theorem Book.applyPosting_floors (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).floors = b.floors := rfl

@[simp] theorem Book.applyPosting_leases (b : Book) (p : ResourcePosting) :
    (b.applyPosting p).leaseRecords = b.leaseRecords := rfl

theorem Book.balance_applyPosting (b : Book) (p : ResourcePosting) (a : AccountId) (ast : AssetId) :
    (b.applyPosting p).balance a ast =
      if ast = p.asset then
        b.balance a ast
          - (if a = p.source then (p.amount : Int) else 0)
          + (if a = p.destination then (p.amount : Int) else 0)
      else b.balance a ast := by
  unfold Book.applyPosting Book.balance
  simp only [FinMap.get_addDelta, Prod.mk.injEq]
  by_cases hast : ast = p.asset <;> by_cases hs : a = p.source <;> by_cases hd : a = p.destination
  all_goals
    simp_all
    try omega

/-! ## Indicator Summation Lemmas -/

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

/-- Every posting preserves `totalAsset` across registered accounts. -/
theorem Book.applyPosting_conserves (b : Book) (p : ResourcePosting)
    (hsrc : p.source ∈ b.accounts) (hdst : p.destination ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.applyPosting p).totalAsset ast = b.totalAsset ast := by
  unfold Book.totalAsset
  have hpoint : (b.accounts.map fun a => (b.applyPosting p).balance a ast) =
      (b.accounts.map fun a =>
        if ast = p.asset then
          b.balance a ast
            - (if a = p.source then (p.amount : Int) else 0)
            + (if a = p.destination then (p.amount : Int) else 0)
        else b.balance a ast) := by
    apply List.map_congr_left
    intro a _
    exact Book.balance_applyPosting b p a ast
  rw [Book.applyPosting_accounts, hpoint]
  by_cases heq : ast = p.asset
  · subst heq
    simp only [ite_true]
    rw [sum_map_add_sub b.accounts (fun a => b.balance a p.asset) p.source p.destination (p.amount : Int)]
    rw [sum_single_indicator b.accounts p.source (p.amount : Int) hsrc hnodup]
    rw [sum_single_indicator b.accounts p.destination (p.amount : Int) hdst hnodup]
    omega
  · simp only [heq, ite_false]

/-- Every posting ALSO preserves `globalAssetSum` unconditionally (even without account registration). -/
theorem Book.applyPosting_conserves_global (b : Book) (p : ResourcePosting) (ast : AssetId) :
    (b.applyPosting p).globalAssetSum ast = b.globalAssetSum ast := by
  unfold Book.applyPosting Book.globalAssetSum
  have step (m : FinMap (AccountId × AssetId)) (acc : AccountId) (pAst : AssetId) (d : Int) :
      (((m.addDelta (acc, pAst) d).entries.filter (fun q => q.1.2 == ast)).map Prod.snd).sum =
        ((m.entries.filter (fun q => q.1.2 == ast)).map Prod.snd).sum +
          (if pAst = ast then d else 0) := by
    unfold FinMap.addDelta
    cases hd : d == 0 with
    | true =>
      have hd0 : d = 0 := beq_iff_eq.mp hd
      subst hd0; simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      by_cases ha : pAst = ast
      · subst ha; simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · have hb : (pAst == ast) = false := beq_eq_false_iff_ne.mpr ha
        simp [hb, ha]
  rw [step, step]
  by_cases ha : p.asset = ast
  · subst ha; simp; omega
  · simp [ha]

/-! ## The Nine Ledger Operations (with Protected `issuerWellAccount` Namespace) -/

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

/-- Normalization of all 9 operations to a single `ResourcePosting`, routing `mint`, `burn`,
    and `setFloor` through the dedicated `issuerWellAccount asset` namespace (`2 * protectedBase + asset`)
    so `asset : AssetId` can never collide with ordinary user or seat `AccountId`s! -/
def Operation.posting : Operation → ResourcePosting
  | .transfer s d a amt => ⟨s, d, a, amt⟩
  | .mint a d amt => ⟨issuerWellAccount a, d, a, amt⟩
  | .burn s a amt => ⟨s, issuerWellAccount a, a, amt⟩
  | .fee p c a amt => ⟨p, c, a, amt⟩
  | .lease _ h l a rate ep _ => ⟨h, l, a, rate * ep⟩
  | .setFloor a acc _ => ⟨issuerWellAccount a, acc, a, 0⟩
  | .sweep h c a _ _ amt => ⟨h, c, a, amt⟩
  | .hold h e a amt => ⟨h, e, a, amt⟩
  | .release e d a amt => ⟨e, d, a, amt⟩

/-- Minting `amt` of `asset` to an ordinary user `u < protectedBase` (even `asset = 0, u = 0`)
    credits `u` by the full `+amt` instead of self-cancelling! -/
theorem mint_credits_ordinary_user (b : Book) (ast : AssetId) (u : AccountId) (amt : Nat)
    (hu : u < protectedBase) :
    (b.applyPosting (Operation.mint ast u amt).posting).balance u ast =
      b.balance u ast + (amt : Int) := by
  have hne : u ≠ issuerWellAccount ast := Ne.symm (issuerWellAccount_ne_ordinary hu ast)
  rw [Book.balance_applyPosting]
  simp [Operation.posting, hne]

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
      { paid with leaseRecords := (id, ⟨h, l, a, rate * epochs, startsAt, startsAt + epochs⟩) :: paid.leaseRecords }
  | .setFloor a acc fl =>
      { paid with floors := ((acc, a), fl) :: paid.floors }
  | _ => paid

@[simp] theorem Operation.apply_accounts (op : Operation) (b : Book) :
    (op.apply b).accounts = b.accounts := by
  cases op <;> rfl

theorem Operation.apply_total_eq_posting (op : Operation) (b : Book) (ast : AssetId) :
    (op.apply b).totalAsset ast = (b.applyPosting op.posting).totalAsset ast := by
  cases op <;> rfl

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
  unfold Book.totalAsset Book.registerAccount
  simp only [List.map_cons, List.sum_cons]
  have h0 : b.balance acc ast = 0 := adm.2.1 ast
  dsimp [Book.balance] at h0 ⊢
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
        intro h; subst h; simp at hxacc
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact False.elim (hx rfl)
      · rw [ih hin hnodup.2]

theorem Book.deregisterAccount_conserves (b : Book) (acc : AccountId)
    (adm : DeregistrationAdmission b acc) (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (b.deregisterAccount acc).totalAsset ast = b.totalAsset ast := by
  unfold Book.totalAsset Book.deregisterAccount
  exact sum_erase_zero b.accounts acc (fun a => b.balance a ast) adm.2.1 hnodup (adm.2.2.1 ast)

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
  registrations   : List AccountId
  operations      : List Operation
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

theorem registerAccounts_nodup (accs : List AccountId) (b : Book)
    (hnodup : b.accounts.Nodup) (hadm : RegistrationsAdmitted b accs) :
    (registerAccounts b accs).accounts.Nodup := by
  induction accs generalizing b with
  | nil => exact hnodup
  | cons acc tail ih =>
    exact ih (b.registerAccount acc) (List.nodup_cons.mpr ⟨hadm.1.1, hnodup⟩) hadm.2

theorem applyOperations_nodup :
    ∀ (ops : List Operation) {b : Book}, b.accounts.Nodup → (applyOperations b ops).accounts.Nodup
  | [], _, hnodup => hnodup
  | op :: rest, b, hnodup => by
    have h1 : (op.apply b).accounts.Nodup := by rw [op.apply_accounts]; exact hnodup
    exact applyOperations_nodup rest h1

theorem mem_erase_sub {α : Type} [BEq α] {a x : α} :
    ∀ {l : List α}, x ∈ l.erase a → x ∈ l
  | [], h => h
  | b :: bs, h => by
    rw [List.erase_cons] at h
    split at h
    · exact List.Mem.tail b h
    · rcases List.mem_cons.mp h with rfl | hm
      · exact List.Mem.head bs
      · exact List.Mem.tail b (mem_erase_sub hm)

theorem nodup_erase_local (a : AccountId) :
    ∀ {l : List AccountId}, l.Nodup → (l.erase a).Nodup
  | [], h => h
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.erase_cons]
    split
    · exact hnd.2
    · rw [List.nodup_cons]
      exact ⟨fun hm => hnd.1 (mem_erase_sub hm), nodup_erase_local a hnd.2⟩

theorem registerAccounts_conserves (b : Book) (accs : List AccountId)
    (adm : RegistrationsAdmitted b accs) (ast : AssetId) :
    (registerAccounts b accs).totalAsset ast = b.totalAsset ast := by
  induction accs generalizing b with
  | nil => rfl
  | cons acc _ ih =>
    exact (ih (b.registerAccount acc) adm.2).trans (b.registerAccount_conserves acc adm.1 ast)

theorem applyOperations_conserves (b : Book) (ops : List Operation)
    (hnodup : b.accounts.Nodup) (adm : OperationsAdmitted b ops) (ast : AssetId) :
    (applyOperations b ops).totalAsset ast = b.totalAsset ast := by
  induction ops generalizing b with
  | nil => rfl
  | cons op _ ih =>
    have hop := op.apply_conserves b adm.1.sourcePresent adm.1.destinationPresent hnodup ast
    have h1 : (op.apply b).accounts.Nodup := by rw [op.apply_accounts]; exact hnodup
    exact (ih (op.apply b) h1 adm.2).trans hop

theorem deregisterAccounts_conserves (b : Book) (accs : List AccountId)
    (hnodup : b.accounts.Nodup) (adm : DeregistrationsAdmitted b accs) (ast : AssetId) :
    (deregisterAccounts b accs).totalAsset ast = b.totalAsset ast := by
  induction accs generalizing b with
  | nil => rfl
  | cons acc _ ih =>
    have hdec : (b.deregisterAccount acc).accounts.Nodup := nodup_erase_local acc hnodup
    exact (ih (b.deregisterAccount acc) hdec adm.2).trans (b.deregisterAccount_conserves acc adm.1 hnodup ast)

theorem Batch.conservation (b : Book) (batch : Batch)
    (adm : batch.Admission b) (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (batch.apply b).totalAsset ast = b.totalAsset ast := by
  unfold Batch.apply
  have hreg_nodup := registerAccounts_nodup batch.registrations b hnodup adm.1
  have hops_nodup := applyOperations_nodup batch.operations hreg_nodup
  have hdereg := deregisterAccounts_conserves _ batch.deregistrations hops_nodup adm.2.2 ast
  have hops := applyOperations_conserves _ batch.operations hreg_nodup adm.2.1 ast
  have hreg := registerAccounts_conserves b batch.registrations adm.1 ast
  exact hdereg.trans (hops.trans hreg)

end Obend.Ledger

end
