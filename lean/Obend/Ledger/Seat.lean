module
/-
# Obend.Ledger.Seat — ZoE offer-safe seats with protected account positions

An `offer` presents a proposal `{give, want, exit}`:
- The seat's account coordinate is in the protected space (`protectedBase ≤ account`, ≥ 2^256).
- The seat's balances are judged by `safeAt`:
    either every `want` is met, OR every `give` is refunded (Zoe offer safety).
- Crediting a seat is monotone: `safeAt_mono`.
- Unconditional exit payout: `payout_exact`, `exit_pays_allocation`, `exit_recovery_all`.
- Commutativity and conservation: `payout_conserves`.
-/

public import Obend.Ledger.Book

@[expose] public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## Proposals & Offer Safety -/

inductive ExitRule where
  | onDemand
  | afterDeadline (due : Nat)
  deriving DecidableEq, Repr

structure Disclosure where
  offerer : Bool := false
  payee : Bool := false
  holder : Bool := false
  deriving DecidableEq, Repr

structure Proposal where
  give : List (AssetId × Nat)
  want : List (AssetId × Nat)
  exit : ExitRule
  donate : Bool
  disclose : Disclosure := {}
  deriving DecidableEq, Repr

def Proposal.assets (p : Proposal) : List AssetId :=
  ((p.give ++ p.want).map Prod.fst).eraseDups

/-- Check that `p.give` and `p.want` each have duplicate-free asset keys. -/
def Proposal.assetsNodupB (p : Proposal) : Bool :=
  decide ((p.give.map Prod.fst).Nodup ∧ (p.want.map Prod.fst).Nodup)

/-- Total amount requested or offered for `ast` across all entries in `pairs`
    (summing duplicate asset keys so `[(0, 50), (0, 50)]` requires `100` of asset `0`). -/
def assetAmountSum (pairs : List (AssetId × Nat)) (ast : AssetId) : Nat :=
  ((pairs.filter (fun (a, _) => a == ast)).map Prod.snd).sum

/-- Offer safety: either every `want` is met, or every `give` is refunded,
    with per-asset amounts summed across any duplicate keys. -/
def safeAt (b : Book) (account : AccountId) (p : Proposal) : Bool :=
  let wantMet :=
    p.want.all fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum p.want ast : Int) ≤ b.balance account ast)
  let giveRefunded :=
    p.give.all fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum p.give ast : Int) ≤ b.balance account ast)
  wantMet || giveRefunded

theorem atLeast_mono {b b' : Book} {account account' : AccountId}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (pairs fullPairs : List (AssetId × Nat))
    (hall : pairs.all (fun (ast, amt) =>
      decide ((amt : Int) ≤ b.balance account ast) &&
      decide ((assetAmountSum fullPairs ast : Int) ≤ b.balance account ast)) = true) :
    pairs.all (fun (ast, amt) =>
      decide ((amt : Int) ≤ b'.balance account' ast) &&
      decide ((assetAmountSum fullPairs ast : Int) ≤ b'.balance account' ast)) = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall ⊢
    refine ⟨⟨Int.le_trans hall.1.1 (hmore pair.1), Int.le_trans hall.1.2 (hmore pair.1)⟩, ih hall.2⟩

/-- The law is monotone: crediting an account never violates offer safety. -/
theorem safeAt_mono {b b' : Book} {account account' : AccountId} {p : Proposal}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (hsafe : safeAt b account p = true) :
    safeAt b' account' p = true := by
  unfold safeAt at hsafe ⊢
  simp only [Bool.or_eq_true] at hsafe ⊢
  rcases hsafe with hwant | hgive
  · left; exact atLeast_mono hmore p.want p.want hwant
  · right; exact atLeast_mono hmore p.give p.give hgive

/-- Duplicate asset keys in `want` cannot double-count a single asset balance under `safeAt`. -/
example :
    let b : Book := {
      accounts := [protectedBase]
      balances := fun acc ast => if acc == protectedBase && ast == 0 then 60 else 0
      leaseRecords := fun _ => none
      floors := fun _ _ => 0
    }
    let p : Proposal := {
      give := [(1, 100)]
      want := [(0, 50), (0, 50)]
      exit := .onDemand
      donate := false
    }
    safeAt b protectedBase p = false := rfl

/-! ## The Seat Structure & Protected Coordinates (Major Finding 4) -/

/-- A ZoE seat carrying proof that its account coordinate is in the protected space
    (`protectedBase ≤ account`), and that its payee differs from the seat account. -/
structure Seat where
  account : AccountId
  h_protected : protectedBase ≤ account := by decide
  inst : Nat := 0
  offerer : Nat := 0
  payee : AccountId := 0
  h_payee_diff : payee ≠ account := by decide
  proposal : Proposal
  holder : Option Nat := none
  deriving DecidableEq, Repr

/-- Ordinary accounts below `protectedBase` cannot collide with a seat's protected account. -/
theorem ordinary_ne_seat_account {ordinary : AccountId} (s : Seat)
    (h_ord : ordinary < protectedBase) : ordinary ≠ s.account :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord s.h_protected)

/-! ## World Collections & Distinct Seat Accounts (Major Finding 4) -/

/-- A collection of active seats and ledger book, enforcing distinct seat accounts. -/
structure World where
  book : Book
  seats : List Seat
  nodup_seats : (seats.map Seat.account).Nodup := by decide
  assets : List AssetId := []

/-- Lookup an open seat by its unique account coordinate. -/
def World.seat? (w : World) (acc : AccountId) : Option Seat :=
  w.seats.find? (fun s => s.account == acc)

theorem seats_find_mem (seats : List Seat) (hnodup : (seats.map Seat.account).Nodup) {s : Seat} (hmem : s ∈ seats) :
    seats.find? (fun x => x.account == s.account) = some s := by
  induction seats with
  | nil => cases hmem
  | cons head rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    split
    · rename_i hbeq
      have heq : head.account = s.account := beq_iff_eq.mp hbeq
      rcases List.mem_cons.mp hmem with rfl | hin
      · rfl
      · have hcontra : s.account ∈ rest.map Seat.account := List.mem_map_of_mem hin
        rw [← heq] at hcontra
        exact False.elim (hnodup.1 hcontra)
    · rename_i hbeq
      have hne : head.account ≠ s.account := by
        intro heq
        rw [heq] at hbeq
        simp at hbeq
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact False.elim (hne rfl)
      · exact ih hnodup.2 hin

/-- Looking up any registered seat by its account succeeds uniquely. -/
theorem World.seat?_mem (w : World) {s : Seat} (hmem : s ∈ w.seats) :
    w.seat? s.account = some s :=
  seats_find_mem w.seats w.nodup_seats hmem

/-- Injective coordinates: distinct seat entries in a world never share an account. -/
theorem seats_account_inj (w : World) {s1 s2 : Seat}
    (h1 : s1 ∈ w.seats) (h2 : s2 ∈ w.seats) (heq : s1.account = s2.account) :
    s1 = s2 := by
  have h_find1 := w.seat?_mem h1
  have h_find2 := w.seat?_mem h2
  rw [heq] at h_find1
  rw [h_find1] at h_find2
  cases h_find2
  rfl

/-! ## Payout Transfers & Complete Exit Recovery (Major Finding 5) -/

/-- Preconditions for an exit payout:
    1. The payee is distinct from the seat account (`payee ≠ account`).
    2. All balances of the seat account across active assets are non-negative.
    3. The active assets list contains no duplicate entries.
    4. The seat holds zero balance for any asset outside the active assets list. -/
structure ExitPrecondition (b : Book) (account payee : AccountId) (assets : List AssetId) : Prop where
  h_diff : payee ≠ account
  h_nonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast
  h_nodup : assets.Nodup
  h_zero_outside : ∀ ast ∉ assets, b.balance account ast = 0

def payoutPostings (b : Book) (account payee : AccountId) (assets : List AssetId) : List ResourcePosting :=
  assets.map fun ast => ⟨account, payee, ast, (b.balance account ast).toNat⟩

def applyPostings (b : Book) (ps : List ResourcePosting) : Book :=
  ps.foldl Book.applyPosting b

@[simp] theorem applyPostings_nil (b : Book) : applyPostings b [] = b := rfl

@[simp] theorem applyPostings_cons (b : Book) (p : ResourcePosting) (ps : List ResourcePosting) :
    applyPostings b (p :: ps) = applyPostings (b.applyPosting p) ps := rfl

theorem map_congr_mem {α β : Type} (f g : α → β) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem applyPosting_balance_other_asset (b : Book) (p : ResourcePosting) (a : AccountId) (ast : AssetId)
    (hast : ast ≠ p.asset) : (b.applyPosting p).balance a ast = b.balance a ast := by
  unfold Book.balance Book.applyPosting
  dsimp only
  simp [hast]

theorem applyPostings_balance_other_asset (ps : List ResourcePosting) (b : Book) (a : AccountId) (ast : AssetId)
    (haway : ∀ p ∈ ps, ast ≠ p.asset) : (applyPostings b ps).balance a ast = b.balance a ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp : ast ≠ p.asset := haway p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, ast ≠ q.asset := fun q hq => haway q (List.Mem.tail p hq)
    rw [ih (b.applyPosting p) hrest]
    exact applyPosting_balance_other_asset b p a ast hp

theorem payoutPostings_assets_ne (b : Book) (account payee : AccountId) (assets : List AssetId) (ast : AssetId)
    (hnotmem : ast ∉ assets) :
    ∀ p ∈ payoutPostings b account payee assets, ast ≠ p.asset := by
  intro p hp
  simp only [payoutPostings, List.mem_map] at hp
  rcases hp with ⟨a, ha, rfl⟩
  intro heq
  subst heq
  exact hnotmem ha

/-- Applying a single payout transfer zeroes the seat's non-negative balance and increments the payee. -/
theorem payout_single_balance (b : Book) (account payee : AccountId) (ast : AssetId)
    (hdiff : payee ≠ account) (hnonneg : 0 ≤ b.balance account ast) :
    let p : ResourcePosting := ⟨account, payee, ast, (b.balance account ast).toNat⟩
    (b.applyPosting p).balance account ast = 0 ∧
    (b.applyPosting p).balance payee ast = b.balance payee ast + b.balance account ast := by
  unfold Book.applyPosting Book.balance
  dsimp only
  have htoNat : ((b.balances account ast).toNat : Int) = b.balances account ast :=
    Int.toNat_of_nonneg hnonneg
  have h_ne1 : account ≠ payee := Ne.symm hdiff
  have h_ne2 : payee ≠ account := hdiff
  simp [htoNat, h_ne1, h_ne2]

/-- General exact payout theorem across all listed active assets with Nodup. -/
theorem payout_exact (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hdiff : payee ≠ account) (hnodup : assets.Nodup)
    (hnonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast) :
    ∀ ast ∈ assets,
      (applyPostings b (payoutPostings b account payee assets)).balance account ast = 0 ∧
      (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
        b.balance payee ast + b.balance account ast := by
  induction assets generalizing b with
  | nil =>
    intro ast hast
    cases hast
  | cons head rest ih =>
    rw [List.nodup_cons] at hnodup
    intro ast hast
    unfold payoutPostings
    simp only [List.map_cons]
    rw [applyPostings_cons]
    have hhead_nonneg : 0 ≤ b.balance account head := hnonneg head (List.Mem.head rest)
    have hrest_nonneg : ∀ a ∈ rest, 0 ≤ b.balance account a :=
      fun a ha => hnonneg a (List.Mem.tail head ha)
    let b1 := b.applyPosting ⟨account, payee, head, (b.balance account head).toNat⟩
    have hstep := payout_single_balance b account payee head hdiff hhead_nonneg
    have hrest_agree : ∀ a ∈ rest, b1.balance account a = b.balance account a := by
      intro a ha
      have hne : a ≠ head := fun h => hnodup.1 (h ▸ ha)
      exact applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ account a hne
    have hmap_eq : (rest.map fun a => (⟨account, payee, a, (b.balance account a).toNat⟩ : ResourcePosting)) =
        payoutPostings b1 account payee rest := by
      unfold payoutPostings
      apply map_congr_mem
      intro a ha
      rw [hrest_agree a ha]
    rw [hmap_eq]
    have hmem_cases := List.mem_cons.mp hast
    cases hmem_cases with
    | inl heq =>
      subst heq
      have haway : ∀ p ∈ payoutPostings b1 account payee rest, ast ≠ p.asset := by
        apply payoutPostings_assets_ne
        exact hnodup.1
      have hacc_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 account ast haway
      have hpay_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 payee ast haway
      rw [hacc_rest, hpay_rest]
      exact hstep
    | inr hmem =>
      have hnew_nonneg : ∀ a ∈ rest, 0 ≤ b1.balance account a := by
        intro a ha
        rw [hrest_agree a ha]
        exact hrest_nonneg a ha
      have hrec := ih b1 hnodup.2 hnew_nonneg ast hmem
      refine ⟨hrec.1, ?_⟩
      rw [hrec.2]
      have hne : ast ≠ head := fun h => hnodup.1 (h ▸ hmem)
      have hpay_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ payee ast hne
      have hacc_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ account ast hne
      rw [hpay_step, hacc_step]

/-- Unconditional exit payout: moves the seat's whole allocation to payee. -/
theorem exit_pays_allocation (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hdiff : payee ≠ account) (hnodup : assets.Nodup)
    (hnonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast) :
    ∀ ast ∈ assets,
      (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
        b.balance payee ast + b.balance account ast :=
  fun ast hast => (payout_exact b account payee assets hdiff hnodup hnonneg ast hast).2

/-- Unlisted assets are untouched by exit payout postings. -/
theorem payout_unlisted (b : Book) (account payee : AccountId) (assets : List AssetId)
    (ast : AssetId) (hnotmem : ast ∉ assets) (a : AccountId) :
    (applyPostings b (payoutPostings b account payee assets)).balance a ast = b.balance a ast := by
  apply applyPostings_balance_other_asset
  exact payoutPostings_assets_ne b account payee assets ast hnotmem

/-- Complete exit recovery: under `ExitPrecondition`, the seat's balances across ALL
    assets (listed or unlisted) end at exactly zero, and payee receives all holdings. -/
theorem exit_recovery_all (b : Book) (account payee : AccountId) (assets : List AssetId)
    (precond : ExitPrecondition b account payee assets) :
    (∀ ast, (applyPostings b (payoutPostings b account payee assets)).balance account ast = 0) ∧
    (∀ ast ∈ assets, (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
      b.balance payee ast + b.balance account ast) := by
  have hexact := payout_exact b account payee assets precond.h_diff precond.h_nodup precond.h_nonneg
  constructor
  · intro ast
    by_cases hmem : ast ∈ assets
    · exact (hexact ast hmem).1
    · rw [payout_unlisted b account payee assets ast hmem account]
      exact precond.h_zero_outside ast hmem
  · intro ast hast
    exact (hexact ast hast).2

theorem applyPostings_accounts (b : Book) (ps : List ResourcePosting) :
    (applyPostings b ps).accounts = b.accounts := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons, ih]
    rfl

theorem applyPostings_conserves (b : Book) (ps : List ResourcePosting)
    (hps : ∀ p ∈ ps, p.source ∈ b.accounts ∧ p.destination ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyPostings b ps).totalAsset ast = b.totalAsset ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp := hps p (List.Mem.head rest)
    have hcons := b.applyPosting_conserves p hp.1 hp.2 hnodup ast
    have hnodup' : (b.applyPosting p).accounts.Nodup := by
      rw [b.applyPosting_accounts]
      exact hnodup
    have hrest : ∀ q ∈ rest, q.source ∈ (b.applyPosting p).accounts ∧ q.destination ∈ (b.applyPosting p).accounts := by
      intro q hq
      have hq' := hps q (List.Mem.tail p hq)
      rw [b.applyPosting_accounts]
      exact hq'
    have hstep := ih (b.applyPosting p) hrest hnodup'
    rw [hstep]
    exact hcons

/-- Conservation: exit payout preserves total book balances for every asset. -/
theorem payout_conserves (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hacc : account ∈ b.accounts) (hpay : payee ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyPostings b (payoutPostings b account payee assets)).totalAsset ast = b.totalAsset ast := by
  apply applyPostings_conserves
  · intro p hp
    simp only [payoutPostings, List.mem_map] at hp
    rcases hp with ⟨a, _, rfl⟩
    exact ⟨hacc, hpay⟩
  · exact hnodup

/-! ## Multi-Seat Atomic Batch Reallocation (`BatchRealloc`) -/

/-- Multi-seat atomic batch reallocation across participating ZoE seats. -/
structure BatchRealloc where
  postings : List ResourcePosting
  deriving DecidableEq, Repr

/-- Apply a batch reallocation's postings to the ledger book. -/
def applyBatchRealloc (b : Book) (realloc : BatchRealloc) : Book :=
  applyPostings b realloc.postings

/-- Total credits received by `acc` for asset `ast` in `realloc`. -/
def seatCredit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.destination == acc && p.asset == ast).map ResourcePosting.amount).sum

/-- Total debits sent from `acc` for asset `ast` in `realloc`. -/
def seatDebit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.source == acc && p.asset == ast).map ResourcePosting.amount).sum

/-- Sum of credits across all participating seat accounts for asset `ast`. -/
def batchTotalCredits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatCredit realloc acc ast).sum

/-- Sum of debits across all participating seat accounts for asset `ast`. -/
def batchTotalDebits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatDebit realloc acc ast).sum

/-- All assets referenced by participating seat proposals or reallocation postings. -/
def batchAssets (seats : List Seat) (realloc : BatchRealloc) : List AssetId :=
  (seats.flatMap fun s => s.proposal.assets) ++ realloc.postings.map ResourcePosting.asset

/-- Executable safety & conservation checker for a multi-seat ZoE batch reallocation:
    1. Participating `Seat` accounts are pairwise distinct (`seatAccounts.Nodup`).
    2. Every posting moves value exclusively between participating protected `Seat` accounts (`≥ protectedBase`).
    3. For every asset `ast ∈ batchAssets seats realloc`, total credits across participating seats equal total debits.
    4. After reallocation (`b' := applyBatchRealloc b realloc`), every participating seat `s ∈ seats`
       satisfies ZoE Offer Safety (`safeAt b' s.account s.proposal = true`) and non-negative balances. -/
def checkBatchReallocSafe (b : Book) (seats : List Seat) (realloc : BatchRealloc) : Bool :=
  let seatAccounts := seats.map Seat.account
  let nodupSeats := decide seatAccounts.Nodup
  let endpointsInSeats := realloc.postings.all fun p =>
    decide (p.source ∈ seatAccounts) &&
    decide (p.destination ∈ seatAccounts) &&
    decide (protectedBase ≤ p.source) &&
    decide (protectedBase ≤ p.destination)
  let assets := batchAssets seats realloc
  let zeroSumConserved := assets.all fun ast =>
    batchTotalCredits seats realloc ast == batchTotalDebits seats realloc ast
  let b' := applyBatchRealloc b realloc
  let allSeatsOfferSafe := seats.all fun s =>
    safeAt b' s.account s.proposal &&
    assets.all fun ast => decide (0 ≤ b'.balance s.account ast)
  nodupSeats && endpointsInSeats && zeroSumConserved && allSeatsOfferSafe

/-- If `checkBatchReallocSafe b seats realloc = true`, participating seat accounts are pairwise distinct. -/
theorem batchRealloc_nodup_seats (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    (seats.map Seat.account).Nodup := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_safe
  exact h_safe.1.1.1

/-- If `checkBatchReallocSafe b seats realloc = true`, then every participating seat `s ∈ seats`
    satisfies ZoE Offer Safety (`safeAt (applyBatchRealloc b realloc) s.account s.proposal = true`). -/
theorem batchRealloc_preserves_all_seats_offer_safe (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    ∀ s ∈ seats, safeAt (applyBatchRealloc b realloc) s.account s.proposal = true := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true] at h_safe
  intro s hs
  exact (h_safe.2 s hs).1

/-- If `checkBatchReallocSafe b seats realloc = true`, then for every asset in `batchAssets seats realloc`,
    the sum of credits across participating seats equals the sum of debits. -/
theorem batchRealloc_zero_sum_conservation (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    ∀ ast ∈ batchAssets seats realloc,
      batchTotalCredits seats realloc ast = batchTotalDebits seats realloc ast := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h_safe
  intro ast hast
  exact h_safe.1.2 ast hast

theorem filter_asset_nil_of_forall_ne (ps : List ResourcePosting) (pred : AccountId → ResourcePosting → Bool)
    (acc : AccountId) (ast : AssetId) (hne : ∀ p ∈ ps, p.asset ≠ ast) :
    ps.filter (fun p => pred acc p && (p.asset == ast)) = [] := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    have hp : (p.asset == ast) = false := beq_eq_false_iff_ne.mpr (hne p (List.Mem.head rest))
    simp [hp, ih (fun q hq => hne q (List.Mem.tail p hq))]

theorem seatCredit_eq_zero_of_forall_ne (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId)
    (hne : ∀ p ∈ realloc.postings, p.asset ≠ ast) :
    seatCredit realloc acc ast = 0 := by
  unfold seatCredit
  rw [filter_asset_nil_of_forall_ne realloc.postings (fun a p => p.destination == a) acc ast hne]
  rfl

theorem seatDebit_eq_zero_of_forall_ne (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId)
    (hne : ∀ p ∈ realloc.postings, p.asset ≠ ast) :
    seatDebit realloc acc ast = 0 := by
  unfold seatDebit
  rw [filter_asset_nil_of_forall_ne realloc.postings (fun a p => p.source == a) acc ast hne]
  rfl

/-- Unconditional asset-wise zero-sum conservation: if `checkBatchReallocSafe b seats realloc = true`,
    then for **every** asset `ast : AssetId` (whether referenced in `batchAssets` or not),
    `batchTotalCredits seats realloc ast = batchTotalDebits seats realloc ast`. -/
theorem batchRealloc_zero_sum_all_assets (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) (ast : AssetId) :
    batchTotalCredits seats realloc ast = batchTotalDebits seats realloc ast := by
  by_cases hmem : ast ∈ batchAssets seats realloc
  · exact batchRealloc_zero_sum_conservation b seats realloc h_safe ast hmem
  · have hne : ∀ p ∈ realloc.postings, p.asset ≠ ast := by
      intro p hp heq
      apply hmem
      unfold batchAssets
      rw [List.mem_append]
      right
      rw [← heq]
      exact List.mem_map_of_mem hp
    unfold batchTotalCredits batchTotalDebits
    have hmap : ((seats.map Seat.account).map fun acc => seatCredit realloc acc ast) =
        ((seats.map Seat.account).map fun acc => seatDebit realloc acc ast) := by
      apply map_congr_mem
      intro acc _
      rw [seatCredit_eq_zero_of_forall_ne realloc acc ast hne,
          seatDebit_eq_zero_of_forall_ne realloc acc ast hne]
    rw [hmap]

theorem applyPosting_balance_other_account (b : Book) (p : ResourcePosting) (a : AccountId) (ast : AssetId)
    (hsrc : a ≠ p.source) (hdst : a ≠ p.destination) :
    (b.applyPosting p).balance a ast = b.balance a ast := by
  unfold Book.balance Book.applyPosting
  dsimp only
  simp [hsrc, hdst]

theorem applyPostings_balance_other_account (ps : List ResourcePosting) (b : Book) (a : AccountId) (ast : AssetId)
    (haway : ∀ p ∈ ps, a ≠ p.source ∧ a ≠ p.destination) :
    (applyPostings b ps).balance a ast = b.balance a ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih =>
    rw [applyPostings_cons]
    have hp := haway p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, a ≠ q.source ∧ a ≠ q.destination :=
      fun q hq => haway q (List.Mem.tail p hq)
    rw [ih (b.applyPosting p) hrest]
    exact applyPosting_balance_other_account b p a ast hp.1 hp.2

/-- Any batch reallocation whose postings touch only protected accounts (`≥ protectedBase`)
    leaves every ordinary account (`< protectedBase`) strictly invariant. -/
theorem applyBatchRealloc_balance_ordinary_of_protected (b : Book) (realloc : BatchRealloc)
    (h_prot : ∀ p ∈ realloc.postings, protectedBase ≤ p.source ∧ protectedBase ≤ p.destination)
    (ordinary : AccountId) (h_ord : ordinary < protectedBase) (ast : AssetId) :
    (applyBatchRealloc b realloc).balance ordinary ast = b.balance ordinary ast := by
  unfold applyBatchRealloc
  apply applyPostings_balance_other_account
  intro p hp
  obtain ⟨hsrc, hdst⟩ := h_prot p hp
  exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hsrc), Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hdst)⟩

/-- Reallocating among protected `Seat` accounts under `checkBatchReallocSafe` leaves the balance
    of every ordinary account (`< protectedBase`) strictly invariant across all assets. -/
theorem batchRealloc_disjoint_from_ordinary_accounts (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true)
    (ordinary : AccountId) (h_ord : ordinary < protectedBase) (ast : AssetId) :
    (applyBatchRealloc b realloc).balance ordinary ast = b.balance ordinary ast := by
  apply applyBatchRealloc_balance_ordinary_of_protected b realloc _ ordinary h_ord ast
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h_safe
  intro p hp
  have hp' := h_safe.1.1.2 p hp
  exact ⟨hp'.1.2, hp'.2⟩

/-- Total book asset conservation for `applyBatchRealloc` when participating seats are registered in `b`. -/
theorem batchRealloc_conserves (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true)
    (h_reg : ∀ s ∈ seats, s.account ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyBatchRealloc b realloc).totalAsset ast = b.totalAsset ast := by
  unfold applyBatchRealloc
  apply applyPostings_conserves _ _ _ hnodup ast
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h_safe
  intro p hp
  have hp' := h_safe.1.1.2 p hp
  rcases List.mem_map.mp hp'.1.1.1 with ⟨s1, hs1, hacc1⟩
  rcases List.mem_map.mp hp'.1.1.2 with ⟨s2, hs2, hacc2⟩
  exact ⟨hacc1 ▸ h_reg s1 hs1, hacc2 ▸ h_reg s2 hs2⟩

end Obend.Ledger
