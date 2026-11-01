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

/-- Offer safety: either every `want` is met, or every `give` is refunded. -/
def safeAt (b : Book) (account : AccountId) (p : Proposal) : Bool :=
  let wantMet := p.want.all fun (ast, amt) => (amt : Int) ≤ b.balance account ast
  let giveRefunded := p.give.all fun (ast, amt) => (amt : Int) ≤ b.balance account ast
  wantMet || giveRefunded

theorem atLeast_mono {b b' : Book} {account account' : AccountId}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (pairs : List (AssetId × Nat))
    (hall : pairs.all (fun (ast, amt) => (amt : Int) ≤ b.balance account ast) = true) :
    pairs.all (fun (ast, amt) => (amt : Int) ≤ b'.balance account' ast) = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall ⊢
    refine ⟨Int.le_trans hall.1 (hmore pair.1), ih hall.2⟩

/-- The law is monotone: crediting an account never violates offer safety. -/
theorem safeAt_mono {b b' : Book} {account account' : AccountId} {p : Proposal}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (hsafe : safeAt b account p = true) :
    safeAt b' account' p = true := by
  unfold safeAt at hsafe ⊢
  simp only [Bool.or_eq_true] at hsafe ⊢
  rcases hsafe with hwant | hgive
  · left; exact atLeast_mono hmore p.want hwant
  · right; exact atLeast_mono hmore p.give hgive

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

end Obend.Ledger
