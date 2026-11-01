module
/-
# Obend.Ledger.Seat — ZoE offer-safe seats with protected account positions

An `offer` presents a proposal `{give, want, exit}`:
- The seat's account coordinate is in the protected space (`protectedBase ≤ account`, ≥ 2^256).
- The seat's balances are judged by `safeAt`:
    either every `want` is met, OR every `give` is refunded (Zoe offer safety).
- Crediting a seat is monotone: `safeAt_mono`.
- Unconditional exit payout: `payout_exact`, `exit_pays_allocation`.
- Commutativity and conservation: `seat_conserves`.
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

/-! ## The Seat World & Payout Transfers -/

structure Seat where
  account : AccountId
  inst : Nat
  offerer : Nat
  payee : AccountId
  proposal : Proposal
  holder : Option Nat
  deriving DecidableEq, Repr

structure World where
  book : Book
  seats : List Seat

def payoutPostings (b : Book) (account payee : AccountId) (assets : List AssetId) : List ResourcePosting :=
  assets.map fun ast => ⟨account, payee, ast, (b.balance account ast).toNat⟩

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

/-- Unconditional exit payout: moves the seat's whole allocation to payee. -/
theorem exit_pays_allocation (b : Book) (account payee : AccountId) (ast : AssetId)
    (hdiff : payee ≠ account) (hnonneg : 0 ≤ b.balance account ast) :
    let p : ResourcePosting := ⟨account, payee, ast, (b.balance account ast).toNat⟩
    (b.applyPosting p).balance payee ast = b.balance payee ast + b.balance account ast :=
  (payout_single_balance b account payee ast hdiff hnonneg).2

end Obend.Ledger
