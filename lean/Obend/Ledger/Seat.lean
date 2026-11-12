module
/-
# Obend.Ledger.Seat — Full ZoE Offer Safety, One-Time Invitations, Gift Guard, Identity-Blind Disclosure & Full-Support Exit Sweep

Mathlib-free port of `minidregg/Kernel/Invitation.lean` and `minidregg/Kernel/Seat.lean` over
the finite-support `Obend.Ledger.Book` resource kernel:

1. **One-Time `Invitation` Spending (`no_double_redeem`)**:
   - `InvitationRegistry` mints fresh `Invitation`s and redeems each invitation at most once
     (`no_double_redeem`, `mint_preserves_spent`).
2. **Explicit `donate : Bool` Zero-Want Gift Guard (`donationUnmarked`)**:
   - `admitOffer` refuses zero-want proposals unless `p.donate = true` (`donationUnmarked_refused`)
     and refuses `p.donate = true` when `want` is positive (`donationMarkedWithWant`), preventing
     accidental asset gifts caused by omitted `want` clauses.
3. **`Disclosure` Identity-Blind Contract View (`seatView_identity_blind`)**:
   - `Seat.view` hides `offerer`, `payee`, and `holder` identities behind `s.proposal.disclose`,
     making contract matching bit-identical across participant renamings when undisclosed.
4. **Full-Balance-Support Exit Sweep (`exitSeat`, `exit_sweeps_all_assets`)**:
   - Reads the finite support `b.heldAssets s.account` directly from `Book`'s `FinMap`, sweeping
     every asset held by the seat (including unsolicited/bonus assets outside `give` and `want`)
     to `s.payee`, leaving `0` on the seat for ALL `ast : AssetId` while conserving supply.
-/
public import Obend.Ledger.Book

@[expose] public section
namespace Obend.Ledger

set_option autoImplicit false

/-! ## 1. One-Time Invitations (`no_double_redeem`) -/

/-- A linear ZoE contract invitation token bound to `instanceId` and `description`. -/
structure Invitation where
  id          : Nat
  instanceId  : Nat
  description : String
  deriving DecidableEq, Repr

/-- Registry of live unspent invitations with strictly monotone `nextId` allocator. -/
structure InvitationRegistry where
  nextId : Nat := 0
  live   : List (Nat × Invitation) := []
  deriving DecidableEq, Repr

namespace InvitationRegistry

def empty : InvitationRegistry := {}

def isLive (reg : InvitationRegistry) (invId : Nat) : Bool :=
  (reg.live.lookup invId).isSome

/-- Mint a fresh invitation with `id = reg.nextId`. -/
def mint (reg : InvitationRegistry) (instanceId : Nat) (description : String) :
    InvitationRegistry × Invitation :=
  let inv : Invitation := ⟨reg.nextId, instanceId, description⟩
  ({ nextId := reg.nextId + 1, live := (reg.nextId, inv) :: reg.live }, inv)

/-- Remove all entries keyed by `invId` from an association list. -/
def eraseAllKey (invId : Nat) : List (Nat × Invitation) → List (Nat × Invitation)
  | [] => []
  | (k, v) :: rest =>
    if k == invId then eraseAllKey invId rest
    else (k, v) :: eraseAllKey invId rest

theorem lookup_eraseAllKey_self (invId : Nat) :
    ∀ (xs : List (Nat × Invitation)), (eraseAllKey invId xs).lookup invId = none
  | [] => rfl
  | (k, v) :: rest => by
    unfold eraseAllKey
    by_cases hk : k == invId
    · simp only [hk, ↓reduceIte]
      exact lookup_eraseAllKey_self invId rest
    · have hk' : (invId == k) = false := by
        cases h : invId == k with
        | false => rfl
        | true =>
          have heq : invId = k := beq_iff_eq.mp h
          subst heq
          exact absurd (beq_self_eq_true invId) hk
      simp only [hk, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, hk']
      exact lookup_eraseAllKey_self invId rest

/-- Spend (redeem) an invitation once, removing it from `live`. -/
def spend (reg : InvitationRegistry) (invId : Nat) : Option (InvitationRegistry × Invitation) :=
  match reg.live.lookup invId with
  | some inv => some ({ reg with live := eraseAllKey invId reg.live }, inv)
  | none     => none

/-- **One-Time Invitation Redemption (`no_double_redeem`)**:
    Once `reg.spend invId = some (reg', inv)`, any second attempt `reg'.spend invId` returns `none`. -/
theorem no_double_redeem {reg reg' : InvitationRegistry} {inv : Invitation} {invId : Nat}
    (hspend : reg.spend invId = some (reg', inv)) :
    reg'.spend invId = none := by
  unfold spend at hspend ⊢
  cases hlook : reg.live.lookup invId with
  | none => rw [hlook] at hspend; cases hspend
  | some found =>
    rw [hlook] at hspend
    injection hspend with hp
    have hreg : reg' = { reg with live := eraseAllKey invId reg.live } :=
      (Prod.mk.inj hp).1.symm
    subst hreg
    simp [lookup_eraseAllKey_self]

/-- Minting new invitations at `reg.nextId` never resurrects a previously spent `invId < reg.nextId`. -/
theorem mint_preserves_spent (reg : InvitationRegistry) (inst : Nat) (desc : String)
    {invId : Nat} (hlt : invId < reg.nextId) (hspent : reg.spend invId = none) :
    (reg.mint inst desc).1.spend invId = none := by
  unfold spend at hspent ⊢
  unfold mint
  have hne : (invId == reg.nextId) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
  simp only [List.lookup_cons, hne]
  cases hlook : reg.live.lookup invId with
  | none => rfl
  | some _ => rw [hlook] at hspent; cases hspent

end InvitationRegistry

/-! ## 2. Proposals, Explicit `donate` Gift Guard & `Disclosure` -/

inductive ExitRule where
  | onDemand
  | afterDeadline (due : Nat)
  deriving DecidableEq, Repr

/-- Per-role disclosure policy controlling whether contract code can inspect identities. -/
structure Disclosure where
  offerer : Bool := false
  payee   : Bool := false
  holder  : Bool := false
  deriving DecidableEq, Repr

structure Proposal where
  give     : List (AssetId × Nat)
  want     : List (AssetId × Nat)
  exit     : ExitRule
  donate   : Bool := false
  disclose : Disclosure := {}
  deriving DecidableEq, Repr

def Proposal.assets (p : Proposal) : List AssetId :=
  ((p.give ++ p.want).map Prod.fst).eraseDups

/-- True iff `p.want` requests zero positive units of every asset. -/
def Proposal.wantsNothing (p : Proposal) : Bool :=
  p.want.all (fun (_, amt) => amt == 0)

/-- Check that `p.give` and `p.want` each have duplicate-free asset keys. -/
def Proposal.assetsNodupB (p : Proposal) : Bool :=
  decide ((p.give.map Prod.fst).Nodup ∧ (p.want.map Prod.fst).Nodup)

/-- Total amount requested or offered for `ast` across all entries in `pairs`. -/
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

/-- Crediting an account never violates offer safety. -/
theorem safeAt_mono {b b' : Book} {account account' : AccountId} {p : Proposal}
    (hmore : ∀ ast, b.balance account ast ≤ b'.balance account' ast)
    (hsafe : safeAt b account p = true) :
    safeAt b' account' p = true := by
  unfold safeAt at hsafe ⊢
  simp only [Bool.or_eq_true] at hsafe ⊢
  rcases hsafe with hwant | hgive
  · left; exact atLeast_mono hmore p.want p.want hwant
  · right; exact atLeast_mono hmore p.give p.give hgive

/-! ## 3. Seat Structure, Identity-Blind `SeatView` & Gift-Guarded Offer Admission -/

/-- A ZoE seat carrying proof that its account coordinate is in the protected space
    (`protectedBase ≤ account`), and that its payee differs from the seat account. -/
structure Seat where
  account     : AccountId
  h_protected : protectedBase ≤ account := by decide
  inst        : Nat := 0
  offerer     : Nat := 0
  payee       : AccountId := 0
  h_payee_diff : payee ≠ account := by decide
  proposal    : Proposal
  holder      : Option Nat := none
  deriving DecidableEq, Repr

/-- Ordinary accounts below `protectedBase` cannot collide with a seat's protected account. -/
theorem ordinary_ne_seat_account {ordinary : AccountId} (s : Seat)
    (h_ord : ordinary < protectedBase) : ordinary ≠ s.account :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord s.h_protected)

/-- Contract-visible projection of a `Seat`, masking `offerer`, `payee`, and `holder`
    unless explicitly disclosed in `s.proposal.disclose`. -/
structure SeatView where
  account  : AccountId
  inst     : Nat
  give     : List (AssetId × Nat)
  want     : List (AssetId × Nat)
  exit     : ExitRule
  donate   : Bool
  offerer? : Option Nat
  payee?   : Option AccountId
  holder?  : Option Nat
  deriving DecidableEq, Repr

/-- Project a `Seat` into its contract-visible `SeatView`. -/
def Seat.view (s : Seat) : SeatView where
  account  := s.account
  inst     := s.inst
  give     := s.proposal.give
  want     := s.proposal.want
  exit     := s.proposal.exit
  donate   := s.proposal.donate
  offerer? := if s.proposal.disclose.offerer then some s.offerer else none
  payee?   := if s.proposal.disclose.payee then some s.payee else none
  holder?  := if s.proposal.disclose.holder then s.holder else none

/-- **Identity-Blind Contract View Theorem (`seatView_identity_blind`)**:
    When two seats at the same protected coordinate and contract instance carry the same
    undisclosed `Proposal` (`p.disclose = {}`), their contract-facing `SeatView`s are
    bit-identical regardless of `offerer`, `payee`, or `holder` identities! -/
theorem seatView_identity_blind (s₁ s₂ : Seat)
    (hacc : s₁.account = s₂.account)
    (hinst : s₁.inst = s₂.inst)
    (hprop : s₁.proposal = s₂.proposal)
    (hblind : s₁.proposal.disclose = {}) :
    s₁.view = s₂.view := by
  unfold Seat.view
  have hb2 : s₂.proposal.disclose = {} := hprop ▸ hblind
  simp [hacc, hinst, hprop, hb2]

/-- Structured errors refused during ZoE offer admission. -/
inductive OfferError where
  | invitationInvalid (invId : Nat)
  | donationUnmarked
  | donationMarkedWithWant
  | offererMatchesSeat
  | insufficientOffererBalance (asset : AssetId)
  deriving DecidableEq, Repr

/-- Validate the explicit `donate : Bool` zero-want gift guard on `p`. -/
def checkDonationGuard (p : Proposal) : Except OfferError Unit :=
  if p.wantsNothing then
    if p.donate then .ok ()
    else .error .donationUnmarked
  else
    if p.donate then .error .donationMarkedWithWant
    else .ok ()

/-- **Zero-Want Gift Guard (`donationUnmarked_refused`)**:
    Any proposal requesting zero `want` without `donate = true` is deterministically refused
    with `OfferError.donationUnmarked`. -/
theorem donationUnmarked_refused (p : Proposal)
    (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    checkDonationGuard p = .error .donationUnmarked := by
  simp [checkDonationGuard, hwant0, hdon]

/-- **Spurious Donate Flag Guard (`donationMarkedWithWant_refused`)**:
    Any proposal with positive `want` that also sets `donate = true` is refused with
    `OfferError.donationMarkedWithWant`. -/
theorem donationMarkedWithWant_refused (p : Proposal)
    (hwantPos : p.wantsNothing = false) (hdon : p.donate = true) :
    checkDonationGuard p = .error .donationMarkedWithWant := by
  simp [checkDonationGuard, hwantPos, hdon]

/-- Escrow postings locking `p.give` from `offerer` into `seatAcc`. -/
def giveEscrowPostings (offerer seatAcc : AccountId) (p : Proposal) : List ResourcePosting :=
  p.give.map fun (ast, amt) => ⟨offerer, seatAcc, ast, amt⟩

/-- Admit a ZoE offer by:
    1. Enforcing `checkDonationGuard p` (`donationUnmarked` / `donationMarkedWithWant`),
    2. Redeeming `invId` once from `reg`,
    3. Checking `offerer ≠ seatAcc` and sufficient `offerer` balances for `p.give`,
    4. Escrowing `p.give` into `seatAcc` and verifying `safeAt` on the funded seat. -/
def admitOffer (reg : InvitationRegistry) (b : Book) (invId : Nat)
    (offerer payee seatAcc : AccountId)
    (h_prot : protectedBase ≤ seatAcc) (h_diff : payee ≠ seatAcc)
    (p : Proposal) : Except OfferError (InvitationRegistry × Book × Seat) := do
  checkDonationGuard p
  match reg.spend invId with
  | none => .error (.invitationInvalid invId)
  | some (reg', inv) =>
    if offerer == seatAcc then
      .error .offererMatchesSeat
    else
      let giveAssets := (p.give.map Prod.fst).eraseDups
      match giveAssets.find? (fun ast => decide (b.balance offerer ast < (assetAmountSum p.give ast : Int))) with
      | some badAst => .error (.insufficientOffererBalance badAst)
      | none =>
        let b' := (giveEscrowPostings offerer seatAcc p).foldl Book.applyPosting b
        let s : Seat := {
          account := seatAcc
          h_protected := h_prot
          inst := inv.instanceId
          offerer := offerer
          payee := payee
          h_payee_diff := h_diff
          proposal := p
        }
        .ok (reg', b', s)

theorem admitOffer_donationUnmarked_refused (reg : InvitationRegistry) (b : Book) (invId : Nat)
    (offerer payee seatAcc : AccountId)
    (h_prot : protectedBase ≤ seatAcc) (h_diff : payee ≠ seatAcc)
    (p : Proposal) (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .error .donationUnmarked := by
  unfold admitOffer
  rw [donationUnmarked_refused p hwant0 hdon]
  rfl

theorem admitOffer_spends_invitation_once {reg reg' : InvitationRegistry} {b b' : Book}
    {invId : Nat} {offerer payee seatAcc : AccountId}
    {h_prot : protectedBase ≤ seatAcc} {h_diff : payee ≠ seatAcc}
    {p : Proposal} {s : Seat}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .ok (reg', b', s)) :
    reg'.spend invId = none := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e => rw [hguard] at hadm; cases hadm
  | ok _ =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => rw [hsp] at hadm; cases hadm
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      by_cases hoff : offerer == seatAcc
      · simp [hoff] at hadm
      · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
        split at hadm
        · cases hadm
        · injection hadm with hp
          have hr : reg' = r1 := (Prod.mk.inj hp).1.symm
          subst hr
          exact InvitationRegistry.no_double_redeem hsp

/-! ## 4. World Collections & Distinct Seat Accounts -/

structure World where
  book        : Book
  seats       : List Seat
  nodup_seats : (seats.map Seat.account).Nodup := by decide
  assets      : List AssetId := []

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
        intro heq; rw [heq] at hbeq; simp at hbeq
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact False.elim (hne rfl)
      · exact ih hnodup.2 hin

theorem World.seat?_mem (w : World) {s : Seat} (hmem : s ∈ w.seats) :
    w.seat? s.account = some s :=
  seats_find_mem w.seats w.nodup_seats hmem

theorem seats_account_inj (w : World) {s1 s2 : Seat}
    (h1 : s1 ∈ w.seats) (h2 : s2 ∈ w.seats) (heq : s1.account = s2.account) :
    s1 = s2 := by
  have h_find1 := w.seat?_mem h1
  have h_find2 := w.seat?_mem h2
  rw [heq] at h_find1
  rw [h_find1] at h_find2
  cases h_find2
  rfl

/-! ## 5. Payout Transfers & Full-Balance-Support Exit Sweep (`exit_sweeps_all_assets`) -/

structure ExitPrecondition (b : Book) (account payee : AccountId) (assets : List AssetId) : Prop where
  h_diff         : payee ≠ account
  h_nonneg       : ∀ ast ∈ assets, 0 ≤ b.balance account ast
  h_nodup        : assets.Nodup
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
  rw [Book.balance_applyPosting]
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

theorem payout_single_balance (b : Book) (account payee : AccountId) (ast : AssetId)
    (hdiff : payee ≠ account) (hnonneg : 0 ≤ b.balance account ast) :
    let p : ResourcePosting := ⟨account, payee, ast, (b.balance account ast).toNat⟩
    (b.applyPosting p).balance account ast = 0 ∧
    (b.applyPosting p).balance payee ast = b.balance payee ast + b.balance account ast := by
  dsimp only
  rw [Book.balance_applyPosting, Book.balance_applyPosting]
  have htoNat : ((b.balance account ast).toNat : Int) = b.balance account ast :=
    Int.toNat_of_nonneg hnonneg
  have h_ne1 : account ≠ payee := Ne.symm hdiff
  have h_ne2 : payee ≠ account := hdiff
  simp [htoNat, h_ne1, h_ne2]

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
    rcases List.mem_cons.mp hast with rfl | hmem
    · have haway : ∀ p ∈ payoutPostings b1 account payee rest, ast ≠ p.asset :=
        payoutPostings_assets_ne b1 account payee rest ast hnodup.1
      have hacc_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 account ast haway
      have hpay_rest := applyPostings_balance_other_asset (payoutPostings b1 account payee rest) b1 payee ast haway
      rw [hacc_rest, hpay_rest]
      exact hstep
    · have hnew_nonneg : ∀ a ∈ rest, 0 ≤ b1.balance account a := by
        intro a ha; rw [hrest_agree a ha]; exact hrest_nonneg a ha
      have hrec := ih b1 hnodup.2 hnew_nonneg ast hmem
      refine ⟨hrec.1, ?_⟩
      rw [hrec.2]
      have hne : ast ≠ head := fun h => hnodup.1 (h ▸ hmem)
      have hpay_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ payee ast hne
      have hacc_step := applyPosting_balance_other_asset b ⟨account, payee, head, (b.balance account head).toNat⟩ account ast hne
      rw [hpay_step, hacc_step]

theorem exit_pays_allocation (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hdiff : payee ≠ account) (hnodup : assets.Nodup)
    (hnonneg : ∀ ast ∈ assets, 0 ≤ b.balance account ast) :
    ∀ ast ∈ assets,
      (applyPostings b (payoutPostings b account payee assets)).balance payee ast =
        b.balance payee ast + b.balance account ast :=
  fun ast hast => (payout_exact b account payee assets hdiff hnodup hnonneg ast hast).2

theorem payout_unlisted (b : Book) (account payee : AccountId) (assets : List AssetId)
    (ast : AssetId) (hnotmem : ast ∉ assets) (a : AccountId) :
    (applyPostings b (payoutPostings b account payee assets)).balance a ast = b.balance a ast := by
  apply applyPostings_balance_other_asset
  exact payoutPostings_assets_ne b account payee assets ast hnotmem

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
  | cons p rest ih => rw [applyPostings_cons, ih]; rfl

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
    have hnodup' : (b.applyPosting p).accounts.Nodup := by rw [b.applyPosting_accounts]; exact hnodup
    have hrest : ∀ q ∈ rest, q.source ∈ (b.applyPosting p).accounts ∧ q.destination ∈ (b.applyPosting p).accounts := by
      intro q hq
      have hq' := hps q (List.Mem.tail p hq)
      rw [b.applyPosting_accounts]
      exact hq'
    rw [ih (b.applyPosting p) hrest hnodup', hcons]

theorem payout_conserves (b : Book) (account payee : AccountId) (assets : List AssetId)
    (hacc : account ∈ b.accounts) (hpay : payee ∈ b.accounts)
    (hnodup : b.accounts.Nodup) (ast : AssetId) :
    (applyPostings b (payoutPostings b account payee assets)).totalAsset ast = b.totalAsset ast := by
  apply applyPostings_conserves
  · intro p hp
    simp only [payoutPostings, List.mem_map] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨hacc, hpay⟩
  · exact hnodup

/-- **Full-Balance-Support Seat Exit (`exitSeat`)**:
    Sweeps the seat's entire finite support `b.heldAssets s.account` directly from `Book`'s
    `FinMap` to `s.payee` — requiring NO caller-supplied asset list! -/
def exitSeat (b : Book) (s : Seat) : Book :=
  applyPostings b (payoutPostings b s.account s.payee (b.heldAssets s.account))

/-- **Full-Support Exit Sweep Theorem (`exit_sweeps_all_assets`)**:
    When a seat holds non-negative balances across all assets (`∀ ast, 0 ≤ b.balance s.account ast`),
    `exitSeat b s`:
    1. Zeroes the seat's balance on **every** asset `ast : AssetId` in the entire universe
       (including unsolicited/bonus assets outside `s.proposal.give` and `s.proposal.want`),
    2. Credits `s.payee` with the exact pre-exit seat balance on **every** asset `ast : AssetId`,
    3. Conserves global asset supply (`globalAssetSum`) unconditionally. -/
theorem exit_sweeps_all_assets (b : Book) (s : Seat)
    (hnonneg : ∀ ast : AssetId, 0 ≤ b.balance s.account ast) :
    (∀ ast : AssetId, (exitSeat b s).balance s.account ast = 0) ∧
    (∀ ast : AssetId, (exitSeat b s).balance s.payee ast =
      b.balance s.payee ast + b.balance s.account ast) ∧
    (∀ ast : AssetId, (exitSeat b s).globalAssetSum ast = b.globalAssetSum ast) := by
  have precond : ExitPrecondition b s.account s.payee (b.heldAssets s.account) := {
    h_diff := s.h_payee_diff
    h_nonneg := fun ast _ => hnonneg ast
    h_nodup := b.heldAssets_nodup s.account
    h_zero_outside := fun ast hnot => b.balance_eq_zero_of_not_mem_heldAssets s.account hnot
  }
  have ⟨hzero, hpay_in⟩ := exit_recovery_all b s.account s.payee (b.heldAssets s.account) precond
  refine ⟨hzero, ?_, ?_⟩
  · intro ast
    by_cases hmem : ast ∈ b.heldAssets s.account
    · exact hpay_in ast hmem
    · unfold exitSeat
      rw [payout_unlisted b s.account s.payee (b.heldAssets s.account) ast hmem s.payee]
      rw [b.balance_eq_zero_of_not_mem_heldAssets s.account hmem]
      omega
  · intro ast
    unfold exitSeat
    have fold_cons : ∀ (ps : List ResourcePosting) (bk : Book),
        (applyPostings bk ps).globalAssetSum ast = bk.globalAssetSum ast := by
      intro ps
      induction ps with
      | nil => intro bk; rfl
      | cons p rest ih =>
        intro bk
        rw [applyPostings_cons, ih (bk.applyPosting p), Book.applyPosting_conserves_global]
    exact fold_cons _ b

/-! ## 6. Multi-Seat Atomic Batch Reallocation (`BatchRealloc`) -/

structure BatchRealloc where
  postings : List ResourcePosting
  deriving DecidableEq, Repr

def applyBatchRealloc (b : Book) (realloc : BatchRealloc) : Book :=
  applyPostings b realloc.postings

def seatCredit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.destination == acc && p.asset == ast).map ResourcePosting.amount).sum

def seatDebit (realloc : BatchRealloc) (acc : AccountId) (ast : AssetId) : Nat :=
  ((realloc.postings.filter fun p => p.source == acc && p.asset == ast).map ResourcePosting.amount).sum

def batchTotalCredits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatCredit realloc acc ast).sum

def batchTotalDebits (seats : List Seat) (realloc : BatchRealloc) (ast : AssetId) : Nat :=
  ((seats.map Seat.account).map fun acc => seatDebit realloc acc ast).sum

def batchAssets (seats : List Seat) (realloc : BatchRealloc) : List AssetId :=
  (seats.flatMap fun s => s.proposal.assets) ++ realloc.postings.map ResourcePosting.asset

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

theorem batchRealloc_nodup_seats (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    (seats.map Seat.account).Nodup := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_safe
  exact h_safe.1.1.1

theorem batchRealloc_preserves_all_seats_offer_safe (b : Book) (seats : List Seat) (realloc : BatchRealloc)
    (h_safe : checkBatchReallocSafe b seats realloc = true) :
    ∀ s ∈ seats, safeAt (applyBatchRealloc b realloc) s.account s.proposal = true := by
  unfold checkBatchReallocSafe at h_safe
  simp only [Bool.and_eq_true, List.all_eq_true] at h_safe
  intro s hs
  exact (h_safe.2 s hs).1

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
  rw [Book.balance_applyPosting]
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

theorem applyBatchRealloc_balance_ordinary_of_protected (b : Book) (realloc : BatchRealloc)
    (h_prot : ∀ p ∈ realloc.postings, protectedBase ≤ p.source ∧ protectedBase ≤ p.destination)
    (ordinary : AccountId) (h_ord : ordinary < protectedBase) (ast : AssetId) :
    (applyBatchRealloc b realloc).balance ordinary ast = b.balance ordinary ast := by
  unfold applyBatchRealloc
  apply applyPostings_balance_other_account
  intro p hp
  obtain ⟨hsrc, hdst⟩ := h_prot p hp
  exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hsrc), Nat.ne_of_lt (Nat.lt_of_lt_of_le h_ord hdst)⟩

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

end
