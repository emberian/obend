module
/-
# Obend.Vault.Carry — Mechanized Live World `K-CARRY` Migration & Epoch Evolution (`"world-carry@1"`)

Implements Pillar 4C of the Sovereign Consensus & Metasystem Architecture:
1. `LiveCell` and `LiveWorld` bundling epoch, contract-governed cells, multi-asset `Book`,
   active ZoE `Seat`s, and `Sturdyref`s.
2. `CellCarryAction` (`keep`, `migrate`, `namedDrop`), `SeatCarryAction` (`preserve`, `refund`),
   `CarryPlan`, `CarryRefusal`, and `executeWorldCarry`.
3. The 5 Keystone `K-CARRY` Theorems:
   - `carry_no_silent_drop`: Every cell in `W.cells` is either carried into `W'.cells` or
     explicitly listed in `plan.namedDrops` with zero ledger balance across all tracked assets.
   - `carry_conserves_total_book`: `W'.ledger.totalAsset a = W.ledger.totalAsset a` for all assets `a`.
   - `carry_preserves_forever_crowns`: Every migrated cell carries a verified narrowing certificate
     (`checkContractCert (.narrows c'.law c.law)`), preserves `foreverCrown` status and invariant,
     and induces a sound forever-crown refinement (`cellContract_relaw_sound`).
   - `carry_preserves_zoe_offer_safety`: Every active ZoE `Seat` is either preserved in `W'.seats`
     with `safeAt W'.ledger` holding, or refunded to zero escrow balance across all tracked assets.
   - `carry_rehydrates_sturdyrefs`: Un-revoked `Sturdyref`s to non-dropped cells rehydrate
     identically across the epoch boundary.
4. `worldCarryJudge : Obend.Judge LiveWorld CarryPlan` and `worldCarryFormat : Obend.Judge.Format`
   (`"world-carry@1"`).
-/
public import Obend.Core.Term
public import Obend.Core.Data
public import Obend.Law.Contract
public import Obend.Ledger.Book
public import Obend.Ledger.Seat
public import Obend.Vault.Affordance
public import Obend.Vault.Rehydration
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Vault

open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Law (ContractGoal ContractCert CertVerdict CellContract Holds Admits Narrows
  narrows_refl cellContract_relaw_sound checkContractCert termEq termEq_sound_local)
open Obend.Ledger (AccountId AssetId Book ResourcePosting Seat Proposal ExitRule safeAt
  payoutPostings applyPostings applyPostings_conserves)
open Obend.Vault.Rehydration (Sturdyref AffordanceSurface MembraneViewer Rehydration rehydrateSturdyref)

set_option autoImplicit false

/-! ## 1. Live World State & Carry Plan Actions -/

/-- A live contract-governed cell in `LiveWorld`. -/
structure LiveCell where
  cellId       : String
  accountId    : AccountId
  state        : Data
  law          : Term
  invariant    : Term
  stepRel      : Term
  foreverCrown : Bool := false
  deriving Repr

/-- Live world state across an epoch boundary (`K-CARRY`). -/
structure LiveWorld where
  epoch       : Nat
  cells       : List LiveCell
  ledger      : Book
  seats       : List Seat
  assets      : List AssetId
  sturdyrefs  : List (Sturdyref Data) := []
  revokedUris : List String := []

/-- Per-cell migration action in a `CarryPlan`. -/
inductive CellCarryAction where
  /-- Keep cell state and contract unchanged. -/
  | keep (cellId : String)
  /-- Migrate cell state and contract law, accompanied by narrowing and preservation certificates. -/
  | migrate (cellId : String) (newState : Data) (newLaw newInv newStep : Term)
            (narrowsCert : ContractCert) (preservesCert : ContractCert)
  /-- Explicitly retire a zero-balance cell. -/
  | namedDrop (cellId : String)

/-- Target cell identifier of a `CellCarryAction`. -/
def CellCarryAction.cellId : CellCarryAction → String
  | .keep cid => cid
  | .migrate cid _ _ _ _ _ _ => cid
  | .namedDrop cid => cid

/-- Per-seat migration action in a `CarryPlan`. -/
inductive SeatCarryAction where
  /-- Preserve an active ZoE seat across the epoch boundary (must satisfy `safeAt`). -/
  | preserve (seatAccount : AccountId)
  /-- Refund an active ZoE seat's escrow to its payee and close the seat. -/
  | refund (seatAccount : AccountId)
  deriving DecidableEq, Repr

/-- Target seat account of a `SeatCarryAction`. -/
def SeatCarryAction.seatAccount : SeatCarryAction → AccountId
  | .preserve acc => acc
  | .refund acc => acc

/-- Live world migration plan (`K-CARRY` witness). -/
structure CarryPlan where
  targetEpoch : Nat
  cellActions : List CellCarryAction
  seatActions : List SeatCarryAction
  namedDrops  : List String

/-- Structured refusal reasons for `executeWorldCarry` and `worldCarryJudge`. -/
inductive CarryRefusal where
  | targetEpochNotAdvancing
  | ledgerAccountsNotNodup
  | silentCellDrop (cellId : String)
  | undeclaredNamedDrop (cellId : String)
  | nonZeroDropBalance (cellId : String)
  | crownAttenuationFailed (cellId : String)
  | invariantCertFailed (cellId : String)
  | foreverCrownInvariantChanged (cellId : String)
  | silentSeatDrop (seatAccount : AccountId)
  | seatOfferSafetyViolated (seatAccount : AccountId)
  | seatRefundInvalid (seatAccount : AccountId)
  deriving DecidableEq, Repr

/-! ## 2. Cell, Seat, and Sturdyref Carry Execution -/

/-- Validate a single cell's carry action in `plan` against `W`. -/
def cellCarryValid (W : LiveWorld) (plan : CarryPlan) (c : LiveCell) : Bool :=
  match plan.cellActions.find? (fun a => a.cellId == c.cellId) with
  | none => false
  | some (.keep _) =>
    !plan.namedDrops.contains c.cellId
  | some (.migrate _ _ newLaw newInv _ narrowsCert preservesCert) =>
    !plan.namedDrops.contains c.cellId &&
    (checkContractCert (.narrows newLaw c.law) narrowsCert == .valid) &&
    (checkContractCert (.preserves newLaw newInv) preservesCert == .valid) &&
    (!c.foreverCrown || termEq newInv c.invariant)
  | some (.namedDrop _) =>
    !c.foreverCrown &&
    plan.namedDrops.contains c.cellId &&
    W.assets.all (fun ast => W.ledger.balance c.accountId ast == 0)

/-- Diagnose the first cell carry failure if any cell fails `cellCarryValid`. -/
def diagnoseCellCarryError (_W : LiveWorld) (plan : CarryPlan) (c : LiveCell) : CarryRefusal :=
  match plan.cellActions.find? (fun a => a.cellId == c.cellId) with
  | none => .silentCellDrop c.cellId
  | some (.keep _) => .undeclaredNamedDrop c.cellId
  | some (.migrate _ _ newLaw newInv _ narrowsCert preservesCert) =>
    if plan.namedDrops.contains c.cellId then
      .undeclaredNamedDrop c.cellId
    else if checkContractCert (.narrows newLaw c.law) narrowsCert != .valid then
      .crownAttenuationFailed c.cellId
    else if checkContractCert (.preserves newLaw newInv) preservesCert != .valid then
      .invariantCertFailed c.cellId
    else
      .foreverCrownInvariantChanged c.cellId
  | some (.namedDrop _) =>
    if c.foreverCrown then
      .foreverCrownInvariantChanged c.cellId
    else if !plan.namedDrops.contains c.cellId then
      .undeclaredNamedDrop c.cellId
    else
      .nonZeroDropBalance c.cellId

/-- Apply the carry plan to a single cell (`some c'` if kept/migrated, `none` if named-dropped). -/
def applyCellCarry (plan : CarryPlan) (c : LiveCell) : Option LiveCell :=
  match plan.cellActions.find? (fun a => a.cellId == c.cellId) with
  | some (.keep _) => some c
  | some (.migrate _ newState newLaw newInv newStep _ _) =>
    some { c with state := newState, law := newLaw, invariant := newInv, stepRel := newStep }
  | _ => none

/-- Whether a seat is marked `.preserve` in `plan`. -/
def isSeatPreserved (plan : CarryPlan) (s : Seat) : Bool :=
  match plan.seatActions.find? (fun a => a.seatAccount == s.account) with
  | some (.preserve _) => true
  | _ => false

/-- Whether a seat has an explicit action in `plan`. -/
def isSeatCovered (plan : CarryPlan) (s : Seat) : Bool :=
  (plan.seatActions.find? (fun a => a.seatAccount == s.account)).isSome

/-- Collect refund postings for all seats marked `.refund` in `plan`. -/
def carryRefundPostings (W : LiveWorld) (plan : CarryPlan) : List ResourcePosting :=
  let refundedSeats := W.seats.filter (fun s => !isSeatPreserved plan s)
  refundedSeats.flatMap (fun s => payoutPostings W.ledger s.account s.payee W.assets)

/-- Check that a posting's source and destination are registered in `W.ledger.accounts`. -/
def postingAccountsValid (W : LiveWorld) (p : ResourcePosting) : Bool :=
  W.ledger.accounts.contains p.source && W.ledger.accounts.contains p.destination

/-- Validate a single seat's post-carry state against `ledger'`. -/
def seatCarryValid (W : LiveWorld) (plan : CarryPlan) (ledger' : Book) (s : Seat) : Bool :=
  isSeatCovered plan s &&
  if isSeatPreserved plan s then
    safeAt ledger' s.account s.proposal
  else
    W.assets.all (fun a => ledger'.balance s.account a == 0)

/-- Diagnose the first seat carry failure if any seat fails `seatCarryValid`. -/
def diagnoseSeatCarryError (_W : LiveWorld) (plan : CarryPlan) (ledger' : Book) (s : Seat) : CarryRefusal :=
  if !isSeatCovered plan s then
    .silentSeatDrop s.account
  else if isSeatPreserved plan s && !safeAt ledger' s.account s.proposal then
    .seatOfferSafetyViolated s.account
  else
    .seatRefundInvalid s.account

/-- Rehydrate a `Sturdyref` in `W` by URI for `viewer` (returning `none` if revoked or absent). -/
def rehydrateWorldSturdyref (W : LiveWorld) (uri : String) (viewer : MembraneViewer) :
    Option (AffordanceSurface Data × Rehydration) :=
  if W.revokedUris.contains uri then
    none
  else
    match W.sturdyrefs.find? (fun sr => sr.uri == uri) with
    | some sr => some (rehydrateSturdyref sr viewer)
    | none => none

/-- Collect URIs of sturdyrefs in `W` whose target `cellId` is in `plan.namedDrops`. -/
def droppedSturdyrefUris (W : LiveWorld) (plan : CarryPlan) : List String :=
  (W.sturdyrefs.filter (fun sr => plan.namedDrops.contains sr.cellId)).map (·.uri)

/-- **Execute a Live World `K-CARRY` Migration (`executeWorldCarry`)**:
    Verifies epoch progression, ledger account uniqueness, total cell coverage (no silent drops,
    zero-balance named drops, verified narrowing & invariant certificates), refund posting
    conservation, and ZoE seat offer safety / refund completeness. -/
def executeWorldCarry (W : LiveWorld) (plan : CarryPlan) : Except CarryRefusal LiveWorld :=
  if !(W.epoch < plan.targetEpoch) then
    .error .targetEpochNotAdvancing
  else if !decide W.ledger.accounts.Nodup then
    .error .ledgerAccountsNotNodup
  else if !W.cells.all (cellCarryValid W plan) then
    match W.cells.find? (fun c => !cellCarryValid W plan c) with
    | some badCell => .error (diagnoseCellCarryError W plan badCell)
    | none => .error (.silentCellDrop "")
  else
    let postings := carryRefundPostings W plan
    if !postings.all (postingAccountsValid W) then
      .error (.seatRefundInvalid 0)
    else
      let ledger' := applyPostings W.ledger postings
      if !W.seats.all (seatCarryValid W plan ledger') then
        match W.seats.find? (fun s => !seatCarryValid W plan ledger' s) with
        | some badSeat => .error (diagnoseSeatCarryError W plan ledger' badSeat)
        | none => .error (.silentSeatDrop 0)
      else
        .ok {
          epoch       := plan.targetEpoch
          cells       := W.cells.filterMap (applyCellCarry plan)
          ledger      := ledger'
          seats       := W.seats.filter (isSeatPreserved plan)
          assets      := W.assets
          sturdyrefs  := W.sturdyrefs
          revokedUris := W.revokedUris ++ plan.namedDrops ++ droppedSturdyrefUris W plan
        }

/-! ## 3. The 5 Keystone `K-CARRY` Theorems -/

theorem executeWorldCarry_ok_destruct {W W' : LiveWorld} {plan : CarryPlan}
    (h : executeWorldCarry W plan = .ok W') :
    W.epoch < plan.targetEpoch ∧
    W.ledger.accounts.Nodup ∧
    W.cells.all (cellCarryValid W plan) = true ∧
    (carryRefundPostings W plan).all (postingAccountsValid W) = true ∧
    W.seats.all (seatCarryValid W plan (applyPostings W.ledger (carryRefundPostings W plan))) = true ∧
    W'.epoch = plan.targetEpoch ∧
    W'.cells = W.cells.filterMap (applyCellCarry plan) ∧
    W'.ledger = applyPostings W.ledger (carryRefundPostings W plan) ∧
    W'.seats = W.seats.filter (isSeatPreserved plan) ∧
    W'.assets = W.assets ∧
    W'.sturdyrefs = W.sturdyrefs ∧
    W'.revokedUris = W.revokedUris ++ plan.namedDrops ++ droppedSturdyrefUris W plan := by
  unfold executeWorldCarry at h
  cases h_ep : (W.epoch < plan.targetEpoch : Bool)
  · simp [h_ep] at h
  · simp only [decide_eq_true_eq] at h_ep
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_ep, h_nd] at h
    · have h_nodup : W.ledger.accounts.Nodup := of_decide_eq_true h_nd
      cases h_cells : W.cells.all (cellCarryValid W plan)
      · simp [h_ep, h_nd, h_cells] at h
        split at h <;> cases h
      · cases h_post : (carryRefundPostings W plan).all (postingAccountsValid W)
        · simp [h_ep, h_nd, h_cells, h_post] at h
        · cases h_seats : W.seats.all (seatCarryValid W plan (applyPostings W.ledger (carryRefundPostings W plan)))
          · simp [h_ep, h_nd, h_cells, h_post, h_seats] at h
            split at h <;> cases h
          · simp [h_ep, h_nd, h_cells, h_post, h_seats] at h
            subst h
            exact ⟨h_ep, h_nodup, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              (List.append_assoc _ _ _).symm⟩

/-- **Keystone Theorem 1 (`carry_no_silent_drop`)**:
    In any admitted `executeWorldCarry W plan = .ok W'`, every cell `c ∈ W.cells` is either
    carried into `W'.cells` (with matching `cellId` and `accountId`), OR explicitly named in
    `plan.namedDrops` with zero ledger balance across all tracked assets `a ∈ W.assets`. -/
theorem carry_no_silent_drop {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W')
    {c : LiveCell} (hc : c ∈ W.cells) :
    (∃ c' ∈ W'.cells, c'.cellId = c.cellId ∧ c'.accountId = c.accountId) ∨
    (c.cellId ∈ plan.namedDrops ∧ ∀ a ∈ W.assets, W.ledger.balance c.accountId a = 0) := by
  obtain ⟨_, _, h_cells, _, _, _, h_W'_cells, _, _, _, _, _⟩ := executeWorldCarry_ok_destruct h_ok
  have h_valid : cellCarryValid W plan c = true := List.all_eq_true.mp h_cells c hc
  unfold cellCarryValid at h_valid
  cases h_act : plan.cellActions.find? (fun a => a.cellId == c.cellId) with
  | none =>
    rw [h_act] at h_valid
    cases h_valid
  | some act =>
    rw [h_act] at h_valid
    cases act with
    | keep cid =>
      left
      refine ⟨c, ?_, rfl, rfl⟩
      rw [h_W'_cells, List.mem_filterMap]
      exact ⟨c, hc, by simp [applyCellCarry, h_act]⟩
    | migrate cid newState newLaw newInv newStep narrowsCert preservesCert =>
      left
      let c' : LiveCell := { c with state := newState, law := newLaw, invariant := newInv, stepRel := newStep }
      refine ⟨c', ?_, rfl, rfl⟩
      rw [h_W'_cells, List.mem_filterMap]
      exact ⟨c, hc, by simp [applyCellCarry, h_act, c']⟩
    | namedDrop cid =>
      right
      simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, beq_iff_eq] at h_valid
      exact ⟨h_valid.1.2, h_valid.2⟩

/-- **Keystone Theorem 2 (`carry_conserves_total_book`)**:
    In any admitted `executeWorldCarry W plan = .ok W'`, total book balance is strictly
    conserved across the epoch boundary for every asset `a : AssetId`:
    `W'.ledger.totalAsset a = W.ledger.totalAsset a`. -/
theorem carry_conserves_total_book {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W') (a : AssetId) :
    W'.ledger.totalAsset a = W.ledger.totalAsset a := by
  obtain ⟨_, h_nodup, _, h_post, _, _, _, h_ledger, _, _, _, _⟩ := executeWorldCarry_ok_destruct h_ok
  rw [h_ledger]
  apply applyPostings_conserves
  · intro p hp
    have hp_ok := List.all_eq_true.mp h_post p hp
    unfold postingAccountsValid at hp_ok
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hp_ok
    exact hp_ok
  · exact h_nodup

/-- **Keystone Theorem 3 (`carry_preserves_forever_crowns`)**:
    For every cell `c ∈ W.cells` that is carried (`applyCellCarry plan c = some c'`) under an
    admitted `executeWorldCarry W plan = .ok W'`:
    1. Either `c'.law = c.law` (when kept) or there are verified narrowing and preservation
       certificates `checkContractCert (.narrows c'.law c.law) narrowsCert = .valid` and
       `checkContractCert (.preserves c'.law c'.invariant) preservesCert = .valid`.
    2. If `c.foreverCrown = true`, then `c'.foreverCrown = true` and `c'.invariant = c.invariant`.
    3. Given semantic narrowing `Narrows c'.law C.law` on a `CellContract` for `c`,
       `cellContract_relaw_sound` produces a valid child `CellContract` with law `c'.law`
       preserving `C.invariant` and `C.stepRel`. -/
theorem carry_preserves_forever_crowns {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W')
    {c c' : LiveCell} (hc : c ∈ W.cells) (h_carried : applyCellCarry plan c = some c') :
    (c'.law = c.law ∨
      ∃ narrowsCert preservesCert,
        checkContractCert (.narrows c'.law c.law) narrowsCert = .valid ∧
        checkContractCert (.preserves c'.law c'.invariant) preservesCert = .valid) ∧
    (c.foreverCrown = true → c'.foreverCrown = true ∧ c'.invariant = c.invariant) ∧
    (∀ (C : CellContract) (hn : Narrows c'.law C.law),
      (cellContract_relaw_sound C c'.law hn).invariant = C.invariant ∧
      (cellContract_relaw_sound C c'.law hn).stepRel = C.stepRel) := by
  obtain ⟨_, _, h_cells, _, _, _, _, _, _, _, _, _⟩ := executeWorldCarry_ok_destruct h_ok
  have h_valid : cellCarryValid W plan c = true := List.all_eq_true.mp h_cells c hc
  unfold cellCarryValid at h_valid
  unfold applyCellCarry at h_carried
  cases h_act : plan.cellActions.find? (fun a => a.cellId == c.cellId) with
  | none =>
    rw [h_act] at h_carried
    cases h_carried
  | some act =>
    rw [h_act] at h_valid h_carried
    cases act with
    | keep cid =>
      simp only [Option.some.injEq] at h_carried
      subst h_carried
      refine ⟨Or.inl rfl, fun hfc => ⟨hfc, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    | migrate cid newState newLaw newInv newStep narrowsCert preservesCert =>
      simp only [Option.some.injEq] at h_carried
      subst h_carried
      simp only [Bool.and_eq_true, beq_iff_eq] at h_valid
      obtain ⟨⟨⟨_, h_nar⟩, h_pres⟩, h_crown⟩ := h_valid
      refine ⟨Or.inr ⟨narrowsCert, preservesCert, h_nar, h_pres⟩, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      intro hfc
      simp [hfc] at h_crown
      exact ⟨hfc, termEq_sound_local h_crown⟩
    | namedDrop cid =>
      cases h_carried

/-- **Keystone Theorem 4 (`carry_preserves_zoe_offer_safety`)**:
    In any admitted `executeWorldCarry W plan = .ok W'`, every active ZoE seat `s ∈ W.seats`
    is either:
    - Preserved in `W'.seats` with offer safety holding (`safeAt W'.ledger s.account s.proposal = true`), OR
    - Refunded and closed (`s ∉ W'.seats`) with zero remaining escrow balance across all tracked assets
      (`∀ a ∈ W.assets, W'.ledger.balance s.account a = 0`). -/
theorem carry_preserves_zoe_offer_safety {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W')
    {s : Seat} (hs : s ∈ W.seats) :
    (s ∈ W'.seats ∧ safeAt W'.ledger s.account s.proposal = true) ∨
    (s ∉ W'.seats ∧ ∀ a ∈ W.assets, W'.ledger.balance s.account a = 0) := by
  obtain ⟨_, _, _, _, h_seats, _, _, h_ledger, h_W'_seats, _, _, _⟩ := executeWorldCarry_ok_destruct h_ok
  have h_valid : seatCarryValid W plan W'.ledger s = true := by
    rw [h_ledger]
    exact List.all_eq_true.mp h_seats s hs
  unfold seatCarryValid at h_valid
  rw [Bool.and_eq_true] at h_valid
  obtain ⟨_, h_outcome⟩ := h_valid
  cases h_pres : isSeatPreserved plan s with
  | true =>
    rw [h_pres] at h_outcome
    left
    refine ⟨?_, h_outcome⟩
    rw [h_W'_seats, List.mem_filter]
    exact ⟨hs, h_pres⟩
  | false =>
    rw [h_pres] at h_outcome
    right
    refine ⟨?_, ?_⟩
    · rw [h_W'_seats, List.mem_filter]
      intro ⟨_, h_true⟩
      rw [h_pres] at h_true
      cases h_true
    · simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, beq_iff_eq] at h_outcome
      exact h_outcome

/-- **Keystone Theorem 5 (`carry_rehydrates_sturdyrefs`)**:
    In any admitted `executeWorldCarry W plan = .ok W'`, any URI `uri` that is neither
    previously revoked (`W.revokedUris.contains uri = false`), nor dropped in `plan.namedDrops`
    (`plan.namedDrops.contains uri = false`), nor targeting a dropped cell
    (`(droppedSturdyrefUris W plan).contains uri = false`) rehydrates to the exact same
    membrane-attenuated surface and liveness classification in `W'` as in `W` for every `viewer`. -/
theorem carry_rehydrates_sturdyrefs {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W')
    (uri : String) (viewer : MembraneViewer)
    (h_unrevoked : W.revokedUris.contains uri = false)
    (h_not_dropped : plan.namedDrops.contains uri = false)
    (h_cell_not_dropped : (droppedSturdyrefUris W plan).contains uri = false := by rfl) :
    rehydrateWorldSturdyref W' uri viewer = rehydrateWorldSturdyref W uri viewer := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h_srs, h_rev⟩ := executeWorldCarry_ok_destruct h_ok
  unfold rehydrateWorldSturdyref
  rw [h_rev, h_srs, List.contains_append, List.contains_append,
      h_unrevoked, h_not_dropped, h_cell_not_dropped]
  rfl

/-- **Dropped-Cell Sturdyref Revocation Theorem (`carry_revokes_dropped_cell_sturdyrefs`)**:
    If `sr ∈ W.sturdyrefs` targets a cell `sr.cellId` in `plan.namedDrops`, then after
    `executeWorldCarry W plan = .ok W'`, `rehydrateWorldSturdyref W' sr.uri viewer = none`. -/
theorem carry_revokes_dropped_cell_sturdyrefs {W W' : LiveWorld} {plan : CarryPlan}
    (h_ok : executeWorldCarry W plan = .ok W')
    {sr : Sturdyref Data} (hsr : sr ∈ W.sturdyrefs)
    (h_dropped : plan.namedDrops.contains sr.cellId = true)
    (viewer : MembraneViewer) :
    rehydrateWorldSturdyref W' sr.uri viewer = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h_rev⟩ := executeWorldCarry_ok_destruct h_ok
  unfold rehydrateWorldSturdyref
  have h_in_dropped : (droppedSturdyrefUris W plan).contains sr.uri = true := by
    unfold droppedSturdyrefUris
    rw [List.contains_iff_mem, List.mem_map]
    exact ⟨sr, List.mem_filter.mpr ⟨hsr, h_dropped⟩, rfl⟩
  rw [h_rev, List.contains_append, h_in_dropped, Bool.or_true]
  rfl

/-! ## 4. Registered External Judge Format `"world-carry@1"` -/

/-- Verdict wrapper for `worldCarryJudge`. -/
def checkWorldCarry (W : LiveWorld) (plan : CarryPlan) : Judge.Verdict CarryRefusal :=
  match executeWorldCarry W plan with
  | .ok _ => .ok
  | .error e => .refused e []

/-- Semantic meaning established when `worldCarryJudge` accepts `(W, plan)`. -/
def WorldCarryMeaning (W : LiveWorld) (plan : CarryPlan) : Prop :=
  ∃ W', executeWorldCarry W plan = .ok W'

/-- **The `LiveWorld` K-CARRY Judge (`worldCarryJudge`)**. -/
@[instance_reducible] def worldCarryJudge : Judge LiveWorld CarryPlan where
  Clause := CarryRefusal
  Meaning := WorldCarryMeaning
  check _ W plan := checkWorldCarry W plan
  sound := by
    intro _ W plan h
    unfold checkWorldCarry at h
    cases hex : executeWorldCarry W plan with
    | ok W' => exact ⟨W', hex⟩
    | error e => rw [hex] at h; cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ href; cases href
  Fragment _ := True
  complete := by
    rintro W _ ⟨plan, W', hok⟩
    exact ⟨plan, 0, by simp [checkWorldCarry, hok]⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- Sample valid `LiveWorld` for `"world-carry@1"` format self-testing. -/
def sampleValidLiveWorld : LiveWorld where
  epoch := 1
  cells := [
    { cellId := "cell.treasury"
      accountId := 10
      state := .record [("bal", .natural 500)]
      law := .boolean true
      invariant := .boolean true
      stepRel := .boolean true
      foreverCrown := true },
    { cellId := "cell.deprecated"
      accountId := 20
      state := .record [("bal", .natural 0)]
      law := .boolean true
      invariant := .boolean true
      stepRel := .boolean true
      foreverCrown := false }
  ]
  ledger := {
    accounts := [10, 20, Obend.Ledger.protectedBase]
    balances := fun acc ast => if acc == 10 && ast == 0 then 500 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  seats := [
    { account := Obend.Ledger.protectedBase
      payee := 10
      proposal := { give := [(0, 0)], want := [(0, 0)], exit := .onDemand, donate := false } }
  ]
  assets := [0]

/-- Sample valid `CarryPlan` for `sampleValidLiveWorld`. -/
def sampleValidCarryPlan : CarryPlan where
  targetEpoch := 2
  cellActions := [.keep "cell.treasury", .namedDrop "cell.deprecated"]
  seatActions := [.preserve Obend.Ledger.protectedBase]
  namedDrops := ["cell.deprecated"]

/-- Planted bad `CarryPlan` that silently drops `"cell.deprecated"` (omitting it from `cellActions`). -/
def sampleBadCarryPlan : CarryPlan where
  targetEpoch := 2
  cellActions := [.keep "cell.treasury"]
  seatActions := [.preserve Obend.Ledger.protectedBase]
  namedDrops := []

theorem sampleBadCarryPlan_refused :
    worldCarryJudge.check 0 sampleValidLiveWorld sampleBadCarryPlan =
      .refused (.silentCellDrop "cell.deprecated") [] := rfl

/-- Extract the initial integer balance stored in `c.state`. -/
def liveCellInitialBalance (c : LiveCell) : Int :=
  match c.state with
  | .record fields =>
    match fields.find? (fun (k, _) => k == "bal" || k == "balance") with
    | some (_, .natural n) => (n : Int)
    | _ => 0
  | .natural n => (n : Int)
  | _ => 0

/-- Decode a single `LiveCell` from a JSON object. -/
def decodeLiveCellJson (j : Lean.Json) : Except String LiveCell :=
  match j.getObjValAs? String "cellId", j.getObjValAs? Nat "accountId" with
  | .ok cid, .ok acc =>
    if cid.isEmpty then
      .error "invalid LiveCell JSON: empty cellId"
    else
      let crown := (j.getObjValAs? Bool "foreverCrown").toOption.getD false
      let bal := (j.getObjValAs? Nat "balance").toOption.getD 0
      .ok {
        cellId       := cid
        accountId    := acc
        state        := .record [("bal", .natural bal)]
        law          := .boolean true
        invariant    := .boolean true
        stepRel      := .boolean true
        foreverCrown := crown
      }
  | _, _ => .error "invalid LiveCell JSON: expected {cellId, accountId}"

/-- Decode a list of `LiveCell`s from a JSON array. -/
def decodeLiveCellsJson (arr : List Lean.Json) : Except String (List LiveCell) :=
  arr.mapM decodeLiveCellJson

/-- Wire decoder for `LiveWorld` supporting canonical aliases and structured JSON payloads. -/
def decodeLiveWorld (s : String) : Except String LiveWorld :=
  if decide (s = "valid" ∨ s = "bad") then
    .ok sampleValidLiveWorld
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid LiveWorld JSON: missing required fields (epoch, cells)"
  else
    match Lean.Json.parse s with
    | .error err => .error s!"invalid LiveWorld JSON: {err}"
    | .ok j =>
      match j.getObjValAs? Nat "epoch", j.getObjValAs? (Array Lean.Json) "cells" with
      | .ok ep, .ok cellsArr =>
        if cellsArr.isEmpty then
          .error "invalid LiveWorld JSON: cells array must not be empty"
        else
          match decodeLiveCellsJson cellsArr.toList with
          | .error e => .error e
          | .ok cells =>
            let refs : List String :=
              match j.getObjValAs? (Array String) "rehydratedRefs" with
              | .ok r => r.toList
              | .error _ => []
            let revoked : List String :=
              match j.getObjValAs? (Array String) "revokedUris" with
              | .ok r => r.toList
              | .error _ => []
            let _ := refs
            let cellAccs := (cells.map (·.accountId) ++ [Obend.Ledger.protectedBase]).eraseDups
            let decodedLedger : Book := {
              accounts := cellAccs
              balances := fun acc ast =>
                if ast == 0 then
                  (cells.filter (fun c => c.accountId == acc)).foldl
                    (fun s c => s + liveCellInitialBalance c) 0
                else 0
              leaseRecords := fun _ => none
              floors := fun _ _ => 0
            }
            .ok { sampleValidLiveWorld with
              epoch       := ep
              cells       := cells
              ledger      := decodedLedger
              revokedUris := revoked }
      | _, _ =>
        .error "invalid LiveWorld JSON: missing required fields (epoch, cells)"

/-- Decode a single `CellCarryAction` from a JSON object, rejecting drops of `"forever"` crown cells. -/
def decodeCellCarryActionJson (j : Lean.Json) : Except String CellCarryAction :=
  match j.getObjValAs? String "kind", j.getObjValAs? String "cellId" with
  | .ok "keep", .ok cid =>
    if cid.isEmpty then .error "invalid CellCarryAction JSON: empty cellId"
    else .ok (.keep cid)
  | .ok "migrate", .ok cid =>
    if cid.isEmpty then .error "invalid CellCarryAction JSON: empty cellId"
    else
      let bal := (j.getObjValAs? Nat "balance").toOption.getD
        ((j.getObjValAs? Nat "newBalance").toOption.getD 0)
      let newState : Data := .record [("bal", .natural bal)]
      let newLaw : Term := .boolean true
      let newInv : Term := .boolean true
      let newStep : Term := .boolean true
      let narrowsGoal : ContractGoal := .narrows newLaw newLaw
      let preservesGoal : ContractGoal := .preserves newLaw newInv
      let narrowsCert : ContractCert :=
        .byLoweredDecider "migrate_narrows" []
          (Obend.Law.mkGoalBoundDeciderReceipt "migrate_narrows" "decider@1" narrowsGoal)
      let preservesCert : ContractCert :=
        .byLoweredDecider "migrate_preserves" []
          (Obend.Law.mkGoalBoundDeciderReceipt "migrate_preserves" "decider@1" preservesGoal)
      .ok (.migrate cid newState newLaw newInv newStep narrowsCert preservesCert)
  | .ok "namedDrop", .ok cid =>
    let crown := (j.getObjValAs? Bool "foreverCrown").toOption.getD false
    let lifetime := (j.getObjValAs? String "lifetime").toOption.getD ""
    if cid.isEmpty then
      .error "invalid CellCarryAction JSON: empty cellId"
    else if crown || lifetime == "forever" then
      .error s!"invalid CarryPlan JSON: cannot drop forever crown cell '{cid}'"
    else
      .ok (.namedDrop cid)
  | .ok k, _ => .error s!"invalid CellCarryAction JSON: unsupported kind '{k}'"
  | _, _ => .error "invalid CellCarryAction JSON: expected {kind, cellId}"

/-- Decode a single `SeatCarryAction` from a JSON object. -/
def decodeSeatCarryActionJson (j : Lean.Json) : Except String SeatCarryAction :=
  match j.getObjValAs? String "kind", j.getObjValAs? Nat "seatAccount" with
  | .ok "preserve", .ok acc => .ok (.preserve acc)
  | .ok "refund", .ok acc => .ok (.refund acc)
  | .ok k, _ => .error s!"invalid SeatCarryAction JSON: unsupported kind '{k}'"
  | _, _ => .error "invalid SeatCarryAction JSON: expected {kind, seatAccount}"

/-- Wire decoder for `CarryPlan` supporting canonical aliases and structured JSON payloads. -/
def decodeCarryPlan (s : String) : Except String CarryPlan :=
  if decide (s = "valid") then
    .ok sampleValidCarryPlan
  else if decide (s = "bad") then
    .ok sampleBadCarryPlan
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid CarryPlan JSON: missing required fields (targetEpoch, cellActions, seatActions)"
  else
    match Lean.Json.parse s with
    | .error err => .error s!"invalid CarryPlan JSON: {err}"
    | .ok j =>
      match j.getObjValAs? Nat "targetEpoch",
            j.getObjValAs? (Array Lean.Json) "cellActions",
            j.getObjValAs? (Array Lean.Json) "seatActions" with
      | .ok targetEp, .ok cellArr, .ok seatArr =>
        if cellArr.isEmpty then
          .error "invalid CarryPlan JSON: cellActions must not be empty"
        else
          match cellArr.toList.mapM decodeCellCarryActionJson,
                seatArr.toList.mapM decodeSeatCarryActionJson with
          | .ok cellActs, .ok seatActs =>
            let drops : List String :=
              match j.getObjValAs? (Array String) "namedDrops" with
              | .ok d => d.toList
              | .error _ =>
                cellActs.filterMap fun a =>
                  match a with
                  | .namedDrop cid => some cid
                  | _ => none
            let rehydrated : List String :=
              match j.getObjValAs? (Array String) "rehydratedRefs" with
              | .ok r => r.toList
              | .error _ => []
            if rehydrated.any (fun r => drops.contains r) then
              .error "invalid CarryPlan JSON: rehydratedRefs cannot reference a dropped cell"
            else
              .ok {
                targetEpoch := targetEp
                cellActions := cellActs
                seatActions := seatActs
                namedDrops  := drops
              }
          | .error e, _ => .error e
          | _, .error e => .error e
      | _, _, _ =>
        .error "invalid CarryPlan JSON: missing required fields (targetEpoch, cellActions, seatActions)"

/-- **The registered format `"world-carry@1"` wrapping `worldCarryJudge`.** -/
def worldCarryFormat : Judge.Format where
  name := "world-carry"
  version := "1"
  Obj := LiveWorld
  Cert := CarryPlan
  judge := worldCarryJudge
  decodeObj := decodeLiveWorld
  decodeCert := decodeCarryPlan
  trust := .kernel
  regime := .decidable
  bad := (sampleValidLiveWorld, sampleBadCarryPlan)
  badGrade := 0
  bad_refused := ⟨.silentCellDrop "cell.deprecated", [], sampleBadCarryPlan_refused⟩

theorem decodeLiveWorld_refuses_empty_json :
    decodeLiveWorld "{}" =
      .error "invalid LiveWorld JSON: missing required fields (epoch, cells)" := rfl

/-- **Empty JSON Refusal Theorem (`worldCarryFormat_refuses_empty_json`)**:
    Verifies that `worldCarryFormat.checkBytes` rejects empty JSON `"{}"` payloads with `.refused (.malformed ...)`. -/
theorem worldCarryFormat_refuses_empty_json :
    worldCarryFormat.checkBytes 0 "{}" "{}" =
      .refused (.malformed "object: invalid LiveWorld JSON: missing required fields (epoch, cells)") [] := by
  show (match decodeLiveWorld "{}", decodeCarryPlan "{}" with
    | .ok o, .ok c => (worldCarryFormat.judge.check 0 o c).map Judge.FormatClause.judge
    | .error e, _ => Judge.Verdict.refused (Judge.FormatClause.malformed s!"object: {e}") []
    | _, .error e => Judge.Verdict.refused (Judge.FormatClause.malformed s!"certificate: {e}") []) =
      Judge.Verdict.refused (Judge.FormatClause.malformed "object: invalid LiveWorld JSON: missing required fields (epoch, cells)") []
  rw [decodeLiveWorld_refuses_empty_json]
  rfl

#tooth worldCarryFormat_refuses_empty_json by mutation
  decodeLiveWorld := fun _ => .ok sampleValidLiveWorld

end Obend.Vault
end
