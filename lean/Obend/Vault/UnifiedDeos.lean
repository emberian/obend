module
/-
# Obend.Vault.UnifiedDeos — Unified DeOS Spine ("One Vault, Not Four")

Single authoritative bridge tying Obend's live journaled Vault (`Obend.Vault.Replay.World`)
to the unified Ledger, Markets, Capability/Carry, Selective-Disclosure Projection, and
Simplex BFT Finality stack — with zero shadow worlds and zero tautological certificates:

1. **Journaled World & `Reasons`-Gated Mandates (`Replay.World` + `Mandate` + `Reasons`)**:
   - Projects `CheckedCarry.VaultAuthState` directly from `Replay.World` (`grants`, `retention`,
     `journal.length`) without duplicating journal state.
   - Binds `Obend.Reasons.State` well-founded justification support (`status because == .supported`)
     into `Mandate.Caveat` (`reasonsCaveat`, `worldReasonsCaveat`), connecting `Replay.justified_needs_support`
     to `Mandate.delegate_conserves` and `Mandate.delegate_child_attenuates`.
2. **One Resource Ledger, ZoE Offer Safety & Sealed Escrow (`Floors` + `Register` + `Seat` + `Escrow`)**:
   - Connects finite-support typed-account `FloorBook` (`AccountKind`: `user | issuerWell | seat | escrow | feePool`)
     to `Register.Reg` + `Movement` (`realizeBatchOnReg_sound`), one-time `Invitation` spending
     (`InvitationRegistry.no_double_redeem`), `donate` gift guards (`admitOffer_donationUnmarked_refused`),
     full-support `exitSeat` (`exit_sweeps_all_assets`), and `EscrowReachable` no-theft (`sealedescrow_no_theft`).
3. **Footprint No-TOCTOU, Markets & Blinded Projections (`Hyperedge` + `Clearing` + `Netting` + `AutomataConfinement` + `Projection`)**:
   - Connects `Footprint` (`no_toctou`, `vaultTurn_disjoint_commutes`, `stateBoundTurn_conserves_actual_state_balances`),
     `drexClearingJudge` (`ClearingSemanticMeaning`), `nettingJudge` (`netting@1`, `net_conserves`,
     `net_reduces_gross_exposure`, `settleNetting_agrees_with_gross`, `NettingCert.toMovements_balanced`),
     `dclutchHoardJudge` (`dclutch-hoard-clearing@1`, `DclutchHoardMeaning`), and `BlindedMultiProof`
     (`verifyBlindedMultiProof_revealed_binds`).
4. **Checked Carry (`CheckedCarry`) & Simplex Finality + Durable WAL Recovery (`SimplexProtocol` + `SimplexTrace` + `Finality` + `Run.Durable`)**:
   - Proves universal `AdmissibleCarry` survival across `Replay.World` rerooting, universal `Grants.revoke`
     refusal, title-grant non-narrowing (`TitleMigration.copied_title_grant_not_semantic_narrowing`),
     `simplexTraceJudge` → `SimplexProtocol.Reach` → `SimplexFinalityGate` `.quorum_final` uniqueness +
     SP 800-185 `cshake256Bytes` root binding, and durable WAL crash-recovery anti-equivocation +
     expose-once externalization.
-/
public import Obend.Vault.Replay
public import Obend.Vault.Hyperedge
public import Obend.Vault.Escrow
public import Obend.Vault.Projection
public import Obend.Vault.Mandate
public import Obend.Vault.CheckedCarry
public import Obend.Ledger.Floors
public import Obend.Ledger.Seat
public import Obend.Judge.Clearing
public import Obend.Judge.Netting
public import Obend.Judge.AutomataConfinement
public import Obend.Judge.TranscriptPolicy
public import Obend.Consensus.Simplex
public import Obend.Consensus.SimplexProtocol
public import Obend.Consensus.SimplexTrace
public import Obend.Consensus.Epistemic
public import Obend.Consensus.Finality
public import Obend.Run.Durable
public import Obend.Fold.Collapse
import all Obend.Run.Durable

@[expose] public section
namespace Obend.Vault.UnifiedDeos

open Obend.Ledger
open Obend.Vault
open Obend.Vault.Escrow
open Obend.Vault.Projection
open Obend.Vault.Mandate
open Obend.Vault.CheckedCarry
open Obend.Judge
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace
open Obend.Consensus.Epistemic
open Obend.Consensus.Finality
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable

set_option autoImplicit false

/-! ## 1. Read-Only Projection of `Replay.World` into `CheckedCarry` & `Mandate` -/

/-- Aggregate all active `Retention.Contract` clauses declared in `w.retention`. -/
def worldRetention (w : Obend.Vault.Replay.World) : Retention.Contract :=
  { name := "world-retention"
    retire := w.retention.flatMap (·.retire)
    abandon := w.retention.flatMap (·.abandon) }

/-- Project `CheckedCarry.VaultAuthState` directly from `Replay.World` (`grants`, `worldRetention w`,
    `journal.rows.length`) with cryptographic commitment roots `(grantRoot, storeRoot)`. -/
def worldAuthState (w : Obend.Vault.Replay.World)
    (grantRoot storeRoot : ByteArray := ByteArray.empty) : VaultAuthState :=
  { grants := w.grants
    retention := worldRetention w
    logicalHeight := w.journal.rows.length
    grantRoot := grantRoot
    storeRoot := storeRoot }

/-- Rerooting cryptographic digests `(grantRoot, storeRoot) ↦ (grantRoot', storeRoot')` on
    `Replay.World` preserves exact `AuthorityMeaning`. -/
theorem worldAuthState_reroot_meaning
    (w : Obend.Vault.Replay.World) (g₁ s₁ g₂ s₂ : ByteArray) :
    AuthorityMeaning (worldAuthState w g₁ s₁) (worldAuthState w g₂ s₂) :=
  ⟨fun _ => Iff.rfl, rfl, rfl, rfl, rfl⟩

/-- Rerooting `Replay.World` preserves `AdmissibleCarry` in both directions for every `CarryRequest`. -/
theorem worldAuthState_reroot_admissible_iff
    (w : Obend.Vault.Replay.World) (g₁ s₁ g₂ s₂ : ByteArray) (req : CarryRequest) :
    AdmissibleCarry (worldAuthState w g₁ s₁) req ↔
      AdmissibleCarry (worldAuthState w g₂ s₂) req :=
  neutral_capability_iff (worldAuthState_reroot_meaning w g₁ s₁ g₂ s₂) req

/-- Revoking `req.grantId` on `w.grants` universally refuses `AdmissibleCarry` in the updated `Replay.World`. -/
theorem world_revoke_refuses_carry
    (w : Obend.Vault.Replay.World) (gRoot sRoot : ByteArray) (req : CarryRequest) :
    ¬ AdmissibleCarry (worldAuthState { w with grants := w.grants.revoke req.grantId } gRoot sRoot) req := by
  rintro ⟨standing, isLive, idEq, _⟩
  unfold worldAuthState at isLive
  have hlive := (Transport.mem_live_revoke w.grants req.grantId standing).mp isLive
  exact hlive.2 idEq

/-- Runtime `Mandate.Caveat` backed directly by `Obend.Reasons.State`: admits method invocations
    if and only if justification atom `because` is `.supported` in the well-founded model. -/
def reasonsCaveat (st : Obend.Reasons.State) (because : String) : Caveat :=
  ⟨fun _ => st.status because == .supported⟩

/-- `Mandate.Caveat` projected directly from `Replay.World.reasons`. -/
def worldReasonsCaveat (w : Obend.Vault.Replay.World) (because : String) : Caveat :=
  reasonsCaveat w.reasons because

theorem reasonsCaveat_admits_iff (st : Obend.Reasons.State) (because : String) (method : Nat) :
    (reasonsCaveat st because).admits method = true ↔ st.status because = .supported := by
  unfold reasonsCaveat
  exact beq_iff_eq

/-- If an invocation is authorized by a mandate carrying `worldReasonsCaveat w because` (or any
    child delegated from it), then `because` is `.supported` in `w.reasons` — matching
    `Replay.justified_needs_support`. -/
theorem authorizedBy_worldReasonsCaveat_supported
    (w : Obend.Vault.Replay.World) (because : String)
    (parent child : Mandate) (inv : Invocation)
    (h_parent_cv : parent.caveat = worldReasonsCaveat w because)
    (h_att : attenuates child parent)
    (h_auth : authorizedBy child inv = true) :
    w.reasons.status because = .supported := by
  unfold authorizedBy at h_auth
  simp only [Bool.and_eq_true] at h_auth
  have h_parent_adm : parent.caveat.admits inv.method = true := h_att.2.2.2.2.2 inv.method h_auth.2
  rw [h_parent_cv] at h_parent_adm
  exact (reasonsCaveat_admits_iff w.reasons because inv.method).mp h_parent_adm

/-! ## 2. Unified DeOS Turn Gate Over `Replay.World`, `FloorBook`, `Seat` & `Hyperedge` -/

/-- Canonical external market, automata & transcript judge formats active on the Unified DeOS spine. -/
def unifiedMarketFormats : List Format :=
  [ nettingFormat
  , dclutchHoardFormat
  , dfaFormat
  , cfgCompactFormat
  , tlsnTranscriptFormat
  , simplexTraceFormat ]

/-- Unified DeOS Spine state coupling the live `Replay.World` (read-only projection) with the
    finite-support typed-account `FloorBook`, classical `Book`/`Seat` ZoE registry, and `VaultStore`
    cell snapshot. -/
structure UnifiedDeosSpine where
  world      : Obend.Vault.Replay.World
  store      : VaultStore
  floorBook  : FloorBook
  seatBook   : Book
  invReg     : InvitationRegistry
  seats      : List Seat

/-- Check that an atomic `VaultTurn` and typed-account `FloorBook` batch are jointly admissible on `S`:
    1. `turn.readPins` holds against `S.store` (`admitFootprint` succeeds — no TOCTOU),
    2. `checkTurnStateBalancesBound stateAssets turn = true` (binding `turn.balanced` to state balances),
    3. Every `TurnWitness` on `turn` checks against `unifiedMarketFormats`,
    4. `S.floorBook.admitBatch postings` succeeds (preserving all non-issuer ≥ 0 floors),
    5. Every active ZoE `Seat` in `S.seats` satisfies `safeAt S.seatBook s.account s.proposal = true`. -/
def checkUnifiedTurn (S : UnifiedDeosSpine) (stateAssets : List String)
    (turn : VaultTurn) (postings : List TypedPosting) : Bool :=
  (admitFootprint S.store turn.readPins).isOk &&
  checkTurnStateBalancesBound stateAssets turn &&
  turn.witnesses.all (checkTurnWitness unifiedMarketFormats) &&
  (S.floorBook.admitBatch postings).isSome &&
  S.seats.all (fun s => safeAt S.seatBook s.account s.proposal)

/-- Execute a checked turn on `UnifiedDeosSpine`, advancing `store` via `applyTurn` and `floorBook`
    via `FloorBook.admitBatch`. -/
def stepUnifiedTurn (S : UnifiedDeosSpine) (stateAssets : List String)
    (turn : VaultTurn) (postings : List TypedPosting) : Option UnifiedDeosSpine :=
  if checkUnifiedTurn S stateAssets turn postings then
    match S.floorBook.admitBatch postings with
    | some fb' =>
      some { S with
        store := applyTurn S.store turn
        floorBook := fb' }
    | none => none
  else
    none

/-- Any stale read pin (`(admitFootprint S.store turn.readPins).isOk = false`) deterministically
    refuses `stepUnifiedTurn`. -/
theorem stepUnifiedTurn_refuses_stale_pin
    (S : UnifiedDeosSpine) (stateAssets : List String)
    (turn : VaultTurn) (postings : List TypedPosting)
    (hStale : (admitFootprint S.store turn.readPins).isOk = false) :
    checkUnifiedTurn S stateAssets turn postings = false ∧
    stepUnifiedTurn S stateAssets turn postings = none := by
  have hchk : checkUnifiedTurn S stateAssets turn postings = false := by
    unfold checkUnifiedTurn
    rw [hStale]
    rfl
  refine ⟨hchk, ?_⟩
  unfold stepUnifiedTurn
  rw [hchk]
  rfl

/-! ## 3. Keystone Spine Theorems (Ledger, ZoE Seats, Escrow, Markets, Carry, Projection) -/

/-- Helper proving `realizeBatchOnReg` succeeds and produces `fb'` whenever `FloorBook.admitBatch` succeeds. -/
theorem realizeBatchOnReg_of_admitBatch
    (postings : List TypedPosting) (fb fb' : FloorBook) (g : Reg)
    (hadm : fb.admitBatch postings = some fb') :
    ∃ g' : Reg,
      realizeBatchOnReg (postings.map (fun p => (p, "unified-turn", "UnifiedDeos"))) fb g =
        some (fb', g') := by
  induction postings generalizing fb g with
  | nil =>
    cases hadm
    exact ⟨g, rfl⟩
  | cons p rest ih =>
    unfold FloorBook.admitBatch at hadm
    cases hp : fb.admitPosting p with
    | none => rw [hp] at hadm; cases hadm
    | some fb1 =>
      rw [hp] at hadm
      simp only [List.map_cons, realizeBatchOnReg, hp]
      exact ih fb1 (g.appendTypedPosting p "unified-turn" "UnifiedDeos" 1) hadm

/-- **Keystone 1 — Unified Ledger Conservation, Non-Issuer Floor Preservation & `Register.Reg` Bridge**:
    Whenever `stepUnifiedTurn S stateAssets turn postings = some S'` from a floor-valid `S.floorBook`:
    1. Per-asset algebraic sum is conserved across `S'.floorBook` (`S'.floorBook.assetSum ast = S.floorBook.assetSum ast`),
    2. `FloorsHold S'.floorBook` holds (every `user | seat | escrow | feePool` balance stays `≥ 0`),
    3. For any `Register.Reg` agreeing initially with `S.floorBook`, realizing `postings` on `reg`
       produces `reg'` agreeing identically with `S'.floorBook` on every `(AccountAddr, AssetId)`
       with non-negative balances on all non-issuer accounts,
    4. Every cell-state asset `ast ∈ stateAssets` is conserved across `turn.writeCells`,
    5. Every active ZoE `Seat` in `S'.seats` satisfies `safeAt`. -/
theorem unifiedDeos_ledger_and_turn_sound
    {S S' : UnifiedDeosSpine} {stateAssets : List String}
    {turn : VaultTurn} {postings : List TypedPosting}
    (hFloors : FloorsHold S.floorBook)
    (hStep : stepUnifiedTurn S stateAssets turn postings = some S') :
    (admitFootprint S.store turn.readPins).isOk = true ∧
    FloorsHold S'.floorBook ∧
    (∀ ast : AssetId, S'.floorBook.assetSum ast = S.floorBook.assetSum ast) ∧
    (∀ (reg : Reg),
      (∀ (addr : AccountAddr) (ast : AssetId),
        reg.accountBalance (addr.toRegAccount ast) = S.floorBook.balance addr ast) →
      ∃ reg' : Reg,
        realizeBatchOnReg (postings.map (fun p => (p, "unified-turn", "UnifiedDeos")))
          S.floorBook reg = some (S'.floorBook, reg') ∧
        (∀ (addr : AccountAddr) (ast : AssetId),
          reg'.accountBalance (addr.toRegAccount ast) = S'.floorBook.balance addr ast) ∧
        (∀ (addr : AccountAddr) (ast : AssetId), addr.kind ≠ AccountKind.issuerWell →
          0 ≤ reg'.accountBalance (addr.toRegAccount ast))) ∧
    (∀ ast ∈ stateAssets,
      (turn.writeCells.map (fun d => extractCellAssetBalance d.postState ast)).foldl (· + ·) 0 =
        (turn.writeCells.map (fun d => extractCellAssetBalance d.preState ast)).foldl (· + ·) 0) ∧
    (∀ s ∈ S'.seats, safeAt S'.seatBook s.account s.proposal = true) := by
  unfold stepUnifiedTurn at hStep
  cases hChk : checkUnifiedTurn S stateAssets turn postings with
  | false => simp [hChk] at hStep
  | true =>
    rw [hChk] at hStep
    simp only [↓reduceIte] at hStep
    cases hAdm : S.floorBook.admitBatch postings with
    | none => simp [hAdm] at hStep
    | some fb' =>
      rw [hAdm] at hStep
      injection hStep with hEq
      subst hEq
      unfold checkUnifiedTurn at hChk
      simp only [Bool.and_eq_true, List.all_eq_true] at hChk
      rcases hChk with ⟨⟨⟨⟨hFp, hStateBound⟩, _⟩, _⟩, hSeats⟩
      have hFlPres := FloorBook.admitBatch_preserves_floors postings hFloors hAdm
      refine ⟨hFp, hFlPres.1, hFlPres.2, ?_, ?_, hSeats⟩
      · intro reg hAgree
        obtain ⟨reg', hReal⟩ := realizeBatchOnReg_of_admitBatch postings S.floorBook fb' reg hAdm
        have ⟨hAg', _, hNonneg', _⟩ := realizeBatchOnReg_sound hFloors hAgree hReal
        exact ⟨reg', hReal, hAg', hNonneg'⟩
      · intro ast hMem
        exact (stateBoundTurn_conserves_actual_state_balances turn stateAssets ast hMem hStateBound).2

/-- **Keystone 2 — Full ZoE Offer Safety, Invitation Linearity, Gift Guard & SealedEscrow No-Theft**:
    Unifies the 4 economic safety guarantees on seats and escrows:
    1. Spending an `Invitation` once removes it so any second spend returns `none` (`no_double_redeem`),
    2. Zero-`want` proposals with `donate = false` are refused with `.donationUnmarked`,
    3. `exitSeat` sweeps EVERY asset in the universe (`exit_sweeps_all_assets`), leaving `0` on the seat,
    4. Every `EscrowReachable` state satisfies per-leg conservation and zero theft (`sealedescrow_no_theft`). -/
theorem unifiedDeos_zoe_and_escrow_safety
    {reg reg' : InvitationRegistry} {inv : Invitation} {invId : Nat}
    (hSpend : reg.spend invId = some (reg', inv))
    (b : Book) (offerer payee seatAcc : AccountId)
    (hProt : protectedBase ≤ seatAcc) (hDiff : payee ≠ seatAcc)
    (pGift : Proposal) (hWant0 : pGift.wantsNothing = true) (hDonFalse : pGift.donate = false)
    (bExit : Book) (sExit : Seat)
    (hNonneg : ∀ ast : AssetId, 0 ≤ bExit.balance sExit.account ast)
    (stEsc : EscrowState) (hEsc : EscrowReachable stEsc) :
    reg'.spend invId = none ∧
    admitOffer reg b invId offerer payee seatAcc hProt hDiff pGift = .error .donationUnmarked ∧
    ((∀ ast : AssetId, (exitSeat bExit sExit).balance sExit.account ast = 0) ∧
     (∀ ast : AssetId, (exitSeat bExit sExit).balance sExit.payee ast =
       bExit.balance sExit.payee ast + bExit.balance sExit.account ast) ∧
     (∀ ast : AssetId, (exitSeat bExit sExit).globalAssetSum ast = bExit.globalAssetSum ast)) ∧
    ((∀ side, stEsc.paid side + locked stEsc side = entered stEsc side) ∧
     (∀ side, stEsc.status side = .empty → stEsc.recv side = 0)) :=
  ⟨InvitationRegistry.no_double_redeem hSpend,
   admitOffer_donationUnmarked_refused reg b invId offerer payee seatAcc hProt hDiff pGift hWant0 hDonFalse,
   exit_sweeps_all_assets bExit sExit hNonneg,
   sealedescrow_no_theft stEsc hEsc⟩

/-- **Keystone 3 — Unified Markets (`drex-clearing@1`, `netting@1`, `dclutch-hoard-clearing@1`)**:
    1. Every accepted `drexClearingJudge` batch satisfies `ClearingSemanticMeaning` (duplicate-free
       accounts + universal LP ε-optimality over all feasible circulations),
    2. Multilateral `netting@1` (`nettingJudge`) conserves net exposure (`net_conserves`), cancels
       symmetric cycles to zero (`symmetric_obligations_net_zero`), bounds residual gross exposure
       (`net_reduces_gross_exposure`), agrees on `Book` with gross settlement
       (`settleNetting_agrees_with_gross`), and compiles to balanced `Register.Movement`s,
    3. Every accepted `dclutchHoardJudge` batch preserves `HoardCollateralInvariant` and simplex
       unit-sum KKT funding (`DclutchHoardMeaning`). -/
theorem unifiedDeos_markets_sound
    (grade : Nat)
    (qClear : ClearingQuery) (cClear : Certificate)
    (hClear : drexClearingJudge.check grade qClear cClear = .ok)
    (qNet : NettingQuery) (cNet : NettingCert)
    (hNet : nettingJudge.check grade qNet cNet = .ok)
    (sHoard : HoardMarketState) (cHoard : JointClearingCert)
    (hHoard : dclutchHoardJudge.check grade sHoard cHoard = .ok) :
    ClearingSemanticMeaning qClear cClear ∧
    NettingSpec qNet cNet ∧
    grossExposure cNet.netTransfers ≤ grossExposure qNet.grossObligations ∧
    (∀ acc ast, netPosition cNet.netTransfers acc ast = netPosition qNet.grossObligations acc ast) ∧
    (∀ b : Book, ∀ acc ast,
      (settleObligations b cNet.netTransfers).balance acc ast =
        (settleObligations b qNet.grossObligations).balance acc ast) ∧
    (cNet.toMovements.map (·.debit)).sum = (cNet.toMovements.map (·.credit)).sum ∧
    DclutchHoardMeaning sHoard cHoard := by
  have hClearM : ClearingSemanticMeaning qClear cClear :=
    drexClearingJudge.sound hClear
  have hNetM : NettingSpec qNet cNet :=
    nettingJudge.sound hNet
  have hHoardM : DclutchHoardMeaning sHoard cHoard :=
    dclutchHoardJudge.sound hHoard
  exact ⟨hClearM,
         hNetM,
         net_reduces_gross_exposure hNetM,
         (net_conserves hNetM).1,
         fun b => (settleNetting_agrees_with_gross b hNetM).1,
         cNet.toMovements_balanced,
         hHoardM⟩

/-- **Keystone 4 — Checked Carry, Title Non-Narrowing, `Reasons` Mandates & Blinded MultiProofs**:
    1. Admissible `CheckedCarry.Plan`s forbid silent cell drops (`Plan.no_drop_at`), `Replay.World`
       rerooting preserves `AdmissibleCarry`, and `Grants.revoke` refuses carried authority,
    2. Copied title grants fail semantic narrowing (`TitleMigration.copied_title_grant_not_semantic_narrowing`)
       while explicit translation preserves `NoNewMeaning`,
    3. `Mandate.delegate` conserves budget (`delegate_conserves`), attenuates authority, and
       enforces `w.reasons.status because = .supported` when gated by `worldReasonsCaveat w because`. -/
theorem unifiedDeos_carry_and_mandate_sound
    {source : List Cell} {rel : Cell → Cell → Prop}
    (P : CheckedCarry.Plan source rel) (hNoDrops : NoDrops P)
    (w : Obend.Vault.Replay.World) (g₁ s₁ g₂ s₂ : ByteArray) (req : CarryRequest)
    (parent : Mandate) (childId : Nat) (childP : Principal)
    (reqRights : List Mandate.Auth) (quota : Nat) (mask : List Nat) (term : Nat) (because : String) :
    (∀ i : Fin source.length, ∃ next ∈ P.outputs, rel source[i] next) ∧
    (AdmissibleCarry (worldAuthState w g₁ s₁) req ↔ AdmissibleCarry (worldAuthState w g₂ s₂) req) ∧
    ¬ AdmissibleCarry (worldAuthState { w with grants := w.grants.revoke req.grantId } g₁ s₁) req ∧
    ¬ TitleMigration.NoNewMeaning TitleMigration.oldGrant TitleMigration.copiedGrant ∧
    TitleMigration.NoNewMeaning TitleMigration.oldGrant TitleMigration.correctGrant ∧
    (let (parentAfter, child) :=
       parent.delegate childId childP reqRights quota mask term (worldReasonsCaveat w because)
     parentAfter.budget + child.budget = parent.budget ∧
     attenuates child parent ∧
     (∀ inv : Invocation, authorizedBy child inv = true → w.reasons.status because = .supported)) := by
  refine ⟨P.noDrops_maps_all_cells hNoDrops,
          worldAuthState_reroot_admissible_iff w g₁ s₁ g₂ s₂ req,
          world_revoke_refuses_carry w g₁ s₁ req,
          TitleMigration.copied_title_grant_not_semantic_narrowing,
          TitleMigration.translated_title_grant_preserves_meaning,
          ?_⟩
  dsimp only
  refine ⟨delegate_conserves parent childId childP reqRights quota mask term (worldReasonsCaveat w because),
          delegate_child_attenuates parent childId childP reqRights quota mask term (worldReasonsCaveat w because),
          ?_⟩
  intro inv hAuth
  unfold authorizedBy at hAuth
  simp only [Bool.and_eq_true] at hAuth
  have hCv : ((parent.delegate childId childP reqRights quota mask term
      (worldReasonsCaveat w because)).2.caveat).admits inv.method = true := hAuth.2
  simp only [Mandate.delegate, Caveat.and, Bool.and_eq_true] at hCv
  exact (reasonsCaveat_admits_iff w.reasons because inv.method).mp hCv.2

/-! ## 4. Durable WAL Crash-Recovery & Simplex Finality Spine -/

/-- A single WAL-persisted `SimplexProtocol` notarization vote in `view` for `chain`. -/
structure JournaledSimplexVote where
  view  : Nat
  chain : Chain
  deriving DecidableEq

/-- Volatile in-memory Simplex voter cache reconstructed from `journaledVotes`. -/
structure VolatileSimplexVoter where
  self     : NodeId
  deadline : Nat
  votes    : List JournaledSimplexVote := []
  deriving DecidableEq

/-- Check whether `st` has already cast a vote in `view = v`. -/
def hasVotedSimplexView (st : VolatileSimplexVoter) (v : Nat) : Bool :=
  st.votes.any (fun jv => jv.view == v)

/-- Attempt to cast a Simplex vote in `view = v` for `c`: strictly idempotent / anti-equivocating
    whenever `hasVotedSimplexView st v = true`. -/
def castSimplexVote (st : VolatileSimplexVoter) (v : Nat) (c : Chain) : VolatileSimplexVoter :=
  if hasVotedSimplexView st v then
    st
  else
    { st with votes := ⟨v, c⟩ :: st.votes }

/-- Durable WAL-backed Simplex replica host: persists `journaledVotes` across crashes while
    `volatileState` is lost on crash and reconstructed deterministically upon recovery. -/
structure DurableSimplexHost where
  self           : NodeId
  deadline       : Nat
  journaledVotes : List JournaledSimplexVote
  volatileState  : Option VolatileSimplexVoter
  deriving DecidableEq

/-- Cast a Simplex vote only after journaling the updated `votes` to the durable WAL. -/
def durableCastVote (host : DurableSimplexHost) (v : Nat) (c : Chain) :
    Option DurableSimplexHost :=
  match host.volatileState with
  | none => none
  | some st =>
    let st' := castSimplexVote st v c
    some { host with
      journaledVotes := st'.votes
      volatileState  := some st' }

/-- Crash wipes `volatileState` while preserving `journaledVotes`. -/
def crashSimplexHost (host : DurableSimplexHost) : DurableSimplexHost :=
  { host with volatileState := none }

/-- Recovery reconstructs `volatileState` strictly from the durable WAL `journaledVotes`. -/
def recoverSimplexHost (host : DurableSimplexHost) : DurableSimplexHost :=
  { host with
    volatileState := some {
      self     := host.self
      deadline := host.deadline
      votes    := host.journaledVotes
    } }

/-- **Durable WAL Anti-Equivocation (`durable_recovery_prevents_equivocation`)**:
    After crashing and recovering, any view `v` recorded in `host.journaledVotes`
    rejects conflicting `castSimplexVote` attempts (`castSimplexVote restored v c' = restored`). -/
theorem durable_recovery_prevents_equivocation
    (host : DurableSimplexHost) (v : Nat) (c' : Chain)
    (hv_voted : host.journaledVotes.any (fun jv => jv.view == v) = true) :
    let restored : VolatileSimplexVoter :=
      { self := host.self, deadline := host.deadline, votes := host.journaledVotes }
    (recoverSimplexHost (crashSimplexHost host)).volatileState = some restored ∧
    hasVotedSimplexView restored v = true ∧
    castSimplexVote restored v c' = restored := by
  intro restored
  have hv : hasVotedSimplexView restored v = true := hv_voted
  refine ⟨rfl, hv, ?_⟩
  unfold castSimplexVote
  simp [hv]

/-- **Durable Outbox Linearizability Across Crashes (`durable_expose_once_across_crashes`)**:
    Once effect `n` is exposed on `Run.Durable.hstep`, any non-empty sequence of `extraCrashes + 1`
    crash events followed by `.recover` preserves `n ∈ s_rec.outbox`, keeps `n ∉ pending L s_rec`,
    and refuses duplicate externalization with `.error (.exposed n)`. -/
theorem durable_expose_once_across_crashes
    {Ix : Type} {S : Obend.Slot.Protocol.Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Obend.Run.Shared.Ledger ι W Tok)
    (base : W → Obend.Slot.Protocol.View Tok Fact)
    (sp : ι → Obend.Slot.Protocol.Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s s₁ : DState L S Hole A P Cred Cand Fact Ob i₀)
    (n extraCrashes : Nat)
    (h_exp : hstep L base sp au k J₀ s (.expose n) = .ok s₁) :
    let trace : List (HEvent L S Hole A P Cred Cand Fact) :=
      List.replicate (extraCrashes + 1) .crash ++ [.recover]
    let s_rec := runDurableTrace L base sp au k J₀ s₁ trace
    n ∈ s_rec.outbox ∧
    n ∉ pending L s_rec ∧
    hstep L base sp au k J₀ s_rec (.expose n) = .error (.exposed n) := by
  intro trace s_rec
  have h_pend := pending_decreases_on_expose L base sp au k J₀ s s₁ n h_exp
  have h_idem := crash_recover_idempotent L base sp au k J₀ s₁ (extraCrashes + 1) (by omega)
  have h_j_rec : s_rec.journal = s₁.journal := h_idem.2.1
  have h_o_rec : s_rec.outbox = s₁.outbox := h_idem.2.2
  have h_in_s1 : n ∈ s₁.outbox := by
    rw [h_pend.2.2.1]
    exact List.mem_append_right _ (List.Mem.head _)
  have h_in_rec : n ∈ s_rec.outbox := h_o_rec ▸ h_in_s1
  have h_pend_eq : pending L s_rec = pending L s₁ := by
    unfold pending
    rw [h_j_rec, h_o_rec]
  have h_not_pend : n ∉ pending L s_rec := h_pend_eq ▸ h_pend.2.2.2.2.1
  have h_disp : ∃ i o, s.journal[n]? = some (.dispatch i o) := by
    simp only [hstep] at h_exp
    split at h_exp
    · rename_i i o hio
      exact ⟨i, o, hio⟩
    · cases h_exp
  obtain ⟨i, o, hio⟩ := h_disp
  have h_refused : hstep L base sp au k J₀ s_rec (.expose n) = .error (.exposed n) := by
    simp [hstep, h_j_rec, h_pend.1, hio, h_in_rec]
  exact ⟨h_in_rec, h_not_pend, h_refused⟩

/-- **Keystone 5 — Disjoint Fast-Path Commutativity & Simplex Trace Finality (`UnifiedDeos`)**:
    1. Bernstein-disjoint `VaultTurn`s commute on `VaultStore`, remain mutually `ValidAt` in both
       orders, and yield identical collapsed Merkle roots,
    2. An accepted `simplexTraceJudge` trace `(P, tr)` guarantees `Reach P tr.reverse`,
       under which any two `.quorum_final` `SimplexFinalityGate` promotions at the same chain height
       certify identical block sequences AND identical `chainDigest` values, and `.collapsed` binds
       the exact SP 800-185 `cshake256Bytes` fold of `(chainDigest || vaultRoot)`. -/
theorem unifiedDeos_fastpath_and_simplex_finality_sound
    (H : Obend.Digest.HashBytes.Hash) (schema : List String) (val : Obend.Fold.Collapse.StoreValuation)
    (store₀ : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option Obend.Law.CellContract)
    (formats : List Format)
    (hDisj : DisjointTurns T₁ T₂)
    (hValid₁ : ValidAt store₀ T₁ contracts formats)
    (hValid₂ : ValidAt store₀ T₂ contracts formats)
    (grade : Nat) (P : Protocol) (tr : List Msg)
    (hTrace : simplexTraceJudge.check grade P tr = .ok) :
    ValidAt (applyTurn store₀ T₁) T₂ contracts formats ∧
    ValidAt (applyTurn store₀ T₂) T₁ contracts formats ∧
    applyTurn (applyTurn store₀ T₁) T₂ = applyTurn (applyTurn store₀ T₂) T₁ ∧
    Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₁) T₂) =
      Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₂) T₁) ∧
    Reach P tr.reverse ∧
    (∀ (g₁ g₁' g₂ g₂' : SimplexFinalityGate) (cert₁ cert₂ : FinCert) (d₁ d₂ : ByteArray),
      advanceSimplexGate P tr.reverse g₁ (.finalizeWithCert cert₁ d₁) = some g₁' →
      advanceSimplexGate P tr.reverse g₂ (.finalizeWithCert cert₂ d₂) = some g₂' →
      cert₁.chain.height = cert₂.chain.height →
      cert₁.chain.blocks = cert₂.chain.blocks ∧
      chainDigest cert₁.chain = chainDigest cert₂.chain) ∧
    (∀ (g g' : SimplexFinalityGate) (vRoot : ByteArray),
      advanceSimplexGate P tr.reverse g (.collapseArchive vRoot) = some g' →
      ∃ cert : FinCert,
        g.finCert = some cert ∧
        g'.currentTier = .collapsed ∧
        (foldCollapsedRoot (chainDigest cert.chain) vRoot).data.toList =
          Obend.Digest.Cshake256.cshake256Bytes collapseRootDomain.data.toList
            ((chainDigest cert.chain).data.toList ++ vRoot.data.toList)) := by
  have hBoth := disjoint_both_orders store₀ T₁ T₂ contracts formats hDisj hValid₁ hValid₂
  have hComm := vaultTurn_disjoint_commutes store₀ T₁ T₂ hDisj
  have hRoot :
      Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₁) T₂) =
        Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₂) T₁) := by
    rw [hComm]
  have hReach : Reach P tr.reverse :=
    simplexTraceJudge.sound hTrace
  refine ⟨hBoth.1, hBoth.2, hComm, hRoot, hReach, ?_, ?_⟩
  · intro g₁ g₁' g₂ g₂' cert₁ cert₂ d₁ d₂ hAdv₁ hAdv₂ hHeight
    exact quorum_final_gates_unique_per_height hReach hAdv₁ hAdv₂ hHeight
  · intro g g' vRoot hCol
    rcases advanceSimplexGate_collapsed_binds_cshake P tr.reverse g g' vRoot hCol with
      ⟨cert, hCert, hTier, _, hSpec⟩
    exact ⟨cert, hCert, hTier, hSpec⟩

end Obend.Vault.UnifiedDeos
end
