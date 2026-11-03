module
/-
# Obend.Vault.SovereignEngine — Unified Sovereign Execution Engine (Pillar 5A)

Welds the remediated in-place Sovereign Consensus & Metasystem stack into a single end-to-end
state transition machine:
1. `DeployedGrainContract`: Bundles `ElaboratedIsarCert`, goal-bound `preservesCert` and
   `stepSoundCert` (verified via in-place `Obend.Law.checkContractCert`), `TableDfa` `oraclePolicy`,
   and compiled `Grain` bytecode `grainProg` (`compilePolicyToGrainProg`).
2. `ZkOracleFactEnvelope` & `verifyZkOracleEnvelope`: Welds `"tlsn-transcript-policy@1"` selective-
   disclosure verification (`verifyTlsnTranscriptPolicy` + `checkTurnWitness`) with deterministic
   `Grain` VM evaluation (`evalGrainProg`).
3. `SovereignIntent`: Welds `Mandate` + `Invocation` (`checkInvocation`), 3D `ReactiveAffordance`
   (`reactiveOK`), ZoE `Seat` (`safeAt`), and `Clearing.Order`.
4. `ContendedClearingBatch`: Welds `Clearing.Market` + `Clearing.Certificate` (`drexClearingJudge`),
   multi-seat `BatchRealloc`, and `DragonsExchangeEpochInput` (`stepDragonsExchangeEpoch`).
5. `SovereignWorldState`, `SovereignTransaction`, and `stepSovereignEngine` (using in-place
   witness-bound `Vault.ValidAt` and in-place metadata-bound `Projection.projectVault`).
6. The 3 Master Compositional Theorems:
   - `sovereignEngine_step_conserves_all_assets`
   - `sovereignEngine_enforces_zoe_and_mandates`
   - `sovereignEngine_blinded_view_non_forgeable`
-/
public import Obend.Core.Term
public import Obend.Core.Data
public import Obend.Spec.Elaborate
public import Obend.Law.Contract
public import Obend.Judge.TranscriptPolicy
public import Obend.Judge.Clearing
public import Obend.Judge.Lrat
public import Obend.Lower.PolicyToGrain
public import Obend.Ledger.Book
public import Obend.Ledger.Seat
public import Obend.Vault.Hyperedge
public import Obend.Vault.Projection
public import Obend.Vault.Mandate
public import Obend.Vault.Rehydration
public import Obend.Vault.DragonsExchange
public import Obend.Tactic.Tooth

@[expose] public section
namespace Obend.Vault

open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Spec.Elaborate (ElaboratedIsarCert)
open Obend.Law (ContractGoal ContractCert CertVerdict CellContract Holds Admits checkContractCert)
open Obend.Judge (TableDfa dfaAccepts TlsnTranscriptQuery TlsnTranscriptCert
  verifyTlsnTranscriptPolicy tlsnTranscriptFormat Market Order Certificate ClearingQuery
  drexClearingJudge)
open Obend.Lower (GrainInstr compilePolicyToGrainProg evalGrainProg compilePolicyToGrainProg_sound)
open Obend.Ledger (AccountId AssetId Book ResourcePosting Seat safeAt payoutPostings
  applyPostings applyPostings_conserves BatchRealloc applyBatchRealloc)
open Obend.Vault.Projection (VaultCell ProjectedCell BlindedOpening cellBlind projectCell
  projectVault vaultCommits projectedMerkleRoot projectedMerkleRoot_eq_vaultRoot
  mkBlindedOpening verifyBlindedOpening verify_blinded_opening_complete
  tampered_metadata_opening_refused)
open Obend.Vault.Rehydration (ReactiveAffordance reactiveOK reactiveOK_iff inWindow_iff
  authOfMandateAuth)
open Obend.Digest.HashBytes (Hash Collision)
open Obend.Receipt.Merkle (Bounded mapRoot)

set_option autoImplicit false

/-! ## 1. Deployed Grain Contract (`DeployedGrainContract`) -/

/-- A deployed sovereign contract bundling its elaborated Isar proof certificate, goal-bound
    4-tier invariant/step certificates, DFA oracle policy, and compiled Grain bytecode. -/
structure DeployedGrainContract where
  contractId    : String
  isarCert      : ElaboratedIsarCert
  law           : Term
  invariant     : Term
  stepRel       : Term
  preservesCert : ContractCert
  stepSoundCert : ContractCert
  oraclePolicy  : TableDfa
  maxTokens     : Nat
  grainProg     : List GrainInstr

/-- Executable well-formedness check for a `DeployedGrainContract` using in-place `checkContractCert`. -/
def DeployedGrainContract.wellFormedB (c : DeployedGrainContract) : Bool :=
  c.isarCert.scriptValid &&
  (checkContractCert (.preserves c.law c.invariant) c.preservesCert == .valid) &&
  (checkContractCert (.stepSound c.law c.invariant c.stepRel) c.stepSoundCert == .valid) &&
  (c.grainProg == compilePolicyToGrainProg c.oraclePolicy c.maxTokens)

/-- Proposition that a `DeployedGrainContract` is well-formed. -/
def DeployedGrainContract.WellFormed (c : DeployedGrainContract) : Prop :=
  c.wellFormedB = true

/-- Any well-formed `DeployedGrainContract` has verified `.preserves` and `.stepSound` certificates
    and evaluates its compiled `grainProg` identically to `dfaAccepts c.oraclePolicy`. -/
theorem DeployedGrainContract.wellFormed_sound (c : DeployedGrainContract)
    (h : c.WellFormed) (tokens : List String) :
    c.isarCert.scriptValid = true ∧
    checkContractCert (.preserves c.law c.invariant) c.preservesCert = .valid ∧
    checkContractCert (.stepSound c.law c.invariant c.stepRel) c.stepSoundCert = .valid ∧
    evalGrainProg c.grainProg tokens = some (dfaAccepts c.oraclePolicy tokens) := by
  unfold DeployedGrainContract.WellFormed DeployedGrainContract.wellFormedB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h_isar, h_pres⟩, h_step⟩, h_prog⟩ := h
  refine ⟨h_isar, h_pres, h_step, ?_⟩
  rw [h_prog]
  exact compilePolicyToGrainProg_sound c.oraclePolicy c.maxTokens tokens

/-! ## 2. ZK Oracle Fact Envelope (`ZkOracleFactEnvelope` & `verifyZkOracleEnvelope`) -/

/-- Attested TLSNotary selective-disclosure oracle envelope paired with its turn witness
    and extracted token stream for Grain bytecode policy evaluation. -/
structure ZkOracleFactEnvelope where
  contractId      : String
  tlsnQuery       : TlsnTranscriptQuery
  tlsnCert        : TlsnTranscriptCert
  turnWitness     : TurnWitness
  extractedTokens : List String
  deriving Repr

/-- Verify a `ZkOracleFactEnvelope` against a `DeployedGrainContract`:
    1. Contract identifier matches,
    2. `"tlsn-transcript-policy@1"` judge accepts `(tlsnQuery, tlsnCert)` and `turnWitness`,
    3. `evalGrainProg c.grainProg env.extractedTokens` halts with `some true`. -/
def verifyZkOracleEnvelope (c : DeployedGrainContract) (env : ZkOracleFactEnvelope) : Bool :=
  (c.contractId == env.contractId) &&
  (verifyTlsnTranscriptPolicy env.tlsnQuery env.tlsnCert == .ok) &&
  checkTurnWitness [tlsnTranscriptFormat] env.turnWitness &&
  (evalGrainProg c.grainProg env.extractedTokens == some true)

theorem verifyZkOracleEnvelope_sound (c : DeployedGrainContract) (env : ZkOracleFactEnvelope)
    (h_wf : c.WellFormed) (h_ver : verifyZkOracleEnvelope c env = true) :
    c.contractId = env.contractId ∧
    verifyTlsnTranscriptPolicy env.tlsnQuery env.tlsnCert = .ok ∧
    checkTurnWitness [tlsnTranscriptFormat] env.turnWitness = true ∧
    dfaAccepts c.oraclePolicy env.extractedTokens = true := by
  unfold verifyZkOracleEnvelope at h_ver
  simp only [Bool.and_eq_true, beq_iff_eq] at h_ver
  obtain ⟨⟨⟨h_id, h_tlsn⟩, h_wit⟩, h_grain⟩ := h_ver
  have ⟨_, _, _, h_eval⟩ := c.wellFormed_sound h_wf env.extractedTokens
  rw [h_eval] at h_grain
  injection h_grain with h_dfa
  exact ⟨h_id, h_tlsn, h_wit, h_dfa⟩

/-! ## 3. Sovereign Intent (`SovereignIntent`) -/

/-- Check that a posting's source and destination are registered in `ledger.accounts`. -/
def bookPostingValid (ledger : Book) (p : ResourcePosting) : Bool :=
  ledger.accounts.contains p.source && ledger.accounts.contains p.destination

/-- Check that a seat satisfies `safeAt` in `ledger`. -/
def seatSafeInBook (ledger : Book) (s : Seat) : Bool :=
  safeAt ledger s.account s.proposal

/-- User/agent intent combining a capability `Mandate`, `Invocation`, 3D `ReactiveAffordance`,
    ZoE `Seat`, and clearing `Order`. -/
structure SovereignIntent where
  intentId           : String
  mandate            : Obend.Vault.Mandate.Mandate
  invocation         : Obend.Vault.Mandate.Invocation
  reactiveAffordance : ReactiveAffordance Data
  preState           : Data
  postState          : Data
  seat               : Seat
  order              : Order
  escrowPostings     : List ResourcePosting

/-- Executable admissibility check for a `SovereignIntent` at `height` and `ledger`. -/
def SovereignIntent.admissibleB (ledger : Book) (height : Nat) (intent : SovereignIntent) : Bool :=
  Obend.Vault.Mandate.checkInvocation intent.mandate intent.invocation &&
  reactiveOK intent.reactiveAffordance (intent.mandate.rights.map authOfMandateAuth)
    height intent.preState intent.postState &&
  intent.escrowPostings.all (bookPostingValid ledger) &&
  safeAt (applyPostings ledger intent.escrowPostings) intent.seat.account intent.seat.proposal

/-! ## 4. Contended Clearing Batch (`ContendedClearingBatch`) -/

/-- Contended batch settlement combining `Clearing.Market`, `Clearing.Certificate`,
    multi-seat `BatchRealloc`, and `DragonsExchangeEpochInput`. -/
structure ContendedClearingBatch where
  market       : Market
  orders       : List Order
  clearingCert : Certificate
  batchRealloc : BatchRealloc
  dragonsInput : DragonsExchangeEpochInput
  deriving DecidableEq, Repr

/-- Boolean wrapper for `drexClearingJudge.check`. -/
def checkClearingBatchOk (q : ClearingQuery) (cert : Certificate) : Bool :=
  match drexClearingJudge.check 0 q cert with
  | .ok => true
  | _ => false

/-- Executable admissibility check for a `ContendedClearingBatch`. -/
def ContendedClearingBatch.admissibleB (ledger : Book) (seats : List Seat)
    (dragons : DragonsExchangeState) (batch : ContendedClearingBatch) : Bool :=
  let q : ClearingQuery := {
    market := batch.market
    orders := batch.orders
    transfers := batch.batchRealloc.postings
  }
  checkClearingBatchOk q batch.clearingCert &&
  batch.batchRealloc.postings.all (bookPostingValid ledger) &&
  seats.all (seatSafeInBook (applyBatchRealloc ledger batch.batchRealloc)) &&
  (stepDragonsExchangeEpoch dragons batch.dragonsInput).isSome

/-! ## 5. Sovereign World State, Transactions & Engine Step -/

/-- Complete state of the Unified Sovereign Execution Engine. -/
structure SovereignWorldState where
  height     : Nat
  store      : VaultStore
  vaultCells : List VaultCell
  contracts  : List DeployedGrainContract
  ledger     : Book
  seats      : List Seat
  dragons    : DragonsExchangeState
  assets     : List AssetId

/-- Project the world's `vaultCells` for viewer `v` using in-place metadata-bound `projectVault`. -/
def SovereignWorldState.projectForViewer (H : Hash)
    (W : SovereignWorldState) (v : List Obend.Vault.Projection.Auth) : List ProjectedCell :=
  projectVault H v W.vaultCells

/-- Compute the viewer-projected Merkle root over `W.vaultCells`. -/
def SovereignWorldState.merkleRoot (H : Hash)
    (W : SovereignWorldState) (v : List Obend.Vault.Projection.Auth) : Nat :=
  projectedMerkleRoot H v W.vaultCells

/-- Transactions executed by the Sovereign Engine. -/
inductive SovereignTransaction where
  /-- Deploy a verified `DeployedGrainContract`. -/
  | deployContract (contract : DeployedGrainContract)
  /-- Execute an oracle-gated `VaultTurn` and conserved ledger postings. -/
  | executeOracleTurn (contractId : String) (envelope : ZkOracleFactEnvelope)
      (turn : VaultTurn) (postings : List ResourcePosting)
  /-- Lock a `SovereignIntent` into a ZoE `Seat` after verifying its `Mandate` and 3D `ReactiveAffordance`. -/
  | lockIntentSeat (intent : SovereignIntent)
  /-- Settle a contended clearing batch across `drexClearingJudge`, `BatchRealloc`, and `DragonsExchange`. -/
  | settleContendedBatch (batch : ContendedClearingBatch)
  /-- Exit an active ZoE `Seat` and refund its full allocation to `s.payee`. -/
  | exitSeat (seatAccount : AccountId)

/-- Default registered judge formats for `stepSovereignEngine` turn witness verification. -/
def sovereignJudgeFormats : List Obend.Judge.Format :=
  [tlsnTranscriptFormat, Obend.Judge.Lrat.format]

/-- Executable admissibility check for `.exitSeat` on `s`. -/
def exitSeatAdmissibleB (W : SovereignWorldState) (s : Seat) (seatAcc : AccountId) : Bool :=
  let postings := payoutPostings W.ledger s.account s.payee W.assets
  let ledger' := applyPostings W.ledger postings
  let seats' := W.seats.filter (fun x => x.account != seatAcc)
  postings.all (bookPostingValid W.ledger) &&
  seats'.all (seatSafeInBook ledger') &&
  W.assets.all (fun a => ledger'.balance s.account a == 0)

/-- Executable conservation and duplicate-free cell check for `turn : VaultTurn`. -/
def VaultTurn.conservedB (turn : VaultTurn) : Bool :=
  let assets := ("balance" :: (turn.writeCells.flatMap fun d => d.halfEdges.map Prod.fst)).eraseDups
  assets.all (fun a => sumAssetDelta turn.writeCells a == 0) &&
  (checkNodupCells (turn.writeCells.map CellDelta.cell)).isOk

/-- Executable turn gate (`checkOracleTurnValidAt`) enforcing:
    1. `(admitFootprint W.store turn.readPins).isOk` (no stale read pins / TOCTOU),
    2. `turn.conservedB` (value conservation across `turn.writeCells` and duplicate-free cell deltas),
    3. Every written cell delta `d ∈ turn.writeCells` has its `preState` present in `W.store`, and
    4. Every written cell delta satisfies the deployed contracts' `invariant`, `law`, and `stepRel`. -/
def checkOracleTurnValidAt (W : SovereignWorldState) (turn : VaultTurn) : Bool :=
  (admitFootprint W.store turn.readPins).isOk &&
  turn.conservedB &&
  turn.writeCells.all fun d =>
    let preOk :=
      match W.store d.cell with
      | some cur => Obend.Law.termEq cur.term d.preState.term
      | none => false
    let req := turnRequest turn.turnId turn.occasion d.cell
    let contractsOk :=
      W.contracts.all fun c =>
        Obend.Law.evalHoldsBounded c.invariant d.preState &&
        Obend.Law.evalHoldsBounded c.invariant d.postState &&
        Obend.Law.evalAdmitsBounded c.law d.preState d.postState req &&
        Obend.Law.evalAdmitsBounded c.stepRel d.preState d.postState req
    preOk && contractsOk

/-- **Unified Sovereign Execution Engine Step (`stepSovereignEngine`)**. -/
def stepSovereignEngine (W : SovereignWorldState) (tx : SovereignTransaction) :
    Option SovereignWorldState :=
  if !decide W.ledger.accounts.Nodup then
    none
  else
    match tx with
    | .deployContract c =>
      if c.wellFormedB && W.seats.all (seatSafeInBook W.ledger) then
        some { W with height := W.height + 1, contracts := c :: W.contracts }
      else
        none
    | .executeOracleTurn cid env turn postings =>
      match W.contracts.find? (fun c => c.contractId == cid) with
      | none => none
      | some c =>
        let ledger' := applyPostings W.ledger postings
        if c.wellFormedB &&
           verifyZkOracleEnvelope c env &&
           checkOracleTurnValidAt W turn &&
           turn.witnesses.all (checkTurnWitness sovereignJudgeFormats) &&
           postings.all (bookPostingValid W.ledger) &&
           W.seats.all (seatSafeInBook ledger') then
          some { W with
            height := W.height + 1
            store  := applyTurn W.store turn
            ledger := ledger' }
        else
          none
    | .lockIntentSeat intent =>
      let ledger' := applyPostings W.ledger intent.escrowPostings
      if intent.admissibleB W.ledger W.height &&
         W.seats.all (seatSafeInBook ledger') then
        some { W with
          height := W.height + 1
          ledger := ledger'
          seats  := intent.seat :: W.seats }
      else
        none
    | .settleContendedBatch batch =>
      if batch.admissibleB W.ledger W.seats W.dragons then
        match stepDragonsExchangeEpoch W.dragons batch.dragonsInput with
        | some dragons' =>
          some { W with
            height  := W.height + 1
            ledger  := applyBatchRealloc W.ledger batch.batchRealloc
            dragons := dragons' }
        | none => none
      else
        none
    | .exitSeat seatAcc =>
      match W.seats.find? (fun s => s.account == seatAcc) with
      | none => none
      | some s =>
        if exitSeatAdmissibleB W s seatAcc then
          some { W with
            height := W.height + 1
            ledger := applyPostings W.ledger (payoutPostings W.ledger s.account s.payee W.assets)
            seats  := W.seats.filter (fun x => x.account != seatAcc) }
        else
          none

/-! ## 6. The 3 Master Compositional Theorems -/

theorem postings_conserve_of_bookPostingValid {b : Book} {ps : List ResourcePosting}
    (h_nodup : b.accounts.Nodup)
    (h_valid : ps.all (bookPostingValid b) = true) (a : AssetId) :
    (applyPostings b ps).totalAsset a = b.totalAsset a := by
  apply applyPostings_conserves
  · intro p hp
    have hp_ok := List.all_eq_true.mp h_valid p hp
    unfold bookPostingValid at hp_ok
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hp_ok
    exact hp_ok
  · exact h_nodup

/-- **Master Theorem 1 (`sovereignEngine_step_conserves_all_assets`)**:
    Every admitted transition `stepSovereignEngine W tx = some W'` strictly conserves
    total book balance across all assets `a : AssetId` (`W'.ledger.totalAsset a = W.ledger.totalAsset a`),
    and preserves the Dragon's Exchange full-collateralization & credit-ring solvency invariant
    while conserving net credit-ring balances (`W'.dragons.balances = W.dragons.balances`). -/
theorem sovereignEngine_step_conserves_all_assets
    (W W' : SovereignWorldState) (tx : SovereignTransaction)
    (h_step : stepSovereignEngine W tx = some W') :
    (∀ a : AssetId, W'.ledger.totalAsset a = W.ledger.totalAsset a) ∧
    (DragonsExchangeInvariant W.dragons →
      DragonsExchangeInvariant W'.dragons ∧ W'.dragons.balances = W.dragons.balances) := by
  cases tx with
  | deployContract c =>
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · cases h_cond : (c.wellFormedB && W.seats.all (seatSafeInBook W.ledger))
      · simp [h_nd, h_cond] at h_step
      · simp [h_nd, h_cond] at h_step
        subst h_step
        exact ⟨fun _ => rfl, fun h_inv => ⟨h_inv, rfl⟩⟩
  | executeOracleTurn cid env turn postings =>
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · have h_nodup : W.ledger.accounts.Nodup := of_decide_eq_true h_nd
      cases h_find : W.contracts.find? (fun c => c.contractId == cid) with
      | none => simp [h_nd, h_find] at h_step
      | some c =>
        simp only [h_nd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h_find] at h_step
        cases h_cond : (c.wellFormedB &&
            verifyZkOracleEnvelope c env &&
            checkOracleTurnValidAt W turn &&
            turn.witnesses.all (checkTurnWitness sovereignJudgeFormats) &&
            postings.all (bookPostingValid W.ledger) &&
            W.seats.all (seatSafeInBook (applyPostings W.ledger postings)))
        · simp [h_cond] at h_step
        · simp [h_cond] at h_step
          subst h_step
          simp only [Bool.and_eq_true] at h_cond
          obtain ⟨⟨_, h_post⟩, _⟩ := h_cond
          exact ⟨postings_conserve_of_bookPostingValid h_nodup h_post, fun h_inv => ⟨h_inv, rfl⟩⟩
  | lockIntentSeat intent =>
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · have h_nodup : W.ledger.accounts.Nodup := of_decide_eq_true h_nd
      cases h_cond : (intent.admissibleB W.ledger W.height &&
          W.seats.all (seatSafeInBook (applyPostings W.ledger intent.escrowPostings)))
      · simp [h_nd, h_cond] at h_step
      · simp [h_nd, h_cond] at h_step
        subst h_step
        simp only [Bool.and_eq_true, SovereignIntent.admissibleB] at h_cond
        obtain ⟨⟨⟨_, h_post⟩, _⟩, _⟩ := h_cond
        exact ⟨postings_conserve_of_bookPostingValid h_nodup h_post, fun h_inv => ⟨h_inv, rfl⟩⟩
  | settleContendedBatch batch =>
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · have h_nodup : W.ledger.accounts.Nodup := of_decide_eq_true h_nd
      cases h_adm : batch.admissibleB W.ledger W.seats W.dragons
      · simp [h_nd, h_adm] at h_step
      · cases h_dr : stepDragonsExchangeEpoch W.dragons batch.dragonsInput with
        | none => simp [h_nd, h_adm, h_dr] at h_step
        | some dragons' =>
          simp [h_nd, h_adm, h_dr] at h_step
          subst h_step
          unfold ContendedClearingBatch.admissibleB at h_adm
          simp only [Bool.and_eq_true] at h_adm
          obtain ⟨⟨⟨_, h_post⟩, _⟩, _⟩ := h_adm
          refine ⟨postings_conserve_of_bookPostingValid h_nodup h_post, fun h_inv =>
            stepDragonsExchangeEpoch_preserves_invariant W.dragons dragons' batch.dragonsInput h_inv h_dr⟩
  | exitSeat seatAcc =>
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · have h_nodup : W.ledger.accounts.Nodup := of_decide_eq_true h_nd
      cases h_find : W.seats.find? (fun s => s.account == seatAcc) with
      | none => simp [h_nd, h_find] at h_step
      | some s =>
        simp only [h_nd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h_find] at h_step
        cases h_cond : exitSeatAdmissibleB W s seatAcc
        · simp [h_cond] at h_step
        · simp [h_cond] at h_step
          subst h_step
          unfold exitSeatAdmissibleB at h_cond
          simp only [Bool.and_eq_true] at h_cond
          obtain ⟨⟨h_post, _⟩, _⟩ := h_cond
          exact ⟨postings_conserve_of_bookPostingValid h_nodup h_post, fun h_inv => ⟨h_inv, rfl⟩⟩

/-- **Master Theorem 2 (`sovereignEngine_enforces_zoe_and_mandates`)**:
    Every admitted transition `stepSovereignEngine W tx = some W'` enforces:
    1. **ZoE Offer Safety**: Every active seat `s ∈ W'.seats` satisfies `safeAt W'.ledger s.account s.proposal = true`.
    2. **Mandate & 3D Reactive Affordance Confinement**: When `tx = .lockIntentSeat intent`,
       the invocation is authorized by `intent.mandate` (`checkInvocation = true`, bounded by
       `mandate.budget` and `mandate.expiresAt`) and passes the 3D `ReactiveAffordance` gate
       within `[openHeight, closeHeight]`.
    3. **In-Place Witness-Bound `ValidAt` & Contract Invariance**: When `tx = .executeOracleTurn cid env turn postings`
       and `ValidAt W.store turn contractReg sovereignJudgeFormats` holds, every mutated cell in
       `W'.store` satisfies its contract invariant (`Holds C.invariant d.postState`) and step relation. -/
theorem sovereignEngine_enforces_zoe_and_mandates
    (W W' : SovereignWorldState) (tx : SovereignTransaction)
    (h_step : stepSovereignEngine W tx = some W') :
    (∀ s ∈ W'.seats, safeAt W'.ledger s.account s.proposal = true) ∧
    (∀ intent, tx = .lockIntentSeat intent →
      Obend.Vault.Mandate.checkInvocation intent.mandate intent.invocation = true ∧
      intent.invocation.cost ≤ intent.mandate.budget ∧
      intent.invocation.epoch ≤ intent.mandate.expiresAt ∧
      reactiveOK intent.reactiveAffordance (intent.mandate.rights.map authOfMandateAuth)
        W.height intent.preState intent.postState = true ∧
      intent.reactiveAffordance.openHeight ≤ W.height ∧
      W.height ≤ intent.reactiveAffordance.closeHeight) ∧
    (∀ cid env turn postings (contractReg : String → Option CellContract),
      tx = .executeOracleTurn cid env turn postings →
      ValidAt W.store turn contractReg sovereignJudgeFormats →
      ∀ d ∈ turn.writeCells, ∀ C, contractReg d.cell = some C →
        W'.store d.cell = some d.postState ∧
        Holds C.invariant d.postState ∧
        Admits C.stepRel d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- 1. ZoE offer safety across all 5 transaction constructors
    cases tx with
    | deployContract c =>
      unfold stepSovereignEngine at h_step
      cases h_nd : decide W.ledger.accounts.Nodup
      · simp [h_nd] at h_step
      · cases h_cond : (c.wellFormedB && W.seats.all (seatSafeInBook W.ledger))
        · simp [h_nd, h_cond] at h_step
        · simp [h_nd, h_cond] at h_step
          subst h_step
          simp only [Bool.and_eq_true] at h_cond
          intro s hs
          exact List.all_eq_true.mp h_cond.2 s hs
    | executeOracleTurn cid env turn postings =>
      unfold stepSovereignEngine at h_step
      cases h_nd : decide W.ledger.accounts.Nodup
      · simp [h_nd] at h_step
      · cases h_find : W.contracts.find? (fun c => c.contractId == cid) with
        | none => simp [h_nd, h_find] at h_step
        | some c =>
          simp only [h_nd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h_find] at h_step
          cases h_cond : (c.wellFormedB &&
              verifyZkOracleEnvelope c env &&
              checkOracleTurnValidAt W turn &&
              turn.witnesses.all (checkTurnWitness sovereignJudgeFormats) &&
              postings.all (bookPostingValid W.ledger) &&
              W.seats.all (seatSafeInBook (applyPostings W.ledger postings)))
          · simp [h_cond] at h_step
          · simp [h_cond] at h_step
            subst h_step
            simp only [Bool.and_eq_true] at h_cond
            intro s hs
            exact List.all_eq_true.mp h_cond.2 s hs
    | lockIntentSeat intent =>
      unfold stepSovereignEngine at h_step
      cases h_nd : decide W.ledger.accounts.Nodup
      · simp [h_nd] at h_step
      · cases h_cond : (intent.admissibleB W.ledger W.height &&
            W.seats.all (seatSafeInBook (applyPostings W.ledger intent.escrowPostings)))
        · simp [h_nd, h_cond] at h_step
        · simp [h_nd, h_cond] at h_step
          subst h_step
          simp only [Bool.and_eq_true, SovereignIntent.admissibleB] at h_cond
          obtain ⟨⟨_, h_new_seat⟩, h_old_seats⟩ := h_cond
          intro s hs
          rcases List.mem_cons.mp hs with rfl | h_mem
          · exact h_new_seat
          · exact List.all_eq_true.mp h_old_seats s h_mem
    | settleContendedBatch batch =>
      unfold stepSovereignEngine at h_step
      cases h_nd : decide W.ledger.accounts.Nodup
      · simp [h_nd] at h_step
      · cases h_adm : batch.admissibleB W.ledger W.seats W.dragons
        · simp [h_nd, h_adm] at h_step
        · cases h_dr : stepDragonsExchangeEpoch W.dragons batch.dragonsInput with
          | none => simp [h_nd, h_adm, h_dr] at h_step
          | some dragons' =>
            simp [h_nd, h_adm, h_dr] at h_step
            subst h_step
            unfold ContendedClearingBatch.admissibleB at h_adm
            simp only [Bool.and_eq_true] at h_adm
            obtain ⟨⟨_, h_seats⟩, _⟩ := h_adm
            intro s hs
            exact List.all_eq_true.mp h_seats s hs
    | exitSeat seatAcc =>
      unfold stepSovereignEngine at h_step
      cases h_nd : decide W.ledger.accounts.Nodup
      · simp [h_nd] at h_step
      · cases h_find : W.seats.find? (fun s => s.account == seatAcc) with
        | none => simp [h_nd, h_find] at h_step
        | some s =>
          simp only [h_nd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h_find] at h_step
          cases h_cond : exitSeatAdmissibleB W s seatAcc
          · simp [h_cond] at h_step
          · simp [h_cond] at h_step
            subst h_step
            unfold exitSeatAdmissibleB at h_cond
            simp only [Bool.and_eq_true] at h_cond
            intro x hx
            exact List.all_eq_true.mp h_cond.1.2 x hx
  · -- 2. Mandate & 3D ReactiveAffordance confinement on `.lockIntentSeat`
    intro intent h_tx
    subst h_tx
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · cases h_cond : (intent.admissibleB W.ledger W.height &&
          W.seats.all (seatSafeInBook (applyPostings W.ledger intent.escrowPostings)))
      · simp [h_nd, h_cond] at h_step
      · simp only [Bool.and_eq_true, SovereignIntent.admissibleB] at h_cond
        obtain ⟨⟨⟨⟨h_chk, h_react⟩, _⟩, _⟩, _⟩ := h_cond
        have h_chk_copy := h_chk
        unfold Obend.Vault.Mandate.checkInvocation Obend.Vault.Mandate.authorizedBy at h_chk_copy
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_chk_copy
        obtain ⟨_, ⟨⟨⟨⟨_, _⟩, h_cost⟩, _⟩, h_epoch⟩, _⟩ := h_chk_copy
        have ⟨_, _, h_win⟩ := (reactiveOK_iff _ _ _ _ _).mp h_react
        have ⟨h_lo, h_hi⟩ := (inWindow_iff _ _).mp h_win
        exact ⟨h_chk, h_cost, h_epoch, h_react, h_lo, h_hi⟩
  · -- 3. In-place witness-bound `ValidAt` & contract invariance on `.executeOracleTurn`
    intro cid env turn postings contractReg h_tx h_valid d hd C hC
    subst h_tx
    unfold stepSovereignEngine at h_step
    cases h_nd : decide W.ledger.accounts.Nodup
    · simp [h_nd] at h_step
    · cases h_find : W.contracts.find? (fun c => c.contractId == cid) with
      | none => simp [h_nd, h_find] at h_step
      | some c =>
        simp only [h_nd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h_find] at h_step
        cases h_cond : (c.wellFormedB &&
            verifyZkOracleEnvelope c env &&
            checkOracleTurnValidAt W turn &&
            turn.witnesses.all (checkTurnWitness sovereignJudgeFormats) &&
            postings.all (bookPostingValid W.ledger) &&
            W.seats.all (seatSafeInBook (applyPostings W.ledger postings)))
        · simp [h_cond] at h_step
        · simp [h_cond] at h_step
          subst h_step
          have ⟨h_store, h_inv⟩ :=
            turn.store_post_invariants_hold W.store contractReg sovereignJudgeFormats h_valid d hd C hC
          have h_step_rel :=
            turn.post_step_sound W.store contractReg sovereignJudgeFormats h_valid d hd C hC
          exact ⟨h_store, h_inv, h_step_rel⟩

/-- **Master Theorem 3 (`sovereignEngine_blinded_view_non_forgeable`)**:
    For any world state `W : SovereignWorldState`, viewer `v`, and bounded collision-resistant
    hash `H`:
    1. The viewer-projected Merkle root `W.merkleRoot H v` is bit-identical to the unredacted
       vault root `mapRoot H (vaultCommits H W.vaultCells)`.
    2. Every honest blinded opening `mkBlindedOpening H v W.vaultCells j` (`j < W.vaultCells.length`,
       `j < 2 ^ 256`) verifies against `W.merkleRoot H v`.
    3. Any tampered cell `c_tampered` that alters `id` or `readCap` at index `j` is strictly
       refused by `verifyBlindedOpening` against `W.merkleRoot H v`. -/
theorem sovereignEngine_blinded_view_non_forgeable
    {H : Hash} (hb : Bounded H) (h_no_coll : ¬ Collision H)
    (W : SovereignWorldState) (v : List Obend.Vault.Projection.Auth)
    (j : Nat) (c_tampered : VaultCell)
    (hj : j < W.vaultCells.length) (hjs : j < 2 ^ 256)
    (hid_orig : (W.vaultCells.getD j default).id < 2 ^ 256)
    (hsalt_orig : (W.vaultCells.getD j default).salt < 2 ^ 256)
    (hid_tamp : c_tampered.id < 2 ^ 256)
    (hsalt_tamp : c_tampered.salt < 2 ^ 256)
    (h_tampered : c_tampered.id ≠ (W.vaultCells.getD j default).id ∨
                  c_tampered.readCap ≠ (W.vaultCells.getD j default).readCap) :
    W.merkleRoot H v = mapRoot H (vaultCommits H W.vaultCells) ∧
    verifyBlindedOpening H (mkBlindedOpening H v W.vaultCells j) (W.merkleRoot H v) = true ∧
    verifyBlindedOpening H
      { mkBlindedOpening H v W.vaultCells j with cell := projectCell H v c_tampered }
      (W.merkleRoot H v) = false := by
  have h_root : W.merkleRoot H v = mapRoot H (vaultCommits H W.vaultCells) :=
    projectedMerkleRoot_eq_vaultRoot H v W.vaultCells
  refine ⟨h_root, ?_, ?_⟩
  · rw [h_root]
    exact verify_blinded_opening_complete hb v W.vaultCells j hj hjs
  · exact tampered_metadata_opening_refused hb h_no_coll v W.vaultCells j c_tampered
      hj hjs hid_orig hsalt_orig hid_tamp hsalt_tamp h_tampered

/-- **Stale-Pin Refusal Theorem (`stepSovereignEngine_oracleTurn_refuses_stale_pin`)**:
    Whenever `admitFootprint W.store turn.readPins` is not `.ok` (`.isOk = false`, i.e., a read pin
    in `turn.readPins` mismatches `W.store`), `.executeOracleTurn` is strictly refused (`= none`). -/
theorem stepSovereignEngine_oracleTurn_refuses_stale_pin
    (W : SovereignWorldState) (cid : String) (env : ZkOracleFactEnvelope)
    (turn : VaultTurn) (postings : List ResourcePosting)
    (h_stale : (admitFootprint W.store turn.readPins).isOk = false) :
    stepSovereignEngine W (.executeOracleTurn cid env turn postings) = none := by
  unfold stepSovereignEngine
  cases h_nd : decide W.ledger.accounts.Nodup
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases h_find : W.contracts.find? (fun c => c.contractId == cid) with
    | none => rfl
    | some c =>
      have h_gate : checkOracleTurnValidAt W turn = false := by
        unfold checkOracleTurnValidAt
        rw [h_stale]
        rfl
      simp [h_gate]

#tooth stepSovereignEngine_oracleTurn_refuses_stale_pin by mutation
  stepSovereignEngine := fun W _ => some W

end Obend.Vault
end
