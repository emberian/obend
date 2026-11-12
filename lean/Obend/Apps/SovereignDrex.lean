module
/-
# Obend.Apps.SovereignDrex — Flagship App #7: 4-Validator Sovereign `DReX` + `CheckedCarry` Exchange

Connects the 4-module `.obend` sovereign multi-asset exchange package in `apps/sovereign-drex/`:
1. `apps/sovereign-drex/Seat.obend` (`SovereignDrexSeat`: `BaseZoeSeatSpec` -> `InstitutionalMandateSeatOverride`)
2. `apps/sovereign-drex/OrderBook.obend` (`SovereignDrexOrderBook`: `BaseUniformOrderBookSpec` -> `WholesaleDvPOrderBookOverride`)
3. `apps/sovereign-drex/BatchClearing.obend` (`SovereignDrexClearing`: `BaseBatchClearingSpec` -> `SovereignCarryClearingOverride`)
4. `apps/sovereign-drex/SovereignDrexTop.obend` (`SovereignDrexTop`: `BaseSovereignDrexSpec` -> `CarryUpgradeSovereignDrexOverride`)

directly to the unified DeOS vault, markets, checked carry, and 4-validator Simplex BFT consensus spine:
- `Obend.Vault.UnifiedDeos`:
  * `UnifiedDeosSpine` (`stepUnifiedTurn`, `unifiedDeos_ledger_and_turn_sound`, `stepUnifiedTurn_refuses_stale_pin`),
  * `CheckedCarry` (`Plan.no_drop_at`, `worldAuthState_reroot_admissible_iff`, `world_revoke_refuses_carry`,
    `TitleMigration.copied_title_grant_not_semantic_narrowing`),
  * Multilateral `netting@1` (`nettingJudge`, `net_reduces_gross_exposure`, `settleNetting_agrees_with_gross`),
  * `SimplexProtocol.FinCert` + `SimplexTrace` + `SimplexFinalityGate` (`quorum_final_gates_unique_per_height`),
  * Durable WAL crash-recovery (`durable_recovery_prevents_equivocation`, `durable_expose_once_across_crashes`),
- `Obend.Leaf.Static`, `Obend.Hardware.HDL`, `Obend.Hardware.Synth`, `Obend.Hardware.Compiler`:
  * Vtable flattening (`flatten_sound`), `Leaf.Book` emission (`book_sound`), `compileBookToRtl` LEC, and
    universally verified synchronous batch-clearing + WAL anti-replay `RtlModule` (`sovereignDrexBatchTopRtlModule`).
-/
public import Lean
public import Obend.Hardware.UserspacePhysical
public import Obend.Hardware.Synth
public import Obend.Vault.UnifiedDeos
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
public import Obend.Tactic.Tooth
public import Obend.Elab.Workbook
public meta import Lean
public meta import Obend.Hardware.UserspacePhysical
public meta import Obend.Elab.Workbook

@[expose] public section

namespace Obend.Apps.SovereignDrex

open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Slot
open Obend.Slot.Protocol
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.Ledger
open Obend.Judge
open Obend.Vault
open Obend.Vault.CheckedCarry
open Obend.Vault.UnifiedDeos
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace
open Obend.Consensus.Finality
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Compile-Time Elaboration of `apps/sovereign-drex/*.obend` via `#import_obend` -/

#import_obend "apps/sovereign-drex/Seat.obend" as SovereignDrexSeat
#import_obend "apps/sovereign-drex/OrderBook.obend" as SovereignDrexOrderBook
#import_obend "apps/sovereign-drex/BatchClearing.obend" as SovereignDrexClearing
#import_obend "apps/sovereign-drex/SovereignDrexTop.obend" as SovereignDrexTop

/-- Concrete value check of the elaborated `apps/sovereign-drex/*.obend` workbooks. -/
example :
    SovereignDrexTop.laws_count = 6 ∧
    SovereignDrexSeat.institutionalSafetyAt80_val = .nat 95000 ∧
    SovereignDrexSeat.institutionalMandateAt15_val = .nat 1650 ∧
    SovereignDrexOrderBook.wholesaleVolumeAt20_val = .nat 127000 ∧
    SovereignDrexOrderBook.wholesaleSlackAt10_val = .nat 10040 ∧
    SovereignDrexClearing.sovereignClearedAt12_val = .nat 7000 ∧
    SovereignDrexClearing.sovereignDigestAt5_val = .nat 182 ∧
    SovereignDrexTop.drexSettlementAt8_val = .nat 5000 ∧
    SovereignDrexTop.drexFinalityTagAt3_val = .nat 227 ∧
    SovereignDrexTop.crossModuleDrexSummary_val = .nat 110222 ∧
    SovereignDrexSeat.institutionalOfferSafeValid_val = .boolean true ∧
    SovereignDrexOrderBook.wholesaleCrossingConservedValid_val = .boolean true ∧
    SovereignDrexClearing.sovereignBatchConservationValid_val = .boolean true ∧
    SovereignDrexTop.sovereignDrexEndToEndSafetyValid_val = .boolean true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Vtable Flattening, `Leaf.Book` Emission & `compileBookToRtl` LEC -/

theorem sovereignDrex_compositions_closed :
    SovereignDrexSeat.institutionalZoeSeat_comp.closedB = true ∧
    SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.closedB = true ∧
    SovereignDrexClearing.sovereignCarryClearing_comp.closedB = true ∧
    SovereignDrexTop.carryUpgradedSovereignDrex_comp.closedB = true := by
  decide +kernel

theorem sovereignDrex_flatten_and_book_sound (m : String) :
    (.get SovereignDrexSeat.institutionalZoeSeat_comp.flatten m ≈b
      .get SovereignDrexSeat.institutionalZoeSeat_comp.object m) ∧
    (.get (emit SovereignDrexSeat.institutionalZoeSeat_comp).link m ≈b
      .get SovereignDrexSeat.institutionalZoeSeat_comp.object m) ∧
    (.get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.flatten m ≈b
      .get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.object m) ∧
    (.get (emit SovereignDrexOrderBook.wholesaleDvPOrderBook_comp).link m ≈b
      .get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.object m) ∧
    (.get SovereignDrexClearing.sovereignCarryClearing_comp.flatten m ≈b
      .get SovereignDrexClearing.sovereignCarryClearing_comp.object m) ∧
    (.get (emit SovereignDrexClearing.sovereignCarryClearing_comp).link m ≈b
      .get SovereignDrexClearing.sovereignCarryClearing_comp.object m) ∧
    (.get SovereignDrexTop.carryUpgradedSovereignDrex_comp.flatten m ≈b
      .get SovereignDrexTop.carryUpgradedSovereignDrex_comp.object m) ∧
    (.get (emit SovereignDrexTop.carryUpgradedSovereignDrex_comp).link m ≈b
      .get SovereignDrexTop.carryUpgradedSovereignDrex_comp.object m) := by
  have ⟨hc1, hc2, hc3, hc4⟩ := sovereignDrex_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m,
         flatten_sound _ hc4 m, book_sound _ hc4 m⟩

/-- LEC check of `compileBookToRtl` on `SovereignDrexTop` and `SovereignDrexClearing`. -/
example :
    (match compileBookToRtl "sovereign_drex_top" SovereignDrexTop.carryUpgradedSovereignDrex_book,
           compileBookToRtl "sovereign_drex_clearing" SovereignDrexClearing.sovereignCarryClearing_book with
     | some mTop, some mClear =>
       checkRtlModule mTop &&
       checkRtlModule mClear &&
       (evalModuleOutputs mTop (fun _ => 8#64) (fun _ => 0#64) ==
         [ ("out_settledCbdcLiquidity", 125000#64)
         , ("out_finalityCommitTag", 547#64)
         , ("out_validatorQuorum", 3#64)
         , ("out_protectedWelfareCrown", 1000#64)
         , ("out_batchSettlementCbdc", 5000#64)
         ]) &&
       (evalModuleOutputs mClear (fun _ => 5#64) (fun _ => 0#64) ==
         [ ("out_halfEdgeDeltaCount", 6#64)
         , ("out_carryPinDigest", 182#64)
         , ("out_quorumThreshold", 3#64)
         , ("out_welfareCrownFloor", 1000#64)
         , ("out_clearedCbdcAmount", 3500#64)
         ])
     | _, _ => false) = true := by
  decide +kernel

/-! ## 3. Checked Carry, Multilateral `netting@1` & State-Bound Half-Edges (`UnifiedDeos`) -/

/-- **`sovereignDrex_carry_netting_and_hyperedge_sound`**:
    1. Every `NoDrops` `CheckedCarry.Plan` maps every live source cell into `outputs`, `Replay.World`
       rerooting preserves `AdmissibleCarry`, `Grants.revoke` refuses carried authority, and copied
       numeric field grants fail `NoNewMeaning` (`copied_title_grant_not_semantic_narrowing`),
    2. Every accepted `netting@1` batch (`nettingJudge.check grade qNet cNet = .ok`) reduces or preserves
       gross exposure, preserves net positions, agrees with gross settlement on every `Book`, and
       compiles to balanced `Register.Movement`s,
    3. State-bound `VaultTurn`s conserve actual cell state balances (`stateBoundTurn_conserves_actual_state_balances`),
       while unreported cell-balance inflation is strictly refused (`unreported_state_inflation_refused`). -/
theorem sovereignDrex_carry_netting_and_hyperedge_sound
    {source : List Cell} {rel : Cell → Cell → Prop}
    (plan : CheckedCarry.Plan source rel) (hNoDrops : NoDrops plan)
    (w : Obend.Vault.Replay.World) (g₁ s₁ g₂ s₂ : ByteArray) (req : CarryRequest)
    (grade : Nat) (qNet : NettingQuery) (cNet : NettingCert)
    (hNet : nettingJudge.check grade qNet cNet = .ok) :
    (∀ i : Fin source.length, ∃ next ∈ plan.outputs, rel source[i] next) ∧
    (AdmissibleCarry (worldAuthState w g₁ s₁) req ↔ AdmissibleCarry (worldAuthState w g₂ s₂) req) ∧
    ¬ AdmissibleCarry (worldAuthState { w with grants := w.grants.revoke req.grantId } g₁ s₁) req ∧
    ¬ TitleMigration.NoNewMeaning TitleMigration.oldGrant TitleMigration.copiedGrant ∧
    grossExposure cNet.netTransfers ≤ grossExposure qNet.grossObligations ∧
    (∀ (b : Obend.Ledger.Book) acc ast,
      (settleObligations b cNet.netTransfers).balance acc ast =
        (settleObligations b qNet.grossObligations).balance acc ast) ∧
    (cNet.toMovements.map (·.debit)).sum = (cNet.toMovements.map (·.credit)).sum ∧
    (∀ (turn : VaultTurn) (assets : List String) (ast : String),
      ast ∈ assets →
      checkTurnStateBalancesBound assets turn = true →
      (turn.writeCells.map (fun d => extractCellAssetBalance d.postState ast)).foldl (· + ·) 0 =
        (turn.writeCells.map (fun d => extractCellAssetBalance d.preState ast)).foldl (· + ·) 0) ∧
    checkDeltaMatchesStateBalances ["USDC"] unreportedInflationDelta = false := by
  have hNetSpec : NettingSpec qNet cNet := nettingJudge.sound hNet
  refine ⟨plan.noDrops_maps_all_cells hNoDrops,
          worldAuthState_reroot_admissible_iff w g₁ s₁ g₂ s₂ req,
          world_revoke_refuses_carry w g₁ s₁ req,
          TitleMigration.copied_title_grant_not_semantic_narrowing,
          net_reduces_gross_exposure hNetSpec,
          fun b => (settleNetting_agrees_with_gross b hNetSpec).1,
          cNet.toMovements_balanced,
          fun turn assets ast hMem hBound =>
            (stateBoundTurn_conserves_actual_state_balances turn assets ast hMem hBound).2,
          unreported_state_inflation_refused.2.2⟩

/-! ## 4. Unified DeOS Turn Gate & 4-Validator Simplex BFT Finality -/

/-- 4-validator committee (`V0..V3`, $N = 4, f = 1$, quorum $2f + 1 = 3$) for `apps/sovereign-drex/`. -/
def drexCommittee4 : List Nat := [0, 1, 2, 3]

/-- Attested finality gate for Epoch 3 (`faults = 1`, `stateRoot = 118`). -/
def drexAttestedGate : QuorumBoundFinalityGate :=
  { turnId        := 3
    currentTier   := .attested
    faults        := 1
    stateRoot     := 118
    attestSigners := [0]
    qcSigners     := []
    qcDigest      := none
    merkleRoot    := none
    committee     := drexCommittee4 }

/-- Promoted `.quorum_final` gate signed by 3-of-4 validators `[0, 1, 2]` (`qcDigest = 227`). -/
def drexQuorumFinalGate : QuorumBoundFinalityGate :=
  { drexAttestedGate with
    currentTier := .quorum_final
    qcSigners   := [0, 1, 2]
    qcDigest    := some 227 }

/-- **`sovereignDrex_engine_and_bft_finality_sound`**:
    1. Every admitted `stepUnifiedTurn S stateAssets turn postings = some S'` from a floor-valid
       `FloorBook` preserves `FloorsHold` (all non-issuer floors ≥ 0), conserves per-asset supply,
       realizes exact `Register.Reg` deltas, enforces ZoE `safeAt` across `S'.seats`, and refuses
       stale read footprints (`stepUnifiedTurn_refuses_stale_pin`),
    2. On `drexCommittee4` ($N = 4, f = 1$), `drexAttestedGate` promotes to `.quorum_final`, and
       any two conflicting 3-of-4 quorums `blockA ≠ blockB` yield a constructive `SlashingReceipt`
       catching `≥ 2` equivocating validators (`simplex_accountable_safety`),
    3. Over any reachable `Reach P sent`, any two `.quorum_final` `SimplexFinalityGate`s
       at the same chain height certify identical blocks and identical cSHAKE256 `chainDigest`s. -/
theorem sovereignDrex_engine_and_bft_finality_sound
    {S S' : UnifiedDeosSpine} {stateAssets : List String}
    {turn : VaultTurn} {postings : List TypedPosting}
    (hFloors : FloorsHold S.floorBook)
    (hStep : stepUnifiedTurn S stateAssets turn postings = some S') :
    FloorsHold S'.floorBook ∧
    (∀ ast : AssetId, S'.floorBook.assetSum ast = S.floorBook.assetSum ast) ∧
    (∀ s ∈ S'.seats, safeAt S'.seatBook s.account s.proposal = true) ∧
    (∀ staleTurn stalePostings,
      (admitFootprint S.store staleTurn.readPins).isOk = false →
      stepUnifiedTurn S stateAssets staleTurn stalePostings = none) ∧
    advanceQuorumBoundGate drexAttestedGate (.formQC 227 [0, 1, 2] 118) = some drexQuorumFinalGate ∧
    (∀ (sent : Sent) (view : Nat) (targetA targetB : Target),
      targetA ≠ targetB →
      3 ≤ (drexCommittee4.filter fun n => voted sent n view targetA).length →
      3 ≤ (drexCommittee4.filter fun n => voted sent n view targetB).length →
      let receipt := extractReceipt drexCommittee4 sent view targetA targetB
      drexQuorumFinalGate.currentTier = .quorum_final ∧
      admitsOp drexQuorumFinalGate.currentTier .stateWrite = true ∧
      receipt.checks sent = true ∧
      2 ≤ receipt.signers.length ∧
      (∀ v ∈ receipt.signers, v ∈ drexCommittee4 ∧ ¬ VoteOnce sent v view)) ∧
    (∀ {P : Protocol} {sent : Sent},
      Reach P sent →
      ∀ {g₁ g₁' g₂ g₂' : SimplexFinalityGate} {c₁ c₂ : FinCert} {r₁ r₂ : ByteArray},
        advanceSimplexGate P sent g₁ (.finalizeWithCert c₁ r₁) = some g₁' →
        advanceSimplexGate P sent g₂ (.finalizeWithCert c₂ r₂) = some g₂' →
        c₁.chain.height = c₂.chain.height →
        c₁.chain.blocks = c₂.chain.blocks ∧ chainDigest c₁.chain = chainDigest c₂.chain) := by
  have hSpine := unifiedDeos_ledger_and_turn_sound hFloors hStep
  have hGatePromote :
      advanceQuorumBoundGate drexAttestedGate (.formQC 227 [0, 1, 2] 118) = some drexQuorumFinalGate := by
    decide +kernel
  have hCommLen : drexCommittee4.length ≤ 3 * 1 + 1 := by decide +kernel
  refine ⟨hSpine.2.1,
          hSpine.2.2.1,
          hSpine.2.2.2.2.2,
          fun t ps hStale => (stepUnifiedTurn_refuses_stale_pin S stateAssets t ps hStale).2,
          hGatePromote,
          ?_,
          @quorum_final_gates_unique_per_height⟩
  intro sent view targetA targetB hNe hQA hQB
  have hAcc := accountable drexCommittee4 1 sent view targetA targetB hCommLen hNe hQA hQB
  exact ⟨rfl, rfl, hAcc.1, hAcc.2.1, hAcc.2.2⟩

/-- **`sovereignDrex_durable_wal_crash_recovery_sound`**:
    1. Disjoint `VaultTurn`s `T₁, T₂` remain mutually `ValidAt`, commute on `VaultStore`, and yield
       identical collapsed Merkle roots,
    2. After crashing (`crashSimplexHost`) and replaying the durable WAL (`recoverSimplexHost`),
       any previously voted view `v` rejects conflicting votes `c'` (`castSimplexVote restoredState v c' = restoredState`),
    3. Once a settlement effect `n` is exposed (`hstep ... s (.expose n) = .ok s₁`), post-crash recovery
       across `extraCrashes + 1` crashes retains `n ∈ s_rec.outbox` and refuses duplicate execution
       with `.error (.exposed n)`. -/
theorem sovereignDrex_durable_wal_crash_recovery_sound
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Ledger ι W Tok)
    (base : W → View Tok Fact)
    (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s s₁ : DState L S Hole A P Cred Cand Fact Ob i₀)
    (n extraCrashes : Nat)
    (h_exp : hstep L base sp au k J₀ s (.expose n) = .ok s₁)
    (host : DurableSimplexHost) (v : Nat) (c' : Chain)
    (hv_voted : host.journaledVotes.any (fun jv => jv.view == v) = true)
    (H : Obend.Digest.HashBytes.Hash) (schema : List String) (val : StoreValuation)
    (store₀ : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option Obend.Law.CellContract)
    (formats : List Obend.Judge.Format)
    (h_disj : DisjointTurns T₁ T₂)
    (h₁ : ValidAt store₀ T₁ contracts formats)
    (h₂ : ValidAt store₀ T₂ contracts formats) :
    let restoredState : VolatileSimplexVoter :=
      { self := host.self, deadline := host.deadline, votes := host.journaledVotes }
    let trace : List (HEvent L S Hole A P Cred Cand Fact) :=
      List.replicate (extraCrashes + 1) .crash ++ [.recover]
    let s_rec := runDurableTrace L base sp au k J₀ s₁ trace
    ValidAt (applyTurn store₀ T₁) T₂ contracts formats ∧
    ValidAt (applyTurn store₀ T₂) T₁ contracts formats ∧
    applyTurn (applyTurn store₀ T₁) T₂ = applyTurn (applyTurn store₀ T₂) T₁ ∧
    Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₁) T₂) =
      Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₂) T₁) ∧
    (recoverSimplexHost (crashSimplexHost host)).volatileState = some restoredState ∧
    castSimplexVote restoredState v c' = restoredState ∧
    n ∈ s_rec.outbox ∧
    n ∉ pending L s_rec ∧
    hstep L base sp au k J₀ s_rec (.expose n) = .error (.exposed n) := by
  have hBoth := disjoint_both_orders store₀ T₁ T₂ contracts formats h_disj h₁ h₂
  have hComm := vaultTurn_disjoint_commutes store₀ T₁ T₂ h_disj
  have hRoot :
      Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₁) T₂) =
        Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₂) T₁) := by
    rw [hComm]
  have hEqv := durable_recovery_prevents_equivocation host v c' hv_voted
  have hExpOnce := durable_expose_once_across_crashes L base sp au k J₀ s s₁ n extraCrashes h_exp
  exact ⟨hBoth.1, hBoth.2, hComm, hRoot, hEqv.1, hEqv.2.2, hExpOnce.1, hExpOnce.2.1, hExpOnce.2.2⟩

/-! ## 5. Verified Synchronous Hardware Batch-Clearing & WAL Anti-Replay `RtlModule` -/

/-- Synchronous `RtlModule` (`sovereign_drex_batch_top`) for Flagship App #7:
    evaluates 3-of-4 BFT validator quorum, `BatchClearing.obend` `carryPinDigest` in both base and
    carry-upgraded modes, `always_ff` WAL monotone-epoch anti-replay, half-edge balance conservation,
    ZoE offer safety, and protected welfare-crown preservation. -/
def sovereignDrexBatchTopRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames :=
      [ "in_lot_count"
      , "in_epoch_id"
      , "in_validator_votes"
      , "in_carry_upgrade_en"
      , "in_old_cbdc_total"
      , "in_delta_debit"
      , "in_delta_credit"
      , "in_seat_cbdc_after"
      , "in_seat_want_floor"
      , "in_forever_crown_drop_req"
      , "in_tx_pin_digest" ]
  , wires :=
      [ { wireIdx := 0,  name := "v0",
          expr := .alu .bitAnd (.inputPort 2) (.const 1#64) }
      , { wireIdx := 1,  name := "v1",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 1#64)) (.const 1#64) }
      , { wireIdx := 2,  name := "v2",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 2#64)) (.const 1#64) }
      , { wireIdx := 3,  name := "v3",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 3#64)) (.const 1#64) }
      , { wireIdx := 4,  name := "vote_cnt",
          expr := .alu .add (.alu .add (.wireRef 0) (.wireRef 1))
                            (.alu .add (.wireRef 2) (.wireRef 3)) }
      , { wireIdx := 5,  name := "quorum_ok",
          expr := .mux (.alu .ult (.wireRef 4) (.const 3#64)) (.const 0#64) (.const 1#64) }
      , { wireIdx := 6,  name := "base_half_edges",
          expr := .mux (.inputPort 3) (.const 6#64) (.const 4#64) }
      , { wireIdx := 7,  name := "carry_pin_digest",
          expr := .alu .add (.alu .add (.alu .mul (.inputPort 1) (.const 32#64)) (.wireRef 6))
                            (.mux (.inputPort 3) (.const 16#64) (.const 0#64)) }
      , { wireIdx := 8,  name := "epoch_monotone_ok",
          expr := .alu .ult (.regRead 1) (.inputPort 1) }
      , { wireIdx := 9,  name := "pin_fresh_ok",
          expr := .alu .eq (.inputPort 10) (.wireRef 7) }
      , { wireIdx := 10, name := "half_edge_balanced",
          expr := .alu .eq (.inputPort 5) (.inputPort 6) }
      , { wireIdx := 11, name := "zoe_offer_safe",
          expr := .mux (.alu .ult (.inputPort 7) (.inputPort 8)) (.const 0#64) (.const 1#64) }
      , { wireIdx := 12, name := "crown_preserved",
          expr := .alu .eq (.inputPort 9) (.const 0#64) }
      , { wireIdx := 13, name := "guards_a",
          expr := .alu .bitAnd (.alu .bitAnd (.wireRef 5) (.wireRef 8)) (.wireRef 9) }
      , { wireIdx := 14, name := "guards_b",
          expr := .alu .bitAnd (.alu .bitAnd (.wireRef 10) (.wireRef 11)) (.wireRef 12) }
      , { wireIdx := 15, name := "turn_ok",
          expr := .alu .bitAnd (.wireRef 13) (.wireRef 14) }
      , { wireIdx := 16, name := "new_cbdc_total",
          expr := .mux (.wireRef 15)
                       (.alu .sub (.alu .add (.inputPort 4) (.inputPort 6)) (.inputPort 5))
                       (.inputPort 4) }
      ]
  , regs :=
      [ { regIdx := 0, name := "reg_wal_committed_count", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
      , { regIdx := 1, name := "reg_last_committed_epoch", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.inputPort 1) (.regRead 1) }
      ]
  , outputs :=
      [ { name := "out_validator_quorum",        expr := .const 3#64 }
      , { name := "out_vote_count",              expr := .wireRef 4 }
      , { name := "out_quorum_reached",          expr := .wireRef 5 }
      , { name := "out_protected_welfare_crown", expr := .const 1000#64 }
      , { name := "out_settled_cbdc_liquidity",
          expr := .mux (.inputPort 3) (.const 125000#64) (.const 100000#64) }
      , { name := "out_batch_settlement_cbdc",
          expr := .alu .add (.alu .mul (.inputPort 0) (.const 500#64)) (.const 1000#64) }
      , { name := "out_finality_commit_tag",
          expr := .alu .add (.alu .add (.alu .mul (.inputPort 1) (.const 64#64)) (.const 3#64))
                            (.mux (.inputPort 3) (.const 32#64) (.const 0#64)) }
      , { name := "out_carry_pin_digest",        expr := .wireRef 7 }
      , { name := "out_pin_fresh_ok",            expr := .wireRef 9 }
      , { name := "out_epoch_monotone_ok",       expr := .wireRef 8 }
      , { name := "out_new_cbdc_total",          expr := .wireRef 16 }
      , { name := "out_turn_admitted",           expr := .wireRef 15 }
      , { name := "out_wal_committed_count",     expr := .regRead 0 }
      , { name := "out_last_committed_epoch",    expr := .regRead 1 }
      ]
  }

/-- Input port environment builder for `sovereignDrexBatchTopRtlModule`. -/
def mkDrexRtlInputs
    (lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin : Nat) :
    Nat → BitVec 64
  | 0  => BitVec.ofNat 64 lots
  | 1  => BitVec.ofNat 64 epoch
  | 2  => BitVec.ofNat 64 votes
  | 3  => BitVec.ofNat 64 carryEn
  | 4  => BitVec.ofNat 64 oldTotal
  | 5  => BitVec.ofNat 64 debit
  | 6  => BitVec.ofNat 64 credit
  | 7  => BitVec.ofNat 64 seatAfter
  | 8  => BitVec.ofNat 64 wantFloor
  | 9  => BitVec.ofNat 64 dropCrown
  | 10 => BitVec.ofNat 64 txPin
  | _  => 0#64

/-- Universal Hardware Anti-Replay & CBDC Conservation Theorem
    (`sovereignDrexBatchTopRtlModule_epoch_replay_refused`):
    For ALL input combinations `(lots, epoch, votes, carryEn, oldTotal, debit, credit, seatAfter, wantFloor, dropCrown, txPin)`
    and ANY sequential register state `regSt : Nat → BitVec 64` where `epoch` does not strictly advance
    `reg_last_committed_epoch` (`BitVec.ult (regSt 1) (BitVec.ofNat 64 epoch) = false`):
    1. `out_turn_admitted = some 0#64` (turn admission is unconditionally blocked),
    2. `out_new_cbdc_total = some (BitVec.ofNat 64 oldTotal)` (CBDC supply is unchanged),
    3. Both `reg_wal_committed_count` (`regIdx = 0`) and `reg_last_committed_epoch` (`regIdx = 1`)
       hold their exact pre-cycle values across `stepModuleRegs` (zero double-execution). -/
theorem sovereignDrexBatchTopRtlModule_epoch_replay_refused
    (lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin : Nat)
    (regSt : Nat → BitVec 64)
    (hReplay : BitVec.ult (regSt 1) (BitVec.ofNat 64 epoch) = false) :
    let ins := mkDrexRtlInputs lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin
    let outs := evalModuleOutputs sovereignDrexBatchTopRtlModule ins regSt
    let nextSt := stepModuleRegs sovereignDrexBatchTopRtlModule false ins regSt
    outs.lookup "out_turn_admitted" = some 0#64 ∧
    outs.lookup "out_new_cbdc_total" = some (BitVec.ofNat 64 oldTotal) ∧
    nextSt 0 = regSt 0 ∧
    nextSt 1 = regSt 1 := by
  dsimp only
  have hTurnZero :
      evalWireTable
        (mkDrexRtlInputs lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin)
        regSt sovereignDrexBatchTopRtlModule.wires 15 = 0#64 := by
    simp only [sovereignDrexBatchTopRtlModule, evalWireTable, List.foldl, evalRtlExpr,
      evalAluOp, mkDrexRtlInputs, hReplay]
    simp [BitVec.and_zero, BitVec.zero_and]
  have hNewTotal :
      evalWireTable
        (mkDrexRtlInputs lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin)
        regSt sovereignDrexBatchTopRtlModule.wires 16 = BitVec.ofNat 64 oldTotal := by
    simp only [sovereignDrexBatchTopRtlModule, evalWireTable, List.foldl, evalRtlExpr,
      evalAluOp, mkDrexRtlInputs, hReplay]
    simp [BitVec.and_zero, BitVec.zero_and]
  have hRegs : sovereignDrexBatchTopRtlModule.regs =
      [ { regIdx := 0, name := "reg_wal_committed_count", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
      , { regIdx := 1, name := "reg_last_committed_epoch", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.inputPort 1) (.regRead 1) } ] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold evalModuleOutputs
    change some (evalWireTable _ regSt sovereignDrexBatchTopRtlModule.wires 15) = some 0#64
    rw [hTurnZero]
  · unfold evalModuleOutputs
    change some (evalWireTable _ regSt sovereignDrexBatchTopRtlModule.wires 16) =
      some (BitVec.ofNat 64 oldTotal)
    rw [hNewTotal]
  · rw [stepModuleRegs_eq_foldl_next, hRegs]
    simp only [List.foldl, regNextValue, evalRtlExpr, hTurnZero]
    rfl
  · rw [stepModuleRegs_eq_foldl_next, hRegs]
    simp only [List.foldl, regNextValue, evalRtlExpr, hTurnZero]
    rfl

/-- Concrete synthesis, netlist validity & 4-cycle waveform check (`checkRtlModule`,
    `synthesizeModuleToBels`, base Epoch 3 admit, replay Epoch 3 refuse, stale-pin Epoch 5 refuse,
    fresh-pin Epoch 5 admit). -/
example :
    checkRtlModule sovereignDrexBatchTopRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels sovereignDrexBatchTopRtlModule) = true ∧
    (let st0 : Nat → BitVec 64 := fun _ => 0#64
     let inEp3Base := mkDrexRtlInputs 8 3 0b0111 0 1000000 50000 50000 95000 75000 0 100
     let outEp3Base := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp3Base st0
     let st1 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp3Base st0
     let outReplay := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp3Base st1
     let st2 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp3Base st1
     let inEp5Stale := mkDrexRtlInputs 12 5 0b1111 1 1000000 50000 50000 95000 75000 0 164
     let outStale := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp5Stale st2
     let st3 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp5Stale st2
     let inEp5Fresh := mkDrexRtlInputs 12 5 0b1111 1 1000000 50000 50000 95000 75000 0 182
     let outFresh := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp5Fresh st3
     let st4 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp5Fresh st3
     outEp3Base.lookup "out_carry_pin_digest" = some 100#64 ∧
     outEp3Base.lookup "out_turn_admitted" = some 1#64 ∧
     st1 0 = 1#64 ∧ st1 1 = 3#64 ∧
     outReplay.lookup "out_epoch_monotone_ok" = some 0#64 ∧
     outReplay.lookup "out_turn_admitted" = some 0#64 ∧
     st2 0 = 1#64 ∧ st2 1 = 3#64 ∧
     outStale.lookup "out_carry_pin_digest" = some 182#64 ∧
     outStale.lookup "out_pin_fresh_ok" = some 0#64 ∧
     outStale.lookup "out_turn_admitted" = some 0#64 ∧
     st3 0 = 1#64 ∧ st3 1 = 3#64 ∧
     outFresh.lookup "out_pin_fresh_ok" = some 1#64 ∧
     outFresh.lookup "out_turn_admitted" = some 1#64 ∧
     st4 0 = 2#64 ∧ st4 1 = 5#64) := by
  decide +kernel

/-! ## 6. `#tooth` Mutation-Killing Guards -/

def brokenDrexRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames := ["in_lot_count"]
  , wires := []
  , regs := []
  , outputs := [{ name := "out_turn_admitted", expr := .const 1#64 }] }

#tooth sovereignDrexBatchTopRtlModule_epoch_replay_refused by mutation
  sovereignDrexBatchTopRtlModule := brokenDrexRtlModule

def brokenDrexCommittee4 : List Nat := [0, 1, 2, 3, 4, 5]

#tooth sovereignDrex_engine_and_bft_finality_sound by mutation
  drexCommittee4 := brokenDrexCommittee4

end Obend.Apps.SovereignDrex
end
