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
    universally verified synchronous batch-clearing + WAL anti-replay `RtlModule` (`sovereignDrexBatchTopRtlModule`),
- Cross-Chain L1 Settlement & Escrow Custody Gate (`G12`, closing `S1–S7`):
  * **`S1` Finality-Bound `2 × UInt128` Settlement:** lossless `DigestLimbs2x128` (`2 × BitVec 128`) state/effect/clearing
    roots, `SimplexProtocol.FinCert` (`n - f` quorum over `3f + 1 ≤ n`), `IrreversibleOutbox` `effectsRoot` binding,
    variable `1 ≤ turnCount` (`S6`), upgrade-authority genesis init (`S7`), and `nettingJudge` zero-sum conservation
    (`auditL1SettlementBatch_sound`, `unfinalized_fork_rejected`, `equal_height_settlement_unique_or_collision`),
  * **`S2` Domain-Separated Instruction Preimages:** length-framed `(domainTag, chainId, programId, clearingRoot,
    recipient, amount, nonce)` under distinct `"dregg-pool-unlock-v2"` vs `"dregg-escrow-release-v2"` tags +
    `ProvenClearingRoot` Merkle inclusion + SPL Token-2022 support (`poolUnlock_ne_escrowRelease_preimage`,
    `poolUnlock_rejected_by_escrowRelease`, `crossInstruction_digest_splice_rejected_or_collision`),
  * **`S3` Staggered Release vs Refund Windows:** `now ≤ tRelease` on release vs `tRelease + deltaFinality < now`
    (`0 < deltaFinality`) or `Simplex` abort `FinCert` on refund (`release_and_refund_mutually_exclusive`),
  * **`S4` `0x00/0x01` Merkle Domain Separation:** `0x00` leaf vs `0x01` internal node vs `0x02` empty framing +
    positional `(treeSize, leafIndex)` binding (`taggedLeaf_ne_taggedInternal_preimage`,
    `verifyTaggedMerkleProof256_sound_or_collision`, `taggedMerkle_refutes_64byte_splice`),
  * Multi-turn trace safety (`ValidL1SettlementTrace`, `sovereignDrex_l1_settlement_trace_safe`).
-/
public import Lean
public import Obend.Core.Digest
public import Obend.Receipt.Merkle
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Vault.UnifiedDeos
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
public import Obend.Tactic.Tooth
public import Obend.Elab.Workbook
import all Obend.Core.Digest
import all Obend.Receipt.Merkle
import all Obend.Vault.IrreversibleOutbox
import all Obend.Judge.Netting
import all Obend.Hardware.Compiler
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.Finality
meta import Lean
public meta import Obend.Elab.Workbook

public section

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

/-- Canonical 4-validator Simplex protocol (`N = 4, f = 1`, node `3` faulty) for `apps/sovereign-drex/`. -/
def drexProtocol4 : Protocol :=
  ⟨[0, 1, 2, 3], 1, (· == 3), by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Canonical 32-byte vault root digest for Epoch 3 finality promotion. -/
def drexVaultRoot : ByteArray :=
  ByteArray.mk (List.replicate 32 0xA5).toArray

/-- Canonical 3-of-4 `FinCert` (`[0, 1, 2]` finalizing `[.block 3 227]`) for Epoch 3. -/
def drexFinCert : FinCert :=
  ⟨3, [.block 3 227], [0, 1, 2]⟩

/-- Canonical 3-of-4 finalize votes in `Sent` matching `drexFinCert`. -/
def drexFinalizedSent : Sent :=
  [ ⟨0, 3, .finalize, .block [.block 3 227]⟩
  , ⟨1, 3, .finalize, .block [.block 3 227]⟩
  , ⟨2, 3, .finalize, .block [.block 3 227]⟩ ]

/-- Attested Simplex finality gate for Epoch 3 (`vaultRoot = drexVaultRoot`). -/
def drexAttestedGate : SimplexFinalityGate :=
  { turnId      := ByteArray.mk (List.replicate 32 0x03).toArray
    currentTier := .attested
    vaultRoot   := some drexVaultRoot }

/-- Promoted `.quorum_final` Simplex gate certified by `drexFinCert`. -/
def drexQuorumFinalGate : SimplexFinalityGate :=
  { drexAttestedGate with
    currentTier := .quorum_final
    finCert     := some drexFinCert
    vaultRoot   := some drexVaultRoot }

/-- **`sovereignDrex_engine_and_bft_finality_sound`**:
    1. Every admitted `stepUnifiedTurn S stateAssets turn postings = some S'` from a floor-valid
       `FloorBook` preserves `FloorsHold` (all non-issuer floors ≥ 0), conserves per-asset supply,
       realizes exact `Register.Reg` deltas, enforces ZoE `safeAt` across `S'.seats`, and refuses
       stale read footprints (`stepUnifiedTurn_refuses_stale_pin`),
    2. On `drexCommittee4` ($N = 4, f = 1$), `drexAttestedGate` promotes to `.quorum_final` via
       `advanceSimplexGate`, and any two conflicting 3-of-4 quorums `targetA ≠ targetB` yield a
       constructive `SlashingReceipt` catching `≥ 2` equivocating validators (`accountable`),
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
    advanceSimplexGate drexProtocol4 drexFinalizedSent drexAttestedGate
      (.finalizeWithCert drexFinCert drexVaultRoot) = some drexQuorumFinalGate ∧
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
      advanceSimplexGate drexProtocol4 drexFinalizedSent drexAttestedGate
        (.finalizeWithCert drexFinCert drexVaultRoot) = some drexQuorumFinalGate := by
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

/-! ## 6. Gate `G12` (`S4` & `S1` Root Carrier): Lossless `2 × UInt128` Digest Limbs & `0x00/0x01` Merkle Framing -/

open Obend.Core.Digest (Digest256)
open Obend.Digest.HashBytes (CollisionAmong be ofBE be_injective ofBE_lt length_be)
open Obend.Receipt.Merkle (SaltedLeaf256 BlindedNode256 ScopedCollision256 encodeFields
  encodeFields_injective leb128 leb128_injective bytesOfDigest256 bytesOfDigest256_injective
  hashBytes256 leafPreimage256 internalPreimage256 saltedSubtreeRoot256 saltedTreeRoot256
  evalBlindedNode256 buildBlindedMultiproof256 evalBlindedNode256_build extractSubtreeCollision
  subtreeScopePreimages defaultSaltedLeaf256)
open Obend.Vault.IrreversibleOutbox (EffectClass OutboxBound64 effectCommitBytes
  checkChainTipCommit checkChainTipCommit_sound SentSteps)

abbrev UInt128 := BitVec 128

structure DigestLimbs2x128 where
  hi : UInt128
  lo : UInt128
  deriving DecidableEq, Repr, Inhabited

namespace DigestLimbs2x128
def toDigest256 (x : DigestLimbs2x128) : Digest256 := BitVec.ofNat 256 (x.hi.toNat * 2 ^ 128 + x.lo.toNat)
def ofDigest256 (d : Digest256) : DigestLimbs2x128 := ⟨BitVec.ofNat 128 (d.toNat / 2 ^ 128), BitVec.ofNat 128 (d.toNat % 2 ^ 128)⟩
def toBytes32 (x : DigestLimbs2x128) : List UInt8 := be 16 x.hi.toNat ++ be 16 x.lo.toNat
def ofByteArray32? (bs : ByteArray) : Option DigestLimbs2x128 :=
  if bs.size == 32 then some (ofDigest256 (BitVec.ofNat 256 (ofBE bs.data.toList))) else none
def checkLimbsEq (a b : DigestLimbs2x128) : Bool := (a.hi == b.hi) && (a.lo == b.lo)
theorem limbs_lt_two_pow_128 (x : DigestLimbs2x128) : x.hi.toNat < 2 ^ 128 ∧ x.lo.toNat < 2 ^ 128 := ⟨x.hi.isLt, x.lo.isLt⟩
theorem toDigest256_ofDigest256 (d : Digest256) : (ofDigest256 d).toDigest256 = d := by
  apply BitVec.eq_of_toNat_eq; have hd := d.isLt; simp only [toDigest256, ofDigest256, BitVec.toNat_ofNat]; omega
theorem ofDigest256_toDigest256 (x : DigestLimbs2x128) : ofDigest256 x.toDigest256 = x := by
  have hhi := x.hi.isLt; have hlo := x.lo.isLt
  cases x with | mk hi lo =>
    dsimp only at hhi hlo; simp only [ofDigest256, toDigest256, DigestLimbs2x128.mk.injEq]
    constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega
theorem toDigest256_injective {x y : DigestLimbs2x128} (h : x.toDigest256 = y.toDigest256) : x = y := by
  rw [← ofDigest256_toDigest256 x, ← ofDigest256_toDigest256 y, h]
theorem ofDigest256_injective {a b : Digest256} (h : ofDigest256 a = ofDigest256 b) : a = b := by
  rw [← toDigest256_ofDigest256 a, ← toDigest256_ofDigest256 b, h]
@[simp] theorem toBytes32_length (x : DigestLimbs2x128) : x.toBytes32.length = 32 := by simp [toBytes32, length_be]
theorem toBytes32_injective {x y : DigestLimbs2x128} (h : x.toBytes32 = y.toBytes32) : x = y := by
  unfold toBytes32 at h; obtain ⟨hHi, hLo⟩ := List.append_inj h (by simp [length_be])
  have hpow : (2 : Nat) ^ 128 = 256 ^ 16 := by decide
  have hHiEq := BitVec.eq_of_toNat_eq (be_injective (hpow ▸ x.hi.isLt) (hpow ▸ y.hi.isLt) hHi)
  have hLoEq := BitVec.eq_of_toNat_eq (be_injective (hpow ▸ x.lo.isLt) (hpow ▸ y.lo.isLt) hLo)
  cases x; cases y; simp only [DigestLimbs2x128.mk.injEq] at *; exact ⟨hHiEq, hLoEq⟩
theorem checkLimbsEq_iff (a b : DigestLimbs2x128) : checkLimbsEq a b = true ↔ a = b := by
  cases a; cases b; simp only [checkLimbsEq, Bool.and_eq_true, beq_iff_eq, DigestLimbs2x128.mk.injEq]
@[simp] theorem checkLimbsEq_refl (a : DigestLimbs2x128) : checkLimbsEq a a = true := (checkLimbsEq_iff a a).2 rfl
end DigestLimbs2x128

def merkleLeafTagByte : UInt8 := 0x00
def merkleInternalTagByte : UInt8 := 0x01
def merkleEmptyTagByte : UInt8 := 0x02
def encodeTaggedLeafPreimage (leafIndex : Nat) (salt : Digest256) (payload : List UInt8) : List UInt8 :=
  encodeFields [[merkleLeafTagByte], leb128 leafIndex, bytesOfDigest256 salt, payload]
def encodeTaggedInternalPreimage (spanSize startIdx : Nat) (left right : Digest256) : List UInt8 :=
  encodeFields [[merkleInternalTagByte], leb128 spanSize, leb128 startIdx, bytesOfDigest256 left, bytesOfDigest256 right]
def encodeTaggedEmptyPreimage : List UInt8 := encodeFields [[merkleEmptyTagByte]]
private theorem encodeTaggedLeafPreimage_eq_merkle (idx : Nat) (salt : Digest256) (p : List UInt8) :
    encodeTaggedLeafPreimage idx salt p = leafPreimage256 idx salt p := rfl
private theorem encodeTaggedInternalPreimage_eq_merkle (sz st : Nat) (l r : Digest256) :
    encodeTaggedInternalPreimage sz st l r = internalPreimage256 sz st l r := rfl
theorem taggedLeaf_ne_taggedInternal_preimage (leafIndex : Nat) (salt : Digest256)
    (payload : List UInt8) (spanSize startIdx : Nat) (left right : Digest256) :
    encodeTaggedLeafPreimage leafIndex salt payload ≠ encodeTaggedInternalPreimage spanSize startIdx left right := by
  intro h; have hTag : ([merkleLeafTagByte] : List UInt8) = [merkleInternalTagByte] :=
    (List.cons.inj (encodeFields_injective _ _ h)).1
  exact absurd (List.cons.inj hTag).1 (by decide)
def taggedLeavesOfPayloads (payloads : List (List UInt8)) : List SaltedLeaf256 := payloads.map (fun p => ⟨0#256, p⟩)
@[simp] theorem taggedLeavesOfPayloads_length (payloads : List (List UInt8)) :
    (taggedLeavesOfPayloads payloads).length = payloads.length := by simp [taggedLeavesOfPayloads]
private theorem taggedLeaves_getD (payloads : List (List UInt8)) (i : Nat) :
    (taggedLeavesOfPayloads payloads).getD i defaultSaltedLeaf256 = ⟨0#256, payloads.getD i []⟩ := by
  induction payloads generalizing i with
  | nil => rfl
  | cons _ _ ih => cases i with | zero => rfl | succ k => exact ih k
def computeTaggedSubtree256 (H : Obend.Digest.HashBytes.Hash) (startIdx : Nat) (slice : List (List UInt8)) : Digest256 :=
  saltedSubtreeRoot256 H startIdx (taggedLeavesOfPayloads slice)
def computeTaggedMerkleRoot256 (H : Obend.Digest.HashBytes.Hash) (payloads : List (List UInt8)) : Digest256 :=
  saltedTreeRoot256 H (taggedLeavesOfPayloads payloads)
structure TaggedMerkleProof256 where
  treeSize  : Nat
  leafIndex : Nat
  payload   : List UInt8
  tree      : BlindedNode256
  deriving DecidableEq, Repr
def buildTaggedMerkleProof256 (H : Obend.Digest.HashBytes.Hash) (payloads : List (List UInt8)) (leafIndex : Nat) : TaggedMerkleProof256 :=
  let mp := buildBlindedMultiproof256 H (taggedLeavesOfPayloads payloads) [leafIndex]
  ⟨mp.treeSize, leafIndex, payloads.getD leafIndex [], mp.tree⟩
def checkLeafIndexInBounds (leafIndex treeSize : Nat) : Bool := decide (leafIndex < treeSize)
def verifyTaggedMerkleProof256 (H : Obend.Digest.HashBytes.Hash) (proof : TaggedMerkleProof256) (expectedRoot : Digest256) : Bool :=
  checkLeafIndexInBounds proof.leafIndex proof.treeSize &&
  match evalBlindedNode256 H proof.tree proof.treeSize 0 with
  | some (r, [(idx, ⟨salt, pay⟩)]) => r == expectedRoot && idx == proof.leafIndex && salt == 0#256 && pay == proof.payload
  | _ => false
theorem verifyTaggedMerkleProof256_complete (H : Obend.Digest.HashBytes.Hash)
    (payloads : List (List UInt8)) (leafIndex : Nat) (hIdx : leafIndex < payloads.length) :
    verifyTaggedMerkleProof256 H (buildTaggedMerkleProof256 H payloads leafIndex) (computeTaggedMerkleRoot256 H payloads) = true := by
  have hRange : ∀ i ∈ [leafIndex], 0 ≤ i ∧ i < 0 + (taggedLeavesOfPayloads payloads).length := by
    intro i hi; rcases List.mem_singleton.mp hi with rfl; exact ⟨Nat.zero_le _, by simp [hIdx]⟩
  have hEv := evalBlindedNode256_build H (taggedLeavesOfPayloads payloads) 0 [leafIndex] (List.pairwise_singleton _ _) hRange
  rw [List.map_singleton, Nat.sub_zero, taggedLeaves_getD] at hEv
  unfold verifyTaggedMerkleProof256 buildTaggedMerkleProof256 computeTaggedMerkleRoot256 saltedTreeRoot256 checkLeafIndexInBounds
  dsimp only [buildBlindedMultiproof256]; rw [hEv]; simp [hIdx]
def taggedMerkleScopePreimages (H : Obend.Digest.HashBytes.Hash) (payloads : List (List UInt8)) (proof : TaggedMerkleProof256) : List (List UInt8) :=
  subtreeScopePreimages H 0 (taggedLeavesOfPayloads payloads) proof.tree
def extractTaggedMerkleBinding (H : Obend.Digest.HashBytes.Hash) (payloads : List (List UInt8)) (proof : TaggedMerkleProof256)
    (hEv : evalBlindedNode256 H proof.tree (taggedLeavesOfPayloads payloads).length 0 =
           some (computeTaggedMerkleRoot256 H payloads, [(proof.leafIndex, ⟨0#256, proof.payload⟩)])) :
    PSum (PLift (payloads[proof.leafIndex]? = some proof.payload)) (ScopedCollision256 H (taggedMerkleScopePreimages H payloads proof)) :=
  match extractSubtreeCollision H proof.tree (taggedLeavesOfPayloads payloads) 0 [(proof.leafIndex, ⟨0#256, proof.payload⟩)] hEv with
  | .inl ok => PSum.inl ⟨by
      have hGet := ok proof.leafIndex ⟨0#256, proof.payload⟩ List.mem_cons_self
      rw [Nat.sub_zero, taggedLeavesOfPayloads, List.getElem?_map] at hGet
      cases hp : payloads[proof.leafIndex]? with
      | none => rw [hp] at hGet; cases hGet
      | some _ => rw [hp] at hGet; injection hGet with hLeaf; injection hLeaf with _ hPay; rw [hPay]⟩
  | .inr col => PSum.inr col
theorem verifyTaggedMerkleProof256_sound_or_collision (H : Obend.Digest.HashBytes.Hash)
    (payloads : List (List UInt8)) (proof : TaggedMerkleProof256) (hSize : proof.treeSize = payloads.length)
    (hVer : verifyTaggedMerkleProof256 H proof (computeTaggedMerkleRoot256 H payloads) = true) :
    (proof.leafIndex < payloads.length ∧ payloads[proof.leafIndex]? = some proof.payload) ∨
    Nonempty (ScopedCollision256 H (taggedMerkleScopePreimages H payloads proof)) := by
  unfold verifyTaggedMerkleProof256 at hVer; obtain ⟨hB, hMatch⟩ := (Bool.and_eq_true _ _).mp hVer
  have hLt : proof.leafIndex < payloads.length := hSize ▸ of_decide_eq_true hB
  cases hEv : evalBlindedNode256 H proof.tree proof.treeSize 0 with
  | none => rw [hEv] at hMatch; cases hMatch
  | some pair =>
    rcases pair with ⟨r, opened⟩; cases opened with
    | nil => rw [hEv] at hMatch; cases hMatch
    | cons hd tl => cases tl with
      | cons _ _ => rw [hEv] at hMatch; cases hMatch
      | nil =>
        rcases hd with ⟨idx, salt, pay⟩; rw [hEv] at hMatch; dsimp only at hMatch
        simp only [Bool.and_eq_true, beq_iff_eq] at hMatch; rcases hMatch with ⟨⟨⟨hR, hI⟩, hS⟩, hP⟩; subst hR hI hS hP
        have hEv' : evalBlindedNode256 H proof.tree (taggedLeavesOfPayloads payloads).length 0 =
            some (computeTaggedMerkleRoot256 H payloads, [(proof.leafIndex, ⟨0#256, proof.payload⟩)]) := by
          rw [taggedLeavesOfPayloads_length, ← hSize]; exact hEv
        match extractTaggedMerkleBinding H payloads proof hEv' with
        | .inl ok => exact .inl ⟨hLt, ok.down⟩
        | .inr col => exact .inr ⟨col⟩
def spliced64Payload (left right : Digest256) : List UInt8 := bytesOfDigest256 left ++ bytesOfDigest256 right
@[simp] theorem spliced64Payload_length (left right : Digest256) : (spliced64Payload left right).length = 64 := by
  simp [spliced64Payload, bytesOfDigest256, length_be]
theorem taggedMerkle_refutes_64byte_splice (H : Obend.Digest.HashBytes.Hash)
    (payloads : List (List UInt8)) (hGe2 : 2 ≤ payloads.length) (idx : Nat) (left right : Digest256) :
    let pay64 := spliced64Payload left right
    verifyTaggedMerkleProof256 H ⟨payloads.length, idx, pay64, .openedLeaf idx 0#256 pay64⟩ (computeTaggedMerkleRoot256 H payloads) = false ∧
    (let rootSplice : TaggedMerkleProof256 := ⟨1, 0, pay64, .openedLeaf 0 0#256 pay64⟩
     verifyTaggedMerkleProof256 H rootSplice (computeTaggedMerkleRoot256 H payloads) = false ∨
     Nonempty (ScopedCollision256 H
       [encodeTaggedLeafPreimage 0 0#256 pay64,
        encodeTaggedInternalPreimage payloads.length 0
          (computeTaggedSubtree256 H 0 (payloads.take (payloads.length / 2)))
          (computeTaggedSubtree256 H (payloads.length / 2) (payloads.drop (payloads.length / 2)))])) := by
  dsimp only; refine ⟨?_, ?_⟩
  · have hNe1 : (payloads.length == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
    unfold verifyTaggedMerkleProof256 evalBlindedNode256; dsimp only; rw [hNe1, Bool.false_and]; simp
  · let pay64 := spliced64Payload left right
    let rootSplice : TaggedMerkleProof256 := ⟨1, 0, pay64, .openedLeaf 0 0#256 pay64⟩
    cases hv : verifyTaggedMerkleProof256 H rootSplice (computeTaggedMerkleRoot256 H payloads) with
    | false => exact .inl rfl
    | true =>
      have hLeafEq : hashBytes256 H (encodeTaggedLeafPreimage 0 0#256 pay64) = computeTaggedMerkleRoot256 H payloads := by
        rw [encodeTaggedLeafPreimage_eq_merkle]
        simp [verifyTaggedMerkleProof256, evalBlindedNode256, checkLeafIndexInBounds, rootSplice] at hv; exact hv
      have h0 : payloads.length ≠ 0 := by omega
      have h1 : payloads.length ≠ 1 := by omega
      have hTreeEq : computeTaggedMerkleRoot256 H payloads =
          hashBytes256 H (encodeTaggedInternalPreimage payloads.length 0
            (computeTaggedSubtree256 H 0 (payloads.take (payloads.length / 2)))
            (computeTaggedSubtree256 H (payloads.length / 2) (payloads.drop (payloads.length / 2)))) := by
        unfold computeTaggedMerkleRoot256 saltedTreeRoot256; rw [saltedSubtreeRoot256]
        simp only [taggedLeavesOfPayloads_length, h0, h1, ↓reduceIte, Nat.zero_add]
        simp only [encodeTaggedInternalPreimage_eq_merkle, computeTaggedSubtree256, taggedLeavesOfPayloads, List.map_take, List.map_drop]
      rw [hTreeEq] at hLeafEq
      exact .inr ⟨⟨_, _, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
        taggedLeaf_ne_taggedInternal_preimage _ _ _ _ _ _ _, hLeafEq⟩⟩

/-! ## 7. Gate `G12` (`S2` & `S7`): Domain-Separated Pool-Unlock vs Escrow-Release Preimages -/

inductive L1VaultInstructionKind where | poolUnlock | escrowRelease deriving DecidableEq, Repr, Inhabited
def dreggPoolUnlockV2Tag : List UInt8 :=
  [0x64, 0x72, 0x65, 0x67, 0x67, 0x2d, 0x70, 0x6f, 0x6f, 0x6c, 0x2d, 0x75, 0x6e, 0x6c, 0x6f, 0x63, 0x6b, 0x2d, 0x76, 0x32]
def dreggEscrowReleaseV2Tag : List UInt8 :=
  [0x64, 0x72, 0x65, 0x67, 0x67, 0x2d, 0x65, 0x73, 0x63, 0x72, 0x6f, 0x77, 0x2d, 0x72, 0x65, 0x6c, 0x65, 0x61, 0x73, 0x65, 0x2d, 0x76, 0x32]
def L1VaultInstructionKind.domainTagName : L1VaultInstructionKind → String
  | .poolUnlock => "dregg-pool-unlock-v2" | .escrowRelease => "dregg-escrow-release-v2"
def L1VaultInstructionKind.domainTagBytes : L1VaultInstructionKind → List UInt8
  | .poolUnlock => dreggPoolUnlockV2Tag | .escrowRelease => dreggEscrowReleaseV2Tag
theorem L1VaultInstructionKind.domainTagBytes_injective {k₁ k₂ : L1VaultInstructionKind}
    (h : k₁.domainTagBytes = k₂.domainTagBytes) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | exact absurd h (by decide)
inductive L1TokenProgram where | splTokenLegacy | splToken2022 | nativeOrErc20 deriving DecidableEq, Repr, Inhabited
structure L1InstructionClaim where
  chainId      : UInt64
  programId    : Digest256
  clearingRoot : DigestLimbs2x128
  recipient    : Digest256
  amount       : UInt64
  nonce        : UInt64
  deriving DecidableEq, Repr
def encodeL1InstructionPreimage (kind : L1VaultInstructionKind) (c : L1InstructionClaim) : List UInt8 :=
  encodeFields [kind.domainTagBytes, be 8 c.chainId.toNat, bytesOfDigest256 c.programId,
    c.clearingRoot.toBytes32, bytesOfDigest256 c.recipient, be 8 c.amount.toNat, be 8 c.nonce.toNat]
def l1InstructionDigest256 (H : Obend.Digest.HashBytes.Hash) (kind : L1VaultInstructionKind) (c : L1InstructionClaim) : Digest256 :=
  hashBytes256 H (encodeL1InstructionPreimage kind c)
theorem encodeL1InstructionPreimage_injective {k₁ k₂ : L1VaultInstructionKind} {c₁ c₂ : L1InstructionClaim}
    (h : encodeL1InstructionPreimage k₁ c₁ = encodeL1InstructionPreimage k₂ c₂) : k₁ = k₂ ∧ c₁ = c₂ := by
  have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hDom, hChain, hProg, hClear, hRecip, hAmt, hNonce⟩
  have hpow64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hk := L1VaultInstructionKind.domainTagBytes_injective hDom
  have hcChain := UInt64.toNat_inj.mp (be_injective (hpow64 ▸ c₁.chainId.toNat_lt) (hpow64 ▸ c₂.chainId.toNat_lt) hChain)
  have hcAmt := UInt64.toNat_inj.mp (be_injective (hpow64 ▸ c₁.amount.toNat_lt) (hpow64 ▸ c₂.amount.toNat_lt) hAmt)
  have hcNonce := UInt64.toNat_inj.mp (be_injective (hpow64 ▸ c₁.nonce.toNat_lt) (hpow64 ▸ c₂.nonce.toNat_lt) hNonce)
  have hcProg := bytesOfDigest256_injective hProg; have hcClear := DigestLimbs2x128.toBytes32_injective hClear
  have hcRecip := bytesOfDigest256_injective hRecip
  cases c₁; cases c₂; simp only [L1InstructionClaim.mk.injEq] at *; exact ⟨hk, hcChain, hcProg, hcClear, hcRecip, hcAmt, hcNonce⟩
theorem poolUnlock_ne_escrowRelease_preimage (c₁ c₂ : L1InstructionClaim) :
    encodeL1InstructionPreimage .poolUnlock c₁ ≠ encodeL1InstructionPreimage .escrowRelease c₂ :=
  fun h => nomatch (encodeL1InstructionPreimage_injective h).1
structure L1VaultConfig where
  chainId               : UInt64
  programId             : Digest256
  upgradeAuthority      : Digest256
  acceptedTokenPrograms : List L1TokenProgram
  deriving DecidableEq, Repr
structure L1InstructionAuth where
  authorizedKind    : L1VaultInstructionKind
  claim             : L1InstructionClaim
  tokenProgram      : L1TokenProgram
  attestationDigest : Digest256
  clearingLeafProof : TaggedMerkleProof256
  deriving DecidableEq, Repr
inductive EscrowLifecycleStatus where | locked | released | refunded deriving DecidableEq, Repr, Inhabited
inductive L1SettlementRefusal where
  | unauthorizedGenesisInit | instructionDomainMismatch (expected actual : L1VaultInstructionKind)
  | chainIdMismatch (expected actual : UInt64) | programIdMismatch | unsupportedTokenProgram (prog : L1TokenProgram)
  | zeroTransferAmount | replayNonceConsumed (nonce : UInt64) | unprovenClearingRoot | attestationDigestMismatch
  | clearingLeafPayloadMismatch | invalidMerkleInclusionProof | escrowNotFound (idx : Nat)
  | escrowAlreadyTerminal (status : EscrowLifecycleStatus) | zeroFinalityDelta | releaseWindowExpired (now tRelease : Nat)
  | refundBeforeFinalityBuffer (now tRelease deltaFinality : Nat) | escrowClaimFieldMismatch
  | invalidSwapCommitCert | invalidSwapAbortCert | swapAlreadyCommitted | nonMonotoneSettlementEpoch (prev next : Nat)
  | zeroTurnBatch | prevStateRootMismatch | nonMonotoneFinalizedHeight (prev next : Nat)
  | missingOrInvalidFinCert | malformedOrMismatchedEffectsRoot | mismatchedClearingRoot | nettingConservationRefused
  deriving DecidableEq, Repr
def auditL1InstructionAuth (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig) (provenClearingRoots : List DigestLimbs2x128)
    (consumedNonces : List UInt64) (expectedKind : L1VaultInstructionKind) (auth : L1InstructionAuth) :
    Except L1SettlementRefusal Digest256 :=
  if auth.authorizedKind != expectedKind then .error (.instructionDomainMismatch expectedKind auth.authorizedKind)
  else if auth.claim.chainId != cfg.chainId then .error (.chainIdMismatch cfg.chainId auth.claim.chainId)
  else if auth.claim.programId != cfg.programId then .error .programIdMismatch
  else if !cfg.acceptedTokenPrograms.contains auth.tokenProgram then .error (.unsupportedTokenProgram auth.tokenProgram)
  else if auth.claim.amount == 0 then .error .zeroTransferAmount
  else if consumedNonces.contains auth.claim.nonce then .error (.replayNonceConsumed auth.claim.nonce)
  else if !provenClearingRoots.contains auth.claim.clearingRoot then .error .unprovenClearingRoot
  else
    let expectedPreimage := encodeL1InstructionPreimage expectedKind auth.claim
    let expectedDigest := l1InstructionDigest256 H expectedKind auth.claim
    if auth.attestationDigest != expectedDigest then .error .attestationDigestMismatch
    else if auth.clearingLeafProof.payload != expectedPreimage then .error .clearingLeafPayloadMismatch
    else if !verifyTaggedMerkleProof256 H auth.clearingLeafProof auth.claim.clearingRoot.toDigest256 then
      .error .invalidMerkleInclusionProof
    else .ok expectedDigest
def auditPoolUnlock (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig) (provenClearingRoots : List DigestLimbs2x128)
    (consumedNonces : List UInt64) (auth : L1InstructionAuth) : Except L1SettlementRefusal Digest256 :=
  auditL1InstructionAuth H cfg provenClearingRoots consumedNonces .poolUnlock auth
def auditEscrowReleaseAuth (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig) (provenClearingRoots : List DigestLimbs2x128)
    (consumedNonces : List UInt64) (auth : L1InstructionAuth) : Except L1SettlementRefusal Digest256 :=
  auditL1InstructionAuth H cfg provenClearingRoots consumedNonces .escrowRelease auth
private theorem eq_of_not_bne {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : ¬ ((a != b) = true)) : a = b := by
  cases hb : (a == b); · exfalso; apply h; simp [bne, hb]
  exact beq_iff_eq.mp hb
private theorem of_not_bnot {b : Bool} (h : ¬ ((!b) = true)) : b = true := by
  cases b; · exfalso; exact h rfl
  rfl
private theorem attestation_eq_of_auditL1InstructionAuth_ok {H : Obend.Digest.HashBytes.Hash} {cfg : L1VaultConfig}
    {roots : List DigestLimbs2x128} {nonces : List UInt64} {kind : L1VaultInstructionKind} {auth : L1InstructionAuth} {d : Digest256}
    (h : auditL1InstructionAuth H cfg roots nonces kind auth = .ok d) :
    auth.authorizedKind = kind ∧ auth.claim.nonce ∉ nonces ∧ auth.attestationDigest = l1InstructionDigest256 H kind auth.claim := by
  unfold auditL1InstructionAuth at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  dsimp only at h; split at h; · cases h
  rename_i hKind _ _ _ _ hNonce _ hAtt
  exact ⟨eq_of_not_bne hKind, fun hm => hNonce (List.contains_iff_mem.mpr hm), eq_of_not_bne hAtt⟩
theorem poolUnlock_rejected_by_escrowRelease (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig)
    (roots : List DigestLimbs2x128) (nonces : List UInt64) (auth : L1InstructionAuth) {d : Digest256}
    (hPool : auditPoolUnlock H cfg roots nonces auth = .ok d) :
    auditEscrowReleaseAuth H cfg roots nonces auth = .error (.instructionDomainMismatch .escrowRelease .poolUnlock) := by
  have hk := (attestation_eq_of_auditL1InstructionAuth_ok hPool).1
  unfold auditEscrowReleaseAuth auditL1InstructionAuth; simp [hk]
theorem escrowRelease_rejected_by_poolUnlock (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig)
    (roots : List DigestLimbs2x128) (nonces : List UInt64) (auth : L1InstructionAuth) {d : Digest256}
    (hEsc : auditEscrowReleaseAuth H cfg roots nonces auth = .ok d) :
    auditPoolUnlock H cfg roots nonces auth = .error (.instructionDomainMismatch .poolUnlock .escrowRelease) := by
  have hk := (attestation_eq_of_auditL1InstructionAuth_ok hEsc).1
  unfold auditPoolUnlock auditL1InstructionAuth; simp [hk]
def crossInstruction_digest_splice_rejected_or_collision (H : Obend.Digest.HashBytes.Hash) (cfg : L1VaultConfig)
    (roots : List DigestLimbs2x128) (nonces : List UInt64) (poolClaim escClaim : L1InstructionClaim)
    (tok : L1TokenProgram) (prf : TaggedMerkleProof256) :
    let forgedAuth : L1InstructionAuth := ⟨.escrowRelease, escClaim, tok, l1InstructionDigest256 H .poolUnlock poolClaim, prf⟩
    PSum (PLift ((auditEscrowReleaseAuth H cfg roots nonces forgedAuth).isOk = false))
      (ScopedCollision256 H [encodeL1InstructionPreimage .poolUnlock poolClaim, encodeL1InstructionPreimage .escrowRelease escClaim]) :=
  let forgedAuth : L1InstructionAuth := ⟨.escrowRelease, escClaim, tok, l1InstructionDigest256 H .poolUnlock poolClaim, prf⟩
  match hRes : auditEscrowReleaseAuth H cfg roots nonces forgedAuth with
  | .error _ => PSum.inl ⟨by rw [hRes]; rfl⟩
  | .ok _ => PSum.inr ⟨_, _, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
      poolUnlock_ne_escrowRelease_preimage poolClaim escClaim, (attestation_eq_of_auditL1InstructionAuth_ok hRes).2.2⟩

/-! ## 8. Gate `G12` (`S3`): Staggered Non-Overlapping Release vs Refund Windows & `Simplex` Abort Certs -/

inductive SwapDecisionKind where | commitSwap (clearingRoot : DigestLimbs2x128) | abortSwap deriving DecidableEq, Repr
def swapDecisionDomain : List UInt8 :=
  [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x44, 0x52, 0x45, 0x58, 0x2D, 0x53, 0x57, 0x41, 0x50, 0x2D, 0x44, 0x45, 0x43, 0x49, 0x53, 0x49, 0x4F, 0x4E, 0x2D, 0x56, 0x32]
def cshakeSwapDecisionHash : Obend.Digest.HashBytes.Hash := Obend.Digest.Cshake256.cshake256Bytes swapDecisionDomain
theorem cshakeSwapDecisionHash_length_32 (msg : List UInt8) : (cshakeSwapDecisionHash msg).length = 32 := by simp [cshakeSwapDecisionHash]
def encodeSwapDecisionPreimage (swapId : Digest256) : SwapDecisionKind → List UInt8
  | .commitSwap root => encodeFields [[0x01], bytesOfDigest256 swapId, root.toBytes32]
  | .abortSwap => encodeFields [[0x02], bytesOfDigest256 swapId]
theorem encodeSwapDecisionPreimage_injective {s₁ s₂ : Digest256} {d₁ d₂ : SwapDecisionKind}
    (h : encodeSwapDecisionPreimage s₁ d₁ = encodeSwapDecisionPreimage s₂ d₂) : s₁ = s₂ ∧ d₁ = d₂ := by
  cases d₁ <;> cases d₂
  · have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, true_and, and_true] at hf
    exact ⟨bytesOfDigest256_injective hf.1, congrArg SwapDecisionKind.commitSwap (DigestLimbs2x128.toBytes32_injective hf.2)⟩
  · have hf := encodeFields_injective _ _ h; simp at hf
  · have hf := encodeFields_injective _ _ h; simp at hf
  · have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, true_and, and_true] at hf
    exact ⟨bytesOfDigest256_injective hf, rfl⟩
theorem commitSwap_ne_abortSwap_preimage (s₁ s₂ : Digest256) (r : DigestLimbs2x128) :
    encodeSwapDecisionPreimage s₁ (.commitSwap r) ≠ encodeSwapDecisionPreimage s₂ .abortSwap :=
  fun h => nomatch (encodeSwapDecisionPreimage_injective h).2
def swapDecisionCommitNat (H : Obend.Digest.HashBytes.Hash) (swapId : Digest256) (dec : SwapDecisionKind) : Nat :=
  ofBE ((H (encodeSwapDecisionPreimage swapId dec)).take 32)
theorem swapDecisionCommitNat_lt (H : Obend.Digest.HashBytes.Hash) (swapId : Digest256) (dec : SwapDecisionKind) :
    swapDecisionCommitNat H swapId dec < 256 ^ 32 :=
  Nat.lt_of_lt_of_le (ofBE_lt _) (Nat.pow_le_pow_right (by decide) (List.length_take_le 32 _))
def checkReleaseWindow (now tRelease : Nat) : Bool := decide (now ≤ tRelease)
def checkTimeoutRefundWindow (now tRelease deltaFinality : Nat) : Bool := decide (0 < deltaFinality) && decide (tRelease + deltaFinality < now)
structure CrossChainEscrow where
  escrowId       : UInt64
  swapId         : Digest256
  decisionHeight : Nat
  depositor      : Digest256
  beneficiary    : Digest256
  amount         : UInt64
  tRelease       : Nat
  deltaFinality  : Nat
  status         : EscrowLifecycleStatus := .locked
  paidRelease    : Nat := 0
  paidRefund     : Nat := 0
  deriving DecidableEq, Repr
inductive EscrowRefundReason where | postWindowTimeout | certifiedSimplexAbort (abortCert : FinCert) deriving DecidableEq, Repr
inductive EscrowAction where
  | release (now : Nat) (commitCert : FinCert) (auth : L1InstructionAuth)
  | refund (now : Nat) (reason : EscrowRefundReason)
  deriving DecidableEq, Repr
def auditCrossChainEscrowStep (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (sent : Sent) (cfg : L1VaultConfig)
    (provenClearingRoots : List DigestLimbs2x128) (committedSwapIds : List Digest256) (consumedNonces : List UInt64)
    (esc : CrossChainEscrow) (act : EscrowAction) : Except L1SettlementRefusal CrossChainEscrow :=
  if esc.status != .locked then .error (.escrowAlreadyTerminal esc.status)
  else if !decide (0 < esc.deltaFinality) then .error .zeroFinalityDelta
  else match act with
    | .release now commitCert auth =>
      if !checkReleaseWindow now esc.tRelease then .error (.releaseWindowExpired now esc.tRelease)
      else if !(commitCert.checks P sent && decide (commitCert.chain.height = esc.decisionHeight) &&
                checkChainTipCommit commitCert.chain commitCert.view
                  (swapDecisionCommitNat H esc.swapId (.commitSwap auth.claim.clearingRoot))) then .error .invalidSwapCommitCert
      else if !(auth.claim.recipient == esc.beneficiary && auth.claim.amount == esc.amount && auth.claim.nonce == esc.escrowId) then
        .error .escrowClaimFieldMismatch
      else match auditEscrowReleaseAuth H cfg provenClearingRoots consumedNonces auth with
        | .error e => .error e
        | .ok _ => .ok { esc with status := .released, paidRelease := esc.amount.toNat, paidRefund := 0 }
    | .refund now .postWindowTimeout =>
      if !checkTimeoutRefundWindow now esc.tRelease esc.deltaFinality then .error (.refundBeforeFinalityBuffer now esc.tRelease esc.deltaFinality)
      else if committedSwapIds.contains esc.swapId then .error .swapAlreadyCommitted
      else .ok { esc with status := .refunded, paidRelease := 0, paidRefund := esc.amount.toNat }
    | .refund _ (.certifiedSimplexAbort abortCert) =>
      if !(abortCert.checks P sent && decide (abortCert.chain.height = esc.decisionHeight) &&
           checkChainTipCommit abortCert.chain abortCert.view (swapDecisionCommitNat H esc.swapId .abortSwap)) then
        .error .invalidSwapAbortCert
      else .ok { esc with status := .refunded, paidRelease := 0, paidRefund := esc.amount.toNat }
private theorem getLast_blocks_eq_of_block_tip {c₁ c₂ : Chain} {v₁ p₁ v₂ p₂ : Nat}
    (hBlocks : c₁.blocks = c₂.blocks) (hTip₁ : c₁.getLast? = some (.block v₁ p₁)) (hTip₂ : c₂.getLast? = some (.block v₂ p₂)) : p₁ = p₂ := by
  have last_filter_block : ∀ (xs : Chain) (v p : Nat), xs.getLast? = some (.block v p) → (xs.blocks).getLast? = some (.block v p) := by
    intro xs; induction xs with
    | nil => intro _ _ h; cases h
    | cons x rest ih =>
      intro v p h; cases rest with
      | nil => simp only [List.getLast?_singleton, Option.some.injEq] at h; subst h; rfl
      | cons y ys =>
        have ihR := ih v p (by simpa using h)
        have hStep : Chain.blocks (x :: y :: ys) =
            (match x.isBlock with | true => x :: Chain.blocks (y :: ys) | false => Chain.blocks (y :: ys)) := rfl
        rw [hStep]; cases Entry.isBlock x
        · exact ihR
        · dsimp only; cases hF : Chain.blocks (y :: ys) with
          | nil => rw [hF] at ihR; cases ihR
          | cons _ _ => rw [hF] at ihR; exact ihR
  have hb₁ := last_filter_block c₁ v₁ p₁ hTip₁; have hb₂ := last_filter_block c₂ v₂ p₂ hTip₂
  rw [hBlocks] at hb₁; rw [hb₁] at hb₂; injection hb₂ with hEnt; injection hEnt with _ hp
theorem release_and_refund_mutually_exclusive (now tRelease deltaFinality : Nat) :
    ¬ (checkReleaseWindow now tRelease = true ∧ checkTimeoutRefundWindow now tRelease deltaFinality = true) ∧
    (0 < deltaFinality → checkReleaseWindow (tRelease + 1) tRelease = false ∧ checkTimeoutRefundWindow (tRelease + 1) tRelease deltaFinality = false) ∧
    (∀ {P : Protocol} {H : Obend.Digest.HashBytes.Hash} {sent : Sent} (_hReach : Reach P sent) (_hLen32 : ∀ m, (H m).length = 32)
       (cfgA cfgB : L1VaultConfig) (rootsA rootsB : List DigestLimbs2x128) (committedA committedB : List Digest256)
       (noncesA noncesB : List UInt64) (esc : CrossChainEscrow) (nowRel nowRef : Nat) (commitCert : FinCert)
       (auth : L1InstructionAuth) (escRel escRef : CrossChainEscrow),
       auditCrossChainEscrowStep P H sent cfgA rootsA committedA noncesA esc (.release nowRel commitCert auth) = .ok escRel →
       ((auditCrossChainEscrowStep P H sent cfgB rootsB committedB noncesB esc (.refund nowRel .postWindowTimeout) = .ok escRef → False) ∧
        ((nowRel + esc.deltaFinality < nowRef → esc.swapId ∈ committedB) →
          auditCrossChainEscrowStep P H sent cfgB rootsB committedB noncesB esc (.refund nowRef .postWindowTimeout) = .ok escRef → False) ∧
        (∀ abortCert : FinCert,
          auditCrossChainEscrowStep P H sent cfgB rootsB committedB noncesB esc (.refund nowRef (.certifiedSimplexAbort abortCert)) = .ok escRef →
          CollisionAmong H (fun m => m = encodeSwapDecisionPreimage esc.swapId (.commitSwap auth.claim.clearingRoot) ∨
            m = encodeSwapDecisionPreimage esc.swapId .abortSwap)) ∧
        (escRel.status = .released ∧ escRel.paidRelease + escRel.paidRefund = esc.amount.toNat ∧
         ∀ nextAct : EscrowAction,
           auditCrossChainEscrowStep P H sent cfgA rootsA committedA noncesA escRel nextAct = .error (.escrowAlreadyTerminal .released)))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hRel, hRef⟩; simp only [checkReleaseWindow, checkTimeoutRefundWindow, Bool.and_eq_true, decide_eq_true_eq] at hRel hRef; omega
  · intro _; simp only [checkReleaseWindow, checkTimeoutRefundWindow, Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact ⟨by omega, .inr (by omega)⟩
  · intro P H sent hReach hLen32 cfgA cfgB rootsA rootsB committedA committedB noncesA noncesB esc nowRel nowRef commitCert auth escRel escRef hRelStep
    unfold auditCrossChainEscrowStep at hRelStep
    split at hRelStep; · cases hRelStep
    split at hRelStep; · cases hRelStep
    dsimp only at hRelStep
    split at hRelStep; · cases hRelStep
    split at hRelStep; · cases hRelStep
    split at hRelStep; · cases hRelStep
    rename_i hStNeg hDelNeg hWinRelNeg hCommitNeg _
    have hStF : (esc.status != .locked) = false := Bool.eq_false_iff.mpr hStNeg
    have hDelF : (!decide (0 < esc.deltaFinality)) = false := Bool.eq_false_iff.mpr hDelNeg
    cases hAuth : auditEscrowReleaseAuth H cfgA rootsA noncesA auth with
    | error _ => rw [hAuth] at hRelStep; cases hRelStep
    | ok _ =>
      rw [hAuth] at hRelStep; dsimp only at hRelStep; injection hRelStep with hEscRelEq
      have hWinRel := of_not_bnot hWinRelNeg; have hCommitChk := of_not_bnot hCommitNeg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hCommitChk; obtain ⟨⟨hCertChecks, hCertHeight⟩, hCertTip⟩ := hCommitChk
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hRefSame; unfold auditCrossChainEscrowStep at hRefSame; rw [hStF, hDelF] at hRefSame; dsimp only [Bool.false_eq_true, ↓reduceIte] at hRefSame
        cases hWinRef : checkTimeoutRefundWindow nowRel esc.tRelease esc.deltaFinality <;> rw [hWinRef] at hRefSame
        · cases hRefSame
        · simp only [checkReleaseWindow, checkTimeoutRefundWindow, Bool.and_eq_true, decide_eq_true_eq] at hWinRel hWinRef; omega
      · intro hRelay hRefB; unfold auditCrossChainEscrowStep at hRefB; rw [hStF, hDelF] at hRefB; dsimp only [Bool.false_eq_true, ↓reduceIte] at hRefB
        cases hWinRef : checkTimeoutRefundWindow nowRef esc.tRelease esc.deltaFinality <;> rw [hWinRef] at hRefB
        · cases hRefB
        · simp only [checkReleaseWindow, checkTimeoutRefundWindow, Bool.and_eq_true, decide_eq_true_eq] at hWinRel hWinRef
          rw [List.contains_iff_mem.mpr (hRelay (by omega))] at hRefB; cases hRefB
      · intro abortCert hAbortStep; unfold auditCrossChainEscrowStep at hAbortStep; rw [hStF, hDelF] at hAbortStep; dsimp only [Bool.false_eq_true, ↓reduceIte] at hAbortStep
        cases hAbortChk : (abortCert.checks P sent && decide (abortCert.chain.height = esc.decisionHeight) &&
          checkChainTipCommit abortCert.chain abortCert.view (swapDecisionCommitNat H esc.swapId .abortSwap)) <;> rw [hAbortChk] at hAbortStep
        · cases hAbortStep
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hAbortChk; obtain ⟨⟨hAbChecks, hAbHeight⟩, hAbTip⟩ := hAbortChk
          have hBlocks := FinCert.unique_per_height_reach hReach hCertChecks hAbChecks (hCertHeight.trans hAbHeight.symm)
          have hPayEq := getLast_blocks_eq_of_block_tip hBlocks (checkChainTipCommit_sound hCertTip) (checkChainTipCommit_sound hAbTip)
          let m₁ := encodeSwapDecisionPreimage esc.swapId (.commitSwap auth.claim.clearingRoot)
          let m₂ := encodeSwapDecisionPreimage esc.swapId .abortSwap
          unfold swapDecisionCommitNat at hPayEq; change ofBE ((H m₁).take 32) = ofBE ((H m₂).take 32) at hPayEq
          rw [List.take_of_length_le (Nat.le_of_eq (hLen32 m₁)), List.take_of_length_le (Nat.le_of_eq (hLen32 m₂))] at hPayEq
          exact ⟨m₁, m₂, .inl rfl, .inr rfl, commitSwap_ne_abortSwap_preimage esc.swapId esc.swapId auth.claim.clearingRoot, hPayEq⟩
      · subst hEscRelEq; exact ⟨rfl, by simp, fun _ => rfl⟩

/-! ## 9. Gate `G12` (`S1`, `S5–S7`): Finality-Bound `2 × 128b` L1 Settlement, `effectsRoot`, Netting & Trace Safety -/

structure OutboxSettlementEffect where
  nullifierId : Nat
  effectClass : EffectClass
  payload     : ByteArray
  deriving DecidableEq
def checkOutboxEffectsWellFormed : Nat → List OutboxSettlementEffect → Bool
  | _, [] => true
  | prevHighWater, e :: rest =>
    decide (prevHighWater < e.nullifierId) && decide (e.nullifierId < OutboxBound64) &&
    decide (e.payload.data.toList.length < OutboxBound64) && (e.effectClass == .irreversibleActuation) &&
    checkOutboxEffectsWellFormed e.nullifierId rest
example : checkOutboxEffectsWellFormed 0 [⟨1, .irreversibleActuation, ByteArray.empty⟩] = true := by decide
theorem checkOutboxEffectsWellFormed_sound :
    ∀ (prev : Nat) (es : List OutboxSettlementEffect), checkOutboxEffectsWellFormed prev es = true →
      ∀ e ∈ es, prev < e.nullifierId ∧ e.nullifierId < OutboxBound64 ∧
        e.payload.data.toList.length < OutboxBound64 ∧ e.effectClass = .irreversibleActuation
  | _, [], _, _, hm => nomatch hm
  | _, e :: rest, h, x, hm => by
    simp only [checkOutboxEffectsWellFormed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨hMono, hIdB⟩, hPayB⟩, hCls⟩, hRest⟩
    rcases List.mem_cons.mp hm with rfl | hTail
    · exact ⟨hMono, hIdB, hPayB, hCls⟩
    · have ih := checkOutboxEffectsWellFormed_sound e.nullifierId rest hRest x hTail
      exact ⟨Nat.lt_trans hMono ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
def computeOutboxEffectsRoot256 (H : Obend.Digest.HashBytes.Hash) (effects : List OutboxSettlementEffect) : Digest256 :=
  computeTaggedMerkleRoot256 H (effects.map fun e => (effectCommitBytes e.nullifierId e.effectClass e.payload).data.toList)
def settlementBatchDomain : List UInt8 :=
  [0x4F, 0x42, 0x45, 0x4E, 0x44, 0x2D, 0x44, 0x52, 0x45, 0x58, 0x2D, 0x4C, 0x31, 0x2D, 0x53, 0x45, 0x54, 0x54, 0x4C, 0x45, 0x4D, 0x45, 0x4E, 0x54, 0x2D, 0x56, 0x32]
def cshakeSettlementHash : Obend.Digest.HashBytes.Hash := Obend.Digest.Cshake256.cshake256Bytes settlementBatchDomain
theorem cshakeSettlementHash_length_32 (msg : List UInt8) : (cshakeSettlementHash msg).length = 32 := by simp [cshakeSettlementHash]
structure L1SettlementBatch where
  epoch          : Nat
  turnCount      : Nat
  prevStateRoot  : DigestLimbs2x128
  postStateRoot  : DigestLimbs2x128
  effectsRoot    : DigestLimbs2x128
  clearingRoot   : DigestLimbs2x128
  committedSwaps : List Digest256
  outboxEffects  : List OutboxSettlementEffect
  clearingLeaves : List (List UInt8)
  netQuery       : NettingQuery
  netCert        : NettingCert
  finCert        : FinCert
def encodeSettlementBatchHeader (chainId : UInt64) (programId : Digest256) (b : L1SettlementBatch) : List UInt8 :=
  encodeFields [be 8 chainId.toNat, bytesOfDigest256 programId, leb128 b.epoch, leb128 b.turnCount,
    b.prevStateRoot.toBytes32, b.postStateRoot.toBytes32, b.effectsRoot.toBytes32, b.clearingRoot.toBytes32,
    encodeFields (b.committedSwaps.map bytesOfDigest256)]
private theorem map_bytesOfDigest256_injective :
    ∀ {xs ys : List Digest256}, xs.map bytesOfDigest256 = ys.map bytesOfDigest256 → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [bytesOfDigest256_injective h.1, map_bytesOfDigest256_injective h.2]
theorem encodeSettlementBatchHeader_injective {c₁ c₂ : UInt64} {p₁ p₂ : Digest256} {b₁ b₂ : L1SettlementBatch}
    (h : encodeSettlementBatchHeader c₁ p₁ b₁ = encodeSettlementBatchHeader c₂ p₂ b₂) :
    c₁ = c₂ ∧ p₁ = p₂ ∧ b₁.epoch = b₂.epoch ∧ b₁.turnCount = b₂.turnCount ∧ b₁.prevStateRoot = b₂.prevStateRoot ∧
    b₁.postStateRoot = b₂.postStateRoot ∧ b₁.effectsRoot = b₂.effectsRoot ∧ b₁.clearingRoot = b₂.clearingRoot ∧
    b₁.committedSwaps = b₂.committedSwaps := by
  have hf := encodeFields_injective _ _ h; simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hCh, hPr, hEp, hTc, hPrev, hPost, hEff, hClr, hSwaps⟩
  have hpow64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact ⟨UInt64.toNat_inj.mp (be_injective (hpow64 ▸ c₁.toNat_lt) (hpow64 ▸ c₂.toNat_lt) hCh),
         bytesOfDigest256_injective hPr, leb128_injective hEp, leb128_injective hTc,
         DigestLimbs2x128.toBytes32_injective hPrev, DigestLimbs2x128.toBytes32_injective hPost,
         DigestLimbs2x128.toBytes32_injective hEff, DigestLimbs2x128.toBytes32_injective hClr,
         map_bytesOfDigest256_injective (encodeFields_injective _ _ hSwaps)⟩
def settlementBatchCommitNat (H : Obend.Digest.HashBytes.Hash) (chainId : UInt64) (programId : Digest256) (b : L1SettlementBatch) : Nat :=
  ofBE ((H (encodeSettlementBatchHeader chainId programId b)).take 32)
structure L1SettlementState where
  cfg                 : L1VaultConfig
  currentEpoch        : Nat
  committedHeight     : Nat
  headStateRoot       : DigestLimbs2x128
  highWaterNullifier  : Nat
  provenEffectsRoots  : List DigestLimbs2x128
  provenClearingRoots : List DigestLimbs2x128
  committedSwapIds    : List Digest256
  consumedPoolNonces  : List UInt64
  escrows             : List CrossChainEscrow
  deriving DecidableEq, Repr
def initL1SettlementState (callerAuthority : Digest256) (cfg : L1VaultConfig) (genesisStateRoot : DigestLimbs2x128) :
    Except L1SettlementRefusal L1SettlementState :=
  if callerAuthority == cfg.upgradeAuthority then .ok ⟨cfg, 0, 0, genesisStateRoot, 0, [], [], [], [], []⟩
  else .error .unauthorizedGenesisInit
theorem initL1SettlementState_rejects_unauthorized (callerAuthority : Digest256) (cfg : L1VaultConfig)
    (genesisStateRoot : DigestLimbs2x128) (hUnauth : callerAuthority ≠ cfg.upgradeAuthority) :
    initL1SettlementState callerAuthority cfg genesisStateRoot = .error .unauthorizedGenesisInit := by
  unfold initL1SettlementState; rw [beq_eq_false_iff_ne.mpr hUnauth]; rfl
def checkSettlementFinCert (P : Protocol) (sent : Sent) (expectedPayload : Nat) (cert : FinCert) : Bool :=
  cert.checks P sent && checkChainTipCommit cert.chain cert.view expectedPayload
def checkSettlementEffectsRoot (H : Obend.Digest.HashBytes.Hash) (prevHighWater : Nat)
    (claimedRoot : DigestLimbs2x128) (effects : List OutboxSettlementEffect) : Bool :=
  checkOutboxEffectsWellFormed prevHighWater effects &&
  DigestLimbs2x128.checkLimbsEq claimedRoot (DigestLimbs2x128.ofDigest256 (computeOutboxEffectsRoot256 H effects))
def auditL1SettlementBatch (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (sent : Sent)
    (st : L1SettlementState) (batch : L1SettlementBatch) : Except L1SettlementRefusal L1SettlementState :=
  if !decide (st.currentEpoch < batch.epoch) then .error (.nonMonotoneSettlementEpoch st.currentEpoch batch.epoch)
  else if !decide (1 ≤ batch.turnCount) then .error .zeroTurnBatch
  else if !DigestLimbs2x128.checkLimbsEq batch.prevStateRoot st.headStateRoot then .error .prevStateRootMismatch
  else if !decide (st.committedHeight < batch.finCert.chain.height) then .error (.nonMonotoneFinalizedHeight st.committedHeight batch.finCert.chain.height)
  else if !checkSettlementFinCert P sent (settlementBatchCommitNat H st.cfg.chainId st.cfg.programId batch) batch.finCert then .error .missingOrInvalidFinCert
  else if !checkSettlementEffectsRoot H st.highWaterNullifier batch.effectsRoot batch.outboxEffects then .error .malformedOrMismatchedEffectsRoot
  else if !DigestLimbs2x128.checkLimbsEq batch.clearingRoot (DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H batch.clearingLeaves)) then
    .error .mismatchedClearingRoot
  else match nettingJudge.check 0 batch.netQuery batch.netCert with
    | .refused _ _ | .uncovered => .error .nettingConservationRefused
    | .ok =>
      let nextHighWater := match batch.outboxEffects.getLast? with | some lastEff => lastEff.nullifierId | none => st.highWaterNullifier
      .ok { st with
        currentEpoch := batch.epoch, committedHeight := batch.finCert.chain.height
        headStateRoot := batch.postStateRoot, highWaterNullifier := nextHighWater
        provenEffectsRoots := batch.effectsRoot :: st.provenEffectsRoots
        provenClearingRoots := batch.clearingRoot :: st.provenClearingRoots
        committedSwapIds := batch.committedSwaps ++ st.committedSwapIds }
def stepL1SettlementBatch (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (sent : Sent)
    (st : L1SettlementState) (batch : L1SettlementBatch) : Option L1SettlementState :=
  match auditL1SettlementBatch P H sent st batch with | .ok st' => some st' | .error _ => none
theorem auditL1SettlementBatch_sound {P : Protocol} {H : Obend.Digest.HashBytes.Hash} {sent : Sent}
    {st st' : L1SettlementState} {batch : L1SettlementBatch} (hAcc : auditL1SettlementBatch P H sent st batch = .ok st') :
    st.currentEpoch < batch.epoch ∧ 1 ≤ batch.turnCount ∧ batch.prevStateRoot = st.headStateRoot ∧
    st'.headStateRoot = batch.postStateRoot ∧ (batch.postStateRoot.hi.toNat < 2 ^ 128 ∧ batch.postStateRoot.lo.toNat < 2 ^ 128) ∧
    st.committedHeight < batch.finCert.chain.height ∧ batch.finCert.checks P sent = true ∧
    Finalized P sent batch.finCert.view batch.finCert.chain ∧
    batch.finCert.chain.getLast? = some (.block batch.finCert.view (settlementBatchCommitNat H st.cfg.chainId st.cfg.programId batch)) ∧
    batch.effectsRoot.toDigest256 = computeOutboxEffectsRoot256 H batch.outboxEffects ∧
    (∀ e ∈ batch.outboxEffects, st.highWaterNullifier < e.nullifierId ∧ e.effectClass = .irreversibleActuation) ∧
    batch.clearingRoot.toDigest256 = computeTaggedMerkleRoot256 H batch.clearingLeaves ∧
    NettingSpec batch.netQuery batch.netCert ∧ grossExposure batch.netCert.netTransfers ≤ grossExposure batch.netQuery.grossObligations ∧
    (∀ (b : Obend.Ledger.Book) acc ast,
      (settleObligations b batch.netCert.netTransfers).balance acc ast = (settleObligations b batch.netQuery.grossObligations).balance acc ast) ∧
    (∀ (b : Obend.Ledger.Book) ast, (settleObligations b batch.netCert.netTransfers).globalAssetSum ast = b.globalAssetSum ast) := by
  unfold auditL1SettlementBatch at hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  split at hAcc; · cases hAcc
  rename_i hEpN hTcN hPrevN hHtN hFinN hEffN hClrN
  cases hNet : nettingJudge.check 0 batch.netQuery batch.netCert with
  | refused _ _ => rw [hNet] at hAcc; cases hAcc
  | uncovered => rw [hNet] at hAcc; cases hAcc
  | ok =>
    rw [hNet] at hAcc; dsimp only at hAcc; injection hAcc with hStEq; subst hStEq
    have hFin := (Bool.and_eq_true _ _).mp (of_not_bnot hFinN)
    have hEff := (Bool.and_eq_true _ _).mp (of_not_bnot hEffN)
    have hEffDig : batch.effectsRoot.toDigest256 = computeOutboxEffectsRoot256 H batch.outboxEffects := by
      rw [(DigestLimbs2x128.checkLimbsEq_iff _ _).mp hEff.2, DigestLimbs2x128.toDigest256_ofDigest256]
    have hClrDig : batch.clearingRoot.toDigest256 = computeTaggedMerkleRoot256 H batch.clearingLeaves := by
      rw [(DigestLimbs2x128.checkLimbsEq_iff _ _).mp (of_not_bnot hClrN), DigestLimbs2x128.toDigest256_ofDigest256]
    have hNetSpec := nettingJudge.sound hNet
    have hEffWf := checkOutboxEffectsWellFormed_sound st.highWaterNullifier batch.outboxEffects hEff.1
    exact ⟨of_decide_eq_true (of_not_bnot hEpN), of_decide_eq_true (of_not_bnot hTcN),
      (DigestLimbs2x128.checkLimbsEq_iff _ _).mp (of_not_bnot hPrevN), rfl,
      DigestLimbs2x128.limbs_lt_two_pow_128 batch.postStateRoot, of_decide_eq_true (of_not_bnot hHtN),
      hFin.1, FinCert.checks_implies_finalized hFin.1, checkChainTipCommit_sound hFin.2,
      hEffDig, fun e he => ⟨(hEffWf e he).1, (hEffWf e he).2.2.2⟩, hClrDig, hNetSpec, net_reduces_gross_exposure hNetSpec,
      fun b => (settleNetting_agrees_with_gross b hNetSpec).1, fun b => (settleNetting_agrees_with_gross b hNetSpec).2⟩
theorem unfinalized_fork_rejected (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (sent : Sent)
    (st : L1SettlementState) (forkBatch : L1SettlementBatch) (hNoQuorum : forkBatch.finCert.checks P sent = false) :
    stepL1SettlementBatch P H sent st forkBatch = none := by
  cases hs : stepL1SettlementBatch P H sent st forkBatch with
  | none => rfl
  | some _ =>
    unfold stepL1SettlementBatch at hs; cases ha : auditL1SettlementBatch P H sent st forkBatch with
    | error _ => rw [ha] at hs; cases hs
    | ok _ => have hFin := (auditL1SettlementBatch_sound ha).2.2.2.2.2.2.1; rw [hNoQuorum] at hFin; cases hFin
theorem equal_height_settlement_unique_or_collision {P : Protocol} {H : Obend.Digest.HashBytes.Hash} {sent : Sent}
    (hReach : Reach P sent) (hLen32 : ∀ m, (H m).length = 32) {st st₁ st₂ : L1SettlementState} {b₁ b₂ : L1SettlementBatch}
    (h₁ : auditL1SettlementBatch P H sent st b₁ = .ok st₁) (h₂ : auditL1SettlementBatch P H sent st b₂ = .ok st₂)
    (hHeight : b₁.finCert.chain.height = b₂.finCert.chain.height) :
    (b₁.epoch = b₂.epoch ∧ b₁.turnCount = b₂.turnCount ∧ b₁.prevStateRoot = b₂.prevStateRoot ∧
     b₁.postStateRoot = b₂.postStateRoot ∧ b₁.effectsRoot = b₂.effectsRoot ∧ b₁.clearingRoot = b₂.clearingRoot ∧
     b₁.committedSwaps = b₂.committedSwaps) ∨
    CollisionAmong H (fun m => m = encodeSettlementBatchHeader st.cfg.chainId st.cfg.programId b₁ ∨
      m = encodeSettlementBatchHeader st.cfg.chainId st.cfg.programId b₂) := by
  have s₁ := auditL1SettlementBatch_sound h₁; have s₂ := auditL1SettlementBatch_sound h₂
  have hBlocks := FinCert.unique_per_height_reach hReach s₁.2.2.2.2.2.2.1 s₂.2.2.2.2.2.2.1 hHeight
  have hPayEq := getLast_blocks_eq_of_block_tip hBlocks s₁.2.2.2.2.2.2.2.2.1 s₂.2.2.2.2.2.2.2.2.1
  let m₁ := encodeSettlementBatchHeader st.cfg.chainId st.cfg.programId b₁
  let m₂ := encodeSettlementBatchHeader st.cfg.chainId st.cfg.programId b₂
  if hPre : m₁ = m₂ then
    obtain ⟨_, _, hEp, hTc, hPrev, hPost, hEff, hClr, hSw⟩ := encodeSettlementBatchHeader_injective hPre
    exact .inl ⟨hEp, hTc, hPrev, hPost, hEff, hClr, hSw⟩
  else
    unfold settlementBatchCommitNat at hPayEq; change ofBE ((H m₁).take 32) = ofBE ((H m₂).take 32) at hPayEq
    rw [List.take_of_length_le (Nat.le_of_eq (hLen32 m₁)), List.take_of_length_le (Nat.le_of_eq (hLen32 m₂))] at hPayEq
    exact .inr ⟨m₁, m₂, .inl rfl, .inr rfl, hPre, hPayEq⟩
theorem l1SettlementBatch_skip_implies_violation (P : Protocol) (H : Obend.Digest.HashBytes.Hash)
    (sent : Sent) (st : L1SettlementState) (batch : L1SettlementBatch) (hSkip : stepL1SettlementBatch P H sent st batch = none) :
    (∃ r : L1SettlementRefusal, auditL1SettlementBatch P H sent st batch = .error r) ∧
    (¬ (st.currentEpoch < batch.epoch) ∨ ¬ (1 ≤ batch.turnCount) ∨ batch.prevStateRoot ≠ st.headStateRoot ∨
     ¬ (st.committedHeight < batch.finCert.chain.height) ∨
     checkSettlementFinCert P sent (settlementBatchCommitNat H st.cfg.chainId st.cfg.programId batch) batch.finCert = false ∨
     checkSettlementEffectsRoot H st.highWaterNullifier batch.effectsRoot batch.outboxEffects = false ∨
     batch.clearingRoot ≠ DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H batch.clearingLeaves) ∨
     nettingJudge.check 0 batch.netQuery batch.netCert ≠ .ok) := by
  unfold stepL1SettlementBatch at hSkip
  cases hAud : auditL1SettlementBatch P H sent st batch with
  | ok _ => rw [hAud] at hSkip; cases hSkip
  | error r =>
    refine ⟨⟨r, rfl⟩, ?_⟩; unfold auditL1SettlementBatch at hAud
    by_cases h1 : st.currentEpoch < batch.epoch
    · simp only [decide_eq_true h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
      by_cases h2 : 1 ≤ batch.turnCount
      · simp only [decide_eq_true h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
        by_cases h3 : batch.prevStateRoot = st.headStateRoot
        · simp only [(DigestLimbs2x128.checkLimbsEq_iff _ _).2 h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
          by_cases h4 : st.committedHeight < batch.finCert.chain.height
          · simp only [decide_eq_true h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
            cases h5 : checkSettlementFinCert P sent (settlementBatchCommitNat H st.cfg.chainId st.cfg.programId batch) batch.finCert with
            | false => exact .inr (.inr (.inr (.inr (.inl rfl))))
            | true =>
              simp only [h5, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
              cases h6 : checkSettlementEffectsRoot H st.highWaterNullifier batch.effectsRoot batch.outboxEffects with
              | false => exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
              | true =>
                simp only [h6, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
                by_cases h7 : batch.clearingRoot = DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H batch.clearingLeaves)
                · simp only [(DigestLimbs2x128.checkLimbsEq_iff _ _).2 h7, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAud
                  cases h8 : nettingJudge.check 0 batch.netQuery batch.netCert with
                  | ok => rw [h8] at hAud; cases hAud
                  | refused _ _ => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (fun hc => nomatch hc)))))))
                  | uncovered => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (fun hc => nomatch hc)))))))
                · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h7))))))
          · exact .inr (.inr (.inr (.inl h4)))
        · exact .inr (.inr (.inl h3))
      · exact .inr (.inl h2)
    · exact .inl h1
theorem auditL1SettlementBatch_complete (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (sent : Sent)
    (st : L1SettlementState) (batch : L1SettlementBatch)
    (hEp : st.currentEpoch < batch.epoch) (hTc : 1 ≤ batch.turnCount) (hPrev : batch.prevStateRoot = st.headStateRoot)
    (hHt : st.committedHeight < batch.finCert.chain.height)
    (hFin : checkSettlementFinCert P sent (settlementBatchCommitNat H st.cfg.chainId st.cfg.programId batch) batch.finCert = true)
    (hEff : checkSettlementEffectsRoot H st.highWaterNullifier batch.effectsRoot batch.outboxEffects = true)
    (hClr : batch.clearingRoot = DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H batch.clearingLeaves))
    (hNet : nettingJudge.check 0 batch.netQuery batch.netCert = .ok) :
    ∃ st' : L1SettlementState, stepL1SettlementBatch P H sent st batch = some st' := by
  unfold stepL1SettlementBatch auditL1SettlementBatch
  simp only [decide_eq_true hEp, decide_eq_true hTc, (DigestLimbs2x128.checkLimbsEq_iff _ _).2 hPrev,
    decide_eq_true hHt, hFin, hEff, (DigestLimbs2x128.checkLimbsEq_iff _ _).2 hClr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNet]
  exact ⟨_, rfl⟩
inductive L1ProtocolTurn where
  | settleBatch (nextSent : Sent) (batch : L1SettlementBatch) | poolUnlock (auth : L1InstructionAuth)
  | openEscrow (esc : CrossChainEscrow) | stepEscrow (nextSent : Sent) (escrowIdx : Nat) (action : EscrowAction)
def stepL1ProtocolTurn (P : Protocol) (H : Obend.Digest.HashBytes.Hash) (_sent : Sent) (st : L1SettlementState) :
    L1ProtocolTurn → Except L1SettlementRefusal L1SettlementState
  | .settleBatch nextSent batch => auditL1SettlementBatch P H nextSent st batch
  | .poolUnlock auth =>
    match auditPoolUnlock H st.cfg st.provenClearingRoots st.consumedPoolNonces auth with
    | .error e => .error e
    | .ok _ => .ok { st with consumedPoolNonces := auth.claim.nonce :: st.consumedPoolNonces }
  | .openEscrow esc =>
    if esc.status != .locked then .error (.escrowAlreadyTerminal esc.status)
    else if !decide (0 < esc.deltaFinality) then .error .zeroFinalityDelta
    else .ok { st with escrows := st.escrows ++ [{ esc with paidRelease := 0, paidRefund := 0 }] }
  | .stepEscrow nextSent idx act =>
    match st.escrows[idx]? with
    | none => .error (.escrowNotFound idx)
    | some esc =>
      match auditCrossChainEscrowStep P H nextSent st.cfg st.provenClearingRoots st.committedSwapIds st.consumedPoolNonces esc act with
      | .error e => .error e
      | .ok esc' =>
        let nextNonces := match act with | .release _ _ auth => auth.claim.nonce :: st.consumedPoolNonces | .refund _ _ => st.consumedPoolNonces
        .ok { st with consumedPoolNonces := nextNonces, escrows := st.escrows.set idx esc' }
def EscrowWellConserved (e : CrossChainEscrow) : Prop :=
  0 < e.deltaFinality ∧ ¬ (0 < e.paidRelease ∧ 0 < e.paidRefund) ∧
  e.paidRelease + e.paidRefund + (if e.status == .locked then e.amount.toNat else 0) = e.amount.toNat
def ValidL1SettlementTrace (P : Protocol) (H : Obend.Digest.HashBytes.Hash) :
    Sent → L1SettlementState → List L1ProtocolTurn → Sent → L1SettlementState → Prop
  | sent₀, st₀, [], sentF, stF => sentF = sent₀ ∧ stF = st₀ ∧ Reach P sent₀
  | sent₀, st₀, t :: rest, sentF, stF =>
    Reach P sent₀ ∧
    let nextSent := match t with | .settleBatch s _ | .stepEscrow s _ _ => s | .poolUnlock _ | .openEscrow _ => sent₀
    SentSteps P sent₀ nextSent ∧
    ∃ st₁ : L1SettlementState, stepL1ProtocolTurn P H sent₀ st₀ t = .ok st₁ ∧ ValidL1SettlementTrace P H nextSent st₁ rest sentF stF
private theorem escrow_set_preserves_all {es : List CrossChainEscrow} {idx : Nat} {e' : CrossChainEscrow}
    (hAll : ∀ x ∈ es, EscrowWellConserved x) (he' : EscrowWellConserved e') : ∀ x ∈ es.set idx e', EscrowWellConserved x := by
  induction es generalizing idx with
  | nil => intro _ hm; cases hm
  | cons a rest ih =>
    cases idx with
    | zero => intro x hm; rcases List.mem_cons.mp hm with rfl | hT; exact he'; exact hAll x (.tail a hT)
    | succ _ => intro x hm; rcases List.mem_cons.mp hm with rfl | hT; exact hAll x (.head rest); exact ih (fun y hy => hAll y (.tail a hy)) x hT
private theorem auditL1SettlementBatch_step_inv {P : Protocol} {H : Obend.Digest.HashBytes.Hash}
    {sent : Sent} {st st' : L1SettlementState} {batch : L1SettlementBatch} (h : auditL1SettlementBatch P H sent st batch = .ok st') :
    st.currentEpoch ≤ st'.currentEpoch ∧ st.committedHeight ≤ st'.committedHeight ∧
    st.highWaterNullifier ≤ st'.highWaterNullifier ∧ st'.consumedPoolNonces = st.consumedPoolNonces ∧ st'.escrows = st.escrows := by
  have hSnd := auditL1SettlementBatch_sound h; unfold auditL1SettlementBatch at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  cases hNet : nettingJudge.check 0 batch.netQuery batch.netCert with
  | refused _ _ => rw [hNet] at h; cases h
  | uncovered => rw [hNet] at h; cases h
  | ok =>
    rw [hNet] at h; dsimp only at h; injection h with hEq; subst hEq
    refine ⟨Nat.le_of_lt hSnd.1, Nat.le_of_lt hSnd.2.2.2.2.2.1, ?_, rfl, rfl⟩
    dsimp only; cases hLast : batch.outboxEffects.getLast? with
    | none => exact Nat.le_refl _
    | some lastEff => exact Nat.le_of_lt (hSnd.2.2.2.2.2.2.2.2.2.2.1 lastEff (List.mem_of_getLast? hLast)).1
private theorem auditCrossChainEscrowStep_conserves {P : Protocol} {H : Obend.Digest.HashBytes.Hash}
    {sent : Sent} {cfg : L1VaultConfig} {roots : List DigestLimbs2x128} {swaps : List Digest256} {nonces : List UInt64}
    {esc esc' : CrossChainEscrow} {act : EscrowAction} (hOld : EscrowWellConserved esc)
    (h : auditCrossChainEscrowStep P H sent cfg roots swaps nonces esc act = .ok esc') :
    EscrowWellConserved esc' ∧ (∀ now c auth, act = .release now c auth → auth.claim.nonce ∉ nonces) := by
  unfold auditCrossChainEscrowStep at h
  split at h; · cases h
  split at h; · cases h
  cases act with
  | release _ _ auth =>
    dsimp only at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    cases hRel : auditEscrowReleaseAuth H cfg roots nonces auth with
    | error _ => rw [hRel] at h; cases h
    | ok _ =>
      rw [hRel] at h; dsimp only at h; injection h with hEq; subst hEq
      refine ⟨And.intro hOld.1 (And.intro (fun ⟨_, h0⟩ => nomatch h0) (by simp)), fun _ _ _ hAct => ?_⟩
      injection hAct with _ _ hAuthEq; subst hAuthEq; exact (attestation_eq_of_auditL1InstructionAuth_ok hRel).2.1
  | refund _ reason =>
    have hRefWc : EscrowWellConserved { esc with status := .refunded, paidRelease := 0, paidRefund := esc.amount.toNat } :=
      And.intro hOld.1 (And.intro (fun ⟨h0, _⟩ => nomatch h0) (by simp))
    cases reason with
    | postWindowTimeout =>
      dsimp only at h; split at h; · cases h
      split at h; · cases h
      injection h with hEq; subst hEq; exact ⟨hRefWc, fun _ _ _ hc => nomatch hc⟩
    | certifiedSimplexAbort _ =>
      dsimp only at h; split at h; · cases h
      injection h with hEq; subst hEq; exact ⟨hRefWc, fun _ _ _ hc => nomatch hc⟩
theorem sovereignDrex_l1_settlement_trace_safe {P : Protocol} {H : Obend.Digest.HashBytes.Hash}
    {sent₀ sentF : Sent} {st₀ stF : L1SettlementState} {turns : List L1ProtocolTurn}
    (hNonces₀ : st₀.consumedPoolNonces.Nodup) (hEsc₀ : ∀ e ∈ st₀.escrows, EscrowWellConserved e)
    (hTrace : ValidL1SettlementTrace P H sent₀ st₀ turns sentF stF) :
    Reach P sentF ∧ st₀.currentEpoch ≤ stF.currentEpoch ∧ st₀.committedHeight ≤ stF.committedHeight ∧
    st₀.highWaterNullifier ≤ stF.highWaterNullifier ∧ stF.consumedPoolNonces.Nodup ∧ (∀ e ∈ stF.escrows, EscrowWellConserved e) := by
  induction turns generalizing sent₀ st₀ with
  | nil => rcases hTrace with ⟨rfl, rfl, hR⟩; exact ⟨hR, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, hNonces₀, hEsc₀⟩
  | cons t rest ih =>
    rcases hTrace with ⟨_, _, st₁, hStep, hRest⟩
    have hStepInv : st₀.currentEpoch ≤ st₁.currentEpoch ∧ st₀.committedHeight ≤ st₁.committedHeight ∧
        st₀.highWaterNullifier ≤ st₁.highWaterNullifier ∧ st₁.consumedPoolNonces.Nodup ∧ (∀ e ∈ st₁.escrows, EscrowWellConserved e) := by
      cases t with
      | settleBatch _ _ =>
        obtain ⟨hEp, hHt, hHw, hNc, hEs⟩ := auditL1SettlementBatch_step_inv hStep
        exact ⟨hEp, hHt, hHw, hNc ▸ hNonces₀, hEs ▸ hEsc₀⟩
      | poolUnlock auth =>
        dsimp only [stepL1ProtocolTurn] at hStep
        cases hAud : auditPoolUnlock H st₀.cfg st₀.provenClearingRoots st₀.consumedPoolNonces auth with
        | error _ => rw [hAud] at hStep; cases hStep
        | ok _ =>
          rw [hAud] at hStep; injection hStep with hEq; subst hEq
          exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
            List.nodup_cons.mpr ⟨(attestation_eq_of_auditL1InstructionAuth_ok hAud).2.1, hNonces₀⟩, hEsc₀⟩
      | openEscrow esc =>
        dsimp only [stepL1ProtocolTurn] at hStep
        split at hStep; · cases hStep
        split at hStep; · cases hStep
        rename_i hSt hDel; injection hStep with hEq; subst hEq
        have hL : esc.status = .locked := eq_of_not_bne hSt
        have hPos := of_decide_eq_true (of_not_bnot hDel)
        refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, hNonces₀, fun x hx => ?_⟩
        rcases List.mem_append.mp hx with hOld | hNew
        · exact hEsc₀ x hOld
        · rcases List.mem_singleton.mp hNew with rfl
          exact And.intro hPos (And.intro (fun ⟨h0, _⟩ => nomatch h0) (by simp [hL]))
      | stepEscrow nextSent idx act =>
        dsimp only [stepL1ProtocolTurn] at hStep
        cases hGet : st₀.escrows[idx]? with
        | none => rw [hGet] at hStep; cases hStep
        | some esc =>
          rw [hGet] at hStep; dsimp only at hStep
          cases hEscAud : auditCrossChainEscrowStep P H nextSent st₀.cfg st₀.provenClearingRoots st₀.committedSwapIds st₀.consumedPoolNonces esc act with
          | error _ => rw [hEscAud] at hStep; cases hStep
          | ok esc' =>
            rw [hEscAud] at hStep; dsimp only at hStep; injection hStep with hEq; subst hEq
            obtain ⟨hWc', hFresh⟩ := auditCrossChainEscrowStep_conserves (hEsc₀ esc (List.mem_of_getElem? hGet)) hEscAud
            refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ?_, escrow_set_preserves_all hEsc₀ hWc'⟩
            cases act with
            | release now c auth => exact List.nodup_cons.mpr ⟨hFresh now c auth rfl, hNonces₀⟩
            | refund _ _ => exact hNonces₀
    obtain ⟨hRF, hEpF, hHtF, hHwF, hNdF, hEscF⟩ := ih hStepInv.2.2.2.1 hStepInv.2.2.2.2 hRest
    exact ⟨hRF, Nat.le_trans hStepInv.1 hEpF, Nat.le_trans hStepInv.2.1 hHtF, Nat.le_trans hStepInv.2.2.1 hHwF, hNdF, hEscF⟩
def drexProtocol5 : Protocol := ⟨[0, 1, 2, 3, 4], 1, (· == 4), by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem sovereignDrex_g12_pipeline_inhabited (H : Obend.Digest.HashBytes.Hash) :
    let cfg : L1VaultConfig := ⟨101, 0xD2E6#256, 0xA11CE#256, [.splTokenLegacy, .splToken2022, .nativeOrErc20]⟩
    let effs : List OutboxSettlementEffect := [⟨1, .irreversibleActuation, ByteArray.mk #[0x42, 0x99]⟩]
    let clrLeaves : List (List UInt8) := [[0x11], [0x77]]
    let clrRoot := DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H clrLeaves)
    ∃ (st₀ st₁ : L1SettlementState) (escRef : CrossChainEscrow),
      initL1SettlementState 0xA11CE#256 cfg ⟨1#128, 2#128⟩ = .ok st₀ ∧
      ValidL1SettlementTrace drexProtocol5 H [] st₀ [] [] st₀ ∧
      verifyTaggedMerkleProof256 H (buildTaggedMerkleProof256 H clrLeaves 0) (computeTaggedMerkleRoot256 H clrLeaves) = true ∧
      auditCrossChainEscrowStep drexProtocol5 H [] cfg [clrRoot] [] []
        ⟨9, 0x99#256, 1, 0xAA#256, 0xBB#256, 250, 100, 15, .locked, 0, 0⟩ (.refund 116 .postWindowTimeout) = .ok escRef ∧
      (let b0 : L1SettlementBatch :=
         ⟨1, 3, ⟨1#128, 2#128⟩, ⟨3#128, 4#128⟩, DigestLimbs2x128.ofDigest256 (computeOutboxEffectsRoot256 H effs),
          clrRoot, [0x55#256], effs, clrLeaves, ⟨[⟨1, 2, 0, 100⟩, ⟨2, 1, 0, 40⟩]⟩, ⟨[⟨1, 2, 0, 60⟩]⟩, ⟨1, [.block 1 0], [0, 1, 2, 3]⟩⟩
       let tip := settlementBatchCommitNat H cfg.chainId cfg.programId b0
       let b : L1SettlementBatch := { b0 with finCert := ⟨1, [.block 1 tip], [0, 1, 2, 3]⟩ }
       let sent4 : Sent := [⟨0, 1, .finalize, .block [.block 1 tip]⟩, ⟨1, 1, .finalize, .block [.block 1 tip]⟩,
                            ⟨2, 1, .finalize, .block [.block 1 tip]⟩, ⟨3, 1, .finalize, .block [.block 1 tip]⟩]
       auditL1SettlementBatch drexProtocol5 H sent4 st₀ b = .ok st₁) := by
  dsimp only
  let cfg : L1VaultConfig := ⟨101, 0xD2E6#256, 0xA11CE#256, [.splTokenLegacy, .splToken2022, .nativeOrErc20]⟩
  let effs : List OutboxSettlementEffect := [⟨1, .irreversibleActuation, ByteArray.mk #[0x42, 0x99]⟩]
  let clrLeaves : List (List UInt8) := [[0x11], [0x77]]
  let clrRoot := DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H clrLeaves)
  let st₀ : L1SettlementState := ⟨cfg, 0, 0, ⟨1#128, 2#128⟩, 0, [], [], [], [], []⟩
  let b0 : L1SettlementBatch :=
    ⟨1, 3, ⟨1#128, 2#128⟩, ⟨3#128, 4#128⟩, DigestLimbs2x128.ofDigest256 (computeOutboxEffectsRoot256 H effs),
     clrRoot, [0x55#256], effs, clrLeaves, ⟨[⟨1, 2, 0, 100⟩, ⟨2, 1, 0, 40⟩]⟩, ⟨[⟨1, 2, 0, 60⟩]⟩, ⟨1, [.block 1 0], [0, 1, 2, 3]⟩⟩
  let tip := settlementBatchCommitNat H cfg.chainId cfg.programId b0
  let b : L1SettlementBatch := { b0 with finCert := ⟨1, [.block 1 tip], [0, 1, 2, 3]⟩ }
  let sent4 : Sent := [⟨0, 1, .finalize, .block [.block 1 tip]⟩, ⟨1, 1, .finalize, .block [.block 1 tip]⟩,
                       ⟨2, 1, .finalize, .block [.block 1 tip]⟩, ⟨3, 1, .finalize, .block [.block 1 tip]⟩]
  have hTipEq : settlementBatchCommitNat H cfg.chainId cfg.programId b = tip := rfl
  have hCertChk : b.finCert.checks drexProtocol5 sent4 = true := by
    simp [b, sent4, drexProtocol5, FinCert.checks, Protocol.quorum, finalizeVoted]
  have hTipChk : checkChainTipCommit b.finCert.chain b.finCert.view (settlementBatchCommitNat H cfg.chainId cfg.programId b) = true := by
    rw [hTipEq]; simp [b, checkChainTipCommit]
  have hWf : checkOutboxEffectsWellFormed 0 effs = true := by decide
  have hNetOk : nettingJudge.check 0 b.netQuery b.netCert = .ok := rfl
  have h1 : (!decide (st₀.currentEpoch < b.epoch)) = false := rfl
  have h2 : (!decide (1 ≤ b.turnCount)) = false := rfl
  have h3 : (!DigestLimbs2x128.checkLimbsEq b.prevStateRoot st₀.headStateRoot) = false := rfl
  have h4 : (!decide (st₀.committedHeight < b.finCert.chain.height)) = false := by simp [st₀, b, Chain.height, Entry.isBlock]
  have h5 : (!checkSettlementFinCert drexProtocol5 sent4 (settlementBatchCommitNat H st₀.cfg.chainId st₀.cfg.programId b) b.finCert) = false := by
    simp [checkSettlementFinCert, hCertChk, hTipChk, st₀]
  have h6 : (!checkSettlementEffectsRoot H st₀.highWaterNullifier b.effectsRoot b.outboxEffects) = false := by
    simp [checkSettlementEffectsRoot, st₀, b, b0, hWf]
  have h7 : (!DigestLimbs2x128.checkLimbsEq b.clearingRoot (DigestLimbs2x128.ofDigest256 (computeTaggedMerkleRoot256 H b.clearingLeaves))) = false := by
    simp [b, b0, clrRoot]
  let escRef : CrossChainEscrow := ⟨9, 0x99#256, 1, 0xAA#256, 0xBB#256, 250, 100, 15, .refunded, 0, 250⟩
  let st₁ : L1SettlementState :=
    { st₀ with
      currentEpoch := 1, committedHeight := 1, headStateRoot := ⟨3#128, 4#128⟩, highWaterNullifier := 1
      provenEffectsRoots := [b.effectsRoot], provenClearingRoots := [clrRoot], committedSwapIds := [0x55#256] }
  refine ⟨st₀, st₁, escRef, ?_⟩
  refine ⟨rfl, ⟨rfl, rfl, Reach.nil⟩, verifyTaggedMerkleProof256_complete H clrLeaves 0 (by decide), rfl, ?_⟩
  change auditL1SettlementBatch drexProtocol5 H sent4 st₀ b = .ok st₁
  unfold auditL1SettlementBatch; rw [h1, h2, h3, h4, h5, h6, h7]; dsimp only [↓reduceIte]; rw [hNetOk]; rfl

end Obend.Apps.SovereignDrex
end
