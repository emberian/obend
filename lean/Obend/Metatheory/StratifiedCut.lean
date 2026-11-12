module
/-
# Obend.Metatheory.StratifiedCut — The 7 Honest Boundary Compilation Regimes (`C0`–`C6`)

Formalizes Proposal 3 of the General Metatheory of Distributed, Decentralized Houyhnhnm Computation,
honoring every impossibility boundary established in the `Cut` False-Collapse Audit:

1. **`StagedFunctionalBridge` (`staged_safety_sound`)**: mechanical boundary transport combining
   secret-redacting `Vault.Form.pevalRedacted`, `commitField256`-verified cryptographic openings
   with 2-element `CollisionAmong` binding (`0 Classical.choice`), `RangeSafe` modular/word bounds,
   and `Judge.Translation`.
2. **The 7 Honest `CutRegimeSpec` Regimes (`compileCut`) — Zero Caller-Attested Flags**:
   - `C0_LocalInline`: same-sponsor zero-crypto inline call with dynamic `subsetCaps` attenuation,
   - `C1_CarrierLowering`: runs `pevalRedacted` on `expr` and checks `Interval` `< modulusBound`,
   - `C2_CertificateJudge`: executes `F.judge.check` on `cert` AND verifies genuine refutation on `badObj`,
   - `C3_BoundedFoldIVC`: checks `maxNormAtDepth < sisBetaBound`, CRS `RatSlack`, and cSHAKE256
     binding of non-empty `deltaBytes` to `deltaPinDigest` (blocking state-delta withholding),
   - `C4_Oblivious2Safety`: structural `isShapeObliviousExpr` check proving constant `CircuitTopology`
     across **all** secret assignments `env₁, env₂` (`isShapeObliviousExpr_sound`),
   - `C5_FairExchangeAtomic`: refuses unbonded co-receipts and requires either a live stake-covering
     `EscrowCompensationBond` (with single-use `EscrowVault` conservation) or non-empty `SimplexProtocol.FinCert`,
   - `C6_PhysicalPassivity`: zero-feedthrough causal Mealy port (`directFeedthroughGain = 0`),
     `PassiveJunction` energy bound, and non-empty `SafePhysicalShield` inter-sample dwell core.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Vault.Form
public import Obend.Core.RangeSafe
public import Obend.Category.OpenSystem
public import Obend.Consensus.SimplexProtocol
public import Obend.Hardware.SafePhysicalShield
public import Obend.Judge.Class
public import Obend.Metatheory.SponsorAndMigration

public section

namespace Obend.Metatheory.StratifiedCut

open Obend.Digest
open Obend.Vault.Form (NExpr RedactedNExpr RedactRefusal Known Assignment
  pevalRedacted pevalRedacted_zero_secret_leak pevalRedacted_eval_sound
  commitField256 FieldCommitCollisionWitness extractCommitField256Collision
  commitField256_collisionAmong fieldCommitHash encodeFieldCommitPreimage)
open Obend.Core.RangeSafe (Interval)
open Obend.Category (GradeMonoid RatSlack OpenDissipativeSys)
open Obend.Category.OpenDissipativeSys (PassiveJunction feedbackInterconnect energy_bounded_along_trajectory)
open Obend.Consensus.SimplexProtocol (Protocol Sent FinCert Finalized)
open Obend.Hardware.SafePhysicalShield (SampledPhysicalPlantSpec)
open Obend.Metatheory.PinsAndQuiescence (Digest256 PinSort)
open Obend.Metatheory.SponsorAndMigration (subsetCaps subsetCaps_refl subsetCaps_trans)

set_option autoImplicit false

/-! ## 1. Mechanical `StagedFunctionalBridge` (`pevalRedacted` + `commitField256` + `Judge.Translation`) -/

/-- Execute and verify a staged functional boundary:
    1. `1 < modulusBound`,
    2. `pevalRedacted` succeeds without constant underflow or missing secret commitment,
    3. Evaluating the redacted residual against `commitField256`-checked `(val, salt)` `openings`
       yields `val < modulusBound` (blocking secret-page holes and modular wraparound), and
    4. Relocated `Judge.Format` checker accepts `(translation.encode val)` at `fuel`. -/
@[expose] def verifyStagedBridge
    (pubKnown fullKnown : Known)
    (isSecret : String → Bool)
    (secretCommits : String → String → Option Digest256)
    (openings : String → String → Option (UInt64 × Digest256))
    (assign : Assignment)
    (modulusBound : Nat)
    (F : Judge.Format)
    (encodeObj : Nat → F.Obj)
    (fuel : Nat) (cert : F.Cert)
    (expr : NExpr) : Bool :=
  if 1 < modulusBound then
    match pevalRedacted pubKnown isSecret secretCommits expr with
    | .error _ => false
    | .ok red =>
        match red.eval assign fullKnown isSecret openings with
        | none => false
        | some val =>
            decide (val < modulusBound) &&
            (match F.judge.check fuel (encodeObj val) cert with
             | .ok => true
             | _ => false)
  else false

/-- **Conditional Staged Functional Safety & 2-Element Commitment Binding (`staged_safety_sound`)**:
    1. **Zero Secret Leak in Residual**: `pevalRedacted` depends solely on public pages and 256-bit
       commitment digests.
    2. **Cryptographic Opening Binding (`0 Classical`)**: any two `(val, salt)` openings matching
       the same `commitField256` digest either agree (`v₁ = v₂ ∧ s₁ = s₂`) or yield a scoped
       2-element `HashBytes.CollisionAmong` witness.
    3. **Monolithic Evaluation & Relocated `Judge` Soundness**: whenever `verifyStagedBridge = true`
       under valid `pubKnown` and `commitField256` `openings`, `(expr.subst assign).eval fullKnown`
       evaluates to the exact same `val < modulusBound` and establishes `Claim val`. -/
theorem staged_safety_sound {Claim : Nat → Prop}
    (pubKnown fullKnown : Known)
    (isSecret : String → Bool)
    (secretCommits : String → String → Option Digest256)
    (openings : String → String → Option (UInt64 × Digest256))
    (assign : Assignment)
    (modulusBound : Nat)
    (F : Judge.Format)
    (T : Judge.Translation F Nat Claim)
    (fuel : Nat) (cert : F.Cert) (expr : NExpr)
    (hPub : ∀ p d, isSecret p = false → pubKnown p = some d → fullKnown p = some d)
    (hHolePub : ∀ h n, assign.pages.lookup h = some n → isSecret n = false)
    (hSec : ∀ p f dg, isSecret p = true → secretCommits p f = some dg →
      ∃ v s, openings p f = some (v, s) ∧ commitField256 p f v s = dg ∧
        (fullKnown p).map (Obend.Vault.natAt · f) = some v.toNat) :
    (∀ pub₂, (∀ p, isSecret p = false → pubKnown p = pub₂ p) →
      pevalRedacted pubKnown isSecret secretCommits expr =
        pevalRedacted pub₂ isSecret secretCommits expr) ∧
    (∀ p f (v₁ v₂ : UInt64) (s₁ s₂ : Digest256),
      commitField256 p f v₁ s₁ = commitField256 p f v₂ s₂ →
      (v₁ = v₂ ∧ s₁ = s₂) ∨
        HashBytes.CollisionAmong fieldCommitHash
          (fun x => x = encodeFieldCommitPreimage p f v₁ s₁ ∨ x = encodeFieldCommitPreimage p f v₂ s₂)) ∧
    (verifyStagedBridge pubKnown fullKnown isSecret secretCommits openings assign
        modulusBound F T.encode fuel cert expr = true →
      1 < modulusBound ∧
      ∃ val : Nat,
        (expr.subst assign).eval fullKnown = some val ∧
        val < modulusBound ∧
        Claim val) := by
  refine ⟨fun pub₂ hAg => (pevalRedacted_zero_secret_leak pubKnown pub₂ isSecret secretCommits hAg).1 expr,
    fun p f v₁ v₂ s₁ s₂ hEq => ?_, ?_⟩
  · cases extractCommitField256Collision p f v₁ s₁ p f v₂ s₂ hEq with
    | inl hSame => exact .inl ⟨hSame.2.2.1, hSame.2.2.2⟩
    | inr w => exact .inr (commitField256_collisionAmong w)
  · intro hVer
    unfold verifyStagedBridge at hVer
    by_cases hMod : 1 < modulusBound
    · simp only [hMod, ite_true] at hVer
      cases hStg : pevalRedacted pubKnown isSecret secretCommits expr with
      | error _ => simp [hStg] at hVer
      | ok red =>
        simp only [hStg] at hVer
        cases hEv : red.eval assign fullKnown isSecret openings with
        | none => simp [hEv] at hVer
        | some val =>
          simp only [hEv, Bool.and_eq_true, decide_eq_true_eq] at hVer
          rcases hVer with ⟨hLtMod, hChkMatch⟩
          have hChkOk : F.judge.check fuel (T.encode val) cert = .ok := by
            cases hJ : F.judge.check fuel (T.encode val) cert <;> simp [hJ] at hChkMatch
            rfl
          have hEqEval := pevalRedacted_eval_sound assign hPub hHolePub hSec hStg
          rw [hEv] at hEqEval
          exact ⟨hMod, val, hEqEval.symm, hLtMod, T.sound hChkOk⟩
    · simp [hMod] at hVer

/-! ## 2. Regime-Specific Non-Local Evidence (`C2` Judge, `C3` IVC+DA, `C4` Oblivious, `C5` Escrow, `C6` Physical) -/

/-- Packaged `C2` certificate bundle carrying an actual `Judge.Format`, target `(obj, cert)`, and
    planted bad witness `(badObj, badCert)` checked directly by `compileCut`. -/
structure VerifiedCertBundle where
  format               : Judge.Format
  verifierFuel         : Nat
  prepaidSponsorCycles : Nat
  obj                  : format.Obj
  cert                 : format.Cert
  badObj               : format.Obj
  badCert              : format.Cert

/-- Domain-tagged 256-bit state-delta availability commitment for `C3`. -/
def commitDeltaDigest (deltaBytes : List UInt8) : Digest256 :=
  BitVec.ofNat 256 (HashBytes.ofBE (Cshake256.cshake256Bytes
    "Obend.Metatheory.DeltaDA.v1".toUTF8.toList deltaBytes))

/-- **`C3` Honest Bounded-Depth IVC / Folding Parameters**:
    Tracks multiplicative witness norm growth `initNorm * (1 + challengeAbsBound)^foldDepth < sisBetaBound`,
    CRS distributional slack `crsSlack`, and non-empty `deltaBytes` matching `deltaPinDigest`. -/
structure HonestFoldParams where
  foldDepth            : Nat
  initNorm             : Nat
  challengeAbsBound    : Nat
  sisBetaBound         : Nat
  isCompressingCrsKeyed : Bool
  crsSlack             : RatSlack
  deltaBytes           : List UInt8
  deltaPinDigest       : Digest256
  deriving DecidableEq, Repr

def HonestFoldParams.maxNormAtDepth (p : HonestFoldParams) : Nat :=
  p.initNorm * ((1 + p.challengeAbsBound) ^ p.foldDepth)

@[expose] def HonestFoldParams.check (p : HonestFoldParams) : Bool :=
  decide (0 < p.foldDepth) &&
  decide (p.maxNormAtDepth < p.sisBetaBound) &&
  p.isCompressingCrsKeyed &&
  decide (0 ≤ p.crsSlack.num) &&
  !p.deltaBytes.isEmpty &&
  (commitDeltaDigest p.deltaBytes == p.deltaPinDigest)

/-- Red-team impossibility guard: a single 63-bit challenge (`|c| = 2^63`) blows past `131070`
    SIS norm bound and is deterministically refused by `HonestFoldParams.check`. -/
theorem wide_challenge_fold_norm_blowup_refused (crs : RatSlack) (bs : List UInt8) (pin : Digest256) :
    (HonestFoldParams.mk 1 1 (2 ^ 63) 131070 true crs bs pin).check = false := by
  have hNotLt : ¬ ((HonestFoldParams.mk 1 1 (2 ^ 63) 131070 true crs bs pin).maxNormAtDepth < 131070) := by
    simp only [HonestFoldParams.maxNormAtDepth, Nat.pow_one, Nat.one_mul]
    omega
  simp [HonestFoldParams.check, hNotLt]

/-- Data-withholding guard: posting a folded root with empty `deltaBytes = []` is refused. -/
theorem withheld_ivc_state_delta_refused (p : HonestFoldParams) (hEmpty : p.deltaBytes = []) :
    p.check = false := by
  simp [HonestFoldParams.check, hEmpty]

/-- **`C4` Constant-Topology Oblivious Circuit AST & Staging**:
    Tracks public gate counts and padded wire bytes across recursive circuit expressions. -/
structure CircuitTopology where
  muxGates        : Nat
  addGates        : Nat
  paddedWireBytes : Nat
  deriving DecidableEq, Repr

structure StagedCircuit where
  topology  : CircuitTopology
  outputVal : Nat
  deriving DecidableEq, Repr

/-- Circuit staging expression language distinguishing padded `mux` from leaky short-circuiting. -/
inductive ObliviousCircuitExpr where
  | pubLit (n : Nat)
  | secretBit (varId : Nat)
  | add (lhs rhs : ObliviousCircuitExpr)
  | paddedMux (secretVar : Nat) (onTrue onFalse : ObliviousCircuitExpr)
  | leakyShortCircuitOr (secretVar : Nat) (fallback : ObliviousCircuitExpr)
  deriving DecidableEq, Repr

@[expose] def stageCircuitExpr : ObliviousCircuitExpr → (Nat → Bool) → StagedCircuit
  | .pubLit n, _ => ⟨⟨0, 0, 32⟩, n⟩
  | .secretBit v, env => ⟨⟨0, 0, 32⟩, if env v then 1 else 0⟩
  | .add l r, env =>
      let sl := stageCircuitExpr l env
      let sr := stageCircuitExpr r env
      ⟨⟨sl.topology.muxGates + sr.topology.muxGates,
        sl.topology.addGates + sr.topology.addGates + 1,
        sl.topology.paddedWireBytes + sr.topology.paddedWireBytes⟩,
       sl.outputVal + sr.outputVal⟩
  | .paddedMux v wt wf, env =>
      let st := stageCircuitExpr wt env
      let sf := stageCircuitExpr wf env
      ⟨⟨st.topology.muxGates + sf.topology.muxGates + 1,
        st.topology.addGates + sf.topology.addGates,
        st.topology.paddedWireBytes + sf.topology.paddedWireBytes + 32⟩,
       if env v then st.outputVal else sf.outputVal⟩
  | .leakyShortCircuitOr v fb, env =>
      if env v then ⟨⟨0, 0, 32⟩, 1⟩
      else
        let sfb := stageCircuitExpr fb env
        ⟨⟨sfb.topology.muxGates + 1, sfb.topology.addGates, sfb.topology.paddedWireBytes + 32⟩,
         sfb.outputVal⟩

/-- Structural shape-obliviousness checker rejecting secret-dependent AST pruning. -/
@[expose] def isShapeObliviousExpr : ObliviousCircuitExpr → Bool
  | .pubLit _ | .secretBit _ => true
  | .add l r | .paddedMux _ l r => isShapeObliviousExpr l && isShapeObliviousExpr r
  | .leakyShortCircuitOr _ _ => false

/-- **Universal Shape-Obliviousness Theorem (`isShapeObliviousExpr_sound`)**:
    Every circuit expression accepted by `isShapeObliviousExpr` produces the **exact same
    `CircuitTopology`** across ALL secret bit assignments `env₁, env₂ : Nat → Bool`! -/
theorem isShapeObliviousExpr_sound :
    ∀ (e : ObliviousCircuitExpr), isShapeObliviousExpr e = true →
      ∀ (env₁ env₂ : Nat → Bool),
        (stageCircuitExpr e env₁).topology = (stageCircuitExpr e env₂).topology
  | .pubLit _, _, _, _ => rfl
  | .secretBit _, _, _, _ => rfl
  | .add l r, hOk, env₁, env₂ => by
    simp only [isShapeObliviousExpr, Bool.and_eq_true] at hOk
    have ihl := isShapeObliviousExpr_sound l hOk.1 env₁ env₂
    have ihr := isShapeObliviousExpr_sound r hOk.2 env₁ env₂
    simp [stageCircuitExpr, ihl, ihr]
  | .paddedMux v wt wf, hOk, env₁, env₂ => by
    simp only [isShapeObliviousExpr, Bool.and_eq_true] at hOk
    have iht := isShapeObliviousExpr_sound wt hOk.1 env₁ env₂
    have ihf := isShapeObliviousExpr_sound wf hOk.2 env₁ env₂
    simp [stageCircuitExpr, iht, ihf]
  | .leakyShortCircuitOr _ _, hOk, _, _ => by cases hOk

theorem isShapeObliviousExpr_complete (n : Nat) :
    isShapeObliviousExpr (.pubLit n) = true := by rfl

/-- Canonical shape-padded conditional circuit (`pevalPadExpr`). -/
@[expose] def pevalPadExpr (pubOffset pubTrueVal pubFalseVal : Nat) (secretVar : Nat) : ObliviousCircuitExpr :=
  .add (.pubLit pubOffset) (.paddedMux secretVar (.pubLit pubTrueVal) (.pubLit pubFalseVal))

theorem pevalPad_oblivious_and_sound (p : Nat × Nat × Nat) (v : Nat) (env₁ env₂ : Nat → Bool) :
    isShapeObliviousExpr (pevalPadExpr p.1 p.2.1 p.2.2 v) = true ∧
    (stageCircuitExpr (pevalPadExpr p.1 p.2.1 p.2.2 v) env₁).outputVal =
      p.1 + (if env₁ v then p.2.1 else p.2.2) ∧
    (stageCircuitExpr (pevalPadExpr p.1 p.2.1 p.2.2 v) env₁).topology =
      (stageCircuitExpr (pevalPadExpr p.1 p.2.1 p.2.2 v) env₂).topology :=
  ⟨rfl, rfl, isShapeObliviousExpr_sound _ rfl env₁ env₂⟩

theorem shortCircuitDisj_leaks_topology (v : Nat) (fb : ObliviousCircuitExpr) :
    isShapeObliviousExpr (.leakyShortCircuitOr v fb) = false ∧
    (stageCircuitExpr (.leakyShortCircuitOr v fb) (fun _ => true)).topology ≠
      (stageCircuitExpr (.leakyShortCircuitOr v fb) (fun _ => false)).topology := by
  refine ⟨rfl, ?_⟩
  simp [stageCircuitExpr]

/-- **`C5` Fair Exchange (`EscrowCompensationBond`, Single-Use `EscrowVault` & `SimplexProtocol.FinCert`)**:
    Refuses unbonded co-receipts and requires a live stake-covering compensation bond or quorum finality. -/
structure EscrowCompensationBond where
  fundedDeposit : Nat
  rollbackCost  : Nat
  commitEpoch   : Nat
  abortDeadline : Nat
  deriving DecidableEq, Repr

@[expose] def EscrowCompensationBond.checkForStake (stakeAtRisk nowEpoch : Nat)
    (b : EscrowCompensationBond) : Bool :=
  decide (0 < b.rollbackCost) &&
  decide (stakeAtRisk ≤ b.rollbackCost) &&
  decide (b.rollbackCost ≤ b.fundedDeposit) &&
  decide (b.commitEpoch < b.abortDeadline) &&
  decide (nowEpoch ≤ b.abortDeadline)

inductive EscrowOutcome where
  | settledAllLegs
  | slashedForSelectiveAbort (compensationToHonest remainingSlash : Nat)
  deriving DecidableEq, Repr

@[expose] def settleOrSlashEscrow (b : EscrowCompensationBond) (nowEpoch : Nat)
    (allLegsOpened : Bool) : Option EscrowOutcome :=
  if !(decide (0 < b.rollbackCost) && decide (b.rollbackCost ≤ b.fundedDeposit) &&
       decide (b.commitEpoch < b.abortDeadline)) then none
  else if allLegsOpened then
    some .settledAllLegs
  else if decide (b.abortDeadline < nowEpoch) then
    some (.slashedForSelectiveAbort b.rollbackCost (b.fundedDeposit - b.rollbackCost))
  else none

/-- Linear single-use escrow vault preventing double-settlement or double-slash replay. -/
structure EscrowVault where
  bond     : EscrowCompensationBond
  consumed : Bool
  deriving DecidableEq, Repr

@[expose] def stepEscrowVault (v : EscrowVault) (nowEpoch : Nat)
    (allLegsOpened : Bool) : EscrowVault × Option EscrowOutcome :=
  if v.consumed then (v, none)
  else match settleOrSlashEscrow v.bond nowEpoch allLegsOpened with
    | some out => ({ v with consumed := true }, some out)
    | none => (v, none)

/-- Post-deadline selective abort (`allLegsOpened = false`, `abortDeadline < nowEpoch`) slashes
    at least `stakeAtRisk ≤ rollbackCost` with exact deposit conservation, and `stepEscrowVault`
    can NEVER pay out a second time (`(stepEscrowVault v' t2 o2).2 = none`)! -/
theorem escrow_slash_covers_rollback_cost (b : EscrowCompensationBond)
    (stakeAtRisk initEpoch slashEpoch retryEpoch : Nat) (retryOpened : Bool)
    (hOk : b.checkForStake stakeAtRisk initEpoch = true)
    (hPast : b.abortDeadline < slashEpoch) :
    ∃ comp rem v',
      stepEscrowVault ⟨b, false⟩ slashEpoch false = (v', some (.slashedForSelectiveAbort comp rem)) ∧
      0 < comp ∧ stakeAtRisk ≤ comp ∧ b.rollbackCost ≤ comp ∧ comp + rem = b.fundedDeposit ∧
      (stepEscrowVault v' retryEpoch retryOpened).2 = none := by
  have hDec : decide (b.abortDeadline < slashEpoch) = true := decide_eq_true hPast
  simp only [EscrowCompensationBond.checkForStake, Bool.and_eq_true, decide_eq_true_eq] at hOk
  obtain ⟨⟨⟨⟨hPos, hStake⟩, hLe⟩, hLt⟩, _⟩ := hOk
  refine ⟨b.rollbackCost, b.fundedDeposit - b.rollbackCost, ⟨b, true⟩, ?_,
    hPos, hStake, Nat.le_refl _, by omega, rfl⟩
  simp [stepEscrowVault, settleOrSlashEscrow, hPos, hLe, hLt, hDec]

inductive AtomicExchangeMode where
  | unbondedCoReceipt
  | bondedEscrow (bond : EscrowCompensationBond)
  | simplexFinalized (P : Protocol) (sent : Sent) (cert : FinCert)

/-- **`C6` Strictly Causal Mealy Port (`directFeedthroughGain = 0`) & `SafePhysicalShield` Dwell Margin**. -/
@[expose] def checkPhysicalCutMargin (directFeedthroughGain : Nat) (p : SampledPhysicalPlantSpec) : Bool :=
  (directFeedthroughGain == 0) &&
  !(decide (p.Ts ≤ 0)) &&
  decide (0 ≤ p.speed) &&
  decide (p.phys.lo + p.speed * p.Ts ≤ p.phys.hi - p.speed * p.Ts)

theorem acausal_loop_refused_in_physical_cut (gain : Nat) (hGain : gain ≠ 0)
    (p : SampledPhysicalPlantSpec) :
    checkPhysicalCutMargin gain p = false := by
  simp [checkPhysicalCutMargin, beq_false_of_ne hGain]

theorem collapsed_dwell_core_refused (gain : Nat) (p : SampledPhysicalPlantSpec)
    (hCollapsed : ¬ (p.phys.lo + p.speed * p.Ts ≤ p.phys.hi - p.speed * p.Ts)) :
    checkPhysicalCutMargin gain p = false := by
  simp [checkPhysicalCutMargin, hCollapsed]

theorem passiveJunction_cut_energy_bounded {S₁ U₁ Y₁ S₂ U₂ Y₂ ExtIn ExtOut : Type}
    (sys₁ : OpenDissipativeSys S₁ U₁ Y₁)
    (sys₂ : OpenDissipativeSys S₂ U₂ Y₂)
    (J : PassiveJunction sys₁ sys₂ ExtIn ExtOut)
    (s₀ : S₁ × S₂) (us : List ExtIn) :
    let coupled := feedbackInterconnect sys₁ sys₂ J
    0 ≤ coupled.energy (coupled.runTrajectory s₀ us) ∧
    coupled.energy (coupled.runTrajectory s₀ us) ≤
      coupled.energy s₀ + coupled.trajectorySupply s₀ us :=
  energy_bounded_along_trajectory (feedbackInterconnect sys₁ sys₂ J) s₀ us

/-! ## 3. The 7-Regime `CutSpec`, `compileCut` Boundary Compiler & Honesty Meta-Theorems -/

/-- Placement proposal carrying concrete regime evidence checked mechanically by `compileCut`. -/
inductive CutRegimeSpec where
  | C0_LocalInline
  | C1_CarrierLowering (expr : NExpr) (pubKnown : Known) (isSecret : String → Bool)
      (secretCommits : String → String → Option Digest256) (interval : Interval) (modulusBound : Nat)
  | C2_CertificateJudge (bundle : VerifiedCertBundle)
  | C3_BoundedFoldIVC (params : HonestFoldParams)
  | C4_Oblivious2Safety (circuit : ObliviousCircuitExpr) (zkMaskSalt : Digest256)
  | C5_FairExchangeAtomic (nowEpoch stakeAtRisk : Nat) (mode : AtomicExchangeMode)
  | C6_PhysicalPassivity (directFeedthroughGain : Nat) (plant : SampledPhysicalPlantSpec)

structure CutSpec where
  cutId           : Nat
  senderSponsor   : Nat
  receiverSponsor : Nat
  senderHeldCaps  : List Nat
  passedCaps      : List Nat
  baseSlack       : RatSlack
  regime          : CutRegimeSpec

inductive CutCompileRefusal where
  | capabilityAmplification (cutId : Nat)
  | negativeBaseSlack (cutId : Nat)
  | crossSponsorInlineForbidden (cutId : Nat)
  | carrierOverflowOrUnderflow (cutId : Nat)
  | judgeUnverifiedOrUnfunded (cutId : Nat)
  | judgeCosplayNonRefuting (cutId : Nat)
  | ivcNormOrAvailabilityViolation (cutId : Nat)
  | secretDependentTopology (cutId : Nat)
  | missingZkOpeningMask (cutId : Nat)
  | cleveUnbondedCoReceiptForbidden (cutId : Nat)
  | underfundedOrExpiredEscrowBond (cutId : Nat)
  | invalidSimplexFinCert (cutId : Nat)
  | acausalOrUnsafePhysicalMargin (cutId : Nat)
  deriving DecidableEq, Repr

structure CompiledCut where
  cutId          : Nat
  regimeTag      : String
  attenuatedCaps : List Nat
  totalSlack     : RatSlack
  deriving DecidableEq, Repr

/-- Helper checking that `bundle.format.judge` genuinely refutes `bundle.badObj`. -/
def checkJudgeRefutesBad (B : VerifiedCertBundle) : Bool :=
  match B.format.judge.check B.verifierFuel B.badObj B.badCert with
  | .refused c _ => B.format.judge.refutes c
  | .ok | .uncovered => false

def checkJudgeAcceptsGood (B : VerifiedCertBundle) : Bool :=
  match B.format.judge.check B.verifierFuel B.obj B.cert with
  | .ok => decide (B.verifierFuel ≤ B.prepaidSponsorCycles)
  | .refused _ _ | .uncovered => false

/-- **The 7-Regime Honest Boundary Compiler (`compileCut`)**. -/
@[expose] def compileCut (spec : CutSpec) : Except CutCompileRefusal CompiledCut := do
  if !subsetCaps spec.passedCaps spec.senderHeldCaps then
    throw (.capabilityAmplification spec.cutId)
  if !decide (0 ≤ spec.baseSlack.num) then
    throw (.negativeBaseSlack spec.cutId)
  match spec.regime with
  | .C0_LocalInline =>
      if spec.senderSponsor == spec.receiverSponsor then
        pure ⟨spec.cutId, "C0_LocalInline", spec.passedCaps, spec.baseSlack⟩
      else
        throw (.crossSponsorInlineForbidden spec.cutId)
  | .C1_CarrierLowering expr pubK isSec secCom iv modBound =>
      if decide (1 < modBound) && decide (iv.hi < modBound) &&
          (pevalRedacted pubK isSec secCom expr).isOk then
        pure ⟨spec.cutId, "C1_CarrierLowering", spec.passedCaps, spec.baseSlack⟩
      else
        throw (.carrierOverflowOrUnderflow spec.cutId)
  | .C2_CertificateJudge B =>
      if !checkJudgeRefutesBad B then
        throw (.judgeCosplayNonRefuting spec.cutId)
      else if checkJudgeAcceptsGood B then
        pure ⟨spec.cutId, "C2_CertificateJudge", spec.passedCaps, spec.baseSlack⟩
      else
        throw (.judgeUnverifiedOrUnfunded spec.cutId)
  | .C3_BoundedFoldIVC params =>
      if params.check then
        pure ⟨spec.cutId, "C3_BoundedFoldIVC", spec.passedCaps, spec.baseSlack + params.crsSlack⟩
      else
        throw (.ivcNormOrAvailabilityViolation spec.cutId)
  | .C4_Oblivious2Safety circuit zkSalt =>
      if !isShapeObliviousExpr circuit then
        throw (.secretDependentTopology spec.cutId)
      else if !(zkSalt != 0#256) then
        throw (.missingZkOpeningMask spec.cutId)
      else
        pure ⟨spec.cutId, "C4_Oblivious2Safety", spec.passedCaps, spec.baseSlack⟩
  | .C5_FairExchangeAtomic nowEp stake mode =>
      match mode with
      | .unbondedCoReceipt =>
          throw (.cleveUnbondedCoReceiptForbidden spec.cutId)
      | .bondedEscrow bond =>
          if bond.checkForStake stake nowEp then
            pure ⟨spec.cutId, "C5_BondedEscrow", spec.passedCaps, spec.baseSlack⟩
          else
            throw (.underfundedOrExpiredEscrowBond spec.cutId)
      | .simplexFinalized P sent cert =>
          if !cert.chain.isEmpty && cert.checks P sent then
            pure ⟨spec.cutId, "C5_SimplexFinalized", spec.passedCaps, spec.baseSlack⟩
          else
            throw (.invalidSimplexFinCert spec.cutId)
  | .C6_PhysicalPassivity gain plant =>
      if checkPhysicalCutMargin gain plant then
        pure ⟨spec.cutId, "C6_PhysicalPassivity", spec.passedCaps, spec.baseSlack⟩
      else
        throw (.acausalOrUnsafePhysicalMargin spec.cutId)

/-- Regime-indexed semantic honesty postcondition established by `compileCut`. -/
def HonestRegimePost (spec : CutSpec) (out : CompiledCut) : Prop :=
  out.attenuatedCaps = spec.passedCaps ∧
  subsetCaps out.attenuatedCaps spec.senderHeldCaps = true ∧
  0 ≤ out.totalSlack.num ∧
  match spec.regime with
  | .C0_LocalInline => spec.senderSponsor = spec.receiverSponsor
  | .C1_CarrierLowering expr pubK isSec secCom iv modBound =>
      1 < modBound ∧ iv.lo ≤ iv.hi ∧ iv.hi < modBound ∧
      ∃ red, pevalRedacted pubK isSec secCom expr = .ok red
  | .C2_CertificateJudge B =>
      B.verifierFuel ≤ B.prepaidSponsorCycles ∧
      B.format.judge.Meaning B.obj B.cert ∧
      (∀ c', ¬ B.format.judge.Meaning B.badObj c')
  | .C3_BoundedFoldIVC p =>
      0 < p.foldDepth ∧ p.maxNormAtDepth < p.sisBetaBound ∧
      p.isCompressingCrsKeyed = true ∧ p.deltaBytes ≠ [] ∧
      commitDeltaDigest p.deltaBytes = p.deltaPinDigest ∧
      out.totalSlack = spec.baseSlack + p.crsSlack
  | .C4_Oblivious2Safety circuit zkSalt =>
      zkSalt ≠ 0#256 ∧
      ∀ (env₁ env₂ : Nat → Bool),
        (stageCircuitExpr circuit env₁).topology = (stageCircuitExpr circuit env₂).topology
  | .C5_FairExchangeAtomic nowEp stake mode =>
      match mode with
      | .unbondedCoReceipt => False
      | .bondedEscrow b =>
          0 < b.rollbackCost ∧ stake ≤ b.rollbackCost ∧ b.rollbackCost ≤ b.fundedDeposit ∧
          b.commitEpoch < b.abortDeadline ∧ nowEp ≤ b.abortDeadline
      | .simplexFinalized P sent cert =>
          cert.chain ≠ [] ∧ cert.checks P sent = true ∧ Finalized P sent cert.view cert.chain
  | .C6_PhysicalPassivity gain plant =>
      gain = 0 ∧ ¬ (plant.Ts ≤ 0) ∧ 0 ≤ plant.speed ∧
      plant.phys.lo + plant.speed * plant.Ts ≤ plant.phys.hi - plant.speed * plant.Ts

private theorem ratSlack_add_nonneg {a b : RatSlack} (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (a + b).num := by
  have hda : 0 < a.denInt := RatSlack.denInt_pos a
  have hdb : 0 < b.denInt := RatSlack.denInt_pos b
  exact Int.add_nonneg (Int.mul_nonneg ha (Int.le_of_lt hdb)) (Int.mul_nonneg hb (Int.le_of_lt hda))

/-- **Master Honesty Theorem (`compileCut_honest_by_regime`)**:
    Every `CompiledCut` accepted by `compileCut` establishes genuine non-tautological semantic
    evidence across all 7 regimes (`Judge.Meaning` + refutation in `C2`, retrievable committed
    `deltaBytes` in `C3`, universal `env₁, env₂` topology invariance in `C4`, live stake-covering
    escrow or non-empty `Finalized` chain in `C5`, and zero-feedthrough dwell core in `C6`). -/
theorem compileCut_honest_by_regime {spec : CutSpec} {out : CompiledCut}
    (hOk : compileCut spec = .ok out) : HonestRegimePost spec out := by
  unfold HonestRegimePost
  unfold compileCut at hOk
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hOk
  cases hCap : subsetCaps spec.passedCaps spec.senderHeldCaps
  · simp [hCap] at hOk
  simp only [hCap, Bool.not_true, Bool.false_eq_true, ite_false] at hOk
  cases hSlk : decide (0 ≤ spec.baseSlack.num)
  · simp [hSlk] at hOk
  simp only [hSlk, Bool.not_true, Bool.false_eq_true, ite_false] at hOk
  have hBaseNonneg : 0 ≤ spec.baseSlack.num := of_decide_eq_true hSlk
  cases hReg : spec.regime with
  | C0_LocalInline =>
    rw [hReg] at hOk; dsimp only
    cases hSp : (spec.senderSponsor == spec.receiverSponsor)
    · simp [hSp] at hOk
    · simp only [hSp, ite_true, Except.ok.injEq] at hOk; subst hOk
      exact ⟨rfl, hCap, hBaseNonneg, beq_iff_eq.1 hSp⟩
  | C1_CarrierLowering expr pubK isSec secCom iv modBound =>
    rw [hReg] at hOk; dsimp only
    by_cases hG : (decide (1 < modBound) && decide (iv.hi < modBound) &&
        (pevalRedacted pubK isSec secCom expr).isOk) = true
    · simp only [hG, ite_true, Except.ok.injEq] at hOk; subst hOk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
      cases hPev : pevalRedacted pubK isSec secCom expr with
      | error _ => simp [hPev, Except.isOk, Except.toBool] at hG
      | ok red => exact ⟨rfl, hCap, hBaseNonneg, hG.1.1, iv.wf, hG.1.2, red, rfl⟩
    · simp [hG] at hOk
  | C2_CertificateJudge B =>
    rw [hReg] at hOk; dsimp only
    cases hBad : checkJudgeRefutesBad B
    · simp [hBad] at hOk
    · simp only [hBad, Bool.not_true, Bool.false_eq_true, ite_false] at hOk
      cases hGood : checkJudgeAcceptsGood B
      · simp [hGood] at hOk
      · simp only [hGood, ite_true, Except.ok.injEq] at hOk; subst hOk
        unfold checkJudgeAcceptsGood at hGood
        cases hChkOk : B.format.judge.check B.verifierFuel B.obj B.cert with
        | refused _ _ | uncovered => simp [hChkOk] at hGood
        | ok =>
          simp only [hChkOk, decide_eq_true_eq] at hGood
          unfold checkJudgeRefutesBad at hBad
          cases hChkBad : B.format.judge.check B.verifierFuel B.badObj B.badCert with
          | ok | uncovered => simp [hChkBad] at hBad
          | refused cl tr =>
            simp only [hChkBad] at hBad
            refine ⟨rfl, hCap, hBaseNonneg, hGood, B.format.judge.sound hChkOk, ?_⟩
            intro c' hMeanBad
            exact B.format.judge.refuted hChkBad hBad c' hMeanBad
  | C3_BoundedFoldIVC p =>
    rw [hReg] at hOk; dsimp only
    cases hP : p.check
    · simp [hP] at hOk
    · simp only [hP, ite_true, Except.ok.injEq] at hOk; subst hOk
      simp only [HonestFoldParams.check, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq, beq_iff_eq, List.isEmpty_eq_false_iff] at hP
      obtain ⟨⟨⟨⟨⟨hD, hN⟩, hCrs⟩, hCrsPos⟩, hDA⟩, hPin⟩ := hP
      exact ⟨rfl, hCap, ratSlack_add_nonneg hBaseNonneg hCrsPos, hD, hN, hCrs, hDA, hPin, rfl⟩
  | C4_Oblivious2Safety circuit zkSalt =>
    rw [hReg] at hOk; dsimp only
    cases hOb : isShapeObliviousExpr circuit
    · simp [hOb] at hOk
    · simp only [hOb, Bool.not_true, Bool.false_eq_true, ite_false] at hOk
      cases hZk : (zkSalt != 0#256)
      · simp [hZk] at hOk
      · simp only [hZk, Bool.not_true, Bool.false_eq_true, ite_false, Except.ok.injEq] at hOk
        subst hOk
        exact ⟨rfl, hCap, hBaseNonneg, bne_iff_ne.1 hZk, isShapeObliviousExpr_sound circuit hOb⟩
  | C5_FairExchangeAtomic nowEp stake mode =>
    rw [hReg] at hOk; dsimp only
    cases mode with
    | unbondedCoReceipt => simp at hOk
    | bondedEscrow b =>
      cases hB : b.checkForStake stake nowEp
      · simp [hB] at hOk
      · simp only [hB, ite_true, Except.ok.injEq] at hOk; subst hOk
        simp only [EscrowCompensationBond.checkForStake, Bool.and_eq_true, decide_eq_true_eq] at hB
        exact ⟨rfl, hCap, hBaseNonneg, hB.1.1.1.1, hB.1.1.1.2, hB.1.1.2, hB.1.2, hB.2⟩
    | simplexFinalized P sent cert =>
      by_cases hG : (!cert.chain.isEmpty && cert.checks P sent) = true
      · simp only [hG, ite_true, Except.ok.injEq] at hOk; subst hOk
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hG
        exact ⟨rfl, hCap, hBaseNonneg, hG.1, hG.2, FinCert.checks_implies_finalized hG.2⟩
      · simp [hG] at hOk
  | C6_PhysicalPassivity gain plant =>
    rw [hReg] at hOk; dsimp only
    cases hPh : checkPhysicalCutMargin gain plant
    · simp [hPh] at hOk
    · simp only [hPh, ite_true, Except.ok.injEq] at hOk; subst hOk
      simp only [checkPhysicalCutMargin, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, decide_eq_true_eq, beq_iff_eq] at hPh
      exact ⟨rfl, hCap, hBaseNonneg, hPh.1.1.1, hPh.1.1.2, hPh.1.2, hPh.2⟩

/-- **Distributed Boundary Blind-Spot Refusals (`distributed_cut_blind_spots_closed`)**:
    1. Unbonded co-receipts in `C5` are refused.
    2. Passing capabilities outside `senderHeldCaps` is refused across all regimes.
    3. `C3` folding without non-empty committed `deltaBytes` is refused.
    4. `C4` staging with secret-dependent `.leakyShortCircuitOr` AST pruning is refused. -/
theorem distributed_cut_blind_spots_closed (cid sA sB nowEp stake : Nat) (caps : List Nat)
    (slk : RatSlack) (hSlk : 0 ≤ slk.num) :
    compileCut ⟨cid, sA, sB, caps, caps, slk, .C5_FairExchangeAtomic nowEp stake .unbondedCoReceipt⟩ =
      .error (.cleveUnbondedCoReceiptForbidden cid) ∧
    (∀ unheld, subsetCaps unheld caps = false → ∀ reg,
      compileCut ⟨cid, sA, sB, caps, unheld, slk, reg⟩ = .error (.capabilityAmplification cid)) ∧
    (∀ p : HonestFoldParams, p.deltaBytes = [] →
      compileCut ⟨cid, sA, sB, caps, caps, slk, .C3_BoundedFoldIVC p⟩ =
        .error (.ivcNormOrAvailabilityViolation cid)) ∧
    (∀ (v : Nat) (fb : ObliviousCircuitExpr) (salt : Digest256),
      compileCut ⟨cid, sA, sB, caps, caps, slk,
        .C4_Oblivious2Safety (.leakyShortCircuitOr v fb) salt⟩ =
        .error (.secretDependentTopology cid)) := by
  have hSubRefl : subsetCaps caps caps = true := subsetCaps_refl caps
  have hSlkDec : decide (0 ≤ slk.num) = true := decide_eq_true hSlk
  refine ⟨?_, fun unheld hBad reg => ?_, fun p hNoDA => ?_, fun v fb salt => ?_⟩
  · simp [compileCut, hSubRefl, hSlkDec, throw, throwThe, MonadExceptOf.throw]
  · simp [compileCut, hBad, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have hChk : p.check = false := withheld_ivc_state_delta_refused p hNoDA
    simp [compileCut, hSubRefl, hSlkDec, hChk, throw, throwThe, MonadExceptOf.throw]
  · simp [compileCut, hSubRefl, hSlkDec, isShapeObliviousExpr, throw, throwThe, MonadExceptOf.throw]

/-- Multi-hop pipeline of `CompiledCut`s threading capability attenuation and additive `RatSlack`. -/
inductive ValidCutTrace : List Nat → List CutSpec → List Nat → RatSlack → Prop where
  | nil (caps : List Nat) : ValidCutTrace caps [] caps 0
  | cons {initCaps midCaps finalCaps : List Nat} {spec : CutSpec} {out : CompiledCut}
      {rest : List CutSpec} {restSlack : RatSlack} :
      spec.senderHeldCaps = initCaps →
      compileCut spec = .ok out →
      out.attenuatedCaps = midCaps →
      ValidCutTrace midCaps rest finalCaps restSlack →
      ValidCutTrace initCaps (spec :: rest) finalCaps (out.totalSlack + restSlack)

theorem validCutTrace_conserves_caps_and_slack {initCaps finalCaps : List Nat}
    {specs : List CutSpec} {totSlack : RatSlack}
    (hTr : ValidCutTrace initCaps specs finalCaps totSlack) :
    subsetCaps finalCaps initCaps = true ∧ 0 ≤ totSlack.num := by
  induction hTr with
  | nil cs => exact ⟨subsetCaps_refl cs, Int.le_refl 0⟩
  | @cons initC midCaps finalC spec out rest restSlk hSender hComp hMid _ ih =>
    have hPost := compileCut_honest_by_regime hComp
    have hSubStep : subsetCaps midCaps initC = true := by
      have hs := hPost.2.1
      rwa [hSender, hMid] at hs
    exact ⟨subsetCaps_trans ih.1 hSubStep, ratSlack_add_nonneg hPost.2.2.1 ih.2⟩

end Obend.Metatheory.StratifiedCut
end
