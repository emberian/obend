module
/- Persistent post-quantum custody integration: epoch latches, revocation, and multi-turn
safety. The namespace is preserved for existing consumers; cryptographic primitives remain
in `Obend.Crypto.ThresholdHashMpc` without imports of policy, OS, or hardware integration. -/
public import Obend.Crypto.ThresholdHashMpc
public import Obend.Polis.GrainPowerbox
public import Obend.OS.Sel4MicrokitKernel
public import Obend.Hardware.GlitchAndTempestSafe
import all Obend.Polis.GrainPowerbox

public section
namespace Obend.Crypto.ThresholdHashMpc

open Obend
open Obend.Analysis
open Obend.Apps.ZkNtt
open Obend.Crypto
open Obend.Crypto.BinaryTower256
open Obend.Crypto.ThresholdMpcUcGames
open Obend.Crypto.PqHashSignatures
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Judge.Computational
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Polis.GrainPowerbox
open Obend.OS.Sel4MicrokitKernel
open Obend.Hardware.PipelinedRisc
open Obend.Hardware.GlitchAndTempestSafe

set_option autoImplicit false

/-! ## 5. Multi-Turn Custody Safety (`EpochLatchState`, `GrainPowerbox`, `Sel4MicrokitKernel`, `GlitchAndTempestSafe`) -/

/-- Persistent monotonic anti-double-sign latch state per custody node (`leanSig` stateful leaf guard). -/
structure EpochLatchState where
  highWater : Option Nat
  boundDigest : Option (List UInt8)
  deriving DecidableEq, Repr

def initEpochLatch : EpochLatchState := ⟨none, none⟩

/-- **Load-Bearing Persist-Before-Sign Monotonic Latch (`stepEpochLatch`)**:
    1. Strictly higher epoch `hw < ep`: advances `highWater := some ep, boundDigest := some mu`;
    2. Same epoch `ep = hw`: permits **idempotent crash-recovery retry ONLY when `boundDigest == some mu`**!
       Mutating this branch to omit `st.boundDigest = some mu` is caught immediately by `#tooth` witness #2!
    3. Stale epoch `ep < hw`: strictly refuses (`none`)! -/
@[expose] def stepEpochLatch (st : EpochLatchState) (ep : Nat) (mu : List UInt8) : Option EpochLatchState :=
  match st.highWater with
  | none => some { highWater := some ep, boundDigest := some mu }
  | some hw =>
    if hw < ep then
      some { highWater := some ep, boundDigest := some mu }
    else if ep = hw then
      if st.boundDigest = some mu then some st else none
    else
      none

/-- Single honest node's sequence of latch transitions `(ep, mu)` from `st`. -/
def ValidNodeLatchTrace : EpochLatchState → List (Nat × List UInt8) → EpochLatchState → Prop
  | st, [], st' => st' = st
  | st, (ep, mu) :: rest, stFinal =>
    ∃ stNext, stepEpochLatch st ep mu = some stNext ∧ ValidNodeLatchTrace stNext rest stFinal

private theorem stepEpochLatch_monotone {st st' : EpochLatchState} {ep : Nat} {mu : List UInt8}
    (hStep : stepEpochLatch st ep mu = some st') :
    (∃ hw', st'.highWater = some hw' ∧ ep ≤ hw') ∧
    (∀ hw, st.highWater = some hw → hw ≤ ep ∧ (ep = hw → st.boundDigest = some mu ∧ st' = st)) ∧
    (st.highWater = none ∨ (∃ hw, st.highWater = some hw ∧ hw < ep) →
      st' = { highWater := some ep, boundDigest := some mu }) := by
  unfold stepEpochLatch at hStep
  cases hHw : st.highWater with
  | none =>
    rw [hHw] at hStep
    simp only [Option.some.injEq] at hStep
    subst hStep
    refine ⟨⟨ep, rfl, Nat.le_refl _⟩, ?_, fun _ => rfl⟩
    intro _ h; cases h
  | some hw =>
    rw [hHw] at hStep
    by_cases hLt : hw < ep
    · simp only [hLt, ↓reduceIte, Option.some.injEq] at hStep
      subst hStep
      refine ⟨⟨ep, rfl, Nat.le_refl _⟩, fun hw0 hEq => ?_, fun _ => rfl⟩
      injection hEq with hEq'; subst hEq'
      exact ⟨by omega, fun _ => by omega⟩
    · simp only [hLt, ↓reduceIte] at hStep
      by_cases hEqEp : ep = hw
      · subst hEqEp
        simp only [↓reduceIte] at hStep
        by_cases hBd : st.boundDigest = some mu
        · simp only [hBd, ↓reduceIte, Option.some.injEq] at hStep
          subst hStep
          refine ⟨⟨ep, hHw, Nat.le_refl _⟩, fun hw0 hEq => ?_, fun hOr => ?_⟩
          · injection hEq with hEq'; subst hEq'
            exact ⟨Nat.le_refl _, fun _ => ⟨hBd, rfl⟩⟩
          · rcases hOr with hN | ⟨hw0, hS, hL⟩
            · cases hN
            · injection hS with hE; omega
        · simp [hBd] at hStep
      · simp [hEqEp] at hStep

private theorem latch_trace_locked_after_ep :
    ∀ (evs : List (Nat × List UInt8)) (st stFinal : EpochLatchState) (ep : Nat) (mu : List UInt8),
      st.highWater = some ep →
      st.boundDigest = some mu →
      ValidNodeLatchTrace st evs stFinal →
      ∀ mu', (ep, mu') ∈ evs → mu' = mu
  | [], _, _, _, _, _, _, _, _, hMem => by cases hMem
  | (ep2, mu2) :: rest, st, stFinal, ep, mu, hHw, hBd, ⟨stNext, hStep, hRest⟩, mu', hMem => by
    obtain ⟨_, hFromSome, _⟩ := stepEpochLatch_monotone hStep
    obtain ⟨hLe, hEqImp⟩ := hFromSome ep hHw
    simp only [List.mem_cons, Prod.mk.injEq] at hMem
    rcases hMem with ⟨heM, hmM⟩ | hInRest
    · subst heM hmM
      obtain ⟨hBdEq, _⟩ := hEqImp rfl
      rw [hBd] at hBdEq
      injection hBdEq with hMuEq
      exact hMuEq.symm
    · by_cases hSame : ep2 = ep
      · obtain ⟨_, hStSame⟩ := hEqImp hSame
        rw [hStSame] at hRest
        exact latch_trace_locked_after_ep rest st stFinal ep mu hHw hBd hRest mu' hInRest
      · have hStrict : ep < ep2 := by omega
        have hNoLower : ∀ (tail : List (Nat × List UInt8)) (s sF : EpochLatchState) (hwCur : Nat),
            s.highWater = some hwCur → ValidNodeLatchTrace s tail sF →
            ∀ e m, (e, m) ∈ tail → hwCur ≤ e := by
          intro tail
          induction tail with
          | nil => intro _ _ _ _ _ _ _ hm; cases hm
          | cons hd tl ih =>
            rcases hd with ⟨e0, m0⟩
            intro s sF hwCur hsHw ⟨sN, hsStep, hsTl⟩ e m hm
            obtain ⟨⟨hwN, hsNHw, he0Le⟩, hsFrom, _⟩ := stepEpochLatch_monotone hsStep
            have hCurLeE0 : hwCur ≤ e0 := (hsFrom hwCur hsHw).1
            simp only [List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨he0, _⟩ | hmTl
            · subst he0; exact hCurLeE0
            · have hNLe := ih sN sF hwN hsNHw hsTl e m hmTl
              omega
        obtain ⟨⟨hwN, hNextHw, hEp2Le⟩, _, _⟩ := stepEpochLatch_monotone hStep
        have hGe := hNoLower rest stNext stFinal hwN hNextHw hRest ep mu' hInRest
        omega

/-- Every honest node's persistent latch trace assigns at most ONE digest `mu` to any epoch `ep`,
    even across arbitrary crash-recovery retries, out-of-order replays, and later epochs! -/
theorem honest_latch_trace_unique_per_epoch :
    ∀ (evs : List (Nat × List UInt8)) (st stFinal : EpochLatchState),
      ValidNodeLatchTrace st evs stFinal →
      ∀ (ep : Nat) (mu₁ mu₂ : List UInt8),
        (ep, mu₁) ∈ evs → (ep, mu₂) ∈ evs → mu₁ = mu₂
  | [], _, _, _, _, _, _, h1, _ => by cases h1
  | (ep0, mu0) :: rest, st, stFinal, ⟨stNext, hStep, hRest⟩, ep, mu₁, mu₂, h1, h2 => by
    have hHeadLock : ∀ (muB : List UInt8),
        stepEpochLatch st ep mu0 = some stNext → (ep, muB) ∈ rest → muB = mu0 := by
      intro muB hStepEp hMemRest
      obtain ⟨_, hFromSome, hFresh⟩ := stepEpochLatch_monotone hStepEp
      cases hStHw : st.highWater with
      | none =>
        rw [hFresh (.inl hStHw)] at hRest
        exact latch_trace_locked_after_ep rest ⟨some ep, some mu0⟩ stFinal ep mu0 rfl rfl hRest muB hMemRest
      | some hw =>
        by_cases hLt : hw < ep
        · rw [hFresh (.inr ⟨hw, hStHw, hLt⟩)] at hRest
          exact latch_trace_locked_after_ep rest ⟨some ep, some mu0⟩ stFinal ep mu0 rfl rfl hRest muB hMemRest
        · have hSame : ep = hw := by have := (hFromSome hw hStHw).1; omega
          obtain ⟨hBd, hStEq⟩ := (hFromSome hw hStHw).2 hSame
          rw [hStEq] at hRest
          exact latch_trace_locked_after_ep rest st stFinal ep mu0 (hSame ▸ hStHw) hBd hRest muB hMemRest
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨he1, hm1⟩ | h1Rest
    · subst he1 hm1
      rcases h2 with ⟨_, hm2⟩ | h2Rest
      · exact hm2.symm
      · exact (hHeadLock mu₂ hStep h2Rest).symm
    · rcases h2 with ⟨he2, hm2⟩ | h2Rest
      · subst he2 hm2; exact hHeadLock mu₁ hStep h1Rest
      · exact honest_latch_trace_unique_per_epoch rest stNext stFinal hRest ep mu₁ mu₂ h1Rest h2Rest

/-- **Stateful `leanSig` Quorum Anti-Double-Sign Safety (`leanSig_quorum_never_double_signs`)**:
    In a custody committee of size `3 * f + 1` with `≤ f` Byzantine/corrupt nodes (`faulty`),
    requiring `2 * f + 1` persist-before-sign latch approvals (`2 * t_latch - n > f`), if quorum
    `q1` signs `(ep, mu₁)` and quorum `q2` signs `(ep, mu₂)` at ANY points along a multi-turn
    execution (across crashes, retries, and partitions), `honest_quorum_intersection` witnesses an
    honest validator `v ∈ q1 ∩ q2` whose persistent latch trace forces `mu₁ = mu₂`! -/
theorem leanSig_quorum_never_double_signs
    (committee : List NodeId) (f : Nat)
    (q1 q2 faulty : NodeId → Bool)
    (nodeLogs : NodeId → List (Nat × List UInt8))
    (nodeFinal : NodeId → EpochLatchState)
    (hSize : committee.length = 3 * f + 1)
    (hQ1 : 2 * f + 1 ≤ (committee.filter q1).length)
    (hQ2 : 2 * f + 1 ≤ (committee.filter q2).length)
    (hFaulty : (committee.filter faulty).length ≤ f)
    (hHonestValid : ∀ v ∈ committee, faulty v = false →
      ValidNodeLatchTrace initEpochLatch (nodeLogs v) (nodeFinal v))
    (ep : Nat) (mu₁ mu₂ : List UInt8)
    (hVoted1 : ∀ v ∈ committee, q1 v = true → faulty v = false → (ep, mu₁) ∈ nodeLogs v)
    (hVoted2 : ∀ v ∈ committee, q2 v = true → faulty v = false → (ep, mu₂) ∈ nodeLogs v) :
    mu₁ = mu₂ := by
  obtain ⟨v, hvMem, hvQ1, hvQ2, hvHonest⟩ :=
    honest_quorum_intersection committee f q1 q2 faulty hSize hQ1 hQ2 hFaulty
  exact honest_latch_trace_unique_per_epoch
    (nodeLogs v) initEpochLatch (nodeFinal v)
    (hHonestValid v hvMem hvHonest) ep mu₁ mu₂
    (hVoted1 v hvMem hvQ1 hvHonest) (hVoted2 v hvMem hvQ2 hvHonest)

/-- Capability-gated custody signing authorization welding `GrainPowerbox.capLive`. -/
@[expose] def checkCustodySignAuth (host : PowerboxHost) (cap : CapDescriptor) (needRights : UInt64) : Bool :=
  capLive host cap needRights

/-- **Transitive Membrane Revocation Blocks Threshold Signing (`revoked_membrane_blocks_threshold_sign`)**:
    Once ANY enclosing `GrainPowerbox` membrane `m ∈ cap.membranes` is present in `host.revokedMembranes`,
    `checkCustodySignAuth` unconditionally evaluates to `false`, blocking threshold share release! -/
theorem revoked_membrane_blocks_threshold_sign
    (host : PowerboxHost) (cap : CapDescriptor) (needRights : UInt64) (m : MembraneId)
    (hm : m ∈ cap.membranes) (hRevoked : host.revokedMembranes.contains m = true) :
    checkCustodySignAuth host cap needRights = false := by
  unfold checkCustodySignAuth capLive
  rw [membranesLive_false_of_mem hm hRevoked]
  rfl

/-- Immutable system configuration for a multi-turn PQ threshold custody MPC cluster. -/
structure CustodyMpcSysConfig where
  engine : ThresholdEngine
  params : PqHashParams
  committee : List NodeId
  maxFaulty : Nat
  faulty : NodeId → Bool
  needRights : UInt64
  sharedBundle : SharedSecretKeyBundle
  logicalSk : PqSecretKey

/-- Mutable multi-turn custody MPC system state (`PowerboxHost`, persistent latches + logs, signed history). -/
structure CustodyMpcSysState where
  powerbox : PowerboxHost
  latches : NodeId → EpochLatchState
  latchLogs : NodeId → List (Nat × List UInt8)
  signedHistory : List (Nat × List UInt8 × List UInt8 × PqHashSig)

/-- Open-world turn inputs to the custody MPC state machine: capability revocation or threshold sign. -/
inductive CustodyMpcTurn where
  | revokeCustodyMembrane (m : MembraneId)
  | thresholdSignTurn (cap : CapDescriptor) (ep : Nat) (msg optRand : List UInt8)
      (maxGrind : Nat) (quorumApprove : NodeId → Bool)

/-- Deterministic single-turn evaluator for `CustodyMpcSysState`. -/
def stepCustodyMpcSys (cfg : CustodyMpcSysConfig) (st : CustodyMpcSysState) (turn : CustodyMpcTurn) :
    Option CustodyMpcSysState :=
  match turn with
  | .revokeCustodyMembrane m =>
    some { st with powerbox := { st.powerbox with revokedMembranes := st.powerbox.revokedMembranes.insert m } }
  | .thresholdSignTurn cap ep msg optRand maxGrind quorumApprove =>
    if !(checkCustodySignAuth st.powerbox cap cfg.needRights) then none
    else if (cfg.committee.filter quorumApprove).length < 2 * cfg.maxFaulty + 1 then none
    else
      let pk := derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk
      let mu := thPreHash cfg.engine.suite pk.pkSeed pk.pkRoot msg
      let honestApprovers := cfg.committee.filter (fun v => quorumApprove v && !(cfg.faulty v))
      if !(honestApprovers.all (fun v => (stepEpochLatch (st.latches v) ep mu).isSome)) then none
      else
        match evalThresholdSign cfg.engine cfg.params cfg.sharedBundle msg optRand ep maxGrind with
        | none => none
        | some sig =>
          let nextLatches : NodeId → EpochLatchState := fun v =>
            if v ∈ cfg.committee ∧ quorumApprove v = true ∧ cfg.faulty v = false then
              (stepEpochLatch (st.latches v) ep mu).getD (st.latches v)
            else st.latches v
          let nextLogs : NodeId → List (Nat × List UInt8) := fun v =>
            if v ∈ cfg.committee ∧ quorumApprove v = true ∧ cfg.faulty v = false then
              st.latchLogs v ++ [(ep, mu)]
            else st.latchLogs v
          some { powerbox := st.powerbox, latches := nextLatches, latchLogs := nextLogs,
                 signedHistory := st.signedHistory ++ [(ep, mu, msg, sig)] }

/-- Recursive Multi-Turn Custody Reachability Relation (`ValidPqCustodyMpcTrace`, `def` for `#tooth` replay). -/
def ValidPqCustodyMpcTrace (cfg : CustodyMpcSysConfig) :
    CustodyMpcSysState → List CustodyMpcTurn → CustodyMpcSysState → Prop
  | st, [], stFinal => stFinal = st
  | st, turn :: rest, stFinal =>
    ∃ stNext, stepCustodyMpcSys cfg st turn = some stNext ∧ ValidPqCustodyMpcTrace cfg stNext rest stFinal

/-- **Environment Anti-Narrowing Completeness (`custodyMpcTurn_skip_implies_violation`)**:
    `stepCustodyMpcSys` rejects ONLY on unauthorized/under-quorum/stale-latch/invalid sign turns; revocations never block! -/
theorem custodyMpcTurn_skip_implies_violation
    (cfg : CustodyMpcSysConfig) (st : CustodyMpcSysState) (turn : CustodyMpcTurn) :
    (∀ m, (stepCustodyMpcSys cfg st (.revokeCustodyMembrane m)).isSome = true) ∧
    (stepCustodyMpcSys cfg st turn = none →
      ∃ cap ep msg optRand maxGrind quorumApprove,
        turn = .thresholdSignTurn cap ep msg optRand maxGrind quorumApprove ∧
        (checkCustodySignAuth st.powerbox cap cfg.needRights = false ∨
         (cfg.committee.filter quorumApprove).length < 2 * cfg.maxFaulty + 1 ∨
         (let pk := derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk
          let mu := thPreHash cfg.engine.suite pk.pkSeed pk.pkRoot msg
          (cfg.committee.filter (fun v => quorumApprove v && !(cfg.faulty v))).all
            (fun v => (stepEpochLatch (st.latches v) ep mu).isSome) = false) ∨
         evalThresholdSign cfg.engine cfg.params cfg.sharedBundle msg optRand ep maxGrind = none)) := by
  refine ⟨fun _ => rfl, fun hNone => ?_⟩
  cases turn with
  | revokeCustodyMembrane m => cases hNone
  | thresholdSignTurn cap ep msg optRand maxGrind qa =>
    refine ⟨cap, ep, msg, optRand, maxGrind, qa, rfl, ?_⟩
    unfold stepCustodyMpcSys at hNone
    dsimp only at hNone
    cases hAuth : checkCustodySignAuth st.powerbox cap cfg.needRights
    · exact .inl rfl
    · rw [hAuth] at hNone
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone
      by_cases hQ : (cfg.committee.filter qa).length < 2 * cfg.maxFaulty + 1
      · exact .inr (.inl hQ)
      · simp only [hQ, ↓reduceIte] at hNone
        cases hAll : (cfg.committee.filter (fun v => qa v && !(cfg.faulty v))).all
            (fun v => (stepEpochLatch (st.latches v) ep
              (thPreHash cfg.engine.suite (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkSeed
                (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkRoot msg)).isSome)
        · exact .inr (.inr (.inl hAll))
        · rw [hAll] at hNone
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone
          cases hEval : evalThresholdSign cfg.engine cfg.params cfg.sharedBundle msg optRand ep maxGrind with
          | none => exact .inr (.inr (.inr rfl))
          | some s => rw [hEval] at hNone; cases hNone

private theorem validNodeLatchTrace_snoc :
    ∀ (evs : List (Nat × List UInt8)) (st0 stMid stNext : EpochLatchState) (ep : Nat) (mu : List UInt8),
      ValidNodeLatchTrace st0 evs stMid →
      stepEpochLatch stMid ep mu = some stNext →
      ValidNodeLatchTrace st0 (evs ++ [(ep, mu)]) stNext
  | [], st0, stMid, stNext, ep, mu, hEq, hStep => by
    subst hEq
    exact ⟨stNext, hStep, rfl⟩
  | (e0, m0) :: rest, st0, stMid, stNext, ep, mu, ⟨s1, hs1, hRest⟩, hStep =>
    ⟨s1, hs1, validNodeLatchTrace_snoc rest s1 stMid stNext ep mu hRest hStep⟩

private theorem custodyTrace_preserves_invariants
    (cfg : CustodyMpcSysConfig)
    (hSize : cfg.committee.length = 3 * cfg.maxFaulty + 1)
    (hFaulty : (cfg.committee.filter cfg.faulty).length ≤ cfg.maxFaulty)
    (hRecon : cfg.sharedBundle.reconstructSk = cfg.logicalSk) :
    ∀ (turns : List CustodyMpcTurn) (st stFinal : CustodyMpcSysState),
      (∀ v ∈ cfg.committee, cfg.faulty v = false →
        ValidNodeLatchTrace initEpochLatch (st.latchLogs v) (st.latches v)) →
      (∀ ep mu msg sig, (ep, mu, msg, sig) ∈ st.signedHistory →
        verifyPqHashSig cfg.engine.suite cfg.params
          (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk) msg sig = true ∧
        ∃ qa : NodeId → Bool,
          2 * cfg.maxFaulty + 1 ≤ (cfg.committee.filter qa).length ∧
          ∀ v ∈ cfg.committee, qa v = true → cfg.faulty v = false → (ep, mu) ∈ st.latchLogs v) →
      ValidPqCustodyMpcTrace cfg st turns stFinal →
      (∀ v ∈ cfg.committee, cfg.faulty v = false →
        ValidNodeLatchTrace initEpochLatch (stFinal.latchLogs v) (stFinal.latches v)) ∧
      (∀ ep mu msg sig, (ep, mu, msg, sig) ∈ stFinal.signedHistory →
        verifyPqHashSig cfg.engine.suite cfg.params
          (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk) msg sig = true ∧
        ∃ qa : NodeId → Bool,
          2 * cfg.maxFaulty + 1 ≤ (cfg.committee.filter qa).length ∧
          ∀ v ∈ cfg.committee, qa v = true → cfg.faulty v = false → (ep, mu) ∈ stFinal.latchLogs v)
  | [], st, stFinal, hLogs, hHist, hEq => by
    subst hEq; exact ⟨hLogs, hHist⟩
  | turn :: rest, st, stFinal, hLogs, hHist, ⟨stNext, hStep, hRest⟩ => by
    cases turn with
    | revokeCustodyMembrane m =>
      simp only [stepCustodyMpcSys, Option.some.injEq] at hStep
      rw [← hStep] at hRest
      exact custodyTrace_preserves_invariants cfg hSize hFaulty hRecon rest
        { st with powerbox := { st.powerbox with revokedMembranes := st.powerbox.revokedMembranes.insert m } }
        stFinal hLogs hHist hRest
    | thresholdSignTurn cap ep msg optRand maxGrind qa =>
      unfold stepCustodyMpcSys at hStep
      dsimp only at hStep
      cases hAuth : checkCustodySignAuth st.powerbox cap cfg.needRights
      · simp [hAuth] at hStep
      · rw [hAuth] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hQLt : (cfg.committee.filter qa).length < 2 * cfg.maxFaulty + 1
        · simp [hQLt] at hStep
        · simp only [hQLt, ↓reduceIte] at hStep
          let pk := derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk
          let mu := thPreHash cfg.engine.suite pk.pkSeed pk.pkRoot msg
          cases hAll : (cfg.committee.filter (fun v => qa v && !(cfg.faulty v))).all
              (fun v => (stepEpochLatch (st.latches v) ep mu).isSome)
          · rw [show (cfg.committee.filter (fun v => qa v && !(cfg.faulty v))).all
                (fun v => (stepEpochLatch (st.latches v) ep
                  (thPreHash cfg.engine.suite (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkSeed
                    (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkRoot msg)).isSome) = false from hAll] at hStep
            simp at hStep
          · rw [show (cfg.committee.filter (fun v => qa v && !(cfg.faulty v))).all
                (fun v => (stepEpochLatch (st.latches v) ep
                  (thPreHash cfg.engine.suite (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkSeed
                    (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk).pkRoot msg)).isSome) = true from hAll] at hStep
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
            cases hSign : evalThresholdSign cfg.engine cfg.params cfg.sharedBundle msg optRand ep maxGrind with
            | none => rw [hSign] at hStep; cases hStep
            | some sig =>
              rw [hSign] at hStep
              simp only [Option.some.injEq] at hStep
              rw [← hStep] at hRest
              have hVerSig : verifyPqHashSig cfg.engine.suite cfg.params pk msg sig = true :=
                (thresholdSign_eq_singleSign cfg.engine cfg.params cfg.sharedBundle cfg.logicalSk
                  hRecon msg optRand ep maxGrind).2 sig hSign
              have hAllProp := List.all_eq_true.mp hAll
              let stStepped : CustodyMpcSysState :=
                { powerbox := st.powerbox
                  latches := fun v =>
                    if v ∈ cfg.committee ∧ qa v = true ∧ cfg.faulty v = false then
                      (stepEpochLatch (st.latches v) ep mu).getD (st.latches v)
                    else st.latches v
                  latchLogs := fun v =>
                    if v ∈ cfg.committee ∧ qa v = true ∧ cfg.faulty v = false then
                      st.latchLogs v ++ [(ep, mu)]
                    else st.latchLogs v
                  signedHistory := st.signedHistory ++ [(ep, mu, msg, sig)] }
              have hNextLogs : ∀ v ∈ cfg.committee, cfg.faulty v = false →
                  ValidNodeLatchTrace initEpochLatch (stStepped.latchLogs v) (stStepped.latches v) := by
                intro v hvMem hvHonest
                dsimp only [stStepped]
                by_cases hQa : qa v = true
                · have hCond : v ∈ cfg.committee ∧ qa v = true ∧ cfg.faulty v = false := ⟨hvMem, hQa, hvHonest⟩
                  simp only [hCond, and_self, ↓reduceIte]
                  have hvInFilt : v ∈ cfg.committee.filter (fun u => qa u && !(cfg.faulty u)) := by
                    rw [List.mem_filter]; simp [hvMem, hQa, hvHonest]
                  obtain ⟨sNextV, hsNextV⟩ := Option.isSome_iff_exists.mp (hAllProp v hvInFilt)
                  rw [hsNextV]; dsimp only [Option.getD]
                  exact validNodeLatchTrace_snoc (st.latchLogs v) initEpochLatch (st.latches v) sNextV ep mu
                    (hLogs v hvMem hvHonest) hsNextV
                · have hNotCond : ¬ (v ∈ cfg.committee ∧ qa v = true ∧ cfg.faulty v = false) :=
                    fun hc => hQa hc.2.1
                  simp only [hNotCond, ↓reduceIte]
                  exact hLogs v hvMem hvHonest
              have hNextHist : ∀ ep' mu' msg' sig',
                  (ep', mu', msg', sig') ∈ stStepped.signedHistory →
                  verifyPqHashSig cfg.engine.suite cfg.params pk msg' sig' = true ∧
                  ∃ qa' : NodeId → Bool,
                    2 * cfg.maxFaulty + 1 ≤ (cfg.committee.filter qa').length ∧
                    ∀ v ∈ cfg.committee, qa' v = true → cfg.faulty v = false →
                      (ep', mu') ∈ stStepped.latchLogs v := by
                intro ep' mu' msg' sig' hMemApp
                dsimp only [stStepped] at hMemApp ⊢
                rw [List.mem_append] at hMemApp
                rcases hMemApp with hOld | hNew
                · obtain ⟨hVOld, qaOld, hQOld, hMemOld⟩ := hHist ep' mu' msg' sig' hOld
                  refine ⟨hVOld, qaOld, hQOld, fun v hvM hQaO hvH => ?_⟩
                  have hIn := hMemOld v hvM hQaO hvH
                  split
                  · exact List.mem_append_left _ hIn
                  · exact hIn
                · simp only [List.mem_singleton, Prod.mk.injEq] at hNew
                  rcases hNew with ⟨rfl, rfl, rfl, rfl⟩
                  refine ⟨hVerSig, qa, by omega, fun v hvM hQaV hvH => ?_⟩
                  have hCond : v ∈ cfg.committee ∧ qa v = true ∧ cfg.faulty v = false := ⟨hvM, hQaV, hvH⟩
                  simp only [hCond, and_self, ↓reduceIte]
                  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              exact custodyTrace_preserves_invariants cfg hSize hFaulty hRecon rest stStepped stFinal
                hNextLogs hNextHist hRest

/-- **Apex Multi-Turn Custody MPC Protocol & Hardware Safety (`pq_threshold_custody_multi_turn_safe`)**:
    Across ANY valid multi-turn execution `ValidPqCustodyMpcTrace` from genesis latch state, establishes:
    (1) stateful `leanSig` anti-double-sign (`ep₁ = ep₂ → mu₁ = mu₂`), (2) standard `verifyPqHashSig = true`,
    (3) transitive `GrainPowerbox` membrane revocation blocking, (4) seL4 Microkit private-frame TOCTOU immunity,
    and (5) dual-rail glitch quarantine + 0-MI TEMPEST masking! -/
theorem pq_threshold_custody_multi_turn_safe
    (cfg : CustodyMpcSysConfig) (initHost : PowerboxHost)
    (turns : List CustodyMpcTurn) (stFinal : CustodyMpcSysState)
    (hSize : cfg.committee.length = 3 * cfg.maxFaulty + 1)
    (hFaulty : (cfg.committee.filter cfg.faulty).length ≤ cfg.maxFaulty)
    (hRecon : cfg.sharedBundle.reconstructSk = cfg.logicalSk)
    (hTrace : ValidPqCustodyMpcTrace cfg
      { powerbox := initHost, latches := fun _ => initEpochLatch, latchLogs := fun _ => [], signedHistory := [] }
      turns stFinal)
    {k₀ k₁ : KState} {icfg : IngressCfg} {da₀ : Nat} {ring disp : ByteArray} {mid : List KEvent}
    (hU : VUnique k₀.maps)
    (hP₀ : translate k₀.maps (.cpu icfg.vpd) icfg.privV true = some da₀)
    (hInv : PrivInv k₀ icfg.vpd (da₀ / pageSize) k₁)
    (hRing : readVia k₁ icfg.vpd icfg.sharedV icfg.len = some ring)
    (hCopy : (translate k₁.maps (.cpu icfg.vpd) icfg.privV true).isSome = true)
    (hAdv : ∀ ev ∈ mid, ev.actor ≠ some icfg.vpd)
    (hD : readVia (runK (ingressCopy icfg k₁) mid) icfg.vpd (dispatchVaddr icfg) icfg.len = some disp)
    (winSpec : RailClockWindowSpec) (imem : InstrMem)
    (obs : RadiatedEmObservation)
    (kMask : Nat) (envSeq : Nat → CoupledPcbPairSpec × HighSpeedEdgeSpec × Bool)
    (s0 s1 : List Bool) (hs0 : s0.length = kMask) (hs1 : s1.length = kMask)
    (distinguisher : List RadiatedEmObservation → CanonicalRat) :
    (∀ ep mu₁ msg₁ sig₁ mu₂ msg₂ sig₂,
      (ep, mu₁, msg₁, sig₁) ∈ stFinal.signedHistory →
      (ep, mu₂, msg₂, sig₂) ∈ stFinal.signedHistory →
      mu₁ = mu₂) ∧
    (∀ ep mu msg sig,
      (ep, mu, msg, sig) ∈ stFinal.signedHistory →
      verifyPqHashSig cfg.engine.suite cfg.params
        (derivePublicKey cfg.engine.suite cfg.params cfg.logicalSk) msg sig = true) ∧
    (∀ cap m, m ∈ cap.membranes → stFinal.powerbox.revokedMembranes.contains m = true →
      checkCustodySignAuth stFinal.powerbox cap cfg.needRights = false) ∧
    (disp = ring ∧ PrivInv k₀ icfg.vpd (da₀ / pageSize) (runK (ingressCopy icfg k₁) mid)) ∧
    ((∀ (fault : GlitchCycleFault) (cpuSt : GlitchProtectedCpuState),
        let cpuSt' := stepGlitchProtectedCpu winSpec imem (.clockCycle fault) cpuSt
        (cpuSt'.mode = .glitchQuarantine ∧ externalActuationOut cpuSt' = 0#64 ∧ externalKeyBusOut cpuSt' = 0#64) ∨
        (cpuSt'.isa = cpuSt.isa) ∨ (cpuSt'.isa = stepIsa imem cpuSt.isa)) ∧
     (((if observeMaskedEm (envSeq 0).1 (envSeq 0).2.1 (envSeq 0).2.2 false false = obs then (1 : CanonicalRat) else 0) +
       (if observeMaskedEm (envSeq 0).1 (envSeq 0).2.1 (envSeq 0).2.2 false true  = obs then 1 else 0)) / 2 =
      ((if observeMaskedEm (envSeq 0).1 (envSeq 0).2.1 (envSeq 0).2.2 true  false = obs then (1 : CanonicalRat) else 0) +
       (if observeMaskedEm (envSeq 0).1 (envSeq 0).2.1 (envSeq 0).2.2 true  true  = obs then 1 else 0)) / 2) ∧
     uniformMaskExpectation kMask (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s0 m)) =
     uniformMaskExpectation kMask (fun m => distinguisher (observeMaskedEmTrace envSeq 0 s1 m))) := by
  let stInit : CustodyMpcSysState :=
    { powerbox := initHost, latches := fun _ => initEpochLatch, latchLogs := fun _ => [], signedHistory := [] }
  obtain ⟨hFinalLogs, hFinalHist⟩ := custodyTrace_preserves_invariants cfg hSize hFaulty hRecon
    turns stInit stFinal (fun _ _ _ => rfl) (fun _ _ _ _ h => by cases h) hTrace
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ep mu₁ msg₁ sig₁ mu₂ msg₂ sig₂ hMem1 hMem2
    obtain ⟨_, qa1, hQ1, hLog1⟩ := hFinalHist ep mu₁ msg₁ sig₁ hMem1
    obtain ⟨_, qa2, hQ2, hLog2⟩ := hFinalHist ep mu₂ msg₂ sig₂ hMem2
    exact leanSig_quorum_never_double_signs
      cfg.committee cfg.maxFaulty qa1 qa2 cfg.faulty
      stFinal.latchLogs stFinal.latches
      hSize hQ1 hQ2 hFaulty hFinalLogs ep mu₁ mu₂ hLog1 hLog2
  · intro ep mu msg sig hMem
    exact (hFinalHist ep mu msg sig hMem).1
  · intro cap m hm hRev
    exact revoked_membrane_blocks_threshold_sign stFinal.powerbox cap cfg.needRights m hm hRev
  · exact copy_into_private_pd_frame_before_verify hU hP₀ hInv hRing hCopy mid hAdv hD
  · exact ⟨(power_glitch_immunity_multi_turn_sound winSpec imem).1,
           masked_dualRail_exact_mutual_info_zero (envSeq 0).1 (envSeq 0).2.1 (envSeq 0).2.2 obs kMask envSeq s0 s1 hs0 hs1 distinguisher⟩

end Obend.Crypto.ThresholdHashMpc
end
