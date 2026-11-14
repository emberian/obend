module
public import Obend.Polis.CapTP
public import Obend.Polis.VerifiableCredentials
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Sumcheck

public section
namespace Obend.Polis.HouyhnhnmTurn
open Obend.Crypto Obend.Vault.Mandate Obend.Polis.CapTP
open Obend.Polis.VerifiableCredentials
open Obend.Digest.Cshake256 Obend.Digest.HashBytes

structure FullPinnedPublicInputs where
  circuitDescDigest : ByteArray
  actorVkDigest : ByteArray
  preStateRoot : ByteArray
  postStateRoot : ByteArray
  capRoot : ByteArray
  revokedRoot : ByteArray
  height : Nat
  turnHash : ByteArray
  deriving DecidableEq

def wellFormedInputs (p : FullPinnedPublicInputs) : Bool :=
  decide (p.circuitDescDigest.size = 32 ∧ p.actorVkDigest.size = 32 ∧
    p.preStateRoot.size = 32 ∧ p.postStateRoot.size = 32 ∧ p.capRoot.size = 32 ∧
    p.revokedRoot.size = 32 ∧ p.turnHash.size = 32)

def natBytes (n : Nat) : ByteArray :=
  Obend.Digest.Cshake256.Native.bytesOfList (leb128 n)

theorem natBytes_injective (a b : Nat) (h : natBytes a = natBytes b) : a = b := by
  have hh := congrArg (fun x : ByteArray => x.data.toList) h
  simp only [natBytes, Obend.Digest.Cshake256.Native.bytesOfList_toList] at hh
  exact (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hh)).1

/-- Three nested frames encode exactly eight fields. The empty ninth slot is reserved,
not an optional input. No hash-injectivity assumption is used. -/
@[expose] def encodePublicInputs (p : FullPinnedPublicInputs) : ByteArray :=
  encodeFrame (encodeFrame p.circuitDescDigest p.actorVkDigest p.preStateRoot)
    (encodeFrame p.postStateRoot p.capRoot p.revokedRoot)
    (encodeFrame (natBytes p.height) p.turnHash ByteArray.empty)

theorem encodePublicInputs_injective (p q : FullPinnedPublicInputs)
    (h : encodePublicInputs p = encodePublicInputs q) : p = q := by
  obtain ⟨ha, hb, hc⟩ := encodeFrame_injective h
  obtain ⟨ha1, ha2, ha3⟩ := encodeFrame_injective ha
  obtain ⟨hb1, hb2, hb3⟩ := encodeFrame_injective hb
  obtain ⟨hc1, hc2, _⟩ := encodeFrame_injective hc
  have hn := natBytes_injective _ _ hc1
  cases p; cases q; simp_all

def relationPrefix (p : FullPinnedPublicInputs) : ByteArray :=
  canonicalPrefix "obend.sovereign-turn.v1" p.circuitDescDigest (encodePublicInputs p)

theorem fenzi_pi_injective (p q : FullPinnedPublicInputs)
    (h : relationPrefix p = relationPrefix q) : p = q :=
  encodePublicInputs_injective p q (bindRelation_injective_prefix h).2.2

def turnTranscript (p : FullPinnedPublicInputs) : Transcript .relationBound :=
  bindRelation "obend.sovereign-turn.v1" p.circuitDescDigest (encodePublicInputs p)
    (Transcript.newUnseeded ByteArray.empty)

@[expose] def emptyRevokedRoot32 : ByteArray := ⟨Array.replicate 32 0⟩
@[expose] def liveRevokedRoot (root : ByteArray) : Bool :=
  decide (root.size = 32 ∧ root ≠ emptyRevokedRoot32)

theorem empty_revoked_root_refused : ∀ root, root = emptyRevokedRoot32 → liveRevokedRoot root = false := by
  intro root h; simp [liveRevokedRoot, h]

structure RowConstraintTrace where
  residuals : Array Int

@[expose] def checkAllRowsNonVacuous (t : RowConstraintTrace) : Bool :=
  !t.residuals.isEmpty && t.residuals.all (· == 0)

/-- The legacy mask erases exactly the final-row obligation. -/
def legacyLastRowGate (isLast : Bool) (gate : Int) : Int :=
  (if isLast then 0 else 1) * gate

theorem legacy_last_row_vacuous (gate : Int) : legacyLastRowGate true gate = 0 := by
  simp [legacyLastRowGate]

theorem lastRowGateGuard (t : RowConstraintTrace) (h : checkAllRowsNonVacuous t = true)
    (i : Nat) (hi : i < t.residuals.size) : t.residuals[i] = 0 := by
  have ha : t.residuals.all (· == 0) = true := (Bool.and_eq_true _ _).mp h |>.2
  have := (Array.all_eq_true.mp ha) i hi
  simpa using this

structure EffectCustom where
  actorId : Nat
  actorVkDigest : ByteArray
  innerStatementDigest : ByteArray
  proof : ByteArray

structure InvocationWithProvenance where
  capabilityIndex : Nat
  invocation : Invocation
  credNul : List UInt64
  chanNul : UInt64

@[expose] def provenanceLive (revoked : SortedU64Set) (boundPrefix : List UInt64) (channel : UInt64) : Bool :=
  boundPrefix.all (fun k => !revoked.contains k) && !revoked.contains channel

theorem ancestor_credNul_revokes_delegation_cone (revoked : SortedU64Set)
    (ancestor channel : UInt64) (boundPrefix : List UInt64) (h : ancestor ∈ boundPrefix) :
    provenanceLive (revoked.insert ancestor) boundPrefix channel = false := by
  have hm : (revoked.insert ancestor).contains ancestor = true :=
    ((revoked.insert ancestor).contains_eq_spec _).mpr (by simp)
  have hf : boundPrefix.all (fun k => !(revoked.insert ancestor).contains k) = false := by
    cases ha : boundPrefix.all (fun k => !(revoked.insert ancestor).contains k)
    · rfl
    · have := List.all_eq_true.mp ha ancestor h
      simp [hm] at this
  simp [provenanceLive, hf]

structure CellState where
  balances : Array Int
  capRoot : ByteArray
  revokedRoot : ByteArray
  actorVkDigest : ByteArray
  actorId : Nat
  revoked : SortedU64Set
  capabilities : Array Mandate

structure StructuredTurn where
  deltas : Array Int
  invocations : Array InvocationWithProvenance
  effects : Array EffectCustom
  rows : RowConstraintTrace

inductive WitnessMode where
  | symbolic
  | collapse

abbrev InnerVerifier := ByteArray → ByteArray → ByteArray → Bool

@[expose] def nextBalances (s : CellState) (t : StructuredTurn) : Array Int :=
  Array.zipWith (· + ·) s.balances t.deltas

/-- Hash-free admission. All accounts here are non-issuers; minting requires a
separate issuance relation rather than bypassing this conservation equation. -/
@[expose] def execTurnSymbolic (verifyInner : InnerVerifier) (s : CellState) (t : StructuredTurn) : Bool :=
  decide (t.deltas.size = s.balances.size) && decide (t.deltas.toList.sum = 0) &&
  (nextBalances s t).all (fun b => decide (0 ≤ b)) &&
  t.invocations.all (fun i => match s.capabilities[i.capabilityIndex]? with
    | none => false
    | some m => checkInvocation m i.invocation && provenanceLive s.revoked i.credNul i.chanNul) &&
  t.effects.all (fun e => decide (e.actorId = s.actorId ∧ e.actorVkDigest = s.actorVkDigest) &&
    verifyInner e.actorVkDigest e.innerStatementDigest e.proof) &&
  decide (s.actorVkDigest.size = 32 ∧ s.capRoot.size = 32) &&
  liveRevokedRoot s.revokedRoot && checkAllRowsNonVacuous t.rows

/-- List semantics of the runtime cell-balance update. -/
def balanceUpdateSpec (balances deltas : List Int) : List Int :=
  List.zipWith (· + ·) balances deltas

theorem balanceUpdate_refines (s : CellState) (t : StructuredTurn) :
    (nextBalances s t).toList = balanceUpdateSpec s.balances.toList t.deltas.toList := by
  simp [nextBalances, balanceUpdateSpec]

theorem sum_balanceUpdate (xs ys : List Int) (h : xs.length = ys.length) :
    (balanceUpdateSpec xs ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [balanceUpdateSpec]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using h
      have hi := ih ys ht
      simp only [balanceUpdateSpec, List.zipWith_cons_cons, List.sum_cons] at hi ⊢
      omega

/-- Conservation is about the resulting balances, not just a caller's claim that
its delta vector is balanced. Length equality prevents zip truncation. -/
theorem symbolic_conserves_balances (v : InnerVerifier) (s : CellState) (t : StructuredTurn)
    (h : execTurnSymbolic v s t = true) : (nextBalances s t).toList.sum = s.balances.toList.sum := by
  simp only [execTurnSymbolic, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hlen, hsum⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  rw [balanceUpdate_refines, sum_balanceUpdate _ _ (by simpa using hlen.symm), hsum, Int.add_zero]

theorem capability_lookup_eq_spec (s : CellState) (index : Nat) :
    s.capabilities[index]? = s.capabilities.toList[index]? := by simp


def revokedCommitment (revoked : SortedU64Set) : ByteArray :=
  cshake32ByteArray "obend.revoked-set.v1".toUTF8.data.toList
    (CapTP.encodeNats (revoked.data.toList.map UInt64.toNat)).data.toList

/-- Successful invocations consume their channel nullifier and leaf credential nullifier.
Ancestor credentials remain usable by sibling delegations. -/
def spendInvocation (revoked : SortedU64Set) (i : InvocationWithProvenance) : SortedU64Set :=
  let withChannel := revoked.insert i.chanNul
  match i.credNul.getLast? with
  | none => withChannel
  | some leaf => withChannel.insert leaf

def spendInvocations : SortedU64Set → List InvocationWithProvenance → SortedU64Set
  | revoked, [] => revoked
  | revoked, i :: rest => spendInvocations (spendInvocation revoked i) rest

def nextState (s : CellState) (t : StructuredTurn) : CellState :=
  let revoked := spendInvocations s.revoked t.invocations.toList
  { s with
    balances := nextBalances s t
    revoked := revoked
    revokedRoot := revokedCommitment revoked }

theorem spendInvocation_monotone (r : SortedU64Set) (i : InvocationWithProvenance) (k : UInt64)
    (h : r.spec k) : (spendInvocation r i).spec k := by
  unfold spendInvocation
  cases i.credNul.getLast? <;> simp [h]

theorem spendInvocation_channel (r : SortedU64Set) (i : InvocationWithProvenance) :
    (spendInvocation r i).spec i.chanNul := by
  unfold spendInvocation
  cases i.credNul.getLast? <;> simp

theorem spendInvocations_monotone (is : List InvocationWithProvenance) (r : SortedU64Set) (k : UInt64)
    (h : r.spec k) : (spendInvocations r is).spec k := by
  induction is generalizing r with
  | nil => exact h
  | cons i is ih => exact ih _ (spendInvocation_monotone r i k h)

theorem spendInvocations_channel (is : List InvocationWithProvenance) (r : SortedU64Set)
    (i : InvocationWithProvenance) (h : i ∈ is) : (spendInvocations r is).spec i.chanNul := by
  induction is generalizing r with
  | nil => cases h
  | cons j is ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact spendInvocations_monotone is _ _ (spendInvocation_channel r i)
    · exact ih _ h

theorem nextState_refuses_replay (s : CellState) (t : StructuredTurn) (i : InvocationWithProvenance)
    (h : i ∈ t.invocations.toList) : provenanceLive (nextState s t).revoked i.credNul i.chanNul = false := by
  have hc := ((nextState s t).revoked.contains_eq_spec i.chanNul).mpr (spendInvocations_channel _ _ i h)
  simp [provenanceLive, hc]

/-- A backend supplies canonical state/turn commitments and a proof verifier. The
soundness and completeness fields are explicit obligations, not custom axioms or
Boolean claims in a bundle. This interface does not implement a SNARK. -/
structure TurnCommitments where
  stateRoot : CellState → ByteArray
  turnHash : StructuredTurn → ByteArray
  circuitDigest : ByteArray
  capabilityRoot : Array Mandate → ByteArray
  stateRoot_size : ∀ s, (stateRoot s).size = 32
  turnHash_size : ∀ t, (turnHash t).size = 32
  circuitDigest_size : circuitDigest.size = 32

/-- Live stores are framed outside the caller's state encoder, so even a balances-only
encoder cannot omit spent nullifiers from the public pre/post state roots. -/
def stateRootBytes (c : TurnCommitments) (s : CellState) : ByteArray :=
  encodeFrame (c.stateRoot s) (revokedCommitment s.revoked) (c.capabilityRoot s.capabilities)

def committedStateRoot (c : TurnCommitments) (s : CellState) : ByteArray :=
  cshake32ByteArray "OBEND.POLIS.TURN_STATE/v1".toUTF8.data.toList (stateRootBytes c s).data.toList

theorem committedStateRoot_size (c : TurnCommitments) (s : CellState) :
    (committedStateRoot c s).size = 32 := cshake32ByteArray_size _ _

theorem committedStateRoot_revoked_binding (c : TurnCommitments) (s t : CellState)
    (h : committedStateRoot c s = committedStateRoot c t) :
    revokedCommitment s.revoked = revokedCommitment t.revoked ∨
      CollisionAmong (cshake256Bytes "OBEND.POLIS.TURN_STATE/v1".toUTF8.data.toList)
        (fun x => x = (stateRootBytes c s).data.toList ∨ x = (stateRootBytes c t).data.toList) := by
  rcases cshake32_binds "OBEND.POLIS.TURN_STATE/v1".toUTF8.data.toList h with he | hc
  · exact .inl (encodeFrame_injective (byteArray_eq_of_toList_eq he)).2.1
  · exact .inr hc

def materializeInputs (c : TurnCommitments) (s : CellState) (t : StructuredTurn)
    (height : Nat) : FullPinnedPublicInputs where
  circuitDescDigest := c.circuitDigest
  actorVkDigest := s.actorVkDigest
  preStateRoot := committedStateRoot c s
  postStateRoot := committedStateRoot c (nextState s t)
  capRoot := s.capRoot
  revokedRoot := s.revokedRoot
  height := height
  turnHash := c.turnHash t

/-- Cached roots must be tied to the live stores before a turn crosses a boundary. -/
@[expose] def RootBindings (c : TurnCommitments) (s : CellState) : Prop :=
  s.revokedRoot = revokedCommitment s.revoked ∧ s.capRoot = c.capabilityRoot s.capabilities

instance (c : TurnCommitments) (s : CellState) : Decidable (RootBindings c s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem symbolic_inputs_wellformed (c : TurnCommitments) (v : InnerVerifier)
    (s : CellState) (t : StructuredTurn) (height : Nat) (h : execTurnSymbolic v s t = true) :
    wellFormedInputs (materializeInputs c s t height) = true := by
  have hs := (Bool.and_eq_true _ _).mp h |>.1 |> (Bool.and_eq_true _ _).mp
  have hr := hs.2
  have hc := (Bool.and_eq_true _ _).mp hs.1 |>.2
  simp only [liveRevokedRoot, decide_eq_true_eq] at hr
  simp only [decide_eq_true_eq] at hc
  unfold wellFormedInputs
  apply decide_eq_true
  exact ⟨c.circuitDigest_size, hc.1, committedStateRoot_size c _, committedStateRoot_size c _,
    hc.2, hr.1, c.turnHash_size _⟩

def TurnRelation (c : TurnCommitments) (v : InnerVerifier) (p : FullPinnedPublicInputs) : Prop :=
  ∃ s t, execTurnSymbolic v s t = true ∧ RootBindings c s ∧
    materializeInputs c s t p.height = p

def turnChallengeTranscript (p : FullPinnedPublicInputs) : Transcript .instanceBound :=
  (bindInstance (encodePublicInputs p) (turnTranscript p)).transcript

structure TurnProofSystem (c : TurnCommitments) (v : InnerVerifier) where
  Receipt : Type
  verify : FullPinnedPublicInputs → ByteArray → Receipt → Bool
  prove : (s : CellState) → (t : StructuredTurn) → (height : Nat) →
    execTurnSymbolic v s t = true → RootBindings c s → Receipt
  sound : ∀ p challenge receipt, verify p challenge receipt = true →
    TurnRelation c v p
  complete : ∀ s t height hs hr,
    verify (materializeInputs c s t height)
      (squeezeChallenge256 (turnChallengeTranscript (materializeInputs c s t height))).1.val
      (prove s t height hs hr) = true

/-- A transparent opening carries the state and turn as data, plus a genuine dual PCS
opening. It does not assume a proof of TurnRelation as part of the receipt carrier. -/
structure DualPcsTurnReceipt where
  state : CellState
  turn : StructuredTurn
  rounds : List (RoundPoly Goldilocks)
  opening : CanopyOpeningProof × AjtaiOpeningProof

def turnInputTable (p : FullPinnedPublicInputs) : List Goldilocks :=
  (cshake32ByteArray "OBEND.POLIS.TURN_TABLE/v1".toUTF8.data.toList
    (encodePublicInputs p).data.toList).data.toList.map (fun b => Goldilocks.ofNat b.toNat)

attribute [local irreducible] cshake32ByteArray honestBoundSumcheckProver verifyDualSumcheckPIOP

theorem turnInputTable_length (p : FullPinnedPublicInputs) : (turnInputTable p).length = 2 ^ 5 := by
  simp only [turnInputTable, List.length_map, Array.length_toList]
  exact cshake32ByteArray_size _ _

attribute [local irreducible] turnInputTable

def verifyDualPcsTurn (c : TurnCommitments) (v : InnerVerifier) (p : FullPinnedPublicInputs)
    (challenge : ByteArray) (r : DualPcsTurnReceipt) : Bool :=
  execTurnSymbolic v r.state r.turn && decide (RootBindings c r.state) &&
  decide (encodePublicInputs (materializeInputs c r.state r.turn p.height) = encodePublicInputs p) &&
  decide (challenge = (squeezeChallenge256 (turnChallengeTranscript p)).1.val) &&
  let pcs := DualPCS (R := Goldilocks) (canopyMerklePCS deployedCanopyHash32)
    (ajtaiLatticePCS (inhabitedAjtaiParams 5))
  verifyDualSumcheckPIOP (canopyMerklePCS deployedCanopyHash32)
    (ajtaiLatticePCS (inhabitedAjtaiParams 5)) ((), ()) 1 5 (pcs.commit ((), ()) 5 (turnInputTable p))
    (hypercubeSum 5 (turnInputTable p)) r.rounds r.opening (turnTranscript p)

def proveDualPcsTurn (c : TurnCommitments) (s : CellState) (t : StructuredTurn) (height : Nat) : DualPcsTurnReceipt :=
  let p := materializeInputs c s t height
  let tbl := turnInputTable p
  let pcs := DualPCS (R := Goldilocks) (canopyMerklePCS deployedCanopyHash32)
    (ajtaiLatticePCS (inhabitedAjtaiParams 5))
  let sc := honestBoundSumcheckProver (R := Goldilocks) (pcs.commit ((), ()) 5 tbl) 5 tbl (turnTranscript p)
  ⟨s, t, sc.1, (pcs.openEval ((), ()) 5 tbl sc.2.1 sc.2.2).1⟩

/-- Concrete, inhabited Dual-PCS realization. Its transparent verifier rechecks the
relation; replacing that work with a succinct arithmetization is a separate optimization. -/
def dualPcsTurnProofSystem (c : TurnCommitments) (v : InnerVerifier) : TurnProofSystem c v where
  Receipt := DualPcsTurnReceipt
  verify := verifyDualPcsTurn c v
  prove s t height _ _ := proveDualPcsTurn c s t height
  sound p challenge r h := by
    simp only [verifyDualPcsTurn, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨r.state, r.turn, h.1.1.1.1, h.1.1.1.2,
      encodePublicInputs_injective _ _ h.1.1.2⟩
  complete s t height hs hr := by
    have h := verifyDualSumcheckPIOP_completeness (canopyMerklePCS deployedCanopyHash32)
      (ajtaiLatticePCS (inhabitedAjtaiParams 5)) ((), ()) (Nat.le_refl 1) 5
      (turnInputTable (materializeInputs c s t height))
      (turnTranscript (materializeInputs c s t height))
      ⟨trivial, (inhabitedAjtaiParams_sisHard 5).1⟩ (turnInputTable_length _)
    simpa only [verifyDualPcsTurn, proveDualPcsTurn, hs, hr,
      show (materializeInputs c s t height).height = height from rfl,
      eq_self, decide_true, Bool.true_and] using h

theorem dualPcsTurnProofSystem_inhabited (c : TurnCommitments) (v : InnerVerifier) :
    Nonempty (TurnProofSystem c v) := ⟨dualPcsTurnProofSystem c v⟩

structure SovereignTurnBundle {c : TurnCommitments} {v : InnerVerifier} (ps : TurnProofSystem c v) where
  publicInputs : FullPinnedPublicInputs
  boundPrefix : ByteArray
  receipt : ps.Receipt

def verifyCipherclerkBundle {c : TurnCommitments} {v : InnerVerifier}
    (ps : TurnProofSystem c v) (b : SovereignTurnBundle ps) : Bool :=
  decide (b.boundPrefix = relationPrefix b.publicInputs) && wellFormedInputs b.publicInputs &&
  liveRevokedRoot b.publicInputs.revokedRoot &&
  TurnProofSystem.verify (c := c) (v := v) ps b.publicInputs (squeezeChallenge256 (turnChallengeTranscript b.publicInputs)).1.val b.receipt

def collapseTurn {c : TurnCommitments} {v : InnerVerifier} (ps : TurnProofSystem c v)
    (s : CellState) (t : StructuredTurn) (height : Nat)
    (hs : execTurnSymbolic v s t = true) (hr : RootBindings c s) :
    SovereignTurnBundle ps :=
  let p := materializeInputs c s t height
  ⟨p, relationPrefix p, ps.prove s t height hs hr⟩

theorem symbolic_collapse_refines {c : TurnCommitments} {v : InnerVerifier}
    (ps : TurnProofSystem c v) (s : CellState) (t : StructuredTurn) (height : Nat)
    (hs : execTurnSymbolic v s t = true) (hr : RootBindings c s) :
    verifyCipherclerkBundle ps (collapseTurn ps s t height hs hr) = true ∧
    (collapseTurn ps s t height hs hr).publicInputs.preStateRoot = committedStateRoot c s ∧
    (collapseTurn ps s t height hs hr).publicInputs.postStateRoot =
      committedStateRoot c (nextState s t) := by
  have hl : liveRevokedRoot s.revokedRoot = true := (Bool.and_eq_true _ _).mp hs |>.1 |> (Bool.and_eq_true _ _).mp |>.2
  refine ⟨?_, rfl, rfl⟩
  simp only [verifyCipherclerkBundle, collapseTurn, decide_true, Bool.true_and]
  rw [ps.complete]
  have hw := symbolic_inputs_wellformed c v s t height hs
  have hl' : liveRevokedRoot (materializeInputs c s t height).revokedRoot = true := hl
  rw [hw, hl']
  rfl

theorem cipherclerk_zero_reexec_sound {c : TurnCommitments} {v : InnerVerifier}
    (ps : TurnProofSystem c v) (b : SovereignTurnBundle ps)
    (h : verifyCipherclerkBundle ps b = true) :
    b.boundPrefix = relationPrefix b.publicInputs ∧ wellFormedInputs b.publicInputs = true ∧
    b.publicInputs.revokedRoot.size = 32 ∧ b.publicInputs.revokedRoot ≠ emptyRevokedRoot32 ∧
    TurnRelation c v b.publicInputs := by
  simp only [verifyCipherclerkBundle, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl := h.1.2
  simp only [liveRevokedRoot, decide_eq_true_eq] at hl
  exact ⟨h.1.1.1, h.1.1.2, hl.1, hl.2, ps.sound _ _ _ h.2⟩

/-- Validity of a collapsed statement entails the actual final constraint, not a
prover-supplied last-row flag. -/
theorem relation_last_row {c : TurnCommitments} {v : InnerVerifier} (p : FullPinnedPublicInputs)
    (h : TurnRelation c v p) : ∃ s t, materializeInputs c s t p.height = p ∧
      ∀ i (hi : i < t.rows.residuals.size), t.rows.residuals[i] = 0 := by
  obtain ⟨s, t, hs, _, hp⟩ := h
  exact ⟨s, t, hp, lastRowGateGuard _ ((Bool.and_eq_true _ _).mp hs).2⟩

structure ReversibleTurn where
  forwardDeltas : Array Int
  deriving DecidableEq

def ReversibleTurn.invert (t : ReversibleTurn) : ReversibleTurn :=
  ⟨t.forwardDeltas.map (- ·)⟩
abbrev BalanceState := Nat → Int
def applyTurn (t : ReversibleTurn) (s : BalanceState) : BalanceState :=
  fun i => s i + t.forwardDeltas[i]?.getD 0

theorem invert_cancel (t : ReversibleTurn) (s : BalanceState) :
    applyTurn t.invert (applyTurn t s) = s := by
  funext i
  simp only [applyTurn, ReversibleTurn.invert, Array.getElem?_map]
  cases h : t.forwardDeltas[i]? <;> simp <;> omega

theorem invert_involutive (t : ReversibleTurn) : t.invert.invert = t := by
  cases t
  simp [ReversibleTurn.invert, Array.map_map, Function.comp_def]

/-- Forks retain a shared immutable backing array and boundPrefix boundary. New turns go
into the branch-local suffix; no state snapshot is stored or copied. -/
structure ReversibleHistory where
  backing : Array ReversibleTurn
  prefixLength : Nat
  prefixBound : prefixLength ≤ backing.size
  localTurns : Array ReversibleTurn

def historySpec (h : ReversibleHistory) : List ReversibleTurn :=
  h.backing.toList.take h.prefixLength ++ h.localTurns.toList

def forkAt (h : ReversibleHistory) (k : Nat) (hk : k ≤ h.prefixLength) : ReversibleHistory :=
  ⟨h.backing, k, Nat.le_trans hk h.prefixBound, #[]⟩

theorem prefixSlice_eq (h : ReversibleHistory) (k : Nat) (hk : k ≤ h.prefixLength) :
    (forkAt h k hk).backing = h.backing := by
  unfold forkAt; rfl

theorem forkAt_preserves_causal_prefix (h : ReversibleHistory) (k : Nat) (hk : k ≤ h.prefixLength) :
    historySpec (forkAt h k hk) = (historySpec h).take k := by
  simp only [historySpec, forkAt, Array.toList_empty, List.append_nil]
  rw [List.take_append_of_le_length]
  · simp [List.take_take, Nat.min_eq_left hk]
  · simp only [List.length_take, Array.length_toList]
    have := h.prefixBound
    omega

def appendTurn (h : ReversibleHistory) (t : ReversibleTurn) : ReversibleHistory :=
  { h with localTurns := h.localTurns.push t }

theorem appendTurn_refines (h : ReversibleHistory) (t : ReversibleTurn) :
    historySpec (appendTurn h t) = historySpec h ++ [t] := by
  simp [historySpec, appendTurn, List.append_assoc]


def applyHistory (turns : List ReversibleTurn) (s : BalanceState) : BalanceState :=
  turns.foldl (fun s t => applyTurn t s) s

def applyHistoryExec (turns : Array ReversibleTurn) (s : BalanceState) : BalanceState :=
  turns.foldl (fun s t => applyTurn t s) s

theorem history_exec_eq_spec (turns : Array ReversibleTurn) (s : BalanceState) :
    applyHistoryExec turns s = applyHistory turns.toList s := by
  simp [applyHistoryExec, applyHistory, Array.foldl_toList]


def rollback (turns : List ReversibleTurn) (s : BalanceState) : BalanceState :=
  applyHistory (turns.reverse.map ReversibleTurn.invert) s

theorem rollbackTo_recovers_checkpoint (suffix : List ReversibleTurn) (checkpoint : BalanceState) :
    rollback suffix (applyHistory suffix checkpoint) = checkpoint := by
  induction suffix generalizing checkpoint with
  | nil => rfl
  | cons t ts ih =>
    simp only [rollback, applyHistory, List.foldl_cons, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_nil]
    have hh := ih (applyTurn t checkpoint)
    unfold rollback applyHistory at hh
    rw [hh]
    exact invert_cancel t checkpoint

/-! ## Sessions: many turns over many capability handles

A turn admitted by `execTurnSymbolic` is checked against one cell state. A session carries that
state across turns: channel nullifiers are spent, credential nullifiers are revoked, each
invocation debits the remaining budget of its handle, and a turn may delegate a child handle.
`stepHouyhnhnmSession` is one turn; `runHouyhnhnmSession` folds it over a list. The theorems
below are about arbitrary lists of turns. -/

/-- What an admitted turn checked, clause by clause. -/
theorem execTurnSymbolic_iff (v : InnerVerifier) (s : CellState) (t : StructuredTurn) :
    execTurnSymbolic v s t = true ↔
      (t.deltas.size = s.balances.size ∧ t.deltas.toList.sum = 0) ∧
      (∀ b ∈ nextBalances s t, 0 ≤ b) ∧
      (∀ i ∈ t.invocations, ∃ m, s.capabilities[i.capabilityIndex]? = some m ∧
        checkInvocation m i.invocation = true ∧
        provenanceLive s.revoked i.credNul i.chanNul = true) ∧
      (∀ e ∈ t.effects, (e.actorId = s.actorId ∧ e.actorVkDigest = s.actorVkDigest) ∧
        v e.actorVkDigest e.innerStatementDigest e.proof = true) ∧
      (s.actorVkDigest.size = 32 ∧ s.capRoot.size = 32) ∧
      liveRevokedRoot s.revokedRoot = true ∧ checkAllRowsNonVacuous t.rows = true := by
  have hinv : ∀ i : InvocationWithProvenance,
      (match s.capabilities[i.capabilityIndex]? with
        | none => false
        | some m => checkInvocation m i.invocation &&
            provenanceLive s.revoked i.credNul i.chanNul) = true ↔
      ∃ m, s.capabilities[i.capabilityIndex]? = some m ∧ checkInvocation m i.invocation = true ∧
        provenanceLive s.revoked i.credNul i.chanNul = true := by
    intro i
    cases s.capabilities[i.capabilityIndex]? with
    | none => simp
    | some m => simp
  simp only [execTurnSymbolic, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true_iff_forall_mem, hinv, and_assoc]

theorem provenanceLive_iff (revoked : SortedU64Set) (boundPrefix : List UInt64) (channel : UInt64) :
    provenanceLive revoked boundPrefix channel = true ↔
      (∀ k ∈ boundPrefix, ¬ revoked.spec k) ∧ ¬ revoked.spec channel := by
  simp only [provenanceLive, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    ← Bool.not_eq_true, SortedU64Set.contains_eq_spec]

/-- **A revoked nullifier refuses the turn.** If `k` is revoked, no turn is admitted that carries
an invocation over channel `k` or whose capability has `k` among its ancestor credentials. -/
theorem execTurnSymbolic_refuses_revoked (v : InnerVerifier) (s : CellState) (t : StructuredTurn)
    (k : UInt64) (hk : s.revoked.spec k) (i : InvocationWithProvenance) (hi : i ∈ t.invocations)
    (hcone : i.chanNul = k ∨ k ∈ i.credNul) : execTurnSymbolic v s t = false := by
  cases h : execTurnSymbolic v s t with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, hlive⟩ := ((execTurnSymbolic_iff v s t).mp h).2.2.1 i hi
    obtain ⟨hpre, hch⟩ := (provenanceLive_iff _ _ _).mp hlive
    rcases hcone with rfl | hmem
    · exact absurd hk hch
    · exact absurd hk (hpre k hmem)

/-! ## The credential receipt as the inner verifier -/

/-- **The inner verifier, concretely**: an effect's proof is an encoded credential statement and
ex-post receipt (`Obend.Polis.VerifiableCredentials`), checked against the statement digest the
effect names, the expected policy, and the actor's verifier key. -/
def vcInnerVerifier (P : ReceiptParams) (pol : StatusPolicy) (policyDigest : ByteArray) : InnerVerifier :=
  verifiableCredentialInnerVerifier P pol policyDigest

/-- Every admitted effect carries a compliant witness under the verifier's policy. -/
theorem execTurnSymbolic_vc_sound (P : ReceiptParams) (pol : StatusPolicy) (policyDigest : ByteArray)
    (s : CellState) (t : StructuredTurn)
    (h : execTurnSymbolic (vcInnerVerifier P pol policyDigest) s t = true) :
    ∀ e ∈ t.effects, e.actorId = s.actorId ∧ e.actorVkDigest = s.actorVkDigest ∧
      ∃ stmt rc, decodeReceiptBytes e.proof = some (stmt, rc) ∧
        statementDigest stmt = e.innerStatementDigest ∧ stmt.policyDigest = policyDigest ∧
        verifyExPostCredentialReceipt P pol s.actorVkDigest stmt rc = true ∧
        CompliantEvaluation pol (receiptView stmt rc.witness) rc.witness := by
  intro e he
  obtain ⟨⟨hid, hvk⟩, hv⟩ := ((execTurnSymbolic_iff _ s t).mp h).2.2.2.1 e he
  obtain ⟨stmt, rc, hdec, hdig, hpol, hacc, hmeaning⟩ :=
    verifiableCredentialInnerVerifier_sound P pol policyDigest _ _ _ hv
  rw [hvk] at hacc
  exact ⟨hid, hvk, stmt, rc, hdec, hdig, hpol, hacc, hmeaning⟩

/-- The effect an actor attaches for an accepted evaluation: the statement's digest and the
encoded honest receipt. -/
def credentialEffect (P : ReceiptParams) (policyDigest : ByteArray) (s : CellState)
    (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) : EffectCustom :=
  ⟨s.actorId, s.actorVkDigest,
    statementDigest (statementOf policyDigest pub (commitTable P (complianceTable pol pub w))),
    encodeReceiptBytes (statementOf policyDigest pub (commitTable P (complianceTable pol pub w)))
      (proveExPostCredentialReceipt P pol s.actorVkDigest
        (statementOf policyDigest pub (commitTable P (complianceTable pol pub w)))
        w)⟩

/-- **Admission is complete for honest credential effects.** A turn admitted without effects is
admitted with the credential effect of any accepted evaluation. -/
theorem execTurnSymbolic_vc_complete (P : ReceiptParams) (policyDigest : ByteArray)
    (s : CellState) (t : StructuredTurn) (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) (hw : checkCredentialEval pol pub w = true)
    (ht : execTurnSymbolic (vcInnerVerifier P pol policyDigest) s { t with effects := #[] } = true) :
    execTurnSymbolic (vcInnerVerifier P pol policyDigest) s
      { t with effects := #[credentialEffect P policyDigest s pol pub w] } = true := by
  obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := (execTurnSymbolic_iff _ s _).mp ht
  refine (execTurnSymbolic_iff _ s _).mpr ⟨h1, h2, h3, ?_, h5, h6, h7⟩
  intro e he
  have hee : e = credentialEffect P policyDigest s pol pub w := by simpa using he
  subst hee
  exact ⟨⟨rfl, rfl⟩, verifiableCredentialInnerVerifier_complete P policyDigest s.actorVkDigest
    pol pub w hw⟩



/-- A child handle carved out of the handle at index `parent`. -/
structure HandleDelegation where
  parent : Nat
  request : DelegationRequest

/-- One session turn: the structured turn, the credential nullifiers it revokes, and at most one
delegation. The channel nullifiers it spends are those of its invocations. -/
structure HouyhnhnmTurn where
  structured : StructuredTurn
  revokedCredentials : List UInt64
  delegation : Option HandleDelegation

/-- A session: the cell, the number of turns taken, for each capability handle the index of the
initial handle it descends from, and the post-state root committed after each turn, newest first. -/
structure HouyhnhnmSessionState where
  cell : CellState
  turnHeight : Nat
  lineage : Array Nat
  postRoots : List ByteArray

/-- A session opens with every handle its own root. -/
def openSession (cell : CellState) : HouyhnhnmSessionState :=
  ⟨cell, 0, Array.range cell.capabilities.size, []⟩

def chanNuls (turn : HouyhnhnmTurn) : List UInt64 :=
  turn.structured.invocations.toList.map (·.chanNul)

/-- Spend channel nullifiers one at a time: each must be absent from the set built so far, so a
nullifier already revoked and a nullifier repeated inside the turn are both refused. -/
def spendChannels (revoked : SortedU64Set) : List UInt64 → Option SortedU64Set
  | [] => some revoked
  | k :: ks => if revoked.contains k then none else spendChannels (revoked.insert k) ks

def revokeAll (revoked : SortedU64Set) (ks : List UInt64) : SortedU64Set :=
  ks.foldl SortedU64Set.insert revoked

/-- Debit one invocation's cost from the remaining budget of its handle. -/
def debitHandle (caps : Array Mandate) (i : InvocationWithProvenance) : Option (Array Mandate) :=
  match caps[i.capabilityIndex]? with
  | none => none
  | some m =>
    if i.invocation.cost ≤ m.budget then
      some (caps.setIfInBounds i.capabilityIndex { m with budget := m.budget - i.invocation.cost })
    else none

/-- Debit every invocation of a turn in order: two invocations on one handle share its budget. -/
def debitHandles (caps : Array Mandate) (is : List InvocationWithProvenance) :
    Option (Array Mandate) :=
  is.foldlM debitHandle caps

/-- Walk the stored `Grant.under parentId` chain in `caps` using fuel (`caps.size`),
    returning every mandate ID `[..., parentId, m.id]` from root to leaf, or `none` if a named
    parent ID is missing or cyclic. -/
def storedAncestryIds (caps : Array Mandate) : Nat → Mandate → Option (List UInt64)
  | 0, _ => none
  | fuel + 1, m =>
    match m.grant with
    | .root _ _ => some [UInt64.ofNat m.id]
    | .under parentId =>
      match caps.find? (fun p => p.id == parentId) with
      | none => none
      | some parent =>
        (storedAncestryIds caps fuel parent).map (· ++ [UInt64.ofNat m.id])

/-- Every invocation's stored capability handle must resolve a valid `Grant` chain in `caps`
    whose every mandate ID is both declared in `i.credNul` AND unrevoked in `revoked`. -/
def storedInvocationsLive (caps : Array Mandate) (revoked : SortedU64Set)
    (is : List InvocationWithProvenance) : Bool :=
  is.all fun i =>
    match caps[i.capabilityIndex]? with
    | none => false
    | some m =>
      match storedAncestryIds caps caps.size m with
      | none => false
      | some chain =>
        chain.all (fun k => decide (k ∈ i.credNul) && !revoked.contains k)

/-- Delegate a child handle: `Mandate.delegate` carves the child's budget out of the parent's,
`childId` must be fresh across `caps`, the child is appended, and it inherits the parent's root. -/
def delegateHandle (caps : Array Mandate) (lineage : Array Nat) :
    Option HandleDelegation → Option (Array Mandate × Array Nat)
  | none => some (caps, lineage)
  | some d =>
    match caps[d.parent]? with
    | none => none
    | some held =>
      match lineage[d.parent]? with
      | none => none
      | some root =>
        if requestFits d.request held && caps.all (fun m => m.id != d.request.childId) then
          some ((caps.setIfInBounds d.parent
              (held.delegate d.request.childId d.request.recipient d.request.rights d.request.quota
                d.request.cells d.request.expiresAt ⟨fun m => d.request.methods.contains m⟩).1).push
              (held.delegate d.request.childId d.request.recipient d.request.rights d.request.quota
                d.request.cells d.request.expiresAt ⟨fun m => d.request.methods.contains m⟩).2,
            lineage.push root)
        else none

/-- The state after a turn whose checks passed. Both cached roots are recomputed from the stores. -/
def nextSession (c : TurnCommitments) (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn)
    (spent : SortedU64Set) (caps : Array Mandate) (lineage : Array Nat) : HouyhnhnmSessionState :=
  let cell : CellState :=
    { st.cell with
      balances := nextBalances st.cell turn.structured
      capabilities := caps
      capRoot := c.capabilityRoot caps
      revoked := revokeAll spent turn.revokedCredentials
      revokedRoot := revokedCommitment (revokeAll spent turn.revokedCredentials) }
  ⟨cell, st.turnHeight + 1, lineage, c.stateRoot cell :: st.postRoots⟩

/-- **One session turn.** -/
def stepHouyhnhnmSession (c : TurnCommitments) (v : InnerVerifier) (st : HouyhnhnmSessionState)
    (turn : HouyhnhnmTurn) : Option HouyhnhnmSessionState :=
  if decide (RootBindings c st.cell) && execTurnSymbolic v st.cell turn.structured &&
      storedInvocationsLive st.cell.capabilities st.cell.revoked turn.structured.invocations.toList then
    match spendChannels st.cell.revoked (chanNuls turn) with
    | none => none
    | some spent =>
      match debitHandles st.cell.capabilities turn.structured.invocations.toList with
      | none => none
      | some debited =>
        match delegateHandle debited st.lineage turn.delegation with
        | none => none
        | some next => some (nextSession c st turn spent next.1 next.2)
  else none

theorem stepHouyhnhnmSession_eq_some_iff (c : TurnCommitments) (v : InnerVerifier)
    (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn) (st' : HouyhnhnmSessionState) :
    stepHouyhnhnmSession c v st turn = some st' ↔
      RootBindings c st.cell ∧ execTurnSymbolic v st.cell turn.structured = true ∧
      storedInvocationsLive st.cell.capabilities st.cell.revoked
        turn.structured.invocations.toList = true ∧
      ∃ spent debited caps lineage,
        spendChannels st.cell.revoked (chanNuls turn) = some spent ∧
        debitHandles st.cell.capabilities turn.structured.invocations.toList = some debited ∧
        delegateHandle debited st.lineage turn.delegation = some (caps, lineage) ∧
        nextSession c st turn spent caps lineage = st' := by
  unfold stepHouyhnhnmSession
  by_cases hr : RootBindings c st.cell
  · cases he : execTurnSymbolic v st.cell turn.structured with
    | false => simp [hr]
    | true =>
      cases hanc : storedInvocationsLive st.cell.capabilities st.cell.revoked
          turn.structured.invocations.toList with
      | false => simp [hr]
      | true =>
        cases hs : spendChannels st.cell.revoked (chanNuls turn) with
        | none => simp [hr]
        | some spent =>
          cases hd : debitHandles st.cell.capabilities turn.structured.invocations.toList with
          | none => simp [hr]
          | some debited =>
            cases hg : delegateHandle debited st.lineage turn.delegation with
            | none => simp [hg]
            | some next =>
              obtain ⟨caps, lineage⟩ := next
              first
                | (simp [hr, hg]; done)
                | (simp [hr, hg]
                   constructor
                   · intro h
                     exact ⟨caps, lineage, ⟨rfl, rfl⟩, h⟩
                   · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
                     exact h)
  · simp [hr]

/-! ### Why a turn is refused -/

/-- The refusal clauses of a session turn, in the order the step tests them: the cached roots
are not bound to the stores; the deltas do not conserve; a balance would go negative; an
invocation has no capability, fails its mandate, or sits under a revoked nullifier; an effect
fails the inner verifier; a root is malformed or the revoked root is the empty one; a row
constraint fails; stored capability ancestry is missing, omitted from `credNul`, or revoked;
a channel nullifier is replayed; a handle's budget is exhausted; the delegation is refused. -/
def HouyhnhnmStepViolation (c : TurnCommitments) (v : InnerVerifier)
    (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn) : Prop :=
  ¬ RootBindings c st.cell ∨
  ¬ (turn.structured.deltas.size = st.cell.balances.size ∧
      turn.structured.deltas.toList.sum = 0) ∨
  ¬ (∀ b ∈ nextBalances st.cell turn.structured, 0 ≤ b) ∨
  ¬ (∀ i ∈ turn.structured.invocations, ∃ m,
      st.cell.capabilities[i.capabilityIndex]? = some m ∧ checkInvocation m i.invocation = true ∧
      provenanceLive st.cell.revoked i.credNul i.chanNul = true) ∨
  ¬ (∀ e ∈ turn.structured.effects,
      (e.actorId = st.cell.actorId ∧ e.actorVkDigest = st.cell.actorVkDigest) ∧
      v e.actorVkDigest e.innerStatementDigest e.proof = true) ∨
  ¬ ((st.cell.actorVkDigest.size = 32 ∧ st.cell.capRoot.size = 32) ∧
      liveRevokedRoot st.cell.revokedRoot = true) ∨
  checkAllRowsNonVacuous turn.structured.rows = false ∨
  storedInvocationsLive st.cell.capabilities st.cell.revoked
    turn.structured.invocations.toList = false ∨
  spendChannels st.cell.revoked (chanNuls turn) = none ∨
  debitHandles st.cell.capabilities turn.structured.invocations.toList = none ∨
  ∃ debited, debitHandles st.cell.capabilities turn.structured.invocations.toList = some debited ∧
    delegateHandle debited st.lineage turn.delegation = none

/-- **The step refuses exactly the violating turns.** -/
theorem stepHouyhnhnmSession_eq_none_iff (c : TurnCommitments) (v : InnerVerifier)
    (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn) :
    stepHouyhnhnmSession c v st turn = none ↔ HouyhnhnmStepViolation c v st turn := by
  unfold HouyhnhnmStepViolation
  constructor
  · intro hnone
    by_cases hr : RootBindings c st.cell
    · cases he : execTurnSymbolic v st.cell turn.structured with
      | false =>
        have hne : ¬ execTurnSymbolic v st.cell turn.structured = true := by rw [he]; decide
        rw [execTurnSymbolic_iff] at hne
        by_cases h1 : turn.structured.deltas.size = st.cell.balances.size ∧
            turn.structured.deltas.toList.sum = 0
        · by_cases h2 : ∀ b ∈ nextBalances st.cell turn.structured, 0 ≤ b
          · by_cases h3 : ∀ i ∈ turn.structured.invocations, ∃ m,
                st.cell.capabilities[i.capabilityIndex]? = some m ∧
                checkInvocation m i.invocation = true ∧
                provenanceLive st.cell.revoked i.credNul i.chanNul = true
            · by_cases h4 : ∀ e ∈ turn.structured.effects,
                  (e.actorId = st.cell.actorId ∧ e.actorVkDigest = st.cell.actorVkDigest) ∧
                  v e.actorVkDigest e.innerStatementDigest e.proof = true
              · by_cases h5 : (st.cell.actorVkDigest.size = 32 ∧ st.cell.capRoot.size = 32) ∧
                    liveRevokedRoot st.cell.revokedRoot = true
                · cases h6 : checkAllRowsNonVacuous turn.structured.rows with
                  | false => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
                  | true => exact absurd ⟨h1, h2, h3, h4, h5.1, h5.2, h6⟩ hne
                · exact .inr (.inr (.inr (.inr (.inr (.inl h5)))))
              · exact .inr (.inr (.inr (.inr (.inl h4))))
            · exact .inr (.inr (.inr (.inl h3)))
          · exact .inr (.inr (.inl h2))
        · exact .inr (.inl h1)
      | true =>
        cases hanc : storedInvocationsLive st.cell.capabilities st.cell.revoked
            turn.structured.invocations.toList with
        | false => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
        | true =>
          cases hs : spendChannels st.cell.revoked (chanNuls turn) with
          | none => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
          | some spent =>
            cases hd : debitHandles st.cell.capabilities turn.structured.invocations.toList with
            | none => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))))
            | some debited =>
              cases hg : delegateHandle debited st.lineage turn.delegation with
              | none =>
                exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨debited, rfl, hg⟩)))))))))
              | some next =>
                have hsome := (stepHouyhnhnmSession_eq_some_iff c v st turn _).mpr
                  ⟨hr, he, hanc, spent, debited, next.1, next.2, hs, hd, hg, rfl⟩
                rw [hnone] at hsome
                cases hsome
    · exact .inl hr
  · intro hviol
    cases hstep : stepHouyhnhnmSession c v st turn with
    | none => rfl
    | some st' =>
      obtain ⟨hr, he, hanc, spent, debited, caps, lineage, hs, hd, hg, _⟩ :=
        (stepHouyhnhnmSession_eq_some_iff c v st turn st').mp hstep
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (execTurnSymbolic_iff _ _ _).mp he
      rcases hviol with h | h | h | h | h | h | h | h | h | h | ⟨d, hd', h⟩
      · exact absurd hr h
      · exact absurd h1 h
      · exact absurd h2 h
      · exact absurd h3 h
      · exact absurd h4 h
      · exact absurd ⟨h5, h6⟩ h
      · rw [h7] at h; cases h
      · rw [hanc] at h; cases h
      · rw [hs] at h; cases h
      · rw [hd] at h; cases h
      · rw [hd] at hd'; cases hd'; rw [hg] at h; cases h

/-- **A skipped turn violates the contract.** The step filter drops no valid turn. -/
theorem houyhnhnmStep_skip_implies_violation (c : TurnCommitments) (v : InnerVerifier)
    (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn)
    (h : stepHouyhnhnmSession c v st turn = none) : HouyhnhnmStepViolation c v st turn :=
  (stepHouyhnhnmSession_eq_none_iff c v st turn).mp h

/-- **Every non-violating turn is taken.** -/
theorem stepHouyhnhnmSession_complete (c : TurnCommitments) (v : InnerVerifier)
    (st : HouyhnhnmSessionState) (turn : HouyhnhnmTurn)
    (h : ¬ HouyhnhnmStepViolation c v st turn) :
    ∃ st', stepHouyhnhnmSession c v st turn = some st' := by
  cases hstep : stepHouyhnhnmSession c v st turn with
  | none => exact absurd ((stepHouyhnhnmSession_eq_none_iff c v st turn).mp hstep) h
  | some st' => exact ⟨st', rfl⟩

/-! ### The nullifier set -/

theorem not_spec_of_contains_false {s : SortedU64Set} {k : UInt64} (h : ¬ s.contains k = true) :
    ¬ s.spec k := fun hs => h ((s.contains_eq_spec k).mpr hs)

theorem spendChannels_spec : ∀ (ks : List UInt64) (r spent : SortedU64Set),
    spendChannels r ks = some spent →
      (∀ k, spent.spec k ↔ r.spec k ∨ k ∈ ks) ∧ (∀ k ∈ ks, ¬ r.spec k) ∧ ks.Nodup
  | [], r, spent, h => by
    simp only [spendChannels, Option.some.injEq] at h
    subst h
    simp
  | k :: ks, r, spent, h => by
    simp only [spendChannels] at h
    split at h
    · cases h
    · rename_i hk
      obtain ⟨h1, h2, h3⟩ := spendChannels_spec ks (r.insert k) spent h
      refine ⟨fun x => ?_, ?_, ?_⟩
      · rw [h1, SortedU64Set.spec_insert, List.mem_cons]
        constructor
        · rintro ((hx | hx) | hx)
          · exact .inr (.inl hx)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | hx | hx)
          · exact .inl (.inr hx)
          · exact .inl (.inl hx)
          · exact .inr hx
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact not_spec_of_contains_false hk
        · exact fun hs => h2 x hx ((SortedU64Set.spec_insert _ _ _).mpr (.inr hs))
      · exact List.nodup_cons.mpr
          ⟨fun hmem => h2 k hmem ((SortedU64Set.spec_insert _ _ _).mpr (.inl rfl)), h3⟩

/-- Spending succeeds exactly on fresh, pairwise distinct channel nullifiers. -/
theorem spendChannels_complete : ∀ (ks : List UInt64) (r : SortedU64Set),
    (∀ k ∈ ks, ¬ r.spec k) → ks.Nodup → ∃ spent, spendChannels r ks = some spent
  | [], r, _, _ => ⟨r, rfl⟩
  | k :: ks, r, hf, hn => by
    obtain ⟨hnotin, hn'⟩ := List.nodup_cons.mp hn
    have hk : r.contains k = false := by
      cases hc : r.contains k with
      | false => rfl
      | true => exact absurd ((r.contains_eq_spec k).mp hc) (hf k List.mem_cons_self)
    obtain ⟨spent, hsp⟩ := spendChannels_complete ks (r.insert k) (by
      intro x hx hs
      rcases (SortedU64Set.spec_insert _ _ _).mp hs with rfl | hs
      · exact hnotin hx
      · exact hf x (List.mem_cons_of_mem _ hx) hs) hn'
    exact ⟨spent, by simp only [spendChannels, hk]; exact hsp⟩

theorem revokeAll_spec (ks : List UInt64) : ∀ (r : SortedU64Set) (k : UInt64),
    (revokeAll r ks).spec k ↔ r.spec k ∨ k ∈ ks := by
  unfold revokeAll
  induction ks with
  | nil => intro r k; simp
  | cons x xs ih =>
    intro r k
    simp only [List.foldl_cons, ih, SortedU64Set.spec_insert, List.mem_cons]
    constructor
    · rintro ((hx | hx) | hx)
      · exact .inr (.inl hx)
      · exact .inl hx
      · exact .inr (.inr hx)
    · rintro (hx | hx | hx)
      · exact .inl (.inr hx)
      · exact .inl (.inl hx)
      · exact .inr hx

/-- The nullifiers a turn adds: its channels and its revoked credentials. -/
theorem step_revoked_spec {c : TurnCommitments} {v : InnerVerifier}
    {st st' : HouyhnhnmSessionState} {turn : HouyhnhnmTurn}
    (h : stepHouyhnhnmSession c v st turn = some st') (k : UInt64) :
    st'.cell.revoked.spec k ↔
      st.cell.revoked.spec k ∨ k ∈ chanNuls turn ∨ k ∈ turn.revokedCredentials := by
  obtain ⟨_, _, _, spent, debited, caps, lineage, hs, _, _, rfl⟩ :=
    (stepHouyhnhnmSession_eq_some_iff c v st turn st').mp h
  simp only [nextSession, revokeAll_spec, (spendChannels_spec _ _ _ hs).1, or_assoc]

/-! ### Budgets and lineage -/

def budgetSum (caps : Array Mandate) : Nat := (caps.toList.map (·.budget)).sum

def turnCost (turn : HouyhnhnmTurn) : Nat :=
  (turn.structured.invocations.toList.map (·.invocation.cost)).sum

theorem sum_map_set {α : Type} (f : α → Nat) : ∀ (l : List α) (i : Nat) (a x : α),
    l[i]? = some a → ((l.set i x).map f).sum + f a = (l.map f).sum + f x
  | [], i, a, x, h => by simp at h
  | b :: l, 0, a, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
    omega
  | b :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := sum_map_set f l i a x h
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
    omega

/-- `new` has the handles of `old`, each no wider than it was. -/
def Narrows (new old : Array Mandate) : Prop :=
  new.size = old.size ∧ ∀ (i : Nat) (m : Mandate), new[i]? = some m → ∃ m0, old[i]? = some m0 ∧ attenuates m m0

theorem Narrows.refl (caps : Array Mandate) : Narrows caps caps :=
  ⟨rfl, fun _ m h => ⟨m, h, attenuates_refl m⟩⟩

theorem Narrows.trans {a b c : Array Mandate} (hab : Narrows a b) (hbc : Narrows b c) :
    Narrows a c := by
  refine ⟨hab.1.trans hbc.1, fun i m h => ?_⟩
  obtain ⟨m1, h1, a1⟩ := hab.2 i m h
  obtain ⟨m2, h2, a2⟩ := hbc.2 i m1 h1
  exact ⟨m2, h2, attenuates_trans a1 a2⟩

theorem narrows_setIfInBounds {caps : Array Mandate} {idx : Nat} {m m' : Mandate}
    (hm : caps[idx]? = some m) (ha : attenuates m' m) :
    Narrows (caps.setIfInBounds idx m') caps := by
  refine ⟨Array.size_setIfInBounds, fun i x hx => ?_⟩
  rw [Array.getElem?_setIfInBounds] at hx
  by_cases hi : idx = i
  · subst hi
    rw [ite_eq_left rfl] at hx
    split at hx
    · cases hx
      exact ⟨m, hm, ha⟩
    · cases hx
  · rw [ite_eq_right hi] at hx
    exact ⟨x, hx, attenuates_refl x⟩

theorem attenuates_debit (m : Mandate) (cost : Nat) :
    attenuates { m with budget := m.budget - cost } m :=
  ⟨fun _ h => h, Nat.sub_le _ _, fun _ h => h, Nat.le_refl _, rfl, fun _ h => h⟩

theorem debitHandle_eq_some {caps caps' : Array Mandate} {i : InvocationWithProvenance}
    (h : debitHandle caps i = some caps') :
    ∃ m, caps[i.capabilityIndex]? = some m ∧ i.invocation.cost ≤ m.budget ∧
      caps' = caps.setIfInBounds i.capabilityIndex
        { m with budget := m.budget - i.invocation.cost } := by
  unfold debitHandle at h
  cases hm : caps[i.capabilityIndex]? with
  | none => rw [hm] at h; cases h
  | some m =>
    rw [hm] at h
    simp only at h
    split at h
    · rename_i hc
      exact ⟨m, rfl, hc, (Option.some.inj h).symm⟩
    · cases h

/-- A debit is refused exactly when the handle is missing or its remaining budget is short. -/
theorem debitHandle_eq_none_iff (caps : Array Mandate) (i : InvocationWithProvenance) :
    debitHandle caps i = none ↔
      ∀ m, caps[i.capabilityIndex]? = some m → m.budget < i.invocation.cost := by
  unfold debitHandle
  cases hm : caps[i.capabilityIndex]? with
  | none => simp
  | some m =>
    by_cases hc : i.invocation.cost ≤ m.budget
    · simp only [hc, ↓reduceIte, reduceCtorEq, Option.some.injEq, forall_eq', false_iff]
      omega
    · simp only [hc, ↓reduceIte, Option.some.injEq, forall_eq', true_iff]
      omega

theorem debitHandle_facts {caps caps' : Array Mandate} {i : InvocationWithProvenance}
    (h : debitHandle caps i = some caps') :
    budgetSum caps' + i.invocation.cost = budgetSum caps ∧ Narrows caps' caps := by
  obtain ⟨m, hm, hc, rfl⟩ := debitHandle_eq_some h
  refine ⟨?_, narrows_setIfInBounds hm (attenuates_debit m _)⟩
  have hl : caps.toList[i.capabilityIndex]? = some m := by simpa using hm
  have hs := sum_map_set (·.budget) caps.toList i.capabilityIndex m
    { m with budget := m.budget - i.invocation.cost } hl
  simp only [budgetSum, Array.toList_setIfInBounds]
  simp only at hs
  omega

theorem debitHandles_facts : ∀ (is : List InvocationWithProvenance) (caps caps' : Array Mandate),
    debitHandles caps is = some caps' →
      budgetSum caps' + (is.map (·.invocation.cost)).sum = budgetSum caps ∧ Narrows caps' caps
  | [], caps, caps', h => by
    simp only [debitHandles, List.foldlM_nil] at h
    cases h
    exact ⟨by simp, Narrows.refl _⟩
  | i :: is, caps, caps', h => by
    simp only [debitHandles, List.foldlM_cons] at h
    cases h1 : debitHandle caps i with
    | none => rw [h1] at h; cases h
    | some mid =>
      rw [h1] at h
      obtain ⟨hb, hn⟩ := debitHandles_facts is mid caps' h
      obtain ⟨hb1, hn1⟩ := debitHandle_facts h1
      refine ⟨?_, hn.trans hn1⟩
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Every handle attenuates the initial handle its lineage names, and the lineage table is as
long as the handle table. -/
def HandleLineage (roots : Array Mandate) (st : HouyhnhnmSessionState) : Prop :=
  st.lineage.size = st.cell.capabilities.size ∧
  ∀ (i : Nat) (m : Mandate), st.cell.capabilities[i]? = some m →
    ∃ (r : Nat) (m0 : Mandate), st.lineage[i]? = some r ∧ roots[r]? = some m0 ∧ attenuates m m0

theorem handleLineage_openSession (cell : CellState) :
    HandleLineage cell.capabilities (openSession cell) := by
  refine ⟨by simp [openSession], fun i m h => ?_⟩
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp h
  have hi' : i < cell.capabilities.size := hi
  refine ⟨i, m, ?_, h, attenuates_refl m⟩
  simp [openSession, hi']

theorem delegateHandle_facts {roots caps caps' : Array Mandate} {lineage lineage' : Array Nat}
    {d : Option HandleDelegation}
    (h : delegateHandle caps lineage d = some (caps', lineage'))
    (hsize : lineage.size = caps.size)
    (hlin : ∀ (i : Nat) (m : Mandate), caps[i]? = some m →
      ∃ (r : Nat) (m0 : Mandate), lineage[i]? = some r ∧ roots[r]? = some m0 ∧ attenuates m m0) :
    budgetSum caps' = budgetSum caps ∧ lineage'.size = caps'.size ∧
      ∀ (i : Nat) (m : Mandate), caps'[i]? = some m →
        ∃ (r : Nat) (m0 : Mandate), lineage'[i]? = some r ∧ roots[r]? = some m0 ∧
          attenuates m m0 := by
  cases d with
  | none =>
    simp only [delegateHandle, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hsize, hlin⟩
  | some d =>
    cases hheld : caps[d.parent]? with
    | none => simp [delegateHandle, hheld] at h
    | some held =>
      cases hroot : lineage[d.parent]? with
      | none => simp [delegateHandle, hheld, hroot] at h
      | some root =>
        by_cases hf : (requestFits d.request held && caps.all (fun m => m.id != d.request.childId)) = true
        · simp only [delegateHandle, hheld, hroot, hf, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨r, m0, hr, hm0, hatt⟩ := hlin d.parent held hheld
          rw [hroot] at hr
          cases hr
          refine ⟨?_, by simp [hsize], fun i m hm => ?_⟩
          · have hl : caps.toList[d.parent]? = some held := by simpa using hheld
            have hs := sum_map_set (·.budget) caps.toList d.parent held
              (held.delegate d.request.childId d.request.recipient d.request.rights
                d.request.quota d.request.cells d.request.expiresAt
                ⟨fun m => d.request.methods.contains m⟩).1 hl
            have hc := delegate_conserves held d.request.childId d.request.recipient
              d.request.rights d.request.quota d.request.cells d.request.expiresAt
              ⟨fun m => d.request.methods.contains m⟩
            simp only [budgetSum, Array.toList_push, Array.toList_setIfInBounds, List.map_append,
              List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
            omega
          · rw [Array.getElem?_push, Array.size_setIfInBounds] at hm
            rw [Array.getElem?_push, hsize]
            by_cases hi : i = caps.size
            · rw [ite_eq_left hi] at hm
              cases hm
              rw [ite_eq_left hi]
              exact ⟨root, m0, rfl, hm0, attenuates_trans (delegate_child_attenuates _ _ _ _ _ _ _ _) hatt⟩
            · rw [ite_eq_right hi] at hm
              rw [ite_eq_right hi]
              obtain ⟨m1, hm1, a1⟩ := (narrows_setIfInBounds hheld
                (delegate_parent_attenuates held d.request.childId d.request.recipient
                  d.request.rights d.request.quota d.request.cells d.request.expiresAt
                  ⟨fun m => d.request.methods.contains m⟩)).2 i m hm
              obtain ⟨r1, m2, hr1, hm2, a2⟩ := hlin i m1 hm1
              exact ⟨r1, m2, hr1, hm2, attenuates_trans a1 a2⟩
        · simp [delegateHandle, hheld, hroot, hf] at h

/-- What one turn does to budgets and lineage. -/
theorem step_budget_and_lineage {c : TurnCommitments} {v : InnerVerifier}
    {st st' : HouyhnhnmSessionState} {turn : HouyhnhnmTurn} (roots : Array Mandate)
    (h : stepHouyhnhnmSession c v st turn = some st') (hl : HandleLineage roots st) :
    budgetSum st'.cell.capabilities + turnCost turn = budgetSum st.cell.capabilities ∧
      HandleLineage roots st' := by
  obtain ⟨_, _, _, spent, debited, caps, lineage, _, hd, hg, rfl⟩ :=
    (stepHouyhnhnmSession_eq_some_iff c v st turn st').mp h
  obtain ⟨hb, hn⟩ := debitHandles_facts _ _ _ hd
  obtain ⟨hb2, hs2, hl2⟩ := delegateHandle_facts (roots := roots) hg (hl.1.trans hn.1.symm)
    (fun i m hm => by
      obtain ⟨m1, hm1, a1⟩ := hn.2 i m hm
      obtain ⟨r, m0, hr, hm0, a0⟩ := hl.2 i m1 hm1
      exact ⟨r, m0, hr, hm0, attenuates_trans a1 a0⟩)
  refine ⟨?_, hs2, hl2⟩
  simp only [nextSession, turnCost]
  omega

/-! ### Traces -/

/-- Run a list of turns; `none` as soon as one is refused. -/
def runHouyhnhnmSession (c : TurnCommitments) (v : InnerVerifier) (st : HouyhnhnmSessionState)
    (turns : List HouyhnhnmTurn) : Option HouyhnhnmSessionState :=
  turns.foldlM (stepHouyhnhnmSession c v) st

/-- `st'` is reached from `st` by taking `turns` in order, every one of them admitted. -/
def ValidHouyhnhnmTrace (c : TurnCommitments) (v : InnerVerifier) (st : HouyhnhnmSessionState)
    (turns : List HouyhnhnmTurn) (st' : HouyhnhnmSessionState) : Prop :=
  runHouyhnhnmSession c v st turns = some st'

theorem validHouyhnhnmTrace_nil (c : TurnCommitments) (v : InnerVerifier)
    (st st' : HouyhnhnmSessionState) : ValidHouyhnhnmTrace c v st [] st' ↔ st = st' := by
  simp [ValidHouyhnhnmTrace, runHouyhnhnmSession]

theorem validHouyhnhnmTrace_cons (c : TurnCommitments) (v : InnerVerifier)
    (st st' : HouyhnhnmSessionState) (turn : HouyhnhnmTurn) (turns : List HouyhnhnmTurn) :
    ValidHouyhnhnmTrace c v st (turn :: turns) st' ↔
      ∃ mid, stepHouyhnhnmSession c v st turn = some mid ∧
        ValidHouyhnhnmTrace c v mid turns st' := by
  simp only [ValidHouyhnhnmTrace, runHouyhnhnmSession, List.foldlM_cons]
  cases stepHouyhnhnmSession c v st turn <;> simp

theorem validHouyhnhnmTrace_append (c : TurnCommitments) (v : InnerVerifier) :
    ∀ (xs ys : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState),
      ValidHouyhnhnmTrace c v st (xs ++ ys) st' ↔
        ∃ mid, ValidHouyhnhnmTrace c v st xs mid ∧ ValidHouyhnhnmTrace c v mid ys st'
  | [], ys, st, st' => by simp [validHouyhnhnmTrace_nil]
  | x :: xs, ys, st, st' => by
    simp only [List.cons_append, validHouyhnhnmTrace_cons, validHouyhnhnmTrace_append c v xs ys]
    constructor
    · rintro ⟨m, hm, mid, h1, h2⟩
      exact ⟨mid, ⟨m, hm, h1⟩, h2⟩
    · rintro ⟨mid, ⟨m, hm, h1⟩, h2⟩
      exact ⟨m, hm, mid, h1, h2⟩

/-- A property every admitted turn preserves holds at the end of every trace. -/
theorem validHouyhnhnmTrace_invariant {c : TurnCommitments} {v : InnerVerifier}
    (P : HouyhnhnmSessionState → Prop)
    (hstep : ∀ st turn st', P st → stepHouyhnhnmSession c v st turn = some st' → P st') :
    ∀ (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState),
      ValidHouyhnhnmTrace c v st turns st' → P st → P st'
  | [], st, st', h, hp => by
    rw [validHouyhnhnmTrace_nil] at h
    exact h ▸ hp
  | turn :: turns, st, st', h, hp => by
    obtain ⟨mid, hm, hrest⟩ := (validHouyhnhnmTrace_cons c v st st' turn turns).mp h
    exact validHouyhnhnmTrace_invariant P hstep turns mid st' hrest (hstep st turn mid hp hm)

/-- **Balances are conserved and stay non-negative along every trace.** The total is the initial
total after any number of turns, and no account that started non-negative goes below zero. -/
theorem validHouyhnhnmTrace_conserves_balances (c : TurnCommitments) (v : InnerVerifier)
    (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace c v st turns st') :
    st'.cell.balances.toList.sum = st.cell.balances.toList.sum ∧
      ((∀ b ∈ st.cell.balances, 0 ≤ b) → ∀ b ∈ st'.cell.balances, 0 ≤ b) := by
  refine validHouyhnhnmTrace_invariant
    (fun s => s.cell.balances.toList.sum = st.cell.balances.toList.sum ∧
      ((∀ b ∈ st.cell.balances, 0 ≤ b) → ∀ b ∈ s.cell.balances, 0 ≤ b))
    ?_ turns st st' h ⟨rfl, fun hb => hb⟩
  intro s turn s' hp hs
  obtain ⟨_, he, _, spent, debited, caps, lineage, _, _, _, rfl⟩ :=
    (stepHouyhnhnmSession_eq_some_iff c v s turn s').mp hs
  refine ⟨?_, fun _ => ((execTurnSymbolic_iff _ _ _).mp he).2.1⟩
  simp only [nextSession]
  rw [symbolic_conserves_balances v s.cell turn.structured he]
  exact hp.1

/-- **Nullifiers accumulate.** A nullifier in the revoked set stays there through every later
turn. -/
theorem validHouyhnhnmTrace_revoked_monotone (c : TurnCommitments) (v : InnerVerifier)
    (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace c v st turns st') (k : UInt64) (hk : st.cell.revoked.spec k) :
    st'.cell.revoked.spec k :=
  validHouyhnhnmTrace_invariant (fun s => s.cell.revoked.spec k)
    (fun _ _ _ hp hs => (step_revoked_spec hs k).mpr (.inl hp)) turns st st' h hk

/-- Every channel nullifier a trace spent and every credential nullifier it revoked is in the
final revoked set. -/
theorem validHouyhnhnmTrace_spent_revoked (c : TurnCommitments) (v : InnerVerifier) :
    ∀ (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState),
      ValidHouyhnhnmTrace c v st turns st' → ∀ turn ∈ turns, ∀ k,
        k ∈ chanNuls turn ∨ k ∈ turn.revokedCredentials → st'.cell.revoked.spec k
  | [], _, _, _, _, hmem, _, _ => by cases hmem
  | t :: ts, st, st', h, turn, hmem, k, hk => by
    obtain ⟨mid, hm, hrest⟩ := (validHouyhnhnmTrace_cons c v st st' t ts).mp h
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact validHouyhnhnmTrace_revoked_monotone c v ts mid st' hrest k
        ((step_revoked_spec hm k).mpr (.inr hk))
    · exact validHouyhnhnmTrace_spent_revoked c v ts mid st' hrest turn hmem k hk

/-- **No replay, and one revocation kills the cone.** Once `k` is in the revoked set, after any
further turns `later`, a turn that invokes over channel `k`, or under a capability with `k` among
its ancestor credentials, is refused. -/
theorem validHouyhnhnmTrace_no_nullifier_replay (c : TurnCommitments) (v : InnerVerifier)
    (later : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace c v st later st') (k : UInt64) (hk : st.cell.revoked.spec k)
    (turn : HouyhnhnmTurn) (i : InvocationWithProvenance)
    (hi : i ∈ turn.structured.invocations) (hcone : i.chanNul = k ∨ k ∈ i.credNul) :
    stepHouyhnhnmSession c v st' turn = none := by
  have hk' := validHouyhnhnmTrace_revoked_monotone c v later st st' h k hk
  cases hstep : stepHouyhnhnmSession c v st' turn with
  | none => rfl
  | some s'' =>
    obtain ⟨_, he, _⟩ := (stepHouyhnhnmSession_eq_some_iff c v st' turn s'').mp hstep
    rw [execTurnSymbolic_refuses_revoked v st'.cell turn.structured k hk' i hi hcone] at he
    cases he

/-- **Stored capability ancestry cannot be bypassed by omitting `credNul`.**
    Even if a caller supplies `i.credNul = []` (omitting revoked ancestor IDs), any invocation
    whose stored capability `m` has a revoked mandate ID `k ∈ chain` in its `Grant` ancestry
    chain is refused by `stepHouyhnhnmSession`. -/
theorem validHouyhnhnmTrace_stored_ancestry_no_bypass
    (c : TurnCommitments) (v : InnerVerifier)
    (later : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace c v st later st') (k : UInt64) (hk : st.cell.revoked.spec k)
    (turn : HouyhnhnmTurn) (i : InvocationWithProvenance)
    (hi : i ∈ turn.structured.invocations)
    (m : Mandate) (hm : st'.cell.capabilities[i.capabilityIndex]? = some m)
    (chain : List UInt64)
    (hchain : storedAncestryIds st'.cell.capabilities st'.cell.capabilities.size m = some chain)
    (hkChain : k ∈ chain) :
    stepHouyhnhnmSession c v st' turn = none := by
  have hk' := validHouyhnhnmTrace_revoked_monotone c v later st st' h k hk
  cases hstep : stepHouyhnhnmSession c v st' turn with
  | none => rfl
  | some s'' =>
    obtain ⟨_, _, hanc, _⟩ := (stepHouyhnhnmSession_eq_some_iff c v st' turn s'').mp hstep
    have hiList : i ∈ turn.structured.invocations.toList := Array.mem_toList_iff.mpr hi
    have hEach := List.all_eq_true.mp hanc i hiList
    simp only [hm, hchain, List.all_eq_true, Bool.and_eq_true] at hEach
    have hkNotRev := (hEach k hkChain).2
    have hkCont : st'.cell.revoked.contains k = true :=
      (st'.cell.revoked.contains_eq_spec k).mpr hk'
    simp [hkCont] at hkNotRev

/-- The total cost of the invocations of a trace. -/
def traceCost (turns : List HouyhnhnmTurn) : Nat := (turns.map turnCost).sum

/-- **Budgets deplete and lineage holds along every trace.** What the handles have left plus
what the trace spent is what they started with, so the trace never spends more than the initial
budgets; every handle, delegated ones included, attenuates the initial handle its lineage names;
and the cached roots stay bound to the stores. -/
theorem validHouyhnhnmTrace_budget_and_lineage (c : TurnCommitments) (v : InnerVerifier)
    (roots : Array Mandate) : ∀ (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState),
      ValidHouyhnhnmTrace c v st turns st' → HandleLineage roots st → RootBindings c st.cell →
        budgetSum st'.cell.capabilities + traceCost turns = budgetSum st.cell.capabilities ∧
        HandleLineage roots st' ∧ RootBindings c st'.cell ∧
        st'.turnHeight = st.turnHeight + turns.length
  | [], st, st', h, hl, hr => by
    rw [validHouyhnhnmTrace_nil] at h
    subst h
    exact ⟨by simp [traceCost], hl, hr, by simp⟩
  | t :: ts, st, st', h, hl, _ => by
    obtain ⟨mid, hm, hrest⟩ := (validHouyhnhnmTrace_cons c v st st' t ts).mp h
    obtain ⟨hb, hl'⟩ := step_budget_and_lineage roots hm hl
    have hr' : RootBindings c mid.cell := by
      obtain ⟨_, _, _, spent, debited, caps, lineage, _, _, _, rfl⟩ :=
        (stepHouyhnhnmSession_eq_some_iff c v st t mid).mp hm
      exact ⟨rfl, rfl⟩
    have hh : mid.turnHeight = st.turnHeight + 1 := by
      obtain ⟨_, _, _, spent, debited, caps, lineage, _, _, _, rfl⟩ :=
        (stepHouyhnhnmSession_eq_some_iff c v st t mid).mp hm
      rfl
    obtain ⟨hb2, hl2, hr2, hh2⟩ :=
      validHouyhnhnmTrace_budget_and_lineage c v roots ts mid st' hrest hl' hr'
    refine ⟨?_, hl2, hr2, ?_⟩
    · simp only [traceCost, List.map_cons, List.sum_cons] at hb2 ⊢
      omega
    · simp only [List.length_cons]
      omega


end Obend.Polis.HouyhnhnmTurn
