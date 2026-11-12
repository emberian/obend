module
public import Obend.Polis.CapTP

public section
namespace Obend.Polis.HouyhnhnmTurn
open Obend.Crypto Obend.Vault.Mandate Obend.Polis.CapTP

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

@[expose] def wellFormedInputs (p : FullPinnedPublicInputs) : Bool :=
  decide (p.circuitDescDigest.size = 32 ∧ p.actorVkDigest.size = 32 ∧
    p.preStateRoot.size = 32 ∧ p.postStateRoot.size = 32 ∧ p.capRoot.size = 32 ∧
    p.revokedRoot.size = 32 ∧ p.turnHash.size = 32)

@[expose] def natBytes (n : Nat) : ByteArray :=
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

@[expose] def relationPrefix (p : FullPinnedPublicInputs) : ByteArray :=
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
    (encodeNats (revoked.data.toList.map UInt64.toNat)).data.toList

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

@[expose] def materializeInputs (c : TurnCommitments) (s : CellState) (t : StructuredTurn)
    (height : Nat) : FullPinnedPublicInputs where
  circuitDescDigest := c.circuitDigest
  actorVkDigest := s.actorVkDigest
  preStateRoot := c.stateRoot s
  postStateRoot := c.stateRoot { s with balances := nextBalances s t }
  capRoot := s.capRoot
  revokedRoot := s.revokedRoot
  height := height
  turnHash := c.turnHash t

/-- Cached roots must be tied to the live stores before a turn crosses a boundary. -/
@[expose] def RootBindings (c : TurnCommitments) (s : CellState) : Prop :=
  s.revokedRoot = revokedCommitment s.revoked ∧ s.capRoot = c.capabilityRoot s.capabilities

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
  exact ⟨c.circuitDigest_size, hc.1, c.stateRoot_size _, c.stateRoot_size _,
    hc.2, hr.1, c.turnHash_size _⟩

def TurnRelation (c : TurnCommitments) (v : InnerVerifier) (p : FullPinnedPublicInputs) : Prop :=
  ∃ s t, execTurnSymbolic v s t = true ∧ RootBindings c s ∧
    materializeInputs c s t p.height = p

structure TurnProofSystem (c : TurnCommitments) (v : InnerVerifier) where
  Receipt : Type
  verify : FullPinnedPublicInputs → ByteArray → Receipt → Bool
  prove : (s : CellState) → (t : StructuredTurn) → (height : Nat) →
    execTurnSymbolic v s t = true → RootBindings c s → Receipt
  sound : ∀ p challenge receipt, verify p challenge receipt = true → TurnRelation c v p
  complete : ∀ s t height hs hr,
    verify (materializeInputs c s t height)
      (squeezeChallenge256 (turnTranscript (materializeInputs c s t height))).1.val
      (prove s t height hs hr) = true

structure SovereignTurnBundle {c : TurnCommitments} {v : InnerVerifier} (ps : TurnProofSystem c v) where
  publicInputs : FullPinnedPublicInputs
  boundPrefix : ByteArray
  receipt : ps.Receipt

@[expose] def verifyCipherclerkBundle {c : TurnCommitments} {v : InnerVerifier}
    (ps : TurnProofSystem c v) (b : SovereignTurnBundle ps) : Bool :=
  decide (b.boundPrefix = relationPrefix b.publicInputs) && wellFormedInputs b.publicInputs &&
  liveRevokedRoot b.publicInputs.revokedRoot &&
  TurnProofSystem.verify (c := c) (v := v) ps b.publicInputs (squeezeChallenge256 (turnTranscript b.publicInputs)).1.val b.receipt

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
    (collapseTurn ps s t height hs hr).publicInputs.preStateRoot = c.stateRoot s ∧
    (collapseTurn ps s t height hs hr).publicInputs.postStateRoot =
      c.stateRoot { s with balances := nextBalances s t } := by
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

@[expose] def ReversibleTurn.invert (t : ReversibleTurn) : ReversibleTurn :=
  ⟨t.forwardDeltas.map (- ·)⟩
abbrev BalanceState := Nat → Int
@[expose] def applyTurn (t : ReversibleTurn) (s : BalanceState) : BalanceState :=
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

end Obend.Polis.HouyhnhnmTurn
