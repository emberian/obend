module
/-
# Obend.Consensus.Simplex — quorum lemmas and a count-based cell contract (not a protocol)

What this module proves (read the statements, 2026-11-04):
- `honest_quorum_intersection`, `qc_same_view_unique` (§5): two 2f+1 quorums of a 3f+1 committee
  with at most f faulty members share an honest member, so two SAME-VIEW quorums agree. These
  quantify over abstract predicates `p q : α → Bool`; they mention no protocol.
- `simplex_accountable_safety` (§7): two overlapping quorums yield at least f+1 members in both.
  The `SlashingReceipt` it extracts names voters and carries no votes, so a third party cannot
  check it; the checkable object is `crates/obend-node`'s `EquivocationSlashReceipt` (two signed
  votes), and no theorem relates the two.
- `simplex_step_respects_law`, `simplexCellContractOf` (§6): a `SimplexState` whose `certSigners`
  is a COUNT satisfies the `LawExpr` / Core4 laws when the count meets 2f+1. A signer set checked
  against a committee lives beside it in `Obend.Consensus.Finality.QuorumBoundFinalityGate`;
  neither checks a signature.

What this module does not contain: a state machine. `State`, `ViewRecord`, `register`,
`broadcast`, `castVote` (§3–§4) are fragments with no proposal, vote, or view-change handler, and
no theorem about `State` beyond `castVote_already_voted`. There is no `simplex_safety`,
`simplex_no_skip_and_fin` or `simplex_bounded_liveness_after_gst`. The executable protocol is the
one-round simulator in `crates/obend-node/src/net.rs`; `DEOS-CONTRACTS-CONSENSUS.md` §5.2 states
what is proved about it and what is only argued.

Absorbs `minidregg/Kernel/GenericSimplex.lean`, `GenericSimplexQuorum.lean`,
and `GenericSimplexCertificateSafety.lean`; Mathlib-free.
-/

public import Obend.Vault.Hyperedge
public import Obend.Core.Data
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
public import Obend.Law.Proofs.Std
public import Obend.Tactic.Tooth

@[expose] public section

namespace Obend.Consensus.Simplex

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## 1. Symbolic Types & Blocks -/

abbrev NodeId := Nat
abbrev Round := Nat
abbrev View := Nat

/-- VaultTurn equality based on unique turnId. -/
def beqVaultTurn (a b : Obend.Vault.VaultTurn) : Bool :=
  a.turnId == b.turnId

instance : BEq Obend.Vault.VaultTurn where
  beq := beqVaultTurn

/-- Consensus block entry carrying turn ID and optional VaultTurn. -/
structure BlockEntry where
  turnId : ByteArray
  turn : Option Obend.Vault.VaultTurn
  deriving BEq

/-- Exact block ancestry chain: list of block entries. Genesis is `[]`. -/
abbrev Block := List BlockEntry
abbrev Argument := Option Block

def Block.height (b : Block) : Nat := b.length

/-- Proposal structure carrying view, height, parent, and payload. -/
structure Proposal where
  view : View
  height : Nat
  parent : Block
  turn : Option Obend.Vault.VaultTurn
  deriving BEq

inductive Kind where
  | propose
  | vote
  | commit
  | candidate
  | ready
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Unified symbolic Simplex message carrier. -/
structure Message where
  sender : NodeId
  view : View
  kind : Kind
  value : Argument
  deriving BEq

abbrev SimplexMsg := Message

/-- Symbolic Vote representation (matches E2E test harness). -/
structure Vote where
  view : View
  blockHash : String
  voter : String
  signature : String
  deriving DecidableEq, BEq, Repr

/-- Notarization / Quorum Certificate for E2E harness. -/
structure NotarizationCert where
  view : View
  blockHash : String
  votes : List Vote
  deriving DecidableEq, BEq, Repr

/-- Quorum Certificate over symbolic NodeIds. -/
structure QuorumCert where
  view : View
  kind : Kind
  value : Argument
  signers : List NodeId
  nodup : signers.Nodup

/-! ## 2. Protocol Configuration & Exponential Backoff -/

structure Config where
  parties : Nat
  faults : Nat
  timeout : Nat
  pumpBudget : Nat := 64
  backoffCap : Nat := 0
  deriving DecidableEq, BEq, Repr, Inhabited

def Config.wellFormed (c : Config) : Bool :=
  c.parties == 3 * c.faults + 1 && c.timeout > 0 && c.pumpBudget > 0

def Config.quorum (c : Config) : Nat := 2 * c.faults + 1

def Config.leader (c : Config) (view : View) : NodeId :=
  (view - 1) % c.parties

/-- Exponential view timeout: doubles with each view entered without commit, capped by `backoffCap`. -/
def viewTimeout (baseTimeout : Nat) (viewsSinceCommit : Nat) (backoffCap : Nat) : Nat :=
  baseTimeout * (2 ^ (min viewsSinceCommit backoffCap))

/-! ## 3. Replicas and Views -/

structure ViewRecord where
  number : View
  proposal : Option Block := none
  voted : Bool := false
  disableRequested : Bool := false
  sentCommit : Option Block := none
  sentCandidates : List Argument := []
  sentReadyCore : List Argument := []
  sentReadyRelay : List Argument := []
  prepared : List Block := []
  disabled : Bool := false
  committed : Option Block := none
  received : List Message := []
  deriving BEq, Inhabited

inductive AuditEvent where
  | send (message : Message)
  | prepare (party view : Nat) (block : Block)
  | disable (party view : Nat)
  | commit (party view : Nat) (block : Block)
  | idle
  deriving BEq, Inhabited

structure State where
  self : NodeId
  current : View := 1
  deadline : Nat
  now : Nat := 0
  views : List ViewRecord := []
  checked : List Block := []
  offers : List BlockEntry := []
  outbox : List Message := []
  audit : List AuditEvent := []
  delivered : List Block := []
  committedTip : Block := []
  needsPoll : Bool := false
  failed : Bool := false
  deriving BEq, Inhabited

/-! ## 4. State Machine Transition Functions -/

def viewAt (s : State) (number : View) : ViewRecord :=
  (s.views.find? (fun v => v.number == number)).getD { number := number }

def putView (s : State) (v : ViewRecord) : State :=
  { s with views := if s.views.any (fun old => old.number == v.number) then
      s.views.map (fun old => if old.number == v.number then v else old)
    else s.views ++ [v] }

def register (s : State) (m : Message) : State :=
  let v := viewAt s m.view
  putView s { v with received := if v.received.contains m then v.received else v.received ++ [m] }

def broadcast (s : State) (view : View) (kind : Kind) (value : Argument) : State :=
  let m : Message := ⟨s.self, view, kind, value⟩
  let s := register s m
  { s with outbox := s.outbox ++ [m], audit := s.audit ++ [.send m] }

def voteEquivocator (v : ViewRecord) (sender : NodeId) : Bool :=
  ((v.received.filter (fun m => m.kind == .vote && m.sender == sender)).map (·.value)).eraseDups.length > 1

def count (v : ViewRecord) (kind : Kind) (value : Argument) : Nat :=
  ((v.received.filter fun m => m.kind == kind && m.value == value &&
    (kind != .vote || !voteEquivocator v m.sender)).map (·.sender)).eraseDups.length

def castVote (s : State) (number : View) (block : Block) : State :=
  let v := viewAt s number
  if v.voted || v.disableRequested then s
  else broadcast (putView s { v with voted := true }) number .vote (some block)

theorem castVote_already_voted (s : State) (number : View) (block : Block)
    (hv : (viewAt s number).voted = true) :
    castVote s number block = s := by
  unfold castVote
  simp [hv]

/-! ## 5. Safety Metatheorems (Machine-Checked Lean 4) -/

/-- Cardinality identity for list filter sums. -/
theorem list_filter_add_card {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter q).length =
    (l.filter (fun x => p x || q x)).length + (l.filter (fun x => p x && q x)).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

theorem list_filter_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases p x <;> simp <;> omega

theorem list_filter_sub {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x && !q x)).length + (l.filter (fun x => p x && q x)).length =
    (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

theorem list_filter_and_le {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x && q x)).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

/-- **Metatheorem 1: Quorum Intersection**.
    Any two quorums of size ≥ 2f+1 in a 3f+1 committee share an honest validator. -/
theorem honest_quorum_intersection {α : Type} (l : List α) (f : Nat)
    (p q faulty : α → Bool)
    (h_size : l.length = 3 * f + 1)
    (h_p : 2 * f + 1 ≤ (l.filter p).length)
    (h_q : 2 * f + 1 ≤ (l.filter q).length)
    (h_faulty : (l.filter faulty).length ≤ f) :
    ∃ x ∈ l, p x = true ∧ q x = true ∧ faulty x = false := by
  have h_sum := list_filter_add_card p q l
  have h_union := list_filter_length_le (fun x => p x || q x) l
  have h_inter : f + 1 ≤ (l.filter (fun x => p x && q x)).length := by
    rw [h_size] at h_union
    omega
  have h_sub := list_filter_sub (fun x => p x && q x) faulty l
  have h_faulty_inter : (l.filter (fun x => (p x && q x) && faulty x)).length ≤ f := by
    have h_le := list_filter_and_le (fun x => p x && q x) faulty l
    omega
  have h_honest_pos : 0 < (l.filter (fun x => (p x && q x) && !faulty x)).length := by
    omega
  match h_match : l.filter (fun x => (p x && q x) && !faulty x) with
  | [] =>
    rw [h_match] at h_honest_pos
    contradiction
  | head :: rest =>
    have h_mem : head ∈ l.filter (fun x => (p x && q x) && !faulty x) := by
      rw [h_match]
      exact List.Mem.head rest
    have ⟨h_in_l, h_cond⟩ := (List.mem_filter.mp h_mem)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h_cond
    exact ⟨head, h_in_l, h_cond.1.1, h_cond.1.2, h_cond.2⟩

/-- **Metatheorem 2: Same-View QC Uniqueness (Conflicting Finalization Safety)**.
    Two QCs formed for the same view must agree on their value. -/
theorem qc_same_view_unique {α : Type} {val1 val2 : α} (f : Nat) (committee : List Nat)
    (p1 p2 faulty : Nat → Bool)
    (h_size : committee.length = 3 * f + 1)
    (h_p1 : 2 * f + 1 ≤ (committee.filter p1).length)
    (h_p2 : 2 * f + 1 ≤ (committee.filter p2).length)
    (h_faulty : (committee.filter faulty).length ≤ f)
    (vote : Nat → Option α)
    (h_v1 : ∀ s ∈ committee, p1 s = true → faulty s = false → vote s = some val1)
    (h_v2 : ∀ s ∈ committee, p2 s = true → faulty s = false → vote s = some val2) :
    val1 = val2 := by
  have ⟨h, h_mem, hp1, hp2, h_not_faulty⟩ :=
    honest_quorum_intersection committee f p1 p2 faulty h_size h_p1 h_p2 h_faulty
  have v1_eq := h_v1 h h_mem hp1 h_not_faulty
  have v2_eq := h_v2 h h_mem hp2 h_not_faulty
  rw [v1_eq] at v2_eq
  exact Option.some.inj v2_eq

/-- **Metatheorem 3: Monotonicity of Committed Heights & Prefix Consistency**. -/
theorem prefix_monotonic_of_ancestor {α : Type} (chain : List α) (parent : List α) (payload : α)
    (h_chain : chain = parent ++ [payload]) :
    parent.IsPrefix chain := by
  rw [h_chain]
  exact List.prefix_append parent [payload]

theorem prefix_length_le {α : Type} {a b : List α} (h : a.IsPrefix b) :
    a.length ≤ b.length := by
  obtain ⟨s, rfl⟩ := h
  simp only [List.length_append]
  omega

/-- **Metatheorem 4: Exponential View Backoff Bound**. -/
theorem exponential_backoff_timing (baseTimeout : Nat) (views : Nat) (cap : Nat) :
    viewTimeout baseTimeout views cap ≤ baseTimeout * 2 ^ cap := by
  dsimp [viewTimeout]
  have h_min : min views cap ≤ cap := Nat.min_le_right ..
  have h_pow : 2 ^ (min views cap) ≤ 2 ^ cap := Nat.pow_le_pow_right (by decide) h_min
  exact Nat.mul_le_mul_left baseTimeout h_pow

theorem exponential_backoff_base (baseTimeout : Nat) (cap : Nat) :
    viewTimeout baseTimeout 0 cap = baseTimeout := by
  dsimp [viewTimeout]
  have h_min : min 0 cap = 0 := Nat.min_eq_left (Nat.zero_le cap)
  rw [h_min]
  simp

/-! ## 6. Inner-System Seam Weld: `SimplexState` / `Cert` `Core.Data` Codecs, `LawExpr` & `CellContract` -/

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Spec.Law (LawExpr LawRef Facts)
open Obend.Law (CellContract Holds Admits law3 okT leNat eqNat andT natT
  admits_iff guard_ok subst_guard subst_binary subst_get subst_bound lawEnv)

/-- Compact Simplex BFT transition certificate carrying view, finalized height, block hash, and signer count. -/
structure Cert where
  view        : View
  blockHeight : Nat
  blockHash   : String
  signerCount : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Deterministic `Obend.Core.Data` encoding of `Cert`. -/
def Cert.toData (c : Cert) : Data :=
  .record
    [ ("view", .natural c.view)
    , ("blockHeight", .natural c.blockHeight)
    , ("blockHash", .label c.blockHash)
    , ("signerCount", .natural c.signerCount) ]

/-- Deterministic `Obend.Core.Data` decoding of `Cert`. -/
def Cert.ofData? : Data → Option Cert
  | .record
      [ ("view", .natural view)
      , ("blockHeight", .natural blockHeight)
      , ("blockHash", .label blockHash)
      , ("signerCount", .natural signerCount) ] =>
    some { view, blockHeight, blockHash, signerCount }
  | _ => none

/-- Exact roundtrip theorem for `Cert.toData` / `Cert.ofData?`. -/
theorem Cert.ofData_toData (c : Cert) :
    Cert.ofData? c.toData = some c := by
  cases c
  rfl

/-- Simplex BFT transition state welded into `.obend` `Core.Data` and relational `LawExpr` contracts. -/
structure SimplexState where
  view            : View
  finalizedHeight : Nat
  faults          : Nat
  quorumThreshold : Nat
  certSigners     : Nat
  latestCert      : Cert
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Deterministic `Obend.Core.Data` encoding of `SimplexState`. -/
def SimplexState.toData (s : SimplexState) : Data :=
  .record
    [ ("view", .natural s.view)
    , ("finalizedHeight", .natural s.finalizedHeight)
    , ("faults", .natural s.faults)
    , ("quorumThreshold", .natural s.quorumThreshold)
    , ("certSigners", .natural s.certSigners)
    , ("latestCert", s.latestCert.toData) ]

/-- Deterministic `Obend.Core.Data` decoding of `SimplexState`. -/
def SimplexState.ofData? : Data → Option SimplexState
  | .record
      [ ("view", .natural view)
      , ("finalizedHeight", .natural finalizedHeight)
      , ("faults", .natural faults)
      , ("quorumThreshold", .natural quorumThreshold)
      , ("certSigners", .natural certSigners)
      , ("latestCert", certData) ] => do
    let latestCert ← Cert.ofData? certData
    pure { view, finalizedHeight, faults, quorumThreshold, certSigners, latestCert }
  | _ => none

/-- Exact roundtrip theorem for `SimplexState.toData` / `SimplexState.ofData?`. -/
theorem SimplexState.ofData_toData (s : SimplexState) :
    SimplexState.ofData? s.toData = some s := by
  cases s with
  | mk view finalizedHeight faults quorumThreshold certSigners latestCert =>
    cases latestCert
    rfl

/-- Relational `LawExpr` enforcing view monotonicity (`view ≤ view'`) across Simplex transitions. -/
def simplexViewMonotoneLaw : LawExpr :=
  LawExpr.monotone "view"

/-- Relational `LawExpr` enforcing the `2*f + 1` quorum threshold (`quorumThreshold ≤ certSigners`),
    immutable fault bound (`writeOnce "faults"` and `faults ≤ quorumThreshold - 1`), and monotonic
    finalized height across Simplex transitions. -/
def simplexQuorumLaw : LawExpr :=
  (LawExpr.leR (.field "quorumThreshold") (.field "certSigners")).and
    ((LawExpr.leROff (.field "faults") (.field "quorumThreshold") (-1)).and
      ((LawExpr.writeOnce "faults").and
        (LawExpr.monotone "finalizedHeight")))

/-- Combined relational `LawExpr` conjoining `simplexViewMonotoneLaw` and `simplexQuorumLaw`. -/
def simplexTransitionLawExpr : LawExpr :=
  simplexViewMonotoneLaw.and simplexQuorumLaw

/-- Constructive record field lookup avoiding `BEq String` (`Classical.choice`) in Lean 4.35. -/
def simplexFieldOfList (field : String) : List (String × Data) → Option Int
  | [] => none
  | (k, v) :: rest =>
    if decide (k = field) then
      match v with
      | .natural n => some (Int.ofNat n)
      | .boolean b => some (if b then 1 else 0)
      | _          => none
    else
      simplexFieldOfList field rest

def simplexFieldOf (field : String) : Data → Option Int
  | .record fields => simplexFieldOfList field fields
  | _ => none

/-- Constructive `LawRef` reader avoiding `BEq String` (`Classical.choice`) in Lean 4.35. -/
def readSimplexRef (_facts : Facts) (state : Data) : LawRef → Option Int
  | .field name => simplexFieldOf name state
  | _           => none

/-- Constructive `LawExpr` evaluator avoiding `BEq Int` and `BEq String` (`Classical.choice`) in Lean 4.35. -/
def evalSimplexLawExpr (facts : Facts) (old : Option Data) (new : Data) : LawExpr → Bool
  | .eqC ref value => decide (readSimplexRef facts new ref = some value)
  | .leC ref value =>
    match readSimplexRef facts new ref with
    | some x => decide (x ≤ value)
    | none   => false
  | .inC ref values =>
    match readSimplexRef facts new ref with
    | some x => values.any (fun v => decide (v = x))
    | none   => false
  | .eqR left right =>
    match readSimplexRef facts new left, readSimplexRef facts new right with
    | some x, some y => decide (x = y)
    | _, _           => false
  | .leR left right =>
    match readSimplexRef facts new left, readSimplexRef facts new right with
    | some x, some y => decide (x ≤ y)
    | _, _           => false
  | .leROff left right offset =>
    match readSimplexRef facts new left, readSimplexRef facts new right with
    | some x, some y => decide (x ≤ y + offset)
    | _, _           => false
  | .monotone field =>
    match old.bind (simplexFieldOf field), simplexFieldOf field new with
    | some before, some after => decide (before ≤ after)
    | _, _                    => false
  | .writeOnce field =>
    match old.bind (simplexFieldOf field) with
    | none        => false
    | some before => decide (simplexFieldOf field new = some before)
  | .not body => !(evalSimplexLawExpr facts old new body)
  | .and left right => evalSimplexLawExpr facts old new left && evalSimplexLawExpr facts old new right
  | .or left right => evalSimplexLawExpr facts old new left || evalSimplexLawExpr facts old new right
  | .implies premise conclusion =>
    !(evalSimplexLawExpr facts old new premise) || evalSimplexLawExpr facts old new conclusion

/-- Evaluate the combined Simplex relational law across `old` and `new` `SimplexState`s. -/
def evalSimplexLaw (facts : Facts) (old new : SimplexState) : Bool :=
  evalSimplexLawExpr facts (some old.toData) new.toData simplexTransitionLawExpr

/-- Advance `SimplexState` by `viewDelta` and `heightDelta` using a notarization/finalization `cert`. -/
def stepSimplexState (s : SimplexState) (viewDelta heightDelta : Nat) (cert : Cert) : SimplexState :=
  { view            := s.view + viewDelta
  , finalizedHeight := s.finalizedHeight + heightDelta
  , faults          := s.faults
  , quorumThreshold := 2 * s.faults + 1
  , certSigners     := cert.signerCount
  , latestCert      := cert }

/-- **Bridge Theorem (`simplex_step_respects_law`)**:
    Any Simplex transition produced by `stepSimplexState` whose certificate meets the `2 * f + 1`
    quorum threshold (`2 * s.faults + 1 ≤ cert.signerCount`) satisfies both `simplexViewMonotoneLaw`
    and `simplexQuorumLaw` (`evalSimplexLaw = true`). -/
theorem simplex_step_respects_law
    (facts : Facts) (s : SimplexState) (viewDelta heightDelta : Nat) (cert : Cert)
    (h_quorum : 2 * s.faults + 1 ≤ cert.signerCount) :
    evalSimplexLawExpr facts (some s.toData)
      (stepSimplexState s viewDelta heightDelta cert).toData simplexViewMonotoneLaw = true ∧
    evalSimplexLawExpr facts (some s.toData)
      (stepSimplexState s viewDelta heightDelta cert).toData simplexQuorumLaw = true ∧
    evalSimplexLaw facts s (stepSimplexState s viewDelta heightDelta cert) = true := by
  have hv : decide (Int.ofNat s.view ≤ Int.ofNat (s.view + viewDelta)) = true :=
    decide_eq_true (Int.ofNat_le.mpr (Nat.le_add_right s.view viewDelta))
  have hq1 : decide (Int.ofNat (2 * s.faults + 1) ≤ Int.ofNat cert.signerCount) = true :=
    decide_eq_true (Int.ofNat_le.mpr h_quorum)
  have hq_f : decide (Int.ofNat s.faults ≤ Int.ofNat (2 * s.faults + 1) + (-1 : Int)) = true :=
    decide_eq_true (by simp only [Int.ofNat_eq_coe]; omega)
  have hq_wo : decide (some (Int.ofNat s.faults) = some (Int.ofNat s.faults)) = true :=
    decide_eq_true rfl
  have hq2 : decide (Int.ofNat s.finalizedHeight ≤ Int.ofNat (s.finalizedHeight + heightDelta)) = true :=
    decide_eq_true (Int.ofNat_le.mpr (Nat.le_add_right s.finalizedHeight heightDelta))
  have h_view :
      evalSimplexLawExpr facts (some s.toData)
        (stepSimplexState s viewDelta heightDelta cert).toData simplexViewMonotoneLaw = true := by
    change decide (Int.ofNat s.view ≤ Int.ofNat (s.view + viewDelta)) = true
    exact hv
  have h_q :
      evalSimplexLawExpr facts (some s.toData)
        (stepSimplexState s viewDelta heightDelta cert).toData simplexQuorumLaw = true := by
    change
      (decide (Int.ofNat (2 * s.faults + 1) ≤ Int.ofNat cert.signerCount) &&
        (decide (Int.ofNat s.faults ≤ Int.ofNat (2 * s.faults + 1) + (-1 : Int)) &&
          (decide (some (Int.ofNat s.faults) = some (Int.ofNat s.faults)) &&
            decide (Int.ofNat s.finalizedHeight ≤ Int.ofNat (s.finalizedHeight + heightDelta))))) = true
    rw [hq1, hq_f, hq_wo, hq2]
    rfl
  have h_both :
      evalSimplexLaw facts s (stepSimplexState s viewDelta heightDelta cert) = true := by
    change
      (decide (Int.ofNat s.view ≤ Int.ofNat (s.view + viewDelta)) &&
        (decide (Int.ofNat (2 * s.faults + 1) ≤ Int.ofNat cert.signerCount) &&
          (decide (Int.ofNat s.faults ≤ Int.ofNat (2 * s.faults + 1) + (-1 : Int)) &&
            (decide (some (Int.ofNat s.faults) = some (Int.ofNat s.faults)) &&
              decide (Int.ofNat s.finalizedHeight ≤ Int.ofNat (s.finalizedHeight + heightDelta)))))) = true
    rw [hv, hq1, hq_f, hq_wo, hq2]
    rfl
  exact ⟨h_view, h_q, h_both⟩

/-- Concrete fixtures for `#tooth` refutation probes on `simplexViewMonotoneLaw` and `simplexQuorumLaw`. -/
def demoSimplexFacts : Facts := ⟨none, none, 1, 1⟩

def demoSimplexCert : Cert :=
  { view := 4, blockHeight := 10, blockHash := "blk-10", signerCount := 3 }

def demoSimplexBase : SimplexState :=
  { view            := 4
  , finalizedHeight := 10
  , faults          := 1
  , quorumThreshold := 3
  , certSigners     := 3
  , latestCert      := demoSimplexCert }

def demoSimplexViewRegressed : SimplexState :=
  { demoSimplexBase with view := 2 }

def demoSimplexUnderQuorum : SimplexState :=
  { demoSimplexBase with certSigners := 2, latestCert := { demoSimplexCert with signerCount := 2 } }

def demoSimplexLoweredThreshold : SimplexState :=
  { demoSimplexBase with quorumThreshold := 1, certSigners := 1, latestCert := { demoSimplexCert with signerCount := 1 } }

/-- Refutation theorem: a view-regressed Simplex transition (`4 → 2`) is rejected. -/
theorem simplex_view_regression_rejected :
    evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexViewRegressed = false := rfl

/-- Refutation theorem: an under-quorum Simplex transition (`2 < 2*1 + 1`) is rejected. -/
theorem simplex_under_quorum_rejected :
    evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexUnderQuorum = false := rfl

/-- Refutation theorem: attempting to bypass quorum by lowering `quorumThreshold` to `1` is rejected. -/
example :
    evalSimplexLaw demoSimplexFacts demoSimplexBase demoSimplexLoweredThreshold = false := rfl

#tooth simplex_view_regression_rejected by mutation
  simplexViewMonotoneLaw := LawExpr.monotone "finalizedHeight"

#tooth simplex_under_quorum_rejected by mutation
  simplexQuorumLaw := LawExpr.monotone "finalizedHeight"

theorem ok_ne_refused_simplex (h : ("ok" : String) = "refused") : False := by
  have hlen : ("ok" : String).utf8ByteSize = ("refused" : String).utf8ByteSize :=
    congrArg String.utf8ByteSize h
  exact absurd hlen (by decide)

theorem guard_ok_simplex {c rest w : Term} {why : String}
    (h : Obend.Core.Term.Evaluates (Obend.Law.guard c why rest) (.inject "ok" w)) :
    Obend.Core.Term.Evaluates c (.boolean true) ∧
      Obend.Core.Term.Evaluates rest (.inject "ok" w) := by
  rcases Obend.Law.ifBool_inv h with ⟨b, hc, hr⟩
  cases b with
  | false =>
    dsimp at hr
    have hval := Obend.Law.evaluates_value (.inject "refused" (.label why)) hr
    injection hval with htag _
    exact False.elim (ok_ne_refused_simplex htag)
  | true =>
    exact ⟨hc, hr⟩

/-- Core4 state invariant for a Simplex cell with fault tolerance `f`:
    `2 * f + 1 ≤ s.certSigners ∧ s.certSigners ≤ 3 * f + 1` (quorum met and committee-bounded). -/
def simplexInvariant (f : Nat) : Term :=
  .lam
    (andT
      (leNat (natT (2 * f + 1)) (.get (.bound 0) "certSigners"))
      (leNat (.get (.bound 0) "certSigners") (natT (3 * f + 1))))

theorem subst_simplexInvariant (f : Nat) (σ : Nat → Term) :
    (simplexInvariant f).substitute σ = simplexInvariant f := by
  simp [simplexInvariant, andT, Obend.Law.falseT, leNat, natT, Term.substitute, subst_binary, subst_get, subst_bound]
  rfl

/-- Core4 step relation body enforcing `old.view ≤ new.view`, `old.finalizedHeight ≤ new.finalizedHeight`,
    `2 * f + 1 ≤ new.certSigners`, and `new.certSigners ≤ 3 * f + 1`. -/
def simplexStepBody (f : Nat) : Term :=
  Obend.Law.guard
    (andT
      (leNat (.get (.bound 2) "view") (.get (.bound 1) "view"))
      (andT
        (leNat (.get (.bound 2) "finalizedHeight") (.get (.bound 1) "finalizedHeight"))
        (andT
          (leNat (natT (2 * f + 1)) (.get (.bound 1) "certSigners"))
          (leNat (.get (.bound 1) "certSigners") (natT (3 * f + 1))))))
    "simplex_law_violation"
    okT

/-- Core4 3-argument relational step law (`old`, `new`, `req`) for Simplex BFT. -/
def simplexStepRel (f : Nat) : Term :=
  law3 (simplexStepBody f)

/-- Core4 transition law combining `simplexInvariant` preservation with `simplexStepBody`. -/
def simplexTransitionLaw (f : Nat) : Term :=
  law3
    (Obend.Law.guard
      (.app (simplexInvariant f) (.bound 1))
      "quorum_shortfall"
      (simplexStepBody f))

/-- Parameterized `Obend.Law.CellContract` for Simplex BFT with fault tolerance `f`
    enforcing both quorum (`2 * f + 1 ≤ certSigners`) and committee upper bound (`certSigners ≤ 3 * f + 1`). -/
def simplexCellContractOf (f : Nat) : CellContract where
  law := simplexTransitionLaw f
  invariant := simplexInvariant f
  stepRel := simplexStepRel f
  inductive_preserves := by
    intro old new req _h_old h_adm
    rw [simplexTransitionLaw, admits_iff] at h_adm
    rcases h_adm with ⟨w, hw⟩
    rw [subst_guard] at hw
    have h_ok := guard_ok_simplex hw
    have h_cond := h_ok.1
    simp [subst_simplexInvariant, subst_bound, lawEnv] at h_cond
    exact h_cond
  step_sound := by
    intro old new req _h_old h_adm
    rw [simplexTransitionLaw, admits_iff] at h_adm
    rcases h_adm with ⟨w, hw⟩
    rw [subst_guard] at hw
    have h_ok := guard_ok_simplex hw
    rw [simplexStepRel, admits_iff]
    exact ⟨w, h_ok.2⟩

/-- Default `Obend.Law.CellContract` instance for Simplex BFT (`f = 1`, quorum `2*f + 1 = 3`, committee `3*f + 1 = 4`). -/
def simplexCellContract : CellContract :=
  simplexCellContractOf 1

/-! ## 7. Accountable Safety (`SlashingReceipt`, `extractSlashingReceipt`, `simplex_accountable_safety`) -/

/-- A record of a view, two conflicting block identifiers (`blockA`, `blockB`), and the validator
    IDs that a pair of vote predicates put on both sides. It carries no votes and no signatures: it
    is the OUTPUT of `extractSlashingReceipt` over predicates the caller supplies, not evidence a
    stranger can check. A checkable receipt holds the two signed votes
    (`crates/obend-node` `EquivocationSlashReceipt`). -/
structure SlashingReceipt where
  view               : Nat
  blockA             : Nat
  blockB             : Nat
  equivocatingVoters : List Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Encode a list of `Nat` validator IDs into `Obend.Core.Data`. -/
def encodeVoterIds : List Nat → Data
  | [] => .variant "nil" (.record [])
  | v :: vs =>
    .variant "cons"
      (.record [ ("head", .natural v), ("tail", encodeVoterIds vs) ])

/-- Decode a list of `Nat` validator IDs from `Obend.Core.Data`. -/
def decodeVoterIds : Data → Option (List Nat)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [ ("head", .natural v), ("tail", rest) ]) => do
    let vs ← decodeVoterIds rest
    pure (v :: vs)
  | _ => none

theorem decodeVoterIds_encodeVoterIds :
    ∀ (vs : List Nat), decodeVoterIds (encodeVoterIds vs) = some vs
  | [] => rfl
  | v :: vs => by
    simp [encodeVoterIds, decodeVoterIds, decodeVoterIds_encodeVoterIds vs]

/-- Deterministic `Obend.Core.Data` encoding of `SlashingReceipt`. -/
def SlashingReceipt.toData (r : SlashingReceipt) : Data :=
  .record
    [ ("view", .natural r.view)
    , ("blockA", .natural r.blockA)
    , ("blockB", .natural r.blockB)
    , ("equivocatingVoters", encodeVoterIds r.equivocatingVoters) ]

/-- Deterministic `Obend.Core.Data` decoding of `SlashingReceipt`. -/
def SlashingReceipt.ofData? : Data → Option SlashingReceipt
  | .record
      [ ("view", .natural view)
      , ("blockA", .natural blockA)
      , ("blockB", .natural blockB)
      , ("equivocatingVoters", vsData) ] => do
    let vs ← decodeVoterIds vsData
    pure { view, blockA, blockB, equivocatingVoters := vs }
  | _ => none

/-- Exact roundtrip theorem for `SlashingReceipt.toData` / `SlashingReceipt.ofData?`. -/
theorem SlashingReceipt.ofData_toData (r : SlashingReceipt) :
    SlashingReceipt.ofData? r.toData = some r := by
  cases r with
  | mk view blockA blockB vs =>
    simp [SlashingReceipt.toData, SlashingReceipt.ofData?, decodeVoterIds_encodeVoterIds]

/-- Constructive membership check on `List Nat` using `decide (v = x)`. -/
def memNatList (v : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => decide (v = x) || memNatList v xs

/-- Constructively extract an accountable `SlashingReceipt` from a validator `committee`
    and two conflicting vote predicates `votedA` (for `blockA`) and `votedB` (for `blockB`). -/
def extractSlashingReceipt
    (view blockA blockB : Nat)
    (committee : List Nat)
    (votedA votedB : Nat → Bool) : SlashingReceipt :=
  { view               := view
  , blockA             := blockA
  , blockB             := blockB
  , equivocatingVoters := committee.filter (fun v => votedA v && votedB v) }

/-- Constructively extract an accountable `SlashingReceipt` from a validator `committee`
    and two explicit voter lists `votersA` and `votersB`. -/
def extractSlashingReceiptFromLists
    (view blockA blockB : Nat)
    (committee votersA votersB : List Nat) : SlashingReceipt :=
  extractSlashingReceipt view blockA blockB committee
    (fun v => memNatList v votersA)
    (fun v => memNatList v votersB)

/-- Filtering a `Nodup` list preserves `Nodup`. -/
theorem nodup_filter_simplex {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    cases h with
    | cons h_not_mem h_xs =>
      simp only [List.filter_cons]
      cases p x with
      | false => exact nodup_filter_simplex p h_xs
      | true =>
        exact List.Pairwise.cons
          (fun y hy => h_not_mem y (List.mem_filter.mp hy).1)
          (nodup_filter_simplex p h_xs)

/-- **Accountable Safety (`simplex_accountable_safety`)**:
    If two distinct blocks `blockA ≠ blockB` both achieve `2*f + 1` quorum certificates
    in the same `view` among at most `3*f + 1` validators in `committee`, then
    `extractSlashingReceipt` constructively extracts at least `f + 1` validators who
    double-voted for both `blockA` and `blockB` (`votedA v = true ∧ votedB v = true`). -/
theorem simplex_accountable_safety
    (view blockA blockB f : Nat)
    (committee : List Nat)
    (votedA votedB : Nat → Bool)
    (h_distinct : blockA ≠ blockB)
    (h_committee : committee.length ≤ 3 * f + 1)
    (h_quorumA : 2 * f + 1 ≤ (committee.filter votedA).length)
    (h_quorumB : 2 * f + 1 ≤ (committee.filter votedB).length) :
    let receipt := extractSlashingReceipt view blockA blockB committee votedA votedB
    receipt.blockA ≠ receipt.blockB ∧
    f + 1 ≤ receipt.equivocatingVoters.length ∧
    (∀ v ∈ receipt.equivocatingVoters, v ∈ committee ∧ votedA v = true ∧ votedB v = true) := by
  dsimp [extractSlashingReceipt]
  have h_sum := list_filter_add_card votedA votedB committee
  have h_union := list_filter_length_le (fun v => votedA v || votedB v) committee
  have h_bound : f + 1 ≤ (committee.filter (fun v => votedA v && votedB v)).length := by
    omega
  refine ⟨h_distinct, h_bound, ?_⟩
  intro v hv
  have ⟨h_in, h_both⟩ := List.mem_filter.mp hv
  simp only [Bool.and_eq_true] at h_both
  exact ⟨h_in, h_both.1, h_both.2⟩

/-- When `committee.Nodup` holds, `extractSlashingReceipt` extracts at least `f + 1`
    distinct (`Nodup`) equivocating validators. -/
theorem simplex_accountable_safety_nodup
    (view blockA blockB f : Nat)
    (committee : List Nat)
    (votedA votedB : Nat → Bool)
    (h_nodup : committee.Nodup)
    (h_distinct : blockA ≠ blockB)
    (h_committee : committee.length ≤ 3 * f + 1)
    (h_quorumA : 2 * f + 1 ≤ (committee.filter votedA).length)
    (h_quorumB : 2 * f + 1 ≤ (committee.filter votedB).length) :
    let receipt := extractSlashingReceipt view blockA blockB committee votedA votedB
    receipt.equivocatingVoters.Nodup ∧
    f + 1 ≤ receipt.equivocatingVoters.length ∧
    (∀ v ∈ receipt.equivocatingVoters, v ∈ committee ∧ votedA v = true ∧ votedB v = true) := by
  have ⟨_, h_len, h_mem⟩ :=
    simplex_accountable_safety view blockA blockB f committee votedA votedB
      h_distinct h_committee h_quorumA h_quorumB
  exact ⟨nodup_filter_simplex (fun v => votedA v && votedB v) h_nodup, h_len, h_mem⟩

end Obend.Consensus.Simplex

