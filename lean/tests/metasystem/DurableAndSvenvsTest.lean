module
import all Obend.Polis.BlumRam
import all Obend.Vault.Log
import all Obend.Vault.WorldTree
/-
# `tests/metasystem/DurableAndSvenvsTest.lean` — End-to-End Verification of Chasm C4 (`VaultDurableBridge` & `SvenvsCorrigibility`)

Exercises end-to-end across concrete instances and universal `#tooth` mutation checks:

1. **Part A — Crash-Torn `SegmentLog` Multi-Segment Rollover & `segmented_exposed_once`:**
   - Concrete two-buyer one-capability `Ledger` (`capLedger`) backed by physical `SegmentLog`
     blocks at `segCap := 200` bytes (forcing segment boundary rotation on the second `OBL1` frame).
   - Verifies multi-segment rollover (`2 ≤ segments.length`, `seg0.length = 200`), torn-tail crash
     leaving a 50-byte partial `OBL1` frame on disk, refusal of dirty-tail submits before recovery,
     exact recovery idempotence (`segmented_torn_crash_recover_idempotent`), post-crash refusal of
     double-spend and double-expose, and concrete instantiation of `segmented_exposed_once`.

2. **Part B — Linear Capability-Carrying `.perform` Plans (`Ty.isTransferable` + `CapTable`):**
   - Dehydrates a multi-capability `.perform` plan (`Ty.isTransferablePlan = true`, `Ty.isPlan = false`)
     into `(DataWire, CapSealFrame)`, round-trips `DataWire` through `Obend.Core.Data.Data`, and
     rehydrates on resume (`rehydrate_dehydrate_roundtrip`, `transfer_conserves_custody_exact`).
   - Verifies deterministic refusal on forged capability indices, tampered frame seals, duplicate
     capability slots, and dropped linear capabilities, plus universal `#tooth` mutation checks.

3. **Part C — `Genealogy.Habitat` Governed by 3-Tier `SpecNeg`, $B$-Corrigibility & `PcaEnvelope`:**
   - Runs a concrete `ConstitutionalStack Genealogy.record` through lateral Tier-2 spec negotiation
     (dropping a non-meta task floor while keeping Tier-1 meta-floors and Tier-0 `.home 3` bedrock),
     Tier-1 meta-amendment, and operator `revert`, instantiating `habitat_bedrock_is_eternal`,
     `override_iff_burned_bridge`, `PcaEnvelope` / `embodiedTurnSelect`, and universal `#tooth` checks.
-/
public import Obend.Vault.Replay
public import Obend.Judge.SvenvsCorrigibility
public import Obend.Judge.Genealogy
public import Obend.Tactic.Tooth
import all Obend.Run.Durable
import all Obend.Run.Shared
import all Obend.Run.Runner
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Slot.Protocol
import all Obend.Slot.Integrity
import all Obend.Slot.Selection
import all Obend.Slot
import all Obend.Receipt
import all Obend.Vault.Rehydration
import all Obend.Core.Data
import all Obend.Vault.Replay
import all Obend.Judge.SvenvsCorrigibility

public section
set_option Elab.async false

namespace Obend.Tests.DurableAndSvenvsTest

open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Vault.Log (Bytes Record encodeRecord encodeAll parseFrom lastHash dig)
open Obend.Vault.Rehydration (genesisSentinel)
open Obend.Vault.SegmentLog (split)
open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared Obend.Run.Durable
open Obend.Run.VaultDurableBridge
open Obend.Judge.Genealogy (Habitat Gate Exec)
open Obend.Judge.SvenvsCorrigibility

set_option autoImplicit false

-- ============================================================================
-- 1. Concrete Two-Buyer Segmented Disk Log with Torn-Tail Crash & Rollover
-- ============================================================================

/-- Minimal two-phase protocol signature (`false` = idle, `true` = committed) for one linear token. -/
@[expose] def capOp : Bool → Type
  | false => Unit
  | true => Empty

@[expose] def capSig : Sig Bool where
  Op := capOp
  Resp := fun _ => Unit
  next := fun _ _ => true

instance decCapOp : (b : Bool) → DecidableEq (capOp b)
  | false, (), () => isTrue rfl
  | true, x, _ => nomatch x

instance : DecidableEq (Σ b, capSig.Op b) :=
  fun ⟨b₁, o₁⟩ ⟨b₂, o₂⟩ =>
    if hb : b₁ = b₂ then
      by
        subst hb
        exact match decCapOp b₁ o₁ o₂ with
          | isTrue ho => isTrue (ho ▸ rfl)
          | isFalse hno => isFalse (fun h => hno (Sigma.mk.inj h |>.2 |> eq_of_heq))
    else
      isFalse (fun h => hb (Sigma.mk.inj h).1)

@[expose] def capHole : Bool → Type := fun _ => Empty

instance : (b : Bool) → DecidableEq (capHole b) := fun _ x _ => nomatch x

def capSpec : Spec capSig Unit Empty Empty where
  consumes := fun {b} _ => match b with | false => some () | true => none
  requires := fun _ => []
  establishes := fun _ => []

/-- Ledger record for two buyers (`false` = Alice, `true` = Bob) competing for one token `()`. -/
structure CapLedRec where
  raw : Nat
  spent : List Unit
  grants : List (Grant Bool Unit)
  height : Nat
  deriving DecidableEq, Repr

theorem capLed_setRaw_ok (d : CapLedRec) (w : Nat) (h : decide (d.raw < w) = true) :
    ((decide (d.raw = w) || decide (d.raw < w)) && decide (d.height ≤ d.height + 1)) = true := by
  rw [h, Bool.or_true, Bool.true_and]; exact decide_eq_true (Nat.le_succ d.height)

theorem capLed_height_le (d d' : CapLedRec)
    (h : ((decide (d.raw = d'.raw) || decide (d.raw < d'.raw)) && decide (d.height ≤ d'.height)) = true) :
    d.height ≤ d'.height := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

@[expose] def capLedger : Ledger Bool Nat Unit :=
  ⟨CapLedRec, CapLedRec.raw, CapLedRec.spent, CapLedRec.grants, fun w w' => decide (w < w'),
    fun d i t => ⟨d.raw, d.spent ++ [t], d.grants ++ [⟨t, i, d.grants.length⟩], d.height + 1⟩,
    fun d w => ⟨w, d.spent, d.grants, d.height + 1⟩, fun d _ => d,
    fun d d' => (decide (d.raw = d'.raw) || decide (d.raw < d'.raw)) && decide (d.height ≤ d'.height),
    CapLedRec.height, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => by simp, fun _ _ _ => by simp,
    capLed_setRaw_ok, fun _ _ => by simp, fun _ _ _ => rfl, capLed_height_le, fun _ _ => rfl,
    fun _ _ => rfl⟩

def capBaseView : Nat → View Unit Empty := fun _ => ⟨(fun e => nomatch e), fun _ => true⟩
def capAuth : Authority Unit Unit := ⟨fun _ _ => true⟩
def capCtl : (j : Bool) → capHole j → SlotCtl capSig capHole (fun _ => Unit) Unit Empty Unit j :=
  fun _ h => nomatch h

def capOpen₀ : Open capSig capHole (fun _ => Unit) Unit Empty Empty false where
  template := .call (S := capSig) (i := false) () (fun () => .ret ())
  Ω := fun _ h => nomatch h
  σ := fun _ h => nomatch h
  Γ := []
  Δ := [()]
  Q := fun _ _ => True
  Φ := []
  hist := ⟨[], none⟩

def capRec₀ : CapLedRec := ⟨0, [], [], 0⟩

def capJ₀ : JCfg capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false :=
  JCfg.init capLedger capRec₀ (fun _ => capOpen₀) (fun _ _ h => nomatch h)

abbrev CapJEv := JEv capLedger capSig capHole (fun _ => Unit) Unit Unit Unit Empty

/-- Lossless first-order codec for `CapJEv`. -/
private def encodeBoolByte (b : Bool) : UInt8 := if b then 1 else 0

private def decodeBoolByte : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] private theorem decodeBoolByte_encodeBoolByte (b : Bool) :
    decodeBoolByte (encodeBoolByte b) = some b := by
  cases b <;> rfl

/-- Self-delimiting base-2 nibble encoding of `Nat` (`0` = terminator, `1` = bit 0, `2` = bit 1). -/
private def encodeBits : Nat → Bytes
  | 0 => [0]
  | n + 1 =>
    let v := n + 1
    (if v % 2 == 0 then (1 : UInt8) else (2 : UInt8)) :: encodeBits (v / 2)
termination_by n => n

private def decodeBitsFuel : Nat → Bytes → Option (Nat × Bytes)
  | 0, _ => none
  | _ + 1, 0 :: rest => some (0, rest)
  | fuel + 1, 1 :: rest => (decodeBitsFuel fuel rest).map fun (hi, rem) => (2 * hi, rem)
  | fuel + 1, 2 :: rest => (decodeBitsFuel fuel rest).map fun (hi, rem) => (2 * hi + 1, rem)
  | _ + 1, _ => none

private theorem decodeBitsFuel_encodeBits :
    ∀ (n : Nat) (extra : Bytes) (fuel : Nat),
      (encodeBits n).length ≤ fuel →
      decodeBitsFuel fuel (encodeBits n ++ extra) = some (n, extra) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind k ih =>
    intro extra fuel hlen
    cases k with
    | zero =>
      cases fuel with
      | zero => simp [encodeBits] at hlen
      | succ f => simp [encodeBits, decodeBitsFuel]
    | succ m =>
      rw [encodeBits] at hlen ⊢
      cases fuel with
      | zero => simp at hlen
      | succ f =>
        simp only [List.length_cons] at hlen
        have hrec := ih ((m + 1) / 2) (by omega) extra f (by omega)
        by_cases heven : (m + 1) % 2 == 0
        · simp only [heven, ↓reduceIte, List.cons_append, decodeBitsFuel, hrec, Option.map_some]
          have hmod : (m + 1) % 2 = 0 := beq_iff_eq.mp heven
          congr 1; congr 1; omega
        · simp only [heven, Bool.false_eq_true, ↓reduceIte, List.cons_append, decodeBitsFuel,
            hrec, Option.map_some]
          have hmod : (m + 1) % 2 = 1 := by
            have hne : (m + 1) % 2 ≠ 0 := fun h => heven (beq_iff_eq.mpr h)
            omega
          congr 1; congr 1; omega

private def decodeBits (bs : Bytes) : Option (Nat × Bytes) :=
  decodeBitsFuel bs.length bs

private theorem decodeBits_encodeBits (n : Nat) (extra : Bytes) :
    decodeBits (encodeBits n ++ extra) = some (n, extra) := by
  unfold decodeBits; apply decodeBitsFuel_encodeBits; simp

private def encodeNatList : List Nat → Bytes
  | [] => [0]
  | x :: xs => 1 :: (encodeBits x ++ encodeNatList xs)

private def decodeNatListFuel : Nat → Bytes → Option (List Nat × Bytes)
  | 0, _ => none
  | _ + 1, 0 :: rest => some ([], rest)
  | fuel + 1, 1 :: rest =>
    match decodeBits rest with
    | none => none
    | some (x, r₁) => (decodeNatListFuel fuel r₁).map fun (xs, r₂) => (x :: xs, r₂)
  | _ + 1, _ => none

private theorem decodeNatListFuel_encodeNatList :
    ∀ (xs : List Nat) (extra : Bytes) (fuel : Nat),
      xs.length + 1 ≤ fuel →
      decodeNatListFuel fuel (encodeNatList xs ++ extra) = some (xs, extra)
  | [], extra, fuel, hlen => by
    cases fuel with
    | zero => omega
    | succ f => simp [encodeNatList, decodeNatListFuel]
  | x :: xs, extra, fuel, hlen => by
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.length_cons] at hlen
      simp only [encodeNatList, List.cons_append, List.append_assoc, decodeNatListFuel,
        decodeBits_encodeBits, decodeNatListFuel_encodeNatList xs extra f (by omega),
        Option.map_some]

private def encodeCapLedRecWords (d : CapLedRec) : List Nat :=
  [d.raw, d.spent.length, d.height] ++ d.grants.flatMap (fun g => [if g.winner then 1 else 0, g.epoch])

private def parseGrantPairs : List Nat → Option (List (Grant Bool Unit))
  | [] => some []
  | 0 :: ep :: rest => (parseGrantPairs rest).map (⟨(), false, ep⟩ :: ·)
  | 1 :: ep :: rest => (parseGrantPairs rest).map (⟨(), true, ep⟩ :: ·)
  | _ => none

private theorem parseGrantPairs_flatMap :
    ∀ (gs : List (Grant Bool Unit)),
      parseGrantPairs (gs.flatMap (fun g => [if g.winner then 1 else 0, g.epoch])) = some gs
  | [] => rfl
  | ⟨(), false, _⟩ :: rest => by simp [parseGrantPairs, parseGrantPairs_flatMap rest]
  | ⟨(), true, _⟩ :: rest => by simp [parseGrantPairs, parseGrantPairs_flatMap rest]

private theorem replicate_unit_eq : ∀ (us : List Unit), List.replicate us.length () = us
  | [] => rfl
  | () :: rest => congrArg (() :: ·) (replicate_unit_eq rest)

private def decodeCapLedRecWords : List Nat → Option CapLedRec
  | raw :: spentLen :: height :: grantWords =>
    (parseGrantPairs grantWords).map fun gs => ⟨raw, List.replicate spentLen (), gs, height⟩
  | _ => none

private theorem decodeCapLedRecWords_encode (d : CapLedRec) :
    decodeCapLedRecWords (encodeCapLedRecWords d) = some d := by
  cases d with
  | mk raw spent grants height =>
    simp [encodeCapLedRecWords, decodeCapLedRecWords, parseGrantPairs_flatMap, replicate_unit_eq]

private def encodeCapJEv : CapJEv → Bytes
  | .world w => 10 :: encodeNatLE w
  | .dispatch buyer ⟨false, ()⟩ => [11, encodeBoolByte buyer]
  | .dispatch _ ⟨true, x⟩ => nomatch x
  | .abandon buyer ⟨false, ()⟩ => [12, encodeBoolByte buyer]
  | .abandon _ ⟨true, x⟩ => nomatch x
  | .own buyer (.base (.respond ⟨false, (), ()⟩)) => [13, encodeBoolByte buyer]
  | .own _ (.base (.respond ⟨true, x, _⟩)) => nomatch x
  | .own buyer (.base (.world d)) => 14 :: encodeBoolByte buyer :: encodeNatList (encodeCapLedRecWords d)
  | .own buyer (.base (.dispatch ⟨false, ()⟩)) => [15, encodeBoolByte buyer]
  | .own _ (.base (.dispatch ⟨true, x⟩)) => nomatch x
  | .own buyer (.base (.abandon ⟨false, ()⟩)) => [16, encodeBoolByte buyer]
  | .own _ (.base (.abandon ⟨true, x⟩)) => nomatch x
  | .own _ (.base (.replan h _ _)) => nomatch h
  | .own _ (.choose _ _ h _ _) => nomatch h
  | .own _ (.advance h) => nomatch h

private def decodeCapJEv : Bytes → Option CapJEv
  | 10 :: rest => some (.world (decodeNatLE rest))
  | [11, b] => (decodeBoolByte b).map fun buyer => .dispatch buyer ⟨false, ()⟩
  | [12, b] => (decodeBoolByte b).map fun buyer => .abandon buyer ⟨false, ()⟩
  | [13, b] => (decodeBoolByte b).map fun buyer => .own buyer (.base (.respond ⟨false, (), ()⟩))
  | 14 :: b :: rest =>
    match decodeBoolByte b, decodeNatListFuel (rest.length + 1) rest with
    | some buyer, some (words, []) =>
      (decodeCapLedRecWords words).map fun d => .own buyer (.base (.world d))
    | _, _ => none
  | [15, b] => (decodeBoolByte b).map fun buyer => .own buyer (.base (.dispatch ⟨false, ()⟩))
  | [16, b] => (decodeBoolByte b).map fun buyer => .own buyer (.base (.abandon ⟨false, ()⟩))
  | _ => none

private theorem decodeCapJEv_encodeCapJEv (ev : CapJEv) : decodeCapJEv (encodeCapJEv ev) = some ev := by
  cases ev with
  | world w => simp [encodeCapJEv, decodeCapJEv]
  | dispatch buyer o =>
    rcases o with ⟨b, op⟩
    cases b with
    | false => cases op; simp [encodeCapJEv, decodeCapJEv]
    | true => nomatch op
  | abandon buyer o =>
    rcases o with ⟨b, op⟩
    cases b with
    | false => cases op; simp [encodeCapJEv, decodeCapJEv]
    | true => nomatch op
  | own buyer cev =>
    cases cev with
    | choose _ _ h _ _ => nomatch h
    | advance h => nomatch h
    | base bev =>
      cases bev with
      | replan h _ _ => nomatch h
      | respond ent =>
        rcases ent with ⟨b, op, r⟩
        cases b with
        | false => cases op; cases r; simp [encodeCapJEv, decodeCapJEv]
        | true => nomatch op
      | dispatch o =>
        rcases o with ⟨b, op⟩
        cases b with
        | false => cases op; simp [encodeCapJEv, decodeCapJEv]
        | true => nomatch op
      | abandon o =>
        rcases o with ⟨b, op⟩
        cases b with
        | false => cases op; simp [encodeCapJEv, decodeCapJEv]
        | true => nomatch op
      | world d =>
        have hlen : (encodeCapLedRecWords d).length + 1 ≤
            (encodeNatList (encodeCapLedRecWords d)).length + 1 := by
          have : ∀ l : List Nat, l.length ≤ (encodeNatList l).length := by
            intro l; induction l with
            | nil => simp [encodeNatList]
            | cons _ tl ih => simp only [encodeNatList, List.length_cons, List.length_append]; omega
          have := this (encodeCapLedRecWords d)
          omega
        have hdec := decodeNatListFuel_encodeNatList (encodeCapLedRecWords d) []
          ((encodeNatList (encodeCapLedRecWords d)).length + 1) hlen
        rw [List.append_nil] at hdec
        change decodeCapJEv (14 :: encodeBoolByte buyer :: encodeNatList (encodeCapLedRecWords d)) =
          some (.own buyer (.base (.world d)))
        simp only [decodeCapJEv, decodeBoolByte_encodeBoolByte, hdec]
        rw [decodeCapLedRecWords_encode d]
        rfl

def capCodec : EventWireCodec CapJEv where
  encodeEv := encodeCapJEv
  decodeEv := decodeCapJEv
  decode_encodeEv := decodeCapJEv_encodeCapJEv

/-- Small 200-byte block capacity so 2 committed `OBL1` frames (~170 bytes each) rotate segments! -/
def testSegCap : Nat := 200
theorem testSegCap_pos : 0 < testSegCap := by decide

def testDisk₀ : SegmentedDState capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false :=
  SegmentedDState.init capLedger testSegCap testSegCap_pos capJ₀

def stepCapDiskFor (Hb : Bytes → Bytes) :=
  segmentedStep capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth) (fun _ => capCtl)
    Hb capCodec capJ₀

def stepCapDisk := stepCapDiskFor sampleIdentityHash

def traceCapDisk :=
  runSegmentedTrace capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth) (fun _ => capCtl)
    sampleIdentityHash capCodec capJ₀

def aliceEv : CapJEv := .dispatch false ⟨false, ()⟩
def bobEv : CapJEv := .dispatch true ⟨false, ()⟩

/-- Alice's dispatch commits token `()` at epoch 0; Bob's subsequent dispatch is refused naming Alice! -/
theorem alice_jrun_and_bob_refused :
    ∃ J₁,
      jrun capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth) (fun _ => capCtl)
        capJ₀ aliceEv = .ok J₁ ∧
      jrun capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth) (fun _ => capCtl)
        J₁ bobEv = .error (.taken () false 0) :=
  ⟨_, rfl, rfl⟩

/-- End-to-end physical segment rollover across `testSegCap = 200`, 50-byte torn-tail crash,
    dirty-tail submit refusal, segment-truncating recovery idempotence, post-recovery double-spend
    & double-expose refusals, and concrete `segmented_exposed_once` for any hash `Hb`! -/
theorem segmented_rollover_crash_recovery_e2e_for (Hb : Bytes → Bytes) :
    ∃ (disk₁ disk₂ crashed recovered :
        SegmentedDState capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false)
      (r_bob : Record),
      stepCapDiskFor Hb testDisk₀ (.submit aliceEv) = .ok disk₁ ∧
      stepCapDiskFor Hb disk₁ (.expose 0) = .ok disk₂ ∧
      2 ≤ disk₂.segments.length ∧
      (∃ seg0 rest, disk₂.segments = seg0 :: rest ∧ seg0.length = 200 ∧ rest ≠ []) ∧
      stepCapDiskFor Hb disk₂ (.tornCrash r_bob 50) = .ok crashed ∧
      crashed.mem = none ∧
      stepCapDiskFor Hb crashed (.submit (.world 1)) = .error .dirtyTailNeedsRecovery ∧
      stepCapDiskFor Hb crashed .recover = .ok recovered ∧
      recovered = disk₂ ∧
      recoverJournalAndOutbox Hb capCodec recovered = some ([aliceEv], [0]) ∧
      stepCapDiskFor Hb recovered (.submit bobEv) = .error (.host (.joint (.taken () false 0))) ∧
      stepCapDiskFor Hb recovered (.expose 0) = .error (.host (.exposed 0)) ∧
      (∀ {n : Nat}, n ∈ ([0] : List Nat) → ∀ {buyer : Bool} {o : Σ b, capSig.Op b},
        ([aliceEv] : List CapJEv)[n]? = some (.dispatch buyer o) →
        capSpec.consumes o.2 = some () → n = 0 ∧ buyer = false) := by
  obtain ⟨J₁, hjAlice, hjBob⟩ := alice_jrun_and_bob_refused
  have h256_pos : 0 < 256 := by decide
  have hgen_lt : genesisSentinel < Obend.Vault.Log.bound := by
    change 0 < 256 ^ 32
    exact Nat.pow_pos h256_pos
  have hlt_pow4 : ∀ {n : Nat}, n < 256 → n < 256 ^ 4 := fun {n} hn =>
    Nat.lt_of_lt_of_le hn (by decide)
  have hpay₁_eq : encodeDiskEntry capCodec (.journalAppend aliceEv) = [1, 11, 0] := by
    simp [encodeDiskEntry, capCodec, aliceEv, encodeCapJEv, encodeBoolByte]
  have hpay₁_lt : (encodeDiskEntry capCodec (.journalAppend aliceEv)).length < 256 ^ 4 :=
    hlt_pow4 (by rw [hpay₁_eq]; decide)
  generalize hrec₁_def : mkChainedRecord Hb genesisSentinel
    (encodeDiskEntry capCodec (.journalAppend aliceEv)) = rec₁
  have hrec₁_wf : rec₁.WF Hb :=
    hrec₁_def ▸ mkChainedRecord_wf Hb hgen_lt hpay₁_lt
  have hrec₁_prev : rec₁.receipt.prevHash = genesisSentinel := by
    rw [← hrec₁_def, mkChainedRecord_prevHash]
  have hrec₁_pay : rec₁.payload = encodeDiskEntry capCodec (.journalAppend aliceEv) := by
    rw [← hrec₁_def, mkChainedRecord_payload]
  generalize hsegs₁_def :
    appendSegmentedBytes testSegCap testSegCap_pos [] (encodeRecord Hb rec₁) = segs₁
  let disk₁ : SegmentedDState capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false :=
    ⟨testSegCap, testSegCap_pos, segs₁, some J₁⟩
  have hStep₁ : stepCapDiskFor Hb testDisk₀ (.submit aliceEv) = .ok disk₁ := by
    unfold stepCapDiskFor segmentedStep testDisk₀ SegmentedDState.init
    simp only [List.flatten_nil, Obend.Vault.Log.parseFrom_nil, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hpay₁_lt, hjAlice, Obend.Vault.Log.lastHash, hrec₁_def, hsegs₁_def]
    rfl
  have hSim₀ := segmentedSimInv_init capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth)
    (fun _ => capCtl) Hb capCodec testSegCap testSegCap_pos capJ₀
  obtain ⟨s₁, hs₁, hSim₁⟩ := segmentedStep_refines_durable capLedger capBaseView (fun _ => capSpec)
    (fun _ => capAuth) (fun _ => capCtl) Hb capCodec capJ₀ (.submit aliceEv) hSim₀ hStep₁
  have hs₁_eq : s₁ = ⟨[aliceEv], [], some J₁⟩ := by
    unfold hstep DState.init SegmentedHEvent.toAbstract at hs₁
    simp only [hjAlice, List.nil_append, Except.ok.injEq] at hs₁
    exact hs₁.symm
  subst hs₁_eq
  have hLink₁ : Obend.Vault.Log.Linked Hb genesisSentinel [rec₁] := ⟨hrec₁_prev, trivial⟩
  have hWf₁ : ∀ r ∈ ([rec₁] : List Record), r.WF Hb := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hrec₁_wf
  have hflat₁ : disk₁.segments.flatten = encodeAll Hb [rec₁] := by
    show segs₁.flatten = _; rw [← hsegs₁_def, appendSegmentedBytes_flatten]; simp [encodeAll]
  have hParse₁ : parseFrom Hb genesisSentinel disk₁.segments.flatten = ([rec₁], [], none) := by
    rw [hflat₁, ← List.append_nil (encodeAll Hb [rec₁]),
      Obend.Vault.Log.parseFrom_encodeAll Hb [rec₁] genesisSentinel hLink₁ hWf₁ []]
    simp [Obend.Vault.Log.parseFrom_nil]
  have hDec₁ : decodeDurableRecords capCodec [rec₁] = some ([aliceEv], []) := by
    simp [decodeDurableRecords, foldDiskEntries, hrec₁_pay, decodeDiskEntry_encodeDiskEntry]
  have hpay₂_eq : encodeDiskEntry capCodec (.outboxExpose 0) = [2] := by
    simp [encodeDiskEntry, encodeNatLE]
  have hpay₂_lt : (encodeDiskEntry capCodec (.outboxExpose 0)).length < 256 ^ 4 :=
    hlt_pow4 (by rw [hpay₂_eq]; decide)
  generalize hrec₂_def : mkChainedRecord Hb
    (lastHash Hb genesisSentinel [rec₁])
    (encodeDiskEntry capCodec (.outboxExpose 0)) = rec₂
  have hrec₂_wf : rec₂.WF Hb :=
    hrec₂_def ▸ mkChainedRecord_wf Hb
      (Obend.Vault.Log.lastHash_lt Hb hgen_lt [rec₁]) hpay₂_lt
  have hrec₂_prev : rec₂.receipt.prevHash = Obend.Vault.Log.Hr Hb rec₁.receipt := by
    rw [← hrec₂_def, mkChainedRecord_prevHash]
    simp only [Obend.Vault.Log.lastHash]
  have hrec₂_pay : rec₂.payload = encodeDiskEntry capCodec (.outboxExpose 0) := by
    rw [← hrec₂_def, mkChainedRecord_payload]
  generalize hsegs₂_def :
    appendSegmentedBytes testSegCap testSegCap_pos segs₁ (encodeRecord Hb rec₂) = segs₂
  let disk₂ : SegmentedDState capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false :=
    ⟨testSegCap, testSegCap_pos, segs₂, some J₁⟩
  have hStep₂ : stepCapDiskFor Hb disk₁ (.expose 0) = .ok disk₂ := by
    unfold stepCapDiskFor segmentedStep
    rw [hParse₁]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hDec₁,
      List.getElem?_cons_zero, aliceEv, List.not_mem_nil, hpay₂_lt, hrec₂_def]
    dsimp only [disk₁, disk₂]
    rw [hsegs₂_def]
  have hCross : testSegCap < (disk₁.segments.flatten ++ encodeRecord Hb rec₂).length := by
    rw [hflat₁]
    simp only [encodeAll, List.append_nil, List.length_append, Obend.Vault.Log.encodeRecord_length,
      hrec₁_pay, hrec₂_pay, hpay₁_eq, hpay₂_eq, List.length_cons, List.length_nil, testSegCap]
    omega
  have ⟨hLen₂, hRot₂⟩ := segmented_append_rotates_across_boundary testSegCap testSegCap_pos
    disk₁.segments (encodeRecord Hb rec₂) hCross
  rw [show disk₁.segments = segs₁ from rfl, hsegs₂_def] at hLen₂ hRot₂
  obtain ⟨s₂, hs₂, hSim₂⟩ := segmentedStep_refines_durable capLedger capBaseView (fun _ => capSpec)
    (fun _ => capAuth) (fun _ => capCtl) Hb capCodec capJ₀ (.expose 0) hSim₁ hStep₂
  have hs₂_eq : s₂ = ⟨[aliceEv], [0], some J₁⟩ := by
    unfold hstep SegmentedHEvent.toAbstract at hs₂
    simp only [List.getElem?_cons_zero, aliceEv, List.not_mem_nil, ↓reduceIte, List.nil_append,
      Except.ok.injEq] at hs₂
    exact hs₂.symm
  subst hs₂_eq
  have hpayBob_eq : encodeDiskEntry capCodec (.journalAppend bobEv) = [1, 11, 1] := by
    simp [encodeDiskEntry, capCodec, bobEv, encodeCapJEv, encodeBoolByte]
  have hpayBob_lt : (encodeDiskEntry capCodec (.journalAppend bobEv)).length < 256 ^ 4 :=
    hlt_pow4 (by rw [hpayBob_eq]; decide)
  generalize hrbob_def : mkChainedRecord Hb
    (lastHash Hb genesisSentinel [rec₁, rec₂])
    (encodeDiskEntry capCodec (.journalAppend bobEv)) = r_bob
  have hr_bob_wf : r_bob.WF Hb :=
    hrbob_def ▸ mkChainedRecord_wf Hb
      (Obend.Vault.Log.lastHash_lt Hb hgen_lt [rec₁, rec₂]) hpayBob_lt
  have hrbob_pay : r_bob.payload = encodeDiskEntry capCodec (.journalAppend bobEv) := by
    rw [← hrbob_def, mkChainedRecord_payload]
  have hk50 : 50 < (encodeRecord Hb r_bob).length := by
    rw [Obend.Vault.Log.encodeRecord_length, hrbob_pay, hpayBob_eq]
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨crashed, recovered, hCrash, hRec, hRecEq, hRecDisk⟩ :=
    segmented_torn_crash_recover_idempotent capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth)
      (fun _ => capCtl) Hb capCodec capJ₀ hSim₂ rfl r_bob hr_bob_wf 50 hk50
  have hLink₂ : Obend.Vault.Log.Linked Hb genesisSentinel [rec₁, rec₂] :=
    ⟨hrec₁_prev, hrec₂_prev, trivial⟩
  have hWf₂ : ∀ r ∈ ([rec₁, rec₂] : List Record), r.WF Hb := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hrec₁_wf
    · exact hrec₂_wf
  have hflat₂ : disk₂.segments.flatten = encodeAll Hb [rec₁, rec₂] := by
    show segs₂.flatten = _
    rw [← hsegs₂_def, appendSegmentedBytes_flatten, show segs₁.flatten = disk₁.segments.flatten from rfl, hflat₁]
    simp [encodeAll]
  have hParse₂ : parseFrom Hb genesisSentinel disk₂.segments.flatten = ([rec₁, rec₂], [], none) := by
    rw [hflat₂, ← List.append_nil (encodeAll Hb [rec₁, rec₂]),
      Obend.Vault.Log.parseFrom_encodeAll Hb [rec₁, rec₂] genesisSentinel hLink₂ hWf₂ []]
    simp [Obend.Vault.Log.parseFrom_nil]
  have hDec₂ : decodeDurableRecords capCodec [rec₁, rec₂] = some ([aliceEv], [0]) := by
    simp [decodeDurableRecords, foldDiskEntries, hrec₁_pay, hrec₂_pay, decodeDiskEntry_encodeDiskEntry]
  have hCrashEq : crashed = ⟨testSegCap, testSegCap_pos,
      split testSegCap testSegCap_pos
        (encodeAll Hb [rec₁, rec₂] ++ (encodeRecord Hb r_bob).take 50),
      none⟩ := by
    have hc := hCrash
    obtain ⟨hw0, hw1, hw2, hw3, hw4⟩ := hr_bob_wf
    unfold segmentedStep at hc
    rw [hParse₂] at hc
    simp only [hw0, hw1, hw2, hw3, hw4, hk50, and_self, ↓reduceIte, Except.ok.injEq] at hc
    exact hc.symm
  have hDirtyRefused : stepCapDiskFor Hb crashed (.submit (.world 1)) = .error .dirtyTailNeedsRecovery := by
    rw [hCrashEq]
    unfold stepCapDiskFor segmentedStep
    dsimp only
    rw [Obend.Vault.SegmentLog.split_join,
      Obend.Vault.Log.parseFrom_encodeAll Hb [rec₁, rec₂] genesisSentinel hLink₂ hWf₂]
    have hne50 : (encodeRecord Hb r_bob).take 50 ≠ [] := by
      intro h; have := congrArg List.length h
      rw [List.length_take] at this; simp only [List.length_nil] at this; omega
    have htorn50 : Obend.Vault.Log.parseOne Hb
        (some (lastHash Hb genesisSentinel [rec₁, rec₂]))
        ((encodeRecord Hb r_bob).take 50) = .error .torn :=
      Obend.Vault.Log.parseOne_torn Hb hr_bob_wf (List.take_append_drop 50 _)
        (by rw [Ne, List.drop_eq_nil_iff]; omega)
    rw [Obend.Vault.Log.parseFrom_error Hb hne50 htorn50]
    have hnot_emp : ((encodeRecord Hb r_bob).take 50).isEmpty = false := by
      cases h : ((encodeRecord Hb r_bob).take 50).isEmpty with
      | false => rfl
      | true => exact absurd (List.isEmpty_iff.mp h) hne50
    simp [hnot_emp]
  have hBobRefused : stepCapDiskFor Hb recovered (.submit bobEv) = .error (.host (.joint (.taken () false 0))) := by
    rw [hRecEq]
    unfold stepCapDiskFor segmentedStep
    rw [hParse₂]
    dsimp only [disk₂]
    simp [hpayBob_lt, hjBob]
  have hReexposeRefused : stepCapDiskFor Hb recovered (.expose 0) = .error (.host (.exposed 0)) := by
    rw [hRecEq]
    unfold stepCapDiskFor segmentedStep
    rw [hParse₂]
    dsimp only [disk₂]
    simp [hDec₂, aliceEv]
  have hReachRec : SegmentedReachable capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth)
      (fun _ => capCtl) Hb capCodec testSegCap testSegCap_pos capJ₀ recovered :=
    .step .recover
      (.step (.tornCrash r_bob 50)
        (.step (.expose 0) (.step (.submit aliceEv) .init hStep₁) hStep₂)
        hCrash)
      hRec
  refine ⟨disk₁, disk₂, crashed, recovered, r_bob, hStep₁, hStep₂, hLen₂, hRot₂,
    hCrash, by rw [hCrashEq], hDirtyRefused, hRec, hRecEq, hRecDisk, hBobRefused, hReexposeRefused, ?_⟩
  intro n hn buyer o hio ht
  exact segmented_exposed_once capLedger capBaseView (fun _ => capSpec) (fun _ => capAuth)
    (fun _ => capCtl) Hb capCodec testSegCap testSegCap_pos rfl rfl
    hReachRec hRecDisk hn List.mem_cons_self hio rfl ht rfl

/-- Instantiation at `sampleIdentityHash`. -/
theorem segmented_rollover_crash_recovery_e2e :
    ∃ (disk₁ disk₂ crashed recovered :
        SegmentedDState capLedger capSig capHole (fun _ => Unit) Unit Unit Empty Empty false)
      (r_bob : Record),
      stepCapDisk testDisk₀ (.submit aliceEv) = .ok disk₁ ∧
      stepCapDisk disk₁ (.expose 0) = .ok disk₂ ∧
      2 ≤ disk₂.segments.length ∧
      (∃ seg0 rest, disk₂.segments = seg0 :: rest ∧ seg0.length = 200 ∧ rest ≠ []) ∧
      stepCapDisk disk₂ (.tornCrash r_bob 50) = .ok crashed ∧
      crashed.mem = none ∧
      stepCapDisk crashed (.submit (.world 1)) = .error .dirtyTailNeedsRecovery ∧
      stepCapDisk crashed .recover = .ok recovered ∧
      recovered = disk₂ ∧
      recoverJournalAndOutbox sampleIdentityHash capCodec recovered = some ([aliceEv], [0]) ∧
      stepCapDisk recovered (.submit bobEv) = .error (.host (.joint (.taken () false 0))) ∧
      stepCapDisk recovered (.expose 0) = .error (.host (.exposed 0)) ∧
      (∀ {n : Nat}, n ∈ ([0] : List Nat) → ∀ {buyer : Bool} {o : Σ b, capSig.Op b},
        ([aliceEv] : List CapJEv)[n]? = some (.dispatch buyer o) →
        capSpec.consumes o.2 = some () → n = 0 ∧ buyer = false) :=
  segmented_rollover_crash_recovery_e2e_for sampleIdentityHash

-- ============================================================================
-- 2. Capability-Carrying `.perform` Plans (`Ty.isTransferable` + `CapTable`)
-- ============================================================================

def yieldPlanTy : Ty :=
  .variant
    (.field "delegateEndpoint"
      (.field "seL4Badge" (.custody 7)
        (.field "sturdyRef" (.custody 11)
          (.field "timeoutTicks" .natural .emptyRow)))
      (.field "ping" .boolean .emptyRow))

def yieldPlanVal : TVal :=
  .variant "delegateEndpoint"
    (.record
      [ ("seL4Badge", .cap 101 7)
      , ("sturdyRef", .cap 202 11)
      , ("timeoutTicks", .natural 500) ])

def yieldCustodyEnv : CustodyEnv :=
  ⟨[⟨101, 7, [0xde, 0xad]⟩, ⟨202, 11, [0xbe, 0xef]⟩]⟩

def checkCapTransferRoundtrip : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 99 yieldCustodyEnv yieldPlanVal with
  | .ok (wire, frame) =>
    match DataWire.ofData? wire.toData with
    | some wireDecoded =>
      match rehydrate sampleIdentityHash sampleSealKey 9 wireDecoded frame with
      | .ok (v', env') =>
        v' == yieldPlanVal && env' == yieldCustodyEnv && frame.table.entries.length == 2
      | .error _ => false
    | none => false
  | .error _ => false

theorem cap_transfer_roundtrip_passes :
    yieldPlanTy.isTransferablePlan = true ∧
    yieldPlanTy.isPlan = false ∧
    TVal.conforms yieldPlanVal yieldPlanTy = true ∧
    checkCapTransferRoundtrip = true :=
  ⟨by decide, by decide, by decide, by decide⟩

def forgedIndexRejected : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 99 yieldCustodyEnv yieldPlanVal with
  | .ok (_, frame) =>
    match rehydrate sampleIdentityHash sampleSealKey 9 (.sealedCap 2 7) frame with
    | .error (.forgedCapIndex 2) => true
    | _ => false
  | .error _ => false

def tamperedSealRejected : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 99 yieldCustodyEnv yieldPlanVal with
  | .ok (wire, frame) =>
    let tampered := { frame with nonce := frame.nonce + 1 }
    match rehydrate sampleIdentityHash sampleSealKey 9 wire tampered with
    | .error .unsealedFrame => true
    | _ => false
  | .error _ => false

theorem test_forged_and_tampered_refused :
    forgedIndexRejected = true ∧
    tamperedSealRejected = true ∧
    dehydrate sampleIdentityHash sampleSealKey 9 1 ⟨[⟨101, 7, [1]⟩]⟩
      (.record [("a", .cap 101 7), ("b", .cap 101 7)]) = .error (.missingOrDuplicateSlot 101) ∧
    dehydrate sampleIdentityHash sampleSealKey 9 1 yieldCustodyEnv (.natural 0) = .error (.droppedCustody 101) :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- A seal made by one authority must fail under a different host key. -/
def forgedAuthorityRejected : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 99 yieldCustodyEnv yieldPlanVal with
  | .error _ => false
  | .ok (wire, frame) =>
    rehydrate sampleIdentityHash (sampleSealKey.set! 0 0x5b) 9 wire frame == .error .unsealedFrame

def staleEpochRejected : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 99 yieldCustodyEnv yieldPlanVal with
  | .error _ => false
  | .ok (wire, frame) =>
    rehydrate sampleIdentityHash sampleSealKey 10 wire frame == .error .unsealedFrame

/-- Even a correctly sealed table cannot restore two capabilities in one slot. -/
def duplicateSlotsRejected : Bool :=
  let tbl : CapTable := ⟨[⟨0, ⟨101, 7, [1]⟩⟩, ⟨1, ⟨101, 8, [2]⟩⟩]⟩
  let frame : CapSealFrame := ⟨99, 9, tbl,
    computeCapFrameSeal sampleIdentityHash sampleSealKey 9 99 tbl⟩
  rehydrate sampleIdentityHash sampleSealKey 9
    (.record [("a", .sealedCap 0 7), ("b", .sealedCap 1 8)]) frame ==
      .error (.missingOrDuplicateSlot 101)

theorem authority_epoch_slots_refused :
    forgedAuthorityRejected = true ∧ staleEpochRejected = true ∧ duplicateSlotsRejected = true := by
  decide

#tooth authority_epoch_slots_refused by mutation
  Obend.Run.VaultDurableBridge.capFramePreimage := fun _ epoch nonce tbl =>
    Obend.Crypto.leb128 epoch.toNat ++ encodeCapTableBytes nonce tbl

#tooth authority_epoch_slots_refused by mutation
  Obend.Run.VaultDurableBridge.CapSealFrame.sealValid := fun Hb key _ frame =>
    decide (key.size = 32 ∧ frame.sealBytes =
      computeCapFrameSeal Hb key frame.epoch frame.nonce frame.table)

#tooth Obend.Run.VaultDurableBridge.rehydrate_restores_nodup_slots by mutation
  Obend.Run.VaultDurableBridge.duplicateSlot := fun _ => none

-- Full-width natural identifiers have distinct encodings past the former 64-bit wrap boundary.
example : encodeCapTableBytes 0 ⟨[⟨0, ⟨1, 2, []⟩⟩]⟩ ≠
    encodeCapTableBytes 0 ⟨[⟨0, ⟨1 + 2^64, 2, []⟩⟩]⟩ := by decide

-- ============================================================================
-- 3. `Genealogy.Habitat` Governed by 3-Tier `SpecNeg` + $B$-Corrigibility + `PcaEnvelope`
-- ============================================================================

def demoGateMetaC : Gate Obend.Judge.Genealogy.record :=
  { name := "metaC"
    formats := ["write@1", "revert@1"]
    floors := [.home 3, .cap "a" 100, .cap "b" 80, .cap "c" 40]
    methods :=
      [ ("write@1", .home 3, .eval .kernel)
      , ("write@1", .cap "a" 100, .eval .kernel)
      , ("write@1", .cap "b" 80, .eval .kernel)
      , ("write@1", .cap "c" 40, .eval .kernel)
      , ("revert@1", .home 3, .lemma)
      , ("revert@1", .cap "a" 100, .lemma)
      , ("revert@1", .cap "b" 80, .lemma)
      , ("revert@1", .cap "c" 40, .lemma) ]
    basis := [.kernel] }

/-- Attempted unconstitutional meta-amendment that drops Tier-0 `.home 3` bedrock — refused! -/
theorem illegal_bedrock_drop_refused :
    checkMetaAmendment demoStack0 [.cap "a" 100] demoGateSpecB [] = false := by decide

def demoActor (stepIdx : Nat) (_st : ConstitutionalStack Obend.Judge.Genealogy.record) :
    String × ConstitutionalMove Obend.Judge.Genealogy.record × String :=
  match stepIdx with
  | 0 => ("agent", .act (.write "a" 40), "silent")
  | 1 => ("agent", .act (.write "a" 75), "silent")
  | 2 => ("negotiator", .negotiateSpec demoGateSpecB [], "drop cap a 50, add cap b 80")
  | 3 => ("agent", .act (.write "a" 75), "now legal under negotiated specB")
  | 4 => ("assembly", .amendMeta [.home 3, .cap "a" 100, .cap "b" 80] demoGateMetaC [], "amend meta")
  | _ => ("operator", .act .revert, "")

def stackAt5 : ConstitutionalStack Obend.Judge.Genealogy.record :=
  runConstitutional Exec.faithful demoActor demoStack0 5

/-- Lateral Tier-2 negotiation unlocked `a := 75` at step 3, Tier-1 meta-amendment succeeded at
    step 4, and Tier-0 `.home 3` bedrock holds throughout! -/
theorem constitutional_run_e2e :
    stackAt5.state.store.get "a" = 75 ∧
    stackAt5.metaFloors = [.home 3, .cap "a" 100, .cap "b" 80] ∧
    Obend.Judge.Genealogy.record.holds (.home 3) stackAt5.state :=
  ⟨by decide, by decide, by decide⟩

/-- Instantiate `habitat_bedrock_is_eternal` over `demoStack0` for ALL `n : Nat`! -/
theorem demo_habitat_bedrock_eternal (n : Nat) :
    Obend.Judge.Genealogy.record.holds (.home 3)
      (runConstitutional Exec.faithful demoActor demoStack0 n).state ∧
    Obend.Judge.Genealogy.admits Exec.faithful
      (runConstitutional Exec.faithful demoActor demoStack0 n).specGate
      (runConstitutional Exec.faithful demoActor demoStack0 n).state
      Obend.Judge.Genealogy.record.revert = true := by
  have hAll := habitat_bedrock_is_eternal Exec.faithful demoActor demoStack0
    rfl
    (by intro φ hφ; simp [demoStack0] at hφ ⊢; exact .inl hφ)
    (by intro φ hφ; simp [demoStack0, demoGateSpecA] at hφ ⊢; exact hφ.elim .inl (.inr ∘ .inl))
    (by intro φ hφ; simp [demoStack0, demoGateSpecA] at hφ; rcases hφ with rfl | rfl | rfl <;> decide)
    (fun t _ => Exec.faithful_holds t)
    n
    (fun t _ => Exec.faithful_holds t)
  exact ⟨hAll.2.1 (.home 3) List.mem_cons_self, hAll.2.2⟩

/-- Concrete `MaxPol` + `override_iff_burned_bridge` + `PcaEnvelope` + `VoluntaryTestimony` checks! -/
def bridgeStep (s a : Nat) : Nat := if a == 0 then s - 1 else s + a
def bridgeRecov (_ : Nat) : Nat := 0
def bridgeHome (s : Nat) : Prop := s = 0
instance : DecidablePred bridgeHome := fun s => inferInstanceAs (Decidable (s = 0))

theorem bridgeHome_parked : HomeRecovParked bridgeStep bridgeRecov bridgeHome := by
  intro s hs; subst hs; rfl

theorem maxpol_and_pca_e2e :
    (enveloped (maxPol bridgeStep (CWithin bridgeStep bridgeRecov bridgeHome 3))
        bridgeRecov (fun _ => 1) 2 = 1 ∧
     enveloped (maxPol bridgeStep (CWithin bridgeStep bridgeRecov bridgeHome 3))
        bridgeRecov (fun _ => 2) 2 = 0) ∧
    (let basePol : Policy Nat Nat := fun _ a => a == 0
     let certOk : Certifier Nat Nat Nat := fun s a r => r * r == s + a
     embodiedTurnSelect basePol certOk (fun _ => 0) (fun _ => (5, none)) 4 = 0 ∧
     embodiedTurnSelect basePol certOk (fun _ => 0) (fun _ => (5, some 3)) 4 = 5 ∧
     embodiedTurnSelect basePol certOk (fun _ => 0) (fun _ => (5, some 2)) 4 = 0) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

example (ctrl : Nat → Nat) :
    enveloped (maxPol bridgeStep (CWithin bridgeStep bridgeRecov bridgeHome 3)) bridgeRecov ctrl 2 ≠ ctrl 2 ↔
      ¬ CWithin bridgeStep bridgeRecov bridgeHome 3 (bridgeStep 2 (ctrl 2)) :=
  override_iff_burned_bridge 3 ctrl bridgeHome_parked ⟨2, by omega, rfl⟩

-- ============================================================================
-- 4. Universal `#tooth` Mutation Verification & `#print axioms` Audit
-- ============================================================================

#tooth Obend.Run.VaultDurableBridge.rehydrate_dehydrate_roundtrip by mutation
  Obend.Run.VaultDurableBridge.CapSealFrame.sealValid := fun _ _ _ _ => false

#tooth Obend.Run.VaultDurableBridge.forged_cap_index_refused by mutation
  Obend.Run.VaultDurableBridge.rehydrateVal := fun _ _ avail => .ok (.natural 0, avail, [])

#tooth Obend.Judge.SvenvsCorrigibility.habitat_bedrock_is_eternal by mutation
  Obend.Judge.SvenvsCorrigibility.floorsContainAll := fun _ _ _ => true

#tooth Obend.Judge.SvenvsCorrigibility.pca_enveloped_safe by mutation
  Obend.Judge.SvenvsCorrigibility.PcaEnvelope.select := fun _ pcc s => (pcc s).1

#print axioms Obend.Core.Ty.custody_isTransferable_not_isData
#print axioms Obend.Core.Ty.isTransferable_forbids_higher_order
#print axioms Obend.Run.VaultDurableBridge.segmented_append_rotates_across_boundary
#print axioms Obend.Run.VaultDurableBridge.parseFrom_committed_with_torn_frame
#print axioms Obend.Run.VaultDurableBridge.segmentedStep_refines_durable
#print axioms Obend.Run.VaultDurableBridge.segmented_torn_crash_recover_idempotent
#print axioms Obend.Run.VaultDurableBridge.segmented_exposed_once
#print axioms Obend.Run.VaultDurableBridge.rehydrate_dehydrate_roundtrip
#print axioms Obend.Run.VaultDurableBridge.transfer_conserves_custody_exact
#print axioms Obend.Run.VaultDurableBridge.forged_cap_index_refused
#print axioms Obend.Judge.SvenvsCorrigibility.safe_weakening_iff
#print axioms Obend.Judge.SvenvsCorrigibility.authority_monotone
#print axioms Obend.Judge.SvenvsCorrigibility.maxpol_transparent_run
#print axioms Obend.Judge.SvenvsCorrigibility.override_iff_burned_bridge
#print axioms Obend.Judge.SvenvsCorrigibility.angelic_recoverability_insufficient
#print axioms Obend.Judge.SvenvsCorrigibility.self_mod_preserves_latency_B
#print axioms Obend.Judge.SvenvsCorrigibility.disjoint_homes_empty_floor
#print axioms Obend.Judge.SvenvsCorrigibility.spec_negotiation_safe
#print axioms Obend.Judge.SvenvsCorrigibility.meta_amendment_safe
#print axioms Obend.Judge.SvenvsCorrigibility.bedrock_is_eternal
#print axioms Obend.Judge.SvenvsCorrigibility.habitat_bedrock_is_eternal
#print axioms Obend.Judge.SvenvsCorrigibility.pca_enveloped_safe
#print axioms Obend.Judge.SvenvsCorrigibility.pca_strictly_subsumes_static_shield
#print axioms Obend.Judge.SvenvsCorrigibility.nondisclosure_is_inert

end Obend.Tests.DurableAndSvenvsTest

end

-- Temporary compact diagnostics for the broker's bounded output tail.
run_cmd do
  let errors := (← get).messages.toList.filter (fun msg => msg.severity == .error)
  for msg in errors do
    let flat := (← msg.data.toString).replace "\n" " "
    Lean.logError m!"prior error line {msg.pos.line}: {String.ofList (flat.toList.take 700)}"
