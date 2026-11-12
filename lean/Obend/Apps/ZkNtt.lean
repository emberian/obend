module
/-
# Obend.Apps.ZkNtt — Flagship App #4: Goldilocks ZK-NTT butterfly + multilinear sumcheck co-processor

Elaborates the 4-module Goldilocks `.obend` hierarchy (`apps/zk-ntt/`): `GoldilocksField.obend`
(the prime $p = 2^{64} - 2^{32} + 1$, canonical `fieldAdd`/`fieldSub`, the 32-bit-limb `fieldMul`
with the shift/mask 128-to-64 reduction), `NttButterflyRadix2.obend`, `SumcheckRoundPoly.obend`
(round accumulators, folding, and `transcriptAbsorb`, the Fiat–Shamir step) and `ZkNttSumcheckTop.obend`.

What is proved: the `.obend` cross-module values (`zk_ntt_workbook_eval_sound`), the Goldilocks
congruences, `goldilocksReduce128Spec_sound` (for every `lo, hi < 2^64` the shift/mask
reduction the hardware uses equals `(lo + 2^64 * hi) % p` and is canonical), `glMul_sound`
(for every pair of 64-bit inputs `a, b`, `glMul`'s limb-multiply and shift/mask reduction wire
network evaluates to canonical `goldilocksMulSpec a.toNat b.toNat`), and
`zkNttCoproc_butterfly_sound` / `zkNttCoproc_glMul_sound` on `zkNttCoprocRtlModule`.

What is hardware: `zkNttCoprocRtlModule`, one `RtlModule` in the 64-bit word language whose
wires are built by `glAdd`/`glSub`/`glMul` (limb multiply + `goldilocksReduce128`), carrying the
radix-2 butterfly (`u ± v·w mod p`) and a sumcheck round unit that accumulates `g(0), g(1), g(2)`,
absorbs them into a transcript register on `sc_absorb` and derives the round challenge from it
(`transcriptAbsorbSpec`), then folds with that registered challenge. `obend-emit-sv zk` writes it to
`apps/zk-ntt/verilator/zk_ntt_coproc.sv`; `obend-emit-sv golden-zk` writes the Lean run of the same
8-round protocol (`zkSumcheckGolden`) that the Verilator harness compares the emitted RTL against,
alongside its own `__uint128_t` reference.

Fixed 2026-11-04 (review/PANEL-DIFF-20261104.md item 5): the previous RTL multiplied with 64-bit
`.mul` and never reduced, and folded with an external `sc_r_in`. The e-graph cost-reduction and
VOP64 sections that kernel-evaluated for hours are gone (review/DECISIONS-20261031.md, second round).

What is not here: any claim that the transcript permutation is a cryptographic hash (the degree-7
power map `x^7` over `F_p` is an algebraic bijection used for deterministic round-challenge binding,
not a sponge or collision-resistant hash).
-/
public import Lean
public import Obend.Apps.ZkNtt.Goldilocks
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Tactic.Weave
public import Obend.Elab.Workbook
public meta import Lean
public meta import Obend.Core.Term
public meta import Obend.Law
public meta import Obend.Spec.Syntax
public meta import Obend.Spec.Parse
public meta import Obend.Spec.Elaborate
public meta import Obend.Spec.FrontEnd
public meta import Obend.Spec.Capture
public meta import Obend.Spec.Sha256
public meta import Obend.Logic.LateBinding
public meta import Obend.Logic.Claim
public meta import Obend.Logic.Rewrite
public meta import Obend.Logic.Frame
public meta import Obend.Logic.Obligation
public meta import Obend.Logic.Program
public meta import Obend.Leaf.Flatten
public meta import Obend.Leaf.Emit
public meta import Obend.Elab.Workbook

@[expose] public section
namespace Obend.Apps.ZkNtt

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Spec.CrossPackage
open Obend.Hardware
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Tactic.Weave

set_option autoImplicit false

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 1. Elaborating the 4 `.obend` Goldilocks ZK-NTT + Sumcheck Modules via `#import_obend` -/

#import_obend "apps/zk-ntt/GoldilocksField.obend" as GoldilocksMod
#import_obend "apps/zk-ntt/NttButterflyRadix2.obend" as ButterflyMod
#import_obend "apps/zk-ntt/SumcheckRoundPoly.obend" as SumcheckMod
#import_obend "apps/zk-ntt/ZkNttSumcheckTop.obend" as ZkNttTopMod

/-! The four modules are imported for their books and terms. They carry no `claim`s and no top-level
evaluation defs any more (2026-11-04): the importer reduced `evalNttButterflyPairSum` and its kin
through the Core4 interpreter on every elaboration, and a few 64-bit multiplies there cost more than
the module's budget; the same values are checked on the emitted hardware and the Lean golden. -/

/-! ## 2. Arithmetic specifications

The shared pure specifications and proofs are imported from `ZkNtt.Goldilocks`.
-/

/-- Transcript constants: the mixing multiplier `2^32`, the round constant `0x5A17`, and the initial
state `0x4F42454E44`. -/
def transcriptAlpha : Nat := 4294967296
def transcriptConst : Nat := 23063
def transcriptIv : Nat := 0x4F42454E44

/-- `transcriptAbsorb` of `SumcheckRoundPoly.obend`: the next transcript state, and the round challenge,
is `(((t + g0) * 2^32 + g1) * 2^32 + g2 + c)^7` in `F_p`. `x^7` is a permutation of `F_p`
(`gcd(7, p - 1) = 1`), so distinct absorbed triples give distinct challenges for a fixed `t`; nothing
cryptographic is claimed. -/
def transcriptAbsorbSpec (t g0 g1 g2 : Nat) : Nat :=
  let s := glN (glN (glN (glN (t + g0) * transcriptAlpha) + g1) * transcriptAlpha + g2 + transcriptConst)
  let s2 := glN (s * s)
  let s4 := glN (s2 * s2)
  glN (glN (s4 * s2) * s)

/-! ## 3. The co-processor as an `RtlModule`: field operations as wire networks -/

/-- Clock domain for the ZK-NTT + Sumcheck co-processor. -/
def zkNttClkDomain : ClkDomain :=
  .coreClk

/-- Wires under construction: appended in order, so every `wireRef` points at an earlier wire. -/
structure WireBuild where
  wires : Array WireAssign := #[]
  next  : Nat := 0

abbrev WireM := StateM WireBuild

/-- Name and append a wire; the result is a reference to it. -/
def wire (name : String) (e : RtlExpr) : WireM RtlExpr := do
  let idx := (← get).next
  modify fun s => { wires := s.wires.push { wireIdx := idx, name := name, expr := e }, next := idx + 1 }
  pure (.wireRef idx)

def glP : RtlExpr := .const 0xFFFFFFFF00000001#64
def glMask32 : RtlExpr := .const 0xFFFFFFFF#64
def glShift32 : RtlExpr := .const 32#64

/-- `x < p ? x : x - p` (every 64-bit word is below `2p`, so one subtraction canonicalizes). -/
def glCanon (tag : String) (x : RtlExpr) : WireM RtlExpr :=
  wire s!"{tag}_canon" (.mux (.alu .ult x glP) x (.alu .sub x glP))

/-- `(a + b) mod p` for canonical `a b`, without a 65th bit: `remP = p - b`; if `remP ≤ a` the sum
wraps and equals `a - remP`, else it is `a + b` (`fieldAdd` in `GoldilocksField.obend`). -/
def glAdd (tag : String) (a b : RtlExpr) : WireM RtlExpr := do
  let remP ← wire s!"{tag}_remp" (.alu .sub glP b)
  wire s!"{tag}_add" (.mux (.alu .ult a remP) (.alu .add a b) (.alu .sub a remP))

/-- `(a - b) mod p` for canonical `a b` (`fieldSub`). -/
def glSub (tag : String) (a b : RtlExpr) : WireM RtlExpr :=
  wire s!"{tag}_sub" (.mux (.alu .ult a b) (.alu .add (.alu .sub glP b) a) (.alu .sub a b))

/-- `(a * b) mod p` for any 64-bit `a b`: four 32×32 limb products (each exact in 64 bits), the
128-bit product `(lo, hi)` assembled from them, then `goldilocksReduce128` (`fieldMul` in
`GoldilocksField.obend`; the reduction is `goldilocksReduce128Spec`, proved sound above). -/
def glMul (tag : String) (a b : RtlExpr) : WireM RtlExpr := do
  let aLo ← wire s!"{tag}_alo" (.alu .bitAnd a glMask32)
  let aHi ← wire s!"{tag}_ahi" (.alu .lshr a glShift32)
  let bLo ← wire s!"{tag}_blo" (.alu .bitAnd b glMask32)
  let bHi ← wire s!"{tag}_bhi" (.alu .lshr b glShift32)
  let p00 ← wire s!"{tag}_p00" (.alu .mul aLo bLo)
  let p01 ← wire s!"{tag}_p01" (.alu .mul aLo bHi)
  let p10 ← wire s!"{tag}_p10" (.alu .mul aHi bLo)
  let p11 ← wire s!"{tag}_p11" (.alu .mul aHi bHi)
  let mid32 ← wire s!"{tag}_mid32"
    (.alu .add (.alu .add (.alu .lshr p00 glShift32) (.alu .bitAnd p01 glMask32)) (.alu .bitAnd p10 glMask32))
  let lo ← wire s!"{tag}_lo"
    (.alu .bitOr (.alu .bitAnd p00 glMask32) (.alu .shl (.alu .bitAnd mid32 glMask32) glShift32))
  let hi ← wire s!"{tag}_hi"
    (.alu .add (.alu .add (.alu .add p11 (.alu .lshr p01 glShift32)) (.alu .lshr p10 glShift32))
      (.alu .lshr mid32 glShift32))
  let hiLo ← wire s!"{tag}_hilo" (.alu .bitAnd hi glMask32)
  let hiHi ← wire s!"{tag}_hihi" (.alu .lshr hi glShift32)
  let mid ← wire s!"{tag}_mid" (.alu .sub (.alu .shl hiLo glShift32) hiLo)
  let loC ← glCanon s!"{tag}_lo" lo
  let t1 ← glAdd s!"{tag}_t1" loC mid
  glSub s!"{tag}_red" t1 hiHi

/-- Ports: `u_in v_in w_in` (butterfly), `sc_clear sc_enable sc_absorb` (1-bit strobes),
`sc_f0_in sc_f1_in` (a hypercube pair). Registers: `acc_g0 acc_g1 acc_g2`, `transcript`,
`challenge`, `pair_cnt`. -/
def buildZkNttCoproc : WireM (List OutputPort × List RegSpec) := do
  let u ← glCanon "u" (.inputPort 0)
  let v ← glCanon "v" (.inputPort 1)
  let w ← glCanon "w" (.inputPort 2)
  let clear := RtlExpr.inputPort 3
  let en := RtlExpr.inputPort 4
  let absorb := RtlExpr.inputPort 5
  let f0 ← glCanon "f0" (.inputPort 6)
  let f1 ← glCanon "f1" (.inputPort 7)
  let g0 := RtlExpr.regRead 0
  let g1 := RtlExpr.regRead 1
  let g2 := RtlExpr.regRead 2
  let tr := RtlExpr.regRead 3
  let chal := RtlExpr.regRead 4
  let cnt := RtlExpr.regRead 5
  -- radix-2 butterfly
  let vw ← glMul "vw" v w
  let even ← glAdd "even" u vw
  let odd ← glSub "odd" u vw
  -- round polynomial accumulation and the fold with the registered challenge
  let f1x2 ← glAdd "f1x2" f1 f1
  let g2term ← glSub "g2term" f1x2 f0
  let diff ← glSub "diff" f1 f0
  let rdiff ← glMul "rdiff" chal diff
  let folded ← glAdd "folded" f0 rdiff
  let g0acc ← glAdd "g0acc" g0 f0
  let g1acc ← glAdd "g1acc" g1 f1
  let g2acc ← glAdd "g2acc" g2 g2term
  let claim ← glAdd "claim" g0 g1
  -- transcript: (((t + g0) * 2^32 + g1) * 2^32 + g2 + c)^7
  let alpha := RtlExpr.const (BitVec.ofNat 64 transcriptAlpha)
  let rc := RtlExpr.const (BitVec.ofNat 64 transcriptConst)
  let a1 ← glAdd "tr_a1" tr g0
  let m1 ← glMul "tr_m1" a1 alpha
  let a2 ← glAdd "tr_a2" m1 g1
  let m2 ← glMul "tr_m2" a2 alpha
  let gc ← glAdd "tr_gc" g2 rc
  let s1 ← glAdd "tr_s" m2 gc
  let s2 ← glMul "tr_s2" s1 s1
  let s4 ← glMul "tr_s4" s2 s2
  let s6 ← glMul "tr_s6" s4 s2
  let s7 ← glMul "tr_s7" s6 s1
  let nextG0 ← wire "next_g0" (.mux clear (.const 0#64) (.mux en g0acc g0))
  let nextG1 ← wire "next_g1" (.mux clear (.const 0#64) (.mux en g1acc g1))
  let nextG2 ← wire "next_g2" (.mux clear (.const 0#64) (.mux en g2acc g2))
  let nextTr ← wire "next_transcript" (.mux absorb s7 tr)
  let nextChal ← wire "next_challenge" (.mux absorb s7 chal)
  let nextCnt ← wire "next_pair_cnt" (.mux clear (.const 0#64) (.mux en (.alu .add cnt (.const 1#64)) cnt))
  let mkReg (idx : Nat) (name : String) (init : BitVec 64) (nx : RtlExpr) : RegSpec :=
    { regIdx := idx, name := name, domain := zkNttClkDomain, resetKind := .syncReset init,
      isSynchronizer := false, nextExpr := nx }
  let regs :=
    [ mkReg 0 "acc_g0" 0#64 nextG0
    , mkReg 1 "acc_g1" 0#64 nextG1
    , mkReg 2 "acc_g2" 0#64 nextG2
    , mkReg 3 "transcript" (BitVec.ofNat 64 transcriptIv) nextTr
    , mkReg 4 "challenge" 0#64 nextChal
    , mkReg 5 "pair_cnt" 0#64 nextCnt ]
  let outs : List OutputPort :=
    [ { name := "goldilocks_even_out", expr := even }
    , { name := "goldilocks_odd_out", expr := odd }
    , { name := "sc_g0_out", expr := g0 }
    , { name := "sc_g1_out", expr := g1 }
    , { name := "sc_g2_out", expr := g2 }
    , { name := "sc_round_claim_out", expr := claim }
    , { name := "sc_folded_out", expr := folded }
    , { name := "sc_challenge_out", expr := chal }
    , { name := "sc_transcript_out", expr := tr }
    , { name := "sc_pair_cnt_out", expr := cnt } ]
  pure (outs, regs)

/-- The co-processor. Emitted by `obend-emit-sv zk` to `apps/zk-ntt/verilator/zk_ntt_coproc.sv`. -/
def zkNttCoprocRtlModule : RtlModule :=
  let r := Id.run (buildZkNttCoproc.run {})
  { name := "zk_ntt_coproc"
    inputNames := ["u_in", "v_in", "w_in", "sc_clear", "sc_enable", "sc_absorb", "sc_f0_in", "sc_f1_in"]
    inputWidths := [64, 64, 64, 1, 1, 1, 64, 64]
    wires := r.2.wires.toList
    regs := r.1.2
    outputs := r.1.1 }

/-- Butterfly inputs `(u, v, w)` with the strobes low. -/
def zkButterflyInputs (u v w : Nat) : Nat → BitVec 64
  | 0 => BitVec.ofNat 64 u
  | 1 => BitVec.ofNat 64 v
  | 2 => BitVec.ofNat 64 w
  | _ => 0#64

/-- Sumcheck-side inputs: strobes and a pair. -/
def zkSumcheckInputs (clear en absorb f0 f1 : Nat) : Nat → BitVec 64
  | 3 => BitVec.ofNat 64 clear
  | 4 => BitVec.ofNat 64 en
  | 5 => BitVec.ofNat 64 absorb
  | 6 => BitVec.ofNat 64 f0
  | 7 => BitVec.ofNat 64 f1
  | _ => 0#64

/-! ## 3b. Universal Soundness of `glCanon`, `glAdd`, `glSub`, `glMul` and `zkNttCoprocRtlModule` -/

/-- Every wire reference inside `e` has index strictly below `bound`. -/
def exprWiresLt (bound : Nat) : RtlExpr → Bool
  | .const _       => true
  | .inputPort _   => true
  | .wireRef idx   => idx < bound
  | .regRead _     => true
  | .alu _ a b     => exprWiresLt bound a && exprWiresLt bound b
  | .mux c t f     => exprWiresLt bound c && exprWiresLt bound t && exprWiresLt bound f
  | .bitNot a      => exprWiresLt bound a
  | .resize _ a    => exprWiresLt bound a

theorem exprWiresLt_mono {b1 b2 : Nat} (hle : b1 ≤ b2) (e : RtlExpr)
    (h : exprWiresLt b1 e = true) : exprWiresLt b2 e = true := by
  induction e with
  | const _ => rfl
  | inputPort _ => rfl
  | wireRef idx =>
    simp only [exprWiresLt, decide_eq_true_eq] at h ⊢
    omega
  | regRead _ => rfl
  | alu _ a b iha ihb =>
    simp only [exprWiresLt, Bool.and_eq_true] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | mux c t f ihc iht ihf =>
    simp only [exprWiresLt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihc h.1.1, iht h.1.2⟩, ihf h.2⟩
  | bitNot a iha => exact iha h
  | resize _ a iha => exact iha h

theorem evalRtlExpr_wires_agree (bound : Nat) (inputs regs w1 w2 : Nat → BitVec 64)
    (e : RtlExpr) (h : exprWiresLt bound e = true)
    (hAgree : ∀ i < bound, w1 i = w2 i) :
    evalRtlExpr inputs w1 regs e = evalRtlExpr inputs w2 regs e := by
  induction e with
  | const _ => rfl
  | inputPort _ => rfl
  | wireRef idx =>
    simp only [exprWiresLt, decide_eq_true_eq] at h
    exact hAgree idx h
  | regRead _ => rfl
  | alu _ a b iha ihb =>
    simp only [exprWiresLt, Bool.and_eq_true] at h
    simp only [evalRtlExpr, iha h.1, ihb h.2]
  | mux c t f ihc iht ihf =>
    simp only [exprWiresLt, Bool.and_eq_true] at h
    simp only [evalRtlExpr, ihc h.1.1, iht h.1.2, ihf h.2]
  | bitNot a iha =>
    simp only [evalRtlExpr, iha h]
  | resize _ a iha =>
    simp only [evalRtlExpr, iha h]

/-- A `WireM` computation is append-only when it advances `next` monotonically and leaves all
wire values below `st.next` unchanged in `evalWireTable`. -/
def WireAppendOnly {α : Type} (m : WireM α) : Prop :=
  ∀ (st : WireBuild) (inputs regs : Nat → BitVec 64),
    let r := Id.run (m.run st)
    st.next ≤ r.2.next ∧
    ∀ i < st.next,
      evalWireTable inputs regs r.2.wires.toList i = evalWireTable inputs regs st.wires.toList i

private theorem wireAppendOnly_pure {α : Type} (x : α) : WireAppendOnly (pure x) := by
  intro st _ _
  exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem wireAppendOnly_bind {α β : Type} {m : WireM α} {f : α → WireM β}
    (hm : WireAppendOnly m) (hf : ∀ x, WireAppendOnly (f x)) :
    WireAppendOnly (m >>= f) := by
  intro st inputs regs
  obtain ⟨hle1, hag1⟩ := hm st inputs regs
  obtain ⟨hle2, hag2⟩ := hf (Id.run (m.run st)).1 (Id.run (m.run st)).2 inputs regs
  exact ⟨Nat.le_trans hle1 hle2,
    fun i hi => (hag2 i (Nat.lt_of_lt_of_le hi hle1)).trans (hag1 i hi)⟩

theorem wire_appendOnly (name : String) (e : RtlExpr) : WireAppendOnly (wire name e) := by
  intro st inputs regs
  change st.next ≤ st.next + 1 ∧ ∀ i < st.next,
    evalWireTable inputs regs (st.wires.push { wireIdx := st.next, name := name, expr := e }).toList i =
      evalWireTable inputs regs st.wires.toList i
  refine ⟨by omega, fun i hi => ?_⟩
  rw [Array.toList_push]
  unfold evalWireTable
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hne : (i == st.next) = false := beq_false_of_ne (by omega)
  simp only [hne]
  rfl

theorem wire_eval (name : String) (e : RtlExpr) (st : WireBuild)
    (inputs regs : Nat → BitVec 64) :
    let r := Id.run ((wire name e).run st)
    exprWiresLt r.2.next r.1 = true ∧
    evalRtlExpr inputs (evalWireTable inputs regs r.2.wires.toList) regs r.1 =
      evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs e := by
  change exprWiresLt (st.next + 1) (.wireRef st.next) = true ∧
    evalRtlExpr inputs (evalWireTable inputs regs
      (st.wires.push { wireIdx := st.next, name := name, expr := e }).toList) regs (.wireRef st.next) =
      evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs e
  refine ⟨by simp [exprWiresLt], ?_⟩
  rw [Array.toList_push]
  simp only [evalRtlExpr]
  unfold evalWireTable
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp

theorem glCanon_appendOnly (tag : String) (x : RtlExpr) : WireAppendOnly (glCanon tag x) :=
  wire_appendOnly _ _

theorem glAdd_appendOnly (tag : String) (a b : RtlExpr) : WireAppendOnly (glAdd tag a b) :=
  wireAppendOnly_bind (wire_appendOnly _ _) fun _ => wire_appendOnly _ _

theorem glSub_appendOnly (tag : String) (a b : RtlExpr) : WireAppendOnly (glSub tag a b) :=
  wire_appendOnly _ _

theorem glMul_appendOnly (tag : String) (a b : RtlExpr) : WireAppendOnly (glMul tag a b) := by
  unfold glMul
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (wire_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (glCanon_appendOnly _ _) fun _ => ?_
  refine wireAppendOnly_bind (glAdd_appendOnly _ _ _) fun _ => ?_
  exact glSub_appendOnly _ _ _

private theorem lt_two_pow_64_of_lt_prime {x : Nat} (hx : x < goldilocksPrime) : x < 2 ^ 64 := by
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldilocksPrime at hx
  omega

private theorem goldilocksCanon64_of_lt {x : Nat} (hx : x < goldilocksPrime) :
    goldilocksCanon64 x = x := by
  unfold goldilocksCanon64
  have hge : ¬ goldilocksPrime ≤ x := by omega
  simp only [hge, ite_false]

private theorem bv_add_toNat (x y : BitVec 64) :
    (evalAluOp .add x y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_add]

private theorem bv_sub_toNat (x y : BitVec 64) :
    (evalAluOp .sub x y).toNat = (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_sub]

private theorem bv_mul_toNat (x y : BitVec 64) :
    (evalAluOp .mul x y).toNat = (x.toNat * y.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_mul]

private theorem bv_or_toNat (x y : BitVec 64) :
    (evalAluOp .bitOr x y).toNat = x.toNat ||| y.toNat := by
  simp only [evalAluOp, BitVec.toNat_or]

private theorem bv_and_mask32_toNat (x : BitVec 64) :
    (evalAluOp .bitAnd x 0xFFFFFFFF#64).toNat = x.toNat % 4294967296 := by
  have hm : (0xFFFFFFFF#64).toNat = 2 ^ 32 - 1 := rfl
  simp only [evalAluOp, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

private theorem bv_lshr_32_toNat (x : BitVec 64) :
    (evalAluOp .lshr x 32#64).toNat = x.toNat / 4294967296 := by
  have hs : (32#64).toNat % 64 = 32 := rfl
  simp only [evalAluOp, BitVec.toNat_ushiftRight, hs, Nat.shiftRight_eq_div_pow]

private theorem bv_shl_32_toNat (x : BitVec 64) :
    (evalAluOp .shl x 32#64).toNat = (x.toNat * 4294967296) % 18446744073709551616 := by
  have hs : (32#64).toNat % 64 = 32 := rfl
  simp only [evalAluOp, BitVec.toNat_shiftLeft, hs, Nat.shiftLeft_eq]

private theorem mux_ult_eq (x y t f : BitVec 64) :
    (if (evalAluOp .ult x y != 0#64) = true then t else f) =
      (if x.toNat < y.toNat then t else f) := by
  have h10 : (1#64 != 0#64) = true := by simp
  unfold evalAluOp BitVec.ult
  by_cases h : x.toNat < y.toNat
  · simp [h, h10]
  · simp [h]

private theorem bv_canon_eq (vx : BitVec 64) :
    (if evalAluOp .ult vx 0xFFFFFFFF00000001#64 != 0#64 then vx
     else evalAluOp .sub vx 0xFFFFFFFF00000001#64) =
      BitVec.ofNat 64 (goldilocksCanon64 vx.toNat) := by
  rw [mux_ult_eq]
  apply BitVec.eq_of_toNat_eq
  have hvx := vx.isLt
  have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hp]
  unfold goldilocksCanon64
  by_cases hlt : vx.toNat < goldilocksPrime
  · have hge : ¬ goldilocksPrime ≤ vx.toNat := by omega
    simp only [hlt, ite_true, hge, ite_false, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hvx).symm
  · have hge : goldilocksPrime ≤ vx.toNat := by omega
    simp only [hlt, ite_false, hge, ite_true, bv_sub_toNat, hp, BitVec.toNat_ofNat, hw]
    rw [hw] at hvx
    unfold goldilocksPrime at hge ⊢
    omega

private theorem bv_add_eq (va vb : BitVec 64)
    (ha : va.toNat < goldilocksPrime) (hb : vb.toNat < goldilocksPrime) :
    let remP := evalAluOp .sub 0xFFFFFFFF00000001#64 vb
    (if evalAluOp .ult va remP != 0#64 then evalAluOp .add va vb else evalAluOp .sub va remP) =
      BitVec.ofNat 64 (goldilocksAddSpec va.toNat vb.toNat) := by
  intro remP
  rw [mux_ult_eq]
  apply BitVec.eq_of_toNat_eq
  have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hrem : remP.toNat = goldilocksPrime - vb.toNat := by
    simp only [remP, bv_sub_toNat, hp]
    unfold goldilocksPrime at hb ⊢
    omega
  rw [hrem]
  unfold goldilocksAddSpec
  rw [goldilocksCanon64_of_lt ha, goldilocksCanon64_of_lt hb]
  dsimp only
  by_cases hlt : va.toNat < goldilocksPrime - vb.toNat
  · have hge : ¬ goldilocksPrime ≤ va.toNat + vb.toNat := by omega
    simp only [hlt, ite_true, hge, ite_false, bv_add_toNat, BitVec.toNat_ofNat, hw]
  · have hge : goldilocksPrime ≤ va.toNat + vb.toNat := by omega
    simp only [hlt, ite_false, hge, ite_true, bv_sub_toNat, hrem, BitVec.toNat_ofNat, hw]
    unfold goldilocksPrime at ha hb hlt hge ⊢
    omega

private theorem bv_sub_eq (va vb : BitVec 64)
    (ha : va.toNat < goldilocksPrime) (hb : vb.toNat < goldilocksPrime) :
    (if evalAluOp .ult va vb != 0#64 then
       evalAluOp .add (evalAluOp .sub 0xFFFFFFFF00000001#64 vb) va
     else evalAluOp .sub va vb) =
      BitVec.ofNat 64 (goldilocksSubSpec va.toNat vb.toNat) := by
  rw [mux_ult_eq]
  apply BitVec.eq_of_toNat_eq
  have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldilocksSubSpec
  rw [goldilocksCanon64_of_lt ha, goldilocksCanon64_of_lt hb]
  dsimp only
  by_cases hlt : va.toNat < vb.toNat
  · have hle : ¬ vb.toNat ≤ va.toNat := by omega
    simp only [hlt, ite_true, hle, ite_false, bv_add_toNat, bv_sub_toNat, hp, BitVec.toNat_ofNat, hw]
    unfold goldilocksPrime at ha hb hlt ⊢
    omega
  · have hle : vb.toNat ≤ va.toNat := by omega
    simp only [hlt, ite_false, hle, ite_true, bv_sub_toNat, BitVec.toNat_ofNat, hw]
    unfold goldilocksPrime at ha hb
    omega

private abbrev evalAt (inputs regs : Nat → BitVec 64) (st : WireBuild) (e : RtlExpr) : BitVec 64 :=
  evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs e

/-- Hoare-style relational postcondition on `WireM`: running `m` from `st` is append-only and its
result `(a, st')` satisfies `post a st'`, without ever reducing `m` inside `Array.push`. -/
def WireHoare {α : Type} (inputs regs : Nat → BitVec 64) (st : WireBuild) (m : WireM α)
    (post : α → WireBuild → Prop) : Prop :=
  let r := Id.run (m.run st)
  st.next ≤ r.2.next ∧
  (∀ i < st.next,
    evalWireTable inputs regs r.2.wires.toList i = evalWireTable inputs regs st.wires.toList i) ∧
  post r.1 r.2

private theorem wireHoare_pure {α : Type} {inputs regs : Nat → BitVec 64} {st : WireBuild}
    (x : α) {Q : α → WireBuild → Prop} (h : Q x st) :
    WireHoare inputs regs st (pure x) Q :=
  ⟨Nat.le_refl _, fun _ _ => rfl, h⟩

private theorem wireHoare_bind {α β : Type} {inputs regs : Nat → BitVec 64} {st : WireBuild}
    {m : WireM α} {f : α → WireM β} {P : α → WireBuild → Prop} {Q : β → WireBuild → Prop}
    (hm : WireHoare inputs regs st m P)
    (hf : ∀ a st1,
      (∀ e, exprWiresLt st.next e = true → exprWiresLt st1.next e = true ∧
        evalAt inputs regs st1 e = evalAt inputs regs st e) →
      P a st1 → WireHoare inputs regs st1 (f a) Q) :
    WireHoare inputs regs st (m >>= f) Q := by
  obtain ⟨hle1, hag1, hp1⟩ := hm
  have keep1 : ∀ e, exprWiresLt st.next e = true → exprWiresLt (Id.run (m.run st)).2.next e = true ∧
      evalAt inputs regs (Id.run (m.run st)).2 e = evalAt inputs regs st e :=
    fun e he => ⟨exprWiresLt_mono hle1 e he, evalRtlExpr_wires_agree st.next inputs regs _ _ e he hag1⟩
  obtain ⟨hle2, hag2, hq2⟩ := hf (Id.run (m.run st)).1 (Id.run (m.run st)).2 keep1 hp1
  exact ⟨Nat.le_trans hle1 hle2,
    fun i hi => (hag2 i (Nat.lt_of_lt_of_le hi hle1)).trans (hag1 i hi), hq2⟩

private theorem wireHoare_of_appendOnly {α : Type} {inputs regs : Nat → BitVec 64} {st : WireBuild}
    {m : WireM α} (hm : WireAppendOnly m) :
    WireHoare inputs regs st m (fun _ _ => True) := by
  obtain ⟨hle, hag⟩ := hm st inputs regs
  exact ⟨hle, hag, trivial⟩

private theorem wireHoare_wire (inputs regs : Nat → BitVec 64) (st : WireBuild)
    (name : String) (e : RtlExpr) (v : BitVec 64) (hv : evalAt inputs regs st e = v) :
    WireHoare inputs regs st (wire name e)
      (fun out st1 => exprWiresLt st1.next out = true ∧ evalAt inputs regs st1 out = v) := by
  obtain ⟨hle, hag⟩ := wire_appendOnly name e st inputs regs
  obtain ⟨hbnd, hev⟩ := wire_eval name e st inputs regs
  exact ⟨hle, hag, hbnd, hev.trans hv⟩

theorem glCanon_sound (tag : String) (x : RtlExpr) (st : WireBuild)
    (inputs regs : Nat → BitVec 64) :
    let r := Id.run ((glCanon tag x).run st)
    let wt0 := evalWireTable inputs regs st.wires.toList
    let wt1 := evalWireTable inputs regs r.2.wires.toList
    exprWiresLt r.2.next r.1 = true ∧
    (evalRtlExpr inputs wt1 regs r.1).toNat < goldilocksPrime ∧
    evalRtlExpr inputs wt1 regs r.1 =
      BitVec.ofNat 64 (goldilocksCanon64 (evalRtlExpr inputs wt0 regs x).toNat) := by
  unfold glCanon
  obtain ⟨hbnd, hev⟩ := wire_eval s!"{tag}_canon"
    (.mux (.alu .ult x glP) x (.alu .sub x glP)) st inputs regs
  refine ⟨hbnd, ?_⟩
  rw [hev]
  simp only [evalRtlExpr, glP]
  rw [bv_canon_eq]
  have hspec := (goldilocksCanon64_spec (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs x).isLt).1
  refine ⟨?_, rfl⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]
  exact hspec

theorem glAdd_sound (tag : String) (a b : RtlExpr) (st : WireBuild)
    (inputs regs : Nat → BitVec 64)
    (ha : exprWiresLt st.next a = true) (hb : exprWiresLt st.next b = true)
    (haLt : (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs a).toNat < goldilocksPrime)
    (hbLt : (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs b).toNat < goldilocksPrime) :
    let r := Id.run ((glAdd tag a b).run st)
    let wt0 := evalWireTable inputs regs st.wires.toList
    let wt1 := evalWireTable inputs regs r.2.wires.toList
    exprWiresLt r.2.next r.1 = true ∧
    (evalRtlExpr inputs wt1 regs r.1).toNat < goldilocksPrime ∧
    evalRtlExpr inputs wt1 regs r.1 =
      BitVec.ofNat 64 (goldilocksAddSpec (evalRtlExpr inputs wt0 regs a).toNat
        (evalRtlExpr inputs wt0 regs b).toNat) := by
  let va := evalAt inputs regs st a
  let vb := evalAt inputs regs st b
  let vremP := evalAluOp .sub 0xFFFFFFFF00000001#64 vb
  suffices hH : WireHoare inputs regs st (glAdd tag a b)
      (fun out stF => exprWiresLt stF.next out = true ∧
        (evalAt inputs regs stF out).toNat < goldilocksPrime ∧
        evalAt inputs regs stF out = BitVec.ofNat 64 (goldilocksAddSpec va.toNat vb.toNat)) from hH.2.2
  unfold glAdd
  refine wireHoare_bind (wireHoare_wire inputs regs st _ _ vremP
    (by simp [evalAt, evalRtlExpr, glP, vremP, vb])) fun remP s1 k1 ⟨_, eremP⟩ => ?_
  obtain ⟨_, ea1⟩ := k1 a ha
  obtain ⟨_, eb1⟩ := k1 b hb
  have hv2 : evalAt inputs regs s1 (.mux (.alu .ult a remP) (.alu .add a b) (.alu .sub a remP)) =
      BitVec.ofNat 64 (goldilocksAddSpec va.toNat vb.toNat) := by
    simp only [evalAt, evalRtlExpr] at ea1 eb1 eremP ⊢
    simp only [ea1, eb1, eremP]
    exact bv_add_eq va vb haLt hbLt
  obtain ⟨hle, hag, hbnd, hev⟩ := wireHoare_wire inputs regs s1 s!"{tag}_add"
    (.mux (.alu .ult a remP) (.alu .add a b) (.alu .sub a remP)) _ hv2
  refine ⟨hle, hag, hbnd, ?_, hev⟩
  rw [hev]
  have hspec := (goldilocksAddSpec_spec va.isLt vb.isLt).1
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]
  exact hspec

theorem glSub_sound (tag : String) (a b : RtlExpr) (st : WireBuild)
    (inputs regs : Nat → BitVec 64)
    (haLt : (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs a).toNat < goldilocksPrime)
    (hbLt : (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs b).toNat < goldilocksPrime) :
    let r := Id.run ((glSub tag a b).run st)
    let wt0 := evalWireTable inputs regs st.wires.toList
    let wt1 := evalWireTable inputs regs r.2.wires.toList
    exprWiresLt r.2.next r.1 = true ∧
    (evalRtlExpr inputs wt1 regs r.1).toNat < goldilocksPrime ∧
    evalRtlExpr inputs wt1 regs r.1 =
      BitVec.ofNat 64 (goldilocksSubSpec (evalRtlExpr inputs wt0 regs a).toNat
        (evalRtlExpr inputs wt0 regs b).toNat) := by
  unfold glSub
  obtain ⟨hbnd, hev⟩ := wire_eval s!"{tag}_sub"
    (.mux (.alu .ult a b) (.alu .add (.alu .sub glP b) a) (.alu .sub a b)) st inputs regs
  refine ⟨hbnd, ?_⟩
  rw [hev]
  simp only [evalRtlExpr, glP]
  rw [bv_sub_eq _ _ haLt hbLt]
  have hspec := (goldilocksSubSpec_spec
    (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs a).isLt
    (evalRtlExpr inputs (evalWireTable inputs regs st.wires.toList) regs b).isLt).1
  refine ⟨?_, rfl⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]
  exact hspec

/-- Pure 64-bit ALU limb schedule of `glMul`: the assembled 128-bit pair `(lo, hi)` represents the
exact unsigned product `va.toNat * vb.toNat`, and its `mid` and `hiHi` reduction terms match
`goldilocksReduce128Spec`. -/
private theorem glMul_limb_reduce_eq (va vb : BitVec 64) :
    let aLo := evalAluOp .bitAnd va 0xFFFFFFFF#64
    let aHi := evalAluOp .lshr va 32#64
    let bLo := evalAluOp .bitAnd vb 0xFFFFFFFF#64
    let bHi := evalAluOp .lshr vb 32#64
    let p00 := evalAluOp .mul aLo bLo
    let p01 := evalAluOp .mul aLo bHi
    let p10 := evalAluOp .mul aHi bLo
    let p11 := evalAluOp .mul aHi bHi
    let mid32 := evalAluOp .add (evalAluOp .add (evalAluOp .lshr p00 32#64)
      (evalAluOp .bitAnd p01 0xFFFFFFFF#64)) (evalAluOp .bitAnd p10 0xFFFFFFFF#64)
    let lo := evalAluOp .bitOr (evalAluOp .bitAnd p00 0xFFFFFFFF#64)
      (evalAluOp .shl (evalAluOp .bitAnd mid32 0xFFFFFFFF#64) 32#64)
    let hi := evalAluOp .add (evalAluOp .add (evalAluOp .add p11 (evalAluOp .lshr p01 32#64))
      (evalAluOp .lshr p10 32#64)) (evalAluOp .lshr mid32 32#64)
    let hiLo := evalAluOp .bitAnd hi 0xFFFFFFFF#64
    let hiHi := evalAluOp .lshr hi 32#64
    let mid := evalAluOp .sub (evalAluOp .shl hiLo 32#64) hiLo
    mid.toNat < goldilocksPrime ∧
    hiHi.toNat < goldilocksPrime ∧
    goldilocksSubSpec (goldilocksAddSpec (goldilocksCanon64 lo.toNat) mid.toNat) hiHi.toNat =
      goldilocksMulSpec va.toNat vb.toNat := by
  intro aLo aHi bLo bHi p00 p01 p10 p11 mid32 lo hi hiLo hiHi mid
  have hva := va.isLt
  have hvb := vb.isLt
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hp2 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have ha0 : aLo.toNat = va.toNat % 4294967296 := bv_and_mask32_toNat va
  have ha1 : aHi.toNat = va.toNat / 4294967296 := bv_lshr_32_toNat va
  have hb0 : bLo.toNat = vb.toNat % 4294967296 := bv_and_mask32_toNat vb
  have hb1 : bHi.toNat = vb.toNat / 4294967296 := bv_lshr_32_toNat vb
  have ha0Lt : aLo.toNat < 4294967296 := by rw [ha0]; exact Nat.mod_lt _ (by omega)
  have ha1Lt : aHi.toNat < 4294967296 := by rw [ha1]; rw [hw] at hva; omega
  have hb0Lt : bLo.toNat < 4294967296 := by rw [hb0]; exact Nat.mod_lt _ (by omega)
  have hb1Lt : bHi.toNat < 4294967296 := by rw [hb1]; rw [hw] at hvb; omega
  have mul32_lt : ∀ x y, x < 4294967296 → y < 4294967296 → x * y < 18446744073709551616 := by
    intro x y hx hy
    have := Nat.mul_le_mul (show x ≤ 4294967295 by omega) (show y ≤ 4294967295 by omega)
    omega
  have hp00 : p00.toNat = aLo.toNat * bLo.toNat := by
    simp only [p00, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ ha0Lt hb0Lt)]
  have hp01 : p01.toNat = aLo.toNat * bHi.toNat := by
    simp only [p01, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ ha0Lt hb1Lt)]
  have hp10 : p10.toNat = aHi.toNat * bLo.toNat := by
    simp only [p10, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ ha1Lt hb0Lt)]
  have hp11 : p11.toNat = aHi.toNat * bHi.toNat := by
    simp only [p11, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ ha1Lt hb1Lt)]
  have hp00HiLt : p00.toNat / 4294967296 < 4294967296 := by
    have := mul32_lt _ _ ha0Lt hb0Lt; omega
  have hmid32 : mid32.toNat = p00.toNat / 4294967296 + p01.toNat % 4294967296 + p10.toNat % 4294967296 := by
    have hm2 : p01.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
    have hm3 : p10.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
    simp only [mid32, bv_add_toNat, bv_lshr_32_toNat, bv_and_mask32_toNat]
    omega
  have hlo : lo.toNat = p00.toNat % 4294967296 + 4294967296 * (mid32.toNat % 4294967296) := by
    have hm1 : p00.toNat % 4294967296 < 2 ^ 32 := by rw [hp2]; exact Nat.mod_lt _ (by omega)
    have hm2 : mid32.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
    have hm2Mul : mid32.toNat % 4294967296 * 4294967296 < 18446744073709551616 := by
      have := Nat.mul_le_mul_right 4294967296 (show mid32.toNat % 4294967296 ≤ 4294967295 by omega)
      omega
    have hshEq : mid32.toNat % 4294967296 * 4294967296 = (mid32.toNat % 4294967296) <<< 32 := by
      rw [Nat.shiftLeft_eq, hp2]
    simp only [lo, bv_or_toNat, bv_and_mask32_toNat, bv_shl_32_toNat]
    rw [Nat.mod_eq_of_lt hm2Mul, hshEq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hm1, ← hshEq,
      Nat.add_comm, Nat.mul_comm _ 4294967296]
  let H : Nat := p11.toNat + p01.toNat / 4294967296 + p10.toNat / 4294967296 + mid32.toNat / 4294967296
  have hProd : lo.toNat + 18446744073709551616 * H = va.toNat * vb.toNat := by
    have d00 := Nat.mod_add_div p00.toNat 4294967296
    have d01 := Nat.mod_add_div p01.toNat 4294967296
    have d10 := Nat.mod_add_div p10.toNat 4294967296
    have dmid := Nat.mod_add_div mid32.toNat 4294967296
    have hLin : lo.toNat + 18446744073709551616 * H =
        p00.toNat + 4294967296 * (p01.toNat + p10.toNat) + 18446744073709551616 * p11.toNat := by
      dsimp only [H]; omega
    rw [hLin, hp00, hp01, hp10, hp11, ha0, ha1, hb0, hb1]
    have da := Nat.mod_add_div va.toNat 4294967296
    have db := Nat.mod_add_div vb.toNat 4294967296
    grind
  have hProdLt : va.toNat * vb.toNat < 18446744073709551616 * 18446744073709551616 := by
    rw [hw] at hva hvb
    have := Nat.mul_le_mul (show va.toNat ≤ 18446744073709551615 by omega)
      (show vb.toNat ≤ 18446744073709551615 by omega)
    omega
  have hHLt : H < 18446744073709551616 := by omega
  have hhi : hi.toNat = H := by
    simp only [hi, bv_add_toNat, bv_lshr_32_toNat]
    dsimp only [H] at hHLt ⊢
    omega
  have hhiLo : hiLo.toNat = hi.toNat % 4294967296 := bv_and_mask32_toNat hi
  have hhiHi : hiHi.toNat = hi.toNat / 4294967296 := bv_lshr_32_toNat hi
  have hhiLoLt : hiLo.toNat < 4294967296 := by rw [hhiLo]; exact Nat.mod_lt _ (by omega)
  have hhiHiLt : hiHi.toNat < 4294967296 := by rw [hhiHi, hhi]; omega
  have hmid : mid.toNat = hiLo.toNat * 4294967296 - hiLo.toNat := by
    simp only [mid, bv_sub_toNat, bv_shl_32_toNat]
    omega
  have hmidLtP : mid.toNat < goldilocksPrime := by unfold goldilocksPrime; omega
  have hhiHiLtP : hiHi.toNat < goldilocksPrime := by unfold goldilocksPrime; omega
  refine ⟨hmidLtP, hhiHiLtP, ?_⟩
  have hCanonIdemp : goldilocksAddSpec (goldilocksCanon64 lo.toNat) mid.toNat =
      goldilocksAddSpec lo.toNat mid.toNat := by
    unfold goldilocksAddSpec
    rw [goldilocksCanon64_of_lt (goldilocksCanon64_spec lo.isLt).1]
  rw [hCanonIdemp, hmid, hhiLo, hhiHi]
  change goldilocksReduce128Spec lo.toNat hi.toNat = goldilocksMulSpec va.toNat vb.toNat
  rw [(goldilocksReduce128Spec_sound lo.isLt hi.isLt).2, hw, hhi, hProd]
  unfold goldilocksMulSpec glN
  exact Nat.mul_mod va.toNat vb.toNat goldilocksPrime

private theorem wireHoare_glCanon (inputs regs : Nat → BitVec 64) (st : WireBuild)
    (tag : String) (x : RtlExpr) :
    WireHoare inputs regs st (glCanon tag x)
      (fun out st1 => exprWiresLt st1.next out = true ∧
        (evalAt inputs regs st1 out).toNat < goldilocksPrime ∧
        evalAt inputs regs st1 out = BitVec.ofNat 64 (goldilocksCanon64 (evalAt inputs regs st x).toNat)) := by
  obtain ⟨hle, hag⟩ := glCanon_appendOnly tag x st inputs regs
  exact ⟨hle, hag, glCanon_sound tag x st inputs regs⟩

private theorem wireHoare_glAdd (inputs regs : Nat → BitVec 64) (st : WireBuild)
    (tag : String) (a b : RtlExpr)
    (ha : exprWiresLt st.next a = true) (hb : exprWiresLt st.next b = true)
    (haLt : (evalAt inputs regs st a).toNat < goldilocksPrime)
    (hbLt : (evalAt inputs regs st b).toNat < goldilocksPrime) :
    WireHoare inputs regs st (glAdd tag a b)
      (fun out st1 => exprWiresLt st1.next out = true ∧
        (evalAt inputs regs st1 out).toNat < goldilocksPrime ∧
        evalAt inputs regs st1 out =
          BitVec.ofNat 64 (goldilocksAddSpec (evalAt inputs regs st a).toNat (evalAt inputs regs st b).toNat)) := by
  obtain ⟨hle, hag⟩ := glAdd_appendOnly tag a b st inputs regs
  exact ⟨hle, hag, glAdd_sound tag a b st inputs regs ha hb haLt hbLt⟩

private theorem wireHoare_glSub (inputs regs : Nat → BitVec 64) (st : WireBuild)
    (tag : String) (a b : RtlExpr)
    (haLt : (evalAt inputs regs st a).toNat < goldilocksPrime)
    (hbLt : (evalAt inputs regs st b).toNat < goldilocksPrime) :
    WireHoare inputs regs st (glSub tag a b)
      (fun out st1 => exprWiresLt st1.next out = true ∧
        (evalAt inputs regs st1 out).toNat < goldilocksPrime ∧
        evalAt inputs regs st1 out =
          BitVec.ofNat 64 (goldilocksSubSpec (evalAt inputs regs st a).toNat (evalAt inputs regs st b).toNat)) := by
  obtain ⟨hle, hag⟩ := glSub_appendOnly tag a b st inputs regs
  exact ⟨hle, hag, glSub_sound tag a b st inputs regs haLt hbLt⟩

/-- **`glMul_sound`**: for any 64-bit wire expressions `a, b` valid in `st`, the 16-wire 32-bit-limb
product and shift/mask reduction network emitted by `glMul` evaluates to canonical
`goldilocksMulSpec va.toNat vb.toNat = (va.toNat * vb.toNat) % goldilocksPrime`. -/
theorem glMul_sound (tag : String) (a b : RtlExpr) (st : WireBuild)
    (inputs regs : Nat → BitVec 64)
    (ha : exprWiresLt st.next a = true) (hb : exprWiresLt st.next b = true) :
    let r := Id.run ((glMul tag a b).run st)
    let wt0 := evalWireTable inputs regs st.wires.toList
    let wt1 := evalWireTable inputs regs r.2.wires.toList
    exprWiresLt r.2.next r.1 = true ∧
    (evalRtlExpr inputs wt1 regs r.1).toNat < goldilocksPrime ∧
    evalRtlExpr inputs wt1 regs r.1 =
      BitVec.ofNat 64 (goldilocksMulSpec (evalRtlExpr inputs wt0 regs a).toNat
        (evalRtlExpr inputs wt0 regs b).toNat) := by
  let va0 := evalAt inputs regs st a
  let vb0 := evalAt inputs regs st b
  let vaLo := evalAluOp .bitAnd va0 0xFFFFFFFF#64
  let vaHi := evalAluOp .lshr va0 32#64
  let vbLo := evalAluOp .bitAnd vb0 0xFFFFFFFF#64
  let vbHi := evalAluOp .lshr vb0 32#64
  let vp00 := evalAluOp .mul vaLo vbLo
  let vp01 := evalAluOp .mul vaLo vbHi
  let vp10 := evalAluOp .mul vaHi vbLo
  let vp11 := evalAluOp .mul vaHi vbHi
  let vmid32 := evalAluOp .add (evalAluOp .add (evalAluOp .lshr vp00 32#64)
    (evalAluOp .bitAnd vp01 0xFFFFFFFF#64)) (evalAluOp .bitAnd vp10 0xFFFFFFFF#64)
  let vlo := evalAluOp .bitOr (evalAluOp .bitAnd vp00 0xFFFFFFFF#64)
    (evalAluOp .shl (evalAluOp .bitAnd vmid32 0xFFFFFFFF#64) 32#64)
  let vhi := evalAluOp .add (evalAluOp .add (evalAluOp .add vp11 (evalAluOp .lshr vp01 32#64))
    (evalAluOp .lshr vp10 32#64)) (evalAluOp .lshr vmid32 32#64)
  let vhiLo := evalAluOp .bitAnd vhi 0xFFFFFFFF#64
  let vhiHi := evalAluOp .lshr vhi 32#64
  let vmid := evalAluOp .sub (evalAluOp .shl vhiLo 32#64) vhiLo
  obtain ⟨hMidLtP, hHiHiLtP, hRedEq⟩ := glMul_limb_reduce_eq va0 vb0
  suffices hH : WireHoare inputs regs st (glMul tag a b)
      (fun out stF => exprWiresLt stF.next out = true ∧
        (evalAt inputs regs stF out).toNat < goldilocksPrime ∧
        evalAt inputs regs stF out = BitVec.ofNat 64 (goldilocksMulSpec va0.toNat vb0.toNat)) from hH.2.2
  unfold glMul
  refine wireHoare_bind (wireHoare_wire inputs regs st _ _ vaLo
    (by simp [evalAt, evalRtlExpr, glMask32, vaLo, va0])) fun aLo s1 k1 ⟨baLo, eaLo⟩ => ?_
  obtain ⟨ha1, ea1⟩ := k1 a ha; obtain ⟨hb1, eb1⟩ := k1 b hb
  refine wireHoare_bind (wireHoare_wire inputs regs s1 _ _ vaHi
    (by simp [evalAt, evalRtlExpr, glShift32, ea1, vaHi, va0])) fun aHi s2 k2 ⟨baHi, eaHi⟩ => ?_
  obtain ⟨baLo2, eaLo2⟩ := k2 aLo baLo; obtain ⟨hb2, eb2⟩ := k2 b hb1
  refine wireHoare_bind (wireHoare_wire inputs regs s2 _ _ vbLo
    (by simp [evalAt, evalRtlExpr, glMask32, eb2, eb1, vbLo, vb0])) fun bLo s3 k3 ⟨bbLo, ebLo⟩ => ?_
  obtain ⟨baLo3, eaLo3⟩ := k3 aLo baLo2; obtain ⟨baHi3, eaHi3⟩ := k3 aHi baHi; obtain ⟨hb3, eb3⟩ := k3 b hb2
  refine wireHoare_bind (wireHoare_wire inputs regs s3 _ _ vbHi
    (by simp [evalAt, evalRtlExpr, glShift32, eb3, eb2, eb1, vbHi, vb0])) fun bHi s4 k4 ⟨bbHi, ebHi⟩ => ?_
  obtain ⟨baLo4, eaLo4⟩ := k4 aLo baLo3; obtain ⟨baHi4, eaHi4⟩ := k4 aHi baHi3; obtain ⟨bbLo4, ebLo4⟩ := k4 bLo bbLo
  refine wireHoare_bind (wireHoare_wire inputs regs s4 _ _ vp00
    (by simp [evalAt, evalRtlExpr, eaLo4, eaLo3, eaLo2, eaLo, ebLo4, ebLo, vp00])) fun p00 s5 k5 ⟨bp00, ep00⟩ => ?_
  obtain ⟨baLo5, eaLo5⟩ := k5 aLo baLo4; obtain ⟨baHi5, eaHi5⟩ := k5 aHi baHi4
  obtain ⟨bbLo5, ebLo5⟩ := k5 bLo bbLo4; obtain ⟨bbHi5, ebHi5⟩ := k5 bHi bbHi
  refine wireHoare_bind (wireHoare_wire inputs regs s5 _ _ vp01
    (by simp [evalAt, evalRtlExpr, eaLo5, eaLo4, eaLo3, eaLo2, eaLo, ebHi5, ebHi, vp01])) fun p01 s6 k6 ⟨bp01, ep01⟩ => ?_
  obtain ⟨baHi6, eaHi6⟩ := k6 aHi baHi5; obtain ⟨bbLo6, ebLo6⟩ := k6 bLo bbLo5
  obtain ⟨bbHi6, ebHi6⟩ := k6 bHi bbHi5; obtain ⟨bp00_6, ep00_6⟩ := k6 p00 bp00
  refine wireHoare_bind (wireHoare_wire inputs regs s6 _ _ vp10
    (by simp [evalAt, evalRtlExpr, eaHi6, eaHi5, eaHi4, eaHi3, eaHi, ebLo6, ebLo5, ebLo4, ebLo, vp10]))
    fun p10 s7 k7 ⟨bp10, ep10⟩ => ?_
  obtain ⟨baHi7, eaHi7⟩ := k7 aHi baHi6; obtain ⟨bbHi7, ebHi7⟩ := k7 bHi bbHi6
  obtain ⟨bp00_7, ep00_7⟩ := k7 p00 bp00_6; obtain ⟨bp01_7, ep01_7⟩ := k7 p01 bp01
  refine wireHoare_bind (wireHoare_wire inputs regs s7 _ _ vp11
    (by simp [evalAt, evalRtlExpr, eaHi7, eaHi6, eaHi5, eaHi4, eaHi3, eaHi, ebHi7, ebHi6, ebHi5, ebHi, vp11]))
    fun p11 s8 k8 ⟨bp11, ep11⟩ => ?_
  obtain ⟨bp00_8, ep00_8⟩ := k8 p00 bp00_7; obtain ⟨bp01_8, ep01_8⟩ := k8 p01 bp01_7; obtain ⟨bp10_8, ep10_8⟩ := k8 p10 bp10
  refine wireHoare_bind (wireHoare_wire inputs regs s8 _ _ vmid32
    (by simp [evalAt, evalRtlExpr, glShift32, glMask32, ep00_8, ep00_7, ep00_6, ep00, ep01_8, ep01_7, ep01, ep10_8, ep10, vmid32]))
    fun mid32 s9 k9 ⟨bmid32, emid32⟩ => ?_
  obtain ⟨bp00_9, ep00_9⟩ := k9 p00 bp00_8; obtain ⟨bp01_9, ep01_9⟩ := k9 p01 bp01_8
  obtain ⟨bp10_9, ep10_9⟩ := k9 p10 bp10_8; obtain ⟨bp11_9, ep11_9⟩ := k9 p11 bp11
  refine wireHoare_bind (wireHoare_wire inputs regs s9 _ _ vlo
    (by simp [evalAt, evalRtlExpr, glShift32, glMask32, ep00_9, ep00_8, ep00_7, ep00_6, ep00, emid32, vlo]))
    fun lo s10 k10 ⟨blo, elo⟩ => ?_
  obtain ⟨bp01_10, ep01_10⟩ := k10 p01 bp01_9; obtain ⟨bp10_10, ep10_10⟩ := k10 p10 bp10_9
  obtain ⟨bp11_10, ep11_10⟩ := k10 p11 bp11_9; obtain ⟨bmid32_10, emid32_10⟩ := k10 mid32 bmid32
  refine wireHoare_bind (wireHoare_wire inputs regs s10 _ _ vhi
    (by simp [evalAt, evalRtlExpr, glShift32, ep11_10, ep11_9, ep11, ep01_10, ep01_9, ep01_8, ep01_7, ep01,
      ep10_10, ep10_9, ep10_8, ep10, emid32_10, emid32, vhi]))
    fun hi s11 k11 ⟨bhi, ehi⟩ => ?_
  obtain ⟨blo_11, elo_11⟩ := k11 lo blo
  refine wireHoare_bind (wireHoare_wire inputs regs s11 _ _ vhiLo
    (by simp [evalAt, evalRtlExpr, glMask32, ehi, vhiLo])) fun hiLo s12 k12 ⟨bhiLo, ehiLo⟩ => ?_
  obtain ⟨blo_12, elo_12⟩ := k12 lo blo_11; obtain ⟨bhi_12, ehi_12⟩ := k12 hi bhi
  refine wireHoare_bind (wireHoare_wire inputs regs s12 _ _ vhiHi
    (by simp [evalAt, evalRtlExpr, glShift32, ehi_12, ehi, vhiHi])) fun hiHi s13 k13 ⟨bhiHi, ehiHi⟩ => ?_
  obtain ⟨blo_13, elo_13⟩ := k13 lo blo_12; obtain ⟨bhiLo_13, ehiLo_13⟩ := k13 hiLo bhiLo
  refine wireHoare_bind (wireHoare_wire inputs regs s13 _ _ vmid
    (by simp [evalAt, evalRtlExpr, glShift32, ehiLo_13, ehiLo, vmid])) fun mid s14 k14 ⟨bmid, emid⟩ => ?_
  obtain ⟨blo_14, elo_14⟩ := k14 lo blo_13; obtain ⟨bhiHi_14, ehiHi_14⟩ := k14 hiHi bhiHi
  refine wireHoare_bind (wireHoare_glCanon inputs regs s14 _ lo) fun loC s15 k15 ⟨bloC, hloCLt, eloC⟩ => ?_
  obtain ⟨bmid_15, emid_15⟩ := k15 mid bmid; obtain ⟨bhiHi_15, ehiHi_15⟩ := k15 hiHi bhiHi_14
  have hmidVal15 : evalAt inputs regs s15 mid = vmid := by rw [emid_15, emid]
  have hmidLt15 : (evalAt inputs regs s15 mid).toNat < goldilocksPrime := by rw [hmidVal15]; exact hMidLtP
  refine wireHoare_bind (wireHoare_glAdd inputs regs s15 _ loC mid bloC bmid_15 hloCLt hmidLt15)
    fun t1 s16 k16 ⟨_, ht1Lt, et1⟩ => ?_
  obtain ⟨_, ehiHi_16⟩ := k16 hiHi bhiHi_15
  have hhiHiVal16 : evalAt inputs regs s16 hiHi = vhiHi := by rw [ehiHi_16, ehiHi_15, ehiHi_14, ehiHi]
  have hhiHiLt16 : (evalAt inputs regs s16 hiHi).toNat < goldilocksPrime := by rw [hhiHiVal16]; exact hHiHiLtP
  have hSub := wireHoare_glSub inputs regs s16 s!"{tag}_red" t1 hiHi ht1Lt hhiHiLt16
  refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, hSub.2.2.2.1, ?_⟩
  rw [hSub.2.2.2.2, hhiHiVal16, et1, hmidVal15, eloC, elo_14, elo_13, elo_12, elo_11, elo]
  have hLoCLt64 : goldilocksCanon64 vlo.toNat < 2 ^ 64 :=
    lt_two_pow_64_of_lt_prime (goldilocksCanon64_spec vlo.isLt).1
  have ht1Lt64 : goldilocksAddSpec (goldilocksCanon64 vlo.toNat) vmid.toNat < 2 ^ 64 :=
    lt_two_pow_64_of_lt_prime (goldilocksAddSpec_spec hLoCLt64 vmid.isLt).1
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLoCLt64, Nat.mod_eq_of_lt ht1Lt64]
  rw [hRedEq]

private theorem wireHoare_glMul (inputs regs : Nat → BitVec 64) (st : WireBuild)
    (tag : String) (a b : RtlExpr)
    (ha : exprWiresLt st.next a = true) (hb : exprWiresLt st.next b = true) :
    WireHoare inputs regs st (glMul tag a b)
      (fun out st1 => exprWiresLt st1.next out = true ∧
        (evalAt inputs regs st1 out).toNat < goldilocksPrime ∧
        evalAt inputs regs st1 out =
          BitVec.ofNat 64 (goldilocksMulSpec (evalAt inputs regs st a).toNat (evalAt inputs regs st b).toNat)) := by
  obtain ⟨hle, hag⟩ := glMul_appendOnly tag a b st inputs regs
  exact ⟨hle, hag, glMul_sound tag a b st inputs regs ha hb⟩

private theorem wireHoare_preserve2 {α β : Type} {inputs regs : Nat → BitVec 64} {st : WireBuild}
    {e1 e2 : RtlExpr} (v1 v2 : BitVec 64)
    (b1 : exprWiresLt st.next e1 = true) (b2 : exprWiresLt st.next e2 = true)
    (hv1 : evalAt inputs regs st e1 = v1) (hv2 : evalAt inputs regs st e2 = v2)
    {m : WireM α} {f : α → WireM β} {Q : β → WireBuild → Prop}
    (hm : WireAppendOnly m)
    (hf : ∀ a st1,
      exprWiresLt st1.next e1 = true → exprWiresLt st1.next e2 = true →
      evalAt inputs regs st1 e1 = v1 → evalAt inputs regs st1 e2 = v2 →
      WireHoare inputs regs st1 (f a) Q) :
    WireHoare inputs regs st (m >>= f) Q := by
  refine wireHoare_bind (wireHoare_of_appendOnly hm) fun a st1 k _ => ?_
  obtain ⟨b1', ev1'⟩ := k e1 b1
  obtain ⟨b2', ev2'⟩ := k e2 b2
  exact hf a st1 b1' b2' (ev1'.trans hv1) (ev2'.trans hv2)

private theorem butterfly_out_arith (u0 v0 w0 : BitVec 64) :
    let cu := (BitVec.ofNat 64 (goldilocksCanon64 u0.toNat)).toNat
    let cv := (BitVec.ofNat 64 (goldilocksCanon64 v0.toNat)).toNat
    let cw := (BitVec.ofNat 64 (goldilocksCanon64 w0.toNat)).toNat
    let vw := (BitVec.ofNat 64 (goldilocksMulSpec cv cw)).toNat
    goldilocksAddSpec cu vw = glN (u0.toNat + goldilocksMulSpec v0.toNat w0.toNat) ∧
    goldilocksSubSpec cu vw = glN (glN u0.toNat + goldilocksPrime - goldilocksMulSpec v0.toNat w0.toNat) := by
  intro cu cv cw vw
  have hpPos : 0 < goldilocksPrime := by unfold goldilocksPrime; omega
  have hc0 := goldilocksCanon64_spec u0.isLt
  have hc1 := goldilocksCanon64_spec v0.isLt
  have hc2 := goldilocksCanon64_spec w0.isLt
  have hc0Lt64 : goldilocksCanon64 u0.toNat < 2 ^ 64 := lt_two_pow_64_of_lt_prime hc0.1
  have hc1Lt64 : goldilocksCanon64 v0.toNat < 2 ^ 64 := lt_two_pow_64_of_lt_prime hc1.1
  have hc2Lt64 : goldilocksCanon64 w0.toNat < 2 ^ 64 := lt_two_pow_64_of_lt_prime hc2.1
  have hcu : cu = goldilocksCanon64 u0.toNat := by simp only [cu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc0Lt64]
  have hcv : cv = goldilocksCanon64 v0.toNat := by simp only [cv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc1Lt64]
  have hcw : cw = goldilocksCanon64 w0.toNat := by simp only [cw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc2Lt64]
  have hMulEq : goldilocksMulSpec cv cw = goldilocksMulSpec v0.toNat w0.toNat := by
    rw [hcv, hcw]; unfold goldilocksMulSpec glN; rw [hc1.2, hc2.2, Nat.mod_mod, Nat.mod_mod]
  have hMulLtP : goldilocksMulSpec v0.toNat w0.toNat < goldilocksPrime := by
    unfold goldilocksMulSpec glN; exact Nat.mod_lt _ hpPos
  have hMulLt64 : goldilocksMulSpec v0.toNat w0.toNat < 2 ^ 64 := lt_two_pow_64_of_lt_prime hMulLtP
  have hvw : vw = goldilocksMulSpec v0.toNat w0.toNat := by
    simp only [vw, hMulEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMulLt64]
  rw [hcu, hvw]
  constructor
  · rw [(goldilocksAddSpec_spec hc0Lt64 hMulLt64).2]
    unfold glN; rw [Nat.add_mod, hc0.2, Nat.mod_mod, ← Nat.add_mod]
  · rw [(goldilocksSubSpec_spec hc0Lt64 hMulLt64).2,
      goldilocksCanon64_of_lt hc0.1, goldilocksCanon64_of_lt hMulLtP, hc0.2]
    rfl

private theorem wireHoare_moduleOutputs (m : WireM (List OutputPort × List RegSpec))
    (name : String) (inNames : List String) (inWidths : List Nat)
    (inputs regs : Nat → BitVec 64)
    (P : List (String × BitVec 64) → Prop)
    (h : WireHoare inputs regs {} m
      (fun res stF => P (res.1.map fun o => (o.name, evalAt inputs regs stF o.expr)))) :
    let r := Id.run (m.run {})
    P (evalModuleOutputs { name := name, inputNames := inNames, inputWidths := inWidths,
                           wires := r.2.wires.toList, regs := r.1.2, outputs := r.1.1 } inputs regs) :=
  h.2.2

/-- **`zkNttCoproc_butterfly_sound`**: for any 64-bit input and register environments,
`zkNttCoprocRtlModule`'s combinational butterfly outputs `"goldilocks_even_out"` and
`"goldilocks_odd_out"` compute canonical `u ± (v * w mod p) mod p` matching `goldilocksMulSpec`. -/
theorem zkNttCoproc_butterfly_sound (inputs regs : Nat → BitVec 64) :
    (evalModuleOutputs zkNttCoprocRtlModule inputs regs).lookup "goldilocks_even_out" =
      some (BitVec.ofNat 64 (glN ((inputs 0).toNat + goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat))) ∧
    (evalModuleOutputs zkNttCoprocRtlModule inputs regs).lookup "goldilocks_odd_out" =
      some (BitVec.ofNat 64 (glN (glN (inputs 0).toNat + goldilocksPrime -
        goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat))) := by
  have hArith := butterfly_out_arith (inputs 0) (inputs 1) (inputs 2)
  refine wireHoare_moduleOutputs buildZkNttCoproc _ _ _ inputs regs
    (fun outs =>
      outs.lookup "goldilocks_even_out" =
        some (BitVec.ofNat 64 (glN ((inputs 0).toNat + goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat))) ∧
      outs.lookup "goldilocks_odd_out" =
        some (BitVec.ofNat 64 (glN (glN (inputs 0).toNat + goldilocksPrime -
          goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat)))) ?_
  unfold buildZkNttCoproc
  refine wireHoare_bind (wireHoare_glCanon inputs regs {} "u" (.inputPort 0)) fun u s1 _ ⟨bu, huLt, eu⟩ => ?_
  refine wireHoare_bind (wireHoare_glCanon inputs regs s1 "v" (.inputPort 1)) fun v s2 k2 ⟨bv, _, ev⟩ => ?_
  obtain ⟨bu2, eu2⟩ := k2 u bu; clear k2
  refine wireHoare_bind (wireHoare_glCanon inputs regs s2 "w" (.inputPort 2)) fun w s3 k3 ⟨bw, _, ew⟩ => ?_
  obtain ⟨bu3, eu3⟩ := k3 u bu2; obtain ⟨bv3, ev3⟩ := k3 v bv; clear k3
  refine wireHoare_bind (wireHoare_of_appendOnly (glCanon_appendOnly "f0" (.inputPort 6))) fun f0 s4 k4 _ => ?_
  obtain ⟨bu4, eu4⟩ := k4 u bu3; obtain ⟨bv4, ev4⟩ := k4 v bv3; obtain ⟨bw4, ew4⟩ := k4 w bw; clear k4
  refine wireHoare_bind (wireHoare_of_appendOnly (glCanon_appendOnly "f1" (.inputPort 7))) fun f1 s5 k5 _ => ?_
  obtain ⟨bu5, eu5⟩ := k5 u bu4; obtain ⟨bv5, ev5⟩ := k5 v bv4; obtain ⟨bw5, ew5⟩ := k5 w bw4; clear k5
  refine wireHoare_bind (wireHoare_glMul inputs regs s5 "vw" v w bv5 bw5) fun vw s6 k6 ⟨bvw, hvwLt, evw⟩ => ?_
  obtain ⟨bu6, eu6⟩ := k6 u bu5; clear k6
  have huLt6 : (evalAt inputs regs s6 u).toNat < goldilocksPrime := by
    rw [eu6, eu5, eu4, eu3, eu2]; exact huLt
  refine wireHoare_bind (wireHoare_glAdd inputs regs s6 "even" u vw bu6 bvw huLt6 hvwLt)
    fun even s7 k7 ⟨beven, _, eeven⟩ => ?_
  obtain ⟨bu7, eu7⟩ := k7 u bu6; obtain ⟨bvw7, evw7⟩ := k7 vw bvw; clear k7
  have huLt7 : (evalAt inputs regs s7 u).toNat < goldilocksPrime := by rw [eu7]; exact huLt6
  have hvwLt7 : (evalAt inputs regs s7 vw).toNat < goldilocksPrime := by rw [evw7]; exact hvwLt
  refine wireHoare_bind (wireHoare_glSub inputs regs s7 "odd" u vw huLt7 hvwLt7)
    fun odd s8 k8 ⟨bodd, _, eodd⟩ => ?_
  obtain ⟨beven8, eeven8⟩ := k8 even beven; clear k8
  have vevenEq : evalAt inputs regs s8 even =
      BitVec.ofNat 64 (glN ((inputs 0).toNat + goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat)) := by
    rw [eeven8, eeven, eu6, eu5, eu4, eu3, eu2, eu, evw, ev5, ev4, ev3, ev, ew5, ew4, ew]
    simp only [evalAt, evalRtlExpr]
    rw [hArith.1]
  have voddEq : evalAt inputs regs s8 odd =
      BitVec.ofNat 64 (glN (glN (inputs 0).toNat + goldilocksPrime -
        goldilocksMulSpec (inputs 1).toNat (inputs 2).toNat)) := by
    rw [eodd, eu7, eu6, eu5, eu4, eu3, eu2, eu, evw7, evw, ev5, ev4, ev3, ev, ew5, ew4, ew]
    simp only [evalAt, evalRtlExpr]
    rw [hArith.2]
  refine wireHoare_preserve2 _ _ beven8 bodd vevenEq voddEq (glAdd_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear beven8 bodd vevenEq voddEq
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glSub_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glSub_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glMul_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glAdd_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glAdd_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glAdd_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glAdd_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glAdd_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glAdd_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glMul_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glAdd_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glMul_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glAdd_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glAdd_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glMul_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glMul_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (glMul_appendOnly _ _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (glMul_appendOnly _ _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (wire_appendOnly _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (wire_appendOnly _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (wire_appendOnly _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (wire_appendOnly _ _)
    fun _ _ b1 b2 h1 h2 => ?_; clear b1' b2' h1' h2'
  refine wireHoare_preserve2 _ _ b1 b2 h1 h2 (wire_appendOnly _ _)
    fun _ _ b1' b2' h1' h2' => ?_; clear b1 b2 h1 h2
  refine wireHoare_preserve2 _ _ b1' b2' h1' h2' (wire_appendOnly _ _)
    fun _ _ _ _ h1 h2 => ?_; clear b1' b2' h1' h2'
  apply wireHoare_pure
  have hneq : ("goldilocks_odd_out" == "goldilocks_even_out") = false := by decide
  simp [List.map, List.lookup, hneq, h1, h2]

/-- **`zkNttCoproc_glMul_sound`**: with `u = 0`, `zkNttCoprocRtlModule`'s `"goldilocks_even_out"`
port outputs canonical `goldilocksMulSpec a.toNat b.toNat` for all 64-bit `a, b : BitVec 64`. -/
theorem zkNttCoproc_glMul_sound (a b : BitVec 64) (regs : Nat → BitVec 64) :
    (evalModuleOutputs zkNttCoprocRtlModule (zkButterflyInputs 0 a.toNat b.toNat) regs).lookup
        "goldilocks_even_out" =
      some (BitVec.ofNat 64 (goldilocksMulSpec a.toNat b.toNat)) := by
  rw [(zkNttCoproc_butterfly_sound (zkButterflyInputs 0 a.toNat b.toNat) regs).1]
  simp only [zkButterflyInputs, BitVec.toNat_ofNat, Nat.zero_mod, BitVec.isLt, Nat.mod_eq_of_lt,
    Nat.zero_add]
  have hpPos : 0 < goldilocksPrime := by unfold goldilocksPrime; omega
  have hMulLtP : goldilocksMulSpec a.toNat b.toNat < goldilocksPrime := by
    unfold goldilocksMulSpec glN; exact Nat.mod_lt _ hpPos
  unfold glN
  rw [Nat.mod_eq_of_lt hMulLtP]

/-- The checks `obend-emit-sv check-zk` runs natively, each with its reason; none is evaluated while
this file elaborates (per-module kernel and native fixtures were what cost the previous version
hours, review/DECISIONS-20261031.md, second round):
1. the module is a DAG and passes the emission gate (`checkRtlModuleW`) and maps to BELs: what lets
   `obend-emit-sv zk` write the file;
2. the butterfly on the carry and borrow corners (`u ≥ p`, all `2^64 - 1`, all `p - 1`,
   `(p-1)^2 = 1`) agrees natively with the `Nat` specification (matching the universal theorems
   `glMul_sound` and `zkNttCoproc_butterfly_sound`);
3. one round through `runModuleTrace` (clear, `(10, 18)`, `(4, 8)`, absorb) reads `14, 26, 38`,
   claim `40`, and a challenge equal to `transcriptAbsorbSpec iv 14 26 38`: the challenge register is
   a function of the absorbed messages and nothing else. -/
def zkBoundaryVectors : List (Nat × Nat × Nat) :=
  [ (0xFFFFFFFF00000003, 2, 1), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
    (18446744069414584320, 18446744069414584320, 18446744069414584320),
    (1, 0xFFFFFFFF00000000, 0xFFFFFFFF00000000), (0, 18446744069414584320, 1),
    (0x00000000FFFFFFFF, 0xFFFFFFFF00000005, 0xFFFFFFFF00000007) ]

def zkCheckGate : Bool :=
  checkRtlModule zkNttCoprocRtlModule && checkRtlModuleW zkNttCoprocRtlModule &&
  checkBelNetlistValid (synthesizeModuleToBels zkNttCoprocRtlModule)

def zkCheckButterfly : Bool :=
  zkBoundaryVectors.all fun (u, v, w) =>
    let outs := evalModuleOutputs zkNttCoprocRtlModule (zkButterflyInputs u v w) (fun _ => 0#64)
    outs.lookup "goldilocks_even_out" == some (BitVec.ofNat 64 (glN (u + goldilocksMulSpec v w))) &&
    outs.lookup "goldilocks_odd_out" ==
      some (BitVec.ofNat 64 (glN (glN u + goldilocksPrime - goldilocksMulSpec v w)))

def zkCheckTranscriptRound : Bool :=
  let regs := runModuleTrace zkNttCoprocRtlModule (fun _ => 0#64)
    [ (true, fun _ => 0#64)
    , (false, zkSumcheckInputs 1 0 0 0 0)
    , (false, zkSumcheckInputs 0 1 0 10 18)
    , (false, zkSumcheckInputs 0 1 0 4 8)
    , (false, zkSumcheckInputs 0 0 1 0 0) ]
  let outs := evalModuleOutputs zkNttCoprocRtlModule (zkSumcheckInputs 0 0 0 0 0) regs
  outs.lookup "sc_g0_out" == some 14#64 && outs.lookup "sc_g1_out" == some 26#64 &&
  outs.lookup "sc_g2_out" == some 38#64 && outs.lookup "sc_round_claim_out" == some 40#64 &&
  outs.lookup "sc_pair_cnt_out" == some 2#64 &&
  outs.lookup "sc_challenge_out" == some (BitVec.ofNat 64 (transcriptAbsorbSpec transcriptIv 14 26 38))

/-! ## 4. The Lean run of the 8-round protocol (the golden the harness compares the RTL against) -/

/-- The 256 hypercube values the harness uses: `p - 17 - (i + 1) * K`, full-width so every round wraps. -/
def zkGoldenTable : List Nat :=
  (List.range 256).map fun i =>
    glN (goldilocksPrime - 17 + goldilocksPrime - glN ((i + 1) * 0x7FEDBCA987654321))

def pairsOf : List Nat → List (Nat × Nat)
  | f0 :: f1 :: rest => (f0, f1) :: pairsOf rest
  | _ => []

/-- One round at the `Nat` level: the three accumulators, the transcript absorb, the verifier's
claim check and update, and the fold with the new challenge. -/
def zkGoldenRound (table : List Nat) (t claim : Nat) :
    (List Nat × Nat × Nat × Nat × Nat × Nat × Bool) :=
  let ps := pairsOf table
  let g0 := ps.foldl (fun a p => glN (a + p.1)) 0
  let g1 := ps.foldl (fun a p => glN (a + p.2)) 0
  let g2 := ps.foldl (fun a p => glN (a + glN (p.2 + p.2 + goldilocksPrime - p.1))) 0
  let t' := transcriptAbsorbSpec t g0 g1 g2
  let ok := glN (g0 + g1) == claim
  let claim' := glN (g0 + goldilocksMulSpec t' (glN (g1 + goldilocksPrime - g0)))
  let table' := ps.map fun p => glN (p.1 + goldilocksMulSpec t' (glN (p.2 + goldilocksPrime - p.1)))
  (table', t', claim', g0, g1, g2, ok)

def zkGoldenRounds : Nat → Nat → List Nat → Nat → Nat → List String → List String
  | 0, _, table, _, claim, acc =>
    acc.reverse ++ [s!"final={table.headD 0}", s!"final_claim={claim}"]
  | k + 1, round, table, t, claim, acc =>
    let (table', t', claim', g0, g1, g2, ok) := zkGoldenRound table t claim
    let lines :=
      [ s!"round{round}_g0={g0}", s!"round{round}_g1={g1}", s!"round{round}_g2={g2}"
      , s!"round{round}_challenge={t'}", s!"round{round}_claim_ok={if ok then 1 else 0}"
      , s!"round{round}_next_claim={claim'}" ]
    zkGoldenRounds k (round + 1) table' t' claim' (lines.reverse ++ acc)

/-- `key=value` lines of the 8-round run (`obend-emit-sv golden-zk`,
`apps/zk-ntt/verilator/zk_ntt_golden.txt`). -/
def zkSumcheckGolden : String :=
  let claim0 := zkGoldenTable.foldl (fun a x => glN (a + x)) 0
  let lines := zkGoldenRounds 8 0 zkGoldenTable transcriptIv claim0 []
  "# Generated by obend-emit-sv golden-zk from Obend.Apps.ZkNtt.zkSumcheckGolden\n" ++
  s!"iv={transcriptIv}\nclaim0={claim0}\n" ++ String.intercalate "\n" lines ++ "\n"

end Obend.Apps.ZkNtt
end
