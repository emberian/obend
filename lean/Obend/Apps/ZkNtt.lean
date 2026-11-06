module
/-
# Obend.Apps.ZkNtt — Flagship App #4: Goldilocks ZK-NTT butterfly + multilinear sumcheck co-processor

Elaborates the 4-module Goldilocks `.obend` hierarchy (`apps/zk-ntt/`): `GoldilocksField.obend`
(the prime $p = 2^{64} - 2^{32} + 1$, canonical `fieldAdd`/`fieldSub`, the 32-bit-limb `fieldMul`
with the shift/mask 128-to-64 reduction), `NttButterflyRadix2.obend`, `SumcheckRoundPoly.obend`
(round accumulators, folding, and `transcriptAbsorb`, the Fiat–Shamir step) and `ZkNttSumcheckTop.obend`.

What is proved: the `.obend` cross-module values (`zk_ntt_workbook_eval_sound`), the Goldilocks
congruences, and `goldilocksReduce128Spec_sound`: for every `lo, hi < 2^64` the shift/mask
reduction the hardware uses equals `(lo + 2^64 * hi) % p` and is canonical.

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

What is not here: a theorem that `glMul`'s wire network equals `goldilocksMulSpec` for every input
(the Nat-level reduction lemma is proved; the limb schedule is checked on the harness's 2048
butterflies and on the boundary vectors in the fixtures below), and any claim that the transcript
permutation is a cryptographic hash.
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

/-- The checks `obend-emit-sv check-zk` runs natively, each with its reason; none is evaluated while
this file elaborates (per-module kernel and native fixtures were what cost the previous version
hours, review/DECISIONS-20261031.md, second round):
1. the module is a DAG and passes the emission gate (`checkRtlModuleW`) and maps to BELs: what lets
   `obend-emit-sv zk` write the file;
2. the butterfly on the carry and borrow corners (`u ≥ p`, all `2^64 - 1`, all `p - 1`,
   `(p-1)^2 = 1`) equals the `Nat` specification: `glMul`'s limb schedule is not proved against
   `goldilocksMulSpec`, and these are the inputs that distinguish a wrong carry;
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
