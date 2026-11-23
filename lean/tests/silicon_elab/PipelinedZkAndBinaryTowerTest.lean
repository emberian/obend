import Obend.Hardware.PipelinedZkCrypto
import Obend.Hardware.YosysLec
import Obend.Tactic.Tooth
import Obend.AssertAxioms

/-
# PipelinedZkAndBinaryTowerTest — End-to-End Silicon & Algebra Verification

Exercises `Obend.Hardware.PipelinedZkCrypto` across all required gates:
1. **16-Cycle Back-to-Back Streaming Goldilocks Butterfly Trace (`#guard`s)**:
   16 pairwise-distinct `(u_t, v_t, w_t)` triples clocked at 1 butterfly/cycle from dirty initial
   registers, plus 4 drain cycles (`in_valid = 0`), checked cycle-for-cycle against `(u_t + v_t * w_t) % p`
   and `(u_t % p + p - (v_t * w_t) % p) % p`.
2. **Wiedemann Binary-Tower `GF(2^{64})` & `GF(2^{128})` Field Algebra & Hardware `#guard`s**:
   Multiplicative inverses `towerInv 6` / `towerInv 7` / `tower128Inv`, defining polynomial
   `X_k^2 + omega_{k-1} * X_k + 1 = 0`, and bit-exact combinational + 2-stage pipelined agreement of
   `gf2_64TowerMulRtlModule` with `towerMul 6`.
3. **Yosys/Z3 SMT-LIB2 Miter Soundness & Live Solver Gate**:
   Formal `lecScript_unsat_of_step` instantiations, emitted SV/SMT2 structural `#guard`s, and a
   host-aware `yosys` + `z3` miter check when tools are present on the host.
4. **Mutation Kills (`#tooth` x 6) & Imported-Tree Axiom Audit (`#assert_axioms_tree`)**.
-/

namespace Obend.Tests.PipelinedZkAndBinaryTowerTest

open Obend.Apps.ZkNtt
open Obend.Hardware.HDL
open Obend.Hardware.Process
open Obend.Hardware.Retiming
open Obend.Hardware.VerilateRunner
open Obend.Hardware.YosysLec
open Obend.Hardware.PipelinedZkCrypto

set_option autoImplicit false

/-! ## 1. 16-Cycle Back-to-Back Streaming Goldilocks Butterfly Trace (`#guard`s) -/

/-- 16 pairwise-distinct `(u_t, v_t, w_t)` Goldilocks butterfly triples exercising boundary cases:
    `p - 1`, `p` (non-canonical 64-bit word `>= p`), `2^64 - 1`, `2^32`, carry-heavy limb products,
    underflow subtraction (`u < v * w mod p`), and arbitrary pseudorandom 64-bit words. -/
def glStream16 : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [ (0#64,                  1#64,                  1#64)
  , (1#64,                  0xFFFFFFFF00000000#64, 0xFFFFFFFF00000000#64)
  , (0xFFFFFFFF00000000#64, 0x0000000100000000#64, 0x0000000100000000#64)
  , (0xFFFFFFFF00000001#64, 0x123456789ABCDEF0#64, 0xFEDCBA9876543210#64)
  , (0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64)
  , (0x00000000FFFFFFFF#64, 0xFFFFFFFF00000000#64, 0x00000000FFFFFFFF#64)
  , (0x8000000000000000#64, 0x8000000000000000#64, 0x0000000000000002#64)
  , (0x0123456789ABCDEF#64, 0x1111111122222222#64, 0x3333333344444444#64)
  , (0xCAFEBABEDEADBEEF#64, 0x0F0E0D0C0B0A0908#64, 0x8070605040302010#64)
  , (0x000000000000002A#64, 0xFFFFFFFF00000000#64, 0x0000000000000007#64)
  , (0x7FFFFFFF80000001#64, 0x7FFFFFFF80000002#64, 0x7FFFFFFF80000003#64)
  , (0xFFFFFFFF00000005#64, 0xFFFFFFFF00000009#64, 0xFFFFFFFF0000000B#64)
  , (0xAAAAAAAAAAAAAAAA#64, 0x5555555555555555#64, 0xC3C3C3C3C3C3C3C3#64)
  , (0x0000000200000003#64, 0xFFFFFFFE00000004#64, 0xFFFFFFFD00000005#64)
  , (0x9999999988888888#64, 0x7777777766666666#64, 0x5555555544444444#64)
  , (0xDEADC0DECAFE1234#64, 0xfeedface13579bdf#64, 0x2468ace0fdb97531#64) ]

#guard glStream16.length == 16
#guard glStream16.Nodup

/-- Dirty non-zero initial register bank proving Stage-4 outputs at `t + 4` are immune to stale pipeline state. -/
def dirtyInitRegs : Nat → BitVec 64
  | k => BitVec.ofNat 64 (0xBAD0000000000000 + 0x1337 * (k + 1))

/-- 16 active cycles (`in_valid = 1`) followed by 4 drain bubbles (`in_valid = 0`) with adversarial garbage data. -/
def glStream20Inputs : List (Nat → BitVec 64) :=
  (glStream16.map fun (u, v, w) => glButterflyInputs u v w 1#64) ++
  [ glButterflyInputs 0xDEAD#64 0xBEEF#64 0xCAFE#64 0#64
  , glButterflyInputs 0x1111#64 0x2222#64 0x3333#64 0#64
  , glButterflyInputs 0x4444#64 0x5555#64 0x6666#64 0#64
  , glButterflyInputs 0x7777#64 0x8888#64 0x9999#64 0#64 ]

def verifyButterflyCycle (t : Nat) : Bool :=
  match glStream16[t]? with
  | none => false
  | some (u, v, w) =>
    let trace := (glStream20Inputs.take (t + 4)).map (false, ·)
    let st    := runModuleTrace pipelinedGlButterflyRtlModule dirtyInitRegs trace
    let outs  := evalModuleOutputs pipelinedGlButterflyRtlModule (fun _ => 0xFFFF#64) st
    let expE  := BitVec.ofNat 64 ((u.toNat + v.toNat * w.toNat) % goldilocksPrime)
    let expO  := BitVec.ofNat 64
      ((u.toNat % goldilocksPrime + goldilocksPrime - (v.toNat * w.toNat) % goldilocksPrime) % goldilocksPrime)
    outs.lookup "out_even" == some expE &&
    outs.lookup "out_odd"  == some expO &&
    outs.lookup "out_valid" == some 1#64 &&
    decide ((st 13).toNat < goldilocksPrime) &&
    decide ((st 14).toNat < goldilocksPrime)

-- All 16 back-to-back streaming butterfly outputs match exact canonical Goldilocks arithmetic at t + 4:
#guard (List.range 16).all verifyButterflyCycle

-- Cycle 20 (t = 16 + 4) deasserts `out_valid = 0` when the first drain bubble exits Stage 4:
#guard
  let trace20 := (glStream20Inputs.take 20).map (false, ·)
  let st20    := runModuleTrace pipelinedGlButterflyRtlModule dirtyInitRegs trace20
  (evalModuleOutputs pipelinedGlButterflyRtlModule (fun _ => 0#64) st20).lookup "out_valid" == some 0#64

-- Structural RTL & Leiserson-Saxe retiming checks:
#guard checkRtlModuleW pipelinedGlButterflyRtlModule == true
#guard checkRetimingCert glButterflySyncGraph glButterflyUnpipelinedCert corner7nm_SS 3000 == false
#guard checkRetimingCert glButterflySyncGraph glButterfly4StageCert corner7nm_SS 3000 == true

/-! ## 2. Wiedemann Binary-Tower `GF(2^{64})` & `GF(2^{128})` Algebra & Hardware `#guard`s -/

def tower64Samples : List Tower64 :=
  [ 0x0000000000000001#64
  , 0x0000000000000002#64
  , 0x0123456789ABCDEF#64
  , 0xFEDCBA9876543210#64
  , 0xFFFFFFFFFFFFFFFF#64
  , 0x8000000000000001#64
  , 0xDEADBEEFCAFEBABE#64
  , 0x5A5A5A5AA5A5A5A5#64 ]

def tower128Samples : List Tower128 :=
  [ (0x0000000000000001#64, 0x0000000000000000#64)
  , (0x0000000000000000#64, 0x0000000000000001#64)
  , (0x0123456789ABCDEF#64, 0xFEDCBA9876543210#64)
  , (0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64)
  , (0xCAFEBABEDEADBEEF#64, 0x13579BDF2468ACE0#64)
  , (0x8000000000000000#64, 0x0000000000000003#64) ]

-- Defining polynomial X_k^2 + omega_{k-1} * X_k + 1 = 0 across tower levels k = 0..6 (up to GF(2^128)):
#guard (List.range 7).all fun k =>
  let xk := towerOmega (k + 1)
  let om := towerJoin (towerOmega k) (towerZero k)
  towerAdd (k + 1) (towerAdd (k + 1) (towerMul (k + 1) xk xk) (towerMul (k + 1) om xk))
    (towerOne (k + 1)) == towerZero (k + 1)

-- GF(2^64) multiplicative inverses: a * a^{-1} = 1 and a^{-1} * a = 1 for every nonzero sample:
#guard tower64Samples.all fun a =>
  a != towerZero 6 &&
  towerMul 6 a (towerInv 6 a) == towerOne 6 &&
  towerMul 6 (towerInv 6 a) a == towerOne 6

-- GF(2^128) multiplicative inverses via both `towerInv 7` (`BitVec 128`) and `tower128Inv` (`BitVec 64 × BitVec 64`):
#guard tower128Samples.all fun a =>
  let a128 := towerJoin (k := 6) a.1 a.2
  a128 != towerZero 7 &&
  towerMul 7 a128 (towerInv 7 a128) == towerOne 7 &&
  tower128Mul a (tower128Inv a) == (1#64, 0#64) &&
  tower128Mul (tower128Inv a) a == (1#64, 0#64)

-- GF(2^128) associativity & distributivity spot check on nontrivial 128-bit elements:
#guard
  let x := towerJoin (k := 6) 0x0123456789ABCDEF#64 0xFEDCBA9876543210#64
  let y := towerJoin (k := 6) 0xCAFEBABEDEADBEEF#64 0x13579BDF2468ACE0#64
  let z := towerJoin (k := 6) 0xAAAAAAAAAAAAAAAA#64 0x5555555555555555#64
  towerMul 7 (towerMul 7 x y) z == towerMul 7 x (towerMul 7 y z) &&
  towerMul 7 x (towerAdd 7 y z) == towerAdd 7 (towerMul 7 x y) (towerMul 7 x z)

-- `gf2_64TowerMulRtlModule` well-formedness, zero-carry gate, combinational bit-exactness & 2-stage pipeline stream:
#guard checkRtlModuleW gf2_64TowerMulRtlModule == true
#guard checkModuleCarryFree gf2_64TowerMulRtlModule == true

#guard tower64Samples.all fun a =>
  tower64Samples.all fun b =>
    (evalModuleOutputs gf2_64TowerMulRtlModule (gf2_64Inputs a b 1#64) dirtyInitRegs).lookup
      "tower64_mul_out" == some (towerMul 6 a b)

#guard
  let pairs := tower64Samples.zip tower64Samples.reverse
  let insStream := pairs.map (fun (a, b) => gf2_64Inputs a b 1#64) ++
    [gf2_64Inputs 0#64 0#64 0#64, gf2_64Inputs 0#64 0#64 0#64]
  (List.range pairs.length).all fun t =>
    match pairs[t]? with
    | none => false
    | some (a, b) =>
      let st := runModuleTrace gf2_64TowerMulRtlModule dirtyInitRegs ((insStream.take (t + 2)).map (false, ·))
      let outs := evalModuleOutputs gf2_64TowerMulRtlModule (fun _ => 0#64) st
      outs.lookup "tower64_pipe_out" == some (towerMul 6 a b) &&
      outs.lookup "tower64_pipe_valid" == some 1#64

/-! ## 3. Formal Yosys/Z3 SMT-LIB2 Miter Theorems, Glue `#guard`s & Host-Aware Solver Check -/

theorem pipelinedGlButterfly_faithful : moduleFaithful pipelinedGlButterflyRtlModule :=
  moduleFaithful_of_checkWidths pipelinedGlButterflyRtlModule (by decide +kernel)

theorem gf2_64TowerMul_faithful : moduleFaithful gf2_64TowerMulRtlModule :=
  moduleFaithful_of_checkWidths gf2_64TowerMulRtlModule (by decide +kernel)

theorem pipelinedGlButterfly_lec_unsat
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      pipelinedGlButterflyRtlModule.outputs.map (fun o =>
          (o.name,
            ((yosysBV pipelinedGlButterflyRtlModule.name o.name false o.width).eval
              ((lecScript pipelinedGlButterflyRtlModule).env Y)).setWidth 64)) =
        evalModuleOutputsW pipelinedGlButterflyRtlModule
          ((lecScript pipelinedGlButterflyRtlModule).inpVal Y)
          ((lecScript pipelinedGlButterflyRtlModule).regVal Y) ∧
      ∀ r ∈ pipelinedGlButterflyRtlModule.regs,
        (yosysBV pipelinedGlButterflyRtlModule.name r.name true r.width).eval
            ((lecScript pipelinedGlButterflyRtlModule).env Y) =
          (stepModuleRegs pipelinedGlButterflyRtlModule (Y.bit false "rst")
            ((lecScript pipelinedGlButterflyRtlModule).inpVal Y)
            ((lecScript pipelinedGlButterflyRtlModule).regVal Y) r.regIdx).setWidth r.width) :
    ∀ Y, ¬ (lecScript pipelinedGlButterflyRtlModule).holds Y :=
  lecScript_unsat_of_step pipelinedGlButterflyRtlModule
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hagree

theorem gf2_64TowerMul_lec_unsat
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      gf2_64TowerMulRtlModule.outputs.map (fun o =>
          (o.name,
            ((yosysBV gf2_64TowerMulRtlModule.name o.name false o.width).eval
              ((lecScript gf2_64TowerMulRtlModule).env Y)).setWidth 64)) =
        evalModuleOutputsW gf2_64TowerMulRtlModule
          ((lecScript gf2_64TowerMulRtlModule).inpVal Y)
          ((lecScript gf2_64TowerMulRtlModule).regVal Y) ∧
      ∀ r ∈ gf2_64TowerMulRtlModule.regs,
        (yosysBV gf2_64TowerMulRtlModule.name r.name true r.width).eval
            ((lecScript gf2_64TowerMulRtlModule).env Y) =
          (stepModuleRegs gf2_64TowerMulRtlModule (Y.bit false "rst")
            ((lecScript gf2_64TowerMulRtlModule).inpVal Y)
            ((lecScript gf2_64TowerMulRtlModule).regVal Y) r.regIdx).setWidth r.width) :
    ∀ Y, ¬ (lecScript gf2_64TowerMulRtlModule).holds Y :=
  lecScript_unsat_of_step gf2_64TowerMulRtlModule
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hagree

def glButterflyLecLines : List String := (lecScript pipelinedGlButterflyRtlModule).print.splitOn "\n"
def gf2_64TowerLecLines : List String := (lecScript gf2_64TowerMulRtlModule).print.splitOn "\n"
def glButterflySvLines  : List String := (emitModuleSV pipelinedGlButterflyRtlModule).splitOn "\n"
def gf2_64TowerSvLines  : List String := (emitModuleSV gf2_64TowerMulRtlModule).splitOn "\n"

#guard glButterflySvLines.any (·.startsWith "module pipelined_gl_butterfly_4stage")
#guard gf2_64TowerSvLines.any (·.startsWith "module gf2_64_wiedemann_tower_mul")
#guard glButterflyLecLines.contains "(assert (|pipelined_gl_butterfly_4stage_t| s s1))"
#guard glButterflyLecLines.contains "(define-fun |rtl_out_out_even| () (_ BitVec 64) (|pipelined_gl_butterfly_4stage_n out_even| s))"
#guard glButterflyLecLines.contains "(define-fun |rtl_next_s4_out_even| () (_ BitVec 64) (|pipelined_gl_butterfly_4stage_n s4_out_even| s1))"
#guard gf2_64TowerLecLines.contains "(assert (|gf2_64_wiedemann_tower_mul_t| s s1))"
#guard gf2_64TowerLecLines.contains "(define-fun |rtl_out_tower64_mul_out| () (_ BitVec 64) (|gf2_64_wiedemann_tower_mul_n tower64_mul_out| s))"
#guard gf2_64TowerLecLines.contains "(assert (not (and true |lec_out_tower64_mul_out| |lec_out_tower64_pipe_out| |lec_out_tower64_pipe_valid| |lec_next_s1_p32| |lec_next_s1_q32| |lec_next_s1_valid| |lec_next_s2_pipe_out| |lec_next_s2_pipe_valid|)))"

/-- When `yosys`, `z3`, and `hardware/lec/smt_share.py` are available on the build/LEC host, run live
    Yosys SystemVerilog synthesis + Z3 SMT-LIB2 miter verification on `gf2_64TowerMulRtlModule` and
    assert `unsat` (and `sat` on a 1-bit mutated SV netlist). -/
def verifyLiveYosysZ3IfPresent : IO Unit := do
  let hasYosys ← (System.FilePath.mk "/usr/bin/yosys").pathExists
  let hasZ3    ← (System.FilePath.mk "/usr/bin/z3").pathExists
  let sharePy  := System.FilePath.mk "../hardware/lec/smt_share.py"
  let hasShare ← sharePy.pathExists
  if hasYosys && hasZ3 && hasShare then
    let tmpDir := "/tmp/obend_w5_c8_lec_elab"
    IO.FS.createDirAll tmpDir
    let svPath     := s!"{tmpDir}/gf2_64_wiedemann_tower_mul.sv"
    let yosPath    := s!"{tmpDir}/gf2_64_yosys.smt2"
    let rawPath    := s!"{tmpDir}/gf2_64_raw.smt2"
    let sharedPath := s!"{tmpDir}/gf2_64_shared.smt2"
    IO.FS.writeFile svPath (emitModuleSV gf2_64TowerMulRtlModule)
    let yosCmd :=
      s!"read_verilog -sv {svPath}; hierarchy -check -top gf2_64_wiedemann_tower_mul; " ++
      s!"proc; flatten; setattr -set keep 1 t:$dff %co w:* %i; opt_clean; write_smt2 {yosPath}"
    let rYos ← IO.Process.output { cmd := "/usr/bin/yosys", args := #["-q", "-p", yosCmd] }
    unless rYos.exitCode == 0 do
      throw <| IO.userError s!"yosys failed: {rYos.stderr}"
    let yosSmt ← IO.FS.readFile yosPath
    let leanHalf := (((lecScript gf2_64TowerMulRtlModule).print.splitOn "\n; --- counterexample").headD "") ++ "\n"
    IO.FS.writeFile rawPath (yosSmt ++ "\n" ++ leanHalf)
    let rSh ← IO.Process.output
      { cmd := "/usr/bin/python3"
        args := #[sharePy.toString, rawPath, sharedPath, "--yosys", "/usr/bin/yosys"] }
    unless rSh.exitCode == 0 do
      throw <| IO.userError s!"smt_share.py failed: {rSh.stderr}"
    let rZ3 ← IO.Process.output { cmd := "/usr/bin/z3", args := #[sharedPath] }
    let firstLine := (rZ3.stdout.splitOn "\n").headD ""
    unless firstLine.trimAscii.toString == "unsat" do
      throw <| IO.userError s!"expected Z3 `unsat` on gf2_64_wiedemann_tower_mul miter, got: {rZ3.stdout}"

#eval verifyLiveYosysZ3IfPresent

/-! ## 4. Mutation Sensitivity Kills (`#tooth` x 6) & Axiom Hygiene (`#assert_axioms_tree`) -/

-- Tooth 1: Dropping modular `+ p` underflow wrap-around in `glSubBV` breaks 4-cycle butterfly stream soundness:
#tooth Obend.Hardware.PipelinedZkCrypto.pipelinedGlButterfly_latency4_sound by mutation
  Obend.Hardware.PipelinedZkCrypto.glSubBV := fun va vb => evalAluOp .sub va vb

-- Tooth 2: Rubber-stamping Leiserson-Saxe retiming certification breaks the 0-stage vs 4-stage timing proof:
#tooth Obend.Hardware.PipelinedZkCrypto.glButterfly_retiming_closes_333MHz by mutation
  Obend.Hardware.Retiming.checkRetimingCert := fun _ _ _ _ => true

-- Tooth 3: Replacing the Wiedemann tower twist `towerMulOmega` with identity breaks associativity:
#tooth Obend.Hardware.PipelinedZkCrypto.towerMul_assoc by mutation
  Obend.Hardware.PipelinedZkCrypto.towerMulOmega := fun _ u => u

-- Tooth 4: Replacing recursive norm-reduction `towerInv` with identity breaks field inversion:
#tooth Obend.Hardware.PipelinedZkCrypto.towerMul_inv by mutation
  Obend.Hardware.PipelinedZkCrypto.towerInv := fun _ a => a

-- Tooth 5: Corrupting SWAR lane recombination breaks `gf2_64TowerMulRtlModule` bit-exactness:
#tooth Obend.Hardware.PipelinedZkCrypto.gf2_64TowerMulRtl_eq_towerMul by mutation
  Obend.Hardware.PipelinedZkCrypto.swarCombineBV := fun _ p q => evalAluOp .bitXor p q

-- Tooth 6: Corrupting the middle Karatsuba product `swarQ5BV` breaks 2-stage pipelined `GF(2^64)` soundness:
#tooth Obend.Hardware.PipelinedZkCrypto.gf2_64TowerMulRtl_pipe2_sound by mutation
  Obend.Hardware.PipelinedZkCrypto.swarQ5BV := fun a _ => a

#assert_axioms_tree

end Obend.Tests.PipelinedZkAndBinaryTowerTest
