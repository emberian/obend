import Obend.Hardware.YosysLec
import Obend.Hardware.Synth
import Obend.Hardware.PipelinedRisc
import Obend.Hardware.PipelinedZkCrypto
import Obend.Hardware.OspcProver
import Obend.Tactic.Tooth

/-!
# `Obend.Hardware.YosysLec`: the printed LEC file against its model and the committed files

The library module proves what `lecScript m` means (`lecScript_holds_iff`) and prints it. These
tests pin the print: every `RtlExpr` constructor against `VerilateRunner.emitExprSmt2`, the glue
lines of committed files verbatim, and all six committed `hardware/sim/*_lec.smt2` files byte-for-byte.
-/

namespace Obend.Tests.YosysLecTest
open Obend.Hardware.HDL Obend.Hardware.VerilateRunner Obend.Hardware.YosysLec
open Obend.Hardware.PipelinedRisc Obend.Hardware.PipelinedZkCrypto Obend.Hardware.OspcProver

/-- One expression per `RtlExpr` constructor, `RtlAluOp` and `RtlWidthOp` (and the out-of-range
`sext` the emitter prints as its operand). -/
def printProbes : List RtlExpr :=
  let a : RtlExpr := .inputPort 0
  let b : RtlExpr := .regRead 2
  let ops : List RtlAluOp :=
    [.add, .sub, .mul, .bitAnd, .bitOr, .bitXor, .shl, .lshr, .ashr, .eq, .ult, .slt, .qmul32]
  ops.map (fun op => .alu op a b) ++
  [ .const 0xdeadbeef#64, .wireRef 7, .mux (.wireRef 1) a b, .bitNot (.alu .add a (.const 1#64)),
    .resize (.slice 15 4) a, .resize (.zext 32) b, .resize (.sext 8 32) a, .resize (.sext 0 9) a,
    .resize (.trunc 12) (.alu .mul a b),
    .mux (.alu .ult a b) (.resize (.sext 16 64) (.alu .qmul32 a b)) (.bitNot (.resize (.slice 63 32) b)) ]

#guard printProbes.all fun e => (smtOf e).print "spec_" == emitExprSmt2 "spec_" e
#guard (smtOf (.alu .shl (.inputPort 0) (.regRead 1))).print "spec_" ==
  "(bvshl in_0 (bvand r_1 #x000000000000003f))"
#guard (smtOf (.resize (.sext 8 32) (.wireRef 3))).print "spec_" ==
  "((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) spec_w_3)))"

/-- SMT-LIB's division by zero, which the model follows: all-ones quotient, dividend remainder. -/
example : (SmtBV.bin .udiv (.lit 5#64) (.lit 0#64)).eval { inp := fun _ => 0, wire := fun _ => 0, reg := fun _ => 0 } =
    BitVec.allOnes 64 := by decide
example : (SmtBV.bin .urem (.lit 5#64) (.lit 0#64)).eval { inp := fun _ => 0, wire := fun _ => 0, reg := fun _ => 0 } =
    5#64 := by decide

/-- All 4 synthesizable `ospcTileDatapathRtl` modules and both `PipelinedZkCrypto` vaults pass
`checkRtlModuleW` and `YosysLec.moduleFaithful`. -/
theorem ospcTileDatapathRtl_faithful (t : Fin 4) :
    checkRtlModule (ospcTileDatapathRtl t) = true ∧
    checkRtlModuleW (ospcTileDatapathRtl t) = true ∧
    moduleFaithful (ospcTileDatapathRtl t) = true := by
  obtain ⟨hm, hmw, hw⟩ := ospcTileDatapathRtl_wellFormed t
  exact ⟨hm, hmw, moduleFaithful_of_checkWidths (ospcTileDatapathRtl t) hw⟩

theorem pipelinedZkVaults_faithful (u : Unit) (hu : u = ()) :
    checkRtlModuleW pipelinedGlButterflyRtlModule = true ∧
    moduleFaithful pipelinedGlButterflyRtlModule = true ∧
    checkRtlModuleW gf2_64TowerMulRtlModule = true ∧
    moduleFaithful gf2_64TowerMulRtlModule = true := by
  obtain ⟨hw1, hcw1⟩ := pipelinedGlButterfly_wellFormed u hu
  obtain ⟨hw2, hcw2, _⟩ := gf2_64TowerMulRtl_wellFormed u hu
  exact ⟨hw1, moduleFaithful_of_checkWidths _ hcw1, hw2, moduleFaithful_of_checkWidths _ hcw2⟩

/-! ## Glue lines, verbatim from the committed files -/

def probeLines : List String := (lecScript widthProbeTwoClockRtl).print.splitOn "\n"
def mac2Lines  : List String := (lecScript Obend.Hardware.Synth.retimedMac2StageRtl).print.splitOn "\n"
def riscLines  : List String := (lecScript pipelinedRiscCoreRtlModule).print.splitOn "\n"
def ospc0Lines : List String := (lecScript (ospcTileDatapathRtl ⟨0, by decide⟩)).print.splitOn "\n"

-- a narrow input and a 1-bit input (Yosys's `Bool`) zero-extended to the 64-bit word
#guard probeLines.contains "(define-fun in_2 () (_ BitVec 64) ((_ zero_extend 48) (|obend_width_probe_n c| s)))"
#guard probeLines.contains "(define-fun in_3 () (_ BitVec 64) ((_ zero_extend 63) (ite (|obend_width_probe_n flag| s) #b1 #b0)))"
-- a narrow register read in `s`, a 1-bit register in `s1`, and a reset wrapper cut to the register's width
#guard probeLines.contains "(define-fun r_0 () (_ BitVec 64) ((_ zero_extend 48) (|obend_width_probe_n acc| s)))"
#guard probeLines.contains "(define-fun |rtl_next_flag_q| () (_ BitVec 1) (ite (|obend_width_probe_n flag_q| s1) #b1 #b0))"
#guard probeLines.contains "(define-fun |spec_next_flag_q| () (_ BitVec 1) ((_ extract 0 0) (ite (|obend_width_probe_n rst_core| s) #x0000000000000000 in_3)))"
-- an output at its port width
#guard probeLines.contains "(define-fun |spec_out_acc_out| () (_ BitVec 16) ((_ extract 15 0) r_0))"
-- the two states, the miter and a 64-bit register
#guard mac2Lines.contains "(assert (|obend_retimed_mac2_t| s s1))"
#guard mac2Lines.contains "(define-fun |rtl_next_mulReg| () (_ BitVec 64) (|obend_retimed_mac2_n mulReg| s1))"
#guard mac2Lines.contains "(assert (not (and true |lec_out_mac_out| |lec_next_mulReg| |lec_next_cReg| |lec_next_outReg|)))"
-- RISC64 & OSPC Tile 0 LEC obligations:
#guard riscLines.contains "(assert (|pipelined_risc_core_5stage_t| s s1))"
#guard riscLines.contains "(define-fun |rtl_out_ex_alu_out| () (_ BitVec 64) (|pipelined_risc_core_5stage_n ex_alu_out| s))"
#guard riscLines.contains "(define-fun |rtl_next_fetch_pc| () (_ BitVec 64) (|pipelined_risc_core_5stage_n fetch_pc| s1))"
#guard ospc0Lines.contains "(assert (|obend_ospc_tile0_t| s s1))"
#guard ospc0Lines.contains "(define-fun |rtl_out_out_face_hi17| () (_ BitVec 17) (|obend_ospc_tile0_n out_face_hi17| s))"
#guard ospc0Lines.contains "(define-fun |rtl_next_cam_q| () (_ BitVec 64) (|obend_ospc_tile0_n cam_q| s1))"

/-! ## All six committed `hardware/sim/*_lec.smt2` files byte-for-byte -/

def checkCommitted (target path qualified : String) (m : RtlModule) : IO Unit := do
  let committed ← IO.FS.readFile path
  let printed := s!"; Generated by obend-emit-sv {target} --lec from {qualified}\n" ++ (lecScript m).print
  unless committed == printed do
    throw <| IO.userError s!"{path} is not the print of lecScript ({committed.length} vs {printed.length} bytes)"

#eval checkCommitted "mac2" "../hardware/sim/obend_retimed_mac2_lec.smt2"
  "Obend.Hardware.Synth.goldenRetimedMacRtl" Obend.Hardware.Synth.retimedMac2StageRtl
#eval checkCommitted "width-probe" "../hardware/sim/obend_width_probe_lec.smt2"
  "Obend.Hardware.VerilateRunner.goldenWidthProbeRtl" widthProbeTwoClockRtl
#eval checkCommitted "risc64" "../hardware/sim/obend_pipelined_risc64_lec.smt2"
  "Obend.Hardware.PipelinedRisc.pipelinedRiscCoreRtlModule" pipelinedRiscCoreRtlModule
#eval checkCommitted "goldilocks-bfly4" "../hardware/sim/obend_goldilocks_bfly4_lec.smt2"
  "Obend.Hardware.PipelinedZkCrypto.pipelinedGlButterflyRtlModule" pipelinedGlButterflyRtlModule
#eval checkCommitted "gf2-64-karatsuba" "../hardware/sim/obend_gf2_64_karatsuba_lec.smt2"
  "Obend.Hardware.PipelinedZkCrypto.gf2_64TowerMulRtlModule" gf2_64TowerMulRtlModule
#eval checkCommitted "ospc-tile0" "../hardware/sim/obend_ospc_tile0_lec.smt2"
  "Obend.Hardware.OspcProver.ospcTileDatapathRtl 0" (ospcTileDatapathRtl ⟨0, by decide⟩)

-- Dropping synchronous BRAM readout injection in `ospcTileDatapathInputs` breaks `ospcTileRtl_refines_ospcTileDatapathRtl`:
#tooth Obend.Hardware.OspcProver.ospcTileRtl_refines_ospcTileDatapathRtl by mutation
  Obend.Hardware.OspcProver.ospcTileDatapathInputs := fun _ inputs _ => inputs

end Obend.Tests.YosysLecTest
