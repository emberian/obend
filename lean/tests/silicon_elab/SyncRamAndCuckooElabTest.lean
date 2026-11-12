import Obend.Hardware.HDL
import Obend.Hardware.YosysLec
import Obend.Lower.SiliconElabFabric
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/silicon_elab/SyncRamAndCuckooElabTest.lean` — `SyncRam`, `QF_AUFBV` Array Miters, 8-Bank Cuckoo `ExprCAM` & `OfflineMemAcc` Suite

Exercises and mutation-tests Wave-5 Lane C1 (`0 sorryAx`, `0` custom axioms):
1. **`SyncRamSpec` (`readFirst` / `writeFirst`) & `YosysLec` SMT-LIB2 Array Miters (`lecMemScript_holds_iff`)**.
2. **8-Bank 2-Choice Cuckoo `ExprCAM` (`CuckooExprCAM`, multi-kick eviction chain, 1-cycle dual-bank lookup, deduplication, victim spill)**.
3. **128-Bit `PackedNodeWord128` & `OfflineMemAcc` (`GoldilocksExt2` Spill Authenticator catching bit-flips, address swaps, and timestamp replays)**.
4. **Synthesizable 8-Bank `SyncRam` `cuckooSiliconElabMemModule` (4-cycle BRAM closed-$\beta$ WHNF & hardware node-metadata Zone-4 `hasSorry`/`hasMVar` gate)**.
5. **6 `#tooth` Mutation Kills & Whole-Tree `#assert_axioms_tree` Audit**.
-/

namespace Obend.Tests.SyncRamAndCuckooElabTest

open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.SiliconElabFabric
open Obend.Hardware.HDL
open Obend.Hardware.YosysLec
open Obend.Apps.ZkNtt
open Obend.Crypto

-- ============================================================================
-- 0. Whole-Tree Axiom Purity Audit (`0 sorryAx`, `0` custom `axiom`s)
-- ============================================================================

#assert_axioms_tree

-- ============================================================================
-- 1. `SyncRamSpec` (`readFirst` vs `writeFirst`) & SMT-LIB2 Array Miters
-- ============================================================================

/-- Dual-bank synchronous RAM testbench module:
Bank 0 (`ram_rf`) uses `.readFirst`; Bank 1 (`ram_wf`) uses `.writeFirst`. -/
def dualModeRamDemo : RtlMemModule where
  core := {
    name := "dual_mode_ram_demo"
    inputNames := ["we", "raddr", "waddr", "wdata"]
    inputWidths := [1, 4, 4, 16]
    wires := []
    regs := [{ regIdx := 0, name := "cycle_q", domain := .coreClk, resetKind := .syncReset 0#64
             , isSynchronizer := false, width := 8
             , nextExpr := .alu .bitAnd (.alu .add (.regRead 0) (.const 1#64)) (.const 0xFF#64) }]
    outputs :=
      [ { name := "rf_out", expr := .regRead 1, width := 16 }
      , { name := "wf_out", expr := .regRead 2, width := 16 } ] }
  rams :=
    [ { ramIdx := 0, name := "ram_rf", rdataName := "rf_rdata", domain := .coreClk, style := .bram, mode := .readFirst
      , addrWidth := 4, dataWidth := 16, readAddrExpr := .inputPort 1
      , writeEnExpr := .inputPort 0, writeAddrExpr := .inputPort 2, writeDataExpr := .inputPort 3 }
    , { ramIdx := 1, name := "ram_wf", rdataName := "wf_rdata", domain := .coreClk, style := .uram, mode := .writeFirst
      , addrWidth := 4, dataWidth := 16, readAddrExpr := .inputPort 1
      , writeEnExpr := .inputPort 0, writeAddrExpr := .inputPort 2, writeDataExpr := .inputPort 3 } ]

#guard checkRtlMemModule dualModeRamDemo == true
#guard checkRtlMemModuleW dualModeRamDemo == true

-- Backwards-compatibility: empty `rams := []` emits 100% byte-identical SystemVerilog and SMT-LIB2
#guard emitMemModuleSV { core := siliconElabRtlModule, rams := [] } == emitModuleSV siliconElabRtlModule
#guard emitYosysMemLecSmt2 { core := siliconElabRtlModule, rams := [] } == emitYosysLecSmt2 siliconElabRtlModule

/-- Same-address read+write collision (`raddr = waddr = 3`, `we = 1`, `wdata = 0xCAFE`, old = `0xBEEF`):
Cycle 1 latches `0xBEEF` on `.readFirst` (`reg 1`) vs `0xCAFE` on `.writeFirst` (`reg 2`);
Cycle 2 (`we = 0`, `raddr = 3`) reads `0xCAFE` from both updated memory arrays. -/
def runDualModeCollisionOk : Bool :=
  let initSt : MemState :=
    { regs := fun _ => 0#64
    , mems := fun _ a => if a == 3#64 then 0xBEEF#64 else 0#64 }
  let cyc1Ins : Nat → BitVec 64 := fun
    | 0 => 1#64 | 1 => 3#64 | 2 => 3#64 | 3 => 0xCAFE#64 | _ => 0#64
  let cyc2Ins : Nat → BitVec 64 := fun
    | 0 => 0#64 | 1 => 3#64 | _ => 0#64
  let st1 := stepMemModule dualModeRamDemo false cyc1Ins initSt
  let st2 := stepMemModule dualModeRamDemo false cyc2Ins st1
  (st1.regs 1 == 0xBEEF#64) && (st1.regs 2 == 0xCAFE#64) &&
  (st1.mems 0 3#64 == 0xCAFE#64) && (st1.mems 1 3#64 == 0xCAFE#64) &&
  (st2.regs 1 == 0xCAFE#64) && (st2.regs 2 == 0xCAFE#64)

#guard runDualModeCollisionOk == true

def dualModeSmtLines : List String := (lecMemScript dualModeRamDemo).print.splitOn "\n"
def dualModeSvLines : List String := (emitMemModuleSV dualModeRamDemo).splitOn "\n"

#guard dualModeSvLines.any (· == "  (* ram_style = \"block\" *) logic [15:0] ram_rf [0:15];")
#guard dualModeSvLines.any (· == "  (* ram_style = \"ultra\" *) logic [15:0] ram_wf [0:15];")
#guard dualModeSmtLines.any (· == "(define-fun |rtl_mem_ram_rf| () (Array (_ BitVec 4) (_ BitVec 16)) (|dual_mode_ram_demo_m ram_rf| s1))")
#guard dualModeSmtLines.contains "(assert (not (and true |lec_out_rf_out| |lec_out_wf_out| |lec_next_cycle_q| |lec_rdata_rf_rdata| |lec_rdata_wf_rdata| |lec_mem_ram_rf| |lec_mem_ram_wf|)))"

-- ============================================================================
-- 2. 8-Bank 2-Choice Cuckoo `ExprCAM` (Multi-Kick Evictions, Dedup & Spill)
-- ============================================================================

/-- Deterministically exercise a 2-choice Cuckoo eviction chain in `bankDepth = 4`:
- `k0` (`loc0 = (0,0), loc1 = (5,0)`) lands in `(0,0)`;
- `k1` (`loc0 = (0,0), loc1 = (5,3)`) sees `(0,0)` occupied and takes Choice-1 `(5,3)`;
- `k2` (`loc0 = (0,0), loc1 = (5,3)`) sees BOTH `(0,0)` and `(5,3)` occupied, kicking `k0` from `(0,0)` to `(5,0)`;
- `k3` (`loc0 = (0,0), loc1 = (5,0)`) with `maxKicks = 0` cleanly reports an HBM victim spill. -/
def cuckooMultiKickTraceOk : Bool :=
  let d := 4
  let k0 : PackedNodeWord := { tag := 0, h0 := 0, h1 := 0, h2 := 16 }
  let k1 : PackedNodeWord := { tag := 0, h0 := 0, h1 := 2, h2 := 14 }
  let k2 : PackedNodeWord := { tag := 0, h0 := 0, h1 := 2, h2 := 30 }
  let k3 : PackedNodeWord := { tag := 0, h0 := 0, h1 := 0, h2 := 32 }
  let cam0 := CuckooExprCAM.empty d
  let (h0, cam1, sp0) := cuckooInsert 8 k0 false cam0
  let (h1, cam2, sp1) := cuckooInsert 8 k1 false cam1
  let (h2, cam3, sp2) := cuckooInsert 8 k2 true  cam2
  let (h0Dup, cam3Dup, spDup) := cuckooInsert 8 k0 false cam3
  let (_, _, spZeroKick) := cuckooInsert 0 k3 false cam3
  (cuckooLoc0 d k0 == (0, 0)) && (cuckooLoc0 d k1 == (0, 0)) && (cuckooLoc0 d k2 == (0, 0)) &&
  sp0.isNone && sp1.isNone && sp2.isNone && spDup.isNone && spZeroKick.isSome &&
  (h0 == 0) && (h1 == 1) && (h2 == 2) && (h0Dup == 0) && (cam3Dup == cam3) &&
  ((cam3.readBankSlot 0 0).map (·.key) == some k2) &&
  ((cam3.readBankSlot 5 0).map (·.key) == some k0) &&
  ((cam3.readBankSlot 5 3).map (·.key) == some k1) &&
  (cuckooLookup? cam3 k0 == some 0) &&
  (cuckooLookup? cam3 k1 == some 1) &&
  (cuckooLookup? cam3 k2 == some 2) &&
  ((cuckooLookupSlot? cam3 k2).map (·.hasSorry) == some true)

#guard cuckooMultiKickTraceOk == true

-- ============================================================================
-- 3. 128-Bit `PackedNodeWord128` & `OfflineMemAcc` (HBM DRAM Spill Integrity)
-- ============================================================================

def sampleNodeW : PackedNodeWord :=
  { tag := 5, h0 := 19, h1 := 42, h2 := 7, symIdx := 513
  , hasLooseBVar := true, hasFVar := false, hasMVar := true, maxLooseBVar := 3 }

#guard unpackNodeWord128 (packNodeWord128 sampleNodeW true 9001) == (sampleNodeW, true, 9001)
#guard unpackNodeWord128 (packNodeWord128 sampleNodeW false 9001) == (sampleNodeW, false, 9001)

def offlineMemDramAttackSuiteOk : Bool :=
  let γ := GoldilocksExt2.mk (Goldilocks.ofNat 0x123456789ABCDEF) (Goldilocks.ofNat 0xFEDCBA987654321)
  let α := GoldilocksExt2.mk (Goldilocks.ofNat 0x777711112222333) (Goldilocks.ofNat 0x999988884444555)
  let t0 : SpillTuple := { addr := 10, word := packNodeWord128 { tag := 4, h0 := 1, h1 := 2 } false 0, timestamp := 100 }
  let t1 : SpillTuple := { addr := 11, word := packNodeWord128 sampleNodeW false 1, timestamp := 101 }
  let t2 : SpillTuple := { addr := 12, word := packNodeWord128 { tag := 8, h0 := 0, h1 := 0, symIdx := 99 } true 2, timestamp := 102 }
  -- 1. Honest out-of-order HBM reload permutation `[t2, t0, t1]`
  let honest := runOfflineMemTrace γ α [t0, t1, t2] [t2, t0, t1]
  -- 2. Planted 1-bit DRAM payload flip in `lo64` of `t1`
  let t1BitFlip : SpillTuple := { t1 with word := { t1.word with lo64 := t1.word.lo64 ^^^ 1#64 } }
  let bitFlip := runOfflineMemTrace γ α [t0, t1, t2] [t2, t0, t1BitFlip]
  -- 3. Planted 1-bit DRAM payload flip in `hi64` of `t1`
  let t1HiFlip : SpillTuple := { t1 with word := { t1.word with hi64 := t1.word.hi64 ^^^ (1#64 <<< 40) } }
  let hiFlip := runOfflineMemTrace γ α [t0, t1, t2] [t2, t0, t1HiFlip]
  -- 4. Planted stale timestamp replay (`t1` returned with timestamp `100` instead of `101`)
  let t1ReplayTs : SpillTuple := { t1 with timestamp := 100 }
  let tsReplay := runOfflineMemTrace γ α [t0, t1, t2] [t2, t0, t1ReplayTs]
  -- 5. Planted address swap (`t1` returned from wrong address `12`)
  let t1AddrSwap : SpillTuple := { t1 with addr := 12 }
  let addrSwap := runOfflineMemTrace γ α [t0, t1, t2] [t2, t0, t1AddrSwap]
  (honest.wProd == honest.rProd) &&
  (bitFlip.wProd != bitFlip.rProd) &&
  (hiFlip.wProd != hiFlip.rProd) &&
  (tsReplay.wProd != tsReplay.rProd) &&
  (addrSwap.wProd != addrSwap.rProd)

#guard offlineMemDramAttackSuiteOk == true

-- ============================================================================
-- 4. `cuckooSiliconElabMemModule` 4-Cycle `SyncRam` WHNF & Zone-4 Metadata Gate
-- ============================================================================

#guard checkRtlMemModule cuckooSiliconElabMemModule == true
#guard checkRtlMemModuleW cuckooSiliconElabMemModule == true

def cuckooSmtLines : List String := (lecMemScript cuckooSiliconElabMemModule).print.splitOn "\n"
#guard cuckooSmtLines.any (· == "(define-fun |rtl_mem_cuckoo_bank0| () (Array (_ BitVec 6) (_ BitVec 64)) (|cuckoo_silicon_elab_top_m cuckoo_bank0| s1))")
#guard cuckooSmtLines.any (· == "(define-fun |rtl_mem_cuckoo_bank7| () (Array (_ BitVec 6) (_ BitVec 64)) (|cuckoo_silicon_elab_top_m cuckoo_bank7| s1))")

/-- Execute a full hardware trace on `cuckooSiliconElabMemModule`:
1. Write `appW` (handle `70`: bank `1`, row `6`), `lamW` (handle `195`: bank `3`, row `3`), and
   `bodyW` (handle `325`: bank `5`, row `5`) through the synchronous BRAM write ports;
2. Pulse `z1_start = 1` with `z1_init_handle = 70`;
3. Run 4 synchronous BRAM clock edges (`z1_step_en = 1`) for closed-$\beta$ reduction `70 → 325`;
4. Latch Zone 4 with `z4_ctrl = 7#64` (`sortOk=1, defeqOk=1, latchZ4=1`) and inspect outputs. -/
def runCuckooHwScenario (sorryOnBody mvarOnLam : Bool) : MemState × List (String × BitVec 64) :=
  let appH := 70; let lamH := 195; let bodyH := 325; let argH := 12
  let appLo  := (packNodeWord128 { tag := 4, h0 := lamH, h1 := argH } false appH).lo64
  let lamLo  := (packNodeWord128 { tag := 5, h0 := 1, h1 := bodyH, hasMVar := mvarOnLam } false lamH).lo64
  let bodyLo := (packNodeWord128 { tag := 8, h0 := 0, h1 := 0, symIdx := 42, hasLooseBVar := false } sorryOnBody bodyH).lo64
  let mkWrite (h : Nat) (w : BitVec 64) : Bool × (Nat → BitVec 64) :=
    (false, fun
      | 0 => 1#64
      | 1 => BitVec.ofNat 64 (h / 64)
      | 2 => BitVec.ofNat 64 (h % 64)
      | 3 => w
      | _ => 0#64)
  let startCyc : Bool × (Nat → BitVec 64) :=
    (false, fun | 4 => 1#64 | 6 => BitVec.ofNat 64 appH | _ => 0#64)
  let stepCyc : Bool × (Nat → BitVec 64) := (false, cuckooIdleStepInputs)
  let latchZ4Cyc : Bool × (Nat → BitVec 64) := (false, fun | 7 => 7#64 | _ => 0#64)
  let initSt : MemState := { regs := fun _ => 0#64, mems := fun _ _ => 0#64 }
  let snap (st : MemState) : MemState :=
    let rArr := Array.ofFn fun (i : Fin 20) => st.regs i.1
    let mArr := Array.ofFn fun (b : Fin 8) => Array.ofFn fun (a : Fin 64) => st.mems b.1 (BitVec.ofNat 64 a.1)
    { regs := fun i => rArr.getD i 0#64
    , mems := fun b a => (mArr.getD b #[]).getD a.toNat 0#64 }
  let trace := [mkWrite appH appLo, mkWrite lamH lamLo, mkWrite bodyH bodyLo,
                startCyc, stepCyc, stepCyc, stepCyc, stepCyc, latchZ4Cyc]
  let stF := trace.foldl (fun st (rst, ins) => snap (stepMemModule cuckooSiliconElabMemModule rst ins st)) initSt
  (stF, evalMemModuleOutputs cuckooSiliconElabMemModule (fun _ => 0#64) stF)

-- Clean closed-beta reduction reduces `70 -> 325` in 1 WHNF macro-step (4 BRAM cycles) and accepts Zone 4!
#guard (runCuckooHwScenario false false).2 ==
  [ ("z1_focus_out", 325#64), ("whnf_phase_out", 0#64), ("z1_steps_out", 1#64), ("z1_bypass_out", 1#64)
  , ("acc_sorry_out", 0#64), ("acc_mvar_out", 0#64), ("z4_status_out", 1#64), ("z4_accepted_out", 1#64) ]

-- Bit-56 `hasSorry` on interned `bodyW` inside BRAM Bank 5 forces `z4_status_out = 0` & `z4_accepted_out = 0`!
#guard (runCuckooHwScenario true false).2 ==
  [ ("z1_focus_out", 325#64), ("whnf_phase_out", 0#64), ("z1_steps_out", 1#64), ("z1_bypass_out", 1#64)
  , ("acc_sorry_out", 1#64), ("acc_mvar_out", 0#64), ("z4_status_out", 0#64), ("z4_accepted_out", 0#64) ]

-- Bit-58 `hasMVar` on interned `lamW` inside BRAM Bank 3 forces `z4_status_out = 2` & `z4_accepted_out = 0`!
#guard (runCuckooHwScenario false true).2 ==
  [ ("z1_focus_out", 325#64), ("whnf_phase_out", 0#64), ("z1_steps_out", 1#64), ("z1_bypass_out", 1#64)
  , ("acc_sorry_out", 0#64), ("acc_mvar_out", 1#64), ("z4_status_out", 2#64), ("z4_accepted_out", 0#64) ]

-- ============================================================================
-- 5. `#tooth` Mutation Kills (`≥ 4` Load-Bearing Hardware/Crypto Mutations)
-- ============================================================================

/-- Mutation 1: Broken `evalSyncRamReadNext` that ignores `.writeFirst` write-bypass forwarding. -/
def evalSyncRamReadNextStaleOnly (inputs wireEnv regState : Nat → BitVec 64)
    (memArr : BitVec 64 → BitVec 64) (ram : SyncRamSpec) : BitVec 64 :=
  let raddr := truncToWidth ram.addrWidth (evalRtlExpr inputs wireEnv regState ram.readAddrExpr)
  truncToWidth ram.dataWidth (memArr raddr)

#tooth Obend.Hardware.YosysLec.lecMemScript_holds_iff by mutation
  Obend.Hardware.HDL.evalSyncRamReadNext := evalSyncRamReadNextStaleOnly

/-- Mutation 2: Broken `cuckooLookupSlot?` that probes only Choice-0 (`banks 0..3`) and drops Choice-1 (`banks 4..7`). -/
def cuckooLookupSlotBank0Only (cam : CuckooExprCAM) (k : PackedNodeWord) : Option CuckooSlot :=
  cuckooProbeSlot? (cam.readBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2) k

#tooth Obend.Lower.SiliconElabFabric.cuckooCam_lookup_iff_member by mutation
  Obend.Lower.SiliconElabFabric.cuckooLookupSlot? := cuckooLookupSlotBank0Only

/-- Mutation 3: Broken `cuckooInsert` that skips deduplication lookup and blindly allocates duplicate handles. -/
def cuckooInsertSkipDedup (maxKicks : Nat) (k : PackedNodeWord) (hasSorry : Bool) (cam : CuckooExprCAM) :
    CamHandle × CuckooExprCAM × Option CuckooSlot :=
  cuckooInsertAux maxKicks k hasSorry cam none

#tooth Obend.Lower.SiliconElabFabric.cuckooCam_no_duplicate_handles by mutation
  Obend.Lower.SiliconElabFabric.cuckooInsert := cuckooInsertSkipDedup

/-- Mutation 4: Broken `encodeSpillLimbs` that drops `timestamp` from the framed `Goldilocks` preimage,
allowing DRAM timestamp replay collisions. -/
def encodeSpillLimbsDropTimestamp (t : SpillTuple) : List Goldilocks :=
  let lo := t.word.lo64.toNat; let hi := t.word.hi64.toNat
  let l0 := lo % 72057594037927936; let l1 := hi % 72057594037927936
  let l3 := t.addr.toNat + 4294967296 * (lo / 72057594037927936) + 1099511627776 * (hi / 72057594037927936)
  [Goldilocks.ofNat l0, Goldilocks.ofNat l1, Goldilocks.ofNat 0, Goldilocks.ofNat l3]

#tooth Obend.Lower.SiliconElabFabric.offlineMemCheck_spill_sound by mutation
  Obend.Lower.SiliconElabFabric.encodeSpillLimbs := encodeSpillLimbsDropTimestamp

/-- Mutation 5: Broken `packNodeWord128` that drops Bit-56 `hasSorry` node metadata during BRAM packing. -/
def packNodeWord128DropSorry (w : PackedNodeWord) (_hasSorry : Bool) (handleId : Nat := 0) : PackedNodeWord128 :=
  let bFVar := if w.hasFVar then 1 else 0
  let bMVar := if w.hasMVar then 1 else 0
  let bLoose := if w.hasLooseBVar then 1 else 0
  let loNat := (w.h1 % 65536) + 65536 * (w.h0 % 65536) + 4294967296 * (w.symIdx % 65536) +
    144115188075855872 * bFVar + 288230376151711744 * bMVar + 576460752303423488 * bLoose +
    1152921504606846976 * (w.tag % 16)
  let hiNat := (w.h2 % 65536) + 65536 * (w.maxLooseBVar % 65536) + 4294967296 * (handleId % 4294967296)
  { lo64 := BitVec.ofNat 64 loNat, hi64 := BitVec.ofNat 64 hiNat }

#tooth Obend.Lower.SiliconElabFabric.unpack_pack_nodeWord128 by mutation
  Obend.Lower.SiliconElabFabric.packNodeWord128 := @packNodeWord128DropSorry

/-- Mutation 6: Broken `stepCamWhnf` no-op breaks `cuckooElabRtl_simulates_stepCamWhnf`. -/
def stepCamWhnfNoop (st : Zone1WhnfState) : Zone1WhnfState := st

#tooth Obend.Lower.SiliconElabFabric.cuckooElabRtl_simulates_stepCamWhnf by mutation
  Obend.Lower.SiliconElabFabric.stepCamWhnf := stepCamWhnfNoop

end Obend.Tests.SyncRamAndCuckooElabTest
