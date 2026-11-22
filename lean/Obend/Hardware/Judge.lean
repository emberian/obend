module
/- Hardware Judge formats: structural acceptance contracts, object-unsatisfiable
refusals, and universally round-tripping deterministic CBOR certificates. -/
public import Obend.Codec.DetCbor
import all Obend.Codec.DetCbor
public import Lean.Data.Json
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Receipt
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.SmallSignalMna
public import Obend.Hardware.Datasheet
public import Obend.Hardware.Circuits
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.DigitalFilterAndArray
public import Obend.Hardware.PinoutEquiv
public import Obend.Hardware.Codec
import all Obend.Hardware.PinoutEquiv
import all Obend.Hardware.Codec
import Obend.Tactic.Tooth
public section
namespace Obend.Hardware.Judge
open Lean (Json toJson)
open Obend.Judge
open Obend.Hardware.Process Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.SmallSignalMna
open Obend.Hardware.Datasheet Obend.Hardware.Circuits
open Obend.Hardware.ReductionMachine Obend.Hardware.DigitalFilterAndArray Obend.Hardware.PinoutEquiv
open Obend.Hardware.Codec
set_option autoImplicit false
/-! Lossless deterministic CBOR. Arrays are fixed tuples or cons cells; arbitrary
naturals use radix-2^32 limbs, so no host-sized field is truncated. -/
open Obend.Codec.DetCbor
open Obend.Hardware.Synth
private class Wire (α : Type) where
  enc : α → CborVal
  dec : CborVal → Option α
  canonical : ∀ x, CanonicalCbor (enc x) = true
  inverse : ∀ x, dec (enc x) = some x
private def pack {α : Type} [Wire α] : α → CborVal := Wire.enc
private def unpack {α : Type} [Wire α] : CborVal → Option α := Wire.dec
private theorem pack_canonical {α : Type} [Wire α] (x : α) : CanonicalCbor (pack x) = true := Wire.canonical x
@[simp] private theorem pack_wf {α : Type} [Wire α] (x : α) :
    wfVal isValidUtf8 true (pack x) = true := pack_canonical x
@[simp] private theorem unpack_pack {α : Type} [Wire α] (x : α) : unpack (pack x) = some x := Wire.inverse x
@[instance_reducible] private def wireIso {α β : Type} [Wire β] (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) : Wire α where
  enc x := pack (f x)
  dec v := (unpack v).map g
  canonical x := pack_canonical (f x)
  inverse x := by simp [unpack_pack, h]
private instance : Wire Bool where
  enc := .simpleBool
  dec | .simpleBool b => some b | _ => none
  canonical _ := rfl
  inverse _ := rfl
private instance : Wire (BitVec 64) where
  enc v := .uint (UInt64.ofNat v.toNat)
  dec | .uint n => some (BitVec.ofNat 64 n.toNat) | _ => none
  canonical _ := rfl
  inverse _ := by simp
private def natCborBig (n : Nat) : CborVal :=
  if n = 0 then .array [.uint 0] else
    .array [.uint 1, .uint (UInt64.ofNat (n % 4294967296)), natCborBig (n / 4294967296)]
termination_by n
private def cborNatBig : CborVal → Option Nat
  | .array [.uint 0] => some 0
  | .array [.uint 1, .uint lo, rest] => (cborNatBig rest).map (fun hi => lo.toNat + 4294967296 * hi)
  | _ => none
termination_by structural v => v
private theorem natCborBig_canonical (n : Nat) : CanonicalCbor (natCborBig n) = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natCborBig]
    split
    · rfl
    · rename_i hn
      have hh := ih (n / 4294967296) (Nat.div_lt_self (by omega) (by decide))
      simpa [CanonicalCbor, wfVal, wfList] using hh
private theorem cborNatBig_natCborBig (n : Nat) : cborNatBig (natCborBig n) = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natCborBig]
    split
    · rename_i hn; subst n; rfl
    · rename_i hn
      have hh := ih (n / 4294967296) (Nat.div_lt_self (by omega) (by decide))
      simp only [cborNatBig, hh, Option.map_some]
      congr 1
      rw [UInt64.toNat_ofNat']
      have hlo : n % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
private def natCbor (n : Nat) : CborVal :=
  if n < 18446744073709551616 then .uint (UInt64.ofNat n) else natCborBig n
private def cborNat : CborVal → Option Nat
  | .uint u => some u.toNat
  | v => do
    let n ← cborNatBig v
    if 18446744073709551616 ≤ n then some n else none
private theorem natCbor_canonical (n : Nat) : CanonicalCbor (natCbor n) = true := by
  unfold natCbor
  split
  · rfl
  · exact natCborBig_canonical n
private theorem cborNat_natCbor (n : Nat) : cborNat (natCbor n) = some n := by
  unfold natCbor
  split
  · rename_i hlt
    simp [cborNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  · rename_i hge
    have hpos : n ≠ 0 := by omega
    have hbig : natCborBig n = .array [.uint 1, .uint (UInt64.ofNat (n % 4294967296)), natCborBig (n / 4294967296)] := by
      rw [natCborBig]; simp [hpos]
    have hrec := cborNatBig_natCborBig n
    rw [hbig] at hrec ⊢
    have hge' : 18446744073709551616 ≤ n := by omega
    simp [cborNat, hrec, hge']
private instance : Wire Nat := ⟨natCbor,cborNat,natCbor_canonical,cborNat_natCbor⟩
private instance {α β : Type} [Wire α] [Wire β] : Wire (α × β) where
  enc x := .array [pack x.1,pack x.2]
  dec | .array [a,b] => do return (← unpack a, ← unpack b) | _ => none
  canonical _ := by simp [CanonicalCbor, wfVal, wfList]
  inverse x := by simp [unpack_pack]
private def listCbor {α : Type} [Wire α] : List α → CborVal
  | [] => .array [.uint 0]
  | x :: xs => .array [.uint 1,pack x,listCbor xs]
private def cborList {α : Type} [Wire α] : CborVal → Option (List α)
  | .array [.uint 0] => some []
  | .array [.uint 1,x,xs] => do return (← unpack x) :: (← cborList xs)
  | _ => none
termination_by structural v => v
private instance {α : Type} [Wire α] : Wire (List α) where
  enc := listCbor
  dec := cborList
  canonical xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := pack_canonical x
      simp_all [listCbor, CanonicalCbor, wfVal, wfList]
  inverse xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [listCbor,cborList,unpack_pack,ih]
private instance : Wire Char := wireIso Char.toNat Char.ofNat Char.ofNat_toNat
private instance : Wire String := wireIso String.toList String.ofList (fun _ => String.ofList_toList)
private instance : Wire Int := wireIso
  (fun x => match x with | .ofNat n => (false,n) | .negSucc n => (true,n))
  (fun (sign,n) => if sign then Int.negSucc n else Int.ofNat n)
  (by intro x; cases x <;> rfl)
private def rtlAluOpCbor : RtlAluOp → CborVal
  | .add => .array [.uint 0] | .sub => .array [.uint 1] | .mul => .array [.uint 2]
  | .bitAnd => .array [.uint 3] | .bitOr => .array [.uint 4] | .bitXor => .array [.uint 5]
  | .shl => .array [.uint 6] | .lshr => .array [.uint 7] | .ashr => .array [.uint 8]
  | .eq => .array [.uint 9] | .ult => .array [.uint 10] | .slt => .array [.uint 11] | .qmul32 => .array [.uint 12]
private def cborRtlAluOp : CborVal → Option RtlAluOp
  | .array [.uint 0] => some .add | .array [.uint 1] => some .sub | .array [.uint 2] => some .mul
  | .array [.uint 3] => some .bitAnd | .array [.uint 4] => some .bitOr | .array [.uint 5] => some .bitXor
  | .array [.uint 6] => some .shl | .array [.uint 7] => some .lshr | .array [.uint 8] => some .ashr
  | .array [.uint 9] => some .eq | .array [.uint 10] => some .ult | .array [.uint 11] => some .slt
  | .array [.uint 12] => some .qmul32 | _ => none
private instance : Wire RtlAluOp where
  enc := rtlAluOpCbor; dec := cborRtlAluOp
  canonical x := by cases x <;> simp_all [rtlAluOpCbor, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [rtlAluOpCbor, cborRtlAluOp]
private def clkDomainCbor : ClkDomain → CborVal
  | .coreClk => .array [.uint 0] | .axiIoClk => .array [.uint 1] | .cfgJtagClk => .array [.uint 2]
private def cborClkDomain : CborVal → Option ClkDomain
  | .array [.uint 0] => some .coreClk | .array [.uint 1] => some .axiIoClk | .array [.uint 2] => some .cfgJtagClk | _ => none
private instance : Wire ClkDomain where
  enc := clkDomainCbor; dec := cborClkDomain
  canonical x := by cases x <;> simp_all [clkDomainCbor, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [clkDomainCbor, cborClkDomain]
private def resetKindCbor : ResetKind → CborVal
  | .resetFree => .array [.uint 0] | .syncReset x0 => .array [.uint 1, pack x0]
private def cborResetKind : CborVal → Option ResetKind
  | .array [.uint 0] => some .resetFree | .array [.uint 1, x0] => do return .syncReset (← unpack x0) | _ => none
private instance : Wire ResetKind where
  enc := resetKindCbor; dec := cborResetKind
  canonical x := by cases x <;> simp_all [resetKindCbor, pack_wf, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [resetKindCbor, cborResetKind, unpack_pack]
private def rtlWidthOpCbor : RtlWidthOp → CborVal
  | .slice x0 x1 => .array [.uint 0, pack x0, pack x1] | .zext x0 => .array [.uint 1, pack x0]
  | .sext x0 x1 => .array [.uint 2, pack x0, pack x1] | .trunc x0 => .array [.uint 3, pack x0]
private def cborRtlWidthOp : CborVal → Option RtlWidthOp
  | .array [.uint 0, x0, x1] => do return .slice (← unpack x0) (← unpack x1)
  | .array [.uint 1, x0] => do return .zext (← unpack x0)
  | .array [.uint 2, x0, x1] => do return .sext (← unpack x0) (← unpack x1)
  | .array [.uint 3, x0] => do return .trunc (← unpack x0)
  | _ => none
private instance : Wire RtlWidthOp where
  enc := rtlWidthOpCbor; dec := cborRtlWidthOp
  canonical x := by cases x <;> simp_all [rtlWidthOpCbor, pack_wf, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [rtlWidthOpCbor, cborRtlWidthOp, unpack_pack]
private def rtlExprCbor : RtlExpr → CborVal
  | .const x0 => .array [.uint 0, pack x0] | .inputPort x0 => .array [.uint 1, pack x0]
  | .wireRef x0 => .array [.uint 2, pack x0] | .regRead x0 => .array [.uint 3, pack x0]
  | .alu x0 x1 x2 => .array [.uint 4, pack x0, rtlExprCbor x1, rtlExprCbor x2]
  | .mux x0 x1 x2 => .array [.uint 5, rtlExprCbor x0, rtlExprCbor x1, rtlExprCbor x2]
  | .bitNot x0 => .array [.uint 6, rtlExprCbor x0] | .resize x0 x1 => .array [.uint 7, pack x0, rtlExprCbor x1]
termination_by structural x => x
private def cborRtlExpr : CborVal → Option RtlExpr
  | .array [.uint 0, x0] => do return .const (← unpack x0)
  | .array [.uint 1, x0] => do return .inputPort (← unpack x0)
  | .array [.uint 2, x0] => do return .wireRef (← unpack x0)
  | .array [.uint 3, x0] => do return .regRead (← unpack x0)
  | .array [.uint 4, x0, x1, x2] => do return .alu (← unpack x0) (← cborRtlExpr x1) (← cborRtlExpr x2)
  | .array [.uint 5, x0, x1, x2] => do return .mux (← cborRtlExpr x0) (← cborRtlExpr x1) (← cborRtlExpr x2)
  | .array [.uint 6, x0] => do return .bitNot (← cborRtlExpr x0)
  | .array [.uint 7, x0, x1] => do return .resize (← unpack x0) (← cborRtlExpr x1)
  | _ => none
termination_by structural x => x
private instance : Wire RtlExpr where
  enc := rtlExprCbor; dec := cborRtlExpr
  canonical x := by induction x <;> simp_all [rtlExprCbor, pack_wf, CanonicalCbor, wfVal, wfList]
  inverse x := by induction x <;> simp_all [rtlExprCbor, cborRtlExpr, unpack_pack]
private instance : Wire WireAssign := wireIso
  (fun x => (x.wireIdx,x.name,x.expr,x.width)) (fun (wireIdx,name,expr,width) => ⟨wireIdx,name,expr,width⟩)
  (by intro x; cases x; rfl)
private instance : Wire RegSpec := wireIso
  (fun x => (x.regIdx,x.name,x.domain,x.resetKind,x.isSynchronizer,x.nextExpr,x.width))
  (fun (regIdx,name,domain,resetKind,isSynchronizer,nextExpr,width) => ⟨regIdx,name,domain,resetKind,isSynchronizer,nextExpr,width⟩)
  (by intro x; cases x; rfl)
private instance : Wire OutputPort := wireIso
  (fun x => (x.name,x.expr,x.width)) (fun (name,expr,width) => ⟨name,expr,width⟩) (by intro x; cases x; rfl)
private instance : Wire RtlModule := wireIso
  (fun x => (x.name,x.inputNames,x.wires,x.regs,x.outputs,x.inputWidths))
  (fun (name,inputNames,wires,regs,outputs,inputWidths) => ⟨name,inputNames,wires,regs,outputs,inputWidths⟩)
  (by intro x; cases x; rfl)
private instance : Wire SyncEdge := wireIso
  (fun x => (x.src,x.dst,x.origRegs,x.combDelayPs)) (fun (src,dst,origRegs,combDelayPs) => ⟨src,dst,origRegs,combDelayPs⟩)
  (by intro x; cases x; rfl)
private instance : Wire SyncGraph := wireIso
  (fun x => (x.name,x.primaryInputs,x.primaryOutputs,x.edges))
  (fun (name,primaryInputs,primaryOutputs,edges) => ⟨name,primaryInputs,primaryOutputs,edges⟩)
  (by intro x; cases x; rfl)
private instance : Wire RetimingCert := wireIso
  (fun x => (x.vertexLags,x.ioLatencyShift)) (fun (vertexLags,ioLatencyShift) => ⟨vertexLags,ioLatencyShift⟩)
  (by intro x; cases x; rfl)
private def carryModeCbor : CarryMode → CborVal
  | .add => .array [.uint 0] | .sub => .array [.uint 1] | .ultCmp => .array [.uint 2] | .sltCmp => .array [.uint 3]
private def cborCarryMode : CborVal → Option CarryMode
  | .array [.uint 0] => some .add | .array [.uint 1] => some .sub
  | .array [.uint 2] => some .ultCmp | .array [.uint 3] => some .sltCmp | _ => none
private instance : Wire CarryMode where
  enc := carryModeCbor; dec := cborCarryMode
  canonical x := by cases x <;> simp_all [carryModeCbor, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [carryModeCbor, cborCarryMode]
private def dspMulModeCbor : DspMulMode → CborVal
  | .mul64 => .array [.uint 0] | .qmul32 => .array [.uint 1]
private def cborDspMulMode : CborVal → Option DspMulMode
  | .array [.uint 0] => some .mul64 | .array [.uint 1] => some .qmul32 | _ => none
private instance : Wire DspMulMode where
  enc := dspMulModeCbor; dec := cborDspMulMode
  canonical x := by cases x <;> simp_all [dspMulModeCbor, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [dspMulModeCbor, cborDspMulMode]
private def shiftDirCbor : ShiftDir → CborVal
  | .shl => .array [.uint 0] | .lshr => .array [.uint 1] | .ashr => .array [.uint 2]
private def cborShiftDir : CborVal → Option ShiftDir
  | .array [.uint 0] => some .shl | .array [.uint 1] => some .lshr | .array [.uint 2] => some .ashr | _ => none
private instance : Wire ShiftDir where
  enc := shiftDirCbor; dec := cborShiftDir
  canonical x := by cases x <;> simp_all [shiftDirCbor, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [shiftDirCbor, cborShiftDir]
private def belKindCbor : BelKind → CborVal
  | .constBel x0 => .array [.uint 0, pack x0] | .portIn x0 => .array [.uint 1, pack x0]
  | .wireTap x0 => .array [.uint 2, pack x0] | .regTap x0 => .array [.uint 3, pack x0]
  | .lut1 x0 => .array [.uint 4, pack x0] | .lut2 x0 => .array [.uint 5, pack x0]
  | .lut3 x0 => .array [.uint 6, pack x0] | .orReduce => .array [.uint 7] | .zeroDetect => .array [.uint 8]
  | .shiftRoute x0 x1 => .array [.uint 9, pack x0, pack x1] | .bitBroadcast x0 => .array [.uint 10, pack x0]
  | .carry4 x0 => .array [.uint 11, pack x0] | .dspMul x0 => .array [.uint 12, pack x0]
  | .ff x0 x1 => .array [.uint 13, pack x0, pack x1] | .route x0 => .array [.uint 14, pack x0]
private def cborBelKind : CborVal → Option BelKind
  | .array [.uint 0, x0] => do return .constBel (← unpack x0)
  | .array [.uint 1, x0] => do return .portIn (← unpack x0)
  | .array [.uint 2, x0] => do return .wireTap (← unpack x0)
  | .array [.uint 3, x0] => do return .regTap (← unpack x0)
  | .array [.uint 4, x0] => do return .lut1 (← unpack x0)
  | .array [.uint 5, x0] => do return .lut2 (← unpack x0)
  | .array [.uint 6, x0] => do return .lut3 (← unpack x0)
  | .array [.uint 7] => some .orReduce | .array [.uint 8] => some .zeroDetect
  | .array [.uint 9, x0, x1] => do return .shiftRoute (← unpack x0) (← unpack x1)
  | .array [.uint 10, x0] => do return .bitBroadcast (← unpack x0)
  | .array [.uint 11, x0] => do return .carry4 (← unpack x0)
  | .array [.uint 12, x0] => do return .dspMul (← unpack x0)
  | .array [.uint 13, x0, x1] => do return .ff (← unpack x0) (← unpack x1)
  | .array [.uint 14, x0] => do return .route (← unpack x0)
  | _ => none
private instance : Wire BelKind where
  enc := belKindCbor; dec := cborBelKind
  canonical x := by cases x <;> simp_all [belKindCbor, pack_wf, CanonicalCbor, wfVal, wfList]
  inverse x := by cases x <;> simp_all [belKindCbor, cborBelKind, unpack_pack]
private instance : Wire BelCell := wireIso
  (fun x => (x.dstName,x.kind,x.inputs))
  (fun (dstName,kind,inputs) => ⟨dstName,kind,inputs⟩)
  (by intro x; cases x; rfl)
private instance : Wire BelNetlist := wireIso
  (fun x => (x.moduleName,x.inputNames,x.cells,x.outputNames))
  (fun (moduleName,inputNames,cells,outputNames) => ⟨moduleName,inputNames,cells,outputNames⟩)
  (by intro x; cases x; rfl)
private instance : Wire ProcessCorner := wireIso
  (fun x => (x.name,x.nodeNm,x.voltageMv,x.tempC,x.tCqMaxPs,x.tCqMinPs,x.tGateMaxPs,x.tGateMinPs,x.tCarryMaxPs,x.tWireHopPs,x.tSetupPs,x.tHoldPs,x.tSkewPs))
  (fun (name,nodeNm,voltageMv,tempC,tCqMaxPs,tCqMinPs,tGateMaxPs,tGateMinPs,tCarryMaxPs,tWireHopPs,tSetupPs,tHoldPs,tSkewPs) => ⟨name,nodeNm,voltageMv,tempC,tCqMaxPs,tCqMinPs,tGateMaxPs,tGateMinPs,tCarryMaxPs,tWireHopPs,tSetupPs,tHoldPs,tSkewPs⟩)
  (by intro x; cases x; rfl)
private instance : Wire PlacedCell := wireIso
  (fun x => (x.cellId,x.tileX,x.tileY,x.belSlot,x.lutInit))
  (fun (cellId,tileX,tileY,belSlot,lutInit) => ⟨cellId,tileX,tileY,belSlot,lutInit⟩)
  (by intro x; cases x; rfl)
private instance : Wire PipHop := wireIso
  (fun x => (x.srcWire,x.dstWire,x.resOhm,x.capFf))
  (fun (srcWire,dstWire,resOhm,capFf) => ⟨srcWire,dstWire,resOhm,capFf⟩)
  (by intro x; cases x; rfl)
private instance : Wire RoutedNet := wireIso
  (fun x => (x.netId,x.srcWire,x.dstWire,x.hops))
  (fun (netId,srcWire,dstWire,hops) => ⟨netId,srcWire,dstWire,hops⟩)
  (by intro x; cases x; rfl)
private instance : Wire TileFrameConfig := wireIso
  (fun x => (x.tileX,x.tileY,x.belSlot,x.lutInit,x.pipMask))
  (fun (tileX,tileY,belSlot,lutInit,pipMask) => ⟨tileX,tileY,belSlot,lutInit,pipMask⟩)
  (by intro x; cases x; rfl)
private instance : Wire BitstreamFrame := wireIso
  (fun x => (x.frameAddr,x.frameData))
  (fun (frameAddr,frameData) => ⟨frameAddr,frameData⟩)
  (by intro x; cases x; rfl)
private instance : Wire PnrCertificate := wireIso
  (fun x => (x.designName,x.placedCells,x.routedNets,x.expectedConfigs,x.bitstreamFrames,x.sinkCapFf))
  (fun (designName,placedCells,routedNets,expectedConfigs,bitstreamFrames,sinkCapFf) => ⟨designName,placedCells,routedNets,expectedConfigs,bitstreamFrames,sinkCapFf⟩)
  (by intro x; cases x; rfl)
private def wireDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | 15 => 'f'
  | _ => '0'
private def wireByteNibble : UInt8 → Option Nat
  | 48 => some 0 | 49 => some 1 | 50 => some 2 | 51 => some 3
  | 52 => some 4 | 53 => some 5 | 54 => some 6 | 55 => some 7
  | 56 => some 8 | 57 => some 9 | 97 => some 10 | 98 => some 11
  | 99 => some 12 | 100 => some 13 | 101 => some 14 | 102 => some 15
  | _ => none
private theorem wireDigit_utf8 (n : Nat) (h : n < 16) :
    ∃ u : UInt8, [wireDigit n].utf8Encode.data.toList = [u] ∧ wireByteNibble u = some n ∧ u ≠ 34 := by
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, rfl, by decide⟩
private def wireHex : List UInt8 → List Char
  | [] => []
  | b :: bs => wireDigit (b.toNat / 16) :: wireDigit (b.toNat % 16) :: wireHex bs
private def wireHexTailBytes : List UInt8 → Option (List UInt8)
  | a :: b :: rest =>
    if a == 34 && b == 125 && rest.isEmpty then some [] else do
      let hi ← wireByteNibble a
      let lo ← wireByteNibble b
      let bytes ← wireHexTailBytes rest
      return UInt8.ofNat (hi * 16 + lo) :: bytes
  | _ => none
private theorem wireHex_utf8_inverse (bs : List UInt8) :
    wireHexTailBytes ((wireHex bs ++ ['"', '}']).utf8Encode.data.toList) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := UInt8.toNat_lt b
    obtain ⟨uhi, hhiEnc, hhiNib, hhiNe⟩ := wireDigit_utf8 (b.toNat / 16) (by omega)
    obtain ⟨ulo, hloEnc, hloNib, _⟩ := wireDigit_utf8 (b.toNat % 16) (Nat.mod_lt _ (by decide))
    have he : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    have hstep : (wireHex (b :: bs) ++ ['"', '}']).utf8Encode.data.toList =
        uhi :: ulo :: (wireHex bs ++ ['"', '}']).utf8Encode.data.toList := by
      rw [wireHex, List.cons_append, List.cons_append,
        List.utf8Encode_cons, ByteArray.toList_data_append, hhiEnc,
        List.utf8Encode_cons, ByteArray.toList_data_append, hloEnc,
        List.singleton_append, List.singleton_append]
    rw [hstep]
    generalize (wireHex bs ++ ['"', '}']).utf8Encode.data.toList = tail at ih ⊢
    simp [wireHexTailBytes, hhiNib, hhiNe, hloNib, ih, -UInt8.ofNat_add, -UInt8.ofNat_mul, he]
private def wireEnvelope (bs : ByteArray) : String :=
  String.ofList (['{','"','c','b','o','r','"',':','"'] ++ wireHex bs.data.toList ++ ['"','}'])
private def readWireEnvelope (s : String) : Option ByteArray :=
  match s.toByteArray.data.toList with
  | 123 :: 34 :: 99 :: 98 :: 111 :: 114 :: 34 :: 58 :: 34 :: rest =>
    (wireHexTailBytes rest).map (fun bs => ⟨bs.toArray⟩)
  | _ => none
private theorem wireEnvelope_inverse (bs : ByteArray) : readWireEnvelope (wireEnvelope bs) = some bs := by
  unfold wireEnvelope readWireEnvelope
  have hpre : ['{','"','c','b','o','r','"',':','"'].utf8Encode.data.toList =
      [123, 34, 99, 98, 111, 114, 34, 58, 34] := rfl
  have hbytes : (['{','"','c','b','o','r','"',':','"'] ++ wireHex bs.data.toList ++ ['"','}']).utf8Encode.data.toList =
      123 :: 34 :: 99 :: 98 :: 111 :: 114 :: 34 :: 58 :: 34 ::
        (wireHex bs.data.toList ++ ['"','}']).utf8Encode.data.toList := by
    rw [List.append_assoc, List.utf8Encode_append, ByteArray.toList_data_append, hpre]
    rfl
  rw [String.toByteArray_ofList, hbytes]
  simp only [wireHex_utf8_inverse, Option.map]
private def encodeWire {α : Type} [Wire α] (x : α) : String := wireEnvelope (encodeDetCbor (pack x))
private def decodeWire {α : Type} [Wire α] (s : String) : Except String α :=
  match readWireEnvelope s >>= decodeDetCbor >>= unpack with
  | some x => .ok x
  | none => .error "malformed deterministic CBOR certificate"
private theorem decodeWire_encodeWire {α : Type} [Wire α] (x : α) :
    decodeWire (encodeWire x) = .ok x := by
  simp [decodeWire,encodeWire,wireEnvelope_inverse,decodeDetCbor_encodeDetCbor _ (pack_canonical x)]
inductive HwClause where
  | emptyRtlTopName
  | unsatRetimeTarget
  | invalidPnrProblem
  | emptyDatasheetSuiteName
  | unsatAgenticMarginTarget
  | rtlInvalidDagOrCdc (modName : String)
  | retimeInvalidLagOrTiming (graphName : String)
  | pnrCollisionShortOrTiming (designName : String)
  | datasheetCalibrationOrMarginViolation (suiteName : String)
  | agenticEdaSwapViolation (partName : String)
  | binaryCborCertViolation (domainId : Nat)
  deriving DecidableEq, Repr
def RtlSynthMeaning (name : String) (m : RtlModule) : Prop :=
  name ≠ "" ∧ m.name = name ∧ m.outputs ≠ [] ∧
  checkWireTableDAG m.inputNames.length m.regs.length m.wires = true ∧
  (∀ r ∈ m.regs, checkExprDAG m.inputNames.length m.regs.length m.wires.length r.nextExpr = true) ∧
  (∀ o ∈ m.outputs, checkExprDAG m.inputNames.length m.regs.length m.wires.length o.expr = true) ∧
  checkModuleCdc m.regs = true
@[expose] def checkRtlSynth (_grade : Nat) (name : String) (m : RtlModule) : Verdict HwClause :=
  if name == "" then .refused .emptyRtlTopName []
  else if m.name == name && !m.outputs.isEmpty && checkRtlModule m then .ok
  else .refused (.rtlInvalidDagOrCdc m.name) []
theorem checkRtlSynth_ok_iff (r : Nat) (name : String) (m : RtlModule) :
    checkRtlSynth r name m = .ok ↔ RtlSynthMeaning name m := by
  unfold checkRtlSynth
  split <;> (try split) <;> simp_all [RtlSynthMeaning, checkRtlModule, List.all_eq_true, and_assoc]
instance rtlSynthJudge : Obend.Judge String RtlModule where
  Clause := HwClause
  Meaning := RtlSynthMeaning
  check := checkRtlSynth
  sound := by intro r o c h; exact (checkRtlSynth_ok_iff r o c).mp h
  refutes | .emptyRtlTopName => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkRtlSynth at hc
    split at hc
    · rename_i ho
      exact hm.1 (beq_iff_eq.mp ho)
    · split at hc
      · cases hc
      · cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c,hc⟩; exact ⟨c,0,(checkRtlSynth_ok_iff 0 o c).mpr hc⟩
  mono := by intros; rfl
abbrev RetimeProblem := SyncGraph × Nat
def checkGraphWellFormed (g : SyncGraph) : Bool :=
  g.name != "" && !g.primaryInputs.isEmpty && !g.primaryOutputs.isEmpty
def RetimeStaMeaning (p : RetimeProblem) (c : RetimingCert) : Prop :=
  checkGraphWellFormed p.1 = true ∧ 0 < p.2 ∧
  (∀ e ∈ p.1.edges, 0 ≤ retimedEdgeWeight (lookupLag c) e) ∧
  checkBoundaryLags p.1 c = true ∧
  (∀ e ∈ p.1.edges, checkRetimedTimingEdge (lookupLag c) corner7nm_SS p.2 e = true) ∧
  (if p.1.edges.any (fun e => retimedEdgeWeight (lookupLag c) e == 0) then
    corner7nm_SS.tCqMaxPs + corner7nm_SS.tSetupPs + corner7nm_SS.tSkewPs ≤ p.2 ∧
    checkAllCombPathsMeetDelay c (p.2 - (corner7nm_SS.tCqMaxPs + corner7nm_SS.tSetupPs + corner7nm_SS.tSkewPs)) p.1.edges = true
   else True)
def checkRetimeSta (_grade : Nat) (p : RetimeProblem) (c : RetimingCert) : Verdict HwClause :=
  if !(checkGraphWellFormed p.1) || p.2 == 0 then .refused .unsatRetimeTarget []
  else if checkRetimingCert p.1 c corner7nm_SS p.2 then .ok
  else .refused (.retimeInvalidLagOrTiming p.1.name) []
theorem checkRetimeSta_ok_iff (r : Nat) (p : RetimeProblem) (c : RetimingCert) :
    checkRetimeSta r p c = .ok ↔ RetimeStaMeaning p c := by
  unfold checkRetimeSta RetimeStaMeaning checkRetimingCert checkAllEdgesNonneg checkEdgeWeightNonneg
  cases hv : checkGraphWellFormed p.1 <;> by_cases hp : p.2 = 0 <;>
    simp [hp, List.all_eq_true, and_assoc, Nat.pos_iff_ne_zero]
instance retimeStaJudge : Obend.Judge RetimeProblem RetimingCert where
  Clause := HwClause
  Meaning := RetimeStaMeaning
  check := checkRetimeSta
  sound := by intro r o c h; exact (checkRetimeSta_ok_iff r o c).mp h
  refutes | .unsatRetimeTarget => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkRetimeSta at hc
    split at hc
    · rename_i ho
      simp [hm.1, Nat.ne_of_gt hm.2.1] at ho
    · split at hc
      · cases hc
      · cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c,hc⟩; exact ⟨c,0,(checkRetimeSta_ok_iff 0 o c).mpr hc⟩
  mono := by intros; rfl
abbrev PnrProblem := BelNetlist × ProcessCorner × Nat
def PnrBitstreamMeaning (p : PnrProblem) (c : PnrCertificate) : Prop :=
  (∀ cell ∈ p.1.cells, checkBelCellValid cell = true) ∧ 0 < p.2.2 ∧
  c.designName = p.1.moduleName ∧ c.placedCells.map (·.cellId) = List.range p.1.cells.length ∧
  checkPlacementInjective c.placedCells = true ∧
  (∀ net ∈ c.routedNets, checkNetConnectivity net = true) ∧ checkRoutingDisjoint c.routedNets = true ∧
  (∀ net ∈ c.routedNets, checkNetElmoreTiming p.2.1 p.2.2 c.sinkCapFf net = true) ∧
  c.bitstreamFrames.map decodeBitstreamFrame = c.expectedConfigs
def checkPnrProblemJudge (_grade : Nat) (p : PnrProblem) (c : PnrCertificate) : Verdict HwClause :=
  if !checkBelNetlistValid p.1 || p.2.2 == 0 then .refused .invalidPnrProblem []
  else if checkPnrCertificate p.1 p.2.1 p.2.2 c then .ok
  else .refused (.pnrCollisionShortOrTiming c.designName) []
theorem checkPnrProblemJudge_ok_iff (r : Nat) (p : PnrProblem) (c : PnrCertificate) :
    checkPnrProblemJudge r p c = .ok ↔ PnrBitstreamMeaning p c := by
  have he : PnrBitstreamMeaning p c ↔ checkBelNetlistValid p.1 = true ∧ p.2.2 ≠ 0 ∧
      checkPnrCertificate p.1 p.2.1 p.2.2 c = true := by
    simp [PnrBitstreamMeaning,checkPnrCertificate,checkBelNetlistValid,List.all_eq_true,and_assoc,Nat.pos_iff_ne_zero]
  rw [he]
  cases hv : checkBelNetlistValid p.1 <;> by_cases hp : p.2.2 = 0 <;>
    cases hc : checkPnrCertificate p.1 p.2.1 p.2.2 c <;> simp [checkPnrProblemJudge,hv,hp,hc]
instance pnrBitstreamJudge : Obend.Judge PnrProblem PnrCertificate where
  Clause := HwClause
  Meaning := PnrBitstreamMeaning
  check := checkPnrProblemJudge
  sound := by intro r o c h; exact (checkPnrProblemJudge_ok_iff r o c).mp h
  refutes | .invalidPnrProblem => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkPnrProblemJudge at hc
    split at hc
    · rename_i ho
      have hv : checkBelNetlistValid o.1 = true := by simpa [checkBelNetlistValid,List.all_eq_true] using hm.1
      simp [hv, Nat.ne_of_gt hm.2.1] at ho
    · split at hc
      · cases hc
      · cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c,hc⟩; exact ⟨c,0,(checkPnrProblemJudge_ok_iff 0 o c).mpr hc⟩
  mono := by intros; rfl
theorem rtlSynthJudge_refutes_nonconstant : (∃ k, rtlSynthJudge.refutes k = true) ∧ (∃ k, rtlSynthJudge.refutes k = false) :=
  ⟨⟨.emptyRtlTopName,rfl⟩,⟨.rtlInvalidDagOrCdc "bad",rfl⟩⟩
theorem retimeStaJudge_refutes_nonconstant : (∃ k, retimeStaJudge.refutes k = true) ∧ (∃ k, retimeStaJudge.refutes k = false) :=
  ⟨⟨.unsatRetimeTarget,rfl⟩,⟨.retimeInvalidLagOrTiming "bad",rfl⟩⟩
theorem pnrBitstreamJudge_refutes_nonconstant : (∃ k, pnrBitstreamJudge.refutes k = true) ∧ (∃ k, pnrBitstreamJudge.refutes k = false) :=
  ⟨⟨.invalidPnrProblem,rfl⟩,⟨.pnrCollisionShortOrTiming "bad",rfl⟩⟩
def badLoopRtlModule : RtlModule where
  name       := "bad_loop_mod"
  inputNames := ["in0"]
  wires      := [{ wireIdx := 0, name := "w0", expr := .alu .add (.wireRef 0) (.const 1#64) }]
  regs       := []
  outputs    := [{ name := "out0", expr := .wireRef 0 }]
theorem badLoopRtlModule_refused :
    checkRtlSynth 0 "bad_loop_mod" badLoopRtlModule =
      .refused (.rtlInvalidDagOrCdc "bad_loop_mod") [] := by
  rfl
def parseLeadingDigitsAux : List Char → Nat → Bool → Option Nat
  | [], acc, true => some acc
  | [], _, false => none
  | c :: cs, acc, seen =>
    if '0' ≤ c && c ≤ '9' then
      parseLeadingDigitsAux cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else if seen then
      some acc
    else
      none
def isWireIdentChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'
def isFieldSepChar (c : Char) : Bool :=
  c == '"' || c == ':' || c == '=' || c == ' ' || c == '\t'
def hasFieldSepHead : List Char → Bool
  | [] => false
  | c :: _ => isFieldSepChar c
def skipFieldSep : List Char → List Char
  | [] => []
  | c :: cs =>
    if isFieldSepChar c then
      skipFieldSep cs
    else
      c :: cs
def parseLeadingStringTokenAux : List Char → List Char → Option String
  | [], acc => if acc.isEmpty then none else some (String.ofList acc.reverse)
  | c :: cs, acc =>
    if isWireIdentChar c || c == '-' || c == '.' then
      parseLeadingStringTokenAux cs (c :: acc)
    else if acc.isEmpty then
      none
    else
      some (String.ofList acc.reverse)
def stripCharPrefix : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p == c then stripCharPrefix ps cs else none
  | _ :: _, [] => none
def scanNatAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option Nat
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match parseLeadingDigitsAux (skipFieldSep rest) 0 false with
          | some n => some n
          | none => scanNatAfterPatternAux pat nextPrev cs
        else
          scanNatAfterPatternAux pat nextPrev cs
      | none => scanNatAfterPatternAux pat nextPrev cs
    else
      scanNatAfterPatternAux pat nextPrev cs
def scanNatAfterPattern (pat : List Char) (cs : List Char) : Option Nat :=
  scanNatAfterPatternAux pat false cs
def scanIntAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option Int
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match skipFieldSep rest with
          | '-' :: digits =>
            match parseLeadingDigitsAux digits 0 false with
            | some n => some (-Int.ofNat n)
            | none => scanIntAfterPatternAux pat nextPrev cs
          | digits =>
            match parseLeadingDigitsAux digits 0 false with
            | some n => some (Int.ofNat n)
            | none => scanIntAfterPatternAux pat nextPrev cs
        else
          scanIntAfterPatternAux pat nextPrev cs
      | none => scanIntAfterPatternAux pat nextPrev cs
    else
      scanIntAfterPatternAux pat nextPrev cs
def scanIntAfterPattern (pat : List Char) (cs : List Char) : Option Int :=
  scanIntAfterPatternAux pat false cs
def scanStringAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option String
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match parseLeadingStringTokenAux (skipFieldSep rest) [] with
          | some s => some s
          | none => scanStringAfterPatternAux pat nextPrev cs
        else
          scanStringAfterPatternAux pat nextPrev cs
      | none => scanStringAfterPatternAux pat nextPrev cs
    else
      scanStringAfterPatternAux pat nextPrev cs
def scanStringAfterPattern (pat : List Char) (cs : List Char) : Option String :=
  scanStringAfterPatternAux pat false cs
def extractStringField (s : String) (field : String) : Option String :=
  match scanStringAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some v => some v
  | none => scanStringAfterPattern field.toList s.toList
def extractNatField (s : String) (field : String) : Option Nat :=
  match scanNatAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some n => some n
  | none => scanNatAfterPattern field.toList s.toList
def extractIntField (s : String) (field : String) : Option Int :=
  match scanIntAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some v => some v
  | none => scanIntAfterPattern field.toList s.toList
def ensureWireFrame (s : String) : Except String Unit :=
  let cs := s.toList
  if cs.contains ':' || cs.contains '=' || cs.contains '{' then
    .ok ()
  else
    .error "invalid wire frame: expected JSON object or key=value wire string"
def requireStringField (s field : String) : Except String String :=
  match extractStringField s field with
  | some v => .ok v
  | none   => .error s!"missing required string field '{field}'"
def requireNatField (s field : String) : Except String Nat :=
  match extractNatField s field with
  | some n => .ok n
  | none   => .error s!"missing required nat field '{field}'"
def requireIntField (s field : String) : Except String Int :=
  match extractIntField s field with
  | some v => .ok v
  | none   => .error s!"missing required int field '{field}'"
def rtlDigitChar (d : Nat) : Char :=
  Char.ofNat ('0'.toNat + d)
def rtlNatToDigitsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let acc' := rtlDigitChar (n % 10) :: acc
    let q := n / 10
    if q == 0 then acc' else rtlNatToDigitsAux fuel q acc'
def rtlNatToStr (n : Nat) : String :=
  String.ofList (rtlNatToDigitsAux (n + 1) n [])
def rtlJoinComma : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "," ++ rtlJoinComma rest
def isFlatRtlOperand : RtlExpr → Bool
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .alu .add (.inputPort 0) (.wireRef _) => true
  | _ => false
def isFlatWireAssign (w : WireAssign) : Bool :=
  match w.expr with
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .alu _ lhs rhs => isFlatRtlOperand lhs && isFlatRtlOperand rhs
  | _ => false
def flattenRtlExprAux (numInputs numRegs : Nat) (wireMap : List (Nat × Nat)) :
    RtlExpr → List WireAssign → (List WireAssign × Nat)
  | .const v, acc =>
    let idx := acc.length
    (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .const v }], idx)
  | .inputPort p, acc =>
    let pSafe := if p < numInputs then p else 0
    let idx := acc.length
    (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .inputPort pSafe }], idx)
  | .wireRef r, acc =>
    let mapped := (wireMap.lookup r).getD 0
    let safeRef := if mapped < acc.length then mapped else 0
    if acc.isEmpty then
      (acc ++ [{ wireIdx := 0, name := "w0", expr := .const 0#64 }], 0)
    else
      (acc, safeRef)
  | .regRead r, acc =>
    let idx := acc.length
    if r < numRegs then
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .regRead r }], idx)
    else
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .const 0#64 }], idx)
  | .alu op lhs rhs, acc =>
    let (acc1, lIdx) := flattenRtlExprAux numInputs numRegs wireMap lhs acc
    let (acc2, rIdx) := flattenRtlExprAux numInputs numRegs wireMap rhs acc1
    let idx := acc2.length
    (acc2 ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .alu op (.wireRef lIdx) (.wireRef rIdx) }], idx)
  | .mux c t f, acc =>
    let (acc1, cIdx) := flattenRtlExprAux numInputs numRegs wireMap c acc
    let (acc2, tIdx) := flattenRtlExprAux numInputs numRegs wireMap t acc1
    let (acc3, fIdx) := flattenRtlExprAux numInputs numRegs wireMap f acc2
    let idx := acc3.length
    let mk (i : Nat) (e : RtlExpr) : WireAssign :=
      { wireIdx := i, name := "w" ++ rtlNatToStr i, expr := e }
    (acc3 ++
      [ mk idx (.alu .eq (.wireRef cIdx) (.const 0#64))
      , mk (idx + 1) (.alu .sub (.const 0#64) (.wireRef idx))
      , mk (idx + 2) (.alu .bitXor (.wireRef (idx + 1)) (.const 0xFFFFFFFFFFFFFFFF#64))
      , mk (idx + 3) (.alu .bitOr
          (.alu .bitAnd (.wireRef (idx + 2)) (.wireRef tIdx))
          (.alu .bitAnd (.wireRef (idx + 1)) (.wireRef fIdx))) ], idx + 3)
  | .bitNot a, acc =>
    let (acc1, aIdx) := flattenRtlExprAux numInputs numRegs wireMap a acc
    let idx := acc1.length
    (acc1 ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .alu .bitXor (.wireRef aIdx) (.const 0xFFFFFFFFFFFFFFFF#64) }], idx)
  | .resize op a, acc =>
    -- A width operator as 3-address ALU wires: masks, a shift, and for `sext` the
    -- `((x & m_f) ^ s) - s` sign-extension identity with `s = 2^(f-1)`.
    let (acc1, aIdx) := flattenRtlExprAux numInputs numRegs wireMap a acc
    let mkW (acc : List WireAssign) (e : RtlExpr) : List WireAssign × Nat :=
      let idx := acc.length
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := e }], idx)
    let mask (w : Nat) : RtlExpr := .const (BitVec.ofNat 64 (2 ^ (min w 64) - 1))
    match op with
    | .zext _ => (acc1, aIdx)
    | .trunc w => mkW acc1 (.alu .bitAnd (.wireRef aIdx) (mask w))
    | .slice hi lo =>
      let (acc2, sIdx) := mkW acc1 (.alu .lshr (.wireRef aIdx) (.const (BitVec.ofNat 64 lo)))
      mkW acc2 (.alu .bitAnd (.wireRef sIdx) (mask (hi + 1 - lo)))
    | .sext f t =>
      if f == 0 then mkW acc1 (.const 0#64)
      else if f ≥ 64 then mkW acc1 (.alu .bitAnd (.wireRef aIdx) (mask t))
      else
      let s : RtlExpr := .const (BitVec.ofNat 64 (2 ^ (f - 1)))
      let (acc2, i1) := mkW acc1 (.alu .bitAnd (.wireRef aIdx) (mask f))
      let (acc3, i2) := mkW acc2 (.alu .bitXor (.wireRef i1) s)
      let (acc4, i3) := mkW acc3 (.alu .sub (.wireRef i2) s)
      mkW acc4 (.alu .bitAnd (.wireRef i3) (mask t))
def flattenWireListAux (numInputs numRegs : Nat) :
    List WireAssign → List (Nat × Nat) → List WireAssign → (List WireAssign × List (Nat × Nat))
  | [], wireMap, acc => (acc, wireMap)
  | w :: ws, wireMap, acc =>
    let (acc', rootIdx) := flattenRtlExprAux numInputs numRegs wireMap w.expr acc
    flattenWireListAux numInputs numRegs ws ((w.wireIdx, rootIdx) :: wireMap) acc'
def normalizeRtlModuleForWire (m : RtlModule) : RtlModule :=
  if m.wires.all isFlatWireAssign && m.regs.all (fun r => isFlatRtlOperand r.nextExpr) &&
      m.outputs.all (fun o => isFlatRtlOperand o.expr) then m else
  let (wires, wireMap) := flattenWireListAux m.inputNames.length m.regs.length m.wires [] []
  let (wires, regs) := m.regs.foldl (fun (acc : List WireAssign × List RegSpec) r =>
    let (ws, idx) := flattenRtlExprAux m.inputNames.length m.regs.length wireMap r.nextExpr acc.1
    (ws, acc.2 ++ [{ r with nextExpr := .wireRef idx }])) (wires, [])
  let (wires, outputs) := m.outputs.foldl (fun (acc : List WireAssign × List OutputPort) o =>
    let (ws, idx) := flattenRtlExprAux m.inputNames.length m.regs.length wireMap o.expr acc.1
    (ws, acc.2 ++ [{ o with expr := .wireRef idx }])) (wires, [])
  { m with wires := wires, regs := regs, outputs := outputs }
theorem evalMuxMask_eq (c t f : BitVec 64) :
    let maskF := 0#64 - (if c == 0#64 then 1#64 else 0#64)
    let maskT := maskF ^^^ 0xFFFFFFFFFFFFFFFF#64
    (maskT &&& t) ||| (maskF &&& f) = (if c != 0#64 then t else f) := by
  by_cases h : c = 0#64
  · simpa [h] using (BitVec.allOnes_and (x := f))
  · simpa [h] using (BitVec.allOnes_and (x := t))
def encodeRtlSynthObj (x : String) : String := encodeWire x
def decodeRtlSynthObj (s : String) : Except String String := decodeWire s
theorem decodeRtlSynthObj_encodeRtlSynthObj_roundtrip (x : String) :
    decodeRtlSynthObj (encodeRtlSynthObj x) = .ok x := decodeWire_encodeWire x
def encodeRtlSynthCert (x : RtlModule) : String := encodeWire x
def decodeRtlSynthCert (s : String) : Except String RtlModule := decodeWire s
theorem decodeRtlSynthCert_encodeRtlSynthCert_roundtrip (x : RtlModule) :
    decodeRtlSynthCert (encodeRtlSynthCert x) = .ok x := decodeWire_encodeWire x
def encodeRetimeObj (x : RetimeProblem) : String := encodeWire x
def decodeRetimeObj (s : String) : Except String RetimeProblem := decodeWire s
theorem decodeRetimeObj_encodeRetimeObj_roundtrip (x : RetimeProblem) :
    decodeRetimeObj (encodeRetimeObj x) = .ok x := decodeWire_encodeWire x
def encodeRetimeCert (x : RetimingCert) : String := encodeWire x
def decodeRetimeCert (s : String) : Except String RetimingCert := decodeWire s
theorem decodeRetimeCert_encodeRetimeCert_roundtrip (x : RetimingCert) :
    decodeRetimeCert (encodeRetimeCert x) = .ok x := decodeWire_encodeWire x
def encodePnrProblem (x : PnrProblem) : String := encodeWire x
def decodePnrProblem (s : String) : Except String PnrProblem := decodeWire s
theorem decodePnrProblem_encodePnrProblem_roundtrip (x : PnrProblem) :
    decodePnrProblem (encodePnrProblem x) = .ok x := decodeWire_encodeWire x
def encodePnrWireCert (x : PnrCertificate) : String := encodeWire x
def decodePnrWireCert (s : String) : Except String PnrCertificate := decodeWire s
theorem decodePnrWireCert_encodePnrWireCert_roundtrip (x : PnrCertificate) :
    decodePnrWireCert (encodePnrWireCert x) = .ok x := decodeWire_encodeWire x
@[expose] def hwSynthFormat : Format where
  name        := "hw-rtl-synth"
  version     := "1"
  Obj         := String
  Cert        := RtlModule
  judge       := rtlSynthJudge
  decodeObj   := decodeRtlSynthObj
  decodeCert  := decodeRtlSynthCert
  trust       := .kernel
  regime      := .decidable
  bad         := ("bad_loop_mod", badLoopRtlModule)
  badGrade    := 0
  bad_refused := ⟨_, _, badLoopRtlModule_refused⟩
@[expose] def rtlSynthFormat : Format where
  name        := "rtl-synth"
  version     := "1"
  Obj         := String
  Cert        := RtlModule
  judge       := rtlSynthJudge
  decodeObj   := decodeRtlSynthObj
  decodeCert  := decodeRtlSynthCert
  trust       := .kernel
  regime      := .decidable
  bad         := ("bad_loop_mod", badLoopRtlModule)
  badGrade    := 0
  bad_refused := ⟨_, _, badLoopRtlModule_refused⟩
theorem hwSynthFormat_sound {r : Nat} {obj cert : String}
    (h : hwSynthFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRtlSynthObj obj = .ok o ∧ decodeRtlSynthCert cert = .ok c ∧
      RtlSynthMeaning o c :=
  hwSynthFormat.checkBytes_sound h
theorem rtlSynthFormat_sound {r : Nat} {obj cert : String}
    (h : rtlSynthFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRtlSynthObj obj = .ok o ∧ decodeRtlSynthCert cert = .ok c ∧
      RtlSynthMeaning o c :=
  rtlSynthFormat.checkBytes_sound h
/-- **Universal Wire Round-Trip Soundness & Completeness (`rtlSynthFormat_roundtrip_iff`)**:
For EVERY grade `r : Nat`, top module name `name : String`, and `m : RtlModule`,
`rtlSynthFormat.checkBytes r (encodeRtlSynthObj name) (encodeRtlSynthCert m) = .ok`
holds iff `RtlSynthMeaning name m`. -/
theorem rtlSynthFormat_roundtrip_iff (r : Nat) (name : String) (m : RtlModule) :
    rtlSynthFormat.checkBytes r (encodeRtlSynthObj name) (encodeRtlSynthCert m) = .ok ↔
      RtlSynthMeaning name m := by
  unfold Format.checkBytes rtlSynthFormat
  dsimp only
  rw [decodeRtlSynthObj_encodeRtlSynthObj_roundtrip, decodeRtlSynthCert_encodeRtlSynthCert_roundtrip]
  dsimp only
  have hMap : ∀ v : Verdict HwClause, Verdict.map FormatClause.judge v = .ok ↔ v = .ok := by
    intro v; cases v <;> simp [Verdict.map]
  rw [hMap]
  exact checkRtlSynth_ok_iff r name m
instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun hEq => by cases hEq; exact h rfl)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun hEq => by cases hEq; exact h rfl)
  | .error _, .ok _ => isFalse (fun hEq => by cases hEq)
  | .ok _, .error _ => isFalse (fun hEq => by cases hEq)
@[expose] def _root_.Obend.Judge.Verdict.isOk {C : Type} : Verdict C → Bool
  | .ok => true
  | _   => false
theorem verdict_eq_ok_of_isOk {C : Type} {v : Verdict C} (h : v.isOk = true) : v = .ok := by
  cases v <;> simp [Obend.Judge.Verdict.isOk] at h ⊢
theorem verdict_ne_ok_of_isOk_false {C : Type} {v : Verdict C} (h : v.isOk = false) : v ≠ .ok := by
  intro hEq; subst hEq; cases h
def flatMulAddRtlModule : RtlModule where
  name       := "obend_flat_mul_add_rtl"
  inputNames := ["arg"]
  wires      :=
    [ { wireIdx := 0, name := "w0", expr := .alu .mul (.inputPort 0) (.const 2#64) }
    , { wireIdx := 1, name := "w1", expr := .alu .add (.wireRef 0) (.const 1#64) } ]
  regs       :=
    [ { regIdx := 0, name := "reg_y", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .wireRef 1 } ]
  outputs    := [{ name := "out_y", expr := .wireRef 1 }]
def checkPnrJudge (_grade : Nat) (periodPs : Nat) (cert : PnrCertificate) : Verdict HwClause :=
  if checkPnrCertificate validAdderBelNetlist corner7nm_SS periodPs cert then
    .ok
  else
    .refused (.pnrCollisionShortOrTiming cert.designName) []
def decodePnrCert (s : String) : Except String PnrCertificate := do
  ensureWireFrame s
  let designName  ← requireStringField s "designName"
  let sinkCap     ← requireNatField s "sinkCapFf"
  let cell1TileY  ← requireNatField s "cell1TileY"
  let cell0Bel    ← requireNatField s "cell0BelSlot"
  let cell1Bel    ← requireNatField s "cell1BelSlot"
  let net0DstWire ← requireNatField s "net0DstWire"
  let net1DstWire ← requireNatField s "net1DstWire"
  return {
    designName  := designName
    placedCells :=
      [ { cellId := 0, tileX := 0, tileY := 0, belSlot := cell0Bel, lutInit := 0x6 }
      , { cellId := 1, tileX := 0, tileY := cell1TileY, belSlot := cell1Bel, lutInit := 0x6 } ]
    routedNets  :=
      [ { netId := 0, srcWire := 10, dstWire := net0DstWire
        , hops := [ { srcWire := 10, dstWire := 11, resOhm := 50, capFf := 4 }
                  , { srcWire := 11, dstWire := net0DstWire, resOhm := 50, capFf := 4 } ] }
      , { netId := 1, srcWire := 20, dstWire := net1DstWire
        , hops := [ { srcWire := 20, dstWire := net1DstWire, resOhm := 40, capFf := 3 } ] } ]
    expectedConfigs := validAdderPnrCert.expectedConfigs
    bitstreamFrames := validAdderPnrCert.bitstreamFrames
    sinkCapFf       := sinkCap
  }
theorem badRetimeCert_refused : checkRetimeSta 0 (macUnretimedGraph,2000) negativeWeightBadCert =
    .refused (.retimeInvalidLagOrTiming "mac_2stage") [] := by decide +kernel
theorem badPnrCert_refused : checkPnrJudge 0 2000 collidingBelPnrCert =
    .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") [] := by decide +kernel
@[expose] def hwRetimeFormat : Format where
  name := "hw-retime-sta"
  version := "1"
  Obj := RetimeProblem
  Cert := RetimingCert
  judge := retimeStaJudge
  decodeObj := decodeRetimeObj
  decodeCert := decodeRetimeCert
  trust := .kernel
  regime := .decidable
  bad := ((macUnretimedGraph,2000),negativeWeightBadCert)
  badGrade := 0
  bad_refused := ⟨_,_,badRetimeCert_refused⟩
theorem badPnrProblemCert_refused :
    checkPnrProblemJudge 0 (validAdderBelNetlist,corner7nm_SS,2000) collidingBelPnrCert =
      .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") [] := by decide +kernel
@[expose] def hwPnrFormat : Format where
  name := "hw-pnr-bitstream"
  version := "1"
  Obj := PnrProblem
  Cert := PnrCertificate
  judge := pnrBitstreamJudge
  decodeObj := decodePnrProblem
  decodeCert := decodePnrWireCert
  trust := .kernel
  regime := .decidable
  bad := ((validAdderBelNetlist,corner7nm_SS,2000),collidingBelPnrCert)
  badGrade := 0
  bad_refused := ⟨_,_,badPnrProblemCert_refused⟩
theorem hwRetimeFormat_sound {r : Nat} {obj cert : String}
    (h : hwRetimeFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRetimeObj obj = .ok o ∧ decodeRetimeCert cert = .ok c ∧ RetimeStaMeaning o c :=
  hwRetimeFormat.checkBytes_sound h
theorem hwPnrFormat_sound {r : Nat} {obj cert : String}
    (h : hwPnrFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodePnrProblem obj = .ok o ∧ decodePnrWireCert cert = .ok c ∧ PnrBitstreamMeaning o c :=
  hwPnrFormat.checkBytes_sound h
/-! ## 5. Format 4: `datasheet-fit@1` (Automated Datasheet Calibration, `74LS00` + `74HCT00` + INA + Buck Judge) -/
/-- Declarative physical/electrical specification for `datasheet-fit@1`: suite identity, DC noise
margins, `74LS00` saturated totem-pole fanout swing, empirical $L_\infty$ curve fit, laser-trimmed INA
common-mode balance, and synchronous Buck CCM & inductor core-saturation bounds. -/
def DatasheetFitMeaning (expectedSuite : String) (c : DatasheetFitCert) : Prop :=
  expectedSuite ≠ "" ∧ c.suiteName = expectedSuite ∧
  c.minMarginMv ≤ noiseMarginHigh c.driverSpec c.receiverSpec c.pullupBoostMv ∧
  c.minMarginMv ≤ noiseMarginLow c.driverSpec c.receiverSpec ∧
  c.driverSpec.volMaxMv < c.receiverSpec.vihMinMv ∧
  c.fanout ≤ c.ttlParams.maxFanout ∧
  evalTtlNandMv c.ttlParams 2000 2000 c.fanout ≤ 400 ∧
  c.modelPreds.length = c.datasheetPoints.length ∧
  0 ≤ c.maxCalErrMv ∧
  maxCurveErrorLInf c.modelPreds c.datasheetPoints ≤ c.maxCalErrMv ∧
  c.inaSpec.gainCmRaw = c.inaSpec.trimCmCancel ∧
  c.buckStage.dutyPermille ≤ 1000 ∧
  0 < c.buckStage.inductanceUh ∧
  0 < c.buckStage.fswKhz ∧
  evalBuckRippleMa c.buckStage ≤ 2 * c.buckStage.iLoadMa ∧
  evalBuckPeakInductorMa c.buckStage ≤ c.buckStage.iSatMaxMa
def checkDatasheetFitJudge (_grade : Nat) (expectedSuite : String) (cert : DatasheetFitCert) : Verdict HwClause :=
  if expectedSuite == "" then .refused .emptyDatasheetSuiteName []
  else if (cert.suiteName == expectedSuite) && checkDatasheetFitSignoff cert then .ok
  else .refused (.datasheetCalibrationOrMarginViolation cert.suiteName) []
theorem checkDatasheetFitJudge_ok_iff (r : Nat) (expectedSuite : String) (c : DatasheetFitCert) :
    checkDatasheetFitJudge r expectedSuite c = .ok ↔ DatasheetFitMeaning expectedSuite c := by
  unfold checkDatasheetFitJudge
  by_cases hEmpty : expectedSuite = ""
  · subst hEmpty; simp [DatasheetFitMeaning]
  · have hB : (expectedSuite == "") = false := beq_eq_false_iff_ne.mpr hEmpty
    simp [hB, hEmpty, DatasheetFitMeaning, checkDatasheetFitSignoff, checkLogicInterface,
      checkTtlFanout, checkModelCalibration, checkBuckCcmSafe, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, and_assoc]
instance datasheetFitJudge : Obend.Judge String DatasheetFitCert where
  Clause := HwClause
  Meaning := DatasheetFitMeaning
  check := checkDatasheetFitJudge
  sound := by intro r o c h; exact (checkDatasheetFitJudge_ok_iff r o c).mp h
  refutes | .emptyDatasheetSuiteName => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkDatasheetFitJudge at hc
    split at hc
    · rename_i ho; exact hm.1 (beq_iff_eq.mp ho)
    · split at hc <;> cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c, hc⟩; exact ⟨c, 0, (checkDatasheetFitJudge_ok_iff 0 o c).mpr hc⟩
  mono := by intro _ _ _ _ _ _; rfl
theorem badDatasheetFitCert_refused :
    checkDatasheetFitJudge 0 "obend_74ls_hct_ina_calibrated" badDirect74HcFitCert =
      .refused (.datasheetCalibrationOrMarginViolation "obend_74ls_hct_ina_calibrated") [] := by decide +kernel
def decodeDatasheetFitObj (s : String) : Except String String := do
  ensureWireFrame s; requireStringField s "suite"
def decodeDatasheetFitCert (s : String) : Except String DatasheetFitCert := do
  ensureWireFrame s
  let suiteName   ← requireStringField s "suiteName"
  let pullup      ← requireIntField s "pullupBoostMv"
  let minMargin   ← requireIntField s "minMarginMv"
  let rcvVihMinMv ← requireIntField s "rcvVihMinMv"
  let rcvVilMaxMv ← requireIntField s "rcvVilMaxMv"
  let fanout      ← requireNatField s "fanout"
  let maxCalErr   ← requireIntField s "maxCalErrMv"
  let buckLoadMa  ← requireNatField s "buckLoadMa"
  return {
    suiteName := suiteName, driverSpec := sn74ls00Datasheet.logic
    receiverSpec := { cd74hct00Datasheet.logic with vihMinMv := rcvVihMinMv, vilMaxMv := rcvVilMaxMv }
    pullupBoostMv := pullup, minMarginMv := minMargin, ttlParams := sn74ls00TotemParams
    fanout := fanout, modelPreds := calibrated74ls00ModelPreds
    datasheetPoints := sn74ls00Datasheet.transferCurve, maxCalErrMv := maxCalErr
    inaSpec := precisionMatchedIna, buckStage := { buck12vTo5v2aSpec with iLoadMa := buckLoadMa } }
def datasheetFitFormat : Format where
  name := "datasheet-fit"; version := "1"; Obj := String; Cert := DatasheetFitCert
  judge := datasheetFitJudge; decodeObj := decodeDatasheetFitObj; decodeCert := decodeDatasheetFitCert
  trust := .kernel; regime := .decidable
  bad := ("obend_74ls_hct_ina_calibrated", badDirect74HcFitCert); badGrade := 0
  bad_refused := ⟨_, _, badDatasheetFitCert_refused⟩
theorem datasheetFitFormat_sound {r : Nat} {obj cert : String}
    (h : datasheetFitFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeDatasheetFitObj obj = .ok o ∧ decodeDatasheetFitCert cert = .ok c ∧
      DatasheetFitMeaning o c :=
  datasheetFitFormat.checkBytes_sound h
theorem datasheetFitFormat_complete {o : String} (h : ∃ c : DatasheetFitCert, DatasheetFitMeaning o c) :
    ∃ c r, datasheetFitJudge.check r o c = .ok :=
  datasheetFitJudge.complete trivial h
/-! ## 6. Format 5: `agentic-eda-swap@1` (Smart-Contract Markdown Vault BOM Swap Judge) -/
/-- Declarative semantic specification for `agentic-eda-swap@1`: vault `.obend` law admission plus
denotational law satisfaction and physical 3.3V LVCMOS static noise-margin inequalities. -/
def AgenticEdaSwapMeaning (minMarginMv : Int) (c : EdaVaultPart) : Prop :=
  let oldData := Obend.Vault.stateOf edaStateKeys baselineLdoPart.toScalarFields
  let newData := Obend.Vault.stateOf edaStateKeys c.toScalarFields
  let reqData := Obend.Vault.requestOf "procurement_scout" .write defaultEdaFacts
  Obend.Vault.judge (Obend.Vault.stateTy edaStateKeys) c.pageName defaultEdaLaws oldData newData reqData = .admitted ∧
  (∀ p ∈ defaultEdaLaws, p.2.denote defaultEdaFacts (some oldData) newData = true) ∧
  defaultDatasheetCite256.pinnedDigest256 = defaultDatasheetCite256.currentDigest256 ∧
  minMarginMv ≤ noiseMarginHigh c.toLogicFamilySpec lvcmos33ReceiverSpec 0 ∧
  minMarginMv ≤ noiseMarginLow c.toLogicFamilySpec lvcmos33ReceiverSpec ∧
  c.toLogicFamilySpec.volMaxMv < lvcmos33ReceiverSpec.vihMinMv
def checkAgenticEdaSwapBool (minMarginMv : Int) (candidatePart : EdaVaultPart) : Bool :=
  judgeAgenticEdaProposal defaultEdaLaws baselineLdoPart candidatePart lvcmos33ReceiverSpec
    minMarginMv defaultDatasheetCite256 "procurement_scout" defaultEdaFacts == .admitted
def checkAgenticEdaJudge (_grade : Nat) (minMarginMv : Int) (candidatePart : EdaVaultPart) : Verdict HwClause :=
  if decide (800 < minMarginMv) then .refused .unsatAgenticMarginTarget []
  else if checkAgenticEdaSwapBool minMarginMv candidatePart then .ok
  else .refused (.agenticEdaSwapViolation candidatePart.pageName) []
theorem checkAgenticEdaSwapBool_iff (minMarginMv : Int) (c : EdaVaultPart) :
    checkAgenticEdaSwapBool minMarginMv c = true ↔ AgenticEdaSwapMeaning minMarginMv c := by
  have hCite : checkDatasheetCite256Fresh defaultDatasheetCite256 = true := by decide
  unfold checkAgenticEdaSwapBool judgeAgenticEdaProposal AgenticEdaSwapMeaning
  dsimp only
  cases hj : Obend.Vault.judge (Obend.Vault.stateTy edaStateKeys) c.pageName defaultEdaLaws
      (Obend.Vault.stateOf edaStateKeys baselineLdoPart.toScalarFields)
      (Obend.Vault.stateOf edaStateKeys c.toScalarFields)
      (Obend.Vault.requestOf "procurement_scout" .write defaultEdaFacts) with
  | refused _ _ => simp
  | undecided _ => simp
  | admitted =>
    have hDenote := Obend.Vault.judge_admits (k := .write) hj
    rw [hCite]; dsimp only
    cases hIf : checkLogicInterface c.toLogicFamilySpec lvcmos33ReceiverSpec 0 minMarginMv
    · simp only [checkLogicInterface, Bool.and_eq_true, Bool.and_eq_false_imp, decide_eq_true_eq,
        decide_eq_false_iff_not] at hIf
      exact ⟨fun h => (by cases h), fun ⟨_, _, _, h1, h2, h3⟩ => False.elim (hIf ⟨h1, h2⟩ h3)⟩
    · simp only [checkLogicInterface, Bool.and_eq_true, decide_eq_true_eq] at hIf
      exact ⟨fun _ => ⟨rfl, hDenote, rfl, hIf.1.1, hIf.1.2, hIf.2⟩, fun _ => rfl⟩
theorem checkAgenticEdaJudge_ok_iff (r : Nat) (minMarginMv : Int) (c : EdaVaultPart) :
    checkAgenticEdaJudge r minMarginMv c = .ok ↔ AgenticEdaSwapMeaning minMarginMv c := by
  unfold checkAgenticEdaJudge
  by_cases hGt : 800 < minMarginMv
  · simp only [decide_eq_true hGt, ↓reduceIte, reduceCtorEq, false_iff]
    intro hm
    have hLow := hm.2.2.2.2.1
    dsimp only [noiseMarginLow, lvcmos33ReceiverSpec, EdaVaultPart.toLogicFamilySpec] at hLow
    omega
  · simp only [decide_eq_false hGt, Bool.false_eq_true, ↓reduceIte]
    cases hb : checkAgenticEdaSwapBool minMarginMv c <;>
      simpa [hb] using (checkAgenticEdaSwapBool_iff minMarginMv c)
instance agenticEdaJudge : Obend.Judge Int EdaVaultPart where
  Clause := HwClause
  Meaning := AgenticEdaSwapMeaning
  check := checkAgenticEdaJudge
  sound := by intro r o c h; exact (checkAgenticEdaJudge_ok_iff r o c).mp h
  refutes | .unsatAgenticMarginTarget => true | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    unfold checkAgenticEdaJudge at hc
    split at hc
    · rename_i hGt
      have hGt' : 800 < o := of_decide_eq_true hGt
      have hLow := hm.2.2.2.2.1
      dsimp only [noiseMarginLow, lvcmos33ReceiverSpec, EdaVaultPart.toLogicFamilySpec] at hLow
      omega
    · split at hc <;> cases hc; cases hk
  Fragment _ := True
  complete := by intro o _ ⟨c, hc⟩; exact ⟨c, 0, (checkAgenticEdaJudge_ok_iff 0 o c).mpr hc⟩
  mono := by intro _ _ _ _ _ _; rfl
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badAgenticEdaSwap_refused :
    checkAgenticEdaJudge 0 400 overbudgetSecondSourcePart =
      .refused (.agenticEdaSwapViolation "U4_LDO") [] := by decide +kernel
def decodeAgenticEdaObj (s : String) : Except String Int := do
  ensureWireFrame s; requireIntField s "minMarginMv"
def decodeAgenticEdaCert (s : String) : Except String EdaVaultPart := do
  ensureWireFrame s
  let pageName ← requireStringField s "pageName"
  let voh ← requireNatField s "vohMinMv"; let vih ← requireNatField s "vihMinMv"
  let vol ← requireNatField s "volMaxMv"; let vil ← requireNatField s "vilMaxMv"
  let pkgW ← requireNatField s "pkgWidthUm"; let pkgL ← requireNatField s "pkgLengthUm"
  let pins ← requireNatField s "pinCount"; let pitch ← requireNatField s "pinPitchUm"
  let tempMc ← requireNatField s "maxTempMc"; let vswr ← requireNatField s "vswrMilli"
  let drcErr ← requireNatField s "drcErrors"; let cost ← requireNatField s "costCents"
  return { pageName := pageName, vohMinMv := voh, vihMinMv := vih, volMaxMv := vol, vilMaxMv := vil
           pkgWidthUm := pkgW, pkgLengthUm := pkgL, pinCount := pins, pinPitchUm := pitch
           maxTempMc := tempMc, vswrMilli := vswr, drcErrors := drcErr, costCents := cost }
def agenticEdaFormat : Format where
  name := "agentic-eda-swap"; version := "1"; Obj := Int; Cert := EdaVaultPart
  judge := agenticEdaJudge; decodeObj := decodeAgenticEdaObj; decodeCert := decodeAgenticEdaCert
  trust := .kernel; regime := .decidable
  bad := (400, overbudgetSecondSourcePart); badGrade := 0
  bad_refused := ⟨_, _, badAgenticEdaSwap_refused⟩
theorem agenticEdaFormat_sound {r : Nat} {obj cert : String}
    (h : agenticEdaFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeAgenticEdaObj obj = .ok o ∧ decodeAgenticEdaCert cert = .ok c ∧
      AgenticEdaSwapMeaning o c :=
  agenticEdaFormat.checkBytes_sound h
/-! ## 12. Format 11: `hw-binary-cbor@1` & `hw-binary-tape-cbor@1` (RFC 8949 Binary CBOR Hardware Judges) -/
/-- Per-domain declarative mathematical specification over decoded `BinaryHwCert` parameters. -/
def BinaryHwCertDomainMeaning (c : BinaryHwCert) : Prop :=
  match c.domain with
  | .pnr =>
    let cfg0 : TileFrameConfig := { tileX := c.p0.toNat, tileY := c.p1.toNat, belSlot := 0, lutInit := 0x6, pipMask := 0x3 }
    let cfg1 : TileFrameConfig := { tileX := c.p2.toNat, tileY := c.p3.toNat, belSlot := 0, lutInit := 0x6, pipMask := 0x1 }
    checkPnrCertificate validAdderBelNetlist corner7nm_SS c.p5.toNat
      { validAdderPnrCert with
        placedCells := [ { cellId := 0, tileX := c.p0.toNat, tileY := c.p1.toNat, belSlot := 0, lutInit := 0x6 }
                       , { cellId := 1, tileX := c.p2.toNat, tileY := c.p3.toNat, belSlot := 0, lutInit := 0x6 } ]
        expectedConfigs := [cfg0, cfg1]
        bitstreamFrames := [encodeBitstreamFrame cfg0, encodeBitstreamFrame cfg1]
        sinkCapFf := c.p4.toNat } = true
  | .retiming =>
    checkRetimingCert macUnretimedGraph
      { vertexLags := [(0, c.p0), (1, c.p1), (2, c.p2)], ioLatencyShift := c.p3 }
      corner7nm_SS c.p5.toNat = true
  | .photonics =>
    let e1 : Obend.Hardware.Photonics.ComplexField := ⟨c.p2, c.p3⟩
    let e2 : Obend.Hardware.Photonics.ComplexField := ⟨c.p4, c.p5⟩
    let (o1, o2) := Obend.Hardware.Photonics.evalDirectionalCoupler2x2 c.p0 c.p1 e1 e2
    let (barCross, _) := Obend.Hardware.Photonics.evalCascadedMzi2x2 c.p0 c.p0 ⟨1, 0⟩ e1 ⟨0, 0⟩
    o1.normSq + o2.normSq = (c.p0 * c.p0 + c.p1 * c.p1) * (e1.normSq + e2.normSq) ∧
      0 < c.p0 * c.p0 + c.p1 * c.p1 ∧ barCross = ⟨0, 0⟩
  | .pcb =>
    Obend.Hardware.PCB.checkSingleEndedZ0 c.p0.toNat c.p1.toNat c.p2.toNat c.p3.toNat c.p4.toNat c.p5.toNat 3000 = true
  | .dpr =>
    ∃ opK rOp decTile,
      decodeTileOpKindBits c.p1.toNat = some opK ∧ decodeRuleOpcodeBits c.p2.toNat = some rOp ∧
      let tile := mkIcapRuleTile c.p0.toNat opK rOp c.p3.toNat
      decodeTileIcapWords (encodeTileIcapWords tile) = some decTile ∧ decTile = tile ∧
      evalRtlExpr (fun _ => BitVec.ofNat 64 c.p4.toNat) (fun _ => 0#64) (fun _ => 0#64) decTile.datapath =
        BitVec.ofNat 64 c.p5.toNat
  | .edaBomSwap =>
    AgenticEdaSwapMeaning c.p5 { baselineLdoPart with
      vohMinMv := c.p0.toNat, volMaxMv := c.p1.toNat, maxTempMc := c.p2.toNat,
      vswrMilli := c.p3.toNat, costCents := c.p4.toNat }
  | .multiphysics =>
    let edges : List Obend.Hardware.ThermalPassivity.ThermalEdge :=
      [ { nodeU := 0, nodeV := 1, conductanceMwPerK := c.p0 }
      , { nodeU := 1, nodeV := 2, conductanceMwPerK := c.p1 } ]
    0 ≤ c.p0 ∧ 0 ≤ c.p1 ∧ 0 ≤ Obend.Hardware.ThermalPassivity.evalLaplacianQuadratic [c.p2, c.p3, c.p4] edges
  | .analog2d =>
    chiralityBalanced2DMismatch c.p0 c.p1 c.p2 c.p3 c.p4 c.p5 10 10 = 0 ∧
      prouhetThueMorseMismatch1D c.p0 c.p1 c.p3 10 = 0
  | .dspBeamformer =>
    let sig : IqPhasor := ⟨c.p0, c.p1⟩
    let matched := iqConjMul sig sig
    matched.q = 0 ∧ matched.i = c.p0 * c.p0 + c.p1 * c.p1 ∧ 0 ≤ matched.i
  | .magnetics =>
    let tri := Obend.Hardware.Magnetics.statorToothRightTriangle2000x1500
    let e := Obend.Hardware.Magnetics.evalElementMagneticEnergyAreaScaled 1000000 tri c.p0 c.p1 c.p2
    let nuNext := Obend.Hardware.Magnetics.stepBhPicardReluctivity c.p3 c.p4 500 c.p3 c.p5
    0 ≤ e ∧ 0 < c.p3 ∧ c.p3 ≤ nuNext ∧ 0 < nuNext
def BinaryHwCertMeaning (expectedDom : HwCertDomain) (c : BinaryHwCert) : Prop :=
  c.domain = expectedDom ∧ BinaryHwCertDomainMeaning c
theorem verifyBinaryHwCert_iff (c : BinaryHwCert) :
    verifyBinaryHwCert c = true ↔ BinaryHwCertDomainMeaning c := by
  rcases c with ⟨dom, p0, p1, p2, p3, p4, p5⟩
  cases dom
  · rfl
  · rfl
  · simp [verifyBinaryHwCert, BinaryHwCertDomainMeaning, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]
  · rfl
  · unfold verifyBinaryHwCert BinaryHwCertDomainMeaning; dsimp only
    cases h1 : decodeTileOpKindBits p1.toNat <;> cases h2 : decodeRuleOpcodeBits p2.toNat
    · simp
    · simp
    · simp
    · rename_i opK rOp
      dsimp only
      cases h3 : decodeTileIcapWords (encodeTileIcapWords (mkIcapRuleTile p0.toNat opK rOp p3.toNat))
      · simp [h3]
      · simp [h3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  · simpa [verifyBinaryHwCert, BinaryHwCertDomainMeaning, checkAgenticEdaSwapBool] using
      (checkAgenticEdaSwapBool_iff p5 { baselineLdoPart with
        vohMinMv := p0.toNat, volMaxMv := p1.toNat, maxTempMc := p2.toNat,
        vswrMilli := p3.toNat, costCents := p4.toNat })
  · simp [verifyBinaryHwCert, BinaryHwCertDomainMeaning, decide_eq_true_eq]
  · simp [verifyBinaryHwCert, BinaryHwCertDomainMeaning, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  · simp [verifyBinaryHwCert, BinaryHwCertDomainMeaning, decide_eq_true_eq, beq_iff_eq]
  · simp [verifyBinaryHwCert, BinaryHwCertDomainMeaning, decide_eq_true_eq]
def checkBinaryCborJudge (_grade : Nat) (expectedDom : HwCertDomain) (cert : BinaryHwCert) : Verdict HwClause :=
  if (cert.domain == expectedDom) && verifyBinaryHwCert cert then .ok
  else .refused (.binaryCborCertViolation cert.domain.toCode) []
theorem checkBinaryCborJudge_ok_iff (r : Nat) (expectedDom : HwCertDomain) (c : BinaryHwCert) :
    checkBinaryCborJudge r expectedDom c = .ok ↔ BinaryHwCertMeaning expectedDom c := by
  unfold checkBinaryCborJudge BinaryHwCertMeaning
  by_cases hOk : ((c.domain == expectedDom) && verifyBinaryHwCert c) = true
  · simp only [hOk, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq, verifyBinaryHwCert_iff] at hOk
    exact ⟨fun _ => hOk, fun _ => trivial⟩
  · simp only [hOk, ↓reduceIte, reduceCtorEq, false_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, verifyBinaryHwCert_iff] at hOk
    exact hOk
/-- A wire domain code selects the specification that the certificate must satisfy. -/
def BinaryCborCodeMeaning (domCode : Nat) (c : BinaryHwCert) : Prop :=
  HwCertDomain.fromCode domCode = some c.domain ∧ BinaryHwCertDomainMeaning c

def checkBinaryCborCodeJudge (_grade domCode : Nat) (cert : BinaryHwCert) : Verdict HwClause :=
  match HwCertDomain.fromCode domCode with
  | none => .refused (.binaryCborCertViolation domCode) []
  | some dom => checkBinaryCborJudge 0 dom cert

theorem checkBinaryCborCodeJudge_ok_iff (r domCode : Nat) (c : BinaryHwCert) :
    checkBinaryCborCodeJudge r domCode c = .ok ↔ BinaryCborCodeMeaning domCode c := by
  cases hd : HwCertDomain.fromCode domCode <;>
    simp [checkBinaryCborCodeJudge, BinaryCborCodeMeaning, hd, checkBinaryCborJudge_ok_iff,
      BinaryHwCertMeaning, eq_comm]

instance binaryCborJudge : Obend.Judge Nat BinaryHwCert where
  Clause := HwClause
  Meaning := BinaryCborCodeMeaning
  check := checkBinaryCborCodeJudge
  sound := fun {r o c} => (checkBinaryCborCodeJudge_ok_iff r o c).mp
  refutes | .binaryCborCertViolation d => (HwCertDomain.fromCode d).isNone | _ => false
  refuted := by
    intro r code c k path h hk c' hm
    obtain ⟨hd, _⟩ := hm
    simp only [checkBinaryCborCodeJudge, hd, checkBinaryCborJudge] at h
    split at h
    · cases h
    · cases h
      simp [HwCertDomain.fromCode_toCode] at hk
  Fragment _ := True
  complete := by intro o _ ⟨c, hc⟩; exact ⟨c, 0, (checkBinaryCborCodeJudge_ok_iff 0 o c).mpr hc⟩
  mono := by intro _ _ _ _ _ _; rfl

theorem unregisteredBinaryCborCode_refused (c : BinaryHwCert) :
    checkBinaryCborCodeJudge 0 99 c = .refused (.binaryCborCertViolation 99) [] ∧
    binaryCborJudge.refutes (.binaryCborCertViolation 99) = true := ⟨rfl, rfl⟩

#tooth unregisteredBinaryCborCode_refused by mutation checkBinaryCborCodeJudge := fun _ _ _ => .ok

def badBinaryPnrCert : BinaryHwCert := { adder2nsPnrCert with p5 := 100 }
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badBinaryCborCert_refused :
    checkBinaryCborJudge 0 .pnr badBinaryPnrCert =
      .refused (.binaryCborCertViolation 1) [] := by decide +kernel
def hexCharVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none
def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest =>
    match hexCharVal hi, hexCharVal lo, decodeHexChars rest with
    | some h, some l, some tail => some (UInt8.ofNat (h * 16 + l) :: tail)
    | _, _, _ => none
  | [_] => none
def encodeHexBytes (bytes : List UInt8) : String :=
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList (bytes.flatMap fun b =>
    let n := b.toNat
    [hexDigits.getD (n / 16) '0', hexDigits.getD (n % 16) '0'])
def decodeBinaryCborDomainCode (s : String) : Except String Nat :=
  match s.trimAscii.toString.toNat? <|> extractNatField s "domainId" with
  | some n => .ok n
  | none => .error s!"missing required binary CBOR domain id in '{s}'"

def decodeBinaryCborObj (s : String) : Except String HwCertDomain :=
  match s.trimAscii.toString.toNat? with
  | some n =>
    match HwCertDomain.fromCode n with
    | some d => .ok d
    | none => .error s!"unknown binary CBOR domain id: {n}"
  | none =>
    match extractNatField s "domainId" with
    | some n =>
      match HwCertDomain.fromCode n with
      | some d => .ok d
      | none => .error s!"unknown binary CBOR domain id: {n}"
    | none => .error s!"missing required binary CBOR domain id in '{s}'"
def decodeBinaryCborCert (s : String) : Except String BinaryHwCert := do
  let trimmed := s.trimAscii.toString
  match decodeHexChars trimmed.toList with
  | some rawBytes =>
    match decodeBinaryHwCert rawBytes with
    | some cert => .ok cert
    | none => .error "invalid RFC 8949 CBOR BinaryHwCert frame"
  | none => .error "invalid hex-encoded CBOR byte stream"
/-- Declarative specification for variable-length RFC 8949 CBOR tape/mesh certificates:
restricted strictly to `.magnetics` and `.multiphysics` domains with ≥4 positive mesh words summing
to `metric0` and bounded peak metric `metric1 ≤ 5_000_000`. -/
def BinaryTapeCertMeaning (expectedDom : HwCertDomain) (c : BinaryTapeCert) : Prop :=
  c.domain = expectedDom ∧ (expectedDom = .magnetics ∨ expectedDom = .multiphysics) ∧
  4 ≤ c.words.length ∧ 0 < c.metric0.toNat ∧ 0 < c.metric1.toNat ∧ c.metric1.toNat ≤ 5000000 ∧
  (∀ w ∈ c.words, 0 < w.toNat) ∧ c.words.foldl (fun acc w => acc + w.toNat) 0 = c.metric0.toNat
def checkBinaryTapeCert (_grade : Nat) (expectedDom : HwCertDomain) (cert : BinaryTapeCert) : Verdict HwClause :=
  if expectedDom != .magnetics && expectedDom != .multiphysics then
    .refused (.binaryCborCertViolation expectedDom.toCode) []
  else if (cert.domain == expectedDom) && verifyBinaryTapeCert cert then .ok
  else .refused (.binaryCborCertViolation expectedDom.toCode) []
theorem verifyBinaryTapeCert_iff (c : BinaryTapeCert) :
    verifyBinaryTapeCert c = true ↔
      (c.domain = .magnetics ∨ c.domain = .multiphysics) ∧
      4 ≤ c.words.length ∧ 0 < c.metric0.toNat ∧ 0 < c.metric1.toNat ∧ c.metric1.toNat ≤ 5000000 ∧
      (∀ w ∈ c.words, 0 < w.toNat) ∧ c.words.foldl (fun acc w => acc + w.toNat) 0 = c.metric0.toNat := by
  unfold verifyBinaryTapeCert
  rcases c with ⟨dom, m0, m1, ws⟩
  cases dom <;>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true, Bool.and_false, Bool.false_eq_true, reduceCtorEq, or_self,
      true_or, or_true, true_and, false_and]
  · constructor
    · rintro ⟨⟨⟨⟨_, hm0⟩, hm1⟩, hws⟩, ⟨hlen, hm1b⟩, hsum⟩
      exact ⟨hlen, hm0, hm1, hm1b, hws, hsum⟩
    · rintro ⟨hlen, hm0, hm1, hm1b, hws, hsum⟩
      have hne : ws ≠ [] := by intro h; subst h; simp at hlen
      exact ⟨⟨⟨⟨hne, hm0⟩, hm1⟩, hws⟩, ⟨hlen, hm1b⟩, hsum⟩
  · constructor
    · rintro ⟨⟨⟨⟨_, hm0⟩, hm1⟩, hws⟩, ⟨hlen, hm1b⟩, hsum⟩
      exact ⟨hlen, hm0, hm1, hm1b, hws, hsum⟩
    · rintro ⟨hlen, hm0, hm1, hm1b, hws, hsum⟩
      have hne : ws ≠ [] := by intro h; subst h; simp at hlen
      exact ⟨⟨⟨⟨hne, hm0⟩, hm1⟩, hws⟩, ⟨hlen, hm1b⟩, hsum⟩
theorem checkBinaryTapeCert_sound {grade : Nat} {expectedDom : HwCertDomain} {cert : BinaryTapeCert}
    (h : checkBinaryTapeCert grade expectedDom cert = .ok) :
    BinaryTapeCertMeaning expectedDom cert := by
  unfold checkBinaryTapeCert at h
  split at h
  · cases h
  · split at h
    · rename_i _ hOk
      simp only [Bool.and_eq_true, beq_iff_eq, verifyBinaryTapeCert_iff] at hOk
      obtain ⟨hDomEq, hDomOr, hRest⟩ := hOk
      exact ⟨hDomEq, hDomEq ▸ hDomOr, hRest⟩
    · cases h
theorem checkBinaryTapeCert_ok_iff (r : Nat) (expectedDom : HwCertDomain) (c : BinaryTapeCert) :
    checkBinaryTapeCert r expectedDom c = .ok ↔ BinaryTapeCertMeaning expectedDom c := by
  refine ⟨checkBinaryTapeCert_sound, fun hm => ?_⟩
  rcases hm with ⟨hEq, hOr, hRest⟩
  have hDomOk : (expectedDom != .magnetics && expectedDom != .multiphysics) = false := by
    rcases hOr with rfl | rfl <;> rfl
  have hVer : verifyBinaryTapeCert c = true :=
    (verifyBinaryTapeCert_iff c).mpr ⟨hEq ▸ hOr, hRest⟩
  simp [checkBinaryTapeCert, hDomOk, hEq, hVer]
instance binaryTapeJudge : Obend.Judge HwCertDomain BinaryTapeCert where
  Clause := HwClause
  Meaning := BinaryTapeCertMeaning
  check := checkBinaryTapeCert
  sound := by intro _ _ _ h; exact checkBinaryTapeCert_sound h
  refutes | .binaryCborCertViolation d => d != 7 && d != 10 | _ => false
  refuted := by
    intro r o c k cs hc hk c' hm
    have hCode : k = .binaryCborCertViolation o.toCode := by
      unfold checkBinaryTapeCert at hc
      split at hc
      · cases hc; rfl
      · split at hc
        · cases hc
        · cases hc; rfl
    subst hCode
    rcases hm.2.1 with rfl | rfl <;> simp [HwCertDomain.toCode] at hk
  Fragment _ := True
  complete := by intro o _ ⟨c, hc⟩; exact ⟨c, 0, (checkBinaryTapeCert_ok_iff 0 o c).mpr hc⟩
  mono := by intro _ _ _ _ _ _; rfl
def badBinaryTapeCert : BinaryTapeCert := { statorMesh6WordTapeCert with metric0 := 999 }
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badBinaryTapeCert_refused :
    checkBinaryTapeCert 0 .magnetics badBinaryTapeCert =
      .refused (.binaryCborCertViolation 10) [] := by decide +kernel
def decodeBinaryTapeCertHex (s : String) : Except String BinaryTapeCert := do
  let trimmed := s.trimAscii.toString
  match decodeHexChars trimmed.toList with
  | some rawBytes =>
    match decodeBinaryTapeCert rawBytes with
    | some cert => .ok cert
    | none => .error "invalid RFC 8949 CBOR BinaryTapeCert frame"
  | none => .error "invalid hex-encoded CBOR byte stream"
def binaryTapeFormat : Format where
  name := "hw-binary-tape-cbor"; version := "1"; Obj := HwCertDomain; Cert := BinaryTapeCert
  judge := binaryTapeJudge; decodeObj := decodeBinaryCborObj; decodeCert := decodeBinaryTapeCertHex
  trust := .kernel; regime := .decidable
  bad := (.magnetics, badBinaryTapeCert); badGrade := 0
  bad_refused := ⟨_, _, badBinaryTapeCert_refused⟩
theorem binaryTapeFormat_sound {r : Nat} {obj cert : String}
    (h : binaryTapeFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeBinaryCborObj obj = .ok o ∧ decodeBinaryTapeCertHex cert = .ok c ∧
      BinaryTapeCertMeaning o c :=
  binaryTapeFormat.checkBytes_sound h
def verifyRawBinaryCborCert (expectedDom : HwCertDomain) (raw : ByteArray) : Verdict HwClause :=
  match decodeFromByteArray (α := BinaryHwCert) raw with
  | some cert => checkBinaryCborJudge 0 expectedDom cert
  | none =>
    match decodeFromByteArray (α := BinaryTapeCert) raw with
    | some tapeCert => checkBinaryTapeCert 0 expectedDom tapeCert
    | none => .refused (.binaryCborCertViolation expectedDom.toCode) []
def binaryCborFormat : Format where
  name := "hw-binary-cbor"; version := "1"; Obj := Nat; Cert := BinaryHwCert
  judge := binaryCborJudge; decodeObj := decodeBinaryCborDomainCode; decodeCert := decodeBinaryCborCert
  trust := .kernel; regime := .decidable
  bad := (1, badBinaryPnrCert); badGrade := 0
  bad_refused := ⟨_, _, badBinaryCborCert_refused⟩
theorem binaryCborFormat_sound {r : Nat} {obj cert : String}
    (h : binaryCborFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeBinaryCborDomainCode obj = .ok o ∧ decodeBinaryCborCert cert = .ok c ∧
      BinaryCborCodeMeaning o c :=
  binaryCborFormat.checkBytes_sound h
def hardwareFormats : List Format :=
  [ hwSynthFormat, rtlSynthFormat, hwRetimeFormat, hwPnrFormat
  , datasheetFitFormat, agenticEdaFormat, binaryCborFormat, binaryTapeFormat ]
def findHardwareFormat? (tag : String) : Option Format :=
  hardwareFormats.find? (fun f => s!"{f.name}@{f.version}" == tag)
theorem verifyRawBinaryCborCert_refuses_pnr_tape_bypass :
    let fakePnrTape : BinaryTapeCert := { domain := .pnr, metric0 := 100, metric1 := 100, words := [1] }
    let rawBytes := ByteArray.mk (encodeBinaryTapeCert fakePnrTape).toArray
    verifyRawBinaryCborCert .pnr rawBytes = .refused (.binaryCborCertViolation 1) [] := by
  decide +kernel
private theorem checkPnrJudge_grade_irrel (g o : Nat) (c : PnrCertificate) :
    checkPnrJudge g o c = checkPnrJudge 0 o c := rfl
private theorem checkAgenticEdaJudge_grade_irrel (g : Nat) (o : Int) (c : EdaVaultPart) :
    checkAgenticEdaJudge g o c = checkAgenticEdaJudge 0 o c := rfl
/-- **Kernel Verification of Numeric Wire Field Extraction (`extractNatField_and_extractIntField_verified`)**:
universally quantified over judge `grade : Nat` (`{grade : Nat}` so downstream callers specialize cleanly). -/
theorem extractNatField_and_extractIntField_verified {grade : Nat} :
    extractNatField "{\"mode\": \"golden\", \"costCents\": 320}" "costCents" = some 320 ∧
    extractIntField "{\"mode\": \"golden\", \"minMarginMv\": -150}" "minMarginMv" = some (-150) ∧
    extractNatField "cell1TileY=0,sinkCapFf=5" "cell1TileY" = some 0 ∧
    (let pnr : PnrCertificate :=
       { validAdderPnrCert with
         placedCells :=
           [ { cellId := 0, tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6 }
           , { cellId := 1, tileX := 0,
               tileY := (extractNatField "{\"cell1TileY\": 0}" "cell1TileY").getD 1,
               belSlot := 0, lutInit := 0x6 } ] }
     checkPnrJudge grade 2000 pnr = .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") []) ∧
    (let cand : EdaVaultPart :=
       { baselineLdoPart with
         costCents := (extractNatField "{\"costCents\": 320}" "costCents").getD 120 }
     checkAgenticEdaJudge grade 400 cand = .refused (.agenticEdaSwapViolation "U4_LDO") []) := by
  simp only [checkPnrJudge_grade_irrel, checkAgenticEdaJudge_grade_irrel]
  decide +kernel
/-- **Identifier-Boundary Non-Collision & Strict Decoder Verification (`extractNatField_token_boundary_and_decoders_verified`)**:
universally quantified over `grade : Nat`. -/
theorem extractNatField_token_boundary_and_decoders_verified (grade : Nat) :
    extractNatField "{\"max_fanout\": 99, \"mode\": \"calibrated\"}" "fanout" = none ∧
    extractNatField "max_fanout=99,mode=calibrated" "fanout" = none ∧
    extractIntField "{\"extra_minMarginMv\": -500}" "minMarginMv" = none ∧
    (decodeDatasheetFitCert "mode=calibrated").isOk = false ∧
    (decodeAgenticEdaCert "mode=golden").isOk = false ∧
    (decodeRtlSynthCert "{\"module\": \"m\"}").isOk = false ∧
    (decodePnrCert "{\"mode\": \"valid\"}").isOk = false ∧
    (match decodePnrCert "designName=obend_routed_adder2,sinkCapFf=5,cell1TileY=0,cell0BelSlot=0,cell1BelSlot=0,net0DstWire=12,net1DstWire=21" with
     | .ok c => c.sinkCapFf == 5 &&
       checkPnrJudge grade 2000 c == .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") []
     | .error _ => false) = true := by
  simp only [checkPnrJudge_grade_irrel]
  decide +kernel
end Obend.Hardware.Judge
