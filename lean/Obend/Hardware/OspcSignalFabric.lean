module
/-
# Obend.Hardware.OspcSignalFabric — Clock-Domain-Indexed `RtlSignal`, FABulous/ECP5 Fabric Refinement & `obend-hw-dpi`

Provides the verified hardware signal, bitstream-readback, and isolated DPI transport foundation for the
4-tile OSPC hardware prover (`Obend.Hardware.OspcProver`):

1. **Clock-Domain-Indexed Synchronous Streams (`ClockDomain`, `RtlSignal dom w iv`)**:
   - Statically tags every synchronous bitvector stream with its clock domain (`proverCore`, `hostDpi`,
     `fabricCfg`) and cycle-0 reset value `iv` (`atCycle 0 = iv`).
   - Domain-locked combinational and register combinators (`RtlSignal.const`, `RtlSignal.comb1`,
     `RtlSignal.comb2`, `RtlSignal.mux`, `RtlSignal.reg`, `RtlSignal.regRst`) make cross-domain
     combining ill-typed without an explicit 2-flip-flop synchronizer `cdcSync2FF`.
   - Generic multi-cycle lifting from `HDL.RtlModule`, `HDL.RtlMemModule`, and `Synth.BelNetlist`
     (`moduleRegSignal`, `moduleOutSignal`, `memModule_datapath_signal_and_bel_equiv`).
2. **`FABulous` / ECP5 Bitstream Encoder, Kernel-Checked Decoder/Extractor & Multi-Cycle `Net` Refinement**:
   - `encodeFabulousFrames`: canonical `bit_gen`-compatible binary bitstream encoder (20-byte
     `0xFAB0FAB1` sync header, column/frame-select words `(x <<< 27) ||| (1 <<< f)`, interior tile
     frame words, and desync word with bit 20 set).
   - `decodeFabulousFrames` + `extractFabulousNet`: total, 100% kernel-reducible implementation of the
     `FABulous` binary bitstream decoder and LUT4/FF switch-matrix extractor (`0 partial`,
     `0 native_decide`, `0 sorry`), paired with `ospcFabulousFabric` (`Obend.Hardware.Fabulous.Fabric`)
     and `Obend.Hardware.Fabulous.decodeBin` header/length refusal proofs.
   - End-to-end multi-cycle `StepRealizes` / `ResetRealizes` / `fabric_realizes_module` refinement
     of `ospcExtractedNet` to `ospcFabricSliceRtl`, ECP5 `lut4cModule` cell equivalence, and explicit
     tamper refusals for corrupt sync, desync, frame-select, truncated length, pip-mux, and `I0mux` bits.
3. **Isolated `obend-hw-dpi` Binary Frame Protocol & Deterministic Cycle Server**:
   - Length-framed canonical big-endian `"ODPI"` v1 binary codec (`OspcDpiReq` = 90 bytes,
     `OspcDpiResp` = 87 bytes) mirrored byte-for-byte in pure Rust (`crates/obend-hw-dpi`).
   - Prefix-free encode/decode round-trip theorems (`decodeOspcDpiReq_encodeOspcDpiReq`,
     `decodeOspcDpiResp_encodeOspcDpiResp`), refusal theorems, and single- & multi-cycle DPI server
     refinement (`stepOspcDpiServer_refines_spec`, `runOspcDpiServerTrace_refines_spec`).
-/
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.Fabulous.Net
public import Obend.Hardware.Fabulous.Bitstream
public import Obend.Hardware.Fabulous.Tile
public import Obend.Hardware.Fabulous.Cell
import all Obend.Hardware.HDL
import all Obend.Hardware.Synth
import all Obend.Hardware.Fabulous.Net
import all Obend.Hardware.Fabulous.Bitstream
import all Obend.Hardware.Fabulous.Tile
import all Obend.Hardware.Fabulous.Cell

public section
namespace Obend.Hardware.OspcSignalFabric
open Obend.Hardware.HDL Obend.Hardware.Synth Obend.Hardware.Fabulous
open Std
set_option autoImplicit false

/-! ## 1. Clock-Domain-Indexed Synchronous Streams (`RtlSignal dom w iv`) & 2-FF CDC -/

/-- Clock domains for the OSPC 4-tile hardware prover and its host/configuration boundaries. -/
inductive ClockDomain where
  | proverCore
  | hostDpi
  | fabricCfg
  deriving DecidableEq, Repr

/-- Canonical 1-byte wire tag for `ClockDomain` (mirrored in `crates/obend-hw-dpi`). -/
def ClockDomain.toTag : ClockDomain → UInt8
  | .proverCore => 0x00
  | .hostDpi    => 0x01
  | .fabricCfg  => 0x02

/-- Canonical decoder for 1-byte `ClockDomain` wire tags. -/
def ClockDomain.ofTag? : UInt8 → Option ClockDomain
  | 0x00 => some .proverCore
  | 0x01 => some .hostDpi
  | 0x02 => some .fabricCfg
  | _    => none

theorem ClockDomain.ofTag?_toTag (d : ClockDomain) : ClockDomain.ofTag? d.toTag = some d := by
  cases d <;> rfl

theorem ClockDomain.toTag_injective {a b : ClockDomain} (h : a.toTag = b.toTag) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Map `ClockDomain` to `HDL.ClkDomain` for static RTL CDC checks. -/
def ClockDomain.toHdl : ClockDomain → ClkDomain
  | .proverCore => .coreClk
  | .hostDpi    => .axiIoClk
  | .fabricCfg  => .cfgJtagClk

/-- Clock-domain-indexed synchronous bitvector stream of width `w` with cycle-0 reset value `iv`.
Combinational combinators require identical `dom : ClockDomain`, preventing accidental cross-domain
mixing without an explicit `cdcSync2FF` synchronizer. -/
structure RtlSignal (dom : ClockDomain) (w : Nat) (iv : BitVec w) where
  atCycle    : Nat → BitVec w
  reset_zero : atCycle 0 = iv

namespace RtlSignal

/-- Constant signal in domain `dom` with initial and steady-state value `v`. -/
def const (dom : ClockDomain) {w : Nat} (v : BitVec w) : RtlSignal dom w v where
  atCycle    := fun _ => v
  reset_zero := rfl

/-- Domain-locked unary combinational map. -/
def comb1 {dom : ClockDomain} {w₁ w₂ : Nat} {iv₁ : BitVec w₁}
    (f : BitVec w₁ → BitVec w₂) (s : RtlSignal dom w₁ iv₁) :
    RtlSignal dom w₂ (f iv₁) where
  atCycle    := fun n => f (s.atCycle n)
  reset_zero := congrArg f s.reset_zero

/-- Domain-locked binary combinational map (operands must share `dom`). -/
def comb2 {dom : ClockDomain} {w₁ w₂ w₃ : Nat} {iv₁ : BitVec w₁} {iv₂ : BitVec w₂}
    (f : BitVec w₁ → BitVec w₂ → BitVec w₃)
    (s₁ : RtlSignal dom w₁ iv₁) (s₂ : RtlSignal dom w₂ iv₂) :
    RtlSignal dom w₃ (f iv₁ iv₂) where
  atCycle    := fun n => f (s₁.atCycle n) (s₂.atCycle n)
  reset_zero := by rw [s₁.reset_zero, s₂.reset_zero]

/-- Domain-locked 2:1 multiplexer driven by a 1-bit select signal. -/
def mux {dom : ClockDomain} {w : Nat} {ivc : BitVec 1} {ivt ivf : BitVec w}
    (sel : RtlSignal dom 1 ivc) (ifTrue : RtlSignal dom w ivt) (ifFalse : RtlSignal dom w ivf) :
    RtlSignal dom w (if ivc == 1#1 then ivt else ivf) where
  atCycle    := fun n => if sel.atCycle n == 1#1 then ifTrue.atCycle n else ifFalse.atCycle n
  reset_zero := by rw [sel.reset_zero, ifTrue.reset_zero, ifFalse.reset_zero]

/-- 1-cycle synchronous register in domain `dom` initializing to `iv` at cycle `0`. -/
def reg {dom : ClockDomain} {w : Nat} (iv : BitVec w) {ivD : BitVec w}
    (d : RtlSignal dom w ivD) : RtlSignal dom w iv where
  atCycle
    | 0     => iv
    | n + 1 => d.atCycle n
  reset_zero := rfl

/-- 1-cycle synchronous register with synchronous active-high reset `rst` in domain `dom`. -/
def regRst {dom : ClockDomain} {w : Nat} (iv : BitVec w) {ivR : BitVec 1} {ivD : BitVec w}
    (rst : RtlSignal dom 1 ivR) (d : RtlSignal dom w ivD) : RtlSignal dom w iv where
  atCycle
    | 0     => iv
    | n + 1 => if rst.atCycle n == 1#1 then iv else d.atCycle n
  reset_zero := rfl

theorem const_atCycle (dom : ClockDomain) {w : Nat} (v : BitVec w) (n : Nat) :
    (const dom v).atCycle n = v := by rfl

theorem comb2_atCycle {dom : ClockDomain} {w₁ w₂ w₃ : Nat} {iv₁ : BitVec w₁} {iv₂ : BitVec w₂}
    (f : BitVec w₁ → BitVec w₂ → BitVec w₃)
    (s₁ : RtlSignal dom w₁ iv₁) (s₂ : RtlSignal dom w₂ iv₂) (n : Nat) :
    (comb2 f s₁ s₂).atCycle n = f (s₁.atCycle n) (s₂.atCycle n) := by rfl

theorem reg_zero {dom : ClockDomain} {w : Nat} (iv : BitVec w) {ivD : BitVec w}
    (d : RtlSignal dom w ivD) : (reg iv d).atCycle 0 = iv := by rfl

theorem reg_succ {dom : ClockDomain} {w : Nat} (iv : BitVec w) {ivD : BitVec w}
    (d : RtlSignal dom w ivD) (n : Nat) : (reg iv d).atCycle (n + 1) = d.atCycle n := by rfl

end RtlSignal

/-- Explicit 2-flip-flop clock-domain crossing (CDC) synchronizer transferring a stream from
`src` into `dst` with two cycles of reset-initialized metastability-hardening latency. -/
def cdcSync2FF {src dst : ClockDomain} {w : Nat} {iv : BitVec w}
    (s : RtlSignal src w iv) : RtlSignal dst w iv where
  atCycle
    | 0     => iv
    | 1     => iv
    | n + 2 => s.atCycle n
  reset_zero := rfl

theorem cdcSync2FF_cycle0 {src dst : ClockDomain} {w : Nat} {iv : BitVec w}
    (s : RtlSignal src w iv) : (cdcSync2FF (dst := dst) s).atCycle 0 = iv := by rfl

theorem cdcSync2FF_cycle1 {src dst : ClockDomain} {w : Nat} {iv : BitVec w}
    (s : RtlSignal src w iv) : (cdcSync2FF (dst := dst) s).atCycle 1 = iv := by rfl

theorem cdcSync2FF_latency {src dst : ClockDomain} {w : Nat} {iv : BitVec w}
    (s : RtlSignal src w iv) (n : Nat) :
    (cdcSync2FF (dst := dst) s).atCycle (n + 2) = s.atCycle n := by rfl

theorem cdcSync2FF_const (src dst : ClockDomain) {w : Nat} (v : BitVec w) (n : Nat) :
    (cdcSync2FF (dst := dst) (RtlSignal.const src v)).atCycle n = v := by
  cases n with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem cdcSync2FF_preserves_comb2 {src dst : ClockDomain} {w₁ w₂ w₃ : Nat}
    {iv₁ : BitVec w₁} {iv₂ : BitVec w₂}
    (f : BitVec w₁ → BitVec w₂ → BitVec w₃)
    (s₁ : RtlSignal src w₁ iv₁) (s₂ : RtlSignal src w₂ iv₂) (n : Nat) :
    (cdcSync2FF (dst := dst) (RtlSignal.comb2 f s₁ s₂)).atCycle (n + 2) =
      (RtlSignal.comb2 f (cdcSync2FF (dst := dst) s₁) (cdcSync2FF (dst := dst) s₂)).atCycle (n + 2) := by
  rfl

/-! ## 2. Lifting `RtlModule`, `RtlMemModule` & `BelNetlist` to `RtlSignal .proverCore` -/

/-- Prefix `[stim 0, stim 1, ..., stim (n - 1)]` of an infinite cycle stimulus stream. -/
def stimPrefix (stim : Nat → Bool × (Nat → BitVec 64)) : Nat → List (Bool × (Nat → BitVec 64))
  | 0     => []
  | n + 1 => stimPrefix stim n ++ [stim n]

theorem stimPrefix_length (stim : Nat → Bool × (Nat → BitVec 64)) :
    ∀ n : Nat, (stimPrefix stim n).length = n
  | 0     => rfl
  | n + 1 => by simp [stimPrefix, stimPrefix_length stim n]

theorem runModuleTrace_stimPrefix_succ (m : RtlModule) (regs₀ : Nat → BitVec 64)
    (stim : Nat → Bool × (Nat → BitVec 64)) (n : Nat) :
    runModuleTrace m regs₀ (stimPrefix stim (n + 1)) =
      stepModuleRegs m (stim n).1 (stim n).2 (runModuleTrace m regs₀ (stimPrefix stim n)) := by
  unfold runModuleTrace
  simp [stimPrefix, List.foldl_append]

theorem runMemModuleTrace_stimPrefix_succ (m : RtlMemModule) (st₀ : MemState)
    (stim : Nat → Bool × (Nat → BitVec 64)) (n : Nat) :
    runMemModuleTrace m st₀ (stimPrefix stim (n + 1)) =
      stepMemModule m (stim n).1 (stim n).2 (runMemModuleTrace m st₀ (stimPrefix stim n)) := by
  unfold runMemModuleTrace
  simp [stimPrefix, List.foldl_append]

/-- Lift register `regIdx` of `m : RtlModule` under `stim` to a clock-domain-indexed `RtlSignal .proverCore`. -/
def moduleRegSignal (m : RtlModule) (regs₀ : Nat → BitVec 64)
    (stim : Nat → Bool × (Nat → BitVec 64)) (regIdx : Nat) :
    RtlSignal .proverCore 64 (regs₀ regIdx) where
  atCycle    := fun n => runModuleTrace m regs₀ (stimPrefix stim n) regIdx
  reset_zero := rfl

/-- Lift output port `outIdx` of `m : RtlModule` under `stim` to a clock-domain-indexed `RtlSignal .proverCore`. -/
def moduleOutSignal (m : RtlModule) (regs₀ : Nat → BitVec 64)
    (stim : Nat → Bool × (Nat → BitVec 64)) (outIdx : Nat) :
    RtlSignal .proverCore 64 ((evalModuleOutputs m (stim 0).2 regs₀).getD outIdx ("", 0#64)).2 where
  atCycle    := fun n => ((evalModuleOutputs m (stim n).2 (runModuleTrace m regs₀ (stimPrefix stim n))).getD outIdx ("", 0#64)).2
  reset_zero := rfl

theorem moduleRegSignal_atCycle_eq_runModuleTrace (m : RtlModule) (regs₀ : Nat → BitVec 64)
    (stim : Nat → Bool × (Nat → BitVec 64)) (regIdx n : Nat) :
    (moduleRegSignal m regs₀ stim regIdx).atCycle n =
      runModuleTrace m regs₀ (stimPrefix stim n) regIdx := by rfl

theorem moduleRegSignal_step (m : RtlModule) (regs₀ : Nat → BitVec 64)
    (stim : Nat → Bool × (Nat → BitVec 64)) (regIdx n : Nat) :
    (moduleRegSignal m regs₀ stim regIdx).atCycle (n + 1) =
      stepModuleRegs m (stim n).1 (stim n).2 (fun i => (moduleRegSignal m regs₀ stim i).atCycle n) regIdx := by
  change runModuleTrace m regs₀ (stimPrefix stim (n + 1)) regIdx = _
  rw [runModuleTrace_stimPrefix_succ]
  rfl

/-- Lift a `RtlMemModule` stimulus stream into the port stimulus stream of its datapath `RtlModule`. -/
def liftMemStim (dpInputs : (Nat → BitVec 64) → MemState → Nat → BitVec 64)
    (mMem : RtlMemModule) (st₀ : MemState) (stim : Nat → Bool × (Nat → BitVec 64)) :
    Nat → Bool × (Nat → BitVec 64) :=
  fun n =>
    let stN := runMemModuleTrace mMem st₀ (stimPrefix stim n)
    ((stim n).1, dpInputs (stim n).2 stN)

/-- Universal multi-cycle equivalence between a `RtlMemModule`, its datapath `RtlModule` lifted to
`RtlSignal .proverCore`, and its synthesized `BelNetlist` (`synthesizeModuleToBels`). -/
theorem memModule_datapath_signal_and_bel_equiv
    (mMem : RtlMemModule) (mDp : RtlModule)
    (dpInputs : (Nat → BitVec 64) → MemState → Nat → BitVec 64)
    (hWf : checkRtlModule mDp = true)
    (hStep : ∀ rst ins st,
      stepModuleRegs mDp rst (dpInputs ins st) st.regs = (stepMemModule mMem rst ins st).regs)
    (st₀ : MemState) (stim : Nat → Bool × (Nat → BitVec 64)) (n : Nat) :
    let dpStim := liftMemStim dpInputs mMem st₀ stim
    (∀ regIdx : Nat,
      (moduleRegSignal mDp st₀.regs dpStim regIdx).atCycle n =
        (runMemModuleTrace mMem st₀ (stimPrefix stim n)).regs regIdx) ∧
    runBelNetlistTrace (synthesizeModuleToBels mDp) st₀.regs (stimPrefix dpStim n) =
      runRtlModuleTrace mDp st₀.regs (stimPrefix dpStim n) ∧
    checkSynthesizedRtlSignoff mDp = true ∧
    countFfBels (synthesizeModuleToBels mDp) = mDp.regs.length := by
  intro dpStim
  have hRegs : ∀ k : Nat,
      runModuleTrace mDp st₀.regs (stimPrefix dpStim k) =
        (runMemModuleTrace mMem st₀ (stimPrefix stim k)).regs := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih =>
      rw [runModuleTrace_stimPrefix_succ, runMemModuleTrace_stimPrefix_succ, ih]
      exact hStep (stim j).1 (stim j).2 (runMemModuleTrace mMem st₀ (stimPrefix stim j))
  refine ⟨fun regIdx => congrFun (hRegs n) regIdx,
    synthesizeModuleToBels_trace_equiv mDp hWf st₀.regs (stimPrefix dpStim n),
    checkSynthesizedRtlSignoff_complete mDp hWf,
    (synthesizeModuleToBels_valid_and_ff_count mDp).2⟩

/-! ## 3. `FABulous` / ECP5 Bitstream Encoder, Kernel-Checked Decoder/Extractor & OSPC Slice Refinement -/

/-- Big-endian 4-byte list representation of a 32-bit unsigned word. -/
private def fabBe32List (w : Nat) : List UInt8 :=
  [ UInt8.ofNat ((w >>> 24) &&& 0xFF), UInt8.ofNat ((w >>> 16) &&& 0xFF)
  , UInt8.ofNat ((w >>> 8) &&& 0xFF),  UInt8.ofNat (w &&& 0xFF) ]

private def fabReadBe32 : List UInt8 → Option (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
    some (b0.toNat * 2^24 + b1.toNat * 2^16 + b2.toNat * 2^8 + b3.toNat, rest)
  | _ => none

/-- Encode a `cols × rows` FABulous binary bitstream matching `Obend.Hardware.Fabulous.decodeBin`:
20-byte `0xFAB0FAB1` sync header, column/frame-select words `(x <<< 27) ||| (1 <<< f)`,
interior tile frame words (`y = rows - 2` down to `1`), and trailing desync word (bit 20 set). -/
def encodeFabulousFramesList (cols rows : Nat) (tileCfg : Nat → Nat → Nat)
    (desyncWord : Nat := 1 <<< 20) : List UInt8 :=
  let interior := rows - 2
  let colBytes (x : Nat) : List UInt8 :=
    (List.range 20).flatMap fun f =>
      fabBe32List ((x <<< 27) ||| (1 <<< f)) ++
      (List.range interior).flatMap fun r =>
        let y := rows - 2 - r
        fabBe32List ((tileCfg x y >>> (32 * f)) &&& 0xFFFFFFFF)
  syncHeader ++ (List.range cols).flatMap colBytes ++ fabBe32List desyncWord

/-- `ByteArray` form of `encodeFabulousFramesList` for `Obend.Hardware.Fabulous.decodeBin`. -/
def encodeFabulousFrames (cols rows : Nat) (tileCfg : Nat → Nat → Nat)
    (desyncWord : Nat := 1 <<< 20) : ByteArray :=
  ByteArray.mk (encodeFabulousFramesList cols rows tileCfg desyncWord).toArray

/-- Pure structured-key fabric descriptor (zero `String.toList` / `String.splitOn` / `@[extern] String.hash`
in Lean's kernel) that compiles directly to `Obend.Hardware.Fabulous.Fabric` via `toFabric`. -/
structure KernelFabric where
  /-- `(tile, feature)` ↦ bit pattern -/
  spec : List ((String × String) × Pattern)
  /-- `(dstTile, dstWire)` ↦ incoming pips `(srcTile, srcWire, feature)` -/
  into : List ((String × String) × List (String × String × String))
  /-- `tile` ↦ BELs `(letter, type, prefix)` -/
  bels : List (String × List (String × String × String))
  cols : Nat
  rows : Nat

/-- Convert a `KernelFabric` into an `Obend.Hardware.Fabulous.Fabric` for `Obend.Hardware.Fabulous.extract`. -/
def KernelFabric.toFabric (kf : KernelFabric) : Fabric where
  spec := kf.spec.foldl (fun m ((t, f), v) => m.insert (t ++ "." ++ f) v) {}
  into := kf.into.foldl (fun m ((t, w), v) => m.insert (t ++ "." ++ w) v.toArray) {}
  bels := kf.bels.foldl (fun m (k, v) => m.insert k v.toArray) {}
  cols := kf.cols
  rows := kf.rows

/-- Pure association-list update ORing `val` into key `(x, y)` (mirrors `HashMap.insert` in `decodeBin`). -/
private def cfgOrInsertXY (x y val : Nat) : List ((Nat × Nat) × Nat) → List ((Nat × Nat) × Nat)
  | [] => [((x, y), val)]
  | ((x', y'), v') :: rest =>
    if x == x' && y == y' then ((x', y'), v' ||| val) :: rest
    else ((x', y'), v') :: cfgOrInsertXY x y val rest

private def decodeRowsLoop (x f rows interior : Nat) :
    Nat → List UInt8 → List ((Nat × Nat) × Nat) → Except String (List UInt8 × List ((Nat × Nat) × Nat))
  | 0, bs, cfg => .ok (bs, cfg)
  | rem + 1, bs, cfg =>
    match fabReadBe32 bs with
    | none => .error "unexpected EOF inside frame rows"
    | some (w, rest) =>
      let r := interior - (rem + 1)
      let y := rows - 2 - r
      let cfg' := if w == 0 then cfg else cfgOrInsertXY x y (w <<< (32 * f)) cfg
      decodeRowsLoop x f rows interior rem rest cfg'

private def decodeFramesLoop (x rows interior : Nat) :
    Nat → List UInt8 → List ((Nat × Nat) × Nat) → Except String (List UInt8 × List ((Nat × Nat) × Nat))
  | 0, bs, cfg => .ok (bs, cfg)
  | rem + 1, bs, cfg =>
    let f := 20 - (rem + 1)
    match fabReadBe32 bs with
    | none => .error "unexpected EOF at frame-select word"
    | some (sel, rest) =>
      if sel != ((x <<< 27) ||| (1 <<< f)) then
        .error s!"frame-select mismatch at col {x} frame {f}"
      else
        match decodeRowsLoop x f rows interior interior rest cfg with
        | .error e => .error e
        | .ok (rest', cfg') => decodeFramesLoop x rows interior rem rest' cfg'

private def decodeColsLoop (cols rows interior : Nat) :
    Nat → List UInt8 → List ((Nat × Nat) × Nat) → Except String (List UInt8 × List ((Nat × Nat) × Nat))
  | 0, bs, cfg => .ok (bs, cfg)
  | rem + 1, bs, cfg =>
    let x := cols - (rem + 1)
    match decodeFramesLoop x rows interior 20 bs cfg with
    | .error e => .error e
    | .ok (rest', cfg') => decodeColsLoop cols rows interior rem rest' cfg'

private def checkPrefixBytes : List UInt8 → List UInt8 → Option (List UInt8)
  | [], bs => some bs
  | p :: ps, b :: bs => if p == b then checkPrefixBytes ps bs else none
  | _ :: _, [] => none

/-- Pure kernel-reducible mirror of `Obend.Hardware.Fabulous.decodeBin` (exact same 20-byte
`syncHeader`, 20 frames/col, `(x <<< 27) ||| (1 <<< f)` frame-select verification, interior row
words `y = rows - 2 - r`, and desync bit-20 verification, with tail-recursive list loops so every
decode and refusal reduces cleanly in the Lean kernel under default `maxRecDepth`). -/
private def fabTileName : Nat → Nat → String
  | 0, 0 => "X0Y0"
  | 0, 1 => "X0Y1"
  | 0, 2 => "X0Y2"
  | 1, 0 => "X1Y0"
  | 1, 1 => "X1Y1"
  | 1, 2 => "X1Y2"
  | x, y => s!"X{x}Y{y}"

def decodeFabulousFrames (cols rows : Nat) (b : ByteArray) : Except String (List (String × Nat)) :=
  let interior := rows - 2
  let expected := 20 + cols * 20 * (4 + 4 * interior) + 4
  if b.size != expected then
    .error s!"bitstream is {b.size} bytes; expected {expected}"
  else
    match checkPrefixBytes syncHeader b.data.toList with
    | none => .error "bitstream does not open with the FABulous sync header"
    | some body =>
      match decodeColsLoop cols rows interior cols body [] with
      | .error e => .error e
      | .ok (tail, cfgXY) =>
        match fabReadBe32 tail with
        | none => .error "missing desync word"
        | some (desync, rem) =>
          if !rem.isEmpty then .error "trailing bytes after desync word"
          else if desync &&& (1 <<< 20) == 0 then .error "bitstream does not end with the desync word"
          else .ok (cfgXY.map fun ((x, y), v) => (fabTileName x y, v))

private def featOnKernel (fab : KernelFabric) (cfg : List (String × Nat)) (tile feat : String) :
    Except String Bool :=
  match fab.spec.lookup (tile, feat) with
  | none => .error "feature not in bitStreamSpec"
  | some pat =>
    let bits := (cfg.lookup tile).getD 0
    .ok (pat.all fun (p, v) => bits.testBit p == v)

private def driverKernel (fab : KernelFabric) (cfg : List (String × Nat)) (t w : String) :
    Except String (Option (String × String)) :=
  match fab.into.lookup (t, w) with
  | none => .ok none
  | some pips =>
    match pips with
    | [(st, sw, feat)] =>
      match fab.spec.lookup (st, feat) with
      | some [] => .ok (some (st, sw))
      | _ =>
        match featOnKernel fab cfg st feat with
        | .error e => .error e
        | .ok true => .ok (some (st, sw))
        | .ok false => .error "mux select matches no input"
    | _ =>
      let rec go (hit : Option (String × String)) :
          List (String × String × String) → Except String (Option (String × String))
        | [] =>
          match hit with
          | some h => .ok (some h)
          | none   => .error "mux select matches no input"
        | (st, sw, feat) :: rest =>
          match featOnKernel fab cfg st feat with
          | .error e => .error e
          | .ok true =>
            if hit.isSome then .error "two pips selected"
            else go (some (st, sw)) rest
          | .ok false => go hit rest
      go none pips

private def lutInitFeat (l : String) : Nat → String
  | 0  => l ++ ".INIT"     | 1  => l ++ ".INIT[1]"  | 2  => l ++ ".INIT[2]"  | 3  => l ++ ".INIT[3]"
  | 4  => l ++ ".INIT[4]"  | 5  => l ++ ".INIT[5]"  | 6  => l ++ ".INIT[6]"  | 7  => l ++ ".INIT[7]"
  | 8  => l ++ ".INIT[8]"  | 9  => l ++ ".INIT[9]"  | 10 => l ++ ".INIT[10]" | 11 => l ++ ".INIT[11]"
  | 12 => l ++ ".INIT[12]" | 13 => l ++ ".INIT[13]" | 14 => l ++ ".INIT[14]" | _  => l ++ ".INIT[15]"

private def lutInputName : Nat → String
  | 0 => "I0" | 1 => "I1" | 2 => "I2" | _ => "I3"

private def belAtKernel (fab : KernelFabric) (t w : String) : Option (String × String × String) :=
  ((fab.bels.lookup t).getD []).find? fun (_, ty, pre) =>
    (ty == lutType && (w == pre ++ "O" || w == pre ++ "Co")) ||
    (ty == ioType && (w == pre ++ "O" || w == pre ++ "Q"))

private structure KernelExState where
  gates    : List Gate := []
  gateOf   : List ((String × String) × Nat) := []
  visiting : List (String × String) := []
  flops    : List (Option Flop) := []
  flopOf   : List ((String × String) × Nat) := []

private def listSetAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSetAt xs n v

private def readLutInitBits (fab : KernelFabric) (cfg : List (String × Nat)) (t l : String) :
    Nat → Nat → Except String Nat
  | 0, acc => .ok acc
  | rem + 1, acc =>
    let k := 16 - (rem + 1)
    let f := lutInitFeat l k
    match featOnKernel fab cfg t f with
    | .error e => .error e
    | .ok b => readLutInitBits fab cfg t l rem (if b then acc ||| (1 <<< k) else acc)

private def traceNodeKernel (fab : KernelFabric) (cfg : List (String × Nat)) (pm : List Pin) :
    Nat → String → String → KernelExState → Except String (Lit × KernelExState)
  | 0, _, _, _ => .error "routing/extraction fuel exhausted"
  | fuel + 1, t, w, s =>
    match driverKernel fab cfg t w with
    | .error e => .error e
    | .ok (some (st, sw)) => traceNodeKernel fab cfg pm fuel st sw s
    | .ok none =>
      if w == "GND0" || w == "GND" then .ok (.const false, s)
      else if w == "VCC0" || w == "VCC" then .ok (.const true, s)
      else match belAtKernel fab t w with
        | none => .error "no pip drives node and it is no BEL output"
        | some (l, ty, pre) =>
          if ty == lutType then
            if w == pre ++ "Co" then .error "carry chain (Co) is not modelled"
            else match featOnKernel fab cfg t (l ++ ".FF") with
              | .error e => .error e
              | .ok true =>
                match s.flopOf.lookup (t, l) with
                | some k => .ok (.ff k, s)
                | none =>
                  let k := s.flops.length
                  let s1 : KernelExState :=
                    { s with flops := s.flops ++ [none], flopOf := ((t, l), k) :: s.flopOf }
                  let buildGate : Except String (Lit × KernelExState) :=
                    match s1.gateOf.lookup (t, l) with
                    | some gk => .ok (.gate gk, s1)
                    | none =>
                      if s1.visiting.contains (t, l) then .error "combinational loop"
                      else match featOnKernel fab cfg t (l ++ ".I0mux") with
                        | .error e => .error e
                        | .ok true => .error "carry input (I0mux) is not modelled"
                        | .ok false =>
                          match readLutInitBits fab cfg t l 16 0 with
                          | .error e => .error e
                          | .ok init =>
                            let s2 : KernelExState := { s1 with visiting := (t, l) :: s1.visiting }
                            let stepPin (i : Nat) (st : KernelExState) : Except String (Lit × KernelExState) :=
                              if usesInput init i then traceNodeKernel fab cfg pm fuel t (pre ++ lutInputName i) st
                              else .ok (.const false, st)
                            match stepPin 0 s2 with
                            | .error e => .error e
                            | .ok (i0, sa) =>
                              match stepPin 1 sa with
                              | .error e => .error e
                              | .ok (i1, sb) =>
                                match stepPin 2 sb with
                                | .error e => .error e
                                | .ok (i2, sc) =>
                                  match stepPin 3 sc with
                                  | .error e => .error e
                                  | .ok (i3, sd) =>
                                    let g : Gate := { init := BitVec.ofNat 16 init, i0, i1, i2, i3, site := t ++ "." ++ l }
                                    let gk := sd.gates.length
                                    .ok (.gate gk, { sd with
                                      gates := sd.gates ++ [g]
                                      gateOf := ((t, l), gk) :: sd.gateOf
                                      visiting := sd.visiting.filter (· != (t, l)) })
                  match buildGate with
                  | .error e => .error e
                  | .ok (d, s3) =>
                    match traceNodeKernel fab cfg pm fuel t (pre ++ "EN") s3 with
                    | .error e => .error e
                    | .ok (en, s4) =>
                      match traceNodeKernel fab cfg pm fuel t (pre ++ "SR") s4 with
                      | .error e => .error e
                      | .ok (sr, s5) =>
                        match featOnKernel fab cfg t (l ++ ".SET_NORESET") with
                        | .error e => .error e
                        | .ok rv =>
                          let f : Flop := { d, en, sr, rv, site := t ++ "." ++ l }
                          .ok (.ff k, { s5 with flops := listSetAt s5.flops k (some f) })
              | .ok false =>
                match s.gateOf.lookup (t, l) with
                | some gk => .ok (.gate gk, s)
                | none =>
                  if s.visiting.contains (t, l) then .error "combinational loop"
                  else match featOnKernel fab cfg t (l ++ ".I0mux") with
                    | .error e => .error e
                    | .ok true => .error "carry input (I0mux) is not modelled"
                    | .ok false =>
                      match readLutInitBits fab cfg t l 16 0 with
                      | .error e => .error e
                      | .ok init =>
                        let s2 : KernelExState := { s with visiting := (t, l) :: s.visiting }
                        let stepPin (i : Nat) (st : KernelExState) : Except String (Lit × KernelExState) :=
                          if usesInput init i then traceNodeKernel fab cfg pm fuel t (pre ++ lutInputName i) st
                          else .ok (.const false, st)
                        match stepPin 0 s2 with
                        | .error e => .error e
                        | .ok (i0, sa) =>
                          match stepPin 1 sa with
                          | .error e => .error e
                          | .ok (i1, sb) =>
                            match stepPin 2 sb with
                            | .error e => .error e
                            | .ok (i2, sc) =>
                              match stepPin 3 sc with
                              | .error e => .error e
                              | .ok (i3, sd) =>
                                let g : Gate := { init := BitVec.ofNat 16 init, i0, i1, i2, i3, site := t ++ "." ++ l }
                                let gk := sd.gates.length
                                .ok (.gate gk, { sd with
                                  gates := sd.gates ++ [g]
                                  gateOf := ((t, l), gk) :: sd.gateOf
                                  visiting := sd.visiting.filter (· != (t, l)) })
          else if ty == ioType then
            if w == pre ++ "Q" then .error "IO registered output Q is not modelled"
            else match pm.findIdx? (fun p => p.tile == t && p.bel == l) with
              | some k =>
                match pm[k]? with
                | some ⟨_, _, .output _ _⟩ => .error "output pin read as input"
                | _ => .ok (.pin k, s)
              | none => .error "unmapped IO pin"
          else .error "BEL type not modelled"

private def extractPinsLoop (fab : KernelFabric) (cfg : List (String × Nat))
    (pm : List Pin) (fuel : Nat) :
    Nat → List Pin → List (Nat × Lit) → KernelExState → Except String (List (Nat × Lit) × KernelExState)
  | _, [], outs, s => .ok (outs, s)
  | k, p :: rest, outs, s =>
    match traceNodeKernel fab cfg pm fuel p.tile (p.bel ++ "_T") s with
    | .error e => .error e
    | .ok (tLit, s1) =>
      match p.role with
      | .output _ _ =>
        if tLit != .const false then .error "output pin T not tied low"
        else match traceNodeKernel fab cfg pm fuel p.tile (p.bel ++ "_I") s1 with
          | .error e => .error e
          | .ok (oLit, s2) => extractPinsLoop fab cfg pm fuel (k + 1) rest (outs ++ [(k, oLit)]) s2
      | _ =>
        if tLit != .const true then .error "input pin T not tied high"
        else extractPinsLoop fab cfg pm fuel (k + 1) rest outs s1

/-- Total kernel-reducible FABulous `Net` extractor over decoded configuration `cfg`. -/
def extractFabulousNet (fab : KernelFabric) (cfg : List (String × Nat)) (pm : List Pin)
    (fuel : Nat := 16) : Except String Net :=
  match extractPinsLoop fab cfg pm fuel 0 pm [] {} with
  | .error e => .error e
  | .ok (outs, s) =>
    match s.flops.mapM (fun | some f => Except.ok f | none => Except.error "unfilled flop") with
    | .error e => .error e
    | .ok flops => .ok { gates := s.gates, flops, outs }

/-- Compose `decodeFabulousFrames` and `extractFabulousNet` into a single total, kernel-reducible
bitstream-to-`Net` pipeline. -/
def decodeAndExtractFabulous (fab : KernelFabric) (pm : List Pin) (bin : ByteArray) :
    Except String Net := do
  let cfg ← decodeFabulousFrames fab.cols fab.rows bin
  extractFabulousNet fab cfg pm

/-! ### Concrete 2-BEL OSPC `FABulous` Fabric Slice (Tile 0 `FaceIdeal4` + Tile 2 `DeltaNet` `linear_ok`) -/

/-- `LUT4` truth table `0xCE8A`: 1-bit slice of Tile 0 `FaceIdeal4` update:
- `op_sel = 00`: hold `q` (`I0`)
- `op_sel = 01`: meet `q && in_bit` (`I0 && I1`)
- `op_sel = 10`: join `q || in_bit` (`I0 || I1`)
- `op_sel = 11`: load `in_bit` (`I1`). -/
def OSPC_FACE_LUT4_INIT : BitVec 16 := 0xCE8A#16

/-- `LUT4` truth table `0xA2A2`: Tile 2 `DeltaNet` sticky linearity guard `q && (!redex_en || lin_pair)`. -/
def OSPC_LIN_LUT4_INIT : BitVec 16 := 0xA2A2#16

theorem ospc_face_lut4_spec (q inBit op0 op1 : Bool) :
    lut4 OSPC_FACE_LUT4_INIT q inBit op0 op1 =
      if !op1 && !op0 then q
      else if !op1 && op0 then q && inBit
      else if op1 && !op0 then q || inBit
      else inBit := by
  cases q <;> cases inBit <;> cases op0 <;> cases op1 <;> decide

theorem ospc_lin_lut4_spec (q redexEn linPair unused : Bool) :
    lut4 OSPC_LIN_LUT4_INIT q redexEn linPair unused =
      (q && (if redexEn then linPair else true)) := by
  cases q <;> cases redexEn <;> cases linPair <;> cases unused <;> decide

/-- Reference `RtlModule` for the 2-BEL OSPC fabric slice (`face_bit` + `linear_ok`), matching
every bit lane of `tile0_exprcam_face4` and the `linear_ok` latch of `tile2_deltanet_redex`. -/
def ospcFabricSliceRtl : RtlModule :=
  { name := "obend_ospc_fabulous_slice"
  , inputNames := ["op_sel", "in_face_bit", "redex_en", "lin_pair"]
  , inputWidths := [2, 1, 1, 1]
  , wires :=
      [ ⟨0, "is_meet", .alu .eq (.inputPort 0) (.const 1#64), 1⟩
      , ⟨1, "is_join", .alu .eq (.inputPort 0) (.const 2#64), 1⟩
      , ⟨2, "is_load", .alu .eq (.inputPort 0) (.const 3#64), 1⟩
      , ⟨3, "next_face", .mux (.wireRef 0) (.alu .bitAnd (.regRead 0) (.inputPort 1))
          (.mux (.wireRef 1) (.alu .bitOr (.regRead 0) (.inputPort 1))
            (.mux (.wireRef 2) (.inputPort 1) (.regRead 0))), 1⟩
      , ⟨4, "next_lin", .alu .bitAnd (.regRead 1) (.mux (.inputPort 2) (.inputPort 3) (.const 1#64)), 1⟩ ]
  , regs :=
      [ ⟨0, "face_bit",  .coreClk, .syncReset 0#64, false, .wireRef 3, 1⟩
      , ⟨1, "linear_ok", .coreClk, .syncReset 1#64, false, .wireRef 4, 1⟩ ]
  , outputs :=
      [ ⟨"out_face_bit", .regRead 0, 1⟩
      , ⟨"out_linear_ok", .regRead 1, 1⟩ ] }

theorem ospcFabricSliceRtl_wellFormed :
    checkRtlModule ospcFabricSliceRtl = true ∧
    checkRtlModuleW ospcFabricSliceRtl = true ∧
    checkWidths ospcFabricSliceRtl = true := by decide +kernel

/-- 8-pin IO map on tile `X0Y1` for `ospcFabricSliceRtl`. -/
def ospcFabricPins : List Pin :=
  [ { tile := "X0Y1", bel := "P0", role := .input 0 0 }
  , { tile := "X0Y1", bel := "P1", role := .input 0 1 }
  , { tile := "X0Y1", bel := "P2", role := .input 1 0 }
  , { tile := "X0Y1", bel := "P3", role := .input 2 0 }
  , { tile := "X0Y1", bel := "P4", role := .input 3 0 }
  , { tile := "X0Y1", bel := "P5", role := .reset }
  , { tile := "X0Y1", bel := "P6", role := .output 0 0 }
  , { tile := "X0Y1", bel := "P7", role := .output 1 0 } ]

private def cellSpecEntries (tile letter : String) (baseBit : Nat) : List ((String × String) × Pattern) :=
  ((List.range 16).map fun k =>
    ((tile, lutInitFeat letter k), [(baseBit + k, true)])) ++
  [ ((tile, letter ++ ".FF"), [(baseBit + 16, true)])
  , ((tile, letter ++ ".I0mux"), [(baseBit + 17, true)])
  , ((tile, letter ++ ".SET_NORESET"), [(baseBit + 18, true)]) ]

/-- Concrete 2-column × 3-row (`cols = 2, rows = 3`, interior tiles `X0Y1`, `X1Y1`) kernel-reducible
`FABulous` fabric metadata with muxed switch-matrix pips (`I1_MUX`, `LIN_MUX`) and two `FABULOUS_LC` BELs. -/
def ospcKernelFabric : KernelFabric :=
  { spec :=
      cellSpecEntries "X1Y1" "A" 0 ++
      cellSpecEntries "X1Y1" "B" 20 ++
      [ (("X0Y1", "HW"), [])
      , (("X1Y1", "HW"), [])
      , (("X1Y1", "I1_MUX.FACE"), [(40, true), (41, false)])
      , (("X1Y1", "I1_MUX.ALT"),  [(40, false), (41, true)])
      , (("X1Y1", "LIN_MUX.PAIR"), [(42, true), (43, false)])
      , (("X1Y1", "LIN_MUX.ALT"),  [(42, false), (43, true)]) ]
  , into :=
      [ (("X0Y1", "P0_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P1_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P2_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P3_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P4_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P5_T"), [("X0Y1", "VCC0", "HW")])
      , (("X0Y1", "P6_T"), [("X0Y1", "GND0", "HW")])
      , (("X0Y1", "P7_T"), [("X0Y1", "GND0", "HW")])
      , (("X0Y1", "P6_I"), [("X1Y1", "LA_O", "HW")])
      , (("X0Y1", "P7_I"), [("X1Y1", "LB_O", "HW")])
      , (("X1Y1", "W_P0"), [("X0Y1", "P0_O", "HW")])
      , (("X1Y1", "W_P2"), [("X0Y1", "P2_O", "HW")])
      , (("X1Y1", "W_P3"), [("X0Y1", "P3_O", "HW")])
      , (("X1Y1", "W_P4"), [("X0Y1", "P4_O", "HW")])
      , (("X1Y1", "LA_I0"), [("X1Y1", "LA_O", "HW")])
      , (("X1Y1", "LA_I1"), [("X1Y1", "W_P2", "I1_MUX.FACE"), ("X1Y1", "W_P0", "I1_MUX.ALT")])
      , (("X1Y1", "LA_I2"), [("X0Y1", "P0_O", "HW")])
      , (("X1Y1", "LA_I3"), [("X0Y1", "P1_O", "HW")])
      , (("X1Y1", "LA_EN"), [("X1Y1", "VCC0", "HW")])
      , (("X1Y1", "LA_SR"), [("X0Y1", "P5_O", "HW")])
      , (("X1Y1", "LB_I0"), [("X1Y1", "LB_O", "HW")])
      , (("X1Y1", "LB_I1"), [("X0Y1", "P3_O", "HW")])
      , (("X1Y1", "LB_I2"), [("X1Y1", "W_P4", "LIN_MUX.PAIR"), ("X1Y1", "W_P3", "LIN_MUX.ALT")])
      , (("X1Y1", "LB_EN"), [("X1Y1", "VCC0", "HW")])
      , (("X1Y1", "LB_SR"), [("X0Y1", "P5_O", "HW")]) ]
  , bels :=
      [ ("X0Y1", [("P0", ioType, "P0_"), ("P1", ioType, "P1_"), ("P2", ioType, "P2_"), ("P3", ioType, "P3_"),
                  ("P4", ioType, "P4_"), ("P5", ioType, "P5_"), ("P6", ioType, "P6_"), ("P7", ioType, "P7_")])
      , ("X1Y1", [("A", lutType, "LA_"), ("B", lutType, "LB_")]) ]
  , cols := 2
  , rows := 3 }

/-- `Obend.Hardware.Fabulous.Fabric` view of `ospcKernelFabric` for `Obend.Hardware.Fabulous.extract`. -/
def ospcFabulousFabric : Fabric := ospcKernelFabric.toFabric

/-- Valid configuration bit word for tile `X1Y1`:
- BEL `A`: `INIT = 0xCE8A`, `FF = 1`, `I0mux = 0`, `SET_NORESET = 0`
- BEL `B`: `INIT = 0xA2A2`, `FF = 1`, `I0mux = 0`, `SET_NORESET = 1`
- Switch-matrix muxes: `I1_MUX = (1,0)` (`FACE`), `LIN_MUX = (1,0)` (`PAIR`). -/
def ospcTile1CfgBits : Nat :=
  OSPC_FACE_LUT4_INIT.toNat |||
  (1 <<< 16) |||
  (OSPC_LIN_LUT4_INIT.toNat <<< 20) |||
  (1 <<< 36) |||
  (1 <<< 38) |||
  (1 <<< 40) |||
  (1 <<< 42)

/-- Encoded 344-byte FABulous binary bitstream for `ospcKernelFabric`. -/
def ospcFabulousBitstream : ByteArray :=
  encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)

/-- Expected extracted `Net` configured by `ospcFabulousBitstream`. -/
def ospcExtractedNet : Net where
  gates :=
    [ { init := OSPC_FACE_LUT4_INIT, i0 := .ff 0, i1 := .pin 2, i2 := .pin 0, i3 := .pin 1, site := "X1Y1.A" }
    , { init := OSPC_LIN_LUT4_INIT,  i0 := .ff 1, i1 := .pin 3, i2 := .pin 4, i3 := .const false, site := "X1Y1.B" } ]
  flops :=
    [ { d := .gate 0, en := .const true, sr := .pin 5, rv := false, site := "X1Y1.A" }
    , { d := .gate 1, en := .const true, sr := .pin 5, rv := true,  site := "X1Y1.B" } ]
  outs := [(6, .ff 0), (7, .ff 1)]

/-- Register-to-flop map: flop 0 holds `(reg 0, bit 0)` (`face_bit`), flop 1 holds `(reg 1, bit 0)` (`linear_ok`). -/
def ospcFabricFlopMap : List (Nat × Nat) := [(0, 0), (1, 0)]

/-- **Kernel-Verified Bitstream Decode + Extraction**: `decodeFabulousFrames` + `extractFabulousNet`
on the 344-byte `ospcFabulousBitstream` succeeds and recovers `ospcExtractedNet` identically. -/
private theorem fabReadBe32_fabBe32List (w : Nat) (hw : w < 2 ^ 32) (rest : List UInt8) :
    fabReadBe32 (fabBe32List w ++ rest) = some (w, rest) := by
  have hMod : ∀ n : Nat, (UInt8.ofNat (n &&& 0xFF)).toNat = n % 256 := fun n => by
    have h255 : 255 = 2 ^ 8 - 1 := by decide
    simp only [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, h255, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod]
  simp only [fabBe32List, List.cons_append, List.nil_append, fabReadBe32, hMod,
    Nat.shiftRight_eq_div_pow]
  exact congrArg some (Prod.ext (by omega) rfl)

private theorem checkPrefixBytes_append (pre rest : List UInt8) :
    checkPrefixBytes pre (pre ++ rest) = some rest := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp [checkPrefixBytes, ih]

private theorem fabBe32List_len (w : Nat) : (fabBe32List w).length = 4 := rfl

private theorem flatMap_range_len {α : Type} (n c : Nat) (f : Nat → List α)
    (hf : ∀ k, (f k).length = c) : ((List.range n).flatMap f).length = n * c := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hf,
        Nat.succ_mul]

private theorem encodeFabulousFrames_size (cols rows : Nat) (tileCfg : Nat → Nat → Nat)
    (desyncWord : Nat) :
    (encodeFabulousFrames cols rows tileCfg desyncWord).size =
      20 + cols * 20 * (4 + 4 * (rows - 2)) + 4 := by
  have hCol : ∀ x : Nat,
      ((List.range 20).flatMap fun f =>
        fabBe32List ((x <<< 27) ||| (1 <<< f)) ++
        (List.range (rows - 2)).flatMap fun r =>
          fabBe32List ((tileCfg x (rows - 2 - r) >>> (32 * f)) &&& 0xFFFFFFFF)).length =
      20 * (4 + 4 * (rows - 2)) := fun x => by
    rw [flatMap_range_len 20 (4 + 4 * (rows - 2))]
    intro f
    rw [List.length_append, fabBe32List_len, flatMap_range_len (rows - 2) 4 _ (fun _ => fabBe32List_len _)]
    omega
  change (encodeFabulousFramesList cols rows tileCfg desyncWord).toArray.size = _
  rw [List.size_toArray]
  unfold encodeFabulousFramesList
  simp only [List.length_append, fabBe32List_len, flatMap_range_len cols _ _ hCol,
    show syncHeader.length = 20 by rfl]
  rw [Nat.mul_assoc]

private theorem decodeFramesLoop_colZero (x : Nat) (tail : List UInt8) (cfg : List ((Nat × Nat) × Nat))
    (hx : x < 32) :
    ∀ (rem : Nat), rem ≤ 20 →
      let start := 20 - rem
      let framesBytes :=
        ((List.range rem).map (· + start)).flatMap fun f =>
          fabBe32List ((x <<< 27) ||| (1 <<< f)) ++ fabBe32List 0
      decodeFramesLoop x 3 1 rem (framesBytes ++ tail) cfg = .ok (tail, cfg) := by
  intro rem
  induction rem with
  | zero => intro _; rfl
  | succ k ih =>
    intro hle
    dsimp only
    rw [@List.range_succ_eq_map k, List.map_cons, List.map_map, List.flatMap_cons,
        List.append_assoc, List.append_assoc]
    have hSelLt : (x <<< 27) ||| (1 <<< (20 - (k + 1))) < 2 ^ 32 := by
      have h1 : x <<< 27 < 2 ^ 32 := by
        rw [Nat.shiftLeft_eq]; have : 2 ^ 32 = 32 * 2 ^ 27 := by decide
        omega
      have h2 : 1 <<< (20 - (k + 1)) < 2 ^ 32 := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by decide) (by omega)
      exact Nat.or_lt_two_pow h1 h2
    have hf0 : 0 + (20 - (k + 1)) = 20 - (k + 1) := Nat.zero_add _
    conv => lhs; unfold decodeFramesLoop
    rw [hf0, fabReadBe32_fabBe32List _ hSelLt]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    conv => lhs; unfold decodeRowsLoop
    rw [fabReadBe32_fabBe32List 0 (by decide)]
    simp only [beq_self_eq_true, ↓reduceIte, decodeRowsLoop]
    have hMap : (List.map ((fun y => y + (20 - (k + 1))) ∘ Nat.succ) (List.range k)) =
        (List.range k).map (· + (20 - k)) := by
      apply List.map_congr_left
      intro a _; dsimp; omega
    rw [hMap]
    exact ih (by omega)

private theorem decodeFramesLoop_step1 (f w rem : Nat) (rest : List UInt8) (cfg : List ((Nat × Nat) × Nat))
    (hf : f = 20 - (rem + 1)) (hf20 : f < 20) (hw : w < 2 ^ 32) :
    decodeFramesLoop 1 3 1 (rem + 1) (fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++ (fabBe32List w ++ rest)) cfg =
      decodeFramesLoop 1 3 1 rem rest (if w == 0 then cfg else cfgOrInsertXY 1 1 (w <<< (32 * f)) cfg) := by
  have hSelLt : (1 <<< 27) ||| (1 <<< f) < 2 ^ 32 := by
    have h1 : 1 <<< 27 < 2 ^ 32 := by decide
    have h2 : 1 <<< f < 2 ^ 32 := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by decide) (by omega)
    exact Nat.or_lt_two_pow h1 h2
  conv => lhs; unfold decodeFramesLoop
  rw [← hf, fabReadBe32_fabBe32List _ hSelLt]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  conv => lhs; unfold decodeRowsLoop
  rw [fabReadBe32_fabBe32List w hw]
  simp only [decodeRowsLoop, show 3 - 2 - (1 - (0 + 1)) = 1 from rfl]

private theorem encodeFabulousFrames_2x3_data (cfgVal desyncWord : Nat) :
    (encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then cfgVal else 0) desyncWord).data.toList =
      syncHeader ++
      (((List.range 20).flatMap fun f => fabBe32List ((0 <<< 27) ||| (1 <<< f)) ++ fabBe32List 0) ++
       (((List.range 20).flatMap fun f =>
           fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++
           fabBe32List ((cfgVal >>> (32 * f)) &&& 0xFFFFFFFF)) ++
        fabBe32List desyncWord)) := by
  change (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then cfgVal else 0) desyncWord).toArray.toList = _
  rw [List.toList_toArray]
  unfold encodeFabulousFramesList
  dsimp only
  have hR2 : List.range 2 = [0, 1] := rfl
  have hR1 : List.range (3 - 2) = [0] := rfl
  rw [hR2, hR1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    Nat.sub_zero, show (0 == 1) = false by decide, show (1 == 1) = true by decide,
    Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
    show (0 >>> _) &&& 0xFFFFFFFF = 0 from by simp]

private theorem decodeFabulousFrames_ospc_tile1 (cfgVal : Nat) (hLt : cfgVal < 2 ^ 64) :
    decodeFabulousFrames 2 3
      (encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then cfgVal else 0) (1 <<< 20)) =
      .ok (if cfgVal == 0 then [] else [("X1Y1", cfgVal)]) := by
  unfold decodeFabulousFrames
  rw [encodeFabulousFrames_size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    encodeFabulousFrames_2x3_data, checkPrefixBytes_append]
  conv => lhs; unfold decodeColsLoop
  have hCol0 := decodeFramesLoop_colZero 0
    (((List.range 20).flatMap fun f =>
        fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++
        fabBe32List ((cfgVal >>> (32 * f)) &&& 0xFFFFFFFF)) ++
      fabBe32List (1 <<< 20)) [] (by decide) 20 (by decide)
  dsimp only at hCol0
  have hRange0 : (List.range 20).map (· + (20 - 20)) = List.range 20 := by simp
  rw [hRange0] at hCol0
  simp only [Nat.sub_self, hCol0]
  conv => lhs; unfold decodeColsLoop
  have hRange20 : List.range 20 = [0, 1] ++ (List.range 18).map (· + 2) := by decide
  simp only [show 2 - 1 = 1 by rfl]
  rw [hRange20, List.flatMap_append, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  have hMaskLt : ∀ m : Nat, m &&& 0xFFFFFFFF < 2 ^ 32 := fun m => by
    have h : 0xFFFFFFFF = 2 ^ 32 - 1 := by decide
    rw [h, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)
  rw [decodeFramesLoop_step1 0 ((cfgVal >>> 0) &&& 0xFFFFFFFF) 19 _ [] rfl (by decide) (hMaskLt _)]
  rw [decodeFramesLoop_step1 1 ((cfgVal >>> 32) &&& 0xFFFFFFFF) 18 _ _ rfl (by decide) (hMaskLt _)]
  have hZeroRest : ∀ f ∈ (List.range 18).map (· + 2),
      (cfgVal >>> (32 * f)) &&& 0xFFFFFFFF = 0 := by
    intro f hf
    simp only [List.mem_map, List.mem_range] at hf; obtain ⟨k, _, rfl⟩ := hf
    have hPow : 2 ^ 64 ≤ 2 ^ (32 * (k + 2)) := Nat.pow_le_pow_right (by decide) (by omega)
    have hDiv : cfgVal / 2 ^ (32 * (k + 2)) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hLt hPow)
    simp [Nat.shiftRight_eq_div_pow, hDiv]
  have hFlatEq : ((List.range 18).map (· + 2)).flatMap (fun f =>
        fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++
        fabBe32List ((cfgVal >>> (32 * f)) &&& 0xFFFFFFFF)) =
      ((List.range 18).map (· + (20 - 18))).flatMap (fun f =>
        fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++ fabBe32List 0) := by
    simp only [List.flatMap]
    congr 1
    apply List.map_congr_left
    intro f hf
    rw [hZeroRest f hf]
  rw [hFlatEq, decodeFramesLoop_colZero 1 _ _ (by decide) 18 (by decide)]
  simp only [decodeColsLoop]
  rw [← List.append_nil (fabBe32List (1 <<< 20)), fabReadBe32_fabBe32List (1 <<< 20) (by decide) []]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 <<< 20) &&& (1 <<< 20) == 0) = false by decide]
  have hLo : (cfgVal >>> 0) &&& 0xFFFFFFFF = cfgVal % 2 ^ 32 := by
    have h : 0xFFFFFFFF = 2 ^ 32 - 1 := by decide
    rw [Nat.shiftRight_zero, h, Nat.and_two_pow_sub_one_eq_mod]
  have hHi : (cfgVal >>> 32) &&& 0xFFFFFFFF = cfgVal / 2 ^ 32 := by
    have h : 0xFFFFFFFF = 2 ^ 32 - 1 := by decide
    rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
    have h64 : 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    omega
  have hRecomb : (cfgVal % 2 ^ 32) ||| ((cfgVal / 2 ^ 32) <<< 32) = cfgVal := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_div_two_pow]
    by_cases hi : i < 32
    · simp [hi, show ¬(32 ≤ i) by omega]
    · simp [hi, show 32 ≤ i by omega]
  have hTile11 : fabTileName 1 1 = "X1Y1" := rfl
  rw [hLo, hHi]
  by_cases h0 : cfgVal % 2 ^ 32 = 0 <;> by_cases h1 : cfgVal / 2 ^ 32 = 0
  · have hZ : cfgVal = 0 := by omega
    rw [h0, h1, hZ]
    simp only [beq_self_eq_true, ↓reduceIte, List.map_nil]
  · have hNZ : cfgVal ≠ 0 := by omega
    have hEq : (cfgVal / 2 ^ 32) <<< 32 = cfgVal := by
      conv => rhs; rw [← hRecomb, h0, Nat.zero_or]
    simp only [h0, beq_false_of_ne h1, beq_false_of_ne hNZ, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, cfgOrInsertXY, Nat.mul_one, hEq,
      List.map_cons, List.map_nil, hTile11]
  · have hNZ : cfgVal ≠ 0 := by omega
    have hEq : cfgVal % 2 ^ 32 = cfgVal := by omega
    simp only [h1, beq_false_of_ne hNZ, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, cfgOrInsertXY, Nat.mul_zero, Nat.shiftLeft_zero, hEq,
      List.map_cons, List.map_nil, hTile11]
  · have hNZ : cfgVal ≠ 0 := by omega
    simp only [beq_false_of_ne h0, beq_false_of_ne h1, beq_false_of_ne hNZ,
      Bool.false_eq_true, ↓reduceIte, cfgOrInsertXY, beq_self_eq_true, Bool.and_self,
      Nat.mul_zero, Nat.mul_one, Nat.shiftLeft_zero, hRecomb,
      List.map_cons, List.map_nil, hTile11]

theorem ospc_fabulous_decode_extract_ok :
    decodeAndExtractFabulous ospcKernelFabric ospcFabricPins ospcFabulousBitstream =
      .ok ospcExtractedNet := by
  unfold decodeAndExtractFabulous ospcFabulousBitstream
  rw [show ospcKernelFabric.cols = 2 from rfl, show ospcKernelFabric.rows = 3 from rfl,
      decodeFabulousFrames_ospc_tile1 ospcTile1CfgBits (by decide)]
  rfl

/-- Corrupted bitstream fixtures for tamper-refusal proofs. -/
def corruptSyncBitstream : ByteArray :=
  ByteArray.mk ((0xFF :: syncHeader.tail) ++
    (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 20).toArray

def corruptDesyncBitstream : ByteArray :=
  encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0) 0

def corruptFrameSelectBitstream : ByteArray :=
  ByteArray.mk (syncHeader ++ (0xFF ::
    ((encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 21))).toArray

def corruptTruncatedBitstream : ByteArray :=
  ByteArray.mk syncHeader.toArray

def corruptPipSelectBitstream : ByteArray :=
  encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits ^^^ (1 <<< 40) else 0)

def corruptI0MuxCarryBitstream : ByteArray :=
  encodeFabulousFrames 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits ||| (1 <<< 17) else 0)

private theorem byteArray_get!_cons (b : UInt8) (bs : List UInt8) :
    (ByteArray.mk (b :: bs).toArray).get! 0 = b := by
  change (b :: bs).toArray[0]! = b
  simp

/-- **Tampered Bitstream Refusal (`ospc_fabulous_corrupt_bitstreams_refused`)**:
Corrupting the `0xFAB0FAB1` sync header, truncating frame length, corrupting a frame-select word,
clearing desync bit 20, invalidating a switch-matrix pip select, or asserting unmodelled carry
`I0mux` are all refused (including direct `Obend.Hardware.Fabulous.decodeBin` sync/length refusals). -/
theorem ospc_fabulous_corrupt_bitstreams_refused :
    (decodeBin 2 3 corruptSyncBitstream).isOk = false ∧
    (decodeBin 2 3 corruptTruncatedBitstream).isOk = false ∧
    (decodeFabulousFrames 2 3 corruptDesyncBitstream).isOk = false ∧
    (decodeFabulousFrames 2 3 corruptFrameSelectBitstream).isOk = false ∧
    (decodeAndExtractFabulous ospcKernelFabric ospcFabricPins corruptPipSelectBitstream).isOk = false ∧
    (decodeAndExtractFabulous ospcKernelFabric ospcFabricPins corruptI0MuxCarryBitstream).isOk = false := by
  have hFull : (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).length = 344 := by
    have h := encodeFabulousFrames_size 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0) (1 <<< 20)
    simpa only [encodeFabulousFrames, ByteArray.size, List.size_toArray] using h
  have hDropLen :
      ((encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 20).length =
        324 := by
    rw [List.length_drop, hFull]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Corrupt sync header (`byte 0` flipped from `0x00` to `0xFF`)
    unfold decodeBin corruptSyncBitstream
    have hSz : (ByteArray.mk ((0xFF :: syncHeader.tail) ++
        (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 20).toArray).size = 344 := by
      simp only [ByteArray.size, List.size_toArray, List.length_append, List.length_cons,
        show syncHeader.tail.length = 19 by rfl, hDropLen]
    have hByte0 :
        (ByteArray.mk ((0xFF :: syncHeader.tail) ++
          (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 20).toArray).get! 0 =
        0xFF := by
      rw [List.cons_append, byteArray_get!_cons]
    have hAny : (List.range 20).any (fun i =>
        (ByteArray.mk ((0xFF :: syncHeader.tail) ++
          (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 20).toArray).get! i !=
        syncHeader[i]!) = true := by
      apply List.any_eq_true.mpr
      refine ⟨0, by decide, ?_⟩
      rw [hByte0]
      rfl
    simp only [hSz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hAny, Except.isOk]
    rfl
  · -- Truncated bitstream (20 bytes != 344 bytes)
    unfold decodeBin corruptTruncatedBitstream
    have hSz : (ByteArray.mk syncHeader.toArray).size = 20 := rfl
    simp only [hSz]
    rfl
  · -- Zero desync word (bit 20 = 0)
    unfold decodeFabulousFrames corruptDesyncBitstream
    rw [encodeFabulousFrames_size]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      encodeFabulousFrames_2x3_data, checkPrefixBytes_append]
    conv => lhs; unfold decodeColsLoop
    have hCol0 := decodeFramesLoop_colZero 0
      (((List.range 20).flatMap fun f =>
          fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++
          fabBe32List ((ospcTile1CfgBits >>> (32 * f)) &&& 0xFFFFFFFF)) ++
        fabBe32List 0) [] (by decide) 20 (by decide)
    dsimp only at hCol0
    have hRange0 : (List.range 20).map (· + (20 - 20)) = List.range 20 := by simp
    rw [hRange0] at hCol0
    simp only [Nat.sub_self, hCol0]
    conv => lhs; unfold decodeColsLoop
    have hRange20 : List.range 20 = [0, 1] ++ (List.range 18).map (· + 2) := by decide
    simp only [show 2 - 1 = 1 by rfl]
    rw [hRange20, List.flatMap_append, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    have hMaskLt : ∀ m : Nat, m &&& 0xFFFFFFFF < 2 ^ 32 := fun m => by
      have h : 0xFFFFFFFF = 2 ^ 32 - 1 := by decide
      rw [h, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)
    rw [decodeFramesLoop_step1 0 ((ospcTile1CfgBits >>> 0) &&& 0xFFFFFFFF) 19 _ [] rfl (by decide) (hMaskLt _)]
    rw [decodeFramesLoop_step1 1 ((ospcTile1CfgBits >>> 32) &&& 0xFFFFFFFF) 18 _ _ rfl (by decide) (hMaskLt _)]
    have hZeroRest : ∀ f ∈ (List.range 18).map (· + 2),
        (ospcTile1CfgBits >>> (32 * f)) &&& 0xFFFFFFFF = 0 := by
      intro f hf
      simp only [List.mem_map, List.mem_range] at hf; obtain ⟨k, _, rfl⟩ := hf
      have hLt : ospcTile1CfgBits < 2 ^ 64 := by decide
      have hPow : 2 ^ 64 ≤ 2 ^ (32 * (k + 2)) := Nat.pow_le_pow_right (by decide) (by omega)
      have hDiv : ospcTile1CfgBits / 2 ^ (32 * (k + 2)) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hLt hPow)
      simp [Nat.shiftRight_eq_div_pow, hDiv]
    have hFlatEq : ((List.range 18).map (· + 2)).flatMap (fun f =>
          fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++
          fabBe32List ((ospcTile1CfgBits >>> (32 * f)) &&& 0xFFFFFFFF)) =
        ((List.range 18).map (· + (20 - 18))).flatMap (fun f =>
          fabBe32List ((1 <<< 27) ||| (1 <<< f)) ++ fabBe32List 0) := by
      exact congrArg List.flatten (List.map_congr_left fun f hf => by rw [hZeroRest f hf])
    rw [hFlatEq, decodeFramesLoop_colZero 1 _ _ (by decide) 18 (by decide)]
    simp only [decodeColsLoop]
    rw [← List.append_nil (fabBe32List 0)]
    rw [fabReadBe32_fabBe32List 0 (by decide) []]
    rfl
  · -- Corrupt frame-select word (first byte after sync header set to `0xFF`)
    unfold decodeFabulousFrames corruptFrameSelectBitstream
    have hDrop21 : ((encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 21).length = 323 := by
      rw [List.length_drop, hFull]
    have hSz : (ByteArray.mk (syncHeader ++ (0xFF ::
        ((encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 21))).toArray).size = 344 := by
      simp only [ByteArray.size, List.size_toArray, List.length_append, List.length_cons,
        show syncHeader.length = 20 by rfl, hDrop21]
    simp only [hSz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, checkPrefixBytes_append]
    have hTail3 : ∃ b1 b2 b3 rest,
        (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 21 =
          b1 :: b2 :: b3 :: rest := by
      match h : (encodeFabulousFramesList 2 3 (fun x y => if x == 1 && y == 1 then ospcTile1CfgBits else 0)).drop 21 with
      | b1 :: b2 :: b3 :: rest => exact ⟨b1, b2, b3, rest, rfl⟩
      | [] | [_] | [_, _] => rw [h] at hDrop21; simp at hDrop21
    obtain ⟨b1, b2, b3, rest, hTail⟩ := hTail3
    rw [hTail]
    unfold decodeColsLoop decodeFramesLoop fabReadBe32
    have hNe : ((0xFF : UInt8).toNat * 2^24 + b1.toNat * 2^16 + b2.toNat * 2^8 + b3.toNat) ≠
        ((0 <<< 27) ||| (1 <<< 0)) := by
      have hff : (0xFF : UInt8).toNat = 255 := rfl
      rw [hff]
      have h1 : (0 <<< 27) ||| (1 <<< 0) = 1 := rfl
      rw [h1]; omega
    simp only [bne_iff_ne.mpr hNe, ↓reduceIte, Except.isOk]
    rfl
  · -- Corrupt switch-matrix pip select (bit 40 flipped -> no pip matches `I1_MUX`)
    unfold decodeAndExtractFabulous corruptPipSelectBitstream
    rw [show ospcKernelFabric.cols = 2 from rfl, show ospcKernelFabric.rows = 3 from rfl,
        decodeFabulousFrames_ospc_tile1 (ospcTile1CfgBits ^^^ (1 <<< 40)) (by decide)]
    rfl
  · -- Corrupt carry input `I0mux` asserted (bit 17 set -> unmodelled carry refused)
    unfold decodeAndExtractFabulous corruptI0MuxCarryBitstream
    rw [show ospcKernelFabric.cols = 2 from rfl, show ospcKernelFabric.rows = 3 from rfl,
        decodeFabulousFrames_ospc_tile1 (ospcTile1CfgBits ||| (1 <<< 17)) (by decide)]
    rfl

/-- ECP5 / FABulous `lut4cModule` cell-level soundness for both OSPC LUT4+FF BELs:
instantiating `Obend.Hardware.Fabulous.lut4cModule` with config bits from `ospcTile1CfgBits`
matches the exact next-state equations of `ospcExtractedNet`'s flops (`X1Y1.A` and `X1Y1.B`). -/
theorem ospc_ecp5_lut4c_cells_refine_spec
    (q0 q1 inBit op0 op1 redexEn linPair rst : Bool) :
    let cbA : Nat → Bool := fun j => ospcTile1CfgBits.testBit j
    let cbB : Nat → Bool := fun j => ospcTile1CfgBits.testBit (20 + j)
    stepModuleRegs lut4cModule false (cellIns q0 inBit op0 op1 false rst true cbA) (fun _ => boolBV q0) 0 =
      boolBV (if rst then false else lut4 OSPC_FACE_LUT4_INIT q0 inBit op0 op1) ∧
    stepModuleRegs lut4cModule false (cellIns q1 redexEn linPair false false rst true cbB) (fun _ => boolBV q1) 0 =
      boolBV (if rst then true else lut4 OSPC_LIN_LUT4_INIT q1 redexEn linPair false) := by
  intro cbA cbB
  rw [lut4c_next, lut4c_next]
  have hA : cbA 17 = false ∧ cbA 18 = false ∧ (∀ j < 16, cbA j = OSPC_FACE_LUT4_INIT.getLsbD j) := by
    refine ⟨by decide, by decide, fun j hj => ?_⟩
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
    | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => decide
    | _ + 16, h => omega
  have hB : cbB 17 = false ∧ cbB 18 = true ∧ (∀ j < 16, cbB j = OSPC_LIN_LUT4_INIT.getLsbD j) := by
    refine ⟨by decide, by decide, fun j hj => ?_⟩
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
    | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => decide
    | _ + 16, h => omega
  constructor
  · congr 1
    simp only [mux2, cellLut, hA.1, hA.2.1, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
      Bool.not_true, Bool.false_and, Bool.or_false]
    rw [lut4F_congr cbA OSPC_FACE_LUT4_INIT.getLsbD hA.2.2, ← lut4_eq_lut4F]
    cases rst <;> simp
  · congr 1
    simp only [mux2, cellLut, hB.1, hB.2.1, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
      Bool.not_true, Bool.false_and, Bool.or_false]
    rw [lut4F_congr cbB OSPC_LIN_LUT4_INIT.getLsbD hB.2.2, ← lut4_eq_lut4F]
    cases rst <;> simp

private theorem bv1_cases (v : BitVec 64) (h : v.toNat < 2 ^ 1) :
    v = 0#64 ∨ v = 1#64 := by
  have hv : v.toNat = 0 ∨ v.toNat = 1 := by omega
  rcases hv with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq h0
  · right; exact BitVec.eq_of_toNat_eq h1

private theorem bv2_cases (v : BitVec 64) (h : v.toNat < 2 ^ 2) :
    v = 0#64 ∨ v = 1#64 ∨ v = 2#64 ∨ v = 3#64 := by
  have hv : v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3 := by omega
  rcases hv with h0 | h1 | h2 | h3
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h1))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h2)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h3)))

private theorem ospcExtractedNet_step_bits
    (rst : Bool) (r0 r1 i0 i1 i2 i3 : BitVec 64)
    (hr0 : r0 = 0#64 ∨ r0 = 1#64) (hr1 : r1 = 0#64 ∨ r1 = 1#64)
    (hi0 : i0 = 0#64 ∨ i0 = 1#64 ∨ i0 = 2#64 ∨ i0 = 3#64)
    (hi1 : i1 = 0#64 ∨ i1 = 1#64) (hi2 : i2 = 0#64 ∨ i2 = 1#64) (hi3 : i3 = 0#64 ∨ i3 = 1#64) :
    let q0 := r0.getLsbD 0
    let q1 := r1.getLsbD 0
    let g0 := lut4 OSPC_FACE_LUT4_INIT q0 (i1.getLsbD 0) (i0.getLsbD 0) (i0.getLsbD 1)
    let g1 := lut4 OSPC_LIN_LUT4_INIT q1 (i2.getLsbD 0) (i3.getLsbD 0) false
    let nFace := if rst then 0#64
      else if (if i0 == 1#64 then 1#64 else 0#64) != 0#64 then r0 &&& i1
      else if (if i0 == 2#64 then 1#64 else 0#64) != 0#64 then r0 ||| i1
      else if (if i0 == 3#64 then 1#64 else 0#64) != 0#64 then i1
      else r0
    let nLin := if rst then 1#64
      else r1 &&& (if i2 != 0#64 then i3 else 1#64)
    [mux2 true q0 (mux2 rst g0 false), mux2 true q1 (mux2 rst g1 true)] =
      [nFace.getLsbD 0, nLin.getLsbD 0] := by
  rcases hr0 with rfl | rfl <;> rcases hr1 with rfl | rfl <;>
  rcases hi0 with rfl | rfl | rfl | rfl <;> rcases hi1 with rfl | rfl <;>
  rcases hi2 with rfl | rfl <;> rcases hi3 with rfl | rfl <;> cases rst <;> decide

/-- **Single-Step FABulous Fabric Refinement (`ospcExtractedNet_step_realizes`)**:
For every in-width register file and input cycle of `ospcFabricSliceRtl`, stepping `ospcExtractedNet`
matches `stepModuleRegs ospcFabricSliceRtl` on both flops and produces identical output pins. -/
theorem ospcExtractedNet_step_realizes :
    StepRealizes ospcExtractedNet ospcFabricSliceRtl ospcFabricPins (projOf ospcFabricFlopMap) := by
  intro regs c hR hI
  rcases c with ⟨rst, ins⟩
  have hr0 : regs 0 = 0#64 ∨ regs 0 = 1#64 := bv1_cases (regs 0) (hR 0)
  have hr1 : regs 1 = 0#64 ∨ regs 1 = 1#64 := bv1_cases (regs 1) (hR 1)
  have hi0 : ins 0 = 0#64 ∨ ins 0 = 1#64 ∨ ins 0 = 2#64 ∨ ins 0 = 3#64 := bv2_cases (ins 0) (hI 0)
  have hi1 : ins 1 = 0#64 ∨ ins 1 = 1#64 := bv1_cases (ins 1) (hI 1)
  have hi2 : ins 2 = 0#64 ∨ ins 2 = 1#64 := bv1_cases (ins 2) (hI 2)
  have hi3 : ins 3 = 0#64 ∨ ins 3 = 1#64 := bv1_cases (ins 3) (hI 3)
  constructor
  · apply ospcExtractedNet.step_eq_projOf ospcFabricFlopMap _ _ _ rfl
    change
      [mux2 true ((regs 0).getLsbD 0)
        (mux2 rst (lut4 OSPC_FACE_LUT4_INIT ((regs 0).getLsbD 0) ((ins 1).getLsbD 0) ((ins 0).getLsbD 0) ((ins 0).getLsbD 1)) false),
       mux2 true ((regs 1).getLsbD 0)
        (mux2 rst (lut4 OSPC_LIN_LUT4_INIT ((regs 1).getLsbD 0) ((ins 2).getLsbD 0) ((ins 3).getLsbD 0) false) true)] =
      [(if rst then 0#64
        else if (if ins 0 == 1#64 then 1#64 else 0#64) != 0#64 then regs 0 &&& ins 1
        else if (if ins 0 == 2#64 then 1#64 else 0#64) != 0#64 then regs 0 ||| ins 1
        else if (if ins 0 == 3#64 then 1#64 else 0#64) != 0#64 then ins 1
        else regs 0).getLsbD 0,
       (if rst then 1#64 else regs 1 &&& (if ins 2 != 0#64 then ins 3 else 1#64)).getLsbD 0]
    exact ospcExtractedNet_step_bits rst (regs 0) (regs 1) (ins 0) (ins 1) (ins 2) (ins 3)
      hr0 hr1 hi0 hi1 hi2 hi3
  · rcases hr0 with h0 | h0 <;> rcases hr1 with h1 | h1 <;>
    · simp only [ospcExtractedNet, ospcFabricSliceRtl, ospcFabricPins, ospcFabricFlopMap,
        Net.outputs, outPinValue, evalModuleOutputsW, evalWireTable, evalRtlExpr,
        Lit.eval, projOf, List.map_cons, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
        h0, h1]
      decide

/-- **Power-Up Reset Realization (`ospcExtractedNet_reset_realizes`)**:
From ANY unknown power-up flop state `q : Nat → Bool`, a reset edge loads `(0, 1)` matching
`ospcFabricSliceRtl`'s `.syncReset 0#64` (`face_bit`) and `.syncReset 1#64` (`linear_ok`). -/
theorem ospcExtractedNet_reset_realizes :
    ResetRealizes ospcExtractedNet ospcFabricSliceRtl ospcFabricPins (projOf ospcFabricFlopMap) := by
  intro q regs ins _
  apply ospcExtractedNet.step_eq_projOf ospcFabricFlopMap _ _ _ rfl
  simp only [ospcExtractedNet, ospcFabricSliceRtl, ospcFabricPins, ospcFabricFlopMap,
    Net.gateVals, evalGates, Gate.eval, Lit.eval, Flop.next, pinValues, stepModuleRegs,
    evalWireTable, evalRtlExpr, mux2,
    List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, beq_self_eq_true, Nat.reduceBEq,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.or_false,
    Bool.and_true, Bool.and_false]
  decide

/-- **Multi-Cycle FABulous Bitstream-to-Signal Refinement (`ospc_fabulous_bitstream_refines_slice`)**:
Decoding `ospcFabulousBitstream` through `decodeFabulousFrames` + `extractFabulousNet` produces
`ospcExtractedNet`, whose multi-cycle `Net.run` matches `ospcFabricSliceRtl` and its
`RtlSignal .proverCore` registers for every in-width trace of arbitrary length. -/
theorem ospc_fabulous_bitstream_refines_slice
    (tr : List (Bool × (Nat → BitVec 64))) (regs : Nat → BitVec 64)
    (hRegs : RegsFit ospcFabricSliceRtl regs)
    (hIn : ∀ c ∈ tr, InputsFit ospcFabricSliceRtl c) :
    decodeAndExtractFabulous ospcKernelFabric ospcFabricPins ospcFabulousBitstream =
      .ok ospcExtractedNet ∧
    ospcExtractedNet.run (projOf ospcFabricFlopMap regs) (tr.map (pinValues ospcFabricPins)) =
      ((moduleRun ospcFabricSliceRtl regs tr).1.map fun outs =>
          ospcExtractedNet.outs.map fun (p, _) => (p, outPinValue ospcFabricPins outs p),
       projOf ospcFabricFlopMap (runModuleTrace ospcFabricSliceRtl regs tr)) :=
  ⟨ospc_fabulous_decode_extract_ok,
   fabric_realizes_module ospcExtractedNet ospcFabricSliceRtl ospcFabricPins
     (projOf ospcFabricFlopMap) ospcFabricSliceRtl_wellFormed.2.2
     ospcExtractedNet_step_realizes tr regs hRegs hIn⟩

/-! ## 4. Isolated `obend-hw-dpi` Binary Frame Protocol & Deterministic DPI Server -/

/-- Domain separator for the isolated `obend-hw-dpi` framing protocol (mirrored in `crates/obend-hw-dpi`). -/
def OSPC_HW_DPI_DOMAIN : String := "OBEND.OSPC.HW.DPI/v1"

/-- Canonical 4-byte frame magic `"ODPI"`. -/
def ODPI_MAGIC : List UInt8 := [0x4F, 0x44, 0x50, 0x49]

/-- Canonical frame protocol version byte `1`. -/
def ODPI_VERSION : UInt8 := 0x01

/-- Canonical message kind tags (`StepCycleReq = 0x01`, `StepCycleResp = 0x81`). -/
def ODPI_KIND_STEP_REQ  : UInt8 := 0x01
def ODPI_KIND_STEP_RESP : UInt8 := 0x81

/-- Exact fixed payload lengths (`78` bytes for request, `75` bytes for response; header = `12` bytes). -/
def ODPI_HEADER_LEN       : Nat := 12
def ODPI_REQ_PAYLOAD_LEN  : Nat := 78
def ODPI_RESP_PAYLOAD_LEN : Nat := 75

/-- Refusal error clauses for the isolated `obend-hw-dpi` binary protocol and cycle server. -/
inductive OspcDpiError where
  | badMagic
  | badVersion
  | badDomainTag
  | badMsgKind
  | badFlags
  | lengthMismatch
  | nonCanonicalField
  | domainViolation
  | sequenceMismatch
  | deltaNetLinearityViolation
  deriving DecidableEq, Repr

/-- Host-to-hardware isolated DPI request frame carrying one cycle of fixed-width inputs for all 4 tiles. -/
structure OspcDpiReq where
  domain           : ClockDomain
  seqNo            : BitVec 32
  rst              : Bool
  tile0OpSel       : BitVec 2
  tile0InLo64      : BitVec 64
  tile0InHi17      : BitVec 17
  tile0CamWe       : BitVec 1
  tile0CamAddr     : BitVec 8
  tile0CamWdata    : BitVec 64
  tile0CamQtag     : BitVec 64
  tile1StepEn      : BitVec 1
  tile1SymTag      : BitVec 6
  tile1LutWe       : BitVec 1
  tile1LutWaddr    : BitVec 12
  tile1LutWdata    : BitVec 64
  tile2RedexEn     : BitVec 1
  tile2PeerWord    : BitVec 64
  tile2PortWe      : BitVec 1
  tile2PortAddr    : BitVec 8
  tile2PortWdata   : BitVec 64
  tile3StepEn      : BitVec 1
  tile3ClauseWe    : BitVec 1
  tile3ClauseAddr  : BitVec 8
  tile3ClauseWdata : BitVec 64
  deriving DecidableEq, Repr

/-- Extract the 64-bit port environment for tile `t : Fin 4` from an `OspcDpiReq`. -/
def OspcDpiReq.inputsFor (req : OspcDpiReq) : Fin 4 → (Nat → BitVec 64)
  | ⟨0, _⟩ => fun
      | 0 => req.tile0OpSel.setWidth 64
      | 1 => req.tile0InLo64
      | 2 => req.tile0InHi17.setWidth 64
      | 3 => req.tile0CamWe.setWidth 64
      | 4 => req.tile0CamAddr.setWidth 64
      | 5 => req.tile0CamWdata
      | 6 => req.tile0CamQtag
      | _ => 0#64
  | ⟨1, _⟩ => fun
      | 0 => req.tile1StepEn.setWidth 64
      | 1 => req.tile1SymTag.setWidth 64
      | 2 => req.tile1LutWe.setWidth 64
      | 3 => req.tile1LutWaddr.setWidth 64
      | 4 => req.tile1LutWdata
      | _ => 0#64
  | ⟨2, _⟩ => fun
      | 0 => req.tile2RedexEn.setWidth 64
      | 1 => req.tile2PeerWord
      | 2 => req.tile2PortWe.setWidth 64
      | 3 => req.tile2PortAddr.setWidth 64
      | 4 => req.tile2PortWdata
      | _ => 0#64
  | ⟨3, _⟩ => fun
      | 0 => req.tile3StepEn.setWidth 64
      | 1 => req.tile3ClauseWe.setWidth 64
      | 2 => req.tile3ClauseAddr.setWidth 64
      | 3 => req.tile3ClauseWdata
      | _ => 0#64

/-- Hardware-to-host isolated DPI response frame carrying post-cycle register observables and 256-bit receipt. -/
structure OspcDpiResp where
  domain          : ClockDomain
  seqNo           : BitVec 32
  cycleCount      : BitVec 32
  tile0FaceLo64   : BitVec 64
  tile0FaceHi17   : BitVec 17
  tile0Entails    : BitVec 1
  tile0CamHit     : BitVec 1
  tile1TrieState  : BitVec 6
  tile1LogupHits  : BitVec 32
  tile1HitValid   : BitVec 1
  tile2RedexValid : BitVec 1
  tile2RedexCount : BitVec 32
  tile2LinearOk   : BitVec 1
  tile3Conflict   : BitVec 1
  tile3AssignPos  : BitVec 32
  tile3AssignNeg  : BitVec 32
  receiptLimb0    : BitVec 64
  receiptLimb1    : BitVec 64
  receiptLimb2    : BitVec 64
  receiptLimb3    : BitVec 64
  deriving DecidableEq, Repr

/-! ### Big-Endian Canonical Wire Primitive Encoders & Decoders -/

private def encU8 (x : UInt8) : List UInt8 := [x]

private def encBe16 (n : Nat) : List UInt8 :=
  [UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)]

private def encBe32 (n : Nat) : List UInt8 :=
  [ UInt8.ofNat ((n >>> 24) &&& 0xFF), UInt8.ofNat ((n >>> 16) &&& 0xFF)
  , UInt8.ofNat ((n >>> 8) &&& 0xFF),  UInt8.ofNat (n &&& 0xFF) ]

private def encBe64 (n : Nat) : List UInt8 :=
  [ UInt8.ofNat ((n >>> 56) &&& 0xFF), UInt8.ofNat ((n >>> 48) &&& 0xFF)
  , UInt8.ofNat ((n >>> 40) &&& 0xFF), UInt8.ofNat ((n >>> 32) &&& 0xFF)
  , UInt8.ofNat ((n >>> 24) &&& 0xFF), UInt8.ofNat ((n >>> 16) &&& 0xFF)
  , UInt8.ofNat ((n >>> 8) &&& 0xFF),  UInt8.ofNat (n &&& 0xFF) ]

private theorem encU8_len (x : UInt8) : (encU8 x).length = 1 := rfl
private theorem encBe16_len (n : Nat) : (encBe16 n).length = 2 := rfl
private theorem encBe32_len (n : Nat) : (encBe32 n).length = 4 := rfl
private theorem encBe64_len (n : Nat) : (encBe64 n).length = 8 := rfl

private def decU8 : List UInt8 → Except OspcDpiError (UInt8 × List UInt8)
  | b :: rest => .ok (b, rest)
  | []        => .error .lengthMismatch

private def decBe16 : List UInt8 → Except OspcDpiError (Nat × List UInt8)
  | b0 :: b1 :: rest => .ok (b0.toNat * 256 + b1.toNat, rest)
  | _                => .error .lengthMismatch

private def decBe32 : List UInt8 → Except OspcDpiError (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
    .ok (b0.toNat * 2^24 + b1.toNat * 2^16 + b2.toNat * 2^8 + b3.toNat, rest)
  | _ => .error .lengthMismatch

private def decBe64 : List UInt8 → Except OspcDpiError (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    .ok (b0.toNat * 2^56 + b1.toNat * 2^48 + b2.toNat * 2^40 + b3.toNat * 2^32 +
         b4.toNat * 2^24 + b5.toNat * 2^16 + b6.toNat * 2^8 + b7.toNat, rest)
  | _ => .error .lengthMismatch

private def decBvSmall (w : Nat) (bs : List UInt8) : Except OspcDpiError (BitVec w × List UInt8) := do
  let (b, rest) ← decU8 bs
  if b.toNat < 2 ^ w then .ok (BitVec.ofNat w b.toNat, rest)
  else .error .nonCanonicalField

private def decBv12 (bs : List UInt8) : Except OspcDpiError (BitVec 12 × List UInt8) := do
  let (n, rest) ← decBe16 bs
  if n < 2 ^ 12 then .ok (BitVec.ofNat 12 n, rest)
  else .error .nonCanonicalField

private def decBvBe32 (w : Nat) (bs : List UInt8) : Except OspcDpiError (BitVec w × List UInt8) := do
  let (n, rest) ← decBe32 bs
  if n < 2 ^ w then .ok (BitVec.ofNat w n, rest)
  else .error .nonCanonicalField

private def decBv17 (bs : List UInt8) : Except OspcDpiError (BitVec 17 × List UInt8) :=
  decBvBe32 17 bs

private def decBv32 (bs : List UInt8) : Except OspcDpiError (BitVec 32 × List UInt8) := do
  let (n, rest) ← decBe32 bs
  .ok (BitVec.ofNat 32 n, rest)

private def decBv64 (bs : List UInt8) : Except OspcDpiError (BitVec 64 × List UInt8) := do
  let (n, rest) ← decBe64 bs
  .ok (BitVec.ofNat 64 n, rest)

private theorem nat_and_255 (n : Nat) : n &&& 255 = n % 256 := by
  have h : 255 = 2 ^ 8 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

private theorem uint8_ofNat_toNat_eq_mod (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat]

private theorem uint8_ofNat_toNat_and (n : Nat) : (UInt8.ofNat (n &&& 0xFF)).toNat = n % 256 := by
  rw [uint8_ofNat_toNat_eq_mod, nat_and_255, Nat.mod_mod]

private theorem decBe16_encBe16 (n : Nat) (hn : n < 2 ^ 16) (tail : List UInt8) :
    decBe16 (encBe16 n ++ tail) = .ok (n, tail) := by
  simp only [encBe16, List.cons_append, List.nil_append, decBe16, uint8_ofNat_toNat_and,
    Nat.shiftRight_eq_div_pow]
  exact congrArg Except.ok (Prod.ext (by omega) rfl)

private theorem decBe32_encBe32 (n : Nat) (hn : n < 2 ^ 32) (tail : List UInt8) :
    decBe32 (encBe32 n ++ tail) = .ok (n, tail) := by
  simp only [encBe32, List.cons_append, List.nil_append, decBe32, uint8_ofNat_toNat_and,
    Nat.shiftRight_eq_div_pow]
  exact congrArg Except.ok (Prod.ext (by omega) rfl)

private theorem decBe64_encBe64 (n : Nat) (hn : n < 2 ^ 64) (tail : List UInt8) :
    decBe64 (encBe64 n ++ tail) = .ok (n, tail) := by
  simp only [encBe64, List.cons_append, List.nil_append, decBe64, uint8_ofNat_toNat_and,
    Nat.shiftRight_eq_div_pow]
  exact congrArg Except.ok (Prod.ext (by omega) rfl)

private theorem decBvSmall_enc {w : Nat} (hw : w ≤ 8) (v : BitVec w) (tail : List UInt8) :
    decBvSmall w (encU8 (UInt8.ofNat v.toNat) ++ tail) = .ok (v, tail) := by
  have hlt256 : v.toNat < 256 :=
    Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp only [encU8, List.cons_append, List.nil_append, decBvSmall, decU8, bind, Except.bind,
    uint8_ofNat_toNat_eq_mod, Nat.mod_eq_of_lt hlt256, v.isLt, ↓reduceIte,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decBv1_enc (v : BitVec 1) (tail : List UInt8) :
    decBvSmall 1 (encU8 (UInt8.ofNat v.toNat) ++ tail) = .ok (v, tail) :=
  decBvSmall_enc (by decide) v tail

private theorem decBv2_enc (v : BitVec 2) (tail : List UInt8) :
    decBvSmall 2 (encU8 (UInt8.ofNat v.toNat) ++ tail) = .ok (v, tail) :=
  decBvSmall_enc (by decide) v tail

private theorem decBv6_enc (v : BitVec 6) (tail : List UInt8) :
    decBvSmall 6 (encU8 (UInt8.ofNat v.toNat) ++ tail) = .ok (v, tail) :=
  decBvSmall_enc (by decide) v tail

private theorem decBv8_enc (v : BitVec 8) (tail : List UInt8) :
    decBvSmall 8 (encU8 (UInt8.ofNat v.toNat) ++ tail) = .ok (v, tail) :=
  decBvSmall_enc (by decide) v tail

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem decBv12_enc (v : BitVec 12) (tail : List UInt8) :
    decBv12 (encBe16 v.toNat ++ tail) = .ok (v, tail) := by
  have hlt : v.toNat < 2 ^ 16 :=
    Nat.lt_trans v.isLt (Nat.pow_lt_pow_right (by decide) (by decide))
  unfold decBv12
  rw [decBe16_encBe16 v.toNat hlt tail, except_bind_ok]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true v.isLt), BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decBvBe32_enc {w : Nat} (hw : w ≤ 32) (v : BitVec w) (tail : List UInt8) :
    decBvBe32 w (encBe32 v.toNat ++ tail) = .ok (v, tail) := by
  have hlt : v.toNat < 2 ^ 32 :=
    Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hw)
  unfold decBvBe32
  rw [decBe32_encBe32 v.toNat hlt tail, except_bind_ok]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true v.isLt), BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decBv17_enc (v : BitVec 17) (tail : List UInt8) :
    decBv17 (encBe32 v.toNat ++ tail) = .ok (v, tail) :=
  decBvBe32_enc (by decide) v tail

private theorem decBv32_enc (v : BitVec 32) (tail : List UInt8) :
    decBv32 (encBe32 v.toNat ++ tail) = .ok (v, tail) := by
  simp only [decBv32, bind, Except.bind, decBe32_encBe32 v.toNat v.isLt tail,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decBv64_enc (v : BitVec 64) (tail : List UInt8) :
    decBv64 (encBe64 v.toNat ++ tail) = .ok (v, tail) := by
  simp only [decBv64, bind, Except.bind, decBe64_encBe64 v.toNat v.isLt tail,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decBe32_78 (tail : List UInt8) :
    decBe32 (encBe32 ODPI_REQ_PAYLOAD_LEN ++ tail) = .ok (ODPI_REQ_PAYLOAD_LEN, tail) :=
  decBe32_encBe32 ODPI_REQ_PAYLOAD_LEN (by unfold ODPI_REQ_PAYLOAD_LEN; omega) tail

private theorem decBe32_75 (tail : List UInt8) :
    decBe32 (encBe32 ODPI_RESP_PAYLOAD_LEN ++ tail) = .ok (ODPI_RESP_PAYLOAD_LEN, tail) :=
  decBe32_encBe32 ODPI_RESP_PAYLOAD_LEN (by unfold ODPI_RESP_PAYLOAD_LEN; omega) tail

/-- Encode `OspcDpiReq` to its canonical 90-byte length-framed `"ODPI"` v1 byte list. -/
def encodeOspcDpiReqList (req : OspcDpiReq) : List UInt8 :=
  ODPI_MAGIC ++
  [ODPI_VERSION, req.domain.toTag, ODPI_KIND_STEP_REQ, if req.rst then 1 else 0] ++
  encBe32 ODPI_REQ_PAYLOAD_LEN ++
  encBe32 req.seqNo.toNat ++
  encU8 (UInt8.ofNat req.tile0OpSel.toNat) ++
  encBe64 req.tile0InLo64.toNat ++
  encBe32 req.tile0InHi17.toNat ++
  encU8 (UInt8.ofNat req.tile0CamWe.toNat) ++
  encU8 (UInt8.ofNat req.tile0CamAddr.toNat) ++
  encBe64 req.tile0CamWdata.toNat ++
  encBe64 req.tile0CamQtag.toNat ++
  encU8 (UInt8.ofNat req.tile1StepEn.toNat) ++
  encU8 (UInt8.ofNat req.tile1SymTag.toNat) ++
  encU8 (UInt8.ofNat req.tile1LutWe.toNat) ++
  encBe16 req.tile1LutWaddr.toNat ++
  encBe64 req.tile1LutWdata.toNat ++
  encU8 (UInt8.ofNat req.tile2RedexEn.toNat) ++
  encBe64 req.tile2PeerWord.toNat ++
  encU8 (UInt8.ofNat req.tile2PortWe.toNat) ++
  encU8 (UInt8.ofNat req.tile2PortAddr.toNat) ++
  encBe64 req.tile2PortWdata.toNat ++
  encU8 (UInt8.ofNat req.tile3StepEn.toNat) ++
  encU8 (UInt8.ofNat req.tile3ClauseWe.toNat) ++
  encU8 (UInt8.ofNat req.tile3ClauseAddr.toNat) ++
  encBe64 req.tile3ClauseWdata.toNat

/-- Decode a canonical 90-byte `"ODPI"` v1 `OspcDpiReq` frame, returning the decoded request and
any trailing bytes (enabling prefix-free stream framing). -/
def decodeOspcDpiReqPrefix (bs : List UInt8) : Except OspcDpiError (OspcDpiReq × List UInt8) := do
  match bs with
  | m0 :: m1 :: m2 :: m3 :: ver :: domB :: kind :: flags :: rest0 =>
    if [m0, m1, m2, m3] != ODPI_MAGIC then .error .badMagic
    else if ver != ODPI_VERSION then .error .badVersion
    else match ClockDomain.ofTag? domB with
      | none => .error .badDomainTag
      | some dom =>
        if kind != ODPI_KIND_STEP_REQ then .error .badMsgKind
        else if flags != 0 && flags != 1 then .error .badFlags
        else do
          let (pLen, r0) ← decBe32 rest0
          if pLen != ODPI_REQ_PAYLOAD_LEN then .error .lengthMismatch
          else do
            let (seqNo, r1)             ← decBv32 r0
            let (tile0OpSel, r2)        ← decBvSmall 2 r1
            let (tile0InLo64, r3)       ← decBv64 r2
            let (tile0InHi17, r4)       ← decBv17 r3
            let (tile0CamWe, r5)        ← decBvSmall 1 r4
            let (tile0CamAddr, r6)      ← decBvSmall 8 r5
            let (tile0CamWdata, r7)     ← decBv64 r6
            let (tile0CamQtag, r8)      ← decBv64 r7
            let (tile1StepEn, r9)       ← decBvSmall 1 r8
            let (tile1SymTag, r10)      ← decBvSmall 6 r9
            let (tile1LutWe, r11)       ← decBvSmall 1 r10
            let (tile1LutWaddr, r12)    ← decBv12 r11
            let (tile1LutWdata, r13)    ← decBv64 r12
            let (tile2RedexEn, r14)     ← decBvSmall 1 r13
            let (tile2PeerWord, r15)    ← decBv64 r14
            let (tile2PortWe, r16)      ← decBvSmall 1 r15
            let (tile2PortAddr, r17)    ← decBvSmall 8 r16
            let (tile2PortWdata, r18)   ← decBv64 r17
            let (tile3StepEn, r19)      ← decBvSmall 1 r18
            let (tile3ClauseWe, r20)    ← decBvSmall 1 r19
            let (tile3ClauseAddr, r21)  ← decBvSmall 8 r20
            let (tile3ClauseWdata, r22) ← decBv64 r21
            .ok ({ domain := dom, seqNo, rst := (flags == 1)
                 , tile0OpSel, tile0InLo64, tile0InHi17, tile0CamWe, tile0CamAddr, tile0CamWdata, tile0CamQtag
                 , tile1StepEn, tile1SymTag, tile1LutWe, tile1LutWaddr, tile1LutWdata
                 , tile2RedexEn, tile2PeerWord, tile2PortWe, tile2PortAddr, tile2PortWdata
                 , tile3StepEn, tile3ClauseWe, tile3ClauseAddr, tile3ClauseWdata }, r22)
  | _ => .error .lengthMismatch

/-- Encode `OspcDpiReq` to a `ByteArray` (exact length `90`). -/
def encodeOspcDpiReq (req : OspcDpiReq) : ByteArray :=
  ByteArray.mk (encodeOspcDpiReqList req).toArray

/-- Decode a single exact-length `ByteArray` frame into `OspcDpiReq` (refuses trailing bytes). -/
def decodeOspcDpiReq (b : ByteArray) : Except OspcDpiError OspcDpiReq := do
  let (req, tail) ← decodeOspcDpiReqPrefix b.data.toList
  if tail.isEmpty then .ok req else .error .lengthMismatch

/-- Encode `OspcDpiResp` to its canonical 87-byte length-framed `"ODPI"` v1 byte list. -/
def encodeOspcDpiRespList (resp : OspcDpiResp) : List UInt8 :=
  ODPI_MAGIC ++
  [ODPI_VERSION, resp.domain.toTag, ODPI_KIND_STEP_RESP, 0x00] ++
  encBe32 ODPI_RESP_PAYLOAD_LEN ++
  encBe32 resp.seqNo.toNat ++
  encBe32 resp.cycleCount.toNat ++
  encBe64 resp.tile0FaceLo64.toNat ++
  encBe32 resp.tile0FaceHi17.toNat ++
  encU8 (UInt8.ofNat resp.tile0Entails.toNat) ++
  encU8 (UInt8.ofNat resp.tile0CamHit.toNat) ++
  encU8 (UInt8.ofNat resp.tile1TrieState.toNat) ++
  encBe32 resp.tile1LogupHits.toNat ++
  encU8 (UInt8.ofNat resp.tile1HitValid.toNat) ++
  encU8 (UInt8.ofNat resp.tile2RedexValid.toNat) ++
  encBe32 resp.tile2RedexCount.toNat ++
  encU8 (UInt8.ofNat resp.tile2LinearOk.toNat) ++
  encU8 (UInt8.ofNat resp.tile3Conflict.toNat) ++
  encBe32 resp.tile3AssignPos.toNat ++
  encBe32 resp.tile3AssignNeg.toNat ++
  encBe64 resp.receiptLimb0.toNat ++
  encBe64 resp.receiptLimb1.toNat ++
  encBe64 resp.receiptLimb2.toNat ++
  encBe64 resp.receiptLimb3.toNat

/-- Decode a canonical 87-byte `"ODPI"` v1 `OspcDpiResp` frame with trailing remainder. -/
def decodeOspcDpiRespPrefix (bs : List UInt8) : Except OspcDpiError (OspcDpiResp × List UInt8) := do
  match bs with
  | m0 :: m1 :: m2 :: m3 :: ver :: domB :: kind :: flags :: rest0 =>
    if [m0, m1, m2, m3] != ODPI_MAGIC then .error .badMagic
    else if ver != ODPI_VERSION then .error .badVersion
    else match ClockDomain.ofTag? domB with
      | none => .error .badDomainTag
      | some dom =>
        if kind != ODPI_KIND_STEP_RESP then .error .badMsgKind
        else if flags != 0 then .error .badFlags
        else do
          let (pLen, r0) ← decBe32 rest0
          if pLen != ODPI_RESP_PAYLOAD_LEN then .error .lengthMismatch
          else do
            let (seqNo, r1)            ← decBv32 r0
            let (cycleCount, r2)       ← decBv32 r1
            let (tile0FaceLo64, r3)    ← decBv64 r2
            let (tile0FaceHi17, r4)    ← decBv17 r3
            let (tile0Entails, r5)     ← decBvSmall 1 r4
            let (tile0CamHit, r6)      ← decBvSmall 1 r5
            let (tile1TrieState, r7)   ← decBvSmall 6 r6
            let (tile1LogupHits, r8)   ← decBv32 r7
            let (tile1HitValid, r9)    ← decBvSmall 1 r8
            let (tile2RedexValid, r10) ← decBvSmall 1 r9
            let (tile2RedexCount, r11) ← decBv32 r10
            let (tile2LinearOk, r12)   ← decBvSmall 1 r11
            let (tile3Conflict, r13)   ← decBvSmall 1 r12
            let (tile3AssignPos, r14)  ← decBv32 r13
            let (tile3AssignNeg, r15)  ← decBv32 r14
            let (receiptLimb0, r16)    ← decBv64 r15
            let (receiptLimb1, r17)    ← decBv64 r16
            let (receiptLimb2, r18)    ← decBv64 r17
            let (receiptLimb3, r19)    ← decBv64 r18
            .ok ({ domain := dom, seqNo, cycleCount
                 , tile0FaceLo64, tile0FaceHi17, tile0Entails, tile0CamHit
                 , tile1TrieState, tile1LogupHits, tile1HitValid
                 , tile2RedexValid, tile2RedexCount, tile2LinearOk
                 , tile3Conflict, tile3AssignPos, tile3AssignNeg
                 , receiptLimb0, receiptLimb1, receiptLimb2, receiptLimb3 }, r19)
  | _ => .error .lengthMismatch

/-- Encode `OspcDpiResp` to a `ByteArray` (exact length `87`). -/
def encodeOspcDpiResp (resp : OspcDpiResp) : ByteArray :=
  ByteArray.mk (encodeOspcDpiRespList resp).toArray

/-- Decode a single exact-length `ByteArray` frame into `OspcDpiResp` (refuses trailing bytes). -/
def decodeOspcDpiResp (b : ByteArray) : Except OspcDpiError OspcDpiResp := do
  let (resp, tail) ← decodeOspcDpiRespPrefix b.data.toList
  if tail.isEmpty then .ok resp else .error .lengthMismatch

private theorem encodeOspcDpiReqList_length (req : OspcDpiReq) :
    (encodeOspcDpiReqList req).length = ODPI_HEADER_LEN + ODPI_REQ_PAYLOAD_LEN := by
  unfold encodeOspcDpiReqList ODPI_MAGIC ODPI_HEADER_LEN ODPI_REQ_PAYLOAD_LEN
  repeat rw [List.length_append]
  simp only [List.length_cons, List.length_nil, encU8_len, encBe16_len, encBe32_len, encBe64_len]

theorem encodeOspcDpiReq_size (req : OspcDpiReq) :
    (encodeOspcDpiReq req).size = ODPI_HEADER_LEN + ODPI_REQ_PAYLOAD_LEN := by
  change (encodeOspcDpiReqList req).toArray.size = _
  rw [List.size_toArray, encodeOspcDpiReqList_length]

private theorem encodeOspcDpiRespList_length (resp : OspcDpiResp) :
    (encodeOspcDpiRespList resp).length = ODPI_HEADER_LEN + ODPI_RESP_PAYLOAD_LEN := by
  unfold encodeOspcDpiRespList ODPI_MAGIC ODPI_HEADER_LEN ODPI_RESP_PAYLOAD_LEN
  repeat rw [List.length_append]
  simp only [List.length_cons, List.length_nil, encU8_len, encBe32_len, encBe64_len]

theorem encodeOspcDpiResp_size (resp : OspcDpiResp) :
    (encodeOspcDpiResp resp).size = ODPI_HEADER_LEN + ODPI_RESP_PAYLOAD_LEN := by
  change (encodeOspcDpiRespList resp).toArray.size = _
  rw [List.size_toArray, encodeOspcDpiRespList_length]

/-- **Prefix-Free Request Codec Round-Trip**: decoding `encodeOspcDpiReqList req ++ tail` recovers
`(req, tail)` for EVERY `req` and EVERY trailing byte sequence `tail`. -/
theorem decodeOspcDpiReqPrefix_encode (req : OspcDpiReq) (tail : List UInt8) :
    decodeOspcDpiReqPrefix (encodeOspcDpiReqList req ++ tail) = .ok (req, tail) := by
  rcases req with ⟨dom, seqNo, rst, t0op, t0lo, t0hi, t0we, t0a, t0wd, t0q,
    t1en, t1st, t1we, t1wa, t1wd, t2en, t2p, t2we, t2a, t2wd, t3en, t3we, t3a, t3wd⟩
  have hFlagsOk : ((if rst then (1 : UInt8) else 0) != 0 && (if rst then (1 : UInt8) else 0) != 1) = false := by
    cases rst <;> decide
  have hRstEq : ((if rst then (1 : UInt8) else 0) == 1) = rst := by cases rst <;> decide
  unfold encodeOspcDpiReqList
  repeat rw [List.append_assoc]
  unfold ODPI_MAGIC
  simp only [List.cons_append, List.nil_append]
  unfold decodeOspcDpiReqPrefix
  dsimp only
  simp only [show ([0x4F, 0x44, 0x50, 0x49] != ODPI_MAGIC) = false by rfl,
      show (ODPI_VERSION != ODPI_VERSION) = false by rfl,
      ClockDomain.ofTag?_toTag,
      show (ODPI_KIND_STEP_REQ != ODPI_KIND_STEP_REQ) = false by rfl,
      hFlagsOk, Bool.false_eq_true, ↓reduceIte]
  rw [decBe32_78, except_bind_ok]; dsimp only
  simp only [show (ODPI_REQ_PAYLOAD_LEN != ODPI_REQ_PAYLOAD_LEN) = false by rfl,
      Bool.false_eq_true, ↓reduceIte]
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv2_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv17_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv8_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv6_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv12_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv8_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv8_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [hRstEq]

/-- **Exact Request `ByteArray` Round-Trip**: `decodeOspcDpiReq (encodeOspcDpiReq req) = .ok req`. -/
theorem decodeOspcDpiReq_encodeOspcDpiReq (req : OspcDpiReq) :
    decodeOspcDpiReq (encodeOspcDpiReq req) = .ok req := by
  unfold decodeOspcDpiReq encodeOspcDpiReq
  have h : (ByteArray.mk (encodeOspcDpiReqList req).toArray).data.toList =
      encodeOspcDpiReqList req ++ [] := by simp
  rw [h, decodeOspcDpiReqPrefix_encode]
  rfl

/-- **Prefix-Free Request Injectivity**: no valid encoded request is a strict prefix of another. -/
theorem encodeOspcDpiReq_prefix_free {r₁ r₂ : OspcDpiReq} {t₁ t₂ : List UInt8}
    (h : encodeOspcDpiReqList r₁ ++ t₁ = encodeOspcDpiReqList r₂ ++ t₂) :
    r₁ = r₂ ∧ t₁ = t₂ := by
  have hd := congrArg decodeOspcDpiReqPrefix h
  rw [decodeOspcDpiReqPrefix_encode, decodeOspcDpiReqPrefix_encode] at hd
  cases hd; exact ⟨rfl, rfl⟩

/-- **Prefix-Free Response Codec Round-Trip**: decoding `encodeOspcDpiRespList resp ++ tail`
recovers `(resp, tail)` for EVERY `resp` and EVERY trailing byte sequence `tail`. -/
theorem decodeOspcDpiRespPrefix_encode (resp : OspcDpiResp) (tail : List UInt8) :
    decodeOspcDpiRespPrefix (encodeOspcDpiRespList resp ++ tail) = .ok (resp, tail) := by
  rcases resp with ⟨dom, seqNo, cyc, fLo, fHi, ent, hit, ts, lh, hv, rv, rc, lok, conf, ap, an,
    l0, l1, l2, l3⟩
  unfold encodeOspcDpiRespList
  repeat rw [List.append_assoc]
  unfold ODPI_MAGIC
  simp only [List.cons_append, List.nil_append]
  unfold decodeOspcDpiRespPrefix
  dsimp only
  simp only [show ([0x4F, 0x44, 0x50, 0x49] != ODPI_MAGIC) = false by rfl,
      show (ODPI_VERSION != ODPI_VERSION) = false by rfl,
      ClockDomain.ofTag?_toTag,
      show (ODPI_KIND_STEP_RESP != ODPI_KIND_STEP_RESP) = false by rfl,
      show ((0x00 : UInt8) != 0) = false by rfl,
      Bool.false_eq_true, ↓reduceIte]
  rw [decBe32_75, except_bind_ok]; dsimp only
  simp only [show (ODPI_RESP_PAYLOAD_LEN != ODPI_RESP_PAYLOAD_LEN) = false by rfl,
      Bool.false_eq_true, ↓reduceIte]
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv17_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv6_enc, except_bind_ok]; dsimp only
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv1_enc, except_bind_ok]; dsimp only
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv32_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]; dsimp only
  rw [decBv64_enc, except_bind_ok]

/-- **Exact Response `ByteArray` Round-Trip**: `decodeOspcDpiResp (encodeOspcDpiResp resp) = .ok resp`. -/
theorem decodeOspcDpiResp_encodeOspcDpiResp (resp : OspcDpiResp) :
    decodeOspcDpiResp (encodeOspcDpiResp resp) = .ok resp := by
  unfold decodeOspcDpiResp encodeOspcDpiResp
  have h : (ByteArray.mk (encodeOspcDpiRespList resp).toArray).data.toList =
      encodeOspcDpiRespList resp ++ [] := by simp
  rw [h, decodeOspcDpiRespPrefix_encode]
  rfl

/-- **Refusal Theorems for Malformed DPI Frames**: truncated frames and frames with trailing garbage
bytes are unconditionally refused with `.lengthMismatch`. -/
theorem decodeOspcDpiReq_refuses_empty :
    decodeOspcDpiReq ByteArray.empty = .error .lengthMismatch := by rfl

theorem decodeOspcDpiReq_refuses_trailing_byte (req : OspcDpiReq) (extra : UInt8) :
    decodeOspcDpiReq (ByteArray.mk (encodeOspcDpiReqList req ++ [extra]).toArray) =
      .error .lengthMismatch := by
  unfold decodeOspcDpiReq
  have h : (ByteArray.mk (encodeOspcDpiReqList req ++ [extra]).toArray).data.toList =
      encodeOspcDpiReqList req ++ [extra] := by simp
  rw [h, decodeOspcDpiReqPrefix_encode]
  rfl

/-! ### Deterministic Isolated `obend-hw-dpi` Cycle Server & Refinement -/

/-- State of the isolated `obend-hw-dpi` 4-tile cycle server. -/
structure OspcDpiServerState where
  tiles          : Fin 4 → MemState
  expectedSeq    : BitVec 32
  cycleCount     : BitVec 32
  lastReceipt256 : BitVec 256

/-- Extract the post-cycle observable response from updated 4-tile `MemState`s, pre-edge outputs,
and 256-bit receipt limbs. -/
def buildOspcDpiResp
    (tileMod : Fin 4 → RtlMemModule) (req : OspcDpiReq) (cycleCount : BitVec 32)
    (tilesBefore tilesAfter : Fin 4 → MemState) (receipt256 : BitVec 256) : OspcDpiResp :=
  let out0 := evalMemModuleOutputs (tileMod ⟨0, by omega⟩) (req.inputsFor ⟨0, by omega⟩) (tilesBefore ⟨0, by omega⟩)
  let out1 := evalMemModuleOutputs (tileMod ⟨1, by omega⟩) (req.inputsFor ⟨1, by omega⟩) (tilesBefore ⟨1, by omega⟩)
  let out2 := evalMemModuleOutputs (tileMod ⟨2, by omega⟩) (req.inputsFor ⟨2, by omega⟩) (tilesBefore ⟨2, by omega⟩)
  { domain          := .hostDpi
  , seqNo           := req.seqNo
  , cycleCount      := cycleCount
  , tile0FaceLo64   := (tilesAfter ⟨0, by omega⟩).regs 0
  , tile0FaceHi17   := ((tilesAfter ⟨0, by omega⟩).regs 1).extractLsb' 0 17
  , tile0Entails    := (out0.lookup "out_entails" |>.getD 0#64).extractLsb' 0 1
  , tile0CamHit     := (out0.lookup "out_cam_hit" |>.getD 0#64).extractLsb' 0 1
  , tile1TrieState  := ((tilesAfter ⟨1, by omega⟩).regs 0).extractLsb' 0 6
  , tile1LogupHits  := ((tilesAfter ⟨1, by omega⟩).regs 1).extractLsb' 0 32
  , tile1HitValid   := (out1.lookup "out_hit_valid" |>.getD 0#64).extractLsb' 0 1
  , tile2RedexValid := (out2.lookup "out_redex_valid" |>.getD 0#64).extractLsb' 0 1
  , tile2RedexCount := ((tilesAfter ⟨2, by omega⟩).regs 0).extractLsb' 0 32
  , tile2LinearOk   := ((tilesAfter ⟨2, by omega⟩).regs 1).extractLsb' 0 1
  , tile3Conflict   := ((tilesAfter ⟨3, by omega⟩).regs 2).extractLsb' 0 1
  , tile3AssignPos  := ((tilesAfter ⟨3, by omega⟩).regs 0).extractLsb' 0 32
  , tile3AssignNeg  := ((tilesAfter ⟨3, by omega⟩).regs 1).extractLsb' 0 32
  , receiptLimb0    := receipt256.extractLsb' 192 64
  , receiptLimb1    := receipt256.extractLsb' 128 64
  , receiptLimb2    := receipt256.extractLsb' 64 64
  , receiptLimb3    := receipt256.extractLsb' 0 64 }

/-- Deterministic single-cycle step of the isolated `obend-hw-dpi` server. -/
def stepOspcDpiServer
    (tileMod : Fin 4 → RtlMemModule)
    (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st : OspcDpiServerState) (rawReq : ByteArray) :
    Except OspcDpiError (OspcDpiServerState × ByteArray) := do
  let req ← decodeOspcDpiReq rawReq
  if req.domain != .hostDpi then .error .domainViolation
  else if req.seqNo != st.expectedSeq then .error .sequenceMismatch
  else
    let tiles' : Fin 4 → MemState :=
      fun t => stepMemModule (tileMod t) req.rst (req.inputsFor t) (st.tiles t)
    if (tiles' ⟨2, by omega⟩).regs 1 != 1#64 then .error .deltaNetLinearityViolation
    else
      let cyc' := st.cycleCount + 1#32
      let rec256 := computeRec tiles'
      let resp := buildOspcDpiResp tileMod req cyc' st.tiles tiles' rec256
      let st' : OspcDpiServerState :=
        { tiles := tiles', expectedSeq := st.expectedSeq + 1#32, cycleCount := cyc', lastReceipt256 := rec256 }
      .ok (st', encodeOspcDpiResp resp)

/-- Multi-cycle DPI server trace execution over a list of raw request frames. -/
def runOspcDpiServerTrace
    (tileMod : Fin 4 → RtlMemModule)
    (computeRec : (Fin 4 → MemState) → BitVec 256) :
    OspcDpiServerState → List ByteArray → Except OspcDpiError (OspcDpiServerState × List ByteArray)
  | st, [] => .ok (st, [])
  | st, raw :: rest => do
    let (stMid, resp) ← stepOspcDpiServer tileMod computeRec st raw
    let (stEnd, resps) ← runOspcDpiServerTrace tileMod computeRec stMid rest
    .ok (stEnd, resp :: resps)

/-- **Domain Violation Refusal**: any validly encoded request tagged with a non-`.hostDpi`
domain (`.proverCore` or `.fabricCfg`) is refused with `.domainViolation`. -/
theorem stepOspcDpiServer_refuses_domain_mismatch
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st : OspcDpiServerState) (req : OspcDpiReq) (hDom : req.domain ≠ .hostDpi) :
    stepOspcDpiServer tileMod computeRec st (encodeOspcDpiReq req) = .error .domainViolation := by
  unfold stepOspcDpiServer
  simp only [bind, Except.bind, decodeOspcDpiReq_encodeOspcDpiReq, bne_iff_ne.mpr hDom, ↓reduceIte]

/-- **Sequence Mismatch Refusal**: any `.hostDpi` request with `req.seqNo ≠ st.expectedSeq` is
refused with `.sequenceMismatch`. -/
theorem stepOspcDpiServer_refuses_seq_mismatch
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st : OspcDpiServerState) (req : OspcDpiReq)
    (hDom : req.domain = .hostDpi) (hSeq : req.seqNo ≠ st.expectedSeq) :
    stepOspcDpiServer tileMod computeRec st (encodeOspcDpiReq req) = .error .sequenceMismatch := by
  unfold stepOspcDpiServer
  simp only [bind, Except.bind, decodeOspcDpiReq_encodeOspcDpiReq, hDom,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne.mpr hSeq]

/-- **Single-Cycle Isolated DPI Server Refinement (`stepOspcDpiServer_refines_spec`)**. -/
theorem stepOspcDpiServer_refines_spec
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
    (st st' : OspcDpiServerState) (rawReq rawResp : ByteArray)
    (hOk : stepOspcDpiServer tileMod computeRec st rawReq = .ok (st', rawResp)) :
    ∃ req : OspcDpiReq,
      decodeOspcDpiReq rawReq = .ok req ∧
      req.domain = .hostDpi ∧
      req.seqNo = st.expectedSeq ∧
      (∀ t : Fin 4, st'.tiles t = stepMemModule (tileMod t) req.rst (req.inputsFor t) (st.tiles t)) ∧
      (st'.tiles ⟨2, by omega⟩).regs 1 = 1#64 ∧
      st'.expectedSeq = st.expectedSeq + 1#32 ∧
      st'.cycleCount = st.cycleCount + 1#32 ∧
      st'.lastReceipt256 = computeRec st'.tiles ∧
      rawResp.size = ODPI_HEADER_LEN + ODPI_RESP_PAYLOAD_LEN ∧
      decodeOspcDpiResp rawResp =
        .ok (buildOspcDpiResp tileMod req st'.cycleCount st.tiles st'.tiles st'.lastReceipt256) := by
  unfold stepOspcDpiServer at hOk
  cases hDec : decodeOspcDpiReq rawReq with
  | error e => simp [bind, Except.bind, hDec] at hOk
  | ok req =>
    simp only [bind, Except.bind, hDec] at hOk
    split at hOk
    · cases hOk
    · rename_i hDom
      split at hOk
      · cases hOk
      · rename_i hSeq
        split at hOk
        · cases hOk
        · rename_i hLin
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          obtain ⟨rfl, rfl⟩ := hOk
          refine ⟨req, rfl, by simpa using hDom, by simpa using hSeq, fun _ => rfl,
            by simpa using hLin, rfl, rfl, rfl, encodeOspcDpiResp_size _,
            decodeOspcDpiResp_encodeOspcDpiResp _⟩

/-- **Multi-Cycle DPI Server Trace Refinement (`runOspcDpiServerTrace_refines_spec`)**. -/
theorem runOspcDpiServerTrace_refines_spec
    (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256) :
    ∀ (rawReqs : List ByteArray) (st stEnd : OspcDpiServerState) (rawResps : List ByteArray),
      runOspcDpiServerTrace tileMod computeRec st rawReqs = .ok (stEnd, rawResps) →
      rawResps.length = rawReqs.length ∧
      (∀ r ∈ rawResps, r.size = ODPI_HEADER_LEN + ODPI_RESP_PAYLOAD_LEN ∧ (decodeOspcDpiResp r).isOk = true) ∧
      (rawReqs ≠ [] → (stEnd.tiles ⟨2, by omega⟩).regs 1 = 1#64)
  | [], st, stEnd, rawResps, hOk => by
    simp only [runOspcDpiServerTrace, Except.ok.injEq, Prod.mk.injEq] at hOk
    obtain ⟨rfl, rfl⟩ := hOk
    exact ⟨rfl, (fun _ hr => by cases hr), fun h => absurd rfl h⟩
  | raw :: rest, st, stEnd, rawResps, hOk => by
    unfold runOspcDpiServerTrace at hOk
    cases hStep : stepOspcDpiServer tileMod computeRec st raw with
    | error e => simp [bind, Except.bind, hStep] at hOk
    | ok p =>
      rcases p with ⟨stMid, resp0⟩
      simp only [bind, Except.bind, hStep] at hOk
      cases hRest : runOspcDpiServerTrace tileMod computeRec stMid rest with
      | error e => simp [hRest] at hOk
      | ok q =>
        rcases q with ⟨stFinal, respsRest⟩
        simp only [hRest, Except.ok.injEq, Prod.mk.injEq] at hOk
        obtain ⟨rfl, rfl⟩ := hOk
        obtain ⟨_, _, _, _, _, hLinMid, _, _, _, hSz0, hDec0⟩ :=
          stepOspcDpiServer_refines_spec tileMod computeRec st stMid raw resp0 hStep
        obtain ⟨hLenRest, hAllRest, hLinRest⟩ :=
          runOspcDpiServerTrace_refines_spec tileMod computeRec rest stMid stFinal respsRest hRest
        refine ⟨by simp [hLenRest], ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hrRest
          · exact ⟨hSz0, by rw [hDec0]; rfl⟩
          · exact hAllRest r hrRest
        · intro _
          cases rest with
          | nil =>
            simp only [runOspcDpiServerTrace, Except.ok.injEq, Prod.mk.injEq] at hRest
            obtain ⟨rfl, _⟩ := hRest
            exact hLinMid
          | cons _ _ => exact hLinRest (List.cons_ne_nil _ _)

/-- Non-vacuity witnesses inhabiting `ospc_fabulous_bitstream_refines_slice`,
`stepOspcDpiServer_refines_spec`, and `runOspcDpiServerTrace_refines_spec`. -/
private theorem ospcSignalFabric_refinement_inhabited :
    (∃ (tr : List (Bool × (Nat → BitVec 64))) (regs : Nat → BitVec 64),
      tr ≠ [] ∧ RegsFit ospcFabricSliceRtl regs ∧ ∀ c ∈ tr, InputsFit ospcFabricSliceRtl c) ∧
    (∃ (tileMod : Fin 4 → RtlMemModule) (computeRec : (Fin 4 → MemState) → BitVec 256)
       (st st' : OspcDpiServerState) (rawReq rawResp : ByteArray),
      stepOspcDpiServer tileMod computeRec st rawReq = .ok (st', rawResp) ∧
      runOspcDpiServerTrace tileMod computeRec st [rawReq] = .ok (st', [rawResp])) := by
  refine ⟨?_, ?_⟩
  · let regs : Nat → BitVec 64 := fun i => if i = 1 then 1#64 else 0#64
    let ins0 : Nat → BitVec 64 := fun i => if i = 0 then 3#64 else if i = 1 then 1#64 else 0#64
    refine ⟨[(false, ins0)], regs, List.cons_ne_nil _ _, ?_, ?_⟩
    · intro i
      match i with
      | 0 | 1 => simp [regs, ospcFabricSliceRtl, regWidthOf]
      | _ + 2 => simp [regs, ospcFabricSliceRtl, regWidthOf]
    · intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      intro i
      match i with
      | 0 | 1 | 2 | 3 => simp [ins0, ospcFabricSliceRtl, inputWidth]
      | _ + 4 => simp [ins0, ospcFabricSliceRtl, inputWidth]
  · let sliceMem : RtlMemModule := { core := ospcFabricSliceRtl, rams := [] }
    let tileMod : Fin 4 → RtlMemModule := fun _ => sliceMem
    let computeRec : (Fin 4 → MemState) → BitVec 256 := fun _ => 0#256
    let st : OspcDpiServerState :=
      ⟨fun _ => ⟨fun i => if i = 1 then 1#64 else 0#64, fun _ _ => 0#64⟩, 0#32, 0#32, 0#256⟩
    let req : OspcDpiReq :=
      ⟨.hostDpi, 0#32, false, 3#2, 1#64, 0#17, 0#1, 0#8, 0#64, 0#64,
       0#1, 0#6, 0#1, 0#12, 0#64, 0#1, 0#64, 0#1, 0#8, 0#64, 0#1, 0#1, 0#8, 0#64⟩
    let tiles' : Fin 4 → MemState :=
      fun t => stepMemModule (tileMod t) req.rst (req.inputsFor t) (st.tiles t)
    let st' : OspcDpiServerState := ⟨tiles', 1#32, 1#32, 0#256⟩
    let resp := encodeOspcDpiResp (buildOspcDpiResp tileMod req 1#32 st.tiles tiles' 0#256)
    have hLin : (tiles' ⟨2, by omega⟩).regs 1 = 1#64 := by decide
    have hStep : stepOspcDpiServer tileMod computeRec st (encodeOspcDpiReq req) = .ok (st', resp) := by
      unfold stepOspcDpiServer
      dsimp only [bind, Except.bind]
      rw [decodeOspcDpiReq_encodeOspcDpiReq]
      dsimp only
      have hDom : (req.domain != .hostDpi) = false := rfl
      have hSeq : (req.seqNo != st.expectedSeq) = false := rfl
      have hBne : ((tiles' ⟨2, by omega⟩).regs 1 != 1#64) = false := by rw [hLin]; rfl
      simp only [hDom, hSeq, Bool.false_eq_true, ↓reduceIte]
      change (if ((tiles' ⟨2, by omega⟩).regs 1 != 1#64) = true then Except.error OspcDpiError.deltaNetLinearityViolation
              else Except.ok (st', resp)) = Except.ok (st', resp)
      simp only [hBne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨tileMod, computeRec, st, st', encodeOspcDpiReq req, resp, hStep, ?_⟩
    unfold runOspcDpiServerTrace
    dsimp only [bind, Except.bind]
    rw [hStep]
    rfl

end Obend.Hardware.OspcSignalFabric
end
