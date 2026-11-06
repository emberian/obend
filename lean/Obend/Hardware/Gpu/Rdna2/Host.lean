/-
# Obend.Hardware.Gpu.Rdna2.Host — the dispatch as the host and RADV set it up

What the model is told about the host, each fact with its source:
* the three storage buffers `w`, `c`, `ix` are bindings 0, 1, 2 of one descriptor set (`emitStageWgsl`),
  which RADV lays out as consecutive 16-byte buffer descriptors (the dumps load them at offsets 0, 0x10,
  0x20 of the set); each descriptor is `ac_build_raw_buffer_descriptor` (Mesa 24.2.8
  `src/amd/common/ac_descriptors.c`): base address, stride 0, size in bytes, `OOB_SELECT_RAW`;
* the wave starts with the descriptor set's address low dword in `s2` and the workgroup id in `s3`
  (`radv_shader_args.c`: the global input SGPRs, then `workgroup_ids`), the high dword `0xffff8000`
  supplied by the shader itself (the `s_movk_i32 s1, 0x8000` of every dump), and the thread id in `v0`
  (manual 3.12.2), EXEC all ones (manual 3.12.1; workgroups are one full wave64);
* a dispatch of `threads` threads is `⌈threads / 64⌉` workgroups, run one after another. That is sound
  for these programs because the certificate (`Cert`) refuses a wave that reads a word another wave of
  the same dispatch stored; it is the model's reading of a dispatch, not a claim about the device's
  scheduling.
The buffers sit at fixed addresses (`wAddr`, `cAddr`, `ixAddr`); a 64-bit word `i` of `w` is the dwords
`wDw + 2i` (low) and `wDw + 2i + 1` (high).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Semantics
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph

def descSetHi : UInt64 := 0xffff8000
def descSetLo : UInt32 := 0x1000
def descSetAddr : UInt64 := (descSetHi <<< 32) ||| descSetLo.toUInt64
def wAddr : UInt64 := 0x100000000
def cAddr : UInt64 := 0x200000000
def ixAddr : UInt64 := 0x300000000
/-- The dword address of word 0 of `w`. -/
def wDw : UInt64 := wAddr >>> 2

/-- `ac_build_raw_buffer_descriptor` (Mesa 24.2.8): `desc[0] = va`, `desc[1] = BASE_ADDRESS_HI(va >> 32) |
STRIDE(0)`, `desc[2] = size`, `desc[3]` with `OOB_SELECT_RAW` (3, bits 29:28) and `RESOURCE_LEVEL` (bit 24);
the format and channel selects of `desc[3]` do not reach untyped dword loads (manual 8.1.4: the data
format of `BUFFER_LOAD_<type>` is derived from the opcode, dst_sel identity) and the model does not read them. -/
def rawBufferDescriptor (va : UInt64) (size : Nat) : Array UInt32 :=
  #[va.toUInt32, ((va >>> 32) &&& 0xFFFF).toUInt32, UInt32.ofNat size, ((3 : UInt32) <<< 28) ||| ((1 : UInt32) <<< 24)]

def writeDwords (m : Memory) (addr : UInt64) (ws : Array UInt32) : Memory :=
  ws.zipIdx.foldl (fun m (w, k) => m.insert ((addr >>> 2) + UInt64.ofNat k) w) m

/-- A 64-bit word as its two dwords, low first. -/
def wordDwords (w : Word) : Array UInt32 :=
  let u := UInt64.ofBitVec w
  #[u.toUInt32, (u >>> 32).toUInt32]

/-- Everything but the wire buffer: the constants, the gather tables, the three descriptors. -/
def layoutMem (words : Nat) (consts : List Word) (tables : List Nat) : Memory :=
  let m : Memory := {}
  let m := writeDwords m cAddr (consts.toArray.flatMap wordDwords)
  let m := writeDwords m ixAddr (tables.toArray.map UInt32.ofNat)
  let m := writeDwords m descSetAddr (rawBufferDescriptor wAddr (8 * words))
  let m := writeDwords m (descSetAddr + 16) (rawBufferDescriptor cAddr (8 * consts.length))
  writeDwords m (descSetAddr + 32) (rawBufferDescriptor ixAddr (4 * tables.length))

/-- The memory of a dispatch whose wire buffer holds `flat`. -/
def memOf (words : Nat) (consts : List Word) (tables : List Nat) (flat : Nat → Word) : Memory :=
  (List.range words).foldl (fun m i => writeDwords m (wAddr + UInt64.ofNat (8 * i)) (wordDwords (flat i)))
    (layoutMem words consts tables)

/-- Word `i` of the wire buffer as memory holds it. -/
def wordAt (m : Memory) (i : Nat) : Word :=
  (join64 ((m.get? (wDw + UInt64.ofNat (2 * i))).getD 0) ((m.get? (wDw + UInt64.ofNat (2 * i) + 1)).getD 0)).toBitVec

def fuelOf (prog : Program) : Nat := 16 * prog.size + 64
def groupsOf (threads : Nat) : Nat := (threads + lanes - 1) / lanes

/-- The waves of one dispatch, in workgroup order; `none` if one fails or does not halt. -/
def runWaves (prog : Program) : List Nat → Memory → Option Memory
  | [], m => some m
  | g :: gs, m =>
    let s := run prog (fuelOf prog) (initWave m descSetLo g : WaveState)
    if s.err.isNone && s.halted then runWaves prog gs s.mem else none

/-- The dispatches of a program in order: each stage's program and thread count. -/
def runDispatch : List (Program × Nat) → Memory → Option Memory
  | [], m => some m
  | (prog, threads) :: rest, m => (runWaves prog (List.range (groupsOf threads)) m).bind (runDispatch rest)

end Obend.Hardware.Gpu.Rdna2
