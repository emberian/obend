/-
# Obend.Hardware.Gpu.Rdna2.Check — the dumped programs, run on the model, against the plan's expected outputs

The correspondence of rung G2, stated as a decidable check per graph: for every vector of
`hardware/gpu/graphs/<g>/expected.tsv`, laying the plan's buffers out in the model's memory as RADV binds
them, running each stage's dumped program (`hardware/gpu/isa/<g>.txt`, decoded by `Decode`) once per
workgroup on `Semantics.run`, and reading the output wires back gives the expected words. It is a check,
not a theorem: the universal statements live at the instruction level (`Semantics`); this is the
known-answer run that `Obend.Teeth.Hardware.Rdna2Runs` pins with `native_decide` and `#assert_compiled`
and that `hardware/gpu/isa_check.sh` stage 4 runs on every graph, with a planted bit flip that must fail.

What the model is told about the host, each fact with its source:
* the three storage buffers `w`, `c`, `ix` are bindings 0, 1, 2 of one descriptor set (`emitStageWgsl`),
  which RADV lays out as consecutive 16-byte buffer descriptors (the dumps load them at offsets 0, 0x10,
  0x20 of the set); each descriptor is `ac_build_raw_buffer_descriptor` (Mesa 24.2.8
  `src/amd/common/ac_descriptors.c`): base address, stride 0, size in bytes, `OOB_SELECT_RAW`, of which
  the model reads base, stride, num_records, swizzle, add-tid and OOB_SELECT (manual 8.1.8);
* the wave starts with the descriptor set's address low dword in `s2` and the workgroup id in `s3`
  (`radv_shader_args.c`: the global input SGPRs, then `workgroup_ids`, after the two ring-offset SGPRs),
  the address's high dword `0xffff8000` supplied by the shader itself (the `s_movk_i32 s1, 0x8000` of every
  dump), and the thread id in `v0` (manual 3.12.2: VGPR0 = thread ID in group, X), EXEC all ones
  (manual 3.12.1: the workitem valid mask; workgroups are one full wave64);
* a dispatch of `threads` threads is `⌈threads / 64⌉` workgroups, run one after another (sound for G1's
  programs: no two threads of a stage write one word and no stage reads a word it writes).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Semantics
public import Lean.Data.Json
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Lean (Json)

/-! ## 1. The plan, the vectors and the dumps, parsed -/

structure Plan where
  words : Nat
  wireBase : Array Nat
  wireLen : Array Nat
  consts : Array Int
  tables : Array Nat
  inputs : Array Nat
  outputs : Array Nat
  stageThreads : Array Nat

def parsePlan (s : String) : Except String Plan := do
  let j ← Json.parse s
  let nats (k : String) : Except String (Array Nat) := do
    (← (← j.getObjVal? k).getArr?).mapM (·.getNat?)
  let consts ← (← (← j.getObjVal? "consts").getArr?).mapM fun c => do
    let t ← c.getStr?
    match t.toInt? with
    | some v => pure v
    | none => throw s!"plan: constant {t} is not an integer"
  let stages ← (← (← j.getObjVal? "stages").getArr?).mapM fun st => do (← st.getObjVal? "threads").getNat?
  pure { words := ← (← j.getObjVal? "words").getNat?, wireBase := ← nats "wireBase", wireLen := ← nats "wireLen",
         consts := consts, tables := ← nats "tables", inputs := ← nats "inputs", outputs := ← nats "outputs",
         stageThreads := stages }

/-- One line of `expected.tsv`: the input wires and the output wires, each a list of signed words. -/
structure Vector where
  index : Nat
  inputs : Array (Array Int)
  outputs : Array (Array Int)

def parseWires (s : String) : Except String (Array (Array Int)) :=
  (s.splitOn ";").toArray.mapM fun w =>
    if w == "-" then pure #[] else (w.splitOn ",").toArray.mapM fun e =>
      match e.toInt? with
      | some v => pure v
      | none => throw s!"expected.tsv: {e} is not an integer"

def parseExpected (s : String) : Except String (Array Vector) :=
  (s.splitOn "\n").toArray.filter (· != "") |>.mapM fun ln => do
    match ln.splitOn "\t" with
    | [i, ins, outs] =>
      match i.toNat? with
      | some n => pure { index := n, inputs := ← parseWires ins, outputs := ← parseWires outs }
      | none => throw s!"expected.tsv: bad index {i}"
    | _ => throw s!"expected.tsv: bad line {ln}"

def hexToNat (h : String) : Nat :=
  h.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

/-- The dumped programs, one per `## stage` block: each instruction's dwords. -/
def parseDump (s : String) : Array (Array (Array UInt32)) := Id.run do
  let mut stages : Array (Array (Array UInt32)) := #[]
  let mut cur : Array (Array UInt32) := #[]
  let mut inStage := false
  for ln in s.splitOn "\n" do
    if ln.startsWith "## stage" then
      if inStage then stages := stages.push cur
      cur := #[]; inStage := true
    else if ln.startsWith "\t" then
      match ln.splitOn "\t; " with
      | [_, hexes] => cur := cur.push ((hexes.splitOn " ").filter (· != "") |>.toArray.map fun h => UInt32.ofNat (hexToNat h))
      | _ => pure ()
  if inStage then stages := stages.push cur
  return stages

/-! ## 2. The memory as RADV binds it -/

def descSetHi : UInt64 := 0xffff8000
def descSetLo : UInt32 := 0x1000
def descSetAddr : UInt64 := (descSetHi <<< 32) ||| descSetLo.toUInt64
def wAddr : UInt64 := 0x100000000
def cAddr : UInt64 := 0x200000000
def ixAddr : UInt64 := 0x300000000

/-- `ac_build_raw_buffer_descriptor` (Mesa 24.2.8): `desc[0] = va`, `desc[1] = BASE_ADDRESS_HI(va >> 32) |
STRIDE(0)`, `desc[2] = size`, `desc[3]` with `OOB_SELECT_RAW` (3, bits 29:28) and `RESOURCE_LEVEL` (bit 24);
the format and channel selects of `desc[3]` do not reach untyped dword loads (manual 8.1.4: the data
format of `BUFFER_LOAD_<type>` is derived from the opcode, dst_sel identity) and the model does not read them. -/
def rawBufferDescriptor (va : UInt64) (size : Nat) : Array UInt32 :=
  #[va.toUInt32, ((va >>> 32) &&& 0xFFFF).toUInt32, UInt32.ofNat size, ((3 : UInt32) <<< 28) ||| ((1 : UInt32) <<< 24)]

def writeDwords (m : Memory) (addr : UInt64) (ws : Array UInt32) : Memory :=
  ws.zipIdx.foldl (fun m (w, k) => m.insert ((addr >>> 2) + UInt64.ofNat k) w) m

def int64Dwords (v : Int) : Array UInt32 :=
  let u : UInt64 := UInt64.ofNat ((v % (2 ^ 64 : Int)).toNat)
  #[u.toUInt32, (u >>> 32).toUInt32]

/-- The memory for one vector: zeros in `w` except the input wires at their bases, the constants, the
gather tables, and the three descriptors at the set. -/
def initialMemory (p : Plan) (v : Vector) : Memory := Id.run do
  let mut m : Memory := {}
  m := writeDwords m wAddr (Array.replicate (2 * p.words) 0)
  for (wire, k) in p.inputs.zipIdx do
    let base := p.wireBase.getD wire 0
    for (x, e) in (v.inputs.getD k #[]).zipIdx do
      m := writeDwords m (wAddr + UInt64.ofNat (8 * (base + e))) (int64Dwords x)
  m := writeDwords m cAddr (p.consts.flatMap int64Dwords)
  m := writeDwords m ixAddr (p.tables.map UInt32.ofNat)
  m := writeDwords m descSetAddr (rawBufferDescriptor wAddr (8 * p.words))
  m := writeDwords m (descSetAddr + 16) (rawBufferDescriptor cAddr (8 * p.consts.size))
  m := writeDwords m (descSetAddr + 32) (rawBufferDescriptor ixAddr (4 * p.tables.size))
  return m

/-- The wave of workgroup `g`: `s2` the set's low address, `s3` the group id, `v0` the lane. -/
def initialWave (mem : Memory) (g : Nat) : WaveState := Id.run do
  let mut s := WaveState.init mem
  s := writeSgpr s 2 descSetLo
  s := writeSgpr s 3 (UInt32.ofNat g)
  for lane in [0:lanes] do
    s := writeVgpr s 0 lane (UInt32.ofNat lane)
  return s

/-! ## 3. Running -/

def readWord64 (m : Memory) (addr : UInt64) : Option Int := do
  let lo ← m.get? (addr >>> 2)
  let hi ← m.get? ((addr >>> 2) + 1)
  let u : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
  pure (if u ≥ ((1 : UInt64) <<< 63) then (u.toNat : Int) - 2 ^ 64 else (u.toNat : Int))

/-- Every stage of the dump on every workgroup of its dispatch, then the output wires. -/
def runVector (p : Plan) (progs : Array Program) (v : Vector) : Except String (Nat × Array (Array Int)) := do
  let mut mem := initialMemory p v
  let mut steps := 0
  for (prog, k) in progs.zipIdx do
    let threads := p.stageThreads.getD k 0
    let groups := (threads + lanes - 1) / lanes
    let fuel := 16 * prog.size + 64
    for g in [0:groups] do
      let s := run prog fuel (initialWave mem g)
      if let some e := s.err then throw s!"vector {v.index}, stage {k}, workgroup {g}: {e}"
      if !s.halted then throw s!"vector {v.index}, stage {k}, workgroup {g}: did not halt"
      steps := steps + fuel
      mem := s.mem
  let outs ← p.outputs.mapM fun wire => do
    let base := p.wireBase.getD wire 0
    (Array.range (p.wireLen.getD wire 0)).mapM fun e =>
      match readWord64 mem (wAddr + UInt64.ofNat (8 * (base + e))) with
      | some x => pure x
      | none => throw s!"vector {v.index}: output wire {wire} element {e} is not in memory"
  pure (steps, outs)

def flipBit (progs : Array (Array (Array UInt32))) (stage instr bit : Nat) : Except String (Array (Array (Array UInt32))) := do
  let some st := progs[stage]? | throw s!"flip: no stage {stage}"
  let some ws := st[instr]? | throw s!"flip: no instruction {instr} in stage {stage}"
  let w := bit / 32
  if w ≥ ws.size then throw s!"flip: bit {bit} is beyond the instruction's {ws.size} dwords"
  let ws' := ws.set! w (ws[w]! ^^^ (1 <<< (bit % 32).toUInt32))
  pure (progs.set! stage (st.set! instr ws'))

/-- The check: the dumps' programs decode, and every vector's outputs match. With `flip`, one bit of one
instruction is flipped first (the gate's planted fault). Returns a one-line report or the first failure. -/
def checkGraphReport (isa plan expected : String) (flip : Option (Nat × Nat × Nat)) : Except String String := do
  let p ← parsePlan plan
  let vecs ← parseExpected expected
  let mut dumps := parseDump isa
  if let some (st, ins, b) := flip then dumps ← flipBit dumps st ins b
  if dumps.size != p.stageThreads.size then throw s!"{dumps.size} programs in the dump for {p.stageThreads.size} stages"
  let progs ← dumps.zipIdx.mapM fun (ws, k) =>
    match decodeProgram (ws.flatMap id) with
    | .ok prog => pure prog
    | .error e => throw s!"stage {k}: {e}"
  let mut steps := 0
  for v in vecs do
    let (st, outs) ← runVector p progs v
    steps := steps + st
    if outs != v.outputs then
      throw s!"vector {v.index}: the model gives {outs} where expected.tsv has {v.outputs}"
  pure s!"{progs.size} stages, {vecs.size} vectors: the dumped programs on the model give expected.tsv"

/-- The closed Boolean the teeth pin. -/
def checkGraph (isa plan expected : String) : Bool := (checkGraphReport isa plan expected none).toBool

/-! ## 4. The gem5 differential vectors -/

def parseHex64 (h : String) : UInt64 := UInt64.ofNat (hexToNat h)
def parseHex32 (h : String) : UInt32 := UInt32.ofNat (hexToNat h)

/-- A state from a row's `exec vcc scc [pc]`, `s0..s7`, `v0..v5` columns. -/
def stateOfRow (regs sgprs vgprs : String) (mem : Memory) : Except String (WaveState × Nat) := do
  let r := (regs.splitOn " ").filter (· != "")
  let some ex := r[0]? | throw "row: no exec"
  let some vc := r[1]? | throw "row: no vcc"
  let some sc := r[2]? | throw "row: no scc"
  let pc := match r[3]? with | some p => p.toNat?.getD 0 | none => 0
  let mut s := WaveState.init mem
  s := { s with exec := parseHex64 ex, vcc := parseHex64 vc, scc := sc == "1", pc := pc }
  for (h, k) in ((sgprs.splitOn " ").filter (· != "")).zipIdx do
    s := writeSgpr s k (parseHex32 h)
  for (reg, rk) in (vgprs.splitOn ";").zipIdx do
    for (h, lane) in (reg.splitOn ",").zipIdx do
      s := writeVgpr s rk lane (parseHex32 h)
  pure (s, pc)

/-- One row: decode the words, step from the input state, compare with the output state in every
register the row does not exclude (`skip` names a known RDNA2 departure from the Vega twin). -/
def checkGem5Row (ln : String) : Except String Unit := do
  match ln.splitOn "\t" with
  | [name, words, regsIn, sIn, vIn, regsOut, sOut, vOut, skip] =>
    let ws := ((words.splitOn " ").filter (· != "")).toArray.map fun h => UInt32.ofNat (hexToNat h)
    let prog ← match decodeProgram ws with | .ok p => pure p | .error e => throw s!"{name}: {e}"
    let (s0, _) ← stateOfRow regsIn sIn vIn {}
    let (want, wantPc) ← stateOfRow regsOut sOut vOut {}
    let got := step prog s0
    if let some e := got.err then throw s!"{name}: the model refused: {e}"
    let skips := skip.splitOn ","
    let check (field : String) (ok : Bool) : Except String Unit :=
      if ok || skips.contains field then pure () else throw s!"{name}: {field} differs from gem5's body"
    check "exec" (got.exec == want.exec)
    check "vcc" (got.vcc == want.vcc)
    check "scc" (got.scc == want.scc)
    check "pc" (got.pc == wantPc)
    for k in [0:8] do check s!"s{k}" (readSgpr got k == readSgpr want k)
    for r in [0:6] do
      for lane in [0:lanes] do
        check s!"v{r}" (readVgpr got r lane == readVgpr want r lane)
  | _ => throw s!"bad row: {ln.take 60}"

def checkGem5Report (tsv : String) : Except String String := do
  let rows := (tsv.splitOn "\n").filter fun ln => ln != "" && !ln.startsWith "#"
  for ln in rows do checkGem5Row ln
  let names := rows.map (fun ln => (ln.splitOn "\t").headD "") |>.eraseDups
  pure s!"{rows.length} gem5 vectors over {names.length} instructions agree with the model"

def checkGem5 (tsv : String) : Bool := (checkGem5Report tsv).toBool

end Obend.Hardware.Gpu.Rdna2
