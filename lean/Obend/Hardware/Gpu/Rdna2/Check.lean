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
public import Obend.Hardware.Gpu.Rdna2.Host
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

/-- Each stage's LDS allocation in bytes, from the resource line RADV prints (`LDS: N`). -/
def parseDumpLds (s : String) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for ln in s.splitOn "\n" do
    if ln.startsWith "## stage" then
      match ln.splitOn "LDS: " with
      | [_, rest] => out := out.push (((rest.splitOn ",").headD "0").trimAscii.toString.toNat?.getD 0)
      | _ => out := out.push 0
  return out

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

/-- Read-only constant data embedded in a stage's code image. Offsets are absolute byte
addresses relative to its relocated instruction zero, supplied by the extractor from Mesa's
post-code marker padding and printed pool offsets. Data is never decoded as instructions. -/
abbrev StageData := Array (Nat × Array UInt32)

def parseDumpData (s : String) : Except String (Array StageData) := do
  let mut stages : Array StageData := #[]
  let mut cur : StageData := #[]
  let mut inStage := false
  let mut lastEnd := 0
  for ln in s.splitOn "\n" do
    if ln.startsWith "## stage" then
      if inStage then stages := stages.push cur
      cur := #[]; inStage := true; lastEnd := 0
    else if ln.startsWith ".data" then
      if !inStage then throw "constant data before any stage"
      match (ln.splitOn " ").filter (· != "") with
      | ".data" :: off :: hexes =>
        let some addr := off.toNat? | throw s!"bad constant-data offset: {off}"
        if addr % 4 != 0 || addr < lastEnd then throw "unaligned or overlapping constant data"
        if hexes.isEmpty then throw "empty constant-data record"
        let ws ← hexes.toArray.mapM fun h => do
          if h.length != 8 || !h.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) then
            throw s!"bad constant-data dword: {h}"
          pure (UInt32.ofNat (hexToNat h))
        cur := cur.push (addr, ws)
        lastEnd := addr + 4 * ws.size
      | _ => throw s!"bad constant-data record: {ln}"
  if inStage then stages := stages.push cur
  return stages

/-! ## 2. The memory as RADV binds it -/

def int64Dwords (v : Int) : Array UInt32 :=
  let u : UInt64 := UInt64.ofNat ((v % (2 ^ 64 : Int)).toNat)
  #[u.toUInt32, (u >>> 32).toUInt32]

/-- The wire buffer for one vector: the input wires at their bases, zeros elsewhere. -/
def flatOf (p : Plan) (v : Vector) (i : Nat) : BitVec 64 := Id.run do
  for (wire, k) in p.inputs.zipIdx do
    let base := p.wireBase.getD wire 0
    let xs := v.inputs.getD k #[]
    if base ≤ i && i < base + xs.size then return BitVec.ofInt 64 (xs.getD (i - base) 0)
  return 0#64

/-- The memory for one vector (`Host.memOf`: the layout, and the wire buffer). -/
def initialMemory (p : Plan) (v : Vector) : Memory :=
  memOf p.words (p.consts.toList.map (BitVec.ofInt 64)) p.tables.toList (flatOf p v)


/-! ## 3. Running -/

/-- Every stage of the dump on every workgroup of its dispatch, then the output wires. -/
def runVector (p : Plan) (progs : Array Program) (data : Array StageData) (lds : Array Nat) (v : Vector) : Except String (Nat × Array (Array Int)) := do
  let mut mem := initialMemory p v
  let mut steps := 0
  for (prog, k) in progs.zipIdx do
    let threads := p.stageThreads.getD k 0
    let groups := (threads + lanes - 1) / lanes
    -- A compiler may keep a serial fold as a backward branch rather than unroll it.
    -- Budget by both instruction size and the plan's stored words; this is a bounded
    -- execution allowance, not a termination theorem. Exhaustion remains a refusal.
    let fuel := 16 * prog.size + 64 * p.words + 64
    let pool := data.getD k #[]
    for (addr, ws) in pool do
      mem := writeDwords mem (UInt64.ofNat addr) ws
    for g in [0:groups] do
      let ldsDw := lds.getD k 0 / 4
      let s := run prog fuel (initWave mem descSetLo g (ldsBaseOf g) ldsDw : WaveState)
      if let some e := s.err then throw s!"vector {v.index}, stage {k}, workgroup {g}: {e}"
      -- The pool is read-only: a store into it is a fault, refused like any other.
      for (addr, ws) in pool do
        for (w, j) in ws.zipIdx do
          if s.mem.get? (UInt64.ofNat (addr / 4 + j)) != some w then
            throw s!"vector {v.index}, stage {k}, workgroup {g}: store to a read-only code-data range"
      if !s.halted then throw s!"vector {v.index}, stage {k}, workgroup {g}: did not halt"
      steps := steps + fuel
      mem := s.mem
      -- the workgroup's LDS ends with it: a later workgroup's reads of it are of dwords it has not written
      for j in [0:ldsDw] do
        mem := mem.erase (ldsBaseOf g + UInt64.ofNat j)
    -- Do not let a later stage accidentally read this stage's pool if its dump lost data.
    for (addr, ws) in pool do
      for j in [0:ws.size] do
        mem := mem.erase (UInt64.ofNat (addr / 4 + j))
  let outs ← p.outputs.mapM fun wire => do
    let base := p.wireBase.getD wire 0
    (Array.range (p.wireLen.getD wire 0)).mapM fun e =>
      pure (wordAt mem (base + e)).toInt
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
  let data ← parseDumpData isa
  if data.size != progs.size then throw "constant-data stage count differs from code"
  for (pool, k) in data.zipIdx do
    for (addr, ws) in pool do
      if addr < 4 * (progs.getD k #[]).size then throw s!"stage {k}: constant data overlaps code"
      if addr + 4 * ws.size > wAddr.toNat then throw s!"stage {k}: constant data overlaps host buffers"
  let mut steps := 0
  for v in vecs do
    let (st, outs) ← runVector p progs data (parseDumpLds isa) v
    steps := steps + st
    if outs.size != v.outputs.size then throw s!"vector {v.index}: output count differs from expected.tsv"
    for (actual, k) in outs.zipIdx do
      let expected := v.outputs.getD k #[]
      if actual.size != expected.size then throw s!"vector {v.index}, output {k}: length differs from expected.tsv"
      for e in [0:actual.size] do
        if actual.getD e 0 != expected.getD e 0 then
          throw s!"vector {v.index}, output {k} (wire {p.outputs.getD k 0}), element {e}: the model gives {actual.getD e 0} where expected.tsv has {expected.getD e 0}"
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
  let mut s : WaveState := GWave.init mem 0 0
  let vcc := parseHex64 vc
  s := { s with exec := parseHex64 ex, scc := if sc == "1" then 1 else 0, pc := pc }
  s := writeSgpr (writeSgpr s 106 vcc.toUInt32) 107 (vcc >>> 32).toUInt32
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
    check "vcc" (readSgpr got 106 == readSgpr want 106 && readSgpr got 107 == readSgpr want 107)
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
