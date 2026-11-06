module
/-
# Obend.Hardware.Fabulous.Bitstream — reading a FABulous bitstream back to the `Net` it configures

The inputs are the files FABulous writes for a fabric, read as FABulous's own tools read them:
- the binary bitstream `bit_gen` writes (`fabulous_bit_gen/bit_gen.py`): a 20-byte sync header, then for
  each column `x` and frame `f` a 32-bit frame-select word `(x <<< 27) ||| (1 <<< f)` and one 32-bit
  word per interior row, top row first, where bit `j` of row `y`'s word is configuration bit
  `32·f + j` of tile `XxYy`; then the desync word (bit 20);
- `.FABulous/bitStreamSpec.csv`: per tile, every FASM feature and the configuration bits it sets
  (`gen_bitstream_spec.py`; a switch-matrix pip `src.dst` carries the binary select of `src` on its
  multiplexer, a hard-wired connection carries none);
- `.FABulous/pips.txt`: the routing graph nextpnr routes on (`srcTile,srcWire,dstTile,dstWire,delay,feature`);
- `.FABulous/bel.v2.txt`: the BELs of every tile (`BelBegin,tile,letter,type,prefix`).

`decodeBin` gives each tile's configuration bits; `extract` follows the configured routing back from
every output pin, through LUT4s, to input pins, flops and constants, and returns the `Net`, or a
refusal naming what it met that the model does not cover.

## Scope
Only `LUT4AB` logic tiles and `W_IO` pins are modelled: the eight `LUT4c_frame_config_dffesr` cells
with their flops, and the switch matrix. A configuration that routes through the carry chain
(`I0mux`, `Co`), the `MUX8LUT_frame_config_mux` outputs, an IO's registered output `Q`, the
`Config_access` BELs, or a block RAM, DSP or register-file tile (`RAM_IO`, `DSP_top`/`DSP_bot`,
`RegFile`; none is in the fabric of `hardware/fabulous/fabric.csv`) is refused by name.
-/
public import Obend.Hardware.Fabulous.Net
public import Std.Data.HashMap
public import Std.Data.HashSet
@[expose] public section

namespace Obend.Hardware.Fabulous

open Std Obend.Hardware.HDL

/-! ## 1. Configuration bits from the binary bitstream -/

/-- Parse `XxYy`. -/
def parseTile (s : String) : Option (Nat × Nat) :=
  if s.startsWith "X" then
    match (s.drop 1).toString.splitOn "Y" with
    | [x, y] => do pure (← x.toNat?, ← y.toNat?)
    | _ => none
  else none

def be32 (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat <<< 24 ||| (b.get! (o+1)).toNat <<< 16 ||| (b.get! (o+2)).toNat <<< 8 ||| (b.get! (o+3)).toNat

def syncHeader : List UInt8 :=
  [0x00, 0xAA, 0xFF, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0xFA, 0xB0, 0xFA, 0xB1]

/-- Configuration bits per tile (bit `32·f + j` of the `Nat`), from a bitstream for a fabric of
`cols` columns and `rows` rows (border rows carry no frames). -/
def decodeBin (cols rows : Nat) (b : ByteArray) : Except String (HashMap String Nat) := do
  let frames := 20
  let interior := rows - 2
  let expected := 20 + cols * frames * (4 + 4 * interior) + 4
  if b.size != expected then
    throw s!"bitstream is {b.size} bytes; a {cols}-column, {rows}-row fabric's is {expected}"
  if (List.range 20).any (fun i => b.get! i != syncHeader[i]!) then
    throw "bitstream does not open with the FABulous sync header"
  let mut cfg : HashMap String Nat := {}
  let mut o := 20
  for x in List.range cols do
    for f in List.range frames do
      let sel := be32 b o
      if sel != (x <<< 27 ||| (1 <<< f)) then
        throw s!"frame-select word at byte {o} is {sel}, expected column {x} frame {f}"
      o := o + 4
      for r in List.range interior do
        let y := rows - 2 - r
        let w := be32 b o
        o := o + 4
        let t := tileName x y
        cfg := cfg.insert t (cfg.getD t 0 ||| (w <<< (32 * f)))
  let desync := be32 b o
  if desync &&& (1 <<< 20) == 0 then throw "bitstream does not end with the desync word"
  return cfg

/-! ## 2. FABulous's metadata -/

/-- A feature's configuration bits: `(position, value)`. Empty for a hard-wired connection. -/
abbrev Pattern := List (Nat × Bool)

structure Fabric where
  /-- `"X1Y1.FEATURE"` ↦ its bits. -/
  spec : HashMap String Pattern
  /-- destination node `"X1Y1.WIRE"` ↦ every pip into it: `(srcTile, srcWire, feature)`. -/
  into : HashMap String (Array (String × String × String))
  /-- tile ↦ its BELs `(letter, type, prefix)`. -/
  bels : HashMap String (Array (String × String × String))
  /-- Columns and rows of the grid. -/
  cols : Nat
  rows : Nat

def parsePattern (s : String) : Except String Pattern := do
  let s := (s.trimAscii.toString.replace "\"" "").replace "{" "" |>.replace "}" ""
  if s.trimAscii.toString.isEmpty then return []
  (s.splitOn ",").mapM fun e =>
    match e.splitOn ":" with
    | [p, v] => match p.trimAscii.toString.toNat? with
      | some n =>
        let v := v.trimAscii.toString
        if v == "'1'" then pure (n, true) else if v == "'0'" then pure (n, false)
        else throw s!"bad bit value {v}"
      | none => throw s!"bad bit position {p}"
    | _ => throw s!"bad pattern entry {e}"

def parseSpec (txt : String) : Except String (HashMap String Pattern × Nat × Nat) := do
  let mut spec : HashMap String Pattern := {}
  let mut tile := ""
  let mut cols := 0
  let mut rows := 0
  for line in txt.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "," with
    | [t] =>
      match parseTile t.trimAscii.toString with
      | some (x, y) => tile := t.trimAscii.toString; cols := max cols (x+1); rows := max rows (y+1)
      | none => throw s!"bitStreamSpec.csv: unexpected line {line}"
    | f :: rest => spec := spec.insert (tile ++ "." ++ f) (← parsePattern (",".intercalate rest))
    | [] => pure ()
  return (spec, cols, rows)

def parsePips (txt : String) : HashMap String (Array (String × String × String)) := Id.run do
  let mut into : HashMap String (Array (String × String × String)) := {}
  for line in txt.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "," with
    | [st, sw, dt, dw, _, feat] =>
      let k := dt ++ "." ++ dw
      into := into.insert k ((into.getD k #[]).push (st, sw, feat))
    | _ => pure ()
  return into

def parseBels (txt : String) : HashMap String (Array (String × String × String)) := Id.run do
  let mut bels : HashMap String (Array (String × String × String)) := {}
  for line in txt.splitOn "\n" do
    match line.splitOn "," with
    | ["BelBegin", t, l, ty, pre] => bels := bels.insert t ((bels.getD t #[]).push (l, ty, pre))
    | _ => pure ()
  return bels

def loadFabric (specTxt pipsTxt belsTxt : String) : Except String Fabric := do
  let (spec, cols, rows) ← parseSpec specTxt
  return { spec, into := parsePips pipsTxt, bels := parseBels belsTxt, cols, rows }

/-! ## 3. Following the configuration -/

structure ExState where
  gates : Array Gate := #[]
  gateOf : HashMap String Nat := {}
  visiting : HashSet String := {}
  flops : Array (Option Flop) := #[]
  flopOf : HashMap String Nat := {}
  /-- `(tile, position)` ↦ the value the extraction read there. -/
  support : HashMap (String × Nat) Bool := {}
  /-- Every node the extraction traced ↦ the pips it followed, `(destination, source)` from the node
  backwards, and the node it ended at (a BEL output, a pin or a constant). -/
  paths : HashMap String (List (String × String) × String) := {}

abbrev ExM := StateT ExState (Except String)

/-- `bel.v2.txt` names `LUT4AB`'s `LUT4c_frame_config_dffesr` cells by nextpnr's BEL type. -/
def lutType : String := "FABULOUS_LC"
def ioType : String := "IO_1_bidirectional_frame_config_pass"

/-- Does `tile`'s configuration set `feat`? Reads (and records) the feature's bits. -/
def featOn (fab : Fabric) (cfg : HashMap String Nat) (tile feat : String) : ExM Bool := do
  match fab.spec.get? (tile ++ "." ++ feat) with
  | none => throw s!"{tile}: feature {feat} is not in bitStreamSpec.csv"
  | some pat =>
    let bits := cfg.getD tile 0
    let mut ok := true
    for (p, v) in pat do
      let b := bits.testBit p
      modify fun s => { s with support := s.support.insert (tile, p) b }
      if b != v then ok := false
    return ok

/-- The node driving `n` under the configuration, or `none` if no pip drives it. -/
def driver (fab : Fabric) (cfg : HashMap String Nat) (n : String) : ExM (Option String) := do
  match fab.into.get? n with
  | none => return none
  | some pips =>
    if pips.size == 1 then
      let (st, sw, feat) := pips[0]!
      match fab.spec.get? (st ++ "." ++ feat) with
      | some [] => return some (st ++ "." ++ sw)
      | _ => pure ()
    let mut hit : Option String := none
    for (st, sw, feat) in pips do
      if (← featOn fab cfg st feat) then
        if hit.isSome then throw s!"{n}: two pips selected"
        hit := some (st ++ "." ++ sw)
    match hit with
    | some h => return some h
    | none => throw s!"{n}: its multiplexer's select matches no input"

def splitNode (n : String) : String × String :=
  match n.splitOn "." with
  | [t, w] => (t, w)
  | _ => (n, "")

/-- The LUT4 cells and IO pins of a tile, by the wire their output drives. -/
def belAt (fab : Fabric) (t w : String) : Option (String × String × String) :=
  (fab.bels.getD t #[]).find? fun (_, ty, pre) =>
    (ty == lutType && (w == pre ++ "O" || w == pre ++ "Co")) ||
    (ty == ioType && (w == pre ++ "O" || w == pre ++ "Q")) ||
    (ty != lutType && ty != ioType && !pre.isEmpty && w.startsWith pre) ||
    (ty.startsWith "MUX8LUT" && w.startsWith "M_")

/-- Does a LUT4 truth table depend on input `i`? -/
def usesInput (init i : Nat) : Bool :=
  (List.range 16).any fun k => init.testBit k != init.testBit (k ^^^ (1 <<< i))

mutual
/-- The `Lit` a node carries: routing is followed to a LUT output, a pin, a flop or a constant. -/
partial def traceNode (fab : Fabric) (cfg : HashMap String Nat) (pm : List Pin) (n : String) (hops : Nat := 0)
    (start : String := n) (acc : List (String × String) := []) : ExM Lit := do
  if hops > 4096 then throw s!"{n}: routing does not end (a loop through pips)"
  match ← driver fab cfg n with
  | some src => traceNode fab cfg pm src (hops + 1) start ((n, src) :: acc)
  | none =>
    modify fun s => { s with paths := s.paths.insert start (acc.reverse, n) }
    let (t, w) := splitNode n
    if w.startsWith "GND" then return .const false
    if w.startsWith "VCC" then return .const true
    match belAt fab t w with
    | none => throw s!"{n}: no pip drives it and it is no BEL output"
    | some (l, ty, pre) =>
      if ty == lutType then
        if w == pre ++ "Co" then throw s!"{t}.{l}: the carry chain (Co) is not modelled"
        if ← featOn fab cfg t (l ++ ".FF") then flopLit fab cfg pm t l pre
        else lutGate fab cfg pm t l pre
      else if ty == ioType then
        if w == pre ++ "Q" then throw s!"{t}.{l}: the IO's registered output Q is not modelled"
        match pm.findIdx? (fun p => p.tile == t && p.bel == l) with
        | some k =>
          match pm[k]? with
          | some ⟨_, _, .output _ _⟩ => throw s!"{t}.{l}: output pin {k} is read as an input"
          | _ => return .pin k
        | none => throw s!"{t}.{l}: an IO pin the pin map does not name is read"
      else throw s!"{t}.{l}: BEL type {ty} is not modelled"

/-- A LUT4 cell's combinational output as a gate (allocated after its inputs). -/
partial def lutGate (fab : Fabric) (cfg : HashMap String Nat) (pm : List Pin) (t l pre : String) : ExM Lit := do
  let site := t ++ "." ++ l
  if let some k := (← get).gateOf.get? site then return .gate k
  if (← get).visiting.contains site then throw s!"{site}: a combinational loop"
  modify fun s => { s with visiting := s.visiting.insert site }
  if (← featOn fab cfg t (l ++ ".I0mux")) then throw s!"{site}: the carry input (I0mux) is not modelled"
  let mut init : Nat := 0
  for k in List.range 16 do
    let f := if k == 0 then l ++ ".INIT" else s!"{l}.INIT[{k}]"
    if ← featOn fab cfg t f then init := init ||| (1 <<< k)
  -- An input the truth table does not depend on is not followed (its multiplexer may select
  -- anything, a loop included); it reads as `false`, which leaves the LUT's value unchanged.
  let pin (i : Nat) : ExM Lit :=
    if usesInput init i then traceNode fab cfg pm (t ++ "." ++ pre ++ s!"I{i}") else pure (.const false)
  let i0 ← pin 0
  let i1 ← pin 1
  let i2 ← pin 2
  let i3 ← pin 3
  let g : Gate := { init := BitVec.ofNat 16 init, i0, i1, i2, i3, site }
  let s ← get
  let k := s.gates.size
  set { s with gates := s.gates.push g, gateOf := s.gateOf.insert site k, visiting := s.visiting.erase site }
  return .gate k

/-- A LUT4 cell's flop: allocated on first read, its inputs traced then. -/
partial def flopLit (fab : Fabric) (cfg : HashMap String Nat) (pm : List Pin) (t l pre : String) : ExM Lit := do
  let site := t ++ "." ++ l
  if let some k := (← get).flopOf.get? site then return .ff k
  let s ← get
  let k := s.flops.size
  set { s with flops := s.flops.push none, flopOf := s.flopOf.insert site k }
  let d ← lutGate fab cfg pm t l pre
  let en ← traceNode fab cfg pm (t ++ "." ++ pre ++ "EN")
  let sr ← traceNode fab cfg pm (t ++ "." ++ pre ++ "SR")
  let rv ← featOn fab cfg t (l ++ ".SET_NORESET")
  modify fun s => { s with flops := s.flops.set! k (some { d, en, sr, rv, site }) }
  return .ff k
end

/-- The `Net` the configuration computes on the pins of `pm`, and the configuration bits it read. -/
def extractS (fab : Fabric) (cfg : HashMap String Nat) (pm : List Pin) :
    Except String (Net × ExState) := do
  let act : ExM (List (Nat × Lit)) := do
    let mut outs := #[]
    for h : k in [0:pm.length] do
      let p := pm[k]
      let tNode := p.tile ++ "." ++ p.bel ++ "_T"
      let tLit ← traceNode fab cfg pm tNode
      match p.role with
      | .output _ _ =>
        if tLit != .const false then throw s!"{p.tile}.{p.bel}: output pin {k} is not driven out (T is not tied low)"
        outs := outs.push (k, ← traceNode fab cfg pm (p.tile ++ "." ++ p.bel ++ "_I"))
      | _ =>
        if tLit != .const true then throw s!"{p.tile}.{p.bel}: input pin {k} is driven out (T is not tied high)"
    return outs.toList
  let (outs, s) ← act.run {}
  let flops ← s.flops.toList.mapM fun
    | some f => pure f
    | none => throw "a flop was left unfilled"
  return ({ gates := s.gates.toList, flops, outs }, s)

def extract (fab : Fabric) (cfg : HashMap String Nat) (pm : List Pin) :
    Except String (Net × HashMap (String × Nat) Bool) := do
  let (N, s) ← extractS fab cfg pm
  return (N, s.support)

/-! ## 4. The pin map of `top_wrapper.v` -/

/-- `top_wrapper.v` for a module with these pins: each pin an `IO_1_bidirectional_frame_config_pass`
at its BEL, inputs `.T(1'b1)`, outputs `.T(1'b0)`; `clk` from FABulous's `Global_Clock`. -/
def topWrapper (m : RtlModule) (pm : List Pin) : String := Id.run do
  let sig (port bit : Nat) (names : List String) := s!"{names.getD port "?"}[{bit}]"
  let mut s := "// Generated by Obend.Hardware.Fabulous.topWrapper; regenerate with `obend fabric wrapper`.\n"
  s := s ++ "`default_nettype none\nmodule top_wrapper;\n    wire clk;\n    (* keep *) Global_Clock clk_i (.CLK(clk));\n    wire rst;\n"
  for (n, k) in m.inputNames.zipIdx do
    s := s ++ s!"    wire [{inputWidth m k - 1}:0] {n};\n"
  for o in m.outputs do
    s := s ++ s!"    wire [{o.width - 1}:0] {o.name};\n"
  let outNames := m.outputs.map (·.name)
  for (p, k) in pm.zipIdx do
    let conn := match p.role with
      | .input port bit => s!".O({sig port bit m.inputNames}), .I(1'b0), .T(1'b1)"
      | .reset => ".O(rst), .I(1'b0), .T(1'b1)"
      | .output port bit => s!".O(), .I({sig port bit outNames}), .T(1'b0)"
    s := s ++ s!"    (* keep, BEL=\"{p.tile}.{p.bel}\" *) IO_1_bidirectional_frame_config_pass io{k}_i ({conn});\n"
  let ports := (["    .clk(clk)", "    .rst(rst)"] ++ m.inputNames.map (fun n => s!"    .{n}({n})") ++
    outNames.map (fun n => s!"    .{n}({n})"))
  s := s ++ s!"    {m.name} top_i (\n" ++ ",\n".intercalate (ports.map ("    " ++ ·)) ++ "\n    );\nendmodule\n`resetall\n"
  return s

end Obend.Hardware.Fabulous

namespace Obend.Hardware.Fabulous

open Std Obend.Hardware.HDL

/-! ## 5. The register-to-flop correspondence, found by simulation

The correspondence is a witness: `findFlopMap` proposes, for each flop, the register bit it tracked on
a seeded run from reset, and the bit-level theorems of `Obend.Hardware.Fabulous.Mac8` check it. -/

/-- A 32-bit LCG step. -/
def lcg (s : Nat) : Nat := (s * 1664525 + 1013904223) % 4294967296

/-- Seeded cycles within the module's input widths; the first is a reset, then one in sixteen. -/
def seededCycles (m : RtlModule) (n : Nat) (seed : Nat := 1) : List (Bool × (Nat → BitVec 64)) := Id.run do
  let mut s := seed
  let mut out := #[]
  for t in List.range n do
    let mut ins : Array (BitVec 64) := #[]
    for i in List.range m.inputNames.length do
      s := lcg s
      let w := inputWidth m i
      ins := ins.push (BitVec.ofNat 64 ((s >>> 8) % 2 ^ w))
    s := lcg s
    let rst := t == 0 || (s >>> 12) % 16 == 0
    let insF : Nat → BitVec 64 := fun i => ins.getD i 0#64
    out := out.push (rst, insF)
  return out.toList

/-- For each flop, the register bits `(regIdx, bit)` it equalled after every cycle of `cycles`,
starting from all-zero registers and flops. -/
def flopCandidates (N : Net) (m : RtlModule) (pm : List Pin) (cycles : List (Bool × (Nat → BitVec 64))) :
    Array (List (Nat × Nat)) := Id.run do
  let all := m.regs.flatMap fun r => (List.range r.width).map fun j => (r.regIdx, j)
  let mut cands : Array (List (Nat × Nat)) := Array.replicate N.flops.length all
  let mut q : Array Bool := Array.replicate N.flops.length false
  let mut regs : Array (BitVec 64) := Array.replicate (m.regs.length) 0#64
  for c in cycles do
    let qf : Nat → Bool := fun k => q.getD k false
    let rf : Nat → BitVec 64 := fun i => regs.getD i 0#64
    let q' := N.step (pinValues pm c) qf
    let r' := stepModuleRegs m c.1 c.2 rf
    q := (List.range N.flops.length).toArray.map q'
    regs := (List.range m.regs.length).toArray.map r'
    cands := cands.mapIdx fun k cs => cs.filter fun (r, j) => (regs.getD r 0#64).getLsbD j == q.getD k false
  return cands

/-! ## 6. The Lean text of a `Net` and of its bit-level obligations -/

def litLean : Lit → String
  | .const b => s!"(.const {b})"
  | .pin k => s!"(.pin {k})"
  | .ff k => s!"(.ff {k})"
  | .gate k => s!"(.gate {k})"

def hex16 (v : BitVec 16) : String :=
  let d := Nat.toDigits 16 v.toNat
  "0x" ++ String.ofList (List.replicate (4 - d.length) '0' ++ d)

def netLean (name : String) (N : Net) : String :=
  let g (x : Gate) := s!"  ⟨{hex16 x.init}#16, {litLean x.i0}, {litLean x.i1}, {litLean x.i2}, {litLean x.i3}, \"{x.site}\"⟩"
  let f (x : Flop) := s!"  ⟨{litLean x.d}, {litLean x.en}, {litLean x.sr}, {x.rv}, \"{x.site}\"⟩"
  let o (x : Nat × Lit) := s!"({x.1}, {litLean x.2})"
  s!"def {name} : Net where\n  gates := [\n" ++ ",\n".intercalate (N.gates.map g) ++ "]\n  flops := [\n" ++
    ",\n".intercalate (N.flops.map f) ++ "]\n  outs := [" ++ ", ".intercalate (N.outs.map o) ++ "]\n"

/-- How the obligation writes a literal: `pin` and `ff` are rendered by the caller. -/
def litBV (pin ff : Nat → String) : Lit → String
  | .const b => toString b
  | .pin k => pin k
  | .ff k => ff k
  | .gate k => s!"(v {k})"

/-- The gate equations, one conjunct per gate, as the obligation's hypothesis. -/
def gatesBV (N : Net) (pin ff : Nat → String) : String :=
  " ∧\n      ".intercalate <| N.gates.zipIdx.map fun (x, k) =>
    let l := litBV pin ff
    s!"v {k} = lut4 {hex16 x.init}#16 {l x.i0} {l x.i1} {l x.i2} {l x.i3}"

/-- The flops' next values, as a list. -/
def flopsBV (N : Net) (pin ff : Nat → String) : String :=
  "[" ++ ",\n       ".intercalate (N.flops.zipIdx.map fun (x, k) =>
    let l := litBV pin ff
    s!"mux2 {l x.en} {ff k} (mux2 {l x.sr} {l x.d} {x.rv})") ++ "]"

end Obend.Hardware.Fabulous
