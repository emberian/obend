module
/-
# Obend.Hardware.Fabulous.Tile — the LUT4AB tile, written from FABulous's generated RTL

`run_fab` writes the tile as Verilog: `Tile/LUT4AB/LUT4AB_switch_matrix.v` (every routing multiplexer),
the BELs `LUT4c_frame_config_dffesr.v` and `MUX8LUT_frame_config_mux.v`, the configuration memory
`LUT4AB_ConfigMem.v`, and `LUT4AB.v` that wires them. The primitives they instantiate are FABulous's
`models_pack.v`: `cus_mux21`, `cus_mux41`, `cus_mux81`, `cus_mux161` (output `A[S]`, `S` the binary
select, `S0` lowest), `my_buf`, `clk_buf`, `config_latch`.

This file models the switch matrix as data with one constructor per primitive it instantiates
(`SmPrim`), read from the Verilog by `parseSwitchMatrix`, and compiles it to an `RtlModule`
(`smModule`) whose inputs are the user signals and the configuration bits `ConfigBits` (in 64-bit
words `cfg0`, `cfg1`, ...). The BELs are `RtlModule`s transcribed from their Verilog (`lut4cModule`,
`mux8lutModule`). Each is an `obend-emit-sv` target, and `hardware/fabulous/lec_tile.sh` runs the LEC
of each against FABulous's own Verilog: Yosys reads the RTL FABulous generated, z3 compares it with
Lean's model of the `RtlModule`.

Not modelled here: the configuration memory's latches (`config_latch` loaded by frame strobes; the
model takes `ConfigBits` as they hold them) and the frame-data and clock buffers of `LUT4AB.v`.
-/
public import Obend.Hardware.HDL
public import Std.Data.HashMap
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- A multiplexer input: a switch-matrix input port, or a constant (`GND0`, `VCC0`). -/
inductive SmSrc
  | port (name : String)
  | const (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- One primitive instance of the switch matrix, by the `models_pack.v` cell it is. `ins` is the
`X_input` vector, index 0 first; `base` is `k` in `.S0(ConfigBits[k+0])`. -/
inductive SmPrim
  | mux21 (ins : List SmSrc) (base : Nat)
  | mux41 (ins : List SmSrc) (base : Nat)
  | mux81 (ins : List SmSrc) (base : Nat)
  | mux161 (ins : List SmSrc) (base : Nat)
  /-- `assign X = Y;` -/
  | assign (src : SmSrc)
  deriving DecidableEq, Repr, Inhabited

/-- Number of select bits of a primitive. -/
def SmPrim.selBits : SmPrim → Nat
  | .mux21 .. => 1 | .mux41 .. => 2 | .mux81 .. => 3 | .mux161 .. => 4 | .assign _ => 0

def SmPrim.ins : SmPrim → List SmSrc
  | .mux21 i _ | .mux41 i _ | .mux81 i _ | .mux161 i _ => i
  | .assign s => [s]

def SmPrim.base : SmPrim → Nat
  | .mux21 _ b | .mux41 _ b | .mux81 _ b | .mux161 _ b => b
  | .assign _ => 0

/-- The switch matrix: its scalar input and output ports (in declaration order), the number of
configuration bits, and one primitive per output (`(output, primitive)`). -/
structure SwitchMatrix where
  name : String
  inputs : List String
  outputs : List String
  nCfg : Nat
  prims : List (String × SmPrim)
  deriving DecidableEq, Repr, Inhabited

/-! ## Semantics -/

/-- The select value of a primitive under configuration `cfg`. -/
def SmPrim.sel (p : SmPrim) (cfg : Nat → Bool) : Nat :=
  ((List.range p.selBits).map fun i => if cfg (p.base + i) then 2 ^ i else 0).sum

def SmSrc.eval (inp : String → Bool) : SmSrc → Bool
  | .port n => inp n
  | .const b => b

/-- A primitive's output: the selected input (`cus_muxN1`: `A[S]`), or the assigned signal. -/
def SmPrim.eval (p : SmPrim) (cfg : Nat → Bool) (inp : String → Bool) : Bool :=
  ((p.ins[p.sel cfg]?).map (·.eval inp)).getD false

/-! ## The switch matrix as an `RtlModule` -/

/-- The 64-bit configuration words. -/
def cfgWords (n : Nat) : Nat := (n + 63) / 64

def SwitchMatrix.inputIdx (sm : SwitchMatrix) (n : String) : Nat := (sm.inputs.idxOf? n).getD 0

/-- Configuration bit `i` as a 0/1 word. -/
def cfgBitExpr (nIn i : Nat) : RtlExpr := .resize (.slice (i % 64) (i % 64)) (.inputPort (nIn + i / 64))

def SmSrc.expr (sm : SwitchMatrix) : SmSrc → RtlExpr
  | .port n => .inputPort (sm.inputIdx n)
  | .const b => .const (if b then 1#64 else 0#64)

/-- One level of a multiplexer tree: neighbours paired under configuration bit `i`. -/
def muxPairs (nIn i : Nat) : List RtlExpr → List RtlExpr
  | a :: b :: rest => .mux (cfgBitExpr nIn i) b a :: muxPairs nIn i rest
  | xs => xs

/-- A multiplexer tree of `k` levels: level `j` pairs neighbours under select bit `base + j`. -/
def muxTree (nIn base : Nat) : Nat → Nat → List RtlExpr → RtlExpr
  | _, 0, xs => xs.headD (.const 0#64)
  | j, k + 1, xs => muxTree nIn base (j + 1) k (muxPairs nIn (base + j) xs)

def SmPrim.expr (sm : SwitchMatrix) (p : SmPrim) : RtlExpr :=
  match p with
  | .assign s => s.expr sm
  | _ => muxTree sm.inputs.length p.base 0 p.selBits (p.ins.map (·.expr sm))

/-- The switch matrix as an `RtlModule`: inputs the user ports then `cfg0`, `cfg1`, ...; one 1-bit
wire and one 1-bit output per primitive. -/
def smModule (sm : SwitchMatrix) : RtlModule :=
  let nW := cfgWords sm.nCfg
  { name := sm.name ++ "_lec"
    inputNames := sm.inputs ++ (List.range nW).map (s!"cfg{·}")
    inputWidths := sm.inputs.map (fun _ => 1) ++ (List.range nW).map fun k =>
      if k + 1 == nW && sm.nCfg % 64 != 0 then sm.nCfg % 64 else 64
    wires := sm.prims.zipIdx.map fun ((o, p), k) => { wireIdx := k, name := o, width := 1, expr := p.expr sm }
    regs := []
    outputs := sm.prims.zipIdx.map fun ((o, _), k) => { name := o, expr := .wireRef k, width := 1 } }

/-! ## A tile type -/

/-- A tile type: its switch matrix, the frame position holding each of the tile's `ConfigBits`
(`pos[i]`, from the configuration memory's Verilog), where the switch matrix's `ConfigBits` start, and
its LUT4 cells by port prefix with where each cell's 19 `ConfigBits` start. -/
structure TileModel where
  sm : SwitchMatrix
  pos : List Nat
  smOff : Nat
  cells : List (String × Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `ConfigBits[i]` of a tile whose frame bits are `b`. -/
def TileModel.bit (tm : TileModel) (b : Nat → Bool) (i : Nat) : Bool := b (tm.pos.getD i 0)

/-- The switch matrix's configuration. -/
def TileModel.smCfg (tm : TileModel) (b : Nat → Bool) : Nat → Bool := fun i => tm.bit b (tm.smOff + i)

/-- A cell's 19 configuration bits, from `co`. -/
def TileModel.cellCfg (tm : TileModel) (b : Nat → Bool) (co : Nat) : Nat → Bool := fun j => tm.bit b (co + j)


/-! ## Reading the switch matrix from its Verilog -/

def stripWs (s : String) : String := String.ofList (s.toList.filter (fun c => c != ' ' && c != '\t'))

def srcOf (s : String) : SmSrc :=
  if s == "GND0" || s == "GND" then .const false else if s == "VCC0" || s == "VCC" then .const true else .port s

/-- `ConfigBits[112+0]` ↦ 112. -/
def cfgBase (s : String) : Option Nat :=
  match (s.splitOn "ConfigBits[").getD 1 "" |>.splitOn "+" with
  | b :: _ => b.toNat?
  | [] => none

/-- Parse `LUT4AB_switch_matrix.v`. -/
def parseSwitchMatrix (txt : String) : Except String SwitchMatrix := do
  let lines := (txt.splitOn "\n").map stripWs
  let mut name := ""
  let mut inputs := #[]
  let mut outputs := #[]
  let mut nCfg := 0
  let mut vecs : Std.HashMap String (List SmSrc) := {}
  let mut prims := #[]
  let mut cur : Option (String × Option Nat × Option String) := none   -- (cell, base, out)
  for l in lines do
    if l.startsWith "module" then name := (l.drop 6).toString
    else if l.startsWith "parameterNoConfigBits=" then nCfg := ((l.drop 22).toString.toNat?).getD 0
    else if l.startsWith "input[" then pure ()
    else if l.startsWith "input" then inputs := inputs.push ((l.drop 5).toString.replace "," "")
    else if l.startsWith "output" then outputs := outputs.push ((l.drop 6).toString.replace "," "")
    else if l.startsWith "assign" then
      match (l.drop 6).toString.replace ";" "" |>.splitOn "=" with
      | [lhs, rhs] =>
        if lhs.endsWith "_input" then
          let elems := (rhs.replace "{" "" |>.replace "}" "").splitOn ","
          vecs := vecs.insert ((lhs.dropEnd 6).toString) (elems.reverse.map srcOf)
        else prims := prims.push (lhs, SmPrim.assign (srcOf rhs))
      | _ => throw s!"switch matrix: cannot read `{l}`"
    else if l.startsWith "cus_mux" then cur := some ((l.takeWhile (· != 'i')).toString, none, none)
    else if let some (cell, b, o) := cur then
      if l.startsWith ".S0(" || l.startsWith ".S(" then cur := some (cell, cfgBase l, o)
      else if l.startsWith ".X(" then cur := some (cell, b, some ((l.drop 3).toString.replace ")" ""))
      else if l.startsWith ");" then
        match b, o with
        | some base, some out =>
          let ins := vecs.getD out []
          let p ← match cell with
            | "cus_mux21" => pure (SmPrim.mux21 ins base)
            | "cus_mux41" => pure (SmPrim.mux41 ins base)
            | "cus_mux81" => pure (SmPrim.mux81 ins base)
            | "cus_mux161" => pure (SmPrim.mux161 ins base)
            | c => throw s!"switch matrix: primitive {c} is not one of models_pack.v's multiplexers"
          if ins.length != 2 ^ p.selBits then throw s!"switch matrix: {out} has {ins.length} inputs for {cell}"
          prims := prims.push (out, p)
          cur := none
        | _, _ => throw s!"switch matrix: an instance of {cell} without its select or output"
  let ins := inputs.toList.filter (fun n => n != "ConfigBits" && n != "ConfigBits_N")
  for (o, p) in prims do
    for s in p.ins do
      if let .port n := s then
        if !ins.contains n then throw s!"switch matrix: {o} reads {n}, which is not an input port"
  if prims.size != outputs.size then throw s!"switch matrix: {prims.size} primitives for {outputs.size} outputs"
  return { name, inputs := ins, outputs := outputs.toList, nCfg, prims := prims.toList }

/-- The Lean text of a switch matrix. -/
def smLean (defName : String) (sm : SwitchMatrix) : String :=
  let src : SmSrc → String
    | .port n => s!".port \"{n}\""
    | .const b => s!".const {b}"
  let prim : SmPrim → String
    | .assign s => s!".assign ({src s})"
    | p =>
      let c := match p with | .mux21 .. => "mux21" | .mux41 .. => "mux41" | .mux81 .. => "mux81" | _ => "mux161"
      s!".{c} [{", ".intercalate (p.ins.map src)}] {p.base}"
  let strs (xs : List String) := "[" ++ ", ".intercalate (xs.map (s!"\"{·}\"")) ++ "]"
  s!"def {defName} : SwitchMatrix where\n  name := \"{sm.name}\"\n  nCfg := {sm.nCfg}\n  inputs := {strs sm.inputs}\n" ++
  s!"  outputs := {strs sm.outputs}\n  prims := [\n" ++
  ",\n".intercalate (sm.prims.map fun (o, p) => s!"    (\"{o}\", {prim p})") ++ "]\n"

/-! ## The BELs, transcribed from their Verilog

Every signal is a 0/1 word; `m21 s a0 a1` is `cus_mux21` (`S ? A1 : A0`). -/

def m21 (s a0 a1 : RtlExpr) : RtlExpr := .mux s a1 a0
def bitOf (i k : Nat) : RtlExpr := .resize (.slice k k) (.inputPort i)
def andE (a b : RtlExpr) : RtlExpr := .alu .bitAnd a b
def orE (a b : RtlExpr) : RtlExpr := .alu .bitOr a b

/-- `LUT4c_frame_config_dffesr.v`. Inputs `I` (4), `Ci`, `SR`, `EN`, `ConfigBits` (19: `INIT` 0..15,
`FF` 16, `I0mux` 17, `SET_NORESET` 18). `O = c_out_mux ? LUT_flop : LUT_out` with
`LUT_out = LUT_values[{I3, I2, I1, I0mux}]` (`cus_mux161`), `I0mux = c_I0mux ? Ci : I0`;
`Co = Ci·I1 + Ci·I2 + I1·I2`; on the edge, with `EN`, `LUT_flop <= SR ? c_reset_value : LUT_out`. -/
def lut4cModule : RtlModule :=
  let cb (k : Nat) := bitOf 4 k
  -- wires: 0 = I0mux, 1 = LUT_out
  let sel : List RtlExpr := [.wireRef 0, bitOf 0 1, bitOf 0 2, bitOf 0 3]
  let rec tree : List RtlExpr → List RtlExpr → RtlExpr
    | [], xs => xs.headD (.const 0#64)
    | s :: ss, xs =>
      let rec pr : List RtlExpr → List RtlExpr
        | a :: b :: rest => m21 s a b :: pr rest
        | ys => ys
      tree ss (pr xs)
  { name := "LUT4c_frame_config_dffesr"
    inputNames := ["I", "Ci", "SR", "EN", "ConfigBits"]
    inputWidths := [4, 1, 1, 1, 19]
    wires :=
      [ { wireIdx := 0, name := "I0mux", width := 1, expr := m21 (cb 17) (bitOf 0 0) (.inputPort 1) }
      , { wireIdx := 1, name := "LUT_out", width := 1, expr := tree sel ((List.range 16).map cb) } ]
    regs :=
      [ { regIdx := 0, name := "LUT_flop", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false,
          width := 1, nextExpr := m21 (.inputPort 3) (.regRead 0) (m21 (.inputPort 2) (.wireRef 1) (cb 18)) } ]
    outputs :=
      [ { name := "O", width := 1, expr := m21 (cb 16) (.wireRef 1) (.regRead 0) }
      , { name := "Co", width := 1, expr :=
            orE (orE (andE (.inputPort 1) (bitOf 0 1)) (andE (.inputPort 1) (bitOf 0 2))) (andE (bitOf 0 1) (bitOf 0 2)) } ] }

/-- `MUX8LUT_frame_config_mux.v`. Inputs `A`..`H`, `S` (4), `ConfigBits` (2: `c0`, `c1`). -/
def mux8lutModule : RtlModule :=
  let i (k : Nat) : RtlExpr := .inputPort k
  let S (k : Nat) := bitOf 8 k
  let c0 := bitOf 9 0
  let c1 := bitOf 9 1
  let w (k : Nat) : RtlExpr := .wireRef k
  -- 0 AB, 1 sCD, 2 CD, 3 sEF, 4 EF, 5 sEH, 6 sGH, 7 GH, 8 AD, 9 EH, 10 AH, 11 EH_GH
  let ws : List (String × RtlExpr) :=
    [ ("AB", m21 (S 0) (i 0) (i 1)), ("sCD", m21 c0 (S 1) (S 0)), ("CD", m21 (w 1) (i 2) (i 3)),
      ("sEF", m21 c1 (S 2) (S 0)), ("EF", m21 (w 3) (i 4) (i 5)), ("sEH", m21 c1 (S 3) (S 1)),
      ("sGH", m21 c0 (w 5) (w 3)), ("GH", m21 (w 6) (i 6) (i 7)), ("AD", m21 (S 1) (w 0) (w 2)),
      ("EH", m21 (w 5) (w 4) (w 7)), ("AH", m21 (S 3) (w 8) (w 9)), ("EH_GH", m21 c0 (w 7) (w 9)) ]
  { name := "MUX8LUT_frame_config_mux"
    inputNames := ["A", "B", "C", "D", "E", "F", "G", "H", "S", "ConfigBits"]
    inputWidths := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
    wires := ws.zipIdx.map fun ((n, e), k) => { wireIdx := k, name := n, width := 1, expr := e }
    regs := []
    outputs :=
      [ { name := "M_AB", width := 1, expr := w 0 }, { name := "M_AD", width := 1, expr := m21 c0 (w 2) (w 8) }
      , { name := "M_AH", width := 1, expr := m21 c1 (w 11) (w 10) }, { name := "M_EF", width := 1, expr := w 4 } ] }

/-- The LEC harness of the switch matrix: FABulous's `LUT4AB_switch_matrix` with `ConfigBits` split into
the 64-bit words of `smModule` (and `ConfigBits_N` its complement, as `config_latch` drives it); every
other port passed through under its own name. -/
def smHarness (sm : SwitchMatrix) : String :=
  let nW := cfgWords sm.nCfg
  let wd (k : Nat) := if k + 1 == nW && sm.nCfg % 64 != 0 then sm.nCfg % 64 else 64
  let ports := sm.inputs.map (s!"    input {·}") ++ (List.range nW).map (fun k => s!"    input [{wd k - 1}:0] cfg{k}") ++
    sm.outputs.map (s!"    output {·}")
  let conns := (sm.inputs ++ sm.outputs).map (fun n => s!"    .{n}({n})") ++ ["    .ConfigBits(cb)", "    .ConfigBits_N(~cb)"]
  s!"// Generated by Obend.Hardware.Fabulous.smHarness; the LEC's view of FABulous's {sm.name}.
module {sm.name}_lec (
" ++
    ",
".intercalate ports ++ "
);
" ++
    s!"  wire [{sm.nCfg - 1}:0] cb = " ++ "{" ++ ", ".intercalate ((List.range nW).reverse.map (s!"cfg{·}")) ++ "};
" ++
    s!"  {sm.name} sm (
" ++ ",
".intercalate conns ++ "
  );
endmodule
"

/-! ## The decoder's routing table against the switch-matrix model

The decoder (`Obend.Hardware.Fabulous.Bitstream.driver`) reads a switch-matrix pip `src.dst` of
`bitStreamSpec.csv` as: when the tile's configuration bits match the pip's pattern, `dst` carries `src`.
`pipAgrees` checks one pip against the model, through `posOf` (the tile's `ConfigBits` index ↦ frame
position, `LUT4AB_ConfigMem.v`) and `off` (where the switch matrix's `ConfigBits` start in the tile's,
`LUT4AB.v`); `pip_sound` says that under it the model's `dst` is `src` whenever the decoder says so. -/

/-- The name a pip gives a multiplexer input (`GND0`, `VCC0` for the constants). -/
def SmSrc.name : SmSrc → String
  | .port n => n
  | .const false => "GND0"
  | .const true => "VCC0"

/-- The select value a pattern sets, read at the frame positions of select bits `base + c`. -/
def patSel (pat : List (Nat × Bool)) (posOf : Nat → Nat) (off base w : Nat) : Nat :=
  ((List.range w).map fun c => if pat.lookup (posOf (off + base + c)) == some true then 2 ^ c else 0).sum

/-- Pip `src.dst` with pattern `pat` against the switch-matrix primitive driving `dst`. -/
def pipAgrees (p : SmPrim) (posOf : Nat → Nat) (off : Nat) (src : String) (pat : List (Nat × Bool)) : Bool :=
  if pat.isEmpty then (match p with | .assign s => s.name == src | _ => false)
  else
    pat.length == p.selBits && p.selBits > 0 &&
    (List.range p.selBits).all (fun c => (pat.lookup (posOf (off + p.base + c))).isSome) &&
    ((p.ins[patSel pat posOf off p.base p.selBits]?).map (·.name)) == some src

theorem lookup_of_mem_holds {pat : List (Nat × Bool)} {f : Nat → Bool} (h : ∀ e ∈ pat, f e.1 = e.2)
    {q : Nat} {v : Bool} (hl : pat.lookup q = some v) : f q = v := by
  induction pat with
  | nil => simp at hl
  | cons e rest ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at hl
    by_cases hq : q = a
    · subst hq; simp at hl; subst hl; exact h _ (List.mem_cons_self ..)
    · have : (q == a) = false := by simpa using hq
      rw [this] at hl
      exact ih (fun e he => h e (List.mem_cons_of_mem _ he)) hl

/-- **`pip_sound`**: if a pip agrees with the switch-matrix primitive driving its destination, then
for every configuration whose frame bits satisfy the pip's pattern (`bits`, read through `posOf` and
`off` as the tile's `ConfigBits`) and every value of the inputs, the primitive's output is the pip's
source, which is what the decoder takes it to be. -/
theorem pip_sound (p : SmPrim) (posOf : Nat → Nat) (off : Nat) (src : SmSrc) (pat : List (Nat × Bool))
    (hAg : pipAgrees p posOf off src.name pat = true) (bits : Nat → Bool)
    (hPat : ∀ e ∈ pat, bits e.1 = e.2) (cfg : Nat → Bool) (hCfg : ∀ i, cfg i = bits (posOf (off + i)))
    (hNames : ∀ s ∈ p.ins, s.name = src.name → s = src) (inp : String → Bool) :
    p.eval cfg inp = src.eval inp := by
  unfold pipAgrees at hAg
  split at hAg
  · -- a hard-wired connection
    cases p with
    | assign s =>
      simp only [beq_iff_eq] at hAg
      have := hNames s (by simp [SmPrim.ins]) hAg
      subst this; simp [SmPrim.eval, SmPrim.ins, SmPrim.sel, SmPrim.selBits]
    | _ => simp at hAg
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hAg
    obtain ⟨⟨⟨_, _⟩, hSome⟩, hIdx⟩ := hAg
    have hsel : p.sel cfg = patSel pat (posOf) off p.base p.selBits := by
      unfold SmPrim.sel patSel
      congr 1
      apply List.map_congr_left
      intro c hc
      simp only [List.mem_range] at hc
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hSome c hc)
      have hb := lookup_of_mem_holds hPat hv
      rw [hCfg, show off + (p.base + c) = off + p.base + c by omega, hb, hv]
      cases v <;> simp
    unfold SmPrim.eval
    rw [hsel]
    cases hget : p.ins[patSel pat posOf off p.base p.selBits]? with
    | none => rw [hget] at hIdx; simp at hIdx
    | some s =>
      rw [hget] at hIdx
      simp only [Option.map_some, Option.some.injEq] at hIdx
      have hs := hNames s (List.mem_of_getElem? hget) hIdx
      subst hs; rfl

/-- `ConfigBits[i] = Emulate_Bitstream[j]` of `LUT4AB_ConfigMem.v`'s emulation branch: index ↦ frame position. -/
def parseConfigMap (txt : String) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for l in txt.splitOn "\n" do
    let l := stripWs l
    if l.startsWith "assignConfigBits[" then
      match (l.drop 17).toString.splitOn "]=Emulate_Bitstream[" with
      | [i, rest] => match i.toNat?, ((rest.splitOn "]").headD "").toNat? with
        | some i, some j => m := m.insert i j
        | _, _ => pure ()
      | _ => pure ()
  return m

/-- From a tile's top-level Verilog (`LUT4AB.v`): where its switch matrix's `ConfigBits` start, and its
LUT4 cells by port prefix with where each cell's `ConfigBits` start (`.ConfigBits(ConfigBits[HI-1:LO])`
of each instance). -/
def parseTileLayout (txt : String) : Nat × List (String × Nat) := Id.run do
  let mut cur : String × String := ("", "")
  let mut smOff := 0
  let mut cells : Array (String × Nat) := #[]
  for l in txt.splitOn "\n" do
    let ws := (l.trimAscii.toString.splitOn " ").filter (· != "")
    match ws with
    | [m, inst, "("] => if inst.startsWith "Inst_" then cur := (m, (inst.drop 5).toString)
    | _ =>
      let l := stripWs l
      if l.startsWith ".ConfigBits(ConfigBits[" then
        match ((l.drop 23).toString.splitOn ":").getD 1 "" |>.splitOn "]" with
        | lo :: _ =>
          if let some lo := lo.toNat? then
            if cur.1.endsWith "_switch_matrix" then smOff := lo
            else if cur.1 == "LUT4c_frame_config_dffesr" then
              cells := cells.push (((cur.2.splitOn "LUT4c").headD ""), lo)
        | [] => pure ()
  return (smOff, cells.toList)

/-- The frame position of each `ConfigBits` index, as a list. -/
def configPosList (m : Std.HashMap Nat Nat) : List Nat :=
  let n := m.fold (fun k i _ => max k (i + 1)) 0
  (List.range n).map fun i => m.getD i 0

/-- The Lean text of a tile model. -/
def tileModelLean (defName smName : String) (pos : List Nat) (smOff : Nat) (cells : List (String × Nat)) : String :=
  s!"def {defName} : TileModel where\n  sm := {smName}\n  smOff := {smOff}\n" ++
  "  cells := [" ++ ", ".intercalate (cells.map fun (p, o) => s!"(\"{p}\", {o})") ++ "]\n" ++
  "  pos := [" ++ ", ".intercalate (pos.map toString) ++ "]\n"

end Obend.Hardware.Fabulous
