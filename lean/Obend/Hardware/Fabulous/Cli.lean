module
/-
# Obend.Hardware.Fabulous.Cli — `obend fabric …`

- `obend fabric wrapper --out FILE`: `top_wrapper.v` for `iceStickMac8` on the pins of `mac8Pins`.
- `obend fabric extract --project DIR --bin FILE --out FILE`: read the bitstream back against the
  project's FABulous metadata and write `Mac8Net.lean` (`mac8NetLean`).
- `obend fabric check --project DIR --bin FILE [--golden FILE]`: read the bitstream back and refuse it
  unless it is `mac8Net`, the net `mac8_fabric_realizes_module` is about. With `--golden`, a refusal
  names every configuration bit the verified net reads that this bitstream has otherwise: tile,
  position, frame and bit, and the feature that bit belongs to.
- `obend fabric flip --project DIR --bin FILE --feature TILE.FEATURE --out FILE`: the bitstream with
  the first bit of a feature inverted (the verify script's planted fault).
- `obend fabric vectors --out FILE [--cycles N]`: seeded cycles and `mac_out` before each edge from
  `moduleRun iceStickMac8`, for `hardware/fabulous/mac8_fabric_tb.v`; refused unless `mac8Net.run`
  shows the same on every cycle after the first reset.
-/
public import Obend.Hardware.Fabulous.Extract
public import Obend.Hardware.Fabulous.Mac8
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware Obend.Hardware.HDL Std

def flagVal (flag : String) : List String → Option String
  | f :: v :: rest => if f == flag then some v else flagVal flag rest
  | _ => none

def need (flag : String) (args : List String) : IO String :=
  match flagVal flag args with
  | some v => pure v
  | none => throw (IO.userError s!"obend fabric: missing {flag}")

/-- The features of `tile` whose bits include position `pos`. -/
def featuresAt (fab : Fabric) (tile : String) (pos : Nat) : List String :=
  fab.spec.toList.filterMap fun (k, pat) =>
    if k.startsWith (tile ++ ".") && pat.any (·.1 == pos) then some ((k.drop (tile.length + 1)).toString) else none

/-- Byte offset and bit of configuration bit `pos` of tile `(x, y)` in a bitstream. -/
def bitLocation (rows x y pos : Nat) : Nat × Nat :=
  let interior := rows - 2
  let f := pos / 32
  let j := pos % 32
  let word := 20 + (x * 20 + f) * (4 + 4 * interior) + 4 + 4 * (rows - 2 - y)
  (word + (3 - j / 8), j % 8)

def cmdCheck (args : List String) : IO UInt32 := do
  let fab ← loadProject (← need "--project" args)
  let binPath ← need "--bin" args
  let bin ← IO.FS.readBinFile binPath
  let cfg ← match decodeBin fab.cols fab.rows bin with
    | .ok c => pure c
    | .error e => IO.eprintln s!"refused: {binPath}: {e}"; return 1
  let verdict := extract fab cfg mac8Pins
  match verdict with
  | .ok (N, sup) =>
    if N == mac8Net then
      IO.println s!"fabric check: {binPath} reads back to mac8Net ({N.gates.length} LUT4 gates, {N.flops.length} flops, {N.outs.length} output pins, {sup.size} configuration bits read); mac8_fabric_realizes_module applies"
      return 0
  | .error _ => pure ()
  let why := match verdict with
    | .ok _ => "it reads back to a net other than mac8Net"
    | .error e => s!"it does not read back: {e}"
  IO.eprintln s!"refused: {binPath}: {why}"
  if let some g := flagVal "--golden" args then
    let gbin ← IO.FS.readBinFile g
    match decodeBin fab.cols fab.rows gbin, readBack fab gbin with
    | .ok gcfg, .ok (gN, gsup) =>
      if gN != mac8Net then IO.eprintln s!"  (the golden {g} is not mac8Net either)"; return 1
      let mut n := 0
      for ((tile, pos), v) in gsup.toList do
        let have_ := (cfg.getD tile 0).testBit pos
        if have_ != v then
          n := n + 1
          let feats := featuresAt fab tile pos
          IO.eprintln s!"  tile {tile} bit {pos} (frame {pos / 32}, bit {pos % 32}): the verified configuration has {if v then 1 else 0}, this bitstream {if have_ then 1 else 0}; feature {", ".intercalate feats}"
      let _ := gcfg
      if n == 0 then IO.eprintln "  every bit the verified net reads agrees with the golden; the difference is elsewhere"
    | _, _ => IO.eprintln s!"  (the golden {g} does not read back)"
  return 1

def cmdFlip (args : List String) : IO UInt32 := do
  let fab ← loadProject (← need "--project" args)
  let bin ← IO.FS.readBinFile (← need "--bin" args)
  let feat ← need "--feature" args
  let (tile, f) := match feat.splitOn "." with
    | t :: rest => (t, ".".intercalate rest)
    | [] => ("", "")
  match fab.spec.get? (tile ++ "." ++ f), parseTile tile with
  | some ((pos, _) :: _), some (x, y) =>
    let (byte, bit) := bitLocation fab.rows x y pos
    let b := bin.set! byte ((bin.get! byte) ^^^ (1 <<< bit.toUInt8))
    IO.FS.writeBinFile (← need "--out" args) b
    IO.println s!"flipped tile {tile} bit {pos} (frame {pos / 32}, bit {pos % 32}; byte {byte} bit {bit}), feature {f}"
    return 0
  | _, _ => IO.eprintln s!"obend fabric flip: no feature {feat} with bits"; return 1

def cmdExtract (args : List String) : IO UInt32 := do
  let fab ← loadProject (← need "--project" args)
  let binPath ← need "--bin" args
  match readBack fab (← IO.FS.readBinFile binPath) with
  | .error e => IO.eprintln s!"refused: {binPath}: {e}"; return 1
  | .ok (N, _) =>
    match mac8FlopMapOf N with
    | .error e => IO.eprintln s!"refused: {e}"; return 1
    | .ok fm =>
      let out ← need "--out" args
      IO.FS.writeFile out (mac8NetLean N fm (flagVal "--source" args |>.getD binPath))
      IO.println s!"wrote {out}: {N.gates.length} gates, {N.flops.length} flops"
      return 0

def hex64 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (16 - d.length) '0' ++ d)

def cmdVectors (args : List String) : IO UInt32 := do
  let n := (flagVal "--cycles" args >>= String.toNat?).getD 256
  let tr := seededCycles iceStickMac8 n 7
  -- `moduleRun` and `Net.run` cycle by cycle, each state read into an array once per cycle (a
  -- function-valued state recomputes every earlier cycle on every read).
  let nr := iceStickMac8.regs.length
  let nf := mac8Net.flops.length
  let mut regs : Array (BitVec 64) := Array.replicate nr 0#64
  let mut q : Array Bool := Array.replicate nf false
  let mut lines := #[]
  let mut t := 0
  for c in tr do
    let rf : Nat → BitVec 64 := fun i => regs.getD i 0#64
    let qf : Nat → Bool := fun k => q.getD k false
    let pins := pinValues mac8Pins c
    let outs := evalModuleOutputsW iceStickMac8 c.2 rf
    let want := mac8Net.outs.map fun (p, _) => (p, outPinValue mac8Pins outs p)
    if t > 0 && mac8Net.outputs pins qf != want then
      IO.eprintln s!"refused: mac8Net and iceStickMac8 disagree on cycle {t} of the seeded trace"; return 1
    let w := (if c.1 then 1 <<< 32 else 0) ||| (c.2 2).toNat <<< 16 ||| (c.2 1).toNat <<< 8 ||| (c.2 0).toNat
    let o := match outs with | (_, v) :: _ => v.toNat | [] => 0
    lines := lines.push (hex64 w) |>.push (hex64 o)
    let r' := stepModuleRegs iceStickMac8 c.1 c.2 rf
    let q' := mac8Net.step pins qf
    regs := (List.range nr).toArray.map r'
    q := (List.range nf).toArray.map q'
    t := t + 1
  IO.FS.writeFile (← need "--out" args) ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"wrote {n} cycles; mac8Net shows what iceStickMac8 computes on every cycle after the first reset"
  return 0

def cmdFabric : List String → IO UInt32
  | "wrapper" :: args => do
    IO.FS.writeFile (← need "--out" args) (topWrapper iceStickMac8 mac8Pins); return 0
  | "extract" :: args => cmdExtract args
  | "check" :: args => cmdCheck args
  | "flip" :: args => cmdFlip args
  | "vectors" :: args => cmdVectors args
  | _ => do IO.eprintln "usage: obend fabric (wrapper|extract|check|flip|vectors) ..."; return 2

end Obend.Hardware.Fabulous
