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
- `obend fabric flip --project DIR --bin FILE (--feature TILE.FEATURE | --node TILE.WIRE) --out FILE`: the
  bitstream with the first bit of a feature, or a select bit of the switch-matrix multiplexer driving a
  wire, inverted (the verify script's planted faults).
- `obend fabric vectors --out FILE [--cycles N]`: seeded cycles and `mac_out` before each edge from
  `moduleRun iceStickMac8`, for `hardware/fabulous/mac8_fabric_tb.v`; refused unless `mac8Net.run`
  shows the same on every cycle after the first reset.
-/
public import Obend.Hardware.Fabulous.Extract
public import Obend.Hardware.Fabulous.Mac8
public import Obend.Hardware.Fabulous.LUT4ABSwitchMatrix
public import Obend.Hardware.YosysLec
public import Obend.Hardware.Fabulous.CertGen
public import Obend.Hardware.Fabulous.Bin
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

/-- A bitstream's bytes as a little-endian number (the form of `Mac8Bin.lean`). -/
def binNat (b : ByteArray) : Nat := b.toList.foldr (fun x acc => acc * 256 + x.toNat) 0

/-- The hypotheses of `readback_sound` for certificate `C` and net `N` that a bitstream and a project
discharge outside Lean: the bits `C.required N` are the bitstream's, the wires `C.wiresUsed` are fixed
pips of FABulous's `pips.txt`, and the tiles of `C` have their `fabric.csv` types. -/
def certHyps (fab : Fabric) (cfg : HashMap String Nat) (types : HashMap (Nat × Nat) String) (C : Cert) (N : Net) :
    Except String String := do
  let req := C.required N
  for (x, y, p, v) in req do
    if (cfg.getD (tileName x y) 0).testBit p != v then
      throw s!"tile {tileName x y} bit {p} (frame {p / 32}, bit {p % 32}) is {!v}; the certificate requires {v}"
  let ws := C.wiresUsed
  for (src, dst) in ws do
    let pips := fab.into.getD (tileName dst.x dst.y ++ "." ++ dst.w) #[]
    let ok := pips.size == 1 && pips.toList.all fun (st, sw, f) =>
      st == tileName src.x src.y && sw == src.w && (fab.spec.getD (st ++ "." ++ f) []).isEmpty
    if !ok then throw s!"{tileName src.x src.y}.{src.w} -> {tileName dst.x dst.y}.{dst.w} is not a fixed wire of pips.txt"
  for ((x, y), i) in C.tiles do
    if types.get? (x, y) != (tileModels[i]?.map (·.1)) then
      throw s!"tile {tileName x y} is not a {(tileModels[i]?.map (·.1)).getD "?"} in fabric.csv"
  return s!"{req.length} required configuration bits present, {ws.length} wires fixed in pips.txt, {C.tiles.length} tiles of their fabric.csv types"

/-- The tile-level hypotheses of `mac8_fabric_tiles_realize_module` for this bitstream. -/
def checkTiles (fab : Fabric) (cfg : HashMap String Nat) (dir : String) (binPathT : String) : IO UInt32 := do
  let types := parseFabricCsv (← IO.FS.readFile s!"{dir}/fabric.csv")
  let C ← match extractS fab cfg mac8Pins with
    | .ok (_, s) => match buildCert fab cfg types mac8Pins s with
      | .ok C => pure C
      | .error e => IO.eprintln s!"refused: no readback certificate: {e}"; return 1
    | .error e => IO.eprintln s!"refused: {e}"; return 1
  -- `verify_fabric.sh` also exercises `obend fabric cert` and `obend fabric binlit` on demand
  -- and verifies the same required bits through `binBits` / `binFramed`
  let bin := binNat (← IO.FS.readBinFile binPathT)
  if !binFramed fab.cols fab.rows bin (← IO.FS.readBinFile binPathT).size then
    IO.eprintln "refused: the bitstream is not laid out as binBits reads it"; return 1
  if !(C.required mac8Net).all (fun r => binBits fab.rows bin r.1 r.2.1 r.2.2.1 == r.2.2.2) then
    IO.eprintln "refused: binBits does not read the required bits"; return 1
  match certHyps fab cfg types C mac8Net with
  | .ok msg =>
    IO.println s!"fabric check: readback certificate: {msg}; binBits reads them too"
    return 0
  | .error e => IO.eprintln s!"refused: {e}"; return 1

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
      return ← checkTiles fab cfg (← need "--project" args) binPath
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
  -- `--node TILE.WIRE`: a select bit of the switch-matrix multiplexer driving that wire
  let feat ← match flagVal "--node" args with
    | some n => match (fab.into.getD n #[]).toList.find? (fun (st, _, f) => (fab.spec.getD (st ++ "." ++ f) []) != []) with
      | some (st, _, f) => pure (st ++ "." ++ f)
      | none => do IO.eprintln s!"obend fabric flip: no multiplexer drives {n}"; return 1
    | none => need "--feature" args
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

/-- Lean names of a tile type's generated module: `LUT4AB` ↦ `LUT4ABSwitchMatrix`, `lut4ab`. -/
def tileNames (t : String) : String × String :=
  let base := t.replace "_" ""
  (base ++ "SwitchMatrix", base.toLower)

/-- `obend fabric tile --project DIR [--tile T] --out-lean FILE --out-harness FILE`: tile type `T`'s
switch matrix and tile model, from `Tile/T/T_switch_matrix.v`, `T_ConfigMem.v` and `T.v`. -/
def cmdTile (args : List String) : IO UInt32 := do
  let dir ← need "--project" args
  let t := (flagVal "--tile" args).getD "LUT4AB"
  let (modName, low) := tileNames t
  let txt ← IO.FS.readFile s!"{dir}/Tile/{t}/{t}_switch_matrix.v"
  let pos := configPosList (parseConfigMap (← IO.FS.readFile s!"{dir}/Tile/{t}/{t}_ConfigMem.v"))
  let (smOff, cells) := parseTileLayout (← IO.FS.readFile s!"{dir}/Tile/{t}/{t}.v")
  match parseSwitchMatrix txt with
  | .error e => IO.eprintln s!"refused: {e}"; return 1
  | .ok sm =>
    let hdr := s!"module\n/-\n# Obend.Hardware.Fabulous.{modName} — the {t} switch matrix and tile model of `hardware/fabulous/fabric.csv`\n\n" ++
      s!"Generated by `obend fabric tile` from FABulous's `Tile/{t}/{t}_switch_matrix.v`, `{t}_ConfigMem.v` and `{t}.v`;\n" ++
      s!"do not edit. `hardware/fabulous/lec_tile.sh` checks `smModule {low}SwitchMatrix` against that Verilog.\n-/\n" ++
      "public import Obend.Hardware.Fabulous.Tile\n@[expose] public section\n\nnamespace Obend.Hardware.Fabulous\n\n"
    IO.FS.writeFile (← need "--out-lean" args)
      (hdr ++ smLean s!"{low}SwitchMatrix" sm ++ "\n" ++ tileModelLean s!"{low}Model" s!"{low}SwitchMatrix" pos smOff cells ++
        "\nend Obend.Hardware.Fabulous\n")
    IO.FS.writeFile (← need "--out-harness" args) (smHarness sm)
    IO.println s!"switch matrix {sm.name}: {sm.inputs.length} inputs, {sm.outputs.length} outputs, {sm.nCfg} configuration bits, {sm.prims.length} primitives; {cells.length} LUT4 cells, switch matrix at ConfigBits[{smOff}]"
    return 0

/-- The planted fault of the tile LEC: the switch matrix with the first two inputs of its first
multiplexer exchanged, a one-entry change to the table. -/
def smMutant (sm : SwitchMatrix) : SwitchMatrix × String :=
  let swap : SmPrim → SmPrim
    | .mux21 (a :: b :: r) k => .mux21 (b :: a :: r) k
    | .mux41 (a :: b :: r) k => .mux41 (b :: a :: r) k
    | .mux81 (a :: b :: r) k => .mux81 (b :: a :: r) k
    | .mux161 (a :: b :: r) k => .mux161 (b :: a :: r) k
    | p => p
  match sm.prims.findIdx? (fun (_, p) => p.selBits > 0) with
  | some i =>
    let o := (sm.prims[i]?.map (·.1)).getD "?"
    ({ sm with prims := sm.prims.modify i fun (o, p) => (o, swap p) }, s!"inputs 0 and 1 of the multiplexer driving {o} exchanged")
  | none => (sm, "no multiplexer")

/-- `obend fabric tile-mutant --out FILE`: the Lean half of the LEC for `smMutant lut4abSwitchMatrix`. -/
def cmdTileMutant (args : List String) : IO UInt32 := do
  let (sm, what) := smMutant lut4abSwitchMatrix
  IO.FS.writeFile (← need "--out" args) (Obend.Hardware.YosysLec.emitYosysLecSmt2 (smModule sm))
  IO.println s!"mutant switch matrix: {what}"
  return 0

/-- `obend fabric tile-agree --project DIR`: every switch-matrix pip of every `LUT4AB` tile in the
project's `bitStreamSpec.csv` / `pips.txt` against `lut4abSwitchMatrix` (`pipAgrees`, the hypothesis
of `pip_sound`), and every LUT4 cell and MUX8LUT feature against the `ConfigBits` slice `LUT4AB.v`
gives that BEL, through `LUT4AB_ConfigMem.v`'s index-to-position map. -/
def cmdTileAgree (args : List String) : IO UInt32 := do
  let dir ← need "--project" args
  let fab ← loadProject dir
  let posMap := parseConfigMap (← IO.FS.readFile s!"{dir}/Tile/LUT4AB/LUT4AB_ConfigMem.v")
  let posOf (i : Nat) : Nat := posMap.getD i 100000
  -- `--mutant`: against `smMutant lut4abSwitchMatrix`, which must be refused
  let sm := if args.contains "--mutant" then (smMutant lut4abSwitchMatrix).1 else lut4abSwitchMatrix
  let off := 154
  let prims : Std.HashMap String SmPrim := sm.prims.foldl (fun m (o, p) => m.insert o p) {}
  let tiles := fab.bels.toList.filterMap fun (t, bs) => if bs.any (·.2.1 == lutType) then some t else none
  let mut pips := 0
  let mut feats := 0
  let mut bad : Array String := #[]
  for t in tiles do
    for (o, p) in sm.prims do
      -- distinct sources carry distinct names (the `hNames` hypothesis of `pip_sound`)
      let names := p.ins.map (·.name)
      if p.ins.any (fun a => p.ins.any fun b => a.name == b.name && a != b) then bad := bad.push s!"{t}.{o}: two inputs share a name"
      let _ := names
      for (st, sw, f) in fab.into.getD (t ++ "." ++ o) #[] do
        if st != t then continue
        let pat := fab.spec.getD (st ++ "." ++ f) []
        pips := pips + 1
        if !pipAgrees p posOf off sw pat then bad := bad.push s!"{t}: pip {f} disagrees with the switch-matrix model"
    let _ := prims
    for (l, k) in ["A", "B", "C", "D", "E", "F", "G", "H"].zipIdx do
      let feat (name : String) (b : Nat) : List (String × Nat) := [(name, 19 * k + b)]
      let fs := (List.range 16).flatMap (fun b => feat (if b == 0 then l ++ ".INIT" else s!"{l}.INIT[{b}]") b) ++
        feat (l ++ ".FF") 16 ++ feat (l ++ ".I0mux") 17 ++ feat (l ++ ".SET_NORESET") 18
      for (name, idx) in fs do
        feats := feats + 1
        if fab.spec.get? (t ++ "." ++ name) != some [(posOf idx, true)] then
          bad := bad.push s!"{t}: feature {name} is not ConfigBits[{idx}] (position {posOf idx})"
    for (name, idx) in [("I.c0", 152), ("I.c1", 153)] do
      feats := feats + 1
      if fab.spec.get? (t ++ "." ++ name) != some [(posOf idx, true)] then
        bad := bad.push s!"{t}: feature {name} is not ConfigBits[{idx}]"
  if bad.isEmpty then
    IO.println s!"tile-agree: {tiles.length} LUT4AB tiles, {pips} switch-matrix pips agree with lut4abSwitchMatrix (pipAgrees), {feats} BEL features are the ConfigBits LUT4AB.v gives them"
    return 0
  for b in bad.toList.take 20 do IO.eprintln s!"  {b}"
  IO.eprintln s!"refused: {bad.size} disagreements"
  return 1

/-- The certificate of a bitstream on a project's fabric. -/
def certOf (dir : String) (bin : ByteArray) : IO (Except String (Net × Cert)) := do
  let fab ← loadProject dir
  let types := parseFabricCsv (← IO.FS.readFile s!"{dir}/fabric.csv")
  match decodeBin fab.cols fab.rows bin with
  | .error e => return .error e
  | .ok cfg =>
    match extractS fab cfg mac8Pins with
    | .error e => return .error e
    | .ok (N, s) => return (buildCert fab cfg types mac8Pins s).map (N, ·)

/-- `obend fabric cert --project DIR --bin FILE --out FILE`: write `Mac8Cert.lean`. -/
def cmdCert (args : List String) : IO UInt32 := do
  let dir ← need "--project" args
  let binPath ← need "--bin" args
  match ← certOf dir (← IO.FS.readBinFile binPath) with
  | .error e => IO.eprintln s!"refused: {binPath}: {e}"; return 1
  | .ok (N, C) =>
    if args.contains "--mutant" then
      -- the planted fault: the first switch-matrix entry that reads another entry, its select changed
      let ok (e : Entry) : Bool := e.next.isSome && match e.hop with | .sm .. => true | _ => false
      let flip (e : Entry) : Entry := { e with hop := match e.hop with | .sm k i => .sm k (i ^^^ 1) | h => h }
      let (chunks, done) := C.chunks.foldl (fun (acc, done) (k, es) =>
        if done then (acc.push (k, es), true) else
          match es.findIdx? ok with
          | some j => (acc.push (k, es.modify j flip), true)
          | none => (acc.push (k, es), false)) (#[], false)
      if !done then
        IO.eprintln "no switch-matrix entry"; return 1
      let C' := { C with chunks := chunks.toList }
      if C'.check N || C'.checkF N (endCodes C') then
        IO.eprintln "[FAIL] Cert.check or Cert.checkF accepted a certificate with a switch-matrix select changed"; return 1
      IO.println "mutant certificate (one switch-matrix select changed): Cert.check and Cert.checkF refuse it"
      return 0
    let out ← need "--out" args
    IO.FS.writeFile out (certLean C (flagVal "--source" args |>.getD binPath))
    if let some chk := flagVal "--out-check" args then
      IO.FS.writeFile chk (checkLean C N.gates.length N.flops.length N.outs.length)
    IO.println s!"wrote {out}: {C.entries.length} wires in the cone, {C.gates.length} gates, {C.flops.length} flops, {C.outs.length} outputs, {C.tiles.length} tiles; check against the net: {C.check N}, kernel-cheap form: {C.checkF N (endCodes C)}"
    return 0

/-- `obend fabric binlit --project DIR --bin FILE --out FILE`: write `Mac8Bin.lean`, the bitstream as data. -/
def cmdBinlit (args : List String) : IO UInt32 := do
  let fab ← loadProject (← need "--project" args)
  let binPath ← need "--bin" args
  let out ← need "--out" args
  IO.FS.writeFile out (binLean "mac8Bin" fab.cols fab.rows (← IO.FS.readBinFile binPath) (flagVal "--source" args |>.getD binPath))
  IO.println s!"wrote {out}"
  return 0

def cmdFabric : List String → IO UInt32
  | "wrapper" :: args => do
    IO.FS.writeFile (← need "--out" args) (topWrapper iceStickMac8 mac8Pins); return 0
  | "extract" :: args => cmdExtract args
  | "check" :: args => cmdCheck args
  | "flip" :: args => cmdFlip args
  | "vectors" :: args => cmdVectors args
  | "tile" :: args => cmdTile args
  | "tile-mutant" :: args => cmdTileMutant args
  | "tile-agree" :: args => cmdTileAgree args
  | "cert" :: args => cmdCert args
  | "binlit" :: args => cmdBinlit args
  | _ => do IO.eprintln "usage: obend fabric (wrapper|extract|check|flip|vectors|tile|tile-mutant|tile-agree|cert|binlit) ..."; return 2

end Obend.Hardware.Fabulous
