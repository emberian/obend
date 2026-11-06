module
/-
# Obend.Hardware.Fabulous.CertGen — the readback certificate from an extraction

`buildCert` turns the paths `extractS` followed into a `Cert` (`Obend.Hardware.Fabulous.Readback`): each
pip into a switch-matrix output of a modelled tile becomes `Hop.sm k i`, with `i` the select the tile
model computes from the decoded bits (and refused unless that input is the pip's source), every other pip
a `Hop.wire`. `certLean` writes it as Lean; `obend fabric cert` writes `Mac8Cert.lean`.
-/
public import Obend.Hardware.Fabulous.Bitstream
public import Obend.Hardware.Fabulous.Readback
public import Obend.Hardware.Fabulous.LUT4ABSwitchMatrix
public import Obend.Hardware.Fabulous.WIOSwitchMatrix
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware Obend.Hardware.HDL Std

/-- The modelled tile types, in the order of `Cert.models`. -/
def tileModels : List (String × String × TileModel) :=
  [("LUT4AB", "lut4abModel", lut4abModel), ("W_IO", "wioModel", wioModel)]

/-- `fabric.csv`: `(x, y)` ↦ tile type. -/
def parseFabricCsv (txt : String) : HashMap (Nat × Nat) String := Id.run do
  let mut m : HashMap (Nat × Nat) String := {}
  let mut y := 0
  let mut inFab := false
  for l in txt.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.startsWith "FabricBegin" then inFab := true; continue
    if l.startsWith "FabricEnd" then inFab := false; continue
    if !inFab || l.isEmpty then continue
    for (t, x) in (l.splitOn ",").zipIdx do
      m := m.insert (x, y) t.trimAscii.toString
    y := y + 1
  return m

def nodeOf (n : String) : Except String Node :=
  let (t, w) := splitNode n
  match parseTile t with
  | some (x, y) => .ok ⟨x, y, w⟩
  | none => .error s!"{n}: not a tile wire"

/-- The certificate of an extraction. -/
def buildCert (fab : Fabric) (cfg : HashMap String Nat) (types : HashMap (Nat × Nat) String) (pm : List Pin)
    (s : ExState) : Except String Cert := do
  let modelIdx (x y : Nat) : Option Nat := (types.get? (x, y)) >>= fun t => tileModels.findIdx? (·.1 == t)
  let model (x y : Nat) : Option TileModel := (modelIdx x y) >>= fun i => (tileModels[i]?.map (·.2.2))
  let mut used : HashSet (Nat × Nat) := {}
  let hopsOf (start : String) : StateT (HashSet (Nat × Nat)) (Except String) (List Hop) := do
    let some (steps, _) := s.paths.get? start | throw s!"{start}: the extraction did not trace it"
    let mut hops := #[]
    for (d, src) in steps do
      let dn ← nodeOf d
      let sn ← nodeOf src
      let pips := fab.into.getD d #[]
      let fixed := pips.size == 1 && (pips.toList.all fun (st, _, f) => (fab.spec.getD (st ++ "." ++ f) []).isEmpty)
      match model dn.x dn.y with
      | some tm =>
        match tm.sm.prims.findIdx? (·.1 == dn.w) with
        | some k =>
          if dn.x != sn.x || dn.y != sn.y then throw s!"{d}: a switch-matrix output driven from another tile"
          let p := (tm.sm.prims[k]?.map (·.2)).getD default
          let bits := cfg.getD (tileName dn.x dn.y) 0
          let i := p.sel (tm.smCfg bits.testBit)
          match p.ins[i]? with
          | some src' =>
            if src'.name != sn.w then
              throw s!"{d}: the tile model selects {src'.name}, the decoder {sn.w}"
          | none => throw s!"{d}: the tile model's select {i} is past its inputs"
          modify (·.insert (dn.x, dn.y))
          hops := hops.push (Hop.sm k i)
        | none =>
          if !fixed then throw s!"{d}: a configurable pip outside the switch-matrix model"
          hops := hops.push (Hop.wire sn)
      | none =>
        if !fixed then throw s!"{d}: a configurable pip in a tile with no model"
        hops := hops.push (Hop.wire sn)
    return hops.toList
  let cellOf (site : String) : Except String (Nat × Nat × String) := do
    let (t, l) := splitNode site
    let some (x, y) := parseTile t | throw s!"{site}: not a tile"
    let some (_, _, pre) := (fab.bels.getD t #[]).find? (·.1 == l) | throw s!"{site}: no such BEL"
    return (x, y, pre)
  let flopSites : HashSet String := s.flops.foldl (fun acc f => match f with | some f => acc.insert f.site | none => acc) {}
  let mut gates := #[]
  for g in s.gates do
    let (x, y, pre) ← cellOf g.site
    used := used.insert (x, y)
    let t := tileName x y
    let mut ins := #[]
    for i in List.range 4 do
      if usesInput g.init.toNat i then
        let (h, u) ← (hopsOf s!"{t}.{pre}I{i}").run used
        used := u
        ins := ins.push (some h)
      else ins := ins.push none
    gates := gates.push { x, y, pre, isFlop := flopSites.contains g.site, ins := ins.toList : GateCert }
  let mut flops := #[]
  for f in s.flops do
    let some f := f | throw "a flop was left unfilled"
    let (x, y, pre) ← cellOf f.site
    let t := tileName x y
    let some gate := s.gateOf.get? f.site | throw s!"{f.site}: its LUT is not a gate"
    let (en, u) ← (hopsOf s!"{t}.{pre}EN").run used
    let (sr, u) ← (hopsOf s!"{t}.{pre}SR").run u
    used := u
    flops := flops.push { x, y, pre, gate, en, sr : FlopCert }
  let mut outs := #[]
  let mut pads := #[]
  for h : k in [0:pm.length] do
    let p := pm[k]
    let some (x, y) := parseTile p.tile | throw s!"{p.tile}: not a tile"
    match p.role with
    | .output _ _ =>
      let n := s!"{p.tile}.{p.bel}_I"
      let (hs, u) ← (hopsOf n).run used
      used := u
      outs := outs.push (k, (⟨x, y, p.bel ++ "_I"⟩ : Node), hs)
    | _ => pads := pads.push (k, (⟨x, y, p.bel ++ "_O"⟩ : Node))
  let tiles := used.toList.mergeSort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)) |>.filterMap fun (x, y) =>
    (modelIdx x y).map fun i => ((x, y), i)
  return { models := tileModels.map (·.2.2), tiles, gates := gates.toList, flops := flops.toList,
           outs := outs.toList, pads := pads.toList }

def nodeLean (n : Node) : String := s!"⟨{n.x}, {n.y}, \"{n.w}\"⟩"

def hopLean : Hop → String
  | .sm k i => s!".sm {k} {i}"
  | .wire n => s!".wire {nodeLean n}"

def hopsLean (hs : List Hop) : String := "[" ++ ", ".intercalate (hs.map hopLean) ++ "]"

/-- The text of `Mac8Cert.lean`: one definition per gate, flop and output path. -/
def certLean (C : Cert) (source : String) : String := Id.run do
  let mut out := "module\n/-\n# Obend.Hardware.Fabulous.Mac8Cert — the readback certificate of `hardware/fabulous/obend_ice40_mac8.bin`\n\n" ++
    s!"Generated by `obend fabric cert` from {source}; do not edit. Every input of every gate and flop of\n" ++
    "`mac8Net` and every output pin, with the hops the extraction followed back to its source.\n-/\n" ++
    "public import Obend.Hardware.Fabulous.Readback\npublic import Obend.Hardware.Fabulous.LUT4ABSwitchMatrix\n" ++
    "public import Obend.Hardware.Fabulous.WIOSwitchMatrix\n@[expose] public section\n\nnamespace Obend.Hardware.Fabulous\n\n"
  for (g, k) in C.gates.zipIdx do
    let ins := g.ins.map fun | some hs => s!"some {hopsLean hs}" | none => "none"
    out := out ++ s!"def mac8CertG{k} : GateCert := ⟨{g.x}, {g.y}, \"{g.pre}\", {g.isFlop}, [{", ".intercalate ins}]⟩\n"
  for (f, k) in C.flops.zipIdx do
    out := out ++ s!"def mac8CertF{k} : FlopCert := ⟨{f.x}, {f.y}, \"{f.pre}\", {f.gate}, {hopsLean f.en}, {hopsLean f.sr}⟩\n"
  for ((p, n, hs), k) in C.outs.zipIdx do
    out := out ++ s!"def mac8CertO{k} : Nat × Node × List Hop := ({p}, {nodeLean n}, {hopsLean hs})\n"
  let names (pre : String) (n : Nat) := "[" ++ ", ".intercalate ((List.range n).map (s!"{pre}{·}")) ++ "]"
  out := out ++ "\ndef mac8Cert : Cert where\n  models := [" ++ ", ".intercalate (tileModels.map (·.2.1)) ++ "]\n" ++
    "  tiles := [" ++ ", ".intercalate (C.tiles.map fun ((x, y), i) => s!"(({x}, {y}), {i})") ++ "]\n" ++
    s!"  gates := {names "mac8CertG" C.gates.length}\n  flops := {names "mac8CertF" C.flops.length}\n" ++
    s!"  outs := {names "mac8CertO" C.outs.length}\n" ++
    "  pads := [" ++ ", ".intercalate (C.pads.map fun (k, n) => s!"({k}, {nodeLean n})") ++ "]\n\nend Obend.Hardware.Fabulous\n"
  return out

end Obend.Hardware.Fabulous
