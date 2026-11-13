module
/-
# Obend.Hardware.Fabulous.CertGen — the readback certificate from an extraction

`buildCert` turns the paths `extractS` followed into a `Cert` (`Obend.Hardware.Fabulous.Readback`): each
pip into a switch-matrix output of a modelled tile becomes `Hop.sm k i`, with `i` the select the tile
model computes from the decoded bits (and refused unless that input is the pip's source), every other pip
a `Hop.wire`. `certLean` writes it as Lean (`obend fabric cert --out ...`, generated on demand).
-/
public import Obend.Hardware.Fabulous.Bitstream
public import Obend.Hardware.Fabulous.Readback
public import Obend.Hardware.Fabulous.LUT4ABSwitchMatrix
public import Obend.Hardware.Fabulous.WIOSwitchMatrix
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware Obend.Hardware.HDL Std

deriving instance Hashable for Node

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

/-- The certificate of an extraction: every pip the extraction followed becomes the entry of the wire
it drives, sorted by tile and then by `nameKey` of the wire's name (so `Cert.chunkOKE` reads distinct names
from strictly increasing keys), with the entry of the wire it reads and its distance to a terminal. -/
def buildCert (fab : Fabric) (cfg : HashMap String Nat) (types : HashMap (Nat × Nat) String) (pm : List Pin)
    (s : ExState) : Except String Cert := do
  let modelIdx (x y : Nat) : Option Nat := (types.get? (x, y)) >>= fun t => tileModels.findIdx? (·.1 == t)
  let model (x y : Nat) : Option TileModel := (modelIdx x y) >>= fun i => (tileModels[i]?.map (·.2.2))
  let mut used : HashSet (Nat × Nat) := {}
  -- node ↦ (hop, the node it reads, or none for a constant)
  let mut drv : HashMap Node (Hop × Option Node) := {}
  for (_, (steps, _)) in s.paths.toList do
    for (d, src) in steps do
      let dn ← nodeOf d
      let sn ← nodeOf src
      let pips := fab.into.getD d #[]
      let fixed := pips.size == 1 && (pips.toList.all fun (st, _, f) => (fab.spec.getD (st ++ "." ++ f) []).isEmpty)
      let (hop, nxt) ← match model dn.x dn.y with
        | some tm =>
          match tm.sm.prims.findIdx? (·.1 == dn.w) with
          | some k =>
            if dn.x != sn.x || dn.y != sn.y then throw s!"{d}: a switch-matrix output driven from another tile"
            let p := (tm.sm.prims[k]?.map (·.2)).getD default
            let i := p.sel (tm.smCfg (cfg.getD (tileName dn.x dn.y) 0).testBit)
            match p.ins[i]? with
            | some src' =>
              if src'.name != sn.w then throw s!"{d}: the tile model selects {src'.name}, the decoder {sn.w}"
              used := used.insert (dn.x, dn.y)
              pure (Hop.sm k i, match src' with | .port _ => some sn | .const _ => none)
            | none => throw s!"{d}: the tile model's select {i} is past its inputs"
          | none =>
            if !fixed then throw s!"{d}: a configurable pip outside the switch-matrix model"
            pure (Hop.wire sn, some sn)
        | none =>
          if !fixed then throw s!"{d}: a configurable pip in a tile with no model"
          pure (Hop.wire sn, some sn)
      if let some (h', n') := drv.get? dn then
        if h' != hop || n' != nxt then throw s!"{d}: two different drivers"
      drv := drv.insert dn (hop, nxt)
  let nodes := drv.toList.map (·.1) |>.mergeSort (fun a b =>
    a.x < b.x || (a.x == b.x && (a.y < b.y || (a.y == b.y && nameKey a.w ≤ nameKey b.w))))
  let idx : HashMap Node Nat := nodes.zipIdx.foldl (fun m (n, i) => m.insert n i) {}
  -- distance to a terminal, along the drivers
  let mut rank : HashMap Node Nat := {}
  for n in nodes do
    let mut chain : Array Node := #[]
    let mut cur := n
    let mut base := 0
    repeat
      if let some r := rank.get? cur then base := r + 1; break
      chain := chain.push cur
      match drv.get? cur with
      | some (_, some m) => if drv.contains m then cur := m else base := 0; break
      | _ => base := 0; break
      if chain.size > nodes.length then throw s!"{tileName n.x n.y}.{n.w}: the drivers loop"
    let mut r := base
    for c in chain.reverse do
      rank := rank.insert c r
      r := r + 1
  let entries ← nodes.mapM fun n => do
    let some (hop, nxt) := drv.get? n | throw "internal"
    let next := nxt >>= idx.get?
    pure ({ node := n, rank := rank.getD n 0, hop, next } : Entry)
  let entryOf (n : String) : Except String Nat := do
    let nd ← nodeOf n
    match idx.get? nd with
    | some j => pure j
    | none => throw s!"{n}: no pip drives it"
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
      ins := ins.push (← if usesInput g.init.toNat i then some <$> entryOf s!"{t}.{pre}I{i}" else pure none)
    gates := gates.push { x, y, pre, isFlop := flopSites.contains g.site, ins := ins.toList : GateCert }
  let mut flops := #[]
  for f in s.flops do
    let some f := f | throw "a flop was left unfilled"
    let (x, y, pre) ← cellOf f.site
    let t := tileName x y
    let some gate := s.gateOf.get? f.site | throw s!"{f.site}: its LUT is not a gate"
    flops := flops.push { x, y, pre, gate, en := ← entryOf s!"{t}.{pre}EN", sr := ← entryOf s!"{t}.{pre}SR" : FlopCert }
  let mut outs := #[]
  let mut pads := #[]
  for h : k in [0:pm.length] do
    let p := pm[k]
    let some (x, y) := parseTile p.tile | throw s!"{p.tile}: not a tile"
    match p.role with
    | .output _ _ => outs := outs.push (k, (⟨x, y, p.bel ++ "_I"⟩ : Node), ← entryOf s!"{p.tile}.{p.bel}_I")
    | _ => pads := pads.push (k, (⟨x, y, p.bel ++ "_O"⟩ : Node))
  let tiles := used.toList.mergeSort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)) |>.filterMap fun (x, y) =>
    (modelIdx x y).map fun i => ((x, y), i)
  let chunks := entries.foldl (fun (acc : Array ((Nat × Nat) × Array Entry)) e =>
    match acc.back? with
    | some ((x, y), es) =>
      if x == e.node.x && y == e.node.y then acc.pop.push ((x, y), es.push e) else acc.push ((e.node.x, e.node.y), #[e])
    | none => acc.push ((e.node.x, e.node.y), #[e])) #[]
  return { models := tileModels.map (·.2.2), tiles, chunks := chunks.toList.map fun (k, es) => (k, es.toList),
           gates := gates.toList, flops := flops.toList, outs := outs.toList, pads := pads.toList }

def nodeLean (n : Node) : String := s!"⟨{n.x}, {n.y}, \"{n.w}\"⟩"

def hopLean : Hop → String
  | .sm k i => s!".sm {k} {i}"
  | .wire n => s!".wire {nodeLean n}"


def optLean : Option Nat → String
  | some j => s!"some {j}"
  | none => "none"

/-- The text of `Mac8Cert.lean`: one definition per chunk, then the gates, flops and outputs. -/
def certLean (C : Cert) (source : String) : String := Id.run do
  let mut out := "module\n/-\n# Obend.Hardware.Fabulous.Mac8Cert — the readback certificate of `hardware/fabulous/obend_ice40_mac8.bin`\n\n" ++
    s!"Generated by `obend fabric cert` from {source}; do not edit. Every wire the extraction followed for\n" ++
    "`mac8Net`, once, with the hop that drives it, chunked by tile; gates, flops and output pins index the table.\n-/\n" ++
    "public import Obend.Hardware.Fabulous.Readback\npublic import Obend.Hardware.Fabulous.LUT4ABSwitchMatrix\n" ++
    "public import Obend.Hardware.Fabulous.WIOSwitchMatrix\n@[expose] public section\n\nnamespace Obend.Hardware.Fabulous\n\n"
  for ((k, es), c) in C.chunks.zipIdx do
    out := out ++ s!"def mac8C{c} : (Nat × Nat) × List Entry := (({k.1}, {k.2}), [\n" ++ ",\n".intercalate (es.map fun e =>
      s!"  ⟨{nodeLean e.node}, {e.rank}, {hopLean e.hop}, {optLean e.next}⟩") ++ "])\n\n"
  let gl (g : GateCert) := s!"⟨{g.x}, {g.y}, \"{g.pre}\", {g.isFlop}, [{", ".intercalate (g.ins.map optLean)}]⟩"
  let fl (f : FlopCert) := s!"⟨{f.x}, {f.y}, \"{f.pre}\", {f.gate}, {f.en}, {f.sr}⟩"
  out := out ++ "def mac8Chunks : List ((Nat × Nat) × List Entry) := [" ++
    ", ".intercalate ((List.range C.chunks.length).map (s!"mac8C{·}")) ++ "]\n\n"
  out := out ++ "def mac8CertGates : List GateCert := [\n" ++ ",\n".intercalate (C.gates.map (s!"  {gl ·}")) ++ "]\n\n"
  out := out ++ "def mac8CertFlops : List FlopCert := [\n" ++ ",\n".intercalate (C.flops.map (s!"  {fl ·}")) ++ "]\n\n"
  out := out ++ "def mac8Cert : Cert where\n  models := [" ++ ", ".intercalate (tileModels.map (·.2.1)) ++ "]\n" ++
    "  tiles := [" ++ ", ".intercalate (C.tiles.map fun ((x, y), i) => s!"(({x}, {y}), {i})") ++ "]\n" ++
    "  chunks := mac8Chunks\n  gates := mac8CertGates\n  flops := mac8CertFlops\n" ++
    "  outs := [" ++ ", ".intercalate (C.outs.map fun (p, n, j) => s!"({p}, {nodeLean n}, {j})") ++ "]\n" ++
    "  pads := [" ++ ", ".intercalate (C.pads.map fun (k, n) => s!"({k}, {nodeLean n})") ++ "]\n\nend Obend.Hardware.Fabulous\n"
  return out

/-- Blocks of `w` covering `0..n-1`. -/
def blocksOf (n w : Nat) : List (Nat × Nat) :=
  (List.range ((n + w - 1) / w)).map fun c => (w * c, min w (n - w * c))

/-- `Cert.follow` over an array of the entries. -/
def followArr (C : Cert) (es : Array Entry) : Nat → Nat → Option End
  | 0, _ => none
  | f + 1, j =>
    match es[j]? with
    | none => none
    | some e =>
      match C.target e, e.next with
      | some (.const c), _ => some (.const c)
      | some (.node _), some j' => followArr C es f j'
      | some (.node m), none => some (.node m)
      | none, _ => none

/-- Each entry's path end, numbered as `Cert.endCode` reads it and chunked like the table: the witness
`Cert.checkF` validates one hop at a time. -/
def endCodes (C : Cert) : List (List Nat) := Id.run do
  let es := C.entries.toArray
  let terms := C.terms
  let code (r : Option End) : Nat := match r with
    | some (.const b) => if b then 1 else 0
    | some (.node m) => ((terms.idxOf? m).map (· + 2)).getD 0
    | none => 0
  let mut out := #[]
  let mut j := 0
  for (_, ch) in C.chunks do
    let mut cs := #[]
    for _ in ch do
      cs := cs.push (code (followArr C es es.size j))
      j := j + 1
    out := out.push cs.toList
  return out.toList

/-- The text of `Mac8CertCheck.lean`: the path-end codes `mac8Ends`, `mac8Cert_check` through `Cert.checkF_sound`,
and the bitstream's required bits through `Cert.required_ofF`, each assembled from blocks (`all_of_blocks`) small
enough that every `decide +kernel` stays well under a second's worth of work per item. -/
def checkLean (C : Cert) (nG nF nO : Nat) : String := Id.run do
  let nC := C.chunks.length
  let names (f : Nat → String) (n : Nat) := ", ".intercalate ((List.range n).map f)
  let blLean (w n : Nat) := "[" ++ ", ".intercalate ((blocksOf n w).map fun (a, l) => s!"({a}, {l})") ++ "]"
  let bitP := "(fun r => binBits mac8BinRows mac8Bin r.1 r.2.1 r.2.2.1 == r.2.2.2)"
  let mut out := "module\n/-\n# Obend.Hardware.Fabulous.Mac8CertCheck — `mac8Cert` checked, and the committed bitstream's bits\n\n" ++
    "Generated by `obend fabric cert`; do not edit. `mac8Ends` is each entry's path end (`Cert.endCode`), chunked like\n" ++
    "the table: the witness `Cert.checkF` validates one hop at a time. Every `decide +kernel` here is one block of chunks,\n" ++
    "gates, flops or outputs of `Cert.checkF` or of the required bits; `all_of_blocks`, `Cert.checkF_of`,\n" ++
    "`Cert.checkF_sound` and `Cert.required_ofF` assemble them.\n-/\n" ++
    "public import Obend.Hardware.Fabulous.Mac8Cert\npublic import Obend.Hardware.Fabulous.Mac8Bin\n" ++
    "public import Obend.Hardware.Fabulous.Mac8Net\n@[expose] public section\n\nnamespace Obend.Hardware.Fabulous\n\n" ++
    "set_option maxRecDepth 100000\n\n"
  out := out ++ "def mac8Ends : List (List Nat) := [\n" ++
    ",\n".intercalate ((endCodes C).map fun cs => "  [" ++ ", ".intercalate (cs.map toString) ++ "]") ++ "]\n\n"
  let blocks (tag pred n : String) (w k : Nat) : String := Id.run do
    let mut o := ""
    for ((a, l), i) in (blocksOf k w).zipIdx do
      o := o ++ s!"theorem mac8{tag}{i} : (List.range' {a} {l}).all ({pred}) = true := by decide +kernel\n"
    o := o ++ s!"theorem mac8{tag}_all : (List.range {n}).all ({pred}) = true :=\n  all_of_blocks (blocks := {blLean w k}) (by decide +kernel)\n" ++
      s!"    (by simp only [List.forall_mem_cons]; exact ⟨{names (s!"mac8{tag}{·}") (blocksOf k w).length}, fun _ h => by cases h⟩)\n\n"
    return o
  let nCs := "mac8Cert.chunks.length"
  out := out ++ blocks "CK" "mac8Cert.chunkAtE mac8Ends" nCs 28 nC ++
    blocks "G" "mac8Cert.gateAtE mac8Net mac8Ends" s!"{nG}" 118 nG ++
    blocks "F" "mac8Cert.flopAtE mac8Net mac8Ends" s!"{nF}" 48 nF ++
    blocks "O" "mac8Cert.outAtE mac8Net mac8Ends" s!"{nO}" 48 nO
  let cReq := s!"mac8Cert.chunkAt (chunkReqsOK mac8Cert {bitP})"
  let gReq := s!"fun k => (match mac8Net.gates[k]?, mac8Cert.gates[k]? with | some g, some gc => mac8Cert.cellReqsF gc.x gc.y gc.pre g.init gc.isFlop | _, _ => []).all {bitP}"
  let fReq := s!"fun k => (match mac8Net.flops[k]?, mac8Cert.flops[k]? with | some f, some fc => mac8Cert.rvReqF fc.x fc.y fc.pre f.rv | _, _ => []).all {bitP}"
  out := out ++ blocks "CB" cReq nCs 28 nC ++ blocks "GB" gReq s!"{nG}" 118 nG ++ blocks "FB" fReq s!"{nF}" 48 nF
  out := out ++ "theorem mac8_models_wf : mac8Cert.models.all (·.sm.wf) = true := by decide +kernel\n" ++
    "theorem mac8_lengths : mac8Net.gates.length == mac8Cert.gates.length && mac8Net.flops.length == mac8Cert.flops.length &&\n" ++
    "    mac8Net.outs.length == mac8Cert.outs.length && mac8Cert.chunks.length == mac8Ends.length := by decide +kernel\n" ++
    "theorem mac8_chunks_sorted : chunksSorted mac8Cert.chunks = true := by decide +kernel\n" ++
    "theorem mac8_terms_distinct : distinctNodes mac8Cert.terms = true := by decide +kernel\n\n" ++
    "theorem mac8Cert_checkF : mac8Cert.checkF mac8Net mac8Ends = true :=\n" ++
    "  Cert.checkF_of mac8Cert mac8Net mac8Ends mac8_models_wf mac8_lengths mac8_chunks_sorted mac8CK_all mac8_terms_distinct\n" ++
    "    mac8G_all mac8F_all mac8O_all\n\n" ++
    "theorem mac8Cert_check : mac8Cert.check mac8Net = true := Cert.checkF_sound mac8Cert_checkF\n\n"
  out := out ++ "/-- The committed bitstream is laid out as `binBits` reads it. -/\n" ++
    "theorem mac8Bin_framed : binFramed mac8BinCols mac8BinRows mac8Bin mac8BinSize = true := by decide +kernel\n\n" ++
    "/-- **The committed bitstream has every bit `mac8Cert` requires.** -/\n" ++
    "theorem mac8_bin_required : ∀ r ∈ mac8Cert.required mac8Net, binBits mac8BinRows mac8Bin r.1 r.2.1 r.2.2.1 = r.2.2.2 :=\n" ++
    "  Cert.required_ofF mac8Cert mac8Net _ mac8CB_all mac8GB_all mac8FB_all\n\nend Obend.Hardware.Fabulous\n"
  return out

end Obend.Hardware.Fabulous
