module
/-
# Obend.Hardware.NotebookProjection — hardware and physical notebook projections

Projects circuits, timing, placement, complete routed nets and bitstream frames, CNC toolpaths,
OpenUSD lifecycle tracks, and multiphysics certificates into structured notebook cells.
The established `Obend.Vault.HardwareProjection` and `Obend.Vault.PhysicalProjection` namespaces
remain the public API. Routing/frame payloads have injective Data projections and independently
length-framed byte encodings with a full-width digest binding theorem.
-/

public import Obend.Core.Data
public import Obend.Doc.Structured
public import Obend.Doc.Graph
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.Process
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.DRC
public import Obend.Hardware.Circuits
public import Obend.Hardware.Retiming
public import Obend.Hardware.Analog
public import Obend.Leaf.Emit
public import Obend.Hardware.Kinematics
public import Obend.Hardware.Magnetics
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.VerilateRunner
public import Obend.Analysis.Hybrid
public import Obend.Receipt.Merkle
public section

namespace Obend.Vault.HardwareProjection

open Obend.Core.Data
open Obend.Doc
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Process
open Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC
open Obend.Hardware.Circuits
open Obend.Hardware.Retiming
open Obend.Hardware.Analog
open Obend.Hardware.Magnetics

set_option autoImplicit false

/-! ## 1. Public Type Aliases -/

/-- Primary circuit representation: synchronous RTL module with combinational DAG & CDC discipline. -/
abbrev Circuit := Obend.Hardware.HDL.RtlModule

/-- Primary netlist representation: synthesized FPGA/ASIC primitive `BelNetlist`. -/
abbrev Netlist := Obend.Hardware.Synth.BelNetlist

/-- Composite static timing analysis report specification. -/
structure TimingReport where
  corner        : ProcessCorner
  path          : TimingPath
  clockPeriodPs : Nat
  deriving DecidableEq, Repr

/-- Primary physical layout representation: untrusted PnR placement, routing, and bitstream certificate. -/
abbrev GdsLayout := Obend.Hardware.PlaceRoute.PnrCertificate

/-! ## 2. Data AST Encoding Helpers -/

/-- Encode a signed integer into a canonical `Data.variant`. -/
def dInt (i : Int) : Data :=
  if i ≥ 0 then
    .variant "pos" (.natural i.toNat)
  else
    .variant "neg" (.natural (-i).toNat)

/-- Render ALU operation as string label. -/
def aluOpToString : RtlAluOp → String
  | .add    => "add"
  | .sub    => "sub"
  | .mul    => "mul"
  | .bitAnd => "bitAnd"
  | .bitOr  => "bitOr"
  | .bitXor => "bitXor"
  | .shl    => "shl"
  | .lshr   => "lshr"
  | .ashr   => "ashr"
  | .eq     => "eq"
  | .ult    => "ult"
  | .slt    => "slt"
  | .qmul32 => "qmul32"

/-- Render clock domain as string label. -/
def clkDomainToString : ClkDomain → String
  | .coreClk    => "coreClk"
  | .axiIoClk   => "axiIoClk"
  | .cfgJtagClk => "cfgJtagClk"

/-- Render reset kind as string label. -/
def resetKindToString : ResetKind → String
  | .resetFree   => "resetFree"
  | .syncReset v => s!"syncReset({v.toNat})"

/-- Recursively project an `RtlExpr` AST into `Core.Data`. -/
def rtlExprToData : RtlExpr → Data
  | .const v => .variant "const" (.natural v.toNat)
  | .inputPort idx => .variant "inputPort" (.natural idx)
  | .wireRef idx => .variant "wireRef" (.natural idx)
  | .regRead idx => .variant "regRead" (.natural idx)
  | .alu op lhs rhs =>
    .variant "alu" (.record [
      ("op", .label (aluOpToString op)),
      ("lhs", rtlExprToData lhs),
      ("rhs", rtlExprToData rhs)
    ])
  | .mux c t f =>
    .variant "mux" (.record [
      ("cond", rtlExprToData c),
      ("ifTrue", rtlExprToData t),
      ("ifFalse", rtlExprToData f)
    ])
  | .bitNot a =>
    .variant "bitNot" (rtlExprToData a)
  | .resize op a =>
    let opData : Data := match op with
      | .slice hi lo => .variant "slice" (.record [("hi", .natural hi), ("lo", .natural lo)])
      | .zext w      => .variant "zext" (.natural w)
      | .sext f t    => .variant "sext" (.record [("from", .natural f), ("to", .natural t)])
      | .trunc w     => .variant "trunc" (.natural w)
    .variant "resize" (.record [("op", opData), ("arg", rtlExprToData a)])

/-- Project a wire assignment into `Core.Data`. -/
def wireAssignToData (w : WireAssign) : Data :=
  .record [
    ("index", .natural w.wireIdx),
    ("name", .label w.name),
    ("expr", rtlExprToData w.expr)
  ]

/-- Project a register specification into `Core.Data`. -/
def regSpecToData (r : RegSpec) : Data :=
  .record [
    ("index", .natural r.regIdx),
    ("name", .label r.name),
    ("domain", .label (clkDomainToString r.domain)),
    ("reset_kind", .label (resetKindToString r.resetKind)),
    ("is_synchronizer", .boolean r.isSynchronizer),
    ("next_expr", rtlExprToData r.nextExpr)
  ]

/-- Project an output port into `Core.Data`. -/
def outputPortToData (o : OutputPort) : Data :=
  .record [
    ("name", .label o.name),
    ("expr", rtlExprToData o.expr)
  ]

/-! ## 3. Core Hardware Data Projections -/

/-- Project an `RtlModule` circuit into canonical `Core.Data`. -/
def circuitToData (m : RtlModule) : Data :=
  .record [
    ("kind", .label "circuit"),
    ("type", .label "rtl_module"),
    ("name", .label m.name),
    ("input_count", .natural m.inputNames.length),
    ("inputs", .record (m.inputNames.zipIdx.map fun (name, i) => (toString i, .label name))),
    ("wire_count", .natural m.wires.length),
    ("wires", .record (m.wires.map fun w => (toString w.wireIdx, wireAssignToData w))),
    ("reg_count", .natural m.regs.length),
    ("regs", .record (m.regs.map fun r => (toString r.regIdx, regSpecToData r))),
    ("output_count", .natural m.outputs.length),
    ("outputs", .record (m.outputs.zipIdx.map fun (o, i) => (toString i, outputPortToData o))),
    ("dag_valid", .boolean (checkRtlModule m))
  ]

/-- Project a synchronous retiming graph into `Core.Data`. -/
def syncGraphToData (g : SyncGraph) : Data :=
  .record [
    ("kind", .label "circuit"),
    ("type", .label "sync_graph"),
    ("name", .label g.name),
    ("inputs", .record (g.primaryInputs.zipIdx.map fun (v, i) => (toString i, .natural v))),
    ("outputs", .record (g.primaryOutputs.zipIdx.map fun (v, i) => (toString i, .natural v))),
    ("edges", .record (g.edges.zipIdx.map fun (e, i) => (toString i, .record [
      ("src", .natural e.src),
      ("dst", .natural e.dst),
      ("orig_regs", .natural e.origRegs),
      ("comb_delay_ps", .natural e.combDelayPs)
    ])))
  ]

/-- Project a synthesized `BelNetlist` into canonical `Core.Data`. -/
def belNetlistToData (net : BelNetlist) : Data :=
  .record [
    ("kind", .label "netlist"),
    ("type", .label "bel_netlist"),
    ("module_name", .label net.moduleName),
    ("input_count", .natural net.inputNames.length),
    ("cell_count", .natural net.cells.length),
    ("ff_count", .natural (countFfBels net)),
    ("output_count", .natural net.outputNames.length),
    ("valid", .boolean (checkBelNetlistValid net)),
    ("cells", .record (net.cells.zipIdx.map fun (c, i) =>
      (toString i, .record [("dst", .label c.dstName), ("fanin", .natural c.inputs.length)])))
  ]

/-- Ordered, structurally delimited data sequences with unique record field names. -/
def dataSeq {α : Type} (f : α → Data) : List α → Data
  | [] => .variant "nil" (.record [])
  | x :: xs => .variant "cons" (.record [("head", f x), ("tail", dataSeq f xs)])

theorem dataSeq_injective {α : Type} {f : α → Data}
    (hf : ∀ {a b}, f a = f b → a = b) :
    ∀ {xs ys}, dataSeq f xs = dataSeq f ys → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [dataSeq]
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp [dataSeq] at h
    | cons y ys =>
      have he : f x = f y ∧ dataSeq f xs = dataSeq f ys := by
        simpa [dataSeq] using h
      have hx := hf he.1
      have ht := ih he.2
      simp_all

def pipHopToData (h : PipHop) : Data :=
  .record [("src_wire", .natural h.srcWire), ("dst_wire", .natural h.dstWire),
    ("res_ohm", .natural h.resOhm), ("cap_ff", .natural h.capFf)]

theorem pipHopToData_injective {a b : PipHop} (h : pipHopToData a = pipHopToData b) : a = b := by
  cases a; cases b; simp_all [pipHopToData]

def bitstreamFrameToData (f : BitstreamFrame) : Data :=
  .record [("frame_addr", .natural f.frameAddr), ("frame_data", .natural f.frameData)]

theorem bitstreamFrameToData_injective {a b : BitstreamFrame}
    (h : bitstreamFrameToData a = bitstreamFrameToData b) : a = b := by
  cases a; cases b; simp_all [bitstreamFrameToData]

/-- Project a single routed net into `Core.Data`. -/
def routedNetToData (net : RoutedNet) : Data :=
  .record [
    ("net_id", .natural net.netId),
    ("src_wire", .natural net.srcWire),
    ("dst_wire", .natural net.dstWire),
    ("hops", dataSeq pipHopToData net.hops),
    ("is_contiguous", .boolean (checkNetConnectivity net))
  ]

theorem routedNetToData_injective {a b : RoutedNet}
    (h : routedNetToData a = routedNetToData b) : a = b := by
  have he : a.netId = b.netId ∧ a.srcWire = b.srcWire ∧ a.dstWire = b.dstWire ∧
      dataSeq pipHopToData a.hops = dataSeq pipHopToData b.hops ∧
      checkNetConnectivity a = checkNetConnectivity b := by
    simpa [routedNetToData] using h
  have hh := dataSeq_injective pipHopToData_injective he.2.2.2.1
  cases a; cases b; simp_all

/-- Project routed interconnect netlist into `Core.Data`. -/
def routedNetlistToData (nets : List RoutedNet) : Data :=
  .record [
    ("kind", .label "routed_netlist"),
    ("net_count", .natural nets.length),
    ("nets", .record (nets.zipIdx.map fun (n, i) => (toString i, routedNetToData n))),
    ("is_disjoint", .boolean (checkRoutingDisjoint nets))
  ]

/-- Project static timing analysis results into canonical `Core.Data`. -/
def timingToData (corner : ProcessCorner) (path : TimingPath) (clockPeriodPs : Nat) : Data :=
  let maxArr := maxArrivalPs corner path
  let minArr := minArrivalPs corner path
  let reqPer := requiredPeriodPs corner path
  let closed := checkTimingSignoff corner clockPeriodPs path
  let setupSlack :=
    if reqPer ≤ clockPeriodPs then
      (clockPeriodPs - reqPer : Int)
    else
      -((reqPer - clockPeriodPs : Nat) : Int)
  let holdSlack :=
    if corner.tHoldPs + corner.tSkewPs ≤ minArr then
      ((minArr - (corner.tHoldPs + corner.tSkewPs) : Nat) : Int)
    else
      -(((corner.tHoldPs + corner.tSkewPs) - minArr : Nat) : Int)
  .record [
    ("kind", .label "timing_report"),
    ("path_name", .label path.name),
    ("corner_name", .label corner.name),
    ("node_nm", .natural corner.nodeNm),
    ("voltage_mv", .natural corner.voltageMv),
    ("temp_c", dInt corner.tempC),
    ("clock_period_ps", .natural clockPeriodPs),
    ("max_arrival_ps", .natural maxArr),
    ("min_arrival_ps", .natural minArr),
    ("required_period_ps", .natural reqPer),
    ("setup_slack_ps", dInt setupSlack),
    ("hold_slack_ps", dInt holdSlack),
    ("logic_levels", .natural path.logicLevels),
    ("carry_bits", .natural path.carryBits),
    ("tile_hops", .natural path.tileHops),
    ("timing_closed", .boolean closed),
    ("status", .label (if closed then "TIMING_CLOSED" else "TIMING_VIOLATION"))
  ]

open Obend.Receipt.Merkle (encodeFields encodeFields_injective leb128 leb128_injective)

/-- Unbounded LEB128 length framing; no fixed-width truncation of lengths or natural fields. -/
def frameBytes (fields : List (List UInt8)) : List UInt8 := encodeFields fields

theorem frameBytes_injective {a b : List (List UInt8)} (h : frameBytes a = frameBytes b) : a = b :=
  encodeFields_injective a b h

def pipHopBytes (h : PipHop) : List UInt8 :=
  frameBytes [leb128 h.srcWire, leb128 h.dstWire, leb128 h.resOhm, leb128 h.capFf]

def bitstreamFrameBytes (f : BitstreamFrame) : List UInt8 :=
  frameBytes [leb128 f.frameAddr, leb128 f.frameData]

theorem pipHopBytes_injective {a b : PipHop} (h : pipHopBytes a = pipHopBytes b) : a = b := by
  have he := frameBytes_injective h
  simp only [List.cons.injEq, and_true] at he
  have h1 := leb128_injective he.1
  have h2 := leb128_injective he.2.1
  have h3 := leb128_injective he.2.2.1
  have h4 := leb128_injective he.2.2.2
  cases a; cases b; simp_all

theorem bitstreamFrameBytes_injective {a b : BitstreamFrame}
    (h : bitstreamFrameBytes a = bitstreamFrameBytes b) : a = b := by
  have he := frameBytes_injective h
  simp only [List.cons.injEq, and_true] at he
  have h1 := leb128_injective he.1
  have h2 := leb128_injective he.2
  cases a; cases b; simp_all

theorem map_injective_of {α β : Type} {f : α → β}
    (hf : ∀ {a b}, f a = f b → a = b) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hx := hf h.1
      have ht := ih h.2
      simp_all

def routedNetBytes (n : RoutedNet) : List UInt8 :=
  frameBytes [leb128 n.netId, leb128 n.srcWire, leb128 n.dstWire,
    frameBytes (n.hops.map pipHopBytes)]

theorem routedNetBytes_injective {a b : RoutedNet}
    (h : routedNetBytes a = routedNetBytes b) : a = b := by
  have he := frameBytes_injective h
  simp only [List.cons.injEq, and_true] at he
  have h1 := leb128_injective he.1
  have h2 := leb128_injective he.2.1
  have h3 := leb128_injective he.2.2.1
  have h4 := map_injective_of pipHopBytes_injective (frameBytes_injective he.2.2.2)
  cases a; cases b; simp_all

/-- Domain-separated commitment preimage for the full routing/frame payload of a notebook layout. -/
def pnrRouteFrameBytes (c : PnrCertificate) : List UInt8 :=
  frameBytes ["obend/notebook/routing-frames/v1".toUTF8.toList,
    frameBytes (c.routedNets.map routedNetBytes), frameBytes (c.bitstreamFrames.map bitstreamFrameBytes)]

theorem pnrRouteFrameBytes_binding {a b : PnrCertificate}
    (h : pnrRouteFrameBytes a = pnrRouteFrameBytes b) :
    a.routedNets = b.routedNets ∧ a.bitstreamFrames = b.bitstreamFrames := by
  have he := frameBytes_injective h
  simp only [List.cons.injEq, and_true, true_and] at he
  exact ⟨map_injective_of routedNetBytes_injective (frameBytes_injective he.1),
    map_injective_of bitstreamFrameBytes_injective (frameBytes_injective he.2)⟩

/-- Full-width hashes bind routing/frame data, or expose a collision at exactly those two preimages. -/
theorem pnrRouteFrameDigest_binding (H : List UInt8 → BitVec 256) {a b : PnrCertificate}
    (h : H (pnrRouteFrameBytes a) = H (pnrRouteFrameBytes b)) :
    (a.routedNets = b.routedNets ∧ a.bitstreamFrames = b.bitstreamFrames) ∨
    (pnrRouteFrameBytes a ≠ pnrRouteFrameBytes b ∧ H (pnrRouteFrameBytes a) = H (pnrRouteFrameBytes b)) := by
  by_cases he : pnrRouteFrameBytes a = pnrRouteFrameBytes b
  · exact .inl (pnrRouteFrameBytes_binding he)
  · exact .inr ⟨he, h⟩

/-- Project physical PnR placement, routing, and bitstream into canonical `Core.Data`. -/
def pnrLayoutToData (cert : PnrCertificate) : Data :=
  .record [
    ("kind", .label "gds_layout"),
    ("type", .label "pnr_layout"),
    ("design_name", .label cert.designName),
    ("cell_count", .natural cert.placedCells.length),
    ("net_count", .natural cert.routedNets.length),
    ("frame_count", .natural cert.bitstreamFrames.length),
    ("routed_nets", dataSeq routedNetToData cert.routedNets),
    ("bitstream_frames", dataSeq bitstreamFrameToData cert.bitstreamFrames),
    ("sink_cap_ff", .natural cert.sinkCapFf),
    ("placement_injective", .boolean (checkPlacementInjective cert.placedCells)),
    ("routing_disjoint", .boolean (checkRoutingDisjoint cert.routedNets)),
    ("cells", .record (cert.placedCells.zipIdx.map fun (c, i) =>
      (toString i, .record [
        ("cell_id", .natural c.cellId),
        ("tile_x", .natural c.tileX),
        ("tile_y", .natural c.tileY),
        ("bel_slot", .natural c.belSlot),
        ("lut_init", .natural c.lutInit)
      ]))),
    ("tile_configs", .record (cert.expectedConfigs.zipIdx.map fun (cfg, i) =>
      (toString i, .record [
        ("tile_x", .natural cfg.tileX),
        ("tile_y", .natural cfg.tileY),
        ("bel_slot", .natural cfg.belSlot),
        ("lut_init", .natural cfg.lutInit),
        ("pip_mask", .natural cfg.pipMask)
      ]))),
    ("route_frame_commitment", dataSeq (fun b => .natural b.toNat) (pnrRouteFrameBytes cert))
  ]

/-- Equality of notebook layouts recovers every routed hop and every frame word. -/
theorem pnrLayoutToData_binds_routedNets_and_bitstreamFrames {a b : PnrCertificate}
    (h : pnrLayoutToData a = pnrLayoutToData b) :
    a.routedNets = b.routedNets ∧ a.bitstreamFrames = b.bitstreamFrames := by
  have he := Data.record.inj h
  have hn : dataSeq routedNetToData a.routedNets = dataSeq routedNetToData b.routedNets := by
    exact (Prod.mk.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj he).2).2).2).2).2).2).1).2
  have hf : dataSeq bitstreamFrameToData a.bitstreamFrames = dataSeq bitstreamFrameToData b.bitstreamFrames := by
    exact (Prod.mk.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj he).2).2).2).2).2).2).2).1).2
  exact ⟨dataSeq_injective routedNetToData_injective hn,
    dataSeq_injective bitstreamFrameToData_injective hf⟩

/-- A nonempty routed layout supplies a constructive binding witness. -/
def projectionWitness : PnrCertificate :=
  ⟨"binding", [], [⟨7, 1, 2, [⟨1, 2, 3, 4⟩]⟩], [], [⟨5, 6⟩], 9⟩

theorem pnr_projection_inhabited : ∃ c : PnrCertificate,
    c.routedNets ≠ [] ∧ c.bitstreamFrames ≠ [] ∧
    ∀ d, pnrLayoutToData c = pnrLayoutToData d →
      c.routedNets = d.routedNets ∧ c.bitstreamFrames = d.bitstreamFrames :=
  ⟨projectionWitness, by decide, by decide,
    fun _ h => pnrLayoutToData_binds_routedNets_and_bitstreamFrames h⟩

/-- Project cutline DRC features and deck verification into canonical `Core.Data`. -/
def cutlineDrcToData (deck : FoundryDrcDeck) (feat : CutlineDrcFeature) : Data :=
  let drcClean := checkCutlineDRC deck feat
  .record [
    ("kind", .label "drc_report"),
    ("deck_name", .label deck.deckName),
    ("metal_width_nm", .natural feat.metalWidthNm),
    ("min_metal_width_nm", .natural deck.minMetalWidthNm),
    ("width_ok", .boolean (deck.minMetalWidthNm ≤ feat.metalWidthNm)),
    ("metal_spacing_nm", .natural feat.metalSpacingNm),
    ("min_metal_spacing_nm", .natural deck.minMetalSpacingNm),
    ("spacing_ok", .boolean (deck.minMetalSpacingNm ≤ feat.metalSpacingNm)),
    ("via_width_nm", .natural feat.viaWidthNm),
    ("min_via_width_nm", .natural deck.minViaWidthNm),
    ("via_width_ok", .boolean (deck.minViaWidthNm ≤ feat.viaWidthNm)),
    ("via_enclosure_nm", .natural feat.viaEnclosureNm),
    ("min_via_enclosure_nm", .natural deck.minViaEnclosureNm),
    ("enclosure_ok", .boolean (deck.minViaEnclosureNm ≤ feat.viaEnclosureNm)),
    ("resist_aspect_ok", .boolean (feat.resistOpeningNm > 0 && feat.resistHeightNm ≤ deck.maxResistAspect * feat.resistOpeningNm)),
    ("ild_thickness_nm", .natural feat.ildThicknessNm),
    ("drc_clean", .boolean drcClean),
    ("status", .label (if drcClean then "DRC_CLEAN" else "DRC_VIOLATION"))
  ]

/-! ## 4. Projections into `Doc.Content.cell` -/

/-- Project an `RtlModule` circuit into a `.hardwareSchematic` document cell. -/
def projectCircuit
    (id : String)
    (m : Circuit)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareSchematic (circuitToData m) pins receipt

/-- Project a `BelNetlist` into a `.hardwareSchematic` document cell. -/
def projectNetlist
    (id : String)
    (sig : Netlist)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareSchematic (belNetlistToData sig) pins receipt

/-- Project a static timing analysis result into a `.hardwareTiming` document cell. -/
def projectTiming
    (id : String)
    (corner : ProcessCorner)
    (path : TimingPath)
    (clockPeriodPs : Nat)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareTiming (timingToData corner path clockPeriodPs) pins receipt

/-- Project a composite `TimingReport` record into a `.hardwareTiming` document cell. -/
def projectTimingReport
    (id : String)
    (rep : TimingReport)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  projectTiming id rep.corner rep.path rep.clockPeriodPs pins receipt

/-- Project physical placement and PnR bitstream into a `.hardwareLayout` document cell. -/
def projectGdsii
    (id : String)
    (cert : GdsLayout)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (pnrLayoutToData cert) pins receipt

/-- The actual notebook cell constructor preserves the routing/frame binding contract. -/
theorem projectGdsii_injective_on_nets_and_frames {a b : PnrCertificate} (id : String)
    (h : projectGdsii id a = projectGdsii id b) :
    a.routedNets = b.routedNets ∧ a.bitstreamFrames = b.bitstreamFrames := by
  have he : pnrLayoutToData a = pnrLayoutToData b := by
    simpa [projectGdsii] using h
  exact pnrLayoutToData_binds_routedNets_and_bitstreamFrames he

/-- Project cutline DRC features into a `.hardwareLayout` document cell. -/
def projectDrc
    (id : String)
    (deck : FoundryDrcDeck)
    (feat : CutlineDrcFeature)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (cutlineDrcToData deck feat) pins receipt

/-! ## 5. Metatheorems: Determinism, Semantic Congruence, Safety & Non-Interference -/

/-- Theorem: Circuit projection is strictly deterministic. -/
theorem projectCircuit_deterministic
    (id : String) (m1 m2 : Circuit)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray)
    (hMod : m1 = m2) (hPins : pins1 = pins2) (hRec : rec1 = rec2) :
    projectCircuit id m1 pins1 rec1 = projectCircuit id m2 pins2 rec2 := by
  subst hMod hPins hRec
  rfl

/-- Theorem: Netlist projection is strictly deterministic. -/
theorem projectNetlist_deterministic
    (id : String) (sig1 sig2 : Netlist)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray)
    (hSig : sig1 = sig2) (hPins : pins1 = pins2) (hRec : rec1 = rec2) :
    projectNetlist id sig1 pins1 rec1 = projectNetlist id sig2 pins2 rec2 := by
  subst hSig hPins hRec
  rfl

/-- Theorem: Timing projection is strictly deterministic. -/
theorem projectTiming_deterministic
    (id : String) (c1 c2 : ProcessCorner) (p1 p2 : TimingPath) (clk1 clk2 : Nat)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray)
    (hC : c1 = c2) (hP : p1 = p2) (hClk : clk1 = clk2) (hPins : pins1 = pins2) (hRec : rec1 = rec2) :
    projectTiming id c1 p1 clk1 pins1 rec1 = projectTiming id c2 p2 clk2 pins2 rec2 := by
  subst hC hP hClk hPins hRec
  rfl

/-- Theorem: Layout / GDSII projection is strictly deterministic. -/
theorem projectGdsii_deterministic
    (id : String) (cert1 cert2 : GdsLayout)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray)
    (hCert : cert1 = cert2) (hPins : pins1 = pins2) (hRec : rec1 = rec2) :
    projectGdsii id cert1 pins1 rec1 = projectGdsii id cert2 pins2 rec2 := by
  subst hCert hPins hRec
  rfl

/-- Theorem: Cutline DRC projection is strictly deterministic. -/
theorem projectDrc_deterministic
    (id : String) (deck1 deck2 : FoundryDrcDeck) (feat1 feat2 : CutlineDrcFeature)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray)
    (hDeck : deck1 = deck2) (hFeat : feat1 = feat2) (hPins : pins1 = pins2) (hRec : rec1 = rec2) :
    projectDrc id deck1 feat1 pins1 rec1 = projectDrc id deck2 feat2 pins2 rec2 := by
  subst hDeck hFeat hPins hRec
  rfl

/-- Theorem: FABulous configuration bitstream roundtrip congruence.
Projecting encoded bitstreams recovers the exact original tile configuration. -/
theorem pnr_tile_roundtrip_congr
    (cfg : TileFrameConfig)
    (hWf : wfTileFrameConfig cfg = true) :
    decodeBitstreamFrame (encodeBitstreamFrame cfg) = cfg :=
  bitstream_decode_roundtrip_sound cfg hWf

/-- Theorem: Timing projection signoff soundness.
A timing report passing `checkTimingSignoff` encodes `timing_closed = true`. -/
theorem timing_projection_closed_sound
    (corner : ProcessCorner) (path : TimingPath) (clockPeriodPs : Nat)
    (hClosed : checkTimingSignoff corner clockPeriodPs path = true) :
    (timingToData corner path clockPeriodPs) =
      .record [
        ("kind", .label "timing_report"),
        ("path_name", .label path.name),
        ("corner_name", .label corner.name),
        ("node_nm", .natural corner.nodeNm),
        ("voltage_mv", .natural corner.voltageMv),
        ("temp_c", dInt corner.tempC),
        ("clock_period_ps", .natural clockPeriodPs),
        ("max_arrival_ps", .natural (maxArrivalPs corner path)),
        ("min_arrival_ps", .natural (minArrivalPs corner path)),
        ("required_period_ps", .natural (requiredPeriodPs corner path)),
        ("setup_slack_ps", dInt (if (requiredPeriodPs corner path) ≤ clockPeriodPs then (clockPeriodPs - requiredPeriodPs corner path : Int) else -((requiredPeriodPs corner path - clockPeriodPs : Nat) : Int))),
        ("hold_slack_ps", dInt (if corner.tHoldPs + corner.tSkewPs ≤ minArrivalPs corner path then ((minArrivalPs corner path - (corner.tHoldPs + corner.tSkewPs) : Nat) : Int) else -(((corner.tHoldPs + corner.tSkewPs) - minArrivalPs corner path : Nat) : Int))),
        ("logic_levels", .natural path.logicLevels),
        ("carry_bits", .natural path.carryBits),
        ("tile_hops", .natural path.tileHops),
        ("timing_closed", .boolean true),
        ("status", .label "TIMING_CLOSED")
      ] := by
  simp only [timingToData, hClosed, ite_true]

/-- Theorem: DRC cutline clean implies foundry metal pitch bound. -/
theorem drc_projection_clean_implies_pitch
    (deck : FoundryDrcDeck) (feat : CutlineDrcFeature)
    (hDrc : checkCutlineDRC deck feat = true) :
    deck.minMetalWidthNm + deck.minMetalSpacingNm ≤ feat.metalWidthNm + feat.metalSpacingNm :=
  drc_clean_implies_min_pitch deck feat hDrc

/-- Theorem: Document graph atom non-interference.
Inserting a projected hardware cell into a document graph at `newAtom` preserves all
existing atom labels at `otherAtom ≠ newAtom`. -/
theorem hardware_projection_doc_noninterference
    (G : Graph) (newAtom : AtomId) (cell : Doc.Content)
    (otherAtom : AtomId) (hNe : otherAtom ≠ newAtom) :
    (((newAtom, cell) :: G.atoms).lookup otherAtom) = G.atoms.lookup otherAtom := by
  have : (otherAtom == newAtom) = false := by simpa using hNe
  simp [List.lookup, this]

/-- Theorem: Cryptographic pin and receipt non-interference.
Modifying cell pins or Merkle receipts preserves the projected hardware AST bit-for-bit. -/
theorem hardware_ast_pin_receipt_noninterference
    (id : String) (m : Circuit)
    (pins1 pins2 : List (String × ByteArray))
    (rec1 rec2 : Option ByteArray) :
    match projectCircuit id m pins1 rec1, projectCircuit id m pins2 rec2 with
    | .cell _ _ ast1 _ _, .cell _ _ ast2 _ _ => ast1 = ast2
    | _, _ => False := by
  simp [projectCircuit]

end Obend.Vault.HardwareProjection

namespace Obend.Vault.PhysicalProjection
open Obend.Core.Data
open Obend.Core.Term
open Obend.Doc
open Obend.Vault.HardwareProjection (dInt)
open Obend.Hardware.Kinematics
open Obend.Hardware.Magnetics
open Obend.Hardware.OpenUSD
open Obend.Hardware.VerilateRunner
open Obend.Logic
open Obend.Leaf
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. 5-Axis CNC Kinematic Toolpath & Abbe Compensation Projection -/

/-- Encode a 3D integer-scaled vector `Vec3` into canonical `Core.Data`. -/
def vec3ToData (v : Vec3) : Data :=
  .record [
    ("x", dInt v.x),
    ("y", dInt v.y),
    ("z", dInt v.z)
  ]

/-- Encode a 6D Featherstone spatial motion twist `SpatialTwist6D` into `Core.Data`. -/
def twist6DToData (t : SpatialTwist6D) : Data :=
  .record [
    ("ang", vec3ToData t.ang),
    ("lin", vec3ToData t.lin)
  ]

/-- Encode a 6D Featherstone spatial force wrench `SpatialWrench6D` into `Core.Data`. -/
def wrench6DToData (w : SpatialWrench6D) : Data :=
  .record [
    ("torque", vec3ToData w.torque),
    ("force", vec3ToData w.force)
  ]

/-- Encode a 1D Ruckig 3rd-order jerk-limited trajectory state into `Core.Data`. -/
def ruckigStateToData (st : RuckigState1D) : Data :=
  .record [
    ("pos_scaled_6", dInt st.posScaled6),
    ("vel_scaled_2", dInt st.velScaled2),
    ("acc", dInt st.acc)
  ]

/-- Specification for a 5-axis CNC kinematic toolpath & Abbe error-compensation viewport cell. -/
structure CncToolpathViewportSpec where
  machineName : String
  pTarget     : Vec3
  linErr      : Vec3
  angErr      : Vec3
  abbeArm     : Vec3
  twist       : SpatialTwist6D
  momentum    : SpatialWrench6D
  ruckigInit  : RuckigState1D
  jerkPulse   : Int
  pulseDt     : Int
  deriving DecidableEq, Repr

/-- Project a `CncToolpathViewportSpec` into canonical `Core.Data`. -/
def cncToolpathToData (spec : CncToolpathViewportSpec) : Data :=
  let volErr := evalVolumetricError3D spec.linErr spec.angErr spec.abbeArm
  let compCmd := evalAbbeCompensatedCmd3D spec.pTarget spec.linErr spec.angErr spec.abbeArm
  let actualTip := evalUncompensatedTipPos3D compCmd spec.linErr spec.angErr spec.abbeArm
  let coriolisPower := spatialPower (spatialCrossForce spec.twist spec.momentum) spec.twist
  let rStep1 := stepRuckigSegment spec.ruckigInit spec.jerkPulse spec.pulseDt
  let rStep2 := stepRuckigSegment rStep1 (-spec.jerkPulse) spec.pulseDt
  let millBook := emit goldenCnc5AxisMillComp
  .record [
    ("kind", .label "physical_cnc_5axis"),
    ("machine_name", .label spec.machineName),
    ("target_tip_nm", vec3ToData spec.pTarget),
    ("volumetric_error_nm", vec3ToData volErr),
    ("abbe_compensated_cmd_nm", vec3ToData compCmd),
    ("actual_tip_nm", vec3ToData actualTip),
    ("abbe_exact_cancelled", .boolean (actualTip == spec.pTarget)),
    ("coriolis_power", dInt coriolisPower),
    ("ruckig_final_state", ruckigStateToData rStep2),
    ("userspace_mill_slots", .natural millBook.slots.length),
    ("userspace_mill_closed", .boolean millBook.closedB)
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for a 5-axis CNC kinematic toolpath. -/
def projectCncToolpath
    (id : String)
    (spec : CncToolpathViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (cncToolpathToData spec) pins receipt

/-! ## 2. OpenUSD Scene-Graph (`SdfPath`), `LIVERPS` Relocates, Affine SDF & `timeSamples` Projection -/

/-- Encode an OpenUSD hierarchical `SdfPath` into `Core.Data`. -/
def sdfPathToData (p : SdfPath) : Data :=
  .record (p.zipIdx.map fun (seg, i) => (toString i, .label seg))

/-- Encode an `AffineForm1D` SDF enclosure and its interval bounds into `Core.Data`. -/
def affineSdfToData (af : AffineForm1D) : Data :=
  let iv := af.toInterval
  let selfSub := (AffineForm1D.sub af af).toInterval
  .record [
    ("c0", dInt af.c0),
    ("c1", dInt af.c1),
    ("c2", dInt af.c2),
    ("radius", dInt af.radius),
    ("interval_lo", dInt iv.lo),
    ("interval_hi", dInt iv.hi),
    ("self_cancel_zero", .boolean (selfSub.lo == 0 && selfSub.hi == 0))
  ]

/-- Encode a `UsdPhysicalState` `timeSamples` entry into `Core.Data`. -/
def usdStateToData (st : UsdPhysicalState) : Data :=
  .record [
    ("time_code", .natural st.timeCode),
    ("wall_thickness_um", dInt st.wallThicknessUm),
    ("peak_temp_milli_c", dInt st.peakTempMilliC),
    ("receipt_digest", .natural st.receiptDigest)
  ]

/-- Specification for an OpenUSD scene-graph, `AffineForm1D` SDF, and `timeSamples` lifecycle viewport cell. -/
structure OpenUsdViewportSpec where
  stageName      : String
  primPath       : SdfPath
  relocateSrc    : SdfPath
  relocateDst    : SdfPath
  sdfWallForm    : AffineForm1D
  minWallUm      : Int
  maxTempMilliC  : Int
  initSample     : UsdPhysicalState
  timeSamples    : List UsdPhysicalState
  deriving DecidableEq, Repr

/-- Project an `OpenUsdViewportSpec` into canonical `Core.Data`. -/
def openUsdSceneToData (spec : OpenUsdViewportSpec) : Data :=
  let relocated := applyUsdRelocate spec.relocateSrc spec.relocateDst spec.primPath
  let roundtrip := applyUsdRelocate spec.relocateDst spec.relocateSrc relocated
  let finalSt := finalUsdState spec.initSample spec.timeSamples
  let chainValid :=
    checkPartLifecycleInvariant spec.minWallUm spec.maxTempMilliC spec.initSample &&
    checkUsdTimeSampleChain spec.minWallUm spec.maxTempMilliC spec.initSample spec.timeSamples
  let finalInvariantOk := checkPartLifecycleInvariant spec.minWallUm spec.maxTempMilliC finalSt
  .record [
    ("kind", .label "physical_openusd_scene"),
    ("stage_name", .label spec.stageName),
    ("prim_path", sdfPathToData spec.primPath),
    ("relocated_path", sdfPathToData relocated),
    ("relocate_roundtrip_ok", .boolean (roundtrip == spec.primPath)),
    ("affine_sdf", affineSdfToData spec.sdfWallForm),
    ("sample_count", .natural (spec.timeSamples.length + 1)),
    ("final_state", usdStateToData finalSt),
    ("chain_valid", .boolean chainValid),
    ("final_invariant_ok", .boolean finalInvariantOk)
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for an OpenUSD scene-graph and lifecycle track. -/
def projectOpenUsdScene
    (id : String)
    (spec : OpenUsdViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareLayout (openUsdSceneToData spec) pins receipt

/-! ## 3. Coupled LC-Drive Stator Multiphysics & Continuous ODE Flowpipe Projection -/

/-- Specification for a coupled Courant $P_1$ stator FEMM + continuous ODE flowpipe viewport cell. -/
structure StatorMultiphysicsViewportSpec where
  partName       : String
  statorTriangle : FemmTriangle2D
  ode            : OdeSystem
  initBox        : List (String × Interval)
  steps          : Nat
  safeBounds     : List (String × Interval)
  deriving DecidableEq, Repr

/-- Project a `StatorMultiphysicsViewportSpec` into canonical `Core.Data`. -/
def statorMultiphysicsToData (spec : StatorMultiphysicsViewportSpec) : Data :=
  let statorBook := emit goldenLcDrivesStatorComp
  let femmCoEnergy := evalElementMagneticEnergyAreaScaled 1000000 spec.statorTriangle 10 (-4) 6
  let flowpipeSafe := verifyTrajectorySafety spec.ode spec.initBox spec.steps spec.safeBounds
  .record [
    ("kind", .label "physical_stator_multiphysics"),
    ("part_name", .label spec.partName),
    ("stator_slot_count", .natural statorBook.slots.length),
    ("stator_book_closed", .boolean statorBook.closedB),
    ("femm_coenergy_scaled", dInt femmCoEnergy),
    ("flowpipe_steps", .natural spec.steps),
    ("flowpipe_safe", .boolean flowpipeSafe),
    ("status", .label (if flowpipeSafe && statorBook.closedB then "MULTIPHYSICS_CERTIFIED" else "UNSAFE"))
  ]

/-- Construct a `.obnb` `Doc.Content.cell` quotation for coupled LC-drive stator multiphysics. -/
def projectStatorMultiphysics
    (id : String)
    (spec : StatorMultiphysicsViewportSpec)
    (pins : List (String × ByteArray) := [])
    (receipt : Option ByteArray := none) : Doc.Content :=
  .cell id .hardwareTiming (statorMultiphysicsToData spec) pins receipt

/-! ## 4. Concrete Golden Physical Viewport Specs & Soundness Theorems -/

/-- Golden 5-axis CNC toolpath viewport specification (`Cnc5AxisMill.obend`). -/
def goldenCncViewportSpec : CncToolpathViewportSpec where
  machineName := "Hermle_C42U_5Axis"
  pTarget     := { x := 100000, y := 200000, z := 50000 }
  linErr      := { x := 12, y := -8, z := 5 }
  angErr      := { x := 2, y := -3, z := 1 }
  abbeArm     := { x := 0, y := 0, z := 150 }
  twist       := { ang := { x := 3, y := -4, z := 12 }, lin := { x := 50, y := -20, z := 10 } }
  momentum    := { torque := { x := 90, y := -80, z := 240 }, force := { x := 250, y := -100, z := 50 } }
  ruckigInit  := { posScaled6 := 0, velScaled2 := 0, acc := 0 }
  jerkPulse   := 5
  pulseDt     := 4

/-- Golden OpenUSD scene-graph & `timeSamples` viewport specification (`LcDrivesStatorUsd.obend`). -/
def goldenOpenUsdViewportSpec : OpenUsdViewportSpec where
  stageName     := "LcDrives_Production_Stator"
  primPath      := ["Factory", "Draft", "Stator", "Slot01"]
  relocateSrc   := ["Factory", "Draft"]
  relocateDst   := ["Prod", "LCDrives"]
  sdfWallForm   := { c0 := 1500, c1 := 15, c2 := 10 }
  minWallUm     := 1200
  maxTempMilliC := 180000
  initSample    := { timeCode := 0, wallThicknessUm := 5000, peakTempMilliC := 25000, receiptDigest := 101 }
  timeSamples   :=
    [ { timeCode := 10,  wallThicknessUm := 2200, peakTempMilliC := 65000,  receiptDigest := 202 }
    , { timeCode := 20,  wallThicknessUm := 1500, peakTempMilliC := 55000,  receiptDigest := 303 }
    , { timeCode := 100, wallThicknessUm := 1500, peakTempMilliC := 122000, receiptDigest := 404 } ]

/-- Golden coupled LC-drive stator multiphysics + continuous `Flowpipe` viewport specification.

`safeBounds` is what the degree-1 interval flowpipe certifies for the whole continuous tube, not what
the physics does: from `T ∈ [28, 30]` the solutions of `Ṫ = 20 − T` never leave `[19.9, 30]`, but the
box enclosures widen by about 1.9× per half-second step (the Lie remainder is evaluated over the
a-priori box), and at the third step the a-priori enclosure reaches down to about 14.6. The earlier
`[15, 35]` was passed only by the discrete slices; `verifyTrajectorySafety` now checks the a-priori
enclosures too, so the bound is the method's, `[12, 35]`, as in `Flowpipe`'s own fixture. A tighter
bound needs a mean-value (Lohner) step, not a looser spec. -/
def goldenStatorMultiphysicsSpec : StatorMultiphysicsViewportSpec where
  partName       := "LC_Drives_InSlot_Stator_Assy"
  statorTriangle := goldenStatorToothTriangle
  ode            := thermalCoolingOde
  initBox        := [("T", ⟨28, 30⟩)]
  steps          := 3
  safeBounds     := [("T", ⟨12, 35⟩)]

/-- **Theorem (`physical_projection_deterministic`)**:
All three physical-world `.obnb` projection functions (`projectCncToolpath`, `projectOpenUsdScene`,
`projectStatorMultiphysics`) are deterministic functions of their inputs. -/
theorem physical_projection_deterministic
    (id : String)
    (cnc1 cnc2 : CncToolpathViewportSpec)
    (usd1 usd2 : OpenUsdViewportSpec)
    (st1 st2 : StatorMultiphysicsViewportSpec)
    (hCnc : cnc1 = cnc2) (hUsd : usd1 = usd2) (hSt : st1 = st2) :
    projectCncToolpath id cnc1 = projectCncToolpath id cnc2 ∧
    projectOpenUsdScene id usd1 = projectOpenUsdScene id usd2 ∧
    projectStatorMultiphysics id st1 = projectStatorMultiphysics id st2 := by
  subst hCnc hUsd hSt
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem (`physical_cnc_abbe_projection_sound`)**:
1. For ANY `CncToolpathViewportSpec`, pre-compensating the CNC command by `evalAbbeCompensatedCmd3D`
   cancels the 21-parameter volumetric + Abbe lever-arm error (`abbe_volumetric_compensation_exact`),
   and the Featherstone gyroscopic/Coriolis wrench performs zero mechanical work (`rnea_gyroscopic_coriolis_power_zero`).
2. On `goldenCncViewportSpec`, `cncToolpathToData` certifies `"abbe_exact_cancelled" = true`,
   `"coriolis_power" = 0`, and `"userspace_mill_closed" = true`. -/
theorem physical_cnc_abbe_projection_sound (spec : CncToolpathViewportSpec) :
    evalUncompensatedTipPos3D
      (evalAbbeCompensatedCmd3D spec.pTarget spec.linErr spec.angErr spec.abbeArm)
      spec.linErr spec.angErr spec.abbeArm = spec.pTarget ∧
    spatialPower (spatialCrossForce spec.twist spec.momentum) spec.twist = 0 ∧
    (emit goldenCnc5AxisMillComp).closedB = true := by
  refine ⟨abbe_volumetric_compensation_exact spec.pTarget spec.linErr spec.angErr spec.abbeArm,
    rnea_gyroscopic_coriolis_power_zero spec.twist spec.momentum,
    by decide +kernel⟩

/-- The concrete OpenUSD and stator fixtures satisfy relocation, affine cancellation,
    lifecycle, trajectory, and closed-program checks. Universal contracts are supplied by
    `usd_relocate_roundtrip_exact` and `affine_sub_self_exact_zero`. -/
theorem physical_openusd_lifecycle_fixture :
    let usd := goldenOpenUsdViewportSpec
    let stator := goldenStatorMultiphysicsSpec
    applyUsdRelocate usd.relocateDst usd.relocateSrc
      (applyUsdRelocate usd.relocateSrc usd.relocateDst usd.primPath) = usd.primPath ∧
    (AffineForm1D.sub usd.sdfWallForm usd.sdfWallForm).toInterval = { lo := 0, hi := 0 } ∧
    checkPartLifecycleInvariant usd.minWallUm usd.maxTempMilliC
      (finalUsdState usd.initSample usd.timeSamples) = true ∧
    verifyTrajectorySafety stator.ode stator.initBox stator.steps stator.safeBounds = true ∧
    (emit goldenLcDrivesStatorComp).closedB = true := by
  decide +kernel

/-- **Theorem (`physical_projection_doc_noninterference`)**:
Inserting any projected physical-world cell (`projectCncToolpath`, `projectOpenUsdScene`, or
`projectStatorMultiphysics`) into a `.obnb` document graph at `newAtom` preserves all existing
atoms `otherAtom ≠ newAtom`. -/
theorem physical_projection_doc_noninterference
    (G : Graph) (newAtom : AtomId) (cell : Doc.Content)
    (otherAtom : AtomId) (hNe : otherAtom ≠ newAtom) :
    (((newAtom, cell) :: G.atoms).lookup otherAtom) = G.atoms.lookup otherAtom :=
  Obend.Vault.HardwareProjection.hardware_projection_doc_noninterference G newAtom cell otherAtom hNe

end Obend.Vault.PhysicalProjection
end
