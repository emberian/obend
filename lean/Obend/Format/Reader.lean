module
/-
# Obend.Format.Reader — Pluggable Higher-Layer Format Readers Atop `.obend` & Core4

Provides the universal `FormatReader (SurfaceAST : Type)` interface and 4 concrete,
machine-checked instances:
1. `obnbReader` (`"obnb@1"`): Literate `.obnb` / Markdown workbook reader interleaving prose
   sections, `.obend` cells, `.lean` bridge cells, and `law:` frontmatter.
2. `usdStageReader` (`"usd-stage@1"`): OpenUSD stage reader (`def Xform`, `over`, `subLayers`,
   6D kinematic/thermal attributes) lowering USD layer overrides into `.obend` open-recursive
   `spec` compositions (`extends`, `around`, `def`).
3. `dfaPolicyReader` (`"dfa-policy@1"`): Parser-automaton & prompt/API-transcript confinement
   reader lowering a grammar/DFA + nominal `#kind` hole confinement policy into an `.obend`
   `Syntax.Module` with state-transition methods and an unforgeable `#kind` confinement `law`.
4. `deploymentTopologyReader` (`"dreggnet-deploy@1"`): Elastic cloud deployment reader
   (grains, sturdyref channels, mandate budgets, and TEE attestation pins) lowering into an
   `.obend` `Syntax.Module` of composed specs and laws.
-/
public import Lean
public import Obend.Core.Data
public import Obend.Doc.Structured
public import Obend.Spec.Law
public import Obend.Spec.Syntax
public import Obend.Spec.Parse
public import Obend.Spec.Elaborate
public import Obend.Spec.FrontEnd

@[expose] public section

namespace Obend.Core
abbrev Data := Obend.Core.Data.Data
end Obend.Core

namespace Obend.Format

open Lean (Json toJson)
open Obend.Core.Data (Data)
open Obend.Doc (ProjectionKind)
open Obend.Spec.Syntax
open Obend.Spec.Law (LawExpr LawRef)

set_option autoImplicit false

/-! ## 1. Universal `FormatReader` Interface & FrontEnd Elaboration Bridge -/

/-- Pluggable higher-layer format reader lowering a domain-specific `SurfaceAST` into
    `Obend.Core.Data` (with a verified roundtrip theorem) and `Obend.Spec.Syntax.Module`. -/
structure FormatReader (SurfaceAST : Type) where
  formatId : String
  projectionKind : ProjectionKind
  parse : String → Except String SurfaceAST
  render : SurfaceAST → String
  toCoreData : SurfaceAST → Obend.Core.Data
  ofCoreData : Obend.Core.Data → Option SurfaceAST
  lowerToObend : SurfaceAST → Module
  data_roundtrip : ∀ a, ofCoreData (toCoreData a) = some a

/-- Default execution/checker limits for verifying lowered `.obend` modules through `FrontEnd`. -/
def defaultReaderLimits : Json :=
  Json.mkObj [("heap", toJson "10000"), ("stack", toJson "10000"), ("ticks", toJson "10000")]

/-- Elaborate a lowered `Syntax.Module` through `Obend.Spec.Elaborate.elaborate`. -/
def elaborateLoweredModule (m : Module) (entryDef : String := "entry") :
    Except String Obend.Spec.Elaborate.Output :=
  Obend.Spec.Elaborate.elaborate [m] 0 entryDef (.arr #[]) "application"

/-- Run a lowered `Syntax.Module` through the full `Obend.Spec.FrontEnd.lowerDecoded` and
    `Obend.Spec.FrontEnd.accept` pipeline (bidirectional typechecker, template rigidity checker,
    and package law compiler). -/
def acceptLoweredModule (m : Module) (entryDef : String := "entry") :
    Except String (Σ l : Obend.Spec.FrontEnd.Lowering, Obend.Spec.FrontEnd.Accepted l) := do
  let srcMod : Obend.Spec.FrontEnd.SourceModule := {
    name := m.name
    source := ""
    sha256 := ""
    imports := []
  }
  let lowering ← match Obend.Spec.FrontEnd.lowerDecoded [srcMod] [m] 0 entryDef
      (.arr #[]) (.arr #[]) defaultReaderLimits "application" with
    | .ok l => pure l
    | .error d => .error d.message
  match Obend.Spec.FrontEnd.accept lowering with
  | .ok acc => .ok ⟨lowering, acc⟩
  | .error d => .error d.message

/-- Boolean predicate checking that `reader.lowerToObend ast` passes both `Elaborate` and
    `FrontEnd.accept`. -/
def acceptsReaderAST {SurfaceAST : Type} (reader : FormatReader SurfaceAST)
    (ast : SurfaceAST) (entryDef : String := "entry") : Bool :=
  (acceptLoweredModule (reader.lowerToObend ast) entryDef).isOk

/-! ### Generic `Core.Data` List Encoding Helpers -/

def encodeListData {α : Type} (enc : α → Data) : List α → Data
  | [] => .variant "nil" (.record [])
  | x :: xs => .variant "cons" (.record [("head", enc x), ("tail", encodeListData enc xs)])

def decodeListData {α : Type} (dec : Data → Option α) : Data → Option (List α)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [(_, h), (_, t)]) =>
      match dec h, decodeListData dec t with
      | some x, some xs => some (x :: xs)
      | _, _ => none
  | _ => none

theorem decodeListData_encodeListData {α : Type} (enc : α → Data) (dec : Data → Option α)
    (hrt : ∀ x, dec (enc x) = some x) :
    ∀ xs : List α, decodeListData dec (encodeListData enc xs) = some xs
  | [] => rfl
  | x :: xs => by
      simp only [encodeListData, decodeListData, hrt x, decodeListData_encodeListData enc dec hrt xs]

def encodeStringData (s : String) : Data := .label s

def decodeStringData : Data → Option String
  | .label s => some s
  | _ => none

theorem decodeStringData_encodeStringData (s : String) :
    decodeStringData (encodeStringData s) = some s := rfl

def encodeNatData (n : Nat) : Data := .natural n

def decodeNatData : Data → Option Nat
  | .natural n => some n
  | _ => none

theorem decodeNatData_encodeNatData (n : Nat) :
    decodeNatData (encodeNatData n) = some n := rfl

/-! ### Helper for constructing a valid method signature Json -/

def mkSigJson (name : String) (params : List Param) (resultType : String) : Json :=
  let paramJsons := params.map fun p =>
    Json.mkObj [("name", toJson p.name), ("type", toJson p.type), ("quantity", toJson p.quantity)]
  Json.mkObj [("name", toJson name), ("parameters", Json.arr paramJsons.toArray), ("resultType", toJson resultType)]

/-! ## 2. FormatReader 1: `obnbReader` (`"obnb@1"`) — Literate `.obnb` / Markdown Workbook -/

/-- A cell in an `.obnb` literate workbook. -/
inductive ObnbCell where
  | prose (heading : String) (markdown : String)
  | obend (cellName : String) (stateField : String) (stepDelta : Nat)
  | leanBridge (theoremName : String) (targetSpec : String)
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an `.obnb` literate workbook. -/
structure ObnbWorkbook where
  title : String
  lawName : String
  boundField : String
  maxBound : Nat
  cells : List ObnbCell
  deriving DecidableEq, Repr, Inhabited

def encodeObnbCell : ObnbCell → Data
  | .prose h m => .variant "prose" (.record [("heading", .label h), ("markdown", .label m)])
  | .obend n f d => .variant "obend" (.record [("cellName", .label n), ("stateField", .label f), ("stepDelta", .natural d)])
  | .leanBridge t s => .variant "lean" (.record [("theoremName", .label t), ("targetSpec", .label s)])

def decodeObnbCell : Data → Option ObnbCell
  | .variant "prose" (.record [(_, .label h), (_, .label m)]) => some (.prose h m)
  | .variant "obend" (.record [(_, .label n), (_, .label f), (_, .natural d)]) => some (.obend n f d)
  | .variant "lean" (.record [(_, .label t), (_, .label s)]) => some (.leanBridge t s)
  | _ => none

theorem decodeObnbCell_encodeObnbCell : ∀ c : ObnbCell, decodeObnbCell (encodeObnbCell c) = some c
  | .prose _ _ => rfl
  | .obend _ _ _ => rfl
  | .leanBridge _ _ => rfl

def obnbToCoreData (w : ObnbWorkbook) : Data :=
  .record [
    ("title", .label w.title),
    ("lawName", .label w.lawName),
    ("boundField", .label w.boundField),
    ("maxBound", .natural w.maxBound),
    ("cells", encodeListData encodeObnbCell w.cells)
  ]

def obnbOfCoreData : Data → Option ObnbWorkbook
  | .record [(_, .label title), (_, .label lawName), (_, .label boundField), (_, .natural maxBound), (_, cellsD)] =>
      match decodeListData decodeObnbCell cellsD with
      | some cells => some ⟨title, lawName, boundField, maxBound, cells⟩
      | none => none
  | _ => none

theorem obnb_data_roundtrip (w : ObnbWorkbook) :
    obnbOfCoreData (obnbToCoreData w) = some w := by
  cases w with
  | mk title lawName boundField maxBound cells =>
    simp only [obnbToCoreData, obnbOfCoreData,
      decodeListData_encodeListData encodeObnbCell decodeObnbCell decodeObnbCell_encodeObnbCell cells]

/-- Render an `ObnbWorkbook` to `.obnb` literate Markdown text. -/
def renderObnb (w : ObnbWorkbook) : String :=
  let header := s!"---\nformat: obnb@1\ntitle: {w.title}\nlaw: {w.lawName}\nfield: {w.boundField}\nmaxBound: {w.maxBound}\n---\n"
  let body := String.intercalate "\n" (w.cells.map fun c =>
    match c with
    | .prose h m => s!"# {h}\n{m}"
    | .obend n f d => s!"```obend {n}\n{f} += {d}\n```"
    | .leanBridge t s => s!"```lean {t}\nbridge {s}\n```")
  header ++ body

/-- Parse an `.obnb` literate Markdown workbook into `ObnbWorkbook`. -/
def parseObnb (input : String) : Except String ObnbWorkbook := do
  let rawLines := (input.splitOn "\n").map trimStr |>.filter (fun l => !l.isEmpty && l != "---")
  if rawLines.isEmpty then .error "empty obnb@1 workbook"
  let mut title := "Workbook"
  let mut lawName := "workbookLaw"
  let mut boundField := "progress"
  let mut maxBound : Nat := 100
  let mut cells : List ObnbCell := []
  for l in rawLines do
    if l.startsWith "format:" then
      let fmt := trimStr (dropStr l 7)
      if fmt != "obnb@1" then throw s!"unsupported obnb format: {fmt}"
    else if l.startsWith "title:" then
      title := trimStr (dropStr l 6)
    else if l.startsWith "law:" then
      lawName := trimStr (dropStr l 4)
    else if l.startsWith "field:" then
      boundField := trimStr (dropStr l 6)
    else if l.startsWith "maxBound:" then
      match (trimStr (dropStr l 9)).toNat? with
      | some n => maxBound := n
      | none => throw "invalid maxBound in obnb@1 frontmatter"
    else if l.startsWith "# " then
      let h := trimStr (dropStr l 2)
      cells := cells ++ [.prose h h]
    else if l.startsWith "cell-obend:" then
      let parts := (trimStr (dropStr l 11)).splitOn ":"
      match parts with
      | [n, f, dStr] =>
        let d ← match dStr.toNat? with | some v => pure v | none => throw "invalid obend cell delta"
        cells := cells ++ [.obend (trimStr n) (trimStr f) d]
      | _ => throw "invalid cell-obend syntax (expected cell-obend: name:field:delta)"
    else if l.startsWith "cell-lean:" then
      let parts := (trimStr (dropStr l 10)).splitOn ":"
      match parts with
      | [t, s] => cells := cells ++ [.leanBridge (trimStr t) (trimStr s)]
      | _ => throw "invalid cell-lean syntax (expected cell-lean: theorem:spec)"
    else pure ()
  if !Obend.Spec.Law.plainName boundField then
    throw s!"invalid boundField `{boundField}` in obnb@1"
  return { title, lawName, boundField, maxBound, cells }

/-- Lower an `ObnbWorkbook` into a unified `.obend` `Syntax.Module`. -/
def lowerObnbToObend (w : ObnbWorkbook) : Module :=
  let fld := if Obend.Spec.Law.plainName w.boundField then w.boundField else "progress"
  let lName := if Obend.Spec.Law.plainName w.lawName then w.lawName else "workbookLaw"
  let totalDelta : Nat := w.cells.foldl (fun acc c =>
    match c with
    | .obend _ _ d => acc + d
    | _ => acc) 1
  let bridgeMethod : IsarMethod :=
    match w.cells.findSome? (fun c => match c with | .leanBridge t _ => some t | _ => none) with
    | some thm => .lean thm
    | none => .weave
  let deltaParam : Param := ⟨"delta", "Nat", "default"⟩
  let stepSig : Signature := ⟨"step", [deltaParam], "Nat"⟩
  let stepMethod : Method := {
    name := "step"
    params := [deltaParam]
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") fld) (.var "delta"))
    signature := mkSigJson "step" [deltaParam] "Nat"
  }
  let claim : Claim := {
    name := "monotoneStep"
    params := [deltaParam]
    body := .binary "<=" (.member (.var "self") fld) (.call (.member (.var "self") "step") [.var "delta"])
    method := some bridgeMethod
    steps := [.showStep (.bool true) bridgeMethod]
  }
  let wbSpec : Spec := {
    name := "WorkbookSpec"
    suffix := false
    parents := []
    targetType := "WorkbookState"
    requirements := .arr #[]
    methods := [stepMethod]
    claims := [claim]
  }
  let seedRec : Expr := .record [
    (fld, .nat "0"),
    ("step", .closure [deltaParam] "Nat" (.var "delta"))
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.call (.member (.fix (.var "WorkbookSpec") seedRec) "step") [.nat (toString totalDelta)]))
  let lawExpr : LawExpr :=
    .and (.monotone fld) (.leC (.field fld) (Int.ofNat w.maxBound))
  let contract : ContractDecl := {
    name := lName ++ "Contract"
    targetType := "WorkbookState"
    invariant := some (.binary "<=" (.member (.var "self") fld) (.nat (toString w.maxBound)))
    law := some lawExpr
    method := some bridgeMethod
    steps := [.showStep (.bool true) .omega]
  }
  { name := "ObnbWorkbookModule"
    imports := []
    decls := [
      .record "WorkbookState" [(fld, "Nat")] [stepSig],
      .spec wbSpec,
      entryFn
    ]
    laws := [(lName, lawExpr)]
    header := none
    keeps := []
    lawMethods := [(lName, .omega)]
    contracts := [contract] }

/-- Concrete verified `FormatReader` instance for `.obnb` literate workbooks (`"obnb@1"`). -/
def obnbReader : FormatReader ObnbWorkbook where
  formatId := "obnb@1"
  projectionKind := .obendCode
  parse := parseObnb
  render := renderObnb
  toCoreData := obnbToCoreData
  ofCoreData := obnbOfCoreData
  lowerToObend := lowerObnbToObend
  data_roundtrip := obnb_data_roundtrip

/-! ## 3. FormatReader 2: `usdStageReader` (`"usd-stage@1"`) — OpenUSD Stage Composition -/

/-- A 6D kinematic + thermal USD layer (`def Xform` or `over`). -/
structure UsdLayer where
  layerName : String
  isOver : Bool
  posX : Nat
  posY : Nat
  posZ : Nat
  velX : Nat
  velY : Nat
  thermalMk : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an OpenUSD stage (`"usd-stage@1"`). -/
structure UsdStage where
  stageName : String
  subLayers : List String
  maxThermalMk : Nat
  baseXform : UsdLayer
  overrides : List UsdLayer
  deriving DecidableEq, Repr, Inhabited

def encodeUsdLayer (l : UsdLayer) : Data :=
  .record [
    ("layerName", .label l.layerName),
    ("isOver", .boolean l.isOver),
    ("posX", .natural l.posX),
    ("posY", .natural l.posY),
    ("posZ", .natural l.posZ),
    ("velX", .natural l.velX),
    ("velY", .natural l.velY),
    ("thermalMk", .natural l.thermalMk)
  ]

def decodeUsdLayer : Data → Option UsdLayer
  | .record [(_, .label n), (_, .boolean over), (_, .natural px), (_, .natural py),
             (_, .natural pz), (_, .natural vx), (_, .natural vy), (_, .natural th)] =>
      some ⟨n, over, px, py, pz, vx, vy, th⟩
  | _ => none

theorem decodeUsdLayer_encodeUsdLayer (l : UsdLayer) :
    decodeUsdLayer (encodeUsdLayer l) = some l := by
  cases l; rfl

def usdStageToCoreData (s : UsdStage) : Data :=
  .record [
    ("stageName", .label s.stageName),
    ("subLayers", encodeListData encodeStringData s.subLayers),
    ("maxThermalMk", .natural s.maxThermalMk),
    ("baseXform", encodeUsdLayer s.baseXform),
    ("overrides", encodeListData encodeUsdLayer s.overrides)
  ]

def usdStageOfCoreData : Data → Option UsdStage
  | .record [(_, .label sName), (_, subsD), (_, .natural maxTh), (_, baseD), (_, oversD)] =>
      match decodeListData decodeStringData subsD,
            decodeUsdLayer baseD,
            decodeListData decodeUsdLayer oversD with
      | some subs, some base, some overs => some ⟨sName, subs, maxTh, base, overs⟩
      | _, _, _ => none
  | _ => none

theorem usdStage_data_roundtrip (s : UsdStage) :
    usdStageOfCoreData (usdStageToCoreData s) = some s := by
  cases s with
  | mk sName subs maxTh base overs =>
    simp only [usdStageToCoreData, usdStageOfCoreData,
      decodeListData_encodeListData encodeStringData decodeStringData decodeStringData_encodeStringData subs,
      decodeUsdLayer_encodeUsdLayer base,
      decodeListData_encodeListData encodeUsdLayer decodeUsdLayer decodeUsdLayer_encodeUsdLayer overs]

/-- Render a `UsdStage` to OpenUSD ASCII (`#usda 1.0`) text. -/
def renderUsdStage (s : UsdStage) : String :=
  let subs := String.intercalate "," s.subLayers
  let b := s.baseXform
  let overLines := s.overrides.map fun o =>
    s!"over {o.layerName} {o.posX} {o.posY} {o.posZ} {o.velX} {o.velY} {o.thermalMk}"
  String.intercalate "\n" ([
    "#usda 1.0",
    s!"stage: {s.stageName}",
    s!"subLayers: {subs}",
    s!"maxThermalMk: {s.maxThermalMk}",
    s!"def Xform {b.layerName} {b.posX} {b.posY} {b.posZ} {b.velX} {b.velY} {b.thermalMk}"
  ] ++ overLines)

def parseUsdLayerLine (prefixTag : String) (isOver : Bool) (line : String) : Except String UsdLayer := do
  let rest := trimStr (dropStr line prefixTag.length)
  let toks := (rest.splitOn " ").map trimStr |>.filter (fun t => !t.isEmpty)
  match toks with
  | [name, px, py, pz, vx, vy, th] =>
    let some posX := px.toNat? | throw "invalid posX in usd-stage@1"
    let some posY := py.toNat? | throw "invalid posY in usd-stage@1"
    let some posZ := pz.toNat? | throw "invalid posZ in usd-stage@1"
    let some velX := vx.toNat? | throw "invalid velX in usd-stage@1"
    let some velY := vy.toNat? | throw "invalid velY in usd-stage@1"
    let some thermalMk := th.toNat? | throw "invalid thermalMk in usd-stage@1"
    return { layerName := name, isOver, posX, posY, posZ, velX, velY, thermalMk }
  | _ => throw s!"invalid USD layer syntax in `{line}`"

/-- Parse an OpenUSD ASCII stage (`"usd-stage@1"`). -/
def parseUsdStage (input : String) : Except String UsdStage := do
  let lines := (input.splitOn "\n").map trimStr |>.filter (fun l => !l.isEmpty)
  if !(lines.any (fun l => l == "#usda 1.0")) then
    throw "missing #usda 1.0 header"
  let mut stageName := "DefaultStage"
  let mut subLayers : List String := []
  let mut maxThermalMk : Nat := 350000
  let mut baseOpt : Option UsdLayer := none
  let mut overrides : List UsdLayer := []
  for l in lines do
    if l == "#usda 1.0" then pure ()
    else if l.startsWith "stage:" then
      stageName := trimStr (dropStr l 6)
    else if l.startsWith "subLayers:" then
      let raw := trimStr (dropStr l 10)
      subLayers := if raw.isEmpty then [] else (raw.splitOn ",").map trimStr
    else if l.startsWith "maxThermalMk:" then
      let some v := (trimStr (dropStr l 13)).toNat? | throw "invalid maxThermalMk"
      maxThermalMk := v
    else if l.startsWith "def Xform " then
      baseOpt := some (← parseUsdLayerLine "def Xform " false l)
    else if l.startsWith "over " then
      overrides := overrides ++ [← parseUsdLayerLine "over " true l]
    else throw s!"unrecognized usd-stage@1 line: {l}"
  let some base := baseOpt | throw "usd-stage@1 requires a base `def Xform` layer"
  return { stageName, subLayers, maxThermalMk, baseXform := base, overrides }

/-- Lower a `UsdStage` into an `.obend` `Syntax.Module` with open-recursive `spec` compositions
    (`extends`, `around`, `def`) over 6D kinematic/thermal attributes. -/
def lowerUsdStageToObend (s : UsdStage) : Module :=
  let sampleSig : Signature := ⟨"sample", [], "Nat"⟩
  let baseSample : Method := {
    name := "sample"
    params := []
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "posX") (.member (.var "self") "thermalMk"))
    signature := mkSigJson "sample" [] "Nat"
  }
  let baseClaim : Claim := {
    name := "thermalBounded"
    params := []
    body := .binary "<=" (.member (.var "self") "thermalMk") (.member (.var "self") "sample")
    method := some .frame
  }
  let baseSpec : Spec := {
    name := "BaseXform"
    suffix := false
    parents := []
    targetType := "Xform6D"
    requirements := .arr #[]
    methods := [baseSample]
    claims := [baseClaim]
  }
  let overDelta : Nat := s.overrides.foldl (fun acc o => acc + o.posX + o.velX) 0
  let overSample : Method := {
    name := "sample"
    params := []
    resultType := "Nat"
    qualifier := "around"
    body := .expr (.binary "+" (.member (.var "super") "sample") (.nat (toString overDelta)))
    signature := mkSigJson "sample" [] "Nat"
  }
  let overSpec : Spec := {
    name := "OverXform"
    suffix := false
    parents := ["BaseXform"]
    targetType := "Xform6D"
    requirements := .arr #[]
    methods := [overSample]
    claims := []
  }
  let b := s.baseXform
  let seedRec : Expr := .record [
    ("posX", .nat (toString b.posX)),
    ("posY", .nat (toString b.posY)),
    ("posZ", .nat (toString b.posZ)),
    ("velX", .nat (toString b.velX)),
    ("velY", .nat (toString b.velY)),
    ("thermalMk", .nat (toString b.thermalMk)),
    ("sample", .nat "0")
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.member (.fix (.var "OverXform") seedRec) "sample"))
  let thermalLaw : LawExpr :=
    .and (.leC (.field "thermalMk") (Int.ofNat s.maxThermalMk)) (.monotone "posX")
  { name := "UsdStageModule"
    imports := []
    decls := [
      .record "Xform6D" [
        ("posX", "Nat"), ("posY", "Nat"), ("posZ", "Nat"),
        ("velX", "Nat"), ("velY", "Nat"), ("thermalMk", "Nat")
      ] [sampleSig],
      .spec baseSpec,
      .spec overSpec,
      entryFn
    ]
    laws := [("thermalBound", thermalLaw)]
    header := none
    keeps := []
    lawMethods := [("thermalBound", .frame)]
    contracts := [{
      name := "UsdThermalContract"
      targetType := "Xform6D"
      law := some thermalLaw
      method := some .frame
    }] }

/-- Concrete verified `FormatReader` instance for OpenUSD stages (`"usd-stage@1"`). -/
def usdStageReader : FormatReader UsdStage where
  formatId := "usd-stage@1"
  projectionKind := .hardwareLayout
  parse := parseUsdStage
  render := renderUsdStage
  toCoreData := usdStageToCoreData
  ofCoreData := usdStageOfCoreData
  lowerToObend := lowerUsdStageToObend
  data_roundtrip := usdStage_data_roundtrip

/-! ## 4. FormatReader 3: `dfaPolicyReader` (`"dfa-policy@1"`) — DFA & `#kind` Confinement -/

/-- A transition in a prompt/API-transcript DFA. -/
structure DfaTransition where
  fromState : Nat
  tokenClass : Nat
  toState : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A nominal `#kind` hole confinement rule pinning a transcript slot to an unforgeable kind tag. -/
structure HoleConfinement where
  holeName : String
  requiredKindTag : Nat
  allowedState : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for a parser-automaton & nominal `#kind` confinement policy (`"dfa-policy@1"`). -/
structure DfaPolicy where
  policyName : String
  initialState : Nat
  acceptingStates : List Nat
  transitions : List DfaTransition
  holes : List HoleConfinement
  deriving DecidableEq, Repr, Inhabited

def encodeDfaTransition (t : DfaTransition) : Data :=
  .record [
    ("fromState", .natural t.fromState),
    ("tokenClass", .natural t.tokenClass),
    ("toState", .natural t.toState)
  ]

def decodeDfaTransition : Data → Option DfaTransition
  | .record [(_, .natural f), (_, .natural tok), (_, .natural toSt)] => some ⟨f, tok, toSt⟩
  | _ => none

theorem decodeDfaTransition_encodeDfaTransition (t : DfaTransition) :
    decodeDfaTransition (encodeDfaTransition t) = some t := by
  cases t; rfl

def encodeHoleConfinement (h : HoleConfinement) : Data :=
  .record [
    ("holeName", .label h.holeName),
    ("requiredKindTag", .natural h.requiredKindTag),
    ("allowedState", .natural h.allowedState)
  ]

def decodeHoleConfinement : Data → Option HoleConfinement
  | .record [(_, .label n), (_, .natural k), (_, .natural st)] => some ⟨n, k, st⟩
  | _ => none

theorem decodeHoleConfinement_encodeHoleConfinement (h : HoleConfinement) :
    decodeHoleConfinement (encodeHoleConfinement h) = some h := by
  cases h; rfl

def dfaPolicyToCoreData (p : DfaPolicy) : Data :=
  .record [
    ("policyName", .label p.policyName),
    ("initialState", .natural p.initialState),
    ("acceptingStates", encodeListData encodeNatData p.acceptingStates),
    ("transitions", encodeListData encodeDfaTransition p.transitions),
    ("holes", encodeListData encodeHoleConfinement p.holes)
  ]

def dfaPolicyOfCoreData : Data → Option DfaPolicy
  | .record [(_, .label pName), (_, .natural initSt), (_, accD), (_, transD), (_, holesD)] =>
      match decodeListData decodeNatData accD,
            decodeListData decodeDfaTransition transD,
            decodeListData decodeHoleConfinement holesD with
      | some accs, some trs, some hls => some ⟨pName, initSt, accs, trs, hls⟩
      | _, _, _ => none
  | _ => none

theorem dfaPolicy_data_roundtrip (p : DfaPolicy) :
    dfaPolicyOfCoreData (dfaPolicyToCoreData p) = some p := by
  cases p with
  | mk pName initSt accs trs hls =>
    simp only [dfaPolicyToCoreData, dfaPolicyOfCoreData,
      decodeListData_encodeListData encodeNatData decodeNatData decodeNatData_encodeNatData accs,
      decodeListData_encodeListData encodeDfaTransition decodeDfaTransition decodeDfaTransition_encodeDfaTransition trs,
      decodeListData_encodeListData encodeHoleConfinement decodeHoleConfinement decodeHoleConfinement_encodeHoleConfinement hls]

/-- Render a `DfaPolicy` to `"dfa-policy@1"` text. -/
def renderDfaPolicy (p : DfaPolicy) : String :=
  let accStr := String.intercalate "," (p.acceptingStates.map toString)
  let trLines := p.transitions.map fun t => s!"transition: {t.fromState} {t.tokenClass} {t.toState}"
  let holeLines := p.holes.map fun h => s!"hole: {h.holeName} {h.requiredKindTag} {h.allowedState}"
  String.intercalate "\n" ([
    "format: dfa-policy@1",
    s!"policy: {p.policyName}",
    s!"initial: {p.initialState}",
    s!"accepting: {accStr}"
  ] ++ trLines ++ holeLines)

/-- Parse a `"dfa-policy@1"` manifest into `DfaPolicy`. -/
def parseDfaPolicy (input : String) : Except String DfaPolicy := do
  let lines := (input.splitOn "\n").map trimStr |>.filter (fun l => !l.isEmpty)
  if !(lines.any (fun l => l == "format: dfa-policy@1")) then
    throw "missing format: dfa-policy@1 header"
  let mut policyName := "DefaultDfaPolicy"
  let mut initialState : Nat := 0
  let mut acceptingStates : List Nat := []
  let mut transitions : List DfaTransition := []
  let mut holes : List HoleConfinement := []
  for l in lines do
    if l == "format: dfa-policy@1" then pure ()
    else if l.startsWith "policy:" then
      policyName := trimStr (dropStr l 7)
    else if l.startsWith "initial:" then
      let some st := (trimStr (dropStr l 8)).toNat? | throw "invalid initial state in dfa-policy@1"
      initialState := st
    else if l.startsWith "accepting:" then
      let raw := trimStr (dropStr l 10)
      if !raw.isEmpty then
        acceptingStates ← (raw.splitOn ",").mapM fun s =>
          match (trimStr s).toNat? with
          | some n => pure n
          | none => throw "invalid accepting state in dfa-policy@1"
    else if l.startsWith "transition:" then
      let toks := ((trimStr (dropStr l 11)).splitOn " ").map trimStr |>.filter (fun t => !t.isEmpty)
      match toks with
      | [fStr, tokStr, toStr] =>
        let some f := fStr.toNat? | throw "invalid fromState"
        let some tok := tokStr.toNat? | throw "invalid tokenClass"
        let some toSt := toStr.toNat? | throw "invalid toState"
        transitions := transitions ++ [⟨f, tok, toSt⟩]
      | _ => throw s!"invalid transition line: {l}"
    else if l.startsWith "hole:" then
      let toks := ((trimStr (dropStr l 5)).splitOn " ").map trimStr |>.filter (fun t => !t.isEmpty)
      match toks with
      | [hName, kStr, stStr] =>
        let some k := kStr.toNat? | throw "invalid requiredKindTag"
        let some st := stStr.toNat? | throw "invalid allowedState"
        holes := holes ++ [⟨hName, k, st⟩]
      | _ => throw s!"invalid hole confinement line: {l}"
    else throw s!"unrecognized dfa-policy@1 line: {l}"
  return { policyName, initialState, acceptingStates, transitions, holes }

/-- Lower a `DfaPolicy` into an `.obend` `Syntax.Module` with state-transition methods and an
    unforgeable `#kind` confinement `law`. -/
def lowerDfaPolicyToObend (p : DfaPolicy) : Module :=
  let tokParam : Param := ⟨"token", "Nat", "default"⟩
  let advSig : Signature := ⟨"advance", [tokParam], "Nat"⟩
  let targetState : Nat :=
    match p.transitions.head? with
    | some tr => tr.toState
    | none => p.initialState
  let pinnedKind : Nat :=
    match p.holes.head? with
    | some h => h.requiredKindTag
    | none => 1
  let advMethod : Method := {
    name := "advance"
    params := [tokParam]
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "kindTag") (.nat (toString targetState)))
    signature := mkSigJson "advance" [tokParam] "Nat"
  }
  let confClaim : Claim := {
    name := "preservesKindTag"
    params := [tokParam]
    body := .binary "<=" (.member (.var "self") "kindTag")
                         (.call (.member (.var "self") "advance") [.var "token"])
    method := some (.judge "dfa-air")
  }
  let dfaSpec : Spec := {
    name := "ConfinementDfa"
    suffix := false
    parents := []
    targetType := "TranscriptAutomaton"
    requirements := .arr #[]
    methods := [advMethod]
    claims := [confClaim]
  }
  let seedRec : Expr := .record [
    ("dfaState", .nat (toString p.initialState)),
    ("kindTag", .nat (toString pinnedKind)),
    ("transitionsTaken", .nat "0"),
    ("advance", .closure [tokParam] "Nat" (.var "token"))
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.call (.member (.fix (.var "ConfinementDfa") seedRec) "advance") [.nat "1"]))
  let validStates : List Int :=
    ((p.initialState :: p.acceptingStates ++ p.transitions.map (·.toState)).eraseDups).map Int.ofNat
  let confLaw : LawExpr :=
    .and (.monotone "transitionsTaken")
      (.and (.inC (.field "dfaState") validStates)
        (.and (.writeOnce "kindTag") (.eqC (.field "kindTag") (Int.ofNat pinnedKind))))
  { name := "DfaPolicyModule"
    imports := []
    decls := [
      .record "TranscriptAutomaton" [
        ("dfaState", "Nat"), ("kindTag", "Nat"), ("transitionsTaken", "Nat")
      ] [advSig],
      .spec dfaSpec,
      entryFn
    ]
    laws := [("kindConfinement", confLaw)]
    header := none
    keeps := []
    lawMethods := [("kindConfinement", .judge "dfa-air")]
    contracts := [{
      name := "DfaConfinementContract"
      targetType := "TranscriptAutomaton"
      law := some confLaw
      method := some (.judge "dfa-air")
    }] }

/-- Concrete verified `FormatReader` instance for parser-automaton & `#kind` confinement policies (`"dfa-policy@1"`). -/
def dfaPolicyReader : FormatReader DfaPolicy where
  formatId := "dfa-policy@1"
  projectionKind := .lawContract
  parse := parseDfaPolicy
  render := renderDfaPolicy
  toCoreData := dfaPolicyToCoreData
  ofCoreData := dfaPolicyOfCoreData
  lowerToObend := lowerDfaPolicyToObend
  data_roundtrip := dfaPolicy_data_roundtrip

/-! ## 5. FormatReader 4: `deploymentTopologyReader` (`"dreggnet-deploy@1"`) — Elastic Cloud Deployment -/

/-- A compute grain in a `dreggnet-deploy@1` elastic cloud topology. -/
structure GrainSpec where
  grainName : String
  teeMeasurementPin : Nat
  mandateBudget : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A capability-authenticated SturdyRef channel between grains. -/
structure SturdyRefChannel where
  channelName : String
  sourceGrain : String
  targetGrain : String
  maxEpoch : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an elastic cloud deployment manifest (`"dreggnet-deploy@1"`). -/
structure DeploymentTopology where
  topologyName : String
  totalMandateCap : Nat
  requiredTeePin : Nat
  grains : List GrainSpec
  channels : List SturdyRefChannel
  deriving DecidableEq, Repr, Inhabited

def encodeGrainSpec (g : GrainSpec) : Data :=
  .record [
    ("grainName", .label g.grainName),
    ("teeMeasurementPin", .natural g.teeMeasurementPin),
    ("mandateBudget", .natural g.mandateBudget)
  ]

def decodeGrainSpec : Data → Option GrainSpec
  | .record [(_, .label n), (_, .natural pin), (_, .natural b)] => some ⟨n, pin, b⟩
  | _ => none

theorem decodeGrainSpec_encodeGrainSpec (g : GrainSpec) :
    decodeGrainSpec (encodeGrainSpec g) = some g := by
  cases g; rfl

def encodeSturdyRefChannel (c : SturdyRefChannel) : Data :=
  .record [
    ("channelName", .label c.channelName),
    ("sourceGrain", .label c.sourceGrain),
    ("targetGrain", .label c.targetGrain),
    ("maxEpoch", .natural c.maxEpoch)
  ]

def decodeSturdyRefChannel : Data → Option SturdyRefChannel
  | .record [(_, .label n), (_, .label src), (_, .label dst), (_, .natural ep)] => some ⟨n, src, dst, ep⟩
  | _ => none

theorem decodeSturdyRefChannel_encodeSturdyRefChannel (c : SturdyRefChannel) :
    decodeSturdyRefChannel (encodeSturdyRefChannel c) = some c := by
  cases c; rfl

def deploymentToCoreData (d : DeploymentTopology) : Data :=
  .record [
    ("topologyName", .label d.topologyName),
    ("totalMandateCap", .natural d.totalMandateCap),
    ("requiredTeePin", .natural d.requiredTeePin),
    ("grains", encodeListData encodeGrainSpec d.grains),
    ("channels", encodeListData encodeSturdyRefChannel d.channels)
  ]

def deploymentOfCoreData : Data → Option DeploymentTopology
  | .record [(_, .label tName), (_, .natural cap), (_, .natural pin), (_, grainsD), (_, chansD)] =>
      match decodeListData decodeGrainSpec grainsD,
            decodeListData decodeSturdyRefChannel chansD with
      | some gs, some cs => some ⟨tName, cap, pin, gs, cs⟩
      | _, _ => none
  | _ => none

theorem deploymentTopology_data_roundtrip (d : DeploymentTopology) :
    deploymentOfCoreData (deploymentToCoreData d) = some d := by
  cases d with
  | mk tName cap pin gs cs =>
    simp only [deploymentToCoreData, deploymentOfCoreData,
      decodeListData_encodeListData encodeGrainSpec decodeGrainSpec decodeGrainSpec_encodeGrainSpec gs,
      decodeListData_encodeListData encodeSturdyRefChannel decodeSturdyRefChannel decodeSturdyRefChannel_encodeSturdyRefChannel cs]

/-- Render a `DeploymentTopology` to `"dreggnet-deploy@1"` manifest text. -/
def renderDeploymentTopology (d : DeploymentTopology) : String :=
  let gLines := d.grains.map fun g => s!"grain: {g.grainName} {g.teeMeasurementPin} {g.mandateBudget}"
  let cLines := d.channels.map fun c => s!"channel: {c.channelName} {c.sourceGrain} {c.targetGrain} {c.maxEpoch}"
  String.intercalate "\n" ([
    "format: dreggnet-deploy@1",
    s!"topology: {d.topologyName}",
    s!"totalMandateCap: {d.totalMandateCap}",
    s!"requiredTeePin: {d.requiredTeePin}"
  ] ++ gLines ++ cLines)

/-- Parse a `"dreggnet-deploy@1"` manifest into `DeploymentTopology`. -/
def parseDeploymentTopology (input : String) : Except String DeploymentTopology := do
  let lines := (input.splitOn "\n").map trimStr |>.filter (fun l => !l.isEmpty)
  if !(lines.any (fun l => l == "format: dreggnet-deploy@1")) then
    throw "missing format: dreggnet-deploy@1 header"
  let mut topologyName := "DefaultTopology"
  let mut totalMandateCap : Nat := 1000
  let mut requiredTeePin : Nat := 42
  let mut grains : List GrainSpec := []
  let mut channels : List SturdyRefChannel := []
  for l in lines do
    if l == "format: dreggnet-deploy@1" then pure ()
    else if l.startsWith "topology:" then
      topologyName := trimStr (dropStr l 9)
    else if l.startsWith "totalMandateCap:" then
      let some v := (trimStr (dropStr l 16)).toNat? | throw "invalid totalMandateCap"
      totalMandateCap := v
    else if l.startsWith "requiredTeePin:" then
      let some v := (trimStr (dropStr l 15)).toNat? | throw "invalid requiredTeePin"
      requiredTeePin := v
    else if l.startsWith "grain:" then
      let toks := ((trimStr (dropStr l 6)).splitOn " ").map trimStr |>.filter (fun t => !t.isEmpty)
      match toks with
      | [gName, pinStr, budStr] =>
        let some pin := pinStr.toNat? | throw "invalid grain teeMeasurementPin"
        let some bud := budStr.toNat? | throw "invalid grain mandateBudget"
        grains := grains ++ [⟨gName, pin, bud⟩]
      | _ => throw s!"invalid grain line: {l}"
    else if l.startsWith "channel:" then
      let toks := ((trimStr (dropStr l 8)).splitOn " ").map trimStr |>.filter (fun t => !t.isEmpty)
      match toks with
      | [cName, src, dst, epStr] =>
        let some ep := epStr.toNat? | throw "invalid channel maxEpoch"
        channels := channels ++ [⟨cName, src, dst, ep⟩]
      | _ => throw s!"invalid channel line: {l}"
    else throw s!"unrecognized dreggnet-deploy@1 line: {l}"
  return { topologyName, totalMandateCap, requiredTeePin, grains, channels }

/-- Lower a `DeploymentTopology` into an `.obend` `Syntax.Module` of composed specs and laws
    enforcing grain mandate budgets, SturdyRef channel epochs, and TEE attestation pins. -/
def lowerDeploymentToObend (d : DeploymentTopology) : Module :=
  let dispSig : Signature := ⟨"dispatch", [], "Nat"⟩
  let baseDispatch : Method := {
    name := "dispatch"
    params := []
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "mandateDrawn") (.nat "1"))
    signature := mkSigJson "dispatch" [] "Nat"
  }
  let baseClaim : Claim := {
    name := "mandateMonotone"
    params := []
    body := .binary "<=" (.member (.var "self") "mandateDrawn")
                         (.member (.var "self") "dispatch")
    method := some .omega
  }
  let mandateSpec : Spec := {
    name := "GrainMandateSpec"
    suffix := false
    parents := []
    targetType := "DeploymentGrain"
    requirements := .arr #[]
    methods := [baseDispatch]
    claims := [baseClaim]
  }
  let overDispatch : Method := {
    name := "dispatch"
    params := []
    resultType := "Nat"
    qualifier := "around"
    body := .expr (.binary "+" (.member (.var "super") "dispatch") (.member (.var "self") "teePin"))
    signature := mkSigJson "dispatch" [] "Nat"
  }
  let teeSpec : Spec := {
    name := "TeeChannelSpec"
    suffix := false
    parents := ["GrainMandateSpec"]
    targetType := "DeploymentGrain"
    requirements := .arr #[]
    methods := [overDispatch]
    claims := []
  }
  let initBudget : Nat :=
    match d.grains.head? with
    | some g => g.mandateBudget
    | none => d.totalMandateCap
  let initEpoch : Nat :=
    match d.channels.head? with
    | some c => c.maxEpoch
    | none => 100
  let seedRec : Expr := .record [
    ("teePin", .nat (toString d.requiredTeePin)),
    ("mandateDrawn", .nat "0"),
    ("mandateBudget", .nat (toString initBudget)),
    ("channelEpoch", .nat (toString initEpoch)),
    ("dispatch", .nat "0")
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.member (.fix (.var "TeeChannelSpec") seedRec) "dispatch"))
  let deployLaw : LawExpr :=
    .and (.monotone "mandateDrawn")
      (.and (.leROff (.field "mandateDrawn") (.field "mandateBudget") 0)
        (.and (.writeOnce "mandateBudget")
          (.eqC (.field "teePin") (Int.ofNat d.requiredTeePin))))
  { name := "DeploymentTopologyModule"
    imports := []
    decls := [
      .record "DeploymentGrain" [
        ("teePin", "Nat"), ("mandateDrawn", "Nat"),
        ("mandateBudget", "Nat"), ("channelEpoch", "Nat")
      ] [dispSig],
      .spec mandateSpec,
      .spec teeSpec,
      entryFn
    ]
    laws := [("mandateAndTeePin", deployLaw)]
    header := none
    keeps := []
    lawMethods := [("mandateAndTeePin", .weave)]
    contracts := [{
      name := "DeploymentGrainContract"
      targetType := "DeploymentGrain"
      law := some deployLaw
      method := some .weave
    }] }

/-- Concrete verified `FormatReader` instance for elastic cloud deployment topologies (`"dreggnet-deploy@1"`). -/
def deploymentTopologyReader : FormatReader DeploymentTopology where
  formatId := "dreggnet-deploy@1"
  projectionKind := .deosAffordance
  parse := parseDeploymentTopology
  render := renderDeploymentTopology
  toCoreData := deploymentToCoreData
  ofCoreData := deploymentOfCoreData
  lowerToObend := lowerDeploymentToObend
  data_roundtrip := deploymentTopology_data_roundtrip

end Obend.Format

end
