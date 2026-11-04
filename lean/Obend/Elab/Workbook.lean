module

public import Lean
public meta import Lean
public import Obend.Core.Term
public meta import Obend.Core.Term
public import Obend.Core.Ty
public meta import Obend.Core.Ty
public import Obend.Spec.Law
public meta import Obend.Spec.Law
public import Obend.Spec.LawCompile
public meta import Obend.Spec.LawCompile
public import Obend.Spec.Parse
public meta import Obend.Spec.Parse
public import Obend.Spec.Syntax
public meta import Obend.Spec.Syntax
public import Obend.Spec.Elaborate
public meta import Obend.Spec.Elaborate
public import Obend.Spec.FrontEnd
public meta import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public meta import Obend.Spec.Capture
public import Obend.Logic.LateBinding
public meta import Obend.Logic.LateBinding
public import Obend.Logic.Claim
public meta import Obend.Logic.Claim
public import Obend.Logic.Rewrite
public meta import Obend.Logic.Rewrite
public import Obend.Logic.Frame
public meta import Obend.Logic.Frame
public import Obend.Logic.Obligation
public meta import Obend.Logic.Obligation
public import Obend.Logic.Program
public meta import Obend.Logic.Program
public import Obend.Leaf.Flatten
public meta import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public meta import Obend.Leaf.Emit
public import Obend.Lower.Syntax
public meta import Obend.Lower.Syntax
public import Obend.Lower.Transport
public meta import Obend.Lower.Transport
public import Obend.Lower.Proofs.Book
public meta import Obend.Lower.Proofs.Book
public import Obend.Lower.Reflect
public meta import Obend.Lower.Reflect
public import Obend.Elab.AutoCert
public meta import Obend.Elab.AutoCert
import all Obend.Judge.Class
import all Obend.Logic.Obligation

/-!
# Obend.Elab.Workbook — Bidirectional `.obend` <-> `.lean` Metasystem Bridge

Provides a first-class Lean 4 metasystem bridge allowing `.lean` files to elaborate,
inspect, and prove theorems directly over `.obend` files and inline `.obend` declarations
without manual de Bruijn transcription:

1. `elaborateObendSource` and `loadObendWorkbookFile`:
   Wraps `Obend.Spec.Capture.captureModule`, `Obend.Spec.Elaborate`, `Obend.Spec.FrontEnd.accept`,
   `Obend.Leaf.Flatten`, `Obend.Leaf.Emit`, `Obend.Lower.Reflect`, and `Obend.Elab.AutoCert`
   into a verified `WorkbookPackage`.
2. `obendWorkbookExt`, `#import_obend "path/to/File.obend" as Ns`, and `#obend_decl Ns "..."`:
   Elaborates `.obend` sources at Lean compile time, verifies `FrontEnd.accept`, registers the
   package in `obendWorkbookExt`, and emits concrete kernel-checked Lean constants inside namespace
   `Ns` (`Ns.package`, `Ns.laws_count`, `<def>_term`, `<def>_val`, `<def>_lexpr`,
   `<def>_lowerTerm_eq`, `<def>_comp`, `<def>_book`, `<def>_reflected`, and per-claim obligations
   with machine-checked proofs). This is the one `#import_obend`: `Obend.Stdlib`,
   `Obend.Hardware.UserspacePhysical` and every `Obend.Apps.*` module call it (2026-11-04).
3. `verifyWorkbookObligationsWithLean` (+ soundness theorems):
   Exports verified Lean `TransportCert`, `LawExpr`, and `Justification` certificates back into
   an `.obend` `WorkbookPackage`'s obligation checker.
-/

@[expose] public section

namespace Obend.Elab.Workbook

open Lean (Json toJson Name NameMap Expr Declaration Environment SimplePersistentEnvExtension
  registerSimplePersistentEnvExtension ToExpr toExpr toTypeExpr mkConst mkApp mkApp2 mkApp3
  mkApp4 mkApp5 mkApp7 mkApp9 mkApp10 Level addDecl addAndCompile MonadEnv getEnv modifyEnv)
open Lean.Elab.Command (CommandElabM liftCoreM)
open Obend.Core.Term (Primitive Term)
open Obend.Core.Ty (Quantity Reuse Ty)
open Obend.Spec.Law (LawRef LawExpr)
open Obend.Logic (Layer Composition RStep ClaimObj ClaimClause Support Justification)
open Obend.Leaf (DefKind LeafDef BookItem Book)
open Obend.Lower (NatOp LExpr TransportObj TransportCert)
open Obend.Lower.Reflect (LayoutEnv ReflectedObject lowerTerm reflectComposition)

set_option autoImplicit false

/-! ## 1. Workbook Data Structures -/

/-- Default empty layout environment for `lowerTerm` and `reflectComposition`. -/
def emptyLayoutEnv : LayoutEnv :=
  { fields := [], selfIndex := 0, arity := 0 }

/-- One elaborated definition in an `.obend` workbook package, with its Core4 term,
    optional weak-head reduced value, reflected `LExpr`, `Composition`, `Leaf.Book`,
    and `ReflectedObject`. -/
structure WorkbookDef where
  name : String
  fullKey : String
  knotTerm : Term
  term : Term
  reducedTerm? : Option Term
  lexpr? : Option LExpr
  composition? : Option Composition
  book? : Option Book
  reflectedObject? : Option ReflectedObject

/-- One elaborated specification claim in an `.obend` workbook package, together with
    its `ClaimObj` and any automatically synthesized rewrite justification. -/
structure WorkbookClaim where
  specKey : String
  name : String
  targetDef : String
  claimObj : ClaimObj
  autoSteps? : Option (List RStep)
  autoJustification? : Option Justification
  autoVerified : Bool

/-- A complete elaborated and gate-accepted `.obend` workbook package. -/
structure WorkbookPackage where
  moduleName : String
  entryDef : String
  source : String
  sha256 : String
  accepted : Bool
  erasedTerm : Term
  rootTerm : Term
  defs : List WorkbookDef
  claims : List WorkbookClaim
  laws : List (String × LawExpr)
  /-- Laws declared syntactically in the entry module (emitted as `Ns.laws_count`). -/
  lawsCount : Nat

instance : Inhabited WorkbookPackage where
  default := {
    moduleName := "Main"
    entryDef := ""
    source := ""
    sha256 := ""
    accepted := false
    erasedTerm := .record []
    rootTerm := .record []
    defs := []
    claims := []
    laws := []
    lawsCount := 0
  }

namespace WorkbookPackage

def findDef? (pkg : WorkbookPackage) (name : String) : Option WorkbookDef :=
  pkg.defs.find? (fun d => d.name == name || d.fullKey == name)

def findTerm? (pkg : WorkbookPackage) (name : String) : Option Term :=
  (pkg.findDef? name).map (·.term)

def findLExpr? (pkg : WorkbookPackage) (name : String) : Option LExpr :=
  (pkg.findDef? name).bind (·.lexpr?)

def findComposition? (pkg : WorkbookPackage) (name : String) : Option Composition :=
  (pkg.findDef? name).bind (·.composition?)

def findBook? (pkg : WorkbookPackage) (name : String) : Option Book :=
  (pkg.findDef? name).bind (·.book?)

def findReflected? (pkg : WorkbookPackage) (name : String) : Option ReflectedObject :=
  (pkg.findDef? name).bind (·.reflectedObject?)

def findClaim? (pkg : WorkbookPackage) (name : String) : Option WorkbookClaim :=
  pkg.claims.find? (fun c => c.name == name || (c.specKey ++ "." ++ c.name) == name)

end WorkbookPackage

/-! ## 2. Knot Resolution & `.obend` Elaboration Pipeline -/

/-- Default preview/checker limits for workbook elaboration. -/
def defaultWorkbookLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

/-- Ensure `.obend` source begins with `edition ObjectiveBend 1` when omitted in inline snippets. -/
def normalizeObendSource (src : String) : String :=
  let trimmed := src.trimAscii.toString
  if trimmed.startsWith "edition ObjectiveBend 1" then
    src
  else
    "edition ObjectiveBend 1\n" ++ src

/-- Inline non-recursive `$globals` knot lookups `.get root key` so that standalone and helper-calling
    definitions become `.fix`-free and reflect cleanly via `Obend.Lower.Reflect.lowerTerm`. -/
def resolveKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then
        .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveKnotTerm root rawFields visiting fuel f) (resolveKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveKnotTerm root rawFields visiting fuel l) (resolveKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveKnotTerm root rawFields visiting fuel s) (resolveKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveKnotTerm root rawFields visiting fuel m) (resolveKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveKnotTerm root rawFields visiting fuel s) (resolveKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveKnotTerm root rawFields visiting fuel l) (resolveKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveKnotTerm root rawFields visiting fuel v)
      (resolveKnotTerm root rawFields visiting fuel z)
      (resolveKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveKnotTerm root rawFields visiting fuel c)
      (resolveKnotTerm root rawFields visiting fuel x)
      (resolveKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveKnotTerm root rawFields visiting fuel t) names
      (resolveKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t

/-- Select the default entry declaration from a decoded `Syntax.Module`. -/
def selectCallableDecls (m : Obend.Spec.Syntax.Module) : List Obend.Spec.Syntax.Decl :=
  m.decls.filter fun d =>
    match d with
    | .function .. | .extension .. | .spec .. => true
    | _ => false


/-- Strip layer metadata and `#kind` fields so the emitted `Composition` reduces in the kernel
(`decide +kernel` over `_comp`/`_book` constants). The flattened behaviour is unchanged. -/
def compactLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

def compactCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := compactLayerForKernel C.top
    below := C.below.map compactLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

/-- Format a `FrontEnd.Diagnostic` into a readable error string. -/
def formatDiagnostic (d : Obend.Spec.FrontEnd.Diagnostic) : String :=
  s!"{d.stage}: {d.message}"

/-- Decode a `.fix S seedTerm` composition when `S` decodes to named spec layers and `seedTerm`
    is (or reduces to) a record. -/
def decodeWorkbookWithSeed (want : Composition → Bool) : Term → Option Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none

/-- Step `t` one weak-head step at a time, intercepting `.fix S seedTerm` before `Obend.Law.step?`
    unfolds the fixpoint so multi-layer prototype compositions decode with all layers intact. -/
def findWorkbookObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeWorkbookWithSeed want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findWorkbookObject want fuel)

/-- Locate a `self.m` field access `.get (.bound selfIdx) m` inside an expression context
    (outside binders), returning `(ctxWithHoleAt0, m)` such that
    `Obend.Logic.instantiate ctxWithHoleAt0 (.get (.bound selfIdx) m) = t`. -/
def findSelfGetCtx (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match findSelfGetCtx selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (findSelfGetCtx selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match findSelfGetCtx selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (findSelfGetCtx selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

/-- Propose a rewrite derivation for a workbook claim, extending `Obend.Logic.Program.derive`
    to unfold `self.m` calls inside binary/application contexts (such as `50 + 8 * self.thermalResistance()`). -/
def deriveWorkbook (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => deriveWorkbook o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match findSelfGetCtx o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => deriveWorkbook o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

/-- Propose a rewrite derivation for a `ClaimObj`. -/
def proposeWorkbookDerivation (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => deriveWorkbook o r 4096 l []
    | none => none

/-- Sanitize a file stem into a valid Objective Bend module identifier. -/
def sanitizeModuleName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

/-- Strip optional surrounding double quotes from an import path string. -/
def stripImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

/-- Parse and check one `.obend` module source against already-loaded `prior` modules. -/
def parseAndCheckObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let normSrc := normalizeObendSource src
  let sha256 := Obend.Spec.Sha256.hex normSrc.toUTF8
  let ast ← match Obend.Spec.FrontEnd.parseSource moduleName normSrc with
    | .ok a => pure a
    | .error d => throw (formatDiagnostic d)
  let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let mut lockedImports : List Obend.Spec.FrontEnd.LockedImport := []
  for edge in parsedEdges.toList do
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgeSpan := (edge.getObjVal? "span").toOption.getD .null
    let cleanPath := stripImportQuotes edgePath
    let stemMod := sanitizeModuleName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
    let found? := prior.zipIdx.find? fun ((sm, _), _) =>
      sm.name == stemMod || (edgeAlias != "" && sm.name == edgeAlias)
    let some ((targetSm, _), targetIdx) := found?
      | throw s!"module {moduleName}: imported module for '{edgePath}' (alias '{edgeAlias}') not found in loaded closure"
    lockedImports := lockedImports ++ [{
      path := edgePath
      importAlias := edgeAlias
      span := edgeSpan
      target := targetIdx
      moduleName := targetSm.name
      sha256 := targetSm.sha256
    }]
  let srcMod : Obend.Spec.FrontEnd.SourceModule := {
    name := moduleName
    source := normSrc
    sha256 := sha256
    imports := lockedImports
  }
  let decodedMod ← match Obend.Spec.FrontEnd.checkParsed srcMod ast with
    | .ok m => pure m
    | .error d => throw (formatDiagnostic d)
  return (srcMod, decodedMod)

/-- Elaborate an `.obend` source string through `FrontEnd.parseSource`, `FrontEnd.checkParsed`,
    `Elaborate.elaborate` (`FrontEnd.lowerDecoded`), `FrontEnd.accept`, `Leaf.Flatten`/`Leaf.Emit`,
    and `Lower.Reflect`. Supports multi-module closures via `prior`. -/
def elaborateObendSource (src : String) (moduleName : String := "Main")
    (entryDef? : Option String := none)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := []) :
    Except String WorkbookPackage := do
  let (srcMod, decodedMod) ← parseAndCheckObendModule src moduleName prior
  let normSrc := srcMod.source
  let sha256 := srcMod.sha256
  let callables := selectCallableDecls decodedMod
  let entryDef ← match entryDef? with
    | some e => pure e
    | none =>
      match callables.getLast? with
      | some d => pure d.name
      | none => throw s!"module {moduleName} contains no callable function, extension, or spec"
  let allSrcMods := prior.map Prod.fst ++ [srcMod]
  let allDecodedMods := prior.map Prod.snd ++ [decodedMod]
  let entryIdx := prior.length
  let allLaws := (allDecodedMods.map (·.laws)).flatten
  let decodedForLower := allDecodedMods.zipIdx.map fun (dm, idx) =>
    if idx == entryIdx then { dm with laws := allLaws } else { dm with laws := [] }
  let lowering ← match Obend.Spec.FrontEnd.lowerDecoded allSrcMods decodedForLower entryIdx entryDef
      (Json.arr #[]) (Json.arr #[]) defaultWorkbookLimits "definition" [] with
    | .ok l => pure l
    | .error d => throw (formatDiagnostic d)
  let acc ← match Obend.Spec.FrontEnd.accept lowering with
    | .ok a => pure a
    | .error d => throw (formatDiagnostic d)
  for c in decodedMod.contracts do
    if !c.steps.isEmpty then
      match Obend.Spec.FrontEnd.checkContractIsarCert Obend.Spec.FrontEnd.defaultAutoCertAdmitsTag decodedMod c with
      | .ok _ => pure ()
      | .error d => throw (formatDiagnostic d)
    else if !Obend.Elab.AutoCert.verifyContractAutoCertSteps Obend.Elab.AutoCert.autoCertFormats moduleName none c then
      throw s!"elaborate: refused (autocert-synthesis): contract {c.name} failed automatic certificate synthesis"
  let erasedTerm := acc.erased
  let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
  let rawFields := Obend.Logic.Program.knotFields rootTerm
  let mut wdefs : List WorkbookDef := []
  for d in callables do
    let shortName := d.name
    let fullKey := moduleName ++ "." ++ shortName
    let knotTerm : Term := .get rootTerm fullKey
    let opened := match rawFields.lookup fullKey with
      | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
      | none => knotTerm
    let inlined := resolveKnotTerm rootTerm rawFields [fullKey] 16 opened
    let reducedTerm? := Obend.Law.run 50000 knotTerm
    let wantNamed : Composition → Bool := fun C => C.top.name != ""
    let foundComp? :=
      match findWorkbookObject wantNamed 64 knotTerm with
      | some c => some c
      | none =>
        match findWorkbookObject wantNamed 64 (.app knotTerm (.record [])) with
        | some c => some c
        | none => decodeWorkbookWithSeed wantNamed inlined
    let composition? : Option Composition :=
      match foundComp?.map compactCompositionForKernel with
      | some c => some c
      | none =>
        match d with
        | .function .. =>
          let lc := Obend.Lower.leanComposition shortName inlined
          if lc.closedB then some lc else none
        | _ => none
    let book? : Option Book := composition?.map Obend.Leaf.emit
    let reflectedObject? : Option ReflectedObject :=
      composition?.bind fun c => reflectComposition shortName c emptyLayoutEnv
    let lexpr? : Option LExpr :=
      match lowerTerm emptyLayoutEnv inlined with
      | some e => some e
      | none => reducedTerm?.bind (lowerTerm emptyLayoutEnv)
    wdefs := wdefs ++ [{
      name := shortName
      fullKey := fullKey
      knotTerm := knotTerm
      term := inlined
      reducedTerm? := reducedTerm?
      lexpr? := lexpr?
      composition? := composition?
      book? := book?
      reflectedObject? := reflectedObject?
    }]
  let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
  let mut wclaims : List WorkbookClaim := []
  for (specKey, claimName) in rawClaimPairs do
    let matchingDefs := wdefs.filter fun wd =>
      match wd.composition? with
      | some comp => (Obend.Logic.Program.layerIndex comp specKey).isSome
      | none => false
    let chosenDef? :=
      match matchingDefs.find? (fun wd => wd.composition?.any (fun c => c.top.name == specKey)) with
      | some wd => some wd
      | none => matchingDefs.head?
    if let some wd := chosenDef? then
      if let some comp := wd.composition? then
        if let .ok co := Obend.Logic.Program.claimObj rootTerm comp specKey claimName then
          let steps? := proposeWorkbookDerivation co
          let derivJust? := steps?.map Justification.byDerivation
          let derivOk := match derivJust? with
            | some j => Obend.Logic.obligationCheck 4096 co j == Obend.Judge.Verdict.ok
            | none => false
          let claimDecl? : Option Obend.Spec.Syntax.Claim :=
            allDecodedMods.findSome? fun dm =>
              dm.decls.findSome? fun d =>
                match d with
                | .spec s =>
                  if s.name == specKey || (dm.name ++ "." ++ s.name) == specKey then
                    s.claims.find? (·.name == claimName)
                  else none
                | _ => none
          let (just?, ok) :=
            if derivOk then
              (derivJust?, true)
            else
              match Obend.Elab.AutoCert.synthesizeClaimExternalJudge
                  Obend.Elab.AutoCert.autoCertFormats 4096 moduleName claimName claimDecl? wd.book? co with
              | some extJ =>
                (some extJ,
                 Obend.Logic.obligationCheckWithJudges Obend.Elab.AutoCert.autoCertFormats 4096 co extJ ==
                   Obend.Judge.Verdict.ok)
              | none =>
                (derivJust?, false)
          wclaims := wclaims ++ [{
            specKey := specKey
            name := claimName
            targetDef := wd.name
            claimObj := co
            autoSteps? := steps?
            autoJustification? := just?
            autoVerified := ok
          }]
  return {
    moduleName := moduleName
    entryDef := entryDef
    source := normSrc
    sha256 := sha256
    accepted := true
    erasedTerm := erasedTerm
    rootTerm := rootTerm
    defs := wdefs
    claims := wclaims
    laws := lowering.laws
    lawsCount := decodedMod.laws.length
  }

/-- Resolve a workbook `.obend` file path whether invoked from the repo root or `lean/`. -/
def resolveObendPath (path : System.FilePath) : IO System.FilePath := do
  if ← path.pathExists then
    return path
  let s := path.toString
  if s.startsWith "lean/" then
    let stripped := System.FilePath.mk (s.drop 5).toString
    if ← stripped.pathExists then
      return stripped
  let prefixed := System.FilePath.mk ("lean/" ++ s)
  if ← prefixed.pathExists then
    return prefixed
  let parentRel := System.FilePath.mk ("../" ++ s)
  if ← parentRel.pathExists then
    return parentRel
  return path

/-- Resolve an imported `.obend` path relative to the importing file `parentFile` or `stdlib/` directories. -/
def resolveImportedObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := stripImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← resolveObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← resolveObendPath rel2
  if ← r2.pathExists then return r2
  let r3 ← resolveObendPath (System.FilePath.mk stripped)
  if ← r3.pathExists then return r3
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["stdlib/core/", "stdlib/ledger/", "stdlib/usd/", "stdlib/physical/", "apps/obend-risc/", "apps/zk-ntt/", "apps/foc-hil/", "apps/sdr-ft8/", "apps/fidget-cam/", "apps/quantum-photonic-matter/", "apps/sovereign-drex/", "apps/silicon-kernel-verilator/"] do
    let cand ← resolveObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

/-- Recursively load an `.obend` file and all of its transitive `import`s in topological order. -/
def loadObendModuleClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolveObendPath path
    let modName := sanitizeModuleName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let normSrc := normalizeObendSource rawSrc
      let ast ← match Obend.Spec.FrontEnd.parseSource modName normSrc with
        | .ok a => pure a
        | .error d => return .error (formatDiagnostic d)
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← resolveImportedObendPath resolved edgePath
        match ← loadObendModuleClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckObendModule normSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

/-- Load an `.obend` file from disk (recursively resolving any `import` declarations)
    and elaborate it into a `WorkbookPackage`. -/
def loadObendWorkbookFile (path : System.FilePath) : IO (Except String WorkbookPackage) := do
  match ← loadObendModuleClosure 32 path [] with
  | .error err => return .error err
  | .ok closure =>
    match closure.getLast? with
    | none => return .error s!"empty module closure for {path}"
    | some (lastSrc, _) =>
      return elaborateObendSource lastSrc.source lastSrc.name none closure.dropLast

/-! ## 3. Reverse Bridge: Exporting Lean `TransportCert` / `LawExpr` into `.obend` Obligations -/

/-- Fast structural digest on `LExpr` so `transport@1` certificates can be checked in the Lean kernel
    without evaluating `Obend.Core.Digest.deployed` (Keccak-f[1600]). -/
def workbookSourceDigest : LExpr → Nat
  | .bvar i => i + 1
  | .erased => 2
  | .lit n => n * 3 + 3
  | .boolLit b => if b then 7 else 5
  | .natSucc a => workbookSourceDigest a * 13 + 11
  | .natBin op l r => (NatOp.ctorIdx op + 1) * 17 + workbookSourceDigest l * 31 + workbookSourceDigest r
  | .lam _ b => workbookSourceDigest b * 37 + 19
  | .app f a => workbookSourceDigest f * 41 + workbookSourceDigest a * 43 + 23
  | .letE _ v b => workbookSourceDigest v * 47 + workbookSourceDigest b * 53 + 29
  | .boolRec _ wf wt m => workbookSourceDigest wf * 59 + workbookSourceDigest wt * 61 + workbookSourceDigest m * 67
  | _ => 97

/-- Kernel-reducible `transport@1` checker using `workbookSourceDigest`. -/
def workbookTransportCheck (_ : Nat) (o : TransportObj) (c : TransportCert) :
    Obend.Judge.Verdict Obend.Lower.TransportClause :=
  if c.digest != workbookSourceDigest o.decideExpr then .refused .otherSource []
  else if !Obend.Law.termEq (Obend.Lower.lowerProp o.decideExpr) c.claim then .refused .notTheLowering []
  else if c.argTys != o.argTys then .refused .wrongArgTys []
  else if !Obend.Lower.nonEmptySplits o.decideExpr then .refused .emptySplit []
  else if !Obend.Lower.checkL [] o.decideExpr (Obend.Lower.curry o.argTys .boolean) then .refused .illTyped []
  else .ok

/-- Semantic meaning established by `workbookTransportCheck` (via Tait–Girard `transport_ltyped_holds`). -/
def WorkbookTransportMeaning (o : TransportObj) (c : TransportCert) : Prop :=
  c.digest = workbookSourceDigest o.decideExpr ∧
  c.claim = Obend.Lower.lowerProp o.decideExpr ∧
  c.argTys = o.argTys ∧
  Obend.Lower.LTyped [] o.decideExpr (Obend.Lower.curry o.argTys .boolean) ∧
  Obend.Lower.nonEmptySplits o.decideExpr = true ∧
  ∀ (th : Obend.Lower.SourceTheory) (ds : List Obend.Core.Data.Data),
    Obend.Lower.Consistent th →
    ds.length = o.argTys.length →
    (∀ d ∈ ds, Obend.Lower.DataInFragment d = true) →
    (∀ p ∈ (ds.map Obend.Lower.dataLExpr).zip o.argTys, Obend.Lower.Red p.2 p.1) →
    th.Provable (Obend.Lower.lapps o.decideExpr (ds.map Obend.Lower.dataLExpr)) →
    Obend.Logic.Holds c.claim ds

theorem workbookTransportCheck_ok {r : Nat} {o : TransportObj} {c : TransportCert}
    (h : workbookTransportCheck r o c = .ok) :
    c.digest = workbookSourceDigest o.decideExpr ∧
    c.claim = Obend.Lower.lowerProp o.decideExpr ∧
    c.argTys = o.argTys ∧
    Obend.Lower.nonEmptySplits o.decideExpr = true ∧
    Obend.Lower.checkL [] o.decideExpr (Obend.Lower.curry o.argTys .boolean) = true := by
  unfold workbookTransportCheck at h
  split at h
  · cases h
  · rename_i hd
    split at h
    · cases h
    · rename_i ht
      split at h
      · cases h
      · rename_i ha
        split at h
        · cases h
        · rename_i hs
          split at h
          · cases h
          · rename_i hc
            simp only [bne_iff_ne, ne_eq, Decidable.not_not, Bool.not_eq_true'] at hd ht ha hs hc
            have hteq : Obend.Law.termEq (Obend.Lower.lowerProp o.decideExpr) c.claim = true := by
              cases e : Obend.Law.termEq (Obend.Lower.lowerProp o.decideExpr) c.claim
              · rw [e] at ht; exact absurd rfl ht
              · rfl
            have hsplit : Obend.Lower.nonEmptySplits o.decideExpr = true := by
              cases e : Obend.Lower.nonEmptySplits o.decideExpr
              · rw [e] at hs; exact absurd rfl hs
              · rfl
            have hcheck : Obend.Lower.checkL [] o.decideExpr (Obend.Lower.curry o.argTys .boolean) = true := by
              cases e : Obend.Lower.checkL [] o.decideExpr (Obend.Lower.curry o.argTys .boolean)
              · rw [e] at hc; exact absurd rfl hc
              · rfl
            exact ⟨hd, (Obend.Law.termEq_sound hteq).symm, ha, hsplit, hcheck⟩

instance workbookTransportJudge : Obend.Judge TransportObj TransportCert where
  Clause := Obend.Lower.TransportClause
  Meaning := WorkbookTransportMeaning
  check := workbookTransportCheck
  sound := by
    intro r o c h
    obtain ⟨hd, ht, ha, hs, hc⟩ := workbookTransportCheck_ok h
    have htyped := Obend.Lower.checkL_sound hc
    refine ⟨hd, ht, ha, htyped, hs, ?_⟩
    intro th ds hcons hlen hfrag hred hprov
    rw [ht]
    exact Obend.Lower.transport_ltyped_holds th htyped hs hlen hfrag hred hcons hprov
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o :=
    Obend.Lower.nonEmptySplits o.decideExpr = true ∧
    Obend.Lower.checkL [] o.decideExpr (Obend.Lower.curry o.argTys .boolean) = true
  complete := by
    intro o ⟨hs, hc⟩ _
    refine ⟨⟨workbookSourceDigest o.decideExpr, Obend.Lower.lowerProp o.decideExpr, o.argTys, []⟩, 0, ?_⟩
    simp [workbookTransportCheck, hs, hc]
  mono := by intros; rfl

def reflNatDecideExpr : LExpr :=
  .lam .natural (.natBin .beq (.bvar 0) (.bvar 0))

def reflNatTransportObj : TransportObj :=
  { decideExpr := reflNatDecideExpr, argTys := [.natural] }

def reflNatTransportCert : TransportCert :=
  { digest := workbookSourceDigest reflNatDecideExpr
    claim := Obend.Lower.lowerProp reflNatDecideExpr
    argTys := [.natural]
    supports := [] }

theorem badWorkbookTransport_refused :
    workbookTransportCheck 0 Obend.Lower.badTransportObj Obend.Lower.badTransportCert =
      .refused .otherSource [] := rfl

def decodeWorkbookTransportObj (s : String) : Except String TransportObj :=
  match s with
  | "reflNat" => .ok reflNatTransportObj
  | "bad" => .ok Obend.Lower.badTransportObj
  | _ => Obend.Lower.transportObjOf s

def decodeWorkbookTransportCert (s : String) : Except String TransportCert :=
  match s with
  | "reflNat" => .ok reflNatTransportCert
  | "bad" => .ok Obend.Lower.badTransportCert
  | _ => Obend.Lower.transportCertOf s

def encodeWorkbookTransportObj (o : TransportObj) : String :=
  if workbookSourceDigest o.decideExpr == workbookSourceDigest reflNatDecideExpr && o.argTys == [.natural] then
    "reflNat"
  else
    (Obend.Lower.transportObjJson o).compress

def encodeWorkbookTransportCert (c : TransportCert) : String :=
  if c.digest == workbookSourceDigest reflNatDecideExpr && c.argTys == [.natural] then
    "reflNat"
  else
    (Obend.Lower.transportCertJson c).compress

/-- Kernel-reducible `transport@1` format registered in `workbookFormats`. -/
def workbookTransportFormat : Obend.Judge.Format where
  name := "transport"
  version := "1"
  Obj := TransportObj
  Cert := TransportCert
  judge := workbookTransportJudge
  decodeObj := decodeWorkbookTransportObj
  decodeCert := decodeWorkbookTransportCert
  trust := .kernel
  regime := .decidable
  bad := (Obend.Lower.badTransportObj, Obend.Lower.badTransportCert)
  badGrade := 0
  bad_refused := ⟨.otherSource, [], badWorkbookTransport_refused⟩

/-- Registered judge formats for workbook obligation verification (`transport@1`, `rewrite@1`,
    `lrat@1`, `clearing@1`, `interval@1`, `taylor-model@1`, `sos-lyapunov-cbf@1`, `groebner@1`,
    `rtl-synth@1`, `hw-rtl-synth@1`). -/
def workbookFormats : List Obend.Judge.Format :=
  workbookTransportFormat :: Obend.Elab.AutoCert.autoCertFormats

/-- Convert a Lean `TransportCert` into an `.obend` `.byLoweredLean` obligation justification. -/
def justificationOfTransportCert (cert : TransportCert) (receipt : ByteArray := ByteArray.empty) :
    Justification :=
  .byLoweredLean cert.claim cert.supports receipt

/-- Convert a Lean `(TransportObj, TransportCert)` pair into an external `transport@1` justification. -/
def externalTransportJustification (obj : TransportObj) (cert : TransportCert) : Justification :=
  .byExternalJudge "transport@1"
    (Obend.Logic.mkExternalJudgePayload
      (encodeWorkbookTransportObj obj)
      (encodeWorkbookTransportCert cert))

/-- Verify an `.obend` `ClaimObj` using a Lean `TransportCert` via `.byLoweredLean`. -/
def verifyClaimWithTransport (k : Nat) (claim : ClaimObj) (cert : TransportCert)
    (receipt : ByteArray := ByteArray.empty) : Obend.Judge.Verdict ClaimClause :=
  Obend.Logic.obligationCheckWithJudges workbookFormats k claim
    (justificationOfTransportCert cert receipt)

/-- **Soundness of `verifyClaimWithTransport`**: acceptance establishes
    `obligationMeaningWithJudges workbookFormats`. -/
theorem verifyClaimWithTransport_sound {k : Nat} {claim : ClaimObj} {cert : TransportCert}
    {receipt : ByteArray} (h : verifyClaimWithTransport k claim cert receipt = .ok) :
    Obend.Logic.obligationMeaningWithJudges workbookFormats claim
      (justificationOfTransportCert cert receipt) :=
  Obend.Logic.obligationWithJudges_sound workbookFormats h

/-- Verify an `.obend` `ClaimObj` using an external `transport@1` certificate payload. -/
def verifyClaimWithExternalTransport (k : Nat) (claim : ClaimObj) (obj : TransportObj)
    (cert : TransportCert) : Obend.Judge.Verdict ClaimClause :=
  Obend.Logic.obligationCheckWithJudges workbookFormats k claim
    (externalTransportJustification obj cert)

/-- **Soundness of `verifyClaimWithExternalTransport`**: acceptance establishes
    `obligationMeaningWithJudges workbookFormats`. -/
theorem verifyClaimWithExternalTransport_sound {k : Nat} {claim : ClaimObj}
    {obj : TransportObj} {cert : TransportCert}
    (h : verifyClaimWithExternalTransport k claim obj cert = .ok) :
    Obend.Logic.obligationMeaningWithJudges workbookFormats claim
      (externalTransportJustification obj cert) :=
  Obend.Logic.obligationWithJudges_sound workbookFormats h

/-- Select the justification for a `WorkbookClaim` from provided Lean justifications,
    Lean `TransportCert`s, or the package's auto-synthesized rewrite derivation. -/
def selectClaimJustification (wc : WorkbookClaim)
    (leanJustifications : List (String × Justification))
    (leanTransportCerts : List (String × TransportCert)) : Option Justification :=
  let key := wc.specKey ++ "." ++ wc.name
  match leanJustifications.lookup wc.name <|> leanJustifications.lookup key with
  | some j => some j
  | none =>
    match leanTransportCerts.lookup wc.name <|> leanTransportCerts.lookup key with
    | some cert => some (justificationOfTransportCert cert)
    | none => wc.autoJustification?

/-- Check all claims and exported `LawExpr` invariants in a `WorkbookPackage` using Lean
    justifications, `TransportCert`s, and `LawCompile`. -/
def verifyWorkbookObligationsWithLean (pkg : WorkbookPackage)
    (leanJustifications : List (String × Justification) := [])
    (leanTransportCerts : List (String × TransportCert) := [])
    (leanLaws : List (String × LawExpr) := [])
    (grade : Nat := 4096) : Bool :=
  let claimsOk := pkg.claims.all fun wc =>
    match selectClaimJustification wc leanJustifications leanTransportCerts with
    | some j => Obend.Logic.obligationCheckWithJudges workbookFormats grade wc.claimObj j == .ok
    | none => false
  let lawsOk := (pkg.laws ++ leanLaws).all fun (lawName, lawExpr) =>
    Obend.Law.closedB (Obend.Spec.LawCompile.compile .emptyRow pkg.moduleName lawName lawExpr)
  pkg.accepted && claimsOk && lawsOk

/-- **Soundness of `verifyWorkbookObligationsWithLean`**: if `verifyWorkbookObligationsWithLean`
    returns `true`, then every claim `wc ∈ pkg.claims` has a selected `Justification` `j` whose
    semantic meaning `obligationMeaningWithJudges workbookFormats wc.claimObj j` holds. -/
theorem verifyWorkbookObligationsWithLean_sound
    {pkg : WorkbookPackage}
    {leanJustifications : List (String × Justification)}
    {leanTransportCerts : List (String × TransportCert)}
    {leanLaws : List (String × LawExpr)}
    {grade : Nat}
    (h : verifyWorkbookObligationsWithLean pkg leanJustifications leanTransportCerts leanLaws grade = true)
    {wc : WorkbookClaim} (hwc : wc ∈ pkg.claims) :
    ∃ j, selectClaimJustification wc leanJustifications leanTransportCerts = some j ∧
      Obend.Logic.obligationMeaningWithJudges workbookFormats wc.claimObj j := by
  unfold verifyWorkbookObligationsWithLean at h
  simp only [Bool.and_eq_true] at h
  have hclaims : (pkg.claims.all fun wc =>
      match selectClaimJustification wc leanJustifications leanTransportCerts with
      | some j => Obend.Logic.obligationCheckWithJudges workbookFormats grade wc.claimObj j == .ok
      | none => false) = true := h.1.2
  have hwcOk := List.all_eq_true.1 hclaims wc hwc
  cases hj : selectClaimJustification wc leanJustifications leanTransportCerts with
  | none => rw [hj] at hwcOk; cases hwcOk
  | some j =>
    rw [hj] at hwcOk
    have hcheck : Obend.Logic.obligationCheckWithJudges workbookFormats grade wc.claimObj j = .ok :=
      beq_iff_eq.1 hwcOk
    exact ⟨j, rfl, Obend.Logic.obligationWithJudges_sound workbookFormats hcheck⟩

/-! ## 4. Persistent Environment Extension `obendWorkbookExt` -/

/-- Persistent environment extension storing elaborated `WorkbookPackage`s by namespace `Name`. -/
meta initialize obendWorkbookExt :
    SimplePersistentEnvExtension (Name × WorkbookPackage) (NameMap WorkbookPackage) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun acc arr =>
        arr.foldl (init := acc) fun m (k, v) => m.insert k v
    addEntryFn := fun m (k, v) => m.insert k v
  }

/-- Look up a registered `WorkbookPackage` in the current Lean environment. -/
meta def getRegisteredWorkbook? (env : Environment) (ns : Name) : Option WorkbookPackage :=
  (obendWorkbookExt.getState env).find? ns

/-! ## 5. `ToExpr` Instances for Kernel Constant Materialization -/

/-- Helper constructor for `ReflectedObject` used by `ToExpr ReflectedObject` so the proof field
    `pins_eq` is discharged definitionally by `rfl`. -/
def mkReflectedObject (name : String) (C : Composition) (defs : List (String × LExpr)) :
    ReflectedObject :=
  { name := name
    composition := C
    defs := defs
    pins := (Obend.Leaf.Candidate.book name C).supports
    pins_eq := rfl }

/-- Helper constructor for `ByteArray` used by `ToExpr ByteArray`. -/
def mkByteArrayOfList (bs : List UInt8) : ByteArray :=
  ByteArray.mk bs.toArray

def toExprPrimitive : Primitive → Expr
  | .add => mkConst ``Primitive.add
  | .multiply => mkConst ``Primitive.multiply
  | .equal => mkConst ``Primitive.equal
  | .conjunction => mkConst ``Primitive.conjunction
  | .labelEqual => mkConst ``Primitive.labelEqual
  | .subtract => mkConst ``Primitive.subtract
  | .divide => mkConst ``Primitive.divide
  | .less => mkConst ``Primitive.less
  | .lessEqual => mkConst ``Primitive.lessEqual
  | .modulo => mkConst ``Primitive.modulo
  | .bitAnd => mkConst ``Primitive.bitAnd
  | .bitOr => mkConst ``Primitive.bitOr
  | .bitXor => mkConst ``Primitive.bitXor
  | .shl => mkConst ``Primitive.shl
  | .lshr => mkConst ``Primitive.lshr
  | .ashr => mkConst ``Primitive.ashr
  | .slt => mkConst ``Primitive.slt
  | .qmul32 => mkConst ``Primitive.qmul32

meta def metaToExprPrimitive : Primitive → Expr
  | .add => mkConst ``Primitive.add
  | .multiply => mkConst ``Primitive.multiply
  | .equal => mkConst ``Primitive.equal
  | .conjunction => mkConst ``Primitive.conjunction
  | .labelEqual => mkConst ``Primitive.labelEqual
  | .subtract => mkConst ``Primitive.subtract
  | .divide => mkConst ``Primitive.divide
  | .less => mkConst ``Primitive.less
  | .lessEqual => mkConst ``Primitive.lessEqual
  | .modulo => mkConst ``Primitive.modulo
  | .bitAnd => mkConst ``Primitive.bitAnd
  | .bitOr => mkConst ``Primitive.bitOr
  | .bitXor => mkConst ``Primitive.bitXor
  | .shl => mkConst ``Primitive.shl
  | .lshr => mkConst ``Primitive.lshr
  | .ashr => mkConst ``Primitive.ashr
  | .slt => mkConst ``Primitive.slt
  | .qmul32 => mkConst ``Primitive.qmul32

meta instance : ToExpr Primitive where
  toExpr := metaToExprPrimitive
  toTypeExpr := mkConst ``Primitive

meta partial def toExprTerm : Term → Expr
  | .hole n σ =>
    have : ToExpr Term := ⟨toExprTerm, mkConst ``Obend.Core.Term.Term⟩
    mkApp2 (mkConst ``Term.hole) (toExpr n) (toExpr σ)
  | .bound i => mkApp (mkConst ``Term.bound) (toExpr i)
  | .lam b => mkApp (mkConst ``Term.lam) (toExprTerm b)
  | .app f a => mkApp2 (mkConst ``Term.app) (toExprTerm f) (toExprTerm a)
  | .mix l u => mkApp2 (mkConst ``Term.mix) (toExprTerm l) (toExprTerm u)
  | .fix s i => mkApp2 (mkConst ``Term.fix) (toExprTerm s) (toExprTerm i)
  | .specification m e => mkApp2 (mkConst ``Term.specification) (toExprTerm m) (toExprTerm e)
  | .prototype s g => mkApp2 (mkConst ``Term.prototype) (toExprTerm s) (toExprTerm g)
  | .reflect p => mkApp (mkConst ``Term.reflect) (toExprTerm p)
  | .metadata p => mkApp (mkConst ``Term.metadata) (toExprTerm p)
  | .project p => mkApp (mkConst ``Term.project) (toExprTerm p)
  | .nat n => mkApp (mkConst ``Term.nat) (toExpr n)
  | .boolean b => mkApp (mkConst ``Term.boolean) (toExpr b)
  | .label s => mkApp (mkConst ``Term.label) (toExpr s)
  | .binary op l r => mkApp3 (mkConst ``Term.binary) (toExpr op) (toExprTerm l) (toExprTerm r)
  | .extend i fs =>
    have : ToExpr Term := ⟨toExprTerm, mkConst ``Obend.Core.Term.Term⟩
    mkApp2 (mkConst ``Term.extend) (toExprTerm i) (toExpr fs)
  | .record fs =>
    have : ToExpr Term := ⟨toExprTerm, mkConst ``Obend.Core.Term.Term⟩
    mkApp (mkConst ``Term.record) (toExpr fs)
  | .get t name => mkApp2 (mkConst ``Term.get) (toExprTerm t) (toExpr name)
  | .ifZero v z s => mkApp3 (mkConst ``Term.ifZero) (toExprTerm v) (toExprTerm z) (toExprTerm s)
  | .inject l p => mkApp2 (mkConst ``Term.inject) (toExpr l) (toExprTerm p)
  | .case sc arms =>
    have : ToExpr Term := ⟨toExprTerm, mkConst ``Obend.Core.Term.Term⟩
    mkApp2 (mkConst ``Term.case) (toExprTerm sc) (toExpr arms)
  | .ifBool c x y => mkApp3 (mkConst ``Term.ifBool) (toExprTerm c) (toExprTerm x) (toExprTerm y)
  | .perform p => mkApp (mkConst ``Term.perform) (toExprTerm p)
  | .done v => mkApp (mkConst ``Term.done) (toExprTerm v)
  | .split t names f =>
    mkApp3 (mkConst ``Term.split) (toExprTerm t) (toExpr names) (toExprTerm f)

meta instance : ToExpr Term where
  toExpr := toExprTerm
  toTypeExpr := mkConst ``Obend.Core.Term.Term

meta instance : ToExpr Quantity where
  toExpr
    | .erased => mkConst ``Quantity.erased
    | .affine => mkConst ``Quantity.affine
    | .linear => mkConst ``Quantity.linear
    | .unrestricted => mkConst ``Quantity.unrestricted
  toTypeExpr := mkConst ``Quantity

meta instance : ToExpr Reuse where
  toExpr
    | .once => mkConst ``Reuse.once
    | .reusable => mkConst ``Reuse.reusable
  toTypeExpr := mkConst ``Reuse

meta partial def toExprTy : Ty → Expr
  | .natural => mkConst ``Ty.natural
  | .label => mkConst ``Ty.label
  | .boolean => mkConst ``Ty.boolean
  | .variable i => mkApp (mkConst ``Ty.variable) (toExpr i)
  | .arrow r q d c => mkApp4 (mkConst ``Ty.arrow) (toExpr r) (toExpr q) (toExprTy d) (toExprTy c)
  | .emptyRow => mkConst ``Ty.emptyRow
  | .field n m t => mkApp3 (mkConst ``Ty.field) (toExpr n) (toExprTy m) (toExprTy t)
  | .specification m e => mkApp2 (mkConst ``Ty.specification) (toExprTy m) (toExprTy e)
  | .prototype s t => mkApp2 (mkConst ``Ty.prototype) (toExprTy s) (toExprTy t)
  | .custody i => mkApp (mkConst ``Ty.custody) (toExpr i)
  | .variant r => mkApp (mkConst ``Ty.variant) (toExprTy r)
  | .computation p r res => mkApp3 (mkConst ``Ty.computation) (toExprTy p) (toExprTy r) (toExprTy res)

meta instance : ToExpr Ty where
  toExpr := toExprTy
  toTypeExpr := mkConst ``Ty

meta instance : ToExpr NatOp where
  toExpr
    | .add => mkConst ``NatOp.add
    | .sub => mkConst ``NatOp.sub
    | .mul => mkConst ``NatOp.mul
    | .div => mkConst ``NatOp.div
    | .mod => mkConst ``NatOp.mod
    | .beq => mkConst ``NatOp.beq
    | .ble => mkConst ``NatOp.ble
  toTypeExpr := mkConst ``NatOp

meta partial def toExprLExpr : LExpr → Expr
  | .bvar i => mkApp (mkConst ``LExpr.bvar) (toExpr i)
  | .erased => mkConst ``LExpr.erased
  | .const n b => mkApp2 (mkConst ``LExpr.const) (toExpr n) (toExprLExpr b)
  | .app f a => mkApp2 (mkConst ``LExpr.app) (toExprLExpr f) (toExprLExpr a)
  | .lam d b => mkApp2 (mkConst ``LExpr.lam) (toExpr d) (toExprLExpr b)
  | .letE d v b => mkApp3 (mkConst ``LExpr.letE) (toExpr d) (toExprLExpr v) (toExprLExpr b)
  | .lit n => mkApp (mkConst ``LExpr.lit) (toExpr n)
  | .natSucc a => mkApp (mkConst ``LExpr.natSucc) (toExprLExpr a)
  | .natBin op l r => mkApp3 (mkConst ``LExpr.natBin) (toExpr op) (toExprLExpr l) (toExprLExpr r)
  | .boolLit b => mkApp (mkConst ``LExpr.boolLit) (toExpr b)
  | .natRec res z s m =>
    mkApp4 (mkConst ``LExpr.natRec) (toExpr res) (toExprLExpr z) (toExprLExpr s) (toExprLExpr m)
  | .boolRec res wf wt m =>
    mkApp4 (mkConst ``LExpr.boolRec) (toExpr res) (toExprLExpr wf) (toExprLExpr wt) (toExprLExpr m)
  | .record fs =>
    have : ToExpr LExpr := ⟨toExprLExpr, mkConst ``LExpr⟩
    mkApp (mkConst ``LExpr.record) (toExpr fs)
  | .split names mn mj =>
    mkApp3 (mkConst ``LExpr.split) (toExpr names) (toExprLExpr mn) (toExprLExpr mj)
  | .proj n t => mkApp2 (mkConst ``LExpr.proj) (toExpr n) (toExprLExpr t)
  | .inject l fs =>
    have : ToExpr LExpr := ⟨toExprLExpr, mkConst ``LExpr⟩
    mkApp2 (mkConst ``LExpr.inject) (toExpr l) (toExpr fs)
  | .cases res arms mj =>
    have : ToExpr LExpr := ⟨toExprLExpr, mkConst ``LExpr⟩
    mkApp3 (mkConst ``LExpr.cases) (toExpr res) (toExpr arms) (toExprLExpr mj)
  | .recConst n ty b => mkApp3 (mkConst ``LExpr.recConst) (toExpr n) (toExpr ty) (toExprLExpr b)

meta instance : ToExpr LExpr where
  toExpr := toExprLExpr
  toTypeExpr := mkConst ``LExpr

meta instance : ToExpr Layer where
  toExpr L :=
    mkApp5 (mkConst ``Layer.mk)
      (toExpr L.name) (toExpr L.metadata) (toExpr L.fields) (toExpr L.flat) (toExpr L.composeMeta)
  toTypeExpr := mkConst ``Layer

meta instance : ToExpr Composition where
  toExpr C :=
    mkApp3 (mkConst ``Composition.mk) (toExpr C.top) (toExpr C.below) (toExpr C.seed)
  toTypeExpr := mkConst ``Composition

meta instance : ToExpr DefKind where
  toExpr
    | .method => mkConst ``Obend.Leaf.DefKind.method
    | .cell => mkConst ``Obend.Leaf.DefKind.cell
  toTypeExpr := mkConst ``Obend.Leaf.DefKind

meta instance : ToExpr LeafDef where
  toExpr d :=
    mkApp5 (mkConst ``LeafDef.mk)
      (toExpr d.member) (toExpr d.slot) (toExpr d.kind) (toExpr d.code) (toExpr d.reads)
  toTypeExpr := mkConst ``LeafDef

meta instance : ToExpr BookItem where
  toExpr
    | .slot d => mkApp (mkConst ``BookItem.slot) (toExpr d)
    | .static m v => mkApp2 (mkConst ``BookItem.static) (toExpr m) (toExpr v)
  toTypeExpr := mkConst ``BookItem

meta instance : ToExpr Book where
  toExpr B := mkApp (mkConst ``Book.mk) (toExpr B.items)
  toTypeExpr := mkConst ``Book

meta instance : ToExpr ReflectedObject where
  toExpr ro :=
    mkApp3 (mkConst ``mkReflectedObject) (toExpr ro.name) (toExpr ro.composition) (toExpr ro.defs)
  toTypeExpr := mkConst ``ReflectedObject

meta partial def toExprRStep : RStep → Expr
  | .run n => mkApp (mkConst ``RStep.run) (toExpr n)
  | .lateBinding m L => mkApp2 (mkConst ``RStep.lateBinding) (toExpr m) (toExpr L)
  | .assoc d => mkApp (mkConst ``RStep.assoc) (toExpr d)
  | .composeAssoc d => mkApp (mkConst ``RStep.composeAssoc) (toExpr d)
  | .congr C a inner =>
    have : ToExpr RStep := ⟨toExprRStep, mkConst ``RStep⟩
    mkApp3 (mkConst ``RStep.congr) (toExpr C) (toExpr a) (toExpr inner)
  | .trans f s =>
    have : ToExpr RStep := ⟨toExprRStep, mkConst ``RStep⟩
    mkApp2 (mkConst ``RStep.trans) (toExpr f) (toExpr s)

meta instance : ToExpr RStep where
  toExpr := toExprRStep
  toTypeExpr := mkConst ``RStep

meta instance : ToExpr ClaimObj where
  toExpr o :=
    mkApp4 (mkConst ``ClaimObj.mk) (toExpr o.comp) (toExpr o.layer) (toExpr o.claim) (toExpr o.arity)
  toTypeExpr := mkConst ``ClaimObj

meta instance : ToExpr Support where
  toExpr sp := mkApp2 (mkConst ``Support.mk) (toExpr sp.member) (toExpr sp.unfolded)
  toTypeExpr := mkConst ``Support

meta instance : ToExpr ByteArray where
  toExpr ba := mkApp (mkConst ``mkByteArrayOfList) (toExpr ba.data.toList)
  toTypeExpr := mkConst ``ByteArray

meta instance : ToExpr Justification where
  toExpr
    | .byDerivation steps => mkApp (mkConst ``Justification.byDerivation) (toExpr steps)
    | .byLoweredLean lowered sups receipt =>
      mkApp3 (mkConst ``Justification.byLoweredLean) (toExpr lowered) (toExpr sups) (toExpr receipt)
    | .byExternalJudge fmt payload =>
      mkApp2 (mkConst ``Justification.byExternalJudge) (toExpr fmt) (toExpr payload)
    | .byEval samples => mkApp (mkConst ``Justification.byEval) (toExpr samples)
  toTypeExpr := mkConst ``Justification

meta instance : ToExpr LawRef where
  toExpr
    | .field n => mkApp (mkConst ``LawRef.field) (toExpr n)
    | .subject => mkConst ``LawRef.subject
    | .caller => mkConst ``LawRef.caller
    | .height => mkConst ``LawRef.height
    | .turn => mkConst ``LawRef.turn
  toTypeExpr := mkConst ``LawRef

meta partial def toExprLawExpr : LawExpr → Expr
  | .eqC r v => mkApp2 (mkConst ``LawExpr.eqC) (toExpr r) (toExpr v)
  | .leC r v => mkApp2 (mkConst ``LawExpr.leC) (toExpr r) (toExpr v)
  | .inC r vs => mkApp2 (mkConst ``LawExpr.inC) (toExpr r) (toExpr vs)
  | .eqR l r => mkApp2 (mkConst ``LawExpr.eqR) (toExpr l) (toExpr r)
  | .leR l r => mkApp2 (mkConst ``LawExpr.leR) (toExpr l) (toExpr r)
  | .leROff l r off => mkApp3 (mkConst ``LawExpr.leROff) (toExpr l) (toExpr r) (toExpr off)
  | .monotone f => mkApp (mkConst ``LawExpr.monotone) (toExpr f)
  | .writeOnce f => mkApp (mkConst ``LawExpr.writeOnce) (toExpr f)
  | .not b => mkApp (mkConst ``LawExpr.not) (toExprLawExpr b)
  | .and l r => mkApp2 (mkConst ``LawExpr.and) (toExprLawExpr l) (toExprLawExpr r)
  | .or l r => mkApp2 (mkConst ``LawExpr.or) (toExprLawExpr l) (toExprLawExpr r)
  | .implies p c => mkApp2 (mkConst ``LawExpr.implies) (toExprLawExpr p) (toExprLawExpr c)

meta instance : ToExpr LawExpr where
  toExpr := toExprLawExpr
  toTypeExpr := mkConst ``LawExpr

meta instance : ToExpr WorkbookDef where
  toExpr d :=
    mkApp9 (mkConst ``WorkbookDef.mk)
      (toExpr d.name) (toExpr d.fullKey) (toExpr d.knotTerm) (toExpr d.term)
      (toExpr d.reducedTerm?) (toExpr d.lexpr?) (toExpr d.composition?)
      (toExpr d.book?) (toExpr d.reflectedObject?)
  toTypeExpr := mkConst ``WorkbookDef

meta instance : ToExpr WorkbookClaim where
  toExpr c :=
    mkApp7 (mkConst ``WorkbookClaim.mk)
      (toExpr c.specKey) (toExpr c.name) (toExpr c.targetDef) (toExpr c.claimObj)
      (toExpr c.autoSteps?) (toExpr c.autoJustification?) (toExpr c.autoVerified)
  toTypeExpr := mkConst ``WorkbookClaim

meta instance : ToExpr WorkbookPackage where
  toExpr p :=
    Lean.mkAppN (mkConst ``WorkbookPackage.mk)
      #[toExpr p.moduleName, toExpr p.entryDef, toExpr p.source, toExpr p.sha256,
        toExpr p.accepted, toExpr p.erasedTerm, toExpr p.rootTerm,
        toExpr p.defs, toExpr p.claims, toExpr p.laws, toExpr p.lawsCount]
  toTypeExpr := mkConst ``WorkbookPackage

/-! ## 6. Command Elaborators `#import_obend` and `#obend_decl` -/

private meta def metaEmptyLayoutEnv : LayoutEnv :=
  { fields := [], selfIndex := 0, arity := 0 }

private meta def metaDefaultWorkbookLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

private meta def metaNormalizeObendSource (src : String) : String :=
  let trimmed := src.trimAscii.toString
  if trimmed.startsWith "edition ObjectiveBend 1" then src
  else "edition ObjectiveBend 1\n" ++ src

private meta def metaResolveKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          metaResolveKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (metaResolveKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (metaResolveKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (metaResolveKnotTerm root rawFields visiting fuel f) (metaResolveKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (metaResolveKnotTerm root rawFields visiting fuel l) (metaResolveKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (metaResolveKnotTerm root rawFields visiting fuel s) (metaResolveKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (metaResolveKnotTerm root rawFields visiting fuel m) (metaResolveKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (metaResolveKnotTerm root rawFields visiting fuel s) (metaResolveKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (metaResolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (metaResolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (metaResolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (metaResolveKnotTerm root rawFields visiting fuel l) (metaResolveKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (metaResolveKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, metaResolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, metaResolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (metaResolveKnotTerm root rawFields visiting fuel v)
      (metaResolveKnotTerm root rawFields visiting fuel z)
      (metaResolveKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (metaResolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (metaResolveKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, metaResolveKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (metaResolveKnotTerm root rawFields visiting fuel c)
      (metaResolveKnotTerm root rawFields visiting fuel x)
      (metaResolveKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (metaResolveKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (metaResolveKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (metaResolveKnotTerm root rawFields visiting fuel t) names
      (metaResolveKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t

private meta def metaDecodeWorkbookWithSeed (want : Composition → Bool) : Term → Option Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none

private meta def metaFindWorkbookObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match metaDecodeWorkbookWithSeed want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (metaFindWorkbookObject want fuel)

private meta def metaFindSelfGetCtx (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match metaFindSelfGetCtx selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (metaFindSelfGetCtx selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match metaFindSelfGetCtx selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (metaFindSelfGetCtx selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

private meta def metaDeriveWorkbook (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => metaDeriveWorkbook o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match metaFindSelfGetCtx o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => metaDeriveWorkbook o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

private meta def metaProposeWorkbookDerivation (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => metaDeriveWorkbook o r 4096 l []
    | none => none


/-- Strip layer metadata and `#kind` fields so the emitted `Composition` reduces in the kernel
(`decide +kernel` over `_comp`/`_book` constants). The flattened behaviour is unchanged. -/
private meta def metaCompactLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

private meta def metaCompactCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := metaCompactLayerForKernel C.top
    below := C.below.map metaCompactLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

private meta def metaSanitizeModuleName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

private meta def metaStripImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

private meta def metaParseAndCheckObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let normSrc := metaNormalizeObendSource src
  let sha256 := Obend.Spec.Sha256.hex normSrc.toUTF8
  let ast ← match Obend.Spec.FrontEnd.parseSource moduleName normSrc with
    | .ok a => pure a
    | .error d => throw s!"{d.stage}: {d.message}"
  let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let mut lockedImports : List Obend.Spec.FrontEnd.LockedImport := []
  for edge in parsedEdges.toList do
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgeSpan := (edge.getObjVal? "span").toOption.getD .null
    let cleanPath := metaStripImportQuotes edgePath
    let stemMod := metaSanitizeModuleName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
    let found? := prior.zipIdx.find? fun ((sm, _), _) =>
      sm.name == stemMod || (edgeAlias != "" && sm.name == edgeAlias)
    let some ((targetSm, _), targetIdx) := found?
      | throw s!"module {moduleName}: imported module for '{edgePath}' (alias '{edgeAlias}') not found in loaded closure"
    lockedImports := lockedImports ++ [{
      path := edgePath
      importAlias := edgeAlias
      span := edgeSpan
      target := targetIdx
      moduleName := targetSm.name
      sha256 := targetSm.sha256
    }]
  let srcMod : Obend.Spec.FrontEnd.SourceModule := {
    name := moduleName
    source := normSrc
    sha256 := sha256
    imports := lockedImports
  }
  let decodedMod ← match Obend.Spec.FrontEnd.checkParsed srcMod ast with
    | .ok m => pure m
    | .error d => throw s!"{d.stage}: {d.message}"
  return (srcMod, decodedMod)

private meta def metaElaborateObendSource (src : String) (moduleName : String := "Main")
    (entryDef? : Option String := none)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := []) :
    Except String WorkbookPackage := do
  let (srcMod, decodedMod) ← metaParseAndCheckObendModule src moduleName prior
  let normSrc := srcMod.source
  let sha256 := srcMod.sha256
  let callables := decodedMod.decls.filter fun d =>
    match d with
    | .function .. | .extension .. | .spec .. => true
    | _ => false
  let entryDef ← match entryDef? with
    | some e => pure e
    | none =>
      match callables.getLast? with
      | some d => pure d.name
      | none => throw s!"module {moduleName} contains no callable function, extension, or spec"
  let allSrcMods := prior.map Prod.fst ++ [srcMod]
  let allDecodedMods := prior.map Prod.snd ++ [decodedMod]
  let entryIdx := prior.length
  let allLaws := (allDecodedMods.map (·.laws)).flatten
  let decodedForLower := allDecodedMods.zipIdx.map fun (dm, idx) =>
    if idx == entryIdx then { dm with laws := allLaws } else { dm with laws := [] }
  let lowering ← match Obend.Spec.FrontEnd.lowerDecoded allSrcMods decodedForLower entryIdx entryDef
      (Json.arr #[]) (Json.arr #[]) metaDefaultWorkbookLimits "definition" [] with
    | .ok l => pure l
    | .error d => throw s!"{d.stage}: {d.message}"
  let acc ← match Obend.Spec.FrontEnd.accept lowering with
    | .ok a => pure a
    | .error d => throw s!"{d.stage}: {d.message}"
  for c in decodedMod.contracts do
    if !c.steps.isEmpty then
      match Obend.Spec.FrontEnd.checkContractIsarCert Obend.Spec.FrontEnd.defaultAutoCertAdmitsTag decodedMod c with
      | .ok _ => pure ()
      | .error d => throw s!"{d.stage}: {d.message}"
    else if !Obend.Elab.AutoCert.verifyContractAutoCertSteps Obend.Elab.AutoCert.autoCertFormats moduleName none c then
      throw s!"elaborate: refused (autocert-synthesis): contract {c.name} failed automatic certificate synthesis"
  let erasedTerm := acc.erased
  let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
  let rawFields := Obend.Logic.Program.knotFields rootTerm
  let mut wdefs : List WorkbookDef := []
  for d in callables do
    let shortName := d.name
    let fullKey := moduleName ++ "." ++ shortName
    let knotTerm : Term := .get rootTerm fullKey
    let opened := match rawFields.lookup fullKey with
      | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
      | none => knotTerm
    let inlined := metaResolveKnotTerm rootTerm rawFields [fullKey] 16 opened
    let reducedTerm? := Obend.Law.run 50000 knotTerm
    let wantNamed : Composition → Bool := fun C => C.top.name != ""
    let foundComp? :=
      match metaFindWorkbookObject wantNamed 64 knotTerm with
      | some c => some c
      | none =>
        match metaFindWorkbookObject wantNamed 64 (.app knotTerm (.record [])) with
        | some c => some c
        | none => metaDecodeWorkbookWithSeed wantNamed inlined
    let composition? : Option Composition :=
      match foundComp?.map metaCompactCompositionForKernel with
      | some c => some c
      | none =>
        match d with
        | .function .. =>
          let lc := Obend.Lower.leanComposition shortName inlined
          if lc.closedB then some lc else none
        | _ => none
    let book? : Option Book := composition?.map Obend.Leaf.emit
    let reflectedObject? : Option ReflectedObject :=
      composition?.bind fun c => reflectComposition shortName c metaEmptyLayoutEnv
    let lexpr? : Option LExpr :=
      match lowerTerm metaEmptyLayoutEnv inlined with
      | some e => some e
      | none => reducedTerm?.bind (lowerTerm metaEmptyLayoutEnv)
    wdefs := wdefs ++ [{
      name := shortName
      fullKey := fullKey
      knotTerm := knotTerm
      term := inlined
      reducedTerm? := reducedTerm?
      lexpr? := lexpr?
      composition? := composition?
      book? := book?
      reflectedObject? := reflectedObject?
    }]
  let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
  let mut wclaims : List WorkbookClaim := []
  for (specKey, claimName) in rawClaimPairs do
    let matchingDefs := wdefs.filter fun wd =>
      match wd.composition? with
      | some comp => (Obend.Logic.Program.layerIndex comp specKey).isSome
      | none => false
    let chosenDef? :=
      match matchingDefs.find? (fun wd => wd.composition?.any (fun c => c.top.name == specKey)) with
      | some wd => some wd
      | none => matchingDefs.head?
    if let some wd := chosenDef? then
      if let some comp := wd.composition? then
        if let .ok co := Obend.Logic.Program.claimObj rootTerm comp specKey claimName then
          let steps? := metaProposeWorkbookDerivation co
          let derivJust? := steps?.map Justification.byDerivation
          let derivOk := match derivJust? with
            | some j => Obend.Logic.obligationCheck 4096 co j == Obend.Judge.Verdict.ok
            | none => false
          let claimDecl? : Option Obend.Spec.Syntax.Claim :=
            allDecodedMods.findSome? fun dm =>
              dm.decls.findSome? fun d =>
                match d with
                | .spec s =>
                  if s.name == specKey || (dm.name ++ "." ++ s.name) == specKey then
                    s.claims.find? (·.name == claimName)
                  else none
                | _ => none
          let (just?, ok) :=
            if derivOk then
              (derivJust?, true)
            else
              match Obend.Elab.AutoCert.synthesizeClaimExternalJudge
                  Obend.Elab.AutoCert.autoCertFormats 4096 moduleName claimName claimDecl? wd.book? co with
              | some extJ =>
                (some extJ,
                 Obend.Logic.obligationCheckWithJudges Obend.Elab.AutoCert.autoCertFormats 4096 co extJ ==
                   Obend.Judge.Verdict.ok)
              | none =>
                (derivJust?, false)
          wclaims := wclaims ++ [{
            specKey := specKey
            name := claimName
            targetDef := wd.name
            claimObj := co
            autoSteps? := steps?
            autoJustification? := just?
            autoVerified := ok
          }]
  return {
    moduleName := moduleName
    entryDef := entryDef
    source := normSrc
    sha256 := sha256
    accepted := true
    erasedTerm := erasedTerm
    rootTerm := rootTerm
    defs := wdefs
    claims := wclaims
    laws := lowering.laws
    lawsCount := decodedMod.laws.length
  }

private meta def metaResolveObendPath (path : System.FilePath) : IO System.FilePath := do
  if ← path.pathExists then return path
  let s := path.toString
  if s.startsWith "lean/" then
    let stripped := System.FilePath.mk (s.drop 5).toString
    if ← stripped.pathExists then return stripped
  let prefixed := System.FilePath.mk ("lean/" ++ s)
  if ← prefixed.pathExists then return prefixed
  let parentRel := System.FilePath.mk ("../" ++ s)
  if ← parentRel.pathExists then return parentRel
  return path

private meta def metaResolveImportedObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := metaStripImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← metaResolveObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← metaResolveObendPath rel2
  if ← r2.pathExists then return r2
  let r3 ← metaResolveObendPath (System.FilePath.mk stripped)
  if ← r3.pathExists then return r3
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["stdlib/core/", "stdlib/ledger/", "stdlib/usd/", "stdlib/physical/", "apps/obend-risc/", "apps/zk-ntt/", "apps/foc-hil/", "apps/sdr-ft8/", "apps/fidget-cam/", "apps/quantum-photonic-matter/", "apps/sovereign-drex/", "apps/silicon-kernel-verilator/"] do
    let cand ← metaResolveObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

private meta def metaLoadObendModuleClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← metaResolveObendPath path
    let modName := metaSanitizeModuleName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let normSrc := metaNormalizeObendSource rawSrc
      let ast ← match Obend.Spec.FrontEnd.parseSource modName normSrc with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← metaResolveImportedObendPath resolved edgePath
        match ← metaLoadObendModuleClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match metaParseAndCheckObendModule normSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

private meta def metaLoadObendWorkbookFile (path : System.FilePath) : IO (Except String WorkbookPackage) := do
  match ← metaLoadObendModuleClosure 32 path [] with
  | .error err => return .error err
  | .ok closure =>
    match closure.getLast? with
    | none => return .error s!"empty module closure for {path}"
    | some (lastSrc, _) =>
      return metaElaborateObendSource lastSrc.source lastSrc.name none closure.dropLast

meta def defineWorkbookConst {α : Type} [ToExpr α] (declName : Name) (val : α) :
    CommandElabM Unit := do
  let env ← getEnv
  if env.contains declName then
    return ()
  let decl : Declaration := .defnDecl {
    name := declName
    levelParams := []
    type := toTypeExpr α
    value := toExpr val
    hints := .regular 0
    safety := .safe
  }
  liftCoreM <| Lean.withExporting (isExporting := true) <| addAndCompile decl

meta def defineWorkbookThm (thmName : Name) (ty val : Expr) : CommandElabM Unit := do
  let env ← getEnv
  if env.contains thmName then
    return ()
  let decl : Declaration := .thmDecl {
    name := thmName
    levelParams := []
    type := ty
    value := val
  }
  liftCoreM <| Lean.withExporting (isExporting := true) <| addDecl decl

meta def tryDefineWorkbookThm (thmName : Name) (ty val : Expr) : CommandElabM Unit := do
  let env ← getEnv
  if env.contains thmName then
    return ()
  let decl : Declaration := .thmDecl {
    name := thmName
    levelParams := []
    type := ty
    value := val
  }
  let checkRes ← liftCoreM do
    let opts ← Lean.getOptions
    return (env.setExporting true).unlockAsync.addDeclCore
      (Lean.Core.getMaxHeartbeats opts).toUSize
      (Lean.maxRecDepth.get opts).toUSize
      decl none (doCheck := true)
  if let .ok _ := checkRes then
    liftCoreM <| Lean.withExporting (isExporting := true) <| addDecl decl

/-- Emit all kernel-checked constants and theorems for a `WorkbookPackage` into namespace `ns`. -/
meta def registerAndEmitWorkbook (ns : Name) (pkg : WorkbookPackage) : CommandElabM Unit := do
  modifyEnv fun env => obendWorkbookExt.addEntry env (ns, pkg)
  defineWorkbookConst (ns ++ `package) pkg
  -- No `Ns.accepted`/`Ns.accepted_eq`: reaching this line is the acceptance; a `true = true`
  -- theorem recorded nothing (review/EXPERT-lean-proof-engineering-20261103.md §4).
  defineWorkbookConst (ns ++ `laws_count) pkg.lawsCount
  for d in pkg.defs do
    let dTermName := ns ++ Name.mkSimple (d.name ++ "_term")
    let dKnotName := ns ++ Name.mkSimple (d.name ++ "_knot_term")
    defineWorkbookConst dTermName d.term
    defineWorkbookConst dKnotName d.knotTerm
    if let some rt := d.reducedTerm? then
      defineWorkbookConst (ns ++ Name.mkSimple (d.name ++ "_val")) rt
    if let some le := d.lexpr? then
      let dLExprName := ns ++ Name.mkSimple (d.name ++ "_lexpr")
      defineWorkbookConst dLExprName le
      if (lowerTerm metaEmptyLayoutEnv d.term).isSome then
        let optTy := toTypeExpr (Option LExpr)
        let lhs := mkApp2 (mkConst ``lowerTerm) (mkConst ``emptyLayoutEnv) (mkConst dTermName)
        let rhs := mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``LExpr) (mkConst dLExprName)
        let eqTy := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) optTy lhs rhs
        let eqPrf := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) optTy rhs
        tryDefineWorkbookThm (ns ++ Name.mkSimple (d.name ++ "_lowerTerm_eq")) eqTy eqPrf
    if let some comp := d.composition? then
      defineWorkbookConst (ns ++ Name.mkSimple (d.name ++ "_comp")) comp
    if let some bk := d.book? then
      defineWorkbookConst (ns ++ Name.mkSimple (d.name ++ "_book")) bk
    if let some ro := d.reflectedObject? then
      defineWorkbookConst (ns ++ Name.mkSimple (d.name ++ "_reflected")) ro
      for (mName, mLExpr) in ro.defs do
        if mName != d.name then
          defineWorkbookConst (ns ++ Name.mkSimple (d.name ++ "_" ++ mName ++ "_lexpr")) mLExpr
  for c in pkg.claims do
    let dupCount := (pkg.claims.filter (·.name == c.name)).length
    let prefixes : List String :=
      if dupCount > 1 then
        [c.targetDef ++ "_claim_" ++ c.name, "claim_" ++ c.name]
      else
        ["claim_" ++ c.name]
    for pfx in prefixes do
      let objName := ns ++ Name.mkSimple (pfx ++ "_obj")
      defineWorkbookConst objName c.claimObj
      if let some just := c.autoJustification? then
        let justName := ns ++ Name.mkSimple (pfx ++ "_just")
        defineWorkbookConst justName just
        if c.autoVerified then
          let holdsName := ns ++ Name.mkSimple (pfx ++ "_holds")
          let fmtsE := mkConst ``workbookFormats
          let gradeE := toExpr (4096 : Nat)
          let verdictTy := mkApp (mkConst ``Obend.Judge.Verdict) (mkConst ``ClaimClause)
          let okE := mkApp (mkConst ``Obend.Judge.Verdict.ok) (mkConst ``ClaimClause)
          let checkEqPrf := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) verdictTy okE
          let holdsTy := mkApp3 (mkConst ``Obend.Logic.obligationMeaningWithJudges)
            fmtsE (mkConst objName) (mkConst justName)
          let holdsPrf := mkApp5 (mkConst ``Obend.Logic.obligationWithJudges_sound)
            fmtsE gradeE (mkConst objName) (mkConst justName) checkEqPrf
          defineWorkbookThm holdsName holdsTy holdsPrf

/-- `#import_obend "path/to/File.obend" as Ns`:
    Elaborate an `.obend` file at compile time, verify `FrontEnd.accept`, register the package in
    `obendWorkbookExt`, and emit typed Lean constants in namespace `Ns`. -/
elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res : Except String WorkbookPackage ←
    IO.toEIO (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
      (metaLoadObendWorkbookFile (System.FilePath.mk pathStr))
  match res with
  | .error err =>
    Lean.throwError m!"#import_obend failed on {pathStr}: {err}"
  | .ok pkg =>
    registerAndEmitWorkbook nsId.getId pkg

/-- `#obend_decl Ns "..."`:
    Elaborate an inline `.obend` declaration/module at compile time, verify `FrontEnd.accept`,
    register the package in `obendWorkbookExt`, and emit typed Lean constants in namespace `Ns`. -/
elab "#obend_decl " nsId:ident srcLit:str : command => do
  let srcStr := srcLit.getString
  let modName := metaSanitizeModuleName nsId.getId.toString
  match metaElaborateObendSource srcStr modName none with
  | .error err =>
    Lean.throwError m!"#obend_decl failed in {nsId.getId}: {err}"
  | .ok pkg =>
    registerAndEmitWorkbook nsId.getId pkg

/-- `#obend_decl Ns named "ModName" "..."`: as `#obend_decl`, with the `.obend` module name given
    explicitly (the inline sources of `Obend.Hardware.UserspacePhysical` name their modules). -/
elab "#obend_decl " nsId:ident " named " modLit:str srcLit:str : command => do
  let srcStr := srcLit.getString
  let modName := metaSanitizeModuleName modLit.getString
  match metaElaborateObendSource srcStr modName none with
  | .error err =>
    Lean.throwError m!"#obend_decl failed in {nsId.getId}: {err}"
  | .ok pkg =>
    registerAndEmitWorkbook nsId.getId pkg

end Obend.Elab.Workbook

end
