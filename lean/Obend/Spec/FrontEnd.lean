module
/-
# Obend.Spec.FrontEnd — the Objective Bend front end, source text to checked typed core

`lower` is the whole front end on an already-read package: parse every module (`Obend.Spec.Parse`),
check each module's locked import transcript against its parsed imports, elaborate the selected
declaration (`Obend.Spec.Elaborate`), apply result projections, and render the core
(`dregg.objective-bend.core.v2`) and the typing proposal packet (`dregg.objective-bend.typed-core.v3`)
that the checker reads.

`accept` closes the loop on the SAME value: it decodes the packet the front end just rendered with
the checker's own decoder (`Obend.Core.Packet.decodePacket`) and runs the gate on it
(`Obend.Elab.Gate.admit`: executable annotation preparation with the packet's annotations as hints,
then the proof-producing bidirectional checker `Obend.Core.Bidirectional.checkAgainst`). That the decoded term IS the erasure of the elaborator's annotated
term is a theorem (`Obend.Spec.Proofs.TermWire.decode_json`, applied to the `shallow` bound `accept`
records as `Accepted.packetTerm`), not a run-time comparison: `accept` refuses only a term nested
deeper than the decoder's capacity. An `Accepted` value therefore carries
a typing derivation for exactly the Core4 term the elaborator produced
(`Obend.Spec.Proofs.FrontEndAdequacy` states what that buys).

Ported from minidregg `Compiler/ObjectiveBendFrontEnd.lean` (commit 092027a2). Two changes of
shape, both forced by the module system: `Accepted`'s constructor was `private mk ::` there, and an
exposed body (`accept`) may not cite a private constructor (REPORT-20261030 D5), so it is public and
"built only by `accept`" is a convention of this module; and `packetTerm` was a FIELD proved inside
`accept` from `decode_json`, whose proof unfolds `Lean.Json`, which no `module` can see, so the
proofs are the legacy leaf `Obend.Spec.Proofs.TermWire`, `accept` records the depth bound it checked
(`shallow`) and `packetTerm` is a theorem there about every `Accepted`.
-/
public import Lean
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Packet
public import Obend.Spec.Law
public import Obend.Spec.LawCompile
public import Obend.Spec.Syntax
public import Obend.Spec.Parse
public import Obend.Spec.Types
public import Obend.Spec.Annotated
public import Obend.Spec.Elaborate
public import Obend.Spec.Sha256
public import Obend.Elab.Gate
@[expose] public section
namespace Obend.Spec.FrontEnd
open Lean (Json toJson)
open Obend.Spec.Annotated (ATerm CoreTerm)
open Obend.Spec.Elaborate (Output)
open Obend.Core.Packet (DecodedPacket decodePacket)
open Obend.Core.Check (Checked check)
set_option autoImplicit false

/-! ## Diagnostics -/

/-- A front-end refusal: the stage that refused, its message, and (for a parse refusal) the
line span and module. Rendered as `dregg.bend.compiler-diagnostic.v1`. -/
structure Diagnostic where
  stage : String
  message : String
  span : Option Parse.Span := none
  sourceModule : Option String := none
  deriving Inhabited, Repr

def Diagnostic.json (d : Diagnostic) : Json :=
  Json.mkObj ([("schema", toJson "dregg.bend.compiler-diagnostic.v1"), ("stage", toJson d.stage),
    ("message", toJson d.message)] ++
    (match d.span with | some s => [("span", s.json)] | none => []) ++
    (match d.sourceModule with | some m => [("module", toJson m)] | none => []))

def elaborationRefusal (message : String) : Diagnostic := { stage := "objective-core-elaboration", message }

/-! ## Captured modules -/

/-- An import edge as captured: the parsed edge (path, alias, span) and its lock
(the earlier module it names and that module's source fingerprint). -/
structure LockedImport where
  path : String
  importAlias : String
  span : Json
  target : Nat
  moduleName : String
  sha256 : String
  deriving Inhabited

def LockedImport.json (i : LockedImport) : Json :=
  Json.mkObj [("path", toJson i.path), ("alias", toJson i.importAlias), ("span", i.span),
    ("module", toJson (toString i.target)), ("moduleName", toJson i.moduleName), ("sha256", toJson i.sha256)]

/-- One module of a captured package: its exact source text and fingerprint. -/
structure SourceModule where
  name : String
  source : String
  sha256 : String
  imports : List LockedImport
  deriving Inhabited

def SourceModule.binding (m : SourceModule) : Json :=
  Json.mkObj [("name", toJson m.name), ("sourceSha256", toJson m.sha256),
    ("imports", Json.arr (m.imports.map LockedImport.json).toArray)]

def declarationName (d : Json) : String :=
  match (d.getObjValAs? String "kind").toOption with
  | some "function" => ((d.getObjVal? "signature").bind (·.getObjValAs? String "name")).toOption.getD ""
  | _ => (d.getObjValAs? String "name").toOption.getD ""

/-- A parsed module, checked: its locked import transcript is exactly the parsed one, and its
AST decodes to the elaborator's module. -/
def checkParsed (m : SourceModule) (ast : Json) : Except Diagnostic Syntax.Module := do
  let parsed := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let locked := m.imports.toArray.map fun i =>
    Json.mkObj [("path", toJson i.path), ("alias", toJson i.importAlias), ("span", i.span)]
  if (Json.arr parsed).compress != (Json.arr locked).compress then
    throw (elaborationRefusal "import transcript differs from parsed imports")
  match Syntax.decodeModule (Json.mkObj [("name", toJson m.name),
      ("imports", Json.arr (m.imports.map fun i =>
        Json.mkObj [("alias", toJson i.importAlias), ("moduleName", toJson i.moduleName)]).toArray), ("ast", ast)]) with
  | .ok d => pure d
  | .error e => throw (elaborationRefusal e)

def parseSource (name source : String) : Except Diagnostic Json :=
  match Parse.parseObjective source with
  | .ok ast => pure ast
  | .error d => throw { stage := "objective-source-parse", message := d.message, span := d.span, sourceModule := some name }

/-- Parse one module and check it (`checkParsed`). -/
def parseModule (m : SourceModule) : Except Diagnostic Syntax.Module := do
  checkParsed m (← parseSource m.name m.source)

/-! ## Lowering -/

/-- `^[1-9][0-9]*$` with a value cap. -/
def positive (value : Json) (cap : Nat) : Option Nat := do
  let text ← value.getStr?.toOption
  let n ← text.toNat?
  if n == 0 || toString n != text || n > cap then none else some n

/-- The typed-core packet fields around a typing proposal for `term`, `context` empty. -/
def packetJson (proposal : Json) (term : ATerm) (sourceEntry : String) (modules : List SourceModule)
    (checkWork : Nat) : Json :=
  let field (k : String) := (proposal.getObjVal? k).toOption.getD .null
  Json.mkObj [("schema", toJson "dregg.objective-bend.typed-core.v3"), ("term", term.json),
    ("types", field "types"), ("annotations", field "annotations"), ("bounds", field "bounds"),
    ("shareableVariables", field "shareableVariables"), ("fuel", toJson (toString checkWork)),
    ("context", Json.arr #[]), ("sourceEntry", toJson sourceEntry),
    ("sourceModules", Json.arr (modules.map SourceModule.binding).toArray),
    ("status", toJson "exact core annotation proposal; actual checker must return Checked; no law proof or effect authority")]

/-! ## Templates: each open declaration checked once against its bounds alone (D2) -/

/-- The context every knot field is checked in: `$seed : {}` then `$globals : the knot`. -/
def knotContext : Obend.Core.Ty.Context :=
  [⟨.emptyRow, .unrestricted⟩, ⟨.variable 0, .unrestricted⟩]

/-- OB-LTUO LT2 D2. An open declaration's knot field is its template at its own bounds. It is
checked here by the checker with its `Self` variable RIGID: `Self`'s bound is a lower bound
(members are read through it) and never an alias, so a body that uses `self` where a value
of exactly its bound row is expected, which the alias checker of the whole program would
accept and only a wider instance would refuse, is refused HERE, naming the declaration.
`Obend.Core.Proofs.Templates.Discharges.check_instantiate` is what a template accepted
here buys: acceptance at every instance whose bounds are discharged. -/
def checkTemplate (output : Output) (sourceEntry : String) (modules : List SourceModule) (checkWork : Nat)
    (key : String) (rigidVariables : List Nat) (field : ATerm) : Except Diagnostic Unit := do
  let refuse := fun (why : String) =>
    (throw (elaborationRefusal why) : Except Diagnostic Unit)
  let proposal ← match Elaborate.proposalJson { output with term := field } with
    | .ok proposal => pure proposal
    | .error e => throw (elaborationRefusal ("refused (template-typing): open declaration " ++ key ++
        " has no typed template: " ++ e))
  let packet ← match decodePacket (packetJson proposal field sourceEntry modules checkWork) with
    | .ok packet => pure packet
    | .error e => throw (elaborationRefusal ("refused (template-typing): open declaration " ++ key ++
        " has no typed template: " ++ e))
  let source := packet.source
  let rigidAt := fun (vars : List Nat) => { source with assumptions := { source.assumptions with rigid := vars } }
  match check (rigidAt rigidVariables) knotContext packet.fuel with
  | some _ => pure ()
  | none =>
    -- Which variable only an alias would accept: Self (the first) or Super (the second).
    if (check (rigidAt (rigidVariables.take 1)) knotContext packet.fuel).isSome then
      refuse ("refused (super-rigid): open declaration " ++ key ++ " uses super as a value of its " ++
        "Super bound row; Super ranges over every row beneath that HAS those members (a lower bound), so " ++
        "a value of type Super is not a value of the bound row. Read the members it needs (super.m), or " ++
        "extend super (Super with {...})")
    else
    match check source knotContext packet.fuel with
    | some _ => refuse ("refused (self-rigid): open declaration " ++ key ++ " uses self as a value of its " ++
        "Self bound row; Self ranges over every type that HAS that row (a lower bound), so a value of type " ++
        "Self is not a value of the row. Read the members it needs (self.m) instead")
    | none => refuse ("refused (template-typing): open declaration " ++ key ++
        " does not type-check against its declared bounds")

def checkTemplates (output : Output) (sourceEntry : String) (modules : List SourceModule) (checkWork : Nat) :
    Except Diagnostic Unit :=
  output.templates.forM fun (key, rigidVariables, field) => checkTemplate output sourceEntry modules checkWork key rigidVariables field

structure Lowering where
  output : Output
  /-- The selected term after projections: what the core and the packet carry. -/
  term : ATerm
  sourceEntry : String
  argumentCodec : String
  mode : String
  modules : List SourceModule
  limits : Json
  checkWork : Nat
  /-- The package's enforced laws: the entry module's top-level `law` declarations (a law in any
  other module refuses). The artifact commits them; the kernel installs them on every object
  pinned to the artifact. -/
  laws : List (String × Law.LawExpr)

def project (term : ATerm) (projections : List Json) : Except Diagnostic ATerm :=
  projections.foldlM (init := term) fun t p => do
    let t := match (p.getObjValAs? String "field").toOption with
      | some field => if field.isEmpty then t else ATerm.get t field
      | none => t
    match p.getObjVal? "argument" with
    | .ok (.str n) =>
      if Elaborate.isCanonicalNat n then pure (ATerm.app t (.nat n))
      else throw (elaborationRefusal "projection argument must be canonical Nat")
    | .ok _ => throw (elaborationRefusal "projection argument must be canonical Nat")
    | .error _ => pure t

/-- The default checker work grant, and its ceiling (`Obend.Elab.Work.checkWork` units). -/
def defaultCheckWork : Nat := 65536
def maxCheckWork : Nat := 1048576

/-- Selection mode, projections and limits: `limits` carries `heap`/`stack`/`ticks` (canonical
positive, at most 1000000) and an optional `checkWork` (at most `maxCheckWork`, default
`defaultCheckWork`), the checker's work grant, which travels in the packet. The historical
`typeFuel` (Mini's nesting fuel) is refused by name. Returns the projections and the grant. -/
def options (projections limits : Json) (mode : String) : Except Diagnostic (List Json × Nat) := do
  if mode != "application" && mode != "definition" then
    throw (elaborationRefusal "selection mode must be application or definition")
  let projectionList ← match projections.getArr? with
    | .ok a => pure a.toList
    | .error _ => throw (elaborationRefusal "projections must be an array")
  if mode == "definition" && !projectionList.isEmpty then
    throw (elaborationRefusal "definition mode forbids result projections")
  for key in ["heap", "stack", "ticks"] do
    if (positive ((limits.getObjVal? key).toOption.getD .null) 1000000).isNone then
      throw (elaborationRefusal "preview limits must be canonical positive decimal strings ≤1000000")
  if (limits.getObjVal? "typeFuel").toOption.isSome then
    throw (elaborationRefusal "typeFuel is retired: the checker's grant is limits.checkWork, its work (one per term node plus the annotation types it reads)")
  let grant ← match limits.getObjVal? "checkWork" with
    | .error _ => pure defaultCheckWork
    | .ok v => match positive v maxCheckWork with
      | some n => pure n
      | none => throw (elaborationRefusal s!"checkWork must be a canonical positive decimal string ≤{maxCheckWork}")
  return (projectionList, grant)

/-- The front end on parsed, checked modules: elaborate the selected declaration and project. -/
def lowerDecoded (modules : List SourceModule) (decoded : List Syntax.Module)
    (entryModule : Nat) (entryDefinition : String) (args projections limits : Json) (mode : String) :
    Except Diagnostic Lowering := do
  let (projectionList, checkWork) ← options projections limits mode
  if modules.length > 64 then throw (elaborationRefusal "preview module capacity refused")
  let output ← match Elaborate.elaborate decoded entryModule entryDefinition args mode with
    | .ok o => pure o
    | .error e => throw (elaborationRefusal e)
  let term ← project output.term projectionList
  let some entry := modules[entryModule]? | throw (elaborationRefusal "missing selected entry")
  let argumentCodec := if mode == "definition" then "unapplied-definition"
    else match args with
      | .arr _ => "legacy-canonical-nat-bool-record"
      | _ => "dregg.objective-bend.argument-values.v1"
  checkTemplates output (entry.name ++ "." ++ entryDefinition) modules checkWork
  for (m, index) in decoded.zipIdx do
    if index != entryModule && !m.laws.isEmpty then
      throw (elaborationRefusal ("a law belongs to the package's entry module; " ++ m.name ++
        " is imported and declares " ++ toString m.laws.length ++ " law(s)"))
  let laws := (decoded[entryModule]?.map (·.laws)).getD []
  return ⟨output, term, entry.name ++ "." ++ entryDefinition, argumentCodec, mode, modules, limits, checkWork, laws⟩

/-- The whole front end on read modules: options, parse and check every module, elaborate,
project. -/
def lower (modules : List SourceModule) (entryModule : Nat) (entryDefinition : String)
    (args projections limits : Json) (mode : String) : Except Diagnostic Lowering := do
  discard <| options projections limits mode
  let decoded ← modules.mapM parseModule
  lowerDecoded modules decoded entryModule entryDefinition args projections limits mode

/-- The package's enforced laws as the Law terms a kernel installs on an object whose declared
state type is `S`: each `law NAME: EXPR` compiled to a closed Core4 law of type `lawTy S`
(`Obend.Spec.LawCompile.compile`; it admits exactly what `denote` admits and checks at `lawTy S`,
`Obend.Spec.Proofs.LawCompile`). The package is named by its source entry: a relaw of one of its
laws is refused naming it, since a package law changes by a package upgrade, not a relaw. -/
def Lowering.lawTerms (l : Lowering) (S : Obend.Core.Ty.Ty) : List (String × Obend.Core.Term.Term) :=
  LawCompile.compilePackage S l.sourceEntry l.laws

def Lowering.core (l : Lowering) : Json :=
  Json.mkObj [("schema", toJson "dregg.objective-bend.core.v2"), ("edition", toJson "objective-bend-1"),
    ("term", l.term.json), ("sourceEntry", toJson l.sourceEntry), ("argumentCodec", toJson l.argumentCodec),
    ("selectionMode", toJson l.mode), ("sourceModules", Json.arr (l.modules.map SourceModule.binding).toArray),
    ("status", toJson "elaborated executable term; typing is checked by the actual checker, adequacy in ObjectiveBendFrontEndAdequacy"),
    ("limits", l.limits)]

/-- The typing proposal for the selected term, or why there is none. -/
def Lowering.proposal (l : Lowering) : Except String Json :=
  Elaborate.proposalJson { l.output with term := l.term }

/-- `dregg.objective-bend.typed-core.v3`: exactly the packet the checker reads. An unsupported
proposal is `{status: "unsupported", message}`. -/
def Lowering.packet (l : Lowering) : Json :=
  match l.proposal with
  | .error message => Json.mkObj [("status", toJson "unsupported"), ("message", toJson message)]
  | .ok proposal => packetJson proposal l.term l.sourceEntry l.modules l.checkWork

/-! ## Acceptance: the checker on the front end's own packet -/

/-- The front end's packet, decoded by the checker's decoder: its annotations and assumptions
type the erasure of the elaborator's term, and the proof-producing checker accepted that
term closed. The packet's own term IS that erasure (`Obend.Spec.Proofs.TermWire.Accepted.packetTerm`,
by `decode_json` from `shallow`, `erasure` and `decoded`), so the checker typed exactly what the
packet carries. -/
structure Accepted (l : Lowering) where
  erased : CoreTerm
  erasure : l.term.erase = .ok erased
  proposal : Json
  proposed : l.proposal = .ok proposal
  /-- The selected term is within the decoder's nesting capacity (what `decode_json` needs). -/
  shallow : Annotated.depth l.term ≤ Obend.Core.Packet.termNestingCapacity
  packet : DecodedPacket
  decoded : decodePacket l.packet = .ok packet
  closed : packet.context = []
  /-- The gate's verdict on the decoded packet: preparation, with the packet's annotations as
  hints, then `Bidirectional.checkAgainst` (`Obend.Elab.Gate.admit`). -/
  admitted : Obend.Elab.Gate.Admitted { packet.source with term := erased } [] packet.fuel
  admittedExact : Obend.Elab.Gate.admitSource { packet.source with term := erased } [] packet.fuel = .ok admitted
  /-- The checked source: the prepared annotations and the packet's assumptions on the
  elaborator's erased term. -/
  source : Obend.Core.Check.AnnotatedTerm
  sourceExact : source = { packet.source with term := erased, annotations := admitted.annotations }
  typed : Checked source []

def accept (l : Lowering) : Except Diagnostic (Accepted l) := do
  match erasure : l.term.erase with
  | .error e => throw (elaborationRefusal ("core erasure: " ++ e))
  | .ok erased =>
    match proposed : l.proposal with
    | .error message => throw { stage := "objective-source-type-proposal", message }
    | .ok proposal =>
      if shallow : Annotated.depth l.term ≤ Obend.Core.Packet.termNestingCapacity then
        match decoded : decodePacket l.packet with
        | .error e =>
          throw { stage := "objective-source-type-proposal", message := "typed packet does not decode: " ++ e }
        | .ok packet =>
          if closed : packet.context = [] then
            match admittedExact : Obend.Elab.Gate.admitSource { packet.source with term := erased } [] packet.fuel with
            | .ok admitted =>
              let source := { packet.source with term := erased, annotations := admitted.annotations }
              let typed : Checked source [] := admitted.checked
              pure ⟨erased, erasure, proposal, proposed, shallow, packet, decoded, closed, admitted, admittedExact,
                source, rfl, typed⟩
            | .error _ => throw { stage := "objective-typed-check", message := "the checker refused the front end's typed packet" }
          else throw (elaborationRefusal "typed packet context must be closed")
      else throw (elaborationRefusal "core term nesting exceeds the checker's decoding capacity")

end Obend.Spec.FrontEnd

end
