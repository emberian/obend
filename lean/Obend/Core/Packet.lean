module
/-
# Obend.Core.Packet — typed-core packets on the wire: decode, check, receipt

The JSON edition `dregg.objective-bend.typed-core.v3` (a term, a type table, lambda annotations by
position, bounds, shareability premises, a context, the checker fuel), decoded into an
`AnnotatedTerm` with its context (`decodePacket`), checked (`packetReceipt`), and the kind of rule a
refused packet broke, read off the SAME checker on two variations of the packet (`refusalKind`: ample
fuel, then every quantity unrestricted). `checkPacketFile` is the native entry point the `obend`
executable calls. Split out of `Obend.Core.Check` on 2026-10-30 so the checker's module holds the
checker: no proof reads the wire. The teeth on `refusalKind` are in `Obend.Core.Proofs.CheckTeeth`.
-/
public import Obend.Core.Ty
public import Obend.Core.Term
public import Obend.Core.Check
@[expose] public section
namespace Obend.Core.Packet
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

open Lean (Json toJson)

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

def jsonNat (value : Json) : Except String Nat :=
  match value.getNat? with
  | .ok result => .ok result
  | .error _ => do
      let text ← value.getStr?
      let result ← requireSome "canonical natural required" text.toNat?
      if toString result = text then .ok result else .error "canonical natural required"

def decodeQuantity (value : Json) : Except String Quantity := do
  match ← value.getStr? with
  | "erased" => pure .erased | "affine" => pure .affine
  | "linear" => pure .linear | "unrestricted" => pure .unrestricted
  | _ => .error "explicit Objective quantity required"

def decodeReuse (value : Json) : Except String Reuse := do
  match ← value.getStr? with
  | "once" => pure .once | "reusable" => pure .reusable
  | _ => .error "explicit Objective closure reuse required"

/-- A type on the wire, with its depth. A type is an object `{tag, ...}` whose children
are types, or `{tag:"ref", index}` naming an EARLIER entry of the packet's type table
(`decodeTypeTable`). A ref stands for exactly the type the entry decoded to, depth
included: `decodeTypeWith table fuel` accepts a tree iff the fully inlined JSON of that
tree is accepted by `decodeTypeWith #[] fuel`, and decodes it to the same `Ty`. The table
only shares storage; it changes neither which types a proposal may name nor the
nesting capacity. -/
def decodeTypeWith (table : Array (Ty × Nat)) : Nat → Json → Except String (Ty × Nat)
  | 0, _ => .error "type nesting capacity"
  | fuel + 1, value => do
    match ← value.getObjValAs? String "tag" with
    | "ref" =>
        let index ← jsonNat (← value.getObjVal? "index")
        let some (entry, depth) := table[index]? | .error "type reference names no earlier table entry"
        if depth > fuel + 1 then throw "type nesting capacity"
        pure (entry, depth)
    | "natural" => pure (.natural, 1) | "label" => pure (.label, 1)
    | "boolean" => pure (.boolean, 1) | "emptyRow" => pure (.emptyRow, 1)
    | "variable" => return (.variable (← jsonNat (← value.getObjVal? "index")), 1)
    | "custody" => return (.custody (← jsonNat (← value.getObjVal? "identity")), 1)
    | "field" =>
        let (member, dm) ← decodeTypeWith table fuel (← value.getObjVal? "member")
        let (tail, dt) ← decodeTypeWith table fuel (← value.getObjVal? "tail")
        return (.field (← value.getObjValAs? String "name") member tail, max dm dt + 1)
    | "arrow" =>
        let (domain, dd) ← decodeTypeWith table fuel (← value.getObjVal? "domain")
        let (codomain, dc) ← decodeTypeWith table fuel (← value.getObjVal? "codomain")
        return (.arrow (← decodeReuse (← value.getObjVal? "reuse"))
          (← decodeQuantity (← value.getObjVal? "parameter")) domain codomain, max dd dc + 1)
    | "specification" =>
        let (metadata, dm) ← decodeTypeWith table fuel (← value.getObjVal? "metadata")
        let (extension, de) ← decodeTypeWith table fuel (← value.getObjVal? "extension")
        return (.specification metadata extension, max dm de + 1)
    | "prototype" =>
        let (spec, ds) ← decodeTypeWith table fuel (← value.getObjVal? "spec")
        let (target, dt) ← decodeTypeWith table fuel (← value.getObjVal? "target")
        return (.prototype spec target, max ds dt + 1)
    | "variant" =>
        let (row, dr) ← decodeTypeWith table fuel (← value.getObjVal? "row")
        return (.variant row, dr + 1)
    | "computation" =>
        let (plan, dp) ← decodeTypeWith table fuel (← value.getObjVal? "plan")
        let (response, dr) ← decodeTypeWith table fuel (← value.getObjVal? "response")
        let (result, da) ← decodeTypeWith table fuel (← value.getObjVal? "result")
        return (.computation plan response result, max dp (max dr da) + 1)
    | _ => .error "unknown Objective type constructor"

/-- The type nesting capacity of every type a proposal names, tabled or inline. -/
def typeNestingCapacity : Nat := 256

def decodeType (table : Array (Ty × Nat)) (value : Json) : Except String Ty := do
  return (← decodeTypeWith table typeNestingCapacity value).1

/-- The packet's type table: entry k is decoded against entries 0..k-1 only, so a ref can
never point forward or at itself and every entry is a finite tree. -/
def decodeTypeTable (value : Json) : Except String (Array (Ty × Nat)) := do
  let entries ← value.getArr?
  if entries.size > 1048576 then throw "type table capacity"
  entries.foldlM (fun table entry => do
    pure (table.push (← decodeTypeWith table typeNestingCapacity entry))) #[]

def decodePrimitive (value : Json) : Except String Primitive := do
  match ← value.getStr? with
  | "add" => pure .add | "multiply" => pure .multiply
  | "equal" => pure .equal | "conjunction" => pure .conjunction
  | "labelEqual" => pure .labelEqual
  | "subtract" => pure .subtract | "divide" => pure .divide
  | "less" => pure .less | "lessEqual" => pure .lessEqual | "modulo" => pure .modulo
  | _ => .error "unknown Objective primitive"

/-- Decodes exactly the existing world lowerer's runtime core wire; no second
source translator or alternate fixture term is introduced by the type checker. -/
def decodeTerm : Nat → Json → Except String Term
  | 0, _ => .error "term nesting capacity"
  | fuel + 1, value => do
    let sub := fun key => do decodeTerm fuel (← value.getObjVal? key)
    let fields := fun (_ : Unit) => do
      let array ← (← value.getObjVal? "fields").getArr?
      array.toList.mapM fun field => do
        return (← field.getObjValAs? String "name", ← decodeTerm fuel (← field.getObjVal? "value"))
    match ← value.getObjValAs? String "tag" with
    | "bound" => return .bound (← jsonNat (← value.getObjVal? "index"))
    | "nat" => return .nat (← jsonNat (← value.getObjVal? "value"))
    | "boolean" => return .boolean (← value.getObjValAs? Bool "value")
    | "label" => return .label (← value.getObjValAs? String "value")
    | "lam" => return .lam (← sub "body")
    | "app" => return .app (← sub "fn") (← sub "arg")
    | "mix" => return .mix (← sub "lower") (← sub "upper")
    | "fix" => return .fix (← sub "spec") (← sub "seed")
    | "specification" => return .specification (← sub "metadata") (← sub "extension")
    | "prototype" => return .prototype (← sub "spec") (← sub "target")
    | "reflect" => return .reflect (← sub "value")
    | "metadata" => return .metadata (← sub "value")
    | "project" => return .project (← sub "value")
    | "binary" => return .binary (← decodePrimitive (← value.getObjVal? "primitive")) (← sub "left") (← sub "right")
    | "record" => return .record (← fields ())
    | "extend" => return .extend (← sub "inherited") (← fields ())
    | "get" => return .get (← sub "target") (← value.getObjValAs? String "name")
    | "ifZero" => return .ifZero (← sub "value") (← sub "zero") (← sub "successor")
    | "inject" => return .inject (← value.getObjValAs? String "label") (← sub "payload")
    | "case" => do
        let array ← (← value.getObjVal? "arms").getArr?
        let arms ← array.toList.mapM fun arm => do
          return (← arm.getObjValAs? String "label", ← decodeTerm fuel (← arm.getObjVal? "body"))
        return .case (← sub "scrutinee") arms
    | "ifBool" => return .ifBool (← sub "condition") (← sub "whenTrue") (← sub "whenFalse")
    | "perform" => return .perform (← sub "plan")
    | "done" => return .done (← sub "value")
    | _ => .error "unknown Objective runtime constructor"

def decodeLambda (table : Array (Ty × Nat)) (value : Json) : Except String LambdaAnnotation := do
  return ⟨← decodeType table (← value.getObjVal? "domain"),
    ← decodeType table (← value.getObjVal? "codomain"),
    ← decodeQuantity (← value.getObjVal? "parameter"),
    ← decodeReuse (← value.getObjVal? "reuse")⟩

structure DecodedPacket where
  source : AnnotatedTerm
  context : Context
  fuel : Nat

/-- Everything a packet carries besides its term. -/
structure PacketParts where
  annotations : List Nat → Option LambdaAnnotation
  assumptions : Assumptions
  context : Context
  fuel : Nat

/-- The term nesting capacity of a packet's term (`decodeTerm`'s fuel). -/
def termNestingCapacity : Nat := 4096

def decodePacketParts (value : Json) (table : Array (Ty × Nat)) : Except String PacketParts := do
  let annotations ← (← (← value.getObjVal? "annotations").getArr?).toList.mapM fun entry => do
    let path ← (← (← entry.getObjVal? "path").getArr?).toList.mapM jsonNat
    return (path, ← decodeLambda table entry)
  if !decide (annotations.map Prod.fst).Nodup then throw "duplicate lambda annotation path"
  let bounds ← (← (← value.getObjVal? "bounds").getArr?).toList.mapM fun entry => do
    return (← jsonNat (← entry.getObjVal? "index"), ← decodeType table (← entry.getObjVal? "type"))
  if !decide (bounds.map Prod.fst).Nodup then throw "duplicate future type bound"
  let shareable ← (← (← value.getObjVal? "shareableVariables").getArr?).toList.mapM jsonNat
  if !decide shareable.Nodup then throw "duplicate shareability premise"
  let context ← match value.getObjVal? "context" with
    | .error _ => pure []
    | .ok context => (← context.getArr?).toList.mapM fun entry => do
        return (⟨← decodeType table (← entry.getObjVal? "type"),
          ← decodeQuantity (← entry.getObjVal? "quantity")⟩ : Binding)
  -- the checker's grant: the front end's `limits.checkWork` (`Obend.Elab.Work.checkWork` units)
  let fuel ← match value.getObjVal? "fuel" with
    | .error _ => pure 65536
    | .ok fuel => jsonNat fuel
  if fuel > 1048576 then throw "checker work grant capacity"
  return ⟨fun path => (annotations.find? (fun entry => entry.1 == path)).map Prod.snd,
      ⟨bounds,shareable,[]⟩,context,fuel⟩

/-- Schema, type table, term, then the rest (`decodePacketParts`), in that order. -/
def decodePacket (value : Json) : Except String DecodedPacket := do
  if (← value.getObjValAs? String "schema") != "dregg.objective-bend.typed-core.v3" then
    throw "Objective typed core edition required"
  let table ← decodeTypeTable (← value.getObjVal? "types")
  let term ← decodeTerm termNestingCapacity (← value.getObjVal? "term")
  let parts ← decodePacketParts value table
  return ⟨⟨term, parts.annotations, parts.assumptions⟩, parts.context, parts.fuel⟩

def quantityJson : Quantity → Json
  | .erased => toJson "erased" | .affine => toJson "affine"
  | .linear => toJson "linear" | .unrestricted => toJson "unrestricted"
def reuseJson : Reuse → Json
  | .once => toJson "once" | .reusable => toJson "reusable"

def typeJson : Ty → Json
  | .natural => Json.mkObj [("tag",toJson "natural")]
  | .label => Json.mkObj [("tag",toJson "label")]
  | .boolean => Json.mkObj [("tag",toJson "boolean")]
  | .emptyRow => Json.mkObj [("tag",toJson "emptyRow")]
  | .variable index => Json.mkObj [("tag",toJson "variable"),("index",toJson (toString index))]
  | .custody identity => Json.mkObj [("tag",toJson "custody"),("identity",toJson (toString identity))]
  | .field name member tail => Json.mkObj [("tag",toJson "field"),("name",toJson name),
      ("member",typeJson member),("tail",typeJson tail)]
  | .arrow reuse quantity domain codomain => Json.mkObj [("tag",toJson "arrow"),
      ("reuse",reuseJson reuse),("parameter",quantityJson quantity),
      ("domain",typeJson domain),("codomain",typeJson codomain)]
  | .specification metadata extension => Json.mkObj [("tag",toJson "specification"),
      ("metadata",typeJson metadata),("extension",typeJson extension)]
  | .prototype spec target => Json.mkObj [("tag",toJson "prototype"),
      ("spec",typeJson spec),("target",typeJson target)]
  | .variant row => Json.mkObj [("tag",toJson "variant"),("row",typeJson row)]
  | .computation plan response result => Json.mkObj [("tag",toJson "computation"),
      ("plan",typeJson plan),("response",typeJson response),("result",typeJson result)]

/-- Every quantity in a type made `unrestricted` (arrow parameters at any depth). -/
def unrestrictedTy : Ty → Ty
  | .arrow reuse _ domain codomain => .arrow reuse .unrestricted (unrestrictedTy domain) (unrestrictedTy codomain)
  | .field name member tail => .field name (unrestrictedTy member) (unrestrictedTy tail)
  | .specification metadata extension => .specification (unrestrictedTy metadata) (unrestrictedTy extension)
  | .prototype spec target => .prototype (unrestrictedTy spec) (unrestrictedTy target)
  | .variant row => .variant (unrestrictedTy row)
  | .computation plan response result =>
      .computation (unrestrictedTy plan) (unrestrictedTy response) (unrestrictedTy result)
  | other => other

/-- The kind of rule a refused packet broke. -/
inductive RefusalKind where
  | budget | ownership | typing
  deriving Repr, DecidableEq

/-- Type fuel that bounds only the checker's depth, generous enough that a
program refused with it was not refused for depth. -/
def ampleFuel (fuel : Nat) : Nat := max (fuel * 4) 65536

/-- The same packet with every quantity relaxed to `unrestricted`: lambda
parameters, every arrow in the declared types and bounds, and the context. -/
def relaxQuantities (packet : DecodedPacket) : DecodedPacket :=
  let relaxAnnotation := fun (annotation : LambdaAnnotation) =>
    ({ domain := unrestrictedTy annotation.domain, codomain := unrestrictedTy annotation.codomain,
       parameter := .unrestricted, reuse := annotation.reuse } : LambdaAnnotation)
  { source :=
      { term := packet.source.term,
        annotations := fun position => (packet.source.annotations position).map relaxAnnotation,
        assumptions := { packet.source.assumptions with
          bounds := packet.source.assumptions.bounds.map fun entry => (entry.1, unrestrictedTy entry.2) } },
    context := packet.context.map fun binding =>
      ({ type := unrestrictedTy binding.type, quantity := .unrestricted } : Binding),
    fuel := packet.fuel }

/-- The checker answers accepted or refused; it does not name the rule. To say
which KIND of rule refused, this re-runs the SAME checker on two variations of
the same packet, in order: (1) ample fuel — if that accepts, the refusal was
the checker budget; (2) every quantity relaxed to `unrestricted` — if that
accepts, the refusal was ownership (an affine or linear binding used more than
once, or captured by a closure that may run again). Otherwise it was a typing
or activity rule. No second checker is written: the classification is what the
real checker says about the variations. Meaningful only for a packet `check`
refused. -/
def refusalKind (packet : DecodedPacket) : RefusalKind :=
  if (check packet.source packet.context (ampleFuel packet.fuel)).isSome then .budget
  else
    let relaxed := relaxQuantities packet
    if (check relaxed.source relaxed.context relaxed.fuel).isSome then .ownership else .typing

def refusalReason (packet : DecodedPacket) : String :=
  match refusalKind packet with
  | .budget => s!"checker budget refused: typeFuel {packet.fuel} is too small for this program (it checks with {ampleFuel packet.fuel}); raise limits.typeFuel"
  | .ownership => "ownership refused: an affine or linear parameter is used more than once (both mean at most once), or one is captured by a closure that may run again (the program checks with every quantity unrestricted)"
  | .typing => "typing refused: types disagree, a custody value is shared or captured, or an activity rule (an Activity is refused as an argument, record/extend field, specification or prototype component, or sum payload; a Plan must be a sum of first-order data; a response must be first-order data)"

def packetReceipt (value : Json) : Except String Json := do
  let packet ← decodePacket value
  let result ← requireSome (refusalReason packet) (check packet.source packet.context packet.fuel)
  return Json.mkObj [
    ("schema", toJson "dregg.objective-bend.typing-receipt.v1"),
    ("status", toJson "accepted"),
    ("type", typeJson result.type), ("uses", toJson result.uses),
    ("typingScope", toJson "compiled proof-producing annotated partial checker; preservation and demand adequacy separate"),
    ("laws", toJson "undischarged unless independent total law providers are supplied"),
    ("authority", toJson "no current native authority granted")]

/-- Native entry point for the exact core packet produced by the world lowerer.
Its executable result relies on Lean compilation; it is not a kernel certificate
for the parsed bytes or an executor/authority qualification. -/
def checkPacketFile (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let result := do
    let parsed ← Json.parse input
    packetReceipt parsed
  match result with
  | .ok receipt => IO.println receipt.compress; return 0
  | .error message =>
      IO.eprintln (Json.mkObj [("schema",toJson "dregg.objective-bend.typing-receipt.v1"),
        ("status",toJson "refused"),("stage",toJson "objective-source-type-check"),("message",toJson message)]).compress
      return 2

end Obend.Core.Packet
end
