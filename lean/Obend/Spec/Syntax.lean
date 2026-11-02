module
/-
# Obend.Spec.Syntax — the surface AST of an Objective Bend module, and its decoder

The parser (`Obend.Spec.Parse`) emits the `dregg.objective-bend.module.v1` AST as JSON, the shape
the retired TypeScript parser emitted; the elaborator (`Obend.Spec.Elaborate`) reads the Lean AST
below. `decodeModule` is the one step between them. Ported from the "Surface AST" and "Decoding"
sections of minidregg `Compiler/ObjectiveBendElaborate.lean` (commit 092027a2), split out so the
AST is a leaf the elaborator, the front end and the tests can import without the elaborator.
-/
public import Lean
public import Obend.Spec.Law
public section
namespace Obend.Spec.Syntax
open Lean
set_option autoImplicit false

/-! String helpers (ASCII whitespace, as the TS `trim`). -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
def trimStart (s : String) : String := String.ofList (s.toList.dropWhile isSpace)
def trimEnd (s : String) : String := String.ofList ((s.toList.reverse.dropWhile isSpace).reverse)
def trimStr (s : String) : String := trimEnd (trimStart s)
def dropStr (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def dropEndStr (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

/-! ## Surface AST -/

structure Param where
  name : String
  type : String
  quantity : String
  deriving Inhabited, Repr

inductive Expr where
  | var (name : String)
  | nat (value : String)
  | bool (value : Bool)
  | str (value : String)
  | unit
  | record (fields : List (String × Expr))
  | extend (inherited : Expr) (fields : List (String × Expr))
  | member (target : Expr) (name : String)
  | call (callee : Expr) (args : List Expr)
  | compose (specs : List Expr)
  | fix (spec inherited : Expr)
  | closure (params : List Param) (resultType : String) (body : Expr)
  | binary (op : String) (left right : Expr)
  | ite (condition whenTrue whenFalse : Expr)
  /-- `let name: type = value in body` (type `_` when unannotated). -/
  | letE (name type : String) (value body : Expr)
  deriving Inhabited, Repr

inductive Pattern where
  | zero | succ (binder : String) | wildcard | bool (value : Bool) | ctor (label binder : String)
  deriving Inhabited, Repr, BEq

inductive Body where
  | expr (e : Expr)
  | cases (scrutinee : Expr) (branches : List (Pattern × Body))
  /-- `let name: type = value` then the rest of the body. -/
  | letB (name type : String) (value : Expr) (body : Body)
  deriving Inhabited, Repr

structure Method where
  name : String
  params : List Param
  resultType : String
  qualifier : String
  body : Body
  /-- The authored signature (method JSON minus its body), for the interface label. -/
  signature : Json
  deriving Inhabited

/-- Isar-style structured proof/discharge method in `.obend` specifications, laws, and contracts. -/
inductive IsarMethod where
  | weave
  | frame
  | decide
  | omega
  | lean (decl : String)
  | judge (format : String)
  deriving Inhabited, Repr, BEq, DecidableEq

def IsarMethod.render : IsarMethod → String
  | .weave => "weave"
  | .frame => "frame"
  | .decide => "decide"
  | .omega => "omega"
  | .lean decl => "lean(" ++ decl ++ ")"
  | .judge fmt => "judge(" ++ fmt ++ ")"

def stripQuotes (s : String) : String :=
  let t := trimStr s
  if t.length >= 2 && t.startsWith "\"" && t.endsWith "\"" then
    dropEndStr (dropStr t 1) 1
  else t

def parseIsarMethod (raw : String) : Except String IsarMethod :=
  let s := trimStr raw
  if s == "weave" then .ok .weave
  else if s == "frame" then .ok .frame
  else if s == "decide" then .ok .decide
  else if s == "omega" then .ok .omega
  else if s.startsWith "lean(" && s.endsWith ")" then
    let inner := stripQuotes (dropEndStr (dropStr s 5) 1)
    if inner.isEmpty then .error "empty lean(...) justification"
    else .ok (.lean inner)
  else if s.startsWith "judge(" && s.endsWith ")" then
    let inner := stripQuotes (dropEndStr (dropStr s 6) 1)
    if inner.isEmpty then .error "empty judge(...) justification"
    else .ok (.judge inner)
  else .error ("unknown Isar proof method: " ++ s)

/-- A structured Isar proof step inside a claim or contract block. -/
inductive IsarStep where
  | haveStep (label : String) (prop : Expr) (method : IsarMethod)
  | showStep (prop : Expr) (method : IsarMethod)
  | obtainStep (binder : String) (prop : Expr) (method : IsarMethod)
  | byMethod (method : IsarMethod)
  deriving Inhabited, Repr

structure Claim where
  name : String
  params : List Param
  body : Expr
  /-- Optional Isar-style structured proof method (`by weave`, `by frame`, `by decide`,
      `by omega`, `by lean(...)`, `by judge(...)`). -/
  method : Option IsarMethod := none
  /-- Optional structured Isar proof steps (`have`, `show`, `obtain`). -/
  steps : List IsarStep := []
  deriving Inhabited

/-- Top-level `contract NAME for TARGET [by METHOD]:` block in `.obend`. -/
structure ContractDecl where
  name : String
  targetType : String
  invariant : Option Expr := none
  law : Option Law.LawExpr := none
  step : Option Expr := none
  method : Option IsarMethod := none
  steps : List IsarStep := []
  deriving Inhabited

structure Spec where
  name : String
  suffix : Bool
  parents : List String
  targetType : String
  requirements : Json
  methods : List Method
  claims : List Claim
  /-- `Self has {...}, Super has {...}` of an open spec (OB-LTUO LT2), "" for `spec S for T`. -/
  binders : String := ""
  deriving Inhabited

structure Signature where
  name : String
  params : List Param
  resultType : String
  deriving Inhabited

/-- One method of a protocol implementation: a function whose first parameter is the kind's
instance. -/
structure ProtocolMethod where
  name : String
  params : List Param
  resultType : String
  body : Body
  deriving Inhabited

/-- A parent root of a package: an intention (`NAME@^MAJOR`, resolved in a workspace's ecosystem
root) or an extension (`NAME@0xHASH`, fixed forever). -/
inductive ParentRef where
  | intention (name : String) (major : Nat)
  | extension (name : String) (hash : String)
  deriving Inhabited, Repr, BEq, DecidableEq

@[expose] def ParentRef.name : ParentRef → String
  | .intention n _ => n | .extension n _ => n

def ParentRef.text : ParentRef → String
  | .intention n major => n ++ "@^" ++ toString major
  | .extension n hash => n ++ "@0x" ++ hash

/-- `package NAME extends REF, ...`. -/
structure PackageHeader where
  name : String
  parents : List ParentRef
  deriving Inhabited, Repr

inductive Decl where
  | spec (s : Spec)
  | extension (name : String) (params : List Param) (targetType : String) (body : Body) (binders : String)
  | function (name : String) (params : List Param) (resultType : String) (body : Body)
  | record (name : String) (fields : List (String × String)) (methods : List Signature)
  | sum (name : String) (cases : List (String × String))
  /-- `protocol GENERIC for KIND:`; expanded into functions before elaboration
  (`Obend.Spec.Elaborate.expandProtocols`). -/
  | protocol (generic kind : String) (methods : List ProtocolMethod)
  deriving Inhabited

def Decl.name : Decl → String
  | .spec s => s.name | .extension n .. => n | .function n .. => n | .record n .. => n | .sum n .. => n
  | .protocol g k _ => "protocol " ++ g ++ " for " ++ k

def Decl.binders : Decl → String
  | .spec s => s.binders
  | .extension _ _ _ _ b => b
  | _ => ""

structure Module where
  name : String
  /-- (alias, imported module name) in source order. -/
  imports : List (String × String)
  decls : List Decl
  /-- The module's top-level enforced laws (`law NAME: EXPR`), in source order. They are not
  terms: the elaborator never sees them; the front end hands the entry module's to the artifact. -/
  laws : List (String × Law.LawExpr) := []
  /-- `package NAME extends ...`, when this module is a package's root module. -/
  header : Option PackageHeader := none
  /-- `keeps INV by LAW` lines: the law `LAW` of this module keeps the invariant `INV`
  (`Law.Claim.keeps`), an obligation `obend check --obligations` lists. -/
  keeps : List (String × String) := []
  /-- Optional Isar-style justification methods on top-level `law NAME [by METHOD]: EXPR` declarations. -/
  lawMethods : List (String × IsarMethod) := []
  /-- Top-level `contract NAME for TARGET [by METHOD]:` declarations. -/
  contracts : List ContractDecl := []
  deriving Inhabited

/-! ## Decoding the parser's AST JSON -/

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def arr (j : Json) (k : String) : Except String (List Json) := do return (← (← j.getObjVal? k).getArr?).toList

def decodeParam (j : Json) : Except String Param := do
  return ⟨← str j "name", (← str j "type"), (j.getObjValAs? String "quantity").toOption.getD "default"⟩

mutual
def decodeExpr : Nat → Json → Except String Expr
  | 0, _ => .error "AST nesting capacity"
  | fuel + 1, j => do
    let fields := fun (key : String) => do
      (← arr j key).mapM fun f => do return (← str f "name", ← decodeExpr fuel (← f.getObjVal? "value"))
    let sub := fun (key : String) => do decodeExpr fuel (← j.getObjVal? key)
    match ← str j "kind" with
    | "var" => return .var (← str j "name")
    | "nat" => return .nat (← str j "value")
    | "bool" => return .bool (← j.getObjValAs? Bool "value")
    | "string" => return .str (← str j "value")
    | "unit" => return .unit
    | "record" => return .record (← fields "fields")
    | "extend" => return .extend (← sub "inherited") (← fields "fields")
    | "member" => return .member (← sub "target") (← str j "name")
    | "call" => return .call (← sub "callee") (← (← arr j "args").mapM (decodeExpr fuel))
    | "compose" => return .compose (← (← arr j "specifications").mapM (decodeExpr fuel))
    | "fix" => return .fix (← sub "specification") (← sub "inherited")
    | "extension-value" => return .closure (← (← arr j "parameters").mapM decodeParam) (← str j "targetType") (← sub "body")
    | "lambda" => return .closure (← (← arr j "parameters").mapM decodeParam) (← str j "resultType") (← sub "body")
    | "binary" => return .binary (← str j "op") (← sub "left") (← sub "right")
    | "if" => return .ite (← sub "condition") (← sub "whenTrue") (← sub "whenFalse")
    | "let" => return .letE (← str j "name") (← str j "type") (← sub "value") (← sub "body")
    | other => .error ("unknown AST expression " ++ other)

def decodeBody : Nat → Json → Except String Body
  | 0, _ => .error "AST nesting capacity"
  | fuel + 1, j => do
    match ← str j "kind" with
    | "expression" => return .expr (← decodeExpr fuel (← j.getObjVal? "expression"))
    | "match" =>
      let branches ← (← arr j "branches").mapM fun b => do
        let p ← b.getObjVal? "pattern"
        let binder := (p.getObjValAs? String "binder").toOption.getD "_"
        let pattern ← match ← str p "kind" with
          | "zero" => pure Pattern.zero
          | "succ" => pure (.succ binder)
          | "wildcard" => pure .wildcard
          | "bool" => pure (.bool (← p.getObjValAs? Bool "value"))
          | "constructor" => pure (.ctor (← str p "label") binder)
          | other => .error ("unknown pattern " ++ other)
        return (pattern, ← decodeBody fuel (← b.getObjVal? "body"))
      return .cases (← decodeExpr fuel (← j.getObjVal? "scrutinee")) branches
    | "let" =>
      let value ← decodeExpr fuel (← j.getObjVal? "value")
      let rest ← decodeBody fuel (← j.getObjVal? "body")
      return .letB (← str j "name") (← str j "type") value rest
    | other => .error ("unknown AST body " ++ other)
end

def decodeIsarStep (fuel : Nat) (j : Json) : Except String IsarStep := do
  let m ← parseIsarMethod (← str j "by")
  match ← str j "kind" with
  | "have" =>
    return .haveStep (← str j "label") (← decodeExpr fuel (← j.getObjVal? "prop")) m
  | "show" =>
    return .showStep (← decodeExpr fuel (← j.getObjVal? "prop")) m
  | "obtain" =>
    return .obtainStep (← str j "binder") (← decodeExpr fuel (← j.getObjVal? "prop")) m
  | "by" =>
    return .byMethod m
  | other => .error ("unknown Isar proof step " ++ other)

def decodeOptionalMethod (j : Json) : Except String (Option IsarMethod) := do
  match j.getObjValAs? String "by" with
  | .ok mStr =>
    if trimStr mStr == "" then return none
    else return some (← parseIsarMethod mStr)
  | .error _ => return none

def decodeOptionalSteps (fuel : Nat) (j : Json) : Except String (List IsarStep) := do
  match arr j "steps" with
  | .ok js => js.mapM (decodeIsarStep fuel)
  | .error _ => return []

def withoutKey (j : Json) (key : String) : Json :=
  match j with
  | .obj kvs => .obj (kvs.erase key)
  | other => other

def decodeSignature (j : Json) : Except String Signature := do
  return ⟨← str j "name", ← (← arr j "parameters").mapM decodeParam, ← str j "resultType"⟩

def decodeDecl (j : Json) : Except String Decl := do
  let fuel := 4096
  match ← str j "kind" with
  | "spec" =>
    let methods ← (← arr j "methods").mapM fun m => do
      let name ← str m "name"
      let params ← (← arr m "parameters").mapM decodeParam
      let resultType ← str m "resultType"
      let qualifier := (m.getObjValAs? String "qualifier").toOption.getD "primary"
      let body ← decodeBody fuel (← m.getObjVal? "body")
      return (Method.mk name params resultType qualifier body (withoutKey m "body"))
    let claims ← (← arr j "claims").mapM fun l => do
      let name ← str l "name"
      let params ← (← arr l "parameters").mapM decodeParam
      let body ← decodeExpr fuel (← l.getObjVal? "body")
      let method ← decodeOptionalMethod l
      let steps ← decodeOptionalSteps fuel l
      -- `claim … given COND: BODY` is `if COND then BODY else true`: no new elaboration.
      let fullBody ← match l.getObjVal? "given" with
        | .ok g => pure (.ite (← decodeExpr fuel g) body (.bool true))
        | .error _ => pure body
      return (Claim.mk name params fullBody method steps)
    let name ← str j "name"
    let suffix := (j.getObjValAs? Bool "suffix").toOption.getD false
    let parents ← (← arr j "parents").mapM (fun p => p.getStr?)
    let targetType ← str j "targetType"
    let requirements ← j.getObjVal? "requirements"
    let binders := (j.getObjValAs? String "binders").toOption.getD ""
    return .spec (Spec.mk name suffix parents targetType requirements methods claims binders)
  | "extension" =>
    let name ← str j "name"
    let params ← (← arr j "parameters").mapM decodeParam
    let targetType ← str j "targetType"
    let body ← decodeBody fuel (← j.getObjVal? "body")
    return .extension name params targetType body ((j.getObjValAs? String "binders").toOption.getD "")
  | "function" =>
    let s ← j.getObjVal? "signature"
    let name ← str s "name"
    let params ← (← arr s "parameters").mapM decodeParam
    let resultType ← str s "resultType"
    let body ← decodeBody fuel (← j.getObjVal? "body")
    return .function name params resultType body
  | "record" =>
    let name ← str j "name"
    let fields ← (← arr j "fields").mapM fun f => do return (← str f "name", ← str f "type")
    let methods ← (← arr j "methods").mapM decodeSignature
    return .record name fields methods
  | "sum" => return .sum (← str j "name") (← (← arr j "cases").mapM fun c => do return (← str c "label", ← str c "type"))
  | "protocol" =>
    let methods ← (← arr j "methods").mapM fun m => do
      return ProtocolMethod.mk (← str m "name") (← (← arr m "parameters").mapM decodeParam) (← str m "resultType")
        (← decodeBody fuel (← m.getObjVal? "body"))
    return .protocol (← str j "generic") (← str j "for") methods
  | other => .error ("unknown AST declaration " ++ other)

def decodeContractDecl (j : Json) : Except String ContractDecl := do
  let fuel := 4096
  let name ← str j "name"
  let targetType ← str j "targetType"
  let method ← decodeOptionalMethod j
  let steps ← decodeOptionalSteps fuel j
  let inv ← match j.getObjVal? "invariant" with
    | .ok invJ => pure (some (← decodeExpr fuel invJ))
    | .error _ => pure none
  let lawExpr ← match j.getObjValAs? String "law" with
    | .ok lStr =>
      if trimStr lStr == "" then pure none
      else pure (some (← Law.parse lStr))
    | .error _ => pure none
  let stepExpr ← match j.getObjVal? "step" with
    | .ok stJ => pure (some (← decodeExpr fuel stJ))
    | .error _ => pure none
  return { name, targetType, invariant := inv, law := lawExpr, step := stepExpr, method, steps }

/-- `{name, imports:[{alias, moduleName}], ast}` as the TS elaborator received it. -/
def decodeModule (j : Json) : Except String Module := do
  let ast ← j.getObjVal? "ast"
  let mut decls : List Decl := []
  let mut laws : List (String × Law.LawExpr) := []
  let mut header : Option PackageHeader := none
  let mut keeps : List (String × String) := []
  let mut lawMethods : List (String × IsarMethod) := []
  let mut contracts : List ContractDecl := []
  for d in ← arr ast "declarations" do
    if (str d "kind").toOption == some "keeps" then
      keeps := keeps ++ [(← str d "invariant", ← str d "law")]
    else if (str d "kind").toOption == some "law" then
      let lawName ← str d "name"
      laws := laws ++ [(lawName, ← Law.parse (← str d "source"))]
      if let some m ← decodeOptionalMethod d then
        lawMethods := lawMethods ++ [(lawName, m)]
    else if (str d "kind").toOption == some "contract" then
      contracts := contracts ++ [← decodeContractDecl d]
    else if (str d "kind").toOption == some "package" then
      if header.isSome then throw "a module declares one package"
      let parents ← (← arr d "parents").mapM fun p => do
        match (str p "major").toOption, (str p "hash").toOption with
        | some major, _ => match major.toNat? with
          | some n => pure (ParentRef.intention (← str p "name") n)
          | none => throw "package parent major version"
        | _, some hash => pure (ParentRef.extension (← str p "name") hash)
        | none, none => throw "package parent: major or hash"
      header := some ⟨← str d "name", parents⟩
    else decls := decls ++ [← decodeDecl d]
  Law.checkNames laws
  for (inv, law) in keeps do
    unless laws.any (·.1 == law) do throw s!"keeps {inv} by {law}: {law} is not a law of this module"
    unless decls.any (fun d => d.name == inv) do throw s!"keeps {inv} by {law}: {inv} is not declared in this module"
  return ⟨← str j "name", ← (← arr j "imports").mapM (fun i => do return (← str i "alias", ← str i "moduleName")),
    decls, laws, header, keeps, lawMethods, contracts⟩

end Obend.Spec.Syntax

end
