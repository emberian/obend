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
@[expose] public section
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

structure Claim where
  name : String
  params : List Param
  body : Expr
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

inductive Decl where
  | spec (s : Spec)
  | extension (name : String) (params : List Param) (targetType : String) (body : Body) (binders : String)
  | function (name : String) (params : List Param) (resultType : String) (body : Body)
  | record (name : String) (fields : List (String × String)) (methods : List Signature)
  | sum (name : String) (cases : List (String × String))
  deriving Inhabited

def Decl.name : Decl → String
  | .spec s => s.name | .extension n .. => n | .function n .. => n | .record n .. => n | .sum n .. => n

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
      return (Claim.mk name params body)
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
  | other => .error ("unknown AST declaration " ++ other)

/-- `{name, imports:[{alias, moduleName}], ast}` as the TS elaborator received it. -/
def decodeModule (j : Json) : Except String Module := do
  let ast ← j.getObjVal? "ast"
  let mut decls : List Decl := []
  let mut laws : List (String × Law.LawExpr) := []
  for d in ← arr ast "declarations" do
    if (str d "kind").toOption == some "law" then
      laws := laws ++ [(← str d "name", ← Law.parse (← str d "source"))]
    else decls := decls ++ [← decodeDecl d]
  Law.checkNames laws
  return ⟨← str j "name", ← (← arr j "imports").mapM (fun i => do return (← str i "alias", ← str i "moduleName")),
    decls, laws⟩

end Obend.Spec.Syntax

end
