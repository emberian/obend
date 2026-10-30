module
/-
# Obend.Spec.Annotated — the annotated core: `ATerm`, its rendering and its erasure

The elaborator's output term: Core4 with a typing `Proposal` on every `lam` and a declared sum
type on every `inject`. `ATerm.json` is the rendering the typed packet carries (the wire the
checker's `Obend.Core.Packet.decodeTerm` reads: `Obend.Spec.Proofs.TermWire.decode_json` proves
the two meet); `ATerm.erase` the `Obend.Core.Term` the checker and the machine consume. Also the
type-annotation maps a chain instance uses (`mapTypes`, `instantiate`, `retarget`) and the nesting
`depth` the decoder's fuel must cover. Split out of minidregg
`Compiler/ObjectiveBendElaborate.lean` (`depth` from `Compiler/ObjectiveBendTermWire.lean`),
commit 092027a2.
-/
public import Lean
public import Obend.Core.Term
public import Obend.Spec.Types
@[expose] public section
namespace Obend.Spec.Annotated
open Lean (Json toJson)
open Obend.Spec.Types
set_option autoImplicit false

abbrev CoreTerm := Obend.Core.Term.Term
abbrev CorePrimitive := Obend.Core.Term.Primitive

structure Proposal where
  domain : Option PTy
  codomain : Option PTy
  parameter : String
  reuse : String
  reason : Option String := none
  deriving Inhabited

inductive ATerm where
  | bound (index : Nat)
  | lam (proposal : Proposal) (body : ATerm)
  | app (fn arg : ATerm)
  | mix (lower upper : ATerm)
  | fix (spec seed : ATerm)
  | specification (metadata extension : ATerm)
  | prototype (spec target : ATerm)
  | reflect (value : ATerm) | metadata (value : ATerm) | project (value : ATerm)
  | nat (value : String) | boolean (value : Bool) | label (value : String)
  | binary (primitive : String) (left right : ATerm)
  | extend (inherited : ATerm) (fields : List (String × ATerm))
  | record (fields : List (String × ATerm))
  | get (target : ATerm) (name : String)
  | ifZero (value zero successor : ATerm)
  | inject (label : String) (type : Option PTy) (reason : Option String) (payload : ATerm)
  | case (scrutinee : ATerm) (arms : List (String × ATerm))
  | ifBool (condition whenTrue whenFalse : ATerm)
  /-- Yield a Plan; carries the enclosing activity's Plan and Response types. -/
  | perform (plan response : PTy) (value : ATerm)
  /-- A pure tail of an activity body (inserted, never authored). -/
  | done (plan response : PTy) (value : ATerm)
  deriving Inhabited

mutual
def ATerm.json : ATerm → Json
  | .bound i => Json.mkObj [("tag", "bound"), ("index", toJson i)]
  | .lam _ b => Json.mkObj [("tag", "lam"), ("body", b.json)]
  | .app f a => Json.mkObj [("tag", "app"), ("fn", f.json), ("arg", a.json)]
  | .mix l u => Json.mkObj [("tag", "mix"), ("lower", l.json), ("upper", u.json)]
  | .fix s i => Json.mkObj [("tag", "fix"), ("spec", s.json), ("seed", i.json)]
  | .specification m e => Json.mkObj [("tag", "specification"), ("metadata", m.json), ("extension", e.json)]
  | .prototype s t => Json.mkObj [("tag", "prototype"), ("spec", s.json), ("target", t.json)]
  | .reflect v => Json.mkObj [("tag", "reflect"), ("value", v.json)]
  | .metadata v => Json.mkObj [("tag", "metadata"), ("value", v.json)]
  | .project v => Json.mkObj [("tag", "project"), ("value", v.json)]
  | .nat v => Json.mkObj [("tag", "nat"), ("value", v)]
  | .boolean v => Json.mkObj [("tag", "boolean"), ("value", toJson v)]
  | .label v => Json.mkObj [("tag", "label"), ("value", v)]
  | .binary p l r => Json.mkObj [("tag", "binary"), ("primitive", p), ("left", l.json), ("right", r.json)]
  | .extend i fs => Json.mkObj [("tag", "extend"), ("inherited", i.json), ("fields", fieldsJson fs)]
  | .record fs => Json.mkObj [("tag", "record"), ("fields", fieldsJson fs)]
  | .get t n => Json.mkObj [("tag", "get"), ("target", t.json), ("name", n)]
  | .ifZero v z s => Json.mkObj [("tag", "ifZero"), ("value", v.json), ("zero", z.json), ("successor", s.json)]
  | .inject l _ _ p => Json.mkObj [("tag", "inject"), ("label", l), ("payload", p.json)]
  | .case s arms => Json.mkObj [("tag", "case"), ("scrutinee", s.json), ("arms", armsJson arms)]
  | .ifBool c t f => Json.mkObj [("tag", "ifBool"), ("condition", c.json), ("whenTrue", t.json), ("whenFalse", f.json)]
  | .perform _ _ v => Json.mkObj [("tag", "perform"), ("plan", v.json)]
  | .done _ _ v => Json.mkObj [("tag", "done"), ("value", v.json)]
def fieldsJson : List (String × ATerm) → Json
  | fs => Json.arr (fieldsArray fs).toArray
def fieldsArray : List (String × ATerm) → List Json
  | [] => []
  | (n, v) :: rest => Json.mkObj [("name", n), ("value", v.json)] :: fieldsArray rest
def armsJson : List (String × ATerm) → Json
  | arms => Json.arr (armsArray arms).toArray
def armsArray : List (String × ATerm) → List Json
  | [] => []
  | (l, b) :: rest => Json.mkObj [("label", l), ("body", b.json)] :: armsArray rest
end

/-- Erasure to the Core4 `Term` the checker and demand machine consume. -/
def primitiveOf : String → Except String CorePrimitive
  | "add" => .ok .add | "multiply" => .ok .multiply | "equal" => .ok .equal | "conjunction" => .ok .conjunction
  | "labelEqual" => .ok .labelEqual
  | "subtract" => .ok .subtract | "divide" => .ok .divide | "less" => .ok .less | "lessEqual" => .ok .lessEqual
  | "modulo" => .ok .modulo
  | other => .error ("primitive " ++ other ++ " is not a Core4 constructor yet")

mutual
def ATerm.erase : ATerm → Except String CoreTerm
  | .bound i => .ok (.bound i)
  | .lam _ b => return .lam (← b.erase)
  | .app f a => return .app (← f.erase) (← a.erase)
  | .mix l u => return .mix (← l.erase) (← u.erase)
  | .fix s i => return .fix (← s.erase) (← i.erase)
  | .specification m e => return .specification (← m.erase) (← e.erase)
  | .prototype s t => return .prototype (← s.erase) (← t.erase)
  | .reflect v => return .reflect (← v.erase)
  | .metadata v => return .metadata (← v.erase)
  | .project v => return .project (← v.erase)
  | .nat v => match v.toNat? with
    | some n => if toString n = v then .ok (.nat n) else .error "non-canonical natural"
    | none => .error "non-canonical natural"
  | .boolean v => .ok (.boolean v)
  | .label v => .ok (.label v)
  | .binary p l r => return .binary (← primitiveOf p) (← l.erase) (← r.erase)
  | .extend i fs => return .extend (← i.erase) (← eraseFields fs)
  | .record fs => return .record (← eraseFields fs)
  | .get t n => return .get (← t.erase) n
  | .ifZero v z s => return .ifZero (← v.erase) (← z.erase) (← s.erase)
  | .inject l _ _ p => return .inject l (← p.erase)
  | .case sc arms => return .case (← sc.erase) (← eraseFields arms)
  | .ifBool c t f => return .ifBool (← c.erase) (← t.erase) (← f.erase)
  | .perform _ _ v => return .perform (← v.erase)
  | .done _ _ v => return .done (← v.erase)
def eraseFields : List (String × ATerm) → Except String (List (String × CoreTerm))
  | [] => .ok []
  | (n, v) :: rest => return (n, ← v.erase) :: (← eraseFields rest)
end

mutual
/-- Apply `f` to every type annotation of a lowered term. -/
def ATerm.mapTypes (f : PTy → PTy) : ATerm → ATerm
  | .bound i => .bound i
  | .lam p b => .lam { p with domain := p.domain.map f, codomain := p.codomain.map f } (b.mapTypes f)
  | .app x y => .app (x.mapTypes f) (y.mapTypes f)
  | .mix x y => .mix (x.mapTypes f) (y.mapTypes f)
  | .fix x y => .fix (x.mapTypes f) (y.mapTypes f)
  | .specification x y => .specification (x.mapTypes f) (y.mapTypes f)
  | .prototype x y => .prototype (x.mapTypes f) (y.mapTypes f)
  | .reflect x => .reflect (x.mapTypes f)
  | .metadata x => .metadata (x.mapTypes f)
  | .project x => .project (x.mapTypes f)
  | .nat v => .nat v
  | .boolean v => .boolean v
  | .label v => .label v
  | .binary p x y => .binary p (x.mapTypes f) (y.mapTypes f)
  | .extend x fs => .extend (x.mapTypes f) (ATerm.mapFieldTypes f fs)
  | .record fs => .record (ATerm.mapFieldTypes f fs)
  | .get x n => .get (x.mapTypes f) n
  | .ifZero x z y => .ifZero (x.mapTypes f) (z.mapTypes f) (y.mapTypes f)
  | .inject l t r x => .inject l (t.map f) r (x.mapTypes f)
  | .case x arms => .case (x.mapTypes f) (ATerm.mapFieldTypes f arms)
  | .ifBool x y z => .ifBool (x.mapTypes f) (y.mapTypes f) (z.mapTypes f)
  | .perform p r x => .perform (f p) (f r) (x.mapTypes f)
  | .done p r x => .done (f p) (f r) (x.mapTypes f)
def ATerm.mapFieldTypes (f : PTy → PTy) : List (String × ATerm) → List (String × ATerm)
  | [] => []
  | (n, x) :: rest => (n, x.mapTypes f) :: ATerm.mapFieldTypes f rest
end

/-- A template's instance at σ: its annotations substituted, then canonical (the instance a
chain emits; MODULAR-TYPING §6 `template[σ]`). -/
def ATerm.instantiate (σ : Nat → Option PTy) (t : ATerm) : ATerm :=
  t.mapTypes fun ty => (ty.subst σ).canonical

/-- Re-annotate the result of the `n`-parameter function `t` as `result` (the last layer of a
chain over a recursive record is annotated with the record's variable, which unfolds to the
row the layer provides). Returns the term and its new type. -/
def ATerm.retarget (result : PTy) : Nat → ATerm → ATerm × Option PTy
  | 0, t => (t, some result)
  | n + 1, .lam p b =>
    let (b', cod) := ATerm.retarget result n b
    (.lam { p with codomain := cod } b', match p.domain, cod with
      | some d, some c => some (arrowTy d c p.parameter p.reuse)
      | _, _ => none)
  | _, t => (t, none)

def notTerm (x : ATerm) : ATerm := .ifBool x (.boolean false) (.boolean true)

mutual
/-- The nesting depth of an elaborated term: what `Obend.Core.Packet.decodeTerm`'s fuel must cover. -/
def depth : ATerm → Nat
  | .bound _ | .nat _ | .boolean _ | .label _ => 1
  | .lam _ b | .reflect b | .metadata b | .project b | .inject _ _ _ b | .perform _ _ b | .done _ _ b => depth b + 1
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b => max (depth a) (depth b) + 1
  | .ifZero a b c | .ifBool a b c => max (depth a) (max (depth b) (depth c)) + 1
  | .extend a fs | .case a fs => max (depth a) (fieldsDepth fs) + 1
  | .record fs => fieldsDepth fs + 1
  | .get a _ => depth a + 1
def fieldsDepth : List (String × ATerm) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (fieldsDepth rest)
end

end Obend.Spec.Annotated

end
