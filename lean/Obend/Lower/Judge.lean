module
/-
# Obend.Lower.Judge — the lowering's certificate, `lower@1`, and its annotations

**The certificate** of a lowering is the lowered term with the digest of its source (`Cert`); the
object is the source, the Lean-lite term the reader produced. The judge re-lowers the source and
compares (`check`): the simplest honest format, whose trust base is the compiled lowering. An accepted
certificate means its term *is* the lowering of the source and so computes what the source computes
(`Meaning`, through `lower_sound_nat`). Its planted bad certificate is `5 - 3` with the term of `5 + 3`
(the `subAdd` mutation), refused by the term clause.

**Annotations** (`annotate`): the tree of lambda (and injection) annotations `checkAgainst` reads at
synthesis positions, computed from the source's types (`typeOf`); the checker's run is the test that
they suffice (`lower_checks` says some annotation does, for every `LTyped` term).
-/
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Typing
public import Obend.Judge.Class
public import Obend.Core.Code
public import Obend.Spec.DataWire
public import Obend.Law.Proofs.Claim
public import Obend.Logic.Obligation
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Core.Data (Data)
open Obend.Core.Proofs.BidirectionalCompleteness (AnnotationTree)
set_option autoImplicit false

/-! ## The source on the wire -/

def natOpName : NatOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod" | .beq => "beq" | .ble => "ble"

def natOpOf : String → Option NatOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div | "mod" => some .mod
  | "beq" => some .beq | "ble" => some .ble | _ => none

open Obend.Core.Code (tyData tyOf listData listOf) in
def lexprData : LExpr → Data
  | .bvar i => .variant "bvar" (.natural i)
  | .erased => .variant "erased" (.record [])
  | .const n b => .variant "const" (.record [("name", .label n), ("body", lexprData b)])
  | .app f a => .variant "app" (.record [("function", lexprData f), ("argument", lexprData a)])
  | .lam T b => .variant "lam" (.record [("domain", tyData T), ("body", lexprData b)])
  | .letE T v b => .variant "let" (.record [("domain", tyData T), ("value", lexprData v), ("body", lexprData b)])
  | .lit n => .variant "lit" (.natural n)
  | .natSucc a => .variant "succ" (lexprData a)
  | .natBin op l r => .variant "natBin" (.record [("op", .label (natOpName op)), ("left", lexprData l),
      ("right", lexprData r)])
  | .boolLit b => .variant "bool" (.boolean b)
  | .natRec T z s m => .variant "natRec" (.record [("result", tyData T), ("zero", lexprData z),
      ("succ", lexprData s), ("major", lexprData m)])
  | .boolRec T x y m => .variant "boolRec" (.record [("result", tyData T), ("false", lexprData x),
      ("true", lexprData y), ("major", lexprData m)])
  | .record fs => .variant "record" (.record (fs.map fun f => (f.1, lexprData f.2)))
  | .split ns F m => .variant "split" (.record [("names", listData (ns.map .label)), ("minor", lexprData F),
      ("major", lexprData m)])
  | .proj n t => .variant "proj" (.record [("name", .label n), ("target", lexprData t)])
  | .inject l fs => .variant "inject" (.record [("label", .label l), ("fields", .record (fs.map fun f => (f.1, lexprData f.2)))])
  | .cases T arms m => .variant "cases" (.record [("result", tyData T),
      ("arms", listData (arms.map fun a => .record [("label", .label a.1), ("names", listData (a.2.1.map .label)),
        ("minor", lexprData a.2.2)])), ("major", lexprData m)])
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)
    | (rename_i h; have := LExpr.sizeOf_arm_lt h; omega)

def labelOf : Data → Option String
  | .label s => some s
  | _ => none

open Obend.Core.Code (tyData tyOf listData listOf) in
partial def lexprOf : Data → Option LExpr
  | .variant "bvar" (.natural i) => some (.bvar i)
  | .variant "erased" (.record []) => some .erased
  | .variant "const" (.record [("name", .label n), ("body", b)]) => do pure (.const n (← lexprOf b))
  | .variant "app" (.record [("function", f), ("argument", a)]) => do pure (.app (← lexprOf f) (← lexprOf a))
  | .variant "lam" (.record [("domain", T), ("body", b)]) => do pure (.lam (← tyOf T) (← lexprOf b))
  | .variant "let" (.record [("domain", T), ("value", v), ("body", b)]) => do
      pure (.letE (← tyOf T) (← lexprOf v) (← lexprOf b))
  | .variant "lit" (.natural n) => some (.lit n)
  | .variant "succ" a => do pure (.natSucc (← lexprOf a))
  | .variant "natBin" (.record [("op", .label op), ("left", l), ("right", r)]) => do
      pure (.natBin (← natOpOf op) (← lexprOf l) (← lexprOf r))
  | .variant "bool" (.boolean b) => some (.boolLit b)
  | .variant "natRec" (.record [("result", T), ("zero", z), ("succ", s), ("major", m)]) => do
      pure (.natRec (← tyOf T) (← lexprOf z) (← lexprOf s) (← lexprOf m))
  | .variant "boolRec" (.record [("result", T), ("false", x), ("true", y), ("major", m)]) => do
      pure (.boolRec (← tyOf T) (← lexprOf x) (← lexprOf y) (← lexprOf m))
  | .variant "record" (.record fs) => do pure (.record (← fs.mapM fun f => do pure (f.1, ← lexprOf f.2)))
  | .variant "split" (.record [("names", ns), ("minor", F), ("major", m)]) => do
      pure (.split (← (← listOf ns).mapM labelOf) (← lexprOf F) (← lexprOf m))
  | .variant "proj" (.record [("name", .label n), ("target", t)]) => do pure (.proj n (← lexprOf t))
  | .variant "inject" (.record [("label", .label l), ("fields", .record fs)]) => do
      pure (.inject l (← fs.mapM fun f => do pure (f.1, ← lexprOf f.2)))
  | .variant "cases" (.record [("result", T), ("arms", arms), ("major", m)]) => do
      let arms ← (← listOf arms).mapM fun
        | .record [("label", .label l), ("names", ns), ("minor", M)] => do
            pure (l, ← (← listOf ns).mapM labelOf, ← lexprOf M)
        | _ => none
      pure (.cases (← tyOf T) arms (← lexprOf m))
  | _ => none

/-- The source's content address: cSHAKE256 of its wire form. -/
def sourceDigest (src : LExpr) : Nat :=
  Obend.Core.Code.textDigest Obend.Core.Digest.deployed (Obend.Spec.DataWire.dataJson (lexprData src)).compress

/-! ## The judge -/

/-- A certificate: the source's digest and the lowered term. -/
structure Cert where
  digest : Nat
  term : Term

inductive Clause where
  /-- the certificate's term is not the lowering of the source -/
  | notTheLowering
  /-- the certificate names another source -/
  | otherSource
  deriving DecidableEq, Repr

def check (_ : Nat) (src : LExpr) (c : Cert) : Obend.Judge.Verdict Clause :=
  if Obend.Law.termEq (lowerT src) c.term then
    if c.digest == sourceDigest src then .ok else .refused .otherSource []
  else .refused .notTheLowering []

/-- What an accepted certificate means: its term is the lowering of the source it names, so it
evaluates to every literal the source reduces to. -/
def Meaning (src : LExpr) (c : Cert) : Prop :=
  c.digest = sourceDigest src ∧ c.term = lowerT src ∧
    ∀ n : Nat, SSteps src (.lit n) → Evaluates c.term (.nat n)

theorem check_ok {r : Nat} {src : LExpr} {c : Cert} (h : check r src c = .ok) :
    c.digest = sourceDigest src ∧ c.term = lowerT src := by
  unfold check at h
  split at h
  · rename_i ht
    split at h
    · rename_i hd; exact ⟨by simpa using hd, (Obend.Law.termEq_sound ht).symm⟩
    · cases h
  · cases h

instance judge : Obend.Judge LExpr Cert where
  Clause := Clause
  Meaning := Meaning
  check := check
  sound := by
    intro r src c h
    obtain ⟨hd, ht⟩ := check_ok h
    exact ⟨hd, ht, fun n run => ht ▸ (by simpa [lowerT] using lower_sound_nat run)⟩
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment _ := True
  complete := by
    intro src _ _
    refine ⟨⟨sourceDigest src, lowerT src⟩, 0, ?_⟩
    simp [check, Obend.Logic.termEq_refl']
  mono := by intros; rfl

/-- The planted bad certificate: `5 - 3` with the term of `5 + 3`. -/
def badSource : LExpr := .natBin .sub (.lit 5) (.lit 3)
def badCert : Cert := ⟨0, lowerT (.natBin .add (.lit 5) (.lit 3))⟩

theorem bad_refused : check 0 badSource badCert = .refused .notTheLowering [] := by
  have h : Obend.Law.termEq (lowerT badSource) badCert.term = false := by
    cases e : Obend.Law.termEq (lowerT badSource) badCert.term
    · rfl
    · have := Obend.Law.termEq_sound e
      simp [badSource, badCert, lowerT, NatOp.prim] at this
  simp only [check, h]; rfl

def certJson (c : Cert) : Lean.Json :=
  Lean.Json.mkObj [("format", "lower@1"), ("digest", Lean.toJson (toString c.digest)),
    ("term", Obend.Logic.termJson c.term)]

def certOf (s : String) : Except String Cert := do
  let j ← Lean.Json.parse s
  let d ← j.getObjValAs? String "digest"
  let some d := d.toNat? | throw "the digest is not a natural"
  let t ← Obend.Logic.termOf (← j.getObjVal? "term")
  pure ⟨d, t⟩

def sourceJson (src : LExpr) : Lean.Json := Obend.Spec.DataWire.dataJson (lexprData src)

def sourceOf (s : String) : Except String LExpr := do
  let j ← Lean.Json.parse s
  let d ← Obend.Spec.DataWire.decodeData Obend.Logic.wireDepth j
  match lexprOf d with
  | some e => pure e
  | none => throw "not the wire form of a Lean-lite term"

/-- **The registered format `lower@1`.** -/
def format : Obend.Judge.Format where
  name := "lower"
  version := "1"
  Obj := LExpr
  Cert := Cert
  judge := judge
  decodeObj := sourceOf
  decodeCert := certOf
  trust := .compiled
  regime := .decidable
  bad := (badSource, badCert)
  badGrade := 0
  bad_refused := ⟨_, _, bad_refused⟩

/-- The formats the lowering registers. -/
def formats : List Obend.Judge.Format := [format]

/-! ## Annotations for the checker -/

/-- The type a fragment term synthesizes (`none` where a constructor of a sum is not annotated). -/
def typeOf (Γ : List Ty) : LExpr → Option Ty
  | .bvar i => Γ[i]?
  | .erased => some .emptyRow
  | .const _ b => typeOf Γ b
  | .app f _ => match typeOf Γ f with
    | some (.arrow _ _ _ B) => some B
    | _ => none
  | .lam A b => (typeOf (A :: Γ) b).map (fn A)
  | .letE A _ b => typeOf (A :: Γ) b
  | .lit _ | .natSucc _ => some .natural
  | .natBin op _ _ => some op.resultTy
  | .boolLit _ => some .boolean
  | .natRec T _ _ _ | .boolRec T _ _ _ | .cases T _ _ => some T
  | .record fs => do
    let ts ← fs.attach.mapM fun ⟨f, _⟩ => do pure (f.1, ← typeOf Γ f.2)
    pure (fieldRow ts)
  | .split ns F _ => do
    let mut t ← typeOf Γ F
    for _ in ns do
      match t with
      | .arrow _ _ _ B => t := B
      | _ => none
    pure t
  | .proj n t => do (← typeOf Γ t).lookup [] 1000 n
  | .inject _ _ => none
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)

def leaf : AnnotationTree := .node none []

def lamAnn (A B : Ty) : LambdaAnnotation := ⟨A, B, .unrestricted, .reusable⟩

/-- The annotation tree of `lowerT e`, node for node (the checker's paths are child indices). -/
def annotate (Γ : List Ty) : LExpr → AnnotationTree
  | .bvar _ | .erased | .lit _ | .boolLit _ => leaf
  | .const _ b => annotate Γ b
  | .app f a => .node none [annotate Γ f, annotate Γ a]
  | .lam A b => .node ((typeOf (A :: Γ) b).map (lamAnn A)) [annotate (A :: Γ) b]
  | .letE A v b => .node none [.node ((typeOf (A :: Γ) b).map (lamAnn A)) [annotate (A :: Γ) b], annotate Γ v]
  | .natSucc a => .node none [annotate Γ a, leaf]
  | .natBin _ l r => .node none [annotate Γ l, annotate Γ r]
  | .natRec T z s m =>
    let target := fn .natural T
    let Γk := .natural :: .emptyRow :: target :: Γ
    let succ := AnnotationTree.node none [.node none [annotate Γ s, leaf], .node none [leaf, leaf]]
    let spec := AnnotationTree.node (some (lamAnn target (fn .emptyRow target)))
      [.node (some (lamAnn .emptyRow target)) [.node (some (lamAnn .natural T))
        [.node none [leaf, annotate Γk z, succ]]]]
    .node none [.node none [spec, leaf], annotate Γ m]
  | .boolRec _ x y m => .node none [annotate Γ m, annotate Γ y, annotate Γ x]
  | .record fs => .node none (fs.attach.map fun ⟨f, _⟩ => annotate Γ f.2)
  | .split _ F m => .node none [annotate Γ m, annotate Γ F]
  | .proj _ t => .node none [annotate Γ t]
  | .inject _ fs => .node none [.node none (fs.attach.map fun ⟨f, _⟩ => annotate Γ f.2)]
  | .cases _ arms m => .node none [annotate Γ m,
      .node none (arms.attach.map fun ⟨a, _⟩ => .node none [leaf, annotate Γ a.2.2])]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)
    | (rename_i h; have := LExpr.sizeOf_arm_lt h; omega)

end Obend.Lower
end
