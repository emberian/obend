module
/-
# Obend.Core.Code — `quote` as a kernel function on held terms; the `Syntax` sum; content addresses

The design is `review/QUOTE-ORIENTATION-20261101.md` §3: `quote` is a function of the kernel on the
terms it holds (a slot's candidates, a law's code, a page's cells, a package member), never a step
of the machine and never applied to a `RuntimeValue`; no `Term` constructor is added.

* `quote : Term → Data` renders `TermTraverse.encode t` (the generic `Tree Tag`) as a value of the
  built-in sum `Syntax` (`syntaxSource`); `unquote` reads it back, refusing any tree that is not the
  encoding of a term. `quote_roundtrip : unquote (quote t) = some t` (T1).
* `dataDigest H` is a Merkle digest of `Data` under a byte hash `H`, every node one `digestWith`;
  `dataDigest_binds`: equal digests are equal data, or `H` collides (`binds_or_collides` at every
  node). `address t := dataDigest deployed (quote t)`, and `digest_of_quote` (T2): equal addresses
  are equal terms, or cSHAKE256 collides. Under a length-only hash two terms share one address
  (`lengthHash_address_collapses`).
* `encodingVersion` is the digest of the `Syntax` schema (`syntaxSchema`, built from `tagData`
  itself), so a change to the rendering of any tag changes the version (or collides).
-/
public import Obend.Core.TermTraverse
public import Obend.Core.Data
public import Obend.Core.Digest
public import Obend.Law.Claim
public import Obend.Core.Check
public import Obend.Core.Bidirectional
public import Obend.Core.Invariant
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Slot.Core4
public import Obend.Tactic.Tooth
import all Obend.Core.Check
public section
namespace Obend.Core.Code
open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag Shape encode decode decode_encode)
open Obend.Core.Data (Data)
open Obend.Digest.HashBytes (Hash Collision ofBE be ofBE_lt)
open Obend.Core.Digest (digestWith deployed Admissible admissible_of_lt binds_or_collides lengthHash)
set_option autoImplicit false

/-! ## §1. The `Syntax` sum: a term's `Tree Tag` as `Data` -/

/-- The empty record, the payload of a nullary constructor. -/
def unit : Data := .record []

def primitiveName : Primitive → String
  | .add => "add" | .multiply => "multiply" | .equal => "equal" | .conjunction => "conjunction"
  | .labelEqual => "labelEqual" | .subtract => "subtract" | .divide => "divide"
  | .less => "less" | .lessEqual => "lessEqual" | .modulo => "modulo"

def primitiveOfName : String → Option Primitive
  | "add" => some .add | "multiply" => some .multiply | "equal" => some .equal
  | "conjunction" => some .conjunction | "labelEqual" => some .labelEqual
  | "subtract" => some .subtract | "divide" => some .divide | "less" => some .less
  | "lessEqual" => some .lessEqual | "modulo" => some .modulo
  | _ => none

theorem primitiveOfName_name (p : Primitive) : primitiveOfName (primitiveName p) = some p := by
  cases p <;> rfl

/-- One constructor of `SyntaxTag` per `Tag`; payloads are the tag's own data. -/
def tagData : Tag → Data
  | .hole n => .variant "hole" (.natural n)
  | .app => .variant "app" unit
  | .mix => .variant "mix" unit
  | .fix => .variant "fix" unit
  | .specification => .variant "specification" unit
  | .prototype => .variant "prototype" unit
  | .reflect => .variant "reflect" unit
  | .metadata => .variant "metadata" unit
  | .project => .variant "project" unit
  | .ifBool => .variant "ifBool" unit
  | .perform => .variant "perform" unit
  | .done => .variant "done" unit
  | .nat value => .variant "nat" (.natural value)
  | .boolean value => .variant "boolean" (.boolean value)
  | .label value => .variant "label" (.label value)
  | .binary p => .variant "binary" (.label (primitiveName p))
  | .extend => .variant "extend" unit
  | .record => .variant "record" unit
  | .ifZero => .variant "ifZero" unit
  | .case => .variant "case" unit
  | .get name => .variant "get" (.label name)
  | .inject name => .variant "inject" (.label name)
  | .field name => .variant "field" (.label name)

@[expose] def tagOf : Data → Option Tag
  | .variant "hole" (.natural n) => some (.hole n)
  | .variant "app" (.record []) => some .app
  | .variant "mix" (.record []) => some .mix
  | .variant "fix" (.record []) => some .fix
  | .variant "specification" (.record []) => some .specification
  | .variant "prototype" (.record []) => some .prototype
  | .variant "reflect" (.record []) => some .reflect
  | .variant "metadata" (.record []) => some .metadata
  | .variant "project" (.record []) => some .project
  | .variant "ifBool" (.record []) => some .ifBool
  | .variant "perform" (.record []) => some .perform
  | .variant "done" (.record []) => some .done
  | .variant "nat" (.natural value) => some (.nat value)
  | .variant "boolean" (.boolean value) => some (.boolean value)
  | .variant "label" (.label value) => some (.label value)
  | .variant "binary" (.label name) => (primitiveOfName name).map .binary
  | .variant "extend" (.record []) => some .extend
  | .variant "record" (.record []) => some .record
  | .variant "ifZero" (.record []) => some .ifZero
  | .variant "case" (.record []) => some .case
  | .variant "get" (.label name) => some (.get name)
  | .variant "inject" (.label name) => some (.inject name)
  | .variant "field" (.label name) => some (.field name)
  | _ => none

theorem tagOf_tagData (tag : Tag) : tagOf (tagData tag) = some tag := by
  cases tag <;> simp [tagData, tagOf, unit, primitiveOfName_name]

mutual
/-- A `Tree Tag` as `Syntax`: `var` (a de Bruijn index), `bind` (one binder), `node` (a tag and
its children as a `SyntaxList`). -/
def shapeData : Shape → Data
  | .var i => .variant "var" (.natural i)
  | .bind b => .variant "bind" (shapeData b)
  | .node tag cs => .variant "node" (.record [("tag", tagData tag), ("children", childrenData cs)])
@[expose] def childrenData : List Shape → Data
  | [] => .variant "nil" unit
  | c :: cs => .variant "cons" (.record [("head", shapeData c), ("tail", childrenData cs)])
end

mutual
def shapeOf : Data → Option Shape
  | .variant "var" (.natural i) => some (.var i)
  | .variant "bind" b => (shapeOf b).map .bind
  | .variant "node" (.record [("tag", tag), ("children", cs)]) => do
      pure (.node (← tagOf tag) (← childrenOf cs))
  | _ => none
def childrenOf : Data → Option (List Shape)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", h), ("tail", t)]) => do
      pure ((← shapeOf h) :: (← childrenOf t))
  | _ => none
end

mutual
theorem shapeOf_shapeData : (s : Shape) → shapeOf (shapeData s) = some s
  | .var i => by simp [shapeData, shapeOf]
  | .bind b => by simp [shapeData, shapeOf, shapeOf_shapeData b]
  | .node tag cs => by simp [shapeData, shapeOf, tagOf_tagData, childrenOf_childrenData cs]
theorem childrenOf_childrenData : (cs : List Shape) → childrenOf (childrenData cs) = some cs
  | [] => by simp [childrenData, childrenOf, unit]
  | c :: cs => by simp [childrenData, childrenOf, shapeOf_shapeData c, childrenOf_childrenData cs]
end

/-! `Law.treeEq` is sound and reflexive (re-proved here: `Obend.Law.Proofs.Claim` keeps them
private to its module). -/
mutual
theorem treeEq_sound : ∀ {a b : Shape}, Obend.Law.treeEq a b = true → a = b
  | .var i, .var j, h => by simp [Obend.Law.treeEq] at h; subst h; rfl
  | .bind a, .bind b, h => by simp only [Obend.Law.treeEq] at h; rw [treeEq_sound h]
  | .node t cs, .node u ds, h => by
    simp only [Obend.Law.treeEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, treesEq_sound h.2]
  | .var _, .bind _, h | .var _, .node _ _, h | .bind _, .var _, h | .bind _, .node _ _, h
  | .node _ _, .var _, h | .node _ _, .bind _, h => by simp [Obend.Law.treeEq] at h
theorem treesEq_sound : ∀ {as bs : List Shape}, Obend.Law.treesEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Obend.Law.treesEq, Bool.and_eq_true] at h
    rw [treeEq_sound h.1, treesEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Obend.Law.treesEq] at h
end

mutual
theorem treeEq_refl : ∀ (a : Shape), Obend.Law.treeEq a a = true
  | .var i => by simp [Obend.Law.treeEq]
  | .bind a => by simp only [Obend.Law.treeEq]; exact treeEq_refl a
  | .node t cs => by simp only [Obend.Law.treeEq, decide_true, Bool.true_and]; exact treesEq_refl cs
theorem treesEq_refl : ∀ (as : List Shape), Obend.Law.treesEq as as = true
  | [] => rfl
  | a :: as => by simp only [Obend.Law.treesEq, Bool.and_eq_true]; exact ⟨treeEq_refl a, treesEq_refl as⟩
end

/-- **`quote`**: the canonical first-order rendering of a term the kernel holds. -/
@[expose] def quote (t : Term) : Data := shapeData (encode t)

/-- Read a quotation back. Only the encoding of a term is accepted: a well-formed tree that
`decode` would repair (a `node .app` with three children, say) is refused. -/
def unquote (d : Data) : Option Term :=
  match shapeOf d with
  | some s => if Obend.Law.treeEq (encode (decode s)) s then some (decode s) else none
  | none => none

/-- **T1 `quote_roundtrip`.** -/
theorem quote_roundtrip (t : Term) : unquote (quote t) = some t := by
  simp [unquote, quote, shapeOf_shapeData, decode_encode, treeEq_refl]

theorem quote_injective {t t' : Term} (h : quote t = quote t') : t = t' := by
  have := quote_roundtrip t
  rw [h, quote_roundtrip t'] at this
  exact (Option.some.inj this).symm

/-- An accepted tree is exactly the encoding of the term it reads back to. -/
theorem unquote_some {d : Data} {t : Term} (h : unquote d = some t) : shapeOf d = some (encode t) := by
  unfold unquote at h
  split at h
  · rename_i s hs
    split at h
    · rename_i heq
      cases h
      rw [hs, treeEq_sound heq]
    · cases h
  · cases h

/-- The refuting pole of T1: a rendering that drops one constructor's tag (`mix` rendered as
`app`) gives two terms one quotation, so no `unquote` can invert it. -/
def lossyTagData : Tag → Data
  | .hole n => .variant "hole" (.natural n)
  | .app | .mix => .variant "app" unit
  | .fix => .variant "fix" unit
  | .specification => .variant "specification" unit
  | .prototype => .variant "prototype" unit
  | .reflect => .variant "reflect" unit
  | .metadata => .variant "metadata" unit
  | .project => .variant "project" unit
  | .ifBool => .variant "ifBool" unit
  | .perform => .variant "perform" unit
  | .done => .variant "done" unit
  | .nat value => .variant "nat" (.natural value)
  | .boolean value => .variant "boolean" (.boolean value)
  | .label value => .variant "label" (.label value)
  | .binary p => .variant "binary" (.label (primitiveName p))
  | .extend => .variant "extend" unit
  | .record => .variant "record" unit
  | .ifZero => .variant "ifZero" unit
  | .case => .variant "case" unit
  | .get name => .variant "get" (.label name)
  | .inject name => .variant "inject" (.label name)
  | .field name => .variant "field" (.label name)

theorem lossy_tags_collapse : lossyTagData .mix = lossyTagData .app ∧ Tag.mix ≠ Tag.app :=
  ⟨rfl, by intro h; cases h⟩

#tooth quote_roundtrip by mutation tagData := lossyTagData

/-! ## §2. Content addresses: a Merkle digest of `Data`, bound node by node -/

/-- A hash whose output is at most 32 bytes: every digest it makes is a first operand inside the
binding domain (`Admissible`), so digests nest. -/
def Short (H : Hash) : Prop := ∀ bytes, (H bytes).length ≤ 32

theorem short_admissible {H : Hash} (hH : Short H) (a b : Nat) : Admissible (digestWith H a b) := by
  apply admissible_of_lt
  have h := ofBE_lt (H (Obend.Core.Digest.preimage a b))
  have hle := Nat.pow_le_pow_right (show 0 < 256 by decide) (hH (Obend.Core.Digest.preimage a b))
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  simp only [digestWith]
  omega

theorem deployed_short : Short deployed := by
  intro bytes; simp [deployed]

theorem lengthHash_short : Short lengthHash := by
  intro bytes; simp [lengthHash]

theorem small_admissible {n : Nat} (h : n < 2 ^ 256) : Admissible n := admissible_of_lt h

/-- One node of the Merkle tree: equal digests have equal operands, or `H` collides. -/
theorem node_binds {H : Hash} {a b a' b' : Nat} (h : digestWith H a b = digestWith H a' b')
    (ha : Admissible a) (ha' : Admissible a') : (a = a' ∧ b = b') ∨ Collision H := by
  rcases binds_or_collides H ha ha' h with e | c
  · exact .inl e
  · exact .inr c.global

section Merkle
variable (H : Hash)

def charsDigest : List Char → Nat
  | [] => digestWith H 6 0
  | c :: cs => digestWith H 7 (digestWith H c.toNat (charsDigest cs))

def textDigest (s : String) : Nat := charsDigest H s.toList

mutual
/-- The Merkle digest of `Data`: one `digestWith` per node, its first operand a constructor code
or a digest, so every operand that must be in the binding domain is. -/
def dataDigest : Data → Nat
  | .natural n => digestWith H 0 n
  | .boolean b => digestWith H 1 (if b then 1 else 0)
  | .label s => digestWith H 2 (textDigest H s)
  | .record fs => digestWith H 3 (fieldsDigest fs)
  | .variant l p => digestWith H 4 (digestWith H (textDigest H l) (dataDigest p))
def fieldsDigest : List (String × Data) → Nat
  | [] => digestWith H 8 0
  | (n, d) :: rest =>
      digestWith H 9 (digestWith H (textDigest H n) (digestWith H (dataDigest d) (fieldsDigest rest)))
end
end Merkle

theorem char_admissible (c : Char) : Admissible c.toNat := by
  apply small_admissible
  have := c.val.toNat_lt
  have h : (2 : Nat) ^ 32 < 2 ^ 256 := by decide
  simp only [Char.toNat] at *
  omega

theorem textDigest_admissible {H : Hash} (hH : Short H) (s : String) : Admissible (textDigest H s) := by
  unfold textDigest
  cases s.toList <;> simp only [charsDigest] <;> exact short_admissible hH _ _

theorem dataDigest_admissible {H : Hash} (hH : Short H) (d : Data) : Admissible (dataDigest H d) := by
  cases d <;> simp only [dataDigest] <;> exact short_admissible hH _ _

theorem charsDigest_binds {H : Hash} (hH : Short H) :
    ∀ {cs cs' : List Char}, charsDigest H cs = charsDigest H cs' → cs = cs' ∨ Collision H
  | [], [], _ => .inl rfl
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [charsDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | c :: cs, c' :: cs', h => by
    simp only [charsDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | col
    · rcases node_binds e (char_admissible c) (char_admissible c') with ⟨ec, er⟩ | col
      · rcases charsDigest_binds hH er with rfl | col
        · exact .inl (by rw [Char.toNat_inj.1 ec])
        · exact .inr col
      · exact .inr col
    · exact .inr col

theorem textDigest_binds {H : Hash} (hH : Short H) {s s' : String}
    (h : textDigest H s = textDigest H s') : s = s' ∨ Collision H := by
  rcases charsDigest_binds hH h with e | c
  · exact .inl (String.toList_inj.1 e)
  · exact .inr c

mutual
/-- **Binding of the Merkle digest.** Equal digests are equal data, or `H` collides. -/
theorem dataDigest_binds {H : Hash} (hH : Short H) :
    ∀ {d d' : Data}, dataDigest H d = dataDigest H d' → d = d' ∨ Collision H
  | .natural n, .natural n', h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · exact .inl (by rw [e])
    · exact .inr c
  | .boolean b, .boolean b', h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · left; cases b <;> cases b' <;> simp_all
    · exact .inr c
  | .label s, .label s', h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · rcases textDigest_binds hH e with rfl | c
      · exact .inl rfl
      · exact .inr c
    · exact .inr c
  | .record fs, .record fs', h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · rcases fieldsDigest_binds hH e with rfl | c
      · exact .inl rfl
      · exact .inr c
    · exact .inr c
  | .variant l p, .variant l' p', h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · rcases node_binds e (textDigest_admissible hH _) (textDigest_admissible hH _) with ⟨el, ep⟩ | c
      · rcases textDigest_binds hH el with rfl | c
        · rcases dataDigest_binds hH ep with rfl | c
          · exact .inl rfl
          · exact .inr c
        · exact .inr c
      · exact .inr c
    · exact .inr c
  | .natural _, .boolean _, h | .natural _, .label _, h | .natural _, .record _, h
  | .natural _, .variant _ _, h | .boolean _, .natural _, h | .boolean _, .label _, h
  | .boolean _, .record _, h | .boolean _, .variant _ _, h | .label _, .natural _, h
  | .label _, .boolean _, h | .label _, .record _, h | .label _, .variant _ _, h
  | .record _, .natural _, h | .record _, .boolean _, h | .record _, .label _, h
  | .record _, .variant _ _, h | .variant _ _, .natural _, h | .variant _ _, .boolean _, h
  | .variant _ _, .label _, h | .variant _ _, .record _, h => by
    simp only [dataDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
theorem fieldsDigest_binds {H : Hash} (hH : Short H) :
    ∀ {fs fs' : List (String × Data)}, fieldsDigest H fs = fieldsDigest H fs' → fs = fs' ∨ Collision H
  | [], [], _ => .inl rfl
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [fieldsDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨e, _⟩ | c
    · simp at e
    · exact .inr c
  | (n, d) :: rest, (n', d') :: rest', h => by
    simp only [fieldsDigest] at h
    rcases node_binds h (small_admissible (by decide)) (small_admissible (by decide)) with ⟨_, e⟩ | c
    · rcases node_binds e (textDigest_admissible hH _) (textDigest_admissible hH _) with ⟨en, e⟩ | c
      · rcases node_binds e (dataDigest_admissible hH _) (dataDigest_admissible hH _) with ⟨ed, er⟩ | c
        · rcases textDigest_binds hH en with rfl | c
          · rcases dataDigest_binds hH ed with rfl | c
            · rcases fieldsDigest_binds hH er with rfl | c
              · exact .inl rfl
              · exact .inr c
            · exact .inr c
          · exact .inr c
        · exact .inr c
      · exact .inr c
    · exact .inr c
end

/-- The content address of a term under `H`: the Merkle digest of its quotation. -/
def addressWith (H : Hash) (t : Term) : Nat := dataDigest H (quote t)

/-- **The content address**, under the deployed cSHAKE256. -/
def address (t : Term) : Nat := addressWith deployed t

theorem addressWith_binds {H : Hash} (hH : Short H) {t t' : Term}
    (h : addressWith H t = addressWith H t') : t = t' ∨ Collision H := by
  rcases dataDigest_binds hH h with e | c
  · exact .inl (quote_injective e)
  · exact .inr c

/-- **T2 `digest_of_quote`.** Two terms with one address are one term, or cSHAKE256 (at the
digest primitive's customization) has a collision. -/
theorem digest_of_quote {t t' : Term} (h : address t = address t') : t = t' ∨ Collision deployed :=
  addressWith_binds deployed_short h

/-- The refuting pole of T2: under a hash that reads only its input's length, `nat 1` and `nat 2`
have one address. Binding is carried by the hash, not by the encoding. -/
theorem lengthHash_address_collapses :
    addressWith lengthHash (.nat 1) = addressWith lengthHash (.nat 2) ∧ Term.nat 1 ≠ Term.nat 2 := by
  refine ⟨?_, by intro h; cases h⟩
  have leaf : digestWith lengthHash 0 1 = digestWith lengthHash 0 2 :=
    Obend.Core.Digest.lengthHash_binding_fails 0 1 2 (by decide)
  simp only [addressWith, quote, encode, shapeData, tagData, childrenData, dataDigest, fieldsDigest,
    leaf]

/-! ## §3. The encoding is versioned

`Term` has gained a constructor once (`hole`). A quotation crosses with the digest of the encoding
it was written in, and a reader refuses a tree from another encoding, naming both digests: a
quotation taken under an older `Term` is never silently re-read (orientation §8.1). -/

/-- A `Syntax` list: `nil` / `cons{head, tail}`. -/
def listData : List Data → Data
  | [] => .variant "nil" unit
  | d :: ds => .variant "cons" (.record [("head", d), ("tail", listData ds)])

def listOf : Data → Option (List Data)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", d), ("tail", ds)]) => (listOf ds).map (d :: ·)
  | _ => none

theorem listOf_listData : ∀ ds : List Data, listOf (listData ds) = some ds
  | [] => rfl
  | d :: ds => by simp [listData, listOf, listOf_listData ds]

/-- One representative of every tag constructor, in declaration order. -/
def tagRepresentatives : List Tag :=
  [.hole 0, .app, .mix, .fix, .specification, .prototype, .reflect, .metadata, .project, .ifBool,
    .perform, .done, .nat 0, .boolean false, .label "", .binary .add, .extend, .record, .ifZero,
    .case, .get "", .inject "", .field ""]

/-- The schema of an encoding: how it renders each tag, in order. -/
def schemaWith (render : Tag → Data) : Data := listData (tagRepresentatives.map render)

/-- The `Syntax` schema of this edition. -/
def syntaxSchema : Data := schemaWith tagData

/-- **The encoding's digest.** Never evaluated by a proof (one cSHAKE256 per node). -/
def encodingVersion : Nat := dataDigest deployed syntaxSchema

/-- Two encodings with one version render every tag alike, or cSHAKE256 collides. -/
theorem encodingVersion_binds {render : Tag → Data}
    (h : dataDigest deployed (schemaWith render) = encodingVersion) :
    schemaWith render = syntaxSchema ∨ Collision deployed :=
  dataDigest_binds deployed_short h

/-- The lossy rendering (`mix` as `app`) is another encoding: its schema differs from this
edition's, so its version differs or cSHAKE256 collides. -/
theorem lossy_schema_differs : schemaWith lossyTagData ≠ syntaxSchema := by
  intro h
  simp only [schemaWith, syntaxSchema, tagRepresentatives, List.map, listData, lossyTagData,
    tagData, Data.variant.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq] at h
  simp at h

/-- A quotation as it crosses: the encoding's digest, then the body. -/
def versioned (version : Nat) (body : Data) : Data :=
  .record [("encoding", .natural version), ("body", body)]

inductive VersionRefusal where
  /-- Not a versioned quotation at all. -/
  | malformed
  /-- Written in encoding `found`; this reader reads `expected`. -/
  | foreignEncoding (found expected : Nat)
  deriving Repr, DecidableEq

def readVersioned (expected : Nat) : Data → Except VersionRefusal Data
  | .record [("encoding", .natural found), ("body", body)] =>
      if found = expected then .ok body else .error (.foreignEncoding found expected)
  | _ => .error .malformed

theorem readVersioned_versioned (version : Nat) (body : Data) :
    readVersioned version (versioned version body) = .ok body := by
  simp [readVersioned, versioned]

/-- **`quote_versioned`.** A reader of encoding `expected` refuses a quotation written in
another encoding, naming both digests. -/
theorem quote_versioned {found expected : Nat} (differ : found ≠ expected) (body : Data) :
    readVersioned expected (versioned found body) = .error (.foreignEncoding found expected) := by
  simp [readVersioned, versioned, differ]

/-! ## §4. The `Syntax` built-in sum, as Objective Bend declares it

Like `SpecMeta`, a built-in sum resolved by bare name and declared by no module. A program sees a
quotation as a value of `Syntax`: binders are positions (`bind`), never depths, and nothing in it
is an address or a closure (orientation §2.3, §5). -/
def syntaxSource : String :=
  "sum Syntax:\n  var: Nat\n  bind: Syntax\n  node: {tag: SyntaxTag, children: SyntaxList}\n\n" ++
  "sum SyntaxList:\n  nil: {}\n  cons: {head: Syntax, tail: SyntaxList}\n\n" ++
  "sum SyntaxTag:\n  hole: Nat\n  app: {}\n  mix: {}\n  fix: {}\n  specification: {}\n" ++
  "  prototype: {}\n  reflect: {}\n  metadata: {}\n  project: {}\n  ifBool: {}\n  perform: {}\n" ++
  "  done: {}\n  nat: Nat\n  boolean: Bool\n  label: String\n  binary: String\n  extend: {}\n" ++
  "  record: {}\n  ifZero: {}\n  case: {}\n  get: String\n  inject: String\n  field: String\n"

/-! ## §5. Codecs for what a quotation carries besides its term

A held term is checked against annotations and assumptions. The annotations the kernel holds are a
finite `AnnotationTree` (the form full annotated completeness produces and the wire carries), so a
quotation carries them exactly; the assumptions are carried so that an importer can refuse a
quotation checked under another theory, by name. Lists are `Syntax` lists (`listData`). -/

open Obend.Core.Ty (Ty Quantity Reuse LambdaAnnotation Context Binding)
open Obend.Core.Check (Assumptions AnnotatedTerm Checked PartialTyping)
open Obend.Core.Bidirectional (CheckRefusal checkAgainst checkAgainst_sound)
open Obend.Core.Proofs.BidirectionalCompleteness (AnnotationTree treeAnnotations)

deriving instance DecidableEq for Obend.Core.Check.Assumptions

theorem mapM_roundtrip {α : Type} (f : Data → Option α) (g : α → Data)
    (h : ∀ x, f (g x) = some x) : ∀ xs : List α, (xs.map g).mapM f = some xs
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, h x, mapM_roundtrip f g h xs]

/-- A list of anything with a codec. -/
def listWith {α : Type} (g : α → Data) (xs : List α) : Data := listData (xs.map g)
def listOfWith {α : Type} (f : Data → Option α) (d : Data) : Option (List α) :=
  (listOf d).bind (·.mapM f)

theorem listOfWith_listWith {α : Type} (f : Data → Option α) (g : α → Data)
    (h : ∀ x, f (g x) = some x) (xs : List α) : listOfWith f (listWith g xs) = some xs := by
  simp [listOfWith, listWith, listOf_listData, mapM_roundtrip f g h xs]

def quantityData : Quantity → Data
  | .erased => .label "erased" | .affine => .label "affine"
  | .linear => .label "linear" | .unrestricted => .label "unrestricted"
def quantityOf : Data → Option Quantity
  | .label "erased" => some .erased | .label "affine" => some .affine
  | .label "linear" => some .linear | .label "unrestricted" => some .unrestricted
  | _ => none
theorem quantityOf_quantityData (q : Quantity) : quantityOf (quantityData q) = some q := by
  cases q <;> rfl

def reuseData : Reuse → Data
  | .once => .label "once" | .reusable => .label "reusable"
def reuseOf : Data → Option Reuse
  | .label "once" => some .once | .label "reusable" => some .reusable
  | _ => none
theorem reuseOf_reuseData (r : Reuse) : reuseOf (reuseData r) = some r := by
  cases r <;> rfl

def tyData : Ty → Data
  | .natural => .variant "natural" unit
  | .label => .variant "label" unit
  | .boolean => .variant "boolean" unit
  | .variable i => .variant "variable" (.natural i)
  | .arrow r q d c => .variant "arrow" (.record [("reuse", reuseData r), ("parameter", quantityData q),
      ("domain", tyData d), ("codomain", tyData c)])
  | .emptyRow => .variant "emptyRow" unit
  | .field n m t => .variant "field" (.record [("name", .label n), ("member", tyData m), ("tail", tyData t)])
  | .specification m e => .variant "specification" (.record [("metadata", tyData m), ("extension", tyData e)])
  | .prototype s t => .variant "prototype" (.record [("spec", tyData s), ("target", tyData t)])
  | .custody i => .variant "custody" (.natural i)
  | .variant r => .variant "variant" (tyData r)
  | .computation p r c => .variant "computation" (.record [("plan", tyData p), ("response", tyData r),
      ("result", tyData c)])

def tyOf : Data → Option Ty
  | .variant "natural" (.record []) => some .natural
  | .variant "label" (.record []) => some .label
  | .variant "boolean" (.record []) => some .boolean
  | .variant "variable" (.natural i) => some (.variable i)
  | .variant "arrow" (.record [("reuse", r), ("parameter", q), ("domain", d), ("codomain", c)]) => do
      pure (.arrow (← reuseOf r) (← quantityOf q) (← tyOf d) (← tyOf c))
  | .variant "emptyRow" (.record []) => some .emptyRow
  | .variant "field" (.record [("name", .label n), ("member", m), ("tail", t)]) => do
      pure (.field n (← tyOf m) (← tyOf t))
  | .variant "specification" (.record [("metadata", m), ("extension", e)]) => do
      pure (.specification (← tyOf m) (← tyOf e))
  | .variant "prototype" (.record [("spec", s), ("target", t)]) => do
      pure (.prototype (← tyOf s) (← tyOf t))
  | .variant "custody" (.natural i) => some (.custody i)
  | .variant "variant" r => (tyOf r).map .variant
  | .variant "computation" (.record [("plan", p), ("response", r), ("result", c)]) => do
      pure (.computation (← tyOf p) (← tyOf r) (← tyOf c))
  | _ => none

theorem tyOf_tyData : ∀ ty : Ty, tyOf (tyData ty) = some ty
  | .natural | .label | .boolean | .emptyRow => rfl
  | .variable i | .custody i => rfl
  | .arrow r q d c => by
    simp [tyData, tyOf, reuseOf_reuseData, quantityOf_quantityData, tyOf_tyData d, tyOf_tyData c]
  | .field n m t => by simp [tyData, tyOf, tyOf_tyData m, tyOf_tyData t]
  | .specification m e => by simp [tyData, tyOf, tyOf_tyData m, tyOf_tyData e]
  | .prototype s t => by simp [tyData, tyOf, tyOf_tyData s, tyOf_tyData t]
  | .variant r => by simp [tyData, tyOf, tyOf_tyData r]
  | .computation p r c => by simp [tyData, tyOf, tyOf_tyData p, tyOf_tyData r, tyOf_tyData c]

def annotationData (a : LambdaAnnotation) : Data :=
  .record [("domain", tyData a.domain), ("codomain", tyData a.codomain),
    ("parameter", quantityData a.parameter), ("reuse", reuseData a.reuse)]
def annotationOf : Data → Option LambdaAnnotation
  | .record [("domain", d), ("codomain", c), ("parameter", q), ("reuse", r)] => do
      pure ⟨← tyOf d, ← tyOf c, ← quantityOf q, ← reuseOf r⟩
  | _ => none
theorem annotationOf_annotationData (a : LambdaAnnotation) :
    annotationOf (annotationData a) = some a := by
  simp [annotationData, annotationOf, tyOf_tyData, quantityOf_quantityData, reuseOf_reuseData]

def optionData {α : Type} (g : α → Data) : Option α → Data
  | none => .variant "none" unit
  | some x => .variant "some" (g x)
def optionOf {α : Type} (f : Data → Option α) : Data → Option (Option α)
  | .variant "none" (.record []) => some none
  | .variant "some" x => (f x).map some
  | _ => none
theorem optionOf_optionData {α : Type} (f : Data → Option α) (g : α → Data)
    (h : ∀ x, f (g x) = some x) : ∀ o : Option α, optionOf f (optionData g o) = some o
  | none => rfl
  | some x => by simp [optionData, optionOf, h x]

mutual
def treeData : AnnotationTree → Data
  | .node here children => .record [("here", optionData annotationData here),
      ("children", forestData children)]
def forestData : List AnnotationTree → Data
  | [] => .variant "nil" unit
  | t :: ts => .variant "cons" (.record [("head", treeData t), ("tail", forestData ts)])
end

mutual
def treeOf : Data → Option AnnotationTree
  | .record [("here", here), ("children", children)] => do
      pure (.node (← optionOf annotationOf here) (← forestOf children))
  | _ => none
def forestOf : Data → Option (List AnnotationTree)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", h), ("tail", t)]) => do
      pure ((← treeOf h) :: (← forestOf t))
  | _ => none
end

mutual
theorem treeOf_treeData : ∀ t : AnnotationTree, treeOf (treeData t) = some t
  | .node here children => by
    simp [treeData, treeOf, optionOf_optionData annotationOf annotationData
      annotationOf_annotationData, forestOf_forestData children]
theorem forestOf_forestData : ∀ ts : List AnnotationTree, forestOf (forestData ts) = some ts
  | [] => rfl
  | t :: ts => by simp [forestData, forestOf, treeOf_treeData t, forestOf_forestData ts]
end

def boundData (b : Nat × Ty) : Data := .record [("index", .natural b.1), ("bound", tyData b.2)]
def boundOf : Data → Option (Nat × Ty)
  | .record [("index", .natural i), ("bound", ty)] => (tyOf ty).map (i, ·)
  | _ => none
theorem boundOf_boundData (b : Nat × Ty) : boundOf (boundData b) = some b := by
  simp [boundData, boundOf, tyOf_tyData]

def naturalOf : Data → Option Nat
  | .natural n => some n
  | _ => none

def assumptionsData (θ : Assumptions) : Data :=
  .record [("bounds", listWith boundData θ.bounds),
    ("shareableVariables", listWith Data.natural θ.shareableVariables),
    ("rigid", listWith Data.natural θ.rigid)]
def assumptionsOf : Data → Option Assumptions
  | .record [("bounds", b), ("shareableVariables", s), ("rigid", r)] => do
      pure ⟨← listOfWith boundOf b, ← listOfWith naturalOf s, ← listOfWith naturalOf r⟩
  | _ => none
theorem assumptionsOf_assumptionsData (θ : Assumptions) :
    assumptionsOf (assumptionsData θ) = some θ := by
  simp [assumptionsData, assumptionsOf, listOfWith_listWith boundOf boundData boundOf_boundData,
    listOfWith_listWith naturalOf Data.natural (fun _ => rfl)]

/-! ## §6. `Code Ψ A θ` and the checked importer -/

/-- A term as the kernel holds it: its finite annotation tree and the theory it is checked under. -/
structure Held where
  term : Term
  tree : AnnotationTree
  assumptions : Assumptions

@[expose] def Held.annotated (h : Held) : AnnotatedTerm := ⟨h.term, treeAnnotations h.tree, h.assumptions⟩

/-- **`Code Ψ A θ`**: a term typed at `A` in hypotheses `Ψ` under the theory `θ`. The typing is
`Typed` of the slot calculus (`Slot/Core4.lean`): a `Checked` certificate at type `A`. -/
@[expose] def Code (Ψ : Context) (A : Ty) (θ : Assumptions) : Type :=
  { t : AnnotatedTerm // t.assumptions = θ ∧ ∃ c : Checked t Ψ, c.type = A }

theorem Code.typed {Ψ : Context} {A : Ty} {θ : Assumptions} (c : Code Ψ A θ) :
    Obend.Slot.Core4.Typed Ψ c.val A := c.2.2

/-- The body of a quotation of held code. -/
def heldData (h : Held) : Data :=
  .record [("term", quote h.term), ("annotations", treeData h.tree),
    ("assumptions", assumptionsData h.assumptions)]
def heldOf : Data → Option Held
  | .record [("term", t), ("annotations", a), ("assumptions", θ)] => do
      pure ⟨← unquote t, ← treeOf a, ← assumptionsOf θ⟩
  | _ => none
theorem heldOf_heldData (h : Held) : heldOf (heldData h) = some h := by
  simp [heldData, heldOf, quote_roundtrip, treeOf_treeData, assumptionsOf_assumptionsData]

/-- A quotation of held code as it crosses: the encoding version, then the body. -/
def quotation (version : Nat) (h : Held) : Data := versioned version (heldData h)

/-! ### Diagnosis: the index that escaped, the hole that was found -/

mutual
/-- The first free index of a tree that escapes `n` hypotheses, counted at the root. -/
def escapeOf : Nat → Shape → Option Nat
  | n, .var i => if i < n then none else some i
  | n, .bind b => (escapeOf (n + 1) b).map (· - 1)
  | n, .node _ cs => escapesOf n cs
def escapesOf : Nat → List Shape → Option Nat
  | _, [] => none
  | n, c :: cs => match escapeOf n c with
    | some i => some i
    | none => escapesOf n cs
end

mutual
theorem escapeOf_scoped : ∀ (n : Nat) (s : Shape), Tree.Scoped n s → escapeOf n s = none
  | n, .var i, h => by simp only [Tree.Scoped, Tree.All] at h; simp [escapeOf, h]
  | n, .bind b, h => by
    rw [Obend.Core.Invariant.shape_scoped_bind] at h
    simp [escapeOf, escapeOf_scoped (n + 1) b h]
  | n, .node tag cs, h => by
    rw [Obend.Core.Invariant.shape_scoped_node] at h
    simp only [escapeOf]; exact escapesOf_scoped n cs h
theorem escapesOf_scoped : ∀ (n : Nat) (cs : List Shape), (∀ c ∈ cs, Tree.Scoped n c) →
    escapesOf n cs = none
  | _, [], _ => rfl
  | n, c :: cs, h => by
    simp only [escapesOf, escapeOf_scoped n c (h c (by simp))]
    exact escapesOf_scoped n cs (fun c' m => h c' (by simp [m]))
end

mutual
/-- The position (in the `Syntax` tree) and identity of the first hole. -/
def holeOf : Shape → Option (List Nat × Nat)
  | .var _ => none
  | .bind b => (holeOf b).map fun found => (0 :: found.1, found.2)
  | .node (.hole n) _ => some ([], n)
  | .node _ cs => holesOf 0 cs
def holesOf : Nat → List Shape → Option (List Nat × Nat)
  | _, [] => none
  | i, c :: cs => match holeOf c with
    | some found => some (i :: found.1, found.2)
    | none => holesOf (i + 1) cs
end

/-- A term with no hole anywhere: the shape of `Scoped`, without the `hole` rule. -/
inductive NoHole : Term → Prop where
  | bound (i : Nat) : NoHole (.bound i)
  | lam {b : Term} : NoHole b → NoHole (.lam b)
  | app {f a : Term} : NoHole f → NoHole a → NoHole (.app f a)
  | mix {a b : Term} : NoHole a → NoHole b → NoHole (.mix a b)
  | fix {a b : Term} : NoHole a → NoHole b → NoHole (.fix a b)
  | specification {a b : Term} : NoHole a → NoHole b → NoHole (.specification a b)
  | prototype {a b : Term} : NoHole a → NoHole b → NoHole (.prototype a b)
  | reflect {t : Term} : NoHole t → NoHole (.reflect t)
  | metadata {t : Term} : NoHole t → NoHole (.metadata t)
  | project {t : Term} : NoHole t → NoHole (.project t)
  | natural (v : Nat) : NoHole (.nat v)
  | boolean (v : Bool) : NoHole (.boolean v)
  | label (v : String) : NoHole (.label v)
  | binary {p : Primitive} {a b : Term} : NoHole a → NoHole b → NoHole (.binary p a b)
  | extend {t : Term} {fs : List (String × Term)} :
      NoHole t → (∀ f ∈ fs, NoHole f.2) → NoHole (.extend t fs)
  | record {fs : List (String × Term)} : (∀ f ∈ fs, NoHole f.2) → NoHole (.record fs)
  | get {t : Term} {name : String} : NoHole t → NoHole (.get t name)
  | condition {t z s : Term} : NoHole t → NoHole z → NoHole s → NoHole (.ifZero t z s)
  | inject {tag : String} {p : Term} : NoHole p → NoHole (.inject tag p)
  | case {t : Term} {arms : List (String × Term)} :
      NoHole t → (∀ arm ∈ arms, NoHole arm.2) → NoHole (.case t arms)
  | ifBool {c t f : Term} : NoHole c → NoHole t → NoHole f → NoHole (.ifBool c t f)
  | perform {plan : Term} : NoHole plan → NoHole (.perform plan)
  | done {value : Term} : NoHole value → NoHole (.done value)

/-- A typed term has no hole: `PartialTyping` has no rule for one. -/
theorem typed_noHole {θ : Assumptions} {Γ : Context} {t : Term} {A : Ty} {u : Obend.Core.Ty.Uses}
    (typed : PartialTyping θ Γ t A u) : NoHole t := by
  refine PartialTyping.rec
    (motive_1 := fun _ term _ _ _ => NoHole term)
    (motive_2 := fun _ fields _ _ _ => ∀ field ∈ fields, NoHole field.2)
    (motive_3 := fun _ _ arms _ _ _ _ => ∀ arm ∈ arms, NoHole arm.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intros; exact .bound _
  · intros; exact .natural _
  · intros; exact .boolean _
  · intros; exact .label _
  · intros; exact .lam (by assumption)
  · intros; assumption
  · intros; exact .app (by assumption) (by assumption)
  · intros; exact .record (by assumption)
  · intros; exact .get (by assumption)
  · intros; exact .extend (by assumption) (by assumption)
  · intros; exact .specification (by assumption) (by assumption)
  · intros; exact .prototype (by assumption) (by assumption)
  · intros; exact .reflect (by assumption)
  · intros; exact .metadata (by assumption)
  · intros; exact .project (by assumption)
  · intros; exact .mix (by assumption) (by assumption)
  · intros; exact .fix (by assumption) (by assumption)
  · intros; exact .binary (by assumption) (by assumption)
  · intros; exact .condition (by assumption) (by assumption) (by assumption)
  · intros; exact .inject (by assumption)
  · intros; exact .case (by assumption) (by assumption)
  · intros; exact .ifBool (by assumption) (by assumption) (by assumption)
  · intros; exact .perform (by assumption)
  · intros; exact .done (by assumption)
  · intros; exact .case (by assumption) (by assumption)
  · intro _ field member; simp at member
  · intro _ name body rest type row bu ru hb hr _ ihb ihr field member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihb
    · exact ihr field member
  · intro _ _ result arm member; simp at member
  · intro _ _ name body rest payload row result bu ru hb _ _ _ _ _ ihb ihr arm member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihb
    · exact ihr arm member

theorem holesOf_none {i : Nat} {cs : List Shape} (h : ∀ c ∈ cs, holeOf c = none) :
    holesOf i cs = none := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih =>
    simp only [holesOf, h c (by simp)]
    exact ih (fun c' m => h c' (by simp [m]))

theorem noHole_holeOf {t : Term} (h : NoHole t) : holeOf (encode t) = none := by
  induction h with
  | bound => simp [encode, holeOf]
  | lam _ ih => simp [encode, holeOf, ih]
  | app _ _ ih1 ih2 | mix _ _ ih1 ih2 | fix _ _ ih1 ih2 | specification _ _ ih1 ih2
  | prototype _ _ ih1 ih2 | binary _ _ ih1 ih2 =>
    simp only [encode, holeOf]; exact holesOf_none (by simp [ih1, ih2])
  | reflect _ ih | metadata _ ih | project _ ih | get _ ih | inject _ ih | perform _ ih | done _ ih =>
    simp only [encode, holeOf]; exact holesOf_none (by simp [ih])
  | natural | boolean | label => simp [encode, holeOf, holesOf]
  | extend _ _ iht ihf =>
    simp only [encode, holeOf]
    refine holesOf_none ?_
    simp only [List.mem_cons, List.mem_map]
    rintro c (rfl | ⟨f, hf, rfl⟩)
    · exact iht
    · simp only [holeOf]; exact holesOf_none (by simp [ihf f hf])
  | record _ ihf =>
    simp only [encode, holeOf]
    refine holesOf_none ?_
    simp only [List.mem_map]
    rintro c ⟨f, hf, rfl⟩
    simp only [holeOf]; exact holesOf_none (by simp [ihf f hf])
  | condition _ _ _ ih1 ih2 ih3 =>
    simp only [encode, holeOf]; exact holesOf_none (by simp [holeOf, ih1, ih2, ih3])
  | case _ _ iht iha =>
    simp only [encode, holeOf]
    refine holesOf_none ?_
    simp only [List.mem_cons, List.mem_map]
    rintro c (rfl | ⟨f, hf, rfl⟩)
    · exact iht
    · simp only [holeOf]; exact holesOf_none (by simp [holeOf, iha f hf])
  | ifBool _ _ _ ih1 ih2 ih3 =>
    simp only [encode, holeOf]; exact holesOf_none (by simp [ih1, ih2, ih3])

/-! ### The importer -/

inductive ImportRefusal where
  /-- Not a versioned quotation, or one written in another encoding (both digests named). -/
  | version (refusal : VersionRefusal)
  /-- The body is not a term, an annotation tree and a theory in this encoding. -/
  | malformed
  /-- Checked under `found`; this import is at `expected`. -/
  | assumptionsDiffer (found expected : Assumptions)
  /-- A free index escapes the hypotheses (counted at the root). -/
  | escapedIndex (index : Nat)
  /-- A hole, at its `Syntax` position: a term with a hole is data, never code. -/
  | holeInCode (position : List Nat) (identity : Nat)
  /-- The checker's own refusal, with its position. -/
  | rejected (refusal : CheckRefusal)

/-- Why the checker refused: an escaped index first, then a hole, else the checker's words. -/
def diagnose (Ψ : Context) (t : Term) (refusal : CheckRefusal) : ImportRefusal :=
  match escapeOf Ψ.length (encode t) with
  | some i => .escapedIndex i
  | none => match holeOf (encode t) with
    | some found => .holeInCode found.1 found.2
    | none => .rejected refusal

/-- Check a held term at `A` in `Ψ` under `θ`. -/
def checkHeld (Ψ : Context) (A : Ty) (θ : Assumptions) (h : Held) :
    Except ImportRefusal (Code Ψ A θ) :=
  if hθ : h.assumptions = θ then
    match accepted : checkAgainst h.annotated Ψ A with
    | .ok c => .ok ⟨h.annotated, hθ, c, (checkAgainst_sound accepted).1⟩
    | .error e => .error (diagnose Ψ h.term e)
  else .error (.assumptionsDiffer h.assumptions θ)

/-- **The checked importer** of a reader of encoding `version`. -/
def importWith (version : Nat) (Ψ : Context) (A : Ty) (θ : Assumptions) (d : Data) :
    Except ImportRefusal (Code Ψ A θ) :=
  match readVersioned version d with
  | .error e => .error (.version e)
  | .ok body => match heldOf body with
    | none => .error .malformed
    | some h => checkHeld Ψ A θ h

/-- The deployed importer reads this edition's encoding. -/
def «import» (Ψ : Context) (A : Ty) (θ : Assumptions) (d : Data) : Except ImportRefusal (Code Ψ A θ) :=
  importWith encodingVersion Ψ A θ d

theorem importWith_ok {version : Nat} {Ψ : Context} {A : Ty} {θ : Assumptions} {d : Data}
    {c : Code Ψ A θ} (h : importWith version Ψ A θ d = .ok c) :
    ∃ body held, readVersioned version d = .ok body ∧ heldOf body = some held ∧
      c.val = held.annotated ∧ ∃ k, checkAgainst held.annotated Ψ A = .ok k := by
  unfold importWith at h
  split at h
  · cases h
  · rename_i body hv
    split at h
    · cases h
    · rename_i held hb
      unfold checkHeld at h
      split at h
      · split at h
        · rename_i k hk
          cases h
          exact ⟨body, held, hv, hb, rfl, k, hk⟩
        · cases h
      · cases h

/-- **T6 `import_sound`.** An import is code under exactly the importer's theory, and the checker
accepted exactly the imported annotated term. -/
theorem import_sound {version : Nat} {Ψ : Context} {A : Ty} {θ : Assumptions} {d : Data}
    {c : Code Ψ A θ} (h : importWith version Ψ A θ d = .ok c) :
    c.val.assumptions = θ ∧ Obend.Slot.Core4.Typed Ψ c.val A ∧
      ∃ k, checkAgainst c.val Ψ A = .ok k := by
  obtain ⟨_, held, _, _, hc, k, hk⟩ := importWith_ok h
  refine ⟨c.2.1, c.typed, ?_⟩
  rw [hc]
  exact ⟨k, hk⟩

/-- **T8 `import_scoped`.** Code is scoped by its hypotheses: no index escapes `Ψ`. Every import is
code, so every import is scoped. -/
theorem code_scoped {Ψ : Context} {A : Ty} {θ : Assumptions} (c : Code Ψ A θ) :
    Obend.Core.Invariant.Scoped Ψ.length c.val.term := by
  obtain ⟨k, _⟩ := c.2.2
  exact Obend.Core.MachineTyping.source_scoped k.derivation

theorem import_scoped {version : Nat} {Ψ : Context} {A : Ty} {θ : Assumptions} {d : Data}
    {c : Code Ψ A θ} (_ : importWith version Ψ A θ d = .ok c) :
    Obend.Core.Invariant.Scoped Ψ.length c.val.term := code_scoped c

/-- Holes are never code (orientation §8.2). -/
theorem code_noHole {Ψ : Context} {A : Ty} {θ : Assumptions} (c : Code Ψ A θ) : NoHole c.val.term := by
  obtain ⟨k, _⟩ := c.2.2
  exact typed_noHole k.derivation

/-- **`splice_scoped`** (T8's second half): hypotheses `Scoped |Ψ|` substituted by fillings
`Scoped |Ψ′|` give a term `Scoped |Ψ′|`. -/
theorem splice_scoped {n m : Nat} {t : Term} (ht : Obend.Core.Invariant.Scoped n t)
    (σ : Nat → Term) (hσ : ∀ i, i < n → Obend.Core.Invariant.Scoped m (σ i)) :
    Obend.Core.Invariant.Scoped m (t.substitute σ) := by
  rw [Obend.Core.Invariant.scoped_encode_iff] at ht ⊢
  exact Obend.Core.TermTraverse.scoped_substitute t n m ht σ
    (fun i hi => (Obend.Core.Invariant.scoped_encode_iff m (σ i)).1 (hσ i hi))

/-- The quotation of an accepted held term imports to exactly that term. -/
theorem import_roundtrip (version : Nat) {Ψ : Context} {A : Ty} {θ : Assumptions} (held : Held)
    (hθ : held.assumptions = θ) {k : Checked held.annotated Ψ}
    (accepted : checkAgainst held.annotated Ψ A = .ok k) :
    ∃ c : Code Ψ A θ, importWith version Ψ A θ (quotation version held) = .ok c ∧
      c.val = held.annotated := by
  refine ⟨⟨held.annotated, hθ, k, (checkAgainst_sound accepted).1⟩, ?_, rfl⟩
  unfold importWith quotation
  rw [readVersioned_versioned]
  simp only [heldOf_heldData]
  unfold checkHeld
  rw [dite_eq_left_of_eq_true (eq_true hθ)]
  split
  · rename_i k' hk'
    rw [accepted] at hk'
  · rename_i e he
    rw [accepted] at he
    cases he

/-- Realizing an annotation tree at the root needs nothing: it is the tree's own lookup. -/
theorem treeAnnotations_realizes (tree : AnnotationTree) :
    Obend.Core.Proofs.BidirectionalCompleteness.Realizes (treeAnnotations tree) [] tree := by
  intro suffix; rfl

/-- Full annotated completeness with its witness in view: a derivation is accepted by the checker
under the annotations of some finite tree. -/
theorem tree_complete {θ : Assumptions} {Ψ : Context} {t : Term} {A : Ty} {u : Obend.Core.Ty.Uses}
    (typed : PartialTyping θ Ψ t A u) (safe : Obend.Core.Ty.safeUses Ψ u = true)
    (valid : Obend.Core.Ty.validContext θ.shareableVariables Ψ = true)
    (assumptionsValid : θ.valid = true) :
    ∃ tree k, checkAgainst ⟨t, treeAnnotations tree, θ⟩ Ψ A = .ok k := by
  obtain ⟨tree, completeTerm⟩ := Obend.Core.Proofs.BidirectionalCompleteness.complete typed
  have yielded := ((completeTerm (treeAnnotations tree) [] (treeAnnotations_realizes tree)).2 A
    (Obend.Core.Check.sameType_refl _ _))
  unfold Obend.Core.Proofs.BidirectionalCompleteness.Yields at yielded
  split at yielded
  · rename_i result accepted
    have safe' : Obend.Core.Ty.safeUses Ψ result.uses = true := by rw [yielded]; exact safe
    refine ⟨tree, ⟨A, result.uses, result.derivation, safe', valid, assumptionsValid⟩, ?_⟩
    simp only [checkAgainst, accepted, bind, Except.bind, Obend.Core.Bidirectional.need_ok safe',
      Obend.Core.Bidirectional.need_ok valid, Obend.Core.Bidirectional.need_ok assumptionsValid,
      pure, Except.pure]
  · exact yielded.elim

/-- **T6 `import_complete`.** Every code has a quotation (its term, under a finite annotation tree,
at its own theory) that imports back to its term. The tree is the importer's witness, not the
supplied annotations: an importer that trusted those would not be complete
(`annotation_presence_not_coverage`, and `empty_tree_refused` below). -/
theorem import_complete (version : Nat) {Ψ : Context} {A : Ty} {θ : Assumptions} (c : Code Ψ A θ) :
    ∃ tree, ∃ c' : Code Ψ A θ,
      importWith version Ψ A θ (quotation version ⟨c.val.term, tree, θ⟩) = .ok c' ∧
        c'.val.term = c.val.term := by
  obtain ⟨hθ, k, hk⟩ := c.2
  have derivation := k.derivation
  have safe := k.safe
  have valid := k.contextValid
  have av := k.assumptionsValid
  rw [hθ] at derivation valid av
  rw [hk] at derivation
  simp only [AnnotatedTerm.erase] at derivation
  obtain ⟨tree, k', accepted⟩ := tree_complete derivation safe valid av
  obtain ⟨c', hc', same⟩ := import_roundtrip version ⟨c.val.term, tree, θ⟩ rfl accepted
  exact ⟨tree, c', hc', by rw [same]; rfl⟩

/-! ### The refusals, each by name -/

theorem import_foreignEncoding {found version : Nat} (differ : found ≠ version) (Ψ : Context) (A : Ty)
    (θ : Assumptions) (held : Held) :
    importWith version Ψ A θ (quotation found held) =
      .error (.version (.foreignEncoding found version)) := by
  unfold importWith quotation
  rw [quote_versioned differ]

theorem import_assumptionsDiffer (version : Nat) (Ψ : Context) (A : Ty) {θ : Assumptions} {held : Held}
    (differ : held.assumptions ≠ θ) :
    importWith version Ψ A θ (quotation version held) = .error (.assumptionsDiffer held.assumptions θ) := by
  unfold importWith quotation
  rw [readVersioned_versioned]
  simp only [heldOf_heldData]
  unfold checkHeld
  rw [dite_eq_right_of_eq_false (eq_false differ)]

theorem checkHeld_refused {Ψ : Context} {A : Ty} {θ : Assumptions} {held : Held}
    (hθ : held.assumptions = θ) (refused : ∀ k, checkAgainst held.annotated Ψ A ≠ .ok k) :
    ∃ e, checkHeld Ψ A θ held = .error (diagnose Ψ held.term e) := by
  unfold checkHeld
  rw [dite_eq_left_of_eq_true (eq_true hθ)]
  split
  · rename_i k hk; exact absurd hk (refused k)
  · rename_i e _; exact ⟨e, rfl⟩

theorem accepted_typed {Ψ : Context} {A : Ty} {held : Held} {k : Checked held.annotated Ψ}
    (accepted : checkAgainst held.annotated Ψ A = .ok k) :
    PartialTyping held.assumptions Ψ held.term A k.uses := by
  have := (checkAgainst_sound accepted)
  rw [this.1] at this
  exact this.2

/-- **`escapedIndex`.** A quotation whose term has an index escaping `Ψ` is refused, naming the
index (counted at the root). -/
theorem import_escapedIndex (version : Nat) {Ψ : Context} (A : Ty) {θ : Assumptions} {held : Held}
    (hθ : held.assumptions = θ) {i : Nat} (escapes : escapeOf Ψ.length (encode held.term) = some i) :
    importWith version Ψ A θ (quotation version held) = .error (.escapedIndex i) := by
  have refused : ∀ k, checkAgainst held.annotated Ψ A ≠ .ok k := by
    intro k accepted
    have inScope := Obend.Core.MachineTyping.source_scoped (accepted_typed accepted)
    rw [Obend.Core.Invariant.scoped_encode_iff] at inScope
    rw [escapeOf_scoped _ _ inScope] at escapes
    cases escapes
  obtain ⟨e, he⟩ := checkHeld_refused hθ refused
  unfold importWith quotation
  rw [readVersioned_versioned]
  simp only [heldOf_heldData, he, diagnose, escapes]

/-- **`holeInCode`.** A quotation whose term has a hole is refused, naming its position. -/
theorem import_holeInCode (version : Nat) {Ψ : Context} (A : Ty) {θ : Assumptions} {held : Held}
    (hθ : held.assumptions = θ) (inScope : escapeOf Ψ.length (encode held.term) = none)
    {found : List Nat × Nat} (hole : holeOf (encode held.term) = some found) :
    importWith version Ψ A θ (quotation version held) = .error (.holeInCode found.1 found.2) := by
  have refused : ∀ k, checkAgainst held.annotated Ψ A ≠ .ok k := by
    intro k accepted
    rw [noHole_holeOf (typed_noHole (accepted_typed accepted))] at hole
    cases hole
  obtain ⟨e, he⟩ := checkHeld_refused hθ refused
  unfold importWith quotation
  rw [readVersioned_versioned]
  simp only [heldOf_heldData, he, diagnose, inScope, hole]

/-! ### Teeth: every refusal is reachable, and the tree is the importer's witness -/

theorem escape_tooth : escapeOf 0 (encode (.bound 0)) = some 0 := by simp [encode, escapeOf]

theorem hole_tooth : holeOf (encode (.lam (.hole 3 []))) = some ([0], 3) := by simp [encode, holeOf]

/-- The tooth of T8: `bound 0` quoted for an empty context is refused, naming index 0. -/
theorem escaped_import_tooth (version : Nat) :
    importWith version [] .natural {} (quotation version ⟨.bound 0, .node none [], {}⟩) =
      .error (.escapedIndex 0) :=
  import_escapedIndex (Ψ := []) (held := ⟨.bound 0, .node none [], {}⟩) version .natural rfl escape_tooth

theorem hole_scoped : escapeOf 0 (encode (.lam (.hole 3 []))) = none := by simp [encode, escapeOf, escapesOf]

/-- The tooth of `holeInCode`: a lambda over a hole is refused at the hole's position. -/
theorem hole_import_tooth (version : Nat) :
    importWith version [] .natural {} (quotation version ⟨.lam (.hole 3 []), .node none [], {}⟩) =
      .error (.holeInCode [0] 3) :=
  import_holeInCode (Ψ := []) (held := ⟨.lam (.hole 3 []), .node none [], {}⟩) version .natural rfl
    hole_scoped hole_tooth

/-- `λx. x` applied to `0`, typed at `Nat`: the lambda needs its annotation in synthesis. -/
def identityApplied : Term := .app (.lam (.bound 0)) (.nat 0)

/-- Under the empty tree the checker refuses it (no lambda annotation in synthesis position). -/
theorem empty_tree_refused :
    (checkAgainst ⟨identityApplied, treeAnnotations (.node none []), {}⟩ [] .natural).toBool = false := by
  decide +kernel

/-- Under the tree that annotates the lambda, it is accepted: the witness of `import_complete`
is the tree, and it exists. -/
def identityTree : AnnotationTree :=
  .node none [.node (some ⟨.natural, .natural, .unrestricted, .once⟩) []]

theorem identity_tree_accepted :
    (checkAgainst ⟨identityApplied, treeAnnotations identityTree, {}⟩ [] .natural).toBool = true := by
  decide +kernel

/-! ## §7. Mirrors: reflection is reached through a value one must hold

Bracha–Ungar's stratification as a lattice (orientation §2.10, §3.5): a `Mirror` is data naming a
held term and a depth `structure ⊑ metadata ⊑ code`; the kernel's `quote` answers only a mirror of
depth `code`; a mirror derived from a mirror is never deeper than its parent. -/

inductive Depth where
  | structure | metadata | code
  deriving DecidableEq, Repr

def Depth.rank : Depth → Nat
  | .structure => 0 | .metadata => 1 | .code => 2

instance : LE Depth := ⟨fun x y => x.rank ≤ y.rank⟩
instance (x y : Depth) : Decidable (x ≤ y) := inferInstanceAs (Decidable (x.rank ≤ y.rank))

theorem Depth.le_refl (d : Depth) : d ≤ d := Nat.le_refl d.rank
theorem Depth.le_trans {a b c : Depth} (h : a ≤ b) (h' : b ≤ c) : a ≤ c := Nat.le_trans h h'
theorem Depth.le_code (d : Depth) : d ≤ .code := by cases d <;> decide

structure Mirror where
  over : String
  depth : Depth
  deriving DecidableEq, Repr

/-- A mirror for `wanted`, derived from `m`: never deeper than `m`. -/
def Mirror.derive (m : Mirror) (wanted : Depth) : Mirror :=
  ⟨m.over, if wanted ≤ m.depth then wanted else m.depth⟩

/-- **T14 `mirror_attenuates`.** A derived mirror names the same target and is no deeper than its
parent, nor than what was asked for. -/
theorem mirror_attenuates (m : Mirror) (wanted : Depth) :
    (m.derive wanted).over = m.over ∧ (m.derive wanted).depth ≤ m.depth ∧
      (m.derive wanted).depth ≤ wanted := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [Mirror.derive] <;> split
  · assumption
  · exact Depth.le_refl _
  · exact Depth.le_refl _
  · rename_i h
    have : ¬ wanted.rank ≤ m.depth.rank := h
    show m.depth.rank ≤ wanted.rank
    omega

/-- No chain of derivations amplifies. -/
theorem derive_chain (m : Mirror) : ∀ ds : List Depth, (ds.foldl Mirror.derive m).depth ≤ m.depth
  | [] => Depth.le_refl _
  | d :: ds => Depth.le_trans (derive_chain (m.derive d) ds) (mirror_attenuates m d).2.1

def depthData : Depth → Data
  | .structure => .label "structure" | .metadata => .label "metadata" | .code => .label "code"
def depthOf : Data → Option Depth
  | .label "structure" => some .structure | .label "metadata" => some .metadata
  | .label "code" => some .code | _ => none

/-- A mirror is data: a program holds it and hands it back. -/
def mirrorData (m : Mirror) : Data := .record [("over", .label m.over), ("depth", depthData m.depth)]
def mirrorOf : Data → Option Mirror
  | .record [("over", .label over), ("depth", d)] => (depthOf d).map (⟨over, ·⟩)
  | _ => none
theorem mirrorOf_mirrorData (m : Mirror) : mirrorOf (mirrorData m) = some m := by
  cases m with | mk over depth => cases depth <;> rfl

inductive MirrorRefusal where
  /-- No held term has this name. -/
  | unknown (over : String)
  /-- The mirror held is too shallow for the operation (named with its depth). -/
  | shallow (over : String) (held : Depth)
  deriving DecidableEq, Repr

/-- **The kernel's `quote` through a mirror**: only a mirror of depth `code` is answered. -/
def quoteVia (store : String → Option Held) (version : Nat) (m : Mirror) : Except MirrorRefusal Data :=
  match store m.over with
  | none => .error (.unknown m.over)
  | some h => if m.depth = .code then .ok (quotation version h) else .error (.shallow m.over m.depth)

theorem quoteVia_ok {store : String → Option Held} {version : Nat} {m : Mirror} {d : Data}
    (h : quoteVia store version m = .ok d) :
    m.depth = .code ∧ ∃ held, store m.over = some held ∧ d = quotation version held := by
  unfold quoteVia at h
  split at h
  · cases h
  · rename_i held hs
    split at h
    · cases h; exact ⟨by assumption, held, hs, rfl⟩
    · cases h

theorem quoteVia_code {store : String → Option Held} {version : Nat} {m : Mirror} {held : Held}
    (hs : store m.over = some held) (hd : m.depth = .code) :
    quoteVia store version m = .ok (quotation version held) := by
  simp [quoteVia, hs, hd]

/-- The tooth of T14: a `metadata` mirror cannot quote, whatever it names, and nothing derived
from it can. -/
theorem metadata_mirror_cannot_quote (store : String → Option Held) (version : Nat) (over : String)
    (held : Held) (hs : store over = some held) (ds : List Depth) :
    quoteVia store version ⟨over, .metadata⟩ = .error (.shallow over .metadata) ∧
      ∀ d, quoteVia store version (ds.foldl Mirror.derive ⟨over, .metadata⟩) ≠ .ok d := by
  refine ⟨by simp [quoteVia, hs], fun d h => ?_⟩
  have := (quoteVia_ok h).1
  have chain := derive_chain ⟨over, .metadata⟩ ds
  rw [this] at chain
  exact absurd chain (by show ¬ (2 ≤ 1); decide)

end Obend.Core.Code
end
