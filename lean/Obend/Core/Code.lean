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
public import Obend.Tactic.Tooth
@[expose] public section
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

def tagOf : Data → Option Tag
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
def childrenData : List Shape → Data
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
def quote (t : Term) : Data := shapeData (encode t)

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
  intro bytes; simp [deployed, Obend.Digest.cshake_hash]

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

end Obend.Core.Code
end
