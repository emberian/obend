module
/-
# Obend.Core.Nominal — a kind's identity on the record types of Core4

Decided 2026-11-01 (contract C1, `review/DECISIONS-20261031.md`; `astra/ASTRA-DECISIONS-20261101.md`
§3): kinds are nominal in type checking, not only at direct calls. A kind's stable identity (its
declaring module and name, `KindId`) is written ON its record type as a BRAND: the field `#kind`
whose member is the one-label sum `kindTy k`, and whose value is that sum's one constructor.
`Ty.kinded k layout` is the type of an instance of `k` with fields `layout`. A record type with no
brand is an anonymous structural record, the separate facility it always was.

Why a field and not a new `Ty` constructor or a rigid variable: the brand rides on every rule the
checker already has. Two kinds with equal layouts are two rows whose `#kind` members are different
sums, and they never agree, at the root (`kinded_refuses`) or under any constructor
(`kinded_domain_refuses`, the higher-order crossing). Every position a record reaches (a
quotation's type, an import's expected type, an arrow's domain, a Plan's payload, a checkpoint)
carries the brand without a rule of its own; first-order data stays data (`Ty.isData`), which a
rigid variable is not. No typing rule, `Term` constructor or machine step is added, so every
theorem of the calculus holds of kinded programs as it stood. One label for every kind means an
extension that constructs an instance of another kind overwrites the brand (`extend` keeps the
first field of a name), so an object grown layer by layer (`X`, then `XY`) is at each layer the
kind that layer declares.

What a brand is not: an authority. A Core term that writes the brand builds an instance of the
kind; the front end writes it only where a record is constructed at the kind
(`Obend.Spec.Elaborate.brandAt`: a literal or an extension checked against it), and `#kind` is no
source identifier. A representation is extracted by reading fields, never by dropping the brand
(there is no width subtyping to drop it). The version of a kind's layout, law and methods is not in
the brand: an identity is stable across revisions, and which revision a quotation was checked under
is the pin it carries (`Obend.Core.Code`).
-/
public import Obend.Core.Brand
public import Obend.Core.Data
public import Obend.Core.Check
public import Obend.Core.TypeGraphHead
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.Bidirectional
public section
namespace Obend.Core.Nominal
open Obend.Core.Ty Obend.Core.Check Obend.Core.TypeGraph Obend.Core.AliasExposure
set_option autoImplicit false

export Obend.Core.Brand (KindId brandLabel isBrand)

/-- The member of an instance's brand: the one-label sum naming its kind. -/
@[expose] def kindTy (k : KindId) : Ty := .variant (.field k .emptyRow .emptyRow)

/-- **An instance's type**: kind `k`'s brand, then its layout. -/
@[expose] def _root_.Obend.Core.Ty.Ty.kinded (k : KindId) (layout : Ty) : Ty := .field brandLabel (kindTy k) layout

/-- The labels the type graph shows of a row at its root (through aliases); `[]` for a non-row. -/
@[expose] def rowLabels (θ : Assumptions) (t : Ty) : List String :=
  match (graph θ).label (.type t) with
  | .row labels _ _ => labels
  | _ => []

/-- **Agreement keeps every row label, so every brand**: types the checker agrees on show one
label list at their roots, and name one set of kinds. -/
theorem sameType_rowLabels {θ : Assumptions} {a b : Ty} (h : sameType θ a b = true) :
    rowLabels θ a = rowLabels θ b := by
  have related := (sameType_iff θ a b).mp h
  have labels := (Obend.Core.FinitePresentation.bisimilar_closed _ _ _ related).1
  unfold rowLabels
  rw [labels]

/-- A closed one-field row shows exactly its label. -/
theorem single_rowLabels (θ : Assumptions) (name : String) (member : Ty) :
    rowLabels θ (.field name member .emptyRow) = [name] := by
  have present : Ty.field name member .emptyRow ∈
      support θ (.field name member .emptyRow) (.field name member .emptyRow) := left_mem_support _ _ _
  unfold rowLabels
  simp only [graph, observe, expose, exposeWalk, constructorHead, rowTag, ↓reduceIte, rowObservation]
  unfold Obend.Core.RecursiveRows.labels
  rw [Obend.Core.RecursiveRows.scanLabels]
  simp only [expose, exposeWalk, constructorHead, present, ↓reduceDIte]
  rw [Obend.Core.RecursiveRows.scanLabels]
  simp [expose, exposeWalk, constructorHead, Obend.Core.RecursiveRows.insertLabel]

/-- Two kind sums agree only when they name one kind. -/
theorem kindTy_agree {θ : Assumptions} {k k' : KindId} (h : Equivalent θ (kindTy k) (kindTy k')) : k = k' := by
  have rows := variant_components h
  have labels := sameType_rowLabels ((sameType_iff θ _ _).mpr rows)
  simp only [single_rowLabels, List.cons.injEq, and_true] at labels
  exact labels

/-- The brand of an instance's type is what its row gives `#kind`. -/
theorem kinded_lookup (θ : Assumptions) (k : KindId) (layout : Ty) :
    (Ty.kinded k layout).lookup θ.bounds 1 brandLabel = some (kindTy k) := by
  simp [Ty.kinded, Ty.lookup]

/-- **Kinds are nominal in checking**: an instance of `k` never agrees with a type whose `#kind`
member is another kind's, whatever the two layouts. -/
theorem kinded_refuses {θ : Assumptions} {k k' : KindId} {layout other : Ty} {fuel : Nat}
    (differ : k ≠ k') (brand : other.lookup θ.bounds fuel brandLabel = some (kindTy k')) :
    sameType θ (Ty.kinded k layout) other = false := by
  cases h : sameType θ (Ty.kinded k layout) other
  · rfl
  · obtain ⟨depth, member, found, related⟩ :=
      Obend.Core.TypeGraph.equivalent_lookup_transport ((sameType_iff θ _ _).mp h) fuel brandLabel _ brand
    have own : (Ty.kinded k layout).lookup θ.bounds (max depth 1) brandLabel = some (kindTy k) :=
      Ty.lookup_mono (kinded_lookup θ k layout) (Nat.le_max_right _ _)
    rw [Ty.lookup_mono found (Nat.le_max_left _ _)] at own
    cases own
    exact absurd (kindTy_agree related) differ

/-- Two kinds, whatever their layouts, never agree. -/
theorem kinds_never_agree {θ : Assumptions} {k k' : KindId} (layout layout' : Ty) (differ : k ≠ k') :
    sameType θ (Ty.kinded k layout) (Ty.kinded k' layout') = false :=
  kinded_refuses differ (kinded_lookup θ k' layout')

/-- **The higher-order crossing**: a function over instances of `k` never agrees with a function
over instances of another kind (a `Kilo → Nat` is not a `Mile → Nat`), whatever the layouts,
codomains, reuses and quantities. -/
theorem kinded_domain_refuses {θ : Assumptions} {k k' : KindId} {layout other codomain codomain' : Ty}
    {reuse reuse' : Reuse} {q q' : Quantity} {fuel : Nat} (differ : k ≠ k')
    (brand : other.lookup θ.bounds fuel brandLabel = some (kindTy k')) :
    sameType θ (.arrow reuse q (Ty.kinded k layout) codomain) (.arrow reuse' q' other codomain') = false := by
  cases h : sameType θ (.arrow reuse q (Ty.kinded k layout) codomain) (.arrow reuse' q' other codomain')
  · rfl
  · obtain ⟨_, _, domains, _⟩ := arrow_components ((sameType_iff θ _ _).mp h)
    have := kinded_refuses (layout := layout) differ brand
    rw [(sameType_iff θ _ _).mpr domains] at this
    cases this

/-! ## Naming the kinds a refusal crossed -/

/-- The kind a brand member names. -/
@[expose] def kindOfMember : Ty → Option KindId
  | .variant (.field k _ _) => some k
  | _ => none

/-- The kind a row names syntactically: its first brand field's. -/
@[expose] def kindOf : Ty → Option KindId
  | .field name m tail => if isBrand name then kindOfMember m else kindOf tail
  | _ => none

/-- The first position, in a syntactic walk of two types side by side, where they name different
kinds: `(expected, actual)`. A diagnosis for a refusal, never a judgment. -/
@[expose] def kindClash : Ty → Ty → Option (KindId × KindId)
  | .arrow _ _ d c, .arrow _ _ d' c' => (kindClash d d').or (kindClash c c')
  | .variant r, .variant r' => kindClash r r'
  | .computation p r a, .computation p' r' a' => ((kindClash p p').or (kindClash r r')).or (kindClash a a')
  | .specification m e, .specification m' e' => (kindClash m m').or (kindClash e e')
  | .prototype s t, .prototype s' t' => (kindClash s s').or (kindClash t t')
  | e@(.field ..), a@(.field ..) =>
    match kindOf e, kindOf a with
    | some k, some k' => if k = k' then none else some (k, k')
    | some k, none => some (k, "(no kind)")
    | none, some k' => some ("(no kind)", k')
    | none, none => none
  | _, _ => none

/-- A checker refusal that crossed two kinds, named: `(path, expected kind, actual kind)`. -/
@[expose] def crossedKinds : Obend.Core.Bidirectional.CheckRefusal → Option (List Nat × KindId × KindId)
  | .typeMismatch path expected actual => (kindClash expected actual).map fun (k, k') => (path, k, k')
  | _ => none

/-! ## Data at a kind

The data wire does not carry brands (`Obend.Spec.DataWire`): a reply or an argument read from the
wire is constructed at its declared type, so the reader writes back each brand that type names. -/

/-- A row's member type by label, syntactically. -/
@[expose] def memberOf : Ty → String → Option Ty
  | .field n m t, l => if n = l then some m else memberOf t l
  | _, _ => none

mutual
/-- **Data constructed at a type**: every record the type declares a kind of carries that kind's
brand. Conformance (`Data.conforms`) is checked after, never assumed. -/
@[expose] def brandData : Nat → Ty → Obend.Core.Data.Data → Obend.Core.Data.Data
  | 0, _, d => d
  | n + 1, t, .record fs =>
    let fs' := brandFieldsData n t fs
    match kindOf t with
    | some k => if fs.any (·.1 == brandLabel) then .record fs' else .record ((brandLabel, .variant k (.record [])) :: fs')
    | none => .record fs'
  | n + 1, .variant row, .variant l p => .variant l (match memberOf row l with
    | some m => brandData n m p
    | none => p)
  | _ + 1, _, d => d
@[expose] def brandFieldsData : Nat → Ty → List (String × Obend.Core.Data.Data) → List (String × Obend.Core.Data.Data)
  | _, _, [] => []
  | n, t, (l, v) :: rest => (l, match memberOf t l with
    | some m => brandData n m v
    | none => v) :: brandFieldsData n t rest
end

/-! ## Teeth: Mile and Kilo, the same layout -/

/-- One layout, two kinds. -/
@[expose] def distance : Ty := .field "n" .natural .emptyRow
@[expose] def mile : Ty := Ty.kinded "Units.Mile" distance
@[expose] def kilo : Ty := Ty.kinded "Units.Kilo" distance

/-- `λf. f`, typed `(Kilo → Nat) → (Kilo → Nat)` by its annotation, checked at
`(Kilo → Nat) → (Mile → Nat)`: the higher-order Kilo-to-Mile crossing. -/
@[expose] def crossing : AnnotatedTerm :=
  ⟨.lam (.bound 0), fun p => if p = [] then
    some ⟨.arrow .reusable .unrestricted kilo .natural, .arrow .reusable .unrestricted kilo .natural,
      .unrestricted, .reusable⟩ else none, {}⟩

@[expose] def crossingType : Ty :=
  .arrow .reusable .unrestricted (.arrow .reusable .unrestricted kilo .natural)
    (.arrow .reusable .unrestricted mile .natural)

end Obend.Core.Nominal

end
