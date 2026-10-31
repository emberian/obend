module
/-
# Obend.Logic.LateBinding — the frame rule of the claim logic

`review/PROGRAM-LOGIC-20261101.md` §2.7, §5.3 T1. A spec layer is lowered by the elaborator
(`Obend.Spec.Elaborate` `layerAt`, `chainFix`) to `specification META (λself. λsuper. extend super
{defs})`, and `compose(a, b)` (`composeStep`) to `specification (composed{…}) (mix a b)`, folded left
over the operands (no β redexes since `1e039ff`; the composed metadata is carried by the layer the
step adds, `composeMeta`). `fix` of such a chain over a record seed is the object `O`.

**Late binding** (`late_binding`): `O.m` reduces to the body of the *outermost* layer providing `m`,
with `self := O` and `super :=` the row beneath that layer (`superAt`), which is the composition of
the layers beneath it applied to `O` and the seed. The proof is a finite reduction: `Step.fix`, the
composition's two β steps, `applySpecification` and `mix_apply` per layer, the layer's own two β
steps, `extendTarget` until the inherited row is a record, `extendRecord`, and `Step.field`, whose
`find?` meets the outermost provider first because `extendFields` lists the new fields first.

Compositions are written **outermost layer first** (a stack): `compose(Base, Twice, Augmented)`
is `⟨Augmented, [Twice, Base], seed⟩`, and a layer's index counts from the outside (`0` is the
last layer of the source composition). `providesLast` is the first index in that order whose layer
lists the member.

Elaborate emits two layer shapes (`layerAt`): `λself. λsuper. extend super {defs}`, and, over a
recursive record target, the flat delegating `λself. λsuper. {f = def or super.f, …}` naming every
field of the row. A delegating layer hides the row beneath it from `providesLast`, and its
delegation entries `super.f` are chased by `unfoldIn` through `late_binding_at`, the suffix form of
T1 that is also the late binding of `super.p` at a prefix (`superBelow` of any suffix).

The right-hand side is one parallel substitution (`openTerm`: `0 ↦ super`, `1 ↦ self`, `k+2 ↦ k`),
which is exactly what the two β steps leave (`open_sequential`), with no closedness hypothesis.

`object_bequiv_of_operands`: the elaborator's operands are knot references that *reduce* to the
layer terms; the object built from the operands is `≈b` the object built from the layers, so a fact
about the decoded composition is a fact about the program's own `fix`.
-/
public import Obend.Equiv.Behaviour
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Equiv
set_option autoImplicit false

/-! ## The lowered shapes -/

/-- A spec layer: its declared metadata and its methods, each under the layer's two binders
(`super` at index 0, `self` at index 1). -/
structure Layer where
  name : String
  metadata : Term
  fields : List (String × Term)
  /-- the delegating record shape (a recursive record target), else `extend` -/
  flat : Bool := false
  /-- the metadata of the `compose` step that adds this layer over the ones beneath it (unused for
  the innermost layer) -/
  composeMeta : Term := .record []

/-- What a layer returns over the row beneath it: `extend super {defs}`, or the flat record. -/
def Layer.provide (L : Layer) (sup : Term) (fields : List (String × Term)) : Term :=
  if L.flat then .record fields else .extend sup fields

/-- `λself. λsuper. extend super {defs}`, or `λself. λsuper. {defs}` (Elaborate `layerAt`). -/
def Layer.extension (L : Layer) : Term := .lam (.lam (L.provide (.bound 0) L.fields))

/-- The layer as the chain operand reduces to: `specification META extension`. -/
def Layer.term (L : Layer) : Term := .specification L.metadata L.extension

/-- The layer lists the member. -/
def Layer.provides (L : Layer) (m : String) : Bool := L.fields.any (·.1 == m)

/-- The layer's body for the member, under its two binders. -/
def Layer.body (L : Layer) (m : String) : Option Term := (L.fields.find? (·.1 == m)).map (·.2)

/-- One composition step over lowered operands (Elaborate `composeStep`):
`specification (composed{…}) (mix value right)`. -/
def composeStep (md value right : Term) : Term := .specification md (.mix value right)

/-- The composition of a stack (outermost first) with operand terms `op`: the left fold of the
elaborator, seen from its last operand. -/
def composeWith (op : Layer → Term) : Layer → List Layer → Term
  | top, [] => op top
  | top, next :: rest => composeStep top.composeMeta (composeWith op next rest) (op top)

/-- The composition of the layer terms. -/
def composeTerm (top : Layer) (below : List Layer) : Term := composeWith Layer.term top below

/-- A composition closed by `fix` over a record seed: outermost layer first. -/
structure Composition where
  top : Layer
  below : List Layer
  seed : List (String × Term)

namespace Composition

def layers (C : Composition) : List Layer := C.top :: C.below

/-- The object: `fix (compose …) seed`. -/
def object (C : Composition) : Term := .fix (composeTerm C.top C.below) (.record C.seed)

end Composition

/-- The row beneath a suffix of the stack, as a term over the object `O`: the seed beneath the
innermost layer, else the composition of the suffix applied to `O` and the seed. -/
def superBelow (O : Term) (seed : List (String × Term)) : List Layer → Term
  | [] => .record seed
  | next :: rest => .app (.app (composeTerm next rest) O) (.record seed)

/-- `super := sup`, `self := O`, every other index down by two. -/
def selfSuper (O sup : Term) : Nat → Term
  | 0 => sup
  | 1 => O
  | k + 2 => .bound k

/-- A layer body with `self := O` and `super := sup`: one parallel substitution. -/
def openTerm (t O sup : Term) : Term := t.substitute (selfSuper O sup)

/-- The two β steps leave exactly the parallel substitution. -/
theorem open_sequential (t O sup : Term) :
    (t.substitute (liftSubstitution (single O))).substitute (single sup) = openTerm t O sup := by
  rw [Obend.Core.TermTraverse.substitute_comp]
  unfold openTerm
  congr 1; funext i
  match i with
  | 0 => simp [liftSubstitution, single, Term.substitute, selfSuper]
  | 1 => simp [liftSubstitution, single, selfSuper, shift_one_cancel]
  | k + 2 => simp [liftSubstitution, single, selfSuper, Term.rename, Term.substitute]

def openFields (fields : List (String × Term)) (O sup : Term) : List (String × Term) :=
  fields.map fun f => (f.1, openTerm f.2 O sup)

/-- The record a suffix of the stack reduces to over the object `O`. -/
def rowOf (O : Term) (seed : List (String × Term)) : List Layer → List (String × Term)
  | [] => seed
  | L :: rest => if L.flat then openFields L.fields O (superBelow O seed rest)
      else extendFields (rowOf O seed rest) (openFields L.fields O (superBelow O seed rest))

/-- The index (outermost first) of the last layer of the composition giving `m` an entry; a flat
layer hides the row beneath it. -/
def providesLast : List Layer → String → Option Nat
  | [], _ => none
  | L :: rest, m => if L.provides m then some 0 else if L.flat then none else (providesLast rest m).map (· + 1)

/-- The body the `j`-th layer gives `m`. -/
def bodyAt (layers : List Layer) (j : Nat) (m : String) : Option Term := layers[j]?.bind (·.body m)

namespace Composition

/-- The `super` a claim or method of layer `j` sees in the object: the row beneath it. -/
def superAt (C : Composition) (j : Nat) : Term := superBelow C.object C.seed (C.layers.drop (j + 1))

end Composition

/-- A delegation entry: `super.m` under the layer's binders. -/
def isDelegation (b : Term) (m : String) : Bool :=
  match b with
  | .get (.bound 0) m' => m' == m
  | _ => false

/-- What `(superBelow O seed ls).m` unfolds to by late binding, delegations chased: the index (in
`ls`) of the providing layer and the opened body. -/
def unfoldIn (O : Term) (seed : List (String × Term)) : Nat → List Layer → String → Option (Nat × Term)
  | 0, _, _ => none
  | fuel + 1, ls, m =>
    match providesLast ls m with
    | some j => match bodyAt ls j m with
      | some b =>
        if isDelegation b m then (unfoldIn O seed fuel (ls.drop (j + 1)) m).map fun (i, u) => (i + j + 1, u)
        else some (j, openTerm b O (superBelow O seed (ls.drop (j + 1))))
      | none => none
    | none => none

namespace Composition

/-- What `O.m` unfolds to by late binding: the index of the last provider and its body with
`self := O`, `super := superAt`; none when no layer provides `m`. -/
def unfold (C : Composition) (m : String) : Option (Nat × Term) :=
  unfoldIn C.object C.seed C.layers.length C.layers m

end Composition

/-! ## The reduction -/

theorem steps_app_fn {f f' : Term} (a : Term) (h : Steps f f') : Steps (.app f a) (.app f' a) :=
  steps_congr (fun x => .app x a) (fun s => .application _ s) h

theorem steps_get {t t' : Term} (m : String) (h : Steps t t') : Steps (.get t m) (.get t' m) :=
  steps_congr (fun x => .get x m) (fun s => .target _ s) h

theorem steps_extend {t t' : Term} (fs : List (String × Term)) (h : Steps t t') :
    Steps (.extend t fs) (.extend t' fs) :=
  steps_congr (fun x => .extend x fs) (fun s => .extendTarget _ s) h

theorem openFields_eq (fields : List (String × Term)) (O sup : Term) :
    ((fields.map fun f => (f.1, f.2.substitute (liftSubstitution (single O)))).map
      fun f => (f.1, f.2.substitute (single sup))) = openFields fields O sup := by
  simp [openFields, List.map_map, Function.comp_def, open_sequential]

/-- A layer applied to the object and the row beneath it: four steps to what it provides. -/
theorem layer_apply (L : Layer) (O sup : Term) :
    Steps (.app (.app L.term O) sup) (L.provide sup (openFields L.fields O sup)) := by
  refine .next (.application _ (.applySpecification _ _ _)) ?_
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq]
  unfold Layer.provide
  cases L.flat
  · simp only [Bool.false_eq_true, ite_false, Term.substitute, liftSubstitution, single]
    rw [openFields_eq]; exact .refl _
  · simp only [ite_true, Term.substitute]
    rw [openFields_eq]; exact .refl _

/-- A composition step applied to the object and a row: `Y O (X O s)`. -/
theorem compose_apply (md X Y O s : Term) :
    Steps (.app (.app (composeStep md X Y) O) s) (.app (.app Y O) (.app (.app X O) s)) :=
  .next (.application _ (.applySpecification _ _ _)) (mix_apply _ _ _ _)

/-- The outermost layer of a suffix, applied: what it provides over the row beneath it. -/
theorem superBelow_cons (O : Term) (seed : List (String × Term)) (L : Layer) (rest : List Layer) :
    Steps (superBelow O seed (L :: rest))
      (L.provide (superBelow O seed rest) (openFields L.fields O (superBelow O seed rest))) := by
  cases rest with
  | nil => exact layer_apply L O _
  | cons next rest =>
    simp only [superBelow, composeTerm, composeWith]
    exact steps_trans (compose_apply _ _ _ _ _) (layer_apply L O _)

/-- Every suffix of the stack reduces to its record over any `O`. -/
theorem superBelow_record (O : Term) (seed : List (String × Term)) :
    (ls : List Layer) → Steps (superBelow O seed ls) (.record (rowOf O seed ls))
  | [] => .refl _
  | L :: rest => by
    refine steps_trans (superBelow_cons O seed L rest) ?_
    unfold Layer.provide
    simp only [rowOf]
    cases L.flat
    · simp only [Bool.false_eq_true, ite_false]
      exact steps_trans (steps_extend _ (superBelow_record O seed rest)) (steps_one (.extendRecord _ _))
    · exact .refl _

theorem find_openFields (fields : List (String × Term)) (O sup : Term) (m : String) :
    (openFields fields O sup).find? (·.1 == m) =
      (fields.find? (·.1 == m)).map fun f => (f.1, openTerm f.2 O sup) := by
  simp [openFields, List.find?_map, Function.comp_def]

theorem find_filter_none {fs inherited : List (String × Term)} {m : String}
    (h : fs.find? (·.1 == m) = none) :
    (inherited.filter fun prior => !(fs.any fun field => field.1 == prior.1)).find? (·.1 == m) =
      inherited.find? (·.1 == m) := by
  induction inherited with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : p.1 = m
    · obtain ⟨n, t⟩ := p
      simp only at hp
      subst hp
      have hany : (fs.any fun field => field.1 == n) = false := by
        rw [List.any_eq_false]
        intro f hf hfm
        rw [List.find?_eq_none] at h
        exact absurd hfm (h f hf)
      rw [List.filter_cons, hany]
      simp
    · simp only [List.filter_cons]
      split
      · simp [hp, ih]
      · simp [hp, ih]

/-- `find?` on an extended row: the new fields first. -/
theorem find_extendFields (inherited fs : List (String × Term)) (m : String) :
    (extendFields inherited fs).find? (·.1 == m) =
      match fs.find? (·.1 == m) with
      | some p => some p
      | none => inherited.find? (·.1 == m) := by
  unfold extendFields
  rw [List.find?_append]
  cases h : fs.find? (·.1 == m) with
  | some p => rfl
  | none => simp only [Option.none_or]; exact find_filter_none h

theorem find_name {fs : List (String × Term)} {m : String} {p : String × Term}
    (h : fs.find? (·.1 == m) = some p) : p.1 = m := by
  have := List.find?_some h
  simpa using this

theorem body_none {L : Layer} {m : String} (h : L.provides m = false) : L.fields.find? (·.1 == m) = none := by
  rw [List.find?_eq_none]
  intro f hf hm
  simp only [Layer.provides, List.any_eq_false] at h
  exact h f hf hm

theorem body_some {L : Layer} {m : String} (h : L.provides m = true) :
    ∃ b, L.fields.find? (·.1 == m) = some (m, b) := by
  cases hf : L.fields.find? (·.1 == m) with
  | none =>
    simp only [Layer.provides, List.any_eq_true] at h
    obtain ⟨f, hf', hm⟩ := h
    rw [List.find?_eq_none] at hf
    exact absurd hm (hf f hf')
  | some p => exact ⟨p.2, by rw [← find_name hf]⟩

/-- The row of a suffix answers `m` with the outermost provider's opened body. -/
theorem find_rowOf (O : Term) (seed : List (String × Term)) (m : String) (ls : List Layer) :
    ∀ (j : Nat) (b : Term), providesLast ls m = some j → bodyAt ls j m = some b →
      (rowOf O seed ls).find? (·.1 == m) = some (m, openTerm b O (superBelow O seed (ls.drop (j + 1)))) := by
  induction ls with
  | nil => intro _ _ h; cases h
  | cons L rest ih =>
    intro j b h hb
    simp only [providesLast] at h
    by_cases hp : L.provides m = true
    · simp only [hp, ite_true, Option.some.injEq] at h
      subst h
      obtain ⟨b', hb'⟩ := body_some hp
      simp only [bodyAt, List.getElem?_cons_zero, Option.bind_some, Layer.body, hb', Option.map_some,
        Option.some.injEq] at hb
      subst hb
      simp only [rowOf]
      split
      · rw [find_openFields]; simp [hb']
      · rw [find_extendFields, find_openFields]; simp [hb']
    · have hn : L.provides m = false := by simpa using hp
      simp only [hn, Bool.false_eq_true, ite_false] at h
      split at h
      · cases h
      · rename_i hflat
        obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [rowOf, hflat, Bool.false_eq_true, ite_false]
        rw [find_extendFields, find_openFields, body_none hn]
        simp only [Option.map_none]
        exact ih j' b hj' (by simpa [bodyAt] using hb)

/-- **`late_binding_at`**: in any suffix of the stack, over any `O`, `(row beneath).m` reduces to
the outermost provider's body. At the whole stack this is T1; at a proper suffix it is the late
binding of `super.m` (`late_binding_prefix`). -/
theorem late_binding_at (O : Term) (seed : List (String × Term)) (ls : List Layer) (m : String) (j : Nat)
    (b : Term) (hj : providesLast ls m = some j) (hb : bodyAt ls j m = some b) :
    Steps (.get (superBelow O seed ls) m) (openTerm b O (superBelow O seed (ls.drop (j + 1)))) :=
  steps_trans (steps_get m (superBelow_record O seed ls))
    (steps_one (.field _ _ _ (find_rowOf O seed m ls j b hj hb)))

/-- `O.m` steps to `(row beneath the whole stack).m`. -/
theorem object_get (C : Composition) (m : String) :
    Steps (.get C.object m) (.get (superBelow C.object C.seed C.layers) m) :=
  steps_one (.target _ (.fix _ _))

/-- **T1 `late_binding`.** In a composition closed over a record seed, `O.m` reduces to the body of
the last layer providing `m`, with `self := O` and `super := superAt j`. -/
theorem late_binding (C : Composition) (m : String) (j : Nat) (b : Term)
    (hj : providesLast C.layers m = some j) (hb : bodyAt C.layers j m = some b) :
    Steps (.get C.object m) (openTerm b C.object (C.superAt j)) :=
  steps_trans (object_get C m) (late_binding_at C.object C.seed C.layers m j b hj hb)

/-- `late_binding` with its right-hand side as the parallel substitution. -/
theorem late_binding_parallel (C : Composition) (m : String) (j : Nat) (b : Term)
    (hj : providesLast C.layers m = some j) (hb : bodyAt C.layers j m = some b) :
    Steps (.get C.object m) (b.substitute fun | 0 => C.superAt j | 1 => C.object | k + 2 => .bound k) := by
  have e : (fun | 0 => C.superAt j | 1 => C.object | k + 2 => .bound k) = selfSuper C.object (C.superAt j) :=
    funext fun i => match i with | 0 | 1 | _ + 2 => rfl
  rw [e]; exact late_binding C m j b hj hb

/-- Late binding as an equation of the logic. -/
theorem late_binding_bequiv (C : Composition) (m : String) (j : Nat) (b : Term)
    (hj : providesLast C.layers m = some j) (hb : bodyAt C.layers j m = some b) :
    .get C.object m ≈b openTerm b C.object (C.superAt j) :=
  bequiv_of_steps (late_binding C m j b hj hb)

theorem open_delegation (O sup : Term) (m : String) : openTerm (.get (.bound 0) m) O sup = .get sup m := by
  simp [openTerm, Term.substitute, selfSuper]

theorem isDelegation_eq {b : Term} {m : String} (h : isDelegation b m = true) : b = .get (.bound 0) m := by
  unfold isDelegation at h
  split at h
  · rename_i m'; have : m' = m := by simpa using h
    subst this; rfl
  · cases h

/-- What `unfoldIn` names, the row reduces to: late binding with delegations chased. -/
theorem unfoldIn_steps (O : Term) (seed : List (String × Term)) (m : String) :
    ∀ (fuel : Nat) (ls : List Layer) {i : Nat} {u : Term}, unfoldIn O seed fuel ls m = some (i, u) →
      Steps (.get (superBelow O seed ls) m) u
  | 0, _, _, _, h => by cases h
  | fuel + 1, ls, i, u, h => by
    simp only [unfoldIn] at h
    split at h
    · rename_i j hj
      split at h
      · rename_i b hb
        have step := late_binding_at O seed ls m j b hj hb
        split at h
        · rename_i hd
          rw [isDelegation_eq hd, open_delegation] at step
          obtain ⟨⟨i', u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
          cases e
          exact steps_trans step (unfoldIn_steps O seed m fuel _ hu)
        · cases h; exact step
      · cases h
    · cases h

/-- `unfold` is late binding: what it names, `O.m` reduces to. -/
theorem late_binding_unfold {C : Composition} {m : String} {j : Nat} {u : Term} (h : C.unfold m = some (j, u)) :
    Steps (.get C.object m) u :=
  steps_trans (object_get C m) (unfoldIn_steps C.object C.seed m _ _ h)

/-! ## The program's operands -/

theorem ahead_composeWith {op op' : Layer → Term} (h : ∀ L, Ahead (op L) (op' L)) :
    ∀ (top : Layer) (below : List Layer), Ahead (composeWith op top below) (composeWith op' top below)
  | top, [] => h top
  | top, next :: rest =>
    .specification (Ahead.refl _) (.mix (ahead_composeWith h next rest) (h top))

/-- **The program's object is the decoded composition's.** When each operand the elaborator emits
(a knot reference) reduces to its layer's term, the `fix` over the operands is `≈b` the object of
the decoded composition. -/
theorem object_bequiv_of_operands (C : Composition) (op : Layer → Term)
    (h : ∀ L, Steps (op L) L.term) :
    .fix (composeWith op C.top C.below) (.record C.seed) ≈b C.object :=
  bequiv_of_ahead (.fix (ahead_composeWith (fun L => Ahead.ofStepsRefl (h L)) C.top C.below) (Ahead.refl _))

end Obend.Logic
end
