module
/-
# Obend.Leaf.Flatten — the compilation `late_binding` justifies

A closed composition over a record target, `O = fix (compose …) {seed}` (`Obend.Logic.Composition`),
is flattened to a **vtable**: one entry per member of the final row, each a method closure under one
binder, `self`. Every `super` a layer's body reads is replaced by the literal record of the
flattened row beneath that layer (`flatRow`), so `super.p` is a field of a known record whose entry is
the provider `providesLast` names on the prefix (`flatRow_find`); `resolve` then performs those
lookups statically, so no `super` and no mix/extend chain remains. The flattened object is
`fix (λself. λ_. {vtable}) {}` (`flatObject`): `self` is the vtable itself.

**`flatten_sound`** (the compilation theorem): `get (flatten C) m ≈b get C.object m` for every member,
and the objects themselves are `≈b`. The two objects are different recursive terms (each method of
`O` mentions `O`, each of the vtable mentions the vtable), so `Ahead` cannot relate them; they are
`Joins`-related (`Obend.Leaf.UpTo`) over the one base pair `(O, flatObject)`, whose unfolding is
`late_binding` row by row: `O` reduces to the record `rowOf` whose entries are the providers' bodies
with `self := O` and `super :=` the row beneath (`superBelow_record`, `find_rowOf`), and the vtable to
the same bodies with `self :=` the vtable and `super :=` the flattened row beneath (`row_joins`).

Scope: compositions whose object and flattening are closed (`Composition.closedB`, decided); the two
layer shapes Elaborate emits (`extend super {defs}` and the flat delegating record).
-/
public import Obend.Leaf.UpTo
@[expose] public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
set_option autoImplicit false

/-! ## The vtable -/

/-- A layer body (under `self` at 1, `super` at 0) moved under one binder, `self`, with `super := sup`. -/
def toSelf (sup : Term) : Nat → Term
  | 0 => sup
  | 1 => .bound 0
  | k + 2 => .bound (k + 1)

/-- The flattened row of a suffix of the stack (outermost first): each entry under one binder,
`self`; a layer's `super` is the literal record of the flattened row beneath it. -/
def flatRow (seed : List (String × Term)) : List Layer → List (String × Term)
  | [] => mapFields (·.rename Nat.succ) seed
  | L :: rest =>
    let fs := mapFields (·.substitute (toSelf (.record (flatRow seed rest)))) L.fields
    if L.flat then fs else extendFields (flatRow seed rest) fs

/-- `fix (λself. λ_. {vtable}) {}`: the object whose `self` is its own vtable. -/
def flatObject (vt : List (String × Term)) : Term :=
  .fix (.lam (.lam (.record (mapFields (·.rename Nat.succ) vt)))) (.record [])

/-- A vtable with `self := X`. -/
def instRow (X : Term) (vt : List (String × Term)) : List (String × Term) := mapFields (instantiate · X) vt

/-! ## Static resolution of fields of literal records -/

theorem sizeOf_snd_lt_of_mem {l : List (String × Term)} {x : String × Term} (h : x ∈ l) :
    sizeOf x.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x.2 < sizeOf x := by cases x; simp +arith
  omega

/-- `get g p`, the field read statically when `g` is a literal record listing `p`. -/
def resolveGet : Term → String → Term
  | .record fs, p =>
    match fs.find? (·.1 == p) with
    | some (_, b) => b
    | none => .get (.record fs) p
  | g, p => .get g p

/-- Every `get {fs} p` whose record is literal (after resolution) and lists `p` is replaced by the
entry: the static form of `super.p`, whose provider `flatRow_find` names. -/
def resolve : Term → Term
  | .hole n σ => .hole n (σ.map resolve)
  | .bound i => .bound i
  | .lam b => .lam (resolve b)
  | .app f a => .app (resolve f) (resolve a)
  | .mix l u => .mix (resolve l) (resolve u)
  | .fix s i => .fix (resolve s) (resolve i)
  | .specification m e => .specification (resolve m) (resolve e)
  | .prototype s g => .prototype (resolve s) (resolve g)
  | .reflect p => .reflect (resolve p)
  | .metadata p => .metadata (resolve p)
  | .project p => .project (resolve p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => .binary op (resolve l) (resolve r)
  | .extend i fs => .extend (resolve i) (fs.map fun f => (f.1, resolve f.2))
  | .record fs => .record (fs.map fun f => (f.1, resolve f.2))
  | .get g p => resolveGet (resolve g) p
  | .ifZero v z s => .ifZero (resolve v) (resolve z) (resolve s)
  | .inject l p => .inject l (resolve p)
  | .case sc arms => .case (resolve sc) (arms.map fun a => (a.1, resolve a.2))
  | .ifBool c x y => .ifBool (resolve c) (resolve x) (resolve y)
  | .perform p => .perform (resolve p)
  | .done v => .done (resolve v)
  | .split t names f => .split (resolve t) names (resolve f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

theorem zip_map_self_rel {R : Term → Term → Prop} (g : Term → Term) :
    ∀ (fs : List (String × Term)), (∀ x ∈ fs, R x.2 (g x.2)) →
      ∀ p ∈ fs.zip (fs.map fun f => (f.1, g f.2)), R p.1.2 p.2.2
  | [], _, p, hp => by simp at hp
  | x :: xs, h, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h x List.mem_cons_self
    · exact zip_map_self_rel g xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) p hp

theorem ahead_resolveGet {g g' : Term} (p : String) (h : Ahead g g') : Ahead (.get g p) (resolveGet g' p) := by
  unfold resolveGet
  split
  · rename_i fs'
    split
    · rename_i n b' hit
      have hn : n = p := by have := List.find?_some hit; simpa using this
      subst hn
      obtain ⟨fs, s, names, rel⟩ := Obend.Equiv.inv_record_ahead h
      obtain ⟨b, hit0, a⟩ := find_right names rel hit
      exact .run (steps_snoc (Obend.Equiv.steps_get _ s) (.field _ _ _ hit0)) a
    · exact .get p h
  · exact .get p h

/-- **Static resolution is reduction in context.** -/
theorem ahead_resolve : (t : Term) → Ahead t (resolve t)
  | .hole n σ => by
    simp only [resolve]
    refine .hole n (by simp) ?_
    intro p hp
    rw [List.zip_map_right] at hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hp
    obtain ⟨he, ha⟩ := zip_self σ (a, b) hab
    have hb : a = b := he
    subst hb
    have member : a ∈ σ := ha
    exact ahead_resolve a
  | .bound i => by simp only [resolve]; exact .bound i
  | .lam b => by simp only [resolve]; exact .lam (ahead_resolve b)
  | .app f a => by simp only [resolve]; exact .app (ahead_resolve f) (ahead_resolve a)
  | .mix l u => by simp only [resolve]; exact .mix (ahead_resolve l) (ahead_resolve u)
  | .fix s i => by simp only [resolve]; exact .fix (ahead_resolve s) (ahead_resolve i)
  | .specification m e => by simp only [resolve]; exact .specification (ahead_resolve m) (ahead_resolve e)
  | .prototype s g => by simp only [resolve]; exact .prototype (ahead_resolve s) (ahead_resolve g)
  | .reflect p => by simp only [resolve]; exact .reflect (ahead_resolve p)
  | .metadata p => by simp only [resolve]; exact .metadata (ahead_resolve p)
  | .project p => by simp only [resolve]; exact .project (ahead_resolve p)
  | .nat n => by simp only [resolve]; exact .nat n
  | .boolean b => by simp only [resolve]; exact .boolean b
  | .label l => by simp only [resolve]; exact .label l
  | .binary op l r => by simp only [resolve]; exact .binary op (ahead_resolve l) (ahead_resolve r)
  | .extend i fs => by
    simp only [resolve]
    exact .extend (ahead_resolve i) (names_map _ fs).symm
      (zip_map_self_rel resolve fs fun x _ => ahead_resolve x.2)
  | .record fs => by
    simp only [resolve]
    exact .record (names_map _ fs).symm (zip_map_self_rel resolve fs fun x _ => ahead_resolve x.2)
  | .get g p => by simp only [resolve]; exact ahead_resolveGet p (ahead_resolve g)
  | .ifZero v z s => by
    simp only [resolve]; exact .ifZero (ahead_resolve v) (ahead_resolve z) (ahead_resolve s)
  | .inject l p => by simp only [resolve]; exact .inject l (ahead_resolve p)
  | .case sc arms => by
    simp only [resolve]
    exact .case (ahead_resolve sc) (names_map _ arms).symm
      (zip_map_self_rel resolve arms fun x _ => ahead_resolve x.2)
  | .ifBool c x y => by
    simp only [resolve]; exact .ifBool (ahead_resolve c) (ahead_resolve x) (ahead_resolve y)
  | .perform p => by simp only [resolve]; exact .perform (ahead_resolve p)
  | .done v => by simp only [resolve]; exact .done (ahead_resolve v)
  | .split t names f => by simp only [resolve]; exact .split names (ahead_resolve t) (ahead_resolve f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)
    | (have := List.sizeOf_lt_of_mem member; omega)

/-! ## The flattened object unfolds to its vtable -/

theorem instantiate_succ (e X : Term) : instantiate (e.rename Nat.succ) X = e := by
  rw [instantiate_eq, shift_one_cancel]

theorem openTerm_succ (e X s : Term) : openTerm (e.rename Nat.succ) X s = instantiate e X := by
  unfold openTerm
  rw [Obend.Core.TermTraverse.rename_substitute, instantiate_eq]
  congr 1; funext n; cases n <;> rfl

/-- Two β steps: `(λ. λ. R) a b` is `R` with `self := a`, `super := b`. -/
theorem beta_two (R a b : Term) : Steps (.app (.app (.lam (.lam R)) a) b) (openTerm R a b) := by
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq, open_sequential]
  exact .refl _

/-- `fix (λ. λ. R) s` unfolds to `R` with `self :=` itself and `super := s`. -/
theorem fix_unfold (R s : Term) :
    Steps (.app (.app (.lam (.lam R)) (.fix (.lam (.lam R)) s)) s) (openTerm R (.fix (.lam (.lam R)) s) s) :=
  beta_two _ _ _

theorem openTerm_record (fs : List (String × Term)) (X s : Term) :
    openTerm (.record fs) X s = .record (mapFields (openTerm · X s) fs) := by
  simp only [openTerm, Term.substitute, mapFields]

/-- `flatObject vt` takes one step, then reaches its vtable with `self :=` itself. -/
theorem flatObject_unfold (vt : List (String × Term)) :
    ∃ f₁, Step (flatObject vt) f₁ ∧ Steps f₁ (.record (instRow (flatObject vt) vt)) := by
  refine ⟨_, .fix _ _, ?_⟩
  have e : openTerm (.record (mapFields (·.rename Nat.succ) vt)) (flatObject vt) (.record []) =
      .record (instRow (flatObject vt) vt) := by
    rw [openTerm_record]
    simp only [mapFields, instRow, List.map_map, Function.comp_def, openTerm_succ]
  rw [← e]
  exact fix_unfold _ _

/-! ## The rows join -/

theorem instantiate_toSelf (b X F : Term) :
    instantiate (b.substitute (toSelf X)) F = openTerm b F (instantiate X F) := by
  rw [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  unfold openTerm
  congr 1; funext n
  match n with
  | 0 => simp only [toSelf, selfSuper, instantiate_eq]
  | 1 => simp only [toSelf, selfSuper, Term.substitute, single]
  | k + 2 => simp only [toSelf, selfSuper, Term.substitute, single]

theorem instantiate_record (fs : List (String × Term)) (F : Term) :
    instantiate (.record fs) F = .record (instRow F fs) := by
  simp only [instantiate_eq, Term.substitute, instRow, mapFields]

theorem mapFields_rel {R : Term → Term → Prop} (g g' : Term → Term) (fs : List (String × Term))
    (h : ∀ x, R (g x) (g' x)) :
    (mapFields g fs).map Prod.fst = (mapFields g' fs).map Prod.fst ∧
      ∀ p ∈ (mapFields g fs).zip (mapFields g' fs), R p.1.2 p.2.2 :=
  ⟨fields_map_names g g' rfl,
    fields_map_rel (R := Eq) g g' (zip_refl (fun a b => a.2 = b.2) fs fun _ _ => rfl)
      (fun x _ e => e ▸ h x)⟩

/-- **The rows join.** Over any `O` and `F` that join, the row a suffix of the stack reduces to
over `O` (`rowOf`) and the flattened row of that suffix with `self := F` agree name by name, and
their entries join: the same provider's body, `self` the object on each side, `super` the row
beneath on the left and its flattening on the right. -/
theorem row_joins {B : Term → Term → Prop} (hB : ClosedPairs B) {O F : Term} (hOF : Joins B O F)
    (seed : List (String × Term)) :
    ∀ ls : List Layer, (rowOf O seed ls).map Prod.fst = (instRow F (flatRow seed ls)).map Prod.fst ∧
      ∀ p ∈ (rowOf O seed ls).zip (instRow F (flatRow seed ls)), Joins B p.1.2 p.2.2
  | [] => by
    have e : instRow F (flatRow seed []) = seed := by
      simp only [instRow, flatRow, mapFields, List.map_map, Function.comp_def, instantiate_succ]
      simp
    rw [e]
    show (seed.map Prod.fst = seed.map Prod.fst) ∧ ∀ p ∈ seed.zip seed, Joins B p.1.2 p.2.2
    exact ⟨rfl, zip_refl (fun a b => Joins B a.2 b.2) seed fun x _ => .refl x.2⟩
  | L :: rest => by
    obtain ⟨n1, r1⟩ := row_joins hB hOF seed rest
    have hsup : Joins B (superBelow O seed rest) (.record (instRow F (flatRow seed rest))) :=
      .run (superBelow_record O seed rest) (.record n1 r1)
    have ef : instRow F (mapFields (·.substitute (toSelf (.record (flatRow seed rest)))) L.fields) =
        mapFields (openTerm · F (.record (instRow F (flatRow seed rest)))) L.fields := by
      simp only [instRow, mapFields, List.map_map, Function.comp_def, instantiate_toSelf, instantiate_record]
    have hf := mapFields_rel (R := Joins B) (openTerm · O (superBelow O seed rest))
      (openTerm · F (.record (instRow F (flatRow seed rest)))) L.fields fun b =>
        joins_substitute hB (.refl b) fun n => match n with
          | 0 => hsup
          | 1 => hOF
          | _ + 2 => .refl _
    simp only [rowOf, flatRow]
    cases L.flat
    · simp only [Bool.false_eq_true, ite_false]
      rw [show instRow F (extendFields (flatRow seed rest)
          (mapFields (·.substitute (toSelf (.record (flatRow seed rest)))) L.fields)) =
          extendFields (instRow F (flatRow seed rest))
            (instRow F (mapFields (·.substitute (toSelf (.record (flatRow seed rest)))) L.fields)) from
        (extendFields_map _ _ _).symm, ef]
      exact extendFields_rel n1 r1 hf.1 hf.2
    · simp only [ite_true]
      rw [ef]
      exact hf

/-! ## The compilation theorem -/


/-- The flattened row of the whole stack, before static resolution. -/
def _root_.Obend.Logic.Composition.flatRaw (C : Composition) : List (String × Term) := flatRow C.seed C.layers

/-- **The vtable**: the flattened row with every `super.p` read statically. -/
def _root_.Obend.Logic.Composition.vtable (C : Composition) : List (String × Term) := mapFields resolve C.flatRaw

/-- **The flattened object**: `self` is the vtable. -/
def _root_.Obend.Logic.Composition.flatten (C : Composition) : Term := flatObject C.vtable

/-- The scope of `flatten_sound`: the object and its unresolved flattening are closed. -/
def _root_.Obend.Logic.Composition.closedB (C : Composition) : Bool :=
  Obend.Law.closedB C.object && Obend.Law.closedB (flatObject C.flatRaw)

/-- The one base pair: the object and its flattening. -/
def _root_.Obend.Logic.Composition.pair (C : Composition) (o f : Term) : Prop := o = C.object ∧ f = flatObject C.flatRaw

theorem _root_.Obend.Logic.Composition.object_unfold (C : Composition) :
    Step C.object (superBelow C.object C.seed C.layers) := .fix _ _

/-- The pair is a base: `late_binding`, row by row, is its unfolding. -/
theorem _root_.Obend.Logic.Composition.pair_closed (C : Composition) (hc : C.closedB = true) :
    ClosedPairs C.pair := by
  rintro o f ⟨rfl, rfl⟩
  simp only [Composition.closedB, Bool.and_eq_true] at hc
  exact ⟨closed_of_closedB hc.1, closed_of_closedB hc.2⟩

theorem _root_.Obend.Logic.Composition.pair_base (C : Composition) (hc : C.closedB = true) : Base C.pair where
  closed := C.pair_closed hc
  unfold := by
    rintro o f ⟨rfl, rfl⟩
    obtain ⟨f₁, sf, sf'⟩ := flatObject_unfold C.flatRaw
    have ⟨names, rel⟩ := row_joins (C.pair_closed hc) (O := C.object) (F := flatObject C.flatRaw)
      (.base ⟨rfl, rfl⟩) C.seed C.layers
    exact ⟨_, _, f₁, _, C.object_unfold, superBelow_record _ _ _, sf, sf', .record names rel⟩


/-- Static resolution changes the vtable only by reduction in context. -/
theorem resolve_ahead (vt : List (String × Term)) : Ahead (flatObject vt) (flatObject (mapFields resolve vt)) := by
  refine .fix (.lam (.lam (.record ?_ ?_))) (.refl _)
  · simp [mapFields, List.map_map, Function.comp_def]
  · intro p hp
    simp only [mapFields, List.map_map, Function.comp_def] at hp
    rw [List.zip_map, List.mem_map] at hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hp
    obtain ⟨he, _⟩ := zip_self vt (x, y) hxy
    simp only at he ⊢
    subst he
    exact ahead_rename (ahead_resolve x.2) _

/-- The object and its unresolved flattening are `≈b`. -/
theorem object_bequiv_flatRaw (C : Composition) (hc : C.closedB = true) :
    C.object ≈b flatObject C.flatRaw :=
  bequiv_of_joins (C.pair_base hc) (.base ⟨rfl, rfl⟩)

/-- **The object is `≈b` its flattening.** -/
theorem flatten_object (C : Composition) (hc : C.closedB = true) : C.flatten ≈b C.object :=
  (BEquiv.trans (object_bequiv_flatRaw C hc) (bequiv_of_ahead (resolve_ahead C.flatRaw))).symm

/-- **`flatten_sound`, the compilation theorem.** For a closed composition over a record target,
every member of the flattened object (`self` the vtable, every `super.p` resolved to its provider) is
`≈b` the member of `fix (compose …) {seed}`. -/
theorem flatten_sound (C : Composition) (hc : C.closedB = true) (m : String) :
    .get C.flatten m ≈b .get C.object m :=
  (BEquiv.trans (bequiv_of_joins (C.pair_base hc) (.get m (.base ⟨rfl, rfl⟩)))
    (bequiv_of_ahead (.get m (resolve_ahead C.flatRaw)))).symm

/-! ## `super.p` names its provider -/

theorem find_mapFields_none {fields : List (String × Term)} {m : String} (g : Term → Term)
    (h : fields.find? (·.1 == m) = none) : (mapFields g fields).find? (·.1 == m) = none := by
  rw [List.find?_eq_none] at h ⊢
  intro f hf
  simp only [mapFields, List.mem_map] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  exact h f' hf'

/-- **The provider of `super.p`.** In the flattened row of a suffix of the stack, the entry for
`m` is the body of the last layer providing it (`providesLast`), with `super :=` the flattened row
beneath that layer: the row `late_binding_at` reads, flattened. So `super.p` in a layer's entry,
which reads the literal record of the row beneath it, lands on the provider `providesLast` names on
that prefix, statically. -/
theorem flatRow_find (seed : List (String × Term)) (m : String) (ls : List Layer) :
    ∀ (j : Nat) (b : Term), providesLast ls m = some j → bodyAt ls j m = some b →
      (flatRow seed ls).find? (·.1 == m) =
        some (m, b.substitute (toSelf (.record (flatRow seed (ls.drop (j + 1)))))) := by
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
      simp only [flatRow]
      split
      · rw [find_mapFields _ hb']; rfl
      · rw [find_extendFields, find_mapFields _ hb']; rfl
    · have hn : L.provides m = false := by simpa using hp
      simp only [hn, Bool.false_eq_true, ite_false] at h
      split at h
      · cases h
      · rename_i hflat
        obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [flatRow, hflat, Bool.false_eq_true, ite_false]
        rw [find_extendFields, find_mapFields_none _ (body_none hn)]
        exact ih j' b hj' (by simpa [bodyAt] using hb)

end Obend.Leaf
end
