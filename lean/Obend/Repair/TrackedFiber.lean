module
public import Obend.Category.FiberGrowth
public import Obend.Repair.QuotAssembly
import all Obend.Repair.QuotAssembly

/-!
# Reusing a suspended computation on a growing fiber

A membrane can keep the program and its input while the set of copies behind a
name changes. The input here is fixed: the tracker does not receive a copy ID.
This is the delayed-application universal from Breadstuffs'
`Dregg2.Realizability.EncodedQuantifiers`, interpreted with Obend's
`CodeTracker.eval`. Each copy may accept several outputs.
-/
public section
namespace Obend.Repair.TrackedFiber
open Obend.Category.Projection (forallAlong forallAlong_iff)
open Obend.Category.FiberGrowth (insert forall_at_insert)
set_option autoImplicit false

universe u v w z
variable {Code : Type u} {Val : Type v} [T : CodeTracker Code Val]
variable {E : Type w} {B : Type z}

/-- A suspended application owes an accepted result at each point over `b`.
There is no definedness obligation at an empty fiber. -/
def Serves (p : E → B) (accept : E → Val → Prop) (b : B) (code : Code) (input : Val) : Prop :=
  forallAlong p (fun e => ∃ out, T.eval code input = some out ∧ accept e out) b

/-- With an actual point to force the application, all copies must accept one
and the same result, since the tracker runs on the same input. -/
theorem serves_iff_common_output (p : E → B) (accept : E → Val → Prop) (b : B)
    (code : Code) (input : Val) (point : E) (over : p point = b) :
    Serves p accept b code input ↔
      ∃ out, T.eval code input = some out ∧ forallAlong p (fun e => accept e out) b := by
  unfold Serves
  rw [forallAlong_iff]
  constructor
  · intro h
    obtain ⟨out, run, _⟩ := h point over
    refine ⟨out, run, (forallAlong_iff ..).mpr ?_⟩
    intro e he
    obtain ⟨other, run', ok⟩ := h e he
    exact Option.some.inj (run'.symm.trans run) ▸ ok
  · rintro ⟨out, run, ok⟩ e he
    exact ⟨out, run, (forallAlong_iff ..).mp ok e he⟩

/-- Exact residual obligation on insertion, even if a retained copy changed
its contract. The fresh point forces definedness even at a formerly empty name. -/
theorem serves_insert_iff (p : E → B) (name : B) (accept : Option E → Val → Prop)
    (code : Code) (input : Val) :
    Serves (insert p name) accept name code input ↔
      ∃ out, T.eval code input = some out ∧
        forallAlong p (fun e => accept (some e) out) name ∧ accept none out := by
  rw [serves_iff_common_output (insert p name) accept name code input none rfl]
  simp only [forall_at_insert]

/-- A recorded run and the retained copies' current agreement reduce the entire
extension test to one check on its actual result. -/
theorem serves_insert_of_run_iff (p : E → B) (name : B) (accept : Option E → Val → Prop)
    (code : Code) (input out : Val) (run : T.eval code input = some out)
    (retained : forallAlong p (fun e => accept (some e) out) name) :
    Serves (insert p name) accept name code input ↔ accept none out := by
  rw [serves_insert_iff]
  constructor
  · rintro ⟨w, hw, _, fresh⟩
    exact Option.some.inj (hw.symm.trans run) ▸ fresh
  · exact fun fresh => ⟨out, run, retained, fresh⟩

/-- A tracked assembly morphism already supplies a common output where the
same raw input realizes every copy. This produces an explicit run of its tracker. -/
theorem hom_common_output {Y : Type z} {A : Assembly Code Val E} {Z : Assembly Code Val Y}
    (h : AsmHom A Z) (p : E → B) (point : E) (input : Val)
    (shared : ∀ e, p e = p point → A.Realizes input e) :
    ∃ out, T.eval h.tracker input = some out ∧
      forallAlong p (fun e => Z.Realizes out (h.specFun e)) (p point) := by
  apply (serves_iff_common_output p _ _ _ _ point rfl).mp
  exact (forallAlong_iff ..).mpr fun e he => h.tracks e input (shared e he)

/-- If an output realizer determines its semantic value (a modest assembly),
copies sharing a single input realizer have the same observable. This gives the
fiberwise equality used by quotient descent. -/
theorem observation_agrees_of_shared_input {Y : Type z}
    {A : Assembly Code Val E} {Z : Assembly Code Val Y}
    (h : AsmHom A Z) (p : E → B) (point : E) (input : Val)
    (shared : ∀ e, p e = p point → A.Realizes input e)
    (modest : ∀ out y y', Z.Realizes out y → Z.Realizes out y' → y = y') :
    ∀ e, p e = p point → h.specFun e = h.specFun point := by
  obtain ⟨out, _, allAccept⟩ := hom_common_output h p point input shared
  have atCopy := (forallAlong_iff ..).mp allAccept
  exact fun e he => modest out _ _ (atCopy e he) (atCopy point rfl)

/-! The old copy has tag 0 and the fresh copy has tag 1. -/

/-- The observable on the two-copy example. -/
@[expose] def copyTag : Option Unit → Nat
  | some () => 0
  | none => 1

/-- One program can return each copy's tag when the input carries that tag. -/
theorem explicit_copy_input (e : Option Unit) :
    ∃ out, CanonCode.eval (AsmHom.id natAssembly).tracker (.nat (copyTag e)) = some out ∧
      natAssembly.Realizes out (copyTag e) :=
  (AsmHom.id natAssembly).tracks (copyTag e) (.nat (copyTag e)) rfl

/-- On the same input, every program fails to serve the two distinct tag
contracts simultaneously, even though they each have a realizer. -/
theorem hidden_copy_no_uniform_output (code : CanonCode) (input : CanonVal) :
    ¬ Serves (insert (fun _ : Unit => ()) ()) (fun e out => natAssembly.Realizes out (copyTag e))
        () code input := by
  intro h
  obtain ⟨out, _, retained, fresh⟩ := (serves_insert_iff ..).mp h
  have old := (forallAlong_iff ..).mp retained () rfl
  change out = .nat 0 at old
  change out = .nat 1 at fresh
  cases old.symm.trans fresh

/-- Projecting a pair component from a number is undefined. The old empty
fiber admits this suspended application; even a fresh trivial contract forces it. -/
theorem empty_then_first_copy :
    let p := fun _ : Empty => ()
    Serves p (fun _ _ => True) () CanonCode.fst (CanonVal.nat 0) ∧
      ¬ Serves (insert p ()) (fun _ _ => True) () CanonCode.fst (CanonVal.nat 0) := by
  dsimp only
  constructor
  · exact (forallAlong_iff ..).mpr fun e _ => nomatch e
  · intro h
    obtain ⟨out, impossible, _⟩ := (serves_insert_iff ..).mp h
    change none = some out at impossible
    cases impossible

end Obend.Repair.TrackedFiber
end
