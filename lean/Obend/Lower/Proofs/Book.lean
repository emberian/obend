module
/-
# Obend.Lower.Proofs.Book — Lean to the Leaf book

A lowered program `t` is the one member `name` of a one-layer flat composition over the empty seed
(`leanComposition`), which `Obend.Leaf.emit` turns into a book. `lean_to_book` composes the links:
the source run of `e n` to the literal `m` (Lean-lite's reduction) gives the Core4 evaluation of the
lowered application (`lower_sound_nat`); the composition's object reads the member back as `t`
(`late_binding`); the book computes what the object computes (`book_sound`). So the book's member,
applied to `n`, halts with `m`.
-/
public import Obend.Lower.Proofs.Sound
public import Obend.Leaf.Emit
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_substitute)
open Obend.Equiv
open Obend.Logic
set_option autoImplicit false

/-- The one-layer composition whose member `name` is the lowered program `t` (moved under the
layer's `self` and `super` binders, which it does not read). -/
def leanComposition (name : String) (t : Term) : Composition where
  top := { name := "lean", metadata := .record [], fields := [(name, t.rename (· + 2))], flat := true }
  below := []
  seed := []

theorem openTerm_shift2 (t O sup : Term) : openTerm (t.rename (· + 2)) O sup = t := by
  unfold openTerm
  rw [rename_substitute]
  exact substitute_bound t

/-- The object's member is the lowered program. -/
theorem leanComposition_get (name : String) (t : Term) :
    Steps (.get (leanComposition name t).object name) t := by
  have := late_binding (leanComposition name t) name 0 (t.rename (· + 2))
    (by simp [providesLast, Composition.layers, leanComposition, Layer.provides])
    (by simp [bodyAt, Composition.layers, leanComposition, Layer.body])
  rwa [openTerm_shift2] at this

/-- The book's member is equivalent to the lowered program. -/
theorem book_member (name : String) (t : Term) (hc : (leanComposition name t).closedB = true) :
    .get (Obend.Leaf.emit (leanComposition name t)).link name ≈b t :=
  BEquiv.trans (Obend.Leaf.book_sound _ hc name) (bequiv_of_steps (leanComposition_get name t))

/-- **Lean to the Leaf book**: if the fragment function `e` applied to `n` reduces to `m` in the
source semantics, the book emitted for its lowering, its member applied to `n`, halts with `m`. -/
theorem lean_to_book (name : String) (e : LExpr) (n m : Nat)
    (hc : (leanComposition name (lowerT e)).closedB = true) (run : SSteps (.app e (.lit n)) (.lit m)) :
    Halts (.app (.get (Obend.Leaf.emit (leanComposition name (lowerT e))).link name) (.nat n)) (.natural m) := by
  have ev := lower_sound_nat run
  simp only [lowerT] at ev
  have same := book_member name (lowerT e) hc Term.bound (.app (.bound 0) (.nat n))
  simp only [instantiate, Term.substitute, substitute_bound] at same
  exact (same.halts _).2 ⟨_, ev, .natural m⟩

end Obend.Lower
end
