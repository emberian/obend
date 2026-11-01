module
/- The leaf emitter on `tests/obend-source/ReviewMember.obend`, transcribed as Elaborate lowers it
(`Teeth/Logic/FrameTeeth`; the run over the elaborator's own output is `tests/run-leaf.py`).

* `compose(Base, Twice, Augmented)` flattens and emits to a book of two method slots, `review` and
  `twice`; `twice` reads slot 0 through `self`; `Augmented.review`'s `super.review` is resolved to
  `Base.review` statically (no `super`, no mix/extend chain is left in the book);
* `twiceOfThree`: the book computes `7`, as the object does (`book_sound` at this composition);
* the specialization slot: at the program's own view the stored book is usable and kept; with
  `Override` composed last it is blocked naming exactly the object's pin, and the machine is
  selected, which computes `3` where the stale book would still say `7`; with Augmented at `+ 2` it
  is blocked naming the object's pin and Augmented's;
* no residual `super` row: ReviewMember projects `super` only, and its vtable holds no record of a
  suffix row's shape (`vtable_clean`); a layer passing `super` first-class (`Leak`) fails the check,
  and its vtable does hold the row literal;
* `#tooth`: with the inner layer winning in the flattened row, the stored proof of `flatten_sound`
  is refused; with the object pin dropped from a book's supports, the stored proof of
  `book_usable_sound` is refused. -/
public import Obend.Tactic.Tooth
public import Obend.Teeth.Logic.FrameTeeth
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
import all Obend.Leaf.BendTT
public import Obend.Leaf.Specialize
public import Obend.Leaf.Residual
public import Obend.Leaf.BendTT
@[expose] public section
open Obend.Core.Term Obend.Logic Obend.Leaf Obend.Leaf.BendTT Obend.Slot Obend.Slot.World Obend.Equiv
open Obend.Teeth.Logic.Review (base twice augmented override seed)

namespace Obend.Teeth.Leaf.Review

/-- `compose(Base, Twice, Augmented(n))`, outermost first. -/
def comp (n : Nat) : Composition := ⟨augmented n, [twice, base], seed⟩

/-- With `Override` composed last. -/
def overridden : Composition := ⟨override, [augmented 1, twice, base], seed⟩

theorem comp_closed : (comp 1).closedB = true := by decide +kernel

/-- The book: two method slots, `twice` reading slot 0 through `self`. -/
theorem book_shape :
    (emit (comp 1)).slots = ["review", "twice"] ∧
      (emit (comp 1)).defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
        [("review", 0, .method, []), ("twice", 1, .method, [0])] ∧
      (emit (comp 1)).closedB = true := by
  decide +kernel

/-- `Augmented.review` in the book: `super.review` is `Base.review`, read statically. -/
theorem augmented_resolved :
    ((emit (comp 1)).defs.head?.map fun d => Obend.Law.termEq d.code
      (.lam (.lam (.binary .add (.app (.lam (.binary .add (.bound 0) (.nat 1))) (.bound 0)) (.nat 1))))) =
      some true := by
  decide +kernel

/-- Branded at its kind, as the front end constructs it (`REPORT-C1-20261101.md` §1). -/
def branded : Composition :=
  ⟨augmented 1, [twice, base], ("#kind", .inject "ReviewBase.Review" (.record [])) :: seed⟩

/-- The brand is the book's static metadata, not a slot; the dispatcher answers it. -/
theorem brand_static :
    (emit branded).slots = ["review", "twice"] ∧ (emit branded).statics.map (·.1) = ["#kind"] ∧
      (Obend.Law.run 50 (.get (emit branded).link "#kind")).map
        (Obend.Law.termEq · (.inject "ReviewBase.Review" (.record []))) = some true := by
  decide +kernel

theorem brand_sound : .get (emit branded).link "#kind" ≈b .get branded.object "#kind" :=
  book_sound branded (by decide +kernel) "#kind"

/-- `twiceOfThree() = twice(3)`, read from the linked book. -/
def bookTwiceOfThree (C : Composition) : Term := .app (.get (emit C).link "twice") (.nat 3)

/-- The same read from the object `fix (compose …) {seed}`. -/
def objectTwiceOfThree (C : Composition) : Term := .app (.get C.object "twice") (.nat 3)

/-- The natural a run reaches. -/
def natOf : Option Term → Option Nat
  | some (.nat n) => some n
  | _ => none

theorem book_seven : natOf (Obend.Law.run 200 (bookTwiceOfThree (comp 1))) = some 7 := by decide +kernel

theorem object_seven : natOf (Obend.Law.run 200 (objectTwiceOfThree (comp 1))) = some 7 := by decide +kernel

/-- `book_sound` at this composition: the two reads are `≈b`. -/
theorem twice_sound : .get (emit (comp 1)).link "twice" ≈b .get (comp 1).object "twice" :=
  book_sound (comp 1) comp_closed "twice"

/-! ## The specialization slot -/

def book : Candidate := .book "twiceOfThree" (comp 1)

/-- The supports a read names as dead. -/
def deadCells : Reading LeafPin Candidate → List LeafCell
  | .blocked _ d => d.map (·.cell)
  | _ => []

def view (C : Composition) (clock : Nat) : LeafView := viewOf clock "twiceOfThree" C

theorem book_usable_here : specSlot.usable (holdsAt (view (comp 1) 0)) book = true := by decide +kernel

theorem book_kept :
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot (view (comp 1) 0)
      (specOrder "twiceOfThree" (comp 1)) (some book) = .ok book := by
  rw [show book = .book "twiceOfThree" (comp 1) from rfl, specialize_choice]
  rw [show specSlot.usable (holdsAt (view (comp 1) 0)) (.book "twiceOfThree" (comp 1)) = true from book_usable_here]
  rfl

theorem override_blocks :
    deadCells (specSlot.read (holdsAt (view overridden 1)) (some book)) = [.object "twiceOfThree"] := by
  decide +kernel

theorem override_selects_machine :
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot (view overridden 1)
      (specOrder "twiceOfThree" (comp 1)) (some book) = .ok .machine := by
  rw [show book = .book "twiceOfThree" (comp 1) from rfl, specialize_choice]
  have : specSlot.usable (holdsAt (view overridden 1)) (.book "twiceOfThree" (comp 1)) = false := by
    decide +kernel
  rw [this]; rfl

/-- The machine at the overridden program computes `3`; the stale book would still say `7`. -/
theorem override_machine_three : natOf (Obend.Law.run 200 (objectTwiceOfThree overridden)) = some 3 := by
  decide +kernel

theorem augmented_blocks :
    deadCells (specSlot.read (holdsAt (view (comp 2) 1)) (some book)) =
      [.object "twiceOfThree", .layer "ReviewMember.Augmented"] := by
  decide +kernel

/-! ## No residual `super` row -/

/-- The shapes of the suffix rows of a composition. -/
def rowShapes (C : Composition) (ns : List String) : Bool := (suffixNames C.seed C.layers).contains ns

theorem review_projects_super :
    superOnlyProjectedRow (comp 1).seed (comp 1).layers = true ∧
      cleanRow (rowShapes (comp 1)) (comp 1).seed (comp 1).layers = true := by decide +kernel

theorem review_no_residual : ∀ e ∈ (comp 1).vtable, recordBad (rowShapes (comp 1)) e.2 = false :=
  vtable_clean _ _ review_projects_super.1 review_projects_super.2

/-- `def leak(v): (λx. x)(super)`: `super` passed first-class. -/
def leak : Obend.Logic.Layer :=
  Obend.Teeth.Logic.Review.layer "ReviewMember.Leak" [("leak", .lam (.app (.lam (.bound 0)) (.bound 1)))]

def leaky : Composition := ⟨leak, [augmented 1, twice, base], seed⟩

theorem leak_refused_and_residual :
    superOnlyProjectedRow leaky.seed leaky.layers = false ∧
      leaky.vtable.any (fun e => recordBad (rowShapes leaky) e.2) = true := by decide +kernel

/-! ## BendTT Target Emission & Soundness (`Obend.Leaf.BendTT`) -/

/-- The natural a `BendTT` run reaches. -/
def natOfB : Option BTerm → Option Nat
  | some (.nat n) => some n
  | _ => none

/-- `ReviewMember` (`comp 1`) emits cleanly to `BendTT` (`emitBendTT (emit (comp 1))`) with an
acyclic leaf call graph (`bb.acyclicDefs = true`, zero `.fix` knots inside its method bodies),
evaluating `twice(3) = 7` and `review(3) = 5` under `BendTT.runB`. -/
theorem review_bendtt_verified :
    (match emitBendTT (emit (comp 1)) with
     | some bb =>
       bb.acyclicDefs &&
       (natOfB (runB 200 (.app (.get bb.dispatch "twice") (BTerm.nat 3))) == some 7) &&
       (natOfB (runB 200 (.app (.get bb.dispatch "review") (BTerm.nat 3))) == some 5)
     | none => false) = true := by
  decide +kernel

/-- End-to-end `book_to_bendtt_sound` on `ReviewMember`: `BendTT.runB` on `emitBendTT (emit (comp 1))`
establishes `Halts (.app (.get (comp 1).object "twice") (.nat 3)) (.natural 7)` on the source
Core4 object. -/
theorem review_bendtt_halts_object :
    ∃ bb : BBook,
      emitBendTT (emit (comp 1)) = some bb ∧
      Halts (.app (.get (comp 1).object "twice") (Term.nat 3)) (.natural 7) := by
  have hver := review_bendtt_verified
  cases h : emitBendTT (emit (comp 1)) with
  | none => simp [h] at hver
  | some bb =>
    rw [h] at hver
    simp only [Bool.and_eq_true, beq_iff_eq] at hver
    have h7 : natOfB (runB 200 (.app (.get bb.dispatch "twice") (BTerm.nat 3))) = some 7 := hver.1.2
    unfold natOfB at h7
    cases hr : runB 200 (.app (.get bb.dispatch "twice") (BTerm.nat 3)) with
    | none => simp [hr] at h7
    | some v =>
      rw [hr] at h7
      cases v <;> simp at h7
      subst h7
      exact ⟨bb, rfl, (book_to_bendtt_sound (comp 1) comp_closed h "twice" 3 200 7 hr).2⟩

/-! ## Teeth -/

/-- `self` left at the wrong binder: the vtable's entries see the `{}` argument as `self`. -/
def flatObjectUnshifted (vt : List (String × Term)) : Term := .fix (.lam (.lam (.record vt))) (.record [])

#tooth Obend.Leaf.flatten_sound by mutation Obend.Leaf.flatObject := flatObjectUnshifted

/-- A book's supports without its object's pin: only the layers it flattened. -/
def supportsLayersOnly : Candidate → List LeafPin
  | .book _ C => C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine => []

#tooth Obend.Leaf.book_usable_sound by mutation Obend.Leaf.Candidate.supports := supportsLayersOnly

/-- Dropping the outer `.fix` knot in `BBook.dispatch` breaks `emitBendTT_dispatch`. -/
def bbookDispatchUnfixed (B : BBook) : BTerm :=
  .record (B.items.map BBookItem.entry)

#tooth Obend.Leaf.BendTT.emitBendTT_dispatch by mutation Obend.Leaf.BendTT.BBook.dispatch := bbookDispatchUnfixed

end Obend.Teeth.Leaf.Review
end
