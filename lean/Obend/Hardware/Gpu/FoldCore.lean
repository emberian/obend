module
/- Compact Core4 folds: one bounded recursive accumulator, shared by every range.
The shape selects ranges at run time; scan prefixes are never expanded in syntax. -/
public import Obend.Hardware.Gpu.SourceElem
public import Obend.Hardware.ArrayFold
@[expose] public section
namespace Obend.Hardware.Gpu.ArraySource.Core
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu.Source
set_option autoImplicit false

def reduceBinary : ReduceOp → Binary
  | .add => .add | .mul => .mul | .band => .band | .bor => .bor

@[simp] theorem reduceBinary_eval (op : ReduceOp) (a b : Word) :
    (reduceBinary op).eval a b = op.combine a b := by cases op <;> rfl

/-- self, unused super, source, cursor, remaining count, accumulator. -/
def foldLoopSpec (op : ReduceOp) : Term :=
  .lam (.lam (.lam (.lam (.lam (.lam
    (.ifZero (.bound 1) (.bound 0)
      (.app (.app (.app (.app (.bound 6) (.bound 4))
        (.binary .add (.bound 3) (.nat 1))) (.bound 0))
        ((reduceBinary op).term (.bound 1) (.app (.bound 4) (.bound 3))))))))))

def foldLoop (op : ReduceOp) : Term := .fix (foldLoopSpec op) (.nat 0)
def loopCall (op : ReduceOp) (source start len acc : Term) : Term :=
  .app (.app (.app (.app (foldLoop op) source) start) len) acc

@[simp] theorem foldLoopSpec_substitute (op : ReduceOp) (σ : Nat → Term) :
    (foldLoopSpec op).substitute σ = foldLoopSpec op := by
  simp [foldLoopSpec, Term.substitute, liftSubstitution, Term.rename, Binary.substitute]
@[simp] theorem foldLoop_substitute (op : ReduceOp) (σ : Nat → Term) :
    (foldLoop op).substitute σ = foldLoop op := by simp [foldLoop, Term.substitute]
@[simp] theorem loopCall_substitute (op : ReduceOp) (s i n a : Term) (σ : Nat → Term) :
    (loopCall op s i n a).substitute σ =
      loopCall op (s.substitute σ) (i.substitute σ) (n.substitute σ) (a.substitute σ) := by
  simp [loopCall]

/-- A symbolic unfolding, before any source or accumulator is substituted. -/
theorem loopCall_unfold_vars (op : ReduceOp) :
    Steps (loopCall op (.bound 0) (.bound 1) (.bound 2) (.bound 3))
      (.ifZero (.bound 2) (.bound 3)
        (loopCall op (.bound 1) (.binary .add (.bound 2) (.nat 1)) (.bound 0)
          ((reduceBinary op).term (.bound 4) (.app (.bound 1) (.bound 2))))) := by
  cases op <;> unfold loopCall foldLoop
  all_goals
    refine .next (.application _ (.application _ (.application _ (.application _ (.fix _ _))))) ?_
    simp only [foldLoopSpec, reduceBinary, Binary.term]
    repeat first
      | exact Steps.refl _
      | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _)))))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename])
      | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _))))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
      | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _)))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
      | (apply Steps.next (Step.application _ (Step.application _ (Step.beta _ _))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
      | (apply Steps.next (Step.application _ (Step.beta _ _)); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
      | (apply Steps.next (Step.beta _ _); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])

def foldSub (s i n a : Term) : Nat → Term
  | 0 => s | 1 => i | 2 => n | _ => a

theorem loopCall_zero_vars (op : ReduceOp) :
    Steps (loopCall op (.bound 0) (.bound 1) (.nat 0) (.bound 2)) (.bound 2) := by
  have h := steps_substitute (foldSub (.bound 0) (.bound 1) (.nat 0) (.bound 2))
    (loopCall_unfold_vars op)
  simp only [loopCall_substitute, Term.substitute, foldSub, liftSubstitution,
    Term.rename, Binary.substitute] at h
  exact steps_trans h (.next (.zero _ _) (.refl _))

theorem loopCall_succ_vars (op : ReduceOp) (n : Nat) :
    Steps (loopCall op (.bound 0) (.bound 1) (.nat (n+1)) (.bound 2))
      (loopCall op (.bound 0) (.binary .add (.bound 1) (.nat 1)) (.nat n)
        ((reduceBinary op).term (.bound 2) (.app (.bound 0) (.bound 1)))) := by
  have h := steps_substitute (foldSub (.bound 0) (.bound 1) (.nat (n+1)) (.bound 2))
    (loopCall_unfold_vars op)
  simp only [loopCall_substitute, Term.substitute, foldSub, liftSubstitution,
    Term.rename, Binary.substitute] at h
  apply steps_trans h
  refine .next (.successor n _ _) ?_
  simp only [instantiate, loopCall_substitute, Binary.substitute, Term.substitute]
  exact .refl _

theorem loopCall_sound (op : ReduceOp) (source : Term) (read : Nat → Word)
    (hs : ∀ i, Steps (.app source (.nat i)) (.nat (read i).toNat))
    (start len : Nat) (acc : Word) :
    Steps (loopCall op source (.nat start) (.nat len) (.nat acc.toNat))
      (.nat (foldRange op read start len acc).toNat) := by
  induction len generalizing start acc with
  | zero =>
    have h := steps_substitute (foldSub source (.nat start) (.nat acc.toNat) (.nat 0))
      (loopCall_zero_vars op)
    simpa [loopCall_substitute, Term.substitute, foldSub, foldRange] using h
  | succ n ih =>
    have h := steps_substitute (foldSub source (.nat start) (.nat acc.toNat) (.nat 0))
      (loopCall_succ_vars op n)
    simp only [loopCall_substitute, Term.substitute, foldSub, Binary.substitute] at h
    apply steps_trans h
    have hi : Steps (.binary .add (.nat start) (.nat 1)) (.nat (start+1)) :=
      .next (.primitive .add _ _ _ (.natural _) (.natural _) rfl) (.refl _)
    have ha : Steps ((reduceBinary op).term (.nat acc.toNat) (.app source (.nat start)))
        (.nat (op.combine acc (read start)).toNat) := by
      apply steps_of_ahead_word _ ((reduceBinary op).congrAhead (.refl _) (.run (hs start) (.nat _)))
      simpa using (reduceBinary op).steps acc (read start)
    have hf : foldRange op read start (n+1) acc =
        foldRange op read (start+1) n (op.combine acc (read start)) := by
      simp [foldRange, List.range'_succ]
    rw [hf]
    exact steps_of_ahead_word _
      (.app (.app (.app (.app (.refl _) (.refl _)) (.run hi (.nat _))) (.refl _))
        (.run ha (.nat _))) (ih (start+1) (op.combine acc (read start)))

/-- A closed selector accepts a range-fold function and an output index. -/
def foldSelector (mode : Option ScanMode) : Nat → List Nat → Term
  | _, [] => .lam (.lam (.nat 0))
  | start, n :: ns =>
    let width := match mode with | none => 1 | some _ => n
    let count := match mode with
      | none => .nat n
      | some m => .binary .add (.bound 0) (.nat m.extra)
    .lam (.lam (.ifBool (.binary .less (.bound 0) (.nat width))
      (.app (.app (.bound 1) (.nat start)) count)
      (.app (.app (foldSelector mode (start+n) ns) (.bound 1))
        (.binary .subtract (.bound 0) (.nat width)))))

@[simp] theorem foldSelector_substitute (m : Option ScanMode) (start : Nat)
    (ns : List Nat) (σ : Nat → Term) :
    (foldSelector m start ns).substitute σ = foldSelector m start ns := by
  induction ns generalizing start σ with
  | nil => simp [foldSelector, Term.substitute]
  | cons n ns ih => cases m <;>
      simp [foldSelector, Term.substitute, liftSubstitution, Term.rename, ih]

/-- Source occurs once; the closed loop is shared across all selected ranges. -/
def foldRangeFunction (op : ReduceOp) : Term :=
  .lam (.lam (.lam (loopCall op (.bound 2) (.bound 1) (.bound 0) (.nat op.identity.toNat))))

def foldTerm (op : ReduceOp) (shape : FoldShape) (source : Term) : Term :=
  .app (foldSelector shape.mode 0 shape.segments) (.app (foldRangeFunction op) source)

@[simp] theorem foldRangeFunction_substitute (op : ReduceOp) (σ : Nat → Term) :
    (foldRangeFunction op).substitute σ = foldRangeFunction op := by
  simp [foldRangeFunction, Term.substitute, liftSubstitution, Term.rename]

theorem foldTerm_substitute (op : ReduceOp) (shape : FoldShape) (source : Term)
    (σ : Nat → Term) : (foldTerm op shape source).substitute σ =
      foldTerm op shape (source.substitute σ) := by simp [foldTerm]

theorem foldRangeFunction_apply_vars (op : ReduceOp) :
    Steps (.app (.app (.app (foldRangeFunction op) (.bound 0)) (.bound 1)) (.bound 2))
      (loopCall op (.bound 0) (.bound 1) (.bound 2) (.nat op.identity.toNat)) := by
  unfold foldRangeFunction
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  simp only [instantiate, Term.substitute, loopCall_substitute, liftSubstitution, Term.rename]
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute, loopCall_substitute, liftSubstitution, Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, loopCall_substitute]
  exact .refl _

theorem foldRangeFunction_sound (op : ReduceOp) (source : Term) (read : Nat → Word)
    (hs : ∀ i, Steps (.app source (.nat i)) (.nat (read i).toNat)) (start len : Nat) :
    Steps (.app (.app (.app (foldRangeFunction op) source) (.nat start)) (.nat len))
      (.nat (foldRange op read start len op.identity).toNat) := by
  have h := steps_substitute (foldSub source (.nat start) (.nat len) (.nat 0))
    (foldRangeFunction_apply_vars op)
  simp only [Term.substitute, foldRangeFunction_substitute, loopCall_substitute, foldSub] at h
  exact steps_trans h (loopCall_sound op source read hs start len op.identity)

def foldWidth (m : Option ScanMode) (n : Nat) : Nat := match m with | none => 1 | some _ => n
def foldCount (m : Option ScanMode) (n : Nat) (i : Term) : Term :=
  match m with | none => .nat n | some m => .binary .add i (.nat m.extra)

@[simp] theorem foldCount_substitute (m : Option ScanMode) (n : Nat) (i : Term) (σ : Nat → Term) :
    (foldCount m n i).substitute σ = foldCount m n (i.substitute σ) := by
  cases m <;> simp [foldCount, Term.substitute]

theorem foldSelector_cons_vars (m : Option ScanMode) (start n : Nat) (ns : List Nat) :
    Steps (.app (.app (foldSelector m start (n::ns)) (.bound 0)) (.bound 1))
      (.ifBool (.binary .less (.bound 1) (.nat (foldWidth m n)))
        (.app (.app (.bound 0) (.nat start)) (foldCount m n (.bound 1)))
        (.app (.app (foldSelector m (start+n) ns) (.bound 0))
          (.binary .subtract (.bound 1) (.nat (foldWidth m n))))) := by
  cases m <;> simp only [foldSelector, foldWidth, foldCount]
  all_goals
    refine .next (.application _ (.beta _ _)) ?_
    simp only [instantiate, Term.substitute, liftSubstitution, Term.rename, foldSelector_substitute]
    refine .next (.beta _ _) ?_
    simp only [instantiate, Term.substitute, foldSelector_substitute]
    exact .refl _

theorem fold_ifLess (i n : Nat) (yes no : Term) :
    Steps (.ifBool (.binary .less (.nat i) (.nat n)) yes no) (if i < n then yes else no) := by
  refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases h : i < n
  · simpa [primitiveResult, h] using Steps.next (Step.ifTrue yes no) (.refl yes)
  · simpa [primitiveResult, h] using Steps.next (Step.ifFalse yes no) (.refl no)

theorem foldSelector_cons (m : Option ScanMode) (start n : Nat) (ns : List Nat)
    (f : Term) (i : Nat) :
    Steps (.app (.app (foldSelector m start (n::ns)) f) (.nat i))
      (if i < foldWidth m n then
        .app (.app f (.nat start)) (foldCount m n (.nat i)) else
        .app (.app (foldSelector m (start+n) ns) f)
          (.binary .subtract (.nat i) (.nat (foldWidth m n)))) := by
  have h := steps_substitute (foldSub f (.nat i) (.nat 0) (.nat 0))
    (foldSelector_cons_vars m start n ns)
  simp only [Term.substitute, foldSelector_substitute, foldCount_substitute, foldSub] at h
  exact steps_trans h (fold_ifLess _ _ _ _)


def foldPrefix (m : Option ScanMode) (start n : Nat) : List (Nat × Nat) :=
  match m with | none => [(start,n)]
               | some m => (List.range n).map fun i => (start,i+m.extra)

def foldCountValue (m : Option ScanMode) (n i : Nat) : Nat :=
  match m with | none => n | some m => i+m.extra

@[simp] theorem foldPrefix_length (m : Option ScanMode) (start n : Nat) :
    (foldPrefix m start n).length = foldWidth m n := by
  cases m <;> simp [foldPrefix, foldWidth]

theorem foldPrefix_getD (m : Option ScanMode) (start n i : Nat) (f : Nat → Nat → Word)
    (hi : i < foldWidth m n) :
    ((foldPrefix m start n).map fun r => f r.1 r.2).getD i 0#64 =
      f start (foldCountValue m n i) := by
  cases m with
  | none =>
    have : i = 0 := by simpa [foldWidth] using hi
    subst i
    rfl
  | some m =>
    simp only [foldWidth] at hi
    simp [foldPrefix, List.map_map, List.getD_eq_getElem?_getD,
      List.getElem?_range hi, foldCountValue]

theorem fold_getD_append_left {α : Type} (xs ys : List α) (i : Nat) (d : α)
    (hi : i < xs.length) : (xs++ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fold_getD_append_right {α : Type} (xs ys : List α) (i : Nat) (d : α)
    (hi : xs.length ≤ i) : (xs++ys).getD i d = ys.getD (i-xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem foldCount_steps (m : Option ScanMode) (n i : Nat) :
    Steps (foldCount m n (.nat i)) (.nat (foldCountValue m n i)) := by
  cases m with
  | none => exact .refl _
  | some m => exact .next (.primitive .add _ _ _ (.natural _) (.natural _) rfl) (.refl _)

/-- The descriptor selects exactly the reference contiguous intervals, including
zero-length reduction segments and zero-default out-of-range observations. -/
theorem foldSelector_sound (m : Option ScanMode) (ns : List Nat) (f : Term)
    (value : Nat → Nat → Word)
    (hf : ∀ start len, Steps (.app (.app f (.nat start)) (.nat len))
      (.nat (value start len).toNat)) (start i : Nat) :
    Steps (.app (.app (foldSelector m start ns) f) (.nat i))
      (.nat (((segmentRanges m start ns).map fun r => value r.1 r.2).getD i 0#64).toNat) := by
  induction ns generalizing start i with
  | nil =>
    simp only [foldSelector, segmentRanges, List.map_nil, List.getD_nil, BitVec.toNat_ofNat, Nat.zero_mod]
    refine .next (.application _ (.beta _ _)) ?_
    simp only [instantiate, Term.substitute]
    refine .next (.beta _ _) ?_
    simp only [instantiate, Term.substitute]
    exact .refl _
  | cons n ns ih =>
    apply steps_trans (foldSelector_cons m start n ns f i)
    have he : segmentRanges m start (n::ns) =
        foldPrefix m start n ++ segmentRanges m (start+n) ns := rfl
    rw [he, List.map_append]
    by_cases hi : i < foldWidth m n
    · simp only [hi, ↓reduceIte]
      rw [fold_getD_append_left _ _ i _ (by simpa using hi), foldPrefix_getD m start n i value hi]
      exact steps_of_ahead_word _
        (.app (.refl _) (.run (foldCount_steps m n i) (.nat _)))
        (hf start (foldCountValue m n i))
    · simp only [hi, ↓reduceIte]
      rw [fold_getD_append_right _ _ i _ (by simp; omega)]
      simp only [List.length_map, foldPrefix_length]
      have hs : Steps (.binary .subtract (.nat i) (.nat (foldWidth m n)))
          (.nat (i-foldWidth m n)) :=
        .next (.primitive .subtract _ _ _ (.natural _) (.natural _) rfl) (.refl _)
      exact steps_of_ahead_word _ (.app (.refl _) (.run hs (.nat _)))
        (ih (start+n) (i-foldWidth m n))

/-- Universal Core4 reduction of all four fold shapes. No computed array is
quoted into the term: the hypothesis concerns only the original source reads. -/
theorem foldTerm_sound (op : ReduceOp) (shape : FoldShape) (source : Term) (xs : Vec)
    (hs : ∀ i, Steps (.app source (.nat i)) (.nat (xs.getD i 0#64).toNat)) (i : Nat) :
    Steps (.app (foldTerm op shape source) (.nat i))
      (.nat ((evalFold op shape (fun i => xs.getD i 0#64)).getD i 0#64).toNat) := by
  have h := foldSelector_sound shape.mode shape.segments (.app (foldRangeFunction op) source)
    (fun start len => foldRange op (fun i => xs.getD i 0#64) start len op.identity)
    (foldRangeFunction_sound op source (fun i => xs.getD i 0#64) hs) 0 i
  have he : segmentRanges shape.mode 0 shape.segments = shape.ranges := by
    cases shape <;> simp [FoldShape.mode, FoldShape.segments, FoldShape.ranges, segmentRanges]
  simpa only [foldTerm, he, evalFold] using h

end Obend.Hardware.Gpu.ArraySource.Core
end
