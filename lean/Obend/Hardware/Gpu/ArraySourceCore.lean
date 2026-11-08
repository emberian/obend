module
/- Compact Core4 interpretation of the lexical array source. Arrays are total
index functions, zero outside their finite shape. Each source let is one Core4
lambda application. Maps retain a single scalar body rather than expanding it
once per array element. Finite constants and gather tables are literal functions.
No array operation is added to the Core4 calculus. -/
public import Obend.Hardware.Gpu.ArraySource
public import Obend.Hardware.Gpu.ArrayEncoding
public import Obend.Hardware.Gpu.SourceElem
public import Obend.Hardware.Gpu.FoldCore
@[expose] public section
namespace Obend.Hardware.Gpu.ArraySource.Core
open Obend.Core.Term Obend.Equiv
open Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.Source
set_option autoImplicit false

/-- A source array denotes a total Core4 index function. -/
def ArrayDenotes (term : Term) (values : Vec) : Prop :=
  ∀ i, Steps (.app term (.nat i)) (.nat (values.getD i 0#64).toNat)

def extend {α : Type} (head : α) (tail : Nat → α) : Nat → α
  | 0 => head
  | i + 1 => tail i

/-- Substitution underneath an array let, followed by its beta step. -/
theorem instantiate_lift (body argument : Term) (σ : Nat → Term) :
    instantiate (body.substitute (liftSubstitution σ)) argument =
      body.substitute (extend argument σ) := by
  simp only [instantiate_eq, substitute_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [liftSubstitution, single, Term.substitute, extend]
  | succ i =>
    simp only [liftSubstitution, rename_substitute, single, extend]
    exact substitute_bound _

/-- Read one element of a source expression; all source array variables remain
functions, including the argument arrays. -/
def _root_.Obend.Hardware.Gpu.ArraySource.Rhs.at (r : Rhs) (lens : Nat → Nat) (env : Nat → Term) (index : Term) : Term :=
  match r with
  | .map n op args =>
      .ifBool (.binary .less index (.nat n))
        (elemTerm op (args.map fun a => .app (env a) index)) (.nat 0)
  | .gather f a =>
      .ifBool (.binary .less index (.nat f.table.length))
        (.app (env a) (.app (encodeNats f.table) index)) (.nat 0)
  | .concat a b =>
      .ifBool (.binary .less index (.nat (lens a)))
        (.app (env a) index)
        (.app (env b) (.binary .subtract index (.nat (lens a))))
  | .literal vs => .app (encodeNats (vs.map (·.toNat))) index
  | .fold op shape a => .app (foldTerm op shape (env a)) index

/-- Compact source array function. The new binder is the element index. -/
def _root_.Obend.Hardware.Gpu.ArraySource.Rhs.term (r : Rhs) (lens : Nat → Nat) : Term :=
  .lam (r.at lens (fun a => .bound (a + 1)) (.bound 0))

theorem _root_.Obend.Hardware.Gpu.ArraySource.Rhs.at_substitute (r : Rhs) (lens : Nat → Nat) (env : Nat → Term)
    (index : Term) (σ : Nat → Term) :
    (r.at lens env index).substitute σ =
      r.at lens (fun a => (env a).substitute σ) (index.substitute σ) := by
  cases r <;> simp [Rhs.at, Term.substitute, elemTerm_substitute,
    encodeNats_substitute, foldTerm_substitute, List.map_map, Function.comp_def]

theorem _root_.Obend.Hardware.Gpu.ArraySource.Rhs.apply (r : Rhs) (lens : Nat → Nat) (σ : Nat → Term) (i : Nat) :
    Steps (.app ((r.term lens).substitute σ) (.nat i)) (r.at lens σ (.nat i)) := by
  simp only [Rhs.term, Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_lift, Rhs.at_substitute]
  simp only [Term.substitute, extend]
  exact .refl _

theorem ifLess_steps (i n : Nat) (yes no : Term) :
    Steps (.ifBool (.binary .less (.nat i) (.nat n)) yes no) (if i < n then yes else no) := by
  refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases h : i < n
  · simpa [primitiveResult, h] using Steps.next (Step.ifTrue yes no) (.refl yes)
  · simpa [primitiveResult, h] using Steps.next (Step.ifFalse yes no) (.refl no)

theorem getD_map_lt {α β : Type} (xs : List α) (f : α → β) (i : Nat)
    (a : α) (b : β) (hi : i < xs.length) :
    (xs.map f).getD i b = f (xs.getD i a) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem map_arguments_sound (args : List Nat) (terms : Nat → Term) (values : Env)
    (h : ∀ a, ArrayDenotes (terms a) (values a)) (i j : Nat) :
    Steps ((args.map fun a => Term.app (terms a) (.nat i)).getD j (.nat 0))
      (.nat ((args.map fun a => (values a).getD i 0#64).getD j 0#64).toNat) := by
  induction args generalizing j with
  | nil => simp; exact .refl _
  | cons a args ih => cases j with
    | zero => exact h a i
    | succ j => exact ih j

theorem app_argument_word (fn index : Term) (i : Nat) (value : Word)
    (hi : Steps index (.nat i))
    (hv : Steps (.app fn (.nat i)) (.nat value.toNat)) :
    Steps (.app fn index) (.nat value.toNat) :=
  steps_of_ahead_word value (.app (.refl fn) (.run hi (.nat i))) hv

theorem _root_.Obend.Hardware.Gpu.ArraySource.Rhs.at_sound (r : Rhs) (lens : Nat → Nat) (terms : Nat → Term) (values : Env)
    (hl : ∀ a, lens a = (values a).length)
    (h : ∀ a, ArrayDenotes (terms a) (values a)) (i : Nat) :
    Steps (r.at lens terms (.nat i)) (.nat ((r.eval values).getD i 0#64).toNat) := by
  cases r with
  | fold op shape a => exact foldTerm_sound op shape (terms a) (values a) (h a) i
  | literal vs =>
    have hm : (vs.map (·.toNat)).getD i 0 = (vs.getD i 0#64).toNat := by
      induction vs generalizing i with
      | nil => simp
      | cons v vs ih => cases i with
        | zero => rfl
        | succ i => exact ih i
    simpa only [Rhs.at, Rhs.eval, hm] using encodeNats_apply (vs.map (·.toNat)) i
  | map n op args =>
    apply steps_trans (ifLess_steps i n _ _)
    by_cases hi : i < n
    · simp only [hi, ↓reduceIte, Rhs.eval, getD_range_map n _ _ i hi]
      exact elemTerm_sound op _ _ (map_arguments_sound args terms values h i)
    · simp only [hi, ↓reduceIte, Rhs.eval]
      rw [getD_of_le_length _ i _ (by simp; omega)]
      exact .refl _
  | gather f a =>
    apply steps_trans (ifLess_steps i f.table.length _ _)
    by_cases hi : i < f.table.length
    · simp only [hi, ↓reduceIte, Rhs.eval]
      rw [getD_map_lt f.table _ i 0 0#64 hi]
      exact app_argument_word _ _ _ _ (encodeNats_apply f.table i) (h a (f.table.getD i 0))
    · simp only [hi, ↓reduceIte, Rhs.eval]
      rw [getD_of_le_length _ i _ (by simp; omega)]
      exact .refl _
  | concat a b =>
    apply steps_trans (ifLess_steps i (lens a) _ _)
    by_cases hi : i < lens a
    · simp only [hi, ↓reduceIte, Rhs.eval]
      rw [getD_append_of_lt _ _ i _ (by rw [← hl a]; exact hi)]
      exact h a i
    · simp only [hi, ↓reduceIte, Rhs.eval]
      have heq : i = (values a).length + (i - lens a) := by rw [← hl a]; omega
      have ha : (values a ++ values b).getD i 0#64 = (values b).getD (i - lens a) 0#64 := by
        calc
          _ = (values a ++ values b).getD ((values a).length + (i - lens a)) 0#64 :=
            congrArg (fun k => (values a ++ values b).getD k 0#64) heq
          _ = _ := getD_append_right (values a) (values b) (i - lens a) 0#64
      rw [ha]
      have hs : Steps (.binary .subtract (.nat i) (.nat (lens a))) (.nat (i - lens a)) :=
        .next (.primitive .subtract _ _ _ (.natural _) (.natural _) rfl) (.refl _)
      exact app_argument_word _ _ _ _ hs (h b (i - lens a))

theorem _root_.Obend.Hardware.Gpu.ArraySource.Rhs.term_sound (r : Rhs) (lens : Nat → Nat) (terms : Nat → Term) (values : Env)
    (hl : ∀ a, lens a = (values a).length) (h : ∀ a, ArrayDenotes (terms a) (values a)) :
    ArrayDenotes ((r.term lens).substitute terms) (r.eval values) :=
  fun i => steps_trans (r.apply lens terms i) (r.at_sound lens terms values hl h i)

theorem _root_.Obend.Hardware.Gpu.ArraySource.Rhs.length_sound (r : Rhs) (lens : Nat → Nat) (env : Env)
    (hl : ∀ a, lens a = (env a).length) : r.length lens = (r.eval env).length := by
  cases r <;> simp [Rhs.length, Rhs.eval, hl, evalFold, FoldShape.outLen]

/-- Array lets become actual Core4 lambda applications; their terms are not
expanded into their uses. The result is a small product of array functions. -/
def _root_.Obend.Hardware.Gpu.ArraySource.Program.term (p : Program) (lens : Nat → Nat) : Term :=
  match p with
  | .ret arrays => pack (arrays.map Term.bound)
  | .letE value body =>
      .app (.lam (body.term (extend (value.length lens) lens))) (value.term lens)

/-- Observation semantics of the complete source term. This is a Core4 reduction
statement for every output and index, rather than an encoding of evaluated data. -/
theorem _root_.Obend.Hardware.Gpu.ArraySource.Program.term_sound (p : Program) (lens : Nat → Nat) (terms : Nat → Term) (values : Env)
    (hl : ∀ a, lens a = (values a).length)
    (h : ∀ a, ArrayDenotes (terms a) (values a))
    (output : Nat) (ho : output < (p.eval values).length) (index : Nat) :
    Steps (.app (nth ((p.term lens).substitute terms) output) (.nat index))
      (.nat (((p.eval values).getD output []).getD index 0#64).toNat) := by
  induction p generalizing lens terms values with
  | ret arrays =>
    simp only [Program.term, pack_substitute, List.map_map, Function.comp_def, Term.substitute, Program.eval] at *
    have ho' : output < arrays.length := by simpa using ho
    have hp := nth_pack (arrays.map terms) output (by simpa using ho')
    rw [getD_map_lt arrays terms output 0 (.nat 0) ho'] at hp
    rw [getD_map_lt arrays values output 0 [] ho']
    exact steps_trans (steps_app _ hp) (h (arrays.getD output 0) index)
  | letE value body ih =>
    simp only [Program.term, Term.substitute]
    have hb : Steps
        (.app (.lam ((body.term (extend (value.length lens) lens)).substitute (liftSubstitution terms)))
          ((value.term lens).substitute terms))
        ((body.term (extend (value.length lens) lens)).substitute
          (extend ((value.term lens).substitute terms) terms)) := by
      exact .next (.beta _ _) (by rw [instantiate_lift]; exact .refl _)
    apply steps_trans (steps_app _ (nth_steps output hb))
    apply ih (extend (value.length lens) lens)
      (extend ((value.term lens).substitute terms) terms) (push (value.eval values) values)
    · intro a
      cases a with
      | zero => exact value.length_sound lens values hl
      | succ a => exact hl a
    · intro a
      cases a with
      | zero => exact value.term_sound lens terms values hl h
      | succ a => exact h a
    · exact ho

end Obend.Hardware.Gpu.ArraySource.Core
