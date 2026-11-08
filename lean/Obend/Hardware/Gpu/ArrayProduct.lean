module
/- Finite products of array functions in existing Core4 records. The representation
is a head/tail spine; no generated numeric field names enter the source language. -/
public import Obend.Leaf.Emit
@[expose] public section
namespace Obend.Hardware.Gpu.ArraySource.Core
open Obend.Core.Term Obend.Equiv
set_option autoImplicit false

def pack : List Term → Term
  | [] => .record []
  | x :: xs => .record [("head", x), ("tail", pack xs)]

def nth (t : Term) : Nat → Term
  | 0 => .get t "head"
  | i + 1 => nth (.get t "tail") i

theorem pack_substitute (xs : List Term) (σ : Nat → Term) :
    (pack xs).substitute σ = pack (xs.map (·.substitute σ)) := by
  induction xs with
  | nil => simp [pack, Term.substitute]
  | cons x xs ih => simp [pack, Term.substitute, ih]

theorem nth_substitute (t : Term) (i : Nat) (σ : Nat → Term) :
    (nth t i).substitute σ = nth (t.substitute σ) i := by
  induction i generalizing t with
  | zero => simp [nth, Term.substitute]
  | succ i ih => simp [nth, Term.substitute, ih]

theorem nth_steps (i : Nat) {t t' : Term} (h : Steps t t') :
    Steps (nth t i) (nth t' i) := by
  induction i generalizing t t' with
  | zero => exact steps_get "head" h
  | succ i ih => exact ih (steps_get "tail" h)

theorem nth_pack (xs : List Term) (i : Nat) (hi : i < xs.length) :
    Steps (nth (pack xs) i) (xs.getD i (.nat 0)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact .next (.field _ "head" x rfl) (.refl _)
    | succ i =>
      have ht : Steps (.get (pack (x :: xs)) "tail") (pack xs) :=
        .next (.field _ "tail" (pack xs) rfl) (.refl _)
      exact steps_trans (nth_steps i ht) (ih i (by simpa using hi))

end Obend.Hardware.Gpu.ArraySource.Core
end
