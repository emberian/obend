module
/- Scoped renaming and substitution composition. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

 public theorem scoped_substitute_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Term) (hf : ∀ i, i < n → f i = .bound i) : term.substitute f = term := by
  exact Obend.Core.TermTraverse.scoped_substitute_identity term n ((scoped_encode_iff n term).1 h) f hf


 public theorem scoped_substitution_congr {n : Nat} {term : Term} (h : Scoped n term)
    (first second : Nat → Term) (same : ∀ i, i < n → first i = second i) :
    term.substitute first = term.substitute second := by
  exact Obend.Core.TermTraverse.scoped_substitution_congr term n ((scoped_encode_iff n term).1 h) first second same


 theorem liftRename_comp (first second : Nat → Nat) :
    (fun i => liftRename second (liftRename first i)) = liftRename (fun i => second (first i)) := by
  funext i; cases i <;> rfl

 theorem liftRename_substitution_comp (rename : Nat → Nat) (substitution : Nat → Term) :
    (fun i => liftSubstitution substitution (liftRename rename i)) =
      liftSubstitution (fun i => substitution (rename i)) := by
  funext i; cases i <;> rfl

 public theorem scoped_rename_comp {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Nat) :
    (term.rename first).rename second = term.rename (fun i => second (first i)) := by
  exact Obend.Core.TermTraverse.rename_comp term first second


 public theorem scoped_rename_substitute {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Term) :
    (term.rename first).substitute second = term.substitute (fun i => second (first i)) := by
  exact Obend.Core.TermTraverse.rename_substitute term first second


 public theorem lifted_substitution_scoped {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) :
    ∀ i, i < n+1 → Scoped (m+1) (liftSubstitution substitution i) := by
  intro i hi
  cases i with
  | zero => exact .bound (Nat.zero_lt_succ _)
  | succ i => exact scoped_weaken (images i (Nat.lt_of_succ_lt_succ hi))

 theorem lifted_substitution_rename {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) (rename : Nat → Nat) :
    ∀ i, i < n+1 →
      (liftSubstitution substitution i).rename (liftRename rename) =
        liftSubstitution (fun j => (substitution j).rename rename) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.rename,liftRename]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi)),
        scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi))]
      rfl

 theorem scoped_substitute_rename {n m : Nat} {term : Term} (h : Scoped n term)
    (substitution : Nat → Term) (images : ∀ i, i < n → Scoped m (substitution i))
    (rename : Nat → Nat) :
    (term.substitute substitution).rename rename =
      term.substitute (fun i => (substitution i).rename rename) := by
  exact Obend.Core.TermTraverse.substitute_rename term substitution rename


 theorem lifted_substitution_comp {n m k : Nat} {first second : Nat → Term}
    (images : ∀ i, i < n → Scoped m (first i))
    (nextImages : ∀ i, i < m → Scoped k (second i)) :
    ∀ i, i < n+1 → (liftSubstitution first i).substitute (liftSubstitution second) =
      liftSubstitution (fun j => (first j).substitute second) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_substitute (images i (Nat.lt_of_succ_lt_succ hi))]
      simpa only [liftSubstitution] using
        (scoped_substitute_rename (images i (Nat.lt_of_succ_lt_succ hi)) second nextImages Nat.succ).symm

 public theorem scoped_substitute_comp {n m k : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Term) (images : ∀ i, i < n → Scoped m (first i))
    (second : Nat → Term) (nextImages : ∀ i, i < m → Scoped k (second i)) :
    (term.substitute first).substitute second =
      term.substitute (fun i => (first i).substitute second) := by
  exact Obend.Core.TermTraverse.substitute_comp term first second

end Obend.Core.Proofs.Adequacy
