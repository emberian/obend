module
/- Sharing examples: executor and source agree. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- All unused arguments, including arbitrary diverging Fix computations,
remain suspended at their original lexical address. This is a general theorem
about the actual bounded executor, not a single closed native test. -/
 theorem unused_argument_executor (argument : Term) (number : Nat) :
    runBounded ⟨1,1⟩ 5 (initial (.app (.lam (.nat number)) argument)) =
      .finished (.natural number)
        ⟨#[.suspended ⟨argument,[]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial]

 theorem unused_argument_source (argument : Term) (number : Nat) :
    Evaluates (.app (.lam (.nat number)) argument) (.nat number) := by
  constructor
  · have beta := Step.beta (.nat number) argument
    simpa [instantiate,Term.substitute] using Steps.next beta (Steps.refl _)
  · exact .natural _

/-- The second demand sees the first demand's cache at the identical address.
This exercises real memoization for every natural argument. -/
 theorem shared_argument_executor (number : Nat) :
    runBounded ⟨1,2⟩ 13
      (initial (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.nat number,[]⟩ (.natural number)],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    Array.set!,Array.setIfInBounds]

 theorem shared_argument_source (number : Nat) :
    Evaluates (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number)) (.nat (number+number)) := by
  constructor
  · have beta := Step.beta (.binary .add (.bound 0) (.bound 0)) (.nat number)
    have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
      (.natural _) (.natural _) rfl
    exact .next (by simpa [instantiate,Term.substitute] using beta) (.next primitive (.refl _))
  · exact .natural _

/-- Two demands of the same record field cache exactly its one address. The
other field retains arbitrary source, including a divergent knot, suspended.
The record target itself also retains its original source and cached pointer map. -/
 theorem shared_field_executor (unused : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 21
      (initial (.app
        (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
        (.record [("x",.nat number),("unused",unused)]))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.record [("x",.nat number),("unused",unused)],[]⟩
          (.record [("x",1),("unused",2)]),
        .cached ⟨.nat number,[]⟩ (.natural number),
        .suspended ⟨unused,[]⟩],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    allocateFields,Array.set!,Array.setIfInBounds]

 theorem shared_field_source (unused : Term) (number : Nat) :
    Evaluates (.app
      (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
      (.record [("x",.nat number),("unused",unused)])) (.nat (number+number)) := by
  let fields : List (String × Term) := [("x",.nat number),("unused",unused)]
  have field := Step.field fields "x" (.nat number) rfl
  have beta := Step.beta (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")) (.record fields)
  have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
    (.natural _) (.natural _) rfl
  constructor
  · exact .next (by simpa [instantiate,Term.substitute,fields] using beta)
      (.next (.binaryLeft .add _ field)
        (.next (.binaryRight .add _ (.natural _) field) (.next primitive (.refl _))))
  · exact .natural _

/-- General tied Fix can return a ground target without demanding either
recursive self or inherited target. Both argument thunks stay suspended, while
the tied address is memoized in place with its retained unfolding origin. -/
 theorem fixed_constant_executor (inherited : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 11 (initial (.fix (.lam (.lam (.nat number))) inherited)) =
    .finished (.natural number)
      ⟨#[.cached
          ⟨.app (.app (.lam (.lam (.nat number))) (.bound 0)) (inherited.rename Nat.succ),[0]⟩
          (.natural number),
        .suspended ⟨.bound 0,[0]⟩,
        .suspended ⟨inherited.rename Nat.succ,[0]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,Term.rename,
    Array.set!,Array.setIfInBounds]

 theorem fixed_constant_source (inherited : Term) (number : Nat) :
    Evaluates (.fix (.lam (.lam (.nat number))) inherited) (.nat number) := by
  constructor
  · have selfBeta := Step.beta (.lam (.nat number)) (.fix (.lam (.lam (.nat number))) inherited)
    have inheritedBeta := Step.beta (.nat number) inherited
    exact .next (.fix _ _) (.next (.application inherited (by
      simpa [instantiate,Term.substitute] using selfBeta)) (.next (by
        simpa [instantiate,Term.substitute] using inheritedBeta) (.refl _)))
  · exact .natural _

end Obend.Core.Proofs.Adequacy
