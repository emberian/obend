module
/- The work the bidirectional checker does on an annotated term, as a grant measures it.

`elaborate` makes one call per term node (an unannotated case in synthesis makes a second
call on its first arm), and at an annotated node it reads, and may compare, the
annotation's types. `checkWork` counts one per node plus the constructors of every
annotation the checker reads, so it grows with a record's width as well as its depth
(a 1,000-field record of literals costs more than 1,000, where the retired `termDepth`
gave 3). It does not meter agreement decisions: `sameType` is a finite visited-pair
search whose cost is quadratic in the type graph's support, and that is not a function
of these counts alone. A grant over `checkWork` is a structural admissibility limit that
scales with what the checker reads, not a CPU or memory bound. -/
public import Obend.Core.Check

@[expose] public section
namespace Obend.Elab.Work
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check
set_option autoImplicit false

/-- The number of constructors in a type. -/
def tyNodes : Ty → Nat
  | .arrow _ _ a b | .field _ a b | .specification a b | .prototype a b => tyNodes a + tyNodes b + 1
  | .variant a => tyNodes a + 1
  | .computation a b c => tyNodes a + tyNodes b + tyNodes c + 1
  | _ => 1

/-- What reading the annotation at a position costs: nothing when there is none. -/
def annotationWork (annotations : Annotations) (path : List Nat) : Nat :=
  match annotations path with
  | some annotation => tyNodes annotation.domain + tyNodes annotation.codomain
  | none => 0

mutual
/-- One per node, plus the annotation read there, at the checker's own source positions. -/
def termWork (annotations : Annotations) (path : List Nat) : Term → Nat
  | .hole _ _ | .bound _ | .nat _ | .boolean _ | .label _ => 1 + annotationWork annotations path
  | .lam t | .reflect t | .metadata t | .project t | .inject _ t | .perform t | .done t | .get t _ =>
    1 + annotationWork annotations path + termWork annotations (path ++ [0]) t
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b =>
    1 + annotationWork annotations path + termWork annotations (path ++ [0]) a + termWork annotations (path ++ [1]) b
  | .ifZero a b c | .ifBool a b c =>
    1 + annotationWork annotations path + termWork annotations (path ++ [0]) a +
      termWork annotations (path ++ [1]) b + termWork annotations (path ++ [2]) c
  | .extend t fields =>
    1 + annotationWork annotations path + termWork annotations (path ++ [0]) t + fieldsWork annotations (path ++ [1]) 0 fields
  | .record fields => 1 + annotationWork annotations path + fieldsWork annotations path 0 fields
  | .case t arms =>
    1 + annotationWork annotations path + termWork annotations (path ++ [0]) t + fieldsWork annotations (path ++ [1]) 0 arms
def fieldsWork (annotations : Annotations) (path : List Nat) (index : Nat) : List (String × Term) → Nat
  | [] => 0
  | (_, t) :: rest => termWork annotations (path ++ [index]) t + fieldsWork annotations path (index + 1) rest
end

/-- The checker's work on an annotated term. -/
def checkWork (source : AnnotatedTerm) : Nat := termWork source.annotations [] source.term

mutual
/-- Structural nesting: the measure the retired `Slot.Core4.termDepth` was, kept for the front
end's `typeFuel`, which bounded the historical checker's recursion and still bounds nesting. -/
def nestingDepth : Term → Nat
  | .hole _ _ | .bound _ | .nat _ | .boolean _ | .label _ => 1
  | .lam t | .reflect t | .metadata t | .project t | .inject _ t | .perform t | .done t | .get t _ => nestingDepth t + 1
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b =>
    max (nestingDepth a) (nestingDepth b) + 1
  | .ifZero a b c | .ifBool a b c => max (nestingDepth a) (max (nestingDepth b) (nestingDepth c)) + 1
  | .extend t fields => max (nestingDepth t) (fieldsDepth fields) + 1
  | .record fields => fieldsDepth fields + 1
  | .case t arms => max (nestingDepth t) (fieldsDepth arms) + 1
def fieldsDepth : List (String × Term) → Nat
  | [] => 0
  | (_, t) :: rest => max (nestingDepth t + 1) (fieldsDepth rest)
end

/-- Every node costs at least one. -/
theorem termWork_pos (annotations : Annotations) (path : List Nat) (t : Term) : 0 < termWork annotations path t := by
  cases t <;> simp [termWork] <;> omega

end Obend.Elab.Work
end
