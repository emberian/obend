module
public import Lean

public section
open Lean.Parser.Tactic

/-- Split a derivation or constructor, simplify every arm with the supplied
lemmas and local hypotheses, then try congruence reasoning and arithmetic.
Unsolved arms remain available to subsequent tactics. Splitting and simp errors
are deliberately not caught, so an invalid hypothesis or lemma is reported.
-/
macro "obend_cases " h:elimTarget " with " "[" lemmas:simpLemma,* "]" : tactic =>
  `(tactic| cases $h <;>
    (simp_all (config := { failIfUnchanged := false }) [$lemmas,*]
     try (first | grind | omega)))

/-- The induction form retains the induction hypotheses in surviving arms. -/
macro "obend_cases " "induction " h:elimTarget " with " "[" lemmas:simpLemma,* "]" : tactic =>
  `(tactic| induction $h <;>
    (simp_all (config := { failIfUnchanged := false }) [$lemmas,*]
     try (first | grind | omega)))
