module
/- Executable probes of preparation and its bounded search, run by the build (`#guard`). -/
public import Obend.Elab.Prepare
public meta import Obend.Elab.Prepare

@[expose] public section

namespace Obend.Elab.Proofs.PrepareProbes
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Elab.Prepare
open Obend.Core.Term (Term)

/-- `(λx.x) 3` at `Nat`, erased. -/
def letProbe : AnnotatedTerm := ⟨.app (.lam (.bound 0)) (.nat 3), noHints, {}⟩

-- The bare checker refuses it at the lambda in function position.
#guard (match checkAgainst letProbe [] .natural with
  | .error (.missingLambdaAnnotation [0]) => true | _ => false)
#guard (prepareChecked letProbe [] .natural).toBool

/-- A let whose body uses the bound variable twice gets an unrestricted parameter. -/
def twiceProbe : AnnotatedTerm :=
  ⟨.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat 3), noHints, {}⟩
#guard (prepareChecked twiceProbe [] .natural).toBool

/-- A lambda stored in a record and projected: synthesis position, no local information. -/
def storedProbe : AnnotatedTerm :=
  ⟨.app (.get (.record [("f", .lam (.bound 0))]) "f") (.nat 3), noHints, {}⟩
#guard (match prepareChecked storedProbe [] .natural with
  | .error (.silent [0, 0, 0] "lambda") => true | _ => false)
-- The bounded search fills it from the scalar candidates and the checker accepts.
#guard (prepareSearch 1 storedProbe [] .natural).toBool

/-- The same shape with a record parameter: no scalar candidate fits, all 72 are tried, and the
refusal names the path and the count, not "untypable". -/
def recordParameterProbe : AnnotatedTerm :=
  ⟨.app (.get (.record [("f", .lam (.get (.bound 0) "x"))]) "f") (.record [("x", .nat 1)]), noHints, {}⟩
#guard (match prepareSearch 1 recordParameterProbe [] .natural with
  | .error (.searchExhausted [0, 0, 0] 72) => true | _ => false)

end Obend.Elab.Proofs.PrepareProbes
end
