module
/-
# Obend.Slot.Core4 — Core4 as a contextual calculus, on its closed-hole fragment

The instance the slot theory needs, at the language this library is about. A HOLE is a free de Bruijn
hypothesis of an open Core4 term (`Term.bound x` with `x` beyond the binders above it); a FILLING is
a closed annotated term; `msubst` substitutes fillings for the hypotheses they name and merges the
fillings' lambda annotations at the positions where they land, so the filled term is again an
`AnnotatedTerm` the checker reads.

What fragment this is, said as LANG-68 said it of nano: a hole here has the EMPTY local context. CMTT's
`u :: [Ψ ⊢ A]` with `Ψ ≠ []` and occurrences `u[σ]` carrying a substitution are not expressible: Core4
has no hole former, and a free variable cannot carry a context. So `Calculus.check Ψ t A` judges a
filling in the context `Ψ` of the HOLE'S SURROUNDINGS, and the filling may use those hypotheses, but a
filling is itself never open in further holes (depth one). The checker is Core4's own `check` at the
front end's type fuel; `strengthen`/`weaken` rename hypotheses with `Term.rename`.

Nothing here is proved about `check` under `msubst` (the substitution lemma of the calculus): that is
the law `CalculusLaws.msubst_lemma` nano stated of its instance, and it is owed here as a theorem about
`Obend.Core.Check` (a typed closed filling at a hypothesis of its type keeps the whole typed). What is
proved: the three equations a slot reader relies on (`msubst_var_filled`, `msubst_var_open`,
`uses_var`), and `annotationsAt_root`.
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Slot.Calculus

@[expose] public section
namespace Obend.Slot.Core4

open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty Context)
open Obend.Core.Check (AnnotatedTerm Annotations)
open Obend.Core.Ty (LambdaAnnotation)
set_option autoImplicit false

/-- Does hypothesis `x` (a free de Bruijn index, counted at the root) occur in `t`? Each binder
shifts the index sought by one: `lam`, the successor arm of `ifZero`, every `case` arm. -/
def freeIn (x : Nat) : Term → Bool
  | .bound index => index == x
  | .lam body => freeIn (x + 1) body
  | .app function argument => freeIn x function || freeIn x argument
  | .mix lower upper => freeIn x lower || freeIn x upper
  | .fix spec inherited => freeIn x spec || freeIn x inherited
  | .specification metadata extension => freeIn x metadata || freeIn x extension
  | .prototype spec target => freeIn x spec || freeIn x target
  | .reflect target => freeIn x target
  | .metadata spec => freeIn x spec
  | .project target => freeIn x target
  | .nat _ => false
  | .boolean _ => false
  | .label _ => false
  | .binary _ left right => freeIn x left || freeIn x right
  | .extend inherited fields => freeIn x inherited || (fields.map fun field => freeIn x field.2).any id
  | .record fields => (fields.map fun field => freeIn x field.2).any id
  | .get target _ => freeIn x target
  | .ifZero value zero successorBody => freeIn x value || freeIn x zero || freeIn (x + 1) successorBody
  | .inject _ payload => freeIn x payload
  | .case scrutinee arms => freeIn x scrutinee || (arms.map fun arm => freeIn (x + 1) arm.2).any id
  | .ifBool condition whenTrue whenFalse => freeIn x condition || freeIn x whenTrue || freeIn x whenFalse
  | .perform plan => freeIn x plan
  | .done value => freeIn x value
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf field.snd < sizeOf field := by
         cases field
         simp +arith
       omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf arm.snd < sizeOf arm := by
         cases arm
         simp +arith
       omega)

/-- The filling of hypothesis `x` at binder depth `depth`, if `σ` fills it: a `bound index` with
`depth ≤ index` is the hypothesis `index - depth`. -/
def fillingAt (σ : Nat → Option AnnotatedTerm) (depth index : Nat) : Option AnnotatedTerm :=
  if depth ≤ index then σ (index - depth) else none

/-- Walk `t` along a checker position (`Obend.Core.Check.infer`'s conventions: children numbered as
the checker numbers them, record fields by their index, `extend` fields under `1`, `case` arms under
`1`, binders counted). If the path passes through a filled hypothesis, the answer is the filling's own
annotation at the rest of the path; otherwise it is `ann` at the whole path. -/
def annotationsAt (σ : Nat → Option AnnotatedTerm) (ann : Annotations) :
    Nat → List Nat → Term → List Nat → Option LambdaAnnotation
  | depth, path, .bound index, rest =>
      match fillingAt σ depth index with
      | some f => f.annotations rest
      | none => ann (path ++ rest)
  | depth, path, .lam body, 0 :: rest => annotationsAt σ ann (depth + 1) (path ++ [0]) body rest
  | depth, path, .app function argument, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) function rest
  | depth, path, .app function argument, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) argument rest
  | depth, path, .mix lower upper, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) lower rest
  | depth, path, .mix lower upper, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) upper rest
  | depth, path, .fix spec inherited, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .fix spec inherited, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) inherited rest
  | depth, path, .specification metadata extension, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) metadata rest
  | depth, path, .specification metadata extension, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) extension rest
  | depth, path, .prototype spec target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .prototype spec target, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) target rest
  | depth, path, .reflect target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .metadata spec, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .project target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .binary _ left right, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) left rest
  | depth, path, .binary _ left right, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) right rest
  | depth, path, .extend inherited fields, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) inherited rest
  | depth, path, .extend inherited fields, 1 :: k :: rest =>
      match hget : fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [1, k]) field.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .record fields, k :: rest =>
      match hget : fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [k]) field.2 rest
      | none => ann (path ++ k :: rest)
  | depth, path, .get target _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .ifZero value zero successorBody, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | depth, path, .ifZero value zero successorBody, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) zero rest
  | depth, path, .ifZero value zero successorBody, 2 :: rest => annotationsAt σ ann (depth + 1) (path ++ [2]) successorBody rest
  | depth, path, .inject _ payload, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) payload rest
  | depth, path, .case scrutinee arms, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) scrutinee rest
  | depth, path, .case scrutinee arms, 1 :: k :: rest =>
      match hget : arms[k]? with
      | some arm => annotationsAt σ ann (depth + 1) (path ++ [1, k]) arm.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .ifBool condition whenTrue whenFalse, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) condition rest
  | depth, path, .ifBool condition whenTrue whenFalse, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) whenTrue rest
  | depth, path, .ifBool condition whenTrue whenFalse, 2 :: rest => annotationsAt σ ann depth (path ++ [2]) whenFalse rest
  | depth, path, .perform plan, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) plan rest
  | depth, path, .done value, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | _, path, _, rest => ann (path ++ rest)
termination_by _ _ t _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hmem := List.mem_of_getElem? hget
       have hlist := List.sizeOf_lt_of_mem hmem
       first
         | (have hpair : sizeOf field.snd < sizeOf field := by cases field; simp +arith
            omega)
         | (have hpair : sizeOf arm.snd < sizeOf arm := by cases arm; simp +arith
            omega))

/-- Fill the hypotheses `σ` names in an annotated term: the term by `Term.substitute` (a filling is
closed, so lifting under binders renames nothing that matters), the annotations by `annotationsAt`.
Assumptions are the template's. -/
def msubst (σ : Nat → Option AnnotatedTerm) (t : AnnotatedTerm) : AnnotatedTerm where
  term := t.term.substitute fun index =>
    match σ index with
    | some f => f.term
    | none => .bound index
  annotations := annotationsAt σ t.annotations 0 [] t.term
  assumptions := t.assumptions

/-- The front end's type fuel (`Obend.Core.Check`'s preview wire caps `typeFuel` at 16384). -/
def checkFuel : Nat := 16384

/-- Hypothesis `x` as a term: a bare `bound x`, no annotations. -/
def var (x : Nat) : AnnotatedTerm := ⟨.bound x, fun _ => none, {}⟩

/-- Rename hypothesis indices from `x` on down by one (the hypothesis `x` itself must be unused). -/
def lowerFrom (x : Nat) (index : Nat) : Nat := if x < index then index - 1 else index

/-- Rename hypothesis indices from `x` on up by one, making room at `x`. -/
def liftFrom (x : Nat) (index : Nat) : Nat := if x ≤ index then index + 1 else index

instance : Obend.Slot.Calculus AnnotatedTerm where
  Ty := Ty
  Ctx := Context
  msubst := msubst
  check Ψ t A :=
    match Obend.Core.Check.check t Ψ checkFuel with
    | some checked => decide (checked.type = A)
    | none => false
  uses t x := freeIn x t.term
  drop Ψ x := Ψ.eraseIdx x
  strengthen x t := { t with term := t.term.rename (lowerFrom x) }
  weaken x t := { t with term := t.term.rename (liftFrom x) }
  var := var
  lookup Ψ x := (Ψ[x]?).map (·.type)

/-- At the root (depth 0, empty path), a filled hypothesis answers with the filling's own annotations. -/
theorem annotationsAt_root (σ : Nat → Option AnnotatedTerm) (ann : Annotations) (x : Nat)
    (f : AnnotatedTerm) (h : σ x = some f) (rest : List Nat) :
    annotationsAt σ ann 0 [] (.bound x) rest = f.annotations rest := by
  simp [annotationsAt, fillingAt, h]

/-- Filling a hypothesis that `σ` names gives the filling. -/
theorem msubst_var_filled (σ : Nat → Option AnnotatedTerm) (x : Nat) (f : AnnotatedTerm)
    (h : σ x = some f) : msubst σ (var x) = { f with assumptions := {} } := by
  unfold msubst var
  simp only [Obend.Core.Term.Term.substitute, h]
  congr 1
  funext rest
  exact annotationsAt_root σ (fun _ => none) x f h rest

/-- A hypothesis `σ` does not name is left open. -/
theorem msubst_var_open (σ : Nat → Option AnnotatedTerm) (x : Nat) (h : σ x = none) :
    msubst σ (var x) = var x := by
  unfold msubst var
  simp only [Obend.Core.Term.Term.substitute, h]
  congr 1
  funext rest
  simp [annotationsAt, fillingAt, h]

/-- A hypothesis occurs in itself. -/
theorem uses_var (x : Nat) : Obend.Slot.Calculus.uses (var x) x = true := by
  simp [Obend.Slot.Calculus.uses, var, freeIn]

#assert_axioms annotationsAt_root msubst_var_filled msubst_var_open uses_var

end Obend.Slot.Core4
end
