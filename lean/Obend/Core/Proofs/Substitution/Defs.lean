module
/- Filling hypotheses: `fillingAt`, `annotationsAt`, `fillTerm`, `msubst`, `UsesLE`, `Fillings`, `FilledAnn`. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-! ## Filling hypotheses -/

/-- The filling of hypothesis `x` at binder depth `depth`, if `σ` fills it: a `bound index` with
`depth ≤ index` is the hypothesis `index - depth`. -/
@[expose] public def fillingAt (σ : Nat → Option AnnotatedTerm) (depth index : Nat) : Option AnnotatedTerm :=
  if depth ≤ index then σ (index - depth) else none

/-- Walk `t` along a checker position (`infer`'s conventions: children numbered as the checker
numbers them, record fields by their index, `extend` fields under `1`, `case` arms under `1`,
binders counted). If the path passes through a filled hypothesis, the answer is the filling's own
annotation at the rest of the path; otherwise it is `ann` at the whole path. Structural on the
path, so the kernel evaluates it. -/
@[expose] public def annotationsAt (σ : Nat → Option AnnotatedTerm) (ann : Annotations) :
    Nat → List Nat → Term → List Nat → Option LambdaAnnotation
  | depth, path, .bound index, rest =>
      match fillingAt σ depth index with
      | some f => f.annotations rest
      | none => ann (path ++ rest)
  | depth, path, .lam body, 0 :: rest => annotationsAt σ ann (depth + 1) (path ++ [0]) body rest
  | depth, path, .app function _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) function rest
  | depth, path, .app _ argument, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) argument rest
  | depth, path, .mix lower _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) lower rest
  | depth, path, .mix _ upper, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) upper rest
  | depth, path, .fix spec _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .fix _ inherited, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) inherited rest
  | depth, path, .specification metadata _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) metadata rest
  | depth, path, .specification _ extension, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) extension rest
  | depth, path, .prototype spec _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .prototype _ target, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) target rest
  | depth, path, .reflect target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .metadata spec, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .project target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .binary _ left _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) left rest
  | depth, path, .binary _ _ right, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) right rest
  | depth, path, .extend inherited _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) inherited rest
  | depth, path, .extend _ fields, 1 :: k :: rest =>
      match fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [1, k]) field.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .record fields, k :: rest =>
      match fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [k]) field.2 rest
      | none => ann (path ++ k :: rest)
  | depth, path, .get target _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .ifZero value _ _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | depth, path, .ifZero _ zero _, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) zero rest
  | depth, path, .ifZero _ _ successorBody, 2 :: rest => annotationsAt σ ann (depth + 1) (path ++ [2]) successorBody rest
  | depth, path, .inject _ payload, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) payload rest
  | depth, path, .case scrutinee _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) scrutinee rest
  | depth, path, .case _ arms, 1 :: k :: rest =>
      match arms[k]? with
      | some arm => annotationsAt σ ann (depth + 1) (path ++ [1, k]) arm.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .ifBool condition _ _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) condition rest
  | depth, path, .ifBool _ whenTrue _, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) whenTrue rest
  | depth, path, .ifBool _ _ whenFalse, 2 :: rest => annotationsAt σ ann depth (path ++ [2]) whenFalse rest
  | depth, path, .perform plan, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) plan rest
  | depth, path, .done value, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | _, path, _, rest => ann (path ++ rest)
termination_by structural _ _ _ rest => rest

/-- The term substitution `msubst` applies at binder depth `depth`: a filling's term where `σ`
fills, the hypothesis itself otherwise. Fillings are closed, so lifting under a binder changes
nothing (`liftSubstitution_fillTerm`). -/
@[expose] public def fillTerm (σ : Nat → Option AnnotatedTerm) (depth : Nat) (index : Nat) : Term :=
  match fillingAt σ depth index with
  | some f => f.term
  | none => .bound index

/-- Fill the hypotheses `σ` names in an annotated term: the term by `Term.substitute`, the
annotations by `annotationsAt`. Assumptions are the template's. -/
@[expose] public def msubst (σ : Nat → Option AnnotatedTerm) (t : AnnotatedTerm) : AnnotatedTerm where
  term := t.term.substitute (fillTerm σ 0)
  annotations := annotationsAt σ t.annotations 0 [] t.term
  assumptions := t.assumptions

/-- Pointwise `≤` on use vectors of one length. -/
public inductive UsesLE : Uses → Uses → Prop
  | nil : UsesLE [] []
  | cons {a b : Nat} {u v : Uses} : a ≤ b → UsesLE u v → UsesLE (a :: u) (b :: v)

/-- What the lemma asks of the fillings: each is closed, and checks (under the template's assumptions
`asm`, with its own annotations) in the hole's context `Ψ` at fuel `m`, at exactly the type `Ψ`
declares for the hypothesis it fills. -/
public structure Fillings (asm : Assumptions) (Ψ : Context) (m : Nat) (σ : Nat → Option AnnotatedTerm) : Prop where
  closed : ∀ x f, σ x = some f → Scoped 0 f.term
  typed : ∀ x f, σ x = some f → ∃ (b : Binding) (r : Inferred asm Ψ f.term),
    Ψ[x]? = some b ∧ infer asm f.annotations Ψ [] m f.term = some r ∧ r.type = b.type

/-- The annotations `ann'` of the filled term agree, below `pos`, with what `annotationsAt` reads off
`term` at `(depth, pos)`. -/
@[expose] public def FilledAnn (σ : Nat → Option AnnotatedTerm) (ann ann' : Annotations) (depth : Nat)
    (pos : List Nat) (term : Term) : Prop :=
  ∀ rest, ann' (pos ++ rest) = annotationsAt σ ann depth pos term rest

/-- `FilledAnn` for each item of a field or arm list, numbered from `index` under `pos`. -/
@[expose] public def FilledAnnList (σ : Nat → Option AnnotatedTerm) (ann ann' : Annotations) (depth : Nat)
    (pos : List Nat) (index : Nat) (items : List (String × Term)) : Prop :=
  ∀ j rest, (hj : j < items.length) →
    ann' (pos ++ (index + j) :: rest) = annotationsAt σ ann depth (pos ++ [index + j]) (items[j]).2 rest

/-- `σ` filling hypothesis `0` with `f`, nothing else. -/
@[expose] public def fillZero (f : AnnotatedTerm) : Nat → Option AnnotatedTerm := fun i => if i = 0 then some f else none

@[expose] public def fuelTemplate : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun p => if p = [] then
    some ⟨.natural, .arrow .reusable .unrestricted .natural .natural, .unrestricted, .reusable⟩ else none, {}⟩
@[expose] public def fuelFilling : AnnotatedTerm :=
  ⟨.lam (.bound 0), fun p => if p = [] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩
@[expose] public def fuelContext : Context := [⟨.arrow .reusable .unrestricted .natural .natural, .unrestricted⟩]

@[expose] public def linearTemplate : AnnotatedTerm := ⟨.binary .add (.bound 0) (.bound 1), fun _ => none, {}⟩
@[expose] public def linearFilling : AnnotatedTerm := ⟨.bound 1, fun _ => none, {}⟩
@[expose] public def linearContext : Context := [⟨.natural, .unrestricted⟩, ⟨.natural, .linear⟩]

@[expose] public def sumRow : Ty := .field "l" .natural .emptyRow
@[expose] public def sumAssumptions : Assumptions := ⟨[(0, .variant sumRow)], [], []⟩
@[expose] public def aliasFilling : AnnotatedTerm :=
  ⟨.inject "l" (.nat 1), fun p => if p = [] then some ⟨.natural, .variable 0, .unrestricted, .reusable⟩ else none,
    sumAssumptions⟩
@[expose] public def aliasTemplate : AnnotatedTerm := ⟨.bound 0, fun _ => none, {}⟩
@[expose] public def aliasContext : Context := [⟨.variable 0, .linear⟩]

end Obend.Core.Proofs.Substitution
