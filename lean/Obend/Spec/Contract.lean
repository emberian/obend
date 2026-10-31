module
/-
# Obend.Spec.Contract — the composition contract of an Objective Bend specification chain (GPT-6 row D).

A layer of `fix(compose(L₁, …, Lₙ), seed)` makes three kinds of claim about rows:

* `assumes`  — members it reads from the FINAL self `S` (its `Self has {...}` bound and its
  `requires`), at the types it reads them;
* `consumes` — members it reads from the row BENEATH it (`Super has {...}`);
* `provides` — the members it defines.

`F_L(S, I) = provides ++ I` is the row a layer leaves (the first entry of a name wins, as Core4
`overlay` after `extend`), and its contract is `C_L(S, I) = assumes ⊆ S ∧ consumes ⊆ I ∧
no provided member changes the type of a member of I`. The contract of a composition is

    C_{A;B}(S, I) = C_A(S, I) ∧ C_B(S, F_A(S, I)),    F_{A;B}(S, I) = F_B(S, F_A(S, I)),

which is `Obend.Spec.Proofs.Contract.run_append`. `discharge` is that contract checked at `fix`: thread the seed
through every layer, then require the final row to be exactly the final self. The elaborator's
`chainFix` decides every one of its contract refusals by calling `checkLayer` and `close` here,
so the theorems (`Obend.Spec.Proofs.Contract`) are about the checks that run. Ported from minidregg
`Compiler/ObjectiveBendContract.lean` (commit 092027a2).

Rows are lists of `(name, type)`; the elaborator passes canonical types, so `==` on a type is
the elaborator's `sameTy`. -/
public import Lean
public section
namespace Obend.Spec.Contract
set_option autoImplicit false

abbrev Row (τ : Type) := List (String × τ)

variable {τ : Type} [BEq τ]

/-- The type a row gives `name`: its first entry of that name. -/
@[expose] def get? (row : Row τ) (name : String) : Option τ :=
  (row.find? (·.1 == name)).map (·.2)

/-- The members of `required` that `actual` lacks or has at another type. -/
@[expose] def missing (actual required : Row τ) : List String :=
  required.filterMap fun (n, t) => if get? actual n == some t then none else some n

/-- The members a layer provides at a type other than the one the row beneath gives them:
a REPLACEMENT. An addition (absent beneath) and an override (same type) are not listed. -/
def replaced (beneath provides : Row τ) : List String :=
  provides.filterMap fun (n, t) => match get? beneath n with
    | some t' => if t' == t then none else some n
    | none => none

structure Layer (τ : Type) where
  name : String
  assumes : Row τ
  consumes : Row τ
  provides : Row τ
  /-- A layer whose result row is exactly `provides` (an extension declaring its whole result
  type), rather than `provides` over the row beneath (a specification's methods). -/
  whole : Bool := false

/-- The named refusals of a composition contract. The elaborator renders each with the text
the `refused (...)` cohort rows pin. -/
inductive Refusal where
  | selfBound (layer : String) (missing : List String)
  | inheritedUnprovided (layer : String) (missing beneath : List String)
  | replaceUndeclared (layer : String) (members : List String)
  | requiresUnprovided (missing : List String)
  | seedExtra (extra : List String)
  | providedMismatch
  deriving Repr, BEq

/-- `F_L(S, I)`. -/
def Layer.leaves (layer : Layer τ) (beneath : Row τ) : Row τ :=
  if layer.whole then layer.provides else layer.provides ++ beneath

/-- The clauses of `C_L(S, I)` about what the layer READS: its assumptions about the final self,
then what it consumes from the row beneath. -/
@[expose] def checkBounds (self beneath : Row τ) (layer : Layer τ) : Except Refusal Unit :=
  let unmetSelf := missing self layer.assumes
  if !unmetSelf.isEmpty then .error (.selfBound layer.name unmetSelf) else
  let unmetSuper := missing beneath layer.consumes
  if !unmetSuper.isEmpty then .error (.inheritedUnprovided layer.name unmetSuper (beneath.map (·.1))) else
  .ok ()

/-- The clause of `C_L(S, I)` about what the layer WRITES: an addition needs the member absent
beneath, an override needs it at the same type, and a type change is a replacement, which no
source form declares, so it is refused by name. On success, `F_L(S, I)`. -/
@[expose] def checkProvides (beneath : Row τ) (layer : Layer τ) : Except Refusal (Row τ) :=
  let changed := replaced beneath layer.provides
  if !changed.isEmpty then .error (.replaceUndeclared layer.name changed) else
  .ok (layer.leaves beneath)

/-- `C_L(S, I)`, deciding which clause fails first; on success, `F_L(S, I)`. -/
@[expose] def checkLayer (self beneath : Row τ) (layer : Layer τ) : Except Refusal (Row τ) :=
  (checkBounds self beneath layer).bind fun _ => checkProvides beneath layer

/-- The chain's contract threaded from `seed`: the row every layer leaves, or the first refusal. -/
@[expose] def run (self : Row τ) : Row τ → List (Layer τ) → Except Refusal (Row τ)
  | beneath, [] => .ok beneath
  | beneath, layer :: rest => (checkLayer self beneath layer).bind fun next => run self next rest

/-- The final row against the final self: exact, else what is missing, else what is extra,
else a type mismatch. `names` lists a row's member names without repetition. -/
def names (row : Row τ) : List String := (row.map (·.1)).eraseDups

@[expose] def close (self final : Row τ) : Except Refusal Unit :=
  if missing final self |>.isEmpty then
    if (names final).all (fun n => (get? self n).isSome) then .ok ()
    else .error (.seedExtra ((names final).filter fun n => (get? self n).isNone))
  else
    let absent := (names self).filter fun n => (get? final n).isNone
    if !absent.isEmpty then .error (.requiresUnprovided absent)
    else
      let extra := (names final).filter fun n => (get? self n).isNone
      if !extra.isEmpty then .error (.seedExtra extra) else .error .providedMismatch

/-- The composition contract discharged at `fix`. -/
@[expose] def discharge (self seed : Row τ) (chain : List (Layer τ)) : Except Refusal Unit :=
  (run self seed chain).bind (close self)

end Obend.Spec.Contract

end
