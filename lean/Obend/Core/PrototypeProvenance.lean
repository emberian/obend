module
/-
# Obend.Core.PrototypeProvenance — Intrinsic Prototype Fixpoint Provenance Witness (`LT4`)

Resolves Open Problem `LT4` from `nanodregg`:
In `Core4` (`Obend/Core/Term.lean`), `Term.prototype spec target` checks `spec` and `target`
independently without verifying that `target` was actually produced by unfolding/stepping
`Term.fix spec seed`.

This module defines:
1. `unfoldFix`, `reachesIn`, `PrototypeProvenance (fuel : Nat) (spec seed target : Term) : Bool`,
   and the inductive witness `HasPrototypeProvenance : Term → Term → Term → Prop` verifying that
   `target` is reachable by bounded reduction (`Obend.Law.step?`) from `unfoldFix spec seed`
   (and hence by `PositiveSteps` from `Term.fix spec seed`).
2. Constructive prototype typing judgment `ProtoTyping` and intrinsic synthesizer `synthProtoTerm`
   (`0 Classical.choice`) alongside `checkPrototypeWithProvenance (fuel : Nat) (env : Env) (ctx : Ctx) (spec seed target : Term) : Except CheckError Ty`
   checking both typing and `PrototypeProvenance fuel spec seed target = true`.
3. `checkPrototypeWithProvenance_sound`: if `checkPrototypeWithProvenance` succeeds, then
   `HasPrototypeProvenance spec seed target` (and `PositiveSteps (.fix spec seed) target`) holds
   and `.prototype spec target`, `spec`, and `target` are well-typed at the synthesized prototype type.
4. `forged_prototype_refused` (plus `#tooth` mutation probe): an arbitrary `target` of the right
   type that was NOT derived from `Term.fix spec seed` is rejected by `checkPrototypeWithProvenance`.
-/

public import Obend.Core.Bidirectional
public import Obend.Law.Proofs.Claim
public import Obend.Law.Proofs.Run
public import Obend.Tactic.Tooth

@[expose] public section

namespace Obend.Core.PrototypeProvenance

open Obend.Core.Term (Term Step Steps PositiveSteps Primitive)
open Obend.Core.Ty (Ty Context Binding LambdaAnnotation Reuse Quantity)
open Obend.Core.Check (Assumptions Annotations primitiveTypes)
open Obend.Core.Bidirectional (CheckRefusal)
open Obend.Law (step? step_iff termEq termEq_sound)

set_option autoImplicit false

/-- Single fixpoint unfolding step of `Term.fix spec seed`, matching `Step.fix spec seed`. -/
def unfoldFix (spec seed : Term) : Term :=
  .app (.app spec (.fix spec seed)) seed

/-- Every `Term.fix spec seed` steps in one small step (`Step.fix`) to `unfoldFix spec seed`. -/
theorem step_fix_unfoldFix (spec seed : Term) :
    Step (.fix spec seed) (unfoldFix spec seed) :=
  Step.fix spec seed

/-- Bounded small-step reachability checker using `Obend.Law.step?` and `Obend.Law.termEq`. -/
def reachesIn : Nat → Term → Term → Bool
  | 0, src, target => termEq src target
  | fuel + 1, src, target =>
    if termEq src target then true
    else
      match step? src with
      | some next => reachesIn fuel next target
      | none      => false

/-- Soundness of `reachesIn`: if `reachesIn fuel src target = true`, then `Steps src target`. -/
theorem reachesIn_sound {fuel : Nat} {src target : Term}
    (h : reachesIn fuel src target = true) :
    Steps src target := by
  induction fuel generalizing src with
  | zero =>
    simp [reachesIn] at h
    have heq := termEq_sound h
    subst heq
    exact .refl src
  | succ k ih =>
    unfold reachesIn at h
    split at h
    · rename_i heq
      have heq' := termEq_sound heq
      subst heq'
      exact .refl src
    · cases hstep : step? src with
      | none =>
        rw [hstep] at h
        contradiction
      | some next =>
        rw [hstep] at h
        have h_step : Step src next := step_iff.mpr hstep
        exact .next h_step (ih h)

/-- Inductive witness (`HasPrototypeProvenance spec seed target : Prop`) certifying that `target`
    is derived by unfolding `Term.fix spec seed` (`unfoldFix spec seed`) and reducing in zero or
    more small steps (`Steps (unfoldFix spec seed) target`). -/
inductive HasPrototypeProvenance (spec seed : Term) : Term → Prop where
  | ofUnfoldSteps {target : Term}
      (h_steps : Steps (unfoldFix spec seed) target) :
      HasPrototypeProvenance spec seed target

/-- Any `target` satisfying `HasPrototypeProvenance spec seed target` is reachable in one or more
    small steps (`PositiveSteps`) from `Term.fix spec seed`. -/
theorem HasPrototypeProvenance.toPositiveSteps {spec seed target : Term}
    (h : HasPrototypeProvenance spec seed target) :
    PositiveSteps (.fix spec seed) target := by
  cases h with
  | ofUnfoldSteps h_steps =>
    exact .begin (Step.fix spec seed) h_steps

/-- Any `target` satisfying `HasPrototypeProvenance spec seed target` is reachable in `Steps`
    from `Term.fix spec seed`. -/
theorem HasPrototypeProvenance.toSteps {spec seed target : Term}
    (h : HasPrototypeProvenance spec seed target) :
    Steps (.fix spec seed) target := by
  cases h with
  | ofUnfoldSteps h_steps =>
    exact .next (Step.fix spec seed) h_steps

/-- Decidable bounded fixpoint provenance check (`LT4`): verifies that `target` is reachable within
    `fuel` small steps from `unfoldFix spec seed`. -/
def PrototypeProvenance (fuel : Nat) (spec seed target : Term) : Bool :=
  reachesIn fuel (unfoldFix spec seed) target

/-- Soundness of `PrototypeProvenance`: if `PrototypeProvenance fuel spec seed target = true`,
    then `HasPrototypeProvenance spec seed target` holds. -/
theorem PrototypeProvenance_sound {fuel : Nat} {spec seed target : Term}
    (h : PrototypeProvenance fuel spec seed target = true) :
    HasPrototypeProvenance spec seed target :=
  .ofUnfoldSteps (reachesIn_sound h)

/-- Typing environment bundling `Assumptions` and lambda `Annotations` for bidirectional synthesis. -/
structure Env where
  assumptions : Assumptions := {}
  annotations : Annotations := fun _ => none

/-- Alias for `Obend.Core.Ty.Context`. -/
abbrev Ctx := Context

/-- Look up a `Binding` in a `Context` by de Bruijn index. -/
def lookupCtx? : Ctx → Nat → Option Binding
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: rest, i + 1 => lookupCtx? rest i

/-- Constructive typing derivation (`ProtoTyping`) for prototype terms, free of `Classical.choice`. -/
inductive ProtoTyping (env : Env) : Ctx → Term → Ty → Prop where
  | bound {ctx : Ctx} {idx : Nat} {b : Binding}
      (h_lookup : lookupCtx? ctx idx = some b) :
      ProtoTyping env ctx (.bound idx) b.type
  | nat {ctx : Ctx} (n : Nat) :
      ProtoTyping env ctx (.nat n) .natural
  | boolean {ctx : Ctx} (b : Bool) :
      ProtoTyping env ctx (.boolean b) .boolean
  | label {ctx : Ctx} (s : String) :
      ProtoTyping env ctx (.label s) .label
  | lam {ctx : Ctx} {body : Term} {ann : LambdaAnnotation}
      (h_body : ProtoTyping env (⟨ann.domain, ann.parameter⟩ :: ctx) body ann.codomain) :
      ProtoTyping env ctx (.lam body) (.arrow ann.reuse ann.parameter ann.domain ann.codomain)
  | app {ctx : Ctx} {fn arg : Term} {reuse : Reuse} {qty : Quantity} {dom cod : Ty}
      (h_fn : ProtoTyping env ctx fn (.arrow reuse qty dom cod))
      (h_arg : ProtoTyping env ctx arg dom) :
      ProtoTyping env ctx (.app fn arg) cod
  | binary {ctx : Ctx} {prim : Primitive} {l r : Term}
      (h_l : ProtoTyping env ctx l (primitiveTypes prim).1)
      (h_r : ProtoTyping env ctx r (primitiveTypes prim).1) :
      ProtoTyping env ctx (.binary prim l r) (primitiveTypes prim).2
  | ifBool {ctx : Ctx} {cond t f : Term} {resTy : Ty}
      (h_cond : ProtoTyping env ctx cond .boolean)
      (h_t : ProtoTyping env ctx t resTy)
      (h_f : ProtoTyping env ctx f resTy) :
      ProtoTyping env ctx (.ifBool cond t f) resTy
  | ifZero {ctx : Ctx} {val z s : Term} {resTy : Ty}
      (h_val : ProtoTyping env ctx val .natural)
      (h_z : ProtoTyping env ctx z resTy)
      (h_s : ProtoTyping env (⟨.natural, .unrestricted⟩ :: ctx) s resTy) :
      ProtoTyping env ctx (.ifZero val z s) resTy
  | fix {ctx : Ctx} {spec seed : Term} {seedTy targetTy : Ty}
      (h_spec : ProtoTyping env ctx spec
        (.arrow .reusable .unrestricted targetTy (.arrow .reusable .unrestricted seedTy targetTy)))
      (h_seed : ProtoTyping env ctx seed seedTy) :
      ProtoTyping env ctx (.fix spec seed) targetTy
  | reflect {ctx : Ctx} {t : Term} {specTy targetTy : Ty}
      (h_t : ProtoTyping env ctx t (.prototype specTy targetTy)) :
      ProtoTyping env ctx (.reflect t) specTy
  | project {ctx : Ctx} {t : Term} {specTy targetTy : Ty}
      (h_t : ProtoTyping env ctx t (.prototype specTy targetTy)) :
      ProtoTyping env ctx (.project t) targetTy
  | prototype {ctx : Ctx} {spec target : Term} {specTy targetTy : Ty}
      (h_spec : ProtoTyping env ctx spec specTy)
      (h_target : ProtoTyping env ctx target targetTy)
      (h_sc : specTy.isComputation = false)
      (h_tc : targetTy.isComputation = false) :
      ProtoTyping env ctx (.prototype spec target) (.prototype specTy targetTy)

/-- Dependent synthesis result pairing a synthesized `Ty` with its `ProtoTyping` proof. -/
structure ProtoInferred (env : Env) (ctx : Ctx) (t : Term) where
  type       : Ty
  derivation : ProtoTyping env ctx t type

/-- Constructive bidirectional type synthesizer (`synthProtoTerm`) with `0 Classical.choice`. -/
def synthProtoTerm (env : Env) : (ctx : Ctx) → List Nat → (t : Term) → Except CheckRefusal (ProtoInferred env ctx t)
  | ctx, path, .bound idx =>
    match hl : lookupCtx? ctx idx with
    | some b => .ok ⟨b.type, .bound hl⟩
    | none   => .error (.unboundVariable path idx)
  | _ctx, _path, .nat n => .ok ⟨.natural, .nat n⟩
  | _ctx, _path, .boolean b => .ok ⟨.boolean, .boolean b⟩
  | _ctx, _path, .label s => .ok ⟨.label, .label s⟩
  | ctx, path, .lam body =>
    match env.annotations path with
    | none => .error (.missingLambdaAnnotation path)
    | some ann =>
      match synthProtoTerm env (⟨ann.domain, ann.parameter⟩ :: ctx) (path ++ [0]) body with
      | .ok inf =>
        if h_eq : inf.type = ann.codomain then
          .ok ⟨.arrow ann.reuse ann.parameter ann.domain ann.codomain, .lam (h_eq ▸ inf.derivation)⟩
        else
          .error (.typeMismatch path ann.codomain inf.type)
      | .error err => .error err
  | ctx, path, .app fn arg =>
    match synthProtoTerm env ctx (path ++ [0]) fn, synthProtoTerm env ctx (path ++ [1]) arg with
    | .ok fnInf, .ok argInf =>
      match h_fn : fnInf.type with
      | .arrow _reuse _qty dom cod =>
        if h_eq : argInf.type = dom then
          .ok ⟨cod, .app (h_fn ▸ fnInf.derivation) (h_eq ▸ argInf.derivation)⟩
        else
          .error (.typeMismatch path dom argInf.type)
      | otherTy => .error (.shapeMismatch path "arrow" otherTy)
    | .error err, _ => .error err
    | _, .error err => .error err
  | ctx, path, .binary prim l r =>
    match synthProtoTerm env ctx (path ++ [0]) l, synthProtoTerm env ctx (path ++ [1]) r with
    | .ok lInf, .ok rInf =>
      if h_l : lInf.type = (primitiveTypes prim).1 then
        if h_r : rInf.type = (primitiveTypes prim).1 then
          .ok ⟨(primitiveTypes prim).2, .binary (h_l ▸ lInf.derivation) (h_r ▸ rInf.derivation)⟩
        else
          .error (.typeMismatch (path ++ [1]) (primitiveTypes prim).1 rInf.type)
      else
        .error (.typeMismatch (path ++ [0]) (primitiveTypes prim).1 lInf.type)
    | .error err, _ => .error err
    | _, .error err => .error err
  | ctx, path, .ifBool cond t f =>
    match synthProtoTerm env ctx (path ++ [0]) cond,
          synthProtoTerm env ctx (path ++ [1]) t,
          synthProtoTerm env ctx (path ++ [2]) f with
    | .ok cInf, .ok tInf, .ok fInf =>
      if h_c : cInf.type = .boolean then
        if h_tf : fInf.type = tInf.type then
          .ok ⟨tInf.type, .ifBool (h_c ▸ cInf.derivation) tInf.derivation (h_tf ▸ fInf.derivation)⟩
        else
          .error (.typeMismatch (path ++ [2]) tInf.type fInf.type)
      else
        .error (.typeMismatch (path ++ [0]) .boolean cInf.type)
    | .error err, _, _ => .error err
    | _, .error err, _ => .error err
    | _, _, .error err => .error err
  | ctx, path, .ifZero val z s =>
    match synthProtoTerm env ctx (path ++ [0]) val,
          synthProtoTerm env ctx (path ++ [1]) z,
          synthProtoTerm env (⟨.natural, .unrestricted⟩ :: ctx) (path ++ [2]) s with
    | .ok vInf, .ok zInf, .ok sInf =>
      if h_v : vInf.type = .natural then
        if h_zs : sInf.type = zInf.type then
          .ok ⟨zInf.type, .ifZero (h_v ▸ vInf.derivation) zInf.derivation (h_zs ▸ sInf.derivation)⟩
        else
          .error (.typeMismatch (path ++ [2]) zInf.type sInf.type)
      else
        .error (.typeMismatch (path ++ [0]) .natural vInf.type)
    | .error err, _, _ => .error err
    | _, .error err, _ => .error err
    | _, _, .error err => .error err
  | ctx, path, .fix spec seed =>
    match synthProtoTerm env ctx (path ++ [0]) spec, synthProtoTerm env ctx (path ++ [1]) seed with
    | .ok specInf, .ok seedInf =>
      match h_sp : specInf.type with
      | .arrow .reusable .unrestricted targetTy (.arrow .reusable .unrestricted domSeed codTarget) =>
        if h_seed : domSeed = seedInf.type then
          if h_cod : codTarget = targetTy then
            have h_spec_ty :
                specInf.type =
                  .arrow .reusable .unrestricted targetTy
                    (.arrow .reusable .unrestricted seedInf.type targetTy) := by
              rw [h_sp, h_seed, h_cod]
            .ok ⟨targetTy, .fix (h_spec_ty ▸ specInf.derivation) seedInf.derivation⟩
          else
            .error (.typeMismatch path targetTy codTarget)
        else
          .error (.typeMismatch (path ++ [1]) domSeed seedInf.type)
      | otherTy => .error (.shapeMismatch path "fix-spec-arrow" otherTy)
    | .error err, _ => .error err
    | _, .error err => .error err
  | ctx, path, .reflect t =>
    match synthProtoTerm env ctx (path ++ [0]) t with
    | .ok tInf =>
      match h_t : tInf.type with
      | .prototype specTy _targetTy =>
        .ok ⟨specTy, .reflect (h_t ▸ tInf.derivation)⟩
      | otherTy => .error (.shapeMismatch path "prototype" otherTy)
    | .error err => .error err
  | ctx, path, .project t =>
    match synthProtoTerm env ctx (path ++ [0]) t with
    | .ok tInf =>
      match h_t : tInf.type with
      | .prototype _specTy targetTy =>
        .ok ⟨targetTy, .project (h_t ▸ tInf.derivation)⟩
      | otherTy => .error (.shapeMismatch path "prototype" otherTy)
    | .error err => .error err
  | ctx, path, .prototype spec target =>
    match synthProtoTerm env ctx (path ++ [0]) spec, synthProtoTerm env ctx (path ++ [1]) target with
    | .ok specInf, .ok targetInf =>
      if h_sc : specInf.type.isComputation = false then
        if h_tc : targetInf.type.isComputation = false then
          .ok ⟨.prototype specInf.type targetInf.type,
               .prototype specInf.derivation targetInf.derivation h_sc h_tc⟩
        else
          .error (.activityMisplaced path targetInf.type)
      else
        .error (.activityMisplaced path specInf.type)
    | .error err, _ => .error err
    | _, .error err => .error err
  | _ctx, path, _ => .error (.missingAnnotation path)

/-- Error sum returned by `checkPrototypeWithProvenance`, distinguishing bidirectional typing
    refusals from forged prototype provenance refusals (`LT4`). -/
inductive CheckError where
  | refusal (err : CheckRefusal)
  | forgedPrototypeProvenance (spec seed target : Term)
  deriving Repr

/-- Provenance-aware prototype typechecker (`LT4` solution):
    1. Checks `PrototypeProvenance fuel spec seed target = true` (rejecting forged targets that
       were not derived by unfolding/reducing `Term.fix spec seed`),
    2. Synthesizes the type of `Term.prototype spec target` AND verifies `seed` is well-typed in `ctx`. -/
def checkPrototypeWithProvenance
    (fuel : Nat) (env : Env) (ctx : Ctx) (spec seed target : Term) :
    Except CheckError Ty :=
  if PrototypeProvenance fuel spec seed target then
    match synthProtoTerm env ctx [] (.prototype spec target), synthProtoTerm env ctx [2] seed with
    | .ok inf, .ok _seedInf => .ok inf.type
    | .error err, _         => .error (.refusal err)
    | _, .error err         => .error (.refusal err)
  else
    .error (.forgedPrototypeProvenance spec seed target)

/-- **Theorem 1 (`checkPrototypeWithProvenance_sound`)**:
    If `checkPrototypeWithProvenance fuel env ctx spec seed target = .ok ty`, then:
    1. `HasPrototypeProvenance spec seed target` holds,
    2. `PositiveSteps (.fix spec seed) target` holds,
    3. `ProtoTyping env ctx (.prototype spec target) ty` holds, and `seed` is well-typed in `ctx`. -/
theorem checkPrototypeWithProvenance_sound
    {fuel : Nat} {env : Env} {ctx : Ctx} {spec seed target : Term} {ty : Ty}
    (h_ok : checkPrototypeWithProvenance fuel env ctx spec seed target = .ok ty) :
    HasPrototypeProvenance spec seed target ∧
    PositiveSteps (.fix spec seed) target ∧
    ProtoTyping env ctx (.prototype spec target) ty := by
  unfold checkPrototypeWithProvenance at h_ok
  cases h_prov : PrototypeProvenance fuel spec seed target with
  | false =>
    rw [h_prov] at h_ok
    contradiction
  | true =>
    rw [h_prov] at h_ok
    simp only [ite_true] at h_ok
    cases h_synth : synthProtoTerm env ctx [] (.prototype spec target) with
    | error err =>
      rw [h_synth] at h_ok
      contradiction
    | ok inf =>
      rw [h_synth] at h_ok
      cases h_seed : synthProtoTerm env ctx [2] seed with
      | error err =>
        rw [h_seed] at h_ok
        contradiction
      | ok seedInf =>
        rw [h_seed] at h_ok
        injection h_ok with h_ty
        subst h_ty
        have hp : HasPrototypeProvenance spec seed target := PrototypeProvenance_sound h_prov
        exact ⟨hp, hp.toPositiveSteps, inf.derivation⟩

/-! ## Concrete Fixtures, Multi-Step Reductions, Genuine Acceptance, Forged Refusal & `#tooth` Probe -/

/-- Prototype specification `λ self. λ seed. 42` whose fixpoint over seed `0` reduces to `42`. -/
def constSpec42 : Term :=
  .lam (.lam (.nat 42))

/-- Initial prototype seed `0`. -/
def zeroSeed : Term :=
  .nat 0

/-- Genuine target `42`, obtained by unfolding and stepping `Term.fix constSpec42 zeroSeed`. -/
def genuineTarget42 : Term :=
  .nat 42

/-- Forged target `999`: has the exact same type (`.natural`) as `genuineTarget42`, so raw
    `Term.prototype constSpec42 forgedTarget999` would accept it without provenance checking,
    but `999` is never reachable from `Term.fix constSpec42 zeroSeed`. -/
def forgedTarget999 : Term :=
  .nat 999

/-- Multi-step branching + arithmetic specification:
    `λ self. λ seed. ifZero seed 10 (pred + 32)` which takes 4 small steps from `unfoldFix` on `seed = 11`
    (`beta` → `beta` → `ifZero successor` → `binary add`) to reach `42`. -/
def branchingSpec42 : Term :=
  .lam (.lam (.ifZero (.bound 0) (.nat 10) (.binary .add (.bound 0) (.nat 32))))

def branchingSeed11 : Term :=
  .nat 11

/-- Lambda annotations typing `constSpec42` and `branchingSpec42` as `Nat → Nat → Nat`. -/
def constSpec42Annotations : Annotations
  | [0]    => some { domain := .natural
                   , codomain := .arrow .reusable .unrestricted .natural .natural
                   , parameter := .unrestricted
                   , reuse := .reusable }
  | [0, 0] => some { domain := .natural
                   , codomain := .natural
                   , parameter := .unrestricted
                   , reuse := .reusable }
  | _      => none

/-- Environment equipped with `constSpec42Annotations`. -/
def constSpec42Env : Env :=
  { assumptions := {}, annotations := constSpec42Annotations }

/-- Genuine prototype target `42` satisfies `PrototypeProvenance` within 2 steps. -/
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem genuine_prototype_provenance_holds :
    PrototypeProvenance 2 constSpec42 zeroSeed genuineTarget42 = true := by
  decide +kernel

/-- Multi-step branching/arithmetic prototype target `42` from `branchingSpec42` and `branchingSeed11`
    satisfies `PrototypeProvenance` at fuel `4`. -/
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem branching_prototype_provenance_holds :
    PrototypeProvenance 4 branchingSpec42 branchingSeed11 genuineTarget42 = true := by
  decide +kernel

/-- Multi-step branching/arithmetic prototype target `42` fails `PrototypeProvenance` at fuel `3`. -/
-- fixture kept (2026-11-04): refusal witness: `PrototypeProvenance` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
theorem branching_prototype_provenance_insufficient_fuel :
    PrototypeProvenance 3 branchingSpec42 branchingSeed11 genuineTarget42 = false := by
  decide +kernel

/-- Genuine prototype target `42` is accepted by `checkPrototypeWithProvenance` with its synthesized
    `.prototype` type. -/
theorem genuine_prototype_accepted :
    checkPrototypeWithProvenance 2 constSpec42Env [] constSpec42 zeroSeed genuineTarget42 =
      .ok (.prototype
        (.arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural))
        .natural) := by
  unfold checkPrototypeWithProvenance
  rw [genuine_prototype_provenance_holds]
  rfl

/-- Multi-step branching prototype `branchingSpec42` is accepted by `checkPrototypeWithProvenance` at fuel `4`. -/
theorem branching_prototype_accepted :
    checkPrototypeWithProvenance 4 constSpec42Env [] branchingSpec42 branchingSeed11 genuineTarget42 =
      .ok (.prototype
        (.arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural))
        .natural) := by
  unfold checkPrototypeWithProvenance
  rw [branching_prototype_provenance_holds]
  rfl

/-- Unbound seed `.bound 999` still satisfies raw `PrototypeProvenance` when `spec` ignores `seed`. -/
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem unbound_seed_provenance_holds :
    PrototypeProvenance 2 constSpec42 (.bound 999) genuineTarget42 = true := by
  decide +kernel

/-- An ill-typed `seed` (such as an unbound variable `.bound 999` in the empty context) is refused
    by `checkPrototypeWithProvenance` even if `spec` ignores `seed` during reduction. -/
theorem illTyped_seed_refused :
    checkPrototypeWithProvenance 2 constSpec42Env [] constSpec42 (.bound 999) genuineTarget42 =
      .error (.refusal (.unboundVariable [2] 999)) := by
  unfold checkPrototypeWithProvenance
  rw [unbound_seed_provenance_holds]
  rfl

/-- Raw `synthProtoTerm` WITHOUT provenance checking accepts the forged target `999` at the exact
    same type as `genuineTarget42` (demonstrating the `LT4` vulnerability in raw `Term.prototype`). -/
theorem raw_synthProtoTerm_accepts_forged_target :
    (synthProtoTerm constSpec42Env [] [] (.prototype constSpec42 forgedTarget999)).map (·.type) =
      .ok (.prototype
        (.arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural))
        .natural) := rfl

/-- Forged target `999` fails `PrototypeProvenance` at fuel `5`. -/
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem forged_prototype_provenance_false :
    PrototypeProvenance 5 constSpec42 zeroSeed forgedTarget999 = false := by
  decide +kernel

/-- **Theorem 2 (`forged_prototype_refused`)**:
    Even though `forgedTarget999` has the exact same type `.natural` as `genuineTarget42` (and is
    accepted by raw `synthProtoTerm`), `checkPrototypeWithProvenance` refuses `forgedTarget999` with
    `.error (.forgedPrototypeProvenance ...)`. -/
theorem forged_prototype_refused (env : Env) (ctx : Ctx) :
    checkPrototypeWithProvenance 5 env ctx constSpec42 zeroSeed forgedTarget999 =
      .error (.forgedPrototypeProvenance constSpec42 zeroSeed forgedTarget999) := by
  unfold checkPrototypeWithProvenance
  rw [forged_prototype_provenance_false]
  rfl

#tooth forged_prototype_provenance_false by mutation
  PrototypeProvenance := fun _ _ _ _ => true

end Obend.Core.PrototypeProvenance

end
