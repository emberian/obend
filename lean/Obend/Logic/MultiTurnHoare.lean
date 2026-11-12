module
/-
# Obend.Logic.MultiTurnHoare — Multi-Turn Interaction-Tree `SafeWP` & Actor Loop Invariants

Upgrades `Obend.Logic.Turn` from single-shot ground turns to a compositional **Multi-Turn
Interaction Program Logic** over `Core4` (`Term`, `Step`, `Yields`, `Obend.Equiv.Interaction`):

1. **Protocols & Multi-Turn Weakest Preconditions (`ProtocolSpec`, `ExpectedPlan`, `SafeWPGen`, `SafeWP`, `WP`)**:
   - `ProtocolSpec := Term → Term → Prop` relates each yielded `plan` to admissible environment
     responses `resp`, paired with `ExpectedPlan proto plan := ∃ resp, proto plan resp` so yielding
     an uninhabited/illegal plan can never be vacuously safe.
   - `SafeWPGen` and `SafeWP` provide `wp_val`, `wp_eval`, `wp_step`, `wp_steps`, and demonic
     environment quantification `wp_perform`, plus turn-bounded `WP proto fuel t Φ` (`wp_implies_safeWP`).
   - Deterministic `Core4` inversion laws (`wp_value_inv`, `wp_step_inv`, `wp_steps_inv`,
     `wp_yields_inv`) exploit `value_no_step`, `yields_no_step`, `step_det`, and `yields_deterministic`.

2. **Modular Evaluation-Context Framing (`CtxWF`, `plugContext`, `wp_bind_ctx`)**:
   - `FrameWF` / `CtxWF` capture the exact value-left invariant of `SourceFrame.binaryRight`, proved
     automatically for every `Yields` context (`yields_ctxWF`).
   - `wp_bind_ctx` verifies a sub-activity `e` inside any `Core4` evaluation context `ctx` and
     chains its postcondition into `plugContext ctx v`, with specialized rules `wp_bind_case`,
     `wp_bind_ifBool`, `wp_bind_ifZero`, `wp_bind_app`, and strict `Nat` sequencing `wp_seqNat`.

3. **Open-Recursive Actor Loop Invariants (`actorLoopFix`, `runActorFix`, `wp_loop_invariant`)**:
   - Builds an open-recursive `Core4` `.fix` server loop `actorLoopFix` and proves `wp_loop_invariant`:
     if `Inv s → SafeWP proto (.app actorStep (.nat s)) (fun v => ∃ s', v = .nat s' ∧ Inv s')`,
     then `n` sequential turns preserve `Inv` across arbitrary demonic environment responses!
   - Directly lifts `Obend.Logic.Turn.counterBump` to `n` arbitrary demonic turns (`counterBump_multiTurn_safeWP`).

4. **Adequacy Against `Obend.Equiv.Interaction` (`safeWP_adequacy`) & 2nd-Refusal-Turn Separation**:
   - `safeWP_adequacy`: if `SafeWP proto t Φ` holds and every `(plan, resp)` in `trace` satisfies
     `proto plan resp`, then `Obend.Equiv.Interaction t trace v` guarantees `Φ v` and
     `ExpectedPlan proto plan` at every turn along `trace`.
   - Verifies `guardedRetryStep` (`streak ≤ 1`) for all $N$ turns while constructively refuting
     `recklessRetryStep` on the **2nd refusal turn** (`recklessRetry_one_turn_safe` vs
     `recklessRetry_two_turns_refuted`).
-/

public import Obend.Logic.Turn

public section

namespace Obend.Equiv

/-- Alias exposing `Core4`'s multi-turn `Interaction` judgment in `Obend.Equiv`. -/
abbrev Interaction := Obend.Core.Term.Interaction

end Obend.Equiv

namespace Obend.Logic

open Obend.Core.Term
open Obend.Core.Data (Data)

set_option autoImplicit false

/-! ## 1. Protocol Specifications, Evaluation Contexts, and `SafeWP` -/

/-- Relational environment contract `proto plan resp`: holds when `resp` is a lawful environment
    reply to yielded plan `plan`. -/
abbrev ProtocolSpec : Type := Term → Term → Prop

/-- Canonical plan admissibility induced by `proto`: at least one lawful response exists, preventing
    demonic quantification over responses from becoming vacuous on illegal plans. -/
@[expose] def ExpectedPlan (proto : ProtocolSpec) (plan : Term) : Prop :=
  ∃ resp : Term, proto plan resp

/-- Explicit alias for `Obend.Core.Term.plug` highlighting innermost-first evaluation context plugging. -/
abbrev plugContext (ctx : List SourceFrame) (hole : Term) : Term :=
  plug ctx hole

@[simp] theorem plugContext_nil (hole : Term) : plugContext [] hole = hole := rfl

@[simp] theorem plugContext_cons (f : SourceFrame) (ctx : List SourceFrame) (hole : Term) :
    plugContext (f :: ctx) hole = plugContext ctx (f.plug hole) := rfl

theorem plugContext_append (c₁ c₂ : List SourceFrame) (hole : Term) :
    plugContext (c₁ ++ c₂) hole = plugContext c₂ (plugContext c₁ hole) := by
  simp only [plugContext, plug, List.foldl_append]

/-- Well-formedness of a single `Core4` `SourceFrame`: `.binaryRight op left` requires `Value left`
    so `Step.binaryRight` and `Yields.binaryRight` apply uniformly. -/
@[expose] def FrameWF : SourceFrame → Prop
  | .binaryRight _ left => Value left
  | _ => True

/-- Well-formedness of an innermost-first evaluation context `List SourceFrame`. -/
@[expose] def CtxWF (ctx : List SourceFrame) : Prop :=
  ∀ f ∈ ctx, FrameWF f

@[simp] theorem ctxWF_nil : CtxWF [] := by
  intro _ h; cases h

theorem ctxWF_singleton {f : SourceFrame} (hf : FrameWF f) : CtxWF [f] := by
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  exact hf

theorem ctxWF_append {c₁ c₂ : List SourceFrame} (h₁ : CtxWF c₁) (h₂ : CtxWF c₂) :
    CtxWF (c₁ ++ c₂) := by
  intro f hf
  rcases List.mem_append.1 hf with hm₁ | hm₂
  · exact h₁ f hm₁
  · exact h₂ f hm₂

/-- Every context extracted from `Yields` is automatically `CtxWF`. -/
theorem yields_ctxWF {t plan : Term} {ctx : List SourceFrame} (hy : Yields t plan ctx) :
    CtxWF ctx := by
  induction hy with
  | perform _ => exact ctxWF_nil
  | application a _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | field n _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | extend fs _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | binaryLeft op r _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | binaryRight op hv _ ih => exact ctxWF_append ih (ctxWF_singleton hv)
  | condition z s _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | case arms _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | ifBool wt wf _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | reflect _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | metadata _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | project _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)
  | split names fn _ ih => exact ctxWF_append ih (ctxWF_singleton trivial)

/-- Generalized multi-turn weakest precondition parameterized by both `proto : ProtocolSpec`
    and explicit plan obligation `expectedPlan : Term → Prop`. -/
inductive SafeWPGen (proto : ProtocolSpec) (expectedPlan : Term → Prop) :
    Term → (Term → Prop) → Prop where
  | val {v : Term} {Φ : Term → Prop} :
      Value v → Φ v → SafeWPGen proto expectedPlan v Φ
  | step {t t' : Term} {Φ : Term → Prop} :
      Step t t' → SafeWPGen proto expectedPlan t' Φ → SafeWPGen proto expectedPlan t Φ
  | perform {t plan : Term} {ctx : List SourceFrame} {Φ : Term → Prop} :
      Yields t plan ctx →
      expectedPlan plan →
      (∀ resp : Term, proto plan resp → SafeWPGen proto expectedPlan (plugContext ctx resp) Φ) →
      SafeWPGen proto expectedPlan t Φ

/-- Canonical multi-turn weakest precondition `SafeWP proto t Φ` with `ExpectedPlan proto`. -/
abbrev SafeWP (proto : ProtocolSpec) (t : Term) (Φ : Term → Prop) : Prop :=
  SafeWPGen proto (ExpectedPlan proto) t Φ

/-- Turn/step-indexed bounded weakest precondition `WP proto fuel t Φ`. -/
inductive WP (proto : ProtocolSpec) : Nat → Term → (Term → Prop) → Prop where
  | val {fuel : Nat} {v : Term} {Φ : Term → Prop} :
      Value v → Φ v → WP proto fuel v Φ
  | step {fuel : Nat} {t t' : Term} {Φ : Term → Prop} :
      Step t t' → WP proto fuel t' Φ → WP proto (fuel + 1) t Φ
  | perform {fuel : Nat} {t plan : Term} {ctx : List SourceFrame} {Φ : Term → Prop} :
      Yields t plan ctx →
      ExpectedPlan proto plan →
      (∀ resp : Term, proto plan resp → WP proto fuel (plugContext ctx resp) Φ) →
      WP proto (fuel + 1) t Φ

theorem wp_implies_safeWP {proto : ProtocolSpec} {fuel : Nat} {t : Term} {Φ : Term → Prop}
    (h : WP proto fuel t Φ) : SafeWP proto t Φ := by
  induction h with
  | val hv hΦ => exact .val hv hΦ
  | step hst _ ih => exact .step hst ih
  | perform hy hexp _ ih => exact .perform hy hexp ih

/-! ## 2. Structural Rules (`wp_val`, `wp_eval`, `wp_step`, `wp_perform`, `wp_mono`) -/

theorem wp_val {proto : ProtocolSpec} {v : Term} {Φ : Term → Prop}
    (hv : Value v) (hΦ : Φ v) : SafeWP proto v Φ :=
  .val hv hΦ

theorem wp_step {proto : ProtocolSpec} {t t' : Term} {Φ : Term → Prop}
    (hst : Step t t') (hwp : SafeWP proto t' Φ) : SafeWP proto t Φ :=
  .step hst hwp

theorem wp_stepsGen {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t t' : Term} {Φ : Term → Prop}
    (hsteps : Steps t t') (hwp : SafeWPGen proto expectedPlan t' Φ) :
    SafeWPGen proto expectedPlan t Φ := by
  induction hsteps with
  | refl => exact hwp
  | next hst _ ih => exact .step hst (ih hwp)

theorem wp_steps {proto : ProtocolSpec} {t t' : Term} {Φ : Term → Prop}
    (hsteps : Steps t t') (hwp : SafeWP proto t' Φ) : SafeWP proto t Φ :=
  wp_stepsGen hsteps hwp

/-- **`wp_eval`**: any pure terminating `Core4` evaluation `Evaluates t v` with `Φ v` satisfies `SafeWP`. -/
theorem wp_eval {proto : ProtocolSpec} {t v : Term} {Φ : Term → Prop}
    (hev : Evaluates t v) (hΦ : Φ v) : SafeWP proto t Φ :=
  wp_steps hev.1 (.val hev.2 hΦ)

/-- **`wp_perform` (Demonic Environment Choice)**: at a `Yields` redex, verifying `ExpectedPlan`
    and continuation safety across *all* `proto`-admissible responses establishes `SafeWP`. -/
theorem wp_perform {proto : ProtocolSpec} {t plan : Term} {ctx : List SourceFrame} {Φ : Term → Prop}
    (hy : Yields t plan ctx)
    (hexp : ExpectedPlan proto plan)
    (hcont : ∀ resp : Term, proto plan resp → SafeWP proto (plugContext ctx resp) Φ) :
    SafeWP proto t Φ :=
  .perform hy hexp hcont

/-- Executable `step?`-driven rule used by `by obend_wp`. -/
theorem wp_step_of_step? {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t t' : Term} {Φ : Term → Prop}
    (hs : Obend.Law.step? t = some t')
    (hwp : SafeWPGen proto expectedPlan t' Φ) :
    SafeWPGen proto expectedPlan t Φ :=
  .step (Obend.Law.step?_sound t hs) hwp

/-- Executable `yields?`-driven rule used by `by obend_wp`. -/
theorem wp_perform_of_yields? {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t plan : Term} {ctx : List SourceFrame} {Φ : Term → Prop}
    (hy : yields? t = some (plan, ctx))
    (hexp : expectedPlan plan)
    (hcont : ∀ resp : Term, proto plan resp → SafeWPGen proto expectedPlan (plugContext ctx resp) Φ) :
    SafeWPGen proto expectedPlan t Φ :=
  .perform (yields?_sound t hy) hexp hcont

/-- Consequence / postcondition weakening (`wp_mono`). -/
theorem wp_monoGen {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t : Term} {Ψ Φ : Term → Prop}
    (hwp : SafeWPGen proto expectedPlan t Ψ)
    (himp : ∀ v : Term, Value v → Ψ v → Φ v) :
    SafeWPGen proto expectedPlan t Φ := by
  induction hwp with
  | val hv hΨ => exact .val hv (himp _ hv hΨ)
  | step hst _ ih => exact .step hst (ih himp)
  | perform hy hexp _ ih => exact .perform hy hexp (fun resp hp => ih resp hp himp)

theorem wp_mono {proto : ProtocolSpec} {t : Term} {Ψ Φ : Term → Prop}
    (hwp : SafeWP proto t Ψ)
    (himp : ∀ v : Term, Value v → Ψ v → Φ v) :
    SafeWP proto t Φ :=
  wp_monoGen hwp himp

/-! ## 3. Modular Evaluation-Context Framing (`wp_bind_ctx`) -/

theorem frame_plug_step {f : SourceFrame} {e e' : Term}
    (hwf : FrameWF f) (hst : Step e e') : Step (f.plug e) (f.plug e') := by
  cases f with
  | application arg => exact .application arg hst
  | field name => exact .target name hst
  | extend fs => exact .extendTarget fs hst
  | binaryLeft op r => exact .binaryLeft op r hst
  | binaryRight op l => exact .binaryRight op l hwf hst
  | condition z s => exact .condition z s hst
  | case arms => exact .caseTarget arms hst
  | ifBool wt wf => exact .ifCondition wt wf hst
  | reflect => exact .reflectStep hst
  | metadata => exact .metadataStep hst
  | project => exact .projectStep hst
  | split names fn => exact .splitTarget names fn hst

theorem plug_step {ctx : List SourceFrame} {e e' : Term}
    (hctx : CtxWF ctx) (hst : Step e e') :
    Step (plugContext ctx e) (plugContext ctx e') := by
  induction ctx generalizing e e' with
  | nil => exact hst
  | cons f rest ih =>
    have hf : FrameWF f := hctx f List.mem_cons_self
    have hrest : CtxWF rest := fun g hg => hctx g (List.mem_cons_of_mem f hg)
    exact ih hrest (frame_plug_step hf hst)

theorem frame_plug_yields {f : SourceFrame} {e plan : Term} {innerCtx : List SourceFrame}
    (hwf : FrameWF f) (hy : Yields e plan innerCtx) :
    Yields (f.plug e) plan (innerCtx ++ [f]) := by
  cases f with
  | application arg => exact .application arg hy
  | field name => exact .field name hy
  | extend fs => exact .extend fs hy
  | binaryLeft op r => exact .binaryLeft op r hy
  | binaryRight op l => exact .binaryRight op hwf hy
  | condition z s => exact .condition z s hy
  | case arms => exact .case arms hy
  | ifBool wt wf => exact .ifBool wt wf hy
  | reflect => exact .reflect hy
  | metadata => exact .metadata hy
  | project => exact .project hy
  | split names fn => exact .split names fn hy

theorem plug_yields {ctx innerCtx : List SourceFrame} {e plan : Term}
    (hctx : CtxWF ctx) (hy : Yields e plan innerCtx) :
    Yields (plugContext ctx e) plan (innerCtx ++ ctx) := by
  induction ctx generalizing e innerCtx with
  | nil =>
    simp only [plugContext_nil, List.append_nil]
    exact hy
  | cons f rest ih =>
    have hf : FrameWF f := hctx f List.mem_cons_self
    have hrest : CtxWF rest := fun g hg => hctx g (List.mem_cons_of_mem f hg)
    have hy1 : Yields (f.plug e) plan (innerCtx ++ [f]) := frame_plug_yields hf hy
    have hy2 := ih hrest hy1
    simpa only [plugContext_cons, List.append_assoc, List.singleton_append] using hy2

/-- **`wp_bind_ctx` (Modular Context Framing)**: verify sub-computation `e` with postcondition `Ψ`,
    then verify `plugContext ctx v` for every resulting value `v` satisfying `Ψ v`. -/
theorem wp_bind_ctxGen {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {ctx : List SourceFrame} {e : Term} {Ψ Φ : Term → Prop}
    (hctx : CtxWF ctx)
    (he : SafeWPGen proto expectedPlan e Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWPGen proto expectedPlan (plugContext ctx v) Φ) :
    SafeWPGen proto expectedPlan (plugContext ctx e) Φ := by
  induction he with
  | val hv hΨ => exact hcont _ hv hΨ
  | step hst _ ih => exact .step (plug_step hctx hst) (ih hcont)
  | perform hy hexp _ ih =>
    refine .perform (plug_yields hctx hy) hexp (fun resp hproto => ?_)
    rw [plugContext_append]
    exact ih resp hproto hcont

theorem wp_bind_ctx {proto : ProtocolSpec}
    {ctx : List SourceFrame} {e : Term} {Ψ Φ : Term → Prop}
    (hctx : CtxWF ctx)
    (he : SafeWP proto e Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWP proto (plugContext ctx v) Φ) :
    SafeWP proto (plugContext ctx e) Φ :=
  wp_bind_ctxGen hctx he hcont

theorem wp_bind_case {proto : ProtocolSpec}
    {e : Term} {arms : List (String × Term)} {Ψ Φ : Term → Prop}
    (he : SafeWP proto e Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWP proto (.case v arms) Φ) :
    SafeWP proto (.case e arms) Φ :=
  wp_bind_ctx (ctx := [.case arms]) (ctxWF_singleton trivial) he hcont

theorem wp_bind_ifBool {proto : ProtocolSpec}
    {c wt wf : Term} {Ψ Φ : Term → Prop}
    (hc : SafeWP proto c Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWP proto (.ifBool v wt wf) Φ) :
    SafeWP proto (.ifBool c wt wf) Φ :=
  wp_bind_ctx (ctx := [.ifBool wt wf]) (ctxWF_singleton trivial) hc hcont

theorem wp_bind_ifZero {proto : ProtocolSpec}
    {n z s : Term} {Ψ Φ : Term → Prop}
    (hn : SafeWP proto n Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWP proto (.ifZero v z s) Φ) :
    SafeWP proto (.ifZero n z s) Φ :=
  wp_bind_ctx (ctx := [.condition z s]) (ctxWF_singleton trivial) hn hcont

theorem wp_bind_app {proto : ProtocolSpec}
    {f a : Term} {Ψ Φ : Term → Prop}
    (hf : SafeWP proto f Ψ)
    (hcont : ∀ v : Term, Value v → Ψ v → SafeWP proto (.app v a) Φ) :
    SafeWP proto (.app f a) Φ :=
  wp_bind_ctx (ctx := [.application a]) (ctxWF_singleton trivial) hf hcont

/-- Strict `Core4` `Nat`-activity binder: evaluates `e` in evaluation position via `(e + 1)` inside
    `ifZero`, binding de Bruijn `.bound 0` in `body` to the exact resulting `.nat m`! -/
@[expose] def seqNat (e body : Term) : Term :=
  .ifZero (.binary .add e (.nat 1)) (.done (.nat 0)) body

theorem wp_seqNat {proto : ProtocolSpec} {e body : Term}
    {Ψ : Nat → Prop} {Φ : Term → Prop}
    (he : SafeWP proto e (fun v => ∃ m : Nat, v = .nat m ∧ Ψ m))
    (hcont : ∀ m : Nat, Ψ m → SafeWP proto (instantiate body (.nat m)) Φ) :
    SafeWP proto (seqNat e body) Φ := by
  have hctx : CtxWF [.binaryLeft .add (.nat 1), .condition (.done (.nat 0)) body] := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> trivial
  refine wp_bind_ctx (ctx := [.binaryLeft .add (.nat 1), .condition (.done (.nat 0)) body]) hctx he ?_
  rintro v _ ⟨m, rfl, hm⟩
  change SafeWP proto (.ifZero (.binary .add (.nat m) (.nat 1)) (.done (.nat 0)) body) Φ
  refine wp_step (.condition _ _ (.primitive .add (.nat m) (.nat 1) (.nat (m + 1)) (.natural m) (.natural 1) rfl)) ?_
  exact wp_step (.successor m _ _) (hcont m hm)

/-! ## 4. Deterministic Operational Inversion & Adequacy (`safeWP_adequacy`) -/

theorem wp_value_inv {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {v : Term} {Φ : Term → Prop}
    (hv : Value v) (hwp : SafeWPGen proto expectedPlan v Φ) : Φ v := by
  cases hwp with
  | val _ hΦ => exact hΦ
  | step hst _ => exact False.elim (Obend.Core.Term.value_no_step hv hst)
  | perform hy _ _ => exact False.elim (yields_not_value hy hv)

theorem wp_step_inv {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t t' : Term} {Φ : Term → Prop}
    (hst : Step t t') (hwp : SafeWPGen proto expectedPlan t Φ) :
    SafeWPGen proto expectedPlan t' Φ := by
  cases hwp with
  | val hv _ => exact False.elim (Obend.Core.Term.value_no_step hv hst)
  | step hst' hnext =>
    have heq := step_det hst hst'
    subst heq
    exact hnext
  | perform hy _ _ => exact False.elim (yields_no_step hy _ hst)

theorem wp_steps_inv {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t u : Term} {Φ : Term → Prop}
    (hsteps : Steps t u) (hwp : SafeWPGen proto expectedPlan t Φ) :
    SafeWPGen proto expectedPlan u Φ := by
  induction hsteps with
  | refl => exact hwp
  | next hst _ ih => exact ih (wp_step_inv hst hwp)

theorem wp_yields_inv {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {u plan : Term} {ctx : List SourceFrame} {Φ : Term → Prop}
    (hy : Yields u plan ctx) (hwp : SafeWPGen proto expectedPlan u Φ) :
    expectedPlan plan ∧
      ∀ resp : Term, proto plan resp → SafeWPGen proto expectedPlan (plugContext ctx resp) Φ := by
  cases hwp with
  | val hv _ => exact False.elim (yields_not_value hy hv)
  | step hst _ => exact False.elim (yields_no_step hy _ hst)
  | perform hy' hexp hcont =>
    obtain ⟨hp, hc⟩ := yields_deterministic hy hy'
    subst hp; subst hc
    exact ⟨hexp, hcont⟩

/-- Every `(plan, resp)` pair in `trace` obeys `proto`. -/
@[expose] def ValidTrace (proto : ProtocolSpec) (trace : List (Term × Term)) : Prop :=
  ∀ entry ∈ trace, proto entry.1 entry.2

/-- Every yielded `plan` recorded in `trace` satisfies `expectedPlan`. -/
@[expose] def AllPlansExpected (expectedPlan : Term → Prop) (trace : List (Term × Term)) : Prop :=
  ∀ entry ∈ trace, expectedPlan entry.1

/-- **`safeWPGen_adequacy`**: general adequacy of `SafeWPGen` against `Obend.Equiv.Interaction`. -/
theorem safeWPGen_adequacy {proto : ProtocolSpec} {expectedPlan : Term → Prop}
    {t v : Term} {trace : List (Term × Term)} {Φ : Term → Prop}
    (hwp : SafeWPGen proto expectedPlan t Φ)
    (htrace : ValidTrace proto trace)
    (hint : Obend.Equiv.Interaction t trace v) :
    Φ v ∧ AllPlansExpected expectedPlan trace := by
  induction hint with
  | finish hev =>
    have hwpVal := wp_steps_inv hev.1 hwp
    refine ⟨wp_value_inv hev.2 hwpVal, ?_⟩
    intro _ hmem; cases hmem
  | turn hsteps hyields _ ih =>
    have hwpYield := wp_steps_inv hsteps hwp
    obtain ⟨hexp, hcont⟩ := wp_yields_inv hyields hwpYield
    have hhead : proto _ _ := htrace _ List.mem_cons_self
    have htail : ValidTrace proto _ := fun e he => htrace e (List.mem_cons_of_mem _ he)
    obtain ⟨hΦ, hrestPlans⟩ := ih (hcont _ hhead) htail
    refine ⟨hΦ, ?_⟩
    intro entry hentry
    rcases List.mem_cons.1 hentry with rfl | hmem
    · exact hexp
    · exact hrestPlans entry hmem

/-- **`safeWP_adequacy`**: Adequacy & Soundness of `SafeWP` against `Obend.Equiv.Interaction`. -/
theorem safeWP_adequacy {proto : ProtocolSpec}
    {t v : Term} {trace : List (Term × Term)} {Φ : Term → Prop}
    (hwp : SafeWP proto t Φ)
    (htrace : ValidTrace proto trace)
    (hint : Obend.Equiv.Interaction t trace v) :
    Φ v ∧ AllPlansExpected (ExpectedPlan proto) trace :=
  safeWPGen_adequacy hwp htrace hint

/-- Contrapositive refutation principle: exhibiting one `proto`-valid `Interaction` trace whose
    result violates `Φ` refutes `SafeWP proto t Φ`. -/
theorem not_safeWP_of_bad_interaction {proto : ProtocolSpec}
    {t v : Term} {trace : List (Term × Term)} {Φ : Term → Prop}
    (htrace : ValidTrace proto trace)
    (hint : Obend.Equiv.Interaction t trace v)
    (hbad : ¬ Φ v) :
    ¬ SafeWP proto t Φ :=
  fun hwp => hbad (safeWP_adequacy hwp htrace hint).1

/-! ## 5. $N$-Turn Open-Recursive `Core4` `.fix` Actor Loop (`wp_loop_invariant`) -/

/-- Substitution-closed `Core4` term (`∀ σ, t.substitute σ = t`). Every `Closed t` satisfies
    `SubstClosed t` (`substClosed_of_closed`), and concrete terms reduce directly via `simp`. -/
abbrev SubstClosed (t : Term) : Prop :=
  ∀ σ : Nat → Term, Term.substitute σ t = t

theorem substClosed_of_closed {t : Term} (hc : Closed t) : SubstClosed t :=
  closed_subst hc

theorem substClosed_rename {t : Term} (hc : SubstClosed t) (f : Nat → Nat) : t.rename f = t := by
  have h := Obend.Core.TermTraverse.substitute_rename t (fun i => .bound i) f
  rw [hc (fun i => .bound i)] at h
  have hrhs : (fun i => (Term.bound i).rename f) = (fun i => Term.bound (f i)) := by
    funext i
    simp [Term.rename]
  rw [hrhs, hc (fun i => .bound (f i))] at h
  exact h

private theorem steps_append {a b c : Term} (h₁ : Steps a b) (h₂ : Steps b c) : Steps a c := by
  induction h₁ with
  | refl => exact h₂
  | next hs _ ih => exact .next hs (ih h₂)

/-- Open-recursive `Core4` `.fix` specification executing closed `actorStep` for `n` sequential turns:
    ```
    fix (λ self super n s.
      ifZero n (done s)
        (k ↦ seqNat (actorStep s) (self k (bound 0))))
      {}
    ``` -/
@[expose] def actorLoopSpec (actorStep : Term) : Term :=
  .lam (.lam (.lam (.lam
    (.ifZero (.bound 1)
      (.done (.bound 0))
      (seqNat (.app actorStep (.bound 1))
        (.app (.app (.bound 5) (.bound 1)) (.bound 0)))))))

/-- Open-recursive `Core4` `.fix` knot for an $N$-turn server/actor over `actorStep`. -/
@[expose] def actorLoopFix (actorStep : Term) : Term :=
  .fix (actorLoopSpec actorStep) (.record [])

/-- Applied $N$-turn open-recursive `Core4` actor run `actorLoopFix actorStep (.nat n) (.nat s)`. -/
@[expose] def runActorFix (actorStep : Term) (n : Nat) (s : Nat) : Term :=
  .app (.app (actorLoopFix actorStep) (.nat n)) (.nat s)

theorem substClosed_actorLoopFix {actorStep : Term} (hc : SubstClosed actorStep) :
    SubstClosed (actorLoopFix actorStep) := by
  intro σ
  simp [actorLoopFix, actorLoopSpec, seqNat, Term.substitute, liftSubstitution, Term.rename, hc]

set_option linter.unusedSimpArgs false in
theorem runActorFix_zero_steps {actorStep : Term} (s : Nat)
    (hStepClosed : SubstClosed actorStep) :
    Steps (runActorFix actorStep 0 s) (.nat s) := by
  have hLoopClosed : SubstClosed (actorLoopFix actorStep) := substClosed_actorLoopFix hStepClosed
  refine .next (.application (.nat s) (.application (.nat 0) (.fix _ _))) ?_
  change Steps (.app (.app (.app (.app (actorLoopSpec actorStep) (actorLoopFix actorStep)) (.record [])) (.nat 0)) (.nat s)) (.nat s)
  unfold actorLoopSpec
  refine .next (.application (.nat s) (.application (.nat 0) (.application (.record []) (.beta _ _)))) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, seqNat, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.application (.nat s) (.application (.nat 0) (.beta _ _))) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.application (.nat s) (.beta _ _)) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.beta _ _) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.zero _ _) ?_
  exact .next (.done _) (.refl _)

set_option linter.unusedSimpArgs false in
theorem runActorFix_succ_steps {actorStep : Term} (k s : Nat)
    (hStepClosed : SubstClosed actorStep) :
    Steps (runActorFix actorStep (k + 1) s)
      (seqNat (.app actorStep (.nat s))
        (.app (.app (actorLoopFix actorStep) (.nat k)) (.bound 0))) := by
  have hLoopClosed : SubstClosed (actorLoopFix actorStep) := substClosed_actorLoopFix hStepClosed
  refine .next (.application (.nat s) (.application (.nat (k + 1)) (.fix _ _))) ?_
  change Steps (.app (.app (.app (.app (actorLoopSpec actorStep) (actorLoopFix actorStep)) (.record [])) (.nat (k + 1))) (.nat s)) _
  unfold actorLoopSpec
  refine .next (.application (.nat s) (.application (.nat (k + 1)) (.application (.record []) (.beta _ _)))) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, seqNat, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.application (.nat s) (.application (.nat (k + 1)) (.beta _ _))) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.application (.nat s) (.beta _ _)) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.beta _ _) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  refine .next (.successor k _ _) ?_
  simp (config := { failIfUnchanged := false }) [instantiate, seqNat, Term.substitute,
    liftSubstitution, Term.rename, liftRename,
    hStepClosed, substClosed_rename hStepClosed, hLoopClosed, substClosed_rename hLoopClosed]
  exact .refl _

/-- **`wp_loop_invariant` ($N$-Turn Open-Recursive `Core4` `.fix` Actor Loop Rule)**:
    If one turn `.app actorStep (.nat s)` preserves `Inv` across all demonic environment responses,
    then `n` sequential turns of the open-recursive `Core4` `.fix` loop `runActorFix actorStep n s₀`
    preserve `Inv` for every `n : Nat`! -/
theorem wp_loop_invariant {proto : ProtocolSpec}
    {actorStep : Term} {Inv : Nat → Prop}
    (hStepClosed : SubstClosed actorStep)
    (hTurn : ∀ s : Nat, Inv s →
      SafeWP proto (.app actorStep (.nat s)) (fun v => ∃ s' : Nat, v = .nat s' ∧ Inv s'))
    (n : Nat) {s₀ : Nat} (hInit : Inv s₀) :
    SafeWP proto (runActorFix actorStep n s₀) (fun v => ∃ s_fin : Nat, v = .nat s_fin ∧ Inv s_fin) := by
  induction n generalizing s₀ with
  | zero =>
    exact wp_steps (runActorFix_zero_steps s₀ hStepClosed)
      (wp_val (.natural s₀) ⟨s₀, rfl, hInit⟩)
  | succ k ih =>
    refine wp_steps (runActorFix_succ_steps k s₀ hStepClosed) ?_
    refine wp_seqNat (hTurn s₀ hInit) (fun s₁ hInv₁ => ?_)
    have hLoopClosed : SubstClosed (actorLoopFix actorStep) := substClosed_actorLoopFix hStepClosed
    have hInst : instantiate (.app (.app (actorLoopFix actorStep) (.nat k)) (.bound 0)) (.nat s₁) =
        runActorFix actorStep k s₁ := by
      simp [instantiate, runActorFix, Term.substitute, hLoopClosed]
    rw [hInst]
    exact ih hInv₁

/-! ## 6. Multi-Turn `Counter.obend`, Guarded Retry Actor & 2nd-Refusal-Turn Separation -/

/-- Demonic protocol for `Obend.Logic.Turn.counterBump`: any write plan may be answered by
    `writtenResponse` or `refusedResponse`. -/
@[expose] def counterProto : ProtocolSpec := fun plan resp =>
  (∃ c : Nat, plan = counterBumpPlan c) ∧
    (resp = writtenResponse.term ∨ resp = refusedResponse.term)

theorem counterBump_substClosed : SubstClosed counterBump := by
  intro σ
  simp [counterBump, Term.substitute, liftSubstitution, Term.rename]

/-- Single-turn `SafeWP` for `Turn.counterBump` preserving monotonicity `c₀ ≤ s'`. -/
theorem counterBump_turn_safeWP (c₀ s : Nat) (hle : c₀ ≤ s) :
    SafeWP counterProto (.app counterBump (.nat s)) (fun v => ∃ s' : Nat, v = .nat s' ∧ c₀ ≤ s') := by
  refine wp_step (.beta _ (.nat s)) ?_
  rw [counterBump_beta s]
  have hexp : ExpectedPlan counterProto (counterBumpPlan s) :=
    ⟨writtenResponse.term, ⟨s, rfl⟩, Or.inl rfl⟩
  refine wp_perform (.case _ (.perform (counterBumpPlan s))) hexp ?_
  intro resp ⟨_, hresp⟩
  rcases hresp with rfl | rfl
  · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, writtenResponse, Data.term]
    refine wp_step (.caseInject "written" (.record []) _ _ rfl) ?_
    simp [instantiate, Term.substitute]
    refine wp_step (.done _) ?_
    refine wp_step (.primitive .add (.nat s) (.nat 1) (.nat (s + 1)) (.natural s) (.natural 1) rfl) ?_
    exact wp_val (.natural (s + 1)) ⟨s + 1, rfl, by omega⟩
  · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, refusedResponse, Data.term]
    refine wp_step (.caseInject "refused" (.record []) _ _ rfl) ?_
    simp [instantiate, Term.substitute]
    exact wp_step (.done _) (wp_val (.natural s) ⟨s, rfl, hle⟩)

/-- $N$-turn monotonicity of `Turn.counterBump` across arbitrary demonic write/refusal sequences! -/
theorem counterBump_multiTurn_safeWP (n c₀ : Nat) :
    SafeWP counterProto (runActorFix counterBump n c₀) (fun v => ∃ c_fin : Nat, v = .nat c_fin ∧ c₀ ≤ c_fin) :=
  wp_loop_invariant counterBump_substClosed (counterBump_turn_safeWP c₀) n (Nat.le_refl c₀)

/-- Environment protocol for a write-or-backoff retry channel. -/
@[expose] def retryProto : ProtocolSpec := fun plan resp =>
  (plan = .label "propose" ∧ (resp = writtenResponse.term ∨ resp = refusedResponse.term)) ∨
  (plan = .label "cooldown" ∧ resp = .inject "ack" (.record []))

theorem retryProto_propose_expected : ExpectedPlan retryProto (.label "propose") :=
  ⟨writtenResponse.term, Or.inl ⟨rfl, Or.inl rfl⟩⟩

theorem retryProto_cooldown_expected : ExpectedPlan retryProto (.label "cooldown") :=
  ⟨.inject "ack" (.record []), Or.inr ⟨rfl, rfl⟩⟩

/-- `Core4` expression resetting the streak on cooldown (`streak * 0 = 0`).
    Mutating `0` to `1` or `.add streak 1` breaks the invariant on the 2nd refusal turn! -/
@[expose] def nextCooldownStreak (streakTerm : Term) : Term :=
  .binary .multiply streakTerm (.nat 0)

/-- Guarded backoff actor step (`λ streak. ifBool (streak < 1) proposeBranch cooldownBranch`). -/
@[expose] def guardedRetryStep : Term :=
  .lam
    (.ifBool (.binary .less (.bound 0) (.nat 1))
      (.case (.perform (.label "propose"))
        [ ("written", .done (.nat 0)),
          ("refused", .done (.binary .add (.bound 1) (.nat 1))) ])
      (.case (.perform (.label "cooldown"))
        [ ("ack", .done (nextCooldownStreak (.bound 1))) ]))

/-- Reckless actor step that omits cooldown and always increments `streak + 1` on `"refused"`. -/
@[expose] def recklessRetryStep : Term :=
  .lam
    (.case (.perform (.label "propose"))
      [ ("written", .done (.nat 0)),
        ("refused", .done (.binary .add (.bound 1) (.nat 1))) ])

theorem guardedRetryStep_substClosed : SubstClosed guardedRetryStep := by
  intro σ
  simp [guardedRetryStep, nextCooldownStreak, Term.substitute, liftSubstitution, Term.rename]

theorem recklessRetryStep_substClosed : SubstClosed recklessRetryStep := by
  intro σ
  simp [recklessRetryStep, Term.substitute, liftSubstitution, Term.rename]

/-- Single-turn `SafeWP` for `guardedRetryStep`: preserves `r ≤ 1` across every demonic response. -/
theorem guardedRetry_turn_safeWP (r : Nat) (hrLe : r ≤ 1) :
    SafeWP retryProto (.app guardedRetryStep (.nat r)) (fun v => ∃ r' : Nat, v = .nat r' ∧ r' ≤ 1) := by
  refine wp_step (.beta _ (.nat r)) ?_
  simp [nextCooldownStreak, instantiate, Term.substitute, liftSubstitution, Term.rename]
  refine wp_step (.ifCondition _ _ (.primitive .less (.nat r) (.nat 1) (.boolean (decide (r < 1)))
    (.natural r) (.natural 1) rfl)) ?_
  by_cases hlt : r < 1
  · simp only [hlt, decide_true]
    refine wp_step (.ifTrue _ _) ?_
    refine wp_perform (.case _ (.perform (.label "propose"))) retryProto_propose_expected ?_
    intro resp hproto
    rcases hproto with ⟨_, hresp⟩ | ⟨hbad, _⟩
    · rcases hresp with rfl | rfl
      · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, writtenResponse, Data.term]
        refine wp_step (.caseInject "written" (.record []) _ _ rfl) ?_
        simp [instantiate, Term.substitute]
        exact wp_step (.done _) (wp_val (.natural 0) ⟨0, rfl, by omega⟩)
      · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, refusedResponse, Data.term]
        refine wp_step (.caseInject "refused" (.record []) _ _ rfl) ?_
        simp [instantiate, Term.substitute]
        refine wp_step (.done _) ?_
        refine wp_step (.primitive .add (.nat r) (.nat 1) (.nat (r + 1)) (.natural r) (.natural 1) rfl) ?_
        exact wp_val (.natural (r + 1)) ⟨r + 1, rfl, by omega⟩
    · simp at hbad
  · simp only [hlt, decide_false]
    refine wp_step (.ifFalse _ _) ?_
    refine wp_perform (.case _ (.perform (.label "cooldown"))) retryProto_cooldown_expected ?_
    intro resp hproto
    rcases hproto with ⟨hbad, _⟩ | ⟨_, rfl⟩
    · simp at hbad
    · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug]
      refine wp_step (.caseInject "ack" (.record []) _ _ rfl) ?_
      simp [instantiate, Term.substitute]
      refine wp_step (.done _) ?_
      refine wp_step (.primitive .multiply (.nat r) (.nat 0) (.nat (r * 0)) (.natural r) (.natural 0) rfl) ?_
      simp only [Nat.mul_zero]
      exact wp_val (.natural 0) ⟨0, rfl, by omega⟩

/-- **$N$-Turn Guarded Retry Invariant (`guardedRetry_loop_safeWP`)**: for *every* turn count `n`
    and *every* initial streak `r₀ ≤ 1`, `runActorFix guardedRetryStep n r₀` maintains `r_fin ≤ 1`. -/
theorem guardedRetry_loop_safeWP (n r₀ : Nat) (hr₀ : r₀ ≤ 1) :
    SafeWP retryProto (runActorFix guardedRetryStep n r₀) (fun v => ∃ r_fin : Nat, v = .nat r_fin ∧ r_fin ≤ 1) :=
  wp_loop_invariant guardedRetryStep_substClosed guardedRetry_turn_safeWP n hr₀

/-- **Adequacy Corollary (`guardedRetry_interaction_adequate`)**: every `n`-turn `Interaction`
    against any valid demonic trace finishes with `r_fin ≤ 1` and yields only expected plans. -/
theorem guardedRetry_interaction_adequate (n r₀ : Nat) (hr₀ : r₀ ≤ 1)
    {trace : List (Term × Term)} {v : Term}
    (htrace : ValidTrace retryProto trace)
    (hint : Obend.Equiv.Interaction (runActorFix guardedRetryStep n r₀) trace v) :
    (∃ r_fin : Nat, v = .nat r_fin ∧ r_fin ≤ 1) ∧ AllPlansExpected (ExpectedPlan retryProto) trace :=
  safeWP_adequacy (guardedRetry_loop_safeWP n r₀ hr₀) htrace hint

/-- **Why 1-Turn Checking Misses the Bug (`recklessRetry_one_turn_safe`)**: starting from `streak = 0`,
    `recklessRetryStep` *still* satisfies `r' ≤ 1` after 1 turn even when refused (`0 + 1 = 1 ≤ 1`)! -/
theorem recklessRetry_one_turn_safe :
    SafeWP retryProto (runActorFix recklessRetryStep 1 0) (fun v => ∃ r' : Nat, v = .nat r' ∧ r' ≤ 1) := by
  refine wp_steps (runActorFix_succ_steps 0 0 recklessRetryStep_substClosed) ?_
  refine wp_seqNat (Ψ := fun m => m ≤ 1) ?_ (fun m hm => ?_)
  · refine wp_step (.beta _ (.nat 0)) ?_
    simp [instantiate, Term.substitute, liftSubstitution, Term.rename]
    refine wp_perform (.case _ (.perform (.label "propose"))) retryProto_propose_expected ?_
    intro resp hproto
    rcases hproto with ⟨_, hresp⟩ | ⟨hbad, _⟩
    · rcases hresp with rfl | rfl
      · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, writtenResponse, Data.term]
        refine wp_step (.caseInject "written" (.record []) _ _ rfl) ?_
        simp [instantiate, Term.substitute]
        exact wp_step (.done _) (wp_val (.natural 0) ⟨0, rfl, by omega⟩)
      · dsimp only [plugContext, plug, List.foldl, SourceFrame.plug, refusedResponse, Data.term]
        refine wp_step (.caseInject "refused" (.record []) _ _ rfl) ?_
        simp [instantiate, Term.substitute]
        refine wp_step (.done _) ?_
        refine wp_step (.primitive .add (.nat 0) (.nat 1) (.nat 1) (.natural 0) (.natural 1) rfl) ?_
        exact wp_val (.natural 1) ⟨1, rfl, by omega⟩
    · simp at hbad
  · have hLoopClosed : SubstClosed (actorLoopFix recklessRetryStep) :=
      substClosed_actorLoopFix recklessRetryStep_substClosed
    have hInst : instantiate (.app (.app (actorLoopFix recklessRetryStep) (.nat 0)) (.bound 0)) (.nat m) =
        runActorFix recklessRetryStep 0 m := by
      simp [instantiate, runActorFix, Term.substitute, hLoopClosed]
    rw [hInst]
    exact wp_steps (runActorFix_zero_steps m recklessRetryStep_substClosed) (wp_val (.natural m) ⟨m, rfl, hm⟩)

/-- Helper: one refusal turn of `recklessRetryStep` inside `seqNat` steps `s` to `s + 1`. -/
private theorem recklessRetry_refused_seqNat_turn (k s : Nat) :
    ∃ ctx,
      Steps (runActorFix recklessRetryStep (k + 1) s)
        (seqNat (.case (.perform (.label "propose"))
            [ ("written", .done (.nat 0)),
              ("refused", .done (.binary .add (.nat s) (.nat 1))) ])
          (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0))) ∧
      Yields (seqNat (.case (.perform (.label "propose"))
            [ ("written", .done (.nat 0)),
              ("refused", .done (.binary .add (.nat s) (.nat 1))) ])
          (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0)))
        (.label "propose") ctx ∧
      Steps (plug ctx refusedResponse.term) (runActorFix recklessRetryStep k (s + 1)) := by
  have hUnroll := runActorFix_succ_steps k s recklessRetryStep_substClosed
  have hBeta : Step
      (seqNat (.app recklessRetryStep (.nat s))
        (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0)))
      (seqNat (.case (.perform (.label "propose"))
          [ ("written", .done (.nat 0)),
            ("refused", .done (.binary .add (.nat s) (.nat 1))) ])
        (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0))) := by
    have hb : Step (.app recklessRetryStep (.nat s))
        (.case (.perform (.label "propose"))
          [ ("written", .done (.nat 0)),
            ("refused", .done (.binary .add (.nat s) (.nat 1))) ]) := by
      simpa [recklessRetryStep, instantiate, Term.substitute, liftSubstitution, Term.rename]
        using Step.beta
          (.case (.perform (.label "propose"))
            [ ("written", .done (.nat 0)),
              ("refused", .done (.binary .add (.bound 1) (.nat 1))) ])
          (.nat s)
    exact .condition _ _ (.binaryLeft .add (.nat 1) hb)
  have hYield : Yields
      (seqNat (.case (.perform (.label "propose"))
          [ ("written", .done (.nat 0)),
            ("refused", .done (.binary .add (.nat s) (.nat 1))) ])
        (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0)))
      (.label "propose")
      ([.case [ ("written", .done (.nat 0)),
                ("refused", .done (.binary .add (.nat s) (.nat 1))) ],
        .binaryLeft .add (.nat 1),
        .condition (.done (.nat 0)) (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0))]) :=
    .condition _ _ (.binaryLeft .add (.nat 1) (.case _ (.perform (.label "propose"))))
  refine ⟨_, steps_append hUnroll (.next hBeta (.refl _)), hYield, ?_⟩
  dsimp only [plug, List.foldl, SourceFrame.plug, refusedResponse, Data.term]
  have hCase : Step
      (.case (.inject "refused" (.record []))
        [ ("written", .done (.nat 0)),
          ("refused", .done (.binary .add (.nat s) (.nat 1))) ])
      (.done (.binary .add (.nat s) (.nat 1))) := by
    simpa [instantiate, Term.substitute] using
      Step.caseInject "refused" (.record [])
        [ ("written", .done (.nat 0)),
          ("refused", .done (.binary .add (.nat s) (.nat 1))) ]
        (.done (.binary .add (.nat s) (.nat 1))) rfl
  refine .next (.condition _ _ (.binaryLeft .add (.nat 1) hCase)) ?_
  refine .next (.condition _ _ (.binaryLeft .add (.nat 1) (.done _))) ?_
  refine .next (.condition _ _ (.binaryLeft .add (.nat 1)
    (.primitive .add (.nat s) (.nat 1) (.nat (s + 1)) (.natural s) (.natural 1) rfl))) ?_
  refine .next (.condition _ _ (.primitive .add (.nat (s + 1)) (.nat 1) (.nat (s + 1 + 1))
    (.natural (s + 1)) (.natural 1) rfl)) ?_
  refine .next (.successor (s + 1) _ _) ?_
  have hLoopClosed : SubstClosed (actorLoopFix recklessRetryStep) :=
    substClosed_actorLoopFix recklessRetryStep_substClosed
  have hInst : instantiate (.app (.app (actorLoopFix recklessRetryStep) (.nat k)) (.bound 0)) (.nat (s + 1)) =
      runActorFix recklessRetryStep k (s + 1) := by
    simp [instantiate, runActorFix, Term.substitute, hLoopClosed]
  rw [hInst]
  exact .refl _

/-- **2nd-Refusal-Turn Refutation (`recklessRetry_two_turns_refuted`)**: on 2 consecutive environment
    refusal turns `[("propose", refused), ("propose", refused)]`, `runActorFix recklessRetryStep 2 0`
    evaluates to `.nat 2`, constructively refuting `SafeWP` for `r_fin ≤ 1`! -/
theorem recklessRetry_two_turns_refuted :
    ¬ SafeWP retryProto (runActorFix recklessRetryStep 2 0)
        (fun v => ∃ r_fin : Nat, v = .nat r_fin ∧ r_fin ≤ 1) := by
  obtain ⟨ctx₁, hs₁, hy₁, hp₁⟩ := recklessRetry_refused_seqNat_turn 1 0
  obtain ⟨ctx₂, hs₂, hy₂, hp₂⟩ := recklessRetry_refused_seqNat_turn 0 1
  have hFinSteps : Steps (plug ctx₂ refusedResponse.term) (.nat 2) :=
    steps_append hp₂ (runActorFix_zero_steps 2 recklessRetryStep_substClosed)
  have hRun2 : Obend.Equiv.Interaction (runActorFix recklessRetryStep 2 0)
      [(.label "propose", refusedResponse.term), (.label "propose", refusedResponse.term)] (.nat 2) :=
    .turn hs₁ hy₁ (.turn (steps_append hp₁ hs₂) hy₂ (.finish ⟨hFinSteps, .natural 2⟩))
  have hValid : ValidTrace retryProto
      [(.label "propose", refusedResponse.term), (.label "propose", refusedResponse.term)] := by
    intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl <;> exact Or.inl ⟨rfl, Or.inr rfl⟩
  refine not_safeWP_of_bad_interaction hValid hRun2 ?_
  rintro ⟨r_fin, heq, hle⟩
  cases heq
  omega

end Obend.Logic
end
