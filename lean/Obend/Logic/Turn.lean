module
/-
# Obend.Logic.Turn — interaction-tree turn verification & T4 `caseSplit`

Closes item (7) of `lean/docs/REPORT-LOGIC-20261101.md` and `review/PROGRAM-LOGIC-20261101.md`
§2.4, §5.2, §5.4:

1. **Executable yield extraction (`yields?`, `runToYield`)**:
   - `yields? : Term → Option (Term × List SourceFrame)` extracts the yielded plan and inner-first
     evaluation context, sound (`yields?_sound`) and complete (`yields?_complete`) against `Yields`.
   - `runToYield : Nat → Term → Option (Term × List SourceFrame)` iterates `Law.step?` until `yields?`
     matches, monotone in fuel (`runToYield_mono_le`) and sound (`runToYield_sound`).
   - `steps_yields_unique`: because `Step` is deterministic and a yielding term cannot step
     (`yields_no_step`), the yielded state, plan, and context reached from any start term are unique.
2. **The Turn Judge (`turnJudge : Judge TurnProblem Unit`)**:
   - Twin of `Logic.Ground.ground` for one-turn `Interaction` obligations:
     `Meaning p _ := Interaction p.term [(p.expectedPlan, p.response.term)] p.expectedResult.term`.
   - Sound on `.ok` (`turn_sound`) and refuting on both `.planMismatch` and `.resultMismatch`
     (`turn_refutes`).
3. **`Counter.obend` `bump` verified across all responses**:
   - `counter_bump_written_verified` & `counter_bump_refused_verified`: ground turn-judge proofs by
     `decide +kernel` and universally quantified `Interaction` theorems (`counter_bump_interaction`)
     for all `count : Nat` across both `written` (`count + 1`) and `refused` (`count`) responses.
4. **T4 `caseSplit` (`holdsEq_ifBool_split`, `holdsEq_case_split`, `boolSplit_sound`, `caseSplit_sound`)**:
   - Proof-tree case-splitting on open Boolean and variant scrutinees: when both branches of an
     `ifBool` (or all matching arms of a `case`) rewrite to a common right-hand side `r` via
     `Logic.Rewrite.replay`, the conditional is `HoldsEq` to `r` under every substitution whose
     scrutinee evaluates to a Boolean (or listed variant).
-/
public import Obend.Logic.Rewrite
public import Obend.Logic.Ground
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
set_option autoImplicit false

/-! ## 1. Executable `Yields` and `runToYield` -/

/-- Extract the yielded plan and evaluation context when `t` is at a `Yields` redex. -/
def yields? : Term → Option (Term × List SourceFrame)
  | .perform plan => some (plan, [])
  | .app f a => (yields? f).map fun (p, ctx) => (p, ctx ++ [.application a])
  | .get t n => (yields? t).map fun (p, ctx) => (p, ctx ++ [.field n])
  | .extend t fs => (yields? t).map fun (p, ctx) => (p, ctx ++ [.extend fs])
  | .binary op l r =>
    match yields? l with
    | some (p, ctx) => some (p, ctx ++ [.binaryLeft op r])
    | none =>
      if Obend.Law.isValueB l then
        (yields? r).map fun (p, ctx) => (p, ctx ++ [.binaryRight op l])
      else none
  | .ifZero v z s => (yields? v).map fun (p, ctx) => (p, ctx ++ [.condition z s])
  | .case t arms => (yields? t).map fun (p, ctx) => (p, ctx ++ [.case arms])
  | .ifBool c x y => (yields? c).map fun (p, ctx) => (p, ctx ++ [.ifBool x y])
  | .reflect t => (yields? t).map fun (p, ctx) => (p, ctx ++ [.reflect])
  | .metadata t => (yields? t).map fun (p, ctx) => (p, ctx ++ [.metadata])
  | .project t => (yields? t).map fun (p, ctx) => (p, ctx ++ [.project])
  | .split t names f => (yields? t).map fun (p, ctx) => (p, ctx ++ [.split names f])
  | _ => none

theorem isValueB_value' {t : Term} (h : Obend.Law.isValueB t = true) : Value t := by
  cases t <;> simp [Obend.Law.isValueB] at h <;> constructor

theorem value_isValueB' {t : Term} (h : Value t) : Obend.Law.isValueB t = true := by
  cases h <;> rfl

theorem yields?_sound : (t : Term) → ∀ {plan : Term} {ctx : List SourceFrame},
    yields? t = some (plan, ctx) → Yields t plan ctx
  | .perform p, plan, ctx, h => by
    simp only [yields?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .perform _
  | .app f a, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .application a (yields?_sound f hy)
  | .get t n, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .field n (yields?_sound t hy)
  | .extend t fs, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .extend fs (yields?_sound t hy)
  | .binary op l r, plan, ctx, h => by
    have ihl := @yields?_sound l
    have ihr := @yields?_sound r
    simp only [yields?] at h
    split at h
    · rename_i p c hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .binaryLeft op r (ihl hy)
    · split at h
      · rename_i hval
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact .binaryRight op (isValueB_value' hval) (ihr hy)
      · cases h
  | .ifZero v z s, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .condition z s (yields?_sound v hy)
  | .case t arms, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .case arms (yields?_sound t hy)
  | .ifBool c x y, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c'⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .ifBool x y (yields?_sound c hy)
  | .reflect t, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .reflect (yields?_sound t hy)
  | .metadata t, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .metadata (yields?_sound t hy)
  | .project t, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .project (yields?_sound t hy)
  | .split t names f, plan, ctx, h => by
    simp only [yields?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, c⟩, hy, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact .split names f (yields?_sound t hy)
  | .bound _, _, _, h | .hole _ _, _, _, h | .lam _, _, _, h | .mix _ _, _, _, h
  | .fix _ _, _, _, h | .specification _ _, _, _, h | .prototype _ _, _, _, h
  | .nat _, _, _, h | .boolean _, _, _, h | .label _, _, _, h
  | .record _, _, _, h | .inject _ _, _, _, h | .done _, _, _, h => by
    simp [yields?] at h

theorem value_yields?_none {t : Term} (hv : Value t) : yields? t = none := by
  cases hv <;> rfl

theorem yields?_complete {t plan : Term} {ctx : List SourceFrame} (hy : Yields t plan ctx) :
    yields? t = some (plan, ctx) := by
  induction hy with
  | perform p => rfl
  | application a _ ih => simp [yields?, ih]
  | field n _ ih => simp [yields?, ih]
  | extend fs _ ih => simp [yields?, ih]
  | binaryLeft op r _ ih => simp [yields?, ih]
  | binaryRight op hv _ ih =>
    simp [yields?, value_yields?_none hv, value_isValueB' hv, ih]
  | condition z s _ ih => simp [yields?, ih]
  | case arms _ ih => simp [yields?, ih]
  | ifBool x y _ ih => simp [yields?, ih]
  | reflect _ ih => simp [yields?, ih]
  | metadata _ ih => simp [yields?, ih]
  | project _ ih => simp [yields?, ih]
  | split names f _ ih => simp [yields?, ih]

/-- Run `t` for at most `fuel` steps until it reaches a `Yields` redex. -/
def runToYield : Nat → Term → Option (Term × List SourceFrame)
  | 0, t => yields? t
  | fuel + 1, t =>
    match yields? t with
    | some res => some res
    | none =>
      match Obend.Law.step? t with
      | some t' => runToYield fuel t'
      | none => none

theorem runToYield_sound : ∀ (fuel : Nat) {t plan : Term} {ctx : List SourceFrame},
    runToYield fuel t = some (plan, ctx) → ∃ u, Steps t u ∧ Yields u plan ctx
  | 0, t, plan, ctx, h => ⟨t, .refl t, yields?_sound t h⟩
  | fuel + 1, t, plan, ctx, h => by
    simp only [runToYield] at h
    split at h
    · rename_i res hy
      cases h
      exact ⟨t, .refl t, yields?_sound t hy⟩
    · split at h
      · rename_i t' hs
        obtain ⟨u, hsteps, hy⟩ := runToYield_sound fuel h
        exact ⟨u, .next (Obend.Law.step?_sound t hs) hsteps, hy⟩
      · cases h

theorem runToYield_mono : ∀ (fuel : Nat) {t : Term} {res : Term × List SourceFrame},
    runToYield fuel t = some res → runToYield (fuel + 1) t = some res
  | 0, t, res, h => by
    simp only [runToYield] at h ⊢
    rw [h]
  | fuel + 1, t, res, h => by
    rw [runToYield] at h ⊢
    split at h
    · exact h
    · split at h
      · exact runToYield_mono fuel h
      · cases h

theorem runToYield_mono_le {fuel fuel' : Nat} {t : Term} {res : Term × List SourceFrame}
    (le : fuel ≤ fuel') (h : runToYield fuel t = some res) :
    runToYield fuel' t = some res := by
  induction le with
  | refl => exact h
  | step _ ih => exact runToYield_mono _ ih

/-- Deterministic step relation (`Obend.Law.step?_complete` + `step?_sound`). -/
theorem step_det {t u₁ u₂ : Term} (h₁ : Step t u₁) (h₂ : Step t u₂) : u₁ = u₂ := by
  have e₁ := Obend.Law.step?_complete h₁
  have e₂ := Obend.Law.step?_complete h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- A yielding state reached by `Steps` is unique, as are its plan and context. -/
theorem steps_yields_unique {t u₁ u₂ p₁ p₂ : Term} {c₁ c₂ : List SourceFrame}
    (s₁ : Steps t u₁) (y₁ : Yields u₁ p₁ c₁)
    (s₂ : Steps t u₂) (y₂ : Yields u₂ p₂ c₂) :
    u₁ = u₂ ∧ p₁ = p₂ ∧ c₁ = c₂ := by
  induction s₁ with
  | refl =>
    cases s₂ with
    | refl =>
      obtain ⟨hp, hc⟩ := yields_deterministic y₁ y₂
      exact ⟨rfl, hp, hc⟩
    | next st _ => exact absurd st (yields_no_step y₁ _)
  | next st₁ _ ih =>
    cases s₂ with
    | refl => exact absurd st₁ (yields_no_step y₂ _)
    | next st₂ rest₂ =>
      have heq := step_det st₁ st₂
      subst heq
      exact ih y₁ rest₂

/-! ## 2. The Turn Judge (`turnJudge : Judge TurnProblem Unit`) -/

/-- A one-turn activity obligation at a data instance:
`activity` applied to `args` yields `expectedPlan`, and when resumed with `response`
evaluates to `expectedResult`. -/
structure TurnProblem where
  activity : Term
  args : List Data
  expectedPlan : Term
  response : Data
  expectedResult : Data

/-- The applied activity term. -/
def TurnProblem.term (p : TurnProblem) : Term := apps p.activity (p.args.map Data.term)

inductive TurnClause where
  /-- the activity yielded a plan different from `expectedPlan` -/
  | planMismatch
  /-- after resuming with `response`, the activity evaluated to a value different from `expectedResult` -/
  | resultMismatch
  deriving DecidableEq, Repr

/-- Check a one-turn activity obligation at fuel grade `k`. -/
def turnCheck (k : Nat) (p : TurnProblem) (_ : Unit) : Judge.Verdict TurnClause :=
  match runToYield k p.term with
  | none => .uncovered
  | some (plan, ctx) =>
    if Obend.Law.termEq plan p.expectedPlan then
      match Obend.Law.run k (plug ctx p.response.term) with
      | none => .uncovered
      | some v =>
        if Obend.Law.termEq v p.expectedResult.term then .ok
        else .refused .resultMismatch []
    else .refused .planMismatch []

/-- **`turn_sound`**: an accepted turn check establishes the one-turn `Interaction`. -/
theorem turn_sound {k : Nat} {p : TurnProblem} (h : turnCheck k p () = .ok) :
    Interaction p.term [(p.expectedPlan, p.response.term)] p.expectedResult.term := by
  unfold turnCheck at h
  cases hy : runToYield k p.term with
  | none => rw [hy] at h; cases h
  | some pair =>
    obtain ⟨plan, ctx⟩ := pair
    rw [hy] at h
    simp only at h
    by_cases hp : Obend.Law.termEq plan p.expectedPlan = true
    · simp only [hp, ite_true] at h
      cases hr : Obend.Law.run k (plug ctx p.response.term) with
      | none => rw [hr] at h; cases h
      | some v =>
        rw [hr] at h
        simp only at h
        by_cases hv : Obend.Law.termEq v p.expectedResult.term = true
        · obtain ⟨u, hsteps, hyields⟩ := runToYield_sound k hy
          have hplan : plan = p.expectedPlan := termEq_sound' hp
          have hval : v = p.expectedResult.term := termEq_sound' hv
          subst hplan; subst hval
          exact .turn hsteps hyields (.finish (Obend.Law.run_sound k hr))
        · simp [hv] at h
    · simp [hp] at h

/-- **`turn_refutes`**: a refused turn check refutes the one-turn `Interaction`. -/
theorem turn_refutes {k : Nat} {p : TurnProblem} {clause : TurnClause} {path : List Nat}
    (h : turnCheck k p () = .refused clause path) :
    ¬ Interaction p.term [(p.expectedPlan, p.response.term)] p.expectedResult.term := by
  unfold turnCheck at h
  cases hy : runToYield k p.term with
  | none => rw [hy] at h; cases h
  | some pair =>
    obtain ⟨plan, ctx⟩ := pair
    rw [hy] at h
    simp only at h
    obtain ⟨u, hsteps, hyields⟩ := runToYield_sound k hy
    by_cases hp : Obend.Law.termEq plan p.expectedPlan = true
    · simp only [hp, ite_true] at h
      cases hr : Obend.Law.run k (plug ctx p.response.term) with
      | none => rw [hr] at h; cases h
      | some v =>
        rw [hr] at h
        simp only at h
        by_cases hv : Obend.Law.termEq v p.expectedResult.term = true
        · simp [hv] at h
        · intro hint
          cases hint with
          | turn s₂ y₂ rest =>
            obtain ⟨_, _, hce⟩ := steps_yields_unique hsteps hyields s₂ y₂
            subst hce
            cases rest with
            | finish hev =>
              have hev₁ := Obend.Law.run_sound k hr
              have heq := evaluates_unique hev₁ hev
              rw [← heq] at hv
              exact hv (termEq_refl' v)
    · intro hint
      cases hint with
      | turn s₂ y₂ _ =>
        obtain ⟨_, hpe, _⟩ := steps_yields_unique hsteps hyields s₂ y₂
        rw [← hpe] at hp
        exact hp (termEq_refl' plan)

theorem turnCheck_mono {k k' : Nat} {p : TurnProblem} (le : k ≤ k')
    (hne : turnCheck k p () ≠ .uncovered) :
    turnCheck k' p () = turnCheck k p () := by
  unfold turnCheck at hne ⊢
  cases hy : runToYield k p.term with
  | none => simp [hy] at hne
  | some pair =>
    obtain ⟨plan, ctx⟩ := pair
    rw [runToYield_mono_le le hy]
    simp only at hne ⊢
    by_cases hp : Obend.Law.termEq plan p.expectedPlan = true
    · simp only [hp, ite_true] at hne ⊢
      cases hr : Obend.Law.run k (plug ctx p.response.term) with
      | none => simp [hy, hp, hr] at hne
      | some v => rw [run_mono_le le hr]
    · simp [hp]

/-- **The one-turn `Interaction` judge.** -/
instance turnJudge : Judge TurnProblem Unit where
  Clause := TurnClause
  Meaning p _ := Interaction p.term [(p.expectedPlan, p.response.term)] p.expectedResult.term
  check := turnCheck
  sound := by intro k p _ h; exact turn_sound h
  refutes _ := true
  refuted := by intro k p _ clause path h _ _; exact turn_refutes h
  Fragment p := ∃ fuel, turnCheck fuel p () = .ok
  complete := by rintro p ⟨fuel, hf⟩ _; exact ⟨(), fuel, hf⟩
  mono := by intro k k' p _ le hne; exact turnCheck_mono le hne

/-! ## 3. `Counter.obend` `bump` Verified Across All Responses -/

/-- `Counter.obend`'s `bump` activity:
```
def bump(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): count + 1n
    case refused(_): count
``` -/
def counterBump : Term :=
  .lam (.case
    (.perform (.inject "write" (.record [
      ("field", .nat 0),
      ("before", .bound 0),
      ("after", .binary .add (.bound 0) (.nat 1))
    ])))
    [ ("written", .done (.binary .add (.bound 1) (.nat 1))),
      ("refused", .done (.bound 1)) ])

/-- The plan yielded by `counterBump (.nat count)`. -/
def counterBumpPlan (count : Nat) : Term :=
  .inject "write" (.record [
    ("field", .nat 0),
    ("before", .nat count),
    ("after", .binary .add (.nat count) (.nat 1))
  ])

def writtenResponse : Data := .variant "written" (.record [])
def refusedResponse : Data := .variant "refused" (.record [])

/-- Ground turn-judge verification of `bump(5)` on `written` (`6`) and `refused` (`5`),
plus refutation when `written` claims `5`. -/
-- fixture kept (2026-11-04): cheap closed check of `turnCheck` on literal data
theorem counter_bump_turnJudge_verified :
    turnCheck 10 ⟨counterBump, [.natural 5], counterBumpPlan 5, writtenResponse, .natural 6⟩ () = .ok ∧
    turnCheck 10 ⟨counterBump, [.natural 5], counterBumpPlan 5, refusedResponse, .natural 5⟩ () = .ok ∧
    turnCheck 10 ⟨counterBump, [.natural 5], counterBumpPlan 5, writtenResponse, .natural 5⟩ () =
      .refused .resultMismatch [] := by
  decide +kernel

theorem counterBump_beta (count : Nat) :
    instantiate
      (.case
        (.perform (.inject "write" (.record [
          ("field", .nat 0),
          ("before", .bound 0),
          ("after", .binary .add (.bound 0) (.nat 1))
        ])))
        [ ("written", .done (.binary .add (.bound 1) (.nat 1))),
          ("refused", .done (.bound 1)) ])
      (.nat count) =
    .case (.perform (counterBumpPlan count))
      [("written", .done (.binary .add (.nat count) (.nat 1))),
       ("refused", .done (.nat count))] := by
  simp [counterBumpPlan, instantiate, Term.substitute, liftSubstitution, Term.rename]

/-- **Universal verification of `Counter.obend`'s `bump` for all `count : Nat`**:
on `Response.written({})`, `bump(count)` finishes at `count + 1`;
on `Response.refused({})`, `bump(count)` finishes at `count`. -/
theorem counter_bump_interaction (count : Nat) :
    Interaction (.app counterBump (.nat count))
      [(counterBumpPlan count, writtenResponse.term)] (.nat (count + 1)) ∧
    Interaction (.app counterBump (.nat count))
      [(counterBumpPlan count, refusedResponse.term)] (.nat count) := by
  have hbeta : Steps (.app counterBump (.nat count))
      (.case (.perform (counterBumpPlan count))
        [("written", .done (.binary .add (.nat count) (.nat 1))),
         ("refused", .done (.nat count))]) := by
    rw [← counterBump_beta count]
    exact .next (.beta _ (.nat count)) (.refl _)
  have hyield : Yields
      (.case (.perform (counterBumpPlan count))
        [("written", .done (.binary .add (.nat count) (.nat 1))),
         ("refused", .done (.nat count))])
      (counterBumpPlan count)
      [.case [("written", .done (.binary .add (.nat count) (.nat 1))),
              ("refused", .done (.nat count))]] :=
    .case _ (.perform (counterBumpPlan count))
  constructor
  · refine .turn hbeta hyield (.finish ⟨?_, .natural (count + 1)⟩)
    simp only [plug, List.foldl, SourceFrame.plug, writtenResponse, Data.term, Obend.Core.Data.fieldsTerm]
    refine .next (.caseInject "written" (.record []) _ (.done (.binary .add (.nat count) (.nat 1))) rfl) ?_
    have hdone : Step (instantiate (.done (.binary .add (.nat count) (.nat 1))) (.record []))
        (.binary .add (.nat count) (.nat 1)) := by
      have hi : instantiate (.done (.binary .add (.nat count) (.nat 1))) (.record []) =
          .done (.binary .add (.nat count) (.nat 1)) := by
        simp [instantiate, Term.substitute]
      rw [hi]
      exact .done _
    refine .next hdone ?_
    exact .next (.primitive .add (.nat count) (.nat 1) (.nat (count + 1)) (.natural count) (.natural 1) rfl) (.refl _)
  · refine .turn hbeta hyield (.finish ⟨?_, .natural count⟩)
    simp only [plug, List.foldl, SourceFrame.plug, refusedResponse, Data.term, Obend.Core.Data.fieldsTerm]
    refine .next (.caseInject "refused" (.record []) _ (.done (.nat count)) rfl) ?_
    have hdone : Step (instantiate (.done (.nat count)) (.record [])) (.nat count) := by
      have hi : instantiate (.done (.nat count)) (.record []) = .done (.nat count) := by
        simp [instantiate, Term.substitute]
      rw [hi]
      exact .done _
    exact .next hdone (.refl _)

/-! ## 4. T4 `caseSplit`: Proof-Tree Case-Splitting on Open Scrutinees -/

theorem holdsEq_symm {a b : Term} (h : HoldsEq a b) : HoldsEq b a :=
  fun o => (h o).symm

theorem holdsEq_trans {a b c : Term} (h₁ : HoldsEq a b) (h₂ : HoldsEq b c) : HoldsEq a c :=
  fun o => (h₁ o).trans (h₂ o)

theorem holdsEq_of_steps {a b : Term} (h : Steps a b) : HoldsEq a b :=
  holdsEq_of_observed (observed_of_steps (.inl rfl) h)

/-- **T4 semantic Boolean case split (`holdsEq_ifBool_split`)**:
if `s` evaluates to some Boolean, `t₁` is `HoldsEq` to `r` when `s` is `true`, and `t₂` is
`HoldsEq` to `r` when `s` is `false`, then `.ifBool s t₁ t₂` is `HoldsEq` to `r`. -/
theorem holdsEq_ifBool_split {s t₁ t₂ r : Term}
    (hscrut : ∃ b : Bool, Evaluates s (.boolean b))
    (htrue : Evaluates s (.boolean true) → HoldsEq t₁ r)
    (hfalse : Evaluates s (.boolean false) → HoldsEq t₂ r) :
    HoldsEq (.ifBool s t₁ t₂) r := by
  obtain ⟨b, hs, _⟩ := hscrut
  have hcond : Steps (.ifBool s t₁ t₂) (.ifBool (.boolean b) t₁ t₂) :=
    steps_congr (fun x => .ifBool x t₁ t₂) (fun st => .ifCondition t₁ t₂ st) hs
  cases b
  · have hstep : Steps (.ifBool s t₁ t₂) t₂ :=
      steps_trans hcond (steps_one (.ifFalse t₁ t₂))
    exact holdsEq_trans (holdsEq_of_steps hstep) (hfalse ⟨hs, .boolean false⟩)
  · have hstep : Steps (.ifBool s t₁ t₂) t₁ :=
      steps_trans hcond (steps_one (.ifTrue t₁ t₂))
    exact holdsEq_trans (holdsEq_of_steps hstep) (htrue ⟨hs, .boolean true⟩)

/-- **T4 semantic variant case split (`holdsEq_case_split`)**:
if `s` evaluates to `.inject label payload` for an arm `(label, body)` of `arms`, and
`instantiate body payload` is `HoldsEq` to `r`, then `.case s arms` is `HoldsEq` to `r`. -/
theorem holdsEq_case_split {s payload body r : Term} {label : String} {arms : List (String × Term)}
    (hscrut : Evaluates s (.inject label payload))
    (harm : arms.find? (fun arm => arm.1 == label) = some (label, body))
    (hbody : HoldsEq (instantiate body payload) r) :
    HoldsEq (.case s arms) r := by
  have hcond : Steps (.case s arms) (.case (.inject label payload) arms) :=
    steps_congr (fun x => .case x arms) (fun st => .caseTarget arms st) hscrut.1
  have hstep : Steps (.case s arms) (instantiate body payload) :=
    steps_trans hcond (steps_one (.caseInject label payload arms body harm))
  exact holdsEq_trans (holdsEq_of_steps hstep) hbody

/-- Check a proof-tree Boolean split: both `whenTrue` (via `onTrue`) and `whenFalse` (via `onFalse`)
rewrite to `rhs` under resolver `R`. -/
def checkBoolSplit (R : Resolver) (whenTrue whenFalse rhs : Term)
    (onTrue onFalse : List RStep) : Bool :=
  match replay R onTrue whenTrue, replay R onFalse whenFalse with
  | .ok u₁, .ok u₂ => Obend.Law.termEq u₁ rhs && Obend.Law.termEq u₂ rhs
  | _, _ => false

/-- **T4 `boolSplit_sound`**: when `checkBoolSplit` accepts `onTrue` and `onFalse`, then under every
observer-free substitution `σ` where `R` is sound and `s.substitute σ` evaluates to a Boolean,
`(.ifBool s whenTrue whenFalse).substitute σ` and `rhs.substitute σ` have the exact same completed
runs (`HoldsEq`). -/
theorem boolSplit_sound {R : Resolver} {s whenTrue whenFalse rhs : Term}
    {onTrue onFalse : List RStep}
    (hcheck : checkBoolSplit R whenTrue whenFalse rhs onTrue onFalse = true)
    {σ : Nat → Term} (hσ : SubstFree σ) (hR : RSound R σ)
    (hscrut : ∃ b : Bool, Evaluates (s.substitute σ) (.boolean b)) :
    HoldsEq ((Term.ifBool s whenTrue whenFalse).substitute σ) (rhs.substitute σ) := by
  unfold checkBoolSplit at hcheck
  cases h₁ : replay R onTrue whenTrue with
  | error _ => rw [h₁] at hcheck; cases hcheck
  | ok u₁ =>
    cases h₂ : replay R onFalse whenFalse with
    | error _ => rw [h₁, h₂] at hcheck; cases hcheck
    | ok u₂ =>
      rw [h₁, h₂] at hcheck
      simp only [Bool.and_eq_true] at hcheck
      have hu₁ : u₁ = rhs := termEq_sound' hcheck.1
      have hu₂ : u₂ = rhs := termEq_sound' hcheck.2
      subst hu₁; subst hu₂
      have L : Licence .b σ := ⟨.inl rfl, fun _ => hσ⟩
      have obs₁ := replay_sound R L hR onTrue (fun e => by cases e) h₁
      have obs₂ := replay_sound R L hR onFalse (fun e => by cases e) h₂
      simp only [Term.substitute]
      exact holdsEq_ifBool_split hscrut
        (fun _ => holdsEq_of_observed obs₁)
        (fun _ => holdsEq_of_observed obs₂)

end Obend.Logic
end
