module
/-
# Obend.Run.Fold — `Legal` is one fold; a row's verdict reads the pins of the facts it cites

`review/GENERATED-20261031.md` §2.6. The specification of an accepted log (`Obend.Run.Spec.Legal`)
is stated with every clause quantified over the log's prefixes. Here it is one left fold over an
ACCUMULATOR (`Acc`: the world, the spent tokens, the history, the abandoned call, the plan in force,
what each hole's decision cites: the fields the runner's invariant already recomputes), each row
checked by `step` against the accumulator alone, refusing by the name of the first clause it
violates (`Clause`):

- `legal_iff_fold`: `Legal host sp O v₀ cs₀ log` iff the fold of `step` over `log` from `acc₀`
  succeeds and the history is a history of the plan in force at its end (`Kept`, the one clause
  that is not per row). Both directions; the fold's result is `accOf log`.
- `reads acc e`: the facts row `e` reads at the view (a dispatch's required facts and its hole's
  decision citations); `step_world_indep`: two accumulators that differ only in the world, on which
  the host says the same of those facts and of the consumed token's liveness, give the same verdict.
  A world row reads the step relation, not facts (`step_world`).
- `legalAdmission`: all of this as an instance of the audited fold `Obend.Fold.Admission` (world
  component `V`, the rest `Rest`, openings over `Fact ⊕ Tok`); `legal_iff_admission` is
  `legal_iff_fold` through it, and `legal_step_of_pins` is `Obend.Fold.step_of_pins` at a host built
  from a `World` (from `holds_congr`; a token's liveness is the host's, not a pin).

So a ROW RECEIPT is the accumulator before the row (its roots) plus the openings of `reads acc e`:
every clause of `Legal` is decided by them, `DecisionsHeld` included (its `Dispatched` is the
accumulator's `entered`, by `entered_iff`). `OnceSpent` is per row too: a token is spent at a row
only if no earlier row spent it (`once_iff`); the admission clause already refuses it at the masked
view, so the fold's `once` check never fires first (it is kept to mirror `Legal` clause for clause).
-/
public import Obend.Run.Proofs.Invariant
public import Obend.Fold
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Proofs.Invariant
public section

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V : Type}

/-- The accumulator of the fold: the fields of a configuration `Inv` recomputes from the log. -/
structure Acc (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact V : Type) where
  world : V
  spent : List Tok
  hist : Hist S
  ended : Option (Σ i, S.Op i)
  plan : Subst S Hole A
  cites : (j : Ix) → Hole j → List Fact

/-- The clause of `Legal` a row violates. -/
inductive Clause where
  | worldSteps
  | authorized
  | decided
  | once
  | paired
  | final
  | frozen
  deriving DecidableEq, Repr

variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]

/-- The accumulator after a log. -/
def accOf (sp : Spec S Tok Fact Ob) (σ₀ : Subst S Hole A) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (log : List (Event S Hole A Fact V)) : Acc S Hole A Tok Fact V :=
  ⟨worldOf v₀ log, spentBy sp log, histOf log, endedOf log, planOf σ₀ log, citesOf cs₀ log⟩

/-- The start. -/
def acc₀ (σ₀ : Subst S Hole A) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact) : Acc S Hole A Tok Fact V :=
  ⟨v₀, [], ⟨[], none⟩, none, σ₀, cs₀⟩

/-- A world event. -/
@[expose] def Event.isWorld : Event S Hole A Fact V → Bool
  | .world _ => true
  | _ => false

variable [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)]

/-- The citations a dispatch of `o` must find holding: those of the decision of the hole the call
enters, if any. -/
def decisionReads {i : Ix} (P : Prot S Hole A i) (acc : Acc S Hole A Tok Fact V) : List Fact :=
  match entered P acc.hist.answered true with
  | some ⟨j, h⟩ => acc.cites j h
  | none => []

/-- The facts row `e` reads at the view. -/
@[expose] def reads {i : Ix} (sp : Spec S Tok Fact Ob) (P : Prot S Hole A i) (acc : Acc S Hole A Tok Fact V) :
    Event S Hole A Fact V → List Fact
  | .dispatch o => sp.requires o.2 ++ decisionReads P acc
  | _ => []


/-- One row, judged against the accumulator alone. -/
def step (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i)
    (acc : Acc S Hole A Tok Fact V) (e : Event S Hole A Fact V) : Except Clause (Acc S Hole A Tok Fact V) :=
  if acc.ended.isSome && !e.isWorld then .error .final else
  match e with
  | .world v => if host.allowed acc.world v then .ok { acc with world := v } else .error .worldSteps
  | .dispatch o =>
    if acc.hist.inflight.isSome then .error .paired
    else if !admitOp sp (View.mask (host.view acc.world) acc.spent) o.2 then .error .authorized
    else if !(decisionReads P acc).all (host.view acc.world).holds then .error .decided
    else if (match sp.consumes o.2 with
        | some t => decide (t ∈ acc.spent)
        | none => false) then .error .once
    else .ok { acc with spent := acc.spent ++ (sp.consumes o.2).toList, hist := ⟨acc.hist.answered, some o⟩ }
  | .respond r =>
    if acc.hist.inflight = some ⟨r.1, r.2.1⟩ then .ok { acc with hist := ⟨acc.hist.answered ++ [r], none⟩ }
    else .error .paired
  | .abandon o =>
    if acc.hist.inflight = some o then .ok { acc with ended := some o } else .error .paired
  | .replan (j := j) h f cs =>
    if entered P acc.hist.answered acc.hist.inflight.isSome = some ⟨j, h⟩ then .error .frozen
    else .ok { acc with plan := setHole acc.plan h f, cites := setCites acc.cites h cs }

/-! ## The prefix functions, one event at a time -/

theorem worldOf_snoc (v₀ : V) (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    worldOf v₀ (l ++ [e]) = match e with
      | .world v => v
      | _ => worldOf v₀ l := by
  unfold worldOf; rw [List.foldl_append]; cases e <;> rfl

omit [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] in
theorem spentBy_snoc (sp : Spec S Tok Fact Ob) (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    spentBy sp (l ++ [e]) = spentBy sp l ++ match e with
      | .dispatch o => (sp.consumes o.2).toList
      | _ => [] := by
  unfold spentBy; rw [List.filterMap_append]; congr 1; cases e <;> simp [List.filterMap_cons]
  cases sp.consumes _ <;> rfl

omit [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] in
theorem histOf_snoc' (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    histOf (l ++ [e]) = match e with
      | .dispatch o => ⟨(histOf l).answered, some o⟩
      | .respond r => ⟨(histOf l).answered ++ [r], none⟩
      | _ => histOf l := by
  unfold histOf; rw [List.foldl_append]; cases e <;> rfl

omit [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] in
theorem endedOf_snoc (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    endedOf (l ++ [e]) = match e with
      | .abandon o => some o
      | _ => endedOf l := by
  unfold endedOf; rw [List.foldl_append]; cases e <;> rfl

omit [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] in
theorem planOf_snoc (σ₀ : Subst S Hole A) (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    planOf σ₀ (l ++ [e]) = match e with
      | .replan h f _ => setHole (planOf σ₀ l) h f
      | _ => planOf σ₀ l := by
  unfold planOf; rw [List.foldl_append]; cases e <;> rfl

omit [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] in
theorem citesOf_snoc (cs₀ : (j : Ix) → Hole j → List Fact) (l : List (Event S Hole A Fact V))
    (e : Event S Hole A Fact V) :
    citesOf cs₀ (l ++ [e]) = match e with
      | .replan h _ fs => setCites (citesOf cs₀ l) h fs
      | _ => citesOf cs₀ l := by
  unfold citesOf; rw [List.foldl_append]; cases e <;> rfl

/-! ## One row -/

/-- Every clause of `Legal` at one row, of the prefix before it: the bodies of `WorldSteps`,
`Authorized`, `DecisionsHeld`, `Paired`, `AfterAbandon`, `ReplansUnentered`, and the row's share of
`OnceSpent`. -/
def Row (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i) (v₀ : V)
    (cs₀ : (j : Ix) → Hole j → List Fact) (pre : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) : Prop :=
  (∀ v, e = .world v → host.allowed (worldOf v₀ pre) v = true) ∧
  (∀ o, e = .dispatch o → admitOp sp (viewAt host sp v₀ pre) o.2 = true) ∧
  (∀ o, e = .dispatch o → ∀ (j : Ix) (h : Hole j),
    Dispatched P ⟨(histOf pre).answered, some o⟩ j h →
    ∀ f ∈ citesOf cs₀ pre j h, (host.view (worldOf v₀ pre)).holds f = true) ∧
  (∀ o t, e = .dispatch o → sp.consumes o.2 = some t → t ∉ spentBy sp pre) ∧
  ((∀ o, e = .dispatch o → (histOf pre).inflight = none) ∧
    (∀ r, e = .respond r → (histOf pre).inflight = some ⟨r.1, r.2.1⟩) ∧
    (∀ o, e = .abandon o → (histOf pre).inflight = some o)) ∧
  (endedOf pre ≠ none → ∃ v, e = .world v) ∧
  (∀ (j : Ix) (h : Hole j) (f : Prot S Hole A j) cs, e = .replan h f cs → ¬ Dispatched P (histOf pre) j h)

/-- The decision citations of the dispatch of `o` are exactly what `DecisionsHeld` quantifies over. -/
theorem decisionReads_iff {i : Ix} (P : Prot S Hole A i) (H : Hist S) (cs : (j : Ix) → Hole j → List Fact)
    (o : Σ i, S.Op i) (holds : Fact → Bool) (w : V) (sp' : List Tok) :
    (decisionReads P (⟨w, sp', H, none, fun _ _ => none, cs⟩ : Acc S Hole A Tok Fact V)).all holds = true ↔
      ∀ (j : Ix) (h : Hole j), Dispatched P ⟨H.answered, some o⟩ j h → ∀ f ∈ cs j h, holds f = true := by
  unfold decisionReads
  simp only
  constructor
  · intro hall j h hd
    have he := entered_iff.1 hd
    simp only [Option.isSome_some] at he
    rw [he] at hall
    exact fun f hf => List.all_eq_true.1 hall f hf
  · intro hall
    cases he : entered P H.answered true with
    | none => rfl
    | some x =>
      obtain ⟨j, h⟩ := x
      exact List.all_eq_true.2 (hall j h (entered_iff.2 (by simpa using he)))

/-- The accumulator's decision reads depend only on the history and the citations. -/
theorem decisionReads_congr {i : Ix} (P : Prot S Hole A i) (a b : Acc S Hole A Tok Fact V)
    (hh : a.hist = b.hist) (hc : a.cites = b.cites) : decisionReads P a = decisionReads P b := by
  unfold decisionReads; rw [hh, hc]

/-- **One row of the fold is one row of `Legal`**: judged at the accumulator of its prefix, the row
is accepted exactly when every clause holds there, and the accumulator moves to its log's. -/
theorem step_accOf (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (O : Open S Hole A Tok Fact Ob i)
    (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact) (pre : List (Event S Hole A Fact V))
    (e : Event S Hole A Fact V) (a : Acc S Hole A Tok Fact V) :
    step host sp O.template (accOf sp O.σ v₀ cs₀ pre) e = .ok a ↔
      Row host sp O.template v₀ cs₀ pre e ∧ a = accOf sp O.σ v₀ cs₀ (pre ++ [e]) := by
  have hdec : ∀ o, (decisionReads O.template (accOf sp O.σ v₀ cs₀ pre)).all (host.view (worldOf v₀ pre)).holds = true ↔
      ∀ (j : Ix) (h : Hole j), Dispatched O.template ⟨(histOf pre).answered, some o⟩ j h →
        ∀ f ∈ citesOf cs₀ pre j h, (host.view (worldOf v₀ pre)).holds f = true := fun o => by
    rw [decisionReads_congr O.template (accOf sp O.σ v₀ cs₀ pre) ⟨worldOf v₀ pre, spentBy sp pre, histOf pre, none, fun _ _ => none, citesOf cs₀ pre⟩ rfl rfl]
    exact decisionReads_iff _ _ _ o _ _ _
  unfold step Row
  simp only [accOf]
  cases e with
  | world v =>
    simp only [Event.isWorld, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      worldOf_snoc, spentBy_snoc, histOf_snoc', endedOf_snoc, planOf_snoc, citesOf_snoc, List.append_nil]
    by_cases ha : host.allowed (worldOf v₀ pre) v = true
    · simp only [ha, ↓reduceIte, Except.ok.injEq]
      constructor
      · rintro rfl; refine ⟨⟨fun _ e => by cases e; exact ha, ?_⟩, rfl⟩; simp
      · rintro ⟨_, rfl⟩; rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hr; exact absurd (hr.1 v rfl) ha
  | dispatch o =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true, worldOf_snoc, spentBy_snoc, histOf_snoc',
      endedOf_snoc, planOf_snoc, citesOf_snoc]
    cases hend : endedOf pre with
    | some x =>
      simp only [Option.isSome_some, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hr; obtain ⟨v, hv⟩ := hr.2.2.2.2.2.1 (by simp); cases hv
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have hview : viewAt host sp v₀ pre = View.mask (host.view (worldOf v₀ pre)) (spentBy sp pre) := rfl
      by_cases hinfs : (histOf pre).inflight.isSome = true
      · simp only [hinfs, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro hr; have := hr.2.2.2.2.1.1 o rfl; rw [this] at hinfs; cases hinfs
      · have hinf : (histOf pre).inflight = none := by simpa using hinfs
        simp only [hinfs, Bool.false_eq_true, ↓reduceIte]
        by_cases hadm : admitOp sp (View.mask (host.view (worldOf v₀ pre)) (spentBy sp pre)) o.snd = true
        · simp only [hadm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hd : (decisionReads O.template (accOf sp O.σ v₀ cs₀ pre)).all (host.view (worldOf v₀ pre)).holds = true
          · have hd' : (decisionReads O.template ⟨worldOf v₀ pre, spentBy sp pre, histOf pre, none,
                planOf O.σ pre, citesOf cs₀ pre⟩).all (host.view (worldOf v₀ pre)).holds = true := by
              simpa [accOf, hend] using hd
            simp only [hd', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases hc : sp.consumes o.snd with
            | none =>
              simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Option.toList_none, List.append_nil]
              constructor
              · rintro rfl
                refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl⟩
                · intro _ e; cases e
                · intro o' e; cases e; rw [hview]; exact hadm
                · intro o' e; cases e; exact (hdec o).1 hd
                · intro o' t e ht; cases e; rw [hc] at ht; cases ht
                · intro _ _; exact hinf
                · intro _ e; cases e
                · intro _ e; cases e
                · intro h; first | exact absurd rfl h | exact absurd hend h
                · intro _ _ _ _ e; cases e
              · rintro ⟨_, rfl⟩; rfl
            | some t =>
              by_cases ht : t ∈ spentBy sp pre
              · simp only [ht, decide_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
                intro hr; exact absurd ht (hr.2.2.2.1 o t rfl hc)
              · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
                  Option.toList_some]
                constructor
                · rintro rfl
                  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl⟩
                  · intro _ e; cases e
                  · intro o' e; cases e; rw [hview]; exact hadm
                  · intro o' e; cases e; exact (hdec o).1 hd
                  · intro o' t' e ht'; cases e; rw [hc] at ht'; cases ht'; exact ht
                  · intro _ _; exact hinf
                  · intro _ e; cases e
                  · intro _ e; cases e
                  · intro h; first | exact absurd rfl h | exact absurd hend h
                  · intro _ _ _ _ e; cases e
                · rintro ⟨_, rfl⟩; rfl
          · have hd' : ¬ (decisionReads O.template ⟨worldOf v₀ pre, spentBy sp pre, histOf pre, none,
                planOf O.σ pre, citesOf cs₀ pre⟩).all (host.view (worldOf v₀ pre)).holds = true := by
              simpa [accOf, hend] using hd
            simp only [hd', Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
            intro hr; exact absurd ((hdec o).2 (hr.2.2.1 o rfl)) hd
        · simp only [hadm, Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
          intro hr; have := hr.2.1 o rfl; rw [hview] at this; exact absurd this hadm
  | respond r =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true, worldOf_snoc, spentBy_snoc, histOf_snoc',
      endedOf_snoc, planOf_snoc, citesOf_snoc, List.append_nil]
    cases hend : endedOf pre with
    | some x =>
      simp only [Option.isSome_some, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hr; obtain ⟨v, hv⟩ := hr.2.2.2.2.2.1 (by simp); cases hv
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      by_cases hp : (histOf pre).inflight = some ⟨r.1, r.2.1⟩
      · simp only [hp, ↓reduceIte, Except.ok.injEq]
        constructor
        · rintro rfl
          refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl⟩
          · intro _ e; cases e
          · intro _ e; cases e
          · intro _ e; cases e
          · intro _ _ e; cases e
          · intro _ e; cases e
          · intro r' e; injection e with e'; subst e'; first | exact hp | rfl
          · intro _ e; cases e
          · intro h; exact absurd rfl h
          · intro _ _ _ _ e; cases e
        · rintro ⟨_, rfl⟩; rfl
      · simp only [hp, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro hr; exact absurd (hr.2.2.2.2.1.2.1 r rfl) hp
  | abandon o =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true, worldOf_snoc, spentBy_snoc, histOf_snoc',
      endedOf_snoc, planOf_snoc, citesOf_snoc, List.append_nil]
    cases hend : endedOf pre with
    | some x =>
      simp only [Option.isSome_some, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hr; obtain ⟨v, hv⟩ := hr.2.2.2.2.2.1 (by simp); cases hv
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      by_cases hp : (histOf pre).inflight = some o
      · simp only [hp, ↓reduceIte, Except.ok.injEq]
        constructor
        · rintro rfl
          refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl⟩
          · intro _ e; cases e
          · intro _ e; cases e
          · intro _ e; cases e
          · intro _ _ e; cases e
          · intro _ e; cases e
          · intro _ e; cases e
          · intro o' e; injection e with e'; subst e'; first | exact hp | rfl
          · intro h; exact absurd rfl h
          · intro _ _ _ _ e; cases e
        · rintro ⟨_, rfl⟩; rfl
      · simp only [hp, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro hr; exact absurd (hr.2.2.2.2.1.2.2 o rfl) hp
  | replan h f cs =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true, worldOf_snoc, spentBy_snoc, histOf_snoc',
      endedOf_snoc, planOf_snoc, citesOf_snoc, List.append_nil]
    cases hend : endedOf pre with
    | some x =>
      simp only [Option.isSome_some, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hr; obtain ⟨v, hv⟩ := hr.2.2.2.2.2.1 (by simp); cases hv
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      by_cases hz : entered O.template (histOf pre).answered (histOf pre).inflight.isSome = some ⟨_, h⟩
      · simp only [hz, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro hr; exact absurd (entered_iff.2 hz) (hr.2.2.2.2.2.2 _ h f cs rfl)
      · simp only [hz, ↓reduceIte, Except.ok.injEq]
        constructor
        · rintro rfl
          refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩, rfl⟩
          all_goals first
            | (intro _ e; cases e; done)
            | (intro _ _ e; cases e; done)
            | (intro h; first | exact absurd rfl h | exact absurd hend h)
            | (intro j' h' f' cs' e hd; cases e; exact hz (entered_iff.1 hd))
        · rintro ⟨_, rfl⟩; rfl

/-! ## The fold -/

theorem AtEach.and {α : Type} {Q R : List α → α → Prop} {l : List α} :
    AtEach (fun p x => Q p x ∧ R p x) l ↔ AtEach Q l ∧ AtEach R l :=
  ⟨fun h => ⟨fun n z hz => (h n z hz).1, fun n z hz => (h n z hz).2⟩,
    fun ⟨h₁, h₂⟩ n z hz => ⟨h₁ n z hz, h₂ n z hz⟩⟩

/-- Induction from the right. -/
theorem snocInduction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x t ih => rw [List.reverse_cons]; exact snoc _ _ ih

omit [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq (Σ i, S.Op i)] in
/-- `OnceSpent` row by row: no row spends a token an earlier row spent. -/
theorem once_iff (sp : Spec S Tok Fact Ob) (log : List (Event S Hole A Fact V)) :
    OnceSpent sp log ↔
      AtEach (fun pre e => ∀ o t, e = .dispatch o → sp.consumes o.2 = some t → t ∉ spentBy sp pre) log := by
  induction log using snocInduction with
  | nil => exact ⟨fun _ => AtEach.nil _, fun _ => List.nodup_nil⟩
  | snoc l e ih =>
    rw [AtEach.snoc, ← ih]
    unfold OnceSpent
    rw [spentBy_snoc]
    cases e with
    | dispatch o =>
      simp only
      cases hc : sp.consumes o.2 with
      | none =>
        simp only [Option.toList_none, List.append_nil]
        constructor
        · intro hn; refine ⟨hn, ?_⟩
          intro o' t e ht; cases e; rw [hc] at ht; cases ht
        · exact fun h => h.1
      | some t =>
        simp only [Option.toList_some]
        rw [List.nodup_append]
        constructor
        · rintro ⟨hn, -, hd⟩
          refine ⟨hn, ?_⟩
          intro o' t' e ht' hm
          cases e; rw [hc] at ht'; cases ht'
          exact hd t hm t (List.mem_singleton_self t) rfl
        · rintro ⟨hn, hr⟩
          refine ⟨hn, by simp, ?_⟩
          intro a ha b hb e
          rw [List.mem_singleton] at hb
          subst hb; subst e
          exact hr o a rfl hc ha
    | _ => simp

theorem legal_rows_aux {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {cs₀ : (j : Ix) → Hole j → List Fact}
    {log : List (Event S Hole A Fact V)} :
    Legal host sp O v₀ cs₀ log ↔ AtEach (Row host sp O.template v₀ cs₀) log ∧ Kept O.Ω O.σ O.template log := by
  rw [show Legal host sp O v₀ cs₀ log ↔ (WorldSteps host v₀ log ∧ Authorized host sp v₀ log ∧
      DecisionsHeld host O.template v₀ cs₀ log ∧ OnceSpent sp log ∧ Paired log ∧ AfterAbandon log ∧
      ReplansUnentered O.template log) ∧ Kept O.Ω O.σ O.template log from
    ⟨fun h => ⟨⟨h.steps, h.authorized, h.decided, h.once, h.paired, h.final, h.frozen⟩, h.kept⟩,
     fun ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩]
  rw [once_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩
    exact ⟨fun n z hz => ⟨h1 n z hz, h2 n z hz, h3 n z hz, h4 n z hz, h5 n z hz, h6 n z hz, h7 n z hz⟩, h8⟩
  · rintro ⟨hr, h8⟩
    exact ⟨⟨fun n z hz => (hr n z hz).1, fun n z hz => (hr n z hz).2.1, fun n z hz => (hr n z hz).2.2.1,
      fun n z hz => (hr n z hz).2.2.2.1, fun n z hz => (hr n z hz).2.2.2.2.1,
      fun n z hz => (hr n z hz).2.2.2.2.2.1, fun n z hz => (hr n z hz).2.2.2.2.2.2⟩, h8⟩

/-- `Legal`'s per-row clauses are one `AtEach Row`. -/
theorem legal_iff_rows (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (log : List (Event S Hole A Fact V)) :
    Legal host sp O v₀ cs₀ log ↔ AtEach (Row host sp O.template v₀ cs₀) log ∧ Kept O.Ω O.σ O.template log := by
  exact legal_rows_aux

/-- The fold of `step` succeeds exactly when every row holds, and then ends at the log's
accumulator. -/
theorem fold_iff_rows (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (log : List (Event S Hole A Fact V)) (a : Acc S Hole A Tok Fact V) :
    log.foldlM (step host sp O.template) (acc₀ O.σ v₀ cs₀) = .ok a ↔
      AtEach (Row host sp O.template v₀ cs₀) log ∧ a = accOf sp O.σ v₀ cs₀ log := by
  induction log using snocInduction generalizing a with
  | nil =>
    simp only [List.foldlM_nil]
    exact ⟨fun h => ⟨AtEach.nil _, by cases h; rfl⟩, fun ⟨_, h⟩ => by rw [h]; rfl⟩
  | snoc l e ih =>
    rw [List.foldlM_append, AtEach.snoc]
    cases hl : l.foldlM (step host sp O.template) (acc₀ O.σ v₀ cs₀) with
    | error c =>
      simp only [bind, Except.bind]
      constructor
      · intro h; cases h
      · rintro ⟨⟨hrows, _⟩, _⟩
        have := (ih (accOf sp O.σ v₀ cs₀ l)).2 ⟨hrows, rfl⟩
        rw [hl] at this; cases this
    | ok b =>
      obtain ⟨hrows, rfl⟩ := (ih b).1 hl
      simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil]
      have key := step_accOf host sp O v₀ cs₀ l e
      cases hs : step host sp O.template (accOf sp O.σ v₀ cs₀ l) e with
      | error c =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro ⟨_, hr⟩ ha
        have := (key _).2 ⟨hr, rfl⟩; rw [hs] at this; cases this
      | ok b =>
        have hk := (key b).1 hs
        simp only [pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl; exact ⟨⟨hrows, hk.1⟩, hk.2⟩
        · rintro ⟨_, rfl⟩; exact hk.2

/-- **`Legal` is one fold**: a log is `Legal` exactly when the fold of `step` over it succeeds from
the start and the history is a history of the plan in force at its end. -/
public theorem legal_iff_fold (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (log : List (Event S Hole A Fact V)) :
    Legal host sp O v₀ cs₀ log ↔
      ∃ acc, log.foldlM (step host sp O.template) (acc₀ O.σ v₀ cs₀) = .ok acc ∧
        Started (fill O.Ω acc.plan O.template) acc.hist := by
  rw [legal_iff_rows]
  constructor
  · rintro ⟨hrows, hkept⟩
    exact ⟨_, (fold_iff_rows host sp O v₀ cs₀ log _).2 ⟨hrows, rfl⟩, hkept⟩
  · rintro ⟨acc, hf, hk⟩
    obtain ⟨hrows, rfl⟩ := (fold_iff_rows host sp O v₀ cs₀ log acc).1 hf
    exact ⟨hrows, hk⟩

/-! ## A row's verdict reads the pins of the facts it reads -/

theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- **A row's verdict depends only on what it reads**: two accumulators that differ only in their
world, on which the host says the same of every fact the row reads and of the liveness of the token
it consumes, give the same verdict on a row that is not a world move; the accepted accumulators
differ only in the world. -/
public theorem step_world_indep (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i)
    (acc : Acc S Hole A Tok Fact V) (w' : V) (e : Event S Hole A Fact V) (hw : e.isWorld = false)
    (hholds : ∀ f ∈ reads sp P acc e, (host.view acc.world).holds f = (host.view w').holds f)
    (hlive : ∀ o t, e = .dispatch o → sp.consumes o.2 = some t → (host.view acc.world).live t = (host.view w').live t) :
    step host sp P { acc with world := w' } e =
      (step host sp P acc e).map fun a => { a with world := w' } := by
  unfold step
  cases e with
  | world v => cases hw
  | dispatch o =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true]
    have hdr : decisionReads P { acc with world := w' } = decisionReads P acc := rfl
    have hreq : ∀ f ∈ sp.requires o.2, (host.view acc.world).holds f = (host.view w').holds f :=
      fun f hf => hholds f (List.mem_append_left _ hf)
    have hdc : ∀ f ∈ decisionReads P acc, (host.view acc.world).holds f = (host.view w').holds f :=
      fun f hf => hholds f (List.mem_append_right _ hf)
    have hadm : admitOp sp (View.mask (host.view w') acc.spent) o.2 =
        admitOp sp (View.mask (host.view acc.world) acc.spent) o.2 := by
      simp only [admitOp, View.mask]
      congr 1
      · exact all_congr_mem fun f hf => (hreq f hf).symm
      · cases hc : sp.consumes o.2 with
        | none => rfl
        | some t => simp only; rw [hlive o t rfl hc]
    have hall : (decisionReads P acc).all (host.view w').holds =
        (decisionReads P acc).all (host.view acc.world).holds :=
      all_congr_mem fun f hf => (hdc f hf).symm
    simp only [hdr, hadm, hall]
    repeat' split <;> try rfl
  | respond r =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true]
    repeat' split <;> try rfl
  | abandon o =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true]
    repeat' split <;> try rfl
  | replan h f cs =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true]
    repeat' split <;> try rfl

/-- A row that is not a world move keeps the world. -/
theorem step_keeps_world (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i)
    (acc b : Acc S Hole A Tok Fact V) (e : Event S Hole A Fact V) (hw : e.isWorld = false)
    (h : step host sp P acc e = .ok b) : b.world = acc.world := by
  unfold step at h
  cases e with
  | world v => cases hw
  | _ =>
    simp only [Event.isWorld, Bool.not_false, Bool.and_true] at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; rfl)

/-! ## `Legal` as an instance of the audited fold (`Obend.Fold.Admission`) -/

/-- The accumulator less its world. -/
structure Rest (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact : Type) where
  spent : List Tok
  hist : Hist S
  ended : Option (Σ i, S.Op i)
  plan : Subst S Hole A
  cites : (j : Ix) → Hole j → List Fact

def Acc.ofPair (w : V) (r : Rest S Hole A Tok Fact) : Acc S Hole A Tok Fact V :=
  ⟨w, r.spent, r.hist, r.ended, r.plan, r.cites⟩

def Acc.rest (a : Acc S Hole A Tok Fact V) : Rest S Hole A Tok Fact := ⟨a.spent, a.hist, a.ended, a.plan, a.cites⟩

def Acc.toPair (a : Acc S Hole A Tok Fact V) : V × Rest S Hole A Tok Fact := (a.world, a.rest)

/-- What the host says of a fact (`inl`) or of a token's liveness (`inr`): the openings of a row. -/
@[expose] def hostLook (host : Host V Tok Fact) (w : V) : Fact ⊕ Tok → Bool
  | .inl f => (host.view w).holds f
  | .inr t => (host.view w).live t

/-- A row's reads as openings: the facts, and the token it consumes. -/
@[expose] def legalReads (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i) (a : V × Rest S Hole A Tok Fact) :
    Event S Hole A Fact V → List (Fact ⊕ Tok)
  | .dispatch o => (reads sp P (Acc.ofPair a.1 a.2) (.dispatch o)).map .inl ++ (sp.consumes o.2).toList.map .inr
  | _ => []

/-- **`Legal` as an audited fold.** -/
@[expose] def legalAdmission (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i) :
    Obend.Fold.Admission V (Rest S Hole A Tok Fact) (Event S Hole A Fact V) (Fact ⊕ Tok) Clause where
  step a e := (step host sp P (Acc.ofPair a.1 a.2) e).map Acc.toPair
  reads := legalReads sp P
  look := hostLook host
  moves := Event.isWorld
  observe := .world
  allowed := host.allowed
  keeps_world := by
    intro a e b hm h
    cases hs : step host sp P (Acc.ofPair a.1 a.2) e with
    | error c => rw [hs] at h; cases h
    | ok b' =>
      rw [hs] at h; cases h
      exact step_keeps_world host sp P _ b' e hm hs
  step_of_reads := by
    intro a w' e hm hr
    have key := step_world_indep host sp P (Acc.ofPair a.1 a.2) w' e hm
      (fun f hf => by
        have := hr (.inl f) (by cases e <;> simp_all [legalReads, reads, Event.isWorld])
        exact this)
      (fun o t he ht => by
        subst he
        exact hr (.inr t) (by simp [legalReads, ht]))
    show (step host sp P (Acc.ofPair w' a.2) e).map Acc.toPair = _
    rw [show Acc.ofPair w' a.2 = { Acc.ofPair a.1 a.2 with world := w' } from rfl, key]
    cases hs : step host sp P (Acc.ofPair a.1 a.2) e with
    | error c => rfl
    | ok b =>
      simp only [Except.map, Acc.toPair]
      rfl
  observe_ok := by
    intro w w' l ha
    show (step host sp P (Acc.ofPair w l) (.world w')).map Acc.toPair = _
    simp [step, Event.isWorld, Acc.ofPair, ha]
    rfl

theorem foldlM_map {α β γ ε : Type} (f : α → γ → Except ε α) (g : α → β) (g' : β → α)
    (hg : ∀ a, g' (g a) = a) :
    ∀ (l : List γ) (x : α), l.foldlM (fun b c => (f (g' b) c).map g) (g x) = (l.foldlM f x).map g
  | [], x => rfl
  | c :: l, x => by
    simp only [List.foldlM_cons, hg]
    cases f x c with
    | error e => rfl
    | ok y => simp only [bind, Except.bind]; exact foldlM_map f g g' hg l y

/-- **`Legal` is the audited fold's run**: a log is `Legal` exactly when `legalAdmission` folds it
from the start and the history is a history of the plan in force at its end. -/
public theorem legal_iff_admission (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (log : List (Event S Hole A Fact V)) :
    Legal host sp O v₀ cs₀ log ↔
      ∃ b, (legalAdmission host sp O.template).run (acc₀ O.σ v₀ cs₀).toPair log = .ok b ∧
        Started (fill O.Ω b.2.plan O.template) b.2.hist := by
  rw [legal_iff_fold]
  have hfold : (legalAdmission host sp O.template).run (acc₀ O.σ v₀ cs₀).toPair log =
      (log.foldlM (step host sp O.template) (acc₀ O.σ v₀ cs₀)).map Acc.toPair :=
    foldlM_map (step host sp O.template) Acc.toPair (fun p => Acc.ofPair p.1 p.2) (fun _ => rfl) log _
  rw [hfold]
  constructor
  · rintro ⟨acc, h, hk⟩
    exact ⟨acc.toPair, by rw [h]; rfl, hk⟩
  · rintro ⟨b, h, hk⟩
    cases hf : log.foldlM (step host sp O.template) (acc₀ O.σ v₀ cs₀) with
    | error c => rw [hf] at h; cases h
    | ok acc =>
      rw [hf] at h; cases h
      exact ⟨acc, rfl, hk⟩

/-- **A row's verdict depends only on the pins of what it reads** (`Obend.Fold.step_of_pins` at
`Legal`): for a host built from a `World`, accumulators differing only in the world agree on a row
that is not a world move when the pins of the cells of its facts agree, and the liveness of the
token it consumes (not a pin: the host's) agrees. -/
public theorem legal_step_of_pins [World V Fact] (dec : ∀ v v' : V, Decidable (World.Step (Fact := Fact) v v'))
    (live : V → Tok → Bool) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i)
    (a : V × Rest S Hole A Tok Fact) (e : Event S Hole A Fact V) (hm : e.isWorld = false) (w' : V)
    (hp : ∀ f ∈ legalReads sp P a e,
      (match f with | .inl f => Sum.inl (World.pin a.1 (World.cell f)) | .inr t => Sum.inr (live a.1 t) :
        Option (World.Pin V) ⊕ Bool) =
      (match f with | .inl f => Sum.inl (World.pin w' (World.cell f)) | .inr t => Sum.inr (live w' t))) :
    (legalAdmission (Host.ofWorld dec live) sp P).step (w', a.2) e =
      ((legalAdmission (Host.ofWorld dec live) sp P).step a e).map fun b => (w', b.2) :=
  (legalAdmission (Host.ofWorld dec live) sp P).step_of_reads a w' e hm fun f hf => by
    have h := hp f hf
    cases f with
    | inl f =>
      simp only [Sum.inl.injEq] at h
      exact World.holds_congr a.1 w' f h
    | inr t =>
      simp only [Sum.inr.injEq] at h
      exact h

/-- A world row reads the host's step from the accumulator's world, and nothing else. -/
public theorem step_world (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} (P : Prot S Hole A i)
    (acc : Acc S Hole A Tok Fact V) (v : V) :
    step host sp P acc (.world v) = if host.allowed acc.world v then .ok { acc with world := v } else .error .worldSteps := by
  unfold step; simp [Event.isWorld]

end

end Obend.Run

end
