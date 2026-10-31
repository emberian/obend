module
/- Extracted Data agrees. -/
public import Obend.Tactic.Cases
public import Obend.Core.Collect
public import Obend.Core.Data
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Collect.Runs
namespace Obend.Core.Collect
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

/-! ## Extracted Data agrees -/

section ExceptLemmas
variable {ε α β : Type}
@[simp] public theorem except_throw_bind (e : ε) (k : α → Except ε β) : (throw e >>= k : Except ε β) = .error e := rfl
@[simp] public theorem except_map_throw (g : α → β) (e : ε) : (g <$> (throw e : Except ε α)) = .error e := rfl
@[simp] public theorem except_throw_ok (e : ε) (a : α) : ((throw e : Except ε α) = .ok a) ↔ False := by
  constructor <;> intro h <;> cases h
@[simp] public theorem except_error_ok (e : ε) (a : α) : ((Except.error e : Except ε α) = .ok a) ↔ False := by
  constructor <;> intro h <;> cases h
@[simp] public theorem except_bind_ok (x : Except ε α) (k : α → Except ε β) (r : β) :
    (x >>= k) = .ok r ↔ ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x <;> simp [bind, Except.bind]
@[simp] public theorem except_map_ok (g : α → β) (x : Except ε α) (r : β) :
    (g <$> x) = .ok r ↔ ∃ a, x = .ok a ∧ g a = r := by
  cases x <;> simp [Functor.map, Except.map]
@[simp] public theorem except_pure_ok (a b : α) : ((pure a : Except ε α) = .ok b) ↔ a = b := by
  simp [pure, Except.pure]
end ExceptLemmas

open Obend.Core.Data

/-- The continuation `forceWith` takes after one bounded transition. -/
@[expose] public def continueForce (policy : State → Bool) (limits : Limits) (ticks : Nat) : Outcome → Outcome × Nat
  | .suspended .ticks next => forceWith policy limits ticks next
  | other => (other, ticks)

public theorem forceWith_succ_inactive {policy : State → Bool} {limits : Limits} {ticks : Nat} {s : State}
    (inactive : active s.control = false) :
    forceWith policy limits (ticks + 1) s = (runBounded limits 0 s, ticks + 1) := by
  cases control : s.control <;> rw [control] at inactive <;> simp [active] at inactive <;>
    simp [forceWith, control]

public theorem forceWith_succ_active {policy : State → Bool} {limits : Limits} {ticks : Nat} {s : State}
    (isActive : active s.control = true) :
    forceWith policy limits (ticks + 1) s =
      if policy s = false then (.suspended .capacity s, ticks + 1)
      else continueForce policy limits ticks (runBounded limits 1 s) := by
  cases control : s.control <;> rw [control] at isActive <;> simp [active] at isActive <;>
    simp only [forceWith, control] <;> cases policy s <;> simp <;>
    cases runBounded limits 1 s <;> simp [continueForce] <;> rename_i reason _ <;> cases reason <;> rfl

/-- **Forcing agrees** (the bounded forcing every extraction runs), for any policy that
a related state passes whenever the original does (the kernel's is constantly true). -/
theorem related_forceWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → RoomFor limits limits' s t →
      ranOutOfHeap (forceWith policy limits ticks s).1 = false →
      OutcomeRel f D (forceWith policy limits ticks s).1 (forceWith policy limits' ticks t).1 ∧
        (forceWith policy limits' ticks t).2 = (forceWith policy limits ticks s).2 := by
  intro ticks
  induction ticks with
  | zero => intro s t related _ _; exact ⟨runBounded_zero_related related limits limits', rfl⟩
  | succ ticks ih =>
    intro s t related room notCapacity
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [forceWith_succ_inactive isActive, forceWith_succ_inactive (by rw [activeT, isActive])]
      exact ⟨runBounded_zero_related related limits limits', rfl⟩
    | true =>
      rw [forceWith_succ_active isActive] at notCapacity ⊢
      rw [forceWith_succ_active (by rw [activeT, isActive])]
      cases allowed : policy s with
      | false => simp [allowed, ranOutOfHeap] at notCapacity
      | true =>
        have allowedT := respects s t related allowed
        simp only [allowed, allowedT, Bool.true_eq_false, if_false] at notCapacity ⊢
        cases ran : runBounded limits 1 s with
        | suspended reason next =>
          cases reason with
          | ticks =>
            have rel := related_runBounded limits limits' 1 s t related room (by rw [ran]; rfl)
            rw [ran] at rel
            cases ranT : runBounded limits' 1 t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
            obtain ⟨same, nextRel⟩ := rel
            subst same
            rw [ran] at notCapacity
            exact ih _ _ nextRel (room.shift related nextRel) notCapacity
          | capacity => rw [ran] at notCapacity; simp [continueForce, ranOutOfHeap] at notCapacity
        | finished value next | divergent value next | refused value next | yielded value next =>
          have rel := related_runBounded limits limits' 1 s t related room (by rw [ran]; rfl)
          rw [ran] at rel
          cases ranT : runBounded limits' 1 t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
          all_goals exact ⟨rel, rfl⟩


/-- Extraction results agree: same Data, same remaining budget, related states. -/
@[expose] public def ResultRel (f : Nat → Nat) (D : Nat → Prop) (r r' : Result) : Prop :=
  r'.value = r.value ∧ r'.remaining = r.remaining ∧ Related f D r.state r'.state

/-- One field of a record's materialization (the body of `materializeWith`'s fold). -/
@[expose] public def recordStep (policy : State → Bool) (limits : Limits) (depth : Nat)
    (prior : List (String × Data) × State × Budget) (field : String × Nat) :
    Except (Failure × State × Budget) (List (String × Data) × State × Budget) := do
  let bytes := field.1.utf8ByteSize+(toString field.1.utf8ByteSize).utf8ByteSize+1
  if bytes > prior.2.2.bytes || prior.2.2.nodes = 0 then throw (.budget,prior.2.1,prior.2.2)
  let entered : State := {prior.2.1 with control:=.enter field.2,stack:=[]}
  let (outcome,ticks) := forceWith policy limits prior.2.2.ticks entered
  let nextBudget := {prior.2.2 with ticks:=ticks,bytes:=prior.2.2.bytes-bytes}
  match outcome with
  | .finished forced retained =>
    let child ← materializeWith policy limits depth nextBudget forced retained
    pure ((field.1,child.value)::prior.1,child.state,child.remaining)
  | .suspended reason retained => throw (suspensionFailure reason,retained,nextBudget)
  | .divergent _ retained => throw (.divergent,retained,nextBudget)
  | .refused _ retained => throw (.refused,retained,nextBudget)
  | .yielded _ retained => throw (.yielded,retained,nextBudget)

public theorem materializeWith_record (policy : State → Bool) (limits : Limits) (depth : Nat) (budget : Budget)
    (fields : List (String × Nat)) (state : State) :
    materializeWith policy limits (depth+1) budget (.record fields) state = (do
      if budget.nodes = 0 then throw (.budget,state,budget)
      let remaining := {budget with nodes:=budget.nodes-1}
      let headerBytes := (toString fields.length).utf8ByteSize+2
      if headerBytes > remaining.bytes then throw (.budget,state,remaining)
      let remaining := {remaining with bytes:=remaining.bytes-headerBytes}
      if (fields.map Prod.fst).eraseDups.length != fields.length then throw (.duplicateField,state,remaining)
      if fields.length > remaining.nodes then throw (.budget,state,remaining)
      let pair ← fields.foldlM (recordStep policy limits depth) ([],state,remaining)
      pure ⟨.record pair.1.reverse,pair.2.1,pair.2.2⟩) := rfl

theorem foldlM_related {f : Nat → Nat} {D : Nat → Prop}
    {step step' : List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State × Budget) (List (String × Data) × State × Budget)}
    (stepRel : ∀ (acc : List (String × Data)) (st st' : State) (b : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget),
      Related f D st st' → D field.2 → step (acc, st, b) field = .ok out →
      ∃ out', step' (acc, st', b) (field.1, f field.2) = .ok out' ∧ out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧
        Related f D out.2.1 out'.2.1) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st st' : State) (b : Budget)
      (out : List (String × Data) × State × Budget),
      Related f D st st' → AllIn D (fields.map Prod.snd) → fields.foldlM step (acc, st, b) = .ok out →
      ∃ out', (fields.map fun field => (field.1, f field.2)).foldlM step' (acc, st', b) = .ok out' ∧
        out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧ Related f D out.2.1 out'.2.1 := by
  intro fields
  induction fields with
  | nil =>
    intro acc st st' b out related _ folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨_, rfl, rfl, rfl, related⟩
  | cons field rest ih =>
    intro acc st st' b out related inside folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    obtain ⟨mid', first', same1, same2, midRel⟩ :=
      stepRel acc st st' b field mid related (inside field.2 (by simp)) first
    obtain ⟨out', folded', outSame1, outSame2, outRel⟩ :=
      ih mid.1 mid.2.1 mid'.2.1 mid.2.2 out midRel (fun x member => inside x (by simp [member]))
        restFolded
    refine ⟨out', ?_, outSame1, outSame2, outRel⟩
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok]
    refine ⟨mid', first', ?_⟩
    have shape : mid' = (mid.1, mid'.2.1, mid.2.2) := by
      obtain ⟨a, b, c⟩ := mid'
      simp only at same1 same2
      rw [same1, same2]
    rw [shape]; exact folded'

/-- **Materialization agrees**: a related state and the renamed value materialize the
same Data with the same remaining budget, whenever the original succeeds. -/
theorem related_materializeWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s t : State) (r : Result),
      Related f D s t → RoomFor limits limits' s t → AllIn D (valueAddresses value) →
      materializeWith policy limits depth budget value s = .ok r →
      ∃ r', materializeWith policy limits' depth budget (renameValue f value) t = .ok r' ∧
        ResultRel f D r r' := by
  intro depth
  induction depth with
  | zero => intro budget value s t r _ _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s t r related room valueIn found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : D payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have enteredRel : Related f D ⟨s.heap, .enter payload, []⟩ ⟨t.heap, .enter (f payload), []⟩ :=
            ⟨related.heap, allIn_cons payloadIn (allIn_nil D), rfl, by simp, rfl⟩
          cases forced : (forceWith policy limits budget.ticks ⟨s.heap, .enter payload, []⟩).1 with
          | finished value retained =>
            rw [forced] at found
            have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' budget.ticks _ _ enteredRel
              ⟨room.heap, room.stack⟩ (by rw [forced]; rfl)
            rw [forced] at rel
            cases forcedT : (forceWith policy limits' budget.ticks ⟨t.heap, .enter (f payload), []⟩).1 <;>
              rw [forcedT] at rel <;> simp only [OutcomeRel] at rel
            obtain ⟨valueEq, valueIn', retainedRel⟩ := rel
            simp at found
            obtain ⟨a, materialized, rfl⟩ := found
            obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
              ih _ _ _ _ _ retainedRel (room.shift related retainedRel) valueIn' materialized
            refine ⟨⟨.variant label a'.value, a'.state, a'.remaining⟩, ?_, by simp [aValue], aRemaining, aRel⟩
            rw [show renameValue f (.variant label payload) = .variant label (f payload) from rfl]
            simp [materializeWith, c1, c2, forcedT, ticksEq, valueEq, materialized']
          | _ => rw [forced] at found; simp at found
    | record fields =>
      have fieldsIn : AllIn D (fields.map Prod.snd) := valueIn
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              have key := foldlM_related (f := f) (D := D) (step := recordStep policy limits depth)
                (step' := recordStep policy limits' depth) ?_ fields [] s t _ out related fieldsIn folded
              · obtain ⟨out', folded', same1, same2, outRel⟩ := key
                refine ⟨⟨.record out'.1.reverse, out'.2.1, out'.2.2⟩, ?_, by simp [same1], by simp [same2], outRel⟩
                simp [materializeWith_record, renameValue, c1, c2, c3, c4, folded', Function.comp_def]
              · intro acc st st' b field out stRel inField stepped
                simp [recordStep] at stepped
                split at stepped
                · simp at stepped
                · rename_i cond
                  have enteredRel : Related f D ⟨st.heap, .enter field.2, []⟩ ⟨st'.heap, .enter (f field.2), []⟩ :=
                    ⟨stRel.heap, allIn_cons inField (allIn_nil D), rfl, by simp, rfl⟩
                  have stRoom : RoomFor limits limits' st st' := room.shift related stRel
                  cases forced : forceWith policy limits b.ticks ⟨st.heap, .enter field.2, []⟩ with
                  | mk outcome rest =>
                    rw [forced] at stepped
                    cases outcome with
                    | finished value retained =>
                      have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' b.ticks _ _ enteredRel
                        ⟨stRoom.heap, stRoom.stack⟩ (by rw [forced]; rfl)
                      rw [forced] at rel ticksEq
                      cases forcedT : forceWith policy limits' b.ticks ⟨st'.heap, .enter (f field.2), []⟩ with
                      | mk outcome' rest' =>
                        rw [forcedT] at rel ticksEq
                        simp only at rel ticksEq
                        subst ticksEq
                        cases outcome' <;> simp only [OutcomeRel] at rel
                        obtain ⟨valueEq, valueIn', retainedRel⟩ := rel
                        subst valueEq
                        simp at stepped
                        obtain ⟨a, materialized, rfl⟩ := stepped
                        obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
                          ih _ _ _ _ _ retainedRel (room.shift related retainedRel) valueIn' materialized
                        refine ⟨((field.1, a'.value) :: acc, a'.state, a'.remaining), ?_, by simp [aValue],
                          aRemaining, aRel⟩
                        simp [recordStep, cond, forcedT, materialized']
                    | _ => simp at stepped
          · simp at found


/-- **Completion agrees**: a finished related state completes to the same Data. -/
public theorem related_completeWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits)
    (budget : Budget) {s t : State} {r : Result} (related : Related f D s t) (room : RoomFor limits limits' s t)
    (found : completeWith policy limits budget s = .ok r) :
    ∃ r', completeWith policy limits' budget t = .ok r' ∧ ResultRel f D r r' := by
  cases allowed : policy s with
  | false => simp [completeWith, allowed] at found
  | true =>
    have allowedT := respects s t related allowed
    obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
    obtain ⟨heap, control, stack⟩ := s
    obtain ⟨heap', control', stack'⟩ := t
    simp only at hr controlIn controlEq stackIn stackEq allowed allowedT
    subst controlEq stackEq
    have related : Related f D ⟨heap, control, stack⟩ ⟨heap', renameControl f control, stack.map (renameFrame f)⟩ :=
      ⟨hr, controlIn, rfl, stackIn, rfl⟩
    cases control with
    | complete value =>
      cases stack with
      | nil =>
        simp [completeWith, allowed] at found
        obtain ⟨a, materialized, rest⟩ := found
        obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
          related_materializeWith respects limits limits' _ _ _ _ _ _ related room controlIn materialized
        split at rest
        · rename_i bytes encodedAt
          split at rest
          · simp at rest
          · rename_i small
            simp at rest; subst rest
            refine ⟨a', ?_, aValue, aRemaining, aRel⟩
            simp only [renameControl, List.map_nil] at allowedT materialized'
            simp [completeWith, allowedT, renameControl, materialized', aValue, encodedAt, small]
        · simp at rest
      | cons frame rest => simp [completeWith, allowed] at found
    | _ => simp [completeWith, allowed] at found

/-- **Plan extraction agrees**: a yielded related state's Plan is the same Data. -/
public theorem related_yieldedPlanWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits)
    (budget : Budget) {s t : State} {r : Result} (related : Related f D s t) (room : RoomFor limits limits' s t)
    (found : yieldedPlanWith policy limits budget s = .ok r) :
    ∃ r', yieldedPlanWith policy limits' budget t = .ok r' ∧ ResultRel f D r r' := by
  obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at hr controlIn controlEq stackIn stackEq
  subst controlEq stackEq
  cases control with
  | yielded plan =>
    have planIn : D plan := controlIn plan (List.mem_singleton_self plan)
    have enteredRel : Related f D ⟨heap, .enter plan, []⟩ ⟨heap', .enter (f plan), []⟩ :=
      ⟨hr, controlIn, rfl, by simp, rfl⟩
    simp only [yieldedPlanWith, renameControl] at found ⊢
    have enteredRoom : RoomFor limits limits' ⟨heap, .enter plan, []⟩ ⟨heap', .enter (f plan), []⟩ :=
      ⟨room.heap, room.stack⟩
    have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' budget.ticks _ _ enteredRel enteredRoom (by
      cases forced : forceWith policy limits budget.ticks ⟨heap, .enter plan, []⟩ with
      | mk outcome ticks =>
        rw [forced] at found
        cases outcome <;> simp at found
        rfl)
    cases forced : forceWith policy limits budget.ticks ⟨heap, .enter plan, []⟩ with
    | mk outcome ticks =>
      rw [forced] at found rel ticksEq
      cases outcome with
      | finished value retained =>
        cases forcedT : forceWith policy limits' budget.ticks ⟨heap', .enter (f plan), []⟩ with
        | mk outcome' ticks' =>
          rw [forcedT] at rel ticksEq
          simp only at rel ticksEq
          subst ticksEq
          cases outcome' <;> simp only [OutcomeRel] at rel
          obtain ⟨valueEq, valueIn, retainedRel⟩ := rel
          subst valueEq
          simp at found
          obtain ⟨a, materialized, rfl⟩ := found
          obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
            related_materializeWith respects limits limits' _ _ _ _ _ _ retainedRel
              (enteredRoom.shift enteredRel retainedRel) valueIn materialized
          refine ⟨{a' with state := {a'.state with control := .yielded (f plan), stack := stack.map (renameFrame f)}},
            ?_, aValue, aRemaining, aRel.heap, controlIn, rfl, stackIn, rfl⟩
          simp [materialized']
      | _ => simp at found
  | _ => simp [yieldedPlanWith] at found

end Obend.Core.Collect
