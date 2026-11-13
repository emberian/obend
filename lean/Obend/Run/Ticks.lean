module
/-
# Obend.Run.Ticks — Fuel Monotonicity (`runBounded_mono`), Linear-Time `deepenBounded`, and Cost-Indexed Completeness (`WS 27` `G1`)

Closes Gap `G1` (`PLAN.md` Part III & `METATHEORY.md` §3.1):
1. Proves `runBounded_mono` directly on `Obend.Core.Machine.runBounded`
   (`k ≤ k' → runBounded L k s = .finished v s' → runBounded L k' s = .finished v s'`), while
   importing `Obend.Core.MachineFast` so compiled code (`Ticks.c`) uses `@[csimp]` `runBoundedFast`.
2. Provides `deepenBounded L s k : Option (RuntimeValue × State)`, which runs `runBounded L k s` in a
   single linear $O(k)$ pass instead of quadratic `Judge.deepen` $O(k^2)$ replay, and proves that
   `deepenBounded` is both fuel-monotone (`deepenBounded_mono`) and extensionally equal to
   `Judge.deepen (deepenBounded L s) k` (`deepenBounded_eq_deepen`).
3. Proves the object-fragment tick bound (`fragment_within`) and cost-indexed ledger completeness
   (`fragment_cost_indexed_completeness` / `cost_indexed_completeness`) for bounded closures.
-/
public import Obend.Core.MachineFast
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Equiv.Demand
public import Obend.Judge.Class
public section

namespace Obend.Run.Ticks
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Proofs.Adequacy (rawRun)
open Obend.Equiv
open Obend.Equiv.Demand
set_option autoImplicit false

/-! ## 1. Direct Fuel Monotonicity (`runBounded_mono`) & Linear-Time `deepenBounded` -/

/-- The natural number a finished run returns, if it finished with one. -/
@[expose] def finishedNat : Outcome → Option Nat
  | .finished (.natural n) _ => some n
  | _ => none

/-- **Theorem (`runBounded_mono`, WS 27 G1)**:
Monotonicity of `runBounded` with respect to fuel budget `k ≤ k'`: if `runBounded L k s` finishes
with `(v, s')`, then running with any larger fuel budget `k' ≥ k` produces the exact same
`.finished v s'` outcome in a single $O(k')$ pass without quadratic `Judge.deepen` replay. -/
theorem runBounded_mono {L : Limits} {k k' : Nat} {s s' : State} {v : RuntimeValue}
    (h : runBounded L k s = .finished v s') (hle : k ≤ k') :
    runBounded L k' s = .finished v s' := by
  induction k generalizing k' s with
  | zero =>
    cases hc : s.control <;> simp [runBounded, hc] at h
    obtain ⟨rfl, rfl⟩ := h
    cases k' <;> simp [runBounded, step, hc]
  | succ k ih =>
    cases k' with
    | zero => omega
    | succ k' =>
      simp only [runBounded] at h ⊢
      cases hs : step L s with
      | finished v0 s0 => rw [hs] at h; exact h
      | divergent a s0 => rw [hs] at h; cases h
      | refused r s0 => rw [hs] at h; cases h
      | yielded p s0 => rw [hs] at h; cases h
      | suspended reason next =>
        cases reason with
        | ticks => rw [hs] at h; exact ih h (by omega)
        | capacity => rw [hs] at h; cases h

/-- Corollary: `finishedNat (runBounded L k s) = some n` is monotone in the tick budget `k ≤ k'`. -/
theorem finishedNat_mono {L : Limits} {k k' : Nat} {s : State} {n : Nat}
    (h : finishedNat (runBounded L k s) = some n) (hle : k ≤ k') :
    finishedNat (runBounded L k' s) = some n := by
  revert h
  cases hrun : runBounded L k s with
  | finished v s' =>
    cases v with
    | natural m =>
      simp only [finishedNat, Option.some.injEq]
      intro hm
      subst hm
      rw [runBounded_mono hrun hle]
    | _ => simp [finishedNat]
  | _ => simp [finishedNat]

/-- Single-pass $O(k)$ bounded execution extracting a finished `(RuntimeValue × State)`. -/
@[expose] def deepenBounded (L : Limits) (s : State) (k : Nat) : Option (RuntimeValue × State) :=
  match runBounded L k s with
  | .finished v s' => some (v, s')
  | _ => none

/-- **Theorem (`deepenBounded_mono`)**:
Because `runBounded` is fuel-monotone (`runBounded_mono`), `deepenBounded L s` is already monotone
in `k ≤ k'` without needing `Judge.deepen`'s $O(k^2)$ prefix loop. -/
theorem deepenBounded_mono (L : Limits) (s : State) {k k' : Nat} {res : RuntimeValue × State}
    (h : deepenBounded L s k = some res) (hle : k ≤ k') :
    deepenBounded L s k' = some res := by
  unfold deepenBounded at h ⊢
  revert h
  cases hrun : runBounded L k s with
  | finished v s' =>
    simp only [Option.some.injEq]
    intro heq
    subst heq
    rw [runBounded_mono hrun hle]
  | _ => simp

/-- If `deepenBounded L s k = none`, then for every `j ≤ k`, `deepenBounded L s j = none`. -/
theorem deepenBounded_none_of_le (L : Limits) (s : State) {j k : Nat}
    (hnone : deepenBounded L s k = none) (hle : j ≤ k) :
    deepenBounded L s j = none := by
  cases hj : deepenBounded L s j with
  | none => rfl
  | some res =>
    have hk := deepenBounded_mono L s hj hle
    rw [hnone] at hk
    cases hk

/-- **Theorem (`deepenBounded_eq_deepen`)**:
The single-pass linear $O(k)$ `deepenBounded L s k` produces the exact same result as the
quadratic $O(k^2)$ iterative deepening `Judge.deepen (deepenBounded L s) k` for every `k`. -/
theorem deepenBounded_eq_deepen (L : Limits) (s : State) (k : Nat) :
    Judge.deepen (deepenBounded L s) k = deepenBounded L s k := by
  have hiff : ∀ res, Judge.deepen (deepenBounded L s) k = some res ↔ deepenBounded L s k = some res := by
    intro res
    constructor
    · intro hd
      obtain ⟨i, hle, hi⟩ := Judge.deepen_some (deepenBounded L s) hd
      exact deepenBounded_mono L s hi hle
    · intro hb
      obtain ⟨b, hd⟩ := Judge.deepen_isSome (deepenBounded L s) hb
      obtain ⟨i, hle, hi⟩ := Judge.deepen_some (deepenBounded L s) hd
      have hb' := deepenBounded_mono L s hi hle
      rw [hb] at hb'
      injection hb' with hbe
      subst hbe
      exact hd
  cases hd : Judge.deepen (deepenBounded L s) k with
  | some res => exact ((hiff res).mp hd).symm
  | none =>
    cases hb : deepenBounded L s k with
    | none => rfl
    | some res =>
      have hd' := (hiff res).mpr hb
      rw [hd] at hd'
      cases hd'

/-! ## 2. Active-Transition Traces & Object-Fragment Tick Completeness -/

/-- The raw machine has completed `t` with `n` after `T` transitions. -/
@[expose] def Finishes (t : Term) (T n : Nat) : Prop :=
  (rawRun T (initial t)).control = .complete (.natural n)

/-- `T` is the first transition count at which `rawRun` completes `t` with `n`. -/
@[expose] def FirstFinish (t : Term) (T n : Nat) : Prop :=
  Finishes t T n ∧ ∀ T' < T, ∀ v, (rawRun T' (initial t)).control ≠ .complete v

/-- The object fragment: a selection from an object of literals and `self.m` fields, with distinct
names. -/
@[expose] def InFragment (t : Term) : Prop :=
  ∃ (fs : List (String × FE)) (x : String), t = .get (obj fs) x ∧ (fs.map Prod.fst).Nodup

/-- The tick bound on programs satisfying `P`: when the raw machine first completes a program in `P`
after `T` transitions, `T` is within `c` times its least clairvoyant cost, plus `d`. -/
@[expose] def TicksWithinDemandOn (P : Term → Prop) (c d : Nat) : Prop :=
  ∀ (t : Term), P t → ∀ (T n : Nat), FirstFinish t T n →
    ∀ k, CV t (.nat n) k → (∀ w j, CV t w j → k ≤ j) → T ≤ c * k + d

/-- Unconditional tick bound across all Core4 programs whose demand run exists. -/
@[expose] def TicksWithinDemand (c d : Nat) : Prop := TicksWithinDemandOn (fun _ => True) c d

/-- The same tick bound for the bounded machine under limits `L`, counted in `runBounded` ticks. -/
@[expose] def TicksWithinDemandUnder (L : Limits) (P : Term → Prop) (c d : Nat) : Prop :=
  ∀ (t : Term), P t → ∀ (T n : Nat), finishedNat (runBounded L T (initial t)) = some n →
    (∀ T' < T, finishedNat (runBounded L T' (initial t)) = none) →
    ∀ k, CV t (.nat n) k → (∀ w j, CV t w j → k ≤ j) → T ≤ c * k + d

/-- A state the machine still transitions from. -/
def Active (s : State) : Prop :=
  match s.control with
  | .evaluate _ _ | .enter _ | .returned _ => True
  | _ => False

/-- A state within the limits. -/
def Fits (L : Limits) (s : State) : Prop := s.heap.size ≤ L.heap ∧ s.stack.length ≤ L.stack

/-- `n` active transitions within the limits, from `s` to `s'`. -/
inductive Trace (L : Limits) : State → Nat → State → Prop where
  | refl (s : State) : Trace L s 0 s
  | cons {s s' : State} {n : Nat} : Active s → Fits L (stepRaw s) → Trace L (stepRaw s) n s' →
      Trace L s (n + 1) s'

private theorem Trace.next {L : Limits} {s s1 s' : State} {n : Nat} (a : Active s) (e : stepRaw s = s1)
    (f : Fits L s1) (t : Trace L s1 n s') : Trace L s (n + 1) s' := by
  subst e; exact .cons a f t

private theorem Trace.trans {L : Limits} {a b c : State} {n m : Nat} (t : Trace L a n b) (u : Trace L b m c) :
    Trace L a (n + m) c := by
  induction t with
  | refl => simpa using u
  | @cons s0 s1 k x f _ ih =>
    rw [show k + 1 + m = (k + m) + 1 by omega]
    exact .cons x f (ih u)

private theorem Trace.cast {L : Limits} {s s' : State} {n n' : Nat} (e : n = n') (t : Trace L s n s') :
    Trace L s n' s' := e ▸ t

private theorem step_active {L : Limits} {s : State} (a : Active s) (f : Fits L (stepRaw s)) :
    step L s = .suspended .ticks (stepRaw s) := by
  obtain ⟨h1, h2⟩ := f
  unfold step
  cases hc : s.control <;> simp [Active, hc] at a <;> simp [h1, h2]

/-- **`runBounded` composed along active transitions.** -/
theorem runBounded_trace {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') (j : Nat) :
    runBounded L (n + j) s = runBounded L j s' := by
  induction t with
  | refl => simp
  | @cons s0 s1 k a f _ ih =>
    rw [show k + 1 + j = (k + j) + 1 by omega]
    simp only [runBounded, step_active a f]
    exact ih

theorem runBounded_complete {L : Limits} {s : State} {v : RuntimeValue} (h : s.control = .complete v)
    (j : Nat) : runBounded L j s = .finished v s := by
  cases j <;> simp [runBounded, step, h]

/-- Fewer ticks than the trace's transitions leave the run suspended. -/
theorem runBounded_short {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') :
    ∀ j < n, ∃ r, runBounded L j s = .suspended .ticks r := by
  induction t with
  | refl => intro j h; omega
  | @cons s0 s1 k a f _ ih =>
    intro j hj
    cases j with
    | zero =>
      refine ⟨s0, ?_⟩
      simp only [runBounded]
      cases hc : s0.control <;> simp [Active, hc] at a ⊢
    | succ j =>
      simp only [runBounded, step_active a f]
      exact ih j (by omega)

private theorem rawRun_trace {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') : rawRun n s = s' := by
  induction t with
  | refl => rfl
  | cons _ _ _ ih => exact ih

private theorem rawRun_short {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') :
    ∀ j < n, Active (rawRun j s) := by
  induction t with
  | refl => intro j h; omega
  | @cons s0 s1 k a _ _ ih =>
    intro j hj
    cases j with
    | zero => exact a
    | succ j => exact ih j (by omega)

private theorem rawRun_complete {s : State} {v : RuntimeValue} (h : s.control = .complete v) :
    ∀ j, rawRun j s = s
  | 0 => rfl
  | j + 1 => by
    have e : stepRaw s = s := by
      obtain ⟨heap, control, stack⟩ := s
      simp only at h; subst h; rfl
    show rawRun j (stepRaw s) = s
    rw [e]; exact rawRun_complete h j

private theorem rawRun_stays {v : RuntimeValue} : ∀ (a : Nat) {s : State} {b : Nat},
    (rawRun a s).control = .complete v → a ≤ b → (rawRun b s).control = .complete v
  | 0, s, b, h, _ => by simp only [rawRun] at h; rw [rawRun_complete h b]; exact h
  | a + 1, s, b, h, le => by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact rawRun_stays a (s := stepRaw s) h (by omega)

/-- A bounded run that finished is a trace within the limits to a completed state. -/
theorem runBounded_finished_trace {L : Limits} : ∀ (T : Nat) {s s' : State} {v : RuntimeValue},
    runBounded L T s = .finished v s' → ∃ j ≤ T, Trace L s j s' ∧ s'.control = .complete v
  | 0, s, s', v, h => by
    cases hc : s.control <;> simp [runBounded, hc] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, by omega, .refl _, hc⟩
  | T + 1, s, s', v, h => by
    by_cases a : Active s
    · by_cases f : Fits L (stepRaw s)
      · simp only [runBounded, step_active a f] at h
        obtain ⟨j, hj, t, hc⟩ := runBounded_finished_trace T h
        exact ⟨j + 1, by omega, .cons a f t, hc⟩
      · unfold Fits at f
        have hs : step L s = .suspended .capacity s := by
          unfold step
          cases hc : s.control <;> simp [Active, hc] at a ⊢ <;> simp_all
        simp [runBounded, hs] at h
    · cases hc : s.control <;> simp [Active, hc] at a <;> simp [runBounded, step, hc] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by omega, .refl _, hc⟩

/-- **Limits only remove programs**: the raw demand tick bound holds under any capacity limits `L`. -/
theorem ticks_within_under (L : Limits) {P : Term → Prop} {c d : Nat} (h : TicksWithinDemandOn P c d) :
    TicksWithinDemandUnder L P c d := by
  intro t hP T n fin minimal k cv least
  have hfin : ∃ s', runBounded L T (initial t) = .finished (.natural n) s' := by
    revert fin
    cases runBounded L T (initial t) with
    | finished v s' => cases v <;> simp [finishedNat]
    | _ => simp [finishedNat]
  obtain ⟨s', hs'⟩ := hfin
  obtain ⟨j, hj, tr, hc⟩ := runBounded_finished_trace T hs'
  have hT : T ≤ j := by
    rcases Nat.lt_or_ge j T with lt | ge
    · have := minimal j lt
      rw [show j = j + 0 by omega, runBounded_trace tr, runBounded_complete hc] at this
      simp [finishedNat] at this
    · exact ge
  have first : FirstFinish t j n := by
    refine ⟨by rw [Finishes, rawRun_trace tr]; exact hc, fun T' lt v e => ?_⟩
    have a := rawRun_short tr T' lt
    simp [Active, e] at a
  have := h t hP j n first k cv least
  omega

private def addrs {α : Type} : Nat → List (String × α) → List (String × Address)
  | _, [] => []
  | b, f :: fs => (f.1, b) :: addrs (b + 1) fs

private theorem alloc_foldl (env : Environment) : ∀ (E : List (String × Term)) (h : List Cell)
    (acc : List (String × Address)),
    E.foldl (fun (prior : Array Cell × List (String × Address)) field =>
      (prior.1.push (.suspended ⟨field.2, env⟩), (field.1, prior.1.size) :: prior.2)) (h.toArray, acc) =
      ((h ++ E.map fun f => Cell.suspended ⟨f.2, env⟩).toArray, (addrs h.length E).reverse ++ acc)
  | [], h, acc => by simp [addrs]
  | f :: E, h, acc => by
    simp only [List.foldl_cons, List.push_toArray, List.size_toArray]
    refine (alloc_foldl env E (h ++ [.suspended ⟨f.2, env⟩]) ((f.1, h.length) :: acc)).trans ?_
    simp [addrs]

private theorem allocateFields_toArray (h : List Cell) (env : Environment) (E : List (String × Term)) :
    allocateFields h.toArray env E =
      ((h ++ E.map fun f => Cell.suspended ⟨f.2, env⟩).toArray, addrs h.length E) := by
  unfold allocateFields
  rw [alloc_foldl]
  simp

private def fieldEnv : Environment := [2, 1, 0]
private def fieldCell (f : String × FE) : Cell := .suspended ⟨f.2.at (.bound 1), fieldEnv⟩

private def pos : List (String × FE) → String → Nat
  | [], _ => 0
  | f :: fs, m => if f.1 == m then 0 else pos fs m + 1

private def recordValue (fs : List (String × FE)) : RuntimeValue := .record (addrs 3 fs)
private def knotBody (fs : List (String × FE)) : Term := .app (.app (objLam fs) (.bound 0)) (.record [])
private def knotCell (fs : List (String × FE)) : Cell := .cached ⟨knotBody fs, [0]⟩ (recordValue fs)
private def selfSuspended : Cell := .suspended ⟨.bound 0, [0]⟩
private def selfCached (fs : List (String × FE)) : Cell := .cached ⟨.bound 0, [0]⟩ (recordValue fs)
private def superCell : Cell := .suspended ⟨.record [], [0]⟩

private def templateHeap (fs : List (String × FE)) : List Cell :=
  knotCell fs :: selfSuspended :: superCell :: fs.map fieldCell

private theorem look_cons (f : String × FE) (fs : List (String × FE)) (m : String) :
    look (f :: fs) m = if f.1 == m then some f.2 else look fs m := by
  simp only [look, List.find?_cons]
  split <;> simp_all

private theorem look_pos {m : String} {e : FE} : ∀ {fs : List (String × FE)}, look fs m = some e →
    pos fs m < fs.length ∧ (fs.map fieldCell)[pos fs m]? = some (fieldCell (m, e))
  | [], h => by simp [look] at h
  | f :: fs, h => by
    rw [look_cons] at h
    by_cases hf : f.1 = m
    · simp only [hf, beq_self_eq_true, ite_true, Option.some.injEq] at h
      subst h
      obtain ⟨n, e⟩ := f
      simp only at hf
      subst hf
      simp [pos]
    · have hb : (f.1 == m) = false := by simpa using hf
      simp only [hb] at h
      obtain ⟨lt, get⟩ := look_pos h
      simp only [pos, hb]
      exact ⟨by simp; omega, by simpa using get⟩

private theorem find_addrs {m : String} {e : FE} : ∀ {fs : List (String × FE)} (b : Nat), look fs m = some e →
    (addrs b fs).find? (fun field => field.1 == m) = some (m, b + pos fs m)
  | [], _, h => by simp [look] at h
  | f :: fs, b, h => by
    rw [look_cons] at h
    by_cases hf : f.1 = m
    · simp [addrs, pos, hf]
    · have hb : (f.1 == m) = false := by simpa using hf
      simp only [hb] at h
      simp only [addrs, List.find?_cons, hb, pos]
      rw [find_addrs (b + 1) h]
      simp; omega

private theorem pos_inj {m m' : String} {e e' : FE} : ∀ {fs : List (String × FE)}, look fs m = some e →
    look fs m' = some e' → pos fs m = pos fs m' → m = m'
  | [], h, _, _ => by simp [look] at h
  | f :: fs, h, h', hp => by
    rw [look_cons] at h h'
    by_cases hf : f.1 = m <;> by_cases hf' : f.1 = m'
    · exact hf.symm.trans hf'
    · simp [pos, hf] at hp; exact hp
    · simp [pos, hf'] at hp; exact hp.symm
    · have hb : (f.1 == m) = false := by simpa using hf
      have hb' : (f.1 == m') = false := by simpa using hf'
      simp only [hb, hb'] at h h'
      simp [pos, hb, hb'] at hp
      exact pos_inj h h' (by omega)

private theorem addrs_entries (s : Term) : ∀ (b : Nat) (fs : List (String × FE)), addrs b (entries s fs) = addrs b fs
  | _, [] => rfl
  | b, f :: fs => by simp [entries, addrs]; exact addrs_entries s (b + 1) fs

private theorem entries_cells (fs : List (String × FE)) :
    (entries (.bound 1) fs).map (fun f => Cell.suspended ⟨f.2, fieldEnv⟩) = fs.map fieldCell := by
  simp [entries, fieldCell]

private theorem objLam_rename (fs : List (String × FE)) : (objLam fs).rename Nat.succ = objLam fs := by
  have := objLam_selfBody fs
  simp only [selfBody] at this
  injection this with h1 _
  injection h1

private theorem prefix_trace {L : Limits} {fs : List (String × FE)} {x : String} {e : FE}
    (hx : look fs x = some e) (hh : fs.length + 3 ≤ L.heap) (hs : 4 ≤ L.stack) :
    Trace L (initial (.get (obj fs) x)) 12 ⟨(templateHeap fs).toArray, .enter (3 + pos fs x), []⟩ := by
  refine .next (s1 := ⟨#[], .evaluate (obj fs) [], [.field x]⟩) (by simp [Active, initial])
    (by simp [stepRaw, initial]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.suspended ⟨knotBody fs, [0]⟩].toArray, .enter 0, [.field x]⟩) (by simp [Active])
    (by simp [stepRaw, obj, knotBody, objLam_rename, Term.rename]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩].toArray, .evaluate (knotBody fs) [0],
    [.update 0, .field x]⟩) (by simp [Active]) (by simp [stepRaw]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩].toArray, .evaluate (.app (objLam fs) (.bound 0)) [0],
    [.argument (.record []) [0], .update 0, .field x]⟩) (by simp [Active]) (by simp [stepRaw, knotBody])
    (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩].toArray, .evaluate (objLam fs) [0],
    [.argument (.bound 0) [0], .argument (.record []) [0], .update 0, .field x]⟩) (by simp [Active])
    (by simp [stepRaw]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩].toArray,
    .returned (.closure (.lam (.record (entries (.bound 1) fs))) [0]),
    [.argument (.bound 0) [0], .argument (.record []) [0], .update 0, .field x]⟩) (by simp [Active])
    (by simp [stepRaw, objLam]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩, selfSuspended].toArray,
    .evaluate (.lam (.record (entries (.bound 1) fs))) [1, 0],
    [.argument (.record []) [0], .update 0, .field x]⟩) (by simp [Active])
    (by simp [stepRaw, selfSuspended]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩, selfSuspended].toArray,
    .returned (.closure (.record (entries (.bound 1) fs)) [1, 0]),
    [.argument (.record []) [0], .update 0, .field x]⟩) (by simp [Active])
    (by simp [stepRaw]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨[Cell.evaluating ⟨knotBody fs, [0]⟩, selfSuspended, superCell].toArray,
    .evaluate (.record (entries (.bound 1) fs)) fieldEnv, [.update 0, .field x]⟩) (by simp [Active])
    (by simp [stepRaw, superCell, fieldEnv]) (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨([Cell.evaluating ⟨knotBody fs, [0]⟩, selfSuspended, superCell] ++ fs.map fieldCell).toArray,
    .returned (recordValue fs), [.update 0, .field x]⟩) (by simp [Active])
    (by simp only [stepRaw, allocateFields_toArray, entries_cells, addrs_entries, recordValue]; rfl)
    (by simp [Fits]; omega) ?_
  refine .next (s1 := ⟨(templateHeap fs).toArray, .returned (recordValue fs), [.field x]⟩) (by simp [Active])
    (by simp [stepRaw, templateHeap, knotCell]) (by simp [Fits, templateHeap]; omega) ?_
  refine .next (s1 := ⟨(templateHeap fs).toArray, .enter (3 + pos fs x), []⟩) (by simp [Active])
    (by simp [stepRaw, recordValue, find_addrs 3 hx]) (by simp [Fits, templateHeap]; omega) ?_
  exact .refl _

private def selfExtra : Cell → Nat
  | .suspended _ => 3
  | _ => 0

private theorem set_self {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  have lt : i < l.length := by
    rcases Nat.lt_or_ge i l.length with lt | ge
    · exact lt
    · rw [List.getElem?_eq_none ge] at h; cases h
  rw [List.getElem?_eq_getElem lt] at h
  cases h
  exact List.set_getElem_self lt

private theorem self_trace {L : Limits} {fs : List (String × FE)} {hq : List Cell} {rest : List Frame} {c1 : Cell}
    (h0 : hq[0]? = some (knotCell fs)) (h1 : hq[1]? = some c1) (hc1 : c1 = selfSuspended ∨ c1 = selfCached fs)
    (hl : hq.length ≤ L.heap) (hs : rest.length + 1 ≤ L.stack) :
    Trace L ⟨hq.toArray, .enter 1, rest⟩ (selfExtra c1 + 1)
      ⟨(hq.set 1 (selfCached fs)).toArray, .returned (recordValue fs), rest⟩ := by
  rcases hc1 with rfl | rfl
  · have ev : (hq.set 1 (.evaluating ⟨.bound 0, [0]⟩))[0]? = some (knotCell fs) := by
      rw [List.getElem?_set_ne (by omega)]; exact h0
    have ev1 : (hq.set 1 (.evaluating ⟨.bound 0, [0]⟩))[1]? = some (.evaluating ⟨.bound 0, [0]⟩) := by
      rw [List.getElem?_set_self']; simp [h1]
    refine .next (s1 := ⟨(hq.set 1 (.evaluating ⟨.bound 0, [0]⟩)).toArray, .evaluate (.bound 0) [0], .update 1 :: rest⟩)
      (by simp [Active]) (by simp [stepRaw, h1, selfSuspended]) (by simp [Fits]; omega) ?_
    refine .next (s1 := ⟨(hq.set 1 (.evaluating ⟨.bound 0, [0]⟩)).toArray, .enter 0, .update 1 :: rest⟩)
      (by simp [Active]) (by simp [stepRaw]) (by simp [Fits]; omega) ?_
    refine .next (s1 := ⟨(hq.set 1 (.evaluating ⟨.bound 0, [0]⟩)).toArray, .returned (recordValue fs), .update 1 :: rest⟩)
      (by simp [Active]) (by simp [stepRaw, ev, knotCell]) (by simp [Fits]; omega) ?_
    refine .next (s1 := ⟨(hq.set 1 (selfCached fs)).toArray, .returned (recordValue fs), rest⟩)
      (by simp [Active]) (by simp [stepRaw, ev1, selfCached, List.set_set]) (by simp [Fits]; omega) ?_
    exact .refl _
  · refine .next (s1 := ⟨(hq.set 1 (selfCached fs)).toArray, .returned (recordValue fs), rest⟩)
      (by simp [Active]) (by rw [set_self h1]; simp [stepRaw, h1, selfCached]) (by simp [Fits]; omega) ?_
    exact .refl _

private theorem chase_look {fs : List (String × FE)} {k : Nat} {m : String} {p : Nat × Nat}
    (h : chase fs k m = some p) : ∃ e, look fs m = some e := by
  cases k with
  | zero => simp [chase] at h
  | succ k =>
    simp only [chase] at h
    split at h
    · exact ⟨_, by assumption⟩
    · exact ⟨_, by assumption⟩
    · cases h

private theorem force_trace {L : Limits} {fs : List (String × FE)} : ∀ (k : Nat) {z : String} {u d : Nat},
    chase fs k z = some (u, d) → ∀ {hp : List Cell} {stk : List Frame} {c1 : Cell},
    hp[0]? = some (knotCell fs) → hp[1]? = some c1 → (c1 = selfSuspended ∨ c1 = selfCached fs) →
    (∀ i zi ei, walk fs i z = some zi → look fs zi = some ei → hp[3 + pos fs zi]? = some (fieldCell (zi, ei))) →
    hp.length ≤ L.heap → stk.length + d + 3 ≤ L.stack →
    ∃ hp' : List Cell, Trace L ⟨hp.toArray, .enter (3 + pos fs z), stk⟩
        (3 + 6 * d + (if d = 0 then 0 else selfExtra c1)) ⟨hp'.toArray, .returned (.natural u), stk⟩ ∧
      hp'.length = hp.length ∧ hp'[0]? = some (knotCell fs) ∧
      hp'[1]? = (if d = 0 then some c1 else some (selfCached fs)) ∧
      (∀ i zi, walk fs i z = some zi → ∃ o, hp'[3 + pos fs zi]? = some (.cached o (.natural u))) ∧
      (∀ a, a ≠ 1 → (∀ i zi, walk fs i z = some zi → a ≠ 3 + pos fs zi) → hp'[a]? = hp[a]?)
  | 0, z, u, d, hc, _, _, _, _, _, _, _, _, _ => by simp [chase] at hc
  | k + 1, z, u, d, hc, hp, stk, c1, h0, h1, hc1, hpath, hl, hs => by
    have hc' := hc
    simp only [chase] at hc'
    split at hc'
    · rename_i v hlz
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨hv, hd⟩ := hc'
      subst v; subst d
      have hz := hpath 0 z (.lit u) rfl hlz
      simp only [fieldCell, FE.at] at hz
      have walk0 : ∀ i zi, walk fs i z = some zi → i = 0 ∧ zi = z := by
        intro i zi hw
        cases i with
        | zero => simp [walk] at hw; exact ⟨rfl, hw.symm⟩
        | succ i => simp [walk, hlz] at hw
      refine ⟨hp.set (3 + pos fs z) (.cached ⟨.nat u, fieldEnv⟩ (.natural u)), ?_, by simp, ?_, ?_, ?_, ?_⟩
      · refine .next (s1 := ⟨(hp.set (3 + pos fs z) (.evaluating ⟨.nat u, fieldEnv⟩)).toArray,
          .evaluate (.nat u) fieldEnv, .update (3 + pos fs z) :: stk⟩)
          (by simp [Active]) (by simp [stepRaw, hz]) (by simp [Fits]; omega) ?_
        refine .next (s1 := ⟨(hp.set (3 + pos fs z) (.evaluating ⟨.nat u, fieldEnv⟩)).toArray,
          .returned (.natural u), .update (3 + pos fs z) :: stk⟩)
          (by simp [Active]) (by simp [stepRaw]) (by simp [Fits]; omega) ?_
        refine .next (s1 := ⟨(hp.set (3 + pos fs z) (.cached ⟨.nat u, fieldEnv⟩ (.natural u))).toArray,
          .returned (.natural u), stk⟩)
          (by simp [Active]) (by simp [stepRaw, List.getElem?_set_self', hz, List.set_set])
          (by simp [Fits]; omega) ?_
        exact .refl _
      · rw [List.getElem?_set_ne (by omega)]; exact h0
      · rw [List.getElem?_set_ne (by omega)]; simpa using h1
      · intro i zi hw
        obtain ⟨rfl, rfl⟩ := walk0 i zi hw
        exact ⟨⟨.nat u, fieldEnv⟩, by rw [List.getElem?_set_self']; simp [hz]⟩
      · intro a _ hn
        rw [List.getElem?_set_ne (Ne.symm (hn 0 z rfl))]
    · rename_i m hlz
      obtain ⟨⟨u', d'⟩, hcm, he⟩ := Option.map_eq_some_iff.1 hc'
      simp only [Prod.mk.injEq] at he
      obtain ⟨hv, hd⟩ := he
      subst u'; subst d
      obtain ⟨em, hlm⟩ := chase_look hcm
      have hz := hpath 0 z (.ref m) rfl hlz
      simp only [fieldCell, FE.at] at hz
      have walkm : ∀ i, walk fs (i + 1) z = walk fs i m := by intro i; simp [walk, hlz]
      have off : ∀ i zi, walk fs i m = some zi → 3 + pos fs zi ≠ 3 + pos fs z := by
        intro i zi hw he
        have hlzi : ∃ e, look fs zi = some e := by
          obtain ⟨⟨zd, hzd, hld⟩, refs⟩ := chase_walk hcm
          rcases Nat.lt_or_ge i d' with lt | ge
          · obtain ⟨z', m', h1', h2'⟩ := refs i lt; rw [hw] at h1'; cases h1'; exact ⟨_, h2'⟩
          · rcases Nat.lt_or_ge d' i with lt | ge'
            · have := walk_beyond hzd hld (i - d' - 1)
              rw [show d' + (i - d' - 1) + 1 = i by omega, hw] at this; cases this
            · rw [show i = d' by omega, hzd] at hw; cases hw; exact ⟨_, hld⟩
        obtain ⟨ezi, hlzi⟩ := hlzi
        have eq := pos_inj hlzi hlz (by omega)
        subst eq
        have := chase_walk_injective hc (i := i + 1) (j := 0) (by rw [walkm]; exact hw) rfl
        omega
      have hlen1 : 1 < hp.length := by
        rcases Nat.lt_or_ge 1 hp.length with lt | ge
        · exact lt
        · rw [List.getElem?_eq_none ge] at h1; cases h1
      let a := 3 + pos fs z
      let ev : Cell := .evaluating ⟨.get (.bound 1) m, fieldEnv⟩
      let hpz := hp.set a ev
      let hp1 := hpz.set 1 (selfCached fs)
      have hpz0 : hpz[0]? = some (knotCell fs) := by
        simp only [hpz]; rw [List.getElem?_set_ne (by omega)]; exact h0
      have hpz1 : hpz[1]? = some c1 := by
        simp only [hpz]; rw [List.getElem?_set_ne (by omega)]; exact h1
      have hp1a : hp1[a]? = some ev := by
        simp only [hp1, hpz]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self']; simp [a, hz]
      obtain ⟨hp2, t2, len2, h20, h21, cached2, frame2⟩ := force_trace k hcm (hp := hp1)
        (stk := .update a :: stk) (c1 := selfCached fs)
        (by simp only [hp1]; rw [List.getElem?_set_ne (by omega)]; exact hpz0)
        (by simp only [hp1]; rw [List.getElem?_set_self']; simp [hpz, hlen1])
        (.inr rfl)
        (by
          intro i zi ei hw hle
          simp only [hp1, hpz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (off i zi hw).symm]
          exact hpath (i + 1) zi ei (by rw [walkm]; exact hw) hle)
        (by simp [hp1, hpz]; omega) (by simp; omega)
      have hp2a : hp2[a]? = some ev := by
        rw [frame2 a (by omega) (fun i zi hw => (off i zi hw).symm)]; exact hp1a
      refine ⟨hp2.set a (.cached ⟨.get (.bound 1) m, fieldEnv⟩ (.natural u)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have t1 : Trace L ⟨hp.toArray, .enter a, stk⟩ 3 ⟨hpz.toArray, .enter 1, .field m :: .update a :: stk⟩ := by
          refine .next (s1 := ⟨hpz.toArray, .evaluate (.get (.bound 1) m) fieldEnv, .update a :: stk⟩)
            (by simp [Active]) (by simp [stepRaw, a, hpz, ev, hz]) (by simp [Fits, hpz]; omega) ?_
          refine .next (s1 := ⟨hpz.toArray, .evaluate (.bound 1) fieldEnv, .field m :: .update a :: stk⟩)
            (by simp [Active]) (by simp [stepRaw]) (by simp [Fits, hpz]; omega) ?_
          refine .next (s1 := ⟨hpz.toArray, .enter 1, .field m :: .update a :: stk⟩)
            (by simp [Active]) (by simp [stepRaw, fieldEnv]) (by simp [Fits, hpz]; omega) ?_
          exact .refl _
        have ts := self_trace (L := L) (rest := .field m :: .update a :: stk) hpz0 hpz1 hc1
          (by simp [hpz]; omega) (by simp; omega)
        have tsel : Trace L ⟨hp1.toArray, .returned (recordValue fs), .field m :: .update a :: stk⟩ 1
            ⟨hp1.toArray, .enter (3 + pos fs m), .update a :: stk⟩ := by
          refine .next (s1 := ⟨hp1.toArray, .enter (3 + pos fs m), .update a :: stk⟩)
            (by simp [Active]) (by simp [stepRaw, recordValue, find_addrs 3 hlm])
            (by simp [Fits, hp1, hpz]; omega) ?_
          exact .refl _
        have tu : Trace L ⟨hp2.toArray, .returned (.natural u), .update a :: stk⟩ 1
            ⟨(hp2.set a (.cached ⟨.get (.bound 1) m, fieldEnv⟩ (.natural u))).toArray, .returned (.natural u), stk⟩ := by
          refine .next (s1 := ⟨(hp2.set a (.cached ⟨.get (.bound 1) m, fieldEnv⟩ (.natural u))).toArray,
            .returned (.natural u), stk⟩) (by simp [Active]) (by simp [stepRaw, hp2a, ev])
            (by simp [Fits, len2, hp1, hpz]; omega) ?_
          exact .refl _
        refine Trace.cast ?_ ((((t1.trans ts).trans tsel).trans t2).trans tu)
        simp [selfExtra, selfCached]
        omega
      · simp [len2, hp1, hpz]
      · rw [List.getElem?_set_ne (by omega)]; exact h20
      · rw [List.getElem?_set_ne (by omega), h21]; simp
      · intro i zi hw
        cases i with
        | zero =>
          simp [walk] at hw; subst hw
          exact ⟨⟨.get (.bound 1) m, fieldEnv⟩, by rw [List.getElem?_set_self']; simp [hp2a]⟩
        | succ i =>
          rw [walkm] at hw
          obtain ⟨o, ho⟩ := cached2 i zi hw
          exact ⟨o, by rw [List.getElem?_set_ne (off i zi hw).symm]; exact ho⟩
      · intro b hb hn
        have hba : a ≠ b := Ne.symm (hn 0 z rfl)
        rw [List.getElem?_set_ne hba, frame2 b hb (fun i zi hw => hn (i + 1) zi (by rw [walkm]; exact hw))]
        simp only [hp1, hpz]
        rw [List.getElem?_set_ne (Ne.symm hb), List.getElem?_set_ne hba]
    · cases hc'

/-- The run's length: 16 transitions for a literal, `19 + 6d` for a chase of `d ≥ 1` selections. -/
def fragmentTicks (d : Nat) : Nat := if d = 0 then 16 else 19 + 6 * d
private def fragmentLimits (fs : List (String × FE)) : Limits := ⟨fs.length + 3, fs.length + 3⟩

private theorem rest_trace {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) (hh : fs.length + 3 ≤ L.heap) (hs : fs.length + 3 ≤ L.stack) :
    ∃ hp : List Cell, Trace L ⟨(templateHeap fs).toArray, .enter (3 + pos fs x), []⟩ (fragmentTicks d - 12)
        ⟨hp.toArray, .complete (.natural u), []⟩ ∧
      hp.length = fs.length + 3 ∧
      (∀ i zi, walk fs i x = some zi → ∃ o, hp[3 + pos fs zi]? = some (.cached o (.natural u))) ∧
      (∀ a, a ≠ 1 → (∀ i zi, walk fs i x = some zi → a ≠ 3 + pos fs zi) → hp[a]? = (templateHeap fs)[a]?) := by
  have short := chase_short hc
  obtain ⟨hp, t2, len, _, _, cached, frame⟩ := force_trace (L := L) k hc (hp := templateHeap fs) (stk := [])
    (c1 := selfSuspended) (by simp [templateHeap]) (by simp [templateHeap]) (.inl rfl)
    (by
      intro i zi ei _ hl
      have := (look_pos hl).2
      rw [show 3 + pos fs zi = pos fs zi + 3 by omega]
      simpa only [templateHeap, List.getElem?_cons_succ] using this)
    (by simp [templateHeap]; omega) (by simp; omega)
  refine ⟨hp, ?_, by simp [len, templateHeap], cached, frame⟩
  have t3 : Trace L ⟨hp.toArray, .returned (.natural u), []⟩ 1 ⟨hp.toArray, .complete (.natural u), []⟩ :=
    .next (by simp [Active]) (by simp [stepRaw]) (by simp [Fits, len, templateHeap]; omega) (.refl _)
  refine Trace.cast ?_ (t2.trans t3)
  unfold fragmentTicks
  split <;> simp_all [selfExtra, selfSuspended] <;> omega

private theorem fragment_trace {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) (hh : fs.length + 3 ≤ L.heap) (hs : fs.length + 3 ≤ L.stack) :
    ∃ hp : List Cell, Trace L (initial (.get (obj fs) x)) (fragmentTicks d)
        ⟨hp.toArray, .complete (.natural u), []⟩ := by
  obtain ⟨ex, hx⟩ := chase_look hc
  have short := chase_short hc
  obtain ⟨hp, t2, _⟩ := rest_trace hc hh hs
  refine ⟨hp, Trace.cast ?_ ((prefix_trace (L := L) hx hh (by omega)).trans t2)⟩
  unfold fragmentTicks; split <;> omega

/-- **Exact fragment bounded-execution characterization**: with at least `fragmentTicks d` ticks,
`runBounded` finishes with the chase's value; with fewer ticks, it suspends on `.ticks`. -/
theorem fragment_run {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) (hh : fs.length + 3 ≤ L.heap) (hs : fs.length + 3 ≤ L.stack) :
    (∀ T, fragmentTicks d ≤ T → ∃ s, runBounded L T (initial (.get (obj fs) x)) = .finished (.natural u) s) ∧
      (∀ T, T < fragmentTicks d → ∃ s, runBounded L T (initial (.get (obj fs) x)) = .suspended .ticks s) := by
  obtain ⟨hp, t⟩ := fragment_trace hc hh hs
  refine ⟨fun T le => ⟨⟨hp.toArray, .complete (.natural u), []⟩, ?_⟩, runBounded_short t⟩
  rw [show T = fragmentTicks d + (T - fragmentTicks d) by omega, runBounded_trace t]
  exact runBounded_complete rfl _

private theorem hasRef_of_look {fs : List (String × FE)} {z m : String} (h : look fs z = some (.ref m)) :
    hasRef fs = true := by
  obtain ⟨f, hf, he⟩ := Option.map_eq_some_iff.1 h
  simp only [hasRef, List.any_eq_true]
  exact ⟨f, List.mem_of_find?_eq_some hf, by rw [he]⟩

private theorem fragment_ticks {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) :
    headCost fs + 2 * d + 2 ≤ fragmentTicks d ∧ fragmentTicks d ≤ 4 * (headCost fs + 2 * d + 2) := by
  have hhead : 2 ≤ headCost fs ∧ headCost fs ≤ 3 := by unfold headCost; split <;> omega
  by_cases hd : d = 0
  · subst hd; simp only [fragmentTicks, ite_true]; omega
  · have : hasRef fs = true := by
      cases k with
      | zero => simp [chase] at hc
      | succ k =>
        simp only [chase] at hc
        split at hc
        · simp only [Option.some.injEq, Prod.mk.injEq] at hc; omega
        · rename_i m hl; exact hasRef_of_look hl
        · cases hc
    have h3 : headCost fs = 3 := by simp [headCost, this]
    simp only [fragmentTicks, hd, ite_false, h3]; omega

private theorem fragment_first {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) :
    FirstFinish (.get (obj fs) x) (fragmentTicks d) u := by
  obtain ⟨hp, t⟩ := fragment_trace (L := fragmentLimits fs) hc (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨by rw [Finishes, rawRun_trace t], fun T' lt v e => ?_⟩
  have a := rawRun_short t T' lt
  simp [Active, e] at a

/-- **Within four times the demand, the raw machine has completed** with the demand's value. -/
theorem fragment_within {fs : List (String × FE)} {x : String} {u n : Nat}
    (hd : demand fs x = some (u, n)) {T : Nat} (hT : 4 * n ≤ T) : Finishes (.get (obj fs) x) T u := by
  obtain ⟨⟨u', d⟩, hc, he⟩ := Option.map_eq_some_iff.1 hd
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact rawRun_stays _ (fragment_first hc).1 (Nat.le_trans (fragment_ticks hc).2 hT)

/-! ## 3. Cost-Indexed Run Ledgers & Fragment Completeness -/

/-- A machine cell stands for an approximant's entry. -/
inductive CellFor : Cell → Term → Prop where
  | pending (o : Closure) : CellFor (.suspended o) skipped
  | forcing (o : Closure) : CellFor (.evaluating o) skipped
  | literal (env : Environment) (n : Nat) : CellFor (.suspended ⟨.nat n, env⟩) (.nat n)
  | cached (o : Closure) (n : Nat) : CellFor (.cached o (.natural n)) (.nat n)

/-- The heap stands for the approximant: the `i`-th named cell for the `i`-th entry. -/
def HeapFor (heap : Array Cell) (cells : List (String × Address)) (wave : List (String × Term)) : Prop :=
  cells.length = wave.length ∧ ∀ (i : Nat) (c : String × Address) (w : String × Term),
    cells[i]? = some c → wave[i]? = some w → c.1 = w.1 ∧ ∃ cell, heap[c.2]? = some cell ∧ CellFor cell w.2

/-- A run from a state, cut into segments charged against the clairvoyant cost. -/
inductive Ledger (L : Limits) (c : Nat) (cells : List (String × Address))
    (Approximant : List (String × Term) → Prop) : State → Nat → Nat → Prop where
  | done {s : State} {n : Nat} : s.control = .complete (.natural n) → Ledger L c cells Approximant s 0 0
  | segment {s s' : State} {n j T K : Nat} (wave : List (String × Term)) :
      Trace L s n s' → n ≤ c * j → Approximant wave → HeapFor s'.heap cells wave →
      Ledger L c cells Approximant s' T K → Ledger L c cells Approximant s (n + T) (j + K)

/-- A cost-indexed ledger of the machine run from `t` against the approximants of `t`'s knot. -/
structure CostIndexedRun (c : Nat) (t : Term) where
  cost : Nat
  charged_real : ∃ v, CV t v cost
  charged_least : ∀ w j, CV t w j → cost ≤ j
  cells : List (String × Address)
  Approximant : List (String × Term) → Prop
  bound : Limits
  ticks : Nat
  ledger : Ledger bound c cells Approximant (initial t) ticks cost

/-- Every `Ledger` composes into a single `Trace` bounded by `c * K` active transitions ending in a
completed natural value. -/
theorem Ledger.run {L : Limits} {c : Nat} {cells : List (String × Address)} {A : List (String × Term) → Prop}
    {s : State} {T K : Nat} (h : Ledger L c cells A s T K) :
    T ≤ c * K ∧ ∃ s' n, Trace L s T s' ∧ s'.control = .complete (.natural n) := by
  induction h with
  | @done s n hc => exact ⟨by omega, s, n, .refl s, hc⟩
  | @segment s s' n j T K _ tr le _ _ _ ih =>
    obtain ⟨le', s'', n', tr', hc⟩ := ih
    exact ⟨by rw [Nat.mul_add]; omega, s'', n', tr.trans tr', hc⟩

/-- **From ledgers to the demand tick bound**: if every program in `P` that completes with a
clairvoyant derivation has a `CostIndexedRun c`, its transition count is within `c` times its least
clairvoyant cost. -/
theorem ticks_within_of_runs {P : Term → Prop} {c : Nat}
    (h : ∀ t, P t → ∀ T n, FirstFinish t T n → ∀ v k, CV t v k → Nonempty (CostIndexedRun c t)) :
    TicksWithinDemandOn P c 0 := by
  intro t hP T n first k cv _
  obtain ⟨R⟩ := h t hP T n first _ k cv
  obtain ⟨le, s', n', tr, hc⟩ := R.ledger.run
  have hT : T ≤ R.ticks := by
    rcases Nat.lt_or_ge R.ticks T with lt | ge
    · exact absurd (by rw [rawRun_trace tr]; exact hc) (first.2 _ lt (.natural n'))
    · exact ge
  have := Nat.mul_le_mul_left c (R.charged_least _ _ cv)
  omega

private def FragmentWave (fs : List (String × FE)) (w : List (String × Term)) : Prop :=
  ∃ κ, Good fs κ ∧ w = approxL κ fs

private theorem addrs_length {α : Type} : ∀ (b : Nat) (l : List (String × α)), (addrs b l).length = l.length
  | _, [] => rfl
  | b, _ :: l => by simp [addrs, addrs_length (b + 1) l]

private theorem addrs_get {α : Type} : ∀ (l : List (String × α)) (b i : Nat),
    (addrs b l)[i]? = (l[i]?).map (fun f => (f.1, b + i))
  | [], _, _ => by simp [addrs]
  | _ :: _, _, 0 => by simp [addrs]
  | _ :: l, b, i + 1 => by
    simp only [addrs, List.getElem?_cons_succ, addrs_get l (b + 1) i]
    cases l[i]? <;> simp; omega

private theorem pos_index {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) :
    ∀ {i : Nat} {f : String × FE}, fs[i]? = some f → pos fs f.1 = i := by
  induction fs with
  | nil => intro i f h; simp at h
  | cons g fs ih =>
    intro i f h
    simp only [List.map_cons, List.nodup_cons] at nd
    cases i with
    | zero => simp at h; subst h; simp [pos]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hne : (g.1 == f.1) = false := by
        have := List.mem_map_of_mem (f := Prod.fst) (List.mem_of_getElem? h)
        simp only [beq_eq_false_iff_ne]; intro e; exact nd.1 (e ▸ this)
      simp only [pos, hne]
      rw [ih nd.2 h]; rfl

private theorem chase_suffix {fs : List (String × FE)} {u : Nat} : ∀ (i : Nat) {k : Nat} {x z : String} {d : Nat},
    chase fs k x = some (u, d) → walk fs i x = some z → ∃ k' d', chase fs k' z = some (u, d')
  | 0, k, x, z, d, hc, hw => by simp [walk] at hw; subst hw; exact ⟨k, d, hc⟩
  | i + 1, k, x, z, d, hc, hw => by
    cases k with
    | zero => simp [chase] at hc
    | succ k =>
      simp only [walk] at hw
      simp only [chase] at hc
      split at hw
      · rename_i m hl
        simp only [hl] at hc
        obtain ⟨⟨u', d'⟩, hcm, he⟩ := Option.map_eq_some_iff.1 hc
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, _⟩ := he
        exact chase_suffix i hcm hw
      · cases hw

private theorem walk_look {fs : List (String × FE)} {k : Nat} {x : String} {u d : Nat}
    (hc : chase fs k x = some (u, d)) {i : Nat} {z : String} (hw : walk fs i x = some z) :
    ∃ e, look fs z = some e := by
  obtain ⟨k', d', h'⟩ := chase_suffix i hc hw
  exact chase_look h'

private theorem chase_lit {fs : List (String × FE)} {k : Nat} {z : String} {u d v : Nat}
    (hc : chase fs k z = some (u, d)) (hl : look fs z = some (.lit v)) : v = u := by
  cases k with
  | zero => simp [chase] at hc
  | succ k => simp [chase, hl] at hc; exact hc.1

private theorem lookup_names (u : Nat) (n : String) : ∀ (names : List String),
    (names.map fun z => (z, u)).lookup n = if n ∈ names then some u else none
  | [] => by simp
  | z :: names => by
    simp only [List.map_cons, List.lookup, List.mem_cons]
    by_cases h : n = z
    · subst h; simp
    · have hb : (n == z) = false := by simpa using h
      simp only [hb, h, false_or]
      exact lookup_names u n names

private theorem heapFor_template (fs : List (String × FE)) :
    HeapFor (templateHeap fs).toArray (addrs 3 fs) (approxL [] fs) := by
  refine ⟨by simp [addrs_length, approxL], ?_⟩
  intro i c w hc hw
  rw [addrs_get] at hc
  simp only [approxL, List.getElem?_map] at hw
  cases hf : fs[i]? with
  | none => simp [hf] at hc
  | some f =>
    simp only [hf, Option.map_some, Option.some.injEq] at hc hw
    subst hc hw
    refine ⟨rfl, fieldCell f, ?_, ?_⟩
    · rw [List.getElem?_toArray, show 3 + i = i + 3 by omega]
      simp [templateHeap, hf]
    · obtain ⟨n, e⟩ := f
      cases e with
      | lit v => exact .literal _ v
      | ref m => simpa [ent, fieldCell, FE.at] using CellFor.pending ⟨.get (.bound 1) m, fieldEnv⟩

private theorem heapFor_final {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) {hp : List Cell}
    (cached : ∀ i zi, walk fs i x = some zi → ∃ o, hp[3 + pos fs zi]? = some (.cached o (.natural u)))
    (frame : ∀ a, a ≠ 1 → (∀ i zi, walk fs i x = some zi → a ≠ 3 + pos fs zi) → hp[a]? = (templateHeap fs)[a]?) :
    HeapFor hp.toArray (addrs 3 fs)
      (approxL (((List.range (d + 1)).filterMap fun j => walk fs j x).map fun z => (z, u)) fs) := by
  refine ⟨by simp [addrs_length, approxL], ?_⟩
  intro i c w hc' hw
  rw [addrs_get] at hc'
  simp only [approxL, List.getElem?_map] at hw
  cases hf : fs[i]? with
  | none => simp [hf] at hc'
  | some f =>
    simp only [hf, Option.map_some, Option.some.injEq] at hc' hw
    subst hc' hw
    refine ⟨rfl, ?_⟩
    have hpos := pos_index nd hf
    have hlf : look fs f.1 = some f.2 := look_of_mem nd f (List.mem_of_getElem? hf)
    obtain ⟨⟨zd, hzd, hld⟩, _⟩ := chase_walk hc
    by_cases on : ∃ j, walk fs j x = some f.1
    · obtain ⟨j, hj⟩ := on
      obtain ⟨o, ho⟩ := cached j f.1 hj
      rw [hpos] at ho
      refine ⟨_, by simpa using ho, ?_⟩
      have hj' : j < d + 1 := by
        rcases Nat.lt_or_ge j (d + 1) with lt | ge
        · exact lt
        · have := walk_beyond hzd hld (j - d - 1)
          rw [show d + (j - d - 1) + 1 = j by omega, hj] at this; cases this
      obtain ⟨n, e⟩ := f
      cases e with
      | lit v =>
        obtain ⟨k', d', h'⟩ := chase_suffix j hc hj
        have := chase_lit h' hlf
        subst this
        exact .cached o v
      | ref m =>
        have hmem : n ∈ (List.range (d + 1)).filterMap (fun j => walk fs j x) :=
          List.mem_filterMap.2 ⟨j, List.mem_range.2 hj', hj⟩
        simp only [ent, lookup_names, hmem, ite_true]
        exact .cached o u
    · have off : ∀ j zi, walk fs j x = some zi → 3 + i ≠ 3 + pos fs zi := by
        intro j zi hj he
        obtain ⟨e, hl⟩ := walk_look hc hj
        have := pos_inj hl hlf (by omega)
        subst this
        exact on ⟨j, hj⟩
      have hcell := frame (3 + i) (by omega) off
      rw [show 3 + i = i + 3 by omega] at hcell
      simp only [templateHeap, List.getElem?_cons_succ, List.getElem?_map, hf, Option.map_some] at hcell
      refine ⟨fieldCell f, by rw [List.getElem?_toArray, show 3 + i = i + 3 by omega, hcell], ?_⟩
      obtain ⟨n, e⟩ := f
      cases e with
      | lit v => exact .literal _ v
      | ref m =>
        have hmem : n ∉ (List.range (d + 1)).filterMap (fun j => walk fs j x) := by
          intro h
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 h
          exact on ⟨j, hj⟩
        simp only [ent, lookup_names, hmem, ite_false]
        exact .pending _

private theorem fragment_cost_indexed {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    {x : String} {u n : Nat} (hd : demand fs x = some (u, n)) :
    Nonempty (CostIndexedRun 4 (.get (obj fs) x)) := by
  obtain ⟨⟨u', d⟩, hc, he⟩ := Option.map_eq_some_iff.1 hd
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨ex, hx⟩ := chase_look hc
  have short := chase_short hc
  have hh : fs.length + 3 ≤ (fragmentLimits fs).heap := Nat.le_refl _
  have t1 := prefix_trace (L := fragmentLimits fs) hx hh (by simp only [fragmentLimits]; omega)
  obtain ⟨hp, t2, _, cached, frame⟩ := rest_trace (L := fragmentLimits fs) hc hh (Nat.le_refl _)
  have ticks := fragment_ticks hc
  have hhead : 2 ≤ headCost fs := by unfold headCost; split <;> omega
  let κ := ((List.range (d + 1)).filterMap fun j => walk fs j x).map fun z => (z, u')
  have good : Good fs κ := by
    intro m v hl
    simp only [κ, lookup_names] at hl
    split at hl
    · rename_i hm
      simp only [Option.some.injEq] at hl; subst hl
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 hm
      exact chase_suffix j hc hj
    · cases hl
  have ledger : Ledger (fragmentLimits fs) 4 (addrs 3 fs) (FragmentWave fs) (initial (.get (obj fs) x))
      (12 + ((fragmentTicks d - 12) + 0)) (3 + ((headCost fs + 2 * d + 2 - 3) + 0)) :=
    .segment (approxL [] fs) t1 (by omega) ⟨[], by intro m v h; simp at h, rfl⟩ (heapFor_template fs)
      (.segment (approxL κ fs) t2 (by have : 12 ≤ fragmentTicks d := (by unfold fragmentTicks; split <;> omega); omega)
        ⟨κ, good, rfl⟩ (heapFor_final nd hc cached frame) (.done rfl))
  have e1 : 12 + ((fragmentTicks d - 12) + 0) = fragmentTicks d := by unfold fragmentTicks; split <;> omega
  have e2 : 3 + ((headCost fs + 2 * d + 2 - 3) + 0) = headCost fs + 2 * d + 2 := by omega
  rw [e1, e2] at ledger
  exact ⟨{
    cost := headCost fs + 2 * d + 2
    charged_real := ⟨_, demand_exists nd hd⟩
    charged_least := fun w j r => by
      obtain ⟨v, n', hd', _, le⟩ := demand_minimal nd r
      rw [hd] at hd'; cases hd'; exact le
    cells := addrs 3 fs
    Approximant := FragmentWave fs
    bound := fragmentLimits fs
    ticks := fragmentTicks d
    ledger := ledger }⟩

/-- **Theorem (`fragment_cost_indexed_completeness`, Chair 7 Finding 9)**:
Every bounded-closure program in `InFragment` that completes on the machine and has a clairvoyant
derivation `CV t v k` possesses a verified cost-indexed ledger (`CostIndexedRun 4 t`) whose machine
ticks are bounded by $4 \times$ the least clairvoyant demand cost. -/
theorem fragment_cost_indexed_completeness :
    ∀ t, InFragment t → ∀ T n, FirstFinish t T n → ∀ v k, CV t v k → Nonempty (CostIndexedRun 4 t) := by
  rintro t ⟨fs, x, rfl, nd⟩ _ _ _ _ _ cv
  obtain ⟨u, m, hd, _, _⟩ := demand_minimal nd cv
  exact fragment_cost_indexed nd hd

/-- **The tick bound on the object fragment, constant 4**, proved directly through the fragment's
cost-indexed ledger (`fragment_cost_indexed_completeness` + `ticks_within_of_runs`). -/
theorem ticks_within_fragment : TicksWithinDemandOn InFragment 4 0 :=
  ticks_within_of_runs fragment_cost_indexed_completeness

/-- **The tick bound on the object fragment under any machine limits `L`**, constant 4. -/
theorem ticks_within_fragment_under (L : Limits) : TicksWithinDemandUnder L InFragment 4 0 :=
  ticks_within_under L ticks_within_fragment

/-- Statement of general `Core4` cost-indexed completeness (without the `InFragment` restriction)
at constant factor `c`. Kept as an explicit open proposition (`Prop`), never asserted as an axiom. -/
def GeneralCostIndexedCompleteness (c : Nat) : Prop :=
  ∀ t T n, FirstFinish t T n → ∀ v k, CV t v k → Nonempty (CostIndexedRun c t)

/-- Alias `CostIndexedCompleteness` for `GeneralCostIndexedCompleteness`. -/
abbrev CostIndexedCompleteness (c : Nat) : Prop := GeneralCostIndexedCompleteness c

/-- Any proof of `GeneralCostIndexedCompleteness c` immediately establishes `TicksWithinDemand c 0`. -/
theorem ticks_within_of_completeness {c : Nat} (h : GeneralCostIndexedCompleteness c) :
    TicksWithinDemand c 0 :=
  ticks_within_of_runs fun t _ => h t

/-- Alias for `fragment_cost_indexed_completeness` on `InFragment`. -/
theorem cost_indexed_completeness :
    ∀ t, InFragment t → ∀ T n, FirstFinish t T n → ∀ v k, CV t v k → Nonempty (CostIndexedRun 4 t) :=
  fragment_cost_indexed_completeness

end Obend.Run.Ticks
end
