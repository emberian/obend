module
/- The machine's trace on the object fragment of `Obend.Equiv.Demand`, symbolically over the field
list (`lean/docs/REPORT-DEMAND-20261101.md`, follow-up: the fragment tick bound's trace).

For `get (obj fs) x`: twelve transitions settle the template and reach the selected cell
(`prefix_trace`); forcing a field along a chase of `d` selections takes `3 + 6d` transitions, plus 3
the first time `self`'s cell is forced (`force_trace`); one more completes. So the run finishes in
exactly `16` transitions when `d = 0` and `19 + 6d` otherwise (`fragment_run`), with the chase's
value. -/
public import Obend.Equiv.Demand
public import Obend.Core.Machine
public import Obend.Core.Proofs.Adequacy.Defs
@[expose] public section
namespace Obend.Core.Proofs.TickTrace
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Proofs.Adequacy (rawRun)
open Obend.Equiv
open Obend.Equiv.Demand
set_option autoImplicit false

/-! ## Runs composed along active transitions -/

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

theorem Trace.next {L : Limits} {s s1 s' : State} {n : Nat} (a : Active s) (e : stepRaw s = s1)
    (f : Fits L s1) (t : Trace L s1 n s') : Trace L s (n + 1) s' := by
  subst e; exact .cons a f t

theorem Trace.trans {L : Limits} {a b c : State} {n m : Nat} (t : Trace L a n b) (u : Trace L b m c) :
    Trace L a (n + m) c := by
  induction t with
  | refl => simpa using u
  | @cons s0 s1 k x f _ ih =>
    rw [show k + 1 + m = (k + m) + 1 by omega]
    exact .cons x f (ih u)

theorem step_active {L : Limits} {s : State} (a : Active s) (f : Fits L (stepRaw s)) :
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

/-- A trace is the unbounded raw machine's run. -/
theorem rawRun_trace {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') : rawRun n s = s' := by
  induction t with
  | refl => rfl
  | cons _ _ _ ih => exact ih

/-- Before a trace ends, the raw run is still active. -/
theorem rawRun_short {L : Limits} {s s' : State} {n : Nat} (t : Trace L s n s') :
    ∀ j < n, Active (rawRun j s) := by
  induction t with
  | refl => intro j h; omega
  | @cons s0 s1 k a f _ ih =>
    intro j hj
    cases j with
    | zero => exact a
    | succ j => exact ih j (by omega)

/-- A completed state stays completed. -/
theorem rawRun_complete {s : State} {v : RuntimeValue} (h : s.control = .complete v) :
    ∀ j, rawRun j s = s
  | 0 => rfl
  | j + 1 => by
    have e : stepRaw s = s := by
      obtain ⟨heap, control, stack⟩ := s
      simp only at h; subst h; rfl
    show rawRun j (stepRaw s) = s
    rw [e]; exact rawRun_complete h j

theorem rawRun_stays {v : RuntimeValue} : ∀ (a : Nat) {s : State} {b : Nat}, (rawRun a s).control = .complete v →
    a ≤ b → (rawRun b s).control = .complete v
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

/-! ## Allocation, as an append -/

/-- The addresses a record allocated from `base` receives, in field order. -/
def addrs {α : Type} : Nat → List (String × α) → List (String × Address)
  | _, [] => []
  | b, f :: fs => (f.1, b) :: addrs (b + 1) fs

theorem alloc_foldl (env : Environment) : ∀ (E : List (String × Term)) (h : List Cell)
    (acc : List (String × Address)),
    E.foldl (fun (prior : Array Cell × List (String × Address)) field =>
      (prior.1.push (.suspended ⟨field.2, env⟩), (field.1, prior.1.size) :: prior.2)) (h.toArray, acc) =
      ((h ++ E.map fun f => Cell.suspended ⟨f.2, env⟩).toArray, (addrs h.length E).reverse ++ acc)
  | [], h, acc => by simp [addrs]
  | f :: E, h, acc => by
    simp only [List.foldl_cons, List.push_toArray, List.size_toArray]
    refine (alloc_foldl env E (h ++ [.suspended ⟨f.2, env⟩]) ((f.1, h.length) :: acc)).trans ?_
    simp [addrs]

/-- **`allocateFields` as an append**: the fields' cells go after the heap, at `|heap| + i`. -/
theorem allocateFields_toArray (h : List Cell) (env : Environment) (E : List (String × Term)) :
    allocateFields h.toArray env E =
      ((h ++ E.map fun f => Cell.suspended ⟨f.2, env⟩).toArray, addrs h.length E) := by
  unfold allocateFields
  rw [alloc_foldl]
  simp

/-! ## The object's heap -/

/-- The environment the object's fields close over: `super`'s cell 2, `self`'s cell 1, the knot 0. -/
def fieldEnv : Environment := [2, 1, 0]

/-- A field's cell as allocated: suspended, `self` being index 1. -/
def fieldCell (f : String × FE) : Cell := .suspended ⟨f.2.at (.bound 1), fieldEnv⟩

/-- The index of the first field named `m`. -/
def pos : List (String × FE) → String → Nat
  | [], _ => 0
  | f :: fs, m => if f.1 == m then 0 else pos fs m + 1

/-- The record value the template settles to. -/
def recordValue (fs : List (String × FE)) : RuntimeValue := .record (addrs 3 fs)

/-- The knot's body, as the machine allocates it. -/
def knotBody (fs : List (String × FE)) : Term := .app (.app (objLam fs) (.bound 0)) (.record [])

def knotCell (fs : List (String × FE)) : Cell := .cached ⟨knotBody fs, [0]⟩ (recordValue fs)
def selfSuspended : Cell := .suspended ⟨.bound 0, [0]⟩
def selfCached (fs : List (String × FE)) : Cell := .cached ⟨.bound 0, [0]⟩ (recordValue fs)
def superCell : Cell := .suspended ⟨.record [], [0]⟩

/-- The heap once the template is settled: the knot cached, `self` and `super` suspended, every
field suspended. -/
def templateHeap (fs : List (String × FE)) : List Cell :=
  knotCell fs :: selfSuspended :: superCell :: fs.map fieldCell

theorem look_cons (f : String × FE) (fs : List (String × FE)) (m : String) :
    look (f :: fs) m = if f.1 == m then some f.2 else look fs m := by
  simp only [look, List.find?_cons]
  split <;> simp_all

theorem look_pos {m : String} {e : FE} : ∀ {fs : List (String × FE)}, look fs m = some e →
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

theorem find_addrs {m : String} {e : FE} : ∀ {fs : List (String × FE)} (b : Nat), look fs m = some e →
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

theorem pos_inj {m m' : String} {e e' : FE} : ∀ {fs : List (String × FE)}, look fs m = some e →
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

theorem addrs_entries (s : Term) : ∀ (b : Nat) (fs : List (String × FE)), addrs b (entries s fs) = addrs b fs
  | _, [] => rfl
  | b, f :: fs => by simp [entries, addrs]; exact addrs_entries s (b + 1) fs

theorem entries_cells (fs : List (String × FE)) :
    (entries (.bound 1) fs).map (fun f => Cell.suspended ⟨f.2, fieldEnv⟩) = fs.map fieldCell := by
  simp [entries, fieldCell]

theorem objLam_rename (fs : List (String × FE)) : (objLam fs).rename Nat.succ = objLam fs := by
  have := objLam_selfBody fs
  simp only [selfBody] at this
  injection this with h1 _
  injection h1

/-! ## The template: twelve transitions -/

/-- **Twelve transitions** settle the template and enter the selected field's cell. -/
theorem prefix_trace {L : Limits} {fs : List (String × FE)} {x : String} {e : FE}
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

/-! ## Forcing a field along its chase -/

theorem Trace.cast {L : Limits} {s s' : State} {n n' : Nat} (e : n = n') (t : Trace L s n s') :
    Trace L s n' s' := e ▸ t

/-- What forcing `self`'s cell costs beyond reading it: 3 the first time, nothing once cached. -/
def selfExtra : Cell → Nat
  | .suspended _ => 3
  | _ => 0

theorem set_self {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  have lt : i < l.length := by
    rcases Nat.lt_or_ge i l.length with lt | ge
    · exact lt
    · rw [List.getElem?_eq_none ge] at h; cases h
  rw [List.getElem?_eq_getElem lt] at h
  cases h
  exact List.set_getElem_self lt

/-- Reading `self`: one transition when its cell is cached, four when it is first forced. -/
theorem self_trace {L : Limits} {fs : List (String × FE)} {hq : List Cell} {rest : List Frame} {c1 : Cell}
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

theorem chase_look {fs : List (String × FE)} {k : Nat} {m : String} {p : Nat × Nat}
    (h : chase fs k m = some p) : ∃ e, look fs m = some e := by
  cases k with
  | zero => simp [chase] at h
  | succ k =>
    simp only [chase] at h
    split at h
    · exact ⟨_, by assumption⟩
    · exact ⟨_, by assumption⟩
    · cases h

/-- **The forcing lemma**, by induction on the chase: from the cell of `z`, whose chase reaches the
literal `u` in `d` selections, the machine returns `u` in `3 + 6d` transitions, plus 3 if `self`'s
cell is first forced on the way. Every cell on the path ends cached at `u`, `self`'s cell cached once
read, and every other cell is untouched. The path's cells are distinct by `chase_walk_injective`. -/
theorem force_trace {L : Limits} {fs : List (String × FE)} : ∀ (k : Nat) {z : String} {u d : Nat},
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
    · -- a literal: enter, the value, the update
      rename_i v hlz
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
      · intro a ha hn
        rw [List.getElem?_set_ne (Ne.symm (hn 0 z rfl))]
    · -- a selection: enter, `get`, `self`, the selection, the field's chase, the update
      rename_i m hlz
      obtain ⟨⟨u', d'⟩, hcm, he⟩ := Option.map_eq_some_iff.1 hc'
      simp only [Prod.mk.injEq] at he
      obtain ⟨hv, hd⟩ := he
      subst u'; subst d
      obtain ⟨em, hlm⟩ := chase_look hcm
      have hz := hpath 0 z (.ref m) rfl hlz
      simp only [fieldCell, FE.at] at hz
      have walkm : ∀ i, walk fs (i + 1) z = walk fs i m := by intro i; simp [walk, hlz]
      -- the cells on `m`'s path are not `z`'s
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

/-! ## The whole run -/

/-- The run's length: 16 transitions for a literal, `19 + 6d` for a chase of `d ≥ 1` selections. -/
def fragmentTicks (d : Nat) : Nat := if d = 0 then 16 else 19 + 6 * d

/-- After the template: the forcing lemma from the selected cell, and one transition to complete. -/
theorem rest_trace {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
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

/-- The whole run: twelve transitions to the selected cell, then `rest_trace`. -/
theorem fragment_trace {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) (hh : fs.length + 3 ≤ L.heap) (hs : fs.length + 3 ≤ L.stack) :
    ∃ hp : List Cell, Trace L (initial (.get (obj fs) x)) (fragmentTicks d)
        ⟨hp.toArray, .complete (.natural u), []⟩ := by
  obtain ⟨ex, hx⟩ := chase_look hc
  have short := chase_short hc
  obtain ⟨hp, t2, _⟩ := rest_trace hc hh hs
  refine ⟨hp, Trace.cast ?_ ((prefix_trace (L := L) hx hh (by omega)).trans t2)⟩
  unfold fragmentTicks; split <;> omega

/-- **The run on the fragment, exactly**: with at least `fragmentTicks d` ticks it finishes with the
chase's value; with fewer it is still running. -/
theorem fragment_run {L : Limits} {fs : List (String × FE)} {x : String} {k u d : Nat}
    (hc : chase fs k x = some (u, d)) (hh : fs.length + 3 ≤ L.heap) (hs : fs.length + 3 ≤ L.stack) :
    (∀ T, fragmentTicks d ≤ T → ∃ s, runBounded L T (initial (.get (obj fs) x)) = .finished (.natural u) s) ∧
      (∀ T, T < fragmentTicks d → ∃ s, runBounded L T (initial (.get (obj fs) x)) = .suspended .ticks s) := by
  obtain ⟨hp, t⟩ := fragment_trace hc hh hs
  refine ⟨fun T le => ⟨⟨hp.toArray, .complete (.natural u), []⟩, ?_⟩, runBounded_short t⟩
  rw [show T = fragmentTicks d + (T - fragmentTicks d) by omega, runBounded_trace t]
  exact runBounded_complete rfl _

end Obend.Core.Proofs.TickTrace
end
