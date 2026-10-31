module
/- Machine ticks against the two-stage demand cost (`review/EQUIV-PLAN-20261031.md` §5, lane 3;
contract C4).

Under Hackett and Hutton's `Let′` at `fix` the tick bound was false (`ticks_not_within_cv`, retired):
`{a = 7, b = self.a}.b` finishes on the machine and had no clairvoyant derivation. Under the
two-stage rule (`Obend.Equiv.Clairvoyant`: the template settled once, the fields filled in waves)
it has one, and the least cost of each measured program is the demand semantics'
(`Obend.Equiv.Demand.measured_least`).

**The bound on the object fragment** (`ticks_within_fragment`): for `get (obj fs) x` with distinct
names and at most 97 fields (so the limits `⟨100, 100⟩` are never hit), the machine's ticks are at
most 4 times the least clairvoyant cost. The run is traced symbolically
(`Obend.Core.Proofs.TickTrace`): `16` ticks for a literal, `19 + 6d` for a chase of `d ≥ 1`
selections, against the least cost `headCost + 2d + 2` (`fragment_ticks`). The measured programs
are instances (`measured_within`): `.good` 16 ticks at cost 5, `.b` 25 at cost 7; `.bad` has no
derivation and blackholes at 21.

**The general bound's precondition** (`CostIndexedRun`): a ledger of the machine run against the
knot's waves. The run is cut into segments; each costs at most `c` transitions per clairvoyant unit
charged to it (stutters per source reduction bounded), and at the end of each the heap's field cells
stand for an approximant of the knot (`HeapFor`: a suspended cell for `skipped` or for a literal it
will evaluate for free, a cached cell for its value). The charge is the least cost. From a ledger
the bound follows for any program (`ticks_within_of_runs`); the fragment has one at `c = 4`
(`fragment_cost_indexed`), and the fragment's bound is proved through it. What is not proved is
`CostIndexedCompleteness c`: that every program the machine finishes, with a derivation, has a
ledger. That needs a cost-indexed `Core/Proofs/Completeness` (its descent on source cost and an
unbounded stutter rank gives completion, no count of transitions per unit, and no relation between
heap cells and approximants). -/
public import Obend.Core.Proofs.TickTrace
@[expose] public section
namespace Obend.Core.Proofs.TickCost
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Proofs.TickTrace
open Obend.Equiv
open Obend.Equiv.CostTests
open Obend.Equiv.Demand
set_option autoImplicit false

/-- The natural number a finished run returns, if it finished with one. -/
def finishedNat : Outcome → Option Nat
  | .finished (.natural n) _ => some n
  | _ => none

/-- A run that ended at the blackhole. -/
def blackholed : Outcome → Bool
  | .divergent _ _ => true
  | _ => false

/-- The machine's limits for these runs. -/
def limits : Limits := ⟨100, 100⟩

/-- The tick bound on the programs `P`: when a program in `P` first finishes after `T` ticks, `T` is
within `c` times its least clairvoyant cost, plus `d`. -/
def TicksWithinDemandOn (P : Term → Prop) (c d : Nat) : Prop :=
  ∀ (t : Term), P t → ∀ (T n : Nat), finishedNat (runBounded limits T (initial t)) = some n →
    (∀ T' < T, finishedNat (runBounded limits T' (initial t)) = none) →
    ∀ k, CV t (.nat n) k → (∀ w j, CV t w j → k ≤ j) → T ≤ c * k + d

/-- The tick bound, in its true form: for every program whose demand run exists, the machine's
ticks are within `c` times the least demand cost, plus `d`. -/
def TicksWithinDemand (c d : Nat) : Prop := TicksWithinDemandOn (fun _ => True) c d

/-- The object fragment: a selection from an object of literals and `self.m` fields, with distinct
names, small enough for the limits. -/
def InFragment (t : Term) : Prop :=
  ∃ (fs : List (String × FE)) (x : String), t = .get (obj fs) x ∧ (fs.map Prod.fst).Nodup ∧ fs.length ≤ 97

/-! ## The fragment's run against its demand -/

theorem hasRef_of_look {fs : List (String × FE)} {z m : String} (h : look fs z = some (.ref m)) :
    hasRef fs = true := by
  obtain ⟨f, hf, he⟩ := Option.map_eq_some_iff.1 h
  simp only [hasRef, List.any_eq_true]
  exact ⟨f, List.mem_of_find?_eq_some hf, by rw [he]⟩

/-- The ticks of a chase of `d` selections are within the factor 4 of its demand, and above it. -/
theorem fragment_ticks {fs : List (String × FE)} {x : String} {k u d : Nat} (hc : chase fs k x = some (u, d)) :
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

/-- **The machine computes the demand**: the run finishes with the chase's value after exactly
`fragmentTicks d` ticks. -/
theorem fragment_machine {fs : List (String × FE)} {x : String} {k u d : Nat} (hc : chase fs k x = some (u, d))
    (hlen : fs.length ≤ 97) :
    finishedNat (runBounded limits (fragmentTicks d) (initial (.get (obj fs) x))) = some u ∧
      ∀ T < fragmentTicks d, finishedNat (runBounded limits T (initial (.get (obj fs) x))) = none := by
  obtain ⟨fin, short⟩ := fragment_run (L := limits) hc (by simp [limits]; omega) (by simp [limits]; omega)
  obtain ⟨s, hs⟩ := fin _ (Nat.le_refl _)
  refine ⟨by rw [hs]; rfl, fun T lt => ?_⟩
  obtain ⟨r, hr⟩ := short T lt
  rw [hr]; rfl

/-- **Within four times the demand, the run has finished** with the demand's value. -/
theorem fragment_within {fs : List (String × FE)} {x : String} (hlen : fs.length ≤ 97) {u n : Nat}
    (hd : demand fs x = some (u, n)) {T : Nat} (hT : 4 * n ≤ T) :
    finishedNat (runBounded limits T (initial (.get (obj fs) x))) = some u := by
  obtain ⟨⟨u', d⟩, hc, he⟩ := Option.map_eq_some_iff.1 hd
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have short := chase_short hc
  obtain ⟨fin, _⟩ := fragment_run (L := limits) hc (by simp only [limits]; omega) (by simp only [limits]; omega)
  obtain ⟨s, hs⟩ := fin T (Nat.le_trans (fragment_ticks hc).2 hT)
  rw [hs]; rfl

/-! ## The precondition of the general bound: a ledger of the run against the waves -/

/-- A machine cell stands for an approximant's entry: a suspended or forcing cell for `skipped`, a
suspended literal for its value (the knot settles a literal for free; the machine forces it on
demand), a cached cell for its value. -/
inductive CellFor : Cell → Term → Prop where
  | pending (o : Closure) : CellFor (.suspended o) skipped
  | forcing (o : Closure) : CellFor (.evaluating o) skipped
  | literal (env : Environment) (n : Nat) : CellFor (.suspended ⟨.nat n, env⟩) (.nat n)
  | cached (o : Closure) (n : Nat) : CellFor (.cached o (.natural n)) (.nat n)

/-- The heap stands for the approximant: the `i`-th named cell for the `i`-th entry. -/
def HeapFor (heap : Array Cell) (cells : List (String × Address)) (wave : List (String × Term)) : Prop :=
  cells.length = wave.length ∧ ∀ (i : Nat) (c : String × Address) (w : String × Term),
    cells[i]? = some c → wave[i]? = some w → c.1 = w.1 ∧ ∃ cell, heap[c.2]? = some cell ∧ CellFor cell w.2

/-- A run from a state, cut into segments charged against the clairvoyant cost: each segment takes at
most `c` transitions per unit charged, and ends where the heap stands for an approximant. -/
inductive Ledger (L : Limits) (c : Nat) (cells : List (String × Address))
    (Approximant : List (String × Term) → Prop) : State → Nat → Nat → Prop where
  | done {s : State} {n : Nat} : s.control = .complete (.natural n) → Ledger L c cells Approximant s 0 0
  | segment {s s' : State} {n j T K : Nat} (wave : List (String × Term)) :
      Trace L s n s' → n ≤ c * j → Approximant wave → HeapFor s'.heap cells wave →
      Ledger L c cells Approximant s' T K → Ledger L c cells Approximant s (n + T) (j + K)

/-- **What a cost-indexed `Completeness` must provide for `t`**: a ledger of the machine run from
`t`, charged at most the least clairvoyant cost, against the approximants of `t`'s knot. -/
structure CostIndexedRun (L : Limits) (c : Nat) (t : Term) where
  /-- the cost charged -/
  cost : Nat
  /-- a derivation of that cost exists -/
  charged_real : ∃ v, CV t v cost
  /-- and none is cheaper -/
  charged_least : ∀ w j, CV t w j → cost ≤ j
  /-- the cells of the knot's fields -/
  cells : List (String × Address)
  /-- the knot's approximants -/
  Approximant : List (String × Term) → Prop
  /-- the run's length -/
  ticks : Nat
  ledger : Ledger L c cells Approximant (initial t) ticks cost

theorem Ledger.run {L : Limits} {c : Nat} {cells : List (String × Address)} {A : List (String × Term) → Prop}
    {s : State} {T K : Nat} (h : Ledger L c cells A s T K) :
    T ≤ c * K ∧ ∃ s' n, Trace L s T s' ∧ s'.control = .complete (.natural n) := by
  induction h with
  | @done s n hc => exact ⟨by omega, s, n, .refl s, hc⟩
  | @segment s s' n j T K _ tr le _ _ _ ih =>
    obtain ⟨le', s'', n', tr', hc⟩ := ih
    exact ⟨by rw [Nat.mul_add]; omega, s'', n', tr.trans tr', hc⟩

/-- **From ledgers, the bound**: if every program in `P` that finishes, with a derivation, has a
ledger at `c`, its ticks are within `c` times its least cost. -/
theorem ticks_within_of_runs {P : Term → Prop} {c : Nat}
    (h : ∀ t, P t → ∀ T n, finishedNat (runBounded limits T (initial t)) = some n →
      ∀ v k, CV t v k → Nonempty (CostIndexedRun limits c t)) :
    TicksWithinDemandOn P c 0 := by
  intro t hP T n fin minimal k cv _
  obtain ⟨R⟩ := h t hP T n fin _ k cv
  obtain ⟨le, s', n', tr, hc⟩ := R.ledger.run
  have fin0 : finishedNat (runBounded limits R.ticks (initial t)) = some n' := by
    rw [show R.ticks = R.ticks + 0 by omega, runBounded_trace tr, runBounded_complete hc]; rfl
  have hT : T ≤ R.ticks := by
    rcases Nat.lt_or_ge R.ticks T with lt | ge
    · rw [minimal _ lt] at fin0; cases fin0
    · exact ge
  have := Nat.mul_le_mul_left c (R.charged_least _ _ cv)
  omega

/-- **The general precondition**, not proved: every program the machine finishes, with a
clairvoyant derivation, has a ledger at `c`. -/
def CostIndexedCompleteness (c : Nat) : Prop :=
  ∀ t T n, finishedNat (runBounded limits T (initial t)) = some n → ∀ v k, CV t v k →
    Nonempty (CostIndexedRun limits c t)

theorem ticks_within_of_completeness {c : Nat} (h : CostIndexedCompleteness c) : TicksWithinDemand c 0 :=
  ticks_within_of_runs fun t _ => h t

/-! ## The fragment's ledger -/

/-- The fragment's approximants: the waves' records, their known selections the chase's values. -/
def FragmentWave (fs : List (String × FE)) (w : List (String × Term)) : Prop :=
  ∃ κ, Good fs κ ∧ w = approxL κ fs

theorem addrs_length {α : Type} : ∀ (b : Nat) (l : List (String × α)), (addrs b l).length = l.length
  | _, [] => rfl
  | b, _ :: l => by simp [addrs, addrs_length (b + 1) l]

theorem addrs_get {α : Type} : ∀ (l : List (String × α)) (b i : Nat),
    (addrs b l)[i]? = (l[i]?).map (fun f => (f.1, b + i))
  | [], _, _ => by simp [addrs]
  | _ :: _, _, 0 => by simp [addrs]
  | _ :: l, b, i + 1 => by
    simp only [addrs, List.getElem?_cons_succ, addrs_get l (b + 1) i]
    cases l[i]? <;> simp; omega

theorem pos_index {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) :
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

/-- Along a successful chase, every field on the walk chases to the same value. -/
theorem chase_suffix {fs : List (String × FE)} {u : Nat} : ∀ (i : Nat) {k : Nat} {x z : String} {d : Nat},
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

theorem walk_look {fs : List (String × FE)} {k : Nat} {x : String} {u d : Nat} (hc : chase fs k x = some (u, d))
    {i : Nat} {z : String} (hw : walk fs i x = some z) : ∃ e, look fs z = some e := by
  obtain ⟨k', d', h'⟩ := chase_suffix i hc hw
  exact chase_look h'

theorem chase_lit {fs : List (String × FE)} {k : Nat} {z : String} {u d v : Nat}
    (hc : chase fs k z = some (u, d)) (hl : look fs z = some (.lit v)) : v = u := by
  cases k with
  | zero => simp [chase] at hc
  | succ k => simp [chase, hl] at hc; exact hc.1

theorem lookup_names (u : Nat) (n : String) : ∀ (names : List String),
    (names.map fun z => (z, u)).lookup n = if n ∈ names then some u else none
  | [] => by simp
  | z :: names => by
    simp only [List.map_cons, List.lookup, List.mem_cons]
    by_cases h : n = z
    · subst h; simp
    · have hb : (n == z) = false := by simpa using h
      simp only [hb, h, false_or]
      exact lookup_names u n names

/-- The template's heap stands for the first wave: every literal for itself, every selection
`skipped`. -/
theorem heapFor_template (fs : List (String × FE)) :
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

/-- The heap at the end stands for the last wave: the chase's fields known at its value. -/
theorem heapFor_final {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) {x : String} {k u d : Nat}
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

/-- **The fragment has a ledger at 4**: the template (12 transitions, charged 3) ends where the heap
stands for the first wave; the chase and the completion (charged the rest) end where it stands for
the last. -/
theorem fragment_cost_indexed {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) (hlen : fs.length ≤ 97)
    {x : String} {u n : Nat} (hd : demand fs x = some (u, n)) :
    Nonempty (CostIndexedRun limits 4 (.get (obj fs) x)) := by
  obtain ⟨⟨u', d⟩, hc, he⟩ := Option.map_eq_some_iff.1 hd
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨ex, hx⟩ := chase_look hc
  have short := chase_short hc
  have hh : fs.length + 3 ≤ limits.heap := by simp [limits]; omega
  have t1 := prefix_trace (L := limits) hx hh (by simp only [limits]; omega)
  obtain ⟨hp, t2, _, cached, frame⟩ := rest_trace (L := limits) hc hh (by simp only [limits]; omega)
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
  have ledger : Ledger limits 4 (addrs 3 fs) (FragmentWave fs) (initial (.get (obj fs) x))
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
    ticks := fragmentTicks d
    ledger := ledger }⟩

/-- **The tick bound on the object fragment, constant 4**, through the fragment's ledger. -/
theorem ticks_within_fragment : TicksWithinDemandOn InFragment 4 0 := by
  refine ticks_within_of_runs ?_
  rintro t ⟨fs, x, rfl, nd, hlen⟩ T n _ v k cv
  obtain ⟨u, m, hd, _, _⟩ := demand_minimal nd cv
  exact fragment_cost_indexed nd hlen hd

/-! ## The measured programs, as instances -/

/-- `{a = 7, b = self.a}.b` finishes with `7` within 25 ticks, and not within 24. -/
theorem self_field_machine :
    finishedNat (runBounded limits 25 (initial (.get selfField "b"))) = some 7 ∧
      finishedNat (runBounded limits 24 (initial (.get selfField "b"))) = none := by
  have hc : chase selfFieldFields 2 "b" = some (7, 1) := rfl
  obtain ⟨h1, h2⟩ := fragment_machine hc (by decide)
  exact ⟨h1, h2 24 (by decide)⟩

/-- `{good = 7, bad = self.bad}.good` finishes with `7` within 16 ticks, and not within 15. -/
theorem good_machine :
    finishedNat (runBounded limits 16 (initial (.get FareTests.object "good"))) = some 7 ∧
      finishedNat (runBounded limits 15 (initial (.get FareTests.object "good"))) = none := by
  have hc : chase goodBadFields 2 "good" = some (7, 0) := rfl
  obtain ⟨h1, h2⟩ := fragment_machine hc (by decide)
  exact ⟨h1, h2 15 (by decide)⟩

/-- `.bad` reaches the blackhole within 21 ticks, and not within 20. -/
theorem bad_machine :
    blackholed (runBounded limits 21 (initial (.get FareTests.object "bad"))) = true ∧
      blackholed (runBounded limits 20 (initial (.get FareTests.object "bad"))) = false := by
  constructor <;> simp [blackholed, limits, runBounded, step, stepRaw, initial, FareTests.object,
    FareTests.goodBad, allocateFields, Array.set!, Array.setIfInBounds, Term.rename, liftRename]

/-- **The measured programs are within a factor of 4**: each finishes in at most 4 times its least
demand cost and in no fewer ticks than that cost, and the one without a demand run blackholes. -/
theorem measured_within :
    (CV (.get FareTests.object "good") (.nat 7) 5 ∧ (∀ w k, CV (.get FareTests.object "good") w k → 5 ≤ k) ∧
      finishedNat (runBounded limits 16 (initial (.get FareTests.object "good"))) = some 7 ∧
      finishedNat (runBounded limits 15 (initial (.get FareTests.object "good"))) = none ∧ 5 ≤ 16 ∧ 16 ≤ 4 * 5) ∧
    (CV (.get selfField "b") (.nat 7) 7 ∧ (∀ w k, CV (.get selfField "b") w k → 7 ≤ k) ∧
      finishedNat (runBounded limits 25 (initial (.get selfField "b"))) = some 7 ∧
      finishedNat (runBounded limits 24 (initial (.get selfField "b"))) = none ∧ 7 ≤ 25 ∧ 25 ≤ 4 * 7) ∧
    ((∀ v k, ¬ CV (.get FareTests.object "bad") v k) ∧
      blackholed (runBounded limits 21 (initial (.get FareTests.object "bad"))) = true) := by
  obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩, bad⟩ := measured_least
  have frag : ∀ (fs : List (String × FE)) x, (fs.map Prod.fst).Nodup → fs.length ≤ 97 → InFragment (.get (obj fs) x) :=
    fun fs x nd hl => ⟨fs, x, rfl, nd, hl⟩
  have g := ticks_within_fragment _ (frag goodBadFields "good" (by decide) (by decide)) 16 7 good_machine.1
    (fun T' lt => (fragment_machine (rfl : chase goodBadFields 2 "good" = some (7, 0)) (by decide)).2 T' lt) 5 g1 g2
  have b := ticks_within_fragment _ (frag selfFieldFields "b" (by decide) (by decide)) 25 7 self_field_machine.1
    (fun T' lt => (fragment_machine (rfl : chase selfFieldFields 2 "b" = some (7, 1)) (by decide)).2 T' lt) 7 b1 b2
  exact ⟨⟨g1, g2, good_machine.1, good_machine.2, by omega, by rw [Nat.add_zero] at g; exact g⟩,
    ⟨b1, b2, self_field_machine.1, self_field_machine.2, by omega, by rw [Nat.add_zero] at b; exact b⟩,
    ⟨bad, bad_machine.1⟩⟩

/-- The refutation's witness, now an instance: `{a = 7, b = self.a}.b`, which `ticks_not_within_cv`
used to show no bound holds, is within the factor. -/
theorem self_field_within : ∃ k, CV (.get selfField "b") (.nat 7) k ∧ 25 ≤ 4 * k :=
  ⟨7, self_field_cost, by omega⟩

end Obend.Core.Proofs.TickCost
end
