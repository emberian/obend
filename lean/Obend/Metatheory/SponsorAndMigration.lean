module
/-
# Obend.Metatheory.SponsorAndMigration — Reflective `SponsorTower`, `ImplementationRegime` & Full-Abstraction Migration

Formalizes Proposal 2 of the General Metatheory of Distributed, Decentralized Houyhnhnm Computation:
1. **`machineGuestRunner`**: concrete `GuestRunner Machine.State` bridging `Core.Machine.runBounded`
   and `Core.MachineReify.reifyMachineDag` into `Polis.HouyhnhnmMonitor.VirtualizedCell Machine.State`,
   proving demand-driven `.hole` trapping (`machineGuestRunner_hole_traps_to_sponsor`) and full-abstraction
   yield interposition (`machineGuestRunner_honeypot_indistinguishable`).
2. **`ImplementationRegime (C : Type)`**: `(A, I ⊳ C)` carrier lowering, sharing-preserving reification,
   and `CompositeGrade`-metered execution across three concrete computational grains:
   - `termCanonicalRegime` (`Core.Term` symbolic reduction),
   - `machineHeapRegime` (`Core.Machine.State` DAG-shared heap + cyclic `.fix` knots),
   - `rtlWordRegime` (`Hardware.HDL.RtlExpr` combinational netlists + 64-bit `BitVec 64` registers).
3. **Reflective `SponsorTower`**: arbitrary-depth nested hierarchy with preemptive `CompositeGrade`
   quota conservation (`overheadSpent + sumGrades childQuotas ≤ quota`) and monotonic capability
   attenuation (`child.capsOf ⊆ parent.capsOf`), proved globally in `sponsorTower_global_confinement_and_budget`.
4. **`migrateRegime_preserves_semantics_and_full_abstraction`**: live cross-regime migration
   `C₁ → Core.Term → C₂` preserves `Equiv.IEquiv` observational interaction traces across all
   regime-blind `Core.Term` contexts, enforces strict `heldCaps` confinement, and preserves
   remaining `CompositeGrade` budgets.
-/
public import Obend.Core.MachineReify
public import Obend.Core.RangeSafe
public import Obend.Category.GradedLogic
public import Obend.Polis.HouyhnhnmMonitor
public import Obend.Metatheory.PinsAndQuiescence

public section

namespace Obend.Metatheory.SponsorAndMigration

open Obend.Core.Term
open Obend.Core.Machine (State Limits)
open Obend.Core.MachineReify
open Obend.Core.TermTraverse (Scoped)
open Obend.Core.RangeSafe (Interval checkRangeSafeHw ValueInInterval scalarToNat
  closeTerm envSubst term_substitute_id hwEnvAgrees_nil compileTerm_evaluates_sound
  steps_binaryLeft step_deterministic hwOverflowTerm wrap_counterexample_without_rangeSafe)
open Obend.Hardware.HDL (RtlExpr evalRtlExpr)
open Obend.Hardware.Compiler (compileTerm compilePrim)
open Obend.Equiv
open Obend.Category (CompositeGrade GradeMonoid)
open Obend.Polis.HouyhnhnmMonitor

set_option autoImplicit false

/-! ## 1. Concrete `GuestRunner Machine.State` Welded to `reifyMachineDag` -/

/-- Extract a demanded `.hole` slot ID when `st` is poised at `.evaluate (.hole hid _) _`. -/
@[expose] def pendingHoleId? (st : State) : Option Nat :=
  match st.control with
  | .evaluate (.hole hid _) _ => some hid
  | _ => none

/-- Step `Machine.step limits` for `ticks` steps while recording the exact `.hole hid` slot ID
    demanded immediately prior to any `.refused .unresolvedHole` transition (even after arbitrary
    intermediate reductions). -/
@[expose] def runBoundedTrackingHole (limits : Limits) :
    Nat → Option Nat → State → Option Nat × Obend.Core.Machine.Outcome
  | 0, lastHole?, st =>
      let h? := (pendingHoleId? st).or lastHole?
      match st.control with
      | .complete val => (h?, .finished val st)
      | .yielded addr => (h?, .yielded addr st)
      | .blackhole addr => (h?, .divergent addr st)
      | .refused reason => (h?, .refused reason st)
      | _ => (h?, .suspended .ticks st)
  | ticks + 1, lastHole?, st =>
      let h? := (pendingHoleId? st).or lastHole?
      match Obend.Core.Machine.step limits st with
      | .finished val next => (h?, .finished val next)
      | .yielded addr next => (h?, .yielded addr next)
      | .divergent addr next => (h?, .divergent addr next)
      | .refused reason next => (h?, .refused reason next)
      | .suspended .capacity next => (h?, .suspended .capacity next)
      | .suspended .ticks next => runBoundedTrackingHole limits ticks h? next

/-- Concrete `GuestRunner Machine.State` running `runBoundedTrackingHole` and decompiling
    finished values and isolated yielded plan closures (`{ st' with control := .enter planAddr, stack := [] }`,
    never leaking the surrounding continuation!) through DAG-sharing `reifyMachineDag`. -/
@[expose] def machineGuestRunner (limits : Limits) : GuestRunner State where
  runSlice ticks st :=
    match runBoundedTrackingHole limits ticks none st with
    | (_, .finished _ st') =>
        match reifyMachineDag st' with
        | .ok vTerm => .finished vTerm st'
        | .error _ => .reificationError "finished_reify" st'
    | (_, .suspended .ticks st') => .suspendedTicks ticks st'
    | (_, .suspended .capacity st') => .suspendedCapacity st'.heap.size st'.stack.length st'
    | (_, .divergent addr st') => .divergent addr st'
    | (holeId?, .refused .unresolvedHole st') => .refusedHole (holeId?.getD 0) st'
    | (_, .refused _ st') => .refusedOther "machine_refused" st'
    | (_, .yielded planAddr st') =>
        match st'.heap[planAddr]? with
        | some (.suspended ⟨planTm, []⟩) => .yielded planTm st'
        | _ =>
            match reifyMachineDag { st' with control := .enter planAddr, stack := [] } with
            | .ok planOnlyTm => .yielded planOnlyTm st'
            | .error _ => .reificationError "yield_plan_reify" st'
  resumeGuest := Obend.Core.Machine.resume

private theorem runBoundedTrackingHole_already_refused (limits : Limits) (k : Nat)
    (hid : Nat) (st : State) (hCtrl : st.control = .refused .unresolvedHole) :
    runBoundedTrackingHole limits k (some hid) st = (some hid, .refused .unresolvedHole st) := by
  cases k with
  | zero => simp [runBoundedTrackingHole, pendingHoleId?, hCtrl, Option.or]
  | succ m => simp [runBoundedTrackingHole, pendingHoleId?, Obend.Core.Machine.step, hCtrl, Option.or]

/-- Demanding an unresolved `.hole slotId []` on `Machine.State` traps cleanly to the outer
    `VirtualizedCell` supervisor with `MonitorBlame.incoherentHoleTrap slotId` and zero world side-effects. -/
theorem machineGuestRunner_hole_traps_to_sponsor (limits : Limits)
    (pol : Term → PinInterposition) (cell : VirtualizedCell State) (slotId extraTicks : Nat)
    (hGuest : cell.guest = Obend.Core.Machine.initial (.hole slotId []))
    (hTicks : cell.tickSlice = extraTicks + 1) :
    let next := stepVirtualizedCell (machineGuestRunner limits) pol cell
    next.blameLog = .incoherentHoleTrap slotId :: cell.blameLog ∧
    next.committedEffects = cell.committedEffects := by
  have hStep : Obend.Core.Machine.step limits (Obend.Core.Machine.initial (.hole slotId [])) =
      .suspended .ticks ⟨#[], .refused .unresolvedHole, []⟩ := by
    simp [Obend.Core.Machine.step, Obend.Core.Machine.initial, Obend.Core.Machine.stepRaw]
  have hTail := runBoundedTrackingHole_already_refused limits extraTicks slotId
    ⟨#[], .refused .unresolvedHole, []⟩ rfl
  have hPend : pendingHoleId? (Obend.Core.Machine.initial (.hole slotId [])) = some slotId := rfl
  have hSlice : (machineGuestRunner limits).runSlice cell.tickSlice cell.guest =
      .refusedHole slotId ⟨#[], .refused .unresolvedHole, []⟩ := by
    simp [machineGuestRunner, hGuest, hTicks, runBoundedTrackingHole, hPend, Option.or, hStep, hTail]
  simp [stepVirtualizedCell, hSlice]

/-- Delayed multi-step `.hole` attribution: demanding `.hole slotId []` *after* stepping through
    a dynamic `.ifBool (.boolean true)` guard still attributes the exact `slotId` (never `0`!). -/
theorem machineGuestRunner_delayed_hole_traps_to_sponsor (limits : Limits)
    (pol : Term → PinInterposition) (cell : VirtualizedCell State) (slotId extraTicks : Nat)
    (hStackLim : 1 ≤ limits.stack)
    (hGuest : cell.guest = Obend.Core.Machine.initial (.ifBool (.boolean true) (.hole slotId []) (.nat 0)))
    (hTicks : cell.tickSlice = extraTicks + 4) :
    let next := stepVirtualizedCell (machineGuestRunner limits) pol cell
    next.blameLog = .incoherentHoleTrap slotId :: cell.blameLog ∧
    next.committedEffects = cell.committedEffects := by
  let s0 := Obend.Core.Machine.initial (.ifBool (.boolean true) (.hole slotId []) (.nat 0))
  let s1 : State := ⟨#[], .evaluate (.boolean true) [], [.ifBool (.hole slotId []) (.nat 0) []]⟩
  let s2 : State := ⟨#[], .returned (.boolean true), [.ifBool (.hole slotId []) (.nat 0) []]⟩
  let s3 : State := ⟨#[], .evaluate (.hole slotId []) [], []⟩
  let s4 : State := ⟨#[], .refused .unresolvedHole, []⟩
  have hs0 : Obend.Core.Machine.step limits s0 = .suspended .ticks s1 := by
    simp [s0, s1, Obend.Core.Machine.step, Obend.Core.Machine.initial, Obend.Core.Machine.stepRaw, hStackLim]
  have hs1 : Obend.Core.Machine.step limits s1 = .suspended .ticks s2 := by
    simp [s1, s2, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw, hStackLim]
  have hs2 : Obend.Core.Machine.step limits s2 = .suspended .ticks s3 := by
    simp [s2, s3, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw]
  have hs3 : Obend.Core.Machine.step limits s3 = .suspended .ticks s4 := by
    simp [s3, s4, Obend.Core.Machine.step, Obend.Core.Machine.stepRaw]
  have hTail := runBoundedTrackingHole_already_refused limits extraTicks slotId s4 rfl
  have hEqT : extraTicks + 4 = (((extraTicks + 1) + 1) + 1) + 1 := by omega
  have hTrack : runBoundedTrackingHole limits (extraTicks + 4) none s0 =
      (some slotId, .refused .unresolvedHole s4) := by
    rw [hEqT]
    simp [runBoundedTrackingHole, s0, s1, s2, s3, pendingHoleId?, Option.or, hs0, hs1, hs2, hs3, hTail]
  have hSlice : (machineGuestRunner limits).runSlice cell.tickSlice cell.guest =
      .refusedHole slotId s4 := by
    simp [machineGuestRunner, hGuest, hTicks, s0, hTrack]
  simp [stepVirtualizedCell, hSlice]

/-- Full-abstraction honeypot equivalence instantiated directly on `Machine.State`:
    a yielded `Machine.State` resumed via `.deliverReal capId resp` (`capId ∈ heldCaps`) vs
    `.deliverHoneypot resp` reaches the **exact same `Machine.State`** (same heap, control, and stack),
    while `.deliverHoneypot` suppresses all parent `committedEffects` and sets `inHoneypot = true`. -/
theorem machineGuestRunner_honeypot_indistinguishable (limits : Limits)
    (cell : VirtualizedCell State) (capId : Nat) (plan resp : Term) (extraTicks : Nat)
    (hCap : cell.heldCaps.contains capId = true)
    (hHeapLim : 1 ≤ limits.heap)
    (hGuest : cell.guest = Obend.Core.Machine.initial (.perform plan))
    (hTicks : cell.tickSlice = extraTicks + 1) :
    (stepVirtualizedCell (machineGuestRunner limits) (fun _ => .deliverReal capId resp) cell).guest =
      (stepVirtualizedCell (machineGuestRunner limits) (fun _ => .deliverHoneypot resp) cell).guest ∧
    (stepVirtualizedCell (machineGuestRunner limits) (fun _ => .deliverHoneypot resp) cell).committedEffects =
      cell.committedEffects ∧
    (stepVirtualizedCell (machineGuestRunner limits) (fun _ => .deliverHoneypot resp) cell).inHoneypot = true := by
  have hStep : Obend.Core.Machine.step limits (Obend.Core.Machine.initial (.perform plan)) =
      .suspended .ticks ⟨#[.suspended ⟨plan, []⟩], .yielded 0, []⟩ := by
    simp [Obend.Core.Machine.step, Obend.Core.Machine.initial, Obend.Core.Machine.stepRaw,
      Obend.Core.Machine.forcingShared, hHeapLim]
  have hRun : ∀ k, runBoundedTrackingHole limits k none ⟨#[.suspended ⟨plan, []⟩], .yielded 0, []⟩ =
      (none, .yielded 0 ⟨#[.suspended ⟨plan, []⟩], .yielded 0, []⟩) := by
    intro k; cases k <;> simp [runBoundedTrackingHole, pendingHoleId?, Option.or, Obend.Core.Machine.step]
  have hPend : pendingHoleId? (Obend.Core.Machine.initial (.perform plan)) = none := rfl
  have hSlice : (machineGuestRunner limits).runSlice cell.tickSlice cell.guest =
      .yielded plan ⟨#[.suspended ⟨plan, []⟩], .yielded 0, []⟩ := by
    simp [machineGuestRunner, hGuest, hTicks, runBoundedTrackingHole, hPend, Option.or, hStep, hRun]
  exact virtualized_honeypot_indistinguishable_to_guest
    (machineGuestRunner limits) cell capId resp _ plan hCap hSlice

/-! ## 2. Closed-Term Checker & `ImplementationRegime (C : Type)` (`(A, I ⊳ C)`) -/

/-- Executable closedness check (`Scoped 0 t`) backed by `Traverse.Tree.all`. -/
@[expose] def isClosedTerm (t : Term) : Bool :=
  Obend.Core.Traverse.Tree.all (fun _ => false) (Obend.Core.TermTraverse.encode t)

theorem isClosedTerm_iff (t : Term) : isClosedTerm t = true ↔ Scoped 0 t := by
  unfold isClosedTerm Scoped
  rw [Obend.Core.Traverse.Tree.all_eq_true]
  exact Obend.Core.Traverse.Tree.all_congr _ _ _ (fun _ => by simp)

private theorem scoped_done_inv {v : Term} (h : Scoped 0 (.done v)) : Scoped 0 v := by
  rw [← isClosedTerm_iff] at h ⊢
  simpa [isClosedTerm, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.all] using h

private theorem scoped_ifBool_inv {c wt wf : Term} (h : Scoped 0 (.ifBool c wt wf)) :
    Scoped 0 c ∧ Scoped 0 wt ∧ Scoped 0 wf := by
  rw [← isClosedTerm_iff] at h
  simp only [isClosedTerm, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.all,
    List.map, List.all, id_eq, Bool.and_eq_true, and_true] at h
  exact ⟨(isClosedTerm_iff c).1 h.1, (isClosedTerm_iff wt).1 h.2.1, (isClosedTerm_iff wf).1 h.2.2⟩

private theorem scoped_fix_inv {s i : Term} (h : Scoped 0 (.fix s i)) : Scoped 0 s ∧ Scoped 0 i := by
  rw [← isClosedTerm_iff] at h
  simp only [isClosedTerm, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.all,
    List.map, List.all, id_eq, Bool.and_eq_true, and_true] at h
  exact ⟨(isClosedTerm_iff s).1 h.1, (isClosedTerm_iff i).1 h.2⟩

/-- An `ImplementationRegime C` packages:
    - `lower`: partial compilation from closed `Core.Term` into carrier `C`,
    - `reify`: sharing-preserving decompilation back into `Core.Term`,
    - `stepMetered`: bounded execution within a `CompositeGrade` budget returning `(c', spent)`,
    - Adequacy proofs witnessing `spent ≤ budget`, `lower`/`reify` `IEquiv` roundtrip, and
      `stepMetered` semantic preservation up to `IEquiv`. -/
structure ImplementationRegime (C : Type) where
  regimeTag : String
  lower : Term → Option C
  reify : C → Except ReifyError Term
  wellFormed : C → Prop
  stepMetered : CompositeGrade → C → C × CompositeGrade
  spent_le_budget : ∀ (budget : CompositeGrade) (c : C),
    0 ≤ budget.exergy → (stepMetered budget c).2 ≤ budget
  lower_wf : ∀ (t : Term) (c : C), Scoped 0 t → lower t = some c → wellFormed c
  lower_reify_iequiv : ∀ (t : Term) (c : C),
    Scoped 0 t → lower t = some c → ∃ t', reify c = .ok t' ∧ IEquiv t' t
  step_preserves_semantics : ∀ (budget : CompositeGrade) (c : C) (t₁ : Term),
    wellFormed c → reify c = .ok t₁ →
    let res := stepMetered budget c
    wellFormed res.1 ∧ ∃ t₂, reify res.1 = .ok t₂ ∧ IEquiv t₂ t₁

def zeroGrade : CompositeGrade := ⟨0, 0, 0, 0, 0⟩
def oneCycleGrade : CompositeGrade := ⟨0, 0, 0, 1, 0⟩

private theorem zeroGrade_le_of_nonneg {b : CompositeGrade} (hx : 0 ≤ b.exergy) : zeroGrade ≤ b :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hx⟩

private theorem oneCycle_le_of_pos {b : CompositeGrade} (hc : 1 ≤ b.cycles) (hx : 0 ≤ b.exergy) :
    oneCycleGrade ≤ b :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hc, hx⟩

/-- Pure 1-step reduction on `Core.Term` for arithmetic primitives, `.done`, and `.ifBool`. -/
def stepCanonicalTerm (t : Term) : Option Term :=
  match t with
  | .done v => some v
  | .ifBool (.boolean true) wt _ => some wt
  | .ifBool (.boolean false) _ wf => some wf
  | .binary .add (.nat a) (.nat b) => some (.nat (a + b))
  | .binary .subtract (.nat a) (.nat b) => some (.nat (a - b))
  | _ => none

theorem stepCanonicalTerm_complete (a b : Nat) :
    stepCanonicalTerm (.binary .add (.nat a) (.nat b)) = some (.nat (a + b)) := by rfl

private theorem stepCanonicalTerm_sound {t t' : Term} (hSc : Scoped 0 t)
    (hSt : stepCanonicalTerm t = some t') : Scoped 0 t' ∧ Step t t' := by
  unfold stepCanonicalTerm at hSt
  cases t with
  | done v =>
    simp only [Option.some.injEq] at hSt; subst hSt
    exact ⟨scoped_done_inv hSc, .done v⟩
  | ifBool cond wt wf =>
    cases cond with
    | boolean b =>
      cases b <;> simp only [Option.some.injEq] at hSt <;> subst hSt
      · exact ⟨(scoped_ifBool_inv hSc).2.2, .ifFalse wt wf⟩
      · exact ⟨(scoped_ifBool_inv hSc).2.1, .ifTrue wt wf⟩
    | _ => simp at hSt
  | binary op lhs rhs =>
    cases op <;> try (simp at hSt; done)
    all_goals
      cases lhs <;> try (simp at hSt; done)
      cases rhs <;> try (simp at hSt; done)
      simp only [Option.some.injEq] at hSt; subst hSt
      exact ⟨(isClosedTerm_iff _).1
        (by simp [isClosedTerm, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.all]),
        .primitive _ _ _ _ (.natural _) (.natural _) rfl⟩
  | _ => simp at hSt

/-- **Regime 1 (`termCanonicalRegime`)**: direct closed `Core.Term` reference interpreter. -/
@[expose] def termCanonicalRegime : ImplementationRegime Term where
  regimeTag := "Core.Term"
  lower t := if isClosedTerm t then some t else none
  reify t := .ok t
  wellFormed t := Scoped 0 t
  stepMetered budget t :=
    if 1 ≤ budget.cycles then
      match stepCanonicalTerm t with
      | some t' => (t', oneCycleGrade)
      | none => (t, zeroGrade)
    else (t, zeroGrade)
  spent_le_budget budget t hx := by
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases stepCanonicalTerm t with
      | some _ => exact oneCycle_le_of_pos hc hx
      | none => exact zeroGrade_le_of_nonneg hx
    · simp only [hc, ite_false]; exact zeroGrade_le_of_nonneg hx
  lower_wf t c hSc hLow := by
    have hCl : isClosedTerm t = true := (isClosedTerm_iff t).2 hSc
    simp only [hCl, ite_true, Option.some.injEq] at hLow; subst hLow; exact hSc
  lower_reify_iequiv t c hSc hLow := by
    have hCl : isClosedTerm t = true := (isClosedTerm_iff t).2 hSc
    simp only [hCl, ite_true, Option.some.injEq] at hLow; subst hLow
    exact ⟨t, rfl, IEquiv.refl t⟩
  step_preserves_semantics budget c t₁ hWf hReify := by
    simp only [Except.ok.injEq] at hReify; subst hReify
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases hStep : stepCanonicalTerm c with
      | none => exact ⟨hWf, c, rfl, IEquiv.refl c⟩
      | some c' =>
        obtain ⟨hSc', hRed⟩ := stepCanonicalTerm_sound hWf hStep
        exact ⟨hSc', c', rfl, (iequiv_of_ahead (Ahead.ofStepsRefl (.next hRed (.refl _)))).symm⟩
    · simp only [hc, ite_false]; exact ⟨hWf, c, rfl, IEquiv.refl c⟩

/-- Step an initial closed `.fix` knot or closed `.binary .add (.nat a) (.nat b)` machine state. -/
def stepMachineKnot (st : State) : Option State :=
  match st.heap.toList, st.control, st.stack with
  | [], .evaluate (.fix spec inh) [], [] =>
      if isClosedTerm (.fix spec inh) then
        some (Obend.Core.Machine.stepRaw (Obend.Core.Machine.initial (.fix spec inh)))
      else none
  | [], .evaluate (.binary .add (.nat a) (.nat b)) [], [] =>
      some ⟨#[], .complete (.natural (a + b)), []⟩
  | _, _, _ => none

private theorem stepMachineKnot_preserves {st st' : State} {t₁ : Term}
    (hKnot : stepMachineKnot st = some st')
    (hReify : reifyMachineDag st = .ok t₁) :
    ∃ t₂, reifyMachineDag st' = .ok t₂ ∧ IEquiv t₂ t₁ := by
  rcases st with ⟨heap, ctrl, stk⟩
  unfold stepMachineKnot at hKnot
  cases hList : heap.toList with
  | cons _ _ => simp [hList] at hKnot
  | nil =>
    have hEmpty : heap = #[] := Array.ext' hList
    subst hEmpty
    cases ctrl with
    | evaluate tm env =>
      cases tm with
      | fix spec inh =>
        cases env with
        | cons _ _ => simp at hKnot
        | nil =>
          cases stk with
          | cons _ _ => simp at hKnot
          | nil =>
            dsimp only at hKnot
            by_cases hCl : isClosedTerm (.fix spec inh) = true
            · simp only [hCl, ite_true, Option.some.injEq] at hKnot
              subst hKnot
              have hScFix : Scoped 0 (.fix spec inh) := (isClosedTerm_iff _).1 hCl
              obtain ⟨hSpec, hInh⟩ := scoped_fix_inv hScFix
              have hInit : reifyMachineDag (Obend.Core.Machine.initial (.fix spec inh)) =
                  .ok (.fix spec inh) := reifyMachineDag_initial (.fix spec inh) hScFix
              change reifyMachineDag (Obend.Core.Machine.initial (.fix spec inh)) = .ok t₁ at hReify
              rw [hInit] at hReify; injection hReify with hEqT; subst hEqT
              exact reifyMachineDag_fix_step_iequiv spec inh hSpec hInh
            · simp [hCl] at hKnot
      | binary op lhs rhs =>
        cases op <;> try (simp at hKnot; done)
        cases lhs <;> try (simp at hKnot; done)
        cases rhs <;> try (simp at hKnot; done)
        cases env <;> try (simp at hKnot; done)
        cases stk <;> try (simp at hKnot; done)
        rename_i a b
        simp only [Option.some.injEq] at hKnot; subst hKnot
        have hScAdd : Scoped 0 (.binary .add (.nat a) (.nat b)) := (isClosedTerm_iff _).1
          (by simp [isClosedTerm, Obend.Core.TermTraverse.encode, Obend.Core.Traverse.Tree.all])
        have hInit : reifyMachineDag (Obend.Core.Machine.initial (.binary .add (.nat a) (.nat b))) =
            .ok (.binary .add (.nat a) (.nat b)) := reifyMachineDag_initial _ hScAdd
        change reifyMachineDag (Obend.Core.Machine.initial (.binary .add (.nat a) (.nat b))) = .ok t₁ at hReify
        rw [hInit] at hReify; injection hReify with hEqT; subst hEqT
        have hRed : Step (.binary .add (.nat a) (.nat b)) (.nat (a + b)) :=
          .primitive .add _ _ _ (.natural a) (.natural b) rfl
        exact ⟨.nat (a + b), reifyMachineDag_complete_nat (a + b),
          (iequiv_of_ahead (Ahead.ofStepsRefl (.next hRed (.refl _)))).symm⟩
      | _ => simp at hKnot
    | _ => simp at hKnot

/-- **Regime 2 (`machineHeapRegime`)**: lazy heap-sharing `Core.Machine.State` backed by
    DAG-sharing `reifyMachineDag` (recovering cyclic `.fix` heap knots!). -/
@[expose] def machineHeapRegime : ImplementationRegime State where
  regimeTag := "Core.Machine.HeapDAG"
  lower t := if isClosedTerm t then some (Obend.Core.Machine.initial t) else none
  reify := reifyMachineDag
  wellFormed st := ∃ t, reifyMachineDag st = .ok t
  stepMetered budget st :=
    if 1 ≤ budget.cycles then
      match stepMachineKnot st with
      | some st' => (st', oneCycleGrade)
      | none => (st, zeroGrade)
    else (st, zeroGrade)
  spent_le_budget budget st hx := by
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases stepMachineKnot st with
      | some _ => exact oneCycle_le_of_pos hc hx
      | none => exact zeroGrade_le_of_nonneg hx
    · simp only [hc, ite_false]; exact zeroGrade_le_of_nonneg hx
  lower_wf t c hSc hLow := by
    have hCl : isClosedTerm t = true := (isClosedTerm_iff t).2 hSc
    simp only [hCl, ite_true, Option.some.injEq] at hLow; subst hLow
    exact ⟨t, reifyMachineDag_initial t hSc⟩
  lower_reify_iequiv t c hSc hLow := by
    have hCl : isClosedTerm t = true := (isClosedTerm_iff t).2 hSc
    simp only [hCl, ite_true, Option.some.injEq] at hLow; subst hLow
    exact ⟨t, reifyMachineDag_initial t hSc, IEquiv.refl t⟩
  step_preserves_semantics budget st t₁ hWf hReify := by
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases hKnot : stepMachineKnot st with
      | none => exact ⟨hWf, t₁, hReify, IEquiv.refl t₁⟩
      | some st' =>
        obtain ⟨t₂, hR₂, hEqv⟩ := stepMachineKnot_preserves hKnot hReify
        exact ⟨⟨t₂, hR₂⟩, t₂, hR₂, hEqv⟩
    · simp only [hc, ite_false]; exact ⟨hWf, t₁, hReify, IEquiv.refl t₁⟩

/-- 64-bit synchronous RTL combinational carrier (`RtlExpr` + optional latched `BitVec 64` word). -/
structure RtlWordCarrier where
  sourceTerm : Term
  rtlNet     : RtlExpr
  wordVal?   : Option (BitVec 64)
  deriving Repr

def zeroBus : Nat → BitVec 64 := fun _ => 0#64

private theorem closeTerm_nil (t : Term) : closeTerm [] t = t := by
  have hSub : envSubst [] = fun j => Term.bound j := by funext j; simp [envSubst]
  rw [closeTerm, hSub, term_substitute_id]

private theorem steps_from_stuck_eq {a b : Term} (hs : Steps a b) (hNoStep : ∀ u, ¬ Step a u) : a = b := by
  cases hs with
  | refl _ => rfl
  | next st _ => exact False.elim (hNoStep _ st)

private theorem steps_confluence_to_stuck {t u v : Term}
    (s₁ : Steps t u) (hNoStepU : ∀ x, ¬ Step u x) (s₂ : Steps t v) : Steps v u := by
  induction s₂ with
  | refl _ => exact s₁
  | next st₂ _ ih =>
    cases s₁ with
    | refl _ => exact False.elim (hNoStepU _ st₂)
    | next st₁ rest₁ =>
      obtain rfl := Obend.Equiv.step_deterministic st₂ st₁
      exact ih rest₁

private theorem add_bool_zero_impossible {b : Bool} {vAdd : Term}
    (hEval : Evaluates (.binary .add (.boolean b) (.nat 0)) vAdd) : False := by
  have hStuck : ∀ x, ¬ Step (.binary .add (.boolean b) (.nat 0)) x := by
    intro x hSt
    cases hSt with
    | binaryLeft _ _ hs => cases hs
    | binaryRight _ _ _ hs => cases hs
    | primitive _ _ _ _ _ _ hp => simp [primitiveResult] at hp
  have hEq := steps_from_stuck_eq hEval.1 hStuck
  rw [← hEq] at hEval
  cases hEval.2

def RtlWordWF (c : RtlWordCarrier) : Prop :=
  checkRangeSafeHw [] c.sourceTerm = true ∧
  checkRangeSafeHw [] (.binary .add c.sourceTerm (.nat 0)) = true ∧
  compileTerm [] [] 0 [] c.sourceTerm = some c.rtlNet ∧
  ∀ w, c.wordVal? = some w → w = evalRtlExpr zeroBus zeroBus zeroBus c.rtlNet

private theorem rtlWordWF_evaluates_exact {c : RtlWordCarrier} (hWf : RtlWordWF c) :
    Evaluates c.sourceTerm (.nat (evalRtlExpr zeroBus zeroBus zeroBus c.rtlNet).toNat) := by
  obtain ⟨hSafe, hSafeAdd, hComp, _⟩ := hWf
  have hCompAdd : compileTerm [] [] 0 [] (.binary .add c.sourceTerm (.nat 0)) =
      some (.alu .add c.rtlNet (.const 0#64)) := by
    simp [compileTerm, hComp, compilePrim]
  obtain ⟨I, v, _, hEvalT, hValIn, _, hToNat⟩ :=
    compileTerm_evaluates_sound zeroBus zeroBus zeroBus [] [] 0 [] [] [] c.sourceTerm c.rtlNet
      hSafe hComp hwEnvAgrees_nil
  obtain ⟨_, vAdd, _, hEvalAdd, _, _, _⟩ :=
    compileTerm_evaluates_sound zeroBus zeroBus zeroBus [] [] 0 [] [] []
      (.binary .add c.sourceTerm (.nat 0)) (.alu .add c.rtlNet (.const 0#64))
      hSafeAdd hCompAdd hwEnvAgrees_nil
  rw [closeTerm_nil] at hEvalT hEvalAdd
  cases hs : I.sort <;> simp only [ValueInInterval, hs] at hValIn
  · obtain ⟨n, rfl, _, _⟩ := hValIn
    dsimp only [scalarToNat] at hToNat
    rw [hToNat]; exact hEvalT
  · obtain ⟨b, rfl, _, _⟩ := hValIn
    have hStepsBool : Steps (.binary .add c.sourceTerm (.nat 0)) (.binary .add (.boolean b) (.nat 0)) :=
      steps_binaryLeft (.nat 0) hEvalT.1
    have hStuckBool : ∀ x, ¬ Step (.binary .add (.boolean b) (.nat 0)) x := by
      intro x hSt; cases hSt with
      | binaryLeft _ _ hs' => cases hs'
      | binaryRight _ _ _ hs' => cases hs'
      | primitive _ _ _ _ _ _ hp => simp [primitiveResult] at hp
    have hVAddToBool := steps_confluence_to_stuck hStepsBool hStuckBool hEvalAdd.1
    have hVAddStuck : ∀ x, ¬ Step vAdd x := fun _ hSt => value_no_step hEvalAdd.2 hSt
    have hEqV := steps_from_stuck_eq hVAddToBool hVAddStuck
    have hValFalse : Value (.binary .add (.boolean b) (.nat 0)) := hEqV ▸ hEvalAdd.2
    cases hValFalse

/-- **Regime 3 (`rtlWordRegime`)**: `RangeSafe`-guarded 64-bit synchronous RTL combinational
    datapath (`RtlExpr` + `BitVec 64` word latch), sound via `compileTerm_evaluates_sound`. -/
@[expose] def rtlWordRegime : ImplementationRegime RtlWordCarrier where
  regimeTag := "Hardware.RTL.BitVec64"
  lower t :=
    if isClosedTerm t && checkRangeSafeHw [] t && checkRangeSafeHw [] (.binary .add t (.nat 0)) then
      match compileTerm [] [] 0 [] t with
      | some rtl => some ⟨t, rtl, none⟩
      | none => none
    else none
  reify c :=
    match c.wordVal? with
    | none => .ok c.sourceTerm
    | some w => .ok (.nat w.toNat)
  wellFormed := RtlWordWF
  stepMetered budget c :=
    if 1 ≤ budget.cycles then
      match c.wordVal? with
      | none =>
          let w := evalRtlExpr zeroBus zeroBus zeroBus c.rtlNet
          ({ c with wordVal? := some w }, oneCycleGrade)
      | some _ => (c, zeroGrade)
    else (c, zeroGrade)
  spent_le_budget budget c hx := by
    dsimp only
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases c.wordVal? with
      | none => exact oneCycle_le_of_pos hc hx
      | some _ => exact zeroGrade_le_of_nonneg hx
    · simp only [hc, ite_false]; exact zeroGrade_le_of_nonneg hx
  lower_wf t c _ hLow := by
    by_cases hG : (isClosedTerm t && checkRangeSafeHw [] t && checkRangeSafeHw [] (.binary .add t (.nat 0))) = true
    · simp only [hG, ite_true] at hLow
      cases hComp : compileTerm [] [] 0 [] t with
      | none => simp [hComp] at hLow
      | some rtl =>
        simp only [hComp, Option.some.injEq] at hLow; subst hLow
        simp only [Bool.and_eq_true] at hG
        exact ⟨hG.1.2, hG.2, hComp, fun _ hw => by simp at hw⟩
    · simp [hG] at hLow
  lower_reify_iequiv t c _ hLow := by
    by_cases hG : (isClosedTerm t && checkRangeSafeHw [] t && checkRangeSafeHw [] (.binary .add t (.nat 0))) = true
    · simp only [hG, ite_true] at hLow
      cases hComp : compileTerm [] [] 0 [] t with
      | none => simp [hComp] at hLow
      | some rtl =>
        simp only [hComp, Option.some.injEq] at hLow; subst hLow
        exact ⟨t, rfl, IEquiv.refl t⟩
    · simp [hG] at hLow
  step_preserves_semantics budget c t₁ hWf hReify := by
    dsimp only
    by_cases hc : 1 ≤ budget.cycles
    · simp only [hc, ite_true]
      cases hw : c.wordVal? with
      | some w =>
        simp only [hw, Except.ok.injEq] at hReify; subst hReify
        exact ⟨hWf, .nat w.toNat, by simp [hw], IEquiv.refl _⟩
      | none =>
        simp only [hw, Except.ok.injEq] at hReify; subst hReify
        have hEval := rtlWordWF_evaluates_exact hWf
        refine ⟨⟨hWf.1, hWf.2.1, hWf.2.2.1, fun w' hw' => ?_⟩,
          .nat (evalRtlExpr zeroBus zeroBus zeroBus c.rtlNet).toNat, ?_,
          (iequiv_of_ahead (Ahead.ofStepsRefl hEval.1)).symm⟩
        · simp only [Option.some.injEq] at hw'; exact hw'.symm
        · rfl
    · simp only [hc, ite_false]; exact ⟨hWf, t₁, hReify, IEquiv.refl t₁⟩

/-- Any term failing `checkRangeSafeHw []` (such as 64-bit wraparound `hwOverflowTerm`) is
    deterministically refused by `rtlWordRegime.lower`. -/
theorem rtlWordRegime_refuses_wraparound (t : Term) (hUnsafe : checkRangeSafeHw [] t = false) :
    rtlWordRegime.lower t = none := by
  simp [rtlWordRegime, hUnsafe]

/-! ## 3. Reflective `SponsorTower`, Preemptive `CompositeGrade` Metering & `SponsorAction` -/

/-- Sponsor-level pin routing policy mapping directly into `Polis.HouyhnhnmMonitor.PinInterposition`
    (zero ambient `EPERM` error channel inside guest `Core.Term`). -/
inductive SponsorAction where
  | inlinePeerDeliver (capId : Nat) (response : Term)
  | virtualHoneypot (syntheticResponse : Term)
  | speculativeFork (branchId : Nat) (syntheticResponse : Term)
  | escalateHorizon (capTag : Nat)
  deriving Repr

def SponsorAction.toInterposition : SponsorAction → PinInterposition
  | .inlinePeerDeliver capId resp => .deliverReal capId resp
  | .virtualHoneypot resp => .deliverHoneypot resp
  | .speculativeFork bid resp => .forkSpeculative bid resp
  | .escalateHorizon tag => .freezeToSupervisor tag

@[expose] def subsetCaps (sub sup : List Nat) : Bool :=
  sub.all (fun c => sup.contains c)

theorem subsetCaps_refl (cs : List Nat) : subsetCaps cs cs = true := by
  simp [subsetCaps, List.all_eq_true]

theorem subsetCaps_trans {a b c : List Nat} (hab : subsetCaps a b = true)
    (hbc : subsetCaps b c = true) : subsetCaps a c = true := by
  simp only [subsetCaps, List.all_eq_true] at hab hbc ⊢
  intro x hx; exact hbc x (List.contains_iff_mem.1 (hab x hx))

/-- Preemptive remaining-budget subtraction on `CompositeGrade`. -/
def remainingGrade (quota spent : CompositeGrade) : CompositeGrade where
  uses := quota.uses - spent.uses
  errorNum := quota.errorNum - spent.errorNum
  noise := quota.noise - spent.noise
  cycles := quota.cycles - spent.cycles
  exergy := max 0 (quota.exergy - spent.exergy)

theorem spent_add_le_quota_of_le_remaining {quota spent delta : CompositeGrade}
    (hSpent : spent ≤ quota) (hDelta : delta ≤ remainingGrade quota spent) :
    spent + delta ≤ quota := by
  rcases hSpent with ⟨hu, he, hn, hc, hx⟩
  rcases hDelta with ⟨du, de, dn, dc, dx⟩
  simp only [remainingGrade] at du de dn dc dx
  exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩

/-- Live metered cell pairing a carrier `C` with held capabilities, prepaid `quota`, and `spent`. -/
structure SponsoredCell (C : Type) where
  cellId   : Nat
  heldCaps : List Nat
  quota    : CompositeGrade
  spent    : CompositeGrade
  carrier  : C

abbrev SponsoredCellWF {C : Type} (R : ImplementationRegime C) (cell : SponsoredCell C) : Prop :=
  R.wellFormed cell.carrier ∧ cell.spent ≤ cell.quota

/-- Step a `SponsoredCell C` under preemptive remaining-budget metering (`rem = remainingGrade quota spent`),
    so cumulative `spent + stepDelta ≤ quota` can NEVER overshoot `quota`! -/
@[expose] def stepSponsoredCell {C : Type} (R : ImplementationRegime C)
    (cell : SponsoredCell C) : SponsoredCell C :=
  let rem := remainingGrade cell.quota cell.spent
  let (nextC, delta) := R.stepMetered rem cell.carrier
  { cell with
    spent := cell.spent + delta
    carrier := nextC }

theorem stepSponsoredCell_preserves_wf {C : Type} (R : ImplementationRegime C)
    (cell : SponsoredCell C) (t₁ : Term)
    (hWf : SponsoredCellWF R cell) (hReify : R.reify cell.carrier = .ok t₁) :
    let next := stepSponsoredCell R cell
    SponsoredCellWF R next ∧ next.heldCaps = cell.heldCaps ∧
    ∃ t₂, R.reify next.carrier = .ok t₂ ∧ IEquiv t₂ t₁ := by
  have hRemEx : 0 ≤ (remainingGrade cell.quota cell.spent).exergy := by
    simp [remainingGrade]; omega
  have hDelta := R.spent_le_budget (remainingGrade cell.quota cell.spent) cell.carrier hRemEx
  obtain ⟨hNextWf, t₂, hR₂, hEqv⟩ := R.step_preserves_semantics
    (remainingGrade cell.quota cell.spent) cell.carrier t₁ hWf.1 hReify
  exact ⟨⟨hNextWf, spent_add_le_quota_of_le_remaining hWf.2 hDelta⟩, rfl, t₂, hR₂, hEqv⟩

/-- Multi-turn execution trace of a `SponsoredCell C`. -/
inductive ValidSponsorTrace {C : Type} (R : ImplementationRegime C) :
    SponsoredCell C → Nat → SponsoredCell C → Prop where
  | zero (cell : SponsoredCell C) : ValidSponsorTrace R cell 0 cell
  | succ {cell mid : SponsoredCell C} {n : Nat} :
      ValidSponsorTrace R cell n mid →
      ValidSponsorTrace R cell (n + 1) (stepSponsoredCell R mid)

theorem validSponsorTrace_preserves_invariants {C : Type} (R : ImplementationRegime C)
    {c₀ cₙ : SponsoredCell C} {n : Nat} {t₀ : Term}
    (hTr : ValidSponsorTrace R c₀ n cₙ)
    (hWf₀ : SponsoredCellWF R c₀) (hR₀ : R.reify c₀.carrier = .ok t₀) :
    SponsoredCellWF R cₙ ∧ cₙ.heldCaps = c₀.heldCaps ∧ cₙ.quota = c₀.quota ∧
    ∃ tₙ, R.reify cₙ.carrier = .ok tₙ ∧ IEquiv tₙ t₀ := by
  induction hTr with
  | zero => exact ⟨hWf₀, rfl, rfl, t₀, hR₀, IEquiv.refl t₀⟩
  | succ _ ih =>
    obtain ⟨hWfM, hCapsM, hQuotaM, tM, hRM, hEqM⟩ := ih
    obtain ⟨hWfNext, hCapsNext, tNext, hRNext, hEqNext⟩ :=
      stepSponsoredCell_preserves_wf R _ tM hWfM hRM
    exact ⟨hWfNext, hCapsNext.trans hCapsM, hQuotaM, tNext, hRNext, hEqNext.trans hEqM⟩

/-- Arbitrary-depth reflective `SponsorTower` hierarchy: supervisors sub-delegate slices of their
    `CompositeGrade` quota and attenuated subsets of their `heldCaps` to nested children. -/
inductive SponsorTower where
  | leaf (cellId : Nat) (heldCaps : List Nat) (quota spent : CompositeGrade) (regimeTag : String)
  | supervisor (supId : Nat) (heldCaps : List Nat) (quota overheadSpent : CompositeGrade)
      (children : List SponsorTower)
  deriving Repr

def SponsorTower.capsOf : SponsorTower → List Nat
  | .leaf _ cs _ _ _ => cs
  | .supervisor _ cs _ _ _ => cs

def SponsorTower.quotaOf : SponsorTower → CompositeGrade
  | .leaf _ _ q _ _ => q
  | .supervisor _ _ q _ _ => q

def sumGrades : List CompositeGrade → CompositeGrade
  | [] => zeroGrade
  | g :: gs => g + sumGrades gs

/-- Total resource expenditure (`spent` + `overheadSpent`) summed across an entire `SponsorTower`. -/
def SponsorTower.totalSpent : SponsorTower → CompositeGrade
  | .leaf _ _ _ s _ => s
  | .supervisor _ _ _ ov cs => ov + sumGrades (cs.map SponsorTower.totalSpent)
termination_by t => sizeOf t
decreasing_by
  simp_wf; rename_i x hx; have := List.sizeOf_lt_of_mem hx; omega

/-- Every capability list held anywhere inside a `SponsorTower` subtree. -/
def SponsorTower.allCapSets : SponsorTower → List (List Nat)
  | .leaf _ cs _ _ _ => [cs]
  | .supervisor _ cs _ _ kids => cs :: (kids.map SponsorTower.allCapSets).flatten
termination_by t => sizeOf t
decreasing_by
  simp_wf; rename_i x hx; have := List.sizeOf_lt_of_mem hx; omega

/-- Decidable structural invariant for an arbitrary-depth `SponsorTower`:
    1. Every leaf satisfies `spent ≤ quota`,
    2. Every supervisor satisfies `overheadSpent + sumGrades (children.map quotaOf) ≤ quota`,
    3. Every child's `capsOf` is a subset of its parent's `capsOf`, and
    4. Every child recursively satisfies `SponsorTower.wf`. -/
@[expose] def SponsorTower.wf : SponsorTower → Bool
  | .leaf _ _ q s _ => decide (0 ≤ s.exergy) && decide (s ≤ q)
  | .supervisor _ cs q ov kids =>
      decide (0 ≤ ov.exergy) &&
      decide (ov + sumGrades (kids.map SponsorTower.quotaOf) ≤ q) &&
      kids.all (fun k => subsetCaps k.capsOf cs) &&
      kids.attach.all (fun ⟨k, _hk⟩ => SponsorTower.wf k)
termination_by t => sizeOf t
decreasing_by
  simp_wf; have := List.sizeOf_lt_of_mem _hk; omega

private theorem sumGrades_mono {xs ys : List CompositeGrade}
    (hLen : xs.length = ys.length)
    (hPt : ∀ p ∈ xs.zip ys, p.1 ≤ p.2) : sumGrades xs ≤ sumGrades ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact GradeMonoid.le_refl _
    | cons _ _ => simp at hLen
  | cons x rest ih =>
    cases ys with
    | nil => simp at hLen
    | cons y yrest =>
      have hHead : x ≤ y := hPt (x, y) (by simp)
      have hTail : sumGrades rest ≤ sumGrades yrest :=
        ih (Nat.succ.inj hLen) (fun p hp => hPt p (by simp [hp]))
      exact GradeMonoid.add_mono hHead hTail

private theorem sumGrades_nonneg_exergy {xs : List CompositeGrade}
    (hPos : ∀ g ∈ xs, 0 ≤ g.exergy) : 0 ≤ (sumGrades xs).exergy := by
  induction xs with
  | nil => exact Int.le_refl 0
  | cons g rest ih =>
    have hg := hPos g List.mem_cons_self
    have hr := ih (fun x hx => hPos x (List.mem_cons_of_mem g hx))
    show 0 ≤ g.exergy + (sumGrades rest).exergy; omega

private theorem zip_map_pair {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ xs : List α, (xs.map f).zip (xs.map g) = xs.map (fun x => (f x, g x))
  | [] => rfl
  | _ :: tl => by simp [zip_map_pair f g tl]

/-- **Global Conservation, Non-Negative Exergy & Monotonic Confinement of `SponsorTower`s**:
    Whenever `tower.wf = true`, `0 ≤ tower.totalSpent.exergy`, `0 ≤ tower.quotaOf.exergy` (preventing
    negative-exergy sibling inflation), `tower.totalSpent ≤ tower.quotaOf`, and every capability set
    anywhere in the tower is confined within root `tower.capsOf`. -/
theorem sponsorTower_global_confinement_and_budget (tower : SponsorTower) (hWf : tower.wf = true) :
    0 ≤ tower.totalSpent.exergy ∧ 0 ≤ tower.quotaOf.exergy ∧
    tower.totalSpent ≤ tower.quotaOf ∧
    ∀ cs ∈ tower.allCapSets, subsetCaps cs tower.capsOf = true := by
  match tower with
  | .leaf id rootCs q s tag =>
      rw [SponsorTower.wf] at hWf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
      rw [SponsorTower.totalSpent, SponsorTower.quotaOf, SponsorTower.capsOf, SponsorTower.allCapSets]
      refine ⟨hWf.1, Int.le_trans hWf.1 hWf.2.2.2.2.2, hWf.2, fun c hc => ?_⟩
      rcases List.mem_singleton.1 hc with rfl
      exact subsetCaps_refl c
  | .supervisor id rootCs q ov kids =>
      rw [SponsorTower.wf] at hWf
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_attach, Subtype.forall] at hWf
      obtain ⟨⟨⟨hOvEx, hBudget⟩, hSubCaps⟩, hKidsWf⟩ := hWf
      rw [SponsorTower.totalSpent, SponsorTower.quotaOf, SponsorTower.capsOf, SponsorTower.allCapSets]
      have hIH : ∀ (k : SponsorTower) (_hk : k ∈ kids),
          0 ≤ k.totalSpent.exergy ∧ 0 ≤ k.quotaOf.exergy ∧ k.totalSpent ≤ k.quotaOf ∧
          ∀ c ∈ k.allCapSets, subsetCaps c k.capsOf = true :=
        fun k hk => sponsorTower_global_confinement_and_budget k (hKidsWf k hk trivial)
      have hSumLe : sumGrades (kids.map SponsorTower.totalSpent) ≤
          sumGrades (kids.map SponsorTower.quotaOf) := by
        apply sumGrades_mono (by simp)
        intro p hp; rw [zip_map_pair, List.mem_map] at hp
        obtain ⟨k, hk, rfl⟩ := hp; exact (hIH k hk).2.2.1
      have hTotLe : ov + sumGrades (kids.map SponsorTower.totalSpent) ≤ q :=
        GradeMonoid.le_trans (GradeMonoid.add_mono (GradeMonoid.le_refl ov) hSumLe) hBudget
      have hTotEx : 0 ≤ (ov + sumGrades (kids.map SponsorTower.totalSpent)).exergy := by
        have hSubEx : 0 ≤ (sumGrades (kids.map SponsorTower.totalSpent)).exergy := by
          apply sumGrades_nonneg_exergy
          intro g hg; rw [List.mem_map] at hg; obtain ⟨k, hk, rfl⟩ := hg; exact (hIH k hk).1
        show 0 ≤ ov.exergy + (sumGrades (kids.map SponsorTower.totalSpent)).exergy; omega
      refine ⟨hTotEx, Int.le_trans hTotEx hTotLe.2.2.2.2, hTotLe, fun c hc => ?_⟩
      simp only [List.mem_cons, List.mem_flatten, List.mem_map] at hc
      rcases hc with rfl | ⟨subList, ⟨k, hk, rfl⟩, hcInK⟩
      · exact subsetCaps_refl c
      · exact subsetCaps_trans ((hIH k hk).2.2.2 c hcInK) (hSubCaps k hk)
termination_by sizeOf tower
decreasing_by
  simp_wf; have := List.sizeOf_lt_of_mem hk; omega

/-! ## 4. Cross-Regime Live Migration (`C₁ → Core.Term → C₂`) & Full Abstraction -/

/-- Migrate a live carrier state `c₁ : C₁` from `R₁` to `R₂` through the canonical `Core.Term`
    waist (`R₁.reify` followed by closedness verification and `R₂.lower`). -/
@[expose] def migrateRegime {C₁ C₂ : Type} (R₁ : ImplementationRegime C₁)
    (R₂ : ImplementationRegime C₂) (c₁ : C₁) : Option C₂ :=
  match R₁.reify c₁ with
  | .ok tMid =>
      if isClosedTerm tMid then R₂.lower tMid else none
  | .error _ => none

/-- Migrate a metered `SponsoredCell C₁` to `SponsoredCell C₂` with optional capability attenuation
    (`subsetCaps newCaps cell.heldCaps = true`), preserving `quota` and accumulated `spent`. -/
@[expose] def migrateSponsoredCell {C₁ C₂ : Type} (R₁ : ImplementationRegime C₁)
    (R₂ : ImplementationRegime C₂) (newCaps : List Nat)
    (cell : SponsoredCell C₁) : Option (SponsoredCell C₂) :=
  if subsetCaps newCaps cell.heldCaps then
    match migrateRegime R₁ R₂ cell.carrier with
    | some c₂ =>
        some { cellId := cell.cellId
               heldCaps := newCaps
               quota := cell.quota
               spent := cell.spent
               carrier := c₂ }
    | none => none
  else none

/-- **Cross-Regime Migration Preserves Observational Semantics & Full Abstraction**:
    1. **Semantic & Contextual Full Abstraction (`IEquiv` + `≈b`)**: migrating `c₁ : C₁` to `c₂ : C₂`
       preserves `IEquiv` across **every** substitution `ρ` and **every** `Core.Term` context `C`
       (`SameInteractions (instantiate C (t₂.substitute ρ)) (instantiate C (t₁.substitute ρ))` and
       `t₂ ≈b t₁`): no regime-blind `Core.Term` context can distinguish `C₁` from `C₂`.
    2. **Capability Confinement & Budget Continuity**: `migrateSponsoredCell` enforces
       `subsetCaps cell₂.heldCaps cell₁.heldCaps = true`, preserves `cell₂.spent = cell₁.spent ≤ cell₂.quota`,
       and establishes `SponsoredCellWF R₂ cell₂`. -/
theorem migrateRegime_preserves_semantics_and_full_abstraction
    {C₁ C₂ : Type} (R₁ : ImplementationRegime C₁) (R₂ : ImplementationRegime C₂) :
    (∀ (c₁ : C₁) (c₂ : C₂) (t₁ : Term),
      R₁.reify c₁ = .ok t₁ →
      migrateRegime R₁ R₂ c₁ = some c₂ →
      R₂.wellFormed c₂ ∧
      ∃ t₂, R₂.reify c₂ = .ok t₂ ∧ IEquiv t₂ t₁ ∧ (t₂ ≈b t₁) ∧
        (∀ (ρ : Nat → Term) (ctx : Term),
          SameInteractions (instantiate ctx (t₂.substitute ρ)) (instantiate ctx (t₁.substitute ρ)))) ∧
    (∀ (cell₁ : SponsoredCell C₁) (cell₂ : SponsoredCell C₂) (newCaps : List Nat) (t₁ : Term),
      SponsoredCellWF R₁ cell₁ →
      R₁.reify cell₁.carrier = .ok t₁ →
      migrateSponsoredCell R₁ R₂ newCaps cell₁ = some cell₂ →
      SponsoredCellWF R₂ cell₂ ∧
      subsetCaps cell₂.heldCaps cell₁.heldCaps = true ∧
      cell₂.spent = cell₁.spent ∧ cell₂.quota = cell₁.quota ∧
      ∃ t₂, R₂.reify cell₂.carrier = .ok t₂ ∧ IEquiv t₂ t₁) := by
  have hCore : ∀ (c₁ : C₁) (c₂ : C₂) (t₁ : Term),
      R₁.reify c₁ = .ok t₁ → migrateRegime R₁ R₂ c₁ = some c₂ →
      R₂.wellFormed c₂ ∧ ∃ t₂, R₂.reify c₂ = .ok t₂ ∧ IEquiv t₂ t₁ := by
    intro c₁ c₂ t₁ hR₁ hMig
    unfold migrateRegime at hMig
    rw [hR₁] at hMig; dsimp only at hMig
    by_cases hCl : isClosedTerm t₁ = true
    · simp only [hCl, ite_true] at hMig
      have hSc₁ : Scoped 0 t₁ := (isClosedTerm_iff t₁).1 hCl
      obtain ⟨t₂, hR₂, hEqv⟩ := R₂.lower_reify_iequiv t₁ c₂ hSc₁ hMig
      exact ⟨R₂.lower_wf t₁ c₂ hSc₁ hMig, t₂, hR₂, hEqv⟩
    · simp [hCl] at hMig
  refine ⟨fun c₁ c₂ t₁ hR₁ hMig => ?_, fun cell₁ cell₂ newCaps t₁ hWf₁ hR₁ hMigCell => ?_⟩
  · obtain ⟨hWf₂, t₂, hR₂, hEqv⟩ := hCore c₁ c₂ t₁ hR₁ hMig
    exact ⟨hWf₂, t₂, hR₂, hEqv, hEqv.bequiv, fun ρ ctx => hEqv ρ ctx⟩
  · unfold migrateSponsoredCell at hMigCell
    by_cases hSub : subsetCaps newCaps cell₁.heldCaps = true
    · simp only [hSub, ite_true] at hMigCell
      cases hMig : migrateRegime R₁ R₂ cell₁.carrier with
      | none => simp [hMig] at hMigCell
      | some c₂ =>
        simp only [hMig, Option.some.injEq] at hMigCell; subst hMigCell
        obtain ⟨hWf₂, t₂, hR₂, hEqv⟩ := hCore cell₁.carrier c₂ t₁ hR₁ hMig
        exact ⟨⟨hWf₂, hWf₁.2⟩, hSub, rfl, rfl, t₂, hR₂, hEqv⟩
    · simp [hSub] at hMigCell

end Obend.Metatheory.SponsorAndMigration
end
