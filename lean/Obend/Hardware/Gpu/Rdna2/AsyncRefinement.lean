module
public import Obend.Hardware.Gpu.Rdna2.Waitcnt
import Init.Data.List.Sublist
import Init.Data.String.Lemmas
import all Obend.Hardware.Gpu.Rdna2.Semantics

public section
namespace Obend.Hardware.Gpu.Rdna2
namespace Async
set_option autoImplicit false

/-!
Executable delayed writeback semantics for the existing decoded `Inst` and
`WaveState`. Loads evaluate addresses and latch data at ISSUE, but their register
writes become visible only at retirement. VM loads retire FIFO. LGKM retirement
indices are supplied by the environment; arbitrary order conservatively includes
SMEM reordering (and more schedules than a pure LDS stream permits).

Vector stores have their OWN VS queue, not VM_CNT. `s_waitcnt 0` does not drain VS.
Memory accesses while a store is pending are conservatively refused: the existing
Waitcnt register scoreboard does not establish address non-aliasing or memory
ordering. Consequently this module does not claim that the existing checker alone
implies whole-ISA asynchronous/synchronous equivalence. The end-to-end theorem
combines the extended executable tracker with explicit local ISA footprint laws;
the concrete load–wait–use block establishes that these laws are inhabited.
-/

inductive AsyncError where
  | staleInFlightRead
  | invalidRetirementIndex
  | incompleteWait
  | pendingMemoryOrdering
  | counterOverflow
  deriving DecidableEq, Repr

/-- A latched result, not an instruction to re-execute at completion. Array indices
are physical dword slots; a VGPR occupies 64 adjacent slots. -/
structure Writeback where
  destinations : List Reg
  sgprs : Array (Nat × UInt32) := #[]
  vgprs : Array (Nat × UInt32) := #[]
  memory : Array (UInt64 × UInt32) := #[]
  deriving Repr

/-- Apply only the latched writes, preserving PC, EXEC and unrelated registers. -/
def Writeback.apply (w : Writeback) (s : WaveState) : WaveState :=
  { s with
    sgpr := w.sgprs.foldl (fun a (n, v) => a.set! n v) s.sgpr
    vgpr := w.vgprs.foldl (fun a (n, v) => a.set! n v) s.vgpr
    mem := w.memory.foldl (fun m (a, v) => m.insert a v) s.mem }

/-- Sparse delta over the actual decoded destination slots. This avoids scanning
all 16,384 VGPR cells for a scalar load. Completeness of the destination metadata
is checked by the semantic latch law, not assumed from the field's name. -/
def arrayDelta (before after : Array UInt32) (indices : Array Nat) : Array (Nat × UInt32) :=
  indices.filterMap fun n => do
    let v ← after[n]?
    if before[n]? == some v then none else some (n, v)

/-- Latched writes use the real instruction's destination footprint. Memory
changes are captured only for stores; load instructions cannot smuggle memory
writes through this extraction because `FootprintSound.latch` would fail. -/
def capture (i : Inst) (before after : WaveState) : Writeback :=
  { destinations := i.access.writes
    sgprs := arrayDelta before.sgpr after.sgpr
      (i.access.writes.filterMap (fun r => match r with | .s n => some n | .v _ => none)).toArray
    vgprs := arrayDelta before.vgpr after.vgpr
      (i.access.writes.flatMap (fun r => match r with
        | .s _ => [] | .v n => (List.range 64).map (fun l => n * 64 + l))).toArray
    memory := if isVmemStore i || isDsStore i then
      after.mem.toArray.filter (fun (a, v) => before.mem.get? a != some v) else #[] }

structure AsyncWaveState extends WaveState where
  vmQueue : List Writeback := []
  lgkmQueue : List Writeback := []
  vsQueue : List Writeback := []

def AsyncWaveState.init (s : WaveState) : AsyncWaveState := { toGWave := s }

def AsyncWaveState.vmCnt (s : AsyncWaveState) : Nat := s.vmQueue.length
def AsyncWaveState.lgkmCnt (s : AsyncWaveState) : Nat := s.lgkmQueue.length
def AsyncWaveState.vsCnt (s : AsyncWaveState) : Nat := s.vsQueue.length

def pendingHit (q : List Writeback) (r : Reg) : Bool :=
  q.any fun w => w.destinations.contains r

/-- Reads AND overwrites of any pending destination fail closed. This is stricter
than Waitcnt's deliberate in-order WAW exception for two VMEM loads. -/
def stale (s : AsyncWaveState) (a : Access) : Bool :=
  (a.reads ++ a.writes).any fun r => pendingHit s.vmQueue r || pendingHit s.lgkmQueue r

/-- Out-of-order selection by position in the CURRENT queue, not by issue ID. -/
def removeAt {α : Type} : List α → Nat → Option (α × List α)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | x :: xs, n + 1 => (removeAt xs n).map fun (y, ys) => (y, x :: ys)

/-- Removal never manufactures a pending event. -/
theorem removeAt_subset {α : Type} (xs : List α) (n : Nat) (x : α) (ys : List α)
    (h : removeAt xs n = some (x, ys)) : ∀ y ∈ ys, y ∈ xs := by
  induction xs generalizing n ys with
  | nil => simp [removeAt] at h
  | cons a as ih =>
    cases n with
    | zero => simp [removeAt] at h; obtain ⟨rfl, rfl⟩ := h; simp_all
    | succ n =>
      simp only [removeAt] at h
      cases he : removeAt as n with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨b, bs⟩
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · exact List.mem_cons.mpr (Or.inl hy)
        · exact List.mem_cons.mpr (Or.inr (ih n bs he y hy))

inductive Completion where
  | vm
  | lgkm (index : Nat)
  | vs
  deriving DecidableEq, Repr

/-- One adversarial completion. VM and VS offer only the head; LGKM offers any
valid index. Invalid schedules are errors, not silently repaired schedules. -/
def complete (s : AsyncWaveState) (c : Completion) : Except AsyncError AsyncWaveState := do
  match c with
  | .vm =>
    let some (w, ws) := removeAt s.vmQueue 0 | throw .invalidRetirementIndex
    return { s with toGWave := w.apply s.toGWave, vmQueue := ws }
  | .lgkm n =>
    let some (w, ws) := removeAt s.lgkmQueue n | throw .invalidRetirementIndex
    return { s with toGWave := w.apply s.toGWave, lgkmQueue := ws }
  | .vs =>
    let some (w, ws) := removeAt s.vsQueue 0 | throw .invalidRetirementIndex
    return { s with toGWave := w.apply s.toGWave, vsQueue := ws }

/-- Intermediate completions may occur at any boundary, including no completions. -/
def schedule : AsyncWaveState → List Completion → Except AsyncError AsyncWaveState
  | s, [] => .ok s
  | s, c :: cs => do schedule (← complete s c) cs

/-- VM wait: exactly the minimum number of oldest completions. Additional
completions are represented by the arbitrary intermediate schedule. -/
def drainVm : Nat → AsyncWaveState → Except AsyncError AsyncWaveState
  | 0, s => .ok s
  | n + 1, s => do drainVm n (← complete s .vm)

def drainVs : Nat → AsyncWaveState → Except AsyncError AsyncWaveState
  | 0, s => .ok s
  | n + 1, s => do drainVs n (← complete s .vs)

/-- LGKM wait: an explicit adversarial permutation prefix. Too short a prefix
fails the wait, and an invalid index fails the schedule. No FIFO default. -/
def drainLgkm : List Nat → AsyncWaveState → Except AsyncError AsyncWaveState
  | [], s => .ok s
  | n :: ns, s => do drainLgkm ns (← complete s (.lgkm n))

def wait (s : AsyncWaveState) (simm : Nat) (order : List Nat) : Except AsyncError AsyncWaveState := do
  let s ← drainVm (s.vmCnt - waitVm simm) s
  let s ← drainLgkm order s
  if s.lgkmCnt > waitLgkm simm then throw .incompleteWait
  return s

/-- Decoded straight-line step, with the same PC increment and `execInst` as
`Semantics.step`. Branches still obey that semantics, but this list runner does
not fetch their targets; callers using branches must use a program-fetch runner. -/
def memoryInstruction (i : Inst) : Bool :=
  isVmemLoad i || isVmemStore i || isSmemLoad i || isDsLoad i || isDsStore i

def issue (s : AsyncWaveState) (i : Inst) (waitOrder : List Nat := []) : Except AsyncError AsyncWaveState := do
  if s.halted || s.err.isSome then return s
  if i.name == "S_WAITCNT" then
    let t ← wait s (i.field "SIMM16") waitOrder
    return { t with pc := t.pc + i.words.length }
  if i.name == "S_WAITCNT_VSCNT" then
    let t ← drainVs (s.vsCnt - i.field "SIMM16") s
    return { t with pc := t.pc + i.words.length }
  if stale s i.access then throw .staleInFlightRead
  let memOp := memoryInstruction i
  if memOp && (!s.vsQueue.isEmpty || s.lgkmQueue.any (fun w => !w.memory.isEmpty)) then
    throw .pendingMemoryOrdering
  let after := execInst i { s.toGWave with pc := s.pc + i.words.length }
  if after.err.isSome || !memOp then return { s with toGWave := after }
  let w := capture i s.toGWave after
  let delayed := { after with sgpr := s.sgpr, vgpr := s.vgpr, mem := s.mem }
  if isVmemLoad i then
    if s.vmCnt ≥ 63 then throw .counterOverflow
    return { s with toGWave := delayed, vmQueue := s.vmQueue ++ [w] }
  if isVmemStore i then
    if s.vsCnt ≥ 63 then throw .counterOverflow
    return { s with toGWave := delayed, vsQueue := s.vsQueue ++ [w] }
  if s.lgkmCnt ≥ 63 then throw .counterOverflow
  return { s with toGWave := delayed, lgkmQueue := s.lgkmQueue ++ [w] }

structure Turn where
  before : List Completion := []
  instruction : Inst
  waitOrder : List Nat := []

/-- Arbitrarily many instruction boundaries; every failed hazard remains visible. -/
def run : AsyncWaveState → List Turn → Except AsyncError AsyncWaveState
  | s, [] => .ok s
  | s, t :: ts => do run (← issue (← schedule s t.before) t.instruction t.waitOrder) ts

def syncRun : WaveState → List Inst → WaveState
  | s, [] => s
  | s, i :: is => syncRun (if s.halted || s.err.isSome then s else
      execInst i { s with pc := s.pc + i.words.length }) is

/-- The static register predicate reused from Waitcnt, with a conservative LGKM
policy: a nonzero threshold cannot establish completion of any particular event. -/
def counterSafe (p : Pending) (a : Access) : Bool :=
  !(a.reads ++ a.writes).any fun r => p.vm.hits r || p.lgkm.hits r

/-- Concrete pending destinations are covered by the abstract scoreboard. -/
def Covers (p : Pending) (s : AsyncWaveState) : Prop :=
  (∀ r, pendingHit s.vmQueue r = true → p.vm.hits r = true) ∧
  (∀ r, pendingHit s.lgkmQueue r = true → p.lgkm.hits r = true)

/-- The abstract check excludes every actual stale read AND pending overwrite.
The invariant must be propagated using FIFO ages for VM and subset inclusion for
LGKM; it cannot be assumed merely from numeric equality of the two counters. -/
theorem counterSafe_no_stale (p : Pending) (s : AsyncWaveState) (a : Access)
    (cover : Covers p s) (safe : counterSafe p a = true) : stale s a = false := by
  simp only [counterSafe, Bool.not_eq_true', List.any_eq_false] at safe
  simp only [stale, List.any_eq_false]
  intro r hr
  have h := safe r hr
  have hfalse : (p.vm.hits r || p.lgkm.hits r) = false := by simpa using h
  rcases Bool.or_eq_false_iff.mp hfalse with ⟨hv, hl⟩
  suffices hh : (pendingHit s.vmQueue r || pendingHit s.lgkmQueue r) = false by simpa using hh
  apply Bool.or_eq_false_iff.mpr
  constructor
  · cases he : pendingHit s.vmQueue r
    · rfl
    · have := cover.1 r he; simp_all
  · cases he : pendingHit s.lgkmQueue r
    · rfl
    · have := cover.2 r he; simp_all

/-- A genuinely out-of-order removal still preserves the abstract coverage. -/
theorem removed_event_still_covered (p : Events) (q : List Writeback) (n : Nat)
    (w : Writeback) (rest : List Writeback)
    (h : removeAt q n = some (w, rest))
    (cover : ∀ r, pendingHit q r = true → p.hits r = true) :
    ∀ r, pendingHit rest r = true → p.hits r = true := by
  intro r hr
  apply cover r
  simp only [pendingHit, List.any_eq_true] at hr ⊢
  obtain ⟨v, hv, hit⟩ := hr
  exact ⟨v, removeAt_subset q n w rest h v hv, hit⟩

/-- Static FIFO age bound: retain only the newest `k` issued VM events. -/
def fifoWait {α : Type} (k : Nat) (q : List α) : List α := q.drop (q.length - k)

/-- Any early FIFO completions only strengthen the same tight age bound; they
never change which older event a nonzero VM wait guarantees has completed. -/
theorem fifoWait_after_early {α : Type} (q : List α) (k early : Nat) :
    fifoWait k (q.drop early) = (fifoWait k q).drop (early - (q.length - k)) := by
  simp only [fifoWait, List.length_drop, List.drop_drop]
  congr 1
  omega

/-- The executable FIFO drainer implements list-prefix retirement exactly. -/
theorem drainVm_queue (n : Nat) (s t : AsyncWaveState) (h : drainVm n s = .ok t) :
    t.vmQueue = s.vmQueue.drop n := by
  induction n generalizing s t with
  | zero => simp only [drainVm, Except.ok.injEq] at h; subst t; rfl
  | succ n ih =>
    cases hs : s.vmQueue with
    | nil => simp [drainVm, complete, removeAt, hs, bind, Except.bind, throw, throwThe] at h
    | cons w ws =>
      have ht : drainVm n { s with toGWave := w.apply s.toGWave, vmQueue := ws } = .ok t := by
        simpa [drainVm, complete, removeAt, hs] using h
      simpa [hs] using ih _ t ht

/-- Completion cannot introduce a new outstanding register dependency. -/
theorem complete_covers (p : Pending) (s t : AsyncWaveState) (c : Completion)
    (cover : Covers p s) (h : complete s c = .ok t) : Covers p t := by
  cases c with
  | vm =>
    cases he : removeAt s.vmQueue 0 with
    | none => simp [complete, he] at h
    | some pair =>
      rcases pair with ⟨w, ws⟩
      simp [complete, he, pure, Except.pure] at h
      subst t
      exact ⟨removed_event_still_covered p.vm s.vmQueue 0 w ws he cover.1, cover.2⟩
  | lgkm n =>
    cases he : removeAt s.lgkmQueue n with
    | none => simp [complete, he] at h
    | some pair =>
      rcases pair with ⟨w, ws⟩
      simp [complete, he, pure, Except.pure] at h
      subst t
      exact ⟨cover.1, removed_event_still_covered p.lgkm s.lgkmQueue n w ws he cover.2⟩
  | vs =>
    cases he : removeAt s.vsQueue 0 with
    | none => simp [complete, he] at h
    | some pair =>
      rcases pair with ⟨w, ws⟩
      simp [complete, he, pure, Except.pure] at h
      subst t
      exact cover

/-- Coverage survives arbitrary finite inter-instruction schedules, not only a
chosen FIFO schedule. Invalid indices are excluded by the executable outcome. -/
theorem schedule_covers (p : Pending) (s t : AsyncWaveState) (cs : List Completion)
    (cover : Covers p s) (h : schedule s cs = .ok t) : Covers p t := by
  induction cs generalizing s with
  | nil => simp only [schedule, Except.ok.injEq] at h; subst t; exact cover
  | cons c cs ih =>
    cases hc : complete s c with
    | error e => simp [schedule, hc, bind, Except.bind] at h
    | ok u =>
      have ht : schedule u cs = .ok t := by simpa [schedule, hc, bind, Except.bind] using h
      exact ih u (complete_covers p s u c cover hc) ht

/-- A static counter-safe access remains nonstale under EVERY intermediate
completion schedule covered by the scoreboard. -/
theorem counterSafe_all_schedules (p : Pending) (s t : AsyncWaveState)
    (cs : List Completion) (a : Access) (cover : Covers p s)
    (safe : counterSafe p a = true) (h : schedule s cs = .ok t) : stale t a = false :=
  counterSafe_no_stale p t a (schedule_covers p s t cs cover h) safe

/-- Serial materialization of latched writebacks. This interpretation is separate
from both the schedule evaluator and synchronous instruction execution. -/
def materialize (s : WaveState) (q : List Writeback) : WaveState :=
  q.foldl (fun st w => w.apply st) s

/-- Pairwise commutation is the semantic condition needed to reorder completions.
Disjoint physical destination slots suffice; overlapping LDS/global memory words
require an ordering argument, and are not justified by a register-only wait. -/
def Independent (a b : Writeback) : Prop := ∀ s, a.apply (b.apply s) = b.apply (a.apply s)

private theorem materialize_move (s : WaveState) (pre : List Writeback) (w : Writeback)
    (h : ∀ a ∈ pre, Independent a w) :
    materialize (w.apply s) pre = w.apply (materialize s pre) := by
  induction pre generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [materialize, List.foldl_cons]
    rw [h a (by simp) s]
    exact ih (a.apply s) (fun b hb => h b (by simp [hb]))

/-- Retiring ANY element early is semantics preserving when it commutes with the
older entries it bypasses. This equation includes the entire concrete WaveState. -/
theorem retireAt_eq_serial (s : WaveState) (pre post : List Writeback) (w : Writeback)
    (h : ∀ a ∈ pre, Independent a w) :
    materialize (w.apply s) (pre ++ post) = materialize s (pre ++ w :: post) := by
  simp only [materialize, List.foldl_append, List.foldl_cons]
  rw [show pre.foldl (fun st w => w.apply st) (w.apply s) =
    w.apply (pre.foldl (fun st w => w.apply st) s) from materialize_move s pre w h]

/-- Every sequence of legal independent retirements, not just one chosen order. -/
inductive RetirementTrace : WaveState → List Writeback → WaveState → List Writeback → Prop
  | refl (s q) : RetirementTrace s q s q
  | step (s t : WaveState) (pre post rest : List Writeback) (w : Writeback)
      (independent : ∀ a ∈ pre, Independent a w)
      (tail : RetirementTrace (w.apply s) (pre ++ post) t rest) :
      RetirementTrace s (pre ++ w :: post) t rest

theorem retirementTrace_materialize {s t : WaveState} {q rest : List Writeback}
    (trace : RetirementTrace s q t rest) : materialize t rest = materialize s q := by
  induction trace with
  | refl => rfl
  | step s t pre post rest w independent tail ih =>
    exact ih.trans (retireAt_eq_serial s pre post w independent)

/-- At drain completion, every permitted order yields the exact serial state. -/
theorem retireAll_eq_serial {s t : WaveState} {q : List Writeback}
    (trace : RetirementTrace s q t []) : t = materialize s q :=
  retirementTrace_materialize trace

/-- Single-slot writeback, useful for proving real independent completions. -/
def sgprWriteback (n : Nat) (v : UInt32) : Writeback :=
  { destinations := [.s n], sgprs := #[(n, v)] }

theorem sgprWriteback_independent (n m : Nat) (a b : UInt32) (different : n ≠ m) :
    Independent (sgprWriteback n a) (sgprWriteback m b) := by
  intro s
  simp [sgprWriteback, Writeback.apply, Array.setIfInBounds_comm _ _ different.symm]

/-- An inhabited non-FIFO trace with two independent destinations, for arbitrary
initial state and arbitrary load values. -/
theorem two_sgpr_retire_younger_first (s : WaveState) (a b : UInt32) :
    RetirementTrace s [sgprWriteback 8 a, sgprWriteback 9 b]
      ((sgprWriteback 8 a).apply ((sgprWriteback 9 b).apply s)) [] := by
  apply RetirementTrace.step s _ [sgprWriteback 8 a] [] [] (sgprWriteback 9 b)
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    exact sgprWriteback_independent 8 9 a b (by decide)
  · apply RetirementTrace.step _ _ [] [] [] (sgprWriteback 8 a)
    · simp
    · exact RetirementTrace.refl _ []

/-- The list interpreter really uses the existing program-fetch semantics when
its next decoded instruction agrees with that program's current PC. -/
theorem syncRun_cons_step (prog : Program) (s : WaveState) (i : Inst) (is : List Inst)
    (fetch : prog[s.pc]? = some (some i)) :
    syncRun s (i :: is) = syncRun (step prog s) is := by
  simp [syncRun, step, fetch]

/-! ## Executable basic-block counter and store analysis -/

structure BlockCounters where
  pending : Pending := Pending.empty
  vsCnt : Nat := 0
  lgkmStore : Bool := false
  deriving DecidableEq, Repr

def BlockCounters.drained (p : BlockCounters) : Bool :=
  p.pending.vm.isEmpty && p.pending.lgkm.isEmpty && p.vsCnt == 0

/-- Nonzero LGKM waits retain every potentially outstanding destination. LDS
stores have empty destination lists but still occupy an event and a store flag.
No trim operation may discard those events from the numeric upper bound. -/
def updateCounters (p : BlockCounters) (i : Inst) : BlockCounters :=
  if i.name == "S_WAITCNT" then
    { p with
      pending := { p.pending with
        vm := fifoWait (waitVm (i.field "SIMM16")) p.pending.vm
        lgkm := if waitLgkm (i.field "SIMM16") == 0 then [] else p.pending.lgkm
        smem := p.pending.smem && waitLgkm (i.field "SIMM16") != 0 }
      lgkmStore := p.lgkmStore && waitLgkm (i.field "SIMM16") != 0 }
  else if i.name == "S_WAITCNT_VSCNT" then
    { p with vsCnt := min p.vsCnt (i.field "SIMM16") }
  else if isVmemLoad i then
    { p with pending := { p.pending with vm := p.pending.vm ++ [i.access.writes] } }
  else if isVmemStore i then { p with vsCnt := p.vsCnt + 1 }
  else if memoryInstruction i then
    { p with
      pending := { p.pending with
        lgkm := p.pending.lgkm ++ [i.access.writes]
        smem := p.pending.smem || isSmemLoad i }
      lgkmStore := p.lgkmStore || isDsStore i }
  else p

def canIssue (p : BlockCounters) (i : Inst) : Bool :=
  !i.inst.isBranch &&
  (if i.name == "S_WAITCNT" || i.name == "S_WAITCNT_VSCNT" then true else
    counterSafe p.pending i.access &&
    !(memoryInstruction i && (p.vsCnt != 0 || p.lgkmStore)) &&
    (if isVmemLoad i then p.pending.vm.length < 63
     else if isVmemStore i then p.vsCnt < 63
     else if memoryInstruction i then p.pending.lgkm.length < 63 else true))

def trackInstruction (p : BlockCounters) (i : Inst) : Option BlockCounters :=
  if canIssue p i then some (updateCounters p i) else none

def checkAsyncFrom (p : BlockCounters) : List Inst → Bool
  | [] => p.drained
  | i :: is => match trackInstruction p i with
    | none => false
    | some q => checkAsyncFrom q is

/-- An executable counter check, independent of the semantic footprint contracts. -/
def checkAsyncBlock (is : List Inst) : Bool := checkAsyncFrom {} is

/-- Only numeric bounds are needed for terminal draining. Register coverage and
memory noninterference enter the footprint contract separately. -/
def Bounded (p : BlockCounters) (s : AsyncWaveState) : Prop :=
  s.vmCnt ≤ p.pending.vm.length ∧ s.lgkmCnt ≤ p.pending.lgkm.length ∧ s.vsCnt ≤ p.vsCnt

def Decreases (s t : AsyncWaveState) : Prop :=
  t.vmCnt ≤ s.vmCnt ∧ t.lgkmCnt ≤ s.lgkmCnt ∧ t.vsCnt ≤ s.vsCnt

private theorem removeAt_split {α : Type} (q : List α) (n : Nat) (w : α) (rest : List α)
    (h : removeAt q n = some (w, rest)) :
    ∃ pre post, q = pre ++ w :: post ∧ rest = pre ++ post := by
  induction q generalizing n rest with
  | nil => simp [removeAt] at h
  | cons a as ih =>
    cases n with
    | zero => simp only [removeAt, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ⟨[], as, rfl, rfl⟩
    | succ n =>
      cases he : removeAt as n with
      | none => simp [removeAt, he] at h
      | some pair =>
        rcases pair with ⟨b, bs⟩
        simp only [removeAt, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, post, hp, hr⟩ := ih n bs he
        exact ⟨a :: pre, post, by simp [hp], by simp [hr]⟩

private theorem removeAt_length {α : Type} (q : List α) (n : Nat) (w : α) (rest : List α)
    (h : removeAt q n = some (w, rest)) : rest.length + 1 = q.length := by
  obtain ⟨pre, post, rfl, rfl⟩ := removeAt_split q n w rest h
  simp only [List.length_append, List.length_cons]
  omega

private theorem complete_decreases (s t : AsyncWaveState) (c : Completion)
    (h : complete s c = .ok t) : Decreases s t := by
  cases c <;> simp only [complete] at h
  all_goals split at h
  all_goals first | contradiction | skip
  all_goals rename_i w rest he
  all_goals have hn := removeAt_length _ _ w rest he
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst t
  all_goals simp only [Decreases, AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt]
  all_goals omega

private theorem schedule_decreases (s t : AsyncWaveState) (cs : List Completion)
    (h : schedule s cs = .ok t) : Decreases s t := by
  induction cs generalizing s with
  | nil => simp only [schedule, Except.ok.injEq] at h; subst t; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | cons c cs ih =>
    cases hc : complete s c with
    | error e => simp [schedule, hc, bind, Except.bind] at h
    | ok u =>
      have ht : schedule u cs = .ok t := by simpa [schedule, hc, bind, Except.bind] using h
      have a := complete_decreases s u c hc
      have b := ih u ht
      exact ⟨Nat.le_trans b.1 a.1, Nat.le_trans b.2.1 a.2.1, Nat.le_trans b.2.2 a.2.2⟩

private theorem drainVm_counts (n : Nat) (s t : AsyncWaveState) (h : drainVm n s = .ok t) :
    t.vmCnt = s.vmCnt - n ∧ t.lgkmCnt = s.lgkmCnt ∧ t.vsCnt = s.vsCnt := by
  induction n generalizing s t with
  | zero => simp only [drainVm, Except.ok.injEq] at h; subst t; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    cases hs : s.vmQueue with
    | nil => simp [drainVm, complete, removeAt, hs, bind, Except.bind, throw, throwThe] at h
    | cons w ws =>
      have ht : drainVm n { s with toGWave := w.apply s.toGWave, vmQueue := ws } = .ok t := by
        simpa [drainVm, complete, removeAt, hs] using h
      have hi := ih _ t ht
      simp only [AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt, hs,
        List.length_cons] at hi ⊢
      omega

private theorem drainVs_counts (n : Nat) (s t : AsyncWaveState) (h : drainVs n s = .ok t) :
    t.vmCnt = s.vmCnt ∧ t.lgkmCnt = s.lgkmCnt ∧ t.vsCnt = s.vsCnt - n := by
  induction n generalizing s t with
  | zero => simp only [drainVs, Except.ok.injEq] at h; subst t; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    cases hs : s.vsQueue with
    | nil => simp [drainVs, complete, removeAt, hs, bind, Except.bind, throw, throwThe] at h
    | cons w ws =>
      have ht : drainVs n { s with toGWave := w.apply s.toGWave, vsQueue := ws } = .ok t := by
        simpa [drainVs, complete, removeAt, hs] using h
      have hi := ih _ t ht
      simp only [AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt, hs,
        List.length_cons] at hi ⊢
      omega

private theorem drainLgkm_counts (ns : List Nat) (s t : AsyncWaveState)
    (h : drainLgkm ns s = .ok t) :
    t.vmCnt = s.vmCnt ∧ t.lgkmCnt ≤ s.lgkmCnt ∧ t.vsCnt = s.vsCnt := by
  induction ns generalizing s with
  | nil => simp only [drainLgkm, Except.ok.injEq] at h; subst t; exact ⟨rfl, Nat.le_refl _, rfl⟩
  | cons n ns ih =>
    cases he : removeAt s.lgkmQueue n with
    | none => simp [drainLgkm, complete, he, bind, Except.bind, throw, throwThe] at h
    | some pair =>
      rcases pair with ⟨w, ws⟩
      have hn := removeAt_length _ _ w ws he
      have ht : drainLgkm ns { s with toGWave := w.apply s.toGWave, lgkmQueue := ws } = .ok t := by
        simpa [drainLgkm, complete, he, bind, Except.bind, pure, Except.pure] using h
      have hi := ih _ ht
      simp only [AsyncWaveState.lgkmCnt] at hi ⊢
      exact ⟨hi.1, by omega, hi.2.2⟩

private theorem wait_counts (s t : AsyncWaveState) (simm : Nat) (ns : List Nat)
    (h : wait s simm ns = .ok t) :
    t.vmCnt = min s.vmCnt (waitVm simm) ∧ t.lgkmCnt ≤ s.lgkmCnt ∧
    t.lgkmCnt ≤ waitLgkm simm ∧ t.vsCnt = s.vsCnt := by
  unfold wait at h
  cases hv : drainVm (s.vmCnt - waitVm simm) s with
  | error e => simp [hv, bind, Except.bind] at h
  | ok u =>
    cases hl : drainLgkm ns u with
    | error e => simp [hv, hl, bind, Except.bind] at h
    | ok v =>
      simp only [hv, hl, bind, Except.bind] at h
      split at h
      · contradiction
      · rename_i hk
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst t
        have a := drainVm_counts _ s u hv
        have b := drainLgkm_counts ns u v hl
        exact ⟨by omega, by omega, by omega, by omega⟩

private theorem issue_bounded (p : BlockCounters) (s t : AsyncWaveState) (i : Inst) (ns : List Nat)
    (live : (s.halted || s.err.isSome) = false) (bound : Bounded p s)
    (h : issue s i ns = .ok t) : Bounded (updateCounters p i) t := by
  by_cases hw : i.name = "S_WAITCNT"
  · simp only [issue, live, Bool.false_eq_true, ite_false, hw, BEq.rfl, ite_true] at h
    cases he : wait s (i.field "SIMM16") ns with
    | error e => simp [he, bind, Except.bind] at h
    | ok u =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst t
      have hc := wait_counts s u _ ns he
      simp only [Bounded, updateCounters, hw, BEq.rfl, ite_true, fifoWait, List.length_drop]
      simp only [Bounded] at bound
      split <;> simp_all [AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt] <;> omega
  · simp only [issue, live, Bool.false_eq_true, ite_false, beq_iff_eq, hw] at h
    by_cases hz : i.name = "S_WAITCNT_VSCNT"
    · simp only [hz, ite_true] at h
      cases he : drainVs (s.vsCnt - i.field "SIMM16") s with
      | error e => simp [he, bind, Except.bind] at h
      | ok u =>
        simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst t
        have hc := drainVs_counts _ s u he
        simp [Bounded, updateCounters, hz, AsyncWaveState.vmCnt,
          AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt] at bound hc ⊢
        omega
    · simp only [hz, ite_false] at h
      rcases bound with ⟨boundVm, boundLgkm, boundVs⟩
      repeat' first | contradiction | split at h
      all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
      all_goals subst t
      all_goals simp only [updateCounters, beq_iff_eq, hw, hz, ite_false]
      all_goals repeat' split
      all_goals simp_all [Bounded, AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt,
        AsyncWaveState.vsCnt, List.length_append, memoryInstruction]
      all_goals omega

/-! ## Semantic footprint contracts and schedule-independent materialization -/

def queues (s : AsyncWaveState) : List Writeback := s.vmQueue ++ s.lgkmQueue ++ s.vsQueue

def settle (s : AsyncWaveState) : WaveState := materialize s.toGWave (queues s)

/-- Every outstanding pair commutes on arbitrary architectural states. This is
stronger than agreeing on one observed register, and includes memory writes. -/
def Coherent (q : List Writeback) : Prop :=
  ∀ a ∈ q, ∀ b ∈ q, Independent a b

private theorem independent_symm {a b : Writeback} (h : Independent a b) : Independent b a :=
  fun s => (h s).symm

private theorem coherent_insert (pre post : List Writeback) (w : Writeback)
    (old : Coherent (pre ++ post)) (fresh : ∀ a ∈ pre ++ post, Independent w a) :
    Coherent (pre ++ w :: post) := by
  have mem : ∀ a ∈ pre ++ w :: post, a = w ∨ a ∈ pre ++ post := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    rcases ha with ha | rfl | ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ha)
  intro a ha b hb
  rcases mem a ha with haEq | haOld
  · subst a
    rcases mem b hb with hbEq | hbOld
    · subst b; intro st; rfl
    · exact fresh b hbOld
  · rcases mem b hb with hbEq | hbOld
    · subst b; exact independent_symm (fresh a haOld)
    · exact old a haOld b hbOld

private theorem materialize_fields (s : WaveState) (q : List Writeback) :
    (materialize s q).pc = s.pc ∧ (materialize s q).halted = s.halted ∧
    (materialize s q).err = s.err := by
  induction q generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons w ws ih => exact ih (w.apply s)

private theorem materialize_pc_update (s : WaveState) (q : List Writeback) (pc : Nat) :
    materialize { s with pc := pc } q = { materialize s q with pc := pc } := by
  induction q generalizing s with
  | nil => rfl
  | cons w ws ih => exact ih (w.apply s)

private theorem settle_advance (s : AsyncWaveState) (n : Nat) :
    settle { s with pc := s.pc + n } = { settle s with pc := (settle s).pc + n } := by
  simp only [settle, queues, materialize_pc_update, (materialize_fields s.toGWave _).1]

private theorem complete_view (s t : AsyncWaveState) (c : Completion)
    (h : complete s c = .ok t) :
    ∃ w pre post, queues s = pre ++ w :: post ∧ queues t = pre ++ post ∧
      t.toGWave = w.apply s.toGWave := by
  cases c <;> simp only [complete] at h
  all_goals split at h
  all_goals first | contradiction | skip
  all_goals rename_i w rest he
  all_goals obtain ⟨pre, post, hp, hr⟩ := removeAt_split _ _ w rest he
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst t
  · exact ⟨w, pre, post ++ s.lgkmQueue ++ s.vsQueue,
      by simp [queues, hp, List.append_assoc], by simp [queues, hr, List.append_assoc], rfl⟩
  · exact ⟨w, s.vmQueue ++ pre, post ++ s.vsQueue,
      by simp [queues, hp, List.append_assoc], by simp [queues, hr, List.append_assoc], rfl⟩
  · exact ⟨w, s.vmQueue ++ s.lgkmQueue ++ pre, post,
      by simp [queues, hp, List.append_assoc], by simp [queues, hr, List.append_assoc], rfl⟩

private theorem complete_settle (s t : AsyncWaveState) (c : Completion)
    (coherent : Coherent (queues s)) (h : complete s c = .ok t) :
    Coherent (queues t) ∧ settle t = settle s := by
  obtain ⟨w, pre, post, hs, ht, hb⟩ := complete_view s t c h
  have sub : ∀ a ∈ pre ++ post, a ∈ pre ++ w :: post := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha ⊢
    exact ha.elim Or.inl (fun h => Or.inr (Or.inr h))
  constructor
  · intro a ha b hb
    rw [ht] at ha hb
    exact coherent a (hs ▸ sub a ha) b (hs ▸ sub b hb)
  · simp only [settle, hb, ht, hs]
    apply retireAt_eq_serial
    intro a ha
    exact coherent a (by rw [hs]; simp [ha]) w (by rw [hs]; simp)

private theorem schedule_settle (s t : AsyncWaveState) (cs : List Completion)
    (coherent : Coherent (queues s)) (h : schedule s cs = .ok t) :
    Coherent (queues t) ∧ settle t = settle s := by
  induction cs generalizing s with
  | nil => simp only [schedule, Except.ok.injEq] at h; subst t; exact ⟨coherent, rfl⟩
  | cons c cs ih =>
    cases hc : complete s c with
    | error e => simp [schedule, hc, bind, Except.bind] at h
    | ok u =>
      have ht : schedule u cs = .ok t := by simpa [schedule, hc, bind, Except.bind] using h
      have hu := complete_settle s u c coherent hc
      have ht := ih u hu.1 ht
      exact ⟨ht.1, ht.2.trans hu.2⟩

private theorem drainVm_schedule (n : Nat) (s : AsyncWaveState) :
    drainVm n s = schedule s (List.replicate n .vm) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [drainVm, List.replicate_succ, schedule]; congr 1; funext t; exact ih t

private theorem drainVs_schedule (n : Nat) (s : AsyncWaveState) :
    drainVs n s = schedule s (List.replicate n .vs) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [drainVs, List.replicate_succ, schedule]; congr 1; funext t; exact ih t

private theorem drainLgkm_schedule (ns : List Nat) (s : AsyncWaveState) :
    drainLgkm ns s = schedule s (ns.map Completion.lgkm) := by
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih => simp only [drainLgkm, List.map_cons, schedule]; congr 1; funext t; exact ih t

private theorem wait_settle (s t : AsyncWaveState) (simm : Nat) (ns : List Nat)
    (coherent : Coherent (queues s)) (h : wait s simm ns = .ok t) :
    Coherent (queues t) ∧ settle t = settle s := by
  unfold wait at h
  cases hv : drainVm (s.vmCnt - waitVm simm) s with
  | error e => simp [hv, bind, Except.bind] at h
  | ok u =>
    cases hl : drainLgkm ns u with
    | error e => simp [hv, hl, bind, Except.bind] at h
    | ok v =>
      simp only [hv, hl, bind, Except.bind] at h
      split at h
      · contradiction
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst t
        have hu := schedule_settle s u _ coherent ((drainVm_schedule _ s) ▸ hv)
        have hv := schedule_settle u v _ hu.1 ((drainLgkm_schedule ns u) ▸ hl)
        exact ⟨hv.1, hv.2.trans hu.2⟩

def instructionAfter (i : Inst) (s : WaveState) : WaveState :=
  execInst i { s with pc := s.pc + i.words.length }

def delayedBase (i : Inst) (s : WaveState) : WaveState :=
  { instructionAfter i s with sgpr := s.sgpr, vgpr := s.vgpr, mem := s.mem }

/-- Local ISA algebra, deliberately separate from `checkAsyncBlock` and `run`.
The frame law concerns the real `execInst`, not an assumed asynchronous step.
The latch law includes every WaveState field. Pairwise commutation is required
on arbitrary states, so a missing memory-ordering argument cannot hide in a
single evaluated trace. `live` supplies the domain on which the instruction
actually issues rather than inheriting an earlier halt or model error. -/
structure FootprintSound (i : Inst) (s : AsyncWaveState) : Prop where
  live : (s.halted || s.err.isSome) = false
  wait_effect : i.name = "S_WAITCNT" ∨ i.name = "S_WAITCNT_VSCNT" →
    instructionAfter i (settle s) = { settle s with pc := (settle s).pc + i.words.length }
  frame : instructionAfter i (settle s) = materialize (instructionAfter i s.toGWave) (queues s)
  latch : memoryInstruction i = true → (instructionAfter i s.toGWave).err.isSome = false →
    (capture i s.toGWave (instructionAfter i s.toGWave)).apply (delayedBase i s.toGWave) =
      instructionAfter i s.toGWave
  separate : memoryInstruction i = true → (instructionAfter i s.toGWave).err.isSome = false →
    ∀ w ∈ queues s, Independent (capture i s.toGWave (instructionAfter i s.toGWave)) w

private theorem latch_insert (i : Inst) (s : AsyncWaveState) (pre post : List Writeback)
    (hq : queues s = pre ++ post) (coherent : Coherent (queues s)) (fp : FootprintSound i s)
    (hm : memoryInstruction i = true) (he : (instructionAfter i s.toGWave).err.isSome = false) :
    let w := capture i s.toGWave (instructionAfter i s.toGWave)
    Coherent (pre ++ w :: post) ∧
    materialize (delayedBase i s.toGWave) (pre ++ w :: post) = instructionAfter i (settle s) := by
  dsimp only
  constructor
  · apply coherent_insert pre post _ (hq ▸ coherent)
    intro a ha
    exact fp.separate hm he a (hq ▸ ha)
  · rw [← retireAt_eq_serial]
    · rw [fp.latch hm he, ← hq, ← fp.frame]
    · intro a ha
      exact independent_symm (fp.separate hm he a (by rw [hq]; simp [ha]))

private theorem issue_settle (s t : AsyncWaveState) (i : Inst) (ns : List Nat)
    (coherent : Coherent (queues s)) (fp : FootprintSound i s)
    (h : issue s i ns = .ok t) :
    Coherent (queues t) ∧ settle t = instructionAfter i (settle s) := by
  simp only [issue, fp.live, Bool.false_eq_true, ite_false, beq_iff_eq] at h
  by_cases hw : i.name = "S_WAITCNT"
  · simp only [hw, ite_true] at h
    cases he : wait s (i.field "SIMM16") ns with
    | error e => simp [he, bind, Except.bind] at h
    | ok u =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst t
      have hu := wait_settle s u _ ns coherent he
      exact ⟨hu.1, by rw [settle_advance, hu.2, fp.wait_effect (Or.inl hw)]⟩
  · simp only [hw, ite_false] at h
    by_cases hz : i.name = "S_WAITCNT_VSCNT"
    · simp only [hz, ite_true] at h
      cases he : drainVs (s.vsCnt - i.field "SIMM16") s with
      | error e => simp [he, bind, Except.bind] at h
      | ok u =>
        simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst t
        have hu := schedule_settle s u _ coherent ((drainVs_schedule _ s) ▸ he)
        exact ⟨hu.1, by rw [settle_advance, hu.2, fp.wait_effect (Or.inr hz)]⟩
    · simp only [hz, ite_false] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst t
            exact ⟨coherent, fp.frame.symm⟩
          · rename_i clean
            have hc : (instructionAfter i s.toGWave).err.isSome = false ∧ memoryInstruction i = true := by
              simpa only [instructionAfter, Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] using clean
            split at h
            · split at h
              · contradiction
              · simp only [pure, Except.pure, Except.ok.injEq] at h
                subst t
                simpa only [delayedBase, instructionAfter, queues, settle, List.append_assoc, List.cons_append, List.nil_append] using
                  latch_insert i s s.vmQueue (s.lgkmQueue ++ s.vsQueue)
                    (by simp [queues, List.append_assoc]) coherent fp hc.2 hc.1
            · split at h
              · split at h
                · contradiction
                · simp only [pure, Except.pure, Except.ok.injEq] at h
                  subst t
                  simpa only [delayedBase, instructionAfter, queues, settle, List.append_assoc, List.append_nil] using
                    latch_insert i s (queues s) [] (by simp) coherent fp hc.2 hc.1
              · split at h
                · contradiction
                · simp only [pure, Except.pure, Except.ok.injEq] at h
                  subst t
                  simpa only [delayedBase, instructionAfter, queues, settle, List.append_assoc, List.cons_append, List.nil_append] using
                    latch_insert i s (s.vmQueue ++ s.lgkmQueue) s.vsQueue
                      (by simp [queues, List.append_assoc]) coherent fp hc.2 hc.1

/-- Per-instruction validity domains. Completion closure and issue closure only
preserve the domain (e.g. valid addresses and register-file sizes); all semantic
refinement comes from the separate `FootprintSound` algebra. No constructor
assumes a block result, a terminal drain, or equality of `run` and `syncRun`. -/
inductive BlockWellFormed : (AsyncWaveState → Prop) → List Inst → Prop
  | nil (P : AsyncWaveState → Prop) : BlockWellFormed P []
  | cons (P Q : AsyncWaveState → Prop) (i : Inst) (is : List Inst)
      (footprint : ∀ s, P s → FootprintSound i s)
      (completion_closed : ∀ s t c, P s → complete s c = .ok t → P t)
      (issue_closed : ∀ s t ns, P s → issue s i ns = .ok t → Q t)
      (tail : BlockWellFormed Q is) : BlockWellFormed P (i :: is)

private theorem closed_schedule (P : AsyncWaveState → Prop)
    (closed : ∀ s t c, P s → complete s c = .ok t → P t)
    (s t : AsyncWaveState) (cs : List Completion) (hs : P s)
    (h : schedule s cs = .ok t) : P t := by
  induction cs generalizing s with
  | nil => simp only [schedule, Except.ok.injEq] at h; subst t; exact hs
  | cons c cs ih =>
    cases hc : complete s c with
    | error e => simp [schedule, hc, bind, Except.bind] at h
    | ok u =>
      have ht : schedule u cs = .ok t := by simpa [schedule, hc, bind, Except.bind] using h
      exact ih u (closed s u c hs hc) ht

private theorem checked_run_refines (turns : List Turn) (s t : AsyncWaveState)
    (p : BlockCounters) (P : AsyncWaveState → Prop)
    (wf : BlockWellFormed P (turns.map (·.instruction))) (domain : P s)
    (coherent : Coherent (queues s)) (bound : Bounded p s)
    (accepted : checkAsyncFrom p (turns.map (·.instruction)) = true)
    (h : run s turns = .ok t) :
    t.vmQueue = [] ∧ t.lgkmQueue = [] ∧ t.vsQueue = [] ∧
    settle t = syncRun (settle s) (turns.map (·.instruction)) := by
  induction turns generalizing s p P with
  | nil =>
    simp only [run, Except.ok.injEq] at h
    subst t
    simp [checkAsyncFrom, BlockCounters.drained] at accepted
    simp only [Bounded, AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt,
      AsyncWaveState.vsCnt, accepted.1.1, accepted.1.2, accepted.2, List.length_nil] at bound
    exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega),
      List.eq_nil_of_length_eq_zero (by omega), rfl⟩
  | cons turn turns ih =>
    cases wf with
    | cons P Q i is footprint closed post tail =>
      cases hs : schedule s turn.before with
      | error e => simp [run, hs, bind, Except.bind] at h
      | ok u =>
        cases hi : issue u turn.instruction turn.waitOrder with
        | error e => simp [run, hs, hi, bind, Except.bind] at h
        | ok v =>
          have ht : run v turns = .ok t := by simpa [run, hs, hi, bind, Except.bind] using h
          have hu := schedule_settle s u turn.before coherent hs
          have du := closed_schedule P closed s u turn.before domain hs
          have hv := issue_settle u v turn.instruction turn.waitOrder hu.1 (footprint u du) hi
          have bu : Bounded p u := by
            have hd := schedule_decreases s u turn.before hs
            exact ⟨Nat.le_trans hd.1 bound.1, Nat.le_trans hd.2.1 bound.2.1,
              Nat.le_trans hd.2.2 bound.2.2⟩
          have bv := issue_bounded p u v turn.instruction turn.waitOrder (footprint u du).live bu hi
          have ac : checkAsyncFrom (updateCounters p turn.instruction)
              (turns.map (·.instruction)) = true := by
            simp only [List.map_cons, checkAsyncFrom, trackInstruction] at accepted
            split at accepted <;> simp_all
          have result := ih v (updateCounters p turn.instruction) Q tail
            (post u v turn.waitOrder du hi) hv.1 bv ac ht
          refine ⟨result.1, result.2.1, result.2.2.1, ?_⟩
          rw [result.2.2.2, hv.2, hu.2]
          have live : ((settle s).halted || (settle s).err.isSome) = false := by
            simpa only [settle, (materialize_fields s.toGWave _).2.1,
              (materialize_fields s.toGWave _).2.2] using (footprint s domain).live
          simp only [List.map_cons, syncRun, live, Bool.false_eq_true, ite_false, instructionAfter]

/-- End-to-end, multi-instruction refinement of the real delayed interpreter.
The executable tracker supplies the terminal drain; local ISA footprints supply
frame, latching and commutation laws. The schedule is arbitrary: this successful
execution theorem does not select FIFO order for LGKM or assume a final equality. -/
theorem waitcnt_safe_async_refines_sync (s₀ : WaveState) (turns : List Turn) (sFinal : AsyncWaveState)
    (wellFormed : ∃ P, P (AsyncWaveState.init s₀) ∧
      BlockWellFormed P (turns.map (·.instruction)))
    (accepted : checkAsyncBlock (turns.map (·.instruction)) = true)
    (execution : run (AsyncWaveState.init s₀) turns = .ok sFinal) :
    sFinal.vmQueue = [] ∧ sFinal.lgkmQueue = [] ∧ sFinal.vsQueue = [] ∧
    sFinal.toGWave = syncRun s₀ (turns.map (·.instruction)) := by
  obtain ⟨P, start, wf⟩ := wellFormed
  have hc : Coherent (queues (AsyncWaveState.init s₀)) := by simp [Coherent, queues, AsyncWaveState.init]
  have hb : Bounded {} (AsyncWaveState.init s₀) := by simp [Bounded, AsyncWaveState.init,
    AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt, Pending.empty]
  have h := checked_run_refines turns (AsyncWaveState.init s₀) sFinal {} P wf start hc hb accepted execution
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  simpa only [settle, queues, h.1, h.2.1, h.2.2.1, AsyncWaveState.init,
    List.nil_append, materialize, List.foldl_nil] using h.2.2.2

/-! ## Concrete ISA domains and an inhabited load–wait–use block -/

private theorem wait_instruction_effect (i : Inst) (s : WaveState)
    (name : i.name = "S_WAITCNT" ∨ i.name = "S_WAITCNT_VSCNT")
    (clear : modifiersClear i = true) :
    instructionAfter i s = { s with pc := s.pc + i.words.length } := by
  rcases name with name | name <;> simp [instructionAfter, execInst, clear, name, instOp]

/-- Both actual wait opcodes satisfy the frame law for arbitrary pending queues. -/
theorem wait_instruction_footprint (i : Inst) (s : AsyncWaveState)
    (name : i.name = "S_WAITCNT" ∨ i.name = "S_WAITCNT_VSCNT")
    (clear : modifiersClear i = true) (live : (s.halted || s.err.isSome) = false) :
    FootprintSound i s := by
  have mem : memoryInstruction i = false := by
    rcases name with hn | hn <;>
      simp [memoryInstruction, isVmemLoad, isVmemStore, isSmemLoad, isDsLoad, isDsStore, hn]
  refine ⟨live, fun _ => wait_instruction_effect i (settle s) name clear, ?_, ?_, ?_⟩
  · rw [wait_instruction_effect i (settle s) name clear,
      wait_instruction_effect i s.toGWave name clear, materialize_pc_update]
    simp only [settle, (materialize_fields s.toGWave (queues s)).1]
  · intro hm; simp [mem] at hm
  · intro hm; simp [mem] at hm

private theorem nonmemory_empty_footprint (i : Inst) (s : WaveState)
    (hn : i.name ≠ "S_WAITCNT") (hz : i.name ≠ "S_WAITCNT_VSCNT")
    (hm : memoryInstruction i = false) (live : (s.halted || s.err.isSome) = false) :
    FootprintSound i (AsyncWaveState.init s) := by
  refine ⟨live, ?_, rfl, ?_, ?_⟩
  · intro h; rcases h with h | h <;> contradiction
  · intro h; simp [hm] at h
  · intro h; simp [hm] at h

/-- Real SGPR moves, VGPR moves, and S_ENDPGM have no delayed memory effect.
With no pending writes their frame law holds on every live input wave, including
any explicit operand refusal already provided by `Semantics.execInst`. -/
theorem register_instruction_footprint (i : Inst) (s : WaveState)
    (name : i.name = "S_MOV_B32" ∨ i.name = "V_MOV_B32" ∨ i.name = "S_ENDPGM")
    (live : (s.halted || s.err.isSome) = false) : FootprintSound i (AsyncWaveState.init s) := by
  apply nonmemory_empty_footprint i s
  · rcases name with h | h | h <;> simp [h]
  · rcases name with h | h | h <;> simp [h]
  · rcases name with h | h | h <;>
      simp [memoryInstruction, isVmemLoad, isVmemStore, isSmemLoad, isDsLoad, isDsStore, h]
  · exact live

private theorem complete_empty (s : WaveState) (t : AsyncWaveState) (c : Completion)
    (h : complete (AsyncWaveState.init s) c = .ok t) : False := by
  cases c <;> simp [complete, AsyncWaveState.init, removeAt, throw, throwThe] at h

private theorem empty_plain_issue (i : Inst) (s : WaveState) (ns : List Nat)
    (hn : i.name ≠ "S_WAITCNT") (hz : i.name ≠ "S_WAITCNT_VSCNT")
    (hm : memoryInstruction i = false) (live : (s.halted || s.err.isSome) = false) :
    issue (AsyncWaveState.init s) i ns = .ok (AsyncWaveState.init (instructionAfter i s)) := by
  simp [issue, AsyncWaveState.init, hn, hz, hm, live, stale, pendingHit, instructionAfter,
    pure, Except.pure]

private theorem bounded_drained (p : BlockCounters) (s : AsyncWaveState)
    (bound : Bounded p s) (empty : p.drained = true) :
    s.vmQueue = [] ∧ s.lgkmQueue = [] ∧ s.vsQueue = [] := by
  simp [BlockCounters.drained] at empty
  simp only [Bounded, AsyncWaveState.vmCnt, AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt,
    empty.1.1, empty.1.2, empty.2, List.length_nil] at bound
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega),
    List.eq_nil_of_length_eq_zero (by omega)⟩

private theorem empty_eq_init (s : AsyncWaveState)
    (h : s.vmQueue = [] ∧ s.lgkmQueue = [] ∧ s.vsQueue = []) :
    s = AsyncWaveState.init (settle s) := by
  cases s
  simp_all [AsyncWaveState.init, settle, queues, materialize]

namespace ReadWaitUse
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000
/-- Kernel-checked string evaluation rules for the sealed standard-library APIs
used by the existing decoder's family classification. -/
private theorem startsWith_eval (s p : String) :
    s.startsWith p = decide (p.toList <+: s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [String.startsWith_string_iff, decide_eq_true_eq]

private theorem drop_eval (s : String) (n : Nat) :
    (s.drop n).toString = String.ofList (s.toList.drop n) := by
  rw [String.Slice.toString_eq]
  apply String.toList_injective
  exact String.toList_copy_drop.trans String.toList_ofList.symm

attribute [local cbv_eval] startsWith_eval drop_eval

/-- Retrieve the actual instruction, operand and encoding metadata from AMD's
existing tables. Only the decoded operand fields and machine words are supplied;
there is no fabricated `Inst.access` summary in the witness. The test suite also
checks these fields and accesses against the binary decoder. -/
def fromTables (name encoding : String) (fields : List (String × Nat))
    (words : List UInt32) : Option Inst := do
  let ins ← instructions.find? (·.name == name)
  let enc ← encodings.find? (·.name == encoding)
  let ie ← ins.encodings.find? (·.encoding == encoding)
  return { inst := ins, enc, ie, fields, words }

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
def load : Inst := (fromTables "S_LOAD_DWORD" "ENC_SMEM"
  [("SDATA", 8), ("SBASE", 0), ("SOFFSET", 125), ("OFFSET", 0)]
  [0xf4000200, 0xfa000000]).get (by decide)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
def waitAll : Inst := (fromTables "S_WAITCNT" "ENC_SOPP" [("SIMM16", 0)] [0xbf8c0000]).get (by decide)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
def move : Inst := (fromTables "S_MOV_B32" "ENC_SOP1" [("SDST", 10), ("SSRC0", 8)]
  [0xbe8a0308]).get (by decide)

def initial : WaveState := GWave.init (({} : Memory).insert 0 7) 0 0

def issued : AsyncWaveState :=
  { toGWave := delayedBase load initial
    lgkmQueue := [capture load initial (instructionAfter load initial)] }

def returned : AsyncWaveState := AsyncWaveState.init (instructionAfter load initial)
def afterWait : WaveState := instructionAfter waitAll (instructionAfter load initial)
def block : List Inst := [load, waitAll, move]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load_footprint : FootprintSound load (AsyncWaveState.init initial) := by
  refine ⟨by rfl, ?_, rfl, ?_, ?_⟩
  · intro h; rcases h with h | h <;> contradiction
  · intro _ _; cbv
  · intro _ _ w hw; simp [queues, AsyncWaveState.init] at hw

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load_issues (ns : List Nat) : issue (AsyncWaveState.init initial) load ns = .ok issued := by cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load_retires : complete issued (.lgkm 0) = .ok returned := by cbv

/-- The post-load domain includes both possible completion states. -/
def PendingLoad (s : AsyncWaveState) : Prop := s = issued ∨ s = returned

private theorem pending_closed (s t : AsyncWaveState) (c : Completion)
    (hs : PendingLoad s) (h : complete s c = .ok t) : PendingLoad t := by
  rcases hs with rfl | rfl
  · cases c with
    | vm => simp [complete, issued, removeAt, throw, throwThe] at h
    | vs => simp [complete, issued, removeAt, throw, throwThe] at h
    | lgkm n =>
      cases n with
      | zero => rw [load_retires] at h; exact Or.inr (Except.ok.inj h).symm
      | succ n => simp [complete, issued, removeAt, throw, throwThe] at h
  · exact False.elim (complete_empty _ _ _ h)

private theorem pending_coherent (s : AsyncWaveState) (hs : PendingLoad s) : Coherent (queues s) := by
  rcases hs with rfl | rfl <;> simp [Coherent, queues, issued, returned, AsyncWaveState.init, Independent]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem pending_live (s : AsyncWaveState) (hs : PendingLoad s) :
    (s.halted || s.err.isSome) = false := by
  rcases hs with rfl | rfl <;> cbv

private theorem pending_settle (s : AsyncWaveState) (hs : PendingLoad s) :
    settle s = instructionAfter load initial := by
  rcases hs with rfl | rfl
  · exact load_footprint.latch (by cbv) (by
      have h := pending_live returned (Or.inr rfl)
      simpa [returned, AsyncWaveState.init] using (Bool.or_eq_false_iff.mp h).2)
  · rfl

private theorem pending_bound (s : AsyncWaveState) (hs : PendingLoad s) :
    Bounded { pending := { vm := [], lgkm := [[.s 8]], smem := true } } s := by
  rcases hs with rfl | rfl <;>
    simp [Bounded, issued, returned, AsyncWaveState.init, AsyncWaveState.vmCnt,
      AsyncWaveState.lgkmCnt, AsyncWaveState.vsCnt]

private theorem wait_post (s t : AsyncWaveState) (ns : List Nat)
    (hs : PendingLoad s) (h : issue s waitAll ns = .ok t) : t = AsyncWaveState.init afterWait := by
  have fp := wait_instruction_footprint waitAll s (Or.inl rfl) (by cbv) (pending_live s hs)
  have ht := issue_settle s t waitAll ns (pending_coherent s hs) fp h
  have hb := issue_bounded { pending := { vm := [], lgkm := [[.s 8]], smem := true } } s t waitAll ns
    (pending_live s hs) (pending_bound s hs) h
  have he := bounded_drained _ t hb (by cbv)
  rw [empty_eq_init t he, ht.2, pending_settle s hs]
  rfl

/-- All asynchronous states admitted here are concrete real-ISA states, including
both the pending and early-completed load. The wait proof quantifies over every
successful out-of-order retirement list, rather than selecting a single trace. -/
theorem block_wellFormed : BlockWellFormed (fun s => s = AsyncWaveState.init initial) block := by
  apply BlockWellFormed.cons _ PendingLoad load [waitAll, move]
  · intro s hs; subst s; exact load_footprint
  · intro s t c hs h; subst s; exact False.elim (complete_empty _ _ _ h)
  · intro s t ns hs h; subst s
    rw [load_issues] at h
    exact Or.inl (Except.ok.inj h).symm
  · apply BlockWellFormed.cons _ (fun s => s = AsyncWaveState.init afterWait) waitAll [move]
    · intro s hs
      exact wait_instruction_footprint waitAll s (Or.inl rfl) (by cbv) (pending_live s hs)
    · exact pending_closed
    · exact wait_post
    · apply BlockWellFormed.cons _ (fun _ => True) move []
      · intro s hs; subst s
        apply register_instruction_footprint move afterWait (Or.inl rfl)
        have h := pending_live returned (Or.inr rfl)
        rw [afterWait, wait_instruction_effect waitAll _ (Or.inl rfl) (by cbv)]
        exact h
      · intro s t c hs h; subst s; exact False.elim (complete_empty _ _ _ h)
      · intro _ _ _ _ _; trivial
      · exact BlockWellFormed.nil _

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem block_checked : checkAsyncBlock block = true := by cbv

/-- An inhabited multi-instruction instance of the exported theorem, applicable
also when the environment retires the load before its explicit wait. -/
theorem load_wait_use_refines (turns : List Turn) (sFinal : AsyncWaveState)
    (instructions : turns.map (·.instruction) = block)
    (execution : run (AsyncWaveState.init initial) turns = .ok sFinal) :
    sFinal.vmQueue = [] ∧ sFinal.lgkmQueue = [] ∧ sFinal.vsQueue = [] ∧
    sFinal.toGWave = syncRun initial block := by
  have wf : ∃ P, P (AsyncWaveState.init initial) ∧ BlockWellFormed P (turns.map (·.instruction)) :=
    ⟨fun s => s = AsyncWaveState.init initial, rfl, instructions ▸ block_wellFormed⟩
  simpa only [instructions] using waitcnt_safe_async_refines_sync initial turns sFinal wf
    (instructions ▸ block_checked) execution

def turns : List Turn := [⟨[], load, []⟩, ⟨[], waitAll, [0]⟩, ⟨[], move, []⟩]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem load_wait_use_inhabited :
    ∃ sFinal, run (AsyncWaveState.init initial) turns = .ok sFinal ∧
      readSgpr sFinal.toGWave 10 = 7 := by
  exact ⟨AsyncWaveState.init (instructionAfter move afterWait), by cbv, by cbv⟩

end ReadWaitUse

end Async
end Obend.Hardware.Gpu.Rdna2
