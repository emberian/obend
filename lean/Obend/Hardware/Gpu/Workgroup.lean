module
/-
# Barrier-separated workgroup kernels

GPUVerify (Betts et al., OOPSLA 2012, §3, https://nchong.github.io/papers/oopsla12.pdf)
uses delayed visibility and records accesses between barriers. Faial (Cogumbreiro et al., CAV 2021,
§3–4, https://cogumbreiro.github.io/assets/faial-cav21.pdf) separates uniform synchronization from
per-thread access protocols. Here stages are shared by the whole workgroup; their computations may
be different. Loops repeat whole stages, so inactive lanes still encounter every barrier.

`ArrayKernel.evalGroup` is the sequential, delayed-visibility evaluator. `sourceTrace` translates its accesses to the
existing G4 Vulkan model, including address-space-correct barriers. The static certificate below
checks concrete synchronization paths, not sequential outcomes or an enumeration of executions.

`phase_discipline_not_racy` derives the actual G4 race verdict from barrier geometry and phase
ownership. `phase_read_sequential` derives every pure read's unique preceding writer (or initial
zero), using Vulkan reads-from/from-read cycle contradictions. Its hypotheses do not contain a
sequential execution or a latest-write verdict. `sourceTrace_not_racy` and
`sourceTrace_read_sequential` transport those results from an arithmetic-free access protocol to
the source evaluator's trace for every input memory. `SourceProtocol.checkProgram` consumes this
interface with a proven HashSet checker; no G4 relation or field arithmetic runs during admission.

The trace mirrors the emitter's two instructions: workgroupBarrier, then storageBarrier. G4 models
initial values as zero and has no host events; host-provided input/constant values remain dispatch
boundary parameters. The visibility claim applies directly to communicated shared-memory writes;
it does not claim that G4's initial zero denotes an arbitrary input upload.
-/
public import Obend.Hardware.Gpu.Memory
public import Obend.Hardware.ArrayKernel
@[expose] public section

namespace Obend.Hardware.Gpu.Workgroup
open Obend.Hardware.Gpu.Memory
set_option autoImplicit false

/-- A stage's per-lane accesses. Arithmetic and indexing belong to the source language;
this common interface records their memory protocol. -/
abbrev Phase := Nat → List Ev

/-- Every lane encounters the same dynamic barrier instances, including lanes with no accesses. -/
def tracePhases : List Phase → Nat → Nat → List Ev
  | [], _, _ => []
  | p :: ps, lane, inst =>
    p lane ++ [.barrier (2 * inst) [.workgroup], .barrier (2 * inst + 1) [.storage]] ++
      tracePhases ps lane (inst + 1)

/-- G4 trace for one workgroup. Both address spaces are synchronized. -/
def trace (lanes : Nat) (phases : List Phase) : Shape :=
  { threads := (List.range lanes).map fun lane =>
      { id := lane, wg := 0, prog := tracePhases phases lane 0 } }

/-- A finite uniform loop: all lanes execute all iterations. -/
def repeatPhases (count : Nat) (body : List Phase) : List Phase :=
  (List.replicate count body).flatten

/-- Even an inactive lane encounters the phase barrier. -/
theorem phase_barrier (p : Phase) (ps : List Phase) (lane inst : Nat) :
    .barrier (2 * inst) [.workgroup] ∈ tracePhases (p :: ps) lane inst := by
  simp [tracePhases]

/-! ## The source array language uses this same trace interface -/

/-- Prefix-sum array addresses. Bounds are checked by `ArrayKernel.Program.check`. -/
def arrayBase : List Obend.Hardware.ArrayKernel.Buffer → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | b :: bs, i + 1 => b.size + arrayBase bs i

def arrayLoc (bs : List Obend.Hardware.ArrayKernel.Buffer) (array index : Nat) : Loc :=
  { space := match bs[array]? with
      | some b => if b.storage == .shared then .workgroup else .storage
      | none => .storage
    idx := arrayBase bs array + index }

/-- One logical invocation's actual source-language accesses, with arithmetic evaluated by
`ArrayKernel.runRegisters`. Constants have storage locations but are never written by a kernel. -/
def sourceLaneEvents (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group lane : Nat) : List Ev :=
  p.reads.map (fun r => .read (arrayLoc bs r.array (r.index.eval group lane)) false) ++
  (Obend.Hardware.ArrayKernel.laneWrites p mem group lane).map
    (fun (a, i, v) => .write (arrayLoc bs a i) v.toNat false)

/-- Logical invocations are assigned to physical lanes by the emitter's strided loop.
The barrier is outside that loop, inserted by `tracePhases`. -/
def sourcePhase (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) : Phase := fun lane =>
  ((List.range p.lanes).filter (fun logical => logical % width == lane)).flatMap
    (sourceLaneEvents bs p mem group)

/-- Record the source evaluator's concrete accesses at every phase boundary. This construction
is also a protocol projection: changing values cannot change addresses or barriers. -/
def sourcePhases (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (ps : List Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) : List Phase :=
  match ps with
  | [] => []
  | p :: rest => sourcePhase bs p mem group width ::
      sourcePhases bs rest (Obend.Hardware.ArrayKernel.evalPhase p group mem) group width

def sourceTrace (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) : Shape :=
  trace width (sourcePhases p.buffers d.phases mem group width)

/-! The admission protocol erases values, so checking never evaluates field arithmetic. -/

def eraseValue : Ev → Ev
  | .write l _ atomic => .write l 0 atomic
  | e => e

def eraseNode (n : Node) : Node := { n with ev := eraseValue n.ev }
def eraseShape (P : Shape) : Shape :=
  { P with threads := P.threads.map fun t => { t with prog := t.prog.map eraseValue } }

def sourceLaneProtocol (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (group lane : Nat) : List Ev :=
  p.reads.map (fun r => .read (arrayLoc bs r.array (r.index.eval group lane)) false) ++
  p.writes.map (fun w => .write (arrayLoc bs w.array (w.index.eval group lane)) 0 false)

def sourcePhaseProtocol (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (group width : Nat) : Phase := fun lane =>
  ((List.range p.lanes).filter (fun logical => logical % width == lane)).flatMap
    (sourceLaneProtocol bs p group)

def sourceProtocolPhases (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (ps : List Obend.Hardware.ArrayKernel.Phase) (group width : Nat) : List Phase :=
  ps.map (fun p => sourcePhaseProtocol bs p group width)

def sourceProtocolTrace (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (group width : Nat) : Shape :=
  trace width (sourceProtocolPhases p.buffers d.phases group width)

theorem sourceLaneEvents_erase (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group lane : Nat) :
    (sourceLaneEvents bs p mem group lane).map eraseValue = sourceLaneProtocol bs p group lane := by
  simp [sourceLaneEvents, sourceLaneProtocol, Obend.Hardware.ArrayKernel.laneWrites,
    List.map_append, List.map_map, Function.comp_def, eraseValue]

theorem sourcePhase_erase (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (p : Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width lane : Nat) :
    (sourcePhase bs p mem group width lane).map eraseValue =
      sourcePhaseProtocol bs p group width lane := by
  simp [sourcePhase, sourcePhaseProtocol, List.map_flatMap, sourceLaneEvents_erase]

private theorem sourceThread_erase (bs : List Obend.Hardware.ArrayKernel.Buffer)
    (ps : List Obend.Hardware.ArrayKernel.Phase) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width lane inst : Nat) :
    (tracePhases (sourcePhases bs ps mem group width) lane inst).map eraseValue =
      tracePhases (sourceProtocolPhases bs ps group width) lane inst := by
  induction ps generalizing mem inst with
  | nil => rfl
  | cons p ps ih =>
    simp only [sourcePhases, sourceProtocolPhases, List.map_cons, tracePhases,
      List.map_append, List.map_cons, List.map_nil, eraseValue, sourcePhase_erase]
    rw [ih]
    rfl

/-- The cheap access protocol is exactly the value-erasure of the evaluator's trace, for every
input memory. Admission checks this protocol once without running source arithmetic. -/
theorem sourceTrace_erase (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) :
    eraseShape (sourceTrace p d mem group width) = sourceProtocolTrace p d group width := by
  simp [eraseShape, sourceTrace, sourceProtocolTrace, trace, List.map_map, sourceThread_erase]

@[simp] theorem eraseValue_loc (e : Ev) : (eraseValue e).loc? = e.loc? := by
  cases e <;> rfl
@[simp] theorem eraseValue_write (e : Ev) : (eraseValue e).isWrite = e.isWrite := by
  cases e <;> rfl
@[simp] theorem eraseValue_read (e : Ev) : (eraseValue e).isRead = e.isRead := by
  cases e <;> rfl
@[simp] theorem eraseValue_barrier (e : Ev) (i : Nat) (ss : List Space) :
    (eraseValue e == .barrier i ss) = (e == .barrier i ss) := by
  cases e <;> rfl

private theorem map_getD {α β : Type} (xs : List α) (f : α → β) (i : Nat) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> rfl

@[simp] private theorem eraseValue_getD (xs : List Ev) (i : Nat) :
    (xs.map eraseValue).getD i (.barrier 0 []) = eraseValue (xs.getD i (.barrier 0 [])) :=
  map_getD xs eraseValue i (.barrier 0 [])

@[simp] private theorem eraseNode_getD (xs : List Node) (i : Nat) :
    (xs.map eraseNode).getD i default = eraseNode (xs.getD i default) :=
  map_getD xs eraseNode i default

private theorem eraseNodes (P : Shape) : (eraseShape P).nodes = P.nodes.map eraseNode := by
  simp only [Shape.nodes, eraseShape, Thread.nodes, List.flatMap_map, List.map_flatMap,
    List.length_map, List.map_map, Function.comp_def, eraseValue_getD, eraseNode]

/-! ## G4 relation lemmas and a synchronization certificate -/

private theorem mem_pairs {n a b : Nat} {p : Nat → Nat → Bool}
    (ha : a < n) (hb : b < n) (hp : p a b = true) : (a, b) ∈ pairs n p := by
  simp only [pairs, List.mem_flatMap, List.mem_range]
  refine ⟨a, ha, ?_⟩
  simp only [List.mem_filterMap, List.mem_range]
  exact ⟨b, hb, by simp [hp]⟩

private theorem mem_step (r : Rel) {a b : Nat} (h : (a, b) ∈ r) :
    (a, b) ∈ r.step := by
  simp only [Rel.step, List.mem_append]
  exact Or.inl h

private theorem mem_closure (r : Rel) (n : Nat) {a b : Nat} (h : (a, b) ∈ r) :
    (a, b) ∈ r.closure n := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih => exact ih r.step (mem_step r h)

private theorem mem_step_comp (r : Rel) {a b c : Nat}
    (hab : (a, b) ∈ r) (hbc : (b, c) ∈ r) : (a, c) ∈ r.step := by
  by_cases hac : (a, c) ∈ r
  · exact mem_step r hac
  · simp only [Rel.step, List.mem_append]
    right
    apply List.mem_flatMap.mpr
    refine ⟨(a, b), hab, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨(b, c), hbc, ?_⟩
    simp [Rel.has, hac]

/-- The three *base* Vulkan `ithb` edge kinds, before transitive closure. -/
def syncEdges (ns : List Node) (spaces : List Space) : Rel :=
  pairs ns.length fun a b =>
    let x := (ns.getD a default).ev
    let y := (ns.getD b default).ev
    (x.hasSems spaces && y.hasSems spaces && (sw ns).has a b) ||
    ((x.inSpaces spaces || x.hasSems spaces) && (po ns).has a b && y.hasSems spaces) ||
    (x.hasSems spaces && (po ns).has a b && (y.inSpaces spaces || y.hasSems spaces))

/-- A short path certificate. Three edges suffice for write → its barrier → another lane's
barrier → read. Earlier/later phase paths may use the same shared barrier instance. -/
def shortPath (r : Rel) (a b : Nat) : Bool :=
  r.has a b || r.any (fun (x, y) => x == a &&
    (r.has y b || r.any (fun (z, t) => z == y && r.has t b)))

private theorem shortPath_sound (r : Rel) {a b : Nat} (h : shortPath r a b = true) :
    (a, b) ∈ r.closure 2 := by
  simp only [shortPath, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨⟨x,y⟩, hxy, h⟩
  · exact mem_closure r 2 (by simpa [Rel.has] using h)
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨rfl, h | ⟨⟨z,t⟩, hzt, h⟩⟩
    · exact mem_step r.step (mem_step_comp r hxy (by simpa [Rel.has] using h))
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, htb⟩
      exact mem_step_comp r.step (mem_step r hxy)
        (mem_step_comp r hzt (by simpa [Rel.has] using htb))

private theorem closure_add (r : Rel) (n m : Nat) :
    r.closure (n + m) = (r.closure n).closure m := by
  induction n generalizing r with
  | zero => simp [Rel.closure]
  | succ n ih => simpa [Nat.succ_add, Rel.closure] using ih r.step

/-- Finite, value-independent evidence of actual synchronization, not an assumption of an
outcome or of the `racy` result. `po` handles same-thread pairs. -/
def ordered (ns : List Node) (a b : Nat) : Bool :=
  (po ns).has a b || (2 ≤ ns.length &&
    (shortPath (syncEdges ns [.storage]) a b ||
      shortPath (syncEdges ns [.workgroup]) a b ||
      shortPath (syncEdges ns [.storage, .workgroup]) a b))

private theorem path_hb (ns : List Node) (T : List Space) (a b : Nat)
    (hlen : 2 ≤ ns.length) (h : shortPath (syncEdges ns T) a b = true) :
    (a, b) ∈ ithb ns T := by
  have hpath := shortPath_sound _ h
  have hfull := mem_closure ((syncEdges ns T).closure 2) (ns.length - 2) hpath
  rw [← closure_add] at hfull
  have heq : 2 + (ns.length - 2) = ns.length := by omega
  rw [heq] at hfull
  exact hfull

/-- The certificate's edges belong to the real G4 happens-before relation. -/
theorem ordered_hb (ns : List Node) (a b : Nat) (h : ordered ns a b = true) :
    (hb ns).has a b = true := by
  simp only [ordered, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  apply List.contains_iff_mem.mpr
  simp only [hb, List.mem_append]
  rcases h with h | ⟨hlen, (h | h) | h⟩
  · exact Or.inl (Or.inl (Or.inl (by simpa [Rel.has] using h)))
  · exact Or.inl (Or.inl (Or.inr (path_hb ns [.storage] a b hlen h)))
  · exact Or.inl (Or.inr (path_hb ns [.workgroup] a b hlen h))
  · exact Or.inr (path_hb ns [.storage, .workgroup] a b hlen h)

/-- A structural barrier rule, useful without evaluating the quadratic G4 checker.
Only event identities, scopes and program positions are premises. The result is the existing
Vulkan happens-before relation. -/
theorem barrier_orders (ns : List Node) (a b enter leave inst : Nat) (space : Space)
    (ha : a < ns.length) (hb' : b < ns.length)
    (he : enter < ns.length) (hl : leave < ns.length) (hne : enter ≠ leave)
    (hea : (ns.getD enter default).ev = .barrier inst [space])
    (hle : (ns.getD leave default).ev = .barrier inst [space])
    (hwg : (ns.getD enter default).wg = (ns.getD leave default).wg)
    (hat : (ns.getD a default).id.t = (ns.getD enter default).id.t)
    (hai : (ns.getD a default).id.i < (ns.getD enter default).id.i)
    (hbt : (ns.getD leave default).id.t = (ns.getD b default).id.t)
    (hbi : (ns.getD leave default).id.i < (ns.getD b default).id.i)
    (ham : (ns.getD a default).ev.inSpaces [space] = true)
    (hbm : (ns.getD b default).ev.inSpaces [space] = true) :
    (Obend.Hardware.Gpu.Memory.hb ns).has a b = true := by
  have hpoa : (po ns).has a enter = true := by
    apply List.contains_iff_mem.mpr
    apply mem_pairs ha he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hat, hai⟩
  have hpob : (po ns).has leave b = true := by
    apply List.contains_iff_mem.mpr
    apply mem_pairs hl hb'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hbt, hbi⟩
  have hsw : (sw ns).has enter leave = true := by
    apply List.contains_iff_mem.mpr
    apply mem_pairs he hl
    simp only [hne, bne_iff_ne, hwg, beq_self_eq_true, hea, hle,
      Bool.and_eq_true, true_and, and_true]
    exact hne
  have h₁ : (a, enter) ∈ syncEdges ns [space] := by
    apply mem_pairs ha he
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl (Or.inr ⟨⟨Or.inl ham, hpoa⟩, by rw [hea]; simp [Ev.hasSems]⟩)
  have h₂ : (enter, leave) ∈ syncEdges ns [space] := by
    apply mem_pairs he hl
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl (Or.inl ⟨⟨by rw [hea]; simp [Ev.hasSems], by rw [hle]; simp [Ev.hasSems]⟩, hsw⟩)
  have h₃ : (leave, b) ∈ syncEdges ns [space] := by
    apply mem_pairs hl hb'
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨⟨by rw [hle]; simp [Ev.hasSems], hpob⟩, Or.inl hbm⟩
  have hp : shortPath (syncEdges ns [space]) a b = true := by
    simp only [shortPath, Bool.or_eq_true, List.any_eq_true]
    right
    refine ⟨(a, enter), h₁, ?_⟩
    simp only [beq_self_eq_true, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
    right
    exact ⟨(enter, leave), h₂, by simpa [Rel.has] using h₃⟩
  apply ordered_hb ns a b
  simp only [ordered, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  cases space with
  | storage => exact Or.inr ⟨by omega, Or.inl (Or.inl hp)⟩
  | workgroup => exact Or.inr ⟨by omega, Or.inl (Or.inr hp)⟩

/-! ## A phase discipline implies the Vulkan ordering certificates -/

/-- Data produced by a phase lowering, without memory-model proofs or execution outcomes.
`barrier p t` names thread `t`'s barrier after phase `p`, as an index in `Shape.nodes`. -/
structure PhaseLayout where
  phase : Nat → Nat
  barrier : Nat → Nat → Space → Nat

/-- Phase labels parallel to a thread's emitted events, including both barrier instructions. -/
def phaseTags : List Phase → Nat → Nat → List Nat
  | [], _, _ => []
  | p :: ps, lane, inst =>
    List.replicate ((p lane).length + 2) inst ++ phaseTags ps lane (inst + 1)

/-- Position of the workgroup barrier ending phase `p` in one thread's program. -/
def barrierOffset : List Phase → Nat → Nat → Nat
  | [], _, _ => 0
  | p :: _, lane, 0 => (p lane).length
  | p :: ps, lane, n + 1 => (p lane).length + 2 + barrierOffset ps lane n

/-- Extract the structural certificate while lowering the very same phase sequence to events.
Array-backed lookups make phase and barrier lookup constant-time. No memory-model search occurs. -/
def layout (lanes : Nat) (ps : List Phase) : PhaseLayout :=
  let counts := (List.range lanes).map fun lane => ps.map fun p => (p lane).length + 2
  let starts := ((counts.map List.sum).scanl (· + ·) 0).toArray
  let tags := (counts.flatMap fun ns => ns.zipIdx.flatMap fun (n, phase) =>
    List.replicate n phase).toArray
  let barriers := (counts.zipIdx.map fun (ns, lane) =>
    (((ns.scanl (· + ·) 0).drop 1).map fun offset => starts.getD lane 0 + offset - 2).toArray).toArray
  { phase := fun a => tags.getD a 0
    barrier := fun p lane space => (barriers.getD lane #[]).getD p 0 +
      if space = .storage then 1 else 0 }

def sourceLayout (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) : PhaseLayout :=
  layout width (sourcePhases p.buffers d.phases mem group width)

def sourceProtocolLayout (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (group width : Nat) : PhaseLayout :=
  layout width (sourceProtocolPhases p.buffers d.phases group width)

/-- Linear construction of event identities, equivalent to G4's indexed-list definition. -/
def threadNodesFast (t : Thread) : List Node :=
  t.prog.mapIdx fun i e => { id := ⟨t.id, i⟩, wg := t.wg, ev := e }

theorem threadNodesFast_eq (t : Thread) : threadNodesFast t = t.nodes := by
  apply List.ext_getElem
  · simp [threadNodesFast, Thread.nodes]
  · intro i hi hj
    have hib : i < t.prog.length := by simpa [threadNodesFast] using hi
    simp [threadNodesFast, Thread.nodes, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hib]

def nodesFast (P : Shape) : Array Node := (P.threads.flatMap threadNodesFast).toArray

theorem nodesFast_eq (P : Shape) : nodesFast P = P.nodes.toArray := by
  have ht : threadNodesFast = Thread.nodes := funext threadNodesFast_eq
  simp [nodesFast, Shape.nodes, ht]

/-- Local geometry of one access and one barrier. Checks only event labels and positions.
There is no happens-before query or transitive closure in this predicate. -/
def boundary (P : Shape) (c : PhaseLayout) (a p : Nat) (space : Space) (before : Bool) : Bool :=
  let x := P.nodes.getD a default
  let j := c.barrier p x.id.t space
  let y := P.nodes.getD j default
  j < P.nodes.length && y.ev == .barrier (2 * p + if space = .storage then 1 else 0) [space] &&
  x.wg == 0 && y.wg == 0 && x.id.t == y.id.t &&
  (if before then y.id.i < x.id.i else x.id.i < y.id.i)

/-- Linear in the access count times the number of stages: a stage barrier is after its own
accesses and before every later stage's accesses. This checker never materializes Vulkan relations. -/
def PhaseLayout.geometry (P : Shape) (c : PhaseLayout) : Bool :=
  let ns := P.nodes
  ((List.range ns.length).filter fun a => (ns.getD a default).ev.loc?.isSome).all fun a =>
    [.storage, .workgroup].all fun space =>
      boundary P c a (c.phase a) space false &&
        (List.range (c.phase a)).all (fun p => boundary P c a p space true)

/-- Executable form of the geometry check with cached nodes and constant-time array lookup. -/
def boundaryFast (ns : Array Node) (c : PhaseLayout) (a p : Nat) (space : Space)
    (before : Bool) : Bool :=
  let x := ns[a]?.getD default
  let j := c.barrier p x.id.t space
  let y := ns[j]?.getD default
  j < ns.size && y.ev == .barrier (2 * p + if space = .storage then 1 else 0) [space] &&
  x.wg == 0 && y.wg == 0 && x.id.t == y.id.t &&
  (if before then y.id.i < x.id.i else x.id.i < y.id.i)

def PhaseLayout.geometryFast (P : Shape) (c : PhaseLayout) : Bool :=
  let ns := nodesFast P
  ((List.range ns.size).filter fun a => (ns[a]?.getD default).ev.loc?.isSome).all fun a =>
    [.storage, .workgroup].all fun space =>
      boundaryFast ns c a (c.phase a) space false &&
        (List.range (c.phase a)).all (fun p => boundaryFast ns c a p space true)

/-- The optimized checker decides exactly the structural predicate used by the proof. -/
theorem geometryFast_eq (P : Shape) (c : PhaseLayout) : c.geometryFast P = c.geometry P := by
  simp [PhaseLayout.geometryFast, PhaseLayout.geometry, boundaryFast, boundary,
    nodesFast_eq, List.getD_eq_getElem?_getD]

theorem boundary_facts (P : Shape) (c : PhaseLayout) (a p : Nat) (space : Space) (before : Bool)
    (h : boundary P c a p space before = true) :
    let x := P.nodes.getD a default
    let j := c.barrier p x.id.t space
    let y := P.nodes.getD j default
    j < P.nodes.length ∧ y.ev = .barrier (2 * p + if space = .storage then 1 else 0) [space] ∧
    x.wg = 0 ∧ y.wg = 0 ∧ x.id.t = y.id.t ∧
    (if before then y.id.i < x.id.i else x.id.i < y.id.i) := by
  simp only [boundary, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hj, hev⟩, hxw⟩, hyw⟩, ht⟩, hi⟩
  exact ⟨hj, hev, hxw, hyw, ht, by cases before <;> simpa using hi⟩

private theorem mem_bound (P : Shape) (a : Nat) (ha : a ∈ P.static.mems) :
    a < P.nodes.length := List.mem_range.mp (List.mem_filter.mp ha).1

private theorem mem_spaces (P : Shape) (a : Nat) (ha : a ∈ P.static.mems) :
    (P.nodes.getD a default).ev.inSpaces [.storage, .workgroup] = true := by
  have hm := (List.mem_filter.mp ha).2
  change (P.nodes.getD a default).ev.loc?.isSome = true at hm
  cases he : (P.nodes.getD a default).ev with
  | write l v atomic => cases l with | mk space idx => cases space <;> rfl
  | read l atomic => cases l with | mk space idx => cases space <;> rfl
  | rmw l op => cases l with | mk space idx => cases space <;> rfl
  | barrier i sems => rw [he] at hm; contradiction

/-- Cross-phase ordering follows from the barrier geometry, for every access in every kernel,
without assuming race freedom or evaluating the G4 closure. -/
theorem phase_hb (P : Shape) (c : PhaseLayout) (hg : c.geometry P = true)
    (a b : Nat) (ha : a ∈ P.static.mems) (hb' : b ∈ P.static.mems)
    (hab : c.phase a < c.phase b) (space : Space)
    (ham : (P.nodes.getD a default).ev.inSpaces [space] = true)
    (hbm : (P.nodes.getD b default).ev.inSpaces [space] = true) : (hb P.nodes).has a b = true := by
  have hspace : space ∈ [.storage, .workgroup] := by cases space <;> simp
  have hga := List.all_eq_true.mp (List.all_eq_true.mp hg a ha) space hspace
  have hgb := List.all_eq_true.mp (List.all_eq_true.mp hg b hb') space hspace
  simp only [Bool.and_eq_true, List.all_eq_true] at hga hgb
  have hentry := boundary_facts P c a (c.phase a) space false hga.1
  have hexit := boundary_facts P c b (c.phase a) space true (hgb.2 _ (List.mem_range.mpr hab))
  dsimp only at hentry hexit
  obtain ⟨he, hev, haw, hew, hat, hai⟩ := hentry
  obtain ⟨hl, hlv, hbw, hlw, hbt, hbi⟩ := hexit
  simp only [Bool.false_eq_true, ↓reduceIte] at hai hbi
  let enter := c.barrier (c.phase a) (P.nodes.getD a default).id.t space
  let leave := c.barrier (c.phase a) (P.nodes.getD b default).id.t space
  by_cases heq : enter = leave
  · have hpo : (po P.nodes).has a b = true := by
      apply List.contains_iff_mem.mpr
      apply mem_pairs (mem_bound P a ha) (mem_bound P b hb')
      have heq' : c.barrier (c.phase a) (P.nodes.getD a default).id.t space =
          c.barrier (c.phase a) (P.nodes.getD b default).id.t space := heq
      rw [heq'] at hat hai
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨hat.trans hbt.symm, Nat.lt_trans hai hbi⟩
    exact ordered_hb P.nodes a b (by simp only [ordered, hpo, Bool.true_or])
  · exact barrier_orders P.nodes a b enter leave
      (2 * c.phase a + if space = .storage then 1 else 0) space
      (mem_bound P a ha) (mem_bound P b hb') he hl heq hev hlv
      (hew.trans hlw.symm) hat hai hbt.symm hbi ham hbm

private theorem sameLoc_symm (x y : Node) (h : x.sameLoc y = true) :
    y.sameLoc x = true := by
  unfold Node.sameLoc at *
  cases hx : x.ev.loc? <;> cases hy : y.ev.loc? <;> simp_all [beq_iff_eq]

private theorem phase_locord (P : Shape) (c : PhaseLayout) (hg : c.geometry P = true)
    (a b : Nat) (ha : a ∈ P.static.mems) (hb' : b ∈ P.static.mems)
    (hab : c.phase a < c.phase b) (hl : P.static.sameLoc a b = true) :
    P.static.locord.has a b = true := by
  apply List.contains_iff_mem.mpr
  apply mem_pairs (mem_bound P a ha) (mem_bound P b hb')
  simp only [Bool.and_eq_true]
  refine ⟨hl, ?_⟩
  have hloc := hl
  change (P.nodes.getD a default).sameLoc (P.nodes.getD b default) = true at hloc
  unfold Node.sameLoc at hloc
  cases hla : (P.nodes.getD a default).ev.loc? with
  | none => simp only [hla, Bool.false_eq_true] at hloc
  | some l =>
    cases hlb : (P.nodes.getD b default).ev.loc? with
    | none => simp only [hla, hlb, Bool.false_eq_true] at hloc
    | some m =>
      have heq : l = m := by simpa only [hla, hlb, beq_iff_eq] using hloc
      subst m
      apply phase_hb P c hg a b ha hb' hab l.space
      · unfold Ev.inSpaces; rw [hla]; simp
      · unfold Ev.inSpaces; rw [hlb]; simp

/-- The phase's memory protocol: conflicting events must be in different phases. It can be
established by unique scatter addresses plus disjoint source/destination arrays. No synchronization
or execution outcome occurs in this condition. The finite quantifiers are deliberately exposed so
clients can prove it from a symbolic ownership invariant instead of enumerating pairs. -/
def PhaseLayout.Separated (P : Shape) (c : PhaseLayout) : Prop :=
  ∀ a ∈ P.static.mems, ∀ b ∈ P.static.mems,
    a ≠ b → P.static.sameLoc a b = true →
    ((P.nodes.getD a default).ev.isWrite || (P.nodes.getD b default).ev.isWrite) = true →
    c.phase a ≠ c.phase b

instance (P : Shape) (c : PhaseLayout) : Decidable (c.Separated P) :=
  inferInstanceAs (Decidable (∀ a ∈ P.static.mems, ∀ b ∈ P.static.mems,
    a ≠ b → P.static.sameLoc a b = true →
    ((P.nodes.getD a default).ev.isWrite || (P.nodes.getD b default).ev.isWrite) = true →
    c.phase a ≠ c.phase b))

/-- Phase-separated unique writes plus uniform barriers imply race freedom in the actual G4
Vulkan model, universally over phase layouts and memory values. -/
theorem phase_discipline_not_racy (P : Shape) (c : PhaseLayout)
    (hg : c.geometry P = true) (hs : c.Separated P) : P.static.racy = false := by
  apply Bool.eq_false_iff.mpr
  intro hracy
  simp only [Static.racy, List.any_eq_true, Bool.and_eq_true] at hracy
  obtain ⟨a, ha, b, hb', hbad⟩ := hracy
  obtain ⟨⟨⟨⟨⟨hab, hloc⟩, hwrite⟩, _⟩, hnotab⟩, hnotba⟩ := hbad
  have hne : a ≠ b := by simpa using hab
  have hp := hs a ha b hb' hne hloc hwrite
  rcases Nat.lt_or_gt_of_ne hp with hab | hba
  · have ho := phase_locord P c hg a b ha hb' hab hloc
    simp only [ho, Bool.not_true, Bool.false_eq_true] at hnotab
  · have hsym : P.static.sameLoc b a = true := sameLoc_symm _ _ hloc
    have ho := phase_locord P c hg b a hb' ha hba hsym
    simp only [ho, Bool.not_true, Bool.false_eq_true] at hnotba

/-- Check every potentially conflicting pair using program order or scoped barrier paths. -/
def synchronizationSafe (P : Shape) : Bool :=
  let ns := P.nodes
  (List.range ns.length).all fun a => (List.range ns.length).all fun b =>
    a == b || !(ns.getD a default).sameLoc (ns.getD b default) ||
    !((ns.getD a default).ev.isWrite || (ns.getD b default).ev.isWrite) ||
    ordered ns a b || ordered ns b a

/-- General race freedom in G4, for every emitted language instance and every value trace.
The hypothesis is a decidable static path certificate; it does not assert a sequential execution. -/
theorem synchronizationSafe_not_racy (P : Shape) (h : synchronizationSafe P = true) :
    P.static.racy = false := by
  simp only [synchronizationSafe, List.all_eq_true] at h
  apply Bool.eq_false_iff.mpr
  intro hracy
  simp only [Static.racy, List.any_eq_true, Bool.and_eq_true] at hracy
  obtain ⟨a, ha, b, hb', hbad⟩ := hracy
  obtain ⟨⟨⟨⟨⟨hab, hloc⟩, hwrite⟩, hatom⟩, hnotab⟩, hnotba⟩ := hbad
  have ha' : a ∈ List.range P.nodes.length := (List.mem_filter.mp ha).1
  have hb'' : b ∈ List.range P.nodes.length := (List.mem_filter.mp hb').1
  have hs := h a ha' b hb''
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hs
  have hne : a ≠ b := by simpa using hab
  have hsl : (P.nodes.getD a default).sameLoc (P.nodes.getD b default) = true := hloc
  have locord_of {x y : Nat} (hx : x ∈ List.range P.nodes.length)
      (hy : y ∈ List.range P.nodes.length)
      (hl : (P.nodes.getD x default).sameLoc (P.nodes.getD y default) = true)
      (ho : ordered P.nodes x y = true) : P.static.locord.has x y = true := by
    apply List.contains_iff_mem.mpr
    apply mem_pairs (List.mem_range.mp hx) (List.mem_range.mp hy)
    simp only [Bool.and_eq_true]
    exact ⟨hl, ordered_hb P.nodes x y ho⟩
  rcases hs with (((heq | hdiff) | hreads) | ho) | ho
  · exact hne heq
  · exact Bool.noConfusion (hsl.symm.trans hdiff)
  · exact Bool.noConfusion (hwrite.symm.trans hreads)
  · have hl := locord_of ha' hb'' hsl ho
    simp [hl] at hnotab
  · have hsym : (P.nodes.getD b default).sameLoc (P.nodes.getD a default) = true := by
      unfold Node.sameLoc at *
      cases h₁ : (P.nodes.getD a default).ev.loc? <;>
        cases h₂ : (P.nodes.getD b default).ev.loc? <;> simp_all [beq_iff_eq]
    have hl := locord_of hb'' ha' hsym ho
    simp [hl] at hnotba

/-! ## The sequential read rule is forced by G4 consistency -/

/-- Validity of the reads-from part of a closed-workgroup witness. This is the same finite
candidate test as `Static.spec`, exposed without enumerating all rank/order slots. -/
def sourceValid (s : Static) (w : List Nat) (r : Nat) : Bool :=
  match s.rf w r with
  | .init => true
  | .internal a => (s.writesAt r).contains a && a != r
  | .external _ => false

private theorem wf_get (w : List Nat) (cs : List (List Nat)) (h : Wf w cs)
    (i : Nat) (c : List Nat) (hi : cs[i]? = some c) : w.getD i 0 ∈ c := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons x d w ds hx hw ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
              subst c
              exact hx
    | succ i => exact ih i (by simpa using hi)

private theorem posOf_findIdx (xs : List Nat) (r : Nat) :
    posOf xs r = xs.findIdx (· == r) := by
  rw [List.findIdx_eq_getD_findIdx?]
  unfold posOf
  cases xs.findIdx? (· == r) <;> rfl

/-- Closed G4 well-formed witnesses automatically satisfy the finite reads-from candidate
condition; clients need not assume it separately. -/
theorem wf_sourceValid (P : Shape) (w : List Nat) (r : Nat)
    (hex : P.external = []) (hw : Wf w P.spec) (hr : r ∈ P.static.reads) :
    sourceValid P.static w r = true := by
  have hexists : ∃ x ∈ P.static.reads, (x == r) = true := ⟨r, hr, by simp⟩
  have hpos : posOf P.static.reads r < P.static.reads.length := by
    rw [posOf_findIdx]
    exact List.findIdx_lt_length_of_exists hexists
  have hread : P.static.reads[posOf P.static.reads r]? = some r := by
    rw [posOf_findIdx]
    have hval := List.findIdx_getElem (xs := P.static.reads) (p := (· == r))
      (w := List.findIdx_lt_length_of_exists hexists)
    simpa only [beq_iff_eq] using (List.getElem?_eq_getElem
      (List.findIdx_lt_length_of_exists hexists)).trans (congrArg some (by
        simpa only [beq_iff_eq] using hval))
  have hread' : P.static.reads[posOf P.static.reads r] = r := by
    simpa only [List.getElem?_eq_getElem hpos, Option.some.injEq] using hread
  have hea : P.static.externalAt r = [] := by
    simp [Static.externalAt, Shape.static, hex]
  have hspec : P.spec[posOf P.static.reads r]? =
      some (0 :: ((P.static.writesAt r).filter (· != r)).map (· + 1)) := by
    simp [Shape.spec, Static.spec, List.getElem?_append, List.length_map, hpos,
      List.getElem?_map, hread, hread', hea]
  have hc := wf_get w P.spec hw (posOf P.static.reads r) _ hspec
  simp only [List.mem_cons, List.mem_map] at hc
  rcases hc with hz | ⟨a, ha, hk⟩
  · simp only [sourceValid, Static.rf, hz, ↓reduceIte]
  · have haw : a ∈ P.static.writesAt r := (List.mem_filter.mp ha).1
    have hne : a ≠ r := by simpa using (List.mem_filter.mp ha).2
    have hb : a < P.nodes.length := by
      have ham := (List.mem_filter.mp haw).1
      exact List.mem_range.mp (List.mem_filter.mp ham).1
    have heq : P.static.rf w r = .internal a := by
      simp only [Static.rf, ← hk]
      simp [show a + 1 ≠ 0 by omega,
        show a + 1 ≤ P.static.nodes.length by exact hb]
    simp [sourceValid, heq, haw, hne]

/-- `last` is the last write before this read: every other write is either before `last` or after
`r`, in the actual scoped location order. This is static and independent of reads-from choices,
write values, coherence ranks, and the witness's total-order slots. -/
def latestWrite (s : Static) (r last : Nat) : Bool :=
  s.reads.contains r && (s.writesAt r).contains last && last != r &&
  s.locord.has last r && (s.writesAt r).all (fun a =>
    a == last || s.locord.has a last || s.locord.has r a)

/-- A phase-index certificate for a read's reaching definition. Comparisons are on source
stage numbers, not the G4 relation: all other same-location writes precede `last` or follow `r`. -/
def PhaseLayout.latest (P : Shape) (c : PhaseLayout) (r last : Nat) : Bool :=
  P.static.reads.contains r && (P.static.writesAt r).contains last &&
  c.phase last < c.phase r && (P.static.writesAt r).all (fun a =>
    a == last || c.phase a < c.phase last || c.phase r < c.phase a)

private theorem read_mem (P : Shape) (r : Nat) (hr : r ∈ P.static.reads) :
    r ∈ P.static.mems := by
  obtain ⟨hb, hv⟩ := List.mem_filter.mp hr
  apply List.mem_filter.mpr
  refine ⟨hb, ?_⟩
  change (P.nodes.getD r default).ev.isRead = true at hv
  change (P.nodes.getD r default).ev.loc?.isSome = true
  cases he : (P.nodes.getD r default).ev <;> simp_all [Ev.isRead, Ev.loc?]

private theorem write_mem (P : Shape) (r : Nat) (hr : r ∈ P.static.writes) :
    r ∈ P.static.mems := by
  obtain ⟨hb, hv⟩ := List.mem_filter.mp hr
  apply List.mem_filter.mpr
  refine ⟨hb, ?_⟩
  change (P.nodes.getD r default).ev.isWrite = true at hv
  change (P.nodes.getD r default).ev.loc?.isSome = true
  cases he : (P.nodes.getD r default).ev <;> simp_all [Ev.isWrite, Ev.loc?]

private theorem sameLoc_trans (x y z : Node) (hxy : x.sameLoc y = true)
    (hyz : y.sameLoc z = true) : x.sameLoc z = true := by
  unfold Node.sameLoc at *
  cases hx : x.ev.loc? <;> cases hy : y.ev.loc? <;> cases hz : z.ev.loc? <;>
    simp_all [beq_iff_eq]

/-- The source phase reaching-definition certificate entails the real Vulkan latest-write
certificate. This is the missing structural bridge: no happens-before fact is a premise. -/
theorem phase_latestWrite (P : Shape) (c : PhaseLayout) (hg : c.geometry P = true)
    (r last : Nat) (hl : c.latest P r last = true) : latestWrite P.static r last = true := by
  simp only [PhaseLayout.latest, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, List.all_eq_true] at hl
  obtain ⟨⟨⟨hr, hw⟩, hbefore⟩, hall⟩ := hl
  have hrm := read_mem P r hr
  have hlm := write_mem P last (List.mem_filter.mp hw).1
  have hrl : P.static.sameLoc r last = true := (List.mem_filter.mp hw).2
  have hlr : P.static.sameLoc last r = true := sameLoc_symm _ _ hrl
  have hne : last ≠ r := by intro he; subst last; omega
  simp only [latestWrite, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne,
    List.all_eq_true]
  refine ⟨⟨⟨⟨hr, hw⟩, hne⟩, phase_locord P c hg last r hlm hrm hbefore hlr⟩, ?_⟩
  intro a ha
  have ham := write_mem P a (List.mem_filter.mp ha).1
  have hra : P.static.sameLoc r a = true := (List.mem_filter.mp ha).2
  have hoa := hall a ha
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hoa ⊢
  rcases hoa with (heq | hb) | hb
  · exact Or.inl (Or.inl heq)
  · have hal : P.static.sameLoc a last = true :=
      sameLoc_trans _ _ _ (sameLoc_symm _ _ hra) hrl
    exact Or.inl (Or.inr (phase_locord P c hg a last ham hlm hb hal))
  · exact Or.inr (phase_locord P c hg r a hrm ham hb hra)

private theorem consistent_edge (s : Static) (w : List Nat)
    (h : s.consistent w = true) {a b : Nat}
    (he : (a,b) ∈ s.locord ++ s.rfEdges w ++ s.frEdges w ++ s.asmoEdges w) :
    s.ord w a < s.ord w b := by
  dsimp only [Static.consistent, Static.consistentWith] at h
  simp only [Bool.false_eq_true, ite_true, ite_false, List.append_nil, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1.1.2 (a,b) he
  simpa using hh

private theorem consistent_locord (s : Static) (w : List Nat)
    (h : s.consistent w = true) {a b : Nat} (he : s.locord.has a b = true) :
    s.ord w a < s.ord w b :=
  consistent_edge s w h (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl
    (by simpa [Rel.has] using he))))

private theorem consistent_rf (s : Static) (w : List Nat)
    (h : s.consistent w = true) {r a : Nat} (hr : r ∈ s.reads)
    (hf : s.rf w r = .internal a) : s.ord w a < s.ord w r := by
  apply consistent_edge s w h
  simp only [List.mem_append]
  apply Or.inl; apply Or.inl; apply Or.inr
  apply List.mem_filterMap.mpr
  exact ⟨r, hr, by simp [hf]⟩

private theorem consistent_fr_init (s : Static) (w : List Nat)
    (h : s.consistent w = true) {r a : Nat} (hr : r ∈ s.reads)
    (ha : a ∈ s.writesAt r) (hne : a ≠ r) (hf : s.rf w r = .init) :
    s.ord w r < s.ord w a := by
  apply consistent_edge s w h
  simp only [List.mem_append]
  apply Or.inl; apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨a, ha, by simp [hne, hf]⟩

private theorem consistent_fr_shadow (s : Static) (w : List Nat)
    (h : s.consistent w = true) {r a last : Nat} (hr : r ∈ s.reads)
    (hl : last ∈ s.writesAt r) (hlr : last ≠ r) (hal : a ≠ last)
    (hf : s.rf w r = .internal a) (ho : s.locord.has a last = true) :
    s.ord w r < s.ord w last := by
  apply consistent_edge s w h
  simp only [List.mem_append]
  apply Or.inl; apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨last, hl, by simp [hlr, hf, hal, ho]⟩

/-- Every consistent G4 witness reads the latest preceding write. The proof rules out an
initial/stale read by the `fr` cycle and a future read by the `rf` cycle; sequential behavior is
therefore a consequence of the Vulkan constraints, not supplied as a premise. -/
theorem consistent_reads_latest (s : Static) (w : List Nat) (r last : Nat)
    (hc : s.consistent w = true) (hv : sourceValid s w r = true)
    (hl : latestWrite s r last = true) : s.rf w r = .internal last := by
  simp only [latestWrite, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne,
    List.all_eq_true] at hl
  obtain ⟨⟨⟨⟨hr, hw⟩, hne⟩, hbefore⟩, hall⟩ := hl
  have hlr := consistent_locord s w hc hbefore
  cases hf : s.rf w r with
  | init =>
    have hrl := consistent_fr_init s w hc hr hw hne hf
    omega
  | external v => simp [sourceValid, hf] at hv
  | internal a =>
    by_cases heq : a = last
    · simpa [heq]
    · have ha : a ∈ s.writesAt r := by
        have hva : (s.writesAt r).contains a = true ∧ a ≠ r := by
          simpa [sourceValid, hf, Bool.and_eq_true] using hv
        exact List.contains_iff_mem.mp hva.1
      have ho := hall a ha
      simp only [Bool.or_eq_true, beq_iff_eq] at ho
      rcases ho with (he | ho) | ho
      · exact False.elim (heq he)
      · have hrl := consistent_fr_shadow s w hc hr hw hne heq hf ho
        omega
      · have hra := consistent_locord s w hc ho
        have har := consistent_rf s w hc hr hf
        omega

/-- The value rule consumed by a source-language simulation proof. -/
theorem consistent_read_value (s : Static) (w : List Nat) (r last : Nat)
    (hc : s.consistent w = true) (hv : sourceValid s w r = true)
    (hl : latestWrite s r last = true) :
    s.valueOfRead w r = s.valueOfWrite w s.nodes.length last := by
  simp [Static.valueOfRead, consistent_reads_latest s w r last hc hv hl]

/-- Closed, well-formed G4 executions obey the sequential read rule without an extra validity
assumption. Only the static latest-write certificate remains to be discharged by the lowering. -/
theorem closed_read_value (P : Shape) (w : List Nat) (r last : Nat)
    (hex : P.external = []) (hw : Wf w P.spec) (hc : P.consistent w = true)
    (hl : latestWrite P.static r last = true) :
    P.static.valueOfRead w r = P.static.valueOfWrite w P.nodes.length last := by
  have hr : r ∈ P.static.reads := by
    have hh := hl
    simp only [latestWrite, Bool.and_eq_true] at hh
    exact List.contains_iff_mem.mp hh.1.1.1.1
  exact consistent_read_value P.static w r last hc (wf_sourceValid P w r hex hw hr) hl

/-- Sequential visibility from the language's phase discipline, for every closed, well-formed
consistent G4 execution. Its premises check labels, barriers and reaching-definition phase numbers;
they do not assert the result of an execution or a Vulkan ordering edge. -/
theorem phase_read_value (P : Shape) (c : PhaseLayout) (w : List Nat) (r last : Nat)
    (hg : c.geometry P = true) (hl : c.latest P r last = true)
    (hex : P.external = []) (hw : Wf w P.spec) (hc : P.consistent w = true) :
    P.static.valueOfRead w r = P.static.valueOfWrite w P.nodes.length last :=
  closed_read_value P w r last hex hw hc (phase_latestWrite P c hg r last hl)

/-! ## Deterministic sequential reads from phase separation alone -/

/-- Specification of the reaching definition: select the greatest preceding writer phase.
The admission gate does not execute this search; its proof applies to every read. -/
def maxBefore (phase : Nat → Nat) (bound : Nat) : List Nat → Option Nat
  | [] => none
  | a :: rest =>
    let best := maxBefore phase bound rest
    if phase a < bound then
      match best with
      | none => some a
      | some b => if phase b < phase a then some a else some b
    else best

private theorem maxBefore_spec (phase : Nat → Nat) (bound : Nat) (xs : List Nat) :
    match maxBefore phase bound xs with
    | none => ∀ a ∈ xs, ¬ phase a < bound
    | some b => b ∈ xs ∧ phase b < bound ∧
        ∀ a ∈ xs, phase a < bound → phase a ≤ phase b := by
  induction xs with
  | nil => simp [maxBefore]
  | cons a xs ih =>
    cases ht : maxBefore phase bound xs with
    | none =>
      rw [ht] at ih
      by_cases ha : phase a < bound
      · simp only [maxBefore, ht, ha, ↓reduceIte]
        refine ⟨by simp, trivial, ?_⟩
        intro x hx hp
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact False.elim (ih x hx hp)
      · simp only [maxBefore, ht, ha, ↓reduceIte]
        intro x hx hp
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha hp
        · exact ih x hx hp
    | some b =>
      rw [ht] at ih
      obtain ⟨hb, hpb, hmax⟩ := ih
      by_cases ha : phase a < bound
      · by_cases hba : phase b < phase a
        · simp only [maxBefore, ht, ha, hba, ↓reduceIte]
          refine ⟨by simp, trivial, ?_⟩
          intro x hx hp
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Nat.le_refl _
          · exact Nat.le_trans (hmax x hx hp) (Nat.le_of_lt hba)
        · simp only [maxBefore, ht, ha, hba, ↓reduceIte]
          refine ⟨List.mem_cons_of_mem _ hb, hpb, ?_⟩
          intro x hx hp
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · exact hmax x hx hp
      · simp only [maxBefore, ht, ha, ↓reduceIte]
        refine ⟨List.mem_cons_of_mem _ hb, hpb, ?_⟩
        intro x hx hp
        rcases List.mem_cons.mp hx with rfl | hx
        · exact False.elim (ha hp)
        · exact hmax x hx hp

private theorem writesAt_write (P : Shape) (r a : Nat) (ha : a ∈ P.static.writesAt r) :
    (P.nodes.getD a default).ev.isWrite = true :=
  (List.mem_filter.mp (List.mem_filter.mp ha).1).2

private theorem write_read_phase_ne (P : Shape) (c : PhaseLayout) (hs : c.Separated P)
    (r a : Nat) (hr : r ∈ P.static.reads)
    (hplain : (P.nodes.getD r default).ev.isWrite = false) (ha : a ∈ P.static.writesAt r) :
    c.phase r ≠ c.phase a := by
  have hwrite := writesAt_write P r a ha
  have hne : r ≠ a := by
    intro he
    subst a
    exact Bool.noConfusion (hplain.symm.trans hwrite)
  exact hs r (read_mem P r hr) a (write_mem P a (List.mem_filter.mp ha).1) hne
    (List.mem_filter.mp ha).2 (by simp only [hwrite, Bool.or_true])

/-- Phase separation makes the maximal preceding write a valid reaching definition;
there is no additional per-read certificate to assume or run. -/
theorem maxBefore_latest (P : Shape) (c : PhaseLayout) (hs : c.Separated P)
    (r last : Nat) (hr : r ∈ P.static.reads)
    (hplain : (P.nodes.getD r default).ev.isWrite = false)
    (hsel : maxBefore c.phase (c.phase r) (P.static.writesAt r) = some last) :
    c.latest P r last = true := by
  have hspec := maxBefore_spec c.phase (c.phase r) (P.static.writesAt r)
  rw [hsel] at hspec
  obtain ⟨hl, hbefore, hmax⟩ := hspec
  simp only [PhaseLayout.latest, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨hr, hl⟩, hbefore⟩, ?_⟩
  intro a ha
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases heq : a = last
  · exact Or.inl (Or.inl heq)
  · by_cases hab : c.phase a < c.phase r
    · have hle := hmax a ha hab
      have ham := write_mem P a (List.mem_filter.mp ha).1
      have hlm := write_mem P last (List.mem_filter.mp hl).1
      have hal : P.static.sameLoc a last = true := sameLoc_trans _ _ _
        (sameLoc_symm _ _ (List.mem_filter.mp ha).2) (List.mem_filter.mp hl).2
      have hwrite := writesAt_write P r a ha
      have hne := hs a ham last hlm heq hal (by simp only [hwrite, Bool.true_or])
      exact Or.inl (Or.inr (by omega))
    · have hne := write_read_phase_ne P c hs r a hr hplain ha
      exact Or.inr (by omega)

/-- The unique reads-from choice in every closed, consistent execution. Pure reads with no
preceding write read the initial zero; all other pure reads use the greatest prior writer phase. -/
theorem phase_reads_source (P : Shape) (c : PhaseLayout) (w : List Nat) (r : Nat)
    (hg : c.geometry P = true) (hs : c.Separated P)
    (hex : P.external = []) (hw : Wf w P.spec) (hc : P.consistent w = true)
    (hr : r ∈ P.static.reads) (hplain : (P.nodes.getD r default).ev.isWrite = false) :
    P.static.rf w r = match maxBefore c.phase (c.phase r) (P.static.writesAt r) with
      | none => .init
      | some last => .internal last := by
  have hv := wf_sourceValid P w r hex hw hr
  cases hsel : maxBefore c.phase (c.phase r) (P.static.writesAt r) with
  | some last =>
    exact consistent_reads_latest P.static w r last hc hv
      (phase_latestWrite P c hg r last (maxBefore_latest P c hs r last hr hplain hsel))
  | none =>
    have hnone := maxBefore_spec c.phase (c.phase r) (P.static.writesAt r)
    rw [hsel] at hnone
    cases hf : P.static.rf w r with
    | init => rfl
    | external v => simp [sourceValid, hf] at hv
    | internal a =>
      have ha : a ∈ P.static.writesAt r := by
        have hh : (P.static.writesAt r).contains a = true ∧ a ≠ r := by
          simpa [sourceValid, hf, Bool.and_eq_true] using hv
        exact List.contains_iff_mem.mp hh.1
      have hne := write_read_phase_ne P c hs r a hr hplain ha
      have hna := hnone a ha
      have hfuture : c.phase r < c.phase a := by omega
      have hra := phase_locord P c hg r a (read_mem P r hr)
        (write_mem P a (List.mem_filter.mp ha).1) hfuture (List.mem_filter.mp ha).2
      have ho₁ := consistent_locord P.static w hc hra
      have ho₂ := consistent_rf P.static w hc hr hf
      omega

/-- A sequential read at a phase boundary, including the initial-memory case. -/
def phaseReadValue (P : Shape) (c : PhaseLayout) (w : List Nat) (r : Nat) : Nat :=
  match maxBefore c.phase (c.phase r) (P.static.writesAt r) with
  | none => 0
  | some last => P.static.valueOfWrite w P.nodes.length last

/-- Every G4-consistent execution of a phase-disciplined kernel has the sequential read values.
No sequential behavior or per-read latest-write certificate is a hypothesis. -/
theorem phase_read_sequential (P : Shape) (c : PhaseLayout) (w : List Nat) (r : Nat)
    (hg : c.geometry P = true) (hs : c.Separated P)
    (hex : P.external = []) (hw : Wf w P.spec) (hc : P.consistent w = true)
    (hr : r ∈ P.static.reads) (hplain : (P.nodes.getD r default).ev.isWrite = false) :
    P.static.valueOfRead w r = phaseReadValue P c w r := by
  unfold Static.valueOfRead phaseReadValue
  rw [phase_reads_source P c w r hg hs hex hw hc hr hplain]
  cases maxBefore c.phase (c.phase r) (P.static.writesAt r) <;> rfl

/-! ## Transfer checked protocols back to arbitrary source values -/

@[simp] theorem eraseShape_mems (P : Shape) : (eraseShape P).static.mems = P.static.mems := by
  simp only [Shape.static, eraseNodes, List.length_map, eraseNode_getD, eraseNode, eraseValue_loc]

@[simp] theorem eraseShape_reads (P : Shape) : (eraseShape P).static.reads = P.static.reads := by
  simp only [Shape.static, eraseNodes, List.length_map, eraseNode_getD, eraseNode, eraseValue_read]

@[simp] theorem eraseShape_writes (P : Shape) : (eraseShape P).static.writes = P.static.writes := by
  simp only [Shape.static, eraseNodes, List.length_map, eraseNode_getD, eraseNode, eraseValue_write]

@[simp] theorem eraseShape_writesAt (P : Shape) (r : Nat) :
    (eraseShape P).static.writesAt r = P.static.writesAt r := by
  simp only [Static.writesAt, eraseShape_writes, Shape.static, eraseNodes,
    eraseNode_getD, eraseNode, Node.sameLoc, eraseValue_loc, eraseValue_write, List.length_map]

theorem geometry_erase (P : Shape) (c : PhaseLayout) :
    c.geometry (eraseShape P) = c.geometry P := by
  simp only [PhaseLayout.geometry, boundary, eraseNodes, List.length_map,
    eraseNode_getD, eraseNode, eraseValue_loc, eraseValue_barrier]

theorem separated_erase (P : Shape) (c : PhaseLayout) :
    c.Separated (eraseShape P) ↔ c.Separated P := by
  simp only [PhaseLayout.Separated, eraseShape_mems, Static.sameLoc, Shape.static,
    eraseNodes, eraseNode_getD, eraseNode, Node.sameLoc, eraseValue_loc, eraseValue_write,
    List.length_map]

theorem latest_erase (P : Shape) (c : PhaseLayout) (r last : Nat) :
    c.latest (eraseShape P) r last = c.latest P r last := by
  simp only [PhaseLayout.latest, eraseShape_reads, eraseShape_writesAt]

/-- The actual source trace is race-free for every input memory once its arithmetic-free access
protocol passes the structural geometry and unique-access certificate. -/
theorem sourceTrace_not_racy (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) (c : PhaseLayout)
    (hg : c.geometryFast (sourceProtocolTrace p d group width) = true)
    (hs : c.Separated (sourceProtocolTrace p d group width)) :
    (sourceTrace p d mem group width).static.racy = false := by
  apply phase_discipline_not_racy _ c
  · rw [← geometry_erase, sourceTrace_erase, ← geometryFast_eq]
    exact hg
  · apply (separated_erase _ c).mp
    rw [sourceTrace_erase]
    exact hs

/-- In particular, shared reads whose reaching writes are checked by source stage numbers see
those writes in every G4-consistent execution. Initial global/constant loads remain the dispatch
boundary inputs; G4's zero-initial-value litmus model does not assign their host-provided values. -/
theorem sourceTrace_read_value (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) (c : PhaseLayout) (w : List Nat) (r last : Nat)
    (hg : c.geometryFast (sourceProtocolTrace p d group width) = true)
    (hl : c.latest (sourceProtocolTrace p d group width) r last = true)
    (hw : Wf w (sourceTrace p d mem group width).spec)
    (hc : (sourceTrace p d mem group width).consistent w = true) :
    (sourceTrace p d mem group width).static.valueOfRead w r =
      (sourceTrace p d mem group width).static.valueOfWrite w
        (sourceTrace p d mem group width).nodes.length last := by
  apply phase_read_value _ c w r last
  · rw [← geometry_erase, sourceTrace_erase, ← geometryFast_eq]
    exact hg
  · rw [← latest_erase, sourceTrace_erase]
    exact hl
  · rfl
  · exact hw
  · exact hc

/-- The certified value-erased source protocol gives sequential read visibility in the real
source trace for every input memory; the only execution premises are G4's own well-formedness and
consistency. The initial-value clause is G4's zero initialization, so host-provided input values
are still boundary parameters rather than a claim about host events. -/
theorem sourceTrace_read_sequential (p : Obend.Hardware.ArrayKernel.Program)
    (d : Obend.Hardware.ArrayKernel.Dispatch) (mem : Obend.Hardware.ArrayKernel.Memory)
    (group width : Nat) (c : PhaseLayout) (w : List Nat) (r : Nat)
    (hg : c.geometryFast (sourceProtocolTrace p d group width) = true)
    (hs : c.Separated (sourceProtocolTrace p d group width))
    (hw : Wf w (sourceTrace p d mem group width).spec)
    (hc : (sourceTrace p d mem group width).consistent w = true)
    (hr : r ∈ (sourceTrace p d mem group width).static.reads)
    (hplain : ((sourceTrace p d mem group width).nodes.getD r default).ev.isWrite = false) :
    (sourceTrace p d mem group width).static.valueOfRead w r =
      phaseReadValue (sourceTrace p d mem group width) c w r := by
  apply phase_read_sequential _ c w r
  · rw [← geometry_erase, sourceTrace_erase, ← geometryFast_eq]
    exact hg
  · apply (separated_erase _ c).mp
    rw [sourceTrace_erase]
    exact hs
  · rfl
  · exact hw
  · exact hc
  · exact hr
  · exact hplain

end Obend.Hardware.Gpu.Workgroup
