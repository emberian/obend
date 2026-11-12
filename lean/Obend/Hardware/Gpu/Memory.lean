module
/-
# Obend.Hardware.Gpu.Memory — the scoped memory model of our GPUs as a gluing condition on the scope site

Rung G4 of `review/GPU-PROGRAM-20261105.md`. The artifact is the litmus suite under `hardware/gpu/litmus/`
run on hbox's RX 6750 XT (RDNA2, Mesa RADV and AMDVLK), on hbox's UHD 770 (Mesa ANV) and on the Mac's
M2 Max (Metal); the theorem is `allowed_iff_glues`; the gate is `hardware/gpu/verify_litmus.sh`.

## The referent

The model here is not reasoned out alone. Its referent is the Vulkan memory model as an executable
formal artifact: Khronos's Alloy formalization (`github.com/KhronosGroup/Vulkan-MemoryModel`,
`alloy/spirv.als`) and its translation to cat in Dartagnan (`github.com/hernanponcedeleon/Dat3M`,
`cat/vulkan.cat` including `vulkan-common.cat`; Ponce de León, Hernán et al., "Towards Unified
Analysis of GPU Consistency", ASPLOS 2024). WGSL maps onto it by its specification (§14.5 Memory Model,
w3.org/TR/WGSL): a WGSL read or write is a Vulkan memory operation; atomic built-ins are Relaxed with
memory scope Workgroup in the `workgroup` address space and QueueFamily in the `storage` address space;
`storageBarrier()` and `workgroupBarrier()` are control barriers with execution and memory scope
Workgroup, AcquireRelease ordering and the memory semantics of the `storage` (UniformMemory, SPIR-V
storage class 0 below) resp. `workgroup` (WorkgroupMemory, class 1) address space; non-atomic accesses to
either space are non-private with MakeAvailable/MakeVisible at Workgroup scope; no built-in uses
MakeAvailable or MakeVisible semantics. The checker `allowed` must agree with Dartagnan's verdict under
`vulkan.cat` on every litmus shape of the suite: `obend-litmus-check` writes each shape and outcome as a
Dartagnan `.litmus` file (`hardware/gpu/litmus/dartagnan/`) and the gate compares the verdicts; a
disagreement is a defect here until shown otherwise. NVIDIA's own PTX model
(`github.com/NVlabs/ptxmemorymodel`, Alloy and Coq) and GPUMC (Chakraborty et al., CAV 2025,
arXiv 2505.20207) are the neighbouring formalizations; neither is a referent for WGSL.

## The specialization, derived

`vulkan-common.cat` is consistent when `locord ∪ rf ∪ fr ∪ asmo` is acyclic, read-modify-writes are
atomic, non-atomic reads do not read a shadowed write, and mutually ordered atomic writes are totally
ordered by `asmo`. Our events are the ones WGSL emits for the litmus kernels, and for those the general
relations collapse:

* `inscope`: atomics in `storage` have QueueFamily scope and WebGPU submits every dispatch to one
  queue, so any two of them are in scope; atomics in `workgroup` memory have Workgroup scope and only
  threads of one workgroup can name that memory, so any two of them are in scope too. Hence
  `mutordatom` is "both atomic, same location", `asmo` is the coherence order on atomic writes.
* `sw`: WGSL has no acquire or release atomics and no fences other than the barriers, so the only case
  of `sw` is `[REL&F]; po?; [CBAR]; (syncbar & inscope \ id); [CBAR]; po?; [ACQ&F]` with the barrier
  its own fence: two barriers of the same dynamic instance in the same workgroup synchronize.
* `hb = po ∪ ⋃_T ithb_T`, `ithb_T` the transitive closure over the three edge kinds of
  `ithb(SC_T, SEMSC_T)` for a nonempty set `T` of address spaces: barrier to barrier through `sw` when
  both carry the semantics of `T`; an access in a space of `T` (or such a barrier) program-ordered before
  such a barrier; such a barrier program-ordered before an access in a space of `T` (or such a barrier).
  A `storageBarrier` orders no access to `workgroup` memory and a `workgroupBarrier` none to `storage`.
  Since `sw` relates only barriers of one workgroup, `hb` never crosses a workgroup.
* `locord`: every access here is non-private, every atomic write is in `AV` and every atomic read in
  `VIS` at its scope (`(W&A) in AV`, `(R&A) in VIS` in the Alloy), and every non-atomic access carries
  Workgroup-scope availability or visibility by the WGSL specification. So every write is in `AVWG` and
  every read in `VISWG`, and with `chains = id` (`vulkan.cat`, no availability chains) the write-first
  cases of `locord` through the workgroup instance domain are `[W]; (hb & swg); [W]` and
  `[W]; (hb & swg); [R]`; the read-first case is `[R]; hb; [R|W]`; the same-thread case is `hb & int`.
  As `hb` is within a workgroup, all of them are `hb`, and `locord = loc ∩ hb`.
* `fr = rf⁻¹;((W×W) ∩ locord) ∪ rf⁻¹;asmo ∪ {(r, w) | r reads the initial value, w a write to its
  location}`; `atomic`: no `rmw` whose read is `fr`-before a write of another thread that is
  `asmo`-before the rmw's own write; `consistency-rf`: no non-atomic read reads a write `w` with
  `w locord w' locord⁺ r` through writes `w'`. A read-modify-write is one event here (`Ev.rmw`), both a
  read and a write, where the cat has two related by `rmw`; so an `fr` edge out of it and an `asmo` edge
  into it already form a cycle and `atomic` follows from the acyclicity (the same-thread cases the cat's
  `ext` leaves out are cycles through `locord` either way). The clause is kept as the cat states it; it is
  not a separate axiom to plant.

This file carries exactly those definitions (`hb`, `locord`, `fr`, `asmo`, the four constraints), over
events `Ev` and shapes `Shape`. The `racy` flag of the cat (`dr`) is computed by `racy` and reported,
never part of `consistent`, as in the cat.

## The site, the presheaf, the gluing

The places of a shape are its threads; the scope objects are `Obj`: a thread, a workgroup, the device.
`Obj.le` is inclusion, `cover` the canonical covering families (a workgroup by its threads, the device
by its workgroups, a thread by itself); `cover_le` and `cover_stable` are the axioms of a coverage in
Johnstone's sense (Sketches of an Elephant C2.1.1): a cover of `U` pulled back along `V ≤ U` is refined
by a cover of `V`. `Obs P U` is what the harness can record at `U`: the histories of the threads of `U`
(events with the values their reads returned), and `restrictObs` is projection; it is a presheaf
(`restrictObs_comp`) and trivially a sheaf.

A section of the model over `U` is a witness `w : List Nat` for the shape restricted to `U`
(`Shape.restrict`): for each read a reads-from choice (the initial value, a write of `U`, or the value
of a write outside `U`, which the restricted shape remembers as `external`), for each write its rank in
the coherence order of its location, and for each memory event its position in a total order that every
edge of `locord ∪ rf ∪ fr ∪ asmo` respects, which is the acyclicity of the cat witnessed rather than
searched for. `consistent P w` checks the constraints above against that data. Reads from outside `U`
contribute no `fr` edge: `U` does not see where the outside write sits in coherence order, so a section
over a workgroup is exactly what that workgroup's threads can account for by themselves. At a single
thread the constraints reduce to its own coherence (a read after a write of the same location in program
order cannot return the initial value); at a workgroup they add the barriers; at the device they add the
coherence order between workgroups. The model is the gluing question at the device: an observed outcome
is allowed when the family of thread histories it records is the restriction of a section over the
device. `allowed_iff_glues` says that the decidable checker `allowed` answers exactly that question: it
enumerates every witness of the finite shape (`spec`, `sequence`) and `allowed P o = true` iff some
witness is well-formed, consistent and observes `o`. A weak behaviour forbidden by the model is a
witnessed non-gluing, Abramsky and Brandenburger's contextuality with scopes as contexts; a weak
behaviour allowed by the model is one that glues although no sequential order explains it.

## What is proved and what is a checked table

Proved: `allowed_iff_glues` (the checker is the gluing question, for every shape and outcome, by the
completeness of the enumeration `mem_sequence`); `cover_le`, `cover_stable` (the coverage); `le_refl`,
`le_trans`; `restrictObs_comp` (the observation presheaf); `hb_restrict_mono`, `locord_restrict_mono`,
`rfEdges_restrict_mono`, `asmoEdges_restrict_mono`, `frEdges_restrict_mono`,
`consistent_restrictWitness`, `Section.restrict`, and `restrictWitness_comp` (the section presheaf
restricts along `Obj.le`: monotonicity of the restricted relations carries consistent witnesses and
well-formed sections from `U` to `V ≤ U`, functorially along `W ≤ V ≤ U`; `obend-litmus-check restrict`
exercises the same restriction across the suite's shapes). Checked, not proved: that `consistent` agrees
with Dartagnan under `vulkan.cat` on the suite's shapes and outcomes, a table the gate regenerates; that
the devices never show a forbidden outcome and show (or are recorded stronger than) the allowed weak
ones, the tables under `hardware/gpu/litmus/results/`.

## Departures from the devices, named

The devices are stronger than the model where the result tables say so: an allowed weak outcome that no
device showed at GPUHarbor's deployed stress budget is recorded in `results/STRONGER.tsv` with the
device, not claimed forbidden. The model has no subgroup scope (WGSL subgroup built-ins are not used),
no queue-family distinction from the device (one queue), no availability chains (`vulkan.cat`, not
`vulkan-chains.cat`; RADV, AMDVLK, ANV and Metal through wgpu expose none to WGSL), and no host events:
the final value of a location is the last write in its coherence order, which is what the result kernel
of a later dispatch reads. Values are natural numbers; the kernels store 1 and 2.
-/
@[expose] public section

namespace Obend.Hardware.Gpu.Memory
set_option autoImplicit false

/-! ## 1. Events and shapes -/

/-- WGSL address spaces, SPIR-V storage classes 0 and 1 of the cat (`SC0`, `SC1`). -/
inductive Space where
  | storage
  | workgroup
  deriving DecidableEq, Repr, Inhabited

/-- A location: an address space and an index. -/
structure Loc where
  space : Space
  idx : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What a read-modify-write writes, as a function of what it read. -/
inductive RmwOp where
  /-- `atomicExchange(p, v)`. -/
  | exchange (v : Nat)
  /-- `atomicAdd(p, v)`. -/
  | add (v : Nat)
  deriving DecidableEq, Repr

def RmwOp.apply : RmwOp → Nat → Nat
  | .exchange v, _ => v
  | .add v, x => x + v

/-- One event of a thread's straight-line program. -/
inductive Ev where
  /-- `atomicStore` (atomic) or a plain assignment. -/
  | write (loc : Loc) (val : Nat) (atomic : Bool)
  /-- `atomicLoad` (atomic) or a plain load. -/
  | read (loc : Loc) (atomic : Bool)
  /-- An atomic read-modify-write: one event that is both a read and a write (`RMW` of the cat). -/
  | rmw (loc : Loc) (op : RmwOp)
  /-- A control barrier of dynamic instance `inst` at Workgroup execution and memory scope with
  AcquireRelease ordering and the memory semantics of the spaces `sems`: `storageBarrier()` is
  `[.storage]`, `workgroupBarrier()` is `[.workgroup]`. -/
  | barrier (inst : Nat) (sems : List Space)
  deriving DecidableEq, Repr, Inhabited

structure Thread where
  /-- A label kept under restriction, so event identities survive `Shape.restrict`. -/
  id : Nat
  wg : Nat
  prog : List Ev
  deriving DecidableEq, Repr

/-- A litmus shape: threads, and the writes of threads outside this shape when it is the restriction of
a larger one (`external`: a location and the value written). -/
structure Shape where
  threads : List Thread
  external : List (Loc × Nat) := []
  deriving DecidableEq, Repr

/-- An event's identity: the thread label and the position in its program. -/
structure EvId where
  t : Nat
  i : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Static structure: the events of a shape, program order, synchronization, happens-before -/

/-- One event with its identity and workgroup. -/
structure Node where
  id : EvId
  wg : Nat
  ev : Ev
  deriving DecidableEq, Repr, Inhabited

def Thread.nodes (th : Thread) : List Node :=
  (List.range th.prog.length).map fun i => { id := ⟨th.id, i⟩, wg := th.wg, ev := th.prog.getD i (.barrier 0 []) }

/-- Every event of the shape, thread by thread, in program order; the event index is the position. -/
def Shape.nodes (P : Shape) : List Node := P.threads.flatMap Thread.nodes

def Ev.loc? : Ev → Option Loc
  | .write l _ _ => some l
  | .read l _ => some l
  | .rmw l _ => some l
  | .barrier _ _ => none

def Ev.isWrite : Ev → Bool
  | .write .. => true
  | .rmw .. => true
  | _ => false

def Ev.isRead : Ev → Bool
  | .read .. => true
  | .rmw .. => true
  | _ => false

def Ev.isRmw : Ev → Bool
  | .rmw .. => true
  | _ => false

def Ev.isAtomic : Ev → Bool
  | .write _ _ a => a
  | .read _ a => a
  | .rmw .. => true
  | .barrier .. => false

def Ev.isBarrier : Ev → Bool
  | .barrier .. => true
  | _ => false

/-- A relation on event indices as an edge list. -/
abbrev Rel := List (Nat × Nat)

def Rel.has (r : Rel) (a b : Nat) : Bool := r.contains (a, b)

/-- All pairs `(a, b)` of indices below `n` with `p a b`. -/
def pairs (n : Nat) (p : Nat → Nat → Bool) : Rel :=
  (List.range n).flatMap fun a => (List.range n).filterMap fun b => if p a b then some (a, b) else none

/-- One round of `r ∪ r;r`. -/
def Rel.step (r : Rel) : Rel :=
  r ++ (r.flatMap fun (a, b) => r.filterMap fun (b', c) => if b = b' && !r.has a c then some (a, c) else none)

/-- The transitive closure, by `n` rounds (enough for paths over `n` events). -/
def Rel.closure (r : Rel) : Nat → Rel
  | 0 => r
  | n + 1 => (r.step).closure n

/-- `po`: same thread, earlier position. -/
def po (ns : List Node) : Rel :=
  pairs ns.length fun a b =>
    let x := ns.getD a default
    let y := ns.getD b default
    x.id.t == y.id.t && x.id.i < y.id.i

/-- A barrier carrying the semantics of every space in `T`. -/
def Ev.hasSems (e : Ev) (T : List Space) : Bool :=
  match e with
  | .barrier _ sems => T.all (sems.contains ·)
  | _ => false

/-- An access in a space of `T`. -/
def Ev.inSpaces (e : Ev) (T : List Space) : Bool :=
  match e.loc? with
  | some l => T.contains l.space
  | none => false

/-- `sw` specialized: two barriers of the same instance in the same workgroup. -/
def sw (ns : List Node) : Rel :=
  pairs ns.length fun a b =>
    let x := ns.getD a default
    let y := ns.getD b default
    a != b && x.wg == y.wg &&
    (match x.ev, y.ev with
      | .barrier i _, .barrier j _ => i == j
      | _, _ => false)

/-- `ithb(SC_T, SEMSC_T)`: the closure of the three edge kinds, templated by a set of spaces `T`. -/
def ithb (ns : List Node) (T : List Space) : Rel :=
  let p := po ns
  let s := sw ns
  let n := ns.length
  let evOf := fun a => (ns.getD a default).ev
  let sem := fun a => (evOf a).hasSems T
  let sc := fun a => (evOf a).inSpaces T
  let edges := pairs n fun a b =>
    (sem a && sem b && s.has a b) ||
    ((sc a || sem a) && p.has a b && sem b) ||
    (sem a && p.has a b && (sc b || sem b))
  edges.closure n

/-- `hb = po ∪ ithb_{storage} ∪ ithb_{workgroup} ∪ ithb_{storage, workgroup}`. -/
def hb (ns : List Node) : Rel :=
  po ns ++ ithb ns [.storage] ++ ithb ns [.workgroup] ++ ithb ns [.storage, .workgroup]

def Node.sameLoc (x y : Node) : Bool :=
  match x.ev.loc?, y.ev.loc? with
  | some l, some m => l == m
  | _, _ => false

/-- `locord = loc ∩ hb` (derived in the header). -/
def locord (ns : List Node) : Rel :=
  let h := hb ns
  pairs ns.length fun a b => (ns.getD a default).sameLoc (ns.getD b default) && h.has a b

/-- The static part of the model: what the witness search does not change. -/
structure Static where
  nodes : List Node
  hb : Rel
  locord : Rel
  /-- Indices of the reads (reads and rmws), in order: the reads-from slots. -/
  reads : List Nat
  /-- Indices of the writes (writes and rmws), in order: the rank slots. -/
  writes : List Nat
  /-- Indices of the memory events, in order: the order slots. -/
  mems : List Nat
  external : List (Loc × Nat)

def Shape.static (P : Shape) : Static :=
  let ns := P.nodes
  let idx := List.range ns.length
  { nodes := ns
    hb := hb ns
    locord := locord ns
    reads := idx.filter fun a => (ns.getD a default).ev.isRead
    writes := idx.filter fun a => (ns.getD a default).ev.isWrite
    mems := idx.filter fun a => (ns.getD a default).ev.loc?.isSome
    external := P.external }

/-! ## 3. Witnesses: reads-from, coherence ranks, a total order -/

/-- The writes of `s` at the location of event `a`, in index order. -/
def Static.writesAt (s : Static) (a : Nat) : List Nat :=
  s.writes.filter fun w => (s.nodes.getD a default).sameLoc (s.nodes.getD w default)

/-- The external writes at the location of event `a`: positions in `s.external`. -/
def Static.externalAt (s : Static) (a : Nat) : List Nat :=
  (List.range s.external.length).filter fun j =>
    match (s.nodes.getD a default).ev.loc?, s.external.getD j default with
    | some l, (m, _) => l == m
    | none, _ => false

/-- The candidate values of every slot: for a read, `0` (the initial value), `w + 1` for a write `w` of
the shape at its location other than itself, `nodes.length + 1 + j` for the `j`-th external write at
its location; for a write, a rank below the number of writes at its location; for a memory event, a
position below the number of memory events. -/
def Static.spec (s : Static) : List (List Nat) :=
  (s.reads.map fun r =>
    0 :: ((s.writesAt r).filter (· != r)).map (· + 1) ++ (s.externalAt r).map (s.nodes.length + 1 + ·)) ++
  (s.writes.map fun w => List.range (s.writesAt w).length) ++
  (s.mems.map fun _ => List.range s.mems.length)

/-- Where a read reads from. -/
inductive Src where
  | init
  | internal (w : Nat)
  | external (v : Nat)
  deriving DecidableEq, Repr

/-- The position of `a` in `l`, or `l.length`. -/
def posOf (l : List Nat) (a : Nat) : Nat :=
  match l.findIdx? (· == a) with
  | some i => i
  | none => l.length

def Static.rf (s : Static) (w : List Nat) (r : Nat) : Src :=
  let k := w.getD (posOf s.reads r) 0
  if k = 0 then .init
  else if k ≤ s.nodes.length then .internal (k - 1)
  else .external ((s.external.getD (k - s.nodes.length - 1) default).2)

def Static.rank (s : Static) (w : List Nat) (a : Nat) : Nat :=
  w.getD (s.reads.length + posOf s.writes a) 0

def Static.ord (s : Static) (w : List Nat) (a : Nat) : Nat :=
  w.getD (s.reads.length + s.writes.length + posOf s.mems a) 0

/-- The value a write stores: a plain write's constant, an rmw's function of what it read, through the
reads-from choices, with fuel for the (inconsistent) cyclic case. -/
def Static.valueOfWrite (s : Static) (w : List Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, a =>
    match (s.nodes.getD a default).ev with
    | .write _ v _ => v
    | .rmw _ op =>
      op.apply (match s.rf w a with
        | .init => 0
        | .internal b => s.valueOfWrite w fuel b
        | .external v => v)
    | _ => 0

/-- The value a read returns. -/
def Static.valueOfRead (s : Static) (w : List Nat) (r : Nat) : Nat :=
  match s.rf w r with
  | .init => 0
  | .internal a => s.valueOfWrite w s.nodes.length a
  | .external v => v

/-! ## 4. The dynamic relations and the constraints of the cat -/

def Static.atomicAt (s : Static) (a : Nat) : Bool := (s.nodes.getD a default).ev.isAtomic
def Static.threadOf (s : Static) (a : Nat) : Nat := (s.nodes.getD a default).id.t
def Static.sameLoc (s : Static) (a b : Nat) : Bool := (s.nodes.getD a default).sameLoc (s.nodes.getD b default)

/-- `asmo`: both atomic writes at one location, ranked in order. -/
def Static.asmo (s : Static) (w : List Nat) (a b : Nat) : Bool :=
  a != b && s.atomicAt a && s.atomicAt b && s.sameLoc a b && s.rank w a < s.rank w b

/-- `co`: the coherence order of all writes at one location. -/
def Static.co (s : Static) (w : List Nat) (a b : Nat) : Bool :=
  a != b && s.sameLoc a b && s.rank w a < s.rank w b

def Static.rfEdges (s : Static) (w : List Nat) : Rel :=
  s.reads.filterMap fun r =>
    match s.rf w r with
    | .internal a => some (a, r)
    | _ => none

/-- `fr`, from `asmo` and `locord`, with init-reads before every write at their location; a read from an
external write contributes nothing (the restricted shape does not know its coherence position). -/
def Static.frEdges (s : Static) (w : List Nat) : Rel :=
  s.reads.flatMap fun r =>
    (s.writesAt r).filterMap fun w' =>
      if w' = r then none else
      match s.rf w r with
      | .init => some (r, w')
      | .internal a =>
        if a != w' && (s.asmo w a w' || s.locord.has a w') then some (r, w') else none
      | .external _ => none

def Static.asmoEdges (s : Static) (w : List Nat) : Rel :=
  s.writes.flatMap fun a => s.writes.filterMap fun b => if s.asmo w a b then some (a, b) else none

/-- The axiom switches: all on is the model; a planted fault turns one off or adds sequential order. -/
structure Axioms where
  coherence : Bool := true
  barrierSync : Bool := true
  sequential : Bool := false
  deriving Repr

/-- The constraints of `vulkan-common.cat` on a witness: ranks total per location, the order total
over memory events and respecting every edge of `locord ∪ rf ∪ fr ∪ asmo` (acyclicity), `atomic`,
`consistency-rf`. -/
def Static.consistentWith (ax : Axioms) (s : Static) (w : List Nat) : Bool :=
  let locord := if ax.barrierSync then s.locord else
    pairs s.nodes.length fun a b => s.sameLoc a b && (po s.nodes).has a b
  let asmoE := if ax.coherence then s.asmoEdges w else []
  let frE := if ax.coherence then s.frEdges w else
    s.reads.flatMap fun r => (s.writesAt r).filterMap fun w' =>
      if w' = r then none else
      match s.rf w r with
      | .init => some (r, w')
      | .internal a => if a != w' && locord.has a w' then some (r, w') else none
      | .external _ => none
  let poE := if ax.sequential then
    (pairs s.nodes.length fun a b => (po s.nodes).has a b && (s.nodes.getD a default).ev.loc?.isSome
      && (s.nodes.getD b default).ev.loc?.isSome) else []
  let edges := locord ++ s.rfEdges w ++ frE ++ asmoE ++ poE
  -- ranks injective per location over the writes
  (s.writes.all fun a => s.writes.all fun b => a == b || !s.sameLoc a b || s.rank w a != s.rank w b) &&
  -- the order injective over memory events
  (s.mems.all fun a => s.mems.all fun b => a == b || s.ord w a != s.ord w b) &&
  -- every edge goes up
  (edges.all fun (a, b) => s.ord w a < s.ord w b) &&
  -- atomic: no rmw whose read is fr-before a write of another thread asmo-before its own write
  (s.reads.all fun r =>
    !(s.nodes.getD r default).ev.isRmw ||
    (s.writesAt r).all fun w' =>
      s.threadOf w' == s.threadOf r || !(frE.has r w' && s.asmo w w' r)) &&
  -- consistency-rf: a non-atomic read does not read a write shadowed through writes
  (s.reads.all fun r =>
    s.atomicAt r ||
    match s.rf w r with
    | .internal a =>
      let wl : Rel := locord.filter fun (x, _) => (s.nodes.getD x default).ev.isWrite
      let wlc : Rel := Rel.closure wl s.nodes.length
      let wl2 : Rel := wl.flatMap fun (x, y) => wlc.filterMap fun (y', z) =>
        if y = y' then some (x, z) else none
      !Rel.has wl2 a r
    | _ => true)

def Static.consistent (s : Static) (w : List Nat) : Bool := s.consistentWith {} w

/-- `dr` of the cat: same location, not both reads, not mutually ordered atomics, not `locord` either
way. A flag, reported beside the verdict. -/
def Static.racy (s : Static) : Bool :=
  s.mems.any fun a => s.mems.any fun b =>
    a != b && s.sameLoc a b && ((s.nodes.getD a default).ev.isWrite || (s.nodes.getD b default).ev.isWrite) &&
    !(s.atomicAt a && s.atomicAt b) && !s.locord.has a b && !s.locord.has b a

/-! ## 5. Observations: the histories of threads and the final values -/

/-- A thread's history: its events, each with the value it returned if it was a read. -/
abbrev History := List (Ev × Option Nat)

def Static.history (s : Static) (w : List Nat) (t : Nat) : History :=
  (List.range s.nodes.length).filterMap fun a =>
    let n := s.nodes.getD a default
    if n.id.t = t then some (n.ev, if n.ev.isRead then some (s.valueOfRead w a) else none)
    else none

/-- The final value of a location: the write of greatest rank (`co`), or the initial value `0`. -/
def Static.final (s : Static) (w : List Nat) (l : Loc) : Nat :=
  let ws := s.writes.filter fun a => (s.nodes.getD a default).ev.loc? == some l
  match ws.foldl (fun (best : Option Nat) a =>
      match best with
      | none => some a
      | some b => if s.rank w a > s.rank w b then some a else some b) none with
  | some a => s.valueOfWrite w s.nodes.length a
  | none => 0

/-- The locations a shape names, in order of first appearance. -/
def Shape.locs (P : Shape) : List Loc :=
  (P.nodes.filterMap fun n => n.ev.loc?).foldl (fun acc l => if acc.contains l then acc else acc ++ [l]) []

/-- The locations every write of which is atomic: there the final value is the last write in `asmo`,
which is what a later dispatch's `atomicLoad` returns. For a location with non-atomic writes the cat ties
nothing to `co`, and the kernels observe such locations by an explicit read after the barrier. -/
def Shape.atomicLocs (P : Shape) : List Loc :=
  P.locs.filter fun l => P.nodes.all fun n =>
    !(n.ev.isWrite && n.ev.loc? == some l) || n.ev.isAtomic

/-- What the harness records: a history per thread (in the shape's order) and the final values of the
atomic locations (in `Shape.atomicLocs` order). -/
structure Outcome where
  histories : List History
  finals : List Nat
  deriving DecidableEq, Repr

def Static.obs (s : Static) (P : Shape) (w : List Nat) : Outcome :=
  { histories := P.threads.map fun th => s.history w th.id
    finals := P.atomicLocs.map fun l => s.final w l }

/-! ## 6. The checker -/

/-- The cartesian product of candidate lists: every well-formed witness, each exactly once. -/
def sequence : List (List Nat) → List (List Nat)
  | [] => [[]]
  | c :: cs => c.flatMap fun x => (sequence cs).map fun l => x :: l

/-- A witness is well-formed when it picks one candidate per slot. -/
inductive Wf : List Nat → List (List Nat) → Prop
  | nil : Wf [] []
  | cons {x c w cs} : x ∈ c → Wf w cs → Wf (x :: w) (c :: cs)

theorem mem_sequence (specs : List (List Nat)) (w : List Nat) : w ∈ sequence specs ↔ Wf w specs := by
  induction specs generalizing w with
  | nil =>
    simp only [sequence, List.mem_singleton]
    constructor
    · rintro rfl; exact Wf.nil
    · intro h; cases h; rfl
  | cons c cs ih =>
    simp only [sequence, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, l, hl, rfl⟩
      exact Wf.cons hx ((ih l).1 hl)
    · intro h
      cases h with
      | cons hx hw => exact ⟨_, hx, _, (ih _).2 hw, rfl⟩

def Shape.spec (P : Shape) : List (List Nat) := P.static.spec

def Shape.consistentWith (ax : Axioms) (P : Shape) (w : List Nat) : Bool := P.static.consistentWith ax w
def Shape.consistent (P : Shape) (w : List Nat) : Bool := P.static.consistent w
def Shape.obs (P : Shape) (w : List Nat) : Outcome := P.static.obs P w

/-- The checker: is `o` the observation of some well-formed consistent witness? Under `ax`, with a planted
fault for the gate's tooth. -/
def Shape.allowedWith (ax : Axioms) (P : Shape) (o : Outcome) : Bool :=
  let s := P.static
  (sequence s.spec).any fun w => s.consistentWith ax w && decide (s.obs P w = o)

def Shape.allowed (P : Shape) (o : Outcome) : Bool := P.allowedWith {} o

/-- Every outcome the enumeration can produce, each once: the table the gate reads. -/
def Shape.outcomes (P : Shape) : List Outcome :=
  let s := P.static
  (sequence s.spec).foldl (fun acc w => let o := s.obs P w; if acc.contains o then acc else acc ++ [o]) []

/-! ## 7. The site and the sections -/

/-- The scope objects of a shape. -/
inductive Obj where
  | thread (t : Nat)
  | workgroup (g : Nat)
  | device
  deriving DecidableEq, Repr

/-- The workgroup of thread `t` in `P`. -/
def Shape.wgOf (P : Shape) (t : Nat) : Option Nat :=
  (P.threads.find? fun th => th.id == t).map Thread.wg

/-- Inclusion of scope objects: a thread is below its workgroup and below the device when it is a thread
of `P`. -/
def Obj.le (P : Shape) : Obj → Obj → Bool
  | .thread t, .thread t' => t == t'
  | .thread t, .workgroup g => P.wgOf t == some g
  | .thread t, .device => (P.wgOf t).isSome
  | .workgroup g, .workgroup g' => g == g'
  | .workgroup _, .device => true
  | .device, .device => true
  | _, _ => false

theorem le_refl (P : Shape) (U : Obj) : Obj.le P U U = true := by
  cases U <;> simp [Obj.le]

theorem le_trans (P : Shape) {U V W : Obj} (h₁ : Obj.le P U V = true) (h₂ : Obj.le P V W = true) :
    Obj.le P U W = true := by
  cases U <;> cases V <;> cases W <;> simp_all [Obj.le]

/-- The canonical covers: a thread by itself, a workgroup by its threads, the device by its workgroups
(a family, listed once per thread). -/
def cover (P : Shape) : Obj → List Obj
  | .thread t => [.thread t]
  | .workgroup g => (P.threads.filter fun th => P.wgOf th.id == some g).map fun th => .thread th.id
  | .device => P.threads.map fun th => .workgroup th.wg

theorem wgOf_some {P : Shape} {t g : Nat} (h : P.wgOf t = some g) :
    ∃ th ∈ P.threads, th.id = t ∧ th.wg = g := by
  unfold Shape.wgOf at h
  cases hf : P.threads.find? (fun th => th.id == t) with
  | none => simp [hf] at h
  | some th =>
    simp [hf] at h
    exact ⟨th, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem wgOf_of_mem {P : Shape} {th : Thread} (h : th ∈ P.threads) : ∃ g, P.wgOf th.id = some g := by
  unfold Shape.wgOf
  have : (P.threads.find? (fun th' => th'.id == th.id)).isSome := by
    rw [List.find?_isSome]
    exact ⟨th, h, by simp⟩
  cases hf : P.threads.find? (fun th' => th'.id == th.id) with
  | none => simp [hf] at this
  | some th' => exact ⟨th'.wg, by simp⟩

theorem cover_le (P : Shape) (U V : Obj) (h : V ∈ cover P U) : Obj.le P V U = true := by
  cases U with
  | thread t => simp [cover] at h; subst h; simp [Obj.le]
  | workgroup g =>
    simp only [cover, List.mem_map, List.mem_filter] at h
    obtain ⟨th, ⟨_, hwg⟩, rfl⟩ := h
    simpa [Obj.le] using hwg
  | device =>
    simp only [cover, List.mem_map] at h
    obtain ⟨th, _, rfl⟩ := h
    rfl

/-- Johnstone's coverage condition: a cover of `U` pulled back along `V ≤ U` is refined by a cover of
`V`: every member of `cover P V` lies in some member of `cover P U`. -/
theorem cover_stable (P : Shape) (U V : Obj) (hVU : Obj.le P V U = true) :
    ∀ W ∈ cover P V, ∃ U' ∈ cover P U, Obj.le P W U' = true := by
  intro W hW
  cases V with
  | thread t =>
    simp only [cover, List.mem_singleton] at hW
    subst hW
    cases U with
    | thread t' =>
      simp only [Obj.le, beq_iff_eq] at hVU
      subst hVU
      exact ⟨.thread t, by simp [cover], by simp [Obj.le]⟩
    | workgroup g =>
      simp only [Obj.le, beq_iff_eq] at hVU
      obtain ⟨th, hmem, hid, hwg⟩ := wgOf_some hVU
      refine ⟨.thread th.id, ?_, by simp [Obj.le, hid]⟩
      simp only [cover, List.mem_map, List.mem_filter]
      exact ⟨th, ⟨hmem, by simp [hid, hVU]⟩, rfl⟩
    | device =>
      simp only [Obj.le] at hVU
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hVU
      obtain ⟨th, hmem, hid, hwg⟩ := wgOf_some hg
      refine ⟨.workgroup th.wg, ?_, ?_⟩
      · simp only [cover, List.mem_map]
        exact ⟨th, hmem, rfl⟩
      · simp [Obj.le, hg, hwg]
  | workgroup g =>
    simp only [cover, List.mem_map, List.mem_filter] at hW
    obtain ⟨th, ⟨hmem, hwg⟩, rfl⟩ := hW
    cases U with
    | thread _ => simp [Obj.le] at hVU
    | workgroup g' =>
      simp only [Obj.le, beq_iff_eq] at hVU
      subst hVU
      refine ⟨.thread th.id, ?_, by simp [Obj.le]⟩
      simp only [cover, List.mem_map, List.mem_filter]
      exact ⟨th, ⟨hmem, hwg⟩, rfl⟩
    | device =>
      simp only [beq_iff_eq] at hwg
      obtain ⟨th', hmem', _, hwg'⟩ := wgOf_some hwg
      refine ⟨.workgroup g, ?_, by simp [Obj.le, hwg]⟩
      simp only [cover, List.mem_map]
      exact ⟨th', hmem', by rw [hwg']⟩
  | device =>
    cases U with
    | thread _ => simp [Obj.le] at hVU
    | workgroup _ => simp [Obj.le] at hVU
    | device => exact ⟨W, hW, le_refl P W⟩

/-- The observation presheaf: the histories of the threads of `U`. -/
def Shape.obsAt (P : Shape) (U : Obj) (o : Outcome) : List (Nat × History) :=
  (P.threads.zip o.histories).filterMap fun (th, h) =>
    if Obj.le P (.thread th.id) U then some (th.id, h) else none

/-- Restriction of observations along `V ≤ U`: projection. -/
def restrictObs (P : Shape) (V : Obj) (hs : List (Nat × History)) : List (Nat × History) :=
  hs.filter fun (t, _) => Obj.le P (.thread t) V

theorem restrictObs_comp (P : Shape) (V W : Obj) (hs : List (Nat × History)) (hWV : Obj.le P W V = true) :
    restrictObs P W (restrictObs P V hs) = restrictObs P W hs := by
  simp only [restrictObs, List.filter_filter]
  congr 1
  funext ⟨t, h⟩
  by_cases hw : Obj.le P (.thread t) W = true
  · simp [hw, le_trans P hw hWV]
  · simp [hw]

/-- The values a location can hold in `P`: the initial `0`, the constants of its plain writes and
exchanges, and those plus `k` for each `atomicAdd(_, k)` (one round: the kernels add `0`). -/
def Shape.valuesAt (P : Shape) (l : Loc) : List Nat :=
  let base := 0 :: P.threads.flatMap fun th => th.prog.filterMap fun e => match e with
    | .write m v _ => if m == l then some v else none
    | .rmw m (.exchange v) => if m == l then some v else none
    | _ => none
  let adds := P.threads.flatMap fun th => th.prog.filterMap fun e => match e with
    | .rmw m (.add k) => if m == l then some k else none
    | _ => none
  base ++ adds.flatMap fun k => base.map (· + k)

/-- The shape restricted to `U`: its threads, with the writes of the others as external values. -/
def Shape.restrict (P : Shape) (U : Obj) : Shape :=
  { threads := P.threads.filter fun th => Obj.le P (.thread th.id) U
    external := P.external ++ (P.threads.filter fun th => !Obj.le P (.thread th.id) U).flatMap fun th =>
      th.prog.flatMap fun e => match e with
        | .write l v _ => [(l, v)]
        | .rmw l (.exchange v) => [(l, v)]
        | .rmw l (.add k) => (P.valuesAt l).map fun v => (l, v + k)
        | _ => [] }

/-- A section over `U`: a well-formed consistent witness of the restricted shape. -/
def Section (P : Shape) (U : Obj) (w : List Nat) : Prop :=
  Wf w (P.restrict U).spec ∧ (P.restrict U).consistent w = true

/-- The gluing question at the device: the family of thread histories (and the final values) recorded by
`o` is the observation of a section over the device. -/
def Glues (P : Shape) (o : Outcome) : Prop :=
  ∃ w, Section P .device w ∧ (P.restrict .device).obs w = o

theorem restrict_device (P : Shape) : P.restrict .device = P := by
  have h1 : P.threads.filter (fun th => Obj.le P (.thread th.id) .device) = P.threads := by
    rw [List.filter_eq_self]
    intro th hth
    obtain ⟨g, hg⟩ := wgOf_of_mem hth
    simp [Obj.le, hg]
  have h2 : P.threads.filter (fun th => !Obj.le P (.thread th.id) .device) = [] := by
    rw [List.filter_eq_nil_iff]
    intro th hth
    obtain ⟨g, hg⟩ := wgOf_of_mem hth
    simp [Obj.le, hg]
  simp only [Shape.restrict, h1, h2, List.flatMap_nil, List.append_nil]

/-- The checker is the gluing question. -/
theorem allowed_iff_glues (P : Shape) (o : Outcome) : P.allowed o = true ↔ Glues P o := by
  simp only [Shape.allowed, Shape.allowedWith, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Glues, Section, restrict_device, Shape.spec, Shape.consistent, Static.consistent, Shape.obs]
  constructor
  · rintro ⟨w, hw, hc, ho⟩
    exact ⟨w, ⟨(mem_sequence _ _).1 hw, hc⟩, ho⟩
  · rintro ⟨w, ⟨hw, hc⟩, ho⟩
    exact ⟨w, (mem_sequence _ _).2 hw, hc, ho⟩

/-! ## 8. Section restriction along `Obj.le` (the presheaf) -/

/-- Renumber `f` on `xs` by strict precedence count: the `k`-th smallest value gets `k`. -/
def Static.compress (xs : List Nat) (f : Nat → Nat) (a : Nat) : Nat :=
  (xs.filter fun b => decide (f b < f a)).length

private theorem filter_length_le_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem filter_length_lt_of_sep {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true)
    {w : α} (hw : w ∈ xs) (hp : p w = false) (hq : q w = true) :
    (xs.filter p).length < (xs.filter q).length := by
  induction xs with
  | nil => nomatch hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with rfl | hmem
    · have hle := filter_length_le_of_imp xs p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ite_false, ite_true, List.length_cons]
      omega
    · have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hmem
      have hx := h x List.mem_cons_self
      simp only [List.filter_cons]
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

private theorem filter_true_eq {α : Type} (xs : List α) :
    xs.filter (fun _ => true) = xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem compress_lt_length (xs : List Nat) (f : Nat → Nat) {a : Nat} (ha : a ∈ xs) :
    Static.compress xs f a < xs.length := by
  have hlt := filter_length_lt_of_sep xs (fun b => decide (f b < f a)) (fun _ => true)
    (fun _ _ _ => rfl) ha (decide_eq_false (Nat.lt_irrefl _)) rfl
  rw [filter_true_eq] at hlt
  exact hlt

theorem compress_lt_of_lt (xs : List Nat) (f : Nat → Nat) {a b : Nat}
    (ha : a ∈ xs) (hlt : f a < f b) :
    Static.compress xs f a < Static.compress xs f b := by
  exact filter_length_lt_of_sep xs (fun c => decide (f c < f a)) (fun c => decide (f c < f b))
    (fun c _ hc => decide_eq_true (Nat.lt_trans (of_decide_eq_true hc) hlt))
    ha (decide_eq_false (Nat.lt_irrefl _)) (decide_eq_true hlt)

theorem compress_lt_iff (xs : List Nat) (f : Nat → Nat) {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) :
    Static.compress xs f a < Static.compress xs f b ↔ f a < f b := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy (f a) (f b) with hlt | heq | hgt
    · exact hlt
    · have hc : Static.compress xs f a = Static.compress xs f b := by
        simp only [Static.compress, heq]
      omega
    · have hc := compress_lt_of_lt xs f hb hgt
      omega
  · exact compress_lt_of_lt xs f ha

theorem compress_ne_of_ne (xs : List Nat) (f : Nat → Nat) {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : f a ≠ f b) :
    Static.compress xs f a ≠ Static.compress xs f b := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := compress_lt_of_lt xs f ha hlt; omega
  · have := compress_lt_of_lt xs f hb hgt; omega

private theorem compress_congr_on (xs : List Nat) (f g : Nat → Nat) {a : Nat}
    (ha : a ∈ xs) (hfg : ∀ z ∈ xs, f z = g z) :
    Static.compress xs f a = Static.compress xs g a := by
  unfold Static.compress
  congr 1
  apply List.filter_congr
  intro z hz
  rw [hfg z hz, hfg a ha]

theorem compress_comp (zs ys : List Nat) (emb f : Nat → Nat)
    (hSub : ∀ z ∈ zs, emb z ∈ ys) {a : Nat} (ha : a ∈ zs) :
    Static.compress zs (fun z => Static.compress ys f (emb z)) a =
      Static.compress (zs.map emb) f (emb a) := by
  change (zs.filter fun b => decide (Static.compress ys f (emb b) < Static.compress ys f (emb a))).length =
    ((zs.map emb).filter fun b => decide (f b < f (emb a))).length
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro z hz
  simp only [Function.comp_apply]
  exact decide_eq_decide.mpr (compress_lt_iff ys f (hSub z hz) (hSub a ha))

/-- Indices in `xs.flatMap f` belonging to the blocks selected by `q`, in block order. -/
def filterBlocksIdx {α β : Type} (f : α → List β) (q : α → Bool) : List α → List Nat
  | [] => []
  | x :: xs =>
    let n := (f x).length
    let rest := (filterBlocksIdx f q xs).map (· + n)
    if q x then List.range n ++ rest else rest

private theorem getD_append_left {α : Type} (l₁ l₂ : List α) {i : Nat} (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right {α : Type} (l₁ l₂ : List α) {i : Nat} (d : α) (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem getD_range {n i : Nat} (hi : i < n) : (List.range n).getD i 0 = i := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem getD_map_add (l : List Nat) (n : Nat) {i : Nat} (hi : i < l.length) :
    (l.map (· + n)).getD i 0 = l.getD i 0 + n := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem getD_mem_of_lt {α : Type} (l : List α) {i : Nat} (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem filterBlocksIdx_length {α β : Type} (f : α → List β) (q : α → Bool) (xs : List α) :
    (filterBlocksIdx f q xs).length = ((xs.filter q).flatMap f).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterBlocksIdx, List.filter_cons]
    cases q x <;> simp [ih]

theorem filterBlocksIdx_lt_flatMap {α β : Type} (f : α → List β) (q : α → Bool) (xs : List α) :
    ∀ {i : Nat}, i < (filterBlocksIdx f q xs).length →
      (filterBlocksIdx f q xs).getD i 0 < (xs.flatMap f).length := by
  induction xs with
  | nil => intro i hi; simp [filterBlocksIdx] at hi
  | cons x xs ih =>
    intro i hi
    simp only [filterBlocksIdx] at hi ⊢
    cases hq : q x
    · simp only [hq, Bool.false_eq_true, ite_false, List.length_map] at hi ⊢
      rw [getD_map_add _ _ hi]
      have := ih hi
      simp only [List.flatMap_cons, List.length_append]; omega
    · simp only [hq, ite_true, List.length_append, List.length_range, List.length_map] at hi ⊢
      by_cases hin : i < (f x).length
      · rw [getD_append_left _ _ _ (by simp [hin]), getD_range hin]
        simp only [List.flatMap_cons, List.length_append]; omega
      · have hge : (List.range (f x).length).length ≤ i := by simp; omega
        rw [getD_append_right _ _ _ hge]
        simp only [List.length_range] at *
        rw [getD_map_add _ _ (by omega)]
        have := ih (i := i - (f x).length) (by omega)
        simp only [List.flatMap_cons, List.length_append]; omega

theorem filterBlocksIdx_strictMono {α β : Type} (f : α → List β) (q : α → Bool) (xs : List α) :
    ∀ {i j : Nat}, i < j → j < (filterBlocksIdx f q xs).length →
      (filterBlocksIdx f q xs).getD i 0 < (filterBlocksIdx f q xs).getD j 0 := by
  induction xs with
  | nil => intro _ j _ hj; simp [filterBlocksIdx] at hj
  | cons x xs ih =>
    intro i j hij hj
    simp only [filterBlocksIdx] at hj ⊢
    cases hq : q x
    · simp only [hq, Bool.false_eq_true, ite_false, List.length_map] at hj ⊢
      rw [getD_map_add _ _ (by omega), getD_map_add _ _ hj]
      have := ih hij hj; omega
    · simp only [hq, ite_true, List.length_append, List.length_range, List.length_map] at hj ⊢
      by_cases hjn : j < (f x).length
      · rw [getD_append_left _ _ _ (by simp; omega), getD_append_left _ _ _ (by simp [hjn]),
          getD_range (by omega), getD_range hjn]
        exact hij
      · by_cases hin : i < (f x).length
        · rw [getD_append_left _ _ _ (by simp [hin]), getD_range hin,
            getD_append_right _ _ _ (by simp; omega)]
          simp only [List.length_range]
          rw [getD_map_add _ _ (by omega)]; omega
        · rw [getD_append_right _ _ _ (by simp; omega), getD_append_right _ _ _ (by simp; omega)]
          simp only [List.length_range]
          rw [getD_map_add _ _ (by omega), getD_map_add _ _ (by omega)]
          have := ih (i := i - (f x).length) (j := j - (f x).length) (by omega) (by omega)
          omega

theorem filterBlocksIdx_inj {α β : Type} (f : α → List β) (q : α → Bool) (xs : List α)
    {i j : Nat} (hi : i < (filterBlocksIdx f q xs).length) (hj : j < (filterBlocksIdx f q xs).length)
    (heq : (filterBlocksIdx f q xs).getD i 0 = (filterBlocksIdx f q xs).getD j 0) :
    i = j := by
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · have := filterBlocksIdx_strictMono f q xs hlt hj; omega
  · rfl
  · have := filterBlocksIdx_strictMono f q xs hgt hi; omega

theorem filterBlocksIdx_getD_flatMap {α β : Type} (f : α → List β) (q : α → Bool) (xs : List α)
    (d : β) : ∀ {i : Nat}, i < (filterBlocksIdx f q xs).length →
      (xs.flatMap f).getD ((filterBlocksIdx f q xs).getD i 0) d =
        ((xs.filter q).flatMap f).getD i d := by
  induction xs with
  | nil => intro i hi; simp [filterBlocksIdx] at hi
  | cons x xs ih =>
    intro i hi
    simp only [filterBlocksIdx] at hi ⊢
    cases hq : q x
    · simp only [hq, Bool.false_eq_true, ite_false, List.length_map, List.filter_cons, List.flatMap_cons] at hi ⊢
      rw [getD_map_add _ _ hi, getD_append_right (f x) _ _ (by omega)]
      have hsub : (filterBlocksIdx f q xs).getD i 0 + (f x).length - (f x).length =
          (filterBlocksIdx f q xs).getD i 0 := by omega
      rw [hsub]; exact ih hi
    · simp only [hq, ite_true, List.length_append, List.length_range, List.length_map,
        List.filter_cons, List.flatMap_cons] at hi ⊢
      by_cases hin : i < (f x).length
      · rw [getD_append_left (List.range (f x).length) _ _ (by rw [List.length_range]; exact hin),
          getD_range hin, getD_append_left (f x) _ _ hin, getD_append_left (f x) _ _ hin]
      · rw [getD_append_right (List.range (f x).length) _ _ (by rw [List.length_range]; omega),
          List.length_range, getD_map_add _ _ (by omega),
          getD_append_right (f x) _ _ (by omega), getD_append_right (f x) _ _ (by omega)]
        have hsub : (filterBlocksIdx f q xs).getD (i - (f x).length) 0 + (f x).length - (f x).length =
            (filterBlocksIdx f q xs).getD (i - (f x).length) 0 := by omega
        rw [hsub]; exact ih (by omega)

private theorem filterBlocksIdx_mem_or_dropped {α β : Type} (f : α → List β) (q : α → Bool)
    (xs : List α) (d : β) : ∀ {k : Nat}, k < (xs.flatMap f).length →
      (∃ i < (filterBlocksIdx f q xs).length, (filterBlocksIdx f q xs).getD i 0 = k) ∨
      (∃ x ∈ xs, q x = false ∧ (xs.flatMap f).getD k d ∈ f x) := by
  induction xs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk
    simp only [List.flatMap_cons, List.length_append] at hk
    by_cases hkn : k < (f x).length
    · cases hq : q x
      · right
        refine ⟨x, List.mem_cons_self, hq, ?_⟩
        rw [List.flatMap_cons, getD_append_left (f x) _ _ hkn]
        exact getD_mem_of_lt (f x) d hkn
      · left
        refine ⟨k, ?_, ?_⟩
        · simp [filterBlocksIdx, hq]; omega
        · simp only [filterBlocksIdx, hq, ite_true]
          rw [getD_append_left (List.range (f x).length) _ _ (by rw [List.length_range]; exact hkn),
            getD_range hkn]
    · rcases ih (k := k - (f x).length) (by omega) with ⟨i, hi, heq⟩ | ⟨y, hy, hqy, hmem⟩
      · left
        cases hq : q x
        · refine ⟨i, by simp [filterBlocksIdx, hq, hi], ?_⟩
          simp only [filterBlocksIdx, hq, Bool.false_eq_true, ite_false]
          rw [getD_map_add _ _ hi, heq]; omega
        · refine ⟨(f x).length + i, by simp [filterBlocksIdx, hq, hi], ?_⟩
          simp only [filterBlocksIdx, hq, ite_true]
          rw [getD_append_right (List.range (f x).length) _ _ (by rw [List.length_range]; omega),
            List.length_range]
          have hadd : (f x).length + i - (f x).length = i := by omega
          rw [hadd, getD_map_add _ _ hi, heq]; omega
      · right
        refine ⟨y, List.mem_cons_of_mem _ hy, hqy, ?_⟩
        rw [List.flatMap_cons, getD_append_right (f x) _ _ (by omega)]
        exact hmem

theorem filterBlocksIdx_comp {α β : Type} (f : α → List β) (q r : α → Bool) (xs : List α)
    (hrq : ∀ x ∈ xs, r x = true → q x = true) :
    (filterBlocksIdx f r (xs.filter q)).map (fun i => (filterBlocksIdx f q xs).getD i 0) =
      filterBlocksIdx f r xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun y hy => hrq y (List.mem_cons_of_mem _ hy))
    have hx := hrq x List.mem_cons_self
    cases hq : q x
    · have hr : r x = false := by cases hr' : r x <;> simp_all
      simp only [List.filter_cons, filterBlocksIdx, hq, hr, Bool.false_eq_true, ite_false]
      rw [← ih', List.map_map]
      apply List.map_congr_left
      intro i hi
      rcases List.mem_iff_getElem.mp hi with ⟨j, hj, rfl⟩
      have hlt : (filterBlocksIdx f r (xs.filter q))[j] < (filterBlocksIdx f q xs).length := by
        have h1 := filterBlocksIdx_lt_flatMap f r (xs.filter q) hj
        rw [← filterBlocksIdx_length f q xs] at h1
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h1
      exact getD_map_add (filterBlocksIdx f q xs) (f x).length hlt
    · cases hr : r x
      · simp only [List.filter_cons, hq, ite_true]
        simp only [filterBlocksIdx, hq, hr, Bool.false_eq_true, ite_true, ite_false, List.map_map]
        rw [← ih', List.map_map]
        apply List.map_congr_left
        intro i hi
        rcases List.mem_iff_getElem.mp hi with ⟨j, hj, rfl⟩
        have hlt' : (filterBlocksIdx f r (xs.filter q))[j] < (filterBlocksIdx f q xs).length := by
          have h1 := filterBlocksIdx_lt_flatMap f r (xs.filter q) hj
          rw [← filterBlocksIdx_length f q xs] at h1
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h1
        simp only [Function.comp_apply]
        rw [getD_append_right (List.range (f x).length) _ _ (by rw [List.length_range]; omega),
          List.length_range]
        have hsub : (filterBlocksIdx f r (xs.filter q))[j] + (f x).length - (f x).length =
            (filterBlocksIdx f r (xs.filter q))[j] := by omega
        rw [hsub, getD_map_add _ _ hlt']
      · simp only [List.filter_cons, hq, ite_true]
        simp only [filterBlocksIdx, hq, hr, ite_true, List.map_append, List.map_map]
        congr 1
        · apply List.ext_getElem (by simp)
          intro i hi1 hi2
          have hin : i < (f x).length := by simpa using hi2
          simp only [List.getElem_map, List.getElem_range]
          rw [getD_append_left (List.range (f x).length) _ _ (by rw [List.length_range]; exact hin),
            getD_range hin]
        · rw [← ih', List.map_map]
          apply List.map_congr_left
          intro i hi
          rcases List.mem_iff_getElem.mp hi with ⟨j, hj, rfl⟩
          have hlt' : (filterBlocksIdx f r (xs.filter q))[j] < (filterBlocksIdx f q xs).length := by
            have h1 := filterBlocksIdx_lt_flatMap f r (xs.filter q) hj
            rw [← filterBlocksIdx_length f q xs] at h1
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h1
          simp only [Function.comp_apply]
          rw [getD_append_right (List.range (f x).length) _ _ (by rw [List.length_range]; omega),
            List.length_range]
          have hsub : (filterBlocksIdx f r (xs.filter q))[j] + (f x).length - (f x).length =
              (filterBlocksIdx f r (xs.filter q))[j] := by omega
          rw [hsub, getD_map_add _ _ hlt']

private theorem findIdx?_some_getD : ∀ (l : List Nat) {a idx : Nat},
    l.findIdx? (· == a) = some idx → idx < l.length ∧ l.getD idx 0 = a
  | [], _, _, h => by simp at h
  | x :: xs, a, idx, h => by
    simp only [List.findIdx?_cons] at h
    by_cases hxa : (x == a) = true
    · simp only [hxa, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨by simp, beq_iff_eq.mp hxa⟩
    · have hxaf : (x == a) = false := Bool.eq_false_iff.mpr hxa
      simp only [hxaf, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨hklt, hkeq⟩ := findIdx?_some_getD xs hk
      exact ⟨by simp; omega, by simpa [List.getD_eq_getElem?_getD] using hkeq⟩

private theorem findIdx?_eq_some_of_strictMono : ∀ (l : List Nat),
    (∀ i j, i < j → j < l.length → l.getD i 0 < l.getD j 0) →
    ∀ {idx a : Nat}, idx < l.length → l.getD idx 0 = a → l.findIdx? (· == a) = some idx
  | [], _, idx, _, hlt, _ => by simp at hlt
  | x :: xs, _, 0, a, _, heq => by
    simp only [List.getD_cons_zero] at heq
    subst heq
    simp [List.findIdx?_cons]
  | x :: xs, hmono, idx + 1, a, hlt, heq => by
    have hlt0 : x < a := by
      have h := hmono 0 (idx + 1) (by omega) hlt
      rw [List.getD_cons_zero, heq] at h
      exact h
    have hxaf : (x == a) = false := beq_false_of_ne (by omega)
    have hmono' : ∀ i j, i < j → j < xs.length → xs.getD i 0 < xs.getD j 0 := by
      intro i j hij hj
      have h1 := hmono (i + 1) (j + 1) (by omega) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD] using h1
    have heq' : xs.getD idx 0 = a := by simpa [List.getD_eq_getElem?_getD] using heq
    simp only [List.findIdx?_cons, hxaf, Bool.false_eq_true, ite_false, Option.map_eq_some_iff]
    exact ⟨idx, findIdx?_eq_some_of_strictMono xs hmono' (by simp at hlt; omega) heq', rfl⟩

/-- Characterization of `pairs` membership. -/
theorem pairs_has (n : Nat) (p : Nat → Nat → Bool) (a b : Nat) :
    (pairs n p).has a b = true ↔ a < n ∧ b < n ∧ p a b = true := by
  simp only [Rel.has, pairs, List.contains_iff_mem, List.mem_flatMap, List.mem_range,
    List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', b', hb', hif⟩
    split at hif
    · injection hif with hpair; injection hpair with h1 h2; subst h1 h2
      exact ⟨ha', hb', ‹_›⟩
    · cases hif
  · rintro ⟨ha, hb, hp⟩
    exact ⟨a, ha, b, hb, by simp [hp]⟩

theorem Rel.has_append (r₁ r₂ : Rel) (a b : Nat) :
    (r₁ ++ r₂).has a b = (r₁.has a b || r₂.has a b) := by
  simp [Rel.has]

theorem Rel.step_has_iff (r : Rel) (a c : Nat) :
    r.step.has a c = true ↔ r.has a c = true ∨ ∃ b, r.has a b = true ∧ r.has b c = true := by
  unfold Rel.step
  rw [Rel.has_append, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · simp only [Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap] at h
      obtain ⟨⟨a', b⟩, hab, ⟨b', c'⟩, hbc, hif⟩ := h
      dsimp only at hif
      by_cases hcond : (decide (b = b') && !r.contains (a', c')) = true
      · simp only [hcond, ite_true, Option.some.injEq, Prod.mk.injEq] at hif
        obtain ⟨rfl, rfl⟩ := hif
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨rfl, _⟩
        simp only [Rel.has, List.contains_iff_mem]
        exact Or.inr ⟨b, hab, hbc⟩
      · simp only [hcond] at hif; cases hif
  · rintro (h | ⟨b, hab, hbc⟩)
    · exact Or.inl h
    · by_cases hac : r.has a c = true
      · exact Or.inl hac
      · right
        have hacMem : (a, c) ∉ r := by simpa [Rel.has, List.contains_iff_mem] using hac
        simp only [Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap] at hab hbc ⊢
        exact ⟨(a, b), hab, (b, c), hbc, by simp [hacMem]⟩

theorem Rel.closure_hom {r₁ r₂ : Rel} (f : Nat → Nat)
    (h : ∀ x y, r₁.has x y = true → r₂.has (f x) (f y) = true) :
    ∀ (k x y : Nat), (r₁.closure k).has x y = true → (r₂.closure k).has (f x) (f y) = true
  | 0, x, y, hxy => h x y hxy
  | k + 1, x, y, hxy => by
    apply Rel.closure_hom (r₁ := r₁.step) (r₂ := r₂.step) f ?_ k x y hxy
    intro a c hac
    rw [Rel.step_has_iff] at hac ⊢
    rcases hac with hac | ⟨b, hab, hbc⟩
    · exact Or.inl (h a c hac)
    · exact Or.inr ⟨f b, h a b hab, h b c hbc⟩

theorem Rel.closure_mono_steps (r : Rel) {k₁ k₂ x y : Nat} (hle : k₁ ≤ k₂)
    (h : (r.closure k₁).has x y = true) : (r.closure k₂).has x y = true := by
  have step1 : ∀ m, (r.closure m).has x y = true → (r.closure (m + 1)).has x y = true := by
    intro m hm
    exact Rel.closure_hom id (fun a b hab => (Rel.step_has_iff r a b).mpr (Or.inl hab)) m x y hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact h
  | succ d ih => exact step1 (k₁ + d) ih

/-- Restricted threads of `P.restrict V` are the `V`-threads of `(P.restrict U).threads` when `V ≤ U`. -/
theorem restrict_threads_eq_filter (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) :
    (P.restrict V).threads = (P.restrict U).threads.filter (fun th => Obj.le P (.thread th.id) V) := by
  simp only [Shape.restrict, List.filter_filter]
  apply List.filter_congr
  intro th _
  by_cases h : Obj.le P (.thread th.id) V = true
  · simp [h, le_trans P h hVU]
  · simp [h]

theorem restrict_external_subset (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {p : Loc × Nat} (hp : p ∈ (P.restrict U).external) : p ∈ (P.restrict V).external := by
  simp only [Shape.restrict, List.mem_append, List.mem_flatMap, List.mem_filter] at hp ⊢
  rcases hp with hp | ⟨th, ⟨hth, hnU⟩, hp⟩
  · exact Or.inl hp
  · right
    refine ⟨th, ⟨hth, ?_⟩, hp⟩
    by_cases hV : Obj.le P (.thread th.id) V = true
    · simp [le_trans P hV hVU] at hnU
    · simp [hV]

/-- Node index list embedding `(P.restrict V).nodes` into `(P.restrict U).nodes`. -/
def restrictEmbedList (P : Shape) (U V : Obj) : List Nat :=
  filterBlocksIdx Thread.nodes (fun th => Obj.le P (.thread th.id) V) (P.restrict U).threads

/-- Node index map `(P.restrict V).nodes → (P.restrict U).nodes`. -/
def restrictEmbed (P : Shape) (U V : Obj) (a' : Nat) : Nat :=
  (restrictEmbedList P U V).getD a' 0

theorem restrictEmbedList_length (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) :
    (restrictEmbedList P U V).length = (P.restrict V).nodes.length := by
  simp only [restrictEmbedList, filterBlocksIdx_length, Shape.nodes, restrict_threads_eq_filter P hVU]

theorem restrictEmbed_lt (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' < (P.restrict V).nodes.length) :
    restrictEmbed P U V a' < (P.restrict U).nodes.length := by
  rw [← restrictEmbedList_length P hVU] at ha'
  exact filterBlocksIdx_lt_flatMap Thread.nodes _ _ ha'

theorem restrictEmbed_strictMono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (hlt : a' < b') (hb' : b' < (P.restrict V).nodes.length) :
    restrictEmbed P U V a' < restrictEmbed P U V b' := by
  rw [← restrictEmbedList_length P hVU] at hb'
  exact filterBlocksIdx_strictMono Thread.nodes _ _ hlt hb'

theorem restrictEmbed_inj (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (ha' : a' < (P.restrict V).nodes.length) (hb' : b' < (P.restrict V).nodes.length)
    (heq : restrictEmbed P U V a' = restrictEmbed P U V b') : a' = b' := by
  rw [← restrictEmbedList_length P hVU] at ha' hb'
  exact filterBlocksIdx_inj Thread.nodes _ _ ha' hb' heq

theorem restrictEmbed_node (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' < (P.restrict V).nodes.length) :
    (P.restrict U).nodes.getD (restrictEmbed P U V a') default = (P.restrict V).nodes.getD a' default := by
  have haL : a' < (restrictEmbedList P U V).length := by rwa [restrictEmbedList_length P hVU]
  have h := filterBlocksIdx_getD_flatMap Thread.nodes (fun th => Obj.le P (.thread th.id) V)
    (P.restrict U).threads default haL
  simpa [restrictEmbed, restrictEmbedList, Shape.nodes, restrict_threads_eq_filter P hVU] using h

theorem restrictEmbed_len_le (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) :
    (P.restrict V).nodes.length ≤ (P.restrict U).nodes.length := by
  by_cases h0 : (P.restrict V).nodes.length = 0
  · omega
  · let last := (P.restrict V).nodes.length - 1
    have hlast : last < (P.restrict V).nodes.length := by omega
    have hlt := restrictEmbed_lt P hVU hlast
    have hge : last ≤ restrictEmbed P U V last := by
      suffices ∀ k < (P.restrict V).nodes.length, k ≤ restrictEmbed P U V k from this last hlast
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        have hsm := restrictEmbed_strictMono P hVU (show k < k + 1 by omega) hk
        omega
    omega

theorem po_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (h : (po (P.restrict V).nodes).has a' b' = true) :
    (po (P.restrict U).nodes).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  rw [po, pairs_has] at h ⊢
  obtain ⟨ha', hb', hp⟩ := h
  refine ⟨restrictEmbed_lt P hVU ha', restrictEmbed_lt P hVU hb', ?_⟩
  rwa [restrictEmbed_node P hVU ha', restrictEmbed_node P hVU hb']

theorem sw_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (h : (sw (P.restrict V).nodes).has a' b' = true) :
    (sw (P.restrict U).nodes).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  rw [sw, pairs_has] at h ⊢
  obtain ⟨ha', hb', hs⟩ := h
  refine ⟨restrictEmbed_lt P hVU ha', restrictEmbed_lt P hVU hb', ?_⟩
  rw [restrictEmbed_node P hVU ha', restrictEmbed_node P hVU hb']
  have hne : (restrictEmbed P U V a' != restrictEmbed P U V b') = (a' != b') := by
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [bne_iff_ne.mpr hab, bne_iff_ne.mpr (fun heq => hab (restrictEmbed_inj P hVU ha' hb' heq))]
  rwa [hne]

theorem ithb_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) (T : List Space)
    {a' b' : Nat} (h : (ithb (P.restrict V).nodes T).has a' b' = true) :
    (ithb (P.restrict U).nodes T).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  unfold ithb at h ⊢
  dsimp only at h ⊢
  apply Rel.closure_mono_steps _ (restrictEmbed_len_le P hVU)
  refine Rel.closure_hom (restrictEmbed P U V) ?_ (P.restrict V).nodes.length a' b' h
  intro x' y' hxy
  rw [pairs_has] at hxy ⊢
  obtain ⟨hx', hy', he⟩ := hxy
  refine ⟨restrictEmbed_lt P hVU hx', restrictEmbed_lt P hVU hy', ?_⟩
  rw [restrictEmbed_node P hVU hx', restrictEmbed_node P hVU hy']
  simp only [Bool.or_eq_true, Bool.and_eq_true] at he ⊢
  rcases he with (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl (Or.inl ⟨⟨h1, h2⟩, sw_restrict_mono P hVU h3⟩)
  · exact Or.inl (Or.inr ⟨⟨h1, po_restrict_mono P hVU h2⟩, h3⟩)
  · exact Or.inr ⟨⟨h1, po_restrict_mono P hVU h2⟩, h3⟩

/-- Monotonicity of `hb` along `V ≤ U`. -/
theorem hb_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (h : (hb (P.restrict V).nodes).has a' b' = true) :
    (hb (P.restrict U).nodes).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  simp only [hb, Rel.has_append, Bool.or_eq_true] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (po_restrict_mono P hVU h)))
  · exact Or.inl (Or.inl (Or.inr (ithb_restrict_mono P hVU [.storage] h)))
  · exact Or.inl (Or.inr (ithb_restrict_mono P hVU [.workgroup] h))
  · exact Or.inr (ithb_restrict_mono P hVU [.storage, .workgroup] h)

/-- Monotonicity of `locord` along `V ≤ U`. -/
theorem locord_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (h : (locord (P.restrict V).nodes).has a' b' = true) :
    (locord (P.restrict U).nodes).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  rw [locord, pairs_has] at h ⊢
  obtain ⟨ha', hb', hp⟩ := h
  rw [Bool.and_eq_true] at hp ⊢
  obtain ⟨hsl, hhb⟩ := hp
  refine ⟨restrictEmbed_lt P hVU ha', restrictEmbed_lt P hVU hb', ?_, hb_restrict_mono P hVU hhb⟩
  rwa [restrictEmbed_node P hVU ha', restrictEmbed_node P hVU hb']

/-- Restriction of a witness `w` of `P.restrict U` to a witness of `P.restrict V` along `V ≤ U`:
reads from writes inside `V` keep their re-indexed internal writer, reads from writes in `U \ V`
become `external` with the writer's value in `U`, and coherence ranks and memory-order positions
are compressed onto `V`'s events. -/
def restrictWitness (P : Shape) (U V : Obj) (w : List Nat) : List Nat :=
  let sU := (P.restrict U).static
  let sV := (P.restrict V).static
  let embL := restrictEmbedList P U V
  let emb := restrictEmbed P U V
  let extSlot := fun r' v =>
    match (sV.externalAt r').find? fun j => (sV.external.getD j default).2 == v with
    | some j => sV.nodes.length + 1 + j
    | none => sV.nodes.length + 1
  let rfSlot := fun r' =>
    let r := emb r'
    match sU.rf w r with
    | .init => 0
    | .internal a =>
      if (sU.writesAt r).contains a && a != r then
        match embL.findIdx? (· == a) with
        | some a' => a' + 1
        | none => extSlot r' (sU.valueOfWrite w sU.nodes.length a)
      else extSlot r' (sU.valueOfWrite w sU.nodes.length a)
    | .external v => extSlot r' v
  let rankSlot := fun a' => Static.compress ((sV.writesAt a').map emb) (sU.rank w) (emb a')
  let ordSlot := fun a' => Static.compress (sV.mems.map emb) (sU.ord w) (emb a')
  (sV.reads.map rfSlot) ++ (sV.writes.map rankSlot) ++ (sV.mems.map ordSlot)

abbrev Shape.restrictWitness (P : Shape) (U V : Obj) (w : List Nat) : List Nat :=
  Memory.restrictWitness P U V w

private inductive StrictInc : List Nat → Prop
  | nil : StrictInc []
  | cons {x : Nat} {xs : List Nat} : (∀ y ∈ xs, x < y) → StrictInc xs → StrictInc (x :: xs)

private theorem strictInc_filter {l : List Nat} (hl : StrictInc l) (p : Nat → Bool) :
    StrictInc (l.filter p) := by
  induction hl with
  | nil => exact .nil
  | cons hlt _ ih =>
    simp only [List.filter_cons]
    split
    · exact .cons (fun y hy => hlt y (List.mem_filter.mp hy).1) ih
    · exact ih

private theorem strictInc_range' : ∀ (s n : Nat), StrictInc (List.range' s n)
  | _, 0 => .nil
  | s, n + 1 => .cons (fun y hy => by rw [List.mem_range'] at hy; omega) (strictInc_range' (s + 1) n)

private theorem strictInc_range (n : Nat) : StrictInc (List.range n) := by
  rw [List.range_eq_range']; exact strictInc_range' 0 n

private theorem posOf_lt_and_map_getD {l : List Nat} (hl : StrictInc l) (f : Nat → Nat)
    {a : Nat} (ha : a ∈ l) : posOf l a < l.length ∧ (l.map f).getD (posOf l a) 0 = f a := by
  induction hl with
  | nil => nomatch ha
  | @cons x xs hlt _ ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · simp [posOf, List.findIdx?_cons]
    · have hxa : (x == a) = false := beq_false_of_ne (Nat.ne_of_lt (hlt a hmem))
      obtain ⟨ihLt, ihEq⟩ := ih hmem
      unfold posOf at ihLt ihEq ⊢
      simp only [List.findIdx?_cons, hxa, Bool.false_eq_true, ite_false]
      cases hf : xs.findIdx? (· == a) with
      | none =>
        rw [List.findIdx?_eq_none_iff] at hf
        exact absurd (hf a hmem) (by simp)
      | some idx =>
        simp only [hf] at ihLt ihEq
        simp only [Option.map_some, List.length_cons, List.map_cons]
        exact ⟨by omega, by simpa [List.getD_eq_getElem?_getD] using ihEq⟩

private theorem static_reads_strictInc (P : Shape) : StrictInc P.static.reads :=
  strictInc_filter (strictInc_range _) _

private theorem static_writes_strictInc (P : Shape) : StrictInc P.static.writes :=
  strictInc_filter (strictInc_range _) _

private theorem static_mems_strictInc (P : Shape) : StrictInc P.static.mems :=
  strictInc_filter (strictInc_range _) _

private theorem mem_static_reads (P : Shape) {a : Nat} :
    a ∈ P.static.reads ↔ a < P.nodes.length ∧ (P.nodes.getD a default).ev.isRead = true := by
  simp [Shape.static, List.mem_filter, List.mem_range]

private theorem mem_static_writes (P : Shape) {a : Nat} :
    a ∈ P.static.writes ↔ a < P.nodes.length ∧ (P.nodes.getD a default).ev.isWrite = true := by
  simp [Shape.static, List.mem_filter, List.mem_range]

private theorem mem_static_mems (P : Shape) {a : Nat} :
    a ∈ P.static.mems ↔ a < P.nodes.length ∧ (P.nodes.getD a default).ev.loc?.isSome = true := by
  simp [Shape.static, List.mem_filter, List.mem_range]

private theorem mem_static_writesAt (P : Shape) {r a : Nat} :
    a ∈ P.static.writesAt r ↔ a ∈ P.static.writes ∧ P.static.sameLoc r a = true := by
  simp only [Static.writesAt, Static.sameLoc, List.mem_filter]

private theorem isRead_imp_loc_isSome {e : Ev} (h : e.isRead = true) : e.loc?.isSome = true := by
  cases e <;> simp_all [Ev.isRead, Ev.loc?]

private theorem isWrite_imp_loc_isSome {e : Ev} (h : e.isWrite = true) : e.loc?.isSome = true := by
  cases e <;> simp_all [Ev.isWrite, Ev.loc?]

private theorem isRmw_imp_isWrite {e : Ev} (h : e.isRmw = true) : e.isWrite = true := by
  cases e <;> simp_all [Ev.isRmw, Ev.isWrite]

private theorem sameLoc_refl_of_isSome {x : Node} (h : x.ev.loc?.isSome = true) : x.sameLoc x = true := by
  unfold Node.sameLoc
  cases hx : x.ev.loc? <;> simp_all

private theorem sameLoc_imp_isSome {x y : Node} (h : x.sameLoc y = true) :
    x.ev.loc?.isSome = true ∧ y.ev.loc?.isSome = true := by
  unfold Node.sameLoc at h
  cases hx : x.ev.loc? <;> cases hy : y.ev.loc? <;> simp_all

private theorem sameLoc_eq_of_sameLoc {x y z : Node} (hxy : x.sameLoc y = true) :
    x.sameLoc z = y.sameLoc z := by
  unfold Node.sameLoc at hxy ⊢
  cases hx : x.ev.loc? <;> cases hy : y.ev.loc? <;> cases hz : z.ev.loc? <;> simp_all

private theorem reads_subset_mems (P : Shape) {a : Nat} (h : a ∈ P.static.reads) :
    a ∈ P.static.mems := by
  rw [mem_static_reads] at h
  rw [mem_static_mems]
  exact ⟨h.1, isRead_imp_loc_isSome h.2⟩

private theorem writes_subset_mems (P : Shape) {a : Nat} (h : a ∈ P.static.writes) :
    a ∈ P.static.mems := by
  rw [mem_static_writes] at h
  rw [mem_static_mems]
  exact ⟨h.1, isWrite_imp_loc_isSome h.2⟩

private theorem self_mem_writesAt (P : Shape) {a : Nat} (h : a ∈ P.static.writes) :
    a ∈ P.static.writesAt a := by
  rw [mem_static_writesAt]
  refine ⟨h, ?_⟩
  rw [mem_static_writes] at h
  exact sameLoc_refl_of_isSome (isWrite_imp_loc_isSome h.2)

private theorem writesAt_eq_of_sameLoc (s : Static) {a b : Nat} (hab : s.sameLoc a b = true) :
    s.writesAt a = s.writesAt b := by
  simp only [Static.writesAt]
  apply List.filter_congr
  intro w _
  exact sameLoc_eq_of_sameLoc hab

private theorem restrictEmbed_reads (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' ∈ (P.restrict V).static.reads) :
    restrictEmbed P U V a' ∈ (P.restrict U).static.reads := by
  rw [mem_static_reads] at ha' ⊢
  refine ⟨restrictEmbed_lt P hVU ha'.1, ?_⟩
  rw [restrictEmbed_node P hVU ha'.1]
  exact ha'.2

private theorem restrictEmbed_writes (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' ∈ (P.restrict V).static.writes) :
    restrictEmbed P U V a' ∈ (P.restrict U).static.writes := by
  rw [mem_static_writes] at ha' ⊢
  refine ⟨restrictEmbed_lt P hVU ha'.1, ?_⟩
  rw [restrictEmbed_node P hVU ha'.1]
  exact ha'.2

private theorem restrictEmbed_mems (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' ∈ (P.restrict V).static.mems) :
    restrictEmbed P U V a' ∈ (P.restrict U).static.mems := by
  rw [mem_static_mems] at ha' ⊢
  refine ⟨restrictEmbed_lt P hVU ha'.1, ?_⟩
  rw [restrictEmbed_node P hVU ha'.1]
  exact ha'.2

private theorem restrictEmbed_sameLoc (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' b' : Nat} (ha' : a' < (P.restrict V).nodes.length) (hb' : b' < (P.restrict V).nodes.length) :
    (P.restrict U).static.sameLoc (restrictEmbed P U V a') (restrictEmbed P U V b') =
      (P.restrict V).static.sameLoc a' b' := by
  simp only [Static.sameLoc, Shape.static]
  rw [restrictEmbed_node P hVU ha', restrictEmbed_node P hVU hb']

private theorem restrictEmbed_atomicAt (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' < (P.restrict V).nodes.length) :
    (P.restrict U).static.atomicAt (restrictEmbed P U V a') =
      (P.restrict V).static.atomicAt a' := by
  simp only [Static.atomicAt, Shape.static]
  rw [restrictEmbed_node P hVU ha']

private theorem restrictEmbed_threadOf (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' < (P.restrict V).nodes.length) :
    (P.restrict U).static.threadOf (restrictEmbed P U V a') =
      (P.restrict V).static.threadOf a' := by
  simp only [Static.threadOf, Shape.static]
  rw [restrictEmbed_node P hVU ha']

private theorem restrictEmbed_writesAt (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {r' a' : Nat} (hr' : r' < (P.restrict V).nodes.length)
    (ha' : a' ∈ (P.restrict V).static.writesAt r') :
    restrictEmbed P U V a' ∈ (P.restrict U).static.writesAt (restrictEmbed P U V r') := by
  rw [mem_static_writesAt] at ha' ⊢
  have haLt : a' < (P.restrict V).nodes.length := ((mem_static_writes _).mp ha'.1).1
  refine ⟨restrictEmbed_writes P hVU ha'.1, ?_⟩
  rw [restrictEmbed_sameLoc P hVU hr' haLt]
  exact ha'.2

private theorem writesAt_of_restrictEmbed (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {r' a' : Nat} (hr' : r' < (P.restrict V).nodes.length) (ha' : a' < (P.restrict V).nodes.length)
    (ha : restrictEmbed P U V a' ∈ (P.restrict U).static.writesAt (restrictEmbed P U V r')) :
    a' ∈ (P.restrict V).static.writesAt r' := by
  rw [mem_static_writesAt] at ha ⊢
  obtain ⟨haw, hsl⟩ := ha
  rw [mem_static_writes] at haw ⊢
  rw [restrictEmbed_node P hVU ha'] at haw
  rw [restrictEmbed_sameLoc P hVU hr' ha'] at hsl
  exact ⟨⟨ha', haw.2⟩, hsl⟩

private theorem findIdx?_restrictEmbed_some (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' a : Nat} (h : (restrictEmbedList P U V).findIdx? (· == a) = some a') :
    a' < (P.restrict V).nodes.length ∧ restrictEmbed P U V a' = a := by
  obtain ⟨hlt, heq⟩ := findIdx?_some_getD (restrictEmbedList P U V) h
  rw [restrictEmbedList_length P hVU] at hlt
  exact ⟨hlt, heq⟩

private theorem findIdx?_restrictEmbed_of_eq (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    {a' : Nat} (ha' : a' < (P.restrict V).nodes.length) :
    (restrictEmbedList P U V).findIdx? (· == restrictEmbed P U V a') = some a' := by
  apply findIdx?_eq_some_of_strictMono (restrictEmbedList P U V)
  · intro i j hij hj
    rw [restrictEmbedList_length P hVU] at hj
    exact restrictEmbed_strictMono P hVU hij hj
  · rwa [restrictEmbedList_length P hVU]
  · rfl

private theorem getD_reads_slot (P : Shape) (fR fW fM : Nat → Nat) {r : Nat}
    (hr : r ∈ P.static.reads) :
    ((P.static.reads.map fR) ++ (P.static.writes.map fW) ++ (P.static.mems.map fM)).getD
        (posOf P.static.reads r) 0 = fR r := by
  obtain ⟨hlt, heq⟩ := posOf_lt_and_map_getD (static_reads_strictInc P) fR hr
  rw [List.append_assoc, getD_append_left _ _ _ (by simp [hlt])]
  exact heq

private theorem rank_of_slots (P : Shape) (fR fW fM : Nat → Nat) {a : Nat}
    (ha : a ∈ P.static.writes) :
    P.static.rank ((P.static.reads.map fR) ++ (P.static.writes.map fW) ++ (P.static.mems.map fM)) a =
      fW a := by
  obtain ⟨hlt, heq⟩ := posOf_lt_and_map_getD (static_writes_strictInc P) fW ha
  unfold Static.rank
  rw [getD_append_left _ _ _ (by simp; omega), getD_append_right _ _ _ (by simp)]
  simp only [List.length_map]
  have hsub : P.static.reads.length + posOf P.static.writes a - P.static.reads.length =
      posOf P.static.writes a := by omega
  rw [hsub]
  exact heq

private theorem ord_of_slots (P : Shape) (fR fW fM : Nat → Nat) {a : Nat}
    (ha : a ∈ P.static.mems) :
    P.static.ord ((P.static.reads.map fR) ++ (P.static.writes.map fW) ++ (P.static.mems.map fM)) a =
      fM a := by
  obtain ⟨hlt, heq⟩ := posOf_lt_and_map_getD (static_mems_strictInc P) fM ha
  unfold Static.ord
  rw [getD_append_right _ _ _ (by simp)]
  simp only [List.length_append, List.length_map]
  have hsub : P.static.reads.length + P.static.writes.length + posOf P.static.mems a -
      (P.static.reads.length + P.static.writes.length) = posOf P.static.mems a := by omega
  rw [hsub]
  exact heq

theorem rank_restrictWitness (P : Shape) {U V : Obj} (wU : List Nat) {a' : Nat}
    (ha' : a' ∈ (P.restrict V).static.writes) :
    (P.restrict V).static.rank (restrictWitness P U V wU) a' =
      Static.compress (((P.restrict V).static.writesAt a').map (restrictEmbed P U V))
        ((P.restrict U).static.rank wU) (restrictEmbed P U V a') :=
  rank_of_slots (P.restrict V) _ _ _ ha'

theorem ord_restrictWitness (P : Shape) {U V : Obj} (wU : List Nat) {a' : Nat}
    (ha' : a' ∈ (P.restrict V).static.mems) :
    (P.restrict V).static.ord (restrictWitness P U V wU) a' =
      Static.compress ((P.restrict V).static.mems.map (restrictEmbed P U V))
        ((P.restrict U).static.ord wU) (restrictEmbed P U V a') :=
  ord_of_slots (P.restrict V) _ _ _ ha'

theorem rank_restrictWitness_lt_iff (P : Shape) {U V : Obj} (wU : List Nat) {a' b' : Nat}
    (ha' : a' ∈ (P.restrict V).static.writes) (hb' : b' ∈ (P.restrict V).static.writes)
    (hsl : (P.restrict V).static.sameLoc a' b' = true) :
    (P.restrict V).static.rank (restrictWitness P U V wU) a' <
        (P.restrict V).static.rank (restrictWitness P U V wU) b' ↔
      (P.restrict U).static.rank wU (restrictEmbed P U V a') <
        (P.restrict U).static.rank wU (restrictEmbed P U V b') := by
  rw [rank_restrictWitness P wU ha', rank_restrictWitness P wU hb',
    ← writesAt_eq_of_sameLoc _ hsl]
  apply compress_lt_iff
  · exact List.mem_map_of_mem (self_mem_writesAt (P.restrict V) ha')
  · rw [writesAt_eq_of_sameLoc _ hsl]
    exact List.mem_map_of_mem (self_mem_writesAt (P.restrict V) hb')

theorem ord_restrictWitness_lt_iff (P : Shape) {U V : Obj} (wU : List Nat) {a' b' : Nat}
    (ha' : a' ∈ (P.restrict V).static.mems) (hb' : b' ∈ (P.restrict V).static.mems) :
    (P.restrict V).static.ord (restrictWitness P U V wU) a' <
        (P.restrict V).static.ord (restrictWitness P U V wU) b' ↔
      (P.restrict U).static.ord wU (restrictEmbed P U V a') <
        (P.restrict U).static.ord wU (restrictEmbed P U V b') := by
  rw [ord_restrictWitness P wU ha', ord_restrictWitness P wU hb']
  exact compress_lt_iff _ _ (List.mem_map_of_mem ha') (List.mem_map_of_mem hb')

/-- Exact preservation of `asmo` on writes along `V ≤ U`. -/
theorem asmo_restrict_eq (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) (wU : List Nat)
    {a' b' : Nat} (ha' : a' ∈ (P.restrict V).static.writes) (hb' : b' ∈ (P.restrict V).static.writes) :
    (P.restrict V).static.asmo (restrictWitness P U V wU) a' b' =
      (P.restrict U).static.asmo wU (restrictEmbed P U V a') (restrictEmbed P U V b') := by
  have haLt : a' < (P.restrict V).nodes.length := ((mem_static_writes _).mp ha').1
  have hbLt : b' < (P.restrict V).nodes.length := ((mem_static_writes _).mp hb').1
  have hne : (a' != b') = (restrictEmbed P U V a' != restrictEmbed P U V b') := by
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [bne_iff_ne.mpr hab, bne_iff_ne.mpr (fun heq => hab (restrictEmbed_inj P hVU haLt hbLt heq))]
  unfold Static.asmo
  rw [hne, ← restrictEmbed_atomicAt P hVU haLt, ← restrictEmbed_atomicAt P hVU hbLt,
    ← restrictEmbed_sameLoc P hVU haLt hbLt]
  by_cases hsl : (P.restrict V).static.sameLoc a' b' = true
  · have hiff := rank_restrictWitness_lt_iff P (U := U) wU ha' hb' hsl
    rw [restrictEmbed_sameLoc P hVU haLt hbLt, hsl]
    simp only [Bool.and_true]
    cases h1 : ((P.restrict U).static.atomicAt (restrictEmbed P U V a')) <;>
    cases h2 : ((P.restrict U).static.atomicAt (restrictEmbed P U V b')) <;>
    cases h3 : (restrictEmbed P U V a' != restrictEmbed P U V b') <;>
    simp [hiff]
  · have hslf : (P.restrict V).static.sameLoc a' b' = false := Bool.eq_false_iff.mpr hsl
    rw [restrictEmbed_sameLoc P hVU haLt hbLt, hslf]
    simp

private theorem rf_extSlot_eq_external (P : Shape) (V : Obj) (r' v : Nat) :
    let k := match ((P.restrict V).static.externalAt r').find?
        (fun j => ((P.restrict V).static.external.getD j default).2 == v) with
      | some j => (P.restrict V).static.nodes.length + 1 + j
      | none => (P.restrict V).static.nodes.length + 1
    ∃ v', (if k = 0 then Src.init
      else if k ≤ (P.restrict V).static.nodes.length then .internal (k - 1)
      else .external (((P.restrict V).static.external.getD
        (k - (P.restrict V).static.nodes.length - 1) default).2)) = .external v' := by
  cases hf : ((P.restrict V).static.externalAt r').find?
      (fun j => ((P.restrict V).static.external.getD j default).2 == v) with
  | none =>
    dsimp only
    have hk0 : ¬ (P.restrict V).static.nodes.length + 1 = 0 := by omega
    have hkn : ¬ (P.restrict V).static.nodes.length + 1 ≤ (P.restrict V).static.nodes.length := by omega
    exact ⟨_, by simp only [hk0, hkn, ite_false]; rfl⟩
  | some j =>
    dsimp only
    have hk0 : ¬ (P.restrict V).static.nodes.length + 1 + j = 0 := by omega
    have hkn : ¬ (P.restrict V).static.nodes.length + 1 + j ≤ (P.restrict V).static.nodes.length := by omega
    exact ⟨_, by simp only [hk0, hkn, ite_false]; rfl⟩

private theorem rf_restrictWitness_init_iff (P : Shape) {U V : Obj} (wU : List Nat)
    {r' : Nat} (hr' : r' ∈ (P.restrict V).static.reads) :
    (P.restrict V).static.rf (restrictWitness P U V wU) r' = .init ↔
      (P.restrict U).static.rf wU (restrictEmbed P U V r') = .init := by
  change (let k := (restrictWitness P U V wU).getD (posOf (P.restrict V).static.reads r') 0
    if k = 0 then Src.init
    else if k ≤ (P.restrict V).static.nodes.length then .internal (k - 1)
    else .external (((P.restrict V).static.external.getD (k - (P.restrict V).static.nodes.length - 1) default).2)) =
      Src.init ↔ _
  rw [restrictWitness]
  dsimp only
  rw [getD_reads_slot (P.restrict V) _ _ _ hr']
  cases hrf : (P.restrict U).static.rf wU (restrictEmbed P U V r') with
  | init => simp
  | external v =>
    obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r' v
    dsimp only
    rw [hv']; simp
  | internal a =>
    dsimp only
    by_cases hg : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
        (a != restrictEmbed P U V r')) = true
    · simp only [hg, ite_true]
      cases hf : (restrictEmbedList P U V).findIdx? (· == a) with
      | some a' =>
        dsimp only
        simp only [Nat.succ_ne_zero, ite_false]
        split <;> simp
      | none =>
        obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r'
          ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
        dsimp only
        rw [hv']; simp
    · have hgf : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
          (a != restrictEmbed P U V r')) = false := Bool.eq_false_iff.mpr hg
      simp only [hgf, Bool.false_eq_true, ite_false]
      obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r'
        ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
      rw [hv']; simp

private theorem rf_restrictWitness_internal (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (wU : List Nat) {r' a' : Nat} (hr' : r' ∈ (P.restrict V).static.reads)
    (h : (P.restrict V).static.rf (restrictWitness P U V wU) r' = .internal a') :
    a' ∈ (P.restrict V).static.writesAt r' ∧
    a' ≠ r' ∧
    (P.restrict U).static.rf wU (restrictEmbed P U V r') = .internal (restrictEmbed P U V a') := by
  have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
  change (let k := (restrictWitness P U V wU).getD (posOf (P.restrict V).static.reads r') 0
    if k = 0 then Src.init
    else if k ≤ (P.restrict V).static.nodes.length then .internal (k - 1)
    else .external (((P.restrict V).static.external.getD (k - (P.restrict V).static.nodes.length - 1) default).2)) =
      .internal a' at h
  rw [restrictWitness] at h
  dsimp only at h
  rw [getD_reads_slot (P.restrict V) _ _ _ hr'] at h
  cases hrf : (P.restrict U).static.rf wU (restrictEmbed P U V r') with
  | init => rw [hrf] at h; simp at h
  | external v =>
    rw [hrf] at h; dsimp only at h
    obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r' v
    rw [hv'] at h; simp at h
  | internal a =>
    rw [hrf] at h; dsimp only at h
    by_cases hg : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
        (a != restrictEmbed P U V r')) = true
    · simp only [hg, ite_true] at h
      cases hf : (restrictEmbedList P U V).findIdx? (· == a) with
      | none =>
        rw [hf] at h; dsimp only at h
        obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r'
          ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
        rw [hv'] at h; simp at h
      | some a0 =>
        rw [hf] at h; dsimp only at h
        simp only [Nat.succ_ne_zero, ite_false] at h
        obtain ⟨ha0Lt, ha0Eq⟩ := findIdx?_restrictEmbed_some P hVU hf
        have hle : a0 + 1 ≤ (P.restrict V).static.nodes.length := by
          simp only [Shape.static]; omega
        simp only [hle, ite_true, Nat.add_sub_cancel, Src.internal.injEq] at h
        subst a0
        simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne] at hg
        rw [← ha0Eq] at hg
        refine ⟨writesAt_of_restrictEmbed P hVU hrLt ha0Lt hg.1, ?_, congrArg Src.internal ha0Eq.symm⟩
        intro heq; subst a'; exact hg.2 rfl
    · have hgf : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
          (a != restrictEmbed P U V r')) = false := Bool.eq_false_iff.mpr hg
      simp only [hgf, Bool.false_eq_true, ite_false] at h
      obtain ⟨v', hv'⟩ := rf_extSlot_eq_external P V r'
        ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
      rw [hv'] at h; simp at h

/-- Monotonicity of internal `rf` edges along `V ≤ U` (externalized `U \ V` writes drop from
`rfEdges`, while every internal `rf` edge in `V` has memory-event endpoints and maps into `U`). -/
theorem rfEdges_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) (wU : List Nat)
    {a' r' : Nat} (h : ((P.restrict V).static.rfEdges (restrictWitness P U V wU)).has a' r' = true) :
    a' ∈ (P.restrict V).static.mems ∧
    r' ∈ (P.restrict V).static.mems ∧
    ((P.restrict U).static.rfEdges wU).has (restrictEmbed P U V a') (restrictEmbed P U V r') = true := by
  simp only [Static.rfEdges, Rel.has, List.contains_iff_mem, List.mem_filterMap] at h ⊢
  obtain ⟨r0, hr0, hm⟩ := h
  cases hrf : (P.restrict V).static.rf (restrictWitness P U V wU) r0 with
  | init => simp [hrf] at hm
  | external _ => simp [hrf] at hm
  | internal a0 =>
    simp only [hrf, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨hwAt, _, hrfU⟩ := rf_restrictWitness_internal P hVU wU hr0 hrf
    have haw : a0 ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp hwAt).1
    exact ⟨writes_subset_mems _ haw, reads_subset_mems _ hr0,
      restrictEmbed P U V r0, restrictEmbed_reads P hVU hr0, by simp [hrfU]⟩

/-- Monotonicity of `asmo` edges along `V ≤ U`. -/
theorem asmoEdges_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) (wU : List Nat)
    {a' b' : Nat} (h : ((P.restrict V).static.asmoEdges (restrictWitness P U V wU)).has a' b' = true) :
    a' ∈ (P.restrict V).static.mems ∧
    b' ∈ (P.restrict V).static.mems ∧
    ((P.restrict U).static.asmoEdges wU).has (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
  simp only [Static.asmoEdges, Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap] at h ⊢
  obtain ⟨a0, ha0, b0, hb0, hm⟩ := h
  split at hm
  · rename_i hasmo
    injection hm with hp; injection hp with h1 h2; subst h1 h2
    rw [asmo_restrict_eq P hVU wU ha0 hb0] at hasmo
    exact ⟨writes_subset_mems _ ha0, writes_subset_mems _ hb0,
      restrictEmbed P U V a0, restrictEmbed_writes P hVU ha0,
      restrictEmbed P U V b0, restrictEmbed_writes P hVU hb0, by simp [hasmo]⟩
  · cases hm

/-- Monotonicity of `fr` edges along `V ≤ U`. -/
theorem frEdges_restrict_mono (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true) (wU : List Nat)
    {r' w' : Nat} (h : ((P.restrict V).static.frEdges (restrictWitness P U V wU)).has r' w' = true) :
    r' ∈ (P.restrict V).static.mems ∧
    w' ∈ (P.restrict V).static.mems ∧
    ((P.restrict U).static.frEdges wU).has (restrictEmbed P U V r') (restrictEmbed P U V w') = true := by
  simp only [Static.frEdges, Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap] at h ⊢
  obtain ⟨r0, hr0, w0, hw0, hm⟩ := h
  have hrLt : r0 < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr0).1
  have hwW : w0 ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp hw0).1
  have hwLt : w0 < (P.restrict V).nodes.length := ((mem_static_writes _).mp hwW).1
  by_cases hwr : w0 = r0
  · simp [hwr] at hm
  · simp only [hwr, ite_false] at hm
    have hwrU : restrictEmbed P U V w0 ≠ restrictEmbed P U V r0 :=
      fun heq => hwr (restrictEmbed_inj P hVU hwLt hrLt heq)
    cases hrf : (P.restrict V).static.rf (restrictWitness P U V wU) r0 with
    | external _ => simp [hrf] at hm
    | init =>
      simp only [hrf, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have hrfU := (rf_restrictWitness_init_iff P wU hr0).mp hrf
      exact ⟨reads_subset_mems _ hr0, writes_subset_mems _ hwW,
        restrictEmbed P U V r0, restrictEmbed_reads P hVU hr0,
        restrictEmbed P U V w0, restrictEmbed_writesAt P hVU hrLt hw0,
        by simp [hwrU, hrfU]⟩
    | internal a0 =>
      simp only [hrf] at hm
      by_cases hcond : (a0 != w0 && ((P.restrict V).static.asmo (restrictWitness P U V wU) a0 w0 ||
          (P.restrict V).static.locord.contains (a0, w0))) = true
      · simp only [hcond, ite_true, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        obtain ⟨haAt, _, hrfU⟩ := rf_restrictWitness_internal P hVU wU hr0 hrf
        have haW : a0 ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp haAt).1
        have haLt : a0 < (P.restrict V).nodes.length := ((mem_static_writes _).mp haW).1
        simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, List.contains_iff_mem] at hcond
        have hawU : (restrictEmbed P U V a0 != restrictEmbed P U V w0) = true :=
          bne_iff_ne.mpr (fun heq => hcond.1 (restrictEmbed_inj P hVU haLt hwLt heq))
        have horU : ((P.restrict U).static.asmo wU (restrictEmbed P U V a0) (restrictEmbed P U V w0) ||
            (P.restrict U).static.locord.contains (restrictEmbed P U V a0, restrictEmbed P U V w0)) = true := by
          rcases hcond.2 with hasmo | hloc
          · rw [asmo_restrict_eq P hVU wU haW hwW] at hasmo
            simp [hasmo]
          · have hloc' : (locord (P.restrict V).nodes).has a0 w0 = true := by
              simpa [Shape.static, Rel.has, List.contains_iff_mem] using hloc
            have hlocU := locord_restrict_mono P hVU hloc'
            have hmemU : (restrictEmbed P U V a0, restrictEmbed P U V w0) ∈ (P.restrict U).static.locord := by
              simpa [Shape.static, Rel.has, List.contains_iff_mem] using hlocU
            simp [hmemU]
        exact ⟨reads_subset_mems _ hr0, writes_subset_mems _ hwW,
          restrictEmbed P U V r0, restrictEmbed_reads P hVU hr0,
          restrictEmbed P U V w0, restrictEmbed_writesAt P hVU hrLt hw0,
          by simp only [hwrU, ite_false, hrfU, hawU, horU, Bool.true_and, ite_true]⟩
      · simp only [hcond] at hm; cases hm

/-- **Universal consistency restriction (Rung G4)**: if `V ≤ U` (`Obj.le P V U = true`) and `wU`
is consistent on `P.restrict U`, then `restrictWitness P U V wU` is consistent on `P.restrict V`. -/
theorem consistent_restrictWitness (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (wU : List Nat) (hCons : (P.restrict U).consistent wU = true) :
    (P.restrict V).consistent (restrictWitness P U V wU) = true := by
  simp only [Shape.consistent, Static.consistent, Static.consistentWith, Bool.false_eq_true,
    ite_false, List.append_nil, Bool.and_eq_true] at hCons ⊢
  obtain ⟨⟨⟨⟨hRankU, hOrdU⟩, hAcycU⟩, hAtomU⟩, hCrfU⟩ := hCons
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- 1. Ranks injective per location over writes
    rw [List.all_eq_true] at hRankU ⊢
    intro a' ha'
    rw [List.all_eq_true]
    intro b' hb'
    have haLt : a' < (P.restrict V).nodes.length := ((mem_static_writes _).mp ha').1
    have hbLt : b' < (P.restrict V).nodes.length := ((mem_static_writes _).mp hb').1
    by_cases hab : a' = b'
    · subst hab; simp
    · by_cases hsl : (P.restrict V).static.sameLoc a' b' = true
      · have hU := hRankU (restrictEmbed P U V a') (restrictEmbed_writes P hVU ha')
        rw [List.all_eq_true] at hU
        have hUb := hU (restrictEmbed P U V b') (restrictEmbed_writes P hVU hb')
        have habU : (restrictEmbed P U V a' == restrictEmbed P U V b') = false :=
          beq_false_of_ne (fun heq => hab (restrictEmbed_inj P hVU haLt hbLt heq))
        have hslU : (P.restrict U).static.sameLoc (restrictEmbed P U V a') (restrictEmbed P U V b') = true := by
          rw [restrictEmbed_sameLoc P hVU haLt hbLt]; exact hsl
        simp only [habU, hslU, Bool.not_true, Bool.false_or, bne_iff_ne] at hUb
        have hneV : (P.restrict V).static.rank (restrictWitness P U V wU) a' ≠
            (P.restrict V).static.rank (restrictWitness P U V wU) b' := by
          rw [rank_restrictWitness P wU ha', rank_restrictWitness P wU hb',
            ← writesAt_eq_of_sameLoc _ hsl]
          refine compress_ne_of_ne _ _ (List.mem_map_of_mem (self_mem_writesAt _ ha')) ?_ hUb
          rw [writesAt_eq_of_sameLoc _ hsl]
          exact List.mem_map_of_mem (self_mem_writesAt _ hb')
        simp [bne_iff_ne, hneV]
      · have hslf : (P.restrict V).static.sameLoc a' b' = false := Bool.eq_false_iff.mpr hsl
        simp [hslf]
  · -- 2. Order injective over memory events
    rw [List.all_eq_true] at hOrdU ⊢
    intro a' ha'
    rw [List.all_eq_true]
    intro b' hb'
    have haLt : a' < (P.restrict V).nodes.length := ((mem_static_mems _).mp ha').1
    have hbLt : b' < (P.restrict V).nodes.length := ((mem_static_mems _).mp hb').1
    by_cases hab : a' = b'
    · subst hab; simp
    · have hU := hOrdU (restrictEmbed P U V a') (restrictEmbed_mems P hVU ha')
      rw [List.all_eq_true] at hU
      have hUb := hU (restrictEmbed P U V b') (restrictEmbed_mems P hVU hb')
      have habU : (restrictEmbed P U V a' == restrictEmbed P U V b') = false :=
        beq_false_of_ne (fun heq => hab (restrictEmbed_inj P hVU haLt hbLt heq))
      simp only [habU, Bool.false_or, bne_iff_ne] at hUb
      have hneV : (P.restrict V).static.ord (restrictWitness P U V wU) a' ≠
          (P.restrict V).static.ord (restrictWitness P U V wU) b' := by
        rw [ord_restrictWitness P wU ha', ord_restrictWitness P wU hb']
        exact compress_ne_of_ne _ _ (List.mem_map_of_mem ha') (List.mem_map_of_mem hb') hUb
      simp [bne_iff_ne, hneV]
  · -- 3. Acyclicity: every edge of locord ∪ rf ∪ fr ∪ asmo goes up in ord
    rw [List.all_eq_true] at hAcycU ⊢
    rintro ⟨a', b'⟩ he
    have edgeUpU : ∀ x y,
        ((P.restrict U).static.locord ++ (P.restrict U).static.rfEdges wU ++
          (P.restrict U).static.frEdges wU ++ (P.restrict U).static.asmoEdges wU).has x y = true →
        (P.restrict U).static.ord wU x < (P.restrict U).static.ord wU y := by
      intro x y hxy
      simp only [Rel.has, List.contains_iff_mem] at hxy
      exact of_decide_eq_true (hAcycU (x, y) hxy)
    have hhas : ((P.restrict V).static.locord ++
        (P.restrict V).static.rfEdges (restrictWitness P U V wU) ++
        (P.restrict V).static.frEdges (restrictWitness P U V wU) ++
        (P.restrict V).static.asmoEdges (restrictWitness P U V wU)).has a' b' = true := by
      simpa [Rel.has, List.contains_iff_mem] using he
    simp only [Rel.has_append, Bool.or_eq_true] at hhas
    suffices hm : a' ∈ (P.restrict V).static.mems ∧ b' ∈ (P.restrict V).static.mems ∧
        ((P.restrict U).static.locord ++ (P.restrict U).static.rfEdges wU ++
          (P.restrict U).static.frEdges wU ++ (P.restrict U).static.asmoEdges wU).has
          (restrictEmbed P U V a') (restrictEmbed P U V b') = true by
      rw [decide_eq_true_eq, ord_restrictWitness_lt_iff P wU hm.1 hm.2.1]
      exact edgeUpU _ _ hm.2.2
    rcases hhas with ((hloc | hrf) | hfr) | hasmo
    · have hloc' : (locord (P.restrict V).nodes).has a' b' = true := hloc
      have hlocU := locord_restrict_mono P hVU hloc'
      rw [locord, pairs_has] at hloc'
      obtain ⟨haLt, hbLt, hp⟩ := hloc'
      rw [Bool.and_eq_true] at hp
      obtain ⟨haS, hbS⟩ := sameLoc_imp_isSome hp.1
      refine ⟨(mem_static_mems _).mpr ⟨haLt, haS⟩, (mem_static_mems _).mpr ⟨hbLt, hbS⟩, ?_⟩
      simp only [Rel.has_append, Bool.or_eq_true]
      exact Or.inl (Or.inl (Or.inl hlocU))
    · obtain ⟨haM, hbM, hrfU⟩ := rfEdges_restrict_mono P hVU wU hrf
      refine ⟨haM, hbM, ?_⟩
      simp only [Rel.has_append, Bool.or_eq_true]
      exact Or.inl (Or.inl (Or.inr hrfU))
    · obtain ⟨haM, hbM, hfrU⟩ := frEdges_restrict_mono P hVU wU hfr
      refine ⟨haM, hbM, ?_⟩
      simp only [Rel.has_append, Bool.or_eq_true]
      exact Or.inl (Or.inr hfrU)
    · obtain ⟨haM, hbM, hasmoU⟩ := asmoEdges_restrict_mono P hVU wU hasmo
      refine ⟨haM, hbM, ?_⟩
      simp only [Rel.has_append, Bool.or_eq_true]
      exact Or.inr hasmoU
  · -- 4. Atomic: no RMW whose read is fr-before another thread's write asmo-before its own write
    rw [List.all_eq_true] at hAtomU ⊢
    intro r' hr'
    have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
    by_cases hrmw : ((P.restrict V).static.nodes.getD r' default).ev.isRmw = true
    · simp only [hrmw, Bool.not_true, Bool.false_or, List.all_eq_true]
      intro w' hw'
      have hwW : w' ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp hw').1
      have hwLt : w' < (P.restrict V).nodes.length := ((mem_static_writes _).mp hwW).1
      have hrW : r' ∈ (P.restrict V).static.writes :=
        (mem_static_writes _).mpr ⟨hrLt, isRmw_imp_isWrite hrmw⟩
      have hU := hAtomU (restrictEmbed P U V r') (restrictEmbed_reads P hVU hr')
      have hrmwU : ((P.restrict U).static.nodes.getD (restrictEmbed P U V r') default).ev.isRmw = true := by
        simp only [Shape.static] at hrmw ⊢
        rwa [restrictEmbed_node P hVU hrLt]
      simp only [hrmwU, Bool.not_true, Bool.false_or, List.all_eq_true] at hU
      have hUw := hU (restrictEmbed P U V w') (restrictEmbed_writesAt P hVU hrLt hw')
      rw [restrictEmbed_threadOf P hVU hwLt, restrictEmbed_threadOf P hVU hrLt] at hUw
      by_cases hth : ((P.restrict V).static.threadOf w' == (P.restrict V).static.threadOf r') = true
      · simp [hth]
      · have hthf : ((P.restrict V).static.threadOf w' == (P.restrict V).static.threadOf r') = false :=
          Bool.eq_false_iff.mpr hth
        simp only [hthf, Bool.false_or, Bool.not_eq_true', Bool.and_eq_false_imp] at hUw ⊢
        intro hfrV
        have hfrU := (frEdges_restrict_mono P hVU wU hfrV).2.2
        rw [asmo_restrict_eq P hVU wU hwW hrW]
        exact hUw hfrU
    · have hrmwf : ((P.restrict V).static.nodes.getD r' default).ev.isRmw = false :=
        Bool.eq_false_iff.mpr hrmw
      simp only [hrmwf, Bool.not_false, Bool.true_or]
  · -- 5. consistency-rf: a non-atomic read does not read a write shadowed through writes
    rw [List.all_eq_true] at hCrfU ⊢
    intro r' hr'
    have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
    by_cases hat : (P.restrict V).static.atomicAt r' = true
    · simp [hat]
    · have hatf : (P.restrict V).static.atomicAt r' = false := Bool.eq_false_iff.mpr hat
      simp only [hatf, Bool.false_or]
      cases hrf : (P.restrict V).static.rf (restrictWitness P U V wU) r' with
      | init => rfl
      | external _ => rfl
      | internal a' =>
        obtain ⟨_, _, hrfU⟩ := rf_restrictWitness_internal P hVU wU hr' hrf
        have hU := hCrfU (restrictEmbed P U V r') (restrictEmbed_reads P hVU hr')
        have hatUf : (P.restrict U).static.atomicAt (restrictEmbed P U V r') = false := by
          rw [restrictEmbed_atomicAt P hVU hrLt]; exact hatf
        simp only [hatUf, Bool.false_or, hrfU, Bool.not_eq_true'] at hU ⊢
        let wlV : Rel := (P.restrict V).static.locord.filter
          fun (x, _) => ((P.restrict V).static.nodes.getD x default).ev.isWrite
        let wlU : Rel := (P.restrict U).static.locord.filter
          fun (x, _) => ((P.restrict U).static.nodes.getD x default).ev.isWrite
        let wl2V : Rel := wlV.flatMap fun (x, y) =>
          (wlV.closure (P.restrict V).static.nodes.length).filterMap fun (y', z) =>
            if y = y' then some (x, z) else none
        change wl2V.has a' r' = false
        cases hwl2' : wl2V.has a' r' with
        | false => rfl
        | true =>
          exfalso
          have wlMono : ∀ x' z', wlV.has x' z' = true →
              wlU.has (restrictEmbed P U V x') (restrictEmbed P U V z') = true := by
            intro x' z' hxz
            simp only [wlV, wlU, Rel.has, List.contains_iff_mem, List.mem_filter] at hxz ⊢
            obtain ⟨hloc, hw⟩ := hxz
            have hloc' : (locord (P.restrict V).nodes).has x' z' = true := by
              simpa [Shape.static, Rel.has, List.contains_iff_mem] using hloc
            have hxLt : x' < (P.restrict V).nodes.length := ((pairs_has _ _ _ _).mp hloc').1
            have hlocU := locord_restrict_mono P hVU hloc'
            refine ⟨by simpa [Shape.static, Rel.has, List.contains_iff_mem] using hlocU, ?_⟩
            simp only [Shape.static] at hw ⊢
            rwa [restrictEmbed_node P hVU hxLt]
          have wlcMono : ∀ y' z', (wlV.closure (P.restrict V).static.nodes.length).has y' z' = true →
              (wlU.closure (P.restrict U).static.nodes.length).has
                (restrictEmbed P U V y') (restrictEmbed P U V z') = true := by
            intro y' z' hyz
            apply Rel.closure_mono_steps _ (restrictEmbed_len_le P hVU)
            exact Rel.closure_hom (restrictEmbed P U V) wlMono _ y' z' hyz
          simp only [wl2V, Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap] at hwl2'
          obtain ⟨⟨x', y'⟩, hxy, ⟨y0, z'⟩, hyz, hm⟩ := hwl2'
          dsimp only at hm
          by_cases hyy : y' = y0
          · simp only [hyy, ite_true, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            subst hyy
            have hxyU := wlMono x' y' (by simpa [Rel.has, List.contains_iff_mem] using hxy)
            have hyzU := wlcMono y' z' (by simpa [Rel.has, List.contains_iff_mem] using hyz)
            simp only [Rel.has, List.contains_iff_mem] at hxyU hyzU
            have hwl2U : Rel.has (wlU.flatMap fun (x, y) =>
                (wlU.closure (P.restrict U).static.nodes.length).filterMap fun (y', z) =>
                  if y = y' then some (x, z) else none)
                (restrictEmbed P U V x') (restrictEmbed P U V z') = true := by
              simp only [Rel.has, List.contains_iff_mem, List.mem_flatMap, List.mem_filterMap]
              exact ⟨(restrictEmbed P U V x', restrictEmbed P U V y'), hxyU,
                (restrictEmbed P U V y', restrictEmbed P U V z'), hyzU, by simp⟩
            exact absurd hwl2U (by simpa [wlU] using hU)
          · simp [hyy] at hm

/-- `P` is closed under `valuesAt` when every external entry `(l, v)` of `P` has `v ∈ P.valuesAt l`
and every `atomicAdd(l, k)` in `P` maps `P.valuesAt l` into `P.valuesAt l` (satisfied in particular
by every kernel shape whose external list is empty and whose `atomicAdd` increments are `0`). -/
def Shape.valuesClosed (P : Shape) : Bool :=
  (P.external.all fun (l, v) => (P.valuesAt l).contains v) &&
  (P.threads.all fun th => th.prog.all fun e => match e with
    | .rmw l (.add k) => (P.valuesAt l).all fun v => (P.valuesAt l).contains (v + k)
    | _ => true)

theorem valuesClosed_of_addZero (P : Shape) (hExt : P.external = [])
    (hAdd : ∀ th ∈ P.threads, ∀ l k, Ev.rmw l (.add k) ∈ th.prog → k = 0) :
    P.valuesClosed = true := by
  simp only [Shape.valuesClosed, hExt, List.all_nil, Bool.true_and, List.all_eq_true]
  intro th hth e he
  cases e with
  | rmw l op =>
    cases op with
    | exchange _ => rfl
    | add k =>
      have hk0 := hAdd th hth l k he
      subst hk0
      simp only [List.all_eq_true, Nat.add_zero, List.contains_iff_mem]
      exact fun _ hv => hv
  | _ => rfl

private theorem wf_split {w : List Nat} {cs₁ cs₂ : List (List Nat)} (h : Wf w (cs₁ ++ cs₂)) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ Wf w₁ cs₁ ∧ Wf w₂ cs₂ := by
  induction cs₁ generalizing w with
  | nil => exact ⟨[], w, rfl, .nil, h⟩
  | cons _ _ ih =>
    cases h with
    | cons hx hrest =>
      obtain ⟨w₁, w₂, rfl, hw₁, hw₂⟩ := ih hrest
      exact ⟨_ :: w₁, w₂, rfl, .cons hx hw₁, hw₂⟩

private theorem wf_length {w : List Nat} {cs : List (List Nat)} (h : Wf w cs) :
    w.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem wf_getD_mem {w : List Nat} {cs : List (List Nat)} (h : Wf w cs)
    {i : Nat} (hi : i < cs.length) : w.getD i 0 ∈ cs.getD i [] := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hx _ ih =>
    cases i with
    | zero => simpa using hx
    | succ i =>
      simp only [List.length_cons] at hi
      simpa using ih (by omega)

private theorem wf_append {w₁ w₂ : List Nat} {cs₁ cs₂ : List (List Nat)}
    (h₁ : Wf w₁ cs₁) (h₂ : Wf w₂ cs₂) : Wf (w₁ ++ w₂) (cs₁ ++ cs₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hx _ ih => exact .cons hx ih

private theorem wf_map {xs : List Nat} (f : Nat → Nat) (g : Nat → List Nat)
    (h : ∀ x ∈ xs, f x ∈ g x) : Wf (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem wf_read_slot_mem (P : Shape) {w : List Nat} (hWf : Wf w P.spec)
    {r : Nat} (hr : r ∈ P.static.reads) :
    w.getD (posOf P.static.reads r) 0 ∈
      (0 :: ((P.static.writesAt r).filter (· != r)).map (· + 1) ++
        (P.static.externalAt r).map (P.static.nodes.length + 1 + ·)) := by
  obtain ⟨wRW, wM, rfl, hRW, _⟩ := wf_split hWf
  obtain ⟨wR, wW, rfl, hR, _⟩ := wf_split hRW
  obtain ⟨hlt, _⟩ := posOf_lt_and_map_getD (static_reads_strictInc P) id hr
  have hwRLen : wR.length = P.static.reads.length := by
    rw [wf_length hR, List.length_map]
  rw [List.append_assoc, getD_append_left _ _ _ (by omega)]
  have hltMap : posOf P.static.reads r < (P.static.reads.map fun r0 =>
      0 :: ((P.static.writesAt r0).filter (· != r0)).map (· + 1) ++
        (P.static.externalAt r0).map (P.static.nodes.length + 1 + ·)).length := by
    rw [List.length_map]; exact hlt
  have hmem := wf_getD_mem hR hltMap
  have hmapGet : (P.static.reads.map fun r0 =>
      0 :: ((P.static.writesAt r0).filter (· != r0)).map (· + 1) ++
        (P.static.externalAt r0).map (P.static.nodes.length + 1 + ·)).getD (posOf P.static.reads r) [] =
      (0 :: ((P.static.writesAt r).filter (· != r)).map (· + 1) ++
        (P.static.externalAt r).map (P.static.nodes.length + 1 + ·)) := by
    obtain ⟨_, heq⟩ := posOf_lt_and_map_getD (static_reads_strictInc P) (fun x => x) hr
    have hltId : posOf P.static.reads r < (P.static.reads.map fun x => x).length := by
      rw [List.length_map]; exact hlt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltMap,
      List.getElem_map, Option.getD_some]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltId,
      List.getElem_map, Option.getD_some] at heq
    rw [heq]
  rwa [hmapGet] at hmem

private theorem wf_ord_lt (P : Shape) {w : List Nat} (hWf : Wf w P.spec)
    {m : Nat} (hm : m ∈ P.static.mems) :
    P.static.ord w m < P.static.mems.length := by
  obtain ⟨wRW, wM, rfl, hRW, hM⟩ := wf_split hWf
  obtain ⟨wR, wW, rfl, hR, hW⟩ := wf_split hRW
  obtain ⟨hlt, _⟩ := posOf_lt_and_map_getD (static_mems_strictInc P) id hm
  have hwRLen : wR.length = P.static.reads.length := by rw [wf_length hR, List.length_map]
  have hwWLen : wW.length = P.static.writes.length := by rw [wf_length hW, List.length_map]
  unfold Static.ord
  rw [getD_append_right _ _ _ (by simp [hwRLen, hwWLen])]
  have hsub : P.static.reads.length + P.static.writes.length + posOf P.static.mems m -
      (wR ++ wW).length = posOf P.static.mems m := by simp [hwRLen, hwWLen]
  rw [hsub]
  have hltMap : posOf P.static.mems m <
      (P.static.mems.map fun _ => List.range P.static.mems.length).length := by
    rw [List.length_map]; exact hlt
  have hmem := wf_getD_mem hM hltMap
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltMap,
    List.getElem_map, Option.getD_some, List.mem_range] at hmem
  exact hmem

private theorem wf_rf_cases (P : Shape) {w : List Nat} (hWf : Wf w P.spec)
    {r : Nat} (hr : r ∈ P.static.reads) :
    match P.static.rf w r with
    | .init => True
    | .internal a => a ∈ P.static.writesAt r ∧ a ≠ r
    | .external v =>
      ∃ l, (P.nodes.getD r default).ev.loc? = some l ∧ (l, v) ∈ P.external := by
  have hslot := wf_read_slot_mem P hWf hr
  unfold Static.rf
  dsimp only
  rcases List.mem_append.mp hslot with h1 | h2
  · rcases List.mem_cons.mp h1 with h0 | hint
    · rw [h0]; simp
    · simp only [List.mem_map, List.mem_filter, bne_iff_ne] at hint
      obtain ⟨a, ⟨haAt, hne⟩, hk⟩ := hint
      have haLt : a < P.static.nodes.length :=
        ((mem_static_writes _).mp ((mem_static_writesAt _).mp haAt).1).1
      have hk0 : ¬ w.getD (posOf P.static.reads r) 0 = 0 := by omega
      have hkle : w.getD (posOf P.static.reads r) 0 ≤ P.static.nodes.length := by omega
      have hsub : w.getD (posOf P.static.reads r) 0 - 1 = a := by omega
      simp only [hk0, ite_false, hkle, ite_true, hsub]
      exact ⟨haAt, hne⟩
  · simp only [List.mem_map, Static.externalAt, List.mem_filter, List.mem_range] at h2
    obtain ⟨j, ⟨hjLt, hjLoc⟩, hk⟩ := h2
    have hk0 : ¬ w.getD (posOf P.static.reads r) 0 = 0 := by omega
    have hknle : ¬ w.getD (posOf P.static.reads r) 0 ≤ P.static.nodes.length := by omega
    have hsub : w.getD (posOf P.static.reads r) 0 - P.static.nodes.length - 1 = j := by omega
    simp only [hk0, hknle, ite_false, hsub]
    cases hrloc : (P.static.nodes.getD r default).ev.loc? with
    | none => rw [hrloc] at hjLoc; simp at hjLoc
    | some l =>
      rw [hrloc] at hjLoc
      cases hp : P.static.external.getD j default with
      | mk m v =>
        rw [hp] at hjLoc
        simp only [beq_iff_eq] at hjLoc
        subst m
        refine ⟨l, hrloc, ?_⟩
        have hmem := getD_mem_of_lt P.static.external default hjLt
        rw [hp] at hmem
        exact hmem

private theorem node_mem_thread_prog {th : Thread} {n : Node} (hn : n ∈ th.nodes) :
    n.ev ∈ th.prog := by
  simp only [Thread.nodes, List.mem_map, List.mem_range] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  exact getD_mem_of_lt th.prog (.barrier 0 []) hi

private theorem shape_node_ev_mem_prog (P : Shape) {a : Nat} (ha : a < P.nodes.length) :
    ∃ th ∈ P.threads, (P.nodes.getD a default).ev ∈ th.prog := by
  have hmem := getD_mem_of_lt P.nodes default ha
  simp only [Shape.nodes, List.mem_flatMap] at hmem
  obtain ⟨th, hth, hn⟩ := hmem
  exact ⟨th, hth, node_mem_thread_prog hn⟩

private theorem zero_mem_valuesAt (P : Shape) (l : Loc) : 0 ∈ P.valuesAt l := by
  simp [Shape.valuesAt]

private theorem write_mem_valuesAt (P : Shape) {th : Thread} (hth : th ∈ P.threads)
    {l : Loc} {v : Nat} {at_ : Bool} (he : Ev.write l v at_ ∈ th.prog) :
    v ∈ P.valuesAt l := by
  simp only [Shape.valuesAt, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_filterMap]
  exact Or.inl (Or.inr ⟨th, hth, .write l v at_, he, by simp⟩)

private theorem exchange_mem_valuesAt (P : Shape) {th : Thread} (hth : th ∈ P.threads)
    {l : Loc} {v : Nat} (he : Ev.rmw l (.exchange v) ∈ th.prog) :
    v ∈ P.valuesAt l := by
  simp only [Shape.valuesAt, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_filterMap]
  exact Or.inl (Or.inr ⟨th, hth, .rmw l (.exchange v), he, by simp⟩)

private theorem restrict_external_valuesAt (P : Shape) (U : Obj)
    (hClosed : P.valuesClosed = true) {l : Loc} {v : Nat}
    (hp : (l, v) ∈ (P.restrict U).external) : v ∈ P.valuesAt l := by
  simp only [Shape.valuesClosed, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hClosed
  simp only [Shape.restrict, List.mem_append, List.mem_flatMap, List.mem_filter] at hp
  rcases hp with hp | ⟨th, ⟨hth, _⟩, e, he, hm⟩
  · exact hClosed.1 (l, v) hp
  · cases e with
    | write m val at_ =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨hlm, rfl⟩ := hm
      subst m
      exact write_mem_valuesAt P hth he
    | rmw m op =>
      cases op with
      | exchange val =>
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨hlm, rfl⟩ := hm
        subst m
        exact exchange_mem_valuesAt P hth he
      | add k =>
        simp only [List.mem_map, Prod.mk.injEq] at hm
        obtain ⟨v0, hv0, hlm, rfl⟩ := hm
        subst m
        have hadd := hClosed.2 th hth (.rmw l (.add k)) he
        rw [List.all_eq_true] at hadd
        exact List.contains_iff_mem.mp (hadd v0 hv0)
    | read _ _ => simp at hm
    | barrier _ _ => simp at hm

private theorem valueOfWrite_mem_valuesAt (P : Shape) (U : Obj)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hWf : Wf wU (P.restrict U).spec) :
    ∀ (fuel a : Nat) {l : Loc}, a < (P.restrict U).nodes.length →
      ((P.restrict U).nodes.getD a default).ev.loc? = some l →
      (P.restrict U).static.valueOfWrite wU fuel a ∈ P.valuesAt l
  | 0, _, l, _, _ => zero_mem_valuesAt P l
  | fuel + 1, a, l, ha, hloc => by
    obtain ⟨th, hthU, he⟩ := shape_node_ev_mem_prog (P.restrict U) ha
    have hthP : th ∈ P.threads := (List.mem_filter.mp hthU).1
    unfold Static.valueOfWrite
    simp only [Shape.static]
    cases hev : ((P.restrict U).nodes.getD a default).ev with
    | write m val at_ =>
      rw [hev] at he hloc; injection hloc with hml; subst m
      exact write_mem_valuesAt P hthP he
    | read _ _ => exact zero_mem_valuesAt P l
    | barrier _ _ => exact zero_mem_valuesAt P l
    | rmw m op =>
      have hlocOrig := hloc
      rw [hev] at he hloc; injection hloc with hml; subst m
      cases op with
      | exchange val => exact exchange_mem_valuesAt P hthP he
      | add k =>
        have haR : a ∈ (P.restrict U).static.reads :=
          (mem_static_reads _).mpr ⟨ha, by rw [hev]; rfl⟩
        have hprev : (match (P.restrict U).static.rf wU a with
            | .init => 0
            | .internal b => (P.restrict U).static.valueOfWrite wU fuel b
            | .external v => v) ∈ P.valuesAt l := by
          have hrc := wf_rf_cases (P.restrict U) hWf haR
          cases hrf : (P.restrict U).static.rf wU a with
          | init => exact zero_mem_valuesAt P l
          | external v =>
            simp only [hrf] at hrc
            obtain ⟨l', hl', hp⟩ := hrc
            rw [hl'] at hlocOrig; injection hlocOrig with hll; subst l'
            exact restrict_external_valuesAt P U hClosed hp
          | internal b =>
            simp only [hrf] at hrc
            obtain ⟨hbAt, _⟩ := hrc
            rw [mem_static_writesAt] at hbAt
            have hbLt : b < (P.restrict U).nodes.length := ((mem_static_writes _).mp hbAt.1).1
            have hsl := hbAt.2
            simp only [Static.sameLoc, Shape.static, Node.sameLoc] at hsl
            rw [hlocOrig] at hsl
            cases hbloc : ((P.restrict U).nodes.getD b default).ev.loc? with
            | none => rw [hbloc] at hsl; simp at hsl
            | some mb =>
              rw [hbloc] at hsl; simp only [beq_iff_eq] at hsl; subst mb
              exact valueOfWrite_mem_valuesAt P U hClosed hWf fuel b hbLt hbloc
        simp only [Shape.valuesClosed, Bool.and_eq_true, List.all_eq_true] at hClosed
        have hadd := hClosed.2 th hthP (.rmw l (.add k)) he
        rw [List.all_eq_true] at hadd
        exact List.contains_iff_mem.mp (hadd _ hprev)

private theorem dropped_write_mem_external (P : Shape) {U V : Obj}
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hWf : Wf wU (P.restrict U).spec)
    {a : Nat} {l : Loc} (haW : a ∈ (P.restrict U).static.writes)
    (hloc : ((P.restrict U).nodes.getD a default).ev.loc? = some l)
    (hnone : (restrictEmbedList P U V).findIdx? (· == a) = none) :
    (l, (P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a) ∈
      (P.restrict V).external := by
  have haLt : a < (P.restrict U).nodes.length := ((mem_static_writes _).mp haW).1
  have hawEv : ((P.restrict U).nodes.getD a default).ev.isWrite = true :=
    ((mem_static_writes _).mp haW).2
  rcases filterBlocksIdx_mem_or_dropped Thread.nodes (fun th => Obj.le P (.thread th.id) V)
      (P.restrict U).threads default haLt with ⟨i, hi, heq⟩ | ⟨th, hthU, hnV, hmem⟩
  · exact absurd (findIdx?_eq_some_of_strictMono (restrictEmbedList P U V)
      (fun x y hxy hy => filterBlocksIdx_strictMono Thread.nodes _ _ hxy hy) hi heq)
      (by simp [hnone])
  · have hthP : th ∈ P.threads := (List.mem_filter.mp hthU).1
    have hevProg : ((P.restrict U).nodes.getD a default).ev ∈ th.prog := node_mem_thread_prog hmem
    have hnLenPos : ∃ f, (P.restrict U).static.nodes.length = f + 1 :=
      ⟨(P.restrict U).nodes.length - 1, by simp only [Shape.static]; omega⟩
    obtain ⟨f, hf⟩ := hnLenPos
    rw [hf]
    unfold Static.valueOfWrite
    change (l,
      match ((P.restrict U).nodes.getD a default).ev with
      | .write _ v _ => v
      | .rmw _ op =>
        op.apply (match (P.restrict U).static.rf wU a with
          | .init => 0
          | .internal b => (P.restrict U).static.valueOfWrite wU f b
          | .external v => v)
      | _ => 0) ∈ (P.restrict V).external
    have hExtEq : (P.restrict V).external =
        P.external ++ (P.threads.filter fun th => !Obj.le P (.thread th.id) V).flatMap fun th =>
          th.prog.flatMap fun e => match e with
            | .write l v _ => [(l, v)]
            | .rmw l (.exchange v) => [(l, v)]
            | .rmw l (.add k) => (P.valuesAt l).map fun v => (l, v + k)
            | _ => [] := rfl
    rw [hExtEq]
    simp only [List.mem_append, List.mem_flatMap, List.mem_filter]
    right
    refine ⟨th, ⟨hthP, by simp [hnV]⟩, ((P.restrict U).nodes.getD a default).ev, hevProg, ?_⟩
    cases hev : ((P.restrict U).nodes.getD a default).ev with
    | read _ _ => rw [hev] at hawEv; simp [Ev.isWrite] at hawEv
    | barrier _ _ => rw [hev] at hawEv; simp [Ev.isWrite] at hawEv
    | write m val at_ =>
      rw [hev] at hloc; injection hloc with hml; subst m
      simp
    | rmw m op =>
      have hlocOrig := hloc
      rw [hev] at hloc; injection hloc with hml; subst m
      cases op with
      | exchange val => simp [RmwOp.apply]
      | add k =>
        simp only [List.mem_map, Prod.mk.injEq, true_and]
        have haR : a ∈ (P.restrict U).static.reads :=
          (mem_static_reads _).mpr ⟨haLt, by rw [hev]; rfl⟩
        refine ⟨_, ?_, rfl⟩
        have hrc := wf_rf_cases (P.restrict U) hWf haR
        cases hrf : (P.restrict U).static.rf wU a with
        | init => exact zero_mem_valuesAt P l
        | external v =>
          simp only [hrf] at hrc
          obtain ⟨l', hl', hp⟩ := hrc
          rw [hl'] at hlocOrig; injection hlocOrig with hll; subst l'
          exact restrict_external_valuesAt P U hClosed hp
        | internal b =>
          simp only [hrf] at hrc
          obtain ⟨hbAt, _⟩ := hrc
          rw [mem_static_writesAt] at hbAt
          have hbLt : b < (P.restrict U).nodes.length := ((mem_static_writes _).mp hbAt.1).1
          have hsl := hbAt.2
          simp only [Static.sameLoc, Shape.static, Node.sameLoc] at hsl
          rw [hlocOrig] at hsl
          cases hbloc : ((P.restrict U).nodes.getD b default).ev.loc? with
          | none => rw [hbloc] at hsl; simp at hsl
          | some mb =>
            rw [hbloc] at hsl; simp only [beq_iff_eq] at hsl; subst mb
            exact valueOfWrite_mem_valuesAt P U hClosed hWf f b hbLt hbloc

private theorem extSlot_spec (P : Shape) (V : Obj) {r' : Nat} {l : Loc} (v : Nat)
    (hloc : ((P.restrict V).nodes.getD r' default).ev.loc? = some l)
    (hmem : (l, v) ∈ (P.restrict V).external) :
    let sV := (P.restrict V).static
    let k := match (sV.externalAt r').find? fun j => (sV.external.getD j default).2 == v with
      | some j => sV.nodes.length + 1 + j
      | none => sV.nodes.length + 1
    k ∈ (sV.externalAt r').map (sV.nodes.length + 1 + ·) ∧
    (if k = 0 then Src.init
     else if k ≤ sV.nodes.length then .internal (k - 1)
     else .external ((sV.external.getD (k - sV.nodes.length - 1) default).2)) = .external v := by
  rcases List.mem_iff_getElem.mp hmem with ⟨j0, hj0, heq0⟩
  have hj0At : j0 ∈ (P.restrict V).static.externalAt r' := by
    simp only [Static.externalAt, Shape.static, List.mem_filter, List.mem_range]
    refine ⟨hj0, ?_⟩
    rw [hloc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0, Option.getD_some, heq0]
    exact beq_self_eq_true l
  have hval0 : (((P.restrict V).static.external.getD j0 default).2 == v) = true := by
    simp [Shape.static, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0, heq0]
  have hisSome : (((P.restrict V).static.externalAt r').find?
      fun j => ((P.restrict V).static.external.getD j default).2 == v).isSome = true :=
    List.find?_isSome.mpr ⟨j0, hj0At, hval0⟩
  cases hf : ((P.restrict V).static.externalAt r').find?
      fun j => ((P.restrict V).static.external.getD j default).2 == v with
  | none => rw [hf] at hisSome; simp at hisSome
  | some j =>
    have hjMem := List.mem_of_find?_eq_some hf
    have hjVal : ((P.restrict V).static.external.getD j default).2 = v :=
      beq_iff_eq.mp (@List.find?_some _ (fun j => ((P.restrict V).static.external.getD j default).2 == v) _ _ hf)
    dsimp only
    simp only [hf]
    have hk0 : ¬ (P.restrict V).static.nodes.length + 1 + j = 0 := by omega
    have hknle : ¬ (P.restrict V).static.nodes.length + 1 + j ≤ (P.restrict V).static.nodes.length := by omega
    have hsub : (P.restrict V).static.nodes.length + 1 + j - (P.restrict V).static.nodes.length - 1 = j := by omega
    exact ⟨List.mem_map_of_mem hjMem, by simp only [hk0, hknle, ite_false, hsub, hjVal]⟩

/-- Well-formedness of `restrictWitness P U V wU` whenever `P.valuesClosed` and `Wf wU (P.restrict U).spec`. -/
theorem wf_restrictWitness (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hWf : Wf wU (P.restrict U).spec) :
    Wf (restrictWitness P U V wU) (P.restrict V).spec := by
  unfold restrictWitness Shape.spec Static.spec
  apply wf_append
  · apply wf_append
    · apply wf_map
      intro r' hr'
      have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
      have hrLocSome : ((P.restrict V).nodes.getD r' default).ev.loc?.isSome = true :=
        isRead_imp_loc_isSome ((mem_static_reads _).mp hr').2
      obtain ⟨l, hrloc⟩ := Option.isSome_iff_exists.mp hrLocSome
      have hrU : restrictEmbed P U V r' ∈ (P.restrict U).static.reads := restrictEmbed_reads P hVU hr'
      have hrlocU : ((P.restrict U).nodes.getD (restrictEmbed P U V r') default).ev.loc? = some l := by
        rwa [restrictEmbed_node P hVU hrLt]
      have hrc := wf_rf_cases (P.restrict U) hWf hrU
      dsimp only
      cases hrf : (P.restrict U).static.rf wU (restrictEmbed P U V r') with
      | init => simp
      | external v =>
        simp only [hrf] at hrc
        obtain ⟨l', hl', hpU⟩ := hrc
        rw [hl'] at hrlocU; injection hrlocU with hll; subst l'
        have hpV := restrict_external_subset P hVU hpU
        exact List.mem_append_right _ (extSlot_spec P V v hrloc hpV).1
      | internal a =>
        simp only [hrf] at hrc
        obtain ⟨haAt, hne⟩ := hrc
        have hg : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
            (a != restrictEmbed P U V r')) = true := by
          rw [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne]
          exact ⟨haAt, hne⟩
        simp only [hg, ite_true]
        cases hf : (restrictEmbedList P U V).findIdx? (· == a) with
        | some a' =>
          obtain ⟨ha'Lt, ha'Eq⟩ := findIdx?_restrictEmbed_some P hVU hf
          rw [← ha'Eq] at haAt hne
          have ha'At := writesAt_of_restrictEmbed P hVU hrLt ha'Lt haAt
          have ha'ne : a' ≠ r' := fun heq => hne (by rw [heq])
          apply List.mem_append_left
          apply List.mem_cons_of_mem
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ha'At, bne_iff_ne.mpr ha'ne⟩)
        | none =>
          have haW : a ∈ (P.restrict U).static.writes := ((mem_static_writesAt _).mp haAt).1
          have hsl := ((mem_static_writesAt _).mp haAt).2
          simp only [Static.sameLoc, Shape.static, Node.sameLoc] at hsl
          rw [hrlocU] at hsl
          cases haloc : ((P.restrict U).nodes.getD a default).ev.loc? with
          | none => rw [haloc] at hsl; simp at hsl
          | some la =>
            rw [haloc] at hsl; simp only [beq_iff_eq] at hsl; subst la
            have hpV := dropped_write_mem_external P hClosed hWf haW haloc hf
            exact List.mem_append_right _ (extSlot_spec P V _ hrloc hpV).1
    · apply wf_map
      intro w' hw'
      simp only [List.mem_range]
      have hlt := compress_lt_length (((P.restrict V).static.writesAt w').map (restrictEmbed P U V))
        ((P.restrict U).static.rank wU)
        (List.mem_map_of_mem (self_mem_writesAt (P.restrict V) hw'))
      simpa using hlt
  · apply wf_map
    intro m' hm'
    simp only [List.mem_range]
    have hlt := compress_lt_length ((P.restrict V).static.mems.map (restrictEmbed P U V))
      ((P.restrict U).static.ord wU) (List.mem_map_of_mem hm')
    simpa using hlt

/-- **Presheaf section restriction (Rung G4)**: every section over `U` restricts along `V ≤ U`
to a section over `V`. -/
theorem Section.restrict (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hSec : Section P U wU) :
    Section P V (restrictWitness P U V wU) :=
  ⟨wf_restrictWitness P hVU hClosed hSec.1, consistent_restrictWitness P hVU wU hSec.2⟩

private theorem rf_restrictWitness_wf (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hWf : Wf wU (P.restrict U).spec)
    {r' : Nat} (hr' : r' ∈ (P.restrict V).static.reads) :
    (P.restrict V).static.rf (restrictWitness P U V wU) r' =
      match (P.restrict U).static.rf wU (restrictEmbed P U V r') with
      | .init => .init
      | .internal a =>
        match (restrictEmbedList P U V).findIdx? (· == a) with
        | some a' => .internal a'
        | none => .external ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
      | .external v => .external v := by
  have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
  obtain ⟨l, hrloc⟩ := Option.isSome_iff_exists.mp (isRead_imp_loc_isSome ((mem_static_reads _).mp hr').2)
  have hrU : restrictEmbed P U V r' ∈ (P.restrict U).static.reads := restrictEmbed_reads P hVU hr'
  have hrlocU : ((P.restrict U).nodes.getD (restrictEmbed P U V r') default).ev.loc? = some l := by
    rwa [restrictEmbed_node P hVU hrLt]
  have hrc := wf_rf_cases (P.restrict U) hWf hrU
  change (let k := (restrictWitness P U V wU).getD (posOf (P.restrict V).static.reads r') 0
    if k = 0 then Src.init
    else if k ≤ (P.restrict V).static.nodes.length then .internal (k - 1)
    else .external (((P.restrict V).static.external.getD (k - (P.restrict V).static.nodes.length - 1) default).2)) = _
  rw [restrictWitness]
  dsimp only
  rw [getD_reads_slot (P.restrict V) _ _ _ hr']
  cases hrf : (P.restrict U).static.rf wU (restrictEmbed P U V r') with
  | init => simp
  | external v =>
    simp only [hrf] at hrc
    obtain ⟨l', hl', hpU⟩ := hrc
    rw [hl'] at hrlocU; injection hrlocU with hll; subst l'
    exact (extSlot_spec P V v hrloc (restrict_external_subset P hVU hpU)).2
  | internal a =>
    simp only [hrf] at hrc
    obtain ⟨haAt, hne⟩ := hrc
    have hg : (((P.restrict U).static.writesAt (restrictEmbed P U V r')).contains a &&
        (a != restrictEmbed P U V r')) = true := by
      rw [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne]
      exact ⟨haAt, hne⟩
    simp only [hg, ite_true]
    cases hf : (restrictEmbedList P U V).findIdx? (· == a) with
    | some a' =>
      obtain ⟨ha'Lt, _⟩ := findIdx?_restrictEmbed_some P hVU hf
      have hle : a' + 1 ≤ (P.restrict V).static.nodes.length := by simp only [Shape.static]; omega
      simp [hle]
    | none =>
      have haW : a ∈ (P.restrict U).static.writes := ((mem_static_writesAt _).mp haAt).1
      have hsl := ((mem_static_writesAt _).mp haAt).2
      simp only [Static.sameLoc, Shape.static, Node.sameLoc] at hsl
      rw [hrlocU] at hsl
      cases haloc : ((P.restrict U).nodes.getD a default).ev.loc? with
      | none => rw [haloc] at hsl; simp at hsl
      | some la =>
        rw [haloc] at hsl; simp only [beq_iff_eq] at hsl; subst la
        exact (extSlot_spec P V _ hrloc (dropped_write_mem_external P hClosed hWf haW haloc hf)).2

private theorem consistent_rf_ord_lt (Q : Shape) {w : List Nat} (hCons : Q.consistent w = true)
    {r b : Nat} (hr : r ∈ Q.static.reads) (hrf : Q.static.rf w r = .internal b) :
    Q.static.ord w b < Q.static.ord w r := by
  simp only [Shape.consistent, Static.consistent, Static.consistentWith, Bool.false_eq_true,
    ite_true, ite_false, List.append_nil, Bool.and_eq_true] at hCons
  have hAcyc := hCons.1.1.2
  rw [List.all_eq_true] at hAcyc
  have hmem : (b, r) ∈ Q.static.locord ++ Q.static.rfEdges w ++ Q.static.frEdges w ++ Q.static.asmoEdges w := by
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp only [Static.rfEdges, List.mem_filterMap]
    exact ⟨r, hr, by simp [hrf]⟩
  exact of_decide_eq_true (hAcyc (b, r) hmem)

private theorem valueOfWrite_eq_of_gt_ord (Q : Shape) {w : List Nat}
    (hWf : Wf w Q.spec) (hCons : Q.consistent w = true) :
    ∀ (k : Nat) {a fuel₁ fuel₂ : Nat},
      a ∈ Q.static.writes → Q.static.ord w a = k → k < fuel₁ → k < fuel₂ →
      Q.static.valueOfWrite w fuel₁ a = Q.static.valueOfWrite w fuel₂ a := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a fuel₁ fuel₂ ha hk hf₁ hf₂
    cases fuel₁ with
    | zero => omega
    | succ f₁ =>
      cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        unfold Static.valueOfWrite
        cases hev : (Q.static.nodes.getD a default).ev with
        | write _ _ _ => rfl
        | read _ _ => rfl
        | barrier _ _ => rfl
        | rmw _ op =>
          have haLt : a < Q.nodes.length := ((mem_static_writes _).mp ha).1
          have haR : a ∈ Q.static.reads :=
            (mem_static_reads _).mpr ⟨haLt, by have hev' : (Q.nodes.getD a default).ev = _ := hev; rw [hev']; rfl⟩
          have hrc := wf_rf_cases Q hWf haR
          cases hrf : Q.static.rf w a with
          | init => rfl
          | external _ => rfl
          | internal b =>
            simp only [hrf] at hrc
            have hbW : b ∈ Q.static.writes := ((mem_static_writesAt _).mp hrc.1).1
            have hltOrd : Q.static.ord w b < k := by rw [← hk]; exact consistent_rf_ord_lt Q hCons haR hrf
            dsimp only
            rw [ih (Q.static.ord w b) hltOrd (fuel₁ := f₁) (fuel₂ := f₂) hbW rfl (by omega) (by omega)]

private theorem mems_length_le_nodes (Q : Shape) : Q.static.mems.length ≤ Q.static.nodes.length := by
  have h := filter_length_le_of_imp (List.range Q.nodes.length)
    (fun a => (Q.nodes.getD a default).ev.loc?.isSome) (fun _ => true) (fun _ _ _ => rfl)
  rw [filter_true_eq, List.length_range] at h
  exact h

/-- Write values are preserved under `restrictWitness` for consistent well-formed sections. -/
theorem valueOfWrite_restrictWitness (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hSec : Section P U wU)
    {a' : Nat} (ha' : a' ∈ (P.restrict V).static.writes) :
    (P.restrict V).static.valueOfWrite (restrictWitness P U V wU)
        (P.restrict V).static.nodes.length a' =
      (P.restrict U).static.valueOfWrite wU
        (P.restrict U).static.nodes.length (restrictEmbed P U V a') := by
  have hSecV := Section.restrict P hVU hClosed hSec
  suffices hrec : ∀ (k : Nat) {x' : Nat},
      x' ∈ (P.restrict V).static.writes →
      (P.restrict V).static.ord (restrictWitness P U V wU) x' = k →
      (P.restrict V).static.valueOfWrite (restrictWitness P U V wU)
          (P.restrict V).static.nodes.length x' =
        (P.restrict U).static.valueOfWrite wU
          (P.restrict U).static.nodes.length (restrictEmbed P U V x') from
    hrec _ ha' rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x' hx' hk
    have hxLt : x' < (P.restrict V).nodes.length := ((mem_static_writes _).mp hx').1
    have hxU : restrictEmbed P U V x' ∈ (P.restrict U).static.writes := restrictEmbed_writes P hVU hx'
    have hOrdVLt : k < (P.restrict V).static.nodes.length := by
      have h1 := wf_ord_lt (P.restrict V) hSecV.1 (writes_subset_mems _ hx')
      have h2 := mems_length_le_nodes (P.restrict V)
      omega
    have hOrdULt : (P.restrict U).static.ord wU (restrictEmbed P U V x') <
        (P.restrict U).static.nodes.length := by
      have h1 := wf_ord_lt (P.restrict U) hSec.1 (writes_subset_mems _ hxU)
      have h2 := mems_length_le_nodes (P.restrict U)
      omega
    rw [valueOfWrite_eq_of_gt_ord (P.restrict V) hSecV.1 hSecV.2 k hx' hk hOrdVLt (Nat.lt_succ_self k),
      valueOfWrite_eq_of_gt_ord (P.restrict U) hSec.1 hSec.2 _ hxU rfl hOrdULt (Nat.lt_succ_self _)]
    unfold Static.valueOfWrite
    have hnode : ((P.restrict U).static.nodes.getD (restrictEmbed P U V x') default) =
        ((P.restrict V).static.nodes.getD x' default) := restrictEmbed_node P hVU hxLt
    rw [hnode]
    cases hev : ((P.restrict V).static.nodes.getD x' default).ev with
    | write _ _ _ => rfl
    | read _ _ => rfl
    | barrier _ _ => rfl
    | rmw _ op =>
      have hxR : x' ∈ (P.restrict V).static.reads :=
        (mem_static_reads _).mpr ⟨hxLt, by have hev' : ((P.restrict V).nodes.getD x' default).ev = _ := hev; rw [hev']; rfl⟩
      have hxRU : restrictEmbed P U V x' ∈ (P.restrict U).static.reads := restrictEmbed_reads P hVU hxR
      rw [rf_restrictWitness_wf P hVU hClosed hSec.1 hxR]
      have hrc := wf_rf_cases (P.restrict U) hSec.1 hxRU
      cases hrfU : (P.restrict U).static.rf wU (restrictEmbed P U V x') with
      | init => rfl
      | external _ => rfl
      | internal b =>
        simp only [hrfU] at hrc ⊢
        have hbW : b ∈ (P.restrict U).static.writes := ((mem_static_writesAt _).mp hrc.1).1
        have hltOrdU := consistent_rf_ord_lt (P.restrict U) hSec.2 hxRU hrfU
        cases hf : (restrictEmbedList P U V).findIdx? (· == b) with
        | none =>
          dsimp only
          congr 1
          exact (valueOfWrite_eq_of_gt_ord (P.restrict U) hSec.1 hSec.2 _
            (fuel₁ := (P.restrict U).static.ord wU (restrictEmbed P U V x'))
            (fuel₂ := (P.restrict U).static.nodes.length)
            hbW rfl hltOrdU (by omega)).symm
        | some b' =>
          dsimp only
          congr 1
          obtain ⟨hb'Lt, hb'Eq⟩ := findIdx?_restrictEmbed_some P hVU hf
          rw [← hb'Eq] at hrc hrfU hltOrdU hbW ⊢
          have hb'At := writesAt_of_restrictEmbed P hVU hxLt hb'Lt hrc.1
          have hb'W : b' ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp hb'At).1
          have hrfV : (P.restrict V).static.rf (restrictWitness P U V wU) x' = .internal b' := by
            rw [rf_restrictWitness_wf P hVU hClosed hSec.1 hxR, hrfU]
            dsimp only
            rw [findIdx?_restrictEmbed_of_eq P hVU hb'Lt]
          have hltOrdV : (P.restrict V).static.ord (restrictWitness P U V wU) b' < k := by
            rw [← hk]; exact consistent_rf_ord_lt (P.restrict V) hSecV.2 hxR hrfV
          have hb'OrdLt : (P.restrict V).static.ord (restrictWitness P U V wU) b' <
              (P.restrict V).static.nodes.length := by
            have := wf_ord_lt (P.restrict V) hSecV.1 (writes_subset_mems _ hb'W)
            have := mems_length_le_nodes (P.restrict V)
            omega
          rw [valueOfWrite_eq_of_gt_ord (P.restrict V) hSecV.1 hSecV.2 _
              (fuel₁ := k) (fuel₂ := (P.restrict V).static.nodes.length)
              hb'W rfl hltOrdV hb'OrdLt,
            ih _ hltOrdV hb'W rfl,
            (valueOfWrite_eq_of_gt_ord (P.restrict U) hSec.1 hSec.2 _
              (fuel₁ := (P.restrict U).static.ord wU (restrictEmbed P U V x'))
              (fuel₂ := (P.restrict U).static.nodes.length)
              hbW rfl hltOrdU (by omega)).symm]

/-- Read values are preserved under `restrictWitness` for consistent well-formed sections. -/
theorem valueOfRead_restrictWitness (P : Shape) {U V : Obj} (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hSec : Section P U wU)
    {r' : Nat} (hr' : r' ∈ (P.restrict V).static.reads) :
    (P.restrict V).static.valueOfRead (restrictWitness P U V wU) r' =
      (P.restrict U).static.valueOfRead wU (restrictEmbed P U V r') := by
  have hrLt : r' < (P.restrict V).nodes.length := ((mem_static_reads _).mp hr').1
  have hrU : restrictEmbed P U V r' ∈ (P.restrict U).static.reads := restrictEmbed_reads P hVU hr'
  have hrc := wf_rf_cases (P.restrict U) hSec.1 hrU
  unfold Static.valueOfRead
  rw [rf_restrictWitness_wf P hVU hClosed hSec.1 hr']
  cases hrfU : (P.restrict U).static.rf wU (restrictEmbed P U V r') with
  | init => rfl
  | external _ => rfl
  | internal a =>
    simp only [hrfU] at hrc ⊢
    cases hf : (restrictEmbedList P U V).findIdx? (· == a) with
    | none => rfl
    | some a' =>
      dsimp only
      obtain ⟨ha'Lt, ha'Eq⟩ := findIdx?_restrictEmbed_some P hVU hf
      rw [← ha'Eq] at hrc ⊢
      have ha'At := writesAt_of_restrictEmbed P hVU hrLt ha'Lt hrc.1
      have ha'W : a' ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp ha'At).1
      exact valueOfWrite_restrictWitness P hVU hClosed hSec ha'W

theorem restrictEmbedList_comp (P : Shape) {U V W : Obj}
    (hWV : Obj.le P W V = true) (hVU : Obj.le P V U = true) :
    (restrictEmbedList P V W).map (restrictEmbed P U V) = restrictEmbedList P U W := by
  unfold restrictEmbedList restrictEmbed
  rw [restrict_threads_eq_filter P hVU]
  exact filterBlocksIdx_comp Thread.nodes _ _ _ (fun th _ hW => le_trans P hW hWV)

theorem restrictEmbed_comp (P : Shape) {U V W : Obj}
    (hWV : Obj.le P W V = true) (hVU : Obj.le P V U = true)
    {a'' : Nat} (ha'' : a'' < (P.restrict W).nodes.length) :
    restrictEmbed P U V (restrictEmbed P V W a'') = restrictEmbed P U W a'' := by
  have hlen : a'' < (restrictEmbedList P V W).length := by rwa [restrictEmbedList_length P hWV]
  have hmap := congrArg (fun l => l.getD a'' 0) (restrictEmbedList_comp P hWV hVU)
  simpa [restrictEmbed, List.getD_eq_getElem?_getD, hlen] using hmap

/-- **Functoriality of `restrictWitness` along `W ≤ V ≤ U` (Rung G4 presheaf composition law)**. -/
theorem restrictWitness_comp (P : Shape) {U V W : Obj}
    (hWV : Obj.le P W V = true) (hVU : Obj.le P V U = true)
    (hClosed : P.valuesClosed = true) {wU : List Nat} (hSec : Section P U wU) :
    restrictWitness P V W (restrictWitness P U V wU) = restrictWitness P U W wU := by
  have hWU : Obj.le P W U = true := le_trans P hWV hVU
  have hSecV : Section P V (restrictWitness P U V wU) := Section.restrict P hVU hClosed hSec
  have hrfV_lem : ∀ {r' : Nat}, r' ∈ (P.restrict V).static.reads →
      (P.restrict V).static.rf (restrictWitness P U V wU) r' =
        match (P.restrict U).static.rf wU (restrictEmbed P U V r') with
        | .init => .init
        | .internal a =>
          match (restrictEmbedList P U V).findIdx? (· == a) with
          | some a' => .internal a'
          | none => .external ((P.restrict U).static.valueOfWrite wU (P.restrict U).static.nodes.length a)
        | .external v => .external v :=
    fun hr' => rf_restrictWitness_wf P hVU hClosed hSec.1 hr'
  have hvalV_lem : ∀ {a' : Nat}, a' ∈ (P.restrict V).static.writes →
      (P.restrict V).static.valueOfWrite (restrictWitness P U V wU)
          (P.restrict V).static.nodes.length a' =
        (P.restrict U).static.valueOfWrite wU
          (P.restrict U).static.nodes.length (restrictEmbed P U V a') :=
    fun ha' => valueOfWrite_restrictWitness P hVU hClosed hSec ha'
  have hrankV_lem : ∀ {a' : Nat}, a' ∈ (P.restrict V).static.writes →
      (P.restrict V).static.rank (restrictWitness P U V wU) a' =
        Static.compress (((P.restrict V).static.writesAt a').map (restrictEmbed P U V))
          ((P.restrict U).static.rank wU) (restrictEmbed P U V a') :=
    fun ha' => rank_restrictWitness P wU ha'
  have hordV_lem : ∀ {m' : Nat}, m' ∈ (P.restrict V).static.mems →
      (P.restrict V).static.ord (restrictWitness P U V wU) m' =
        Static.compress ((P.restrict V).static.mems.map (restrictEmbed P U V))
          ((P.restrict U).static.ord wU) (restrictEmbed P U V m') :=
    fun hm' => ord_restrictWitness P wU hm'
  generalize hwV : restrictWitness P U V wU = wV at hSecV hrfV_lem hvalV_lem hrankV_lem hordV_lem ⊢
  unfold restrictWitness
  dsimp only
  congr 1
  · congr 1
    · -- 1. Reads slots
      apply List.map_congr_left
      intro r'' hr''
      have hr''Lt : r'' < (P.restrict W).nodes.length := ((mem_static_reads _).mp hr'').1
      have hr'R : restrictEmbed P V W r'' ∈ (P.restrict V).static.reads := restrictEmbed_reads P hWV hr''
      have hrComp := restrictEmbed_comp P hWV hVU hr''Lt
      have hrUR : restrictEmbed P U W r'' ∈ (P.restrict U).static.reads := restrictEmbed_reads P hWU hr''
      have hrcU := wf_rf_cases (P.restrict U) hSec.1 hrUR
      have hrcV := wf_rf_cases (P.restrict V) hSecV.1 hr'R
      have hrfV := hrfV_lem hr'R
      rw [hrComp] at hrfV
      cases hrfU : (P.restrict U).static.rf wU (restrictEmbed P U W r'') with
      | init =>
        rw [hrfU] at hrfV; dsimp only at hrfV
        rw [hrfV]
      | external v =>
        rw [hrfU] at hrfV; dsimp only at hrfV
        rw [hrfV]
      | internal a =>
        rw [hrfU] at hrcU hrfV
        dsimp only at hrfV
        obtain ⟨haAt, hne⟩ := hrcU
        have hgU : (((P.restrict U).static.writesAt (restrictEmbed P U W r'')).contains a &&
            (a != restrictEmbed P U W r'')) = true := by
          rw [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne]
          exact ⟨haAt, hne⟩
        simp only [hgU, ite_true]
        cases hfUV : (restrictEmbedList P U V).findIdx? (· == a) with
        | none =>
          rw [hfUV] at hrfV; dsimp only at hrfV
          have hfUW : (restrictEmbedList P U W).findIdx? (· == a) = none := by
            cases h : (restrictEmbedList P U W).findIdx? (· == a) with
            | none => rfl
            | some a'' =>
              obtain ⟨ha''Lt, ha''Eq⟩ := findIdx?_restrictEmbed_some P hWU h
              rw [← restrictEmbed_comp P hWV hVU ha''Lt] at ha''Eq
              have ha'Lt := restrictEmbed_lt P hWV ha''Lt
              have hsome := findIdx?_restrictEmbed_of_eq P hVU ha'Lt
              rw [ha''Eq] at hsome
              rw [hsome] at hfUV; simp at hfUV
          rw [hrfV, hfUW]
        | some a' =>
          rw [hfUV] at hrfV; dsimp only at hrfV
          rw [hrfV] at hrcV
          obtain ⟨ha'At, ha'ne⟩ := hrcV
          have hgV : (((P.restrict V).static.writesAt (restrictEmbed P V W r'')).contains a' &&
              (a' != restrictEmbed P V W r'')) = true := by
            rw [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne]
            exact ⟨ha'At, ha'ne⟩
          obtain ⟨ha'Lt, ha'Eq⟩ := findIdx?_restrictEmbed_some P hVU hfUV
          cases hfVW : (restrictEmbedList P V W).findIdx? (· == a') with
          | some a'' =>
            obtain ⟨ha''Lt, ha''Eq⟩ := findIdx?_restrictEmbed_some P hWV hfVW
            have ha''UW : restrictEmbed P U W a'' = a := by
              rw [← restrictEmbed_comp P hWV hVU ha''Lt, ha''Eq, ha'Eq]
            have hfUW : (restrictEmbedList P U W).findIdx? (· == a) = some a'' := by
              rw [← ha''UW]; exact findIdx?_restrictEmbed_of_eq P hWU ha''Lt
            rw [hrfV]; dsimp only; simp only [hgV, ite_true, hfVW, hfUW]
          | none =>
            have hfUW : (restrictEmbedList P U W).findIdx? (· == a) = none := by
              cases h : (restrictEmbedList P U W).findIdx? (· == a) with
              | none => rfl
              | some a'' =>
                obtain ⟨ha''Lt, ha''Eq⟩ := findIdx?_restrictEmbed_some P hWU h
                rw [← restrictEmbed_comp P hWV hVU ha''Lt, ← ha'Eq] at ha''Eq
                have heq' := restrictEmbed_inj P hVU (restrictEmbed_lt P hWV ha''Lt) ha'Lt ha''Eq
                have hsome := findIdx?_restrictEmbed_of_eq P hWV ha''Lt
                rw [heq'] at hsome
                rw [hsome] at hfVW; simp at hfVW
            have ha'W : a' ∈ (P.restrict V).static.writes := ((mem_static_writesAt _).mp ha'At).1
            have hvalEq := hvalV_lem ha'W
            rw [ha'Eq] at hvalEq
            rw [hrfV]; dsimp only; simp only [hgV, ite_true, hfVW, hfUW, hvalEq]
    · -- 2. Writes (rank) slots
      apply List.map_congr_left
      intro w'' hw''
      have hw''Lt : w'' < (P.restrict W).nodes.length := ((mem_static_writes _).mp hw'').1
      have hRankCongr : Static.compress
          (((P.restrict W).static.writesAt w'').map (restrictEmbed P V W))
          ((P.restrict V).static.rank wV) (restrictEmbed P V W w'') =
        Static.compress
          (((P.restrict W).static.writesAt w'').map (restrictEmbed P V W))
          (fun z => Static.compress (((P.restrict V).static.writesAt (restrictEmbed P V W w'')).map
            (restrictEmbed P U V)) ((P.restrict U).static.rank wU) (restrictEmbed P U V z))
          (restrictEmbed P V W w'') := by
        have hEqOn : ∀ z ∈ ((P.restrict W).static.writesAt w'').map (restrictEmbed P V W),
            (P.restrict V).static.rank wV z =
              Static.compress (((P.restrict V).static.writesAt (restrictEmbed P V W w'')).map
                (restrictEmbed P U V)) ((P.restrict U).static.rank wU) (restrictEmbed P U V z) := by
          intro z hz
          rcases List.mem_map.mp hz with ⟨z'', hz'', rfl⟩
          have hz'At := restrictEmbed_writesAt P hWV hw''Lt hz''
          have hz'W : restrictEmbed P V W z'' ∈ (P.restrict V).static.writes :=
            ((mem_static_writesAt _).mp hz'At).1
          have hsl := ((mem_static_writesAt _).mp hz'At).2
          rw [hrankV_lem hz'W, writesAt_eq_of_sameLoc _ hsl]
        have hSelfMem : restrictEmbed P V W w'' ∈
            ((P.restrict W).static.writesAt w'').map (restrictEmbed P V W) :=
          List.mem_map_of_mem (self_mem_writesAt _ hw'')
        exact compress_congr_on _ _ _ hSelfMem hEqOn
      rw [hRankCongr, compress_comp _ _ (restrictEmbed P U V) ((P.restrict U).static.rank wU)]
      · rw [List.map_map, restrictEmbed_comp P hWV hVU hw''Lt]
        congr 1
        apply List.map_congr_left
        intro z'' hz''
        exact restrictEmbed_comp P hWV hVU
          (((mem_static_writes _).mp ((mem_static_writesAt _).mp hz'').1).1)
      · intro z hz
        rcases List.mem_map.mp hz with ⟨z'', hz'', rfl⟩
        exact List.mem_map_of_mem (restrictEmbed_writesAt P hWV hw''Lt hz'')
      · exact List.mem_map_of_mem (self_mem_writesAt _ hw'')
  · -- 3. Mems (ord) slots
    apply List.map_congr_left
    intro m'' hm''
    have hm''Lt : m'' < (P.restrict W).nodes.length := ((mem_static_mems _).mp hm'').1
    have hOrdCongr : Static.compress
        ((P.restrict W).static.mems.map (restrictEmbed P V W))
        ((P.restrict V).static.ord wV) (restrictEmbed P V W m'') =
      Static.compress
        ((P.restrict W).static.mems.map (restrictEmbed P V W))
        (fun z => Static.compress ((P.restrict V).static.mems.map (restrictEmbed P U V))
          ((P.restrict U).static.ord wU) (restrictEmbed P U V z))
        (restrictEmbed P V W m'') := by
      have hEqOn : ∀ z ∈ (P.restrict W).static.mems.map (restrictEmbed P V W),
          (P.restrict V).static.ord wV z =
            Static.compress ((P.restrict V).static.mems.map (restrictEmbed P U V))
              ((P.restrict U).static.ord wU) (restrictEmbed P U V z) := by
        intro z hz
        rcases List.mem_map.mp hz with ⟨z'', hz'', rfl⟩
        exact hordV_lem (restrictEmbed_mems P hWV hz'')
      have hSelfMem : restrictEmbed P V W m'' ∈ (P.restrict W).static.mems.map (restrictEmbed P V W) :=
        List.mem_map_of_mem hm''
      exact compress_congr_on _ _ _ hSelfMem hEqOn
    rw [hOrdCongr, compress_comp _ _ (restrictEmbed P U V) ((P.restrict U).static.ord wU)]
    · rw [List.map_map, restrictEmbed_comp P hWV hVU hm''Lt]
      congr 1
      apply List.map_congr_left
      intro z'' hz''
      exact restrictEmbed_comp P hWV hVU (((mem_static_mems _).mp hz'').1)
    · intro z hz
      rcases List.mem_map.mp hz with ⟨z'', hz'', rfl⟩
      exact List.mem_map_of_mem (restrictEmbed_mems P hWV hz'')
    · exact List.mem_map_of_mem hm''

end Obend.Hardware.Gpu.Memory
