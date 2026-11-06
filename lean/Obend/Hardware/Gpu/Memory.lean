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
`le_trans`; `restrictObs_comp` (the observation presheaf). Checked, not proved: that `consistent` agrees
with Dartagnan under `vulkan.cat` on the suite's shapes and outcomes, a table the gate regenerates; that
the devices never show a forbidden outcome and show (or are recorded stronger than) the allowed weak
ones, the tables under `hardware/gpu/litmus/results/`. That the section functor restricts along `Obj.le`
(a consistent device witness restricts to a consistent workgroup witness) is a statement about the
closure computation this file does not prove; the executable checks it on the suite's shapes
(`obend-litmus-check restrict`), and it is named here as the open proof of this rung.

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

end Obend.Hardware.Gpu.Memory
