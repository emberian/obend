module
public import Obend.Hardware.ArrayHypergraph
public import Obend.Hardware.ArrayKernelUnique
@[expose] public section

/-!
Array maps with several results per invocation. Index expressions make gather and
scatter parametric instead of storing one index per element. A phase reads its
input arrays, runs an ordinary `ElemOp` register program, and scatters its results.
Phases compose at a uniform workgroup barrier; dispatches compose at the device.
There is no FFT, field arithmetic, or device instruction in this source language.
-/
namespace Obend.Hardware.ArrayKernel
open Obend.Hardware.ArrayHypergraph
set_option autoImplicit false

inductive Ix where
  | lit (n : Nat)
  | group
  | lane
  | add (a b : Ix)
  | mul (a b : Ix)
  | div (a : Ix) (n : Nat)
  | mod (a : Ix) (n : Nat)
  deriving DecidableEq, Repr

def Ix.eval (g l : Nat) : Ix → Nat
  | .lit n => n
  | .group => g
  | .lane => l
  | .add a b => a.eval g l + b.eval g l
  | .mul a b => a.eval g l * b.eval g l
  | .div a n => a.eval g l / n
  | .mod a n => a.eval g l % n

/-- WGSL indices are u32. Check every intermediate, including expressions whose
final modulo would hide an overflowing multiplication. -/
def Ix.u32Safe (g l : Nat) : Ix → Bool
  | .lit n => n < 2^32
  | .group => g < 2^32
  | .lane => l < 2^32
  | .add a b => a.u32Safe g l && b.u32Safe g l && a.eval g l + b.eval g l < 2^32
  | .mul a b => a.u32Safe g l && b.u32Safe g l && a.eval g l * b.eval g l < 2^32
  | .div a n => a.u32Safe g l && 0 < n && n < 2^32
  | .mod a n => a.u32Safe g l && 0 < n && n < 2^32

/-- Even unreachable shader expressions must have valid u32 literals and
nonzero divisors. This check is independent of the invocation domain. -/
def Ix.syntaxSafe : Ix → Bool
  | .lit n => n < 2^32
  | .group | .lane => true
  | .add a b | .mul a b => a.syntaxSafe && b.syntaxSafe
  | .div a n | .mod a n => a.syntaxSafe && 0 < n && n < 2^32

inductive Storage where
  | device | shared | constant
  deriving DecidableEq, Repr

structure Buffer where
  size : Nat
  storage : Storage
  values : List Word := []
  deriving Repr

instance : Inhabited Buffer := ⟨⟨0, .device, []⟩⟩

structure Read where
  dst : Nat
  array : Nat
  index : Ix
  deriving DecidableEq, Repr

structure Write where
  array : Nat
  index : Ix
  value : Nat
  deriving DecidableEq, Repr

structure Phase where
  lanes : Nat
  reads : List Read
  code : List Instr
  writes : List Write
  deriving Repr

structure Dispatch where
  groups : Nat
  phases : List Phase
  deriving Repr

structure Program where
  buffers : List Buffer
  inputs : List Nat
  outputs : List Nat
  dispatches : List Dispatch
  deriving Repr

abbrev Memory := Array (Array Word)
abbrev Registers := Std.HashMap Nat Word

/-- Loads are interpreted against the phase's immutable input snapshot. -/
def loadRegisters (p : Phase) (mem : Memory) (group lane : Nat) : Registers :=
  p.reads.foldl (fun regs r => regs.insert r.dst
    ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) ∅

def runRegisters (code : List Instr) (regs : Registers) : Registers :=
  code.foldl (fun m i => m.insert i.dst
    (evalElemOp i.op (i.args.map fun a => m.getD a 0#64))) regs

/-- Every result of a multi-output map is the existing elementwise language's
semantics, with the same loaded inputs; sharing is execution, not duplication. -/
theorem runRegisters_sound (code : List Instr) (regs : Registers) (out : Nat) :
    (runRegisters code regs).getD out 0#64 =
      runCode (fun a => regs.getD a 0#64) code out :=
  runCode_hashMap code regs out

def laneWrites (p : Phase) (mem : Memory) (group lane : Nat) : List (Nat × Nat × Word) :=
  let regs := runRegisters p.code (loadRegisters p mem group lane)
  p.writes.map fun w => (w.array, w.index.eval group lane, regs.getD w.value 0#64)

def applyWrite (mem : Memory) (w : Nat × Nat × Word) : Memory :=
  mem.modify w.1 fun xs => xs.setIfInBounds w.2.1 w.2.2

/-- Denotation of a simultaneous array map. Race freedom is a separate condition,
not the assertion that an arbitrary GPU follows this deterministic order. -/
def evalPhase (p : Phase) (group : Nat) (mem : Memory) : Memory :=
  let writes := (List.range p.lanes).flatMap (laneWrites p mem group)
  writes.foldl applyWrite mem

def evalGroup (d : Dispatch) (group : Nat) (mem : Memory) : Memory :=
  d.phases.foldl (fun m p => evalPhase p group m) mem

def evalDispatch (d : Dispatch) (mem : Memory) : Memory :=
  (List.range d.groups).foldl (fun m group => evalGroup d group m) mem

def evalProgram (p : Program) (mem : Memory) : Memory :=
  p.dispatches.foldl (fun m d => evalDispatch d m) mem

def initialMemory (p : Program) (inputs : List (Array Word)) : Memory := Id.run do
  let mut mem := p.buffers.toArray.map fun b =>
    if b.storage == .constant then b.values.toArray else Array.replicate b.size 0#64
  for (id, vals) in p.inputs.zip inputs do
    mem := mem.setIfInBounds id vals
  return mem

/-- A phase never modifies one of its input arrays. This makes the source
snapshot implementable with load/compute/store and one uniform trailing barrier. -/
def Phase.separated (p : Phase) : Bool :=
  p.writes.all fun w => p.reads.all fun r => w.array != r.array

def Phase.closed (p : Phase) : Bool := Id.run do
  let mut names := p.reads.map (·.dst)
  if !names.Nodup then return false
  for i in p.code do
    if names.contains i.dst || !i.args.all names.contains then return false
    names := i.dst :: names
  return p.writes.all fun w => names.contains w.value

def Program.geometrySafe (p : Program) : Bool :=
  [Storage.device, .shared, .constant].all (fun space =>
    p.buffers.foldl (fun (n : Nat) b => if b.storage == space then n+b.size else n) 0 < 2^32) &&
  p.dispatches.all (fun d => d.groups*64 < 2^32 && d.groups ≤ 65535*32768 &&
    d.phases.all (fun ph => ph.lanes ≤ 2^32-64))

def Program.accessSafe (p : Program) (g l a : Nat) (i : Ix) : Bool :=
  a < p.buffers.length && i.u32Safe g l &&
    i.eval g l < (p.buffers.getD a default).size

/-- Pure finite bounds certificate, kept separate from the ownership hash sets
so its logical content has a direct, universal elimination theorem. -/
def Program.boundsSafe (p : Program) : Bool :=
  p.dispatches.all fun d => (List.range d.groups).all fun g =>
    d.phases.all fun ph => (List.range ph.lanes).all fun l =>
      ph.reads.all (fun r => p.accessSafe g l r.array r.index) &&
      ph.writes.all (fun w => p.accessSafe g l w.array w.index)

def Phase.writeAddresses (ph : Phase) (g : Nat) : List (Nat × Nat) :=
  (List.range ph.lanes).flatMap fun l =>
    ph.writes.map fun w => (w.array, w.index.eval g l)

def Dispatch.deviceReadArrays (p : Program) (d : Dispatch) : List Nat :=
  d.phases.flatMap fun ph => ph.reads.filterMap fun r =>
    if (p.buffers.getD r.array default).storage == .device then some r.array else none

def Dispatch.deviceWriteAddresses (p : Program) (d : Dispatch) : List (Nat × Nat) :=
  (List.range d.groups).flatMap fun g => d.phases.flatMap fun ph =>
    (List.range ph.lanes).flatMap fun l => ph.writes.filterMap fun w =>
      if (p.buffers.getD w.array default).storage == .device then
        some (w.array, w.index.eval g l) else none

/-- The pure scatter admission predicate uses a proved hash-set checker. Device
writes are unique over the entire dispatch: this conservative rule also excludes
same-group rewrites in later phases. Shared arrays may be rewritten after barriers.
-/
def Program.ownershipSafe (p : Program) : Bool :=
  p.dispatches.all fun d =>
    let deviceWrites := d.deviceWriteAddresses p
    let deviceReads := d.deviceReadArrays p
    d.phases.all (·.separated) &&
    ((List.range d.groups).all fun g => d.phases.all fun ph =>
      Unique.checkUnique (ph.writeAddresses g)) &&
    Unique.checkUnique deviceWrites &&
    deviceWrites.all (fun loc => !deviceReads.contains loc.1)

/-- Addresses and ownership are checked without materializing arithmetic values
or a quadratic event relation. Shared arrays start uninitialized in each group.
Device arrays must be read-only or write-only throughout one dispatch, so no
inter-workgroup communication is silently justified by sequential evaluation.
Every address is checked at every actual group/lane, including tail groups.
-/
def Program.checkInitialization (p : Program) : Except String Unit := do
  let bs := p.buffers.toArray
  for b in p.buffers do
    if b.storage == .constant && b.values.length != b.size then
      throw "constant buffer length differs from its declaration"
  for id in p.inputs ++ p.outputs do
    unless id < bs.size && (bs[id]!).storage == .device do
      throw "boundary names a missing or non-device array"
  for d in p.dispatches do
    for phase in d.phases do
      unless phase.closed do throw "register program is not closed SSA"
      for r in phase.reads do
        unless r.array < bs.size do throw "read names a missing array"
        unless r.index.syntaxSafe do throw "read index has invalid shader syntax"
      for w in phase.writes do
        unless w.array < bs.size do throw "write names a missing array"
        unless w.index.syntaxSafe do throw "write index has invalid shader syntax"
        if (bs[w.array]!).storage == .constant then throw "write to a constant array"
    for group in [:d.groups] do
      let mut initialized : Std.HashSet (Nat × Nat) := ∅
      for phase in d.phases do
        let mut writes : Std.HashSet (Nat × Nat) := ∅
        for lane in [:phase.lanes] do
          for r in phase.reads do
            let index := r.index.eval group lane
            if (bs[r.array]!).storage == .shared && !initialized.contains (r.array, index) then
              throw "shared read has no preceding write in this group"
          for w in phase.writes do
            let index := w.index.eval group lane
            writes := writes.insert (w.array, index)
        for loc in writes.toList do
          if (bs[loc.1]!).storage == .shared then initialized := initialized.insert loc

/-- Constant storage is read-only, independently of whether any group or lane is active. -/
def Program.noConstantWrites (p : Program) : Bool :=
  p.dispatches.all fun d => d.phases.all fun ph => ph.writes.all fun w =>
    (p.buffers.getD w.array default).storage != .constant

def Program.check (p : Program) : Except String Unit :=
  if p.geometrySafe then
    if p.boundsSafe then
      if p.ownershipSafe then
        if p.noConstantWrites then p.checkInitialization
        else .error "write to a constant array"
      else .error "scatter ownership or read/write separation failed"
    else .error "index bounds or u32 arithmetic failed"
  else .error "storage allocation or dispatch geometry exceeds u32 limits"

theorem Program.check_boundsSafe (p : Program) (h : p.check = .ok ()) :
    p.boundsSafe = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;> simp_all [Program.check]

theorem Program.check_ownershipSafe (p : Program) (h : p.check = .ok ()) :
    p.ownershipSafe = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;>
    cases ho : p.ownershipSafe <;> simp_all [Program.check]

theorem Program.check_noConstantWrites (p : Program) (h : p.check = .ok ()) :
    p.noConstantWrites = true := by
  cases hg : p.geometrySafe <;> cases hb : p.boundsSafe <;>
    cases ho : p.ownershipSafe <;> cases hn : p.noConstantWrites <;> simp_all [Program.check]

end Obend.Hardware.ArrayKernel
