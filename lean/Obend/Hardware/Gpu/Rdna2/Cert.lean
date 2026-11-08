/-
# Obend.Hardware.Gpu.Rdna2.Cert — RADV's machine code computes the plan, for every input

The certificate of rung G2. `certify p progs rs` runs every wave of every dispatch of the decoded dumps
`progs` symbolically (`Sym`): memory at the start of a dispatch is a variable per dword of the wire
buffer, except dwords an earlier dispatch is known to have written as a constant (the constants the
fused kernels read), and the layout's constants elsewhere (`Host`). Every dword a wave stores must lie
in the wire buffer, in a word some kernel of the dispatch owns, be stored once, and equal that kernel's
value (`Lower.pKernel`) at that element up to a residual (`Equiv.residual`), which must be one of `rs`; every word a kernel owns must be stored. `certify_sound` then says: if
`certify` accepts and every residual in `rs` holds, then for every wire buffer the dumped programs, run
on the model as the host dispatches them, end with exactly what `runStages` (`Obend.Hardware.Gpu`)
says the plan computes, every word of the buffer. `certified_outputs` composes that with
`lowerArrayToGpu_sound`: the model's outputs from the machine code are `evalGraph`'s, with no vectors.

The certificate is checked by running `certify` (compiled, `native_decide`) and by proving each residual
with `bv_decide` in a generated module: compiled trust, counted by the census, checked once per artifact.
The waits are checked alongside (`Waitcnt`): the model completes a load when it issues, and the
`s_waitcnt` check is what makes that reading the device's (see `waits_needed` in the header of
`Obend.Hardware.Gpu.Rdna2.Waitcnt`).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Host
public import Obend.Hardware.Gpu.Rdna2.Sym
public import Obend.Hardware.Gpu.Rdna2.Lower
public import Obend.Hardware.Gpu.Rdna2.Equiv
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Tm

/-! ## 1. Memory at the start of a dispatch, as terms -/

/-- Dwords of the wire buffer known for every input: constants an earlier dispatch stored. -/
abbrev Known := Std.HashMap UInt64 UInt32

def inW (words : Nat) (a : UInt64) : Bool := wDw ≤ a && a < wDw + UInt64.ofNat (2 * words)

def layoutOf (p : GpuProgram) : Memory := layoutMem p.words p.consts p.tables

/-- Memory at the start of a dispatch: the wire buffer's dwords (a variable, or the constant an earlier
dispatch stored), and the layout `lay` (computed once: `layoutOf p`) elsewhere. -/
def viewStart (p : GpuProgram) (lay : Memory) (known : Known) (a : UInt64) : Option Tm :=
  if inW p.words a then some (match known.get? a with | some v => lit v | none => var a)
  else (lay.get? a).map lit

def baseView (p : GpuProgram) (lay : Memory) (known : Known) (stored : Std.HashSet UInt64) (a : UInt64) : Option Tm :=
  if stored.contains a then none else viewStart p lay known a

def dwLo (j : Nat) : UInt64 := wDw + UInt64.ofNat (2 * j)

/-- Word `j` of the wire buffer at the start of a dispatch, as a pair of terms; past the buffer, `0`. -/
def readWord (p : GpuProgram) (lay : Memory) (known : Known) (j : Nat) : TP :=
  if j < p.words then
    ((viewStart p lay known (dwLo j)).getD (lit 0), (viewStart p lay known (dwLo j + 1)).getD (lit 0))
  else (lit 0, lit 0)

/-! ## 2. The check -/

instance : Hashable Residual := ⟨fun r => mixHash r.lhs.hsh r.rhs.hsh⟩

/-- A kernel's value at an element: a fold kernel's from the stage's cache `kc` (computed once per
dispatch, `foldValues`), any other's from `pKernel`. -/
def kvOf (cs : Array Word) (ix : Array Nat) (rd : Nat → TP) (kc : List (Kernel × Array TP)) (k : Kernel) (e : Nat) : Option TP :=
  match kc.find? (·.1 == k) with
  | some (_, arr) => arr[e]?
  | none => pKernel cs ix rd k e

/-- The fold kernels of a stage with their values. -/
def foldCache (rd : Nat → TP) (stage : GpuStage) : List (Kernel × Array TP) :=
  stage.kernels.filterMap fun k => (foldValues rd k).map (k, ·)

/-- One stored dword: in the wire buffer, owned, and specified; its residual, `none` if trivial. -/
def storeOk (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (known : Known) (kc : List (Kernel × Array TP)) (a : UInt64) (t : Tm) : Option (Option Residual) :=
  if !inW p.words a then none else
  let off := (a - wDw).toNat
  let i := off / 2
  match stage.kernels.find? (·.owns i) with
  | none => none
  | some k =>
    (kvOf cs ix (readWord p lay known) kc k (i - k.dstBase)).bind fun sp =>
      -- one object for each common subterm, then: the same term, or its residual
      let q := ShareCommon.shareCommon' (t, if off % 2 == 0 then sp.1 else sp.2)
      if q.1 == q.2 then some none
      else (residual q.1 q.2).map fun r => if r.lhs == r.rhs then none else some r

structure Acc where
  stored : Std.HashSet UInt64
  updates : List (UInt64 × Option UInt32)
  needed : Std.HashSet Residual

def checkStores (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (known : Known) (kc : List (Kernel × Array TP)) : List (UInt64 × Tm) → Acc → Option Acc
  | [], acc => some acc
  | (a, t) :: rest, acc =>
    if acc.stored.contains a then none else
    (storeOk p lay cs ix stage known kc a t).bind fun r? =>
      checkStores p lay cs ix stage known kc rest
        { stored := acc.stored.insert a, updates := (a, t.litVal?) :: acc.updates,
          needed := match r? with | some r => acc.needed.insert r | none => acc.needed }

def symWave (p : GpuProgram) (lay : Memory) (prog : Program) (known : Known) (stored : Std.HashSet UInt64) (g : Nat) : SymWave :=
  run prog (fuelOf prog) (initWave (⟨{}, baseView p lay known stored⟩ : SymMem) descSetLo g)

def checkWaves (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (prog : Program) (known : Known) (kc : List (Kernel × Array TP)) : List Nat → Acc → Option Acc
  | [], acc => some acc
  | g :: gs, acc =>
    let st := symWave p lay prog known acc.stored g
    if st.err.isNone && st.halted then
      (checkStores p lay cs ix stage known kc st.mem.stores.toList acc).bind (checkWaves p lay cs ix stage prog known kc gs)
    else none

def ownedDwords (stage : GpuStage) : List UInt64 :=
  stage.kernels.flatMap fun k => (List.range k.count).flatMap fun e => [dwLo (k.dstBase + e), dwLo (k.dstBase + e) + 1]

def applyUpdates (known : Known) (us : List (UInt64 × Option UInt32)) : Known :=
  us.foldr (fun (a, v?) kn => match v? with | some v => kn.insert a v | none => kn.erase a) known

/-- One dispatch: the known constants after it and the residuals it needs. -/
def checkStage (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (prog : Program) (known : Known) :
    Option (Known × Std.HashSet Residual) :=
  (checkWaves p lay cs ix stage prog known (foldCache (readWord p lay known) stage) (List.range (groupsOf stage.threads)) ⟨{}, [], {}⟩).bind fun acc =>
    if (ownedDwords stage).all acc.stored.contains then some (applyUpdates known acc.updates, acc.needed) else none

/-- Every dispatch; the residuals they need. -/
def checkProgram (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) : List GpuStage → List Program → Known → Std.HashSet Residual →
    Option (Std.HashSet Residual)
  | [], [], _, need => some need
  | s :: ss, prog :: progs, known, need =>
    (checkStage p lay cs ix s prog known).bind fun (known', n) => checkProgram p lay cs ix ss progs known' (n.fold (·.insert ·) need)
  | _, _, _, _ => none

/-- The certificate: every dispatch checks, and every residual it needs is one of `rs`. -/
def certify (p : GpuProgram) (progs : List Program) (rs : List Residual) : Bool :=
  -- the wire buffer is small enough that no dword address wraps, and every kernel writes inside it
  p.words < 2 ^ 29 &&
  p.stages.all (·.kernels.all fun k => k.dstBase + k.count ≤ p.words) &&
  match checkProgram p (layoutOf p) p.consts.toArray p.tables.toArray p.stages progs {} {} with
  | some need => need.toList.all rs.contains
  | none => false

/-- The residuals a program needs (for the generator of the module that proves them). -/
def neededResiduals (p : GpuProgram) (progs : List Program) : Option (List Residual) :=
  (checkProgram p (layoutOf p) p.consts.toArray p.tables.toArray p.stages progs {} {}).map (·.toList)

end Obend.Hardware.Gpu.Rdna2
