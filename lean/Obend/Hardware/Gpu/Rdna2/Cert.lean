/-
# Obend.Hardware.Gpu.Rdna2.Cert — RADV's machine code computes the plan, for every input

The certificate of rung G2, for any stage that says what it computes (`Spec`): its thread count, its LDS,
the table of the words it writes as terms over the dispatch's start (`Spec.table`) and its meaning on the
whole state (`Spec.den`); `Spec.Sound` (in `CertSound`) is the promise that the table is the meaning. A
plan's stage (`gpuSpec`) and a block dispatch (`Block.blockSpec`) are the two instances. `certify p progs rs` runs every wave of every dispatch of the decoded dumps
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
dispatch stored), nothing in the LDS regions, and the layout `lay` elsewhere. -/
def viewStart (words : Nat) (lay : Memory) (known : Known) (a : UInt64) : Option Tm :=
  if inW words a then some (match known.get? a with | some v => lit v | none => var a)
  else if inLds a then none
  else (lay.get? a).map lit

def baseView (words : Nat) (lay : Memory) (known : Known) (stored : Std.HashSet UInt64) (a : UInt64) : Option Tm :=
  if stored.contains a then none else viewStart words lay known a

def dwLo (j : Nat) : UInt64 := wDw + UInt64.ofNat (2 * j)

/-- Word `j` of the wire buffer at the start of a dispatch, as a pair of terms; past the buffer, `0`. -/
def readWord (words : Nat) (lay : Memory) (known : Known) (j : Nat) : TP :=
  if j < words then
    ((viewStart words lay known (dwLo j)).getD (lit 0), (viewStart words lay known (dwLo j + 1)).getD (lit 0))
  else (lit 0, lit 0)

/-! ## 2. What a dispatch computes -/

/-- A dispatch as the certificate reads it: `threads` threads in workgroups of one wave with `lds` dwords of
LDS each; `table rd` the words it writes, each as a pair of terms over the start's words `rd` (`none`:
the stage is not understood); `den` its meaning on the whole state `σ`, of which the wire buffer is a
projection (`Spec.Sound`). -/
structure Spec (σ : Type) where
  threads : Nat
  lds : Nat
  table : (Nat → TP) → Option (Std.HashMap Nat TP)
  den : σ → σ

/-! ## 3. The check -/

instance : Hashable Residual := ⟨fun r => mixHash r.lhs.hsh r.rhs.hsh⟩

/-- One stored dword: in the wire buffer, in a word the table specifies; its residual, `none` if trivial. -/
def storeOk (words : Nat) (T : Std.HashMap Nat TP) (a : UInt64) (t : Tm) : Option (Option Residual) :=
  if !inW words a then none else
  let off := (a - wDw).toNat
  match T[off / 2]? with
  | none => none
  | some sp =>
      -- one object for each common subterm, then: the same term, or its residual
      let q := ShareCommon.shareCommon' (t, if off % 2 == 0 then sp.1 else sp.2)
      if q.1 == q.2 then some none
      else (residual q.1 q.2).map fun r => if r.lhs == r.rhs then none else some r

structure Acc where
  stored : Std.HashSet UInt64
  updates : List (UInt64 × Option UInt32)
  needed : Std.HashSet Residual

/-- A wave's stores: its LDS (the work-group's scratch, never read by another) is not checked; every other
dword is stored once per dispatch and checked. -/
def checkStores (words : Nat) (T : Std.HashMap Nat TP) : List (UInt64 × Tm) → Acc → Option Acc
  | [], acc => some acc
  | (a, t) :: rest, acc =>
    if inLds a then checkStores words T rest acc else
    if acc.stored.contains a then none else
    (storeOk words T a t).bind fun r? =>
      checkStores words T rest
        { stored := acc.stored.insert a, updates := (a, t.litVal?) :: acc.updates,
          needed := match r? with | some r => acc.needed.insert r | none => acc.needed }

def symWave (words : Nat) (lay : Memory) (prog : Program) (lds : Nat) (known : Known) (stored : Std.HashSet UInt64) (g : Nat) : SymWave :=
  run prog (fuelOf prog) (initWave (⟨{}, baseView words lay known stored⟩ : SymMem) descSetLo g (ldsBaseOf g) lds)

def checkWaves (words : Nat) (lay : Memory) (T : Std.HashMap Nat TP) (prog : Program) (lds : Nat) (known : Known) : List Nat → Acc → Option Acc
  | [], acc => some acc
  | g :: gs, acc =>
    let st := symWave words lay prog lds known acc.stored g
    if st.err.isNone && st.halted then
      (checkStores words T st.mem.stores.toList acc).bind (checkWaves words lay T prog lds known gs)
    else none

def applyUpdates (known : Known) (us : List (UInt64 × Option UInt32)) : Known :=
  us.foldr (fun (a, v?) kn => match v? with | some v => kn.insert a v | none => kn.erase a) known

/-- Every word of the table stored, both dwords. -/
def tableStored (T : Std.HashMap Nat TP) (stored : Std.HashSet UInt64) : Bool :=
  T.toList.all fun (i, _) => stored.contains (dwLo i) && stored.contains (dwLo i + 1)

/-- One dispatch: the known constants after it and the residuals it needs. -/
def checkStage {σ : Type} (words : Nat) (lay : Memory) (s : Spec σ) (prog : Program) (known : Known) :
    Option (Known × Std.HashSet Residual) :=
  (s.table (readWord words lay known)).bind fun T =>
  (checkWaves words lay T prog s.lds known (List.range (groupsOf s.threads)) ⟨{}, [], {}⟩).bind fun acc =>
    if tableStored T acc.stored then some (applyUpdates known acc.updates, acc.needed) else none

/-- Every dispatch; the residuals they need. -/
def checkProgram {σ : Type} (words : Nat) (lay : Memory) : List (Spec σ) → List Program → Known → Std.HashSet Residual →
    Option (Std.HashSet Residual)
  | [], [], _, need => some need
  | s :: ss, prog :: progs, known, need =>
    (checkStage words lay s prog known).bind fun (known', n) => checkProgram words lay ss progs known' (n.fold (·.insert ·) need)
  | _, _, _, _ => none

/-- The host's dispatches of certified stages: program, threads, LDS. -/
def dispatchesOf {σ : Type} (specs : List (Spec σ)) (progs : List Program) : List (Program × Nat × Nat) :=
  progs.zip (specs.map fun s => (s.threads, s.lds))

/-! ## 4. A stage of a plan -/

/-- A kernel's value at an element: a fold kernel's from the stage's cache `kc` (computed once per
dispatch, `foldValues`), any other's from `pKernel`. -/
def kvOf (cs : Array Word) (ix : Array Nat) (rd : Nat → TP) (kc : List (Kernel × Array TP)) (k : Kernel) (e : Nat) : Option TP :=
  match kc.find? (·.1 == k) with
  | some (_, arr) => arr[e]?
  | none => pKernel cs ix rd k e

/-- The fold kernels of a stage with their values. -/
def foldCache (rd : Nat → TP) (stage : GpuStage) : List (Kernel × Array TP) :=
  stage.kernels.filterMap fun k => (foldValues rd k).map (k, ·)

/-- Words `i < n` of a stage's table: each word's first owning kernel's value there (`runStage`). -/
def gpuTableUpTo (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (rd : Nat → TP) (kc : List (Kernel × Array TP)) :
    Nat → Option (Std.HashMap Nat TP)
  | 0 => some {}
  | n + 1 => (gpuTableUpTo cs ix stage rd kc n).bind fun T =>
    match stage.kernels.find? (·.owns n) with
    | none => some T
    | some k => (kvOf cs ix rd kc k (n - k.dstBase)).map (T.insert n)

def gpuSpec (p : GpuProgram) (cs : Array Word) (ix : Array Nat) (stage : GpuStage) : Spec (Nat → Word) where
  threads := stage.threads
  lds := 0
  table rd := gpuTableUpTo cs ix stage rd (foldCache rd stage) p.words
  den E := runStage p.consts p.tables E stage

/-- The certificate: every dispatch checks, and every residual it needs is one of `rs`. -/
def certify (p : GpuProgram) (progs : List Program) (rs : List Residual) : Bool :=
  -- the wire buffer is small enough that no dword address wraps, and every kernel writes inside it
  p.words < 2 ^ 29 &&
  p.stages.all (·.kernels.all fun k => k.dstBase + k.count ≤ p.words) &&
  match checkProgram p.words (layoutOf p) (p.stages.map (gpuSpec p p.consts.toArray p.tables.toArray)) progs {} {} with
  | some need => need.toList.all rs.contains
  | none => false

/-- The residuals a program needs (for the generator of the module that proves them). -/
def neededResiduals (p : GpuProgram) (progs : List Program) : Option (List Residual) :=
  (checkProgram p.words (layoutOf p) (p.stages.map (gpuSpec p p.consts.toArray p.tables.toArray)) progs {} {}).map (·.toList)

end Obend.Hardware.Gpu.Rdna2
