/-
# Obend.Hardware.Gpu.Rdna2.Cert — RADV's machine code computes the plan, for every input

The certificate of rung G2, for any stage that says what it computes (`Spec`): its thread count, its LDS,
the table of the words it writes as terms over the dispatch's start (`Spec.table`) and its meaning on the
whole state (`Spec.den`); `Spec.Sound` (in `CertSound`) is the promise that the table is the meaning. A
plan's elementwise stage (`Schedule.actionSpecs`, its table `gpuTableUpTo`) and a block dispatch
(`Block.blockSpec`) are the two instances. `checkProgram` runs every wave of every dispatch of the decoded
dumps symbolically (`Sym`): memory at the start of a dispatch is a variable per dword of the wire buffer,
except dwords an earlier dispatch is known to have written as a constant, and the layout's constants
elsewhere (`Host`). Every dword a wave stores must lie in the wire buffer, in a word the stage's table
specifies, be stored once, and equal the table's term up to a residual (`Equiv.residual`), which the caller
requires to be in its proved library; every word of the table must be stored. `checkProgram_sound` then
says the model run of the dumps succeeds and leaves the wire buffer as the stages' meanings compose.
`Schedule.certifySchedule_sound` is that for a graph's emitted schedule and `Certified.certifyDump_sound`
composes it with the emitter's correctness and `lowerArrayToGpu_sound`: the model's outputs from the
machine code are `evalGraph`'s, with no vectors.

The certificate is checked by running `certify` (compiled, `native_decide`) and by proving each residual
with `bv_decide` in a generated module: compiled trust, counted by the census, checked once per artifact.
The waits are checked alongside (`Waitcnt`): the model completes a load when it issues, and the
`s_waitcnt` check is what makes that reading the device's (see `waits_needed` in the header of
`Obend.Hardware.Gpu.Rdna2.Waitcnt`).
-/

module

public import Obend.Hardware.Gpu.Rdna2.Host
public import Obend.Hardware.Gpu.Rdna2.Join
public import Obend.Hardware.Gpu.Rdna2.Lower
public import Obend.Hardware.Gpu.Rdna2.Equiv

@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Tm

/-! ## 1. Memory at the start of a dispatch, as terms -/

/-- Dwords of the wire buffer known for every input: constants an earlier dispatch stored. -/
abbrev Known := Std.HashMap UInt64 UInt32

def inW (words : Nat) (a : UInt64) : Bool := wDw ≤ a && a < wDw + UInt64.ofNat (2 * words)


/-- Memory at the start of a dispatch: the wire buffer's dwords (a variable, or the constant an earlier
dispatch stored), nothing in the LDS regions, and the layout `lay` elsewhere. -/
def viewStart (words : Nat) (lay : Memory) (known : Known) (a : UInt64) : Option Tm :=
  if inW words a then some (match known.get? a with | some v => lit v | none => var a)
  else if inLds a then none
  else (lay.get? a).map lit

/-- The start's view with the dwords `ex` names unreadable (at least those an earlier wave stored). -/
def baseView (words : Nat) (lay : Memory) (known : Known) (ex : UInt64 → Bool) (a : UInt64) : Option Tm :=
  if ex a then none else viewStart words lay known a

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
  /-- The table in parts, wave by wave: `part rd has g` is the words wave `g` writes, given which words
  `has` the earlier waves' parts hold (`Spec.PartsOk`: the parts are the table). A stage with parts never
  holds its whole table: each part is built when its wave is checked and dropped after. -/
  part : Option ((Nat → TP) → (Nat → Bool) → Nat → Option (Std.HashMap Nat TP)) := none

/-! ## 3. The check -/

instance : Hashable Residual := ⟨fun r => mixHash r.lhs.hsh r.rhs.hsh⟩

/-- The table's term for a stored dword: the half of its word the dword's address names. -/
def specAt (words : Nat) (T : Std.HashMap Nat TP) (a : UInt64) : Option Tm :=
  if !inW words a then none else
  let off := (a - wDw).toNat
  (T[off / 2]?).map fun sp => if off % 2 == 0 then sp.1 else sp.2

/-- A stored term against its table term: the same term, or its residual. -/
def storeOkX (t : Tm) : Option Tm → Option (Option Residual)
  | none => none
  | some x => if t == x then some none else (residual t x).map fun r => if r.lhs == r.rhs then none else some r

/-- A stored dword: in a word of the table, and its term the table's up to a residual. -/
def storeOk (words : Nat) (T : Std.HashMap Nat TP) (a : UInt64) (t : Tm) : Option (Option Residual) :=
  storeOkX t (specAt words T a)

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

def checkStoresX : List (UInt64 × Tm × Option Tm) → Acc → Option Acc
  | [], acc => some acc
  | (a, t, x) :: rest, acc =>
    if inLds a then checkStoresX rest acc else
    if acc.stored.contains a then none else
    (storeOkX t x).bind fun r? =>
      checkStoresX rest
        { stored := acc.stored.insert a, updates := (a, t.litVal?) :: acc.updates,
          needed := match r? with | some r => acc.needed.insert r | none => acc.needed }

theorem checkStoresX_eq (words : Nat) (T : Std.HashMap Nat TP) : ∀ (L : List (UInt64 × Tm)) (acc : Acc),
    checkStoresX (L.map fun p => (p.1, p.2, specAt words T p.1)) acc = checkStores words T L acc
  | [], _ => rfl
  | (a, t) :: rest, acc => by
    simp only [List.map_cons, checkStoresX, checkStores, storeOk]
    split
    · exact checkStoresX_eq words T rest acc
    · split
      · rfl
      · congr 1; funext r?; exact checkStoresX_eq words T rest _

/-- A wave's stores with their table terms, one object for each common subterm (one sharing pass per
wave: sharing each dword with its term alone visited the shared part of the wave's terms every time). -/
def sharedStores (words : Nat) (T : Std.HashMap Nat TP) (L : List (UInt64 × Tm)) : List (UInt64 × Tm × Option Tm) :=
  ShareCommon.shareCommon' (L.map fun p => (p.1, p.2, specAt words T p.1))

def symWave (words : Nat) (lay : Memory) (prog : Program) (lds : Nat) (known : Known) (ex : UInt64 → Bool) (g : Nat) : SymWave :=
  srun prog (fuelOf prog) (initWave (⟨{}, baseView words lay known ex⟩ : SymMem) descSetLo g (ldsBaseOf g) lds)

def checkWaves (words : Nat) (lay : Memory) (T : Std.HashMap Nat TP) (prog : Program) (lds : Nat) (known : Known) : List Nat → Acc → Option Acc
  | [], acc => some acc
  | g :: gs, acc =>
    let st := symWave words lay prog lds known acc.stored.contains g
    if st.err.isNone && st.halted then
      (checkStoresX (sharedStores words T st.mem.stores.toList) acc).bind (checkWaves words lay T prog lds known gs)
    else none

def applyUpdates (known : Known) (us : List (UInt64 × Option UInt32)) : Known :=
  us.foldr (fun (a, v?) kn => match v? with | some v => kn.insert a v | none => kn.erase a) known

/-- Every word of the table stored, both dwords. -/
def tableStored (T : Std.HashMap Nat TP) (stored : Std.HashSet UInt64) : Bool :=
  T.toList.all fun (i, _) => stored.contains (dwLo i) && stored.contains (dwLo i + 1)

/-- One dispatch against its whole table: the known constants after it and the residuals it needs. -/
def checkStageW {σ : Type} (words : Nat) (lay : Memory) (s : Spec σ) (prog : Program) (known : Known) :
    Option (Known × Std.HashSet Residual) :=
  (s.table (readWord words lay known)).bind fun T =>
  (checkWaves words lay T prog s.lds known (List.range (groupsOf s.threads)) ⟨{}, [], {}⟩).bind fun acc =>
    if tableStored T acc.stored then some (applyUpdates known acc.updates, acc.needed) else none

/-! ## 4. A stage in parts: two passes, the waves in parallel -/

/-- Word `j` lies in the part of a wave before `g`, read from the owners `O` (each word of a part with the
wave whose part it is). -/
def hasOf (O : Std.HashMap Nat Nat) (g j : Nat) : Bool :=
  match O[j]? with
  | some h => decide (h < g)
  | none => false

/-- The dword's word in the wire buffer. -/
def wordOf (a : UInt64) : Nat := (a - wDw).toNat / 2

/-- `f` on every element, each in its own task; it is `List.map f` (`parMap_eq`). -/
def parMap {α β : Type} (f : α → β) (xs : List α) : List β :=
  (xs.map fun x => Task.spawn fun _ => f x).map Task.get

theorem parMap_eq {α β : Type} (f : α → β) (xs : List α) : parMap f xs = xs.map f := by
  simp only [parMap, List.map_map]; rfl

/-- The first pass, a guess at the owners: every wave's part built, in parallel, as if no earlier part held
a word, and its words given to it. Only a guess: each wave checks it against the part it really has
(`waveOut`), so nothing rests on it. -/
def ownersGuess (part : (Nat → Bool) → Nat → Option (Std.HashMap Nat TP)) (gs : List Nat) : Std.HashMap Nat Nat :=
  (gs.zip (parMap (fun g => (part (fun _ => false) g).map fun P => P.keys) gs)).foldl
    (fun O x => match x.2 with
      | some ks => ks.foldl (fun O j => O.insert j x.1) O
      | none => O) {}

/-- The words each wave owns. -/
def ownedBy (O : Std.HashMap Nat Nat) : Std.HashMap Nat (List Nat) :=
  O.toList.foldl (fun I x => I.insert x.2 (x.1 :: I.getD x.2 [])) {}

/-- A stored dword, checked on its own: its address, its value if a literal, and its term against the
table's (`storeOkX`). -/
def storePre (x : UInt64 × Tm × Option Tm) : UInt64 × Option UInt32 × Option (Option Residual) :=
  (x.1, x.2.1.litVal?, storeOkX x.2.1 x.2.2)

/-- `checkStoresX` on stores checked on their own: only the bookkeeping is left. -/
def checkStoresY : List (UInt64 × Option UInt32 × Option (Option Residual)) → Acc → Option Acc
  | [], acc => some acc
  | (a, v, r) :: rest, acc =>
    if inLds a then checkStoresY rest acc else
    if acc.stored.contains a then none else
    r.bind fun r? =>
      checkStoresY rest
        { stored := acc.stored.insert a, updates := (a, v) :: acc.updates,
          needed := match r? with | some r => acc.needed.insert r | none => acc.needed }

/-- The second pass, one wave, on its own: its part rebuilt from the owners and checked to hold exactly
the words they give it, its symbolic run with every dword of an earlier part's word unreadable (the
earlier waves' stores can only lie there), and its stores checked against the part's terms. -/
def waveOut (words : Nat) (lay : Memory) (part : (Nat → Bool) → Nat → Option (Std.HashMap Nat TP))
    (prog : Program) (lds : Nat) (known : Known) (O : Std.HashMap Nat Nat) (I : Std.HashMap Nat (List Nat))
    (g : Nat) : Option (List (UInt64 × Option UInt32 × Option (Option Residual))) :=
  (part (hasOf O g) g).bind fun P =>
  if P.toList.all (fun x => O[x.1]? == some g) && (I.getD g []).all P.contains then
    let st := symWave words lay prog lds known (fun a => inW words a && hasOf O g (wordOf a)) g
    if st.err.isNone && st.halted then some ((sharedStores words P st.mem.stores.toList).map storePre) else none
  else none

/-- The waves' results in order, every dword stored once. -/
def mergeWaves : List (Option (List (UInt64 × Option UInt32 × Option (Option Residual)))) → Acc → Option Acc
  | [], acc => some acc
  | o :: os, acc => o.bind fun L => (checkStoresY L acc).bind (mergeWaves os)

/-- Every word of the parts stored, both dwords. -/
def ownedStored (O : Std.HashMap Nat Nat) (stored : Std.HashSet UInt64) : Bool :=
  O.toList.all fun (i, _) => stored.contains (dwLo i) && stored.contains (dwLo i + 1)

/-- One dispatch: the known constants after it and the residuals it needs. A stage with parts is checked
in two passes, each wave on its own task: a guess at each word's owner (`ownersGuess`), then every wave
against its part (`waveOut`), merged in order. -/
def checkStage {σ : Type} (words : Nat) (lay : Memory) (s : Spec σ) (prog : Program) (known : Known) :
    Option (Known × Std.HashSet Residual) :=
  match s.part with
  | none => checkStageW words lay s prog known
  | some part =>
    let pt := part (readWord words lay known)
    let gs := List.range (groupsOf s.threads)
    let O := ownersGuess pt gs
    if O.toList.all (fun x => decide (x.2 < groupsOf s.threads)) then
      (mergeWaves (parMap (waveOut words lay pt prog s.lds known O (ownedBy O)) gs) ⟨{}, [], {}⟩).bind fun acc =>
      if ownedStored O acc.stored then some (applyUpdates known acc.updates, acc.needed) else none
    else none

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

/-! ## 5. A stage of a plan -/

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

end Obend.Hardware.Gpu.Rdna2
