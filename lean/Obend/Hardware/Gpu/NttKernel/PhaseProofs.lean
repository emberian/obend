module
import all Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.NttSpec
public import Obend.Hardware.Gpu.PhaseSemantics
public import Obend.Hardware.Gpu.BlockLower
public import Obend.Hardware.Gpu.GoldilocksSourceCorrect
public import Obend.Hardware.Gpu.BlockPlan
public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource
open Obend.Apps.ZkNtt (goldilocksPrime)
namespace BlockNtt
open Obend.Hardware.ArrayKernel

/-- One butterfly uses the same shared field source construction as every
other consumer. A missing twiddle is precisely the source's unit-twiddle case. -/
structure Butterfly where
  sum : Nat
  high : Nat
  read : Option Read

def butterfly (k : GlConsts) (a b : Nat) (twiddle : Option Ix) : BuildM Butterfly := do
  let sum ← glAdd 1 k a b
  let diff ← glSub 1 k a b
  match twiddle with
  | none => pure ⟨sum,diff,none⟩
  | some exponent =>
    let tw ← newWire 1
    let high ← glMul 1 k diff tw
    pure ⟨sum,high,some ⟨tw,4,exponent⟩⟩

/-- The register construction interpreted by `phase`; separating it from the
index-to-write packaging exposes the actual source builder to semantic proofs. -/
def phaseAction (n count p done degree src : Nat) (first : Bool) : BuildM (List Read × List Nat) := do
  let radix := 2^degree
  let stride := count / (2^done * radix)
  let index := phaseIndex radix stride
  let loadIndex := phaseLoadIndex n count radix stride first
  let mut reads : List Read := []
  let mut regs : Array Nat := #[]
  for r in List.range radix do
    let a ← newWire 1
    reads := reads ++ [⟨a, src, loadIndex r⟩]
    regs := regs.push a
  let k ← glConsts 1
  if first && p == 1 then
    for r in List.range radix do
      let canonical ← glCanon 1 k regs[r]!
      regs := regs.set! r canonical
  if first && p > 1 then
    for r in List.range radix do
      let tw ← newWire 1
      let exponent := .mod (.mul (index r) (mulI (.mod .group p) (n/count/p))) n
      reads := reads ++ [⟨tw, 4, exponent⟩]
      let v ← glMul 1 k regs[r]! tw
      regs := regs.set! r v
  for round in List.range degree do
    let bit := radix / 2^(round+1)
    for j in List.range (radix/2) do
      let di := j % bit
      let i0 := 2*j-di
      let i1 := i0+bit
      let a := regs[i0]!
      let b := regs[i1]!
      -- Twiddle depends only on the within-butterfly coordinate; the segment
      -- coordinate has been removed by lane modulo stride.
      let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride)))
        (2^(done+round) * (n/count))
      let result ← butterfly k a b
        (if stride == 1 && di == 0 then none else some exponent)
      match result.read with
      | none => pure ()
      | some read => reads := reads ++ [read]
      regs := (regs.set! i0 result.sum).set! i1 result.high
  return (reads, regs.toList)

/-- One register tile of the DIF network. `done` preceding binary layers have
already run; `degree` layers are fused now. All arithmetic is the shared source
builder above, and both index permutations remain source expressions. -/
def phase (n count logCount p done degree src dst : Nat)
    (first last : Bool) : Phase := Id.run do
  let radix := 2^degree
  let stride := count / (2^done * radix)
  let saveIndex := phaseSaveIndex count logCount p radix stride last
  let ((reads, outputs), st) := (phaseAction n count p done degree src first).run {}
  return { lanes := count/radix, reads, code := registerCode st,
           writes := outputs.zipIdx.map fun (value, r) => ⟨dst, saveIndex r, value⟩ }

/-- Consecutive radix-4 register blocks, with one final radix-2 block when odd. -/
def phaseDegrees (degree : Nat) : List Nat :=
  List.replicate (degree/2) 2 ++ if degree%2 == 0 then [] else [1]

/-- The exact barrier-separated phase list, carrying the completed layer count
and alternating shared source row explicitly. -/
def buildPhases (n logCount p dst : Nat) : Nat → Nat → List Nat → List Phase
  | _, _, [] => []
  | done, input, chunk::rest =>
    let last := done+chunk == logCount
    let output := if last then dst else if input == 2 then 3 else 2
    phase n (2^logCount) logCount p done chunk input output (done == 0) last ::
      buildPhases n logCount p dst (done+chunk) output rest

/-- A Stockham upload groups up to eight binary layers. Radix-4 register blocks
keep 64 lanes active for a 256-element tile; barriers exchange successive pairs of layers. -/
def dispatch (n logP degree src dst : Nat) : Dispatch :=
  { groups := n/(2^degree)
    phases := buildPhases n degree (2^logP) dst 0 src (phaseDegrees degree) }

/-- Substitute source indices while batching independent tiles into a workgroup.
This constructs the indexed source maps; admission checks the resulting accesses. -/
def substitute (group lane : Ix) : Ix → Ix
  | .lit n => .lit n
  | .group => group
  | .lane => lane
  | .add a b => .add (substitute group lane a) (substitute group lane b)
  | .mul a b => .mul (substitute group lane a) (substitute group lane b)
  | .div a n => .div (substitute group lane a) n
  | .mod a n => .mod (substitute group lane a) n
  | .lookup values i => .lookup values (substitute group lane i)

def tileSize (d : Dispatch) : Nat :=
  d.phases.foldl (fun n ph => max n (ph.lanes * ph.writes.length)) 1

def packing (d : Dispatch) : Nat :=
  let lanes := d.phases.foldl (fun n ph => max n ph.lanes) 1
  let k := max 1 (min d.groups (64 / lanes))
  if d.groups % k == 0 then k else 1

/-- A batch is one simultaneous map over independent tile coordinates. Shared
arrays acquire a tile coordinate too; all barriers stay uniform across the batch. -/
def batchTiles (stride : Nat) (d : Dispatch) : Dispatch :=
  let k := packing d
  { groups := d.groups / k
    phases := d.phases.map fun ph =>
      let tile : Ix := .div .lane ph.lanes
      let group : Ix := .add (.mul .group (.lit k)) tile
      let lane : Ix := .mod .lane ph.lanes
      let index (array : Nat) (i : Ix) :=
        let i := substitute group lane i
        if array == 2 || array == 3 then .add i (.mul tile (.lit stride)) else i
      { ph with lanes := ph.lanes*k
                reads := ph.reads.map fun r => { r with index := index r.array r.index }
                writes := ph.writes.map fun w => { w with index := index w.array w.index } } }

end BlockNtt

/-- Balanced upload size: the same policy is used by construction and proofs. -/
def uploadDegree (maximum remaining : Nat) : Nat :=
  let uploads := (remaining + maximum - 1) / maximum
  (remaining + uploads - 1) / uploads

/-- Static upload schedule. Fuel is the remaining number of binary layers,
so construction is total without an unchecked termination assertion. -/
def uploadDegrees (maximum : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, remaining =>
      if remaining = 0 then [] else
        let degree := uploadDegree maximum remaining
        degree :: uploadDegrees maximum fuel (remaining-degree)

/-- The one construction of upload dispatches. Source registers and shared
phases are supplied by `BlockNtt.dispatch`; the schedule only chooses tile sizes. -/
def buildUploads (n : Nat) : List Nat → Nat → Nat → List Obend.Hardware.ArrayKernel.Dispatch × Nat
  | [], _, input => ([], input)
  | degree :: rest, done, input =>
      let output := 1-input
      let tail := buildUploads n rest (done+degree) output
      (BlockNtt.dispatch n done degree input output :: tail.1, tail.2)

def uploadSchedule (n : Nat) : List Nat :=
  let logN := Nat.log2 n
  uploadDegrees (if n ≤ 1024 then 4 else 8) logN logN

def sourceUploads (n : Nat) : List Obend.Hardware.ArrayKernel.Dispatch × Nat :=
  buildUploads n (uploadSchedule n) 0 0

def sharedWords (n : Nat) : Nat :=
  (sourceUploads n).1.foldl
    (fun size d => max size (BlockNtt.tileSize d * BlockNtt.packing d)) 1

/-- Stockham NTT as a composition of general array maps. `n` is a power of two
with initial words canonicalized in registers. The emitter accepts sizes below 2^26. Three uploads suffice for 2^20; each has multiple register maps
separated by workgroup exchanges. Two device arrays are reused between uploads. -/
@[expose] def nttBlockProgram (n : Nat) : Obend.Hardware.ArrayKernel.Program :=
  { buffers := [⟨n, .device, []⟩, ⟨n, .device, []⟩,
      ⟨sharedWords n, .shared, []⟩, ⟨sharedWords n, .shared, []⟩,
      ⟨n, .constant, (twiddlePowers n (rootOfUnity n)).toList⟩],
    inputs := [0], outputs := [(sourceUploads n).2],
    dispatches := (sourceUploads n).1.map fun d => BlockNtt.batchTiles (BlockNtt.tileSize d) d }

/-- The recursive radix-2 NTT in `Nat` arithmetic: `y_k = E_k + ω^k O_k`, `y_{k+n/2} = E_k - ω^k O_k`. -/
partial def nttFast (xs : Array Nat) (ω : Nat) : Array Nat :=
  let n := xs.size
  if n ≤ 1 then xs else
  let half := n / 2
  let ω2 := ω * ω % goldilocksPrime
  let ev := nttFast ((Array.range half).map fun i => xs[2 * i]!) ω2
  let od := nttFast ((Array.range half).map fun i => xs[2 * i + 1]!) ω2
  let pw := (Array.range half).map fun j => powMod ω j goldilocksPrime
  (Array.range n).map fun j =>
    if j < half then (ev[j]! + pw[j]! * od[j]! % goldilocksPrime) % goldilocksPrime
    else
      let j' := j - half
      (ev[j']! + goldilocksPrime - pw[j']! * od[j']! % goldilocksPrime) % goldilocksPrime


open Obend.Hardware.ArrayKernel

/-- Actual program initialization preserves the generated constant table. -/
theorem initial_twiddles (n : Nat) (input : Array Word) :
    (initialMemory (nttBlockProgram n) [input]).getD 4 #[] =
      twiddlePowers n (rootOfUnity n) := by
  simp [initialMemory,nttBlockProgram]


end Obend.Hardware.Gpu.Ntt

section
/-! Concrete index and invocation semantics for the NTT builder's tile batching.
The transformed phases below are definitionally the phases in `batchTiles`.
Memory relations concern source reads; register arithmetic is unchanged. -/
namespace Obend.Hardware.Gpu.NttBatchCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

theorem substitute_eval (group lane : Ix) (i : Ix) (g l : Nat) :
    (substitute group lane i).eval g l = i.eval (group.eval g l) (lane.eval g l) := by
  induction i <;> simp_all [substitute,Ix.eval]

/-- Shared rows carry a tile coordinate; device and constant rows do not. -/
def tileIndex (stride tile array i : Nat) : Nat :=
  if array == 2 || array == 3 then i+tile*stride else i

def batchIndex (stride k lanes array : Nat) (i : Ix) : Ix :=
  let tile : Ix := .div .lane lanes
  let group : Ix := .add (.mul .group (.lit k)) tile
  let lane : Ix := .mod .lane lanes
  let i := substitute group lane i
  if array == 2 || array == 3 then .add i (.mul tile (.lit stride)) else i

def batchPhase (stride k : Nat) (ph : Phase) : Phase :=
  { ph with lanes := ph.lanes*k
            reads := ph.reads.map fun r => {r with index := batchIndex stride k ph.lanes r.array r.index}
            writes := ph.writes.map fun w => {w with index := batchIndex stride k ph.lanes w.array w.index} }

theorem batchTiles_phases (stride : Nat) (d : Dispatch) :
    (batchTiles stride d).phases = d.phases.map (batchPhase stride (packing d)) := by rfl

theorem batchTiles_groups (stride : Nat) (d : Dispatch) :
    (batchTiles stride d).groups = d.groups / packing d := by rfl

theorem batchIndex_eval (stride k lanes array : Nat) (i : Ix) (g l : Nat) :
    (batchIndex stride k lanes array i).eval g l =
      tileIndex stride (l/lanes) array (i.eval (g*k+l/lanes) (l%lanes)) := by
  unfold batchIndex tileIndex
  split <;> simp [Ix.eval,substitute_eval]

theorem batchIndex_eval_tile (stride k lanes array : Nat) (i : Ix)
    (g tile l : Nat) (hl : l < lanes) :
    (batchIndex stride k lanes array i).eval g (tile*lanes+l) =
      tileIndex stride tile array (i.eval (g*k+tile) l) := by
  rw [batchIndex_eval]
  have hd : (tile*lanes+l)/lanes = tile := by
    rw [Nat.mul_comm tile lanes,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hl,Nat.add_zero]
  simp [hd,Nat.mul_add_mod_of_lt hl]

theorem packing_pos (d : Dispatch) : 0 < packing d := by
  unfold packing
  dsimp only
  split <;> omega

theorem packing_divides (d : Dispatch) : packing d ∣ d.groups := by
  unfold packing
  dsimp only
  split
  · rename_i h
    exact Nat.dvd_of_mod_eq_zero (by simpa using h)
  · exact Nat.one_dvd _

/-- Every packed invocation names an existing original group. -/
theorem packed_group_bound (d : Dispatch) (g tile : Nat)
    (hg : g < d.groups / packing d) (ht : tile < packing d) :
    g*packing d+tile < d.groups := by
  have h1 := Nat.mul_le_mul_right (packing d) (Nat.succ_le_of_lt hg)
  have h2 := Nat.div_mul_le_self d.groups (packing d)
  simp only [Nat.succ_mul] at h1
  omega

theorem packed_lane_bound (lanes k tile l : Nat) (ht : tile < k) (hl : l < lanes) :
    tile*lanes+l < lanes*k := by
  have h := Nat.mul_le_mul_right lanes (Nat.succ_le_of_lt ht)
  simp only [Nat.succ_mul] at h
  rw [Nat.mul_comm lanes k]
  omega

def tileWrite (stride tile : Nat) (w : Nat × Nat × Word) : Nat × Nat × Word :=
  (w.1,tileIndex stride tile w.1 w.2.1,w.2.2)

/-- Agreement on exactly the loads of one original invocation is sufficient;
there is no assumption about its arithmetic result or stored outputs. -/
def TileReads (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (source target : Memory) : Prop :=
  ∀ r ∈ ph.reads,
    valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)) =
      valueAt source r.array (r.index.eval (g*k+tile) l)

theorem loadRegisters_batch (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (hl : l < ph.lanes) (source target : Memory)
    (hr : TileReads stride k ph g tile l source target) :
    loadRegisters (batchPhase stride k ph) target g (tile*ph.lanes+l) =
      loadRegisters ph source (g*k+tile) l := by
  unfold loadRegisters batchPhase
  simp only [List.foldl_map,batchIndex_eval_tile stride k ph.lanes _ _ g tile l hl]
  have hreads : ∀ reads : List Read,
      (∀ r ∈ reads, valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)) =
        valueAt source r.array (r.index.eval (g*k+tile) l)) →
      ∀ regs : Registers,
      reads.foldl (fun regs r => regs.insert r.dst
        (valueAt target r.array (tileIndex stride tile r.array (r.index.eval (g*k+tile) l)))) regs =
      reads.foldl (fun regs r => regs.insert r.dst (valueAt source r.array (r.index.eval (g*k+tile) l))) regs := by
    intro reads h
    induction reads with
    | nil => intro regs; rfl
    | cons r rs ih =>
      intro regs
      simp only [List.foldl_cons]
      rw [h r (by simp)]
      exact ih (fun r hr => h r (by simp [hr])) _
  exact hreads ph.reads hr ∅

/-- Actual per-invocation register execution is unchanged by batching, and its
scatter is exactly the original scatter with the shared tile offset attached. -/
theorem laneWrites_batch (stride k : Nat) (ph : Phase) (g tile l : Nat)
    (hl : l < ph.lanes) (source target : Memory)
    (hr : TileReads stride k ph g tile l source target) :
    laneWrites (batchPhase stride k ph) target g (tile*ph.lanes+l) =
      (laneWrites ph source (g*k+tile) l).map (tileWrite stride tile) := by
  have hload := loadRegisters_batch stride k ph g tile l hl source target hr
  unfold laneWrites
  rw [hload]
  simp only [batchPhase,List.map_map,Function.comp_def,tileWrite]
  apply List.map_congr_left
  intro w _
  rw [batchIndex_eval_tile stride k ph.lanes w.array w.index g tile l hl]


/-- Packed lane order is tile-major, preserving each tile's original lane order. -/
theorem range_tiles (lanes k : Nat) :
    List.range (lanes*k) =
      (List.range k).flatMap (fun tile => (List.range lanes).map (fun l => tile*lanes+l)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,List.range_add,ih,List.range_succ,List.flatMap_append]
    simp [Nat.mul_comm]

/-- Exact complete scatter list of the transformed phase. The original tile
memories may differ in their shared rows; each is related only on accessed cells. -/
theorem phaseWrites_batch (stride k : Nat) (ph : Phase) (g : Nat)
    (source : Nat → Memory) (target : Memory)
    (hr : ∀ tile < k, ∀ l < ph.lanes, TileReads stride k ph g tile l (source tile) target) :
    phaseWrites (batchPhase stride k ph) target g =
      (List.range k).flatMap fun tile =>
        (phaseWrites ph (source tile) (g*k+tile)).map (tileWrite stride tile) := by
  change (List.range (ph.lanes*k)).flatMap _ = _
  rw [range_tiles,List.flatMap_assoc]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro tile ht
  change ((List.range ph.lanes).map (fun l => tile*ph.lanes+l)).flatMap _ = _
  rw [List.flatMap_map]
  simp only [phaseWrites,List.map_flatMap,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro l hl
  exact laneWrites_batch stride k ph g tile l (List.mem_range.mp hl) _ target
    (hr tile (List.mem_range.mp ht) l (List.mem_range.mp hl))

/-- This is the actual phase evaluator, with the exact transformed writes. -/
theorem evalPhase_batch_trace (stride k : Nat) (ph : Phase) (g : Nat)
    (source : Nat → Memory) (target : Memory)
    (hr : ∀ tile < k, ∀ l < ph.lanes, TileReads stride k ph g tile l (source tile) target) :
    evalPhase (batchPhase stride k ph) g target =
      ((List.range k).flatMap fun tile =>
        (phaseWrites ph (source tile) (g*k+tile)).map (tileWrite stride tile)).foldl applyWrite target := by
  change (phaseWrites (batchPhase stride k ph) target g).foldl applyWrite target = _
  rw [phaseWrites_batch stride k ph g source target hr]

/-- A word stored by a checked batched phase is computed by precisely the
original tile's register program on its corresponding input cells. -/
theorem evalPhase_batch_value (p : Program) (stride k : Nat) (ph : Phase)
    (g tile l : Nat) (source target : Memory)
    (hg : BlockLower.Good p target) (hb : PhaseInBounds p (batchPhase stride k ph) g)
    (hn : ((batchPhase stride k ph).writeAddresses g).Nodup)
    (ht : tile < k) (hl : l < ph.lanes)
    (hr : TileReads stride k ph g tile l source target) (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride k ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*k+tile) l)) =
      (runRegisters ph.code (loadRegisters ph source (g*k+tile) l)).getD w.value 0#64 := by
  have h := evalPhase_value_written p (batchPhase stride k ph) target g (tile*ph.lanes+l)
    hg hb hn (packed_lane_bound ph.lanes k tile l ht hl)
    {w with index := batchIndex stride k ph.lanes w.array w.index}
    (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have hload := loadRegisters_batch stride k ph g tile l hl source target hr
  have hcode : (batchPhase stride k ph).code = ph.code := by rfl
  simpa only [batchIndex_eval_tile stride k ph.lanes w.array w.index g tile l hl,hload,hcode] using h


/-- Every original group has exactly its quotient/remainder packed coordinates. -/
theorem packed_group_split (d : Dispatch) (q : Nat) (hq : q < d.groups) :
    q/packing d < (batchTiles (tileSize d) d).groups ∧ q%packing d < packing d ∧
      (q/packing d)*packing d+q%packing d = q := by
  exact ⟨Nat.div_lt_div_of_lt_of_dvd (packing_divides d) hq,
    Nat.mod_lt q (packing_pos d),by simpa [Nat.mul_comm] using Nat.div_add_mod q (packing d)⟩

/-- The public builder's admitted phase provides all write-side proof premises. -/
theorem checked_batch_value (p : Program) (hc : p.check = .ok ())
    (stride : Nat) (d : Dispatch) (hd : batchTiles stride d ∈ p.dispatches)
    (ph : Phase) (hph : ph ∈ d.phases) (g tile l : Nat)
    (hg : g < (batchTiles stride d).groups) (ht : tile < packing d) (hl : l < ph.lanes)
    (source target : Memory) (hgood : BlockLower.Good p target)
    (hr : TileReads stride (packing d) ph g tile l source target)
    (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride (packing d) ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*packing d+tile) l)) =
      (runRegisters ph.code (loadRegisters ph source (g*packing d+tile) l)).getD w.value 0#64 := by
  have hm : batchPhase stride (packing d) ph ∈ (batchTiles stride d).phases := by
    rw [batchTiles_phases]
    exact List.mem_map.mpr ⟨ph,hph,rfl⟩
  obtain ⟨hb,hn⟩ := checkedPhase p hc _ hd g hg _ hm
  exact evalPhase_batch_value p stride (packing d) ph g tile l source target
    hgood hb hn ht hl hr w hw


/-- Canonical semantic view of one packed tile. The shared rows are projected
onto the tile's stride; device and constant rows retain their original storage. -/
def tileMemory (stride tile : Nat) (mem : Memory) : Memory :=
  (List.range mem.size).toArray.map fun a =>
    let row := mem.getD a #[]
    if a == 2 || a == 3 then
      (List.range stride).toArray.map fun i => row.getD (i+tile*stride) 0#64
    else row

theorem tileMemory_value (stride tile : Nat) (mem : Memory) (a i : Nat)
    (hi : a = 2 ∨ a = 3 → i < stride) :
    valueAt (tileMemory stride tile mem) a i = valueAt mem a (tileIndex stride tile a i) := by
  by_cases ha : a < mem.size
  · by_cases hs : a = 2 ∨ a = 3
    · have hb : (a == 2 || a == 3) = true := by simpa using hs
      simp [tileMemory,valueAt,tileIndex,Array.getD_eq_getD_getElem?,ha,hb,hs,hi hs]
    · have hb : (a == 2 || a == 3) = false := by simp_all
      simp [tileMemory,valueAt,tileIndex,Array.getD_eq_getD_getElem?,ha,hb,hs]
  · simp [tileMemory,valueAt,Array.getD_eq_getD_getElem?,ha]

theorem tileMemory_reads (stride k : Nat) (ph : Phase) (g tile l : Nat) (target : Memory)
    (hb : ∀ r ∈ ph.reads, r.array = 2 ∨ r.array = 3 → r.index.eval (g*k+tile) l < stride) :
    TileReads stride k ph g tile l (tileMemory stride tile target) target := by
  intro r hr
  exact (tileMemory_value stride tile target r.array _ (hb r hr)).symm

/-- No semantic-memory premise is needed when the original tile is read through
its canonical view; only the source's declared shared-index bounds remain. -/
theorem checked_batch_view_value (p : Program) (hc : p.check = .ok ())
    (stride : Nat) (d : Dispatch) (hd : batchTiles stride d ∈ p.dispatches)
    (ph : Phase) (hph : ph ∈ d.phases) (g tile l : Nat)
    (hg : g < (batchTiles stride d).groups) (ht : tile < packing d) (hl : l < ph.lanes)
    (target : Memory) (hgood : BlockLower.Good p target)
    (hreads : ∀ r ∈ ph.reads, r.array = 2 ∨ r.array = 3 →
      r.index.eval (g*packing d+tile) l < stride)
    (w : Write) (hw : w ∈ ph.writes) :
    valueAt (evalPhase (batchPhase stride (packing d) ph) g target) w.array
      (tileIndex stride tile w.array (w.index.eval (g*packing d+tile) l)) =
      (runRegisters ph.code (loadRegisters ph (tileMemory stride tile target)
        (g*packing d+tile) l)).getD w.value 0#64 :=
  checked_batch_value p hc stride d hd ph hph g tile l hg ht hl _ target hgood
    (tileMemory_reads stride (packing d) ph g tile l target hreads) w hw

end Obend.Hardware.Gpu.NttBatchCorrect
end

section
namespace Obend.Hardware.Gpu.Ntt

/-- Positive integer ceiling division never produces an empty or oversized
piece when the dividend and divisor are both positive. -/
theorem ceil_bounds (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    0 < (n+d-1)/d ∧ (n+d-1)/d ≤ n := by
  constructor
  · apply Nat.div_pos
    · omega
    · exact hd
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have hmul : n ≤ n*d := Nat.le_mul_of_pos_right n hd
    rw [Nat.succ_mul]
    omega

theorem ceil_covers (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    n ≤ d*((n+d-1)/d) := by
  have h := Nat.mod_add_div (n+d-1) d
  have hr := Nat.mod_lt (n+d-1) hd
  omega

theorem uploadDegree_bounds (maximum remaining : Nat) (hm : 0 < maximum)
    (hr : 0 < remaining) :
    0 < uploadDegree maximum remaining ∧ uploadDegree maximum remaining ≤ remaining := by
  have h := ceil_bounds remaining maximum hr hm
  exact ceil_bounds remaining _ hr h.1

theorem uploadDegree_le_maximum (maximum remaining : Nat) (hm : 0 < maximum)
    (hr : 0 < remaining) : uploadDegree maximum remaining ≤ maximum := by
  let uploads := (remaining+maximum-1)/maximum
  have hu : 0 < uploads := (ceil_bounds remaining maximum hr hm).1
  have hc : remaining ≤ maximum*uploads := ceil_covers remaining maximum hr hm
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hu).mpr
  rw [Nat.succ_mul]
  omega

/-- Every scheduled upload makes progress; the schedule covers all binary
layers for every transform size, not just the benchmark sizes. -/
theorem uploadDegrees_sum (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (hf : remaining ≤ fuel) : (uploadDegrees maximum fuel remaining).sum = remaining := by
  induction fuel generalizing remaining with
  | zero =>
    have hz : remaining = 0 := by omega
    simp [uploadDegrees,hz]
  | succ fuel ih =>
    simp only [uploadDegrees]
    split
    · rename_i hz; simp [hz]
    · rename_i hz
      have hb := uploadDegree_bounds maximum remaining hm (by omega)
      rw [List.sum_cons,ih (remaining-uploadDegree maximum remaining) (by omega)]
      omega

theorem uploadDegrees_positive (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (degree : Nat) (hd : degree ∈ uploadDegrees maximum fuel remaining) : 0 < degree := by
  induction fuel generalizing remaining with
  | zero => simp [uploadDegrees] at hd
  | succ fuel ih =>
    simp only [uploadDegrees] at hd
    split at hd
    · simp at hd
    · rename_i hn
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact (uploadDegree_bounds maximum remaining hm (by omega)).1
      · exact ih _ hd

theorem uploadDegrees_bounded (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (degree : Nat) (hd : degree ∈ uploadDegrees maximum fuel remaining) : degree ≤ maximum := by
  induction fuel generalizing remaining with
  | zero => simp [uploadDegrees] at hd
  | succ fuel ih =>
    simp only [uploadDegrees] at hd
    split at hd
    · simp at hd
    · rename_i hn
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact uploadDegree_le_maximum maximum remaining hm (by omega)
      · exact ih _ hd

open Obend.Hardware.ArrayKernel

/-- Composition along the actual constructed list of upload dispatches. The
invariant is indexed by the processed bit count and the current device buffer. -/
theorem buildUploads_invariant (n : Nat) (degrees : List Nat)
    (transform : Dispatch → Dispatch) (I : Nat → Nat → Memory → Prop) (limit : Nat)
    (available : List Dispatch)
    (step : ∀ degree ∈ degrees, ∀ done input mem,
      BlockNtt.dispatch n done degree input (1-input) ∈ available →
      done+degree ≤ limit → I done input mem →
      I (done+degree) (1-input)
        (evalDispatch (transform (BlockNtt.dispatch n done degree input (1-input))) mem))
    (done input : Nat) (mem : Memory)
    (members : ∀ d ∈ (buildUploads n degrees done input).1, d ∈ available)
    (hlimit : done+degrees.sum ≤ limit) (hi : I done input mem) :
    I (done+degrees.sum) (buildUploads n degrees done input).2
      (((buildUploads n degrees done input).1.map transform).foldl
        (fun m d => evalDispatch d m) mem) := by
  induction degrees generalizing done input mem with
  | nil => simpa [buildUploads] using hi
  | cons degree degrees ih =>
    have hs := step degree (by simp) done input mem
      (members _ (by simp [buildUploads]))
      (by simp only [List.sum_cons] at hlimit; omega) hi
    have ht := ih (fun d hd => step d (by simp [hd])) (done+degree) (1-input) _
      (fun d hd => members d (by simp [buildUploads,hd]))
      (by simpa [List.sum_cons,Nat.add_assoc] using hlimit) hs
    simpa [buildUploads,Nat.add_assoc] using ht

/-- Ping-pong device allocation always ends in one of the two device arrays. -/
theorem buildUploads_output (n : Nat) (degrees : List Nat) (done input : Nat)
    (hi : input ≤ 1) : (buildUploads n degrees done input).2 ≤ 1 := by
  induction degrees generalizing done input with
  | nil => exact hi
  | cons degree degrees ih => exact ih (done+degree) (1-input) (by omega)

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower

/-- Every accepted transform's static schedule processes exactly its bit count. -/
theorem uploadSchedule_sum (n : Nat) : (uploadSchedule n).sum = Nat.log2 n := by
  unfold uploadSchedule
  exact uploadDegrees_sum _ _ _ (by split <;> decide) (Nat.le_refl _)

theorem uploadSchedule_bounds (n degree : Nat) (hd : degree ∈ uploadSchedule n) :
    0 < degree ∧ degree ≤ 8 := by
  unfold uploadSchedule at hd
  have hm : 0 < (if n ≤ 1024 then 4 else 8) := by split <;> decide
  have hp := uploadDegrees_positive _ _ _ hm degree hd
  have hb := uploadDegrees_bounded _ _ _ hm degree hd
  have hmax : (if n ≤ 1024 then 4 else 8) ≤ 8 := by split <;> decide
  exact ⟨hp,Nat.le_trans hb hmax⟩

theorem sourceUploads_output (n : Nat) : (sourceUploads n).2 ≤ 1 :=
  buildUploads_output n (uploadSchedule n) 0 0 (by decide)

theorem initial_input (n : Nat) (input : Array Word) :
    (initialMemory (nttBlockProgram n) [input]).getD 0 #[] = input := by
  simp [initialMemory,nttBlockProgram]

/-- Initialization has exactly the shape used by the indexed lowering; no
input-dependent admission condition occurs here. -/
theorem initial_good (n : Nat) (input : Array Word) (hi : input.size = n) :
    BlockLower.Good (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]) := by
  constructor
  · simp [initialMemory,nttBlockProgram]
  · intro a ha
    have hab : a < 5 := ha
    have cases : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;>
      simp [initialMemory,nttBlockProgram,buffer,hi,twiddlePowers_size]

/-- Constant table entries are the actual runtime root powers for every index. -/
theorem initial_twiddle_value (n : Nat) (input : Array Word) (i : Nat) (hi : i < n) :
    (((initialMemory (nttBlockProgram n) [input]).getD 4 #[]).getD i 0#64).toNat =
      modPow (rootOfUnity n) i := by
  rw [initial_twiddles,twiddlePowers_toNat n _ i hi]

theorem maxFold_seed {α : Type} (f : α → Nat) (xs : List α) (seed : Nat) :
    seed ≤ xs.foldl (fun acc x => max acc (f x)) seed := by
  induction xs generalizing seed with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem maxFold_member {α : Type} (f : α → Nat) (xs : List α) (seed : Nat)
    (x : α) (hx : x ∈ xs) : f x ≤ xs.foldl (fun acc x => max acc (f x)) seed := by
  induction xs generalizing seed with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) (maxFold_seed f xs _)
    · exact ih _ hx

/-- Static shared storage covers each actual upload, including its packed tiles. -/
theorem sharedWords_covers (n : Nat) (d : Dispatch) (hd : d ∈ (sourceUploads n).1) :
    BlockNtt.tileSize d * BlockNtt.packing d ≤ sharedWords n :=
  maxFold_member (fun d => BlockNtt.tileSize d * BlockNtt.packing d) _ 1 d hd

theorem good_device (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem)
    (a : Nat) (ha : a ≤ 1) : (mem.getD a #[]).size = n := by
  have h := hg.2 a (by change a < 5; omega)
  have cases : a=0 ∨ a=1 := by omega
  rcases cases with rfl | rfl <;> simpa [buffer,nttBlockProgram] using h

theorem good_shared (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem)
    (a : Nat) (ha : a=2 ∨ a=3) : (mem.getD a #[]).size = sharedWords n := by
  have h := hg.2 a (by change a < 5; omega)
  rcases ha with rfl | rfl <;> simpa [buffer,nttBlockProgram] using h

theorem good_constants (n : Nat) (mem : Memory) (hg : BlockLower.Good (nttBlockProgram n) mem) :
    (mem.getD 4 #[]).size = n := by
  simpa [buffer,nttBlockProgram] using hg.2 4 (by change 4 < 5; decide)

theorem dispatch_good (p : Program) (d : Dispatch) (mem : Memory)
    (hg : BlockLower.Good p mem) : BlockLower.Good p (evalDispatch d mem) := by
  unfold evalDispatch
  induction List.range d.groups generalizing mem with
  | nil => exact hg
  | cons g gs ih => exact ih _ (evalGroup_good p d g mem hg)

theorem output_valid (n i : Nat) (hi : i < n) :
    Valid (nttBlockProgram n) (sourceUploads n).2 i := by
  have h := sourceUploads_output n
  have cases : (sourceUploads n).2 = 0 ∨ (sourceUploads n).2 = 1 := by omega
  rcases cases with hz | hz <;> simp [Valid,buffer,nttBlockProgram,hz,hi]

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource Stockham
open Obend.Apps.ZkNtt (goldilocksPrime)

/-- Initial raw words need not be canonical; the invariant observes residues,
matching the source's first register canonicalization. -/
theorem layout_initial (n ω : Nat) (input : Nat → Nat) :
    LayoutValues 1 n ω input input := by
  intro b hb k hk
  have hk0 : k=0 := by omega
  simp [hk0,initial]

/-- At full size the partial-transform invariant is exactly the natural-order
DFT, with no input or output permutation left to a consumer. -/
theorem layout_final (n ω : Nat) (input values : Nat → Nat)
    (h : LayoutValues n 1 ω input values) (k : Nat) (hk : k < n) :
    values k % goldilocksPrime = dft n ω input k := by
  have hv := h 0 (by decide) k hk
  simpa [partialTransform_eq,dft,sumMod] using hv

/-- Bit-count specialization of the Stockham algebra, in exactly the division
and twiddle coordinates used by the source upload. -/
theorem layout_upload_bits (bits done degree : Nat) (hbits : bits ≤ 32)
    (hd : done+degree ≤ bits) (input before after : Nat → Nat)
    (previous : LayoutValues (2^done) (2^bits / 2^done)
      (rootOfUnity (2^bits)) input before)
    (execute : ∀ g, g < 2^bits / 2^degree → ∀ r, r < 2^degree →
      after (g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done)) =
        dft (2^degree) (rootOfUnity (2^degree))
          (fun t => mulMod (before (g+t*(2^bits/2^degree)))
            (modPow (rootOfUnity (2^bits)) (t*(g%(2^done))*(2^bits/2^degree/2^done)))) r) :
    LayoutValues (2^(done+degree)) (2^bits / 2^(done+degree))
      (rootOfUnity (2^bits)) input after := by
  let m := 2^(bits-(done+degree))
  have hp : 0 < 2^done := Nat.two_pow_pos done
  have hc : 0 < 2^degree := Nat.two_pow_pos degree
  have hdone : done ≤ bits := by omega
  have hdegree : degree ≤ bits := by omega
  have hpm : 2^done*m = 2^(bits-degree) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcm : 2^degree*m = 2^(bits-done) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hn : 2^done*2^degree*m = 2^bits := by
    rw [← Nat.pow_add,← Nat.pow_add]
    congr 1
    omega
  have hdv : 2^bits/2^degree = 2^done*m := by
    rw [Nat.pow_div hdegree (by decide),hpm]
  have hpv : 2^bits/2^done = 2^degree*m := by
    rw [Nat.pow_div hdone (by decide),hcm]
  have hmv : 2^bits/2^degree/2^done = m := by rw [hdv,Nat.mul_div_right m hp]
  have hnew : 2^bits/2^(done+degree) = m := Nat.pow_div hd (by decide)
  have hroot : modPow (rootOfUnity (2^bits)) (2^done*m) = rootOfUnity (2^degree) := by
    rw [hpm]
    exact root_subtransform bits degree hdegree hbits
  have hperiod : modPow (rootOfUnity (2^bits)) (2^done*2^degree*m) = 1 := by
    rw [hn]
    exact root_full bits hbits
  rw [hpv] at previous
  have h := layout_upload (2^done) (2^degree) m (rootOfUnity (2^bits)) input before after
    hp hc hperiod previous (by
      intro g hg r hr
      have he := execute g (by simpa [hdv] using hg) r hr
      simpa only [hmv,hdv,hroot,Nat.mul_div_right m hp] using he)
  simpa only [← Nat.pow_add,hnew] using h

theorem output_cover_bits (bits done degree i : Nat) (hd : done+degree ≤ bits)
    (hi : i < 2^bits) :
    ∃ g, g < 2^bits/2^degree ∧ ∃ r, r < 2^degree ∧
      g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done) = i := by
  let m := 2^(bits-(done+degree))
  have hn : 2^done*2^degree*m = 2^bits := by
    rw [← Nat.pow_add,← Nat.pow_add]
    congr 1
    omega
  have hpm : 2^done*m = 2^(bits-degree) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdv : 2^bits/2^degree = 2^done*m := by
    rw [Nat.pow_div (by omega : degree ≤ bits) (by decide),hpm]
  obtain ⟨g,hg,r,hr,he⟩ := output_cover (2^done) (2^degree) m i
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) (by simpa [hn] using hi)
  exact ⟨g,by simpa [hdv] using hg,r,hr,he⟩

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.NttFieldCorrect
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.GoldilocksSource Obend.Hardware.Gpu.GoldilocksSourceCorrect
open Obend.Apps.ZkNtt (goldilocksPrime)
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Apps.ZkNtt
set_option autoImplicit false

/-- A canonical field value in an allocated register of the actual builder. -/
structure FieldValue (st : Build) (env : Nat → Word) (r value : Nat) : Prop where
  bound : r < st.lengths.size
  value_eq : (evalBuild st env r).toNat = value
  canonical : value < goldilocksPrime

theorem FieldValue.mono {st after : Build} {env : Nat → Word} {r value : Nat}
    (h : FieldValue st env r value) (he : BuildExtends st after) : FieldValue after env r value := by
  exact ⟨Nat.lt_of_lt_of_le h.bound he.size_le,
    congrArg BitVec.toNat (he.frame env r h.bound) |>.trans h.value_eq,h.canonical⟩

theorem add_field (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (glAdd 1 k a b).run st
    FieldValue out.2 env out.1 ((av+bv)%goldilocksPrime) := by
  have hs := glAdd_sound st env 1 k a b ha.bound hb.bound hk
    (by rw [ha.value_eq]; exact ha.canonical) (by rw [hb.value_eq]; exact hb.canonical)
  have hc := glAdd_coordinates st 1 k a b
  dsimp only at hs ⊢
  rw [ha.value_eq,hb.value_eq] at hs
  exact ⟨by omega,hs.2,hs.2 ▸ hs.1⟩

theorem sub_field (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (glSub 1 k a b).run st
    FieldValue out.2 env out.1 ((av+goldilocksPrime-bv)%goldilocksPrime) := by
  have hs := glSub_sound st env 1 k a b ha.bound hb.bound hk
    (by rw [ha.value_eq]; exact ha.canonical) (by rw [hb.value_eq]; exact hb.canonical)
  have hc := glSub_coordinates st 1 k a b
  dsimp only at hs ⊢
  rw [ha.value_eq,hb.value_eq] at hs
  exact ⟨by omega,hs.2,hs.2 ▸ hs.1⟩

/-- The unit-twiddle branch executes the actual field add/sub builders. -/
theorem butterfly_none (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (butterfly k a b none).run st
    BuildExtends st out.2 ∧ out.1.read = none ∧
      FieldValue out.2 env out.1.sum ((av+bv)%goldilocksPrime) ∧
      FieldValue out.2 env out.1.high ((av+goldilocksPrime-bv)%goldilocksPrime) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  have hs := add_field st env k a b av bv hk ha hb
  have hd := sub_field sum.2 env k a b av bv (hk.mono he) (ha.mono he) (hb.mono he)
  simp only [butterfly,bind_run,pure_run]
  change BuildExtends st diff.2 ∧ _ ∧ _ ∧ _
  exact ⟨he.trans hf,True.intro,hs.mono hf,hd⟩

/-- A non-unit twiddle is a fresh source load; it may contain any 64-bit word. -/
theorem butterfly_some (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (index : Ix) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (butterfly k a b (some index)).run st
    BuildExtends st out.2 ∧
      out.1.read = some ⟨st.lengths.size+10,4,index⟩ ∧
      FieldValue out.2 env out.1.sum ((av+bv)%goldilocksPrime) ∧
      FieldValue out.2 env out.1.high
        ((((av+goldilocksPrime-bv)%goldilocksPrime)*(env (st.lengths.size+10)).toNat)%goldilocksPrime) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  let tw := (newWire 1).run diff.2
  let high := (glMul 1 k diff.1 tw.1).run tw.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  have ht := newWire_extends diff.2 1
  have hm := glMul_extends tw.2 1 k diff.1 tw.1
  have hs := add_field st env k a b av bv hk ha hb
  have hd := sub_field sum.2 env k a b av bv (hk.mono he) (ha.mono he) (hb.mono he)
  have hdc := glSub_coordinates sum.2 1 k a b
  have hsc := glAdd_coordinates st 1 k a b
  have htw : tw.1 = st.lengths.size+10 := by
    dsimp only [tw]; rw [newWire_run]
    have hdsize : diff.2.lengths.size = sum.2.lengths.size+5 := hdc.2
    have hssize : sum.2.lengths.size = st.lengths.size+5 := hsc.2
    rw [hdsize,hssize]
  have htb : tw.1 < tw.2.lengths.size := by simp [tw,newWire_run]
  have htv : evalBuild tw.2 env tw.1 = env (st.lengths.size+10) := by
    change evalBuild diff.2 env tw.1 = _
    rw [(hstart.trans (he.trans hf)).fresh_value env tw.1 (by change diff.2.lengths.size ≤ diff.2.lengths.size; exact Nat.le_refl _)]
    rw [htw]
  have hdm := hd.mono ht
  have hval := glMul_sound tw.2 env 1 k diff.1 tw.1 hdm.bound htb
    (((hk.mono he).mono hf).mono ht)
  have hmc := glMul_coordinates tw.2 1 k diff.1 tw.1
  dsimp only at hval
  rw [hdm.value_eq,htv] at hval
  have hhigh : FieldValue high.2 env high.1
      ((((av+goldilocksPrime-bv)%goldilocksPrime)*(env (st.lengths.size+10)).toNat)%goldilocksPrime) :=
    ⟨by dsimp only [high]; omega,hval.2,hval.2 ▸ hval.1⟩
  simp only [butterfly,bind_run,pure_run]
  change BuildExtends st high.2 ∧ _ ∧ _ ∧ _
  exact ⟨((he.trans hf).trans ht).trans hm,by rw [htw],((hs.mono hf).mono ht).mono hm,hhigh⟩

/-- The source loop invariant may mention both the loop accumulator and the
actual register-builder state; every iteration is interpreted, including exit. -/
theorem forIn_state_preserves {α β : Type} (xs : List α)
    (body : α → β → BuildM (ForInStep β)) (P : β → Build → Prop)
    (step : ∀ a b st, P b st → P ((body a b).run st).1.value ((body a b).run st).2)
    (b : β) (st : Build) (hb : P b st) :
    P ((forIn xs b body).run st).1 ((forIn xs b body).run st).2 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st hb
    cases he : (body a b).run st with
    | mk result after =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih out after hp

theorem forIn_extends {α β : Type} (xs : List α)
    (body : α → β → BuildM (ForInStep β))
    (step : ∀ a b st, BuildExtends st ((body a b).run st).2)
    (b : β) (st : Build) : BuildExtends st ((forIn xs b body).run st).2 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using BuildExtends.refl st
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st
    cases he : (body a b).run st with
    | mk result after =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact hp.trans (ih out after)

/-- Both actual butterfly branches allocate fresh destinations only. -/
theorem butterfly_extends (st : Build) (k : GlConsts) (a b : Nat) (twiddle : Option Ix) :
    BuildExtends st ((butterfly k a b twiddle).run st).2 := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  cases twiddle with
  | none =>
    simp only [butterfly,bind_run,pure_run]
    exact he.trans hf
  | some index =>
    let tw := (newWire 1).run diff.2
    simp only [butterfly,bind_run,pure_run]
    exact ((he.trans hf).trans (newWire_extends diff.2 1)).trans
      (glMul_extends tw.2 1 k diff.1 tw.1)

/-- Exact allocation and load metadata of both real butterfly branches. -/
theorem butterfly_coordinates (st : Build) (k : GlConsts) (a b : Nat) (twiddle : Option Ix) :
    let out := (butterfly k a b twiddle).run st
    out.1.sum = st.lengths.size+4 ∧
      out.1.high = st.lengths.size+(if twiddle.isSome then 50 else 9) ∧
      out.2.lengths.size = st.lengths.size+(if twiddle.isSome then 51 else 10) ∧
      out.1.read = twiddle.map (fun index => ⟨st.lengths.size+10,4,index⟩) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have hs := glAdd_coordinates st 1 k a b
  have hd := glSub_coordinates sum.2 1 k a b
  change sum.1 = st.lengths.size+4 ∧ sum.2.lengths.size = st.lengths.size+5 at hs
  change diff.1 = sum.2.lengths.size+4 ∧ diff.2.lengths.size = sum.2.lengths.size+5 at hd
  cases twiddle with
  | none =>
    simp only [butterfly,bind_run,pure_run,Option.isSome_none,Bool.false_eq_true,ite_false,Option.map_none]
    change sum.1 = _ ∧ diff.1 = _ ∧ diff.2.lengths.size = _ ∧ _
    exact ⟨hs.1,by omega,by omega,True.intro⟩
  | some index =>
    let tw := (newWire 1).run diff.2
    let high := (glMul 1 k diff.1 tw.1).run tw.2
    have ht : tw.1 = diff.2.lengths.size ∧ tw.2.lengths.size = diff.2.lengths.size+1 := by
      simp [tw,newWire_run]
    have hm := glMul_coordinates tw.2 1 k diff.1 tw.1
    change high.1 = tw.2.lengths.size+39 ∧ high.2.lengths.size = tw.2.lengths.size+40 at hm
    have htw : tw.1 = st.lengths.size+10 := by omega
    simp only [butterfly,bind_run,pure_run,Option.isSome_some,ite_true,Option.map_some]
    change sum.1 = _ ∧ high.1 = _ ∧ high.2.lengths.size = _ ∧ _
    exact ⟨hs.1,by omega,by omega,by rw [htw]⟩

end Obend.Hardware.Gpu.NttFieldCorrect
end

section
namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open Obend.Apps.ZkNtt (goldilocksPrime)

theorem bind_run {α β : Type} (x : BuildM α) (f : α → BuildM β) (st : Build) :
    (x >>= f).run st = (f (x.run st).1).run (x.run st).2 := by rfl

theorem pure_run {α : Type} (x : α) (st : Build) :
    (pure x : BuildM α).run st = (x,st) := by rfl

/-- Structural invariants of the actual source's stateful loops. The underlying
arithmetic builder is unrestricted; only the returned loop state is observed. -/
theorem forIn_preserves {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (P : β → Prop) (step : ∀ a b st, P b → P ((body a b).run st).1.value)
    (b : β) (st : Build) (hb : P b) : P ((forIn xs b body).run st).1 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st hb
    cases he : (body a b).run st with
    | mk result st' =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih out st' hp

/-- A yielding loop whose visible measure increments once per iteration. -/
theorem forIn_measure {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (measure : β → Nat)
    (step : ∀ a b st, ∃ out st', (body a b).run st = (.yield out,st') ∧ measure out = measure b+1)
    (b : β) (st : Build) : measure ((forIn xs b body).run st).1 = measure b+xs.length := by
  induction xs generalizing b st with
  | nil => simp only [List.forIn_nil,pure_run,List.length_nil,Nat.add_zero]
  | cons a xs ih =>
    obtain ⟨out,st',he,hm⟩ := step a b st
    rw [List.forIn_cons,bind_run,he]
    change measure ((forIn xs out body).run st').1 = _
    rw [ih,hm,List.length_cons]
    omega

abbrev PairState := List Read × Array Nat

def GoodReads (src : Nat) (reads : List Read) : Prop :=
  ∀ r, r ∈ reads → r.array=src ∨ r.array=4

theorem goodReads_append (src : Nat) (reads : List Read) (r : Read)
    (h : GoodReads src reads) (hr : r.array=src ∨ r.array=4) : GoodReads src (reads++[r]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · have : x=r := by simpa using hx
    subst x
    exact hr

/-- Proof-side names for the exact loop bodies elaborated from `phaseAction`.
They are abbreviations, and the action equation below ties them to that sole
source construction. No alternative runtime NTT construction is introduced. -/
abbrev loadBody (src : Nat) (index : Nat → Ix) (r : Nat) (s : PairState) : BuildM (ForInStep PairState) := do
  let a ← newWire 1
  pure (.yield (s.1++[⟨a,src,index r⟩],s.2.push a))

abbrev canonBody (k : GlConsts) (r : Nat) (regs : Array Nat) : BuildM (ForInStep (Array Nat)) := do
  let a ← glCanon 1 k regs[r]!
  pure (.yield (regs.set! r a))

abbrev inputBody (n count p radix stride : Nat) (k : GlConsts) (r : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let tw ← newWire 1
  let exponent := Ix.mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n
  let v ← glMul 1 k s.2[r]! tw
  pure (.yield (s.1++[⟨tw,4,exponent⟩],s.2.set! r v))

abbrev pairBody (n count done radix stride : Nat) (k : GlConsts) (round j : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let bit := radix/2^(round+1)
  let di := j%bit
  let i0 := 2*j-di
  let i1 := i0+bit
  let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride))) (2^(done+round)*(n/count))
  let result ← butterfly k s.2[i0]! s.2[i1]!
    (if stride==1 && di==0 then none else some exponent)
  match result.read with
  | none => pure (.yield (s.1,(s.2.set! i0 result.sum).set! i1 result.high))
  | some r => pure (.yield (s.1++[r],(s.2.set! i0 result.sum).set! i1 result.high))

abbrev roundBody (n count done radix stride : Nat) (k : GlConsts) (round : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let s ← forIn (List.range (radix/2)) s (pairBody n count done radix stride k round)
  pure (.yield s)

theorem load_size (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (loadBody src index)).run st).1.2.size = s.2.size+xs.length := by
  apply forIn_measure xs (loadBody src index) (fun s => s.2.size)
  intro r s st
  refine ⟨_,_,rfl,?_⟩
  simp

theorem load_reads (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build)
    (h : GoodReads src s.1) : GoodReads src ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_preserves xs (loadBody src index) (fun s => GoodReads src s.1) _ s st h
  intro r s st hs
  simp only [loadBody,bind_run,pure_run,ForInStep.value]
  exact goodReads_append src s.1 _ hs (Or.inl rfl)

theorem canon_size (k : GlConsts) (xs : List Nat) (regs : Array Nat) (st : Build) :
    ((forIn xs regs (canonBody k)).run st).1.size = regs.size := by
  apply forIn_preserves xs (canonBody k) (fun rs => rs.size=regs.size) _ regs st rfl
  intro r rs st hs
  simpa only [canonBody,bind_run,pure_run,ForInStep.value,Array.size_set!] using hs

theorem input_size (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (inputBody n count p radix stride k)).run st).1.2.size = s.2.size := by
  apply forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro r ss st hs
  simpa only [inputBody,bind_run,pure_run,ForInStep.value,Array.size_set!] using hs

theorem input_reads (src n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_preserves xs _ (fun ss => GoodReads src ss.1) _ s st h
  intro r ss st hs
  simp only [inputBody,bind_run,pure_run,ForInStep.value]
  exact goodReads_append src ss.1 _ hs (Or.inr rfl)

theorem butterfly_read (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read = some r) : r.array=4 := by
  cases twiddle with
  | none => simp only [butterfly,bind_run,pure_run] at hr; cases hr
  | some exponent =>
    simp only [butterfly,bind_run,pure_run,Option.some.injEq] at hr
    rw [←hr]

theorem pair_size (n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) :
    ((pairBody n count done radix stride k round j s).run st).1.value.2.size = s.2.size := by
  simp only [pairBody,bind_run]
  split <;> simp only [pure_run,ForInStep.value,Array.size_set!]

theorem pair_reads (src n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,bind_run]
  split
  · exact h
  · rename_i r hr
    apply goodReads_append src s.1 r h
    exact Or.inr (butterfly_read _ _ _ _ _ r hr)

theorem rounds_size (n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) :
    ((forIn xs s (roundBody n count done radix stride k)).run st).1.2.size = s.2.size := by
  apply forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro round ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves (List.range (radix/2)) _ (fun ss => ss.2.size=s.2.size) _ ss st hs
  intro j ss st hs
  rw [pair_size]
  exact hs

theorem rounds_reads (src n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_preserves xs _ (fun ss => GoodReads src ss.1) _ s st h
  intro round ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves (List.range (radix/2)) _ (fun ss => GoodReads src ss.1) _ ss st hs
  exact fun j ss st hs => pair_reads src n count done radix stride k round j ss st hs

/-- Definitional decomposition of the sole source action into its actual loops.
This is a proof interface; each loop retains the original source body. -/
theorem phaseAction_run (n count p done degree src : Nat) (first : Bool) (st : Build) :
    (phaseAction n count p done degree src first).run st =
    let radix := 2^degree
    let stride := count/(2^done*radix)
    let loaded := (forIn (List.range radix) ([],#[])
      (loadBody src (phaseLoadIndex n count radix stride first))).run st
    let constants := (glConsts 1).run loaded.2
    let canonical := if first && p==1 then
      (forIn (List.range radix) loaded.1.2 (canonBody constants.1)).run constants.2
      else (loaded.1.2,constants.2)
    let twisted := if first && p>1 then
      (forIn (List.range radix) (loaded.1.1,canonical.1)
        (inputBody n count p radix stride constants.1)).run canonical.2
      else ((loaded.1.1,canonical.1),canonical.2)
    let transformed := (forIn (List.range degree) twisted.1
      (roundBody n count done radix stride constants.1)).run twisted.2
    ((transformed.1.1,transformed.1.2.toList),transformed.2) := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction,hc,ht,Bool.false_eq_true,ite_true,ite_false,bind_run,pure_run] <;> rfl

/-- Every source action emits one output register per radix position. -/
theorem phaseAction_length (n count p done degree src : Nat) (first : Bool) (st : Build) :
    ((phaseAction n count p done degree src first).run st).1.2.length = 2^degree := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp [phaseAction_run,hc,ht,rounds_size,input_size,canon_size,load_size]

/-- Reads added by any source phase are exactly input or twiddle-array reads. -/
theorem phaseAction_reads (n count p done degree src : Nat) (first : Bool) (st : Build) :
    GoodReads src ((phaseAction n count p done degree src first).run st).1.1 := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false] <;>
    apply rounds_reads
  all_goals first | apply input_reads | skip
  all_goals
    apply load_reads
    intro r hr
    cases hr

/-- Actual emitted phase width, discharged from construction rather than an
admission oracle. -/
theorem phase_writes_length (n count bits p done degree src dst : Nat) (first last : Bool) :
    (phase n count bits p done degree src dst first last).writes.length = 2^degree := by
  change (((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).length = _
  simp only [List.length_map,List.length_zipIdx,phaseAction_length]


end Obend.Hardware.Gpu.Ntt.PhaseMetadata
end

section
namespace Obend.Hardware.Gpu.Ntt.PhaseArithmetic
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open ArrayKernel ArrayBuild GoldilocksSource GoldilocksSourceCorrect NttFieldCorrect
open Obend.Apps.ZkNtt (goldilocksPrime)
open BlockNtt RegisterValues
set_option autoImplicit false

/-- The actual source register array represents these canonical field values. -/
def RegValues (st : Build) (env : Nat → Word) (regs : Array Nat) (values : Nat → Nat) : Prop :=
  ∀ i, i < regs.size → FieldValue st env regs[i]! (values i)

theorem RegValues.mono {st after : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RegValues st env regs v) (he : BuildExtends st after) : RegValues after env regs v :=
  fun i hi => (h i hi).mono he

theorem RegValues.set {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RegValues st env regs v) (i r value : Nat) (hi : i < regs.size)
    (hr : FieldValue st env r value) :
    RegValues st env (regs.set! i r) (update v i value) := by
  intro j hj
  simp only [Array.size_set!] at hj
  by_cases he : i=j
  · subst j
    rw [Array.getElem!_set!_self regs i r hi]
    simpa [update_eq] using hr
  · rw [Array.getElem!_set!_ne regs i j r he]
    simpa [update_eq,Ne.symm he] using h j hj

/-- A concrete pair step, including optional constant-buffer input, updates
exactly the two source registers. The twiddle hypothesis concerns the fresh
loaded input register only; all arithmetic and preservation are conclusions. -/
theorem pair_correct (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (twiddle : Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hregs : RegValues st env s.2 values)
    (h0 : 2*j-j%(radix/2^(round+1)) < s.2.size)
    (h1 : 2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (htw : (stride==1 && j%(radix/2^(round+1))==0)=false →
      (env (st.lengths.size+10)).toNat=twiddle)
    (hone : (stride==1 && j%(radix/2^(round+1))==0)=true → twiddle=1) :
    let bit := radix/2^(round+1)
    let i0 := 2*j-j%bit
    let i1 := i0+bit
    let out := (PhaseMetadata.pairBody n count done radix stride k round j s).run st
    BuildExtends st out.2 ∧
      RegValues out.2 env out.1.value.2
        (update (update values i0 ((values i0+values i1)%goldilocksPrime)) i1
          ((((values i0+goldilocksPrime-values i1)%goldilocksPrime)*twiddle)%goldilocksPrime)) := by
  let bit := radix/2^(round+1)
  let di := j%bit
  let i0 := 2*j-di
  let i1 := i0+bit
  let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride))) (2^(done+round)*(n/count))
  have ha := hregs i0 h0
  have hb := hregs i1 h1
  cases hu : (stride==1 && di==0) with
  | false =>
    have h := butterfly_some st env k s.2[i0]! s.2[i1]! (values i0) (values i1)
      exponent hstart hk ha hb
    obtain ⟨result,hr⟩ : ∃ r, (butterfly k s.2[i0]! s.2[i1]! (some exponent)).run st = r := ⟨_,rfl⟩
    dsimp only at h
    rw [hr] at h
    have ht := htw hu
    have high := h.2.2.2
    rw [ht] at high
    have hv := ((hregs.mono h.1).set i0 result.1.sum _ h0 h.2.2.1).set
      i1 result.1.high _ (by simpa only [Array.size_set!] using h1) high
    dsimp only [i0,i1,di,bit,exponent] at hr hu
    dsimp only
    simp only [PhaseMetadata.pairBody,hu,Bool.false_eq_true,ite_false,bind_run,hr,h.2.1,pure_run,ForInStep.value]
    change BuildExtends st result.2 ∧ RegValues result.2 env _ _
    exact ⟨h.1,hv⟩
  | true =>
    have h := butterfly_none st env k s.2[i0]! s.2[i1]! (values i0) (values i1) hk ha hb
    obtain ⟨result,hr⟩ : ∃ r, (butterfly k s.2[i0]! s.2[i1]! none).run st = r := ⟨_,rfl⟩
    dsimp only at h
    rw [hr] at h
    have ht := hone hu
    have high := h.2.2.2
    have hv := ((hregs.mono h.1).set i0 result.1.sum _ h0 h.2.2.1).set
      i1 result.1.high _ (by simpa only [Array.size_set!] using h1) high
    dsimp only [i0,i1,di,bit] at hr hu
    dsimp only
    simp only [PhaseMetadata.pairBody,hu,ite_true,bind_run,hr,h.2.1,pure_run,ForInStep.value]
    change BuildExtends st result.2 ∧ RegValues result.2 env _ _
    simpa only [i0,i1,di,bit,ht,Nat.mul_one,Nat.mod_mod,goldilocksPrime] using And.intro h.1 hv

/-- Input-only agreement with the constant-buffer reads present in the actual
source action. This says nothing about any computed register or output. -/
def Twiddles (env : Nat → Word) (reads : List Read) (table : Ix → Nat) : Prop :=
  ∀ r, r ∈ reads → r.array=4 → (env r.dst).toNat=table r.index

def pairExponent (n count done radix stride round j : Nat) : Ix :=
  mulI (addI (.mod .lane stride) (.lit (j%(radix/2^(round+1))*stride)))
    (2^(done+round)*(n/count))

def pairTwiddle (n count done radix stride round j : Nat) (table : Ix → Nat) : Nat :=
  if stride==1 && j%(radix/2^(round+1))==0 then 1
  else table (pairExponent n count done radix stride round j)

theorem pair_twiddle_read (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build)
    (hu : (stride==1 && j%(radix/2^(round+1))==0)=false) :
    (⟨st.lengths.size+10,4,pairExponent n count done radix stride round j⟩ : Read) ∈
      ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 := by
  have h := (butterfly_coordinates st k
    s.2[2*j-j%(radix/2^(round+1))]!
    s.2[2*j-j%(radix/2^(round+1))+radix/2^(round+1)]!
    (some (pairExponent n count done radix stride round j))).2.2.2
  simp only [Option.map_some] at h
  dsimp only [pairExponent] at h ⊢
  simp only [PhaseMetadata.pairBody,hu,Bool.false_eq_true,ite_false,bind_run,h,pure_run,ForInStep.value]
  simp

theorem pair_values (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hregs : RegValues st env s.2 values)
    (h0 : 2*j-j%(radix/2^(round+1)) < s.2.size)
    (h1 : 2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 table) :
    let out := (PhaseMetadata.pairBody n count done radix stride k round j s).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.value.2
      (pairStep (radix/2^(round+1)) (pairTwiddle n count done radix stride round j table) j values) := by
  apply pair_correct n count done radix stride round j k s st env values
    (pairTwiddle n count done radix stride round j table) hstart hk hregs h0 h1
  · intro hu
    have h := hreads _ (pair_twiddle_read n count done radix stride round j k s st hu) rfl
    simpa only [pairTwiddle,hu,Bool.false_eq_true,ite_false] using h
  · intro hu
    simp only [pairTwiddle,hu,ite_true]

theorem pair_yield (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) :
    ∃ after out, (PhaseMetadata.pairBody n count done radix stride k round j s).run st = (.yield out,after) := by
  simp only [PhaseMetadata.pairBody,bind_run]
  split <;> exact ⟨_,_,rfl⟩

theorem pair_reads_mono (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [PhaseMetadata.pairBody,bind_run]
  split
  · exact hr
  · exact List.mem_append_left _ hr

theorem pairLoop_reads_mono (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro j ss before hh
  exact pair_reads_mono n count done radix stride round j k ss before r hh

/-- Universal refinement of the actual stateful pair loop. The only value
premise beyond its input register values binds its concrete constant reads. -/
theorem pairLoop_values (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word)
    (values : Nat → Nat) (table : Ix → Nat) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (hregs : RegValues st env s.2 values)
    (hbounds : ∀ j, j ∈ xs →
      2*j-j%(radix/2^(round+1)) < s.2.size ∧
      2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (xs.foldl (fun v j => pairStep (radix/2^(round+1))
        (pairTwiddle n count done radix stride round j table) j v) values) := by
  induction xs generalizing s st values with
  | nil =>
    simpa only [List.forIn_nil,pure_run,List.foldl_nil] using And.intro (BuildExtends.refl st) hregs
  | cons j xs ih =>
    obtain ⟨after,ss,hr⟩ := pair_yield n count done radix stride round j k s st
    have hrun : (forIn (j::xs) s (PhaseMetadata.pairBody n count done radix stride k round)).run st =
        (forIn xs ss (PhaseMetadata.pairBody n count done radix stride k round)).run after := by
      rw [List.forIn_cons,bind_run,hr]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 table := by
      rw [hr]
      intro r hmem ha
      exact hreads r (pairLoop_reads_mono n count done radix stride round k xs ss after r hmem) ha
    have hhead := pair_values n count done radix stride round j k s st env values table hstart hk hregs
      (hbounds j (by simp)).1 (hbounds j (by simp)).2 hheadReads
    rw [hr] at hhead
    have hsize := PhaseMetadata.pair_size n count done radix stride k round j s st
    rw [hr] at hsize
    change ss.2.size = s.2.size at hsize
    have htailBounds : ∀ j, j ∈ xs →
        2*j-j%(radix/2^(round+1)) < ss.2.size ∧
        2*j-j%(radix/2^(round+1))+radix/2^(round+1) < ss.2.size := by
      intro jj hj
      simpa only [hsize] using hbounds jj (by simp [hj])
    have htail := ih ss after
      (pairStep (radix/2^(round+1)) (pairTwiddle n count done radix stride round j table) j values)
      (hstart.trans hhead.1) (hk.mono hhead.1) hhead.2 htailBounds hreads
    dsimp only
    rw [hrun,List.foldl_cons]
    exact ⟨hhead.1.trans htail.1,htail.2⟩

theorem pairLoop_size (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) :
    ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.2.size = s.2.size := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro j ss before hh
  rw [PhaseMetadata.pair_size]
  exact hh

theorem rounds_reads_mono (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro round ss before hh
  simp only [PhaseMetadata.roundBody,bind_run,pure_run,ForInStep.value]
  exact pairLoop_reads_mono n count done radix stride round k _ ss before r hh

/-- The actual nested round loops implement the ordered mathematical field
rounds. All memory values enter only through their concrete source reads. -/
theorem rounds_values (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word)
    (values : Nat → Nat) (table : Ix → Nat) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (hregs : RegValues st env s.2 values)
    (hbounds : ∀ round, round ∈ xs → ∀ j, j < radix/2 →
      2*j-j%(radix/2^(round+1)) < s.2.size ∧
      2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (xs.foldl (fun v round => roundValues (radix/2) (radix/2^(round+1))
        (fun j => pairTwiddle n count done radix stride round j table) v) values) := by
  induction xs generalizing s st values with
  | nil =>
    simpa only [List.forIn_nil,pure_run,List.foldl_nil] using And.intro (BuildExtends.refl st) hregs
  | cons round xs ih =>
    obtain ⟨ss,after,hr⟩ : ∃ ss after,
        (forIn (List.range (radix/2)) s (PhaseMetadata.pairBody n count done radix stride k round)).run st =
          (ss,after) := ⟨_,_,rfl⟩
    have hrun : (forIn (round::xs) s (PhaseMetadata.roundBody n count done radix stride k)).run st =
        (forIn xs ss (PhaseMetadata.roundBody n count done radix stride k)).run after := by
      simp only [List.forIn_cons,bind_run,PhaseMetadata.roundBody,pure_run,hr]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((forIn (List.range (radix/2)) s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 table := by
      rw [hr]
      intro r hmem ha
      exact hreads r (rounds_reads_mono n count done radix stride k xs ss after r hmem) ha
    have hhead := pairLoop_values n count done radix stride round k (List.range (radix/2)) s st env values table
      hstart hk hregs (fun j hj => hbounds round (by simp) j (List.mem_range.mp hj)) hheadReads
    rw [hr] at hhead
    have hsize := pairLoop_size n count done radix stride round k (List.range (radix/2)) s st
    rw [hr] at hsize
    change ss.2.size = s.2.size at hsize
    have htailBounds : ∀ rr, rr ∈ xs → ∀ j, j < radix/2 →
        2*j-j%(radix/2^(rr+1)) < ss.2.size ∧
        2*j-j%(radix/2^(rr+1))+radix/2^(rr+1) < ss.2.size := by
      intro rr hrr j hj
      simpa only [hsize] using hbounds rr (by simp [hrr]) j hj
    have htail := ih ss after
      (roundValues (radix/2) (radix/2^(round+1))
        (fun j => pairTwiddle n count done radix stride round j table) values)
      (hstart.trans hhead.1) (hk.mono hhead.1) (by simpa only [roundValues_eq] using hhead.2) htailBounds hreads
    dsimp only
    rw [hrun,List.foldl_cons]
    exact ⟨hhead.1.trans htail.1,htail.2⟩

end Obend.Hardware.Gpu.Ntt.PhaseArithmetic
end

section
namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open Obend.Apps.ZkNtt (goldilocksPrime)

/-- The invariant is required only for iterations actually present in the list. -/
theorem forIn_preserves_mem {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (P : β → Prop) (step : ∀ a, a ∈ xs → ∀ b st, P b → P ((body a b).run st).1.value)
    (b : β) (st : Build) (hb : P b) : P ((forIn xs b body).run st).1 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a (by simp) b st hb
    cases he : (body a b).run st with
    | mk result st' =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih (fun x hx => step x (by simp [hx])) out st' hp

def ReadsWhere (P : Read → Prop) (reads : List Read) : Prop := ∀ r, r ∈ reads → P r

theorem readsWhere_append (P : Read → Prop) (reads : List Read) (r : Read)
    (h : ReadsWhere P reads) (hr : P r) : ReadsWhere P (reads++[r]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · have : x=r := by simpa using hx
    subst x
    exact hr

abbrev inputExponent (n count p radix stride r : Nat) : Ix :=
  .mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n

abbrev roundExponent (n count done radix stride round j : Nat) : Ix :=
  mulI (addI (.mod .lane stride) (.lit ((j%(radix/2^(round+1)))*stride)))
    (2^(done+round)*(n/count))

/-- Exhaustive actual source read shapes. The read-register number is unrestricted
here; allocation freshness is a separate structural contract. -/
def ReadOrigin (n count p done degree src : Nat) (first : Bool) (r : Read) : Prop :=
  let radix := 2^degree
  let stride := count/(2^done*radix)
  (r.array=src ∧ ∃ slot, slot<radix ∧ r.index=phaseLoadIndex n count radix stride first slot) ∨
  (r.array=4 ∧ ∃ slot, slot<radix ∧ r.index=inputExponent n count p radix stride slot) ∨
  (r.array=4 ∧ ∃ round, round<degree ∧ ∃ pair, pair<radix/2 ∧
    r.index=roundExponent n count done radix stride round pair)

theorem load_reads_where (P : Read → Prop) (src : Nat) (index : Nat → Ix) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hload : ∀ slot, slot ∈ xs → ∀ wire, P ⟨wire,src,index slot⟩) :
    ReadsWhere P ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro slot hslot ss st hs
  simp only [loadBody,bind_run,pure_run,ForInStep.value]
  exact readsWhere_append P ss.1 _ hs (hload slot hslot _)

theorem input_reads_where (P : Read → Prop) (n count p radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ slot, slot ∈ xs → ∀ wire, P ⟨wire,4,inputExponent n count p radix stride slot⟩) :
    ReadsWhere P ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro slot hslot ss st hs
  simp only [inputBody,bind_run,pure_run,ForInStep.value]
  exact readsWhere_append P ss.1 _ hs (hread slot hslot _)

theorem butterfly_read_origin (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read=some r) :
    ∃ exponent, twiddle=some exponent ∧ r.array=4 ∧ r.index=exponent := by
  cases twiddle with
  | none => simp only [butterfly,bind_run,pure_run] at hr; cases hr
  | some exponent =>
    simp only [butterfly,bind_run,pure_run,Option.some.injEq] at hr
    exact ⟨exponent,rfl,by rw [←hr],by rw [←hr]⟩

theorem pair_reads_where (P : Read → Prop) (n count done radix stride : Nat) (k : GlConsts)
    (round j : Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ wire, P ⟨wire,4,roundExponent n count done radix stride round j⟩) :
    ReadsWhere P ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,bind_run]
  split
  · exact h
  · rename_i r hr
    apply readsWhere_append P s.1 r h
    obtain ⟨exponent,ht,ha,hi⟩ := butterfly_read_origin _ _ _ _ _ r hr
    split at ht
    · cases ht
    · simp only [Option.some.injEq] at ht
      cases r with
      | mk dst array index =>
        simp only at ha hi
        subst array
        subst index
        rw [←ht]
        exact hread dst

theorem rounds_reads_where (P : Read → Prop) (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ round, round ∈ xs → ∀ pair, pair < radix/2 → ∀ wire,
      P ⟨wire,4,roundExponent n count done radix stride round pair⟩) :
    ReadsWhere P ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro round hround ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves_mem (List.range (radix/2)) _ (fun ss => ReadsWhere P ss.1) _ ss st hs
  intro pair hpair ss st hs
  exact pair_reads_where P n count done radix stride k round pair ss st hs
    (hread round hround pair (List.mem_range.mp hpair))

/-- All reads in the sole phase builder are accounted for by its three source
read sites, with the actual loop membership bounds. -/
theorem phaseAction_reads_where (P : Read → Prop) (n count p done degree src : Nat)
    (first : Bool) (st : Build)
    (hload : ∀ slot, slot<2^degree → ∀ wire,
      P ⟨wire,src,phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first slot⟩)
    (hinput : ∀ slot, slot<2^degree → ∀ wire,
      P ⟨wire,4,inputExponent n count p (2^degree) (count/(2^done*2^degree)) slot⟩)
    (hround : ∀ round, round<degree → ∀ pair, pair<2^degree/2 → ∀ wire,
      P ⟨wire,4,roundExponent n count done (2^degree) (count/(2^done*2^degree)) round pair⟩) :
    ReadsWhere P ((phaseAction n count p done degree src first).run st).1.1 := by
  have hl := load_reads_where P src
    (phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first)
    (List.range (2^degree)) ([],#[]) st
    (by intro r hr; cases hr) (fun slot hslot => hload slot (List.mem_range.mp hslot))
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false]
  all_goals
    apply rounds_reads_where
    · first
      | apply input_reads_where
        · exact hl
        · intro slot hslot
          exact hinput slot (List.mem_range.mp hslot)
      | exact hl
    · intro round hround' pair hpair
      exact hround round (List.mem_range.mp hround') pair hpair

theorem phaseAction_read_origin (n count p done degree src : Nat) (first : Bool)
    (st : Build) (r : Read) (hr : r ∈ ((phaseAction n count p done degree src first).run st).1.1) :
    ReadOrigin n count p done degree src first r := by
  apply phaseAction_reads_where (ReadOrigin n count p done degree src first) n count p done degree src first st
    (fun slot hs wire => Or.inl ⟨rfl,slot,hs,rfl⟩)
    (fun slot hs wire => Or.inr (Or.inl ⟨rfl,slot,hs,rfl⟩))
    (fun round hr pair hp wire => Or.inr (Or.inr ⟨rfl,round,hr,pair,hp,rfl⟩)) r hr

/-- The emitted phase's actual reads have only the three exhaustively proved
source index forms. -/
theorem phase_read_origin (n count bits p done degree src dst : Nat) (first last : Bool)
    (r : Read) (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    ReadOrigin n count p done degree src first r :=
  phaseAction_read_origin n count p done degree src first {} r hr

/-- Every actual read is bounded in its declared source or full twiddle row.
All loop, lane, and transform premises are ordinary numeric shape bounds. -/
theorem phase_read_index_bound (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (hb : bits ≤ total) (h : done+degree ≤ bits)
    (hg : group < 2^total/2^bits) (hl : lane < 2^bits/2^degree)
    (r : Read) (hr : r ∈ (phase (2^total) (2^bits) bits p done degree src dst first last).reads) :
    (r.array=src ∧ r.index.eval group lane < (if first then 2^total else 2^bits)) ∨
      (r.array=4 ∧ r.index.eval group lane < 2^total) := by
  have ho := phase_read_origin (2^total) (2^bits) bits p done degree src dst first last r hr
  rcases ho with ⟨ha,slot,hslot,hi⟩ | ⟨ha,slot,hslot,hi⟩ | ⟨ha,round,hround,pair,hpair,hi⟩
  · left
    refine ⟨ha,?_⟩
    rw [hi]
    cases first with
    | false => exact phase_load_later_lt (2^total) bits done degree group lane slot h hl hslot
    | true => exact phase_load_first_lt total bits done degree group lane slot hb h hg hl hslot
  · right
    refine ⟨ha,?_⟩
    rw [hi]
    exact Nat.mod_lt _ (Nat.two_pow_pos total)
  · right
    refine ⟨ha,?_⟩
    rw [hi]
    simpa only [roundExponent, mulI, addI_eq, Ix.eval, phasePairOffset_eq] using
      phase_round_exponent_lt total bits done degree round lane pair hb h hround

end Obend.Hardware.Gpu.Ntt.PhaseMetadata
end

section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource ArrayKernel BlockNtt RegisterValues PhaseArithmetic
open Obend.Apps.ZkNtt (goldilocksPrime)

theorem difLayer_canonical (bits level : Nat) (hl : level<bits) (input : Nat → Nat)
    (i : Nat) (hi : i<2^bits) : difLayer bits level input i < goldilocksPrime := by
  induction bits generalizing level input i with
  | zero => omega
  | succ bits ih =>
    have hp : 2^(bits+1)=2^bits+2^bits := by rw [Nat.pow_succ]; omega
    cases level with
    | zero =>
      simp only [difLayer_succ_zero, difLayer_succ_succ]
      split <;> exact Nat.mod_lt _ (by decide)
    | succ level =>
      simp only [difLayer_succ_zero, difLayer_succ_succ]
      split
      · rename_i h
        exact ih level (by omega) input i h
      · exact ih level (by omega) _ _ (by rw [hp] at hi; omega)

theorem difStages_canonical (bits start count : Nat) (hc : start+count≤bits) (input : Nat → Nat)
    (hinput : ∀ i, i<2^bits → input i<goldilocksPrime) (i : Nat) (hi : i<2^bits) :
    difStages bits start count input i < goldilocksPrime := by
  cases count with
  | zero => exact hinput i hi
  | succ count => exact difLayer_canonical bits (start+count) (by omega) _ i hi

/-- The source's omitted unit-twiddle load has exactly the same power-table value. -/
theorem pairTwiddle_power (n count done radix stride round j group lane : Nat) :
    pairTwiddle n count done radix stride round j
      (fun ix => modPow (rootOfUnity n) (ix.eval group lane)) =
      modPow (rootOfUnity n)
        (phasePairOffset stride lane j (radix/2^(round+1)) * (2^(done+round)*(n/count))) := by
  unfold pairTwiddle
  split
  · rename_i h
    have hh : stride=1 ∧ j%(radix/2^(round+1))=0 := by simpa using h
    simp [phasePairOffset_eq,hh.1,hh.2,Nat.mod_one]
  · simp only [pairExponent, mulI, addI_eq, Ix.eval, phasePairOffset_eq]

/-- A prefix of the actual register-round fold equals the same prefix of the
whole-vector levels, allowing arbitrary fused register degrees. -/
theorem phase_rounds_stages (total bits done degree rounds group lane : Nat)
    (ht : total≤32) (hb : bits≤total) (hdegree : done+degree≤bits) (hrounds : rounds≤degree)
    (hlane : lane<2^bits/2^degree) (input values : Nat → Nat)
    (hvalues : ∀ r, r<2^degree → values r=input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
    (hinput : ∀ i, i<2^bits → input i<goldilocksPrime) :
    ∀ r, r<2^degree →
    ((List.range rounds).foldl (fun v round => roundValues (2^degree/2) (2^degree/2^(round+1))
      (fun j => pairTwiddle (2^total) (2^bits) done (2^degree) (2^bits/(2^done*2^degree)) round j
        (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane))) v) values) r =
    difStages bits done rounds input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  induction rounds with
  | zero => exact hvalues
  | succ rounds ih =>
    intro r hr
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    have htw : (fun j => pairTwiddle (2^total) (2^bits) done (2^degree)
        (2^bits/(2^done*2^degree)) rounds j
        (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane))) =
        (fun j => modPow (rootOfUnity (2^total))
          (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(rounds+1)) *
            (2^(done+rounds)*(2^total/2^bits)))) := by
      funext j
      exact pairTwiddle_power _ _ _ _ _ _ _ _ _
    rw [htw]
    apply phase_roundValues_layer total bits done degree rounds lane r ht hb hdegree (by omega) hlane hr
    · exact ih (by omega)
    · intro rr hrr
      rw [ih (by omega) rr hrr]
      exact difStages_canonical bits done rounds (by omega) input hinput _
        (phase_index_lt bits done degree lane rr hdegree hlane hrr)

/-- The first phase's common mathematical input for both canonicalization and
nontrivial input twiddle branches. -/
def preparedInput (n count p group : Nat) (first : Bool) (entry : Nat → Nat) (i : Nat) : Nat :=
  if first then mulMod (entry i) (modPow (rootOfUnity n) (i*(group%p)*(n/count/p))) else entry i

theorem preparedInput_canonical (n count p group bound : Nat) (first : Bool) (entry : Nat → Nat)
    (h : first=false → ∀ i, i<bound → entry i<goldilocksPrime) :
    ∀ i, i<bound → preparedInput n count p group first entry i < goldilocksPrime := by
  intro i hi
  cases first with
  | false => exact h rfl i hi
  | true => exact Nat.mod_lt _ (by decide)

theorem inputExponent_power (total bits p done degree group lane r : Nat) (ht : total≤32) :
    modPow (rootOfUnity (2^total))
      ((PhaseMetadata.inputExponent (2^total) (2^bits) p (2^degree)
        (2^bits/(2^done*2^degree)) r).eval group lane) =
      modPow (rootOfUnity (2^total))
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r *
          (group%p)*(2^total/2^bits/p)) := by
  simp only [PhaseMetadata.inputExponent, mulI, Ix.eval, phaseIndex_eval]
  rw [←root_periodic total ht]
  congr 1
  exact (Nat.mul_assoc _ _ _).symm

/-- The actual initialization branches have the same whole-tile input function. -/
theorem prepared_register_eq (total bits p done degree group lane r : Nat) (first : Bool)
    (entry values : Nat → Nat) (ht : total≤32)
    (hv : values r=entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) :
    (if first then if p=1 then values r%goldilocksPrime else
      mulMod (values r) (modPow (rootOfUnity (2^total))
        ((PhaseMetadata.inputExponent (2^total) (2^bits) p (2^degree)
          (2^bits/(2^done*2^degree)) r).eval group lane)) else values r) =
      preparedInput (2^total) (2^bits) p group first entry
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  cases first with
  | false => exact hv
  | true =>
    by_cases hp : p=1
    · simp [hp,preparedInput,hv,mulMod,Nat.mod_one]
    · simp only [ite_true,if_neg hp,preparedInput]
      rw [inputExponent_power _ _ _ _ _ _ _ _ ht,hv]

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open Obend.Apps.ZkNtt (goldilocksPrime)
open GoldilocksSourceCorrect NttFieldCorrect

/-- Actual loaded registers are distinct and have already been allocated. -/
structure ReadAllocation (st : Build) (reads : List Read) : Prop where
  unique : (reads.map Read.dst).Nodup
  bound : ∀ r, r ∈ reads → r.dst < st.lengths.size

theorem ReadAllocation.mono {before after : Build} {reads : List Read}
    (h : ReadAllocation before reads) (he : BuildExtends before after) : ReadAllocation after reads :=
  ⟨h.unique,fun r hr => Nat.lt_of_lt_of_le (h.bound r hr) he.size_le⟩

theorem ReadAllocation.append {before after : Build} {reads : List Read}
    (h : ReadAllocation before reads) (he : BuildExtends before after) (r : Read)
    (fresh : before.lengths.size ≤ r.dst) (bound : r.dst < after.lengths.size) :
    ReadAllocation after (reads++[r]) := by
  constructor
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨h.unique,by simp,?_⟩
    intro a ha b hb
    obtain ⟨read,hm,rfl⟩ := List.mem_map.mp ha
    have hbr : b=r.dst := by simpa using hb
    have hlt := h.bound read hm
    omega
  · intro read hr
    rcases List.mem_append.mp hr with hr | hr
    · exact Nat.lt_of_lt_of_le (h.bound read hr) he.size_le
    · have : read=r := by simpa using hr
      subst read
      exact bound

theorem load_allocation (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build)
    (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (loadBody src index)).run st).2
      ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro slot ss state hs
  simp only [loadBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  apply hs.append (newWire_extends state 1)
  · simp [newWire_run]
  · simp [newWire_run]

theorem canon_allocation (k : GlConsts) (xs : List Nat) (regs : Array Nat) (reads : List Read)
    (st : Build) (h : ReadAllocation st reads) :
    ReadAllocation ((forIn xs regs (canonBody k)).run st).2 reads := by
  apply forIn_state_preserves xs _ (fun _ state => ReadAllocation state reads) _ regs st h
  intro slot rs state hs
  simp only [canonBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run]
  exact hs.mono (glCanon_extends state 1 k rs[slot]!)

theorem input_allocation (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (inputBody n count p radix stride k)).run st).2
      ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro slot ss state hs
  simp only [inputBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  have hn := newWire_extends state 1
  have hm := glMul_extends ((newWire 1).run state).2 1 k ss.2[slot]! ((newWire 1).run state).1
  apply hs.append (hn.trans hm)
  · simp [newWire_run]
  · have hb : ((newWire 1).run state).1 < ((newWire 1).run state).2.lengths.size := by simp [newWire_run]
    exact Nat.lt_of_lt_of_le hb hm.size_le

theorem butterfly_read_bounds (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read=some r) :
    st.lengths.size ≤ r.dst ∧ r.dst < ((butterfly k a b twiddle).run st).2.lengths.size := by
  have hc := butterfly_coordinates st k a b twiddle
  dsimp only at hc
  rw [hc.2.2.2] at hr
  cases twiddle with
  | none => cases hr
  | some index =>
    simp only [Option.map_some,Option.some.injEq] at hr
    rw [←hr]
    simp only [Option.isSome_some,Bool.true_eq,ite_true] at hc
    constructor <;> dsimp only <;> omega

theorem pair_allocation (n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((pairBody n count done radix stride k round j s).run st).2
      ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,PhaseMetadata.bind_run]
  split
  · exact h.mono (butterfly_extends _ _ _ _ _)
  · rename_i r hr
    have hb := butterfly_read_bounds _ _ _ _ _ r hr
    exact h.append (butterfly_extends _ _ _ _ _) r hb.1 hb.2

theorem rounds_allocation (n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadAllocation st s.1) :
    ReadAllocation ((forIn xs s (roundBody n count done radix stride k)).run st).2
      ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_state_preserves xs _ (fun ss state => ReadAllocation state ss.1) _ s st h
  intro round ss state hs
  simp only [roundBody,PhaseMetadata.bind_run,PhaseMetadata.pure_run,ForInStep.value]
  apply forIn_state_preserves (List.range (radix/2)) _ (fun ss state => ReadAllocation state ss.1) _ ss state hs
  exact fun j ss state hs => pair_allocation n count done radix stride k round j ss state hs

/-- Fresh read destinations are an unconditional fact of actual phase construction. -/
theorem phaseAction_allocation (n count p done degree src : Nat) (first : Bool) (st : Build) :
    ReadAllocation ((phaseAction n count p done degree src first).run st).2
      ((phaseAction n count p done degree src first).run st).1.1 := by
  let radix := 2^degree
  let stride := count/(2^done*radix)
  let loaded := (forIn (List.range radix) ([],#[])
    (loadBody src (phaseLoadIndex n count radix stride first))).run st
  have hl : ReadAllocation loaded.2 loaded.1.1 :=
    load_allocation src _ _ ([],#[]) st ⟨by simp,by intro r hr; cases hr⟩
  let constants := (glConsts 1).run loaded.2
  have hk : ReadAllocation constants.2 loaded.1.1 := hl.mono (glConsts_extends loaded.2 1 (by decide))
  let canonical := if first && p==1 then
    (forIn (List.range radix) loaded.1.2 (canonBody constants.1)).run constants.2
    else (loaded.1.2,constants.2)
  have hc : ReadAllocation canonical.2 loaded.1.1 := by
    dsimp only [canonical]
    split
    · exact canon_allocation _ _ _ _ _ hk
    · exact hk
  let twisted := if first && p>1 then
    (forIn (List.range radix) (loaded.1.1,canonical.1)
      (inputBody n count p radix stride constants.1)).run canonical.2
    else ((loaded.1.1,canonical.1),canonical.2)
  have ht : ReadAllocation twisted.2 twisted.1.1 := by
    dsimp only [twisted]
    split
    · exact input_allocation _ _ _ _ _ _ _ _ _ hc
    · exact hc
  let transformed := (forIn (List.range degree) twisted.1
    (roundBody n count done radix stride constants.1)).run twisted.2
  have hf : ReadAllocation transformed.2 transformed.1.1 := rounds_allocation _ _ _ _ _ _ _ _ _ ht
  rw [phaseAction_run]
  exact hf

theorem phase_reads_unique (n count bits p done degree src dst : Nat) (first last : Bool) :
    ((phase n count bits p done degree src dst first last).reads.map Read.dst).Nodup :=
  (phaseAction_allocation n count p done degree src first {}).unique

private theorem loadFold_frame (reads : List Read) (mem : Memory) (group lane key : Nat)
    (regs : Registers) (h : ∀ r, r ∈ reads → r.dst ≠ key) :
    (reads.foldl (fun regs r => regs.insert r.dst
      ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) regs).getD key 0#64 = regs.getD key 0#64 := by
  induction reads generalizing regs with
  | nil => rfl
  | cons r reads ih =>
    rw [List.foldl_cons,ih _ (fun rr hr => h rr (by simp [hr]))]
    have hn := h r (by simp)
    simp [Std.HashMap.getD_insert,hn,Ne.symm hn]

private theorem loadFold_member (reads : List Read) (mem : Memory) (group lane : Nat)
    (regs : Registers) (hu : (reads.map Read.dst).Nodup)
    (r : Read) (hr : r ∈ reads) :
    (reads.foldl (fun regs r => regs.insert r.dst
      ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) regs).getD r.dst 0#64 =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 := by
  induction reads generalizing regs with
  | nil => cases hr
  | cons read reads ih =>
    simp only [List.map_cons,List.nodup_cons] at hu
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with h | h
    · subst r
      rw [loadFold_frame reads mem group lane read.dst _ (by
        intro r hr he
        apply hu.1
        exact List.mem_map.mpr ⟨r,hr,he⟩)]
      simp [Std.HashMap.getD_insert]
    · exact ih _ hu.2 h

/-- Every actual declared load is visible at its register in the phase's real
HashMap loader. Freshness prevents later reads from overwriting that binding. -/
theorem phase_loadRegisters_value (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane : Nat) (r : Read)
    (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    (loadRegisters (phase n count bits p done degree src dst first last) mem group lane).getD r.dst 0#64 =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 := by
  exact loadFold_member _ mem group lane ∅ (phase_reads_unique n count bits p done degree src dst first last) r hr

end Obend.Hardware.Gpu.Ntt.PhaseMetadata
end

end
