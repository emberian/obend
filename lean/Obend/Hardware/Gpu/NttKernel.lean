module
public import Obend.Hardware.Gpu.NttSpec
public import Obend.Hardware.Gpu.PhaseSemantics
public import Obend.Hardware.Gpu.BlockLower
public import Obend.Hardware.Gpu.GoldilocksSourceCorrect
public import Obend.Hardware.Gpu.BlockPlan
public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource
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
  let ω2 := ω * ω % goldilocksP
  let ev := nttFast ((Array.range half).map fun i => xs[2 * i]!) ω2
  let od := nttFast ((Array.range half).map fun i => xs[2 * i + 1]!) ω2
  let pw := (Array.range half).map fun j => powMod ω j goldilocksP
  (Array.range n).map fun j =>
    if j < half then (ev[j]! + pw[j]! * od[j]! % goldilocksP) % goldilocksP
    else
      let j' := j - half
      (ev[j']! + goldilocksP - pw[j']! * od[j']! % goldilocksP) % goldilocksP


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
    values k % goldilocksP = dft n ω input k := by
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
        (update (update values i0 ((values i0+values i1)%goldilocksP)) i1
          ((((values i0+goldilocksP-values i1)%goldilocksP)*twiddle)%goldilocksP)) := by
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
    simpa only [i0,i1,di,bit,ht,Nat.mul_one,Nat.mod_mod,goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using And.intro h.1 hv

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

theorem difLayer_canonical (bits level : Nat) (hl : level<bits) (input : Nat → Nat)
    (i : Nat) (hi : i<2^bits) : difLayer bits level input i < goldilocksP := by
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
    (hinput : ∀ i, i<2^bits → input i<goldilocksP) (i : Nat) (hi : i<2^bits) :
    difStages bits start count input i < goldilocksP := by
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
    (hinput : ∀ i, i<2^bits → input i<goldilocksP) :
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
    (h : first=false → ∀ i, i<bound → entry i<goldilocksP) :
    ∀ i, i<bound → preparedInput n count p group first entry i < goldilocksP := by
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
    (if first then if p=1 then values r%goldilocksP else
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

section
namespace Obend.Hardware.Gpu.Ntt.PhaseInit
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open ArrayKernel ArrayBuild GoldilocksSource GoldilocksSourceCorrect NttFieldCorrect
open BlockNtt RegisterValues PhaseArithmetic
set_option autoImplicit false

/-- Allocated register values before canonicalization may be arbitrary words. -/
structure RawValue (st : Build) (env : Nat → Word) (r value : Nat) : Prop where
  bound : r < st.lengths.size
  value_eq : (evalBuild st env r).toNat=value

def RawRegs (st : Build) (env : Nat → Word) (regs : Array Nat) (values : Nat → Nat) : Prop :=
  ∀ i, i < regs.size → RawValue st env regs[i]! (values i)

theorem RawValue.mono {st after : Build} {env : Nat → Word} {r value : Nat}
    (h : RawValue st env r value) (he : BuildExtends st after) : RawValue after env r value :=
  ⟨Nat.lt_of_lt_of_le h.bound he.size_le,
    (congrArg BitVec.toNat (he.frame env r h.bound)).trans h.value_eq⟩

theorem RawRegs.mono {st after : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (he : BuildExtends st after) : RawRegs after env regs v :=
  fun i hi => (h i hi).mono he

theorem RawRegs.set {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (i r value : Nat) (hi : i < regs.size)
    (hr : RawValue st env r value) : RawRegs st env (regs.set! i r) (update v i value) := by
  intro j hj
  simp only [Array.size_set!] at hj
  by_cases he : i=j
  · subst j; rw [Array.getElem!_set!_self regs i r hi]; simpa [update_eq] using hr
  · rw [Array.getElem!_set!_ne regs i j r he]; simpa [update_eq,Ne.symm he] using h j hj

theorem RawRegs.canonical {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (hc : ∀ i, i < regs.size → v i < goldilocksP) :
    RegValues st env regs v := fun i hi => ⟨(h i hi).bound,(h i hi).value_eq,hc i hi⟩

/-- Mathematical denotation of a once-per-register preparation pass. -/
def prepareValues (xs : List Nat) (f : Nat → Nat → Nat) (v : Nat → Nat) : Nat → Nat :=
  xs.foldl (fun w i => update w i (f i (w i))) v

theorem prepareValues_at (xs : List Nat) (f : Nat → Nat → Nat) (v : Nat → Nat)
    (hn : xs.Nodup) (i : Nat) :
    prepareValues xs f v i = if i ∈ xs then f i (v i) else v i := by
  induction xs generalizing v with
  | nil => simp [prepareValues]
  | cons j xs ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [prepareValues,List.foldl_cons]
    change prepareValues xs f (update v j (f j (v j))) i = _
    rw [ih _ hn'.2]
    by_cases hi : i=j
    · subst i; simp [hn'.1,update_eq]
    · simp [hi,update_eq]

theorem canon_step (k : GlConsts) (r : Nat) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) (hr : r < regs.size) :
    let out := (PhaseMetadata.canonBody k r regs).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.value
      (update values r (values r%goldilocksP)) := by
  obtain ⟨result,heq⟩ : ∃ result, (glCanon 1 k regs[r]!).run st = result := ⟨_,rfl⟩
  have he := glCanon_extends st 1 k regs[r]!
  have hs := glCanon_sound st env 1 k regs[r]! (hv r hr).bound hk
  have hc := glCanon_coordinates st 1 k regs[r]!
  rw [heq] at he hs hc
  have hrval : RawValue result.2 env result.1 (values r%goldilocksP) :=
    ⟨by omega,by simpa only [(hv r hr).value_eq,goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using hs.2⟩
  simp only [PhaseMetadata.canonBody,bind_run,heq,pure_run,ForInStep.value]
  exact ⟨he,(hv.mono he).set r result.1 _ hr hrval⟩

theorem canon_loop (k : GlConsts) (xs : List Nat) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) (hb : ∀ r, r ∈ xs → r < regs.size) :
    let out := (forIn xs regs (PhaseMetadata.canonBody k)).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1
      (prepareValues xs (fun _ v => v%goldilocksP) values) := by
  induction xs generalizing st regs values with
  | nil => simpa only [List.forIn_nil,pure_run,prepareValues,List.foldl_nil] using And.intro (BuildExtends.refl st) hv
  | cons r xs ih =>
    obtain ⟨result,heq⟩ : ∃ result, (glCanon 1 k regs[r]!).run st = result := ⟨_,rfl⟩
    have hstep := canon_step k r regs st env values hk hv (hb r (by simp))
    simp only [PhaseMetadata.canonBody,bind_run,heq,pure_run,ForInStep.value] at hstep
    have htail := ih (regs.set! r result.1) result.2 (update values r (values r%goldilocksP))
      (hk.mono hstep.1) hstep.2 (fun i hi => by simpa only [Array.size_set!] using hb i (by simp [hi]))
    simp only [List.forIn_cons,bind_run,PhaseMetadata.canonBody,heq,pure_run,prepareValues,List.foldl_cons]
    exact ⟨hstep.1.trans htail.1,htail.2⟩

theorem canon_all (k : GlConsts) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) :
    let out := (forIn (List.range regs.size) regs (PhaseMetadata.canonBody k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1 (fun i => values i%goldilocksP) := by
  have h := canon_loop k (List.range regs.size) regs st env values hk hv (fun _ hi => List.mem_range.mp hi)
  have hsize := PhaseMetadata.canon_size k (List.range regs.size) regs st
  refine ⟨h.1,?_⟩
  intro i hi
  have hib : i < regs.size := by simpa only [hsize] using hi
  have hr := h.2 i hi
  have hp := prepareValues_at (List.range regs.size) (fun _ v => v%goldilocksP) values
    List.nodup_range i
  simp only [List.mem_range,if_pos hib] at hp
  rw [hp] at hr
  exact ⟨hr.bound,hr.value_eq,Nat.mod_lt _ (by decide)⟩

def inputExponent (n count p radix stride r : Nat) : Ix :=
  .mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n

theorem input_step (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values) (hr : r < s.2.size)
    (hreads : Twiddles env
      ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 table) :
    let out := (PhaseMetadata.inputBody n count p radix stride k r s).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.value.2
      (update values r ((values r*table (inputExponent n count p radix stride r))%goldilocksP)) := by
  let tw := (newWire 1).run st
  obtain ⟨result,heq⟩ : ∃ result, (glMul 1 k s.2[r]! tw.1).run tw.2 = result := ⟨_,rfl⟩
  have ht := newWire_extends st 1
  have hm := glMul_extends tw.2 1 k s.2[r]! tw.1
  have hc := glMul_coordinates tw.2 1 k s.2[r]! tw.1
  have htw : tw.1 < tw.2.lengths.size := by simp [tw,newWire_run]
  have ha := (hv r hr).mono ht
  have hs := glMul_sound tw.2 env 1 k s.2[r]! tw.1 ha.bound htw (hk.mono ht)
  rw [heq] at hm hc hs
  dsimp only [tw] at heq
  have hread : (env tw.1).toNat=table (inputExponent n count p radix stride r) := by
    apply hreads ⟨tw.1,4,inputExponent n count p radix stride r⟩ _ rfl
    simp only [PhaseMetadata.inputBody,bind_run,heq,pure_run,ForInStep.value]
    simp [tw,inputExponent]
  have htv : evalBuild tw.2 env tw.1 = env tw.1 := by
    change evalBuild st env tw.1 = env tw.1
    exact hstart.fresh_value env tw.1 (by simp [tw,newWire_run])
  have hraw : RawValue result.2 env result.1
      ((values r*table (inputExponent n count p radix stride r))%goldilocksP) := by
    refine ⟨by omega,?_⟩
    have haValue : (evalBuild tw.2 env s.2[r]!).toNat=values r := ha.value_eq
    rw [haValue,htv,hread] at hs
    simpa only [goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using hs.2
  simp only [PhaseMetadata.inputBody,bind_run,heq,pure_run,ForInStep.value]
  exact ⟨ht.trans hm,(hv.mono (ht.trans hm)).set r result.1 _ hr hraw⟩

theorem input_reads_mono (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) (read : Read) (hr : read ∈ s.1) :
    read ∈ ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 := by
  simp only [PhaseMetadata.inputBody,bind_run,pure_run,ForInStep.value]
  exact List.mem_append_left _ hr

theorem inputLoop_reads_mono (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro j ss before hh
  exact input_reads_mono n count p radix stride k j ss before r hh

theorem input_yield (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) :
    ∃ after out, (PhaseMetadata.inputBody n count p radix stride k r s).run st = (.yield out,after) := by
  simp only [PhaseMetadata.inputBody,bind_run,pure_run]
  exact ⟨_,_,rfl⟩

theorem input_loop (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values) (hb : ∀ r, r ∈ xs → r < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.2
      (prepareValues xs (fun r v => (v*table (inputExponent n count p radix stride r))%goldilocksP) values) := by
  induction xs generalizing st s values with
  | nil => simpa only [List.forIn_nil,pure_run,prepareValues,List.foldl_nil] using And.intro (BuildExtends.refl st) hv
  | cons r xs ih =>
    obtain ⟨after,ss,heq⟩ := input_yield n count p radix stride k r s st
    have hrun : (forIn (r::xs) s (PhaseMetadata.inputBody n count p radix stride k)).run st =
        (forIn xs ss (PhaseMetadata.inputBody n count p radix stride k)).run after := by
      rw [List.forIn_cons,bind_run,heq]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 table := by
      rw [heq]
      intro read hmem ha
      exact hreads read (inputLoop_reads_mono n count p radix stride k xs ss after read hmem) ha
    have hstep := input_step n count p radix stride k r s st env values table hstart hk hv
      (hb r (by simp)) hheadReads
    rw [heq] at hstep
    have hsize : ss.2.size=s.2.size := by
      have h := PhaseMetadata.input_size n count p radix stride k [r] s st
      simpa only [List.forIn_cons,bind_run,heq,List.forIn_nil,pure_run] using h
    have htail := ih ss after (update values r ((values r*table (inputExponent n count p radix stride r))%goldilocksP))
      (hstart.trans hstep.1) (hk.mono hstep.1) hstep.2
      (fun i hi => by simpa only [hsize] using hb i (by simp [hi])) hreads
    dsimp only
    rw [hrun]
    exact ⟨hstep.1.trans htail.1,htail.2⟩

theorem input_all (n count p radix stride : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values)
    (hreads : Twiddles env
      ((forIn (List.range s.2.size) s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 table) :
    let out := (forIn (List.range s.2.size) s (PhaseMetadata.inputBody n count p radix stride k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (fun i => (values i*table (inputExponent n count p radix stride i))%goldilocksP) := by
  have h := input_loop n count p radix stride k (List.range s.2.size) s st env values table hstart hk hv
    (fun _ hi => List.mem_range.mp hi) hreads
  have hsize := PhaseMetadata.input_size n count p radix stride k (List.range s.2.size) s st
  refine ⟨h.1,?_⟩
  intro i hi
  have hib : i < s.2.size := by simpa only [hsize] using hi
  have hr := h.2 i hi
  have hp := prepareValues_at (List.range s.2.size)
    (fun r v => (v*table (inputExponent n count p radix stride r))%goldilocksP) values
    List.nodup_range i
  simp only [List.mem_range,if_pos hib] at hp
  rw [hp] at hr
  exact ⟨hr.bound,hr.value_eq,Nat.mod_lt _ (by decide)⟩

/-- The exact initial load loop of the source, before constants or arithmetic. -/
abbrev initialLoads (n count done degree src : Nat) (first : Bool) : PhaseMetadata.PairState × Build :=
  (forIn (List.range (2^degree)) ([],#[])
    (PhaseMetadata.loadBody src (phaseLoadIndex n count (2^degree)
      (count/(2^done*2^degree)) first))).run {}

def preparedValues (n count p done degree : Nat) (first : Bool)
    (inputs : Nat → Nat) (table : Ix → Nat) : Nat → Nat :=
  if first then
    if p=1 then fun i => inputs i%goldilocksP
    else fun i => (inputs i*table (inputExponent n count p (2^degree) (count/(2^done*2^degree)) i))%goldilocksP
  else inputs

def roundResultValues (n count done degree : Nat) (table : Ix → Nat) (values : Nat → Nat) : Nat → Nat :=
  (List.range degree).foldl (fun v round => roundValues (2^degree/2) (2^degree/2^(round+1))
    (fun j => pairTwiddle n count done (2^degree) (count/(2^done*2^degree)) round j table) v) values

def phaseResultValues (n count p done degree : Nat) (first : Bool)
    (inputs : Nat → Nat) (table : Ix → Nat) : Nat → Nat :=
  roundResultValues n count done degree table (preparedValues n count p done degree first inputs table)

theorem initialLoads_extends (n count done degree src : Nat) (first : Bool) :
    BuildExtends {} (initialLoads n count done degree src first).2 := by
  apply forIn_extends
  intro r s st
  simpa only [PhaseMetadata.loadBody,bind_run,pure_run] using newWire_extends st 1

theorem initialLoads_size (n count done degree src : Nat) (first : Bool) :
    (initialLoads n count done degree src first).1.2.size = 2^degree := by
  simpa only [Array.size_empty,List.length_range,Nat.zero_add] using
    PhaseMetadata.load_size src (phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first)
      (List.range (2^degree)) ([],#[]) {}

theorem finish_rounds (n count done degree : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hvalues : RegValues st env s.2 values) (hsize : s.2.size=2^degree)
    (hreads : Twiddles env ((forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st).1.1 table) :
    let out := (forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st
    BuildExtends {} out.2 ∧ ∀ i, i < 2^degree →
      FieldValue out.2 env out.1.2.toList[i]! (roundResultValues n count done degree table values i) := by
  have hr := rounds_values n count done (2^degree) (count/(2^done*2^degree)) k
    (List.range degree) s st env values table hstart hk hvalues
    (fun round hround j hj => by rw [hsize]; exact phase_register_bounds degree round j (List.mem_range.mp hround) hj)
    hreads
  refine ⟨hstart.trans hr.1,?_⟩
  intro i hi
  have hsz := PhaseMetadata.rounds_size n count done (2^degree) (count/(2^done*2^degree)) k
    (List.range degree) s st
  have hib : i < ((forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st).1.2.size := by
    rw [hsz,hsize]; exact hi
  simpa only [Array.getElem!_toList,roundResultValues] using hr.2 i hib

/-- Full source-action arithmetic refinement. The premises concern only the
loaded inputs and concrete constant-buffer reads; every computed register and
output follows from the actual shared field builders and actual source loops. -/
theorem phaseAction_values (n count p done degree src : Nat) (first : Bool)
    (env : Nat → Word) (inputs : Nat → Nat) (table : Ix → Nat) (hp : 0 < p)
    (hinputs : RawRegs (initialLoads n count done degree src first).2 env
      (initialLoads n count done degree src first).1.2 inputs)
    (hcanonical : first=false → ∀ i, i < 2^degree → inputs i < goldilocksP)
    (hreads : Twiddles env ((phaseAction n count p done degree src first).run {}).1.1 table) :
    let out := (phaseAction n count p done degree src first).run {}
    BuildExtends {} out.2 ∧ ∀ i, i < 2^degree →
      FieldValue out.2 env out.1.2[i]! (phaseResultValues n count p done degree first inputs table i) := by
  let loaded := initialLoads n count done degree src first
  let constants := (glConsts 1).run loaded.2
  have hl := initialLoads_extends n count done degree src first
  have hc := glConsts_extends loaded.2 1 (by decide)
  have hk := glConsts_sound loaded.2 env 1 (by decide)
  have hs := initialLoads_size n count done degree src first
  have hraw := hinputs.mono hc
  cases first with
  | false =>
    have hv : RegValues constants.2 env loaded.1.2 inputs := hraw.canonical (by
      intro i hi
      apply hcanonical rfl i
      simpa only [hs] using hi)
    have hrun := PhaseMetadata.phaseAction_run n count p done degree src false {}
    simp only [Bool.false_and,Bool.false_eq_true,ite_false] at hrun
    rw [hrun] at hreads ⊢
    exact finish_rounds n count done degree constants.1 loaded.1 constants.2 env inputs table
      (hl.trans hc) hk hv hs hreads
  | true =>
    by_cases hp1 : p=1
    · subst p
      let canonical := (forIn (List.range (2^degree)) loaded.1.2 (PhaseMetadata.canonBody constants.1)).run constants.2
      have hcan := canon_all constants.1 loaded.1.2 constants.2 env inputs hk hraw
      have hs' : loaded.1.2.size=2^degree := hs
      rw [hs'] at hcan
      have hcs := PhaseMetadata.canon_size constants.1 (List.range (2^degree)) loaded.1.2 constants.2
      have hrun := PhaseMetadata.phaseAction_run n count 1 done degree src true {}
      simp only [Bool.true_and,Nat.reduceBEq,show decide (1>1)=false by decide,Bool.false_eq_true,ite_true,ite_false] at hrun
      rw [hrun] at hreads ⊢
      have hf := finish_rounds n count done degree constants.1 (loaded.1.1,canonical.1) canonical.2 env
        (fun i => inputs i%goldilocksP) table ((hl.trans hc).trans hcan.1) (hk.mono hcan.1) hcan.2
        (hcs.trans hs') hreads
      simpa only [phaseResultValues,preparedValues,ite_true] using hf
    · have hpgt : 1 < p := by omega
      let twisted := (forIn (List.range (2^degree)) loaded.1
        (PhaseMetadata.inputBody n count p (2^degree) (count/(2^done*2^degree)) constants.1)).run constants.2
      have hrun := PhaseMetadata.phaseAction_run n count p done degree src true {}
      have hpne : (p==1)=false := by exact beq_eq_false_iff_ne.mpr hp1
      have hpg : decide (p>1)=true := decide_eq_true hpgt
      simp only [Bool.true_and,hpne,Bool.false_eq_true,hpg,ite_true,ite_false] at hrun
      rw [hrun] at hreads ⊢
      have htwreads : Twiddles env twisted.1.1 table := by
        intro r hmem ha
        exact hreads r (rounds_reads_mono n count done (2^degree) (count/(2^done*2^degree))
          constants.1 (List.range degree) twisted.1 twisted.2 r hmem) ha
      have htw := input_all n count p (2^degree) (count/(2^done*2^degree)) constants.1 loaded.1 constants.2
        env inputs table (hl.trans hc) hk hraw (by rw [show loaded.1.2.size=2^degree from hs]; exact htwreads)
      have hs' : loaded.1.2.size=2^degree := hs
      rw [hs'] at htw
      have hts := PhaseMetadata.input_size n count p (2^degree) (count/(2^done*2^degree)) constants.1
        (List.range (2^degree)) loaded.1 constants.2
      have hf := finish_rounds n count done degree constants.1 twisted.1 twisted.2 env
        (fun i => (inputs i*table (inputExponent n count p (2^degree) (count/(2^done*2^degree)) i))%goldilocksP)
        table ((hl.trans hc).trans htw.1) (hk.mono htw.1) htw.2 (hts.trans hs') hreads
      simpa only [phaseResultValues,preparedValues,ite_true,hp1,ite_false] using hf

end Obend.Hardware.Gpu.Ntt.PhaseInit
end

section
/-! The actual phase initialization pairs every returned input register with
its declared load index. Allocation emits no arithmetic instructions. -/
namespace Obend.Hardware.Gpu.NttLoadCorrect
open Obend.Hardware.ArrayBuild Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.PhaseMetadata
set_option autoImplicit false

theorem loadBody_run (src : Nat) (index : Nat → Ix) (r : Nat) (s : PairState) (st : Build) :
    (loadBody src index r s).run st =
      (.yield (s.1++[⟨st.lengths.size,src,index r⟩],s.2.push st.lengths.size),
        {st with lengths := st.lengths.push 1}) := by rfl

/-- General loop receipt: the appended reads and registers have identical
ordering, and every appended read records the corresponding source index. -/
theorem load_suffix (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ∃ regs : List Nat,
      regs.length = xs.length ∧
      ((forIn xs s (loadBody src index)).run st).1.1 =
        s.1 ++ (regs.zip xs).map (fun (a,r) => ⟨a,src,index r⟩) ∧
      ((forIn xs s (loadBody src index)).run st).1.2.toList = s.2.toList ++ regs ∧
      ((forIn xs s (loadBody src index)).run st).2.edges = st.edges := by
  induction xs generalizing s st with
  | nil =>
    refine ⟨[], rfl, ?_, ?_, ?_⟩
    · change s.1 = s.1 ++ []
      exact (List.append_nil _).symm
    · change s.2.toList = s.2.toList ++ []
      exact (List.append_nil _).symm
    · rfl
  | cons r xs ih =>
    rw [List.forIn_cons,bind_run,loadBody_run]
    change ∃ regs : List Nat, _
    obtain ⟨regs,hl,hr,hg,he⟩ := ih
      (s.1++[⟨st.lengths.size,src,index r⟩],s.2.push st.lengths.size)
      {st with lengths := st.lengths.push 1}
    refine ⟨st.lengths.size::regs,by simp [hl],?_,?_,he⟩
    · simpa [List.append_assoc] using hr
    · simpa [List.append_assoc] using hg

theorem load_reads_eq (src : Nat) (index : Nat → Ix) (radix : Nat) (st : Build) :
    ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.1 =
      (((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.2.toList.zip
        (List.range radix)).map (fun (a,r) => ⟨a,src,index r⟩) := by
  obtain ⟨regs,_,hr,hg,_⟩ := load_suffix src index (List.range radix) ([],#[]) st
  simp only [List.nil_append,Array.toList_empty] at hr hg
  rw [hg]
  exact hr

theorem load_edges (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (loadBody src index)).run st).2.edges = st.edges := by
  obtain ⟨_,_,_,_,he⟩ := load_suffix src index xs s st
  exact he

/-- Every returned register slot is exactly the destination of its declared
source load. This input binding is independent of later arithmetic. -/
theorem load_reg_read (src : Nat) (index : Nat → Ix) (radix : Nat) (st : Build)
    (r : Nat) (hr : r < radix) :
    (⟨((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.2.getD r 0,
       src,index r⟩ : Read) ∈ ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.1 := by
  let loaded := ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1
  have hs : loaded.2.size = radix := by simpa [loaded] using load_size src index (List.range radix) ([],#[]) st
  have hbound : r < loaded.2.size := by omega
  have hzip : r < (loaded.2.toList.zip (List.range radix)).length := by simp [hs,hr]
  have hm := List.getElem_mem (l := loaded.2.toList.zip (List.range radix)) hzip
  have he : (loaded.2.toList.zip (List.range radix))[r] = (loaded.2.getD r 0,r) := by
    simp [List.getElem_zip,Array.getD_eq_getD_getElem?,hbound]
  rw [he] at hm
  rw [load_reads_eq]
  exact List.mem_map.mpr ⟨(loaded.2.getD r 0,r),hm,rfl⟩

end Obend.Hardware.Gpu.NttLoadCorrect
end

section
namespace Obend.Hardware.Gpu.Ntt
open ArrayHypergraph ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open PhaseMetadata PhaseArithmetic NttFieldCorrect

/-- The actual phase loader supplies the initial environment of its emitted code. -/
def phaseEnv (ph : Phase) (mem : Memory) (group lane : Nat) : Nat → Word :=
  fun wire => (loadRegisters ph mem group lane).getD wire 0#64

theorem phaseEnv_read (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane : Nat) (r : Read)
    (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    phaseEnv (phase n count bits p done degree src dst first last) mem group lane r.dst =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 :=
  phase_loadRegisters_value n count bits p done degree src dst first last mem group lane r hr

/-- Actual HashMap execution and the actual builder interpreter are the same
register program, with the actual loaded environment. -/
theorem phase_runRegisters (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane wire : Nat) :
    (runRegisters (phase n count bits p done degree src dst first last).code
      (loadRegisters (phase n count bits p done degree src dst first last) mem group lane)).getD wire 0#64 =
    evalBuild ((phaseAction n count p done degree src first).run {}).2
      (phaseEnv (phase n count bits p done degree src dst first last) mem group lane) wire := by
  exact runRegisters_sound _ _ wire

/-- The actual loader discharges the register arithmetic's input-only twiddle
agreement from the actual constant buffer. No computed-value premise is used. -/
theorem phaseEnv_twiddles (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (hb : bits≤total) (hdegree : done+degree≤bits)
    (hg : group<2^total/2^bits) (hl : lane<2^bits/2^degree)
    (htable : ∀ i, i<2^total → ((mem.getD 4 #[]).getD i 0#64).toNat = modPow (rootOfUnity (2^total)) i) :
    Twiddles (phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)
      ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.1
      (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane)) := by
  intro r hr ha
  have hm : r ∈ (phase (2^total) (2^bits) bits p done degree src dst first last).reads := hr
  have hbounds := phase_read_index_bound total bits p done degree src dst group lane first last
    hb hdegree hg hl r hm
  have hi : r.index.eval group lane < 2^total := by
    rcases hbounds with ⟨_,hi⟩ | ⟨_,hi⟩
    · have hs : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      exact Nat.lt_of_lt_of_le hi hs
    · exact hi
  rw [phaseEnv_read _ _ _ _ _ _ _ _ _ _ _ _ _ r hm,ha]
  exact htable _ hi

/-- Initial source loads remain in the final phase's read list. -/
theorem phase_initial_read_mem (n count p done degree src : Nat) (first : Bool) (r : Read)
    (hr : r ∈ (PhaseInit.initialLoads n count done degree src first).1.1) :
    r ∈ ((phaseAction n count p done degree src first).run {}).1.1 := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false]
  all_goals
    apply rounds_reads_mono
    first
    | apply PhaseInit.inputLoop_reads_mono; exact hr
    | exact hr

/-- The real input loader supplies the raw register values required by the
shared arithmetic proof; initial allocation emits no arithmetic instructions. -/
theorem phase_initial_raw (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (hdegree : done+degree≤bits) (hlane : lane<2^bits/2^degree)
    (hentry : ∀ i, i<2^bits →
      ((mem.getD src #[]).getD (if first then group+i*(2^total/2^bits) else i) 0#64).toNat=entry i) :
    PhaseInit.RawRegs (PhaseInit.initialLoads (2^total) (2^bits) done degree src first).2
      (phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)
      (PhaseInit.initialLoads (2^total) (2^bits) done degree src first).1.2
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) := by
  let loaded := PhaseInit.initialLoads (2^total) (2^bits) done degree src first
  intro r hr
  have hs := PhaseInit.initialLoads_size (2^total) (2^bits) done degree src first
  have hrr : r<2^degree := by simpa only [hs] using hr
  have hget : loaded.1.2.getD r 0 = loaded.1.2[r]! := by
    simp [Array.getD_eq_getD_getElem?,show r<loaded.1.2.size from hr]
  have hm := NttLoadCorrect.load_reg_read src
    (phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first)
    (2^degree) {} r hrr
  change (⟨loaded.1.2.getD r 0,src,
    phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first r⟩ : Read) ∈ loaded.1.1 at hm
  rw [hget] at hm
  have hfinal := phase_initial_read_mem (2^total) (2^bits) p done degree src first _ hm
  have halloc : ReadAllocation loaded.2 loaded.1.1 :=
    load_allocation src _ _ ([],#[]) {} ⟨by simp,by intro r hr; cases hr⟩
  refine ⟨halloc.bound _ hm,?_⟩
  have he := NttLoadCorrect.load_edges src
    (phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first)
    (List.range (2^degree)) ([],#[]) ({} : Build)
  change loaded.2.edges = #[] at he
  have hcode : ∀ env wire, evalBuild loaded.2 env wire=env wire := by
    intro env wire
    simp [evalBuild,registerCode,he,ArrayHypergraph.runCode]
  rw [hcode]
  have henv := phaseEnv_read (2^total) (2^bits) bits p done degree src dst first last mem group lane _ hfinal
  rw [henv,phaseLoadIndex_eval]
  exact hentry _ (phase_index_lt bits done degree lane r hdegree hlane hrr)

/-- The source action's mathematical result is exactly the fused whole-tile
stage result, including the actual first-phase input preparation. -/
theorem phaseResultValues_stages (total bits p done degree group lane : Nat)
    (first : Bool) (entry : Nat → Nat) (ht : total≤32) (hb : bits≤total)
    (hdegree : done+degree≤bits) (hlane : lane<2^bits/2^degree)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP) :
    ∀ r, r<2^degree →
    PhaseInit.phaseResultValues (2^total) (2^bits) p done degree first
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
      (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane)) r =
      difStages bits done degree (preparedInput (2^total) (2^bits) p group first entry)
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  unfold PhaseInit.phaseResultValues PhaseInit.roundResultValues
  apply phase_rounds_stages total bits done degree degree group lane ht hb hdegree (Nat.le_refl _) hlane
  · intro r hr
    have h := prepared_register_eq total bits p done degree group lane r first entry
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) ht rfl
    cases first <;> by_cases hp1 : p=1 <;>
      simpa [PhaseInit.preparedValues,PhaseInit.inputExponent,PhaseMetadata.inputExponent,mulMod,hp1] using h
  · exact preparedInput_canonical _ _ _ _ _ first entry hcanonical

/-- Actual emitted register execution has the exact fused DIF value. All
premises concern transform shape, input memory, and the initial twiddle table. -/
theorem phase_register_value (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (ht : total≤32) (hb : bits≤total) (hp : 0<p) (hdegree : done+degree≤bits)
    (hg : group<2^total/2^bits) (hlane : lane<2^bits/2^degree)
    (hentry : ∀ i, i<2^bits →
      ((mem.getD src #[]).getD (if first then group+i*(2^total/2^bits) else i) 0#64).toNat=entry i)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP)
    (htable : ∀ i, i<2^total → ((mem.getD 4 #[]).getD i 0#64).toNat=modPow (rootOfUnity (2^total)) i)
    (r : Nat) (hr : r<2^degree) :
    ((runRegisters (phase (2^total) (2^bits) bits p done degree src dst first last).code
      (loadRegisters (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)).getD
      (((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.getD r 0) 0#64).toNat =
      difStages bits done degree (preparedInput (2^total) (2^bits) p group first entry)
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  let env := phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane
  let inputs := fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)
  let table := fun (ix : Ix) => modPow (rootOfUnity (2^total)) (ix.eval group lane)
  have hraw := phase_initial_raw total bits p done degree src dst group lane first last mem entry hdegree hlane hentry
  have htw := phaseEnv_twiddles total bits p done degree src dst group lane first last mem hb hdegree hg hlane htable
  have hv := PhaseInit.phaseAction_values (2^total) (2^bits) p done degree src first env inputs table hp hraw
    (fun hf i hi => hcanonical hf _ (phase_index_lt bits done degree lane i hdegree hlane hi)) htw
  have hfield := hv.2 r hr
  have hget : ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.getD r 0 =
      ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2[r]! := by
    have hlen := phaseAction_length (2^total) (2^bits) p done degree src first {}
    simp [List.getD_eq_getElem?_getD,show r<((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.length by omega]
  rw [hget,phase_runRegisters]
  rw [hfield.value_eq]
  exact phaseResultValues_stages total bits p done degree group lane first entry ht hb hdegree hlane hcanonical r hr

end Obend.Hardware.Gpu.Ntt
end

section
/-! Exact phase scheduling and unconditional row framing for the actual NTT
upload builder. Batching changes indices but never the destination array. -/
namespace Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Hardware.Gpu.NttBatchCorrect
open Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

theorem phaseDegrees_sum (degree : Nat) : (phaseDegrees degree).sum = degree := by
  have hm := Nat.mod_lt degree (by decide : 0 < 2)
  have hd := Nat.div_add_mod degree 2
  by_cases h : degree%2=0
  · simp [phaseDegrees,h,List.sum_replicate_nat]
    omega
  · have h1 : degree%2=1 := by omega
    simp [phaseDegrees,h1,List.sum_replicate_nat]
    omega

theorem phaseDegrees_member (degree chunk : Nat) (h : chunk ∈ phaseDegrees degree) :
    chunk = 1 ∨ chunk = 2 := by
  unfold phaseDegrees at h
  rcases List.mem_append.mp h with hr | ht
  · exact Or.inr (List.eq_of_mem_replicate hr)
  · split at ht <;> simp_all

theorem phaseDegrees_ne_nil (degree : Nat) (h : 0 < degree) : phaseDegrees degree ≠ [] := by
  intro he
  have hs := phaseDegrees_sum degree
  rw [he] at hs
  simp at hs
  omega

def phaseOutput (bits dst done input chunk : Nat) : Nat :=
  if done+chunk == bits then dst else if input == 2 then 3 else 2

def finalPhaseBuffer (bits dst : Nat) : Nat → Nat → List Nat → Nat
  | _, input, [] => input
  | done, input, chunk::rest =>
      finalPhaseBuffer bits dst (done+chunk) (phaseOutput bits dst done input chunk) rest

theorem finalPhaseBuffer_complete (bits dst done input : Nat) (chunks : List Nat)
    (hne : chunks ≠ []) (h : done+chunks.sum = bits) :
    finalPhaseBuffer bits dst done input chunks = dst := by
  induction chunks generalizing done input with
  | nil => exact False.elim (hne rfl)
  | cons chunk rest ih =>
    cases rest with
    | nil =>
      have he : done+chunk = bits := by simpa using h
      simp [finalPhaseBuffer,phaseOutput,he]
    | cons next rest =>
      change finalPhaseBuffer bits dst (done+chunk) (phaseOutput bits dst done input chunk) (next::rest) = dst
      apply ih _ _ (by simp)
      simp only [List.sum_cons] at h ⊢
      omega

theorem buildPhases_length (n bits p dst done input : Nat) (chunks : List Nat) :
    (buildPhases n bits p dst done input chunks).length = chunks.length := by
  induction chunks generalizing done input with
  | nil => rfl
  | cons chunk rest ih => simp [buildPhases,ih]

/-- The opaque register construction does not affect the output-array metadata. -/
theorem phase_write_array (n count bits p done degree src dst : Nat) (first last : Bool)
    (w : Write) (hw : w ∈ (phase n count bits p done degree src dst first last).writes) :
    w.array = dst := by
  unfold phase at hw
  dsimp only at hw
  obtain ⟨item,_,he⟩ := List.mem_map.mp hw
  subst w
  rfl

theorem buildPhases_write_arrays (n bits p dst done input : Nat) (chunks : List Nat)
    (ph : Phase) (hph : ph ∈ buildPhases n bits p dst done input chunks)
    (w : Write) (hw : w ∈ ph.writes) : w.array = dst ∨ w.array = 2 ∨ w.array = 3 := by
  induction chunks generalizing done input with
  | nil => simp [buildPhases] at hph
  | cons chunk rest ih =>
    simp only [buildPhases,List.mem_cons] at hph
    rcases hph with he | ht
    · subst ph
      have ha := phase_write_array n (2^bits) bits p done chunk input _ _ _ w hw
      by_cases hl : done+chunk = bits
      · simp [hl] at ha
        exact Or.inl ha
      · by_cases hs : input=2
        · simp [hl,hs] at ha
          exact Or.inr (Or.inr ha)
        · simp [hl,hs] at ha
          exact Or.inr (Or.inl ha)
    · exact ih _ _ ht

/-- An out-of-row store cannot affect that row, even for malformed memory sizes.
This frame fact therefore needs no admission receipt. -/
theorem applyWrite_row_frame (mem : Memory) (w : Nat × Nat × Word) (a : Nat)
    (h : w.1 ≠ a) : (applyWrite mem w).getD a #[] = mem.getD a #[] := by
  simp [applyWrite,Array.getD_eq_getD_getElem?,Array.getElem?_modify,h]

theorem foldWrites_row_frame (ws : List (Nat × Nat × Word)) (mem : Memory) (a : Nat)
    (h : ∀ w ∈ ws, w.1 ≠ a) : (ws.foldl applyWrite mem).getD a #[] = mem.getD a #[] := by
  induction ws generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih (applyWrite mem w) (fun x hx => h x (by simp [hx]))]
    exact applyWrite_row_frame mem w a (h w (by simp))

theorem evalPhase_row_frame (ph : Phase) (g : Nat) (mem : Memory) (a : Nat)
    (h : ∀ w ∈ ph.writes, w.array ≠ a) : (evalPhase ph g mem).getD a #[] = mem.getD a #[] := by
  apply foldWrites_row_frame
  intro w hw
  obtain ⟨l,_,hl⟩ := List.mem_flatMap.mp hw
  obtain ⟨out,ho,he⟩ := List.mem_map.mp hl
  subst w
  exact h out ho

theorem evalPhases_row_frame (phases : List Phase) (g : Nat) (mem : Memory) (a : Nat)
    (h : ∀ ph ∈ phases, ∀ w ∈ ph.writes, w.array ≠ a) :
    (phases.foldl (fun m ph => evalPhase ph g m) mem).getD a #[] = mem.getD a #[] := by
  induction phases generalizing mem with
  | nil => rfl
  | cons ph phases ih =>
    rw [List.foldl_cons,ih (evalPhase ph g mem) (fun p hp => h p (by simp [hp]))]
    exact evalPhase_row_frame ph g mem a (h ph (by simp))

theorem evalDispatch_row_frame (d : Dispatch) (mem : Memory) (a : Nat)
    (h : ∀ ph ∈ d.phases, ∀ w ∈ ph.writes, w.array ≠ a) :
    (evalDispatch d mem).getD a #[] = mem.getD a #[] := by
  unfold evalDispatch
  generalize List.range d.groups = groups
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih]
    exact evalPhases_row_frame d.phases g mem a h

/-- A real packed upload preserves every row except its output and its two
shared workspaces. In particular all other device arrays and twiddles are framed. -/
theorem dispatch_row_frame (n logP degree src dst stride : Nat) (mem : Memory) (a : Nat)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (evalDispatch (batchTiles stride (dispatch n logP degree src dst)) mem).getD a #[] =
      mem.getD a #[] := by
  apply evalDispatch_row_frame
  intro ph hph w hw
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,he⟩ := List.mem_map.mp hph
  subst ph
  obtain ⟨out,hw',he⟩ := List.mem_map.mp hw
  subst w
  have ha := buildPhases_write_arrays n degree (2^logP) dst 0 src (phaseDegrees degree)
    original ho out hw'
  dsimp only
  rcases ha with ha | ha | ha <;> omega


/-- The actual Stockham destination address after final bit reversal. -/
def outputAddress (p count group r : Nat) : Nat :=
  group/p*(p*count)+group%p+r*p

theorem outputAddress_split (p count group r : Nat) :
    outputAddress p count group r = p*((group/p)*count+r)+group%p := by
  simp [outputAddress,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem outputAddress_div (p count group r : Nat) (hp : 0 < p) :
    outputAddress p count group r / p = (group/p)*count+r := by
  rw [outputAddress_split,Nat.mul_add_div hp,Nat.div_eq_of_lt (Nat.mod_lt group hp),Nat.add_zero]

theorem outputAddress_mod (p count group r : Nat) :
    outputAddress p count group r % p = group%p := by
  rw [outputAddress_split]
  simp

theorem outputAddress_register (p count group r : Nat) (hp : 0 < p) (hr : r < count) :
    outputAddress p count group r / p % count = r := by
  rw [outputAddress_div _ _ _ _ hp]
  exact Nat.mul_add_mod_of_lt hr

theorem outputAddress_group (p count group r : Nat) (hp : 0 < p) (hr : r < count) :
    (outputAddress p count group r / p / count)*p + outputAddress p count group r % p = group := by
  rw [outputAddress_div _ _ _ _ hp,outputAddress_mod]
  have hd : ((group/p)*count+r)/count = group/p := by
    rw [Nat.mul_comm (group/p),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hr,Nat.add_zero]
  rw [hd]
  simpa [Nat.mul_comm] using Nat.div_add_mod group p

/-- Distinct workgroups never alias their final device scatter; no source
admission receipt or concrete transform size is used by this arithmetic fact. -/
theorem outputAddress_injective (p count g h r s : Nat) (hp : 0 < p)
    (hr : r < count) (hs : s < count)
    (he : outputAddress p count g r = outputAddress p count h s) : g=h ∧ r=s := by
  constructor
  · have hg := outputAddress_group p count g r hp hr
    have hh := outputAddress_group p count h s hp hs
    rw [he] at hg
    omega
  · have hg := outputAddress_register p count g r hp hr
    have hh := outputAddress_register p count h s hp hs
    rw [he] at hg
    omega

theorem outputAddress_bound (p count tiles g r : Nat) (hp : 0 < p)
    (hg : g < p*tiles) (hr : r < count) : outputAddress p count g r < p*count*tiles := by
  have hq : g/p < tiles := Nat.div_lt_of_lt_mul hg
  have hm := Nat.mul_le_mul_right count (Nat.succ_le_of_lt hq)
  simp only [Nat.succ_mul] at hm
  have hd : outputAddress p count g r / p < tiles*count := by
    rw [outputAddress_div _ _ _ _ hp]
    omega
  have hb := (Nat.div_lt_iff_lt_mul hp).mp hd
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb


/-- Induction principle for the actual barrier-separated, batched phase list.
The invariant may record every tile simultaneously; the step is a real evalPhase. -/
theorem buildPhases_invariant (n bits p dst stride k group : Nat)
    (I : Nat → Nat → Memory → Prop)
    (step : ∀ done input chunk, 0 < chunk → chunk ≤ 2 → done+chunk ≤ bits →
      ∀ mem, I done input mem →
      I (done+chunk) (phaseOutput bits dst done input chunk)
        (evalPhase (batchPhase stride k
          (phase n (2^bits) bits p done chunk input (phaseOutput bits dst done input chunk)
            (done == 0) (done+chunk == bits))) group mem))
    (done input : Nat) (chunks : List Nat)
    (hchunks : ∀ chunk ∈ chunks, 0 < chunk ∧ chunk ≤ 2)
    (hbound : done+chunks.sum ≤ bits) (mem : Memory) (hmem : I done input mem) :
    I (done+chunks.sum) (finalPhaseBuffer bits dst done input chunks)
      (((buildPhases n bits p dst done input chunks).map (batchPhase stride k)).foldl
        (fun m ph => evalPhase ph group m) mem) := by
  induction chunks generalizing done input mem with
  | nil => simpa [buildPhases,finalPhaseBuffer] using hmem
  | cons chunk rest ih =>
    have hc := hchunks chunk (by simp)
    have hb : done+chunk ≤ bits := by simp only [List.sum_cons] at hbound; omega
    have hs := step done input chunk hc.1 hc.2 hb mem hmem
    have ht := ih (done+chunk) (phaseOutput bits dst done input chunk)
      (fun c hc => hchunks c (by simp [hc]))
      (by simp only [List.sum_cons] at hbound; omega) _ hs
    simpa only [buildPhases,finalPhaseBuffer,List.map_cons,List.foldl_cons,List.sum_cons,
      phaseOutput,Nat.add_assoc] using ht

/-- Exact composition endpoint for one packed upload: the schedule covers all
layers and its last phase uses the declared destination array. -/
theorem dispatch_phases_invariant (n logP degree src dst stride group : Nat)
    (hdegree : 0 < degree) (I : Nat → Nat → Memory → Prop)
    (step : ∀ done input chunk, 0 < chunk → chunk ≤ 2 → done+chunk ≤ degree →
      ∀ mem, I done input mem →
      I (done+chunk) (phaseOutput degree dst done input chunk)
        (evalPhase (batchPhase stride (packing (dispatch n logP degree src dst))
          (phase n (2^degree) degree (2^logP) done chunk input
            (phaseOutput degree dst done input chunk) (done == 0) (done+chunk == degree))) group mem))
    (mem : Memory) (hmem : I 0 src mem) :
    I degree dst (evalGroup (batchTiles stride (dispatch n logP degree src dst)) group mem) := by
  have h := buildPhases_invariant n degree (2^logP) dst stride
    (packing (dispatch n logP degree src dst)) group I step 0 src (phaseDegrees degree)
    (fun c hc => by rcases phaseDegrees_member degree c hc with rfl | rfl <;> decide)
    (by rw [phaseDegrees_sum]; omega) mem hmem
  have hf := finalPhaseBuffer_complete degree dst 0 src (phaseDegrees degree)
    (phaseDegrees_ne_nil degree hdegree) (by rw [phaseDegrees_sum]; omega)
  simpa only [phaseDegrees_sum,Nat.zero_add,hf,evalGroup,batchTiles_phases,dispatch] using h


/-- A store at a different coordinate frames this cell, including out-of-bounds
stores. This is a property of the source evaluator, independent of admission. -/
theorem applyWrite_cell_frame (mem : Memory) (w : Nat × Nat × Word) (a i : Nat)
    (h : (w.1,w.2.1) ≠ (a,i)) : valueAt (applyWrite mem w) a i = valueAt mem a i := by
  by_cases ha : w.1 = a
  · have hi : w.2.1 ≠ i := by intro he; exact h (Prod.ext ha he)
    by_cases hb : a < mem.size
    · simp [applyWrite,valueAt,Array.getD_eq_getD_getElem?,Array.getElem?_modify,Array.getElem_modify,ha,hb,
        Array.getElem?_setIfInBounds,hi]
    · simp [applyWrite,valueAt,Array.getD_eq_getD_getElem?,Array.getElem?_modify,ha,hb]
  · exact congrArg (fun row => row.getD i 0#64) (applyWrite_row_frame mem w a ha)

theorem foldWrites_cell_frame (ws : List (Nat × Nat × Word)) (mem : Memory) (a i : Nat)
    (h : ∀ w ∈ ws, (w.1,w.2.1) ≠ (a,i)) :
    valueAt (ws.foldl applyWrite mem) a i = valueAt mem a i := by
  induction ws generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih (applyWrite mem w) (fun x hx => h x (by simp [hx]))]
    exact applyWrite_cell_frame mem w a i (h w (by simp))

theorem evalPhase_cell_frame (ph : Phase) (g : Nat) (mem : Memory) (a i : Nat)
    (h : (a,i) ∉ ph.writeAddresses g) :
    valueAt (evalPhase ph g mem) a i = valueAt mem a i := by
  apply foldWrites_cell_frame
  intro w hw he
  apply h
  rw [← phaseWrites_locations ph mem g]
  exact List.mem_map.mpr ⟨w,hw,he⟩

/-- Pointwise framing composes through the actual phases, with no assumptions
about the values calculated by any other invocation. -/
theorem evalPhases_cell_frame (phases : List Phase) (g : Nat) (mem : Memory) (a i : Nat)
    (h : ∀ ph ∈ phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (phases.foldl (fun m ph => evalPhase ph g m) mem) a i = valueAt mem a i := by
  induction phases generalizing mem with
  | nil => rfl
  | cons ph phases ih =>
    rw [List.foldl_cons,ih (evalPhase ph g mem) (fun p hp => h p (by simp [hp]))]
    exact evalPhase_cell_frame ph g mem a i (h ph (by simp))

end Obend.Hardware.Gpu.NttDispatchCorrect
end

section
namespace Obend.Hardware.Gpu.Ntt
open ArrayKernel BlockNtt PhaseMetadata
open NttBatchCorrect BlockLower

/-- Read bounds of the actual packed source phase in the actual NTT buffers.
The proof derives the original invocation and read form from emitted metadata. -/
theorem packed_phase_reads_valid (total bits p done degree src dst stride k group : Nat)
    (first last : Bool) (hb : bits ≤ total) (hdegree : done+degree ≤ bits)
    (hsrc : src ≤ 3) (hfirst : first=true → src ≤ 1)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    ∀ lane < (batchPhase stride k (phase (2^total) (2^bits) bits p done degree src dst first last)).lanes,
      ∀ r ∈ (batchPhase stride k (phase (2^total) (2^bits) bits p done degree src dst first last)).reads,
        Valid (nttBlockProgram (2^total)) r.array (r.index.eval group lane) := by
  intro lane hl r hr
  let lanes := 2^bits/2^degree
  change lane < lanes*k at hl
  have hlanes : 0 < lanes := by
    dsimp only [lanes]
    rw [Nat.pow_div (by omega) (by decide)]
    exact Nat.two_pow_pos _
  have htile : lane/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [Nat.mul_comm] using hl)
  have hlane := Nat.mod_lt lane hlanes
  obtain ⟨read,hread,rfl⟩ := List.mem_map.mp hr
  change Valid _ read.array ((batchIndex stride k lanes read.array read.index).eval group lane)
  rw [batchIndex_eval]
  have hbound := phase_read_index_bound total bits p done degree src dst (group*k+lane/lanes)
    (lane%lanes) first last hb hdegree (hgroups _ htile) hlane read hread
  rcases hbound with ⟨ha,hi⟩ | ⟨ha,hi⟩
  · rw [ha]
    have hcases : src=0 ∨ src=1 ∨ src=2 ∨ src=3 := by omega
    rcases hcases with hzero | hone | htwo | hthree
    · have hsize : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      have hi' := Nat.lt_of_lt_of_le hi hsize
      simpa [hzero,Valid,buffer,nttBlockProgram,tileIndex] using hi'
    · have hsize : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      have hi' := Nat.lt_of_lt_of_le hi hsize
      simpa [hone,Valid,buffer,nttBlockProgram,tileIndex] using hi'
    all_goals
      have hf : first=false := by
        cases first
        · rfl
        · have := hfirst rfl; omega
      simp only [hf,Bool.false_eq_true,ite_false] at hi
      have hi' : read.index.eval (group*k+lane/lanes) (lane%lanes) < stride := Nat.lt_of_lt_of_le hi hstride
      have hp := Nat.mul_le_mul_right stride (by omega : lane/lanes+1 ≤ k)
      rw [Nat.add_mul,Nat.one_mul] at hp
      have hout : read.index.eval (group*k+lane/lanes) (lane%lanes)+(lane/lanes)*stride < sharedWords (2^total) := by
        rw [Nat.mul_comm stride k] at hshared
        omega
      first
      | simpa [htwo,Valid,buffer,nttBlockProgram,tileIndex] using hout
      | simpa [hthree,Valid,buffer,nttBlockProgram,tileIndex] using hout
  · rw [ha]
    simpa [Valid,buffer,nttBlockProgram,tileIndex] using hi

end Obend.Hardware.Gpu.Ntt
end

section
/-! Source-derived scatter geometry. These facts establish uniqueness from the
actual lane/register permutation, without evaluating an admission checker. -/
namespace Obend.Hardware.Gpu.NttDispatchGeometry
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
set_option autoImplicit false

theorem grid_nodup {α : Type} (rows cols : Nat) (f : Nat → Nat → α)
    (hi : ∀ a < rows, ∀ b < cols, ∀ c < rows, ∀ d < cols,
      f a b = f c d → a=c ∧ b=d) :
    ((List.range rows).flatMap fun a => (List.range cols).map (f a)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := cols))
    intro b d hb hd hne he
    exact hne (hi a (List.mem_range.mp ha) b (List.mem_range.mp hb)
      a (List.mem_range.mp ha) d (List.mem_range.mp hd) he).2
  · apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := rows))
    intro a c ha hc hne x hx y hy he
    obtain ⟨b,hb,hx⟩ := List.mem_map.mp hx
    obtain ⟨d,hd,hy⟩ := List.mem_map.mp hy
    have hxy : f a b = f c d := hx.trans (he.trans hy.symm)
    exact hne (hi a (List.mem_range.mp ha) b (List.mem_range.mp hb)
      c (List.mem_range.mp hc) d (List.mem_range.mp hd) hxy).1

theorem map_zipIdx_second {α β : Type} (xs : List α) (f : Nat → β) :
    xs.zipIdx.map (fun item => f item.2) = (List.range xs.length).map f := by
  calc
    _ = (xs.zipIdx.map Prod.snd).map f := by simp only [List.map_map,Function.comp_def]
    _ = _ := by rw [List.zipIdx_map_snd,←List.range_eq_range']

/-- Exact address enumeration follows from the real phaseAction output length. -/
theorem phase_addresses (n count bits p done degree src dst : Nat) (first last : Bool) (g : Nat) :
    (phase n count bits p done degree src dst first last).writeAddresses g =
      (List.range (count/2^degree)).flatMap fun l =>
        (List.range (2^degree)).map fun r =>
          (dst,(phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r).eval g l) := by
  unfold Phase.writeAddresses
  change (List.range (count/2^degree)).flatMap (fun l => _) = _
  apply congrArg (fun f => (List.range (count/2^degree)).flatMap f)
  funext l
  change ((((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).map fun w => (w.array,w.index.eval g l)) = _
  simp only [List.map_map,Function.comp_def]
  have hm := map_zipIdx_second ((phaseAction n count p done degree src first).run {}).1.2
    (fun r => (dst,(phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r).eval g l))
  simpa only [PhaseMetadata.phaseAction_length] using hm

theorem phaseSaveIndex_injective (bits p done degree g l l' r r' : Nat) (last : Bool)
    (hp : 0 < p) (hd : done+degree ≤ bits)
    (hl : l < 2^bits/2^degree) (hl' : l' < 2^bits/2^degree)
    (hr : r < 2^degree) (hr' : r' < 2^degree)
    (he : (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r).eval g l =
      (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r').eval g l') :
    l=l' ∧ r=r' := by
  have hs : 0 < 2^bits/(2^done*2^degree) := by rw [phase_stride bits done degree hd]; exact Nat.two_pow_pos _
  have hi := phase_index_lt bits done degree l r hd hl hr
  have hi' := phase_index_lt bits done degree l' r' hd hl' hr'
  rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hi,
    phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hi'] at he
  have heq : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) l r =
      laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) l' r' := by
    cases last with
    | false => exact he
    | true =>
      change outputAddress p (2^bits) g _ = outputAddress p (2^bits) g _ at he
      have hr := (outputAddress_injective p (2^bits) g g _ _ hp
        (reverseIndex_lt bits _ hi) (reverseIndex_lt bits _ hi') he).2
      have hx := congrArg (reverseIndex bits) hr
      simpa only [reverseIndex_involution bits _ hi,reverseIndex_involution bits _ hi'] using hx
  exact laneRegisterIndex_injective _ _ _ _ _ _ hs hr hr' heq

/-- Every original phase has a unique scatter for all supported layer positions. -/
theorem phase_addresses_nodup (n bits p done degree src dst : Nat) (first last : Bool) (g : Nat)
    (hp : 0 < p) (hd : done+degree ≤ bits) :
    ((phase n (2^bits) bits p done degree src dst first last).writeAddresses g).Nodup := by
  rw [phase_addresses]
  apply grid_nodup
  intro l hl r hr l' hl' r' hr' he
  exact phaseSaveIndex_injective bits p done degree g l l' r r' last hp hd hl hl' hr hr'
    (congrArg Prod.snd he)

/-- A real phase spans its entire upload tile, independently of its fused radix. -/
theorem phase_tile_size (n bits p done degree src dst : Nat) (first last : Bool)
    (hd : degree ≤ bits) :
    (phase n (2^bits) bits p done degree src dst first last).lanes *
      (phase n (2^bits) bits p done degree src dst first last).writes.length = 2^bits := by
  rw [PhaseMetadata.phase_writes_length]
  change (2^bits/2^degree)*2^degree = _
  exact Nat.div_mul_cancel (Nat.pow_dvd_pow 2 hd)


theorem batch_phase_addresses (n count bits p done degree src dst stride k : Nat)
    (first last : Bool) (g : Nat) :
    (batchPhase stride k (phase n count bits p done degree src dst first last)).writeAddresses g =
      (List.range ((count/2^degree)*k)).flatMap fun l =>
        (List.range (2^degree)).map fun r => (dst,
          (batchIndex stride k (count/2^degree) dst
            (phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r)).eval g l) := by
  unfold Phase.writeAddresses
  change (List.range ((count/2^degree)*k)).flatMap (fun l => _) = _
  apply congrArg (fun f => (List.range ((count/2^degree)*k)).flatMap f)
  funext l
  change (((((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).map fun w =>
      {w with index := batchIndex stride k (count/2^degree) w.array w.index}).map
        fun w => (w.array,w.index.eval g l)) = _
  simp only [List.map_map,Function.comp_def]
  have hm := map_zipIdx_second ((phaseAction n count p done degree src first).run {}).1.2
    (fun r => (dst,(batchIndex stride k (count/2^degree) dst
      (phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r)).eval g l))
  simpa only [PhaseMetadata.phaseAction_length] using hm

theorem batch_save_injective (bits p done degree dst stride k g l l' r r' : Nat)
    (last : Bool) (hp : 0 < p) (hd : done+degree ≤ bits) (hstride : 2^bits ≤ stride)
    (hdevice : last = true → dst ≤ 1) (hshared : last = false → dst=2 ∨ dst=3)
    (hl : l < (2^bits/2^degree)*k) (hl' : l' < (2^bits/2^degree)*k)
    (hr : r < 2^degree) (hr' : r' < 2^degree)
    (he : (batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r)).eval g l =
      (batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r')).eval g l') :
    l=l' ∧ r=r' := by
  let lanes := 2^bits/2^degree
  have hlanes : 0 < lanes := by
    dsimp [lanes]
    rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
    exact Nat.two_pow_pos _
  have hm := Nat.mod_lt l hlanes
  have hm' := Nat.mod_lt l' hlanes
  have hi := phase_index_lt bits done degree (l%lanes) r hd hm hr
  have hi' := phase_index_lt bits done degree (l'%lanes) r' hd hm' hr'
  rw [batchIndex_eval,batchIndex_eval] at he
  change tileIndex stride (l/lanes) dst _ = tileIndex stride (l'/lanes) dst _ at he
  have htile : l/lanes = l'/lanes := by
    cases last with
    | true =>
      have hdst := hdevice rfl
      have h2 : dst ≠ 2 := by omega
      have h3 : dst ≠ 3 := by omega
      simp only [tileIndex,show (dst == 2 || dst == 3) = false by simp [h2,h3],Bool.false_eq_true,ite_false] at he
      rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hi,
        phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hi'] at he
      change outputAddress p (2^bits) (g*k+l/lanes) _ = outputAddress p (2^bits) (g*k+l'/lanes) _ at he
      have hx := (outputAddress_injective p (2^bits) _ _ _ _ hp
        (reverseIndex_lt bits _ hi) (reverseIndex_lt bits _ hi') he).1
      omega
    | false =>
      have hdst := hshared rfl
      have hh : (dst == 2 || dst == 3) = true := by simpa using hdst
      simp only [tileIndex,hh,ite_true] at he
      rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ false hi,
        phaseSaveIndex_eval _ _ _ _ _ _ _ _ false hi'] at he
      simp only [Bool.false_eq_true,ite_false] at he
      have hx := congrArg (fun x => x/stride) he
      have hpos : 0 < stride := by have := Nat.two_pow_pos bits; omega
      rw [Nat.add_mul_div_right _ _ hpos,Nat.add_mul_div_right _ _ hpos,
        Nat.div_eq_of_lt (by omega : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l%lanes) r < stride),
        Nat.div_eq_of_lt (by omega : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l'%lanes) r' < stride)] at hx
      simpa using hx
  have hsave : (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r).eval (g*k+l/lanes) (l%lanes) =
      (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r').eval (g*k+l/lanes) (l'%lanes) := by
    rw [←htile] at he
    dsimp only [lanes] at he ⊢
    unfold tileIndex at he
    split at he <;> omega
  have hx := phaseSaveIndex_injective bits p done degree (g*k+l/lanes)
    (l%lanes) (l'%lanes) r r' last hp hd hm hm' hr hr' hsave
  constructor
  · have h1 := Nat.div_add_mod l lanes
    have h2 := Nat.div_add_mod l' lanes
    rw [htile,hx.1] at h1
    omega
  · exact hx.2

/-- Packed phases have a unique scatter by construction, including independent
shared tile coordinates and the final global Stockham permutation. -/
theorem batch_phase_addresses_nodup (n bits p done degree src dst stride k : Nat)
    (first last : Bool) (g : Nat) (hp : 0 < p) (hd : done+degree ≤ bits)
    (hstride : 2^bits ≤ stride) (hdevice : last=true → dst≤1)
    (hshared : last=false → dst=2 ∨ dst=3) :
    ((batchPhase stride k (phase n (2^bits) bits p done degree src dst first last)).writeAddresses g).Nodup := by
  rw [batch_phase_addresses]
  apply grid_nodup
  intro l hl r hr l' hl' r' hr' he
  exact batch_save_injective bits p done degree dst stride k g l l' r r' last hp hd hstride
    hdevice hshared hl hl' hr hr' (congrArg Prod.snd he)

/-- The allocator's chosen tile stride covers the complete transform tile. -/
theorem dispatch_tileSize_lower (n logP bits src dst : Nat) (hb : 0 < bits) :
    2^bits ≤ tileSize (dispatch n logP bits src dst) := by
  have hn := phaseDegrees_ne_nil bits hb
  cases he : phaseDegrees bits with
  | nil => exact False.elim (hn he)
  | cons c cs =>
    have hsum := phaseDegrees_sum bits
    rw [he] at hsum
    have hc : c ≤ bits := by simp only [List.sum_cons] at hsum; omega
    have hm : phase n (2^bits) bits (2^logP) 0 c src
        (phaseOutput bits dst 0 src c) true (0+c==bits) ∈
        (dispatch n logP bits src dst).phases := by
      simp [dispatch,he,buildPhases,phaseOutput]
    have h := maxFold_member (fun ph : Phase => ph.lanes*ph.writes.length)
      (dispatch n logP bits src dst).phases 1 _ hm
    rw [phase_tile_size _ _ _ _ _ _ _ _ _ hc] at h
    exact h

/-- Bounds for every concrete packed store, derived from its actual slot and
Stockham address rather than a finite checker receipt. -/
theorem packed_phase_writes_valid (total bits logP done degree src dst stride k group : Nat)
    (first last : Bool) (hp : logP+bits ≤ total) (hd : done+degree ≤ bits)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    ∀ lane < (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).lanes,
      ∀ w ∈ (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).writes,
        BlockLower.Valid (nttBlockProgram (2^total)) w.array (w.index.eval group lane) := by
  intro lane hl w hw
  have hm : (w.array,w.index.eval group lane) ∈
      (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).writeAddresses group :=
    List.mem_flatMap.mpr ⟨lane,List.mem_range.mpr hl,List.mem_map.mpr ⟨w,hw,rfl⟩⟩
  rw [batch_phase_addresses] at hm
  obtain ⟨l,hl,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  have hvalid : BlockLower.Valid (nttBlockProgram (2^total)) dst
      ((batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits (2^logP) (2^degree) (2^bits/(2^done*2^degree)) last r)).eval group l) := by
    have hl := List.mem_range.mp hl
    have hr := List.mem_range.mp hr
    let lanes := 2^bits/2^degree
    have hlanes : 0 < lanes := by
      dsimp only [lanes]
      rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
      exact Nat.two_pow_pos _
    have htile : l/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [Nat.mul_comm] using hl)
    have hidx := phase_index_lt bits done degree (l%lanes) r hd (Nat.mod_lt _ hlanes) hr
    rw [batchIndex_eval,phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hidx]
    cases last with
    | false =>
      have ha := hlocal rfl
      have hh : (dst==2 || dst==3)=true := by simpa using ha
      simp only [Bool.false_eq_true,ite_false,tileIndex,hh,ite_true]
      have hm := Nat.mul_le_mul_right stride (by omega : l/lanes+1 ≤ k)
      rw [Nat.add_mul,Nat.one_mul] at hm
      have hi : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l%lanes) r +
          (l/lanes)*stride < sharedWords (2^total) := by
        rw [Nat.mul_comm stride k] at hshared
        omega
      rcases ha with rfl | rfl <;>
        simpa [BlockLower.Valid,BlockLower.buffer,nttBlockProgram] using hi
    | true =>
      have ha := hdevice rfl
      have hh : (dst==2 || dst==3)=false := by simp; omega
      simp only [ite_true,tileIndex,hh,ite_false]
      have hf : 2^total = 2^logP*2^bits*2^(total-(logP+bits)) := by
        rw [←Nat.pow_add,←Nat.pow_add,Nat.add_sub_of_le hp]
      have hg : group*k+l/lanes < 2^logP*2^(total-(logP+bits)) := by
        have hg := hgroups _ htile
        rw [hf] at hg
        simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_div_cancel,
          Nat.two_pow_pos] using hg
      have hi := outputAddress_bound (2^logP) (2^bits) (2^(total-(logP+bits)))
        (group*k+l/lanes) _ (Nat.two_pow_pos _) hg (reverseIndex_lt bits _ hidx)
      rw [←hf] at hi
      have hcases : dst=0 ∨ dst=1 := by omega
      rcases hcases with rfl | rfl <;>
        simpa [BlockLower.Valid,BlockLower.buffer,nttBlockProgram,outputAddress] using hi
  have ha := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  dsimp only [Prod.fst,Prod.snd] at ha hi
  rw [←ha,←hi]
  exact hvalid

/-- Each logical result slot is one of the actual phase's stores. -/
theorem phase_slot_write (n count bits p done degree src dst : Nat) (first last : Bool)
    (r : Nat) (hr : r<2^degree) :
    (⟨dst,phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r,
      ((phaseAction n count p done degree src first).run {}).1.2.getD r 0⟩ : Write) ∈
      (phase n count bits p done degree src dst first last).writes := by
  let regs := ((phaseAction n count p done degree src first).run {}).1.2
  have hlen : r < regs.length := by
    dsimp only [regs]
    rw [PhaseMetadata.phaseAction_length]
    exact hr
  apply List.mem_map.mpr
  refine ⟨(regs.getD r 0,r),?_,rfl⟩
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  change regs[r]? = some (regs.getD r 0)
  rw [List.getElem?_eq_getElem hlen]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlen,Option.getD_some]

/-- Both sides of packed-phase memory safety follow from actual metadata. -/
theorem packed_phase_inBounds (total bits logP done degree src dst stride k group : Nat)
    (first last : Bool) (hp : logP+bits ≤ total) (hd : done+degree ≤ bits)
    (hsrc : src≤3) (hfirst : first=true → src≤1)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    BlockLower.PhaseInBounds (nttBlockProgram (2^total))
      (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)) group :=
  ⟨packed_phase_reads_valid total bits (2^logP) done degree src dst stride k group first last
    (by omega) hd hsrc hfirst hstride hshared hgroups,
   packed_phase_writes_valid total bits logP done degree src dst stride k group first last hp hd
    hstride hshared hdevice hlocal hgroups⟩

end Obend.Hardware.Gpu.NttDispatchGeometry
end

section
/-! Actual packed phase values, with all bounds and scatter obligations derived
from source metadata. No checker or computed-output premise is required. -/
namespace Obend.Hardware.Gpu.NttPackedValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.PhaseSemantics Obend.Hardware.Gpu.GoldilocksSource
set_option autoImplicit false

theorem packed_phase_value (total bits logP done degree src dst stride k group tile lane r : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (htotal : total≤32) (hp : logP+bits≤total) (hd : done+degree≤bits)
    (hsrc : src≤3) (hfirst : first=true → src≤1)
    (hstride : 2^bits≤stride) (hshared : stride*k≤sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ t, t<k → group*k+t<2^total/2^bits)
    (htile : tile<k) (hlane : lane<2^bits/2^degree) (hr : r<2^degree)
    (hgood : BlockLower.Good (nttBlockProgram (2^total)) mem)
    (hentry : ∀ i, i<2^bits →
      (valueAt (tileMemory stride tile mem) src (if first then group*k+tile+i*(2^total/2^bits) else i)).toNat=entry i)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP)
    (htable : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i) :
    (valueAt (evalPhase (batchPhase stride k
      (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)) group mem) dst
      (tileIndex stride tile dst
        ((phaseSaveIndex (2^bits) bits (2^logP) (2^degree)
          (2^bits/(2^done*2^degree)) last r).eval (group*k+tile) lane))).toNat =
    difStages bits done degree
      (preparedInput (2^total) (2^bits) (2^logP) (group*k+tile) first entry)
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  let ph := phase (2^total) (2^bits) bits (2^logP) done degree src dst first last
  have hreads : TileReads stride k ph group tile lane (tileMemory stride tile mem) mem := by
    apply tileMemory_reads
    intro read hread ha
    have hb := PhaseMetadata.phase_read_index_bound total bits (2^logP) done degree src dst
      (group*k+tile) lane first last (by omega) hd (hgroups _ htile) hlane read hread
    rcases hb with ⟨harray,hi⟩ | ⟨harray,_⟩
    · have hf : first=false := by
        cases first
        · rfl
        · have := hfirst rfl; omega
      simp only [hf,Bool.false_eq_true,ite_false] at hi
      exact Nat.lt_of_lt_of_le hi hstride
    · omega
  have hv := evalPhase_batch_value (nttBlockProgram (2^total)) stride k ph group tile lane
    (tileMemory stride tile mem) mem hgood
    (packed_phase_inBounds total bits logP done degree src dst stride k group first last
      hp hd hsrc hfirst hstride hshared hdevice hlocal hgroups)
    (batch_phase_addresses_nodup (2^total) bits (2^logP) done degree src dst stride k first last
      group (Nat.two_pow_pos _) hd hstride hdevice hlocal)
    htile hlane hreads _ (phase_slot_write (2^total) (2^bits) bits (2^logP) done degree src dst first last r hr)
  rw [hv]
  apply phase_register_value total bits (2^logP) done degree src dst (group*k+tile) lane first last
    (tileMemory stride tile mem) entry htotal (by omega) (Nat.two_pow_pos _) hd
    (hgroups _ htile) hlane hentry hcanonical _ r hr
  intro i hi
  change (valueAt (tileMemory stride tile mem) 4 i).toNat = _
  rw [tileMemory_value stride tile mem 4 i (by omega)]
  exact htable i hi

end Obend.Hardware.Gpu.NttPackedValue
end

section
namespace Obend.Hardware.Gpu.Ntt

/-- Every tile position is covered by an actually launched lane and register
of the source phase, including its computed stride. -/
theorem phase_index_cover (bits done degree i : Nat)
    (h : done + degree ≤ bits) (hi : i < 2^bits) :
    ∃ lane, lane < 2^bits / 2^degree ∧ ∃ r, r < 2^degree ∧
      laneRegisterIndex (2^degree) (2^bits / (2^done * 2^degree)) lane r = i := by
  rw [phase_stride bits done degree h]
  have he : 2^bits = (2^degree * 2^done) * 2^(bits-done-degree) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hlanes : 2^bits / 2^degree = 2^done * 2^(bits-done-degree) := by
    conv => lhs; rw [he, Nat.mul_assoc, Nat.mul_div_right _ (Nat.two_pow_pos degree)]
  refine ⟨(i / 2^(bits-done-degree) / 2^degree) * 2^(bits-done-degree) +
    i % 2^(bits-done-degree), ?_, i / 2^(bits-done-degree) % 2^degree, ?_, ?_⟩
  · rw [hlanes]
    apply laneRegisterIndex_cover_lane_lt _ _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    rwa [← he]
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact laneRegisterIndex_cover _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _)

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.NttGroupValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.NttPackedValue
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.GoldilocksSource
set_option autoImplicit false

def tileInput (total bits logP src G : Nat) (initial : Memory) : Nat → Nat :=
  preparedInput (2^total) (2^bits) (2^logP) G true
    (fun i => (valueAt initial src (G+i*(2^total/2^bits))).toNat)

def observed (bits logP stride tile G done input i : Nat) : Nat :=
  if done=bits then outputAddress (2^logP) (2^bits) G (reverseIndex bits i)
  else tileIndex stride tile input i

structure State (total bits logP src dst stride k group : Nat) (initial : Memory)
    (done input : Nat) (mem : Memory) : Prop where
  good : BlockLower.Good (nttBlockProgram (2^total)) mem
  table : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i
  source : ∀ i, valueAt mem src i=valueAt initial src i
  start : done=0 → input=src
  middle : 0<done → done<bits → input=2 ∨ input=3
  value : ∀ tile, tile<k → ∀ i, i<2^bits → 0<done →
    (valueAt mem input (observed bits logP stride tile (group*k+tile) done input i)).toNat =
      difStages bits 0 done (tileInput total bits logP src (group*k+tile) initial) i

theorem packed_row_frame (n bits p done degree src dst stride k group a : Nat)
    (first last : Bool) (mem : Memory) (ha : dst≠a) :
    (evalPhase (batchPhase stride k (phase n (2^bits) bits p done degree src dst first last)) group mem).getD a #[] =
      mem.getD a #[] := by
  apply evalPhase_row_frame
  intro w hw
  change w ∈ (phase n (2^bits) bits p done degree src dst first last).writes.map _ at hw
  obtain ⟨old,hold,he⟩ := List.mem_map.mp hw
  subst w
  change old.array ≠ a
  rw [phase_write_array n (2^bits) bits p done degree src dst first last old hold]
  exact ha

theorem state_step (total bits logP src dst stride k group : Nat) (initial : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hstride : 2^bits≤stride) (hshared : stride*k≤sharedWords (2^total))
    (hgroups : ∀ tile, tile<k → group*k+tile<2^total/2^bits)
    (done input chunk : Nat) (hc : 0<chunk) (hd : done+chunk≤bits)
    (mem : Memory) (hs : State total bits logP src dst stride k group initial done input mem) :
    State total bits logP src dst stride k group initial (done+chunk)
      (phaseOutput bits dst done input chunk)
      (evalPhase (batchPhase stride k
        (phase (2^total) (2^bits) bits (2^logP) done chunk input
          (phaseOutput bits dst done input chunk) (done==0) (done+chunk==bits))) group mem) := by
  let out := phaseOutput bits dst done input chunk
  let ph := batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done chunk input out
    (done==0) (done+chunk==bits))
  have hdone : done<bits := by omega
  have hin : input≤3 := by
    by_cases hz : done=0
    · rw [hs.start hz]; omega
    · rcases hs.middle (by omega) hdone with h | h <;> omega
  have hfirst : (done==0)=true → input≤1 := by
    intro h; rw [hs.start (by simpa using h)]; exact hsrc
  have hout : out=dst ∨ out=2 ∨ out=3 := by
    dsimp only [out,phaseOutput]
    split
    · exact Or.inl rfl
    · split <;> simp
  have hdevice : (done+chunk==bits)=true → out≤1 := by
    intro h; simpa only [out,phaseOutput,h,ite_true] using hdst
  have hlocal : (done+chunk==bits)=false → out=2 ∨ out=3 := by
    intro h; dsimp only [out,phaseOutput]; simp only [h,Bool.false_eq_true,ite_false]; split <;> simp
  have hsource : out≠src := by rcases hout with h | h | h <;> omega
  have hfour : out≠4 := by rcases hout with h | h | h <;> omega
  refine ⟨foldWrites_good _ mem (phaseWrites ph mem group) hs.good,?_,?_,?_,?_,?_⟩
  · intro i hi
    change ((evalPhase ph group mem).getD 4 #[] |>.getD i 0#64).toNat = _
    rw [packed_row_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfour]
    exact hs.table i hi
  · intro i
    change ((evalPhase ph group mem).getD src #[]).getD i 0#64 = _
    rw [packed_row_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsource]
    exact hs.source i
  · omega
  · intro _ hlt
    exact hlocal (by simp; omega)
  · intro tile htile i hi _
    obtain ⟨lane,hlane,r,hr,hindex⟩ := phase_index_cover bits done chunk i hd hi
    let entry : Nat → Nat := if done=0 then
      (fun i => (valueAt initial src (group*k+tile+i*(2^total/2^bits))).toNat)
      else difStages bits 0 done (tileInput total bits logP src (group*k+tile) initial)
    have hentry : ∀ j, j<2^bits →
        (valueAt (tileMemory stride tile mem) input
          (if (done==0) then group*k+tile+j*(2^total/2^bits) else j)).toNat=entry j := by
      intro j hj
      by_cases hz : done=0
      · have he := hs.start hz
        simp only [hz,beq_self_eq_true,ite_true,entry,he]
        rw [tileMemory_value _ _ _ _ _ (by omega)]
        have hh : (src==2 || src==3)=false := by simp; omega
        simp only [tileIndex,hh,Bool.false_eq_true,ite_false]
        rw [hs.source]
      · have hh : (done==0)=false := by simp [hz]
        simp only [hh,Bool.false_eq_true,ite_false,entry,if_neg hz]
        rw [tileMemory_value _ _ _ _ _ (by intro _; omega)]
        have hv := hs.value tile htile j hj (by omega)
        simpa only [observed,if_neg (by omega : done≠bits)] using hv
    have hcanonical : (done==0)=false → ∀ j, j<2^bits → entry j<goldilocksP := by
      intro hz j hj
      have hz' : done≠0 := by simpa using hz
      simp only [entry,if_neg hz']
      apply difStages_canonical bits 0 done (by omega) _ _ j hj
      exact preparedInput_canonical _ _ _ _ _ true _ (by simp)
    have hv := packed_phase_value total bits logP done chunk input out stride k group tile lane r
      (done==0) (done+chunk==bits) mem entry ht hp hd hin hfirst hstride hshared hdevice hlocal
      hgroups htile hlane hr hs.good hentry hcanonical hs.table
    have hidx := phase_index_lt bits done chunk lane r hd hlane hr
    rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ _ hidx,hindex] at hv
    have haddr : tileIndex stride tile out
        (if (done+chunk==bits) then outputAddress (2^logP) (2^bits) (group*k+tile) (reverseIndex bits i) else i) =
        observed bits logP stride tile (group*k+tile) (done+chunk) out i := by
      by_cases he : done+chunk=bits
      · have ho : out=dst := by simp [out,phaseOutput,he]
        have hh : (dst==2 || dst==3)=false := by simp; omega
        simp [he,observed,ho,tileIndex,hh]
      · simp [he,observed]
    change (valueAt (evalPhase ph group mem) out _).toNat = _ at hv
    unfold outputAddress at haddr
    rw [haddr] at hv
    rw [hv]
    by_cases hz : done=0
    · subst done
      simp only [entry,tileInput,Nat.zero_add,beq_self_eq_true,ite_true]
    · have hh : (done==0)=false := by simp [hz]
      simp only [preparedInput,hh,Bool.false_eq_true,ite_false,entry,if_neg hz]
      rw [difStages_fuse]
      simp only [Nat.zero_add]
      congr 2

/-- One actual packed workgroup computes every assigned tile's DFT. Scratch
memory is arbitrary apart from the ordinary row-size invariant. -/
theorem group_value (total logP bits src dst group : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hgroup : group < (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)).groups)
    (hg : BlockLower.Good (nttBlockProgram (2^total)) mem)
    (htable : ∀ i, i<2^total → (valueAt mem 4 i).toNat=modPow (rootOfUnity (2^total)) i)
    (tile : Nat) (htile : tile<packing (dispatch (2^total) logP bits src dst))
    (r : Nat) (hr : r<2^bits) :
    (valueAt (evalGroup (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)) group mem) dst
      (outputAddress (2^logP) (2^bits)
        (group*packing (dispatch (2^total) logP bits src dst)+tile) r)).toNat =
      dft (2^bits) (rootOfUnity (2^bits))
        (tileInput total bits logP src
          (group*packing (dispatch (2^total) logP bits src dst)+tile) mem) r := by
  let d := dispatch (2^total) logP bits src dst
  let stride := tileSize d
  let k := packing d
  have hgroups : ∀ t, t<k → group*k+t<2^total/2^bits := by
    intro t ht
    exact packed_group_bound d group t hgroup ht
  have hs : State total bits logP src dst stride k group mem 0 src mem :=
    ⟨hg,htable,fun _ => rfl,fun _ => rfl,by omega,by omega⟩
  have hv := dispatch_phases_invariant (2^total) logP bits src dst stride group hb
    (State total bits logP src dst stride k group mem)
    (fun done input chunk hc _hc2 hd => state_step total bits logP src dst stride k group mem ht hp hsrc hdst hne
      (dispatch_tileSize_lower _ _ _ _ _ hb) (sharedWords_covers _ _ hm) hgroups done input chunk hc hd)
    mem hs
  have hval := hv.value tile htile (reverseIndex bits r) (reverseIndex_lt bits r hr) hb
  simp only [observed,ite_true,reverseIndex_involution bits r hr] at hval
  rw [hval]
  rw [difStages_eq_dft bits (by omega) _ _ _ (reverseIndex_lt bits r hr),
    reverseIndex_involution bits r hr]
  exact preparedInput_canonical _ _ _ _ _ true _ (by simp)

end Obend.Hardware.Gpu.NttGroupValue
end

section
namespace Obend.Hardware.Gpu.NttGroupFrame
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

/-- A packed phase's device stores belong only to the original groups packed
into its own workgroup. Shared-row writes cannot alias a device destination. -/
theorem batch_phase_other_group (n bits p done degree src out dst stride k g G r : Nat)
    (first last : Bool) (hp : 0 < p) (hk : 0 < k) (hdst : dst ≤ 1)
    (hdegree : done+degree ≤ bits) (hr : r < 2^bits) (hgroup : G/k ≠ g)
    (hdevice : last=true → out=dst) (hshared : last=false → out=2 ∨ out=3) :
    (dst,outputAddress p (2^bits) G r) ∉
      (batchPhase stride k (phase n (2^bits) bits p done degree src out first last)).writeAddresses g := by
  rw [batch_phase_addresses]
  intro hmem
  obtain ⟨lane,hlane,hmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨reg,hreg,he⟩ := List.mem_map.mp hmem
  have hout : out=dst := congrArg Prod.fst he
  have haddr := congrArg Prod.snd he
  have hl := List.mem_range.mp hlane
  have hreg := List.mem_range.mp hreg
  cases last with
  | false => have h := hshared rfl; omega
  | true =>
    subst out
    let lanes := 2^bits/2^degree
    have hlanes : 0 < lanes := by
      dsimp [lanes]
      rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
      exact Nat.two_pow_pos _
    have htile : lane/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [lanes,Nat.mul_comm] using hl)
    have hlocal := Nat.mod_lt lane hlanes
    have hindex := phase_index_lt bits done degree (lane%lanes) reg hdegree hlocal hreg
    rw [batchIndex_eval] at haddr
    change tileIndex stride (lane/lanes) dst _ = outputAddress p (2^bits) G r at haddr
    have h2 : dst ≠ 2 := by omega
    have h3 : dst ≠ 3 := by omega
    simp only [tileIndex,show (dst==2 || dst==3)=false by simp [h2,h3],Bool.false_eq_true,ite_false] at haddr
    rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hindex] at haddr
    change outputAddress p (2^bits) (g*k+lane/lanes) _ = outputAddress p (2^bits) G r at haddr
    have hg := (outputAddress_injective p (2^bits) _ _ _ _ hp
      (reverseIndex_lt bits _ hindex) hr haddr).1
    apply hgroup
    rw [←hg,Nat.mul_comm g k,Nat.mul_add_div hk,Nat.div_eq_of_lt htile,Nat.add_zero]

/-- The actual source phase list satisfies group separation at every local
layer, including the alternating shared rows before its final device write. -/
theorem buildPhases_other_group (n bits p dst stride k g G r done input : Nat)
    (chunks : List Nat) (hp : 0 < p) (hk : 0 < k) (hdst : dst ≤ 1)
    (hbound : done+chunks.sum ≤ bits) (hr : r < 2^bits) (hgroup : G/k ≠ g) :
    ∀ ph ∈ buildPhases n bits p dst done input chunks,
      (dst,outputAddress p (2^bits) G r) ∉ (batchPhase stride k ph).writeAddresses g := by
  induction chunks generalizing done input with
  | nil => intro ph hph; cases hph
  | cons chunk chunks ih =>
    intro ph hph
    simp only [buildPhases,List.mem_cons] at hph
    rcases hph with hph | hph
    · subst ph
      apply batch_phase_other_group n bits p done chunk input _ dst stride k g G r _ _ hp hk hdst
        (by simp only [List.sum_cons] at hbound; omega) hr hgroup
      · intro hlast; simp only [hlast,ite_true]
      · intro hlast
        simp only [hlast,Bool.false_eq_true,ite_false]
        split <;> simp
    · apply ih (done+chunk) _ (by simp only [List.sum_cons] at hbound; omega) ph hph

/-- Every actual packed workgroup preserves destination cells assigned to all
other packed workgroups. No value or memory-bound assumption is needed. -/
theorem group_other_output (n logP bits src dst stride g G r : Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hgroup : G/packing (dispatch n logP bits src dst) ≠ g) :
    valueAt (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem)
      dst (outputAddress (2^logP) (2^bits) G r) =
      valueAt mem dst (outputAddress (2^logP) (2^bits) G r) := by
  apply evalPhases_cell_frame
  intro ph hph
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hph
  apply buildPhases_other_group n bits (2^logP) dst stride
    (packing (dispatch n logP bits src dst)) g G r 0 src (phaseDegrees bits)
    (Nat.two_pow_pos _) (packing_pos _) hdst (by rw [phaseDegrees_sum]; omega) hr hgroup original ho

/-- A group preserves all rows except its destination and the two shared rows. -/
theorem group_row_frame (n logP bits src dst stride g a : Nat) (mem : Memory)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD a #[] = mem.getD a #[] := by
  apply evalPhases_row_frame
  intro ph hph w hw
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hph
  obtain ⟨out,hw',rfl⟩ := List.mem_map.mp hw
  have ha := buildPhases_write_arrays n bits (2^logP) dst 0 src (phaseDegrees bits) original ho out hw'
  dsimp only
  rcases ha with ha | ha | ha <;> omega

theorem group_source_frame (n logP bits src dst stride g : Nat) (mem : Memory)
    (hsrc : src ≤ 1) (hne : src ≠ dst) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD src #[] = mem.getD src #[] :=
  group_row_frame n logP bits src dst stride g src mem hne (by omega) (by omega)

theorem group_twiddle_frame (n logP bits src dst stride g : Nat) (mem : Memory) (hdst : dst ≤ 1) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD 4 #[] = mem.getD 4 #[] :=
  group_row_frame n logP bits src dst stride g 4 mem (by omega) (by decide) (by decide)

theorem groups_other_output (n logP bits src dst stride G r : Nat) (groups : List Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hgroups : ∀ g, g ∈ groups → G/packing (dispatch n logP bits src dst) ≠ g) :
    valueAt (groups.foldl (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem)
      dst (outputAddress (2^logP) (2^bits) G r) = valueAt mem dst (outputAddress (2^logP) (2^bits) G r) := by
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih _ (fun gg hg => hgroups gg (by simp [hg]))]
    exact group_other_output n logP bits src dst stride g G r mem hdst hr (hgroups g (by simp))

/-- Row framing also holds through arbitrary group prefixes or suffixes. -/
theorem groups_row_frame (n logP bits src dst stride a : Nat) (groups : List Nat) (mem : Memory)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (groups.foldl (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem).getD a #[] =
      mem.getD a #[] := by
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih]
    exact group_row_frame n logP bits src dst stride g a mem hd h2 h3

/-- The full actual dispatch retains the output established by the unique
packed group responsible for this original group. Its prefix state is explicit. -/
theorem dispatch_output_at_group (n logP bits src dst stride G r : Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hg : G/packing (dispatch n logP bits src dst) <
      (batchTiles stride (dispatch n logP bits src dst)).groups) :
    valueAt (evalDispatch (batchTiles stride (dispatch n logP bits src dst)) mem)
      dst (outputAddress (2^logP) (2^bits) G r) =
    valueAt (evalGroup (batchTiles stride (dispatch n logP bits src dst))
      (G/packing (dispatch n logP bits src dst))
      ((List.range (G/packing (dispatch n logP bits src dst))).foldl
        (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem))
      dst (outputAddress (2^logP) (2^bits) G r) := by
  let d := batchTiles stride (dispatch n logP bits src dst)
  let owner := G/packing (dispatch n logP bits src dst)
  let suffix := (List.range (d.groups-(owner+1))).map ((owner+1)+·)
  have hsplit : List.range d.groups = List.range (owner+1) ++ suffix := by
    calc
      List.range d.groups = List.range ((owner+1)+(d.groups-(owner+1))) := by congr 1; dsimp [d,owner]; omega
      _ = _ := List.range_add
  change valueAt (evalDispatch d mem) _ _ = _
  unfold evalDispatch
  rw [hsplit,List.foldl_append]
  have hf := groups_other_output n logP bits src dst stride G r suffix
    ((List.range (owner+1)).foldl (fun m g => evalGroup d g m) mem) hdst hr (by
      intro g hmem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
      change owner ≠ owner+1+i
      omega)
  change valueAt (suffix.foldl (fun m g => evalGroup d g m)
    ((List.range (owner+1)).foldl (fun m g => evalGroup d g m) mem)) _ _ = _
  rw [hf]
  simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

end Obend.Hardware.Gpu.NttGroupFrame
end

section
namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open GoldilocksSource Stockham

/-- The exact value contract of an actual batched upload. This is an interface
for proof composition, not an alternative evaluator or an emitted certificate. -/
def UploadDFT (bits done degree src dst : Nat) (mem : Memory) : Prop :=
  let n := 2^bits
  let d := BlockNtt.dispatch n done degree src dst
  let result := evalDispatch (BlockNtt.batchTiles (BlockNtt.tileSize d) d) mem
  ∀ g, g < n/(2^degree) → ∀ r, r < 2^degree →
    (valueAt result dst (g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done))).toNat =
      dft (2^degree) (rootOfUnity (2^degree))
        (fun t => mulMod (valueAt mem src (g+t*(n/2^degree))).toNat
          (modPow (rootOfUnity n) (t*(g%(2^done))*(n/2^degree/2^done)))) r

def TwiddleMemory (n : Nat) (mem : Memory) : Prop :=
  ∀ i, i < n → (valueAt mem 4 i).toNat = modPow (rootOfUnity n) i

structure StageInvariant (bits : Nat) (input : Nat → Nat) (done current : Nat) (mem : Memory) : Prop where
  device : current ≤ 1
  good : BlockLower.Good (nttBlockProgram (2^bits)) mem
  twiddles : TwiddleMemory (2^bits) mem
  values : LayoutValues (2^done) (2^bits/2^done) (rootOfUnity (2^bits)) input
    (fun i => (valueAt mem current i).toNat)
  canonical : 0 < done → ∀ i, i < 2^bits → (valueAt mem current i).toNat < goldilocksP

/-- One actual upload advances the whole-program invariant. All source indices,
bit reversal and register arithmetic enter through the upload value theorem. -/
theorem StageInvariant.step (bits done degree current : Nat) (input : Nat → Nat) (mem : Memory)
    (hbits : bits ≤ 32) (hd : done+degree ≤ bits) (hdegree : 0 < degree)
    (before : StageInvariant bits input done current mem)
    (execute : UploadDFT bits done degree current (1-current) mem) :
    StageInvariant bits input (done+degree) (1-current)
      (evalDispatch (BlockNtt.batchTiles
        (BlockNtt.tileSize (BlockNtt.dispatch (2^bits) done degree current (1-current)))
        (BlockNtt.dispatch (2^bits) done degree current (1-current))) mem) := by
  constructor
  · omega
  · exact dispatch_good _ _ _ before.good
  · intro i hi
    have hf := NttDispatchCorrect.dispatch_row_frame (2^bits) done degree current (1-current)
      (BlockNtt.tileSize (BlockNtt.dispatch (2^bits) done degree current (1-current))) mem 4
      (by omega) (by decide) (by decide)
    simpa only [valueAt,hf] using before.twiddles i hi
  · exact layout_upload_bits bits done degree hbits hd input _ _ before.values execute
  · intro _ i hi
    obtain ⟨g,hg,r,hr,he⟩ := output_cover_bits bits done degree i hd hi
    rw [←he,execute g hg r hr]
    exact Nat.mod_lt _ (by decide)

/-- Whole-source composition. The remaining premise is precisely the actual
upload lemma, universally quantified over its represented memories; the final
public NTT theorem discharges it with the register/phase proof. -/
theorem program_value_of_uploads (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits)
    (uploads : ∀ done degree current mem,
      degree ∈ uploadSchedule (2^bits) → done+degree ≤ bits → current ≤ 1 →
      BlockNtt.dispatch (2^bits) done degree current (1-current) ∈ (sourceUploads (2^bits)).1 →
      BlockLower.Good (nttBlockProgram (2^bits)) mem → TwiddleMemory (2^bits) mem →
      UploadDFT bits done degree current (1-current) mem)
    (i : Nat) (hi : i < 2^bits) :
    (valueAt (evalProgram (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input])) (sourceUploads (2^bits)).2 i).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
  let n := 2^bits
  let values := fun j => (input.getD j 0#64).toNat
  let initial := initialMemory (nttBlockProgram n) [input]
  have hs : (uploadSchedule n).sum = bits := by simpa [n,Nat.log2_two_pow] using uploadSchedule_sum n
  have init : StageInvariant bits values 0 0 initial := by
    constructor
    · decide
    · exact initial_good n input hinput
    · exact initial_twiddle_value n input
    · simpa only [Nat.pow_zero,Nat.div_one,valueAt,initial,initial_input,n,values] using
        layout_initial n (rootOfUnity n) values
    · omega
  let transform := fun d => BlockNtt.batchTiles (BlockNtt.tileSize d) d
  have final := buildUploads_invariant n (uploadSchedule n) transform (StageInvariant bits values) bits
    (sourceUploads n).1 (by
      intro degree hdegree done current mem hmember hbound before
      have hp : 0 < degree := uploadDegrees_positive _ _ _ (by split <;> decide) degree hdegree
      exact before.step bits done degree current values mem (by omega) hbound hp
        (uploads done degree current mem hdegree hbound before.device hmember before.good before.twiddles))
    0 0 initial (fun _ h => h) (by omega) init
  rw [hs,Nat.zero_add] at final
  change StageInvariant bits values bits (sourceUploads n).2
    (evalProgram (nttBlockProgram n) initial) at final
  have hv := layout_final n (rootOfUnity n) values
    (fun j => (valueAt (evalProgram (nttBlockProgram n) initial) (sourceUploads n).2 j).toNat)
    (by simpa only [Nat.div_self (Nat.two_pow_pos bits)] using final.values) i hi
  rw [Nat.mod_eq_of_lt (final.canonical hpos i hi)] at hv
  exact hv

end Obend.Hardware.Gpu.Ntt
end

section
namespace Obend.Hardware.Gpu.NttDispatchValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttGroupValue Obend.Hardware.Gpu.NttGroupFrame
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

theorem groups_good (p : Program) (d : Dispatch) (groups : List Nat) (mem : Memory)
    (hg : BlockLower.Good p mem) : BlockLower.Good p (groups.foldl (fun m g => evalGroup d g m) mem) := by
  induction groups generalizing mem with
  | nil => exact hg
  | cons g groups ih =>
    exact ih (evalGroup d g mem) (evalGroup_good p d g mem hg)

/-- Universal value theorem for the real packed dispatch. Prefix groups retain
its input and constants; suffix groups retain its established output cells. -/
theorem dispatch_value (total logP bits src dst : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hg : BlockLower.Good (nttBlockProgram (2^total)) mem)
    (htable : TwiddleMemory (2^total) mem)
    (G : Nat) (hG : G<2^total/2^bits) (r : Nat) (hr : r<2^bits) :
    (valueAt (evalDispatch (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)) mem) dst
      (outputAddress (2^logP) (2^bits) G r)).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (tileInput total bits logP src G mem) r := by
  let d := dispatch (2^total) logP bits src dst
  let stride := tileSize d
  let packed := batchTiles stride d
  let owner := G/packing d
  let tile := G%packing d
  let beforeGroup := (List.range owner).foldl (fun m g => evalGroup packed g m) mem
  have hsplit := packed_group_split d G hG
  have howner : owner < packed.groups := hsplit.1
  have htile : tile < packing d := hsplit.2.1
  have hjoin : owner*packing d+tile=G := hsplit.2.2
  have hgood : BlockLower.Good (nttBlockProgram (2^total)) beforeGroup := groups_good _ packed (List.range owner) mem hg
  have hsource : beforeGroup.getD src #[] = mem.getD src #[] :=
    groups_row_frame (2^total) logP bits src dst stride src (List.range owner) mem hne (by omega) (by omega)
  have hconstants : beforeGroup.getD 4 #[] = mem.getD 4 #[] :=
    groups_row_frame (2^total) logP bits src dst stride 4 (List.range owner) mem (by omega) (by decide) (by decide)
  have htable' : TwiddleMemory (2^total) beforeGroup := by
    intro i hi
    simpa only [valueAt,hconstants] using htable i hi
  have hv := group_value total logP bits src dst owner beforeGroup ht hp hb hsrc hdst hne hm
    howner hgood htable' tile htile r hr
  change (valueAt (evalGroup packed owner beforeGroup) dst
    (outputAddress (2^logP) (2^bits) (owner*packing d+tile) r)).toNat = _ at hv
  rw [hjoin] at hv
  have hframe := dispatch_output_at_group (2^total) logP bits src dst stride G r mem hdst hr howner
  change valueAt (evalDispatch packed mem) dst _ = valueAt (evalGroup packed owner beforeGroup) dst _ at hframe
  rw [hframe,hv]
  apply congrArg (fun f => dft (2^bits) (rootOfUnity (2^bits)) f r)
  funext i
  simp only [tileInput,preparedInput,ite_true,valueAt,hsource]

/-- The actual-upload contract required by whole-program Stockham composition,
with its checker and computed-value premises completely discharged. -/
theorem upload_dft (total logP bits src dst : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hg : BlockLower.Good (nttBlockProgram (2^total)) mem)
    (htable : TwiddleMemory (2^total) mem) : UploadDFT total logP bits src dst mem := by
  intro G hG r hr
  exact dispatch_value total logP bits src dst mem ht hp hb hsrc hdst hne hm hg htable G hG r hr

end Obend.Hardware.Gpu.NttDispatchValue
end

section
namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

/-- The sole NTT's declared size domain. -/
@[expose] def Supported (n : Nat) : Prop := 2 ≤ n ∧ n = 2^(Nat.log2 n) ∧ n < 2^26
instance (n : Nat) : Decidable (Supported n) := by unfold Supported; infer_instance

/-- The declared size domain is exactly the positive bit counts below 26. -/
theorem supported_log (n : Nat) (h : Supported n) : 0 < Nat.log2 n ∧ Nat.log2 n ≤ 25 := by
  rcases h with ⟨hn,he,hs⟩
  constructor
  · by_cases hz : 0 < Nat.log2 n
    · exact hz
    · have hk : Nat.log2 n = 0 := by omega
      rw [hk] at he
      simp at he
      omega
  · by_cases hz : Nat.log2 n ≤ 25
    · exact hz
    · have hk : 26 ≤ Nat.log2 n := by omega
      have hp : 2^26 ≤ 2^(Nat.log2 n) := Nat.pow_le_pow_right (by decide) hk
      omega

theorem supported_power (bits : Nat) (hp : 0 < bits) (hb : bits ≤ 25) : Supported (2^bits) := by
  constructor
  · have h := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 1 ≤ bits)
    simpa using h
  constructor
  · simp [Nat.log2_two_pow]
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- NTT source admission goes through the general Core4 block fragment. There
is one NTT construction, using shared field arithmetic and the general lowerer. -/
@[expose] def compile (n : Nat) : Except String BlockPlan.Plan :=
  if Supported n then BlockPlan.check (Ntt.nttBlockProgram n)
  else .error "NTT source: expected a supported power-of-two size below 2^26"

def program (n : Nat) : Term := BlockCoreProgram.source (Ntt.nttBlockProgram n)

theorem compile_source (n : Nat) (plan : BlockPlan.Plan) (h : compile n = .ok plan) :
    plan.source = Ntt.nttBlockProgram n := by
  unfold compile at h
  split at h
  · exact BlockPlan.check_source _ plan h
  · contradiction

theorem compile_supported (n : Nat) (plan : BlockPlan.Plan) (h : compile n = .ok plan) :
    Supported n := by
  unfold compile at h
  split at h
  · assumption
  · contradiction

/-- The actual NTT source, including register tiles and shared phases, reaches
flat GPU semantics through the general block-level Core4 theorem. This statement
is universal over inputs; `NttCorrect` separately proves and composes equality
with the DFT for every supported size. -/
theorem source_to_gpu_encoded (n : Nat) (plan : BlockPlan.Plan) (hc : compile n = .ok plan)
    (mem : Memory) (flat : FlatMemory)
    (hg : BlockLower.Good (Ntt.nttBlockProgram n) mem)
    (hf : Represents (Ntt.nttBlockProgram n) mem flat)
    (array index : Nat) (hv : Valid (Ntt.nttBlockProgram n) array index) :
    Steps (BlockPlan.observe (program n) (BlockCoreEncoding.memory mem) array index)
      (.nat ((lowerProgram (Ntt.nttBlockProgram n) flat)
        (address (Ntt.nttBlockProgram n) array index)).toNat) := by
  have he := compile_source n plan hc
  have h := plan.source_to_gpu_encoded mem flat (he.symm ▸ hg) (he.symm ▸ hf)
    array index (he.symm ▸ hv)
  simpa only [BlockPlan.Plan.term, he, program] using h

end Obend.Hardware.Gpu.NttSource
end

section
namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.Ntt

/-- Composition boundary for the upload proof: the actual encoded Core4 source
and the admitted GPU lowering return the same natural-order DFT word. -/
theorem encoded_dft_of_uploads (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits)
    (plan : BlockPlan.Plan) (hc : compile (2^bits) = .ok plan)
    (flat : FlatMemory)
    (hf : Represents (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input]) flat)
    (uploads : ∀ done degree current mem,
      degree ∈ uploadSchedule (2^bits) → done+degree ≤ bits → current ≤ 1 →
      BlockNtt.dispatch (2^bits) done degree current (1-current) ∈ (sourceUploads (2^bits)).1 →
      BlockLower.Good (nttBlockProgram (2^bits)) mem → TwiddleMemory (2^bits) mem →
      UploadDFT bits done degree current (1-current) mem)
    (i : Nat) (hi : i < 2^bits) :
    let value := dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i
    Steps (BlockPlan.observe (program (2^bits))
      (BlockCoreEncoding.memory (initialMemory (nttBlockProgram (2^bits)) [input]))
      (sourceUploads (2^bits)).2 i) (.nat value) ∧
    ((lowerProgram (nttBlockProgram (2^bits)) flat)
      (address (nttBlockProgram (2^bits)) (sourceUploads (2^bits)).2 i)).toNat = value := by
  dsimp only
  have hg := initial_good (2^bits) input hinput
  have he := compile_source (2^bits) plan hc
  have hcheck : (nttBlockProgram (2^bits)).check = .ok () := he ▸ plan.checked
  have hv := output_valid (2^bits) i hi
  have hl := checkedProgram_sound (nttBlockProgram (2^bits)) _ flat hg hf hcheck
  have hvalue := program_value_of_uploads bits hbits hpos input hinput uploads i hi
  have htarget : ((lowerProgram (nttBlockProgram (2^bits)) flat)
      (address (nttBlockProgram (2^bits)) (sourceUploads (2^bits)).2 i)).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
    rw [hl _ _ hv]
    exact hvalue
  constructor
  · have hs := source_to_gpu_encoded (2^bits) plan hc _ flat hg hf _ i hv
    rw [htarget] at hs
    exact hs
  · exact htarget

end Obend.Hardware.Gpu.NttSource
end

section
namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.PhaseSemantics

theorem output_port (n : Nat) : (nttBlockProgram n).outputs.getD 0 0 = (sourceUploads n).2 := by
  simp [nttBlockProgram]

/-- Every supported power-of-two transform, every input word and every output
coordinate: the actual source evaluator is the natural-order Goldilocks DFT.
There is no admission, computed-output, or finite-size certificate premise. -/
theorem nttBlockProgram_dft_power (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits) (i : Nat) (hi : i < 2^bits) :
    (valueAt (evalProgram (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input])) (sourceUploads (2^bits)).2 i).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
  apply program_value_of_uploads bits hbits hpos input hinput
  · intro done degree current mem hdegree hdone hcurrent hmember hgood htable
    exact NttDispatchValue.upload_dft bits done degree current (1-current) mem
      (by omega) hdone (uploadSchedule_bounds (2^bits) degree hdegree).1
      hcurrent (by omega) (by omega) hmember hgood htable
  · exact hi

/-- Universal equality at the actual declared output port, for exactly the
size domain accepted by the NTT source frontend. Inputs may be noncanonical. -/
theorem nttBlockProgram_dft (n : Nat) (hn : NttSource.Supported n)
    (input : Array Word) (hinput : input.size = n) (i : Nat) (hi : i < n) :
    (valueAt (evalProgram (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i).toNat =
      dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i := by
  have hk := NttSource.supported_log n hn
  have h := nttBlockProgram_dft_power (Nat.log2 n) hk.2 hk.1 input
    (by simpa only [← hn.2.1] using hinput) i (by simpa only [← hn.2.1] using hi)
  simpa only [← hn.2.1,output_port] using h

end Obend.Hardware.Gpu.Ntt

namespace Obend.Hardware.Gpu.NttSource
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.Ntt

/-- The actual encoded block source and its admitted general GPU lowering both
return the DFT. The remaining premises describe input shape, source admission
and the flat-memory representation, never an answer or transform property. -/
theorem source_to_gpu_dft_encoded (n : Nat) (plan : BlockPlan.Plan) (hc : compile n = .ok plan)
    (input : Array Word) (hinput : input.size = n) (flat : FlatMemory)
    (hf : Represents (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]) flat)
    (i : Nat) (hi : i < n) :
    let value := dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i
    Steps (BlockPlan.observe (program n)
      (BlockCoreEncoding.memory (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i) (.nat value) ∧
    ((lowerProgram (nttBlockProgram n) flat)
      (address (nttBlockProgram n) ((nttBlockProgram n).outputs.getD 0 0) i)).toNat = value := by
  dsimp only
  simp only [output_port]
  have hg := initial_good n input hinput
  have he := compile_source n plan hc
  have hcheck : (nttBlockProgram n).check = .ok () := he ▸ plan.checked
  have hv := output_valid n i hi
  have hl := checkedProgram_sound (nttBlockProgram n) _ flat hg hf hcheck
  have hvalue := nttBlockProgram_dft n (compile_supported n plan hc) input hinput i hi
  rw [output_port] at hvalue
  have htarget : ((lowerProgram (nttBlockProgram n) flat)
      (address (nttBlockProgram n) (sourceUploads n).2 i)).toNat =
      dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i := by
    rw [hl _ _ hv]
    exact hvalue
  constructor
  · have hs := source_to_gpu_encoded n plan hc _ flat hg hf _ i hv
    rw [htarget] at hs
    exact hs
  · exact htarget

end Obend.Hardware.Gpu.NttSource
end

end
