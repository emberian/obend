module
public import Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.CollectiveTree
@[expose] public section

/-! Work-efficient ordered trees and hierarchical reduce-then-scan in ArrayKernel.
There is no scan shader template or sequential segment invocation. Every tree row
is a separate snapshot array. Across groups, dependencies cross dispatch boundaries.
Static segment/chunk descriptors are compact immutable index tables, not per-element
prefix ranges. Empty reductions explicitly write the monoid identity.
-/
namespace Obend.Hardware.Gpu.CollectiveBlock
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
set_option autoImplicit false

def combineOp : ReduceOp → ElemOp
  | .add => .scalar .add
  | .mul => .scalar .mul
  | .band => .band
  | .bor => .bor

@[simp] theorem combineOp_sound (op : ReduceOp) (a b : Word) :
    evalElemOp (combineOp op) [a,b] = op.combine a b := by
  cases op <;> rfl

def twice : Ix := .mul (.lit 2) .lane
def next : Ix := .add twice (.lit 1)

/-- One ordered tree level; parents write once to a separate compact row. -/
def upPhase (op : ReduceOp) (parents src dst : Nat) : Phase :=
  { lanes := parents
    reads := [⟨0,src,twice⟩, ⟨1,src,next⟩]
    code := [⟨combineOp op,[0,1],2⟩]
    writes := [⟨dst,.lane,2⟩] }

/-- Parent prefix goes left; parent prefix combined with left total goes right. -/
def downPhase (op : ReduceOp) (parents totals src dst : Nat) : Phase :=
  { lanes := parents
    reads := [⟨0,src,.lane⟩, ⟨1,totals,twice⟩]
    code := [⟨combineOp op,[0,1],2⟩]
    writes := [⟨dst,twice,0⟩, ⟨dst,next,2⟩] }

structure Chunk where
  start : Nat
  length : Nat
  result : Nat
  deriving Repr

/-- Segment descriptors in source order, retaining empty segments. Offsets are
explicit so the same metadata constructor supports inductive composition. -/
def segmentsFrom (start result : Nat) : List Nat → List Chunk
  | [] => []
  | n::ns => ⟨start,n,result⟩ :: segmentsFrom (start+n) (result+1) ns

def segments (ns : List Nat) : List Chunk := segmentsFrom 0 0 ns

/-- Positive chunks of one segment, with contiguous aggregate result slots. -/
def segmentChunks (tile start result len : Nat) : List Chunk :=
  (List.range ((len+tile-1)/tile)).map fun j =>
    ⟨start+j*tile, min tile (len-j*tile), result+j⟩

/-- Source order and aggregate order advance together across segment boundaries.
Empty scan segments contribute no chunks. -/
def chunksFrom (tile start result : Nat) : List Nat → List Chunk
  | [] => []
  | n::ns => segmentChunks tile start result n ++
      chunksFrom tile (start+n) (result+(n+tile-1)/tile) ns

def chunks (tile : Nat) (ns : List Nat) : List Chunk := chunksFrom tile 0 0 ns

/-- Split only the selected unfinished descriptors. Original input positions
are retained; aggregate slots are compact and consecutive. -/
def splitChunksFrom (tile result : Nat) : List Chunk → List Chunk
  | [] => []
  | c::cs => segmentChunks tile c.start result c.length ++
      splitChunksFrom tile (result+(c.length+tile-1)/tile) cs

def splitChunks (tile : Nat) (cs : List Chunk) : List Chunk := splitChunksFrom tile 0 cs

/-- Recursive summary descriptors use compact input positions while retaining
the original reduction result slots. Completed descriptors need not recur. -/
def summaryChunksFrom (tile start : Nat) : List Chunk → List Chunk
  | [] => []
  | c::cs => ⟨start,(c.length+tile-1)/tile,c.result⟩ ::
      summaryChunksFrom tile (start+(c.length+tile-1)/tile) cs

def summaryChunks (tile : Nat) (cs : List Chunk) : List Chunk := summaryChunksFrom tile 0 cs

def descriptor (cs : List Chunk) (f : Chunk → Nat) : Ix :=
  .lookup (cs.toArray.map f) .group

structure Build where
  buffers : Array Buffer := #[]
  dispatches : Array Dispatch := #[]
abbrev BuildM := StateT Build (Except String)

def allocate (size : Nat) (storage : Storage := .device) : BuildM Nat := do
  let st ← get
  set {st with buffers := st.buffers.push ⟨size,storage,[]⟩}
  return st.buffers.size

def emit (groups : Nat) (phases : List Phase) : BuildM Unit := do
  if groups > 0 && !phases.isEmpty then
    modify fun s => {s with dispatches := s.dispatches.push ⟨groups,phases⟩}

structure Trees where
  up : Nat
  down : Nat
  depth : Nat

/-- Compact materialized rows, in their canonical decreasing-size order. -/
def treeRows (depth : Nat) : List Buffer :=
  (List.range (depth+1)).map fun k => ⟨2^(depth-k),.shared,[]⟩

/-- At most 4*tile-2 shared words, reused between every group and dispatch. -/
def allocateTrees (depth : Nat) : BuildM Trees := do
  let st ← get
  let rows := (treeRows depth).toArray
  set {st with buffers := st.buffers ++ rows ++ rows}
  return ⟨st.buffers.size,st.buffers.size+depth+1,depth⟩

def loadPhase (src dst valid : Nat) (offset : Ix) : Phase :=
  { lanes := valid, reads := [⟨0,src,.add offset .lane⟩], code := [],
    writes := [⟨dst,.lane,0⟩] }

def fillPhase (op : ReduceOp) (dst start count : Nat) : Phase :=
  { lanes := count, reads := [], code := [⟨.scalar (.const op.identity.toInt),[],0⟩],
    writes := [⟨dst,.add (.lit start) .lane,0⟩] }

/-- Materialize a padded tree once. The padding phase does not read out-of-bounds data. -/
def upsweep (op : ReduceOp) (tree : Trees) (src valid depth : Nat) (offset : Ix) : List Phase :=
  [loadPhase src tree.up valid offset] ++
  (if valid < 2^depth then [fillPhase op tree.up valid (2^depth-valid)] else []) ++
  (List.range depth).map fun k => upPhase op (2^(depth-k-1)) (tree.up+k) (tree.up+k+1)

def seedPhase (op : ReduceOp) (dst : Nat) (seed : Option (Nat × Ix)) : Phase :=
  match seed with
  | none => fillPhase op dst 0 1
  | some (src,index) =>
      { lanes := 1, reads := [⟨0,src,index⟩], code := [], writes := [⟨dst,.lit 0,0⟩] }

def storeScanPhase (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (dst valid : Nat) (offset : Ix) : Phase :=
  { lanes := valid
    reads := [⟨0,tree.down,.lane⟩] ++
      (if mode == .inclusive then [⟨1,tree.up,.lane⟩] else [])
    code := if mode == .inclusive then [⟨combineOp op,[0,1],2⟩] else []
    writes := [⟨dst,.add offset .lane,if mode == .inclusive then 2 else 0⟩] }

def tileDepth (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n-1)+1

/-- Equal-valid-length buckets avoid divergent barriers or a dispatch per segment.
Each bucket uses descriptor lookups to address its arbitrary segment positions. -/
def buckets (cs : List Chunk) : List (Nat × List Chunk) :=
  (cs.map (·.length)).eraseDups.map fun n => (n, cs.filter (·.length == n))

/-- Pure bucket schedule used directly by the builder and semantic proofs. -/
def reducePhases (op : ReduceOp) (tree : Trees) (src dst valid depth : Nat)
    (offset result : Ix) : List Phase :=
  if valid == 0 then
    [{lanes := 1, reads := [], code := [⟨.scalar (.const op.identity.toInt),[],0⟩], writes := [⟨dst,result,0⟩]}]
  else
    upsweep op tree src valid depth offset ++
      [{lanes := 1, reads := [⟨0,tree.up+depth,.lit 0⟩], code := [], writes := [⟨dst,result,0⟩]}]

/-- Pure seeded scan schedule, with the same compact rows as localScan. -/
def scanPhases (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst valid depth : Nat)
    (offset : Ix) (seed : Option (Nat × Ix)) : List Phase :=
  upsweep op tree src valid depth offset ++
    [seedPhase op (tree.down+depth) seed] ++
    ((List.range depth).reverse.map fun k =>
      downPhase op (2^(depth-k-1)) (tree.up+k) (tree.down+k+1) (tree.down+k)) ++
    [storeScanPhase op mode tree dst valid offset]

def localReduce (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk) : BuildM Unit := do
  for (valid, bucket) in buckets cs do
    emit bucket.length (reducePhases op tree src dst valid (tileDepth valid)
      (descriptor bucket (·.start)) (descriptor bucket (·.result)))

def localScan (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat) : BuildM Unit := do
  for (valid, bucket) in buckets cs do
    if valid > 0 then
      emit bucket.length (scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))))

/-- Finish every tile-sized descriptor now. Only longer segments produce
summary descriptors for the next level, so completed segments incur no repeated
work while an unrelated long segment shrinks. Result slots retain source order. -/
def reduceChunksInto (op : ReduceOp) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) : Nat → BuildM Unit
  | 0 => throw "collective reduction: insufficient hierarchy depth"
  | fuel+1 => do
    let small := cs.filter (·.length ≤ tile)
    let large := cs.filter (tile < ·.length)
    localReduce op tree src dst small
    if !large.isEmpty then
      let parts := splitChunks tile large
      let totals ← allocate parts.length
      localReduce op tree src totals parts
      reduceChunksInto op tree tile totals dst (summaryChunks tile large) fuel

/-- Reduce unfinished tiles, recursively scan their compact aggregates, then
reread each unfinished input tile with its prefix. Finished short segments leave
the hierarchy immediately. Dominant global traffic remains two reads/one write. -/
def scanChunksInto (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) : Nat → BuildM Unit
  | 0 => throw "collective scan: insufficient hierarchy depth"
  | fuel+1 => do
    let small := cs.filter (·.length ≤ tile)
    let large := cs.filter (tile < ·.length)
    localScan op mode tree src dst small none
    if !large.isEmpty then
      let parts := splitChunks tile large
      let totals ← allocate parts.length
      let prefixes ← allocate parts.length
      localReduce op tree src totals parts
      scanChunksInto op .exclusive tree tile totals prefixes (summaryChunks tile large) fuel
      localScan op mode tree src dst parts (some prefixes)

/-- Public segment lengths enter the single descriptor hierarchy. -/
def reduceInto (op : ReduceOp) (tree : Trees) (tile src dst : Nat) (ns : List Nat)
    (fuel : Nat) : BuildM Unit :=
  reduceChunksInto op tree tile src dst (segments ns) fuel

def scanInto (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (ns : List Nat) (fuel : Nat) : BuildM Unit :=
  scanChunksInto op mode tree tile src dst (segments ns) fuel

/-- Source construction only: admission still checks the resulting ArrayKernel.
The bounds on tile size describe supported tuning, not input-value hypotheses. -/
def build (op : ReduceOp) (shape : FoldShape) (tileLog : Nat := 8) : Except String Program := do
  unless 1 ≤ tileLog && tileLog ≤ 8 do throw "collective tileLog must be between 1 and 8"
  let ns := shape.segments
  let inputSize := shape.inputLen
  let outputSize := if shape.mode.isSome then inputSize else ns.length
  let action : BuildM Unit := do
    let src ← allocate inputSize
    let dst ← allocate outputSize
    let tree ← allocateTrees tileLog
    let fuel := Nat.log2 (max 1 inputSize)+2
    match shape.mode with
    | none => reduceInto op tree (2^tileLog) src dst ns fuel
    | some mode => scanInto op mode tree (2^tileLog) src dst ns fuel
  let (_,state) ← action.run {}
  return { buffers := state.buffers.toList, inputs := [0], outputs := [1], dispatches := state.dispatches.toList }

end Obend.Hardware.Gpu.CollectiveBlock
end
