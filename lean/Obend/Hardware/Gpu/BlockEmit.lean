module
public import Obend.Hardware.Gpu.BlockLower
public import Obend.Hardware.Gpu
@[expose] public section

/-!
# Workgroup source to WGSL

The source supplies indexing and arithmetic, including butterfly networks. This emitter
has no NTT operation or transform-specific shader. Every phase runs a bounded strided
loop over its logical lanes, then every physical lane reaches the same barriers.
Register programs use the same limb emitter as array graphs. Storage classes follow
WGSL §14.5: workgroupBarrier orders shared memory; storageBarrier orders device memory
within the workgroup. Inter-workgroup dependences require separate dispatches.
-/
namespace Obend.Hardware.Gpu.BlockEmit
open Obend.Hardware.ArrayKernel

def numbers (xs : List Nat) : String := String.intercalate "," (xs.map toString)

/-- Immutable descriptors are pooled in the uploaded u32 index buffer. -/
def ixTables : Ix → List (Array Nat)
  | .lit _ | .group | .lane => []
  | .add a b | .mul a b => ixTables a ++ ixTables b
  | .div a _ | .mod a _ => ixTables a
  | .lookup values i => values :: ixTables i

def indexTables (p : Program) : List (Array Nat) :=
  (p.dispatches.flatMap fun d => d.phases.flatMap fun ph =>
    (ph.reads.flatMap fun r => ixTables r.index) ++
    (ph.writes.flatMap fun w => ixTables w.index)).eraseDups

def tableBase (tables : List (Array Nat)) (values : Array Nat) : Nat :=
  ((tables.takeWhile (· != values)).map (·.size)).sum

def ixText (tables : List (Array Nat)) (indexBase : Nat) : Ix → String
  | .lit n => s!"{n}u"
  | .group => "group"
  | .lane => "lane"
  | .add a b => s!"({ixText tables indexBase a} + {ixText tables indexBase b})"
  | .mul a b => s!"({ixText tables indexBase a} * {ixText tables indexBase b})"
  | .div a n => s!"({ixText tables indexBase a} / {n}u)"
  | .mod a n => s!"({ixText tables indexBase a} % {n}u)"
  | .lookup values i => s!"ix[{indexBase + tableBase tables values}u + {ixText tables indexBase i}]"

/-- Prefix offsets only among buffers in the same address space. Shared buffers are
per-workgroup allocations, never part of the host's device allocation. -/
def bufferBases (p : Program) : List Nat := BlockLower.bufferBases p

def spaceSize (p : Program) (s : Storage) : Nat :=
  (p.buffers.filter fun b => b.storage == s).foldl (fun n b => n + b.size) 0

def accessText (p : Program) (indexBase a : Nat) (i : Ix) : String :=
  let space := match ((p.buffers.drop a).headD ⟨0, .device, []⟩).storage with
    | .device => "w"
    | .shared => "shared_words"
    | .constant => "c"
  s!"{space}[{(bufferBases p).getD a 0}u + {ixText (indexTables p) indexBase i}]"

def phaseText (plant : Plant) (p : Program) (indexBase : Nat) (ph : Phase) : List String :=
  [s!"  for (var lane = lid.x; lane < {ph.lanes}u; lane += {workgroupSize}u) \{"] ++
  (ph.reads.map fun r => s!"    let v{r.dst} = {accessText p indexBase r.array r.index};") ++
  (ph.code.map fun i => s!"    let v{i.dst} = {elemExpr plant i.op (i.args.map fun a => s!"v{a}")};") ++
  (ph.writes.map fun w => s!"    {accessText p indexBase w.array w.index} = v{w.value};") ++
  ["  }", "  workgroupBarrier();", "  storageBarrier();"]

def emitDispatch (plant : Plant) (name : String) (p : Program) (d : Dispatch) (indexBase : Nat := 0) : String :=
  String.intercalate "\n" <|
    [s!"// {name}: generated from ArrayKernel.Program; no transform-specific emission."
    , "@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;"
    , "@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;"
    , "@group(0) @binding(2) var<storage, read> ix : array<u32>;"
    , s!"var<workgroup> shared_words : array<vec2<u32>, {max 1 (spaceSize p .shared)}>;"
    , limbPrelude plant
    , s!"@compute @workgroup_size({workgroupSize})"
    , "fn main(@builtin(workgroup_id) wid : vec3<u32>, @builtin(local_invocation_id) lid : vec3<u32>) {"
    , s!"  let group = wid.x + wid.y * {if d.groups > 65535 then 32768 else max 1 d.groups}u;"
    , s!"  if (group >= {d.groups}u) \{ return; }"] ++
    d.phases.flatMap (phaseText plant p indexBase) ++ ["}", ""]

def traffic (p : Program) (d : Dispatch) (space : Storage) (write : Bool) : Nat :=
  d.groups * (d.phases.foldl (fun n ph => n + ph.lanes * 8 *
    (if write then
      (ph.writes.filter fun w => ((p.buffers.drop w.array).headD ⟨0, .device, []⟩).storage == space).length
    else (ph.reads.filter fun r => ((p.buffers.drop r.array).headD ⟨0, .device, []⟩).storage == space).length)) 0)

/-- The constant buffers' values in order: what the host binds as `c`. -/
def constWords (p : Program) : List ArrayHypergraph.Word :=
  (p.buffers.filterMap fun b => if b.storage == .constant then some b.values else none).flatten

def emitPlan (name : String) (p : Program) : String :=
  let consts := constWords p
  let stages := String.intercalate ",\n    " <| p.dispatches.zipIdx.map fun (d, i) =>
    s!"\{\"file\":\"stage_{i}.wgsl\",\"threads\":{d.groups * workgroupSize},\"logicalReadBytes\":{traffic p d .device false + traffic p d .constant false},\"logicalWriteBytes\":{traffic p d .device true},\"logicalWorkgroupReadBytes\":{traffic p d .shared false},\"logicalWorkgroupWriteBytes\":{traffic p d .shared true}}"
  String.intercalate "\n"
    [ "{"
    , s!"  \"graph\": \"{name}\","
    , s!"  \"words\": {spaceSize p .device},"
    , s!"  \"workgroupSize\": {workgroupSize},"
    , s!"  \"wireBase\": [{numbers (bufferBases p)}],"
    , s!"  \"wireLen\": [{numbers (p.buffers.map (·.size))}],"
    , s!"  \"consts\": [{String.intercalate "," (consts.map fun v => s!"\"{v.toInt}\"")}],"
    , s!"  \"tables\": [{numbers ((indexTables p).flatMap (·.toList))}],"
    , s!"  \"inputs\": [{numbers p.inputs}],"
    , s!"  \"outputs\": [{numbers p.outputs}],"
    , s!"  \"stages\": [\n    {stages}\n  ]"
    , "}", "" ]
end Obend.Hardware.Gpu.BlockEmit
