module
public import Obend.Hardware.Gpu.CollectiveBlock
public import Obend.Hardware.Gpu.BlockEmit
public import Obend.Hardware.Gpu.SourceProtocol
public import Obend.Hardware.Gpu.ArraySchedule
@[expose] public section

/-! One emission route for array programs. Ordinary map/routing stages keep their
checked live layout. Every fold is scheduled as ArrayKernel collectives. Temporary
summaries occupy an arena after the graph's live allocation and are reused between
collectives. Holes preserve other live wires: canonical block prefix allocation
places input/output arrays at precisely their existing physical ranges.
-/
namespace Obend.Hardware.Gpu.ArrayEmit
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayKernel
set_option autoImplicit false

/-- Reindex the two boundary arrays; all other buffers keep their relative order. -/
def arenaIndex (inputFirst : Bool) (a : Nat) : Nat :=
  if a == 0 then (if inputFirst then 1 else 3)
  else if a == 1 then (if inputFirst then 3 else 1)
  else a+3

def renamePhase (f : Nat → Nat) (ph : Phase) : Phase :=
  { ph with reads := ph.reads.map fun r => {r with array := f r.array}
            writes := ph.writes.map fun w => {w with array := f w.array} }

/-- Embed a block collective's input/output in disjoint live graph ranges.
Unused padding buffers are never accessed. No custom physical-address emitter or
unchecked aliasing is introduced: BlockLower's prefix-address proof still applies. -/
def inArena (p : Program) (words src dst : Nat) : Except String Program := do
  unless p.inputs == [0] && p.outputs == [1] && p.buffers.length ≥ 2 do
    throw "collective arena: expected two boundary buffers"
  let a := p.buffers.getD 0 default
  let b := p.buffers.getD 1 default
  unless a.storage == .device && b.storage == .device &&
      src+a.size ≤ words && dst+b.size ≤ words do
    throw "collective arena: boundary outside graph storage"
  let inputFirst := src+a.size ≤ dst
  unless inputFirst || dst+b.size ≤ src do
    throw "collective arena: source/output ranges alias"
  let lo := if inputFirst then src else dst
  let hi := if inputFirst then dst else src
  let first := if inputFirst then a else b
  let second := if inputFirst then b else a
  let hole (n : Nat) : Buffer := ⟨n,.device,[]⟩
  let f := arenaIndex inputFirst
  return { buffers := [hole lo,first,hole (hi-lo-first.size),second,hole (words-hi-second.size)] ++ p.buffers.drop 2
           inputs := p.inputs.map f
           outputs := p.outputs.map f
           dispatches := p.dispatches.map fun d => {d with phases := d.phases.map (renamePhase f)} }

structure Shader where
  threads : Nat
  text : String

structure Artifact where
  words : Nat
  tables : List Nat
  shaders : Array Shader

/-- Executable schedule before text emission. The graph stage number is diagnostic;
collectives retain their admitted block program, not only generated shader text. -/
inductive Action where
  | elementwise (stage : Nat) (kernels : GpuStage)
  | collective (program : Program)

def Action.eval (c : List Word) (ix : List Nat) (action : Action)
    (flat : BlockLower.FlatMemory) : BlockLower.FlatMemory :=
  match action with
  | .elementwise _ stage => fun address =>
      if address.1 == .device then runStage c ix (fun i => flat (.device,i)) stage address.2
      else flat address
  | .collective p => BlockLower.lowerProgram p flat

def evalActions (p : GpuProgram) (actions : List Action)
    (flat : BlockLower.FlatMemory) : BlockLower.FlatMemory :=
  actions.foldl (fun m a => a.eval p.consts p.tables m) flat

structure Schedule where
  words : Nat
  actions : Array Action

/-- Only fold kernels expand here; ordinary kernels remain in their one frontier
action. Both source and renamed programs are structurally admitted. The source
check is also the premise used by the universal collective/arena simulation. -/
def compileKernel (p : GpuProgram) (kern : Kernel) : Except String (List Action) := do
  match kern.body with
  | .fold op shape src =>
    unless kern.count == shape.outLen do throw "collective output shape differs from kernel"
    let source ← CollectiveBlock.build op shape
    let _ ← source.check
    let block ← inArena source p.words src kern.dstBase
    let _ ← block.check
    unless SourceProtocol.checkProgram block workgroupSize do
      throw "array collective: phase protocol rejected"
    return [.collective block]
  | _ => return []

def ordinaryActions (stage : GpuStage) (index : Nat) : List Action :=
  let ordinary := stage.kernels.filter ArraySchedule.ordinary
  if ordinary.isEmpty then [] else [.elementwise index ⟨ordinary⟩]

/-- Expand a frontier in precisely its emitted order: the ordinary snapshot,
then folds in source order. Interval checks justify both serialization and use
of temporary storage beyond the graph's original live allocation. -/
def compileStage (p : GpuProgram) (stage : GpuStage) (index : Nat) : Except String (List Action) := do
  unless ArraySchedule.checkStage p.tables stage do
    throw "array frontier: serialized collective ranges interfere"
  unless ArraySchedule.checkBounds p.words p.tables stage do
    throw "array frontier: kernel range outside live allocation"
  let folds ← stage.kernels.mapM (compileKernel p)
  return ordinaryActions stage index ++ folds.flatten

def compileStages (p : GpuProgram) (stages : List (GpuStage × Nat)) : Except String (List Action) := do
  let actions ← stages.mapM fun (stage,index) => compileStage p stage index
  return actions.flatten

def requiredWords (p : GpuProgram) (actions : List Action) : Nat :=
  actions.foldl (fun words action => match action with
    | .elementwise _ _ => words
    | .collective block => max words (BlockEmit.spaceSize block .device)) p.words

/-- Boundary identifiers must exist even when their vectors are empty. Every
boundary's declared interval lies in the original graph allocation. -/
def checkBoundaries (p : GpuProgram) : Bool :=
  (p.inputs ++ p.outputs).all fun w =>
    w < p.wireBase.length && w < p.wireLen.length &&
      p.wireBase.getD w 0 + p.wireLen.getD w 0 ≤ p.words

def compile (p : GpuProgram) : Except String Schedule := do
  unless checkBoundaries p do throw "array boundary: unknown wire or range outside live allocation"
  let actions ← compileStages p p.stages.zipIdx
  return ⟨requiredWords p actions,actions.toArray⟩

/-- Text generation consumes precisely the expanded semantic action list. -/
def schedule (name : String) (p : GpuProgram) (plant : Plant := .none) : Except String Artifact := do
  let compiled ← compile p
  let mut tables := p.tables
  let mut shaders : Array Shader := #[]
  for action in compiled.actions do
    match action with
    | .elementwise k s =>
      shaders := shaders.push ⟨s.threads,emitStageWgsl plant name k p.stages.length s⟩
    | .collective block =>
      let indexBase := tables.length
      tables := tables ++ (BlockEmit.indexTables block).flatMap (·.toList)
      for d in block.dispatches do
        shaders := shaders.push ⟨d.groups*workgroupSize,
          BlockEmit.emitDispatch plant name block d indexBase⟩
  return ⟨compiled.words,tables,shaders⟩

def planJson (name : String) (p : GpuProgram) (a : Artifact) : String :=
  let nums (xs : List Nat) := String.intercalate "," (xs.map toString)
  let consts := String.intercalate "," (p.consts.map fun v => s!"\"{v.toInt}\"")
  let stages := String.intercalate ",\n    " (a.shaders.toList.zipIdx.map fun (s,i) =>
    s!"\{\"file\":\"stage_{i}.wgsl\",\"threads\":{s.threads}}")
  String.intercalate "\n"
    [ "{", s!"  \"graph\": \"{name}\",", s!"  \"words\": {a.words},"
    , s!"  \"workgroupSize\": {workgroupSize},", s!"  \"wireBase\": [{nums p.wireBase}],"
    , s!"  \"wireLen\": [{nums p.wireLen}],", s!"  \"consts\": [{consts}],"
    , s!"  \"tables\": [{nums a.tables}],", s!"  \"inputs\": [{nums p.inputs}],"
    , s!"  \"outputs\": [{nums p.outputs}],", s!"  \"stages\": [\n    {stages}\n  ]", "}", "" ]

def write (name : String) (p : GpuProgram) (out : System.FilePath)
    (plant : Plant := .none) : IO Artifact := do
  let a ← IO.ofExcept (schedule name p plant)
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "plan.json") (planJson name p a)
  for (s,k) in a.shaders.toList.zipIdx do
    IO.FS.writeFile (out / s!"stage_{k}.wgsl") s.text
  return a

end Obend.Hardware.Gpu.ArrayEmit
end
