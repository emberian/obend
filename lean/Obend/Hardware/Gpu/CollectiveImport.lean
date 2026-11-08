module
public import Lean.Data.Json
public import Obend.Hardware.Gpu.CollectiveBlock
public import Obend.Hardware.Gpu.BlockEmit
public import Obend.Hardware.Gpu.SourceProtocol
@[expose] public section
namespace Obend.Hardware.Gpu.CollectiveImport
open Lean Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
set_option autoImplicit false

structure Spec where
  op : String
  mode : String
  segments : List Nat
  tileLog : Nat := 8
  deriving FromJson

def Spec.operation (s : Spec) : Except String ReduceOp :=
  match s.op with
  | "add" => .ok .add
  | "mul" => .ok .mul
  | "band" => .ok .band
  | "bor" => .ok .bor
  | _ => .error "collective: unsupported word monoid"

def Spec.shape (s : Spec) : Except String FoldShape :=
  match s.mode with
  | "reduce" => .ok (.segReduce s.segments)
  | "inclusive" => .ok (.segScan s.segments .inclusive)
  | "exclusive" => .ok (.segScan s.segments .exclusive)
  | _ => .error "collective: mode must be reduce, inclusive or exclusive"

def writeFile (spec out : System.FilePath) (plant : Plant := .none) : IO Unit := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile spec))
  let s : Spec ← IO.ofExcept (fromJson? j)
  let op ← IO.ofExcept s.operation
  let shape ← IO.ofExcept s.shape
  let p ← IO.ofExcept (CollectiveBlock.build op shape s.tileLog)
  let start ← IO.monoMsNow
  IO.println s!"collective {s.op}/{s.mode}: {shape.inputLen} inputs, {s.segments.length} segments, {p.dispatches.length} dispatches; admitting source"
  (← IO.getStdout).flush
  IO.ofExcept p.check
  IO.println s!"source admission: {(← IO.monoMsNow)-start} ms"
  (← IO.getStdout).flush
  unless SourceProtocol.checkProgram p workgroupSize do
    throw <| IO.userError "collective: source phase protocol rejected"
  IO.println s!"source and G4 admission: {(← IO.monoMsNow)-start} ms"
  IO.FS.createDirAll out
  let name := s!"collective-{s.op}-{s.mode}-{shape.inputLen}"
  IO.FS.writeFile (out / "plan.json") (BlockEmit.emitPlan name p)
  for (d,k) in p.dispatches.zipIdx do
    IO.FS.writeFile (out / s!"stage_{k}.wgsl") (BlockEmit.emitDispatch plant name p d)
  IO.println s!"emitted {p.dispatches.length} dispatches, {BlockEmit.spaceSize p .device} device words, {BlockEmit.spaceSize p .shared} shared words"

end Obend.Hardware.Gpu.CollectiveImport
end
