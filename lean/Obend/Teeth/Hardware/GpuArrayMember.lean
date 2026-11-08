module
/- Executable admission/refusal teeth for actual array members. These are tests,
not specialized compiler theorem statements. Device tests exercise the same path. -/
public meta import Obend.Hardware.Gpu.ArrayPrograms
@[expose] public section
namespace Obend.Teeth.Hardware.GpuArrayMember
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu
open Obend.Hardware.Gpu.ArraySource Obend.Hardware.Gpu.ArrayPrograms

meta def pipeline : Program :=
  .letE (.map 4 (.scalar .add) [0, 0])
    (.letE (.gather ⟨4, 4, [3, 2, 1, 0]⟩ 0)
      (.letE (.fold .add (.reduce 4) 0) (.ret [0, 1])))

meta def rejected {α : Type} (name : String) (result : Except String α) : Except String Unit :=
  match result with
  | .error _ => .ok ()
  | .ok _ => .error s!"array member accepted {name}"

meta def check : Except String Unit := do
  let p ← compileSource "ArrayPipeline" [4] pipeline
  let env := mkEnv p.graph.lengths p.graph.inputs [[1#64, 2#64, 3#64, 4#64]]
  let store := (Array.range p.graph.lengths.length).map fun w => (env w).toArray
  unless evalGraphArr p.graph store == [[20#64], [8#64, 6#64, 4#64, 2#64]] do
    throw "source array pipeline differs from independent expected values"
  let field ← glMulSource 4
  let fieldPlan ← compileSource "SharedGoldilocks" [4,4] field
  let prime := GoldilocksSource.goldilocksP
  let left : Vec := [0#64,1#64,BitVec.ofNat 64 (prime-1),BitVec.allOnes 64]
  let right : Vec := [5#64,BitVec.ofNat 64 (prime-1),BitVec.ofNat 64 (prime-1),BitVec.allOnes 64]
  let fieldEnv := mkEnv fieldPlan.graph.lengths fieldPlan.graph.inputs [left,right]
  let fieldStore := (Array.range fieldPlan.graph.lengths.length).map fun w => (fieldEnv w).toArray
  let expected := (left.zip right).map fun (a,b) => BitVec.ofNat 64 (a.toNat*b.toNat % prime)
  unless evalGraphArr fieldPlan.graph fieldStore == [expected] do
    throw "reified shared field source differs from exact natural modular multiplication"
  rejected "reifier input extent mismatch" (ArrayReify.reify [3] p.graph)
  let overwritten := { p.graph with edges := p.graph.edges.map fun e => {e with dstWire := 0} }
  rejected "reifier overwritten input" (ArrayReify.reify [4] overwritten)
  rejected "different candidate body" (ArrayMember.checkMember
    (memberComposition "ArrayPipeline" [4] pipeline) "run" (.ret [0]) [4])
  rejected "out-of-scope variable" (compileSource "Scope" [4] (.ret [1]))
  rejected "map shape mismatch" (compileSource "Shape" [4]
    (.letE (.map 2 (.scalar .add) [0, 0]) (.ret [0])))
  rejected "malformed gather table" (compileSource "Gather" [4]
    (.letE (.gather ⟨4, 4, [0, 1]⟩ 0) (.ret [0])))
  rejected "fold input extent mismatch" (compileSource "Fold" [4]
    (.letE (.fold .add (.scan 3 .inclusive) 0) (.ret [0])))

#eval match check with
  | .ok () => IO.println "Array source member admission, syntax/scope/shape refusals and outputs: passed"
  | .error e => throw (IO.userError e)

end Obend.Teeth.Hardware.GpuArrayMember
end
