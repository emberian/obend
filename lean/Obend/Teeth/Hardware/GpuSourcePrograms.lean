module
/- Executable admission and independent-output checks for the source frontend.
These are tests, not propositions advertised as compiler theorems. The device gate
runs these same source cases through emitted shader artifacts. -/
public meta import Obend.Hardware.Gpu.SourcePrograms
@[expose] public section
namespace Obend.Teeth.Hardware.GpuSourcePrograms
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu
open Obend.Hardware.Gpu.SourcePrograms

meta def check : Except String Unit := do
  checkRefusals
  for c in cases do
    let p ← c.compile
    unless p.plan.graph.wf do throw s!"{c.name}: graph is ill-formed"
    for xs in c.vectors do
      let env := mkEnv p.plan.graph.lengths p.plan.graph.inputs [xs]
      let store := (Array.range p.plan.graph.lengths.length).map fun w => (env w).toArray
      let actual := evalGraphArr p.plan.graph store
      unless checkSourceExpected c.name [xs] actual do
        throw s!"{c.name}: graph differs from independent scalar reference"

#eval match check with
  | .ok () => IO.println "Source member admission/refusal and independent outputs: passed"
  | .error e => throw (IO.userError e)

end Obend.Teeth.Hardware.GpuSourcePrograms
end
