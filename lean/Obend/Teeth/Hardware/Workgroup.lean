/-
Executable tests for the source array language's G4 phase certificate. These are tests,
not instance theorems standing in for the universal results in `Gpu.Workgroup`.
-/
import Obend.Hardware.Gpu.Workgroup

namespace Obend.Teeth.Hardware.Workgroup
open Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Memory
open Obend.Hardware.Gpu.Workgroup

def loadPhase : Obend.Hardware.ArrayKernel.Phase :=
  { lanes := 2
    reads := [{ dst := 0, array := 0, index := .lane }]
    code := []
    writes := [{ array := 1, index := .lane, value := 0 }] }

def reversePhase : Obend.Hardware.ArrayKernel.Phase :=
  { lanes := 2
    reads := [{ dst := 0, array := 1, index := .mod (.add .lane (.lit 1)) 2 }]
    code := []
    writes := [{ array := 2, index := .lane, value := 0 }] }

def program : Program :=
  { buffers := [{ size := 2, storage := .device }, { size := 2, storage := .shared },
        { size := 2, storage := .device }]
    inputs := [0], outputs := [2]
    dispatches := [{ groups := 1, phases := [loadPhase, reversePhase] }] }

def dispatch : Dispatch := { groups := 1, phases := [loadPhase, reversePhase] }
def memory : Obend.Hardware.ArrayKernel.Memory := #[#[7#64, 11#64], #[0#64, 0#64], #[0#64, 0#64]]
def shape : Shape := sourceTrace program dispatch memory 0 2
def metadata : PhaseLayout := sourceLayout program dispatch memory 0 2

def dropWorkgroupScope (p : Shape) : Shape :=
  { p with threads := p.threads.map fun t => { t with prog := t.prog.map fun e =>
      match e with
      | .barrier i [.workgroup] => .barrier i []
      | _ => e } }

def duplicateWriter : Program :=
  { program with dispatches := [{ groups := 1, phases :=
      [{ loadPhase with writes := [{ array := 1, index := .lit 0, value := 0 }] }, reversePhase] }] }

#eval show IO Unit from do
  unless program.check.isOk do throw (IO.userError "source program should pass admission")
  unless metadata.geometryFast shape do throw (IO.userError "extracted phase geometry rejected")
  if metadata.geometryFast (dropWorkgroupScope shape) then
    throw (IO.userError "missing workgroup memory semantics escaped geometry check")
  unless metadata.latest shape 12 1 do throw (IO.userError "shared read lost its prior-phase writer")
  if duplicateWriter.check.isOk then throw (IO.userError "duplicate scatter escaped admission")
  let result := evalGroup dispatch 0 memory
  unless result.getD 2 #[] == #[11#64, 7#64] do
    throw (IO.userError "source shared reverse gather differs from sequential semantics")
  IO.println "workgroup source trace, phase geometry, reaching definition, and mutations passed"

end Obend.Teeth.Hardware.Workgroup
