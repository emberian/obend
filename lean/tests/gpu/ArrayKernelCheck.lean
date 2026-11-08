import Obend.Hardware.ArrayKernel

open Obend.Hardware.ArrayKernel

/- Executable negative tests of the source admission gate, not theorems. -/
def copyPhase : Phase :=
  { lanes := 4, reads := [⟨0, 0, .lane⟩], code := [], writes := [⟨1, .lane, 0⟩] }

def copyProgram : Program :=
  { buffers := [⟨4, .device, []⟩, ⟨4, .device, []⟩, ⟨4, .shared, []⟩]
    inputs := [0], outputs := [1], dispatches := [⟨1, [copyPhase]⟩] }

def withPhase (ph : Phase) : Program := { copyProgram with dispatches := [⟨1, [ph]⟩] }

def accepted (name : String) (p : Program) : IO Unit := do
  match p.check with
  | .ok () => IO.println s!"PASS {name}"
  | .error e => throw (IO.userError s!"{name}: unexpectedly rejected: {e}")

def rejected (name : String) (p : Program) : IO Unit := do
  match p.check with
  | .ok () => throw (IO.userError s!"{name}: mutation was accepted")
  | .error e => IO.println s!"PASS {name}: {e}"

def main : IO Unit := do
  accepted "parallel copy" copyProgram
  let upload := { copyPhase with writes := [⟨2, .lane, 0⟩] }
  let download := { copyPhase with reads := [⟨0, 2, .lane⟩] }
  accepted "initialized shared exchange"
    { copyProgram with dispatches := [⟨1, [upload, download]⟩] }
  rejected "duplicate output address" (withPhase { copyPhase with writes := [⟨1, .lit 0, 0⟩] })
  rejected "read/write alias" (withPhase { copyPhase with reads := [⟨0, 1, .lane⟩] })
  rejected "uninitialized shared read" (withPhase download)
  rejected "cross-workgroup collision" { copyProgram with dispatches := [⟨2, [copyPhase]⟩] }
  rejected "out of bounds" (withPhase { copyPhase with writes := [⟨1, .add .lane (.lit 1), 0⟩] })
  rejected "overflow hidden by modulo" (withPhase
    { copyPhase with reads := [⟨0, 0, .mod (.mul (.lit 65536) (.lit 65536)) 4⟩] })
  rejected "division by zero" (withPhase { copyPhase with reads := [⟨0, 0, .div .lane 0⟩] })
  rejected "undefined register" (withPhase { copyPhase with writes := [⟨1, .lane, 77⟩] })
  rejected "flat address overflow" { copyProgram with
    buffers := [⟨2^32-1, .device, []⟩, ⟨2, .device, []⟩]
    dispatches := [⟨1, [{ copyPhase with
      lanes := 1
      reads := [⟨0, 1, .lit 1⟩]
      writes := [] }]⟩] }
  rejected "dispatch thread count overflow"
    { copyProgram with dispatches := [⟨2^26, [copyPhase]⟩] }
  rejected "lane induction overflow" (withPhase { copyPhase with lanes := 2^32-63 })
  rejected "inactive read literal overflow" (withPhase
    { copyPhase with lanes := 0, reads := [⟨0, 0, .lit (2^32)⟩] })
  rejected "inactive write literal overflow" (withPhase
    { copyPhase with lanes := 0, writes := [⟨1, .lit (2^32), 0⟩] })
  rejected "zero-group division by zero"
    { copyProgram with dispatches := [⟨0,
      [{ copyPhase with reads := [⟨0, 0, .div .lane 0⟩] }]⟩] }
  rejected "inactive divisor literal overflow" (withPhase
    { copyPhase with lanes := 0, reads := [⟨0, 0, .mod .lane (2^32)⟩] })

#eval main
