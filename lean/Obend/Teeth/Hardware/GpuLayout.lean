/- Executable allocator regression tests, not theorem fixtures. -/
import Obend.Hardware.Gpu.LayoutChecks

#eval (do
  for (name, ok) in Obend.Hardware.Gpu.layoutCheckResults do
    match ok with
    | true => pure ()
    | false => throw (IO.userError s!"GPU layout regression: {name}")
  : IO Unit)
