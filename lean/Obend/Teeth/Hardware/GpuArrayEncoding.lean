module
/- Runtime regression for the large literal/table admission path. This exercises
Core4 syntax encoding, scope checking, and structural equality on a 65536-element
balanced table; it is a test, not a universal compiler claim. -/
public meta import Obend.Hardware.Gpu.ArrayEncoding
public meta import Obend.Law.Claim
@[expose] public section
namespace Obend.Teeth.Hardware.GpuArrayEncoding
open Obend.Hardware.Gpu.ArraySource.Core

meta def checkLargeEncoding : Except String Unit := do
  let t := encodeNats (List.range 65536)
  unless Obend.Law.closedB t do throw "large literal function is not closed"
  unless Obend.Law.termEq t t do throw "large literal function differs from itself"

#eval match checkLargeEncoding with
  | .ok () => IO.println "Balanced 65536-element Core4 literal: closure and structural equality passed"
  | .error e => throw (IO.userError e)

end Obend.Teeth.Hardware.GpuArrayEncoding
end
