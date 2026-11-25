import Obend.Lower.Pancake.DurableTurn

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a .pnk output path")
  let some src := Obend.Lower.Pancake.DurableTurn.source | throw (IO.userError "unprintable program")
  IO.FS.writeFile path src
