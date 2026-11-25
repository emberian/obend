module
import all Obend.Lower.Pancake.DragonStyleShard
import Obend.Tactic.Tooth

public section

open Obend.Lower.Pancake.DragonStyleShard

/-- Emit the exact scalar body used in the clock theorem for the native fixture. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected an output .pnk path")
  let some src := echoSource | throw (IO.userError "unprintable echo kernel")
  IO.FS.writeFile path src

#tooth bounded_ring_conservation by mutation publishPacket :=
  fun s _ rs _ ts m => {s with rxActive := rs, txFree := ts, memory := m}

#tooth echo_refinesClkTight by mutation copyByte := .skip
