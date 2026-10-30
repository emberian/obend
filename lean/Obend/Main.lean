module
/-
# `obend` — check and run typed-core packets (SHIP §1; the executable is rooted here, at `Obend.Main`)

    lake exe obend check FILE.json
        the typing receipt on stdout (exit 0), or the refusal with the kind of rule it broke on
        stderr (exit 2): `Obend.Core.Packet.checkPacketFile`.
    lake exe obend run FILE.json [--ticks N] [--heap N] [--stack N]
        checks the packet, refuses an open program (a non-empty context), then runs the term on the
        demand machine (`Obend.Core.Machine.runBounded`; compiled code takes the `MachineFast` path)
        within the limits (defaults 100000 ticks, 65536 heap cells, 4096 frames), and prints the
        outcome as JSON: finished with the value, suspended (ticks or capacity), divergent at an
        address, refused by name, or yielded a plan. Exit 0 on finished, 3 otherwise, 2 on refusal.

A packet is `dregg.objective-bend.typed-core.v3` JSON, the edition `Obend.Core.Packet` decodes.
-/
public import Obend.Core.Packet
public import Obend.Core.Machine
public import Obend.Core.MachineFast

open Lean (Json toJson)
open Obend.Core

def usage : String :=
  "usage: obend check FILE.json | obend run FILE.json [--ticks N] [--heap N] [--stack N]"

structure RunOptions where
  ticks : Nat := 100000
  heap : Nat := 65536
  stack : Nat := 4096

def parseOptions : List String → RunOptions → Except String RunOptions
  | [], options => .ok options
  | flag :: value :: rest, options =>
    match value.toNat? with
    | none => .error s!"{flag} needs a number, got {value}"
    | some n =>
      match flag with
      | "--ticks" => parseOptions rest { options with ticks := n }
      | "--heap" => parseOptions rest { options with heap := n }
      | "--stack" => parseOptions rest { options with stack := n }
      | _ => .error s!"unknown option {flag}"
  | [flag], _ => .error s!"{flag} needs a value"

def valueJson : Machine.RuntimeValue → Json
  | .natural n => toJson n
  | .boolean b => toJson b
  | .label s => toJson s
  | other => toJson (toString (repr other))

def receipt (status : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("schema", toJson "dregg.objective-bend.run-receipt.v1"), ("status", toJson status)] ++ fields)

def refuse (stage message : String) : IO UInt32 := do
  IO.eprintln (receipt "refused" [("stage", toJson stage), ("message", toJson message)]).compress
  return 2

def runPacket (path : String) (options : RunOptions) : IO UInt32 := do
  let input ← IO.FS.readFile path
  match Json.parse input >>= Packet.decodePacket with
  | .error message => refuse "decode" message
  | .ok packet =>
    if packet.context ≠ [] then
      refuse "closed" "run needs a closed program: the packet's context is not empty"
    else
      match Check.check packet.source packet.context packet.fuel with
      | none => refuse "objective-source-type-check" (Packet.refusalReason packet)
      | some checked =>
        let limits : Machine.Limits := ⟨options.heap, options.stack⟩
        let outcome := Machine.runBounded limits options.ticks (Machine.initial packet.source.term)
        let (status, detail) : String × List (String × Json) :=
          match outcome with
          | .finished value _ => ("finished", [("value", valueJson value)])
          | .suspended .ticks _ => ("suspended", [("reason", toJson "ticks")])
          | .suspended .capacity _ => ("suspended", [("reason", toJson "capacity")])
          | .divergent address _ => ("divergent", [("address", toJson address)])
          | .refused reason _ => ("refused", [("reason", toJson (toString (repr reason)))])
          | .yielded plan _ => ("yielded", [("plan", toJson plan)])
        IO.println (receipt status ([("type", Packet.typeJson checked.type), ("ticks", toJson options.ticks)] ++ detail)).compress
        return (if status == "finished" then 0 else 3)

public def main (args : List String) : IO UInt32 :=
  match args with
  | ["check", path] => Packet.checkPacketFile path
  | "run" :: path :: rest =>
    match parseOptions rest {} with
    | .ok options => runPacket path options
    | .error message => do IO.eprintln message; return 1
  | _ => do IO.eprintln usage; return 1
