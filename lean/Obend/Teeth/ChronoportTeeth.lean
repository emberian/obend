module
import all Obend.Category.Chronoport
import Obend.Tactic.Tooth

/-! Mutations distinguish two boundaries of the successful Rust transition:
the target tick precedes the first scheduled event, and an already stored
event wins a departure-tick tie. -/
open Obend.Category.Chronoport

#tooth observe_arrival by mutation arrival := fun timeline source target =>
  ⟨target, .prebirth, (timeline.history source).latest.payload⟩

#tooth readAt_insert by mutation overlay := fun q marker old =>
  if marker.tick ≤ q then
    match old with
    | none => some marker
    | some previous => if marker.tick < previous.tick then some previous else some marker
  else old
