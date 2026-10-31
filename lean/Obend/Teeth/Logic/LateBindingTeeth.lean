module
/- The teeth of T1 `late_binding` (`Obend.Logic.LateBinding`).

A later provider moves the index: with `providesLast` mutated to name the *innermost* (earliest)
provider instead of the outermost, the stored proof of `late_binding` no longer checks, because
`extendFields` puts the later layer's field first and `Step.field` meets it. And concretely, in a
composition where both layers provide `m`, the unfolding is the outer layer's. -/
public import Obend.Tactic.Tooth
import all Obend.Logic.LateBinding
open Obend.Logic

/-- The earliest provider, as a stale certificate would name it. -/
def innermostProvider : List Layer → String → Option Nat
  | [], _ => none
  | L :: rest, m => match innermostProvider rest m with
    | some j => some (j + 1)
    | none => if L.provides m then some 0 else none

#tooth Obend.Logic.late_binding by mutation Obend.Logic.providesLast := innermostProvider

def provider (name : String) : Layer := { name, metadata := .label name, fields := [("m", .nat 0)] }

/-- In `compose(Inner, Outer)` with both providing `m`, the outer layer (index 0) is the provider,
and the stale index 1 is what the mutation would name. -/
example : providesLast [provider "Outer", provider "Inner"] "m" = some 0 ∧
    innermostProvider [provider "Outer", provider "Inner"] "m" = some 1 := by
  simp [providesLast, innermostProvider, Layer.provides, provider]
