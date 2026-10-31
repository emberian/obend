module
/-
# Obend.Core.Brand — the field a kind's identity is written in

A kind's stable identity is written on its record type as one field, `#kind`, whose member is the
one-label sum naming the kind (`Obend.Core.Nominal`). One label for every kind, so that an
extension constructing an instance of another kind overwrites it (the first field of a name wins);
the label is not a source identifier, so no source field can write it. This leaf holds only the
label and its reading, so the front end's proposal types (`Obend.Spec.Types`) and the data wire
share them without importing the checker.
-/
public import Lean
public section
namespace Obend.Core.Brand
set_option autoImplicit false

/-- A kind's stable identity: its declaring module and name (`Units.Mile`). -/
abbrev KindId := String

/-- The field a kind's identity is written in. -/
@[expose] def brandLabel : String := "#kind"

/-- Whether a field label is the brand. -/
@[expose] def isBrand (label : String) : Bool := label == brandLabel

end Obend.Core.Brand

end
