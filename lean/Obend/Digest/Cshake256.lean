module
/-
# Obend.Digest.Cshake256 -- cSHAKE256: the specification and its compiled path

Import this module.  It is `Sp800185Cshake256Spec`, the list/`BitVec`
definitions that every theorem in the repository is about, together with
`Sp800185Cshake256Fast`, the word and byte-array implementation proved equal
to them for every input (`cshake256Fast_eq`, `absorbPadded_fast_eq`) and
and `Sp800185Cshake256Native`, the kernel seam whose Lean body is that fast path and
whose compiled code is the Rust kernel (`@[csimp]` `cshake256Bytes_eq_native`).  Every
module compiled with this import in scope calls the kernel where the source says
`cshake256Bytes`, and the fast word code where it says `absorbPadded`.
A module importing only the spec would compile against the list definitions:
correct, and about three orders of magnitude slower.
-/

public import Obend.Digest.Cshake256.Spec
public import Obend.Digest.Cshake256.Fast
public import Obend.Digest.Cshake256.Seam
@[expose] public section

end