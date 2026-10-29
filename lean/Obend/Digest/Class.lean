module
/-
# Obend.Digest.Class — the digest a world binds with, as a typeclass

`Digest` is one family of hashes indexed by a customization string, the shape every consumer in
this library asks for (`Obend.Core.Digest.deployed` is `Digest.hash customization`). It carries no
law: the theorems that matter about a hash (`binds_or_collides`, `Collision`) are stated in
`Obend.Core.Digest` over an explicit `Hash` argument, and the class only names which hash the
deployed primitive runs. The one instance here is the proved cSHAKE256 (`Obend.Digest.Cshake256`,
Lean body only). A host that attaches a native kernel (minidregg's Rust `mini_cshake256_32`) does
so by a `@[csimp]` on `cshake256Bytes`, as before, and keeps this instance.
-/
public import Obend.Digest.HashBytes
public import Obend.Digest.Cshake256

@[expose] public section
namespace Obend.Digest

/-- A family of hashes over bytes, one per customization string. 32 output bytes is the
cSHAKE instance's property, not a field: a consumer that needs it proves it of the instance it uses. -/
class Digest where
  hash : (customization : List UInt8) → HashBytes.Hash

/-- The deployed family: cSHAKE256 with an empty function name, 32 bytes out. -/
instance cshake : Digest := ⟨Cshake256.cshake256Bytes⟩

theorem cshake_hash (customization input : List UInt8) :
    Digest.hash customization input = Cshake256.cshake256Bytes customization input := rfl

end Obend.Digest
end
