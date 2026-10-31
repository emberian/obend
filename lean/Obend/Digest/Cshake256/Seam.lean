module
/-
# Obend.Digest.Cshake256.Seam -- the cSHAKE256 kernel seam, standalone: Lean body only (obend copy; minidregg attaches a Rust kernel here by @[extern])

`cshake256Bytes` (`Sp800185Cshake256Spec`) is the definition every theorem is about;
`cshake256Fast` (`Sp800185Cshake256Fast`) is the word-and-byte-array implementation proved
equal to it (`cshake256Fast_eq`). This module adds the third layer: `cshake256Kernel`, whose
Lean body IS the fast path on byte arrays and whose compiled code is the Rust kernel
`mini_cshake256_32` (`native/mini-kernels`, `@[extern]`). Lean states what the kernel computes;
the Rust is the implementation; the equality of the two is NOT a theorem here. It is pinned by
(1) the Lean-authored vectors `native/mini-kernels/testdata/lean-vectors.json` run by
`cargo test -p mini-kernels --test conformance`, and (2) the tree's own conformance theorems
(`Theory.Sp800185Cshake256Conformance`, `Compiler.Sp800185Kmac256`): `native_decide` evaluates
the compiled path, which after `cshake256Bytes_eq_native` is the kernel, so every build of
those modules is a KAT of the kernel against NIST sample 3 and SHAKE256("").

What IS proved: `cshake256Native_eq`, the Lean body of the seam equals the specification for
every input, so the csimp attachment below is sound with respect to the Lean body, and the only
trusted step is "the Rust computes the Lean body" (the kernel's conformance). The kernel decides
nothing: it maps bytes to 32 bytes; every comparison, domain and admission stays in Lean.

Build consequence: compiled code (and `#eval`/`native_decide` at elaboration) needs the symbol.
`scripts/build-mini-kernels.sh` builds `.lake/native/libmini_kernels.a` + the shim object (link
inputs of every Lean executable) and `.lake/native/libmini_kernels_lean.so` (loaded into `lean`
by the lakefile's `--load-dynlib`). Run it before `lake build`.
-/
public import Obend.Digest.Cshake256.Fast
@[expose] public section

namespace Obend.Digest.Cshake256

set_option autoImplicit false

namespace Native

open Fast

/-- A byte array of a list, through the builder the fast path is proved against. -/
def bytesOfList (bytes : List UInt8) : ByteArray := pushList ByteArray.empty bytes

theorem bytesOfList_toList (bytes : List UInt8) : (bytesOfList bytes).data.toList = bytes := by
  rw [bytesOfList, pushList_data, empty_data, List.nil_append]

/-- **The kernel seam.** cSHAKE256 with an empty function name and a 32-byte output on byte
arrays. The Lean body is the proved fast path; the compiled code is `mini_cshake256_32`
(`native/mini-kernels/shim/mini_kernels_lean.c` -> `mini_kernels_cshake256_32`). Both arguments
are borrowed. -/
-- obend standalone (2026-10-29): no Rust kernel; the compiled code IS the Lean fast path.
def cshake256Kernel (customization input : @& ByteArray) : ByteArray :=
  bytesOfList (cshake256Fast customization.data.toList input.data.toList)

/-- The spec's shape (lists in, list out) over the kernel: what the compiled `cshake256Bytes`
runs (`cshake256Bytes_eq_native`). -/
def cshake256Native (customization input : List UInt8) : List UInt8 :=
  (cshake256Kernel (bytesOfList customization) (bytesOfList input)).data.toList

/-- **The seam's Lean body is the specification**, for every customization and input. -/
theorem cshake256Native_eq (customization input : List UInt8) :
    cshake256Native customization input = cshake256Bytes customization input := by
  unfold cshake256Native cshake256Kernel
  rw [bytesOfList_toList, bytesOfList_toList, bytesOfList_toList, cshake256Fast_eq]

end Native

/-- The compiled cSHAKE256 is the kernel seam (replacing `cshake256Bytes_eq_fast`, which stays
a theorem: the fast path is the seam's Lean body and the vectors' generator). -/
@[csimp] theorem cshake256Bytes_eq_native : cshake256Bytes = Native.cshake256Native := by
  funext customization input
  exact (Native.cshake256Native_eq customization input).symm

end Obend.Digest.Cshake256

end