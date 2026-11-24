module
/-
# Obend.Digest.Cshake256.Seam -- the zero-copy ByteArray cSHAKE256 kernel seam

`cshake256Bytes` (`Obend.Digest.Cshake256.Spec`) is the list-based specification every theorem is
about; `cshake256ByteArrayFast` (`Obend.Digest.Cshake256.Fast`) is the zero-copy word-and-`ByteArray`
implementation proved equal to it (`cshake256ByteArrayFast_eq`). This module exposes `cshake256Kernel`,
wired directly to `cshake256ByteArrayFast` without allocating intermediate `List UInt8`s, together
with `cshake256Native_eq` and `@[csimp] theorem cshake256Bytes_eq_native`.
-/
public import Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Spec
import Obend.Tactic.Tooth
public section

namespace Obend.Digest.Cshake256

set_option autoImplicit false

namespace Native

open Fast

/-- A byte array of a list, through the builder the fast path is proved against. -/
@[expose] def bytesOfList (bytes : List UInt8) : ByteArray := pushList ByteArray.empty bytes

theorem bytesOfList_toList (bytes : List UInt8) : (bytesOfList bytes).data.toList = bytes := by
  rw [bytesOfList, pushList_data, empty_data, List.nil_append]

/-- **The kernel seam.** Zero-copy cSHAKE256 (empty function name, 32-byte output) operating
directly on borrowed `ByteArray` slices via `cshake256ByteArrayFast`. -/
@[expose] def cshake256Kernel (customization input : @& ByteArray) : ByteArray :=
  cshake256ByteArrayFast customization input

@[simp] theorem cshake256Kernel_size (customization input : ByteArray) :
    (cshake256Kernel customization input).size = 32 := by
  simp [cshake256Kernel]

theorem cshake256Kernel_toList (customization input : ByteArray) :
    (cshake256Kernel customization input).data.toList =
      cshake256Bytes customization.data.toList input.data.toList :=
  cshake256ByteArrayFast_eq customization input

/-- The spec's shape (lists in, list out) over the kernel: what the compiled `cshake256Bytes`
runs (`cshake256Bytes_eq_native`). -/
@[expose] def cshake256Native (customization input : List UInt8) : List UInt8 :=
  (cshake256Kernel (bytesOfList customization) (bytesOfList input)).data.toList

/-- **The seam's Lean body is the specification**, for every customization and input. -/
theorem cshake256Native_eq (customization input : List UInt8) :
    cshake256Native customization input = cshake256Bytes customization input := by
  unfold cshake256Native cshake256Kernel
  rw [cshake256ByteArrayFast_eq, bytesOfList_toList, bytesOfList_toList]

end Native

/-- Pure-Lean `ByteArray` execution wrapper for `namedBytes` (`Fast.namedByteArrayFast`, not C FFI). -/
def namedBytesFast (name custom input : List UInt8) : List UInt8 :=
  (Fast.namedByteArrayFast
    (Native.bytesOfList name) (Native.bytesOfList custom) (Native.bytesOfList input)).data.toList

theorem namedBytesFast_eq (name custom input : List UInt8) :
    namedBytesFast name custom input = namedBytes name custom input := by
  unfold namedBytesFast
  rw [Fast.namedByteArrayFast_eq, Native.bytesOfList_toList,
    Native.bytesOfList_toList, Native.bytesOfList_toList]

/-- The compiled cSHAKE256 is the zero-copy `ByteArray` kernel seam. -/
@[csimp] theorem cshake256Bytes_eq_native : cshake256Bytes = Native.cshake256Native := by
  funext customization input
  exact (Native.cshake256Native_eq customization input).symm

/-- Route compiled `namedBytes` calls through the pure-Lean unboxed `UInt64` + `ByteArray` sponge. -/
@[csimp] theorem namedBytes_eq_fast : namedBytes = namedBytesFast := by
  funext name custom input
  exact (namedBytesFast_eq name custom input).symm

#tooth Fast.cshake256ByteArrayFast_eq by mutation Fast.cshake256ByteArrayFast :=
  fun _ m => Fast.squeezeByteArray (Fast.absorbByteArray m 0x1f Fast.zeroS)

#tooth Native.cshake256Native_eq by mutation Native.cshake256Kernel :=
  fun _ _ => ByteArray.empty

end Obend.Digest.Cshake256

end
