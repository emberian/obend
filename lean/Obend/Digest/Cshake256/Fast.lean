module
/-
# Obend.Digest.Cshake256.Fast -- the compiled cSHAKE256, proved equal to the spec

`Sp800185Cshake256Spec` defines cSHAKE256 over lists and `BitVec 64` lanes;
every theorem in the repository is about those definitions.  This module is
what the compiled Host runs instead, and it is proved equal to them for every
input:

* `KState`: the Keccak state as twenty-five unboxed `UInt64` fields.  One round
  (`roundS`) is straight-line word code — theta, rho/pi, chi, iota — with no
  arrays, lists or closures.  `keccakF_fast_eq` proves the twenty-four rounds
  equal `keccakF1600` on the lane representation `KState.toState`, stage by
  stage and lane by lane.  The proof is symbolic (each lane is an XOR/AND/NOT/
  rotate term over the input lanes); the permutation is never evaluated by
  the kernel.
* absorption reads rate blocks straight out of a `ByteArray` (`absorbLoop`,
  `absorb_fast_eq` against the spec's `absorbFrom`), padding is built in the
  array (`padBA_data` against `padForRate`), and the 32 output bytes are read
  from the words (`squeeze_fast_eq` against `squeeze32`).
* `cshake256Fast_eq`: for all customizations and inputs, `cshake256Fast` is
  `cshake256Bytes`.  `absorbPadded_fast_eq`: for every byte list,
  `absorbPaddedFast` is `absorbPadded`.

Both equalities are attached with `@[csimp]`, so every compiled caller of
`cshake256Bytes` or `absorbPadded` (the KMAC, the hash-equality atom, the
world root, the Store codec, ...) runs the fast code.  A `@[csimp]` lemma is a
proved rewrite of the compiler's input — no `@[implemented_by]`, no
`@[extern]`, no native code is trusted.  The remaining trust is the one every
compiled Lean definition already carries: the Lean compiler and runtime
implement `UInt64`/`ByteArray` primitives as their Lean definitions say.

`Sp800185Cshake256Core` imports this module and the spec; import Core.
-/

public import Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Spec
public section

namespace Obend.Digest.Cshake256.Fast
open Obend.Digest.Cshake256

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Word helpers -/

/-- Rotate a word left by `r` bits (`r` taken mod 64). -/
@[inline] def rotl (x : UInt64) (r : Nat) : UInt64 :=
  let n := r % 64
  if n = 0 then x
  else (x <<< UInt64.ofNat n) ||| (x >>> UInt64.ofNat (64 - n))

theorem rotl_toBitVec (x : UInt64) (r : Nat) :
    (rotl x r).toBitVec = x.toBitVec.rotateLeft r := by
  simp only [rotl, BitVec.rotateLeft_def]
  by_cases h : r % 64 = 0
  · simp [h, BitVec.ushiftRight_eq_zero]
  · simp [h, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight]
    have hlt : r % 64 < 64 := Nat.mod_lt _ (by decide)
    have hrange : 64 - r % 64 < 64 := by omega
    rw [Nat.mod_eq_of_lt hrange]

/-- Rotate left by a constant: `rotlK x k (64 - k)`.  Callers pass both shift
amounts as `UInt64` literals, so the compiled round is shifts and ORs on
constants, with no branch and no run-time `Nat` arithmetic. -/
@[inline] abbrev rotlK (x : UInt64) (k j : UInt64) : UInt64 := (x <<< k) ||| (x >>> j)

theorem rotlK_toBitVec (x : UInt64) (k j : Nat) (hk : 0 < k) (hk64 : k < 64) (hj : k + j = 64) :
    (rotlK x (UInt64.ofNat k) (UInt64.ofNat j)).toBitVec = x.toBitVec.rotateLeft k := by
  have hr := rotl_toBitVec x k
  have hkm : k % 64 = k := Nat.mod_eq_of_lt hk64
  have hne : k % 64 ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  simp only [rotl, hne, ite_false, hkm, hk0] at hr
  rw [← hr]
  have hjk : j = 64 - k := by omega
  subst hjk
  rfl

theorem bv_rotateLeft_zero (x : BitVec 64) : x.rotateLeft 0 = x := by
  have hr := rotl_toBitVec (UInt64.ofBitVec x) 0
  simp only [rotl, Nat.zero_mod, ite_true, UInt64.toBitVec_ofBitVec] at hr
  exact hr.symm

/-- Byte `j` of `b`, or zero past the end. -/
@[inline] abbrev byteOr0 (b : ByteArray) (j : Nat) : UInt8 :=
  if h : j < b.size then b[j]'h else 0

/-- Byte `j` of `b` as a word, or zero past the end. -/
@[inline] abbrev byteAt (b : ByteArray) (j : Nat) : UInt64 := (byteOr0 b j).toUInt64


/-! ### Rotations by each constant offset -/

theorem rotlK_1 (x : UInt64) : (rotlK x 1 63).toBitVec = x.toBitVec.rotateLeft 1 :=
  rotlK_toBitVec x 1 63 (by decide) (by decide) (by decide)
theorem rotlK_2 (x : UInt64) : (rotlK x 2 62).toBitVec = x.toBitVec.rotateLeft 2 :=
  rotlK_toBitVec x 2 62 (by decide) (by decide) (by decide)
theorem rotlK_3 (x : UInt64) : (rotlK x 3 61).toBitVec = x.toBitVec.rotateLeft 3 :=
  rotlK_toBitVec x 3 61 (by decide) (by decide) (by decide)
theorem rotlK_6 (x : UInt64) : (rotlK x 6 58).toBitVec = x.toBitVec.rotateLeft 6 :=
  rotlK_toBitVec x 6 58 (by decide) (by decide) (by decide)
theorem rotlK_8 (x : UInt64) : (rotlK x 8 56).toBitVec = x.toBitVec.rotateLeft 8 :=
  rotlK_toBitVec x 8 56 (by decide) (by decide) (by decide)
theorem rotlK_10 (x : UInt64) : (rotlK x 10 54).toBitVec = x.toBitVec.rotateLeft 10 :=
  rotlK_toBitVec x 10 54 (by decide) (by decide) (by decide)
theorem rotlK_14 (x : UInt64) : (rotlK x 14 50).toBitVec = x.toBitVec.rotateLeft 14 :=
  rotlK_toBitVec x 14 50 (by decide) (by decide) (by decide)
theorem rotlK_15 (x : UInt64) : (rotlK x 15 49).toBitVec = x.toBitVec.rotateLeft 15 :=
  rotlK_toBitVec x 15 49 (by decide) (by decide) (by decide)
theorem rotlK_18 (x : UInt64) : (rotlK x 18 46).toBitVec = x.toBitVec.rotateLeft 18 :=
  rotlK_toBitVec x 18 46 (by decide) (by decide) (by decide)
theorem rotlK_20 (x : UInt64) : (rotlK x 20 44).toBitVec = x.toBitVec.rotateLeft 20 :=
  rotlK_toBitVec x 20 44 (by decide) (by decide) (by decide)
theorem rotlK_21 (x : UInt64) : (rotlK x 21 43).toBitVec = x.toBitVec.rotateLeft 21 :=
  rotlK_toBitVec x 21 43 (by decide) (by decide) (by decide)
theorem rotlK_25 (x : UInt64) : (rotlK x 25 39).toBitVec = x.toBitVec.rotateLeft 25 :=
  rotlK_toBitVec x 25 39 (by decide) (by decide) (by decide)
theorem rotlK_27 (x : UInt64) : (rotlK x 27 37).toBitVec = x.toBitVec.rotateLeft 27 :=
  rotlK_toBitVec x 27 37 (by decide) (by decide) (by decide)
theorem rotlK_28 (x : UInt64) : (rotlK x 28 36).toBitVec = x.toBitVec.rotateLeft 28 :=
  rotlK_toBitVec x 28 36 (by decide) (by decide) (by decide)
theorem rotlK_36 (x : UInt64) : (rotlK x 36 28).toBitVec = x.toBitVec.rotateLeft 36 :=
  rotlK_toBitVec x 36 28 (by decide) (by decide) (by decide)
theorem rotlK_39 (x : UInt64) : (rotlK x 39 25).toBitVec = x.toBitVec.rotateLeft 39 :=
  rotlK_toBitVec x 39 25 (by decide) (by decide) (by decide)
theorem rotlK_41 (x : UInt64) : (rotlK x 41 23).toBitVec = x.toBitVec.rotateLeft 41 :=
  rotlK_toBitVec x 41 23 (by decide) (by decide) (by decide)
theorem rotlK_43 (x : UInt64) : (rotlK x 43 21).toBitVec = x.toBitVec.rotateLeft 43 :=
  rotlK_toBitVec x 43 21 (by decide) (by decide) (by decide)
theorem rotlK_44 (x : UInt64) : (rotlK x 44 20).toBitVec = x.toBitVec.rotateLeft 44 :=
  rotlK_toBitVec x 44 20 (by decide) (by decide) (by decide)
theorem rotlK_45 (x : UInt64) : (rotlK x 45 19).toBitVec = x.toBitVec.rotateLeft 45 :=
  rotlK_toBitVec x 45 19 (by decide) (by decide) (by decide)
theorem rotlK_55 (x : UInt64) : (rotlK x 55 9).toBitVec = x.toBitVec.rotateLeft 55 :=
  rotlK_toBitVec x 55 9 (by decide) (by decide) (by decide)
theorem rotlK_56 (x : UInt64) : (rotlK x 56 8).toBitVec = x.toBitVec.rotateLeft 56 :=
  rotlK_toBitVec x 56 8 (by decide) (by decide) (by decide)
theorem rotlK_61 (x : UInt64) : (rotlK x 61 3).toBitVec = x.toBitVec.rotateLeft 61 :=
  rotlK_toBitVec x 61 3 (by decide) (by decide) (by decide)
theorem rotlK_62 (x : UInt64) : (rotlK x 62 2).toBitVec = x.toBitVec.rotateLeft 62 :=
  rotlK_toBitVec x 62 2 (by decide) (by decide) (by decide)
/-! ## The word state and one round -/

/-- The Keccak state as twenty-five machine words, unboxed in one object.
Field `a(x+5y)` is lane `(x, y)`. -/
structure KState where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

/-- The spec's lane array of a word state (lane `x + 5*y` is field `a(x+5y)`). -/
def KState.toState (s : KState) : State :=
  #[s.a0.toBitVec, s.a1.toBitVec, s.a2.toBitVec, s.a3.toBitVec, s.a4.toBitVec, s.a5.toBitVec, s.a6.toBitVec, s.a7.toBitVec, s.a8.toBitVec, s.a9.toBitVec, s.a10.toBitVec, s.a11.toBitVec, s.a12.toBitVec, s.a13.toBitVec, s.a14.toBitVec, s.a15.toBitVec, s.a16.toBitVec, s.a17.toBitVec, s.a18.toBitVec, s.a19.toBitVec, s.a20.toBitVec, s.a21.toBitVec, s.a22.toBitVec, s.a23.toBitVec, s.a24.toBitVec]

/-- The all-zero state. -/
abbrev zeroS : KState := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Theta on words, in `thetaCached`'s shape: five column parities, five deltas. -/
@[inline] abbrev thetaS (s : KState) : KState :=
  let c0 := (0 : UInt64) ^^^ s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := (0 : UInt64) ^^^ s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := (0 : UInt64) ^^^ s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := (0 : UInt64) ^^^ s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := (0 : UInt64) ^^^ s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotlK c1 1 63
  let d1 := c0 ^^^ rotlK c2 1 63
  let d2 := c1 ^^^ rotlK c3 1 63
  let d3 := c2 ^^^ rotlK c4 1 63
  let d4 := c3 ^^^ rotlK c0 1 63
  ⟨s.a0 ^^^ d0, s.a1 ^^^ d1, s.a2 ^^^ d2, s.a3 ^^^ d3, s.a4 ^^^ d4, s.a5 ^^^ d0, s.a6 ^^^ d1, s.a7 ^^^ d2, s.a8 ^^^ d3, s.a9 ^^^ d4, s.a10 ^^^ d0, s.a11 ^^^ d1, s.a12 ^^^ d2, s.a13 ^^^ d3, s.a14 ^^^ d4, s.a15 ^^^ d0, s.a16 ^^^ d1, s.a17 ^^^ d2, s.a18 ^^^ d3, s.a19 ^^^ d4, s.a20 ^^^ d0, s.a21 ^^^ d1, s.a22 ^^^ d2, s.a23 ^^^ d3, s.a24 ^^^ d4⟩

/-- Fused rho and pi: target lane `t` takes the rotated source lane. -/
@[inline] abbrev rhoPiS (s : KState) : KState :=
  ⟨s.a0, rotlK s.a6 44 20, rotlK s.a12 43 21, rotlK s.a18 21 43, rotlK s.a24 14 50, rotlK s.a3 28 36, rotlK s.a9 20 44, rotlK s.a10 3 61, rotlK s.a16 45 19, rotlK s.a22 61 3, rotlK s.a1 1 63, rotlK s.a7 6 58, rotlK s.a13 25 39, rotlK s.a19 8 56, rotlK s.a20 18 46, rotlK s.a4 27 37, rotlK s.a5 36 28, rotlK s.a11 10 54, rotlK s.a17 15 49, rotlK s.a23 56 8, rotlK s.a2 62 2, rotlK s.a8 55 9, rotlK s.a14 39 25, rotlK s.a15 41 23, rotlK s.a21 2 62⟩

/-- Chi on words. -/
@[inline] abbrev chiS (s : KState) : KState :=
  ⟨s.a0 ^^^ ((~~~s.a1) &&& s.a2),
   s.a1 ^^^ ((~~~s.a2) &&& s.a3),
   s.a2 ^^^ ((~~~s.a3) &&& s.a4),
   s.a3 ^^^ ((~~~s.a4) &&& s.a0),
   s.a4 ^^^ ((~~~s.a0) &&& s.a1),
   s.a5 ^^^ ((~~~s.a6) &&& s.a7),
   s.a6 ^^^ ((~~~s.a7) &&& s.a8),
   s.a7 ^^^ ((~~~s.a8) &&& s.a9),
   s.a8 ^^^ ((~~~s.a9) &&& s.a5),
   s.a9 ^^^ ((~~~s.a5) &&& s.a6),
   s.a10 ^^^ ((~~~s.a11) &&& s.a12),
   s.a11 ^^^ ((~~~s.a12) &&& s.a13),
   s.a12 ^^^ ((~~~s.a13) &&& s.a14),
   s.a13 ^^^ ((~~~s.a14) &&& s.a10),
   s.a14 ^^^ ((~~~s.a10) &&& s.a11),
   s.a15 ^^^ ((~~~s.a16) &&& s.a17),
   s.a16 ^^^ ((~~~s.a17) &&& s.a18),
   s.a17 ^^^ ((~~~s.a18) &&& s.a19),
   s.a18 ^^^ ((~~~s.a19) &&& s.a15),
   s.a19 ^^^ ((~~~s.a15) &&& s.a16),
   s.a20 ^^^ ((~~~s.a21) &&& s.a22),
   s.a21 ^^^ ((~~~s.a22) &&& s.a23),
   s.a22 ^^^ ((~~~s.a23) &&& s.a24),
   s.a23 ^^^ ((~~~s.a24) &&& s.a20),
   s.a24 ^^^ ((~~~s.a20) &&& s.a21)⟩

/-- Iota: the round constant enters lane `(0,0)`. -/
@[inline] abbrev iotaS (s : KState) (c : UInt64) : KState :=
  { s with a0 := s.a0 ^^^ c }

/-- Little-endian lane read at byte offset `p`; bytes past the end read 0. -/
@[inline] abbrev laneAt (b : ByteArray) (p : Nat) : UInt64 :=
  (0 : UInt64) ^^^ (byteAt b (p + 0) <<< 0) ^^^ (byteAt b (p + 1) <<< 8) ^^^ (byteAt b (p + 2) <<< 16) ^^^ (byteAt b (p + 3) <<< 24) ^^^ (byteAt b (p + 4) <<< 32) ^^^ (byteAt b (p + 5) <<< 40) ^^^ (byteAt b (p + 6) <<< 48) ^^^ (byteAt b (p + 7) <<< 56)

/-- XOR one rate block of `b`, starting at byte `off`, into the seventeen rate lanes. -/
@[inline] abbrev xorBlockS (s : KState) (b : ByteArray) (off : Nat) : KState :=
  ⟨s.a0 ^^^ laneAt b (off + 0), s.a1 ^^^ laneAt b (off + 8), s.a2 ^^^ laneAt b (off + 16), s.a3 ^^^ laneAt b (off + 24), s.a4 ^^^ laneAt b (off + 32), s.a5 ^^^ laneAt b (off + 40), s.a6 ^^^ laneAt b (off + 48), s.a7 ^^^ laneAt b (off + 56), s.a8 ^^^ laneAt b (off + 64), s.a9 ^^^ laneAt b (off + 72), s.a10 ^^^ laneAt b (off + 80), s.a11 ^^^ laneAt b (off + 88), s.a12 ^^^ laneAt b (off + 96), s.a13 ^^^ laneAt b (off + 104), s.a14 ^^^ laneAt b (off + 112), s.a15 ^^^ laneAt b (off + 120), s.a16 ^^^ laneAt b (off + 128), s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24⟩


/-- The spec's rho/pi target index for a source lane. -/
def rpTarget (source : Nat) : Nat :=
  source / 5 + 5 * ((2 * (source % 5) + 3 * (source / 5)) % 5)

/-- The spec's rho/pi value for a source lane. -/
def rpValue (st : State) (source : Nat) : Lane :=
  (lane st (source % 5) (source / 5)).rotateLeft (rotationOffset (source % 5) (source / 5))

/-! ### Per-lane access lemmas (all definitional) -/

theorem toState_size (s : KState) : s.toState.size = 25 := by rfl

theorem toState_getElem_0 (s : KState) (h : 0 < s.toState.size) :
    s.toState[0] = s.a0.toBitVec := by rfl
theorem toState_getElem_1 (s : KState) (h : 1 < s.toState.size) :
    s.toState[1] = s.a1.toBitVec := by rfl
theorem toState_getElem_2 (s : KState) (h : 2 < s.toState.size) :
    s.toState[2] = s.a2.toBitVec := by rfl
theorem toState_getElem_3 (s : KState) (h : 3 < s.toState.size) :
    s.toState[3] = s.a3.toBitVec := by rfl
theorem toState_getElem_4 (s : KState) (h : 4 < s.toState.size) :
    s.toState[4] = s.a4.toBitVec := by rfl
theorem toState_getElem_5 (s : KState) (h : 5 < s.toState.size) :
    s.toState[5] = s.a5.toBitVec := by rfl
theorem toState_getElem_6 (s : KState) (h : 6 < s.toState.size) :
    s.toState[6] = s.a6.toBitVec := by rfl
theorem toState_getElem_7 (s : KState) (h : 7 < s.toState.size) :
    s.toState[7] = s.a7.toBitVec := by rfl
theorem toState_getElem_8 (s : KState) (h : 8 < s.toState.size) :
    s.toState[8] = s.a8.toBitVec := by rfl
theorem toState_getElem_9 (s : KState) (h : 9 < s.toState.size) :
    s.toState[9] = s.a9.toBitVec := by rfl
theorem toState_getElem_10 (s : KState) (h : 10 < s.toState.size) :
    s.toState[10] = s.a10.toBitVec := by rfl
theorem toState_getElem_11 (s : KState) (h : 11 < s.toState.size) :
    s.toState[11] = s.a11.toBitVec := by rfl
theorem toState_getElem_12 (s : KState) (h : 12 < s.toState.size) :
    s.toState[12] = s.a12.toBitVec := by rfl
theorem toState_getElem_13 (s : KState) (h : 13 < s.toState.size) :
    s.toState[13] = s.a13.toBitVec := by rfl
theorem toState_getElem_14 (s : KState) (h : 14 < s.toState.size) :
    s.toState[14] = s.a14.toBitVec := by rfl
theorem toState_getElem_15 (s : KState) (h : 15 < s.toState.size) :
    s.toState[15] = s.a15.toBitVec := by rfl
theorem toState_getElem_16 (s : KState) (h : 16 < s.toState.size) :
    s.toState[16] = s.a16.toBitVec := by rfl
theorem toState_getElem_17 (s : KState) (h : 17 < s.toState.size) :
    s.toState[17] = s.a17.toBitVec := by rfl
theorem toState_getElem_18 (s : KState) (h : 18 < s.toState.size) :
    s.toState[18] = s.a18.toBitVec := by rfl
theorem toState_getElem_19 (s : KState) (h : 19 < s.toState.size) :
    s.toState[19] = s.a19.toBitVec := by rfl
theorem toState_getElem_20 (s : KState) (h : 20 < s.toState.size) :
    s.toState[20] = s.a20.toBitVec := by rfl
theorem toState_getElem_21 (s : KState) (h : 21 < s.toState.size) :
    s.toState[21] = s.a21.toBitVec := by rfl
theorem toState_getElem_22 (s : KState) (h : 22 < s.toState.size) :
    s.toState[22] = s.a22.toBitVec := by rfl
theorem toState_getElem_23 (s : KState) (h : 23 < s.toState.size) :
    s.toState[23] = s.a23.toBitVec := by rfl
theorem toState_getElem_24 (s : KState) (h : 24 < s.toState.size) :
    s.toState[24] = s.a24.toBitVec := by rfl
theorem toState_getD_0 (s : KState) : s.toState.getD 0 zeroLane = s.a0.toBitVec := by rfl
theorem toState_getD_1 (s : KState) : s.toState.getD 1 zeroLane = s.a1.toBitVec := by rfl
theorem toState_getD_2 (s : KState) : s.toState.getD 2 zeroLane = s.a2.toBitVec := by rfl
theorem toState_getD_3 (s : KState) : s.toState.getD 3 zeroLane = s.a3.toBitVec := by rfl
theorem toState_getD_4 (s : KState) : s.toState.getD 4 zeroLane = s.a4.toBitVec := by rfl
theorem toState_getD_5 (s : KState) : s.toState.getD 5 zeroLane = s.a5.toBitVec := by rfl
theorem toState_getD_6 (s : KState) : s.toState.getD 6 zeroLane = s.a6.toBitVec := by rfl
theorem toState_getD_7 (s : KState) : s.toState.getD 7 zeroLane = s.a7.toBitVec := by rfl
theorem toState_getD_8 (s : KState) : s.toState.getD 8 zeroLane = s.a8.toBitVec := by rfl
theorem toState_getD_9 (s : KState) : s.toState.getD 9 zeroLane = s.a9.toBitVec := by rfl
theorem toState_getD_10 (s : KState) : s.toState.getD 10 zeroLane = s.a10.toBitVec := by rfl
theorem toState_getD_11 (s : KState) : s.toState.getD 11 zeroLane = s.a11.toBitVec := by rfl
theorem toState_getD_12 (s : KState) : s.toState.getD 12 zeroLane = s.a12.toBitVec := by rfl
theorem toState_getD_13 (s : KState) : s.toState.getD 13 zeroLane = s.a13.toBitVec := by rfl
theorem toState_getD_14 (s : KState) : s.toState.getD 14 zeroLane = s.a14.toBitVec := by rfl
theorem toState_getD_15 (s : KState) : s.toState.getD 15 zeroLane = s.a15.toBitVec := by rfl
theorem toState_getD_16 (s : KState) : s.toState.getD 16 zeroLane = s.a16.toBitVec := by rfl
theorem toState_getD_17 (s : KState) : s.toState.getD 17 zeroLane = s.a17.toBitVec := by rfl
theorem toState_getD_18 (s : KState) : s.toState.getD 18 zeroLane = s.a18.toBitVec := by rfl
theorem toState_getD_19 (s : KState) : s.toState.getD 19 zeroLane = s.a19.toBitVec := by rfl
theorem toState_getD_20 (s : KState) : s.toState.getD 20 zeroLane = s.a20.toBitVec := by rfl
theorem toState_getD_21 (s : KState) : s.toState.getD 21 zeroLane = s.a21.toBitVec := by rfl
theorem toState_getD_22 (s : KState) : s.toState.getD 22 zeroLane = s.a22.toBitVec := by rfl
theorem toState_getD_23 (s : KState) : s.toState.getD 23 zeroLane = s.a23.toBitVec := by rfl
theorem toState_getD_24 (s : KState) : s.toState.getD 24 zeroLane = s.a24.toBitVec := by rfl
theorem lane_toState_0_0 (s : KState) : lane s.toState 0 0 = s.a0.toBitVec := by rfl
theorem lane_toState_1_0 (s : KState) : lane s.toState 1 0 = s.a1.toBitVec := by rfl
theorem lane_toState_2_0 (s : KState) : lane s.toState 2 0 = s.a2.toBitVec := by rfl
theorem lane_toState_3_0 (s : KState) : lane s.toState 3 0 = s.a3.toBitVec := by rfl
theorem lane_toState_4_0 (s : KState) : lane s.toState 4 0 = s.a4.toBitVec := by rfl
theorem lane_toState_5_0 (s : KState) : lane s.toState 5 0 = s.a0.toBitVec := by rfl
theorem lane_toState_6_0 (s : KState) : lane s.toState 6 0 = s.a1.toBitVec := by rfl
theorem lane_toState_0_1 (s : KState) : lane s.toState 0 1 = s.a5.toBitVec := by rfl
theorem lane_toState_1_1 (s : KState) : lane s.toState 1 1 = s.a6.toBitVec := by rfl
theorem lane_toState_2_1 (s : KState) : lane s.toState 2 1 = s.a7.toBitVec := by rfl
theorem lane_toState_3_1 (s : KState) : lane s.toState 3 1 = s.a8.toBitVec := by rfl
theorem lane_toState_4_1 (s : KState) : lane s.toState 4 1 = s.a9.toBitVec := by rfl
theorem lane_toState_5_1 (s : KState) : lane s.toState 5 1 = s.a5.toBitVec := by rfl
theorem lane_toState_6_1 (s : KState) : lane s.toState 6 1 = s.a6.toBitVec := by rfl
theorem lane_toState_0_2 (s : KState) : lane s.toState 0 2 = s.a10.toBitVec := by rfl
theorem lane_toState_1_2 (s : KState) : lane s.toState 1 2 = s.a11.toBitVec := by rfl
theorem lane_toState_2_2 (s : KState) : lane s.toState 2 2 = s.a12.toBitVec := by rfl
theorem lane_toState_3_2 (s : KState) : lane s.toState 3 2 = s.a13.toBitVec := by rfl
theorem lane_toState_4_2 (s : KState) : lane s.toState 4 2 = s.a14.toBitVec := by rfl
theorem lane_toState_5_2 (s : KState) : lane s.toState 5 2 = s.a10.toBitVec := by rfl
theorem lane_toState_6_2 (s : KState) : lane s.toState 6 2 = s.a11.toBitVec := by rfl
theorem lane_toState_0_3 (s : KState) : lane s.toState 0 3 = s.a15.toBitVec := by rfl
theorem lane_toState_1_3 (s : KState) : lane s.toState 1 3 = s.a16.toBitVec := by rfl
theorem lane_toState_2_3 (s : KState) : lane s.toState 2 3 = s.a17.toBitVec := by rfl
theorem lane_toState_3_3 (s : KState) : lane s.toState 3 3 = s.a18.toBitVec := by rfl
theorem lane_toState_4_3 (s : KState) : lane s.toState 4 3 = s.a19.toBitVec := by rfl
theorem lane_toState_5_3 (s : KState) : lane s.toState 5 3 = s.a15.toBitVec := by rfl
theorem lane_toState_6_3 (s : KState) : lane s.toState 6 3 = s.a16.toBitVec := by rfl
theorem lane_toState_0_4 (s : KState) : lane s.toState 0 4 = s.a20.toBitVec := by rfl
theorem lane_toState_1_4 (s : KState) : lane s.toState 1 4 = s.a21.toBitVec := by rfl
theorem lane_toState_2_4 (s : KState) : lane s.toState 2 4 = s.a22.toBitVec := by rfl
theorem lane_toState_3_4 (s : KState) : lane s.toState 3 4 = s.a23.toBitVec := by rfl
theorem lane_toState_4_4 (s : KState) : lane s.toState 4 4 = s.a24.toBitVec := by rfl
theorem lane_toState_5_4 (s : KState) : lane s.toState 5 4 = s.a20.toBitVec := by rfl
theorem lane_toState_6_4 (s : KState) : lane s.toState 6 4 = s.a21.toBitVec := by rfl
theorem rotationOffset_0_0 : rotationOffset 0 0 = 0 := by rfl
theorem rotationOffset_1_0 : rotationOffset 1 0 = 1 := by rfl
theorem rotationOffset_2_0 : rotationOffset 2 0 = 62 := by rfl
theorem rotationOffset_3_0 : rotationOffset 3 0 = 28 := by rfl
theorem rotationOffset_4_0 : rotationOffset 4 0 = 27 := by rfl
theorem rotationOffset_0_1 : rotationOffset 0 1 = 36 := by rfl
theorem rotationOffset_1_1 : rotationOffset 1 1 = 44 := by rfl
theorem rotationOffset_2_1 : rotationOffset 2 1 = 6 := by rfl
theorem rotationOffset_3_1 : rotationOffset 3 1 = 55 := by rfl
theorem rotationOffset_4_1 : rotationOffset 4 1 = 20 := by rfl
theorem rotationOffset_0_2 : rotationOffset 0 2 = 3 := by rfl
theorem rotationOffset_1_2 : rotationOffset 1 2 = 10 := by rfl
theorem rotationOffset_2_2 : rotationOffset 2 2 = 43 := by rfl
theorem rotationOffset_3_2 : rotationOffset 3 2 = 25 := by rfl
theorem rotationOffset_4_2 : rotationOffset 4 2 = 39 := by rfl
theorem rotationOffset_0_3 : rotationOffset 0 3 = 41 := by rfl
theorem rotationOffset_1_3 : rotationOffset 1 3 = 45 := by rfl
theorem rotationOffset_2_3 : rotationOffset 2 3 = 15 := by rfl
theorem rotationOffset_3_3 : rotationOffset 3 3 = 21 := by rfl
theorem rotationOffset_4_3 : rotationOffset 4 3 = 8 := by rfl
theorem rotationOffset_0_4 : rotationOffset 0 4 = 18 := by rfl
theorem rotationOffset_1_4 : rotationOffset 1 4 = 2 := by rfl
theorem rotationOffset_2_4 : rotationOffset 2 4 = 61 := by rfl
theorem rotationOffset_3_4 : rotationOffset 3 4 = 56 := by rfl
theorem rotationOffset_4_4 : rotationOffset 4 4 = 14 := by rfl
/-- The rho/pi source of each target lane (the inverse of `rpTarget`). -/
def rpSource : Nat → Nat
  | 0 => 0
  | 1 => 6
  | 2 => 12
  | 3 => 18
  | 4 => 24
  | 5 => 3
  | 6 => 9
  | 7 => 10
  | 8 => 16
  | 9 => 22
  | 10 => 1
  | 11 => 7
  | 12 => 13
  | 13 => 19
  | 14 => 20
  | 15 => 4
  | 16 => 5
  | 17 => 11
  | 18 => 17
  | 19 => 23
  | 20 => 2
  | 21 => 8
  | 22 => 14
  | 23 => 15
  | 24 => 21
  | _ => 0

theorem rpSource_0 : rpSource 0 = 0 := by rfl
theorem rpSource_1 : rpSource 1 = 6 := by rfl
theorem rpSource_2 : rpSource 2 = 12 := by rfl
theorem rpSource_3 : rpSource 3 = 18 := by rfl
theorem rpSource_4 : rpSource 4 = 24 := by rfl
theorem rpSource_5 : rpSource 5 = 3 := by rfl
theorem rpSource_6 : rpSource 6 = 9 := by rfl
theorem rpSource_7 : rpSource 7 = 10 := by rfl
theorem rpSource_8 : rpSource 8 = 16 := by rfl
theorem rpSource_9 : rpSource 9 = 22 := by rfl
theorem rpSource_10 : rpSource 10 = 1 := by rfl
theorem rpSource_11 : rpSource 11 = 7 := by rfl
theorem rpSource_12 : rpSource 12 = 13 := by rfl
theorem rpSource_13 : rpSource 13 = 19 := by rfl
theorem rpSource_14 : rpSource 14 = 20 := by rfl
theorem rpSource_15 : rpSource 15 = 4 := by rfl
theorem rpSource_16 : rpSource 16 = 5 := by rfl
theorem rpSource_17 : rpSource 17 = 11 := by rfl
theorem rpSource_18 : rpSource 18 = 17 := by rfl
theorem rpSource_19 : rpSource 19 = 23 := by rfl
theorem rpSource_20 : rpSource 20 = 2 := by rfl
theorem rpSource_21 : rpSource 21 = 8 := by rfl
theorem rpSource_22 : rpSource 22 = 14 := by rfl
theorem rpSource_23 : rpSource 23 = 15 := by rfl
theorem rpSource_24 : rpSource 24 = 21 := by rfl

/-- The last rho/pi write to each target comes from `rpSource`. -/
theorem rhoPi_find (t : Nat) (ht : t < 25) :
    (List.range 25).reverse.find? (fun s => rpTarget s == t) = some (rpSource t) := by
  revert t
  decide

/-! ### The permutation, stage by stage -/

theorem xorColumn_five (st : State) (x : Nat) :
    xorColumn st x = zeroLane ^^^ lane st x 0 ^^^ lane st x 1 ^^^ lane st x 2 ^^^
      lane st x 3 ^^^ lane st x 4 := by rfl

theorem u64_zero_toBitVec : (0 : UInt64).toBitVec = zeroLane := by rfl

/-- Lanewise equality against the twenty-five-lane literal. -/
theorem toState_ext (s : KState) (st : State) (hsize : st.size = 25)
    (h0 : s.toState[0]'(by rw [toState_size]; decide) = st[0]'(by rw [hsize]; decide))
    (h1 : s.toState[1]'(by rw [toState_size]; decide) = st[1]'(by rw [hsize]; decide))
    (h2 : s.toState[2]'(by rw [toState_size]; decide) = st[2]'(by rw [hsize]; decide))
    (h3 : s.toState[3]'(by rw [toState_size]; decide) = st[3]'(by rw [hsize]; decide))
    (h4 : s.toState[4]'(by rw [toState_size]; decide) = st[4]'(by rw [hsize]; decide))
    (h5 : s.toState[5]'(by rw [toState_size]; decide) = st[5]'(by rw [hsize]; decide))
    (h6 : s.toState[6]'(by rw [toState_size]; decide) = st[6]'(by rw [hsize]; decide))
    (h7 : s.toState[7]'(by rw [toState_size]; decide) = st[7]'(by rw [hsize]; decide))
    (h8 : s.toState[8]'(by rw [toState_size]; decide) = st[8]'(by rw [hsize]; decide))
    (h9 : s.toState[9]'(by rw [toState_size]; decide) = st[9]'(by rw [hsize]; decide))
    (h10 : s.toState[10]'(by rw [toState_size]; decide) = st[10]'(by rw [hsize]; decide))
    (h11 : s.toState[11]'(by rw [toState_size]; decide) = st[11]'(by rw [hsize]; decide))
    (h12 : s.toState[12]'(by rw [toState_size]; decide) = st[12]'(by rw [hsize]; decide))
    (h13 : s.toState[13]'(by rw [toState_size]; decide) = st[13]'(by rw [hsize]; decide))
    (h14 : s.toState[14]'(by rw [toState_size]; decide) = st[14]'(by rw [hsize]; decide))
    (h15 : s.toState[15]'(by rw [toState_size]; decide) = st[15]'(by rw [hsize]; decide))
    (h16 : s.toState[16]'(by rw [toState_size]; decide) = st[16]'(by rw [hsize]; decide))
    (h17 : s.toState[17]'(by rw [toState_size]; decide) = st[17]'(by rw [hsize]; decide))
    (h18 : s.toState[18]'(by rw [toState_size]; decide) = st[18]'(by rw [hsize]; decide))
    (h19 : s.toState[19]'(by rw [toState_size]; decide) = st[19]'(by rw [hsize]; decide))
    (h20 : s.toState[20]'(by rw [toState_size]; decide) = st[20]'(by rw [hsize]; decide))
    (h21 : s.toState[21]'(by rw [toState_size]; decide) = st[21]'(by rw [hsize]; decide))
    (h22 : s.toState[22]'(by rw [toState_size]; decide) = st[22]'(by rw [hsize]; decide))
    (h23 : s.toState[23]'(by rw [toState_size]; decide) = st[23]'(by rw [hsize]; decide))
    (h24 : s.toState[24]'(by rw [toState_size]; decide) = st[24]'(by rw [hsize]; decide))
    : s.toState = st := by
  apply Array.ext
  · rw [toState_size, hsize]
  · intro i hi _
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | 8, _ => exact h8
    | 9, _ => exact h9
    | 10, _ => exact h10
    | 11, _ => exact h11
    | 12, _ => exact h12
    | 13, _ => exact h13
    | 14, _ => exact h14
    | 15, _ => exact h15
    | 16, _ => exact h16
    | 17, _ => exact h17
    | 18, _ => exact h18
    | 19, _ => exact h19
    | 20, _ => exact h20
    | 21, _ => exact h21
    | 22, _ => exact h22
    | 23, _ => exact h23
    | 24, _ => exact h24
    | n + 25, h => exact absurd h (by rw [toState_size]; omega)

private theorem thetaCached_getElem (st : State) (i : Nat) (hi : i < (thetaCached st).size) :
    (thetaCached st)[i] =
      lane st (i % 5) (i / 5) ^^^
        (xorColumn st ((i % 5 + 4) % 5) ^^^ (xorColumn st ((i % 5 + 1) % 5)).rotateLeft 1) := by
  simp only [thetaCached, Array.getElem_ofFn]

private theorem thetaS_col {x0 x1 x2 x3 x4 : UInt64} {st : State} {x : Nat}
    (h0 : x0.toBitVec = lane st x 0) (h1 : x1.toBitVec = lane st x 1)
    (h2 : x2.toBitVec = lane st x 2) (h3 : x3.toBitVec = lane st x 3)
    (h4 : x4.toBitVec = lane st x 4) :
    ((0 : UInt64) ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4).toBitVec = xorColumn st x := by
  simp only [xorColumn_five, UInt64.toBitVec_xor, u64_zero_toBitVec, h0, h1, h2, h3, h4]

private theorem thetaS_delta {cA cB : UInt64} {st : State} {xA xB : Nat}
    (hA : cA.toBitVec = xorColumn st xA) (hB : cB.toBitVec = xorColumn st xB) :
    (cA ^^^ rotlK cB 1 63).toBitVec = xorColumn st xA ^^^ (xorColumn st xB).rotateLeft 1 := by
  rw [UInt64.toBitVec_xor, rotlK_1, hA, hB]

theorem thetaS_toState (s : KState) : (thetaS s).toState = thetaCached s.toState := by
  have hc0 : ((0 : UInt64) ^^^ s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20).toBitVec =
      xorColumn s.toState 0 := thetaS_col rfl rfl rfl rfl rfl
  have hc1 : ((0 : UInt64) ^^^ s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21).toBitVec =
      xorColumn s.toState 1 := thetaS_col rfl rfl rfl rfl rfl
  have hc2 : ((0 : UInt64) ^^^ s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22).toBitVec =
      xorColumn s.toState 2 := thetaS_col rfl rfl rfl rfl rfl
  have hc3 : ((0 : UInt64) ^^^ s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23).toBitVec =
      xorColumn s.toState 3 := thetaS_col rfl rfl rfl rfl rfl
  have hc4 : ((0 : UInt64) ^^^ s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24).toBitVec =
      xorColumn s.toState 4 := thetaS_col rfl rfl rfl rfl rfl
  have hd0 := thetaS_delta hc4 hc1
  have hd1 := thetaS_delta hc0 hc2
  have hd2 := thetaS_delta hc1 hc3
  have hd3 := thetaS_delta hc2 hc4
  have hd4 := thetaS_delta hc3 hc0
  apply toState_ext _ _ (by simp [thetaCached])
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd0)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd1)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd2)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd3)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd4)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd0)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd1)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd2)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd3)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd4)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd0)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd1)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd2)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd3)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd4)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd0)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd1)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd2)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd3)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd4)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd0)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd1)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd2)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd3)
  · rw [thetaCached_getElem]; exact (UInt64.toBitVec_xor _ _).trans (congrArg _ hd4)

private theorem chi_getElem (st : State) (i : Nat) (hi : i < (chi st).size) :
    (chi st)[i] =
      lane st (i % 5) (i / 5) ^^^
        ((~~~lane st (i % 5 + 1) (i / 5)) &&& lane st (i % 5 + 2) (i / 5)) := by
  simp only [chi, Array.getElem_ofFn]

private theorem chi_lane_eq (a b c : UInt64) :
    (a ^^^ ((~~~b) &&& c)).toBitVec = a.toBitVec ^^^ ((~~~b.toBitVec) &&& c.toBitVec) := by
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not]

theorem chiS_toState (s : KState) : (chiS s).toState = chi s.toState := by
  apply toState_ext _ _ (by simp [chi])
  · rw [chi_getElem]; exact chi_lane_eq s.a0 s.a1 s.a2
  · rw [chi_getElem]; exact chi_lane_eq s.a1 s.a2 s.a3
  · rw [chi_getElem]; exact chi_lane_eq s.a2 s.a3 s.a4
  · rw [chi_getElem]; exact chi_lane_eq s.a3 s.a4 s.a0
  · rw [chi_getElem]; exact chi_lane_eq s.a4 s.a0 s.a1
  · rw [chi_getElem]; exact chi_lane_eq s.a5 s.a6 s.a7
  · rw [chi_getElem]; exact chi_lane_eq s.a6 s.a7 s.a8
  · rw [chi_getElem]; exact chi_lane_eq s.a7 s.a8 s.a9
  · rw [chi_getElem]; exact chi_lane_eq s.a8 s.a9 s.a5
  · rw [chi_getElem]; exact chi_lane_eq s.a9 s.a5 s.a6
  · rw [chi_getElem]; exact chi_lane_eq s.a10 s.a11 s.a12
  · rw [chi_getElem]; exact chi_lane_eq s.a11 s.a12 s.a13
  · rw [chi_getElem]; exact chi_lane_eq s.a12 s.a13 s.a14
  · rw [chi_getElem]; exact chi_lane_eq s.a13 s.a14 s.a10
  · rw [chi_getElem]; exact chi_lane_eq s.a14 s.a10 s.a11
  · rw [chi_getElem]; exact chi_lane_eq s.a15 s.a16 s.a17
  · rw [chi_getElem]; exact chi_lane_eq s.a16 s.a17 s.a18
  · rw [chi_getElem]; exact chi_lane_eq s.a17 s.a18 s.a19
  · rw [chi_getElem]; exact chi_lane_eq s.a18 s.a19 s.a15
  · rw [chi_getElem]; exact chi_lane_eq s.a19 s.a15 s.a16
  · rw [chi_getElem]; exact chi_lane_eq s.a20 s.a21 s.a22
  · rw [chi_getElem]; exact chi_lane_eq s.a21 s.a22 s.a23
  · rw [chi_getElem]; exact chi_lane_eq s.a22 s.a23 s.a24
  · rw [chi_getElem]; exact chi_lane_eq s.a23 s.a24 s.a20
  · rw [chi_getElem]; exact chi_lane_eq s.a24 s.a20 s.a21

/-- A fold of in-bounds writes, read back at one index: the last write to that
index wins, else the initial array's entry. -/
theorem foldl_setIfInBounds_getElem? {α : Type} (g : Nat → Nat) (f : Nat → α)
    (l : List Nat) (a : Array α) (t : Nat) :
    (l.foldl (fun o s => o.setIfInBounds (g s) (f s)) a)[t]? =
      match l.reverse.find? (fun s => g s == t) with
      | some s => if t < a.size then some (f s) else none
      | none => a[t]? := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
      rw [Array.size_setIfInBounds]
      cases hfind : xs.reverse.find? (fun s => g s == t) with
      | some s => simp
      | none =>
          simp only [Option.none_or, List.find?_cons, List.find?_nil]
          rw [Array.getElem?_setIfInBounds]
          by_cases hgt : g x = t
          · subst hgt
            by_cases hlt : g x < a.size <;> simp [hlt]
          · have hb : (g x == t) = false := by simp [hgt]
            simp only [hb, hgt, ite_false]

theorem rhoPi_eq_fold (st : State) :
    rhoPi st = (List.range 25).foldl
      (fun o s => o.setIfInBounds (rpTarget s) (rpValue st s)) zeroState := by rfl

theorem zeroState_size : zeroState.size = 25 := by rfl

theorem rhoPi_getElem? (st : State) (t : Nat) (ht : t < 25) :
    (rhoPi st)[t]? = some (rpValue st (rpSource t)) := by
  rw [rhoPi_eq_fold, foldl_setIfInBounds_getElem?, rhoPi_find t ht]
  simp [zeroState_size, ht]

theorem rhoPi_size (st : State) : (rhoPi st).size = 25 := by
  rw [rhoPi_eq_fold]
  generalize List.range 25 = l
  have : ∀ (a : State), (l.foldl (fun o s => o.setIfInBounds (rpTarget s) (rpValue st s)) a).size
      = a.size := by
    induction l with
    | nil => intro a; rfl
    | cons x xs ih => intro a; rw [List.foldl_cons, ih, Array.size_setIfInBounds]
  rw [this, zeroState_size]

theorem rhoPi_getElem (st : State) (t : Nat) (ht : t < 25) (h : t < (rhoPi st).size) :
    (rhoPi st)[t] = rpValue st (rpSource t) := by
  apply Option.some.inj
  rw [← Array.getElem?_eq_getElem h, rhoPi_getElem? st t ht]

theorem rhoPiS_toState (s : KState) : (rhoPiS s).toState = rhoPi s.toState := by
  apply toState_ext _ _ (rhoPi_size _)
  · rw [rhoPi_getElem _ _ (by decide)]; exact (bv_rotateLeft_zero s.a0.toBitVec).symm
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_44 s.a6
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_43 s.a12
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_21 s.a18
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_14 s.a24
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_28 s.a3
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_20 s.a9
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_3 s.a10
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_45 s.a16
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_61 s.a22
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_1 s.a1
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_6 s.a7
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_25 s.a13
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_8 s.a19
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_18 s.a20
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_27 s.a4
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_36 s.a5
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_10 s.a11
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_15 s.a17
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_56 s.a23
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_62 s.a2
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_55 s.a8
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_39 s.a14
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_41 s.a15
  · rw [rhoPi_getElem _ _ (by decide)]; exact rotlK_2 s.a21

theorem iotaS_toState (s : KState) (c : UInt64) :
    (iotaS s c).toState = s.toState.setIfInBounds 0 (lane s.toState 0 0 ^^^ c.toBitVec) := by
  apply toState_ext _ _ (by rw [Array.size_setIfInBounds, toState_size])
  · simp only [Array.getElem_setIfInBounds_self, iotaS, toState_getElem_0, UInt64.toBitVec_xor,
      lane_toState_0_0]
  all_goals
    rw [Array.getElem_setIfInBounds_ne (by rw [toState_size]; decide) (by decide)]
    rfl

/-- One word round. -/
@[inline] abbrev roundS (s : KState) (c : UInt64) : KState :=
  iotaS (chiS (rhoPiS (thetaS s))) c

theorem roundS_toState (s : KState) (c : UInt64) :
    (roundS s c).toState = round s.toState c.toBitVec := by
  simp only [roundS, round, iotaS_toState, chiS_toState, rhoPiS_toState, thetaS_toState,
    theta_eq_thetaCached]

/-- The round constants as machine words. -/
abbrev roundConstantsS : List UInt64 := roundConstants.map UInt64.ofBitVec

/-- Keccak-f[1600] on the word state: the spec's twenty-four rounds, in order. -/
@[expose] def keccakS (s : KState) : KState := roundConstantsS.foldl roundS s

/-- **The permutation refinement**: the word permutation is the spec's
Keccak-f[1600] on the lane representation, for every state. -/
theorem keccakF_fast_eq (s : KState) : (keccakS s).toState = keccakF1600 s.toState := by
  have hfold (constants : List Lane) (initial : KState) :
      ((constants.map UInt64.ofBitVec).foldl roundS initial).toState =
        constants.foldl round initial.toState := by
    induction constants generalizing initial with
    | nil => rfl
    | cons constant rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [ih, roundS_toState, UInt64.toBitVec_ofBitVec]
  exact hfold roundConstants s


/-! ### Absorption over a byte array -/

theorem laneAt_eq_fold (b : ByteArray) (p : Nat) :
    laneAt b p = (List.range 8).foldl
      (fun acc t => acc ^^^ (byteAt b (p + t) <<< UInt64.ofNat (8 * t))) 0 := by rfl

theorem toUInt64_eq_ofNat (v : UInt8) : v.toUInt64 = UInt64.ofNat v.toNat := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.lt_trans v.toNat_lt (by decide))).symm

theorem shl_byte (v : UInt8) (t : Nat) (ht : t < 8) :
    (v.toUInt64 <<< UInt64.ofNat (8 * t)).toBitVec =
      BitVec.ofNat 64 (v.toNat * 2 ^ (8 * t)) := by
  rw [toUInt64_eq_ofNat]
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat']
  have hs : 8 * t < 64 := by omega
  have hs64 : 8 * t < 2 ^ 64 := by omega
  rw [BitVec.shiftLeft_eq']
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
  have h64 : (64 : BitVec 64).toNat = 64 := by decide
  rw [h64, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have hpow : BitVec.twoPow 64 (8 * t) = BitVec.ofNat 64 (2 ^ (8 * t)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_twoPow, BitVec.toNat_ofNat]
  rw [hpow, ← BitVec.ofNat_mul]

theorem getD_take_drop (l : List UInt8) (off q : Nat) (hq : q < 136) :
    ((l.drop off).take 136).getD q 0 = l.getD (off + q) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hq, ite_true,
    List.getElem?_drop]

theorem getD_data (b : ByteArray) (j : Nat) : b.data.toList.getD j 0 = byteOr0 b j := by
  unfold byteOr0
  by_cases h : j < b.size
  · simp only [h, ↓reduceDIte, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    have h' : j < b.data.size := h
    rw [Array.getElem?_eq_getElem h']
    rfl
  · simp only [h, ↓reduceDIte, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    have h' : ¬ j < b.data.size := h
    rw [Array.getElem?_eq_none (by omega)]
    rfl

theorem laneAt_eq (b : ByteArray) (off i : Nat) (hi : i < 17) :
    laneFromBlock ((b.data.toList.drop off).take 136) i =
      (laneAt b (off + 8 * i)).toBitVec := by
  have hfold (offsets : List Nat) (h : ∀ t ∈ offsets, t < 8) (acc : UInt64) :
      (offsets.foldl (fun a t => a ^^^ (byteAt b (off + 8 * i + t) <<< UInt64.ofNat (8 * t)))
        acc).toBitVec =
      offsets.foldl (fun a t => a ^^^ BitVec.ofNat 64
        ((((b.data.toList.drop off).take 136).getD (8 * i + t) 0).toNat * 2 ^ (8 * t)))
        acc.toBitVec := by
    induction offsets generalizing acc with
    | nil => rfl
    | cons t rest ih =>
        simp only [List.foldl_cons]
        rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
        have ht : t < 8 := h t (by simp)
        rw [UInt64.toBitVec_xor, byteAt, shl_byte _ _ ht,
          getD_take_drop _ _ _ (by omega), getD_data, Nat.add_assoc]
  rw [laneAt_eq_fold, hfold (List.range 8) (fun t ht => List.mem_range.mp ht) 0]
  rfl

private theorem xorRateBlock_getElem_lt (st : State) (block : List UInt8) (i : Nat)
    (hi : i < rateLanes) (h : i < (xorRateBlock st block).size) :
    (xorRateBlock st block)[i] = st.getD i zeroLane ^^^ laneFromBlock block i := by
  simp only [xorRateBlock, Array.getElem_ofFn, hi, ite_true]

private theorem xorRateBlock_getElem_ge (st : State) (block : List UInt8) (i : Nat)
    (hi : ¬ i < rateLanes) (h : i < (xorRateBlock st block).size) :
    (xorRateBlock st block)[i] = st.getD i zeroLane := by
  simp only [xorRateBlock, Array.getElem_ofFn, hi, ite_false]

theorem xorBlockS_toState (s : KState) (b : ByteArray) (off : Nat) :
    (xorBlockS s b off).toState = xorRateBlock s.toState ((b.data.toList.drop off).take 136) := by
  apply toState_ext _ _ (by simp [xorRateBlock])
  · rw [xorRateBlock_getElem_lt _ _ 0 (by decide), laneAt_eq b off 0 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 1 (by decide), laneAt_eq b off 1 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 2 (by decide), laneAt_eq b off 2 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 3 (by decide), laneAt_eq b off 3 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 4 (by decide), laneAt_eq b off 4 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 5 (by decide), laneAt_eq b off 5 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 6 (by decide), laneAt_eq b off 6 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 7 (by decide), laneAt_eq b off 7 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 8 (by decide), laneAt_eq b off 8 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 9 (by decide), laneAt_eq b off 9 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 10 (by decide), laneAt_eq b off 10 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 11 (by decide), laneAt_eq b off 11 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 12 (by decide), laneAt_eq b off 12 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 13 (by decide), laneAt_eq b off 13 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 14 (by decide), laneAt_eq b off 14 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 15 (by decide), laneAt_eq b off 15 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_lt _ _ 16 (by decide), laneAt_eq b off 16 (by decide)]; exact UInt64.toBitVec_xor _ _
  · rw [xorRateBlock_getElem_ge _ _ 17 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 18 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 19 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 20 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 21 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 22 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 23 (by decide)]; rfl
  · rw [xorRateBlock_getElem_ge _ _ 24 (by decide)]; rfl

/-- Absorb `count` full rate blocks of `b`, starting at byte `off`. -/
@[expose] def absorbLoop (b : ByteArray) : Nat → Nat → KState → KState
  | 0, _, s => s
  | count + 1, off, s => absorbLoop b count (off + 136) (keccakS (xorBlockS s b off))

theorem absorb_fast_eq (b : ByteArray) (count off : Nat) (s : KState) :
    (absorbLoop b count off s).toState =
      absorbFrom count s.toState (b.data.toList.drop off) := by
  induction count generalizing off s with
  | zero => rfl
  | succ count ih =>
      rw [absorbLoop, absorbFrom, ih, keccakF_fast_eq, xorBlockS_toState, List.drop_drop]
      simp only [rateBytes, Nat.add_comm]

theorem zeroS_toState : zeroS.toState = zeroState := by rfl

/-! ### Byte-array builders, proved against their list readings -/

/-- Append every byte of a list. -/
@[expose] def pushList (b : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push b

theorem push_data (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

theorem pushList_data (b : ByteArray) (l : List UInt8) :
    (pushList b l).data.toList = b.data.toList ++ l := by
  induction l generalizing b with
  | nil => simp [pushList]
  | cons x xs ih =>
      simp only [pushList, List.foldl_cons] at ih ⊢
      rw [ih, push_data, List.append_assoc, List.singleton_append]

/-- Append `n` zero bytes. -/
@[expose] def pushZeros (b : ByteArray) : Nat → ByteArray
  | 0 => b
  | n + 1 => pushZeros (b.push 0) n

theorem pushZeros_data (b : ByteArray) (n : Nat) :
    (pushZeros b n).data.toList = b.data.toList ++ List.replicate n 0 := by
  induction n generalizing b with
  | zero => simp [pushZeros]
  | succ n ih =>
      rw [pushZeros, ih, push_data, List.append_assoc, List.replicate_succ, List.singleton_append]

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]
  rfl

/-- `padForRate` on a byte array. -/
@[expose] def padBA (b : ByteArray) (suffix : UInt8) : ByteArray :=
  let count := rateBytes - b.size % rateBytes
  if count = 1 then b.push (suffix ^^^ (128 : UInt8))
  else (pushZeros (b.push suffix) (count - 2)).push 128

theorem padBA_data (b : ByteArray) (suffix : UInt8) :
    (padBA b suffix).data.toList = padForRate b.data.toList suffix := by
  unfold padBA padForRate
  rw [size_eq_length]
  dsimp only
  by_cases hc : rateBytes - b.data.toList.length % rateBytes = 1
  · simp only [hc, ↓reduceIte, push_data]
  · simp only [hc, ↓reduceIte, push_data, pushZeros_data]

/-- The padded sponge over a byte array, before squeezing. -/
@[expose] def spongeS (b : ByteArray) (suffix : UInt8) : KState :=
  let padded := padBA b suffix
  absorbLoop padded (padded.size / rateBytes) 0 zeroS

theorem spongeS_toState (b : ByteArray) (suffix : UInt8) :
    (spongeS b suffix).toState = absorbPadded (padForRate b.data.toList suffix) := by
  unfold spongeS absorbPadded
  rw [absorb_fast_eq, zeroS_toState, size_eq_length, padBA_data, List.drop_zero]

/-! ### Squeezing the first 256 bits -/

/-- Lane `j` of the rate, `j < 4`. -/
@[expose] def outLane (s : KState) : Nat → UInt64
  | 0 => s.a0
  | 1 => s.a1
  | 2 => s.a2
  | 3 => s.a3
  | _ => 0

/-- The first thirty-two output bytes, read straight from the words. -/
@[expose] def squeezeS (s : KState) : List UInt8 :=
  (List.range outputBytes).map fun k => (outLane s (k / 8) >>> UInt64.ofNat (8 * (k % 8))).toUInt8

theorem shr_byte (x : UInt64) (t : Nat) (ht : t < 8) :
    (x >>> UInt64.ofNat (8 * t)).toUInt8 = UInt8.ofNat (x.toBitVec.toNat / 2 ^ (8 * t) % 256) := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
  have hs : 8 * t < 64 := by omega
  have hs64 : 8 * t < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs]
  simp

theorem squeeze_fast_eq (s : KState) : squeezeS s = squeeze32 s.toState := by
  unfold squeezeS squeeze32
  apply List.map_congr_left
  intro k hk
  have hk32 : k < 32 := List.mem_range.mp hk
  have hlane : s.toState.getD (k / 8) zeroLane = (outLane s (k / 8)).toBitVec := by
    have : k / 8 < 4 := by omega
    generalize k / 8 = j at this ⊢
    match j, this with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | j + 4, h => exact absurd h (by omega)
  unfold stateByte
  rw [hlane, shr_byte _ _ (Nat.mod_lt _ (by decide))]

/-! ### The fast cSHAKE256 and the sponge entry point -/

/-- `absorbPadded` through the word permutation over a byte array. -/
def absorbPaddedFast (padded : List UInt8) : State :=
  (absorbLoop (pushList ByteArray.empty padded) (padded.length / rateBytes) 0 zeroS).toState

theorem empty_data : ByteArray.empty.data.toList = [] := by rfl

theorem absorbPadded_fast_eq (padded : List UInt8) :
    absorbPaddedFast padded = absorbPadded padded := by
  unfold absorbPaddedFast absorbPadded
  rw [absorb_fast_eq, pushList_data, empty_data, List.nil_append, List.drop_zero,
    zeroS_toState]

/-- The 32-byte squeeze of the padded sponge of a byte array. -/
@[expose] def spongeBytes (b : ByteArray) (suffix : UInt8) : List UInt8 :=
  squeezeS (spongeS b suffix)

theorem sponge_fast_eq (b : ByteArray) (suffix : UInt8) :
    spongeBytes b suffix = squeeze32 (absorbPadded (padForRate b.data.toList suffix)) := by
  rw [spongeBytes, squeeze_fast_eq, spongeS_toState]

/-- cSHAKE256 (empty function name, 256-bit output) on the fast path: the
input list is copied once into a byte array; framing, padding, absorption and
squeezing never return to lists. -/
@[expose] def cshake256Fast (customization input : List UInt8) : List UInt8 :=
  if customization = [] then spongeBytes (pushList ByteArray.empty input) 0x1f
  else spongeBytes (pushList (pushList ByteArray.empty (customizationPrefix customization)) input)
    0x04

theorem cshake256Fast_eq (customization input : List UInt8) :
    cshake256Fast customization input = cshake256Bytes customization input := by
  unfold cshake256Fast cshake256Bytes
  by_cases h : customization = []
  · simp only [h, ite_true, sponge_fast_eq, pushList_data, empty_data, List.nil_append]
  · simp only [h, ite_false, sponge_fast_eq, pushList_data, empty_data, List.nil_append]


/-! ### Zero-Copy Direct `ByteArray` Absorption & `cshake256ByteArrayFast` -/

/-- Copy `k` bytes starting at `off` from borrowed `src` into `dst` without `List UInt8` conversion. -/
def copySlice (src : @& ByteArray) : Nat → Nat → ByteArray → ByteArray
  | _, 0, dst => dst
  | off, k + 1, dst => copySlice src (off + 1) k (dst.push (byteOr0 src off))

theorem emptyWithCapacity_data (cap : Nat) :
    (ByteArray.emptyWithCapacity cap).data.toList = [] := by rfl

theorem drop_take_succ (l : List UInt8) (off k : Nat) (h : off + (k + 1) ≤ l.length) :
    (l.drop off).take (k + 1) = l.getD off 0 :: (l.drop (off + 1)).take k := by
  have hoff : off < l.length := by omega
  rw [List.drop_eq_getElem_cons hoff, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hoff, Option.getD_some]
  rfl

theorem copySlice_data (src : ByteArray) (off k : Nat) (dst : ByteArray)
    (h : off + k ≤ src.size) :
    (copySlice src off k dst).data.toList =
      dst.data.toList ++ (src.data.toList.drop off).take k := by
  induction k generalizing off dst with
  | zero => simp [copySlice]
  | succ k ih =>
    have hlen : off + (k + 1) ≤ src.data.toList.length := by rwa [← size_eq_length]
    rw [copySlice, ih (off + 1) _ (by omega), push_data, List.append_assoc,
      List.singleton_append, ← getD_data, ← drop_take_succ _ _ _ hlen]

theorem absorbFrom_append_exact (k₁ k₂ : Nat) (st : State) (xs ys : List UInt8)
    (hxs : xs.length = k₁ * rateBytes) :
    absorbFrom (k₁ + k₂) st (xs ++ ys) = absorbFrom k₂ (absorbFrom k₁ st xs) ys := by
  induction k₁ generalizing st xs with
  | zero =>
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa [rateBytes] using hxs)
    subst hnil
    simp [absorbFrom]
  | succ k₁ ih =>
    have hge : rateBytes ≤ xs.length := by rw [hxs]; simp [Nat.succ_mul]
    rw [Nat.succ_add, absorbFrom, absorbFrom, List.take_append_of_le_length hge,
      List.drop_append_of_le_length hge]
    apply ih
    rw [List.length_drop, hxs]
    simp [Nat.succ_mul, rateBytes]

theorem take_le_take : ∀ (m n : Nat) (xs : List UInt8), m ≤ n → (xs.take n).take m = xs.take m
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, [], _ => rfl
  | m + 1, n + 1, x :: xs, h =>
    congrArg (x :: ·) (take_le_take m n xs (Nat.le_of_succ_le_succ h))

theorem absorbFrom_take_blocks (k : Nat) (st : State) (xs : List UInt8)
    (hle : k * rateBytes ≤ xs.length) :
    absorbFrom k st (xs.take (k * rateBytes)) = absorbFrom k st xs := by
  induction k generalizing st xs with
  | zero => rfl
  | succ k ih =>
    have hge : rateBytes ≤ k.succ * rateBytes := by simp [Nat.succ_mul]
    rw [absorbFrom, absorbFrom, take_le_take _ _ _ hge, List.drop_take]
    have hsub : k.succ * rateBytes - rateBytes = k * rateBytes := by
      simp [Nat.succ_mul, rateBytes]
    rw [hsub]
    apply ih
    simp only [rateBytes] at hle ⊢
    rw [List.length_drop]; omega

theorem padForRate_split_blocks (xs : List UInt8) (suffix : UInt8) :
    let full := xs.length / rateBytes
    padForRate xs suffix =
      xs.take (full * rateBytes) ++ padForRate (xs.drop (full * rateBytes)) suffix := by
  dsimp only
  have hrem_len : (xs.drop ((xs.length / rateBytes) * rateBytes)).length = xs.length % rateBytes := by
    rw [List.length_drop]
    have hdiv := Nat.div_add_mod xs.length rateBytes
    rw [Nat.mul_comm] at hdiv
    omega
  have hrem_lt : xs.length % rateBytes < rateBytes := Nat.mod_lt _ (by decide)
  have hmod_eq : (xs.drop ((xs.length / rateBytes) * rateBytes)).length % rateBytes =
      xs.length % rateBytes := by
    rw [hrem_len, Nat.mod_eq_of_lt hrem_lt]
  unfold padForRate
  rw [hmod_eq]
  dsimp only
  have hsplit : xs = xs.take ((xs.length / rateBytes) * rateBytes) ++
      xs.drop ((xs.length / rateBytes) * rateBytes) :=
    (List.take_append_drop _ _).symm
  by_cases hc : rateBytes - xs.length % rateBytes = 1
  · simp only [hc, ↓reduceIte]
    have h1 := congrArg (fun l => l ++ [suffix ^^^ (128 : UInt8)]) hsplit
    simpa only [List.append_assoc] using h1
  · simp only [hc, ↓reduceIte]
    have h1 := congrArg
      (fun l => l ++ [suffix] ++ List.replicate (rateBytes - xs.length % rateBytes - 2) 0 ++ [128])
      hsplit
    simpa only [List.append_assoc] using h1

theorem padForRate_short_length (xs : List UInt8) (suffix : UInt8) (h : xs.length < rateBytes) :
    (padForRate xs suffix).length = rateBytes := by
  unfold padForRate
  unfold rateBytes at h ⊢
  rw [Nat.mod_eq_of_lt h]
  dsimp only
  by_cases hc : 136 - xs.length = 1
  · simp only [hc, ↓reduceIte, List.length_append, List.length_singleton]
    omega
  · simp only [hc, ↓reduceIte, List.length_append, List.length_singleton, List.length_replicate]
    omega

theorem padForRate_append_aligned (pfx xs : List UInt8) (suffix : UInt8)
    (hpfx : pfx.length % rateBytes = 0) :
    padForRate (pfx ++ xs) suffix = pfx ++ padForRate xs suffix := by
  have hmod : (pfx ++ xs).length % rateBytes = xs.length % rateBytes := by
    rw [List.length_append, Nat.add_mod, hpfx, Nat.zero_add, Nat.mod_mod]
  unfold padForRate
  rw [hmod]
  dsimp only
  by_cases hc : rateBytes - xs.length % rateBytes = 1
  · simp only [hc, ↓reduceIte, List.append_assoc]
  · simp only [hc, ↓reduceIte, List.append_assoc]

/-- Streamed zero-copy absorption of borrowed `b : @& ByteArray`: reads all full 136-byte blocks
    straight from `b` via `absorbLoop` without copying `b`, and materializes only the single
    136-byte final padded block. -/
def absorbByteArray (b : @& ByteArray) (suffix : UInt8) (s : KState) : KState :=
  let full := b.size / rateBytes
  let rem := b.size % rateBytes
  let s1 := absorbLoop b full 0 s
  let tail := padBA (copySlice b (full * rateBytes) rem (ByteArray.emptyWithCapacity rateBytes)) suffix
  keccakS (xorBlockS s1 tail 0)

theorem absorbByteArray_toState (b : ByteArray) (suffix : UInt8) (s : KState) :
    (absorbByteArray b suffix s).toState =
      absorbFrom ((padForRate b.data.toList suffix).length / rateBytes)
        s.toState (padForRate b.data.toList suffix) := by
  unfold absorbByteArray
  dsimp only
  let L := b.data.toList
  have hbsize : b.size = L.length := size_eq_length b
  let full := b.size / rateBytes
  let rem := b.size % rateBytes
  have hfull_eq : full = L.length / rateBytes := by simp [full, hbsize]
  have hrem_eq : rem = L.length % rateBytes := by simp [rem, hbsize]
  have hdivmod : full * rateBytes + rem = b.size := by
    have h := Nat.div_add_mod b.size rateBytes
    rw [Nat.mul_comm] at h
    exact h
  let tail := padBA (copySlice b (full * rateBytes) rem (ByteArray.emptyWithCapacity rateBytes)) suffix
  have hdrop_len : (L.drop (full * rateBytes)).length = rem := by
    rw [List.length_drop, ← hbsize]
    omega
  have htail_list : tail.data.toList = padForRate (L.drop (full * rateBytes)) suffix := by
    simp only [tail, padBA_data, copySlice_data b (full * rateBytes) rem _ (by omega),
      emptyWithCapacity_data, List.nil_append]
    rw [List.take_of_length_le (by rw [hdrop_len]; exact Nat.le_refl _)]
  have hrem_lt : (L.drop (full * rateBytes)).length < rateBytes := by
    rw [hdrop_len, hrem_eq]
    exact Nat.mod_lt _ (by decide)
  have htail_len : tail.data.toList.length = rateBytes := by
    rw [htail_list]
    exact padForRate_short_length _ _ hrem_lt
  have hpad_split : padForRate L suffix = L.take (full * rateBytes) ++ tail.data.toList := by
    rw [htail_list, hfull_eq]
    exact padForRate_split_blocks L suffix
  have htake_len : (L.take (full * rateBytes)).length = full * rateBytes :=
    List.length_take_of_le (by rw [← hbsize]; omega)
  have hpad_blocks : (padForRate L suffix).length / rateBytes = full + 1 := by
    rw [hpad_split, List.length_append, htake_len, htail_len]
    have hpos : 0 < rateBytes := by decide
    rw [show full * rateBytes + rateBytes = (full + 1) * rateBytes by simp [Nat.add_mul],
      Nat.mul_div_cancel _ hpos]
  change (keccakS (xorBlockS (absorbLoop b full 0 s) tail 0)).toState =
    absorbFrom ((padForRate L suffix).length / rateBytes) s.toState (padForRate L suffix)
  rw [hpad_blocks, hpad_split, absorbFrom_append_exact full 1 s.toState _ _ htake_len,
    absorbFrom_take_blocks full s.toState L (by rw [← hbsize]; omega)]
  have hs1 : (absorbLoop b full 0 s).toState = absorbFrom full s.toState L := by
    simpa [L, List.drop_zero] using absorb_fast_eq b full 0 s
  rw [keccakF_fast_eq, xorBlockS_toState, hs1]
  simp only [absorbFrom, List.drop_zero, rateBytes]

/-- Build SP 800-185 `customizationPrefix` directly from a borrowed `ByteArray` without `c.data.toList`. -/
def customizationPrefixBA (c : @& ByteArray) : ByteArray :=
  let hdr := leftEncode rateBytes ++ encodeString ([] : List UInt8) ++ leftEncode (8 * c.size)
  let pfx := copySlice c 0 c.size (pushList (ByteArray.emptyWithCapacity (hdr.length + c.size + rateBytes)) hdr)
  let zeroCount := (rateBytes - pfx.size % rateBytes) % rateBytes
  pushZeros pfx zeroCount

theorem customizationPrefixBA_data (c : ByteArray) :
    (customizationPrefixBA c).data.toList = customizationPrefix c.data.toList := by
  unfold customizationPrefixBA customizationPrefix bytepad
  have h136 : ¬(rateBytes = 0) := by decide
  simp only [h136, ↓reduceIte]
  let hdr := leftEncode rateBytes ++ encodeString ([] : List UInt8) ++ leftEncode (8 * c.size)
  let pfx := copySlice c 0 c.size (pushList (ByteArray.emptyWithCapacity (hdr.length + c.size + rateBytes)) hdr)
  have hpfx : pfx.data.toList =
      leftEncode rateBytes ++ (encodeString ([] : List UInt8) ++ encodeString c.data.toList) := by
    dsimp only [pfx, hdr]
    rw [copySlice_data c 0 c.size _ (by omega), pushList_data, emptyWithCapacity_data, List.nil_append,
      List.drop_zero, size_eq_length, List.take_length]
    unfold encodeString
    simp only [List.append_assoc]
  change (pushZeros pfx ((rateBytes - pfx.size % rateBytes) % rateBytes)).data.toList = _
  rw [pushZeros_data, size_eq_length, hpfx]

theorem customizationPrefix_len_mod (xs : List UInt8) :
    (customizationPrefix xs).length % rateBytes = 0 := by
  unfold customizationPrefix bytepad rateBytes
  simp only [show ¬(136 = 0) by decide, ↓reduceIte, List.length_append, List.length_replicate]
  omega

/-- Push one 64-bit word as 8 little-endian bytes directly into `b : ByteArray`. -/
@[inline] def pushLaneLE (b : ByteArray) (w : UInt64) : ByteArray :=
  (((((((b.push (w >>> 0).toUInt8)
    |>.push (w >>> 8).toUInt8)
    |>.push (w >>> 16).toUInt8)
    |>.push (w >>> 24).toUInt8)
    |>.push (w >>> 32).toUInt8)
    |>.push (w >>> 40).toUInt8)
    |>.push (w >>> 48).toUInt8)
    |>.push (w >>> 56).toUInt8

/-- Squeeze the first 32 output bytes directly into a pre-sized `ByteArray` (`0` list allocations). -/
def squeezeByteArray (s : KState) : ByteArray :=
  pushLaneLE (pushLaneLE (pushLaneLE (pushLaneLE (ByteArray.emptyWithCapacity 32) s.a0) s.a1) s.a2) s.a3

theorem pushLaneLE_data (b : ByteArray) (w : UInt64) :
    (pushLaneLE b w).data.toList =
      b.data.toList ++
        [(w >>> 0).toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8,
         (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8] := by
  simp only [pushLaneLE, push_data, List.append_assoc, List.cons_append, List.nil_append]

theorem squeezeByteArray_data (s : KState) :
    (squeezeByteArray s).data.toList = squeezeS s := by
  simp only [squeezeByteArray, pushLaneLE_data, emptyWithCapacity_data, List.nil_append]
  rfl

@[simp] theorem squeezeByteArray_size (s : KState) : (squeezeByteArray s).size = 32 := by
  rw [size_eq_length, squeezeByteArray_data, squeeze_fast_eq, squeeze32_length]

/-- Unboxed `UInt64` base-256 little-endian digit extractor (`≤ 8` bytes, zero `Nat` division). -/
@[inline] def natBytesLEU64 : Nat → UInt64 → List UInt8
  | 0, _ => []
  | fuel + 1, v =>
    if v == 0 then [] else v.toUInt8 :: natBytesLEU64 fuel (v >>> 8)

theorem natBytesLEU64_eq : ∀ (fuel k : Nat) (v : UInt64),
    v.toNat < 256 ^ fuel → v.toNat ≤ k →
    natBytesLEU64 fuel v = natBytesLEAux k v.toNat
  | 0, k, v, hv, _ => by
    have hv0 : v.toNat = 0 := by simp at hv; exact hv
    cases k <;> simp [natBytesLEU64, natBytesLEAux, hv0]
  | fuel + 1, 0, v, _, hk => by
    have hv0 : v.toNat = 0 := by omega
    have hbeq : (v == 0) = true := by
      rw [beq_iff_eq]
      exact UInt64.toNat_inj.mp hv0
    simp [natBytesLEU64, natBytesLEAux, hbeq]
  | fuel + 1, k + 1, v, hv, hk => by
    by_cases hv0 : v.toNat = 0
    · have hbeq : (v == 0) = true := by
        rw [beq_iff_eq]
        exact UInt64.toNat_inj.mp hv0
      simp [natBytesLEU64, natBytesLEAux, hv0, hbeq]
    · have hbeq : (v == 0) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hv0 (by subst h; rfl)
      have hb : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := by
        apply UInt8.toNat_inj.mp
        simp [UInt8.toNat_ofNat']
      have hsh : (v >>> 8).toNat = v.toNat / 256 := by
        simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have hpow : 256 ^ (fuel + 1) = 256 ^ fuel * 256 := Nat.pow_succ ..
      have hdiv_lt : (v >>> 8).toNat < 256 ^ fuel := by
        rw [hsh]
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hv)
      have hdiv_le : (v >>> 8).toNat ≤ k := by rw [hsh]; omega
      simp only [natBytesLEU64, natBytesLEAux, hbeq, Bool.false_eq_true, ↓reduceIte, hv0, hb,
        natBytesLEU64_eq fuel k (v >>> 8) hdiv_lt hdiv_le, hsh]

/-- Peel 8 little-endian bytes of an unboxed `UInt64` word (`k` steps, emitting exact 8 bytes when non-final). -/
@[inline] def pushU64BytesLE : Nat → UInt64 → List UInt8 → List UInt8
  | 0, _, tail => tail
  | k + 1, v, tail => v.toUInt8 :: pushU64BytesLE k (v >>> 8) tail

theorem natBytesLEAux_fuel_irrel : ∀ (f₁ f₂ n : Nat), n ≤ f₁ → n ≤ f₂ →
    natBytesLEAux f₁ n = natBytesLEAux f₂ n
  | 0, f₂, n, h₁, _ => by
    have hn0 : n = 0 := by omega
    subst hn0; cases f₂ <;> simp [natBytesLEAux]
  | f₁ + 1, 0, n, _, h₂ => by
    have hn0 : n = 0 := by omega
    subst hn0; simp [natBytesLEAux]
  | f₁ + 1, f₂ + 1, n, h₁, h₂ => by
    by_cases hn0 : n = 0
    · simp [natBytesLEAux, hn0]
    · simp only [natBytesLEAux, hn0, ↓reduceIte]
      rw [natBytesLEAux_fuel_irrel f₁ f₂ (n / 256) (by omega) (by omega)]

theorem pushU64BytesLE_eq : ∀ (k f : Nat) (n : Nat),
    k ≤ 8 → 256 ^ k ≤ n → n ≤ f →
    pushU64BytesLE k (UInt64.ofNat (n % 256 ^ 8)) (natBytesLEAux (f - k) (n / 256 ^ k)) =
      natBytesLEAux f n := by
  intro k
  have hAux : ∀ (j m f : Nat) (w : UInt64),
      j ≤ 8 → w.toNat % 256 ^ j = m % 256 ^ j → 256 ^ j ≤ m → m ≤ f →
      pushU64BytesLE j w (natBytesLEAux (f - j) (m / 256 ^ j)) = natBytesLEAux f m := by
    intro j
    induction j with
    | zero =>
      intro m f _ _ _ _ _
      simp [pushU64BytesLE]
    | succ j ih =>
      intro m f w hj hmod hbig hmf
      cases f with
      | zero => omega
      | succ f =>
        have hm0 : m ≠ 0 := by
          have hp : 0 < 256 ^ (j + 1) := Nat.pow_pos (by decide)
          omega
        have hpow_j : 256 ^ (j + 1) = 256 * 256 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
        have hw_mod256 : w.toNat % 256 = m % 256 := by
          calc w.toNat % 256 = (w.toNat % 256 ^ (j + 1)) % 256 := by
                rw [hpow_j, Nat.mod_mul_right_mod]
            _ = (m % 256 ^ (j + 1)) % 256 := by rw [hmod]
            _ = m % 256 := by rw [hpow_j, Nat.mod_mul_right_mod]
        have hb : w.toUInt8 = UInt8.ofNat (m % 256) := by
          apply UInt8.toNat_inj.mp
          simp [UInt8.toNat_ofNat', hw_mod256]
        have hsh : (w >>> 8).toNat = w.toNat / 256 := by
          simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        have hw_div_mod : (w >>> 8).toNat % 256 ^ j = (m / 256) % 256 ^ j := by
          rw [hsh]
          let P := 256 ^ j
          have hP : 0 < P := Nat.pow_pos (show 0 < 256 by decide)
          have hdiv_mod : ∀ x : Nat, (x / 256) % P = (x % (256 * P)) / 256 := by
            intro x
            let qx := x / (256 * P)
            let rx := x % (256 * P)
            have hx : x = rx + 256 * (P * qx) := by
              dsimp only [qx, rx]
              rw [← Nat.mul_assoc, Nat.add_comm]
              exact (Nat.div_add_mod x (256 * P)).symm
            have hrx : rx < P * 256 := by
              dsimp only [rx]; rw [Nat.mul_comm]
              exact Nat.mod_lt x (Nat.mul_pos hP (show 0 < 256 by decide))
            have hrx_div : rx / 256 < P := (Nat.div_lt_iff_lt_mul (show 0 < 256 by decide)).mpr hrx
            change (x / 256) % P = rx / 256
            rw [hx, Nat.add_mul_div_left rx (P * qx) (show 0 < 256 by decide),
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrx_div]
          rw [hdiv_mod w.toNat, hdiv_mod m]
          dsimp only [P] at *
          rw [← hpow_j, hmod]
        have hm_div_big : 256 ^ j ≤ m / 256 := by
          rw [Nat.le_div_iff_mul_le (by decide), ← Nat.pow_succ]
          exact hbig
        have hsub : f + 1 - (j + 1) = f - j := by omega
        have hdiv2 : m / 256 ^ (j + 1) = (m / 256) / 256 ^ j := by
          rw [hpow_j, ← Nat.div_div_eq_div_mul]
        simp only [pushU64BytesLE, natBytesLEAux, hm0, ↓reduceIte, hb, hsub, hdiv2]
        congr 1
        exact ih (m / 256) f (w >>> 8) (by omega) hw_div_mod hm_div_big (by omega)
  intro f n hk hbig hnf
  have hpow8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hw_mod : (UInt64.ofNat (n % 256 ^ 8)).toNat % 256 ^ k = n % 256 ^ k := by
    rw [UInt64.toNat_ofNat', hpow8, Nat.mod_mod]
    have h8 : 256 ^ 8 = 256 ^ (8 - k) * 256 ^ k := by
      rw [← Nat.pow_add, show 8 - k + k = 8 by omega]
    rw [h8, Nat.mod_mul_left_mod]
  exact hAux k n f (UInt64.ofNat (n % 256 ^ 8)) hk hw_mod hbig hnf

/-- Fast `natBytesLE`: unboxed `UInt64` loop below `2^64`, and 64-bit limb shifts (`value >>> 64`)
for multi-word bignums without allocating `fuel - 1` GMP bignums per byte. -/
def natBytesLEFast (value : Nat) : List UInt8 :=
  if value < 18446744073709551616 then
    natBytesLEU64 8 (UInt64.ofNat value)
  else
    pushU64BytesLE 8 (UInt64.ofNat value) (natBytesLEFast (value >>> 64))
termination_by value
decreasing_by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self (by omega) (by decide)

theorem natBytesLEFast_eq (value : Nat) : natBytesLEFast value = natBytesLE value := by
  induction value using Nat.strongRecOn with
  | ind value ih =>
    unfold natBytesLEFast
    have hpow8 : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
    have h2_64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    by_cases hlt : value < 18446744073709551616
    · simp only [hlt, ↓reduceIte]
      have hu : (UInt64.ofNat value).toNat = value := by
        rw [UInt64.toNat_ofNat', h2_64]
        exact Nat.mod_eq_of_lt hlt
      rw [natBytesLEU64_eq 8 value (UInt64.ofNat value) (by rw [hu, hpow8]; exact hlt) (by omega),
        hu, natBytesLE]
    · simp only [hlt, ↓reduceIte]
      have hsh_lt : value >>> 64 < value := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_self (by omega) (by decide)
      have hsh_eq : value >>> 64 = value / 256 ^ 8 := by
        rw [Nat.shiftRight_eq_div_pow, h2_64, ← hpow8]
      have hu_eq : UInt64.ofNat value = UInt64.ofNat (value % 256 ^ 8) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', h2_64, ← hpow8, Nat.mod_mod]
      rw [ih (value >>> 64) hsh_lt, natBytesLE, hsh_eq, hu_eq,
        natBytesLEAux_fuel_irrel (value / 256 ^ 8) (value - 8) (value / 256 ^ 8)
          (Nat.le_refl _) (by rw [hpow8]; omega),
        pushU64BytesLE_eq 8 value value (Nat.le_refl 8) (by rw [hpow8]; omega) (Nat.le_refl _),
        natBytesLE]

@[csimp] theorem natBytesLE_eq_fast : @natBytesLE = @natBytesLEFast := by
  funext value
  exact (natBytesLEFast_eq value).symm

/-- Build `bytepad (encodeString n ‖ encodeString c) 136` directly in `ByteArray`. -/
def namedPrefixBA (name custom : @& ByteArray) : ByteArray :=
  let hdr1 := leftEncode rateBytes ++ leftEncode (8 * name.size)
  let hdr2 := leftEncode (8 * custom.size)
  let cap := hdr1.length + name.size + hdr2.length + custom.size + rateBytes
  let b1 := copySlice name 0 name.size (pushList (ByteArray.emptyWithCapacity cap) hdr1)
  let b2 := copySlice custom 0 custom.size (pushList b1 hdr2)
  let zeroCount := (rateBytes - b2.size % rateBytes) % rateBytes
  pushZeros b2 zeroCount

theorem namedPrefixBA_data (name custom : ByteArray) :
    (namedPrefixBA name custom).data.toList =
      bytepad (encodeString name.data.toList ++ encodeString custom.data.toList) rateBytes := by
  unfold namedPrefixBA bytepad
  have h136 : ¬(rateBytes = 0) := by decide
  simp only [h136, ↓reduceIte]
  let hdr1 := leftEncode rateBytes ++ leftEncode (8 * name.size)
  let hdr2 := leftEncode (8 * custom.size)
  let cap := hdr1.length + name.size + hdr2.length + custom.size + rateBytes
  let b1 := copySlice name 0 name.size (pushList (ByteArray.emptyWithCapacity cap) hdr1)
  let b2 := copySlice custom 0 custom.size (pushList b1 hdr2)
  have hb1 : b1.data.toList = leftEncode rateBytes ++ encodeString name.data.toList := by
    dsimp only [b1, hdr1]
    rw [copySlice_data name 0 name.size _ (by omega), pushList_data, emptyWithCapacity_data,
      List.nil_append, List.drop_zero, size_eq_length, List.take_length]
    simp [encodeString, List.append_assoc]
  have hb2 : b2.data.toList =
      leftEncode rateBytes ++ (encodeString name.data.toList ++ encodeString custom.data.toList) := by
    dsimp only [b2, hdr2]
    rw [copySlice_data custom 0 custom.size _ (by omega), pushList_data, hb1,
      List.drop_zero, size_eq_length, List.take_length]
    simp [encodeString, List.append_assoc]
  change (pushZeros b2 ((rateBytes - b2.size % rateBytes) % rateBytes)).data.toList = _
  rw [pushZeros_data, size_eq_length, hb2]

/-- Zero-copy `ByteArray` general `namedBytes` cSHAKE256. -/
def namedByteArrayFast (name custom input : @& ByteArray) : ByteArray :=
  if name.size == 0 && custom.size == 0 then
    squeezeByteArray (absorbByteArray input 0x1f zeroS)
  else
    let pfx := namedPrefixBA name custom
    let s0 := absorbLoop pfx (pfx.size / rateBytes) 0 zeroS
    squeezeByteArray (absorbByteArray input 0x04 s0)

theorem namedByteArrayFast_eq (n c m : ByteArray) :
    (namedByteArrayFast n c m).data.toList =
      namedBytes n.data.toList c.data.toList m.data.toList := by
  unfold namedByteArrayFast namedBytes paddedMessage
  by_cases hnc : n.data.toList = [] ∧ c.data.toList = []
  · have hb : (n.size == 0 && c.size == 0) = true := by
      simp [size_eq_length, hnc.1, hnc.2]
    simp only [hb, hnc.1, hnc.2, and_self, ↓reduceIte, squeezeByteArray_data, squeeze_fast_eq,
      absorbByteArray_toState, zeroS_toState, absorbPadded]
  · have hb : (n.size == 0 && c.size == 0) = false := by
      rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne,
        size_eq_length, size_eq_length]
      by_cases hn0 : n.data.toList.length = 0
      · right; exact fun hc0 => hnc ⟨List.eq_nil_of_length_eq_zero hn0, List.eq_nil_of_length_eq_zero hc0⟩
      · left; exact hn0
    simp only [hb, hnc, Bool.false_eq_true, ↓reduceIte, squeezeByteArray_data, squeeze_fast_eq,
      absorbByteArray_toState]
    let pfx := namedPrefixBA n c
    have hpfx_data : pfx.data.toList =
        bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes :=
      namedPrefixBA_data n c
    have hpfx_mod : (bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes).length % rateBytes = 0 := by
      unfold bytepad rateBytes
      simp only [show ¬(136 = 0) by decide, ↓reduceIte, List.length_append, List.length_replicate]
      omega
    have hpfx_blocks :
        (bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes).length =
          (pfx.size / rateBytes) * rateBytes := by
      rw [size_eq_length, hpfx_data]
      have h := Nat.div_add_mod (bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes).length rateBytes
      rw [hpfx_mod, Nat.add_zero, Nat.mul_comm] at h
      exact h.symm
    have hs0 : (absorbLoop pfx (pfx.size / rateBytes) 0 zeroS).toState =
        absorbFrom (pfx.size / rateBytes) zeroState
          (bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes) := by
      dsimp only [pfx]
      rw [absorb_fast_eq, zeroS_toState, List.drop_zero, hpfx_data]
    change squeeze32 (absorbFrom ((padForRate m.data.toList 4).length / rateBytes)
        (absorbLoop pfx (pfx.size / rateBytes) 0 zeroS).toState (padForRate m.data.toList 4)) = _
    rw [hs0, padForRate_append_aligned _ _ _ hpfx_mod, absorbPadded]
    have htot_div :
        ((bytepad (encodeString n.data.toList ++ encodeString c.data.toList) rateBytes ++
            padForRate m.data.toList 0x04).length) / rateBytes =
          pfx.size / rateBytes + (padForRate m.data.toList 0x04).length / rateBytes := by
      rw [List.length_append, hpfx_blocks]
      have hpos : 0 < rateBytes := by decide
      rw [Nat.mul_comm _ rateBytes, Nat.mul_add_div hpos]
    rw [htot_div, absorbFrom_append_exact (pfx.size / rateBytes) _ zeroState _ _ hpfx_blocks]

/-- **Zero-copy `ByteArray` cSHAKE256**: absorbs `customization` and `input` straight from borrowed
    `ByteArray`s into `KState` and squeezes 32 bytes directly into `ByteArray` without allocating
    any intermediate `List UInt8`s or copying `input`. -/
@[expose] def cshake256ByteArrayFast (customization input : @& ByteArray) : ByteArray :=
  if customization.size == 0 then
    squeezeByteArray (absorbByteArray input 0x1f zeroS)
  else
    let pfx := customizationPrefixBA customization
    let s0 := absorbLoop pfx (pfx.size / rateBytes) 0 zeroS
    squeezeByteArray (absorbByteArray input 0x04 s0)

@[simp] theorem cshake256ByteArrayFast_size (c m : ByteArray) :
    (cshake256ByteArrayFast c m).size = 32 := by
  unfold cshake256ByteArrayFast
  split <;> simp

theorem cshake256ByteArrayFast_eq (c m : ByteArray) :
    (cshake256ByteArrayFast c m).data.toList = cshake256Bytes c.data.toList m.data.toList := by
  unfold cshake256ByteArrayFast cshake256Bytes
  by_cases hc : c.data.toList = []
  · have hsize0 : (c.size == 0) = true := by
      rw [beq_iff_eq, size_eq_length, hc]; rfl
    simp only [hsize0, hc, ↓reduceIte, squeezeByteArray_data, squeeze_fast_eq,
      absorbByteArray_toState, zeroS_toState, absorbPadded]
  · have hsizeN : (c.size == 0) = false := by
      rw [beq_eq_false_iff_ne, size_eq_length]
      exact fun h0 => hc (List.eq_nil_of_length_eq_zero h0)
    simp only [hsizeN, hc, Bool.false_eq_true, ↓reduceIte, squeezeByteArray_data, squeeze_fast_eq,
      absorbByteArray_toState]
    let pfx := customizationPrefixBA c
    have hpfx_data : pfx.data.toList = customizationPrefix c.data.toList := customizationPrefixBA_data c
    have hpfx_mod : (customizationPrefix c.data.toList).length % rateBytes = 0 :=
      customizationPrefix_len_mod c.data.toList
    have hpfx_blocks : (customizationPrefix c.data.toList).length =
        (pfx.size / rateBytes) * rateBytes := by
      rw [size_eq_length, hpfx_data]
      have h := Nat.div_add_mod (customizationPrefix c.data.toList).length rateBytes
      rw [hpfx_mod, Nat.add_zero, Nat.mul_comm] at h
      exact h.symm
    have hs0 : (absorbLoop pfx (pfx.size / rateBytes) 0 zeroS).toState =
        absorbFrom (pfx.size / rateBytes) zeroState (customizationPrefix c.data.toList) := by
      dsimp only [pfx]
      rw [absorb_fast_eq, zeroS_toState, List.drop_zero, hpfx_data]
    change squeeze32 (absorbFrom ((padForRate m.data.toList 4).length / rateBytes)
        (absorbLoop pfx (pfx.size / rateBytes) 0 zeroS).toState (padForRate m.data.toList 4)) =
      squeeze32 (absorbPadded (padForRate (customizationPrefix c.data.toList ++ m.data.toList) 4))
    rw [hs0, padForRate_append_aligned _ _ _ hpfx_mod, absorbPadded]
    have htot_div : ((customizationPrefix c.data.toList ++ padForRate m.data.toList 0x04).length) / rateBytes =
        pfx.size / rateBytes + (padForRate m.data.toList 0x04).length / rateBytes := by
      rw [List.length_append, hpfx_blocks]
      have hpos : 0 < rateBytes := by decide
      rw [Nat.mul_comm _ rateBytes, Nat.mul_add_div hpos]
    rw [htot_div, absorbFrom_append_exact (pfx.size / rateBytes) _ zeroState _ _ hpfx_blocks]

/-! ## Attachment -/

/-- The compiled Host absorbs through the word permutation. -/
@[csimp] theorem absorbPadded_eq_fast : absorbPadded = absorbPaddedFast := by
  funext padded
  exact (absorbPadded_fast_eq padded).symm

/-- The fast path is the specification. It is no longer the `@[csimp]` attachment: the compiled
`cshake256Bytes` is the kernel seam `Native.cshake256Native` (`Obend.Digest.Cshake256.Seam`,
`cshake256Bytes_eq_native`), whose Lean body is this fast path; a module importing only this
file compiles against the list definitions. -/
theorem cshake256Bytes_eq_fast : cshake256Bytes = cshake256Fast := by
  funext customization input
  exact (cshake256Fast_eq customization input).symm

end Obend.Digest.Cshake256.Fast

end