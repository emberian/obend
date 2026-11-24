module
/-
# `ObendKeccakSpecWeld` — Welding Extracted `obend-keccak` MIR to `Obend.Digest.Cshake256` & `Kmac256`

Bridges the Charon + Aeneas extracted Rust MIR of `crates/obend-keccak` (`ObendKeccak.Funs`) directly
to Obend's canonical cryptographic specifications (`Obend.Digest.Cshake256.Spec`,
`Obend.Digest.Cshake256.Fast`, and `Obend.Digest.Kmac256`) with `0 sorry`, `0 axiom`, and
`0 Classical.choice`:

1. **FIPS 202 Constant & Offset Table Welds**:
   - `roundConstants_weld`: `KECCAK_ROUND_CONSTANTS` matches `Obend.Digest.Cshake256.roundConstants`.
   - `rotationOffsets_weld`: `KECCAK_ROTATION_OFFSETS` matches `Obend.Digest.Cshake256.rotationOffsets`.
2. **Exact Single-Round & Universal 24-Round `Keccak-f[1600]` Spec Weld**:
   - `keccak_loop_body_eq_roundS`: one iteration of the extracted MIR `keccak_f1600_loop.body`
     (theta, rho, pi, chi, iota) equals `Obend.Digest.Cshake256.Fast.roundS` across all 25 lanes.
   - `keccak_f1600_eq_keccakS`: the 24-round MIR `keccak_f1600` equals `Fast.keccakS` on every `KState`.
   - `keccak_f1600_refines_spec`: **for every 25-lane array `state : Array Std.U64 25#usize`
     (all $2^{1600}$ states, zero preconditions)**, `obend_keccak.keccak_f1600 state` evaluates to
     `.ok out` with `mirToSpecState out = Obend.Digest.Cshake256.keccakF1600 (mirToSpecState state)`.
3. **NIST SP 800-185 `encoded_width`, `left_encode`, and `right_encode` Spec Welds**:
   - `encoded_width_refines_spec`: for every `value : Std.U64`, `encoded_width value` equals
     `(Obend.Digest.Cshake256.natBytesBE value.val).length` (`1 .. 8`).
   - `left_encode_refines_spec`: for every `value : Std.U64` and buffer `buf`, `left_encode value buf`
     writes the exact byte sequence `Obend.Digest.Cshake256.leftEncode value.val`.
   - `right_encode_refines_spec`: for every `value : Std.U64` and buffer `buf`, `right_encode value buf`
     writes the exact byte sequence `Obend.Digest.Kmac256.rightEncode value.val`.
4. **SP 800-185 §3.3 Empty-Customization Fallback & 32-Byte Squeeze Weld**:
   - `cshake256_empty_eq_shake256_mir`: `Cshake256.new empty empty = Shake256.new` and
     `Cshake256.customized empty = Shake256.new`.
   - `squeeze_loop_32_refines_spec`: squeezing 32 bytes from any rate-aligned `136`-byte-rate state
     produces `Obend.Digest.Cshake256.squeeze32 (mirToSpecState lanes)`.
-/

public import ObendKeccakMirProofs
public import Obend.Digest.Cshake256.Spec
public import Obend.Digest.Cshake256.Fast
public import Obend.Digest.Kmac256
import all ObendKeccak.Types
import all ObendKeccak.Funs
import all ObendKeccakMirProofs
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Kmac256

public section

namespace ObendKeccak.SpecWeld

open Aeneas Aeneas.Std Result ControlFlow Error
open obend_keccak
open ObendKeccak.MirProofs
open Obend.Digest.Cshake256
open Obend.Digest.Cshake256.Fast

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## 1. State & Byte Representations Between Extracted MIR and `Obend.Digest` -/

/-- Embed `Obend.Digest.Cshake256.Fast.KState` into the extracted 25-lane MIR array. -/
@[expose] def kstateToMir (s : KState) : Aeneas.Std.Array Std.U64 25#usize :=
  Aeneas.Std.Array.make 25#usize
    [ ⟨s.a0.toBitVec⟩, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩
    , ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩
    , ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩
    , ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩
    , ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩ ]

/-- Project an extracted 25-lane MIR array into `KState`. -/
@[expose] def mirToKState (a : Aeneas.Std.Array Std.U64 25#usize) : KState :=
  let laneAtIdx (i : Nat) : UInt64 := UInt64.ofBitVec (a.val.getD i 0#u64).bv
  ⟨ laneAtIdx 0, laneAtIdx 1, laneAtIdx 2, laneAtIdx 3, laneAtIdx 4
  , laneAtIdx 5, laneAtIdx 6, laneAtIdx 7, laneAtIdx 8, laneAtIdx 9
  , laneAtIdx 10, laneAtIdx 11, laneAtIdx 12, laneAtIdx 13, laneAtIdx 14
  , laneAtIdx 15, laneAtIdx 16, laneAtIdx 17, laneAtIdx 18, laneAtIdx 19
  , laneAtIdx 20, laneAtIdx 21, laneAtIdx 22, laneAtIdx 23, laneAtIdx 24 ⟩

/-- Project an extracted 25-lane MIR array directly to `Obend.Digest.Cshake256.State` (`Array (BitVec 64)`). -/
@[expose] def mirToSpecState (a : Aeneas.Std.Array Std.U64 25#usize) : State :=
  (mirToKState a).toState

/-- Convert extracted `List Std.U8` bytes into `List UInt8`. -/
@[expose] def mirBytesToUInt8 (xs : List Std.U8) : List UInt8 :=
  xs.map (fun b => UInt8.ofBitVec b.bv)

theorem kstateToMir_mirToKState (a : Aeneas.Std.Array Std.U64 25#usize) :
    kstateToMir (mirToKState a) = a := by
  rcases a with ⟨xs, hlen⟩
  rw [usize_ofNat_val 25 (by decide)] at hlen
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4,
    _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, _ | ⟨x9,
    _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14,
    _ | ⟨x15, _ | ⟨x16, _ | ⟨x17, _ | ⟨x18, _ | ⟨x19,
    _ | ⟨x20, _ | ⟨x21, _ | ⟨x22, _ | ⟨x23, _ | ⟨x24, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at hlen
  subst hlen
  have hu (u : Std.U64) : (⟨u.bv⟩ : Std.U64) = u := by cases u; rfl
  apply Aeneas.Std.Array.ext
  simp [kstateToMir, mirToKState, Aeneas.Std.Array.make, UInt64.toBitVec_ofBitVec, hu]

theorem mirToSpecState_kstateToMir (s : KState) :
    mirToSpecState (kstateToMir s) = s.toState := by
  simp [mirToSpecState, mirToKState, kstateToMir, KState.toState, Aeneas.Std.Array.make]

/-! ## 2. FIPS 202 Constant & Offset Table Welds -/

theorem roundConstants_weld :
    obend_keccak.KECCAK_ROUND_CONSTANTS.val.map UScalar.bv = roundConstants := by
  unfold obend_keccak.KECCAK_ROUND_CONSTANTS roundConstants
  rfl

theorem rotationOffsets_weld :
    obend_keccak.KECCAK_ROTATION_OFFSETS.val.map UScalar.val = rotationOffsets.toList := by
  unfold obend_keccak.KECCAK_ROTATION_OFFSETS rotationOffsets
  rfl

private theorem mir_rc_eq_fast_rc (r : Nat) (hr : r < 24) :
    obend_keccak.KECCAK_ROUND_CONSTANTS.val.getD r 0#u64 =
      ⟨(roundConstantsS.getD r 0).toBitVec⟩ := by
  unfold obend_keccak.KECCAK_ROUND_CONSTANTS roundConstantsS roundConstants
  revert r
  decide

/-! ## 3. Single-Round & 24-Round `Keccak-f[1600]` Spec Weld -/

private def kstateTuple (s : KState) : Lanes25Tuple :=
  ( ⟨s.a0.toBitVec⟩, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩
  , ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩
  , ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩
  , ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩
  , ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩ )

def kstateLoopState (s : KState) (r : Std.Usize) :
    Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
    Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
    Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
    Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
    Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.Usize :=
  ( ⟨s.a0.toBitVec⟩, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩
  , ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩
  , ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩
  , ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩
  , ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩
  , r )

private theorem col_u64_eq (x0 x1 x2 x3 x4 : UInt64) :
    (((((⟨x0.toBitVec⟩ : Std.U64) ^^^ ⟨x1.toBitVec⟩) ^^^ ⟨x2.toBitVec⟩) ^^^ ⟨x3.toBitVec⟩) ^^^
      ⟨x4.toBitVec⟩) =
    ⟨(((0 : UInt64) ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4)).toBitVec⟩ := by
  apply UScalar.ext
  simp only [UScalar.bv_xor, UInt64.toBitVec_xor, u64_zero_toBitVec, zeroLane, BitVec.zero_xor]

private theorem delta_u64_eq (cA cB : UInt64) :
    (⟨cA.toBitVec⟩ : Std.U64) ^^^ core.num.U64.rotate_left ⟨cB.toBitVec⟩ 1#u32 =
      ⟨(cA ^^^ rotlK cB 1 63).toBitVec⟩ := by
  apply UScalar.ext
  simp only [UScalar.bv_xor, UInt64.toBitVec_xor, rotlK_1, core.num.U64.rotate_left]
  rfl

private theorem rho0_eq (x : UInt64) :
    core.num.U64.rotate_left ⟨x.toBitVec⟩ 0#u32 = ⟨x.toBitVec⟩ := by
  apply UScalar.ext
  change x.toBitVec.rotateLeft 0 = x.toBitVec
  exact bv_rotateLeft_zero x.toBitVec

private theorem rhoK_eq (x : UInt64) (k j : Nat) (hk : 0 < k) (hk64 : k < 64) (hj : k + j = 64) :
    core.num.U64.rotate_left ⟨x.toBitVec⟩ (UScalar.ofNat .U32 k) =
      ⟨(rotlK x (UInt64.ofNat k) (UInt64.ofNat j)).toBitVec⟩ := by
  apply UScalar.ext
  have hmod : (UScalar.ofNat .U32 k).val % 64 = k := by
    rw [u32_ofNat_val k (by omega), Nat.mod_eq_of_lt hk64]
  change x.toBitVec.rotateLeft ((UScalar.ofNat .U32 k).val % 64) = _
  rw [hmod, rotlK_toBitVec x k j hk hk64 hj]

/-- **Exact Single-Round MIR Equivalence (`keccak_loop_body_eq_roundS`)**:
    For every state `s : KState` and round index `r < 24`, one iteration of the extracted MIR
    `keccak_f1600_loop.body` computes `Obend.Digest.Cshake256.Fast.roundS s rc` across all 25 lanes
    and advances the round counter to `r + 1`. -/
theorem keccak_loop_body_eq_roundS (s : KState) (r : Nat) (hr : r < 24) :
    obend_keccak.keccak_f1600_loop.body
      ⟨s.a0.toBitVec⟩ ⟨s.a1.toBitVec⟩ ⟨s.a2.toBitVec⟩ ⟨s.a3.toBitVec⟩ ⟨s.a4.toBitVec⟩
      ⟨s.a5.toBitVec⟩ ⟨s.a6.toBitVec⟩ ⟨s.a7.toBitVec⟩ ⟨s.a8.toBitVec⟩ ⟨s.a9.toBitVec⟩
      ⟨s.a10.toBitVec⟩ ⟨s.a11.toBitVec⟩ ⟨s.a12.toBitVec⟩ ⟨s.a13.toBitVec⟩ ⟨s.a14.toBitVec⟩
      ⟨s.a15.toBitVec⟩ ⟨s.a16.toBitVec⟩ ⟨s.a17.toBitVec⟩ ⟨s.a18.toBitVec⟩ ⟨s.a19.toBitVec⟩
      ⟨s.a20.toBitVec⟩ ⟨s.a21.toBitVec⟩ ⟨s.a22.toBitVec⟩ ⟨s.a23.toBitVec⟩ ⟨s.a24.toBitVec⟩
      (UScalar.ofNat .Usize r) =
    .ok (.cont (kstateLoopState (roundS s (roundConstantsS.getD r 0))
                  (UScalar.ofNat .Usize (r + 1)))) := by
  have hrlt : UScalar.ofNat .Usize r < 24#usize := by
    rw [UScalar.lt_iff_val, usize_ofNat_val r (by omega), usize_ofNat_val 24 (by decide)]
    exact hr
  have hrc : Aeneas.Std.Array.index_usize obend_keccak.KECCAK_ROUND_CONSTANTS (UScalar.ofNat .Usize r) =
      .ok ⟨(roundConstantsS.getD r 0).toBitVec⟩ := by
    rw [keccak_round_constants_index r hr, mir_rc_eq_fast_rc r hr]
  have hadd := checked_add_ofNat_usize r (by omega)
  unfold obend_keccak.keccak_f1600_loop.body
  simp only [hrlt, ite_true, bind_eq_result_bind, lift_eq_ok, result_bind_ok, hrc, hadd]
  rw [col_u64_eq s.a0 s.a5 s.a10 s.a15 s.a20,
      col_u64_eq s.a1 s.a6 s.a11 s.a16 s.a21,
      col_u64_eq s.a2 s.a7 s.a12 s.a17 s.a22,
      col_u64_eq s.a3 s.a8 s.a13 s.a18 s.a23,
      col_u64_eq s.a4 s.a9 s.a14 s.a19 s.a24]
  rw [delta_u64_eq, delta_u64_eq, delta_u64_eq, delta_u64_eq, delta_u64_eq]
  have hxor_u64 (a b : UInt64) : (⟨a.toBitVec⟩ : Std.U64) ^^^ ⟨b.toBitVec⟩ = ⟨(a ^^^ b).toBitVec⟩ :=
    UScalar.ext (UInt64.toBitVec_xor a b).symm
  simp only [hxor_u64]
  let t := thetaS s
  change Result.ok (ControlFlow.cont (
    let b00 := core.num.U64.rotate_left ⟨t.a0.toBitVec⟩ 0#u32
    let b02 := core.num.U64.rotate_left ⟨t.a1.toBitVec⟩ 1#u32
    let b04 := core.num.U64.rotate_left ⟨t.a2.toBitVec⟩ 62#u32
    let b01 := core.num.U64.rotate_left ⟨t.a3.toBitVec⟩ 28#u32
    let b03 := core.num.U64.rotate_left ⟨t.a4.toBitVec⟩ 27#u32
    let b13 := core.num.U64.rotate_left ⟨t.a5.toBitVec⟩ 36#u32
    let b10 := core.num.U64.rotate_left ⟨t.a6.toBitVec⟩ 44#u32
    let b12 := core.num.U64.rotate_left ⟨t.a7.toBitVec⟩ 6#u32
    let b14 := core.num.U64.rotate_left ⟨t.a8.toBitVec⟩ 55#u32
    let b11 := core.num.U64.rotate_left ⟨t.a9.toBitVec⟩ 20#u32
    let b21 := core.num.U64.rotate_left ⟨t.a10.toBitVec⟩ 3#u32
    let b23 := core.num.U64.rotate_left ⟨t.a11.toBitVec⟩ 10#u32
    let b20 := core.num.U64.rotate_left ⟨t.a12.toBitVec⟩ 43#u32
    let b22 := core.num.U64.rotate_left ⟨t.a13.toBitVec⟩ 25#u32
    let b24 := core.num.U64.rotate_left ⟨t.a14.toBitVec⟩ 39#u32
    let b34 := core.num.U64.rotate_left ⟨t.a15.toBitVec⟩ 41#u32
    let b31 := core.num.U64.rotate_left ⟨t.a16.toBitVec⟩ 45#u32
    let b33 := core.num.U64.rotate_left ⟨t.a17.toBitVec⟩ 15#u32
    let b30 := core.num.U64.rotate_left ⟨t.a18.toBitVec⟩ 21#u32
    let b32 := core.num.U64.rotate_left ⟨t.a19.toBitVec⟩ 8#u32
    let b42 := core.num.U64.rotate_left ⟨t.a20.toBitVec⟩ 18#u32
    let b44 := core.num.U64.rotate_left ⟨t.a21.toBitVec⟩ 2#u32
    let b41 := core.num.U64.rotate_left ⟨t.a22.toBitVec⟩ 61#u32
    let b43 := core.num.U64.rotate_left ⟨t.a23.toBitVec⟩ 56#u32
    let b40 := core.num.U64.rotate_left ⟨t.a24.toBitVec⟩ 14#u32
    let rc := roundConstantsS.getD r 0
    ( (b00 ^^^ ((~~~b10) &&& b20)) ^^^ (⟨rc.toBitVec⟩ : Std.U64)
    , b10 ^^^ ((~~~b20) &&& b30)
    , b20 ^^^ ((~~~b30) &&& b40)
    , b30 ^^^ ((~~~b40) &&& b00)
    , b40 ^^^ ((~~~b00) &&& b10)
    , b01 ^^^ ((~~~b11) &&& b21)
    , b11 ^^^ ((~~~b21) &&& b31)
    , b21 ^^^ ((~~~b31) &&& b41)
    , b31 ^^^ ((~~~b41) &&& b01)
    , b41 ^^^ ((~~~b01) &&& b11)
    , b02 ^^^ ((~~~b12) &&& b22)
    , b12 ^^^ ((~~~b22) &&& b32)
    , b22 ^^^ ((~~~b32) &&& b42)
    , b32 ^^^ ((~~~b42) &&& b02)
    , b42 ^^^ ((~~~b02) &&& b12)
    , b03 ^^^ ((~~~b13) &&& b23)
    , b13 ^^^ ((~~~b23) &&& b33)
    , b23 ^^^ ((~~~b33) &&& b43)
    , b33 ^^^ ((~~~b43) &&& b03)
    , b43 ^^^ ((~~~b03) &&& b13)
    , b04 ^^^ ((~~~b14) &&& b24)
    , b14 ^^^ ((~~~b24) &&& b34)
    , b24 ^^^ ((~~~b34) &&& b44)
    , b34 ^^^ ((~~~b44) &&& b04)
    , b44 ^^^ ((~~~b04) &&& b14)
    , UScalar.ofNat .Usize (r + 1) ))) = _
  dsimp only
  rw [rho0_eq t.a0,
      rhoK_eq t.a1 1 63 (by decide) (by decide) (by decide),
      rhoK_eq t.a2 62 2 (by decide) (by decide) (by decide),
      rhoK_eq t.a3 28 36 (by decide) (by decide) (by decide),
      rhoK_eq t.a4 27 37 (by decide) (by decide) (by decide),
      rhoK_eq t.a5 36 28 (by decide) (by decide) (by decide),
      rhoK_eq t.a6 44 20 (by decide) (by decide) (by decide),
      rhoK_eq t.a7 6 58 (by decide) (by decide) (by decide),
      rhoK_eq t.a8 55 9 (by decide) (by decide) (by decide),
      rhoK_eq t.a9 20 44 (by decide) (by decide) (by decide),
      rhoK_eq t.a10 3 61 (by decide) (by decide) (by decide),
      rhoK_eq t.a11 10 54 (by decide) (by decide) (by decide),
      rhoK_eq t.a12 43 21 (by decide) (by decide) (by decide),
      rhoK_eq t.a13 25 39 (by decide) (by decide) (by decide),
      rhoK_eq t.a14 39 25 (by decide) (by decide) (by decide),
      rhoK_eq t.a15 41 23 (by decide) (by decide) (by decide),
      rhoK_eq t.a16 45 19 (by decide) (by decide) (by decide),
      rhoK_eq t.a17 15 49 (by decide) (by decide) (by decide),
      rhoK_eq t.a18 21 43 (by decide) (by decide) (by decide),
      rhoK_eq t.a19 8 56 (by decide) (by decide) (by decide),
      rhoK_eq t.a20 18 46 (by decide) (by decide) (by decide),
      rhoK_eq t.a21 2 62 (by decide) (by decide) (by decide),
      rhoK_eq t.a22 61 3 (by decide) (by decide) (by decide),
      rhoK_eq t.a23 56 8 (by decide) (by decide) (by decide),
      rhoK_eq t.a24 14 50 (by decide) (by decide) (by decide)]
  rfl

private def roundPrefix (s0 : KState) : Nat → KState
  | 0 => s0
  | k + 1 => roundS (roundPrefix s0 k) (roundConstantsS.getD k 0)

private theorem roundPrefix_24_eq_keccakS (s0 : KState) :
    roundPrefix s0 24 = keccakS s0 := by
  unfold keccakS roundConstantsS roundConstants
  rfl

/-- **24-Round Word-Level MIR Equivalence (`keccak_f1600_eq_keccakS`)**:
    The extracted Rust MIR `obend_keccak::keccak_f1600` computes `Obend.Digest.Cshake256.Fast.keccakS`
    on every 25-lane state `s : KState`. -/
theorem keccak_f1600_eq_keccakS (s : KState) :
    obend_keccak.keccak_f1600 (kstateToMir s) = .ok (kstateToMir (keccakS s)) := by
  let body := fun (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
                   x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, r) =>
    obend_keccak.keccak_f1600_loop.body
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
      x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r
  let st (k : Nat) := kstateLoopState (roundPrefix s k) (UScalar.ofNat .Usize k)
  have hstep : ∀ k, k < 24 → body (st k) = .ok (.cont (st (k + 1))) := by
    intro k hk
    simpa only [body, st, kstateLoopState, roundPrefix] using
      keccak_loop_body_eq_roundS (roundPrefix s k) k hk
  have hdone : body (st 24) = .ok (.done (kstateTuple (keccakS s))) := by
    have hnot : ¬ (UScalar.ofNat .Usize 24 < 24#usize) := by decide
    simp only [body, st, kstateLoopState, kstateTuple, obend_keccak.keccak_f1600_loop.body,
      hnot, ite_false, roundPrefix_24_eq_keccakS]
  have hloop :
      obend_keccak.keccak_f1600_loop
        ⟨s.a0.toBitVec⟩ ⟨s.a1.toBitVec⟩ ⟨s.a2.toBitVec⟩ ⟨s.a3.toBitVec⟩ ⟨s.a4.toBitVec⟩
        ⟨s.a5.toBitVec⟩ ⟨s.a6.toBitVec⟩ ⟨s.a7.toBitVec⟩ ⟨s.a8.toBitVec⟩ ⟨s.a9.toBitVec⟩
        ⟨s.a10.toBitVec⟩ ⟨s.a11.toBitVec⟩ ⟨s.a12.toBitVec⟩ ⟨s.a13.toBitVec⟩ ⟨s.a14.toBitVec⟩
        ⟨s.a15.toBitVec⟩ ⟨s.a16.toBitVec⟩ ⟨s.a17.toBitVec⟩ ⟨s.a18.toBitVec⟩ ⟨s.a19.toBitVec⟩
        ⟨s.a20.toBitVec⟩ ⟨s.a21.toBitVec⟩ ⟨s.a22.toBitVec⟩ ⟨s.a23.toBitVec⟩ ⟨s.a24.toBitVec⟩
        0#usize = .ok (kstateTuple (keccakS s)) := by
    unfold obend_keccak.keccak_f1600_loop
    exact loop_det_steps body st (kstateTuple (keccakS s)) 24 (by decide) hstep hdone
  unfold obend_keccak.keccak_f1600
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 0#usize = .ok ⟨s.a0.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 1#usize = .ok ⟨s.a1.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 2#usize = .ok ⟨s.a2.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 3#usize = .ok ⟨s.a3.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 4#usize = .ok ⟨s.a4.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 5#usize = .ok ⟨s.a5.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 6#usize = .ok ⟨s.a6.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 7#usize = .ok ⟨s.a7.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 8#usize = .ok ⟨s.a8.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 9#usize = .ok ⟨s.a9.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 10#usize = .ok ⟨s.a10.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 11#usize = .ok ⟨s.a11.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 12#usize = .ok ⟨s.a12.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 13#usize = .ok ⟨s.a13.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 14#usize = .ok ⟨s.a14.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 15#usize = .ok ⟨s.a15.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 16#usize = .ok ⟨s.a16.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 17#usize = .ok ⟨s.a17.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 18#usize = .ok ⟨s.a18.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 19#usize = .ok ⟨s.a19.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 20#usize = .ok ⟨s.a20.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 21#usize = .ok ⟨s.a21.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 22#usize = .ok ⟨s.a22.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 23#usize = .ok ⟨s.a23.toBitVec⟩)
  apply bind_ok_step (rfl : Aeneas.Std.Array.index_usize (kstateToMir s) 24#usize = .ok ⟨s.a24.toBitVec⟩)
  apply bind_ok_step hloop
  rfl

private theorem getElem?_ofFn_go {α : Type} {n : Nat} (f : Fin n → α) (k : Nat) :
    ∀ (acc : _root_.Array α) (_hk : acc.size + k = n) (hkn : k ≤ n) (i : Nat) (hi : i < n),
      (_root_.Array.ofFn.go f acc k hkn)[i]? =
      if hlt : i < acc.size then some (acc[i]'hlt) else some (f ⟨i, hi⟩) := by
  induction k with
  | zero =>
    intro acc _hk _ i hi
    have hlt : i < acc.size := by omega
    rw [_root_.Array.ofFn.go.eq_2, _root_.Array.getElem?_eq_getElem hlt,
        dite_eq_left_of_eq_true (eq_true hlt)]
  | succ k' ih =>
    intro acc _hk _ i hi
    rw [_root_.Array.ofFn.go.eq_1,
        ih (acc.push (f ⟨n - k' - 1, by omega⟩)) (by rw [_root_.Array.size_push]; omega) (by omega) i hi]
    simp only [_root_.Array.size_push]
    if hlt : i < acc.size then
      have hlt1 : i < acc.size + 1 := by omega
      simp only [hlt, hlt1, ↓reduceDIte, _root_.Array.getElem_push_lt hlt]
    else
      simp only [hlt, ↓reduceDIte]
      if hlt1 : i < acc.size + 1 then
        have heq : i = acc.size := by omega
        subst heq
        simp only [hlt1, ↓reduceDIte, _root_.Array.getElem_push_eq]
        congr 2
        apply Fin.ext
        dsimp only
        omega
      else
        simp only [hlt1, ↓reduceDIte]

private theorem getElem?_ofFn_c {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) :
    (_root_.Array.ofFn f)[i]? = some (f ⟨i, hi⟩) := by
  rw [_root_.Array.ofFn,
      getElem?_ofFn_go f n (_root_.Array.emptyWithCapacity n) (by simp) (Nat.le_refl n) i hi]
  simp

private theorem theta_getElem_c (st : _root_.Array Lane) (i : Nat) (hi : i < (theta st).size) :
    (theta st)[i] =
      lane st (i % 5) (i / 5) ^^^ xorColumn st ((i % 5 + 4) % 5) ^^^
        (xorColumn st ((i % 5 + 1) % 5)).rotateLeft 1 := by
  have hi25 : i < 25 := by simpa only [theta, _root_.Array.size_ofFn] using hi
  apply Option.some.inj
  rw [← _root_.Array.getElem?_eq_getElem hi, theta, getElem?_ofFn_c _ i hi25]
  dsimp only
  rw [xorColumn_mod st (i % 5 + 4), xorColumn_mod st (i % 5 + 1)]

private theorem chi_getElem_c (st : _root_.Array Lane) (i : Nat) (hi : i < (chi st).size) :
    (chi st)[i] =
      lane st (i % 5) (i / 5) ^^^
        ((~~~lane st (i % 5 + 1) (i / 5)) &&& lane st (i % 5 + 2) (i / 5)) := by
  have hi25 : i < 25 := by simpa only [chi, _root_.Array.size_ofFn] using hi
  apply Option.some.inj
  rw [← _root_.Array.getElem?_eq_getElem hi, chi, getElem?_ofFn_c _ i hi25]

private theorem theta_col_c {x0 x1 x2 x3 x4 : UInt64} {st : State} {x : Nat}
    (h0 : x0.toBitVec = lane st x 0) (h1 : x1.toBitVec = lane st x 1)
    (h2 : x2.toBitVec = lane st x 2) (h3 : x3.toBitVec = lane st x 3)
    (h4 : x4.toBitVec = lane st x 4) :
    ((0 : UInt64) ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4).toBitVec = xorColumn st x := by
  simp only [xorColumn_five, UInt64.toBitVec_xor, u64_zero_toBitVec, h0, h1, h2, h3, h4]

private theorem theta_lane_c {a d : UInt64} {l cA cB : Lane}
    (hl : a.toBitVec = l) (hd : d.toBitVec = cA ^^^ cB.rotateLeft 1) :
    (a ^^^ d).toBitVec = l ^^^ cA ^^^ cB.rotateLeft 1 := by
  rw [UInt64.toBitVec_xor, hl, hd, BitVec.xor_assoc]

private theorem thetaS_toState_constructive (s : KState) :
    (thetaS s).toState = theta s.toState := by
  have hc0 : ((0 : UInt64) ^^^ s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20).toBitVec =
      xorColumn s.toState 0 := theta_col_c rfl rfl rfl rfl rfl
  have hc1 : ((0 : UInt64) ^^^ s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21).toBitVec =
      xorColumn s.toState 1 := theta_col_c rfl rfl rfl rfl rfl
  have hc2 : ((0 : UInt64) ^^^ s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22).toBitVec =
      xorColumn s.toState 2 := theta_col_c rfl rfl rfl rfl rfl
  have hc3 : ((0 : UInt64) ^^^ s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23).toBitVec =
      xorColumn s.toState 3 := theta_col_c rfl rfl rfl rfl rfl
  have hc4 : ((0 : UInt64) ^^^ s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24).toBitVec =
      xorColumn s.toState 4 := theta_col_c rfl rfl rfl rfl rfl
  have hd0 : (((0 : UInt64) ^^^ s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24) ^^^
      rotlK ((0 : UInt64) ^^^ s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21) 1 63).toBitVec =
      xorColumn s.toState 4 ^^^ (xorColumn s.toState 1).rotateLeft 1 := by
    rw [UInt64.toBitVec_xor, rotlK_1, hc4, hc1]
  have hd1 : (((0 : UInt64) ^^^ s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20) ^^^
      rotlK ((0 : UInt64) ^^^ s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22) 1 63).toBitVec =
      xorColumn s.toState 0 ^^^ (xorColumn s.toState 2).rotateLeft 1 := by
    rw [UInt64.toBitVec_xor, rotlK_1, hc0, hc2]
  have hd2 : (((0 : UInt64) ^^^ s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21) ^^^
      rotlK ((0 : UInt64) ^^^ s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23) 1 63).toBitVec =
      xorColumn s.toState 1 ^^^ (xorColumn s.toState 3).rotateLeft 1 := by
    rw [UInt64.toBitVec_xor, rotlK_1, hc1, hc3]
  have hd3 : (((0 : UInt64) ^^^ s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22) ^^^
      rotlK ((0 : UInt64) ^^^ s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24) 1 63).toBitVec =
      xorColumn s.toState 2 ^^^ (xorColumn s.toState 4).rotateLeft 1 := by
    rw [UInt64.toBitVec_xor, rotlK_1, hc2, hc4]
  have hd4 : (((0 : UInt64) ^^^ s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23) ^^^
      rotlK ((0 : UInt64) ^^^ s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20) 1 63).toBitVec =
      xorColumn s.toState 3 ^^^ (xorColumn s.toState 0).rotateLeft 1 := by
    rw [UInt64.toBitVec_xor, rotlK_1, hc3, hc0]
  apply toState_ext _ _ (by simp only [theta, _root_.Array.size_ofFn])
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd0
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd1
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd2
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd3
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd4
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd0
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd1
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd2
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd3
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd4
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd0
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd1
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd2
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd3
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd4
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd0
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd1
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd2
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd3
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd4
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd0
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd1
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd2
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd3
  · rw [theta_getElem_c]; exact theta_lane_c rfl hd4

private theorem chi_lane_c (a b c : UInt64) :
    (a ^^^ ((~~~b) &&& c)).toBitVec = a.toBitVec ^^^ ((~~~b.toBitVec) &&& c.toBitVec) := by
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not]

private theorem chiS_toState_constructive (s : KState) :
    (chiS s).toState = chi s.toState := by
  apply toState_ext _ _ (by simp only [chi, _root_.Array.size_ofFn])
  · rw [chi_getElem_c]; exact chi_lane_c s.a0 s.a1 s.a2
  · rw [chi_getElem_c]; exact chi_lane_c s.a1 s.a2 s.a3
  · rw [chi_getElem_c]; exact chi_lane_c s.a2 s.a3 s.a4
  · rw [chi_getElem_c]; exact chi_lane_c s.a3 s.a4 s.a0
  · rw [chi_getElem_c]; exact chi_lane_c s.a4 s.a0 s.a1
  · rw [chi_getElem_c]; exact chi_lane_c s.a5 s.a6 s.a7
  · rw [chi_getElem_c]; exact chi_lane_c s.a6 s.a7 s.a8
  · rw [chi_getElem_c]; exact chi_lane_c s.a7 s.a8 s.a9
  · rw [chi_getElem_c]; exact chi_lane_c s.a8 s.a9 s.a5
  · rw [chi_getElem_c]; exact chi_lane_c s.a9 s.a5 s.a6
  · rw [chi_getElem_c]; exact chi_lane_c s.a10 s.a11 s.a12
  · rw [chi_getElem_c]; exact chi_lane_c s.a11 s.a12 s.a13
  · rw [chi_getElem_c]; exact chi_lane_c s.a12 s.a13 s.a14
  · rw [chi_getElem_c]; exact chi_lane_c s.a13 s.a14 s.a10
  · rw [chi_getElem_c]; exact chi_lane_c s.a14 s.a10 s.a11
  · rw [chi_getElem_c]; exact chi_lane_c s.a15 s.a16 s.a17
  · rw [chi_getElem_c]; exact chi_lane_c s.a16 s.a17 s.a18
  · rw [chi_getElem_c]; exact chi_lane_c s.a17 s.a18 s.a19
  · rw [chi_getElem_c]; exact chi_lane_c s.a18 s.a19 s.a15
  · rw [chi_getElem_c]; exact chi_lane_c s.a19 s.a15 s.a16
  · rw [chi_getElem_c]; exact chi_lane_c s.a20 s.a21 s.a22
  · rw [chi_getElem_c]; exact chi_lane_c s.a21 s.a22 s.a23
  · rw [chi_getElem_c]; exact chi_lane_c s.a22 s.a23 s.a24
  · rw [chi_getElem_c]; exact chi_lane_c s.a23 s.a24 s.a20
  · rw [chi_getElem_c]; exact chi_lane_c s.a24 s.a20 s.a21

private theorem roundS_toState_constructive (s : KState) (c : UInt64) :
    (roundS s c).toState = Obend.Digest.Cshake256.round s.toState c.toBitVec := by
  simp only [roundS, Obend.Digest.Cshake256.round, iotaS_toState, chiS_toState_constructive,
    rhoPiS_toState, thetaS_toState_constructive]

private theorem keccakS_toState_constructive (s : KState) :
    (keccakS s).toState = Obend.Digest.Cshake256.keccakF1600 s.toState := by
  have hfold (constants : List Lane) (initial : KState) :
      ((constants.map UInt64.ofBitVec).foldl roundS initial).toState =
        constants.foldl Obend.Digest.Cshake256.round initial.toState := by
    induction constants generalizing initial with
    | nil => rfl
    | cons constant rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih, roundS_toState_constructive, UInt64.toBitVec_ofBitVec]
  exact hfold roundConstants s

/-- **Universal 24-Round `Keccak-f[1600]` Spec Weld (`keccak_f1600_refines_spec`)**:
    For **every** 25-lane array `state : Array Std.U64 25#usize` ($2^{1600}$ states, zero preconditions),
    the extracted Rust MIR `obend_keccak::keccak_f1600` evaluates to `.ok out` and its 25 output lanes
    equal `Obend.Digest.Cshake256.keccakF1600 (mirToSpecState state)`. -/
theorem keccak_f1600_refines_spec (state : Aeneas.Std.Array Std.U64 25#usize) :
    ∃ out,
      obend_keccak.keccak_f1600 state = .ok out ∧
      mirToSpecState out = Obend.Digest.Cshake256.keccakF1600 (mirToSpecState state) := by
  let s := mirToKState state
  refine ⟨kstateToMir (keccakS s), ?_, ?_⟩
  · have heq := keccak_f1600_eq_keccakS s
    simpa only [s, kstateToMir_mirToKState state] using heq
  · rw [mirToSpecState_kstateToMir (keccakS s), keccakS_toState_constructive s]
    rfl

/-! ## 4. NIST SP 800-185 `encoded_width`, `left_encode`, and `right_encode` Spec Welds -/

private theorem natBytesLEAux_eq_of_ge : ∀ (f1 f2 v : Nat), v ≤ f1 → v ≤ f2 →
    natBytesLEAux f1 v = natBytesLEAux f2 v
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, v, hv1, _ => by
    have hv0 : v = 0 := by omega
    subst hv0; simp [natBytesLEAux]
  | _ + 1, 0, v, _, hv2 => by
    have hv0 : v = 0 := by omega
    subst hv0; simp [natBytesLEAux]
  | f1 + 1, f2 + 1, v, hv1, hv2 => by
    simp only [natBytesLEAux]
    split
    · rfl
    · congr 1
      exact natBytesLEAux_eq_of_ge f1 f2 (v / 256) (by omega) (by omega)

private theorem natBytesLE_zero : natBytesLE 0 = [] := rfl

private theorem natBytesLE_pos {v : Nat} (hv : 0 < v) :
    natBytesLE v = UInt8.ofNat (v % 256) :: natBytesLE (v / 256) := by
  cases v with
  | zero => omega
  | succ m =>
    unfold natBytesLE
    simp only [natBytesLEAux, Nat.succ_ne_zero, ite_false]
    congr 1
    exact natBytesLEAux_eq_of_ge m ((m + 1) / 256) ((m + 1) / 256) (by omega) (Nat.le_refl _)

private theorem natBytesLE_length_le_of_lt_pow : ∀ (k v : Nat), v < 256 ^ k →
    (natBytesLE v).length ≤ k
  | 0, v, hv => by
    have hv0 : v = 0 := by simpa using hv
    subst hv0; exact Nat.zero_le _
  | k + 1, v, hv => by
    by_cases hv0 : v = 0
    · subst hv0; simp [natBytesLE_zero]
    · rw [natBytesLE_pos (Nat.pos_of_ne_zero hv0), List.length_cons]
      have hdiv : v / 256 < 256 ^ k := by
        rw [Nat.pow_succ] at hv
        omega
      exact Nat.succ_le_succ (natBytesLE_length_le_of_lt_pow k (v / 256) hdiv)

private theorem natBytesLE_nonempty_of_pos {v : Nat} (hv : 0 < v) : natBytesLE v ≠ [] := by
  rw [natBytesLE_pos hv]
  simp

theorem natBytesBE_length_bounds (v : Std.U64) :
    1 ≤ (natBytesBE v.val).length ∧ (natBytesBE v.val).length ≤ 8 := by
  unfold natBytesBE
  by_cases hv0 : v.val = 0
  · simp [hv0, natBytesLE_zero]
  · have hne := natBytesLE_nonempty_of_pos (Nat.pos_of_ne_zero hv0)
    have hlt : v.val < 256 ^ 8 := by
      have h64 : v.val < 2 ^ 64 := v.bv.isLt
      simpa using h64
    have hle := natBytesLE_length_le_of_lt_pow 8 v.val hlt
    have hpos : 1 ≤ (natBytesLE v.val).length := by
      cases h : natBytesLE v.val with
      | nil => exact absurd h hne
      | cons _ _ => simp
    simp [hne, hpos, hle]

private theorem u64_shr8_val (v : Std.U64) :
    (v >>> 8#i32 : Result Std.U64) = .ok ⟨v.bv >>> 8⟩ ∧
    (⟨v.bv >>> 8⟩ : Std.U64).val = v.val / 256 := by
  refine ⟨rfl, ?_⟩
  change (v.bv >>> 8).toNat = v.bv.toNat / 256
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem encoded_width_loop_fuel (rem : Nat) :
    ∀ (v : Std.U64) (acc : Nat),
      rem = (natBytesLE v.val).length →
      acc + rem ≤ 8 →
      loopFuel (rem + 1) (fun (v1, w1) => obend_keccak.encoded_width_loop.body v1 w1)
        (v, UScalar.ofNat .Usize acc) = .ok (UScalar.ofNat .Usize (acc + rem)) := by
  induction rem with
  | zero =>
    intro v acc hrem _
    match decEq v 0#u64 with
    | isTrue hv0 =>
      subst hv0
      have hnot : ¬ (0#u64 > 0#u64) := by decide
      have hstep0 : obend_keccak.encoded_width_loop.body 0#u64 (UScalar.ofNat .Usize acc) =
          .ok (.done (UScalar.ofNat .Usize acc)) := by
        unfold obend_keccak.encoded_width_loop.body
        simp only [hnot, ite_false]
      rw [loopFuel_succ]
      dsimp only
      rw [hstep0, result_bind_ok]
      rfl
    | isFalse hne0 =>
      exfalso
      have hvne : v.val ≠ 0 := fun hz => hne0 (UScalar.eq_of_val_eq hz)
      have hpos : 0 < v.val := Nat.pos_of_ne_zero hvne
      rw [natBytesLE_pos hpos, List.length_cons] at hrem
      exact Nat.succ_ne_zero _ hrem.symm
  | succ rem' ih =>
    intro v acc hrem hbound
    have hvpos : 0 < v.val := by
      match decEq v.val 0 with
      | isTrue hz =>
        exfalso
        rw [hz, natBytesLE_zero] at hrem
        exact Nat.succ_ne_zero rem' hrem
      | isFalse hnz =>
        exact Nat.pos_of_ne_zero hnz
    have hgt : v > 0#u64 := by
      simpa only [GT.gt, UScalar.lt_iff_val] using (show (0#u64).val < v.val from hvpos)
    obtain ⟨hshr, hvshr⟩ := u64_shr8_val v
    have hadd := checked_add_ofNat_usize acc (by omega)
    have hrem' : rem' = (natBytesLE (⟨v.bv >>> 8⟩ : Std.U64).val).length := by
      rw [hvshr]
      rw [natBytesLE_pos hvpos, List.length_cons] at hrem
      exact Nat.succ.inj hrem
    have hrec := ih ⟨v.bv >>> 8⟩ (acc + 1) hrem' (by omega)
    have hstep1 : obend_keccak.encoded_width_loop.body v (UScalar.ofNat .Usize acc) =
        .ok (.cont (⟨v.bv >>> 8⟩, UScalar.ofNat .Usize (acc + 1))) := by
      unfold obend_keccak.encoded_width_loop.body
      simp only [hgt, ite_true, hshr, hadd, bind_eq_result_bind, result_bind_ok]
    rw [loopFuel_succ]
    dsimp only
    rw [hstep1, result_bind_ok]
    have heq : acc + 1 + rem' = acc + (rem' + 1) := by omega
    simpa only [heq] using hrec

/-- **`encoded_width` Spec Weld**: for every `value : Std.U64`, `obend_keccak::encoded_width value`
    evaluates to `(Obend.Digest.Cshake256.natBytesBE value.val).length` (`1 .. 8`). -/
theorem encoded_width_refines_spec (value : Std.U64) :
    obend_keccak.encoded_width value =
      .ok (UScalar.ofNat .Usize (natBytesBE value.val).length) := by
  unfold obend_keccak.encoded_width
  match decEq value 0#u64 with
  | isTrue hv =>
    subst hv
    rfl
  | isFalse hv =>
    have hv0 : value.val ≠ 0 := fun hz => hv (UScalar.eq_of_val_eq hz)
    have hpos : 0 < value.val := Nat.pos_of_ne_zero hv0
    have hne := natBytesLE_nonempty_of_pos hpos
    have hbe_len : (natBytesBE value.val).length = (natBytesLE value.val).length := by
      simp only [natBytesBE, hne, ite_false, List.length_reverse]
    have hle8 : (natBytesLE value.val).length ≤ 8 := by
      rw [← hbe_len]; exact (natBytesBE_length_bounds value).2
    have hmax : 64 ≤ loopMaxFuel := by decide
    simp only [hv, ite_false, hbe_len]
    unfold obend_keccak.encoded_width_loop
    apply loop_ok_of_loopFuel (fuel := (natBytesLE value.val).length + 1) (by omega)
    simpa only [Nat.zero_add] using
      encoded_width_loop_fuel (natBytesLE value.val).length value 0 rfl (by omega)

private theorem natBytesLE_getElem : ∀ (v j : Nat),
    (hj : j < (natBytesLE v).length) →
    (natBytesLE v)[j]'hj = UInt8.ofNat ((v / 256 ^ j) % 256)
  | v, 0, hj => by
    have hvpos : 0 < v := by
      by_cases hz : v = 0
      · subst hz; simp [natBytesLE_zero] at hj
      · exact Nat.pos_of_ne_zero hz
    simp [natBytesLE_pos hvpos]
  | v, j + 1, hj => by
    have hvpos : 0 < v := by
      by_cases hz : v = 0
      · subst hz; simp [natBytesLE_zero] at hj
      · exact Nat.pos_of_ne_zero hz
    have hj' : j < (natBytesLE (v / 256)).length := by
      rw [natBytesLE_pos hvpos, List.length_cons] at hj
      omega
    have heq_head : (natBytesLE v)[j + 1]'hj = (natBytesLE (v / 256))[j]'hj' := by
      conv => lhs; simp only [natBytesLE_pos hvpos, List.getElem_cons_succ]
    rw [heq_head, natBytesLE_getElem (v / 256) j hj', Nat.div_div_eq_div_mul, ← Nat.pow_succ']

private theorem natBytesBE_getElem (v i : Nat) (hi : i < (natBytesBE v).length) :
    (natBytesBE v)[i]'hi = UInt8.ofNat ((v / 256 ^ ((natBytesBE v).length - 1 - i)) % 256) := by
  by_cases hz : v = 0
  · subst hz
    have hi0 : i = 0 := by
      change i < 1 at hi; omega
    subst hi0
    rfl
  · have hne := natBytesLE_nonempty_of_pos (Nat.pos_of_ne_zero hz)
    have hrev : natBytesBE v = (natBytesLE v).reverse := by simp [natBytesBE, hne]
    have hlen : (natBytesBE v).length = (natBytesLE v).length := by simp [hrev]
    have hj : (natBytesLE v).length - 1 - i < (natBytesLE v).length := by omega
    have hget : (natBytesBE v)[i]'hi = (natBytesLE v)[(natBytesLE v).length - 1 - i]'hj := by
      simp [hrev, List.getElem_reverse]
    rw [hget, hlen, natBytesLE_getElem v _ hj]

private theorem mask8_testBit (i : Nat) : Nat.testBit 255 i = decide (i < 8) := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | k + 8 =>
    have hdiv : 255 / 2 ^ (k + 8) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 255 < 256) (by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.add_comm k 8, Nat.pow_add]
        exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)))
    have hnot : decide (k + 8 < 8) = false := by
      simp
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, hnot]
    rfl

private theorem bv64_and_255_setWidth8 (y : BitVec 64) :
    (y &&& 255#64).setWidth 8 = y.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and]
  have hm : (255#64).toNat = 255 := rfl
  rw [hm]
  have hand : y.toNat &&& 255 = y.toNat % 256 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_and, Nat.testBit_mod_two_pow, mask8_testBit]
    exact Bool.and_comm _ _
  rw [hand, Nat.mod_mod]

private theorem mir_shr_byte_eq_be (value : Std.U64) (w i : Nat)
    (hw : w = (natBytesBE value.val).length) (hi : i < w) :
    let k := w - 1 - i
    UScalar.cast .U8 ((⟨value.bv >>> (8 * k)⟩ : Std.U64) &&& 255#u64) =
      ⟨((natBytesBE value.val)[i]'(by omega)).toBitVec⟩ := by
  dsimp only
  apply UScalar.ext
  change ((value.bv >>> (8 * (w - 1 - i)) &&& 255#64).setWidth 8) = _
  rw [bv64_and_255_setWidth8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (8 * (w - 1 - i)) = 256 ^ (w - 1 - i) := by
    rw [Nat.pow_mul]
  subst hw
  rw [hpow, natBytesBE_getElem value.val i hi]
  simp [UInt8.toNat_ofNat']

private def beMir (v : Std.U64) : List Std.U8 :=
  (natBytesBE v.val).map (fun b => ⟨b.toBitVec⟩)

private theorem beMir_length (v : Std.U64) : (beMir v).length = (natBytesBE v.val).length :=
  List.length_map _

private theorem beMir_getElem (v : Std.U64) (i : Nat) (hi : i < (beMir v).length) :
    (beMir v)[i]'hi = ⟨((natBytesBE v.val)[i]'(by rw [← beMir_length]; exact hi)).toBitVec⟩ := by
  simp [beMir]

private theorem mirBytesToUInt8_beMir (v : Std.U64) :
    mirBytesToUInt8 (beMir v) = natBytesBE v.val := by
  unfold mirBytesToUInt8 beMir
  rw [List.map_map]
  have hid : ((fun b : Std.U8 => UInt8.ofBitVec b.bv) ∘ (fun b : UInt8 => (⟨b.toBitVec⟩ : Std.U8))) = id := by
    funext b; simp
  rw [hid, List.map_id]

private theorem take_succ_eq_append_getElem {α : Type} : ∀ (xs : List α) (k : Nat) (hk : k < xs.length),
    xs.take (k + 1) = xs.take k ++ [xs[k]'hk]
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | x :: xs, k + 1, hk => by
    simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
    exact congrArg (x :: ·) (take_succ_eq_append_getElem xs k (Nat.lt_of_succ_lt_succ hk))

private theorem set_prefix_drop {α : Type} : ∀ (pre rest : List α) (x : α),
    0 < rest.length →
    (pre ++ rest).set pre.length x = pre ++ x :: rest.drop 1
  | [], _ :: _, _, _ => rfl
  | [], [], _, h => absurd h (Nat.lt_irrefl 0)
  | p :: ps, rest, x, h => by
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    exact congrArg (p :: ·) (set_prefix_drop ps rest x h)

private theorem drop_one_drop {α : Type} (xs : List α) (k : Nat) :
    (xs.drop k).drop 1 = xs.drop (k + 1) := by
  rw [List.drop_drop]

/-- **SP 800-185 `left_encode` Spec Weld (`left_encode_refines_spec`)**:
    For every 64-bit integer `value : Std.U64` and 9-byte stack buffer `buf`, the extracted Rust MIR
    `obend_keccak::left_encode value buf` terminates without panic and writes the exact byte list
    `Obend.Digest.Cshake256.leftEncode value.val` into `out[0 .. len]`. -/
theorem left_encode_refines_spec (value : Std.U64) (buf : Aeneas.Std.Array Std.U8 9#usize) :
    ∃ (len : Std.Usize) (out : Aeneas.Std.Array Std.U8 9#usize),
      obend_keccak.left_encode value buf = .ok (len, out) ∧
      mirBytesToUInt8 (out.val.take len.val) = Obend.Digest.Cshake256.leftEncode value.val := by
  let w := (natBytesBE value.val).length
  obtain ⟨hw1, hw8⟩ := natBytesBE_length_bounds value
  have hw_mir := encoded_width_refines_spec value
  let wU : Std.Usize := UScalar.ofNat .Usize w
  have hwU_val : wU.val = w := usize_ofNat_val w (by omega)
  let wByte : Std.U8 := UScalar.cast .U8 wU
  have hwByte_u8 : UInt8.ofBitVec wByte.bv = UInt8.ofNat w := by
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (wU.bv.setWidth 8).toNat = (BitVec.ofNat 8 w).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change wU.val % 256 = w % 256
    rw [hwU_val]
  have ha0_len : (wByte :: buf.val.drop 1).length = (9#usize).val := by
    have hbl : buf.val.length = 9 := buf.property
    rw [usize_ofNat_val 9 (by decide)]
    simp [hbl]
  let a0 : Aeneas.Std.Array Std.U8 9#usize := ⟨wByte :: buf.val.drop 1, ha0_len⟩
  have hupd0 : Aeneas.Std.Array.update buf 0#usize wByte = .ok a0 := by
    apply array_update_eq buf 0#usize wByte a0 (by decide)
    rcases buf with ⟨bs, hb⟩
    rcases bs with _ | ⟨b0, tail⟩
    · simp [usize_ofNat_val 9 (by decide)] at hb
    · rfl
  have harr_len (k : Nat) (hk : k ≤ w) :
      (wByte :: (beMir value).take k ++ buf.val.drop (1 + k)).length = (9#usize).val := by
    have hbl : buf.val.length = 9 := buf.property
    have hbel : (beMir value).length = w := beMir_length value
    rw [usize_ofNat_val 9 (by decide)]
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_take,
      List.length_drop, hbl, hbel, Nat.min_eq_left hk]
    omega
  let arrAt (k : Nat) : Aeneas.Std.Array Std.U8 9#usize :=
    if hk : k ≤ w then ⟨wByte :: (beMir value).take k ++ buf.val.drop (1 + k), harr_len k hk⟩
    else a0
  let st (k : Nat) : Aeneas.Std.Array Std.U8 9#usize × Std.Usize :=
    (arrAt k, UScalar.ofNat .Usize k)
  let body := fun (o1, i1) => obend_keccak.left_encode_loop.body value wU o1 i1
  have hstep : ∀ k, k < w → body (st k) = .ok (.cont (st (k + 1))) := by
    intro k hk
    have hkw : k ≤ w := Nat.le_of_lt hk
    have hk1w : k + 1 ≤ w := hk
    let iU : Std.Usize := UScalar.ofNat .Usize k
    have hiU_val : iU.val = k := usize_ofNat_val k (by omega)
    have hlt : iU < wU := by rw [UScalar.lt_iff_val, hiU_val, hwU_val]; exact hk
    have hsub1 : (wU - 1#usize : Result Std.Usize) = .ok (UScalar.ofNat .Usize (w - 1)) := by
      have hle1 : (1#usize).val ≤ wU.val := by rw [hwU_val, usize_ofNat_val 1 (by decide)]; exact hw1
      simp only [hSub_uscalar_eq, hle1, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change (wU.bv - (1#usize).bv).toNat = (UScalar.ofNat .Usize (w - 1)).val
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle1), usize_ofNat_val (w - 1) (by omega)]
      exact congrArg (· - 1) hwU_val
    have hsub2 : (UScalar.ofNat .Usize (w - 1) - iU : Result Std.Usize) =
        .ok (UScalar.ofNat .Usize (w - 1 - k)) := by
      have hw1_val := usize_ofNat_val (w - 1) (by omega)
      have hle2 : iU.val ≤ (UScalar.ofNat .Usize (w - 1)).val := by rw [hiU_val, hw1_val]; omega
      simp only [hSub_uscalar_eq, hle2, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((UScalar.ofNat .Usize (w - 1)).bv - iU.bv).toNat = (UScalar.ofNat .Usize (w - 1 - k)).val
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle2), usize_ofNat_val (w - 1 - k) (by omega)]
      change (UScalar.ofNat .Usize (w - 1)).val - iU.val = w - 1 - k
      rw [hw1_val, hiU_val]
    have hmul : (8#usize * UScalar.ofNat .Usize (w - 1 - k) : Result Std.Usize) =
        .ok (UScalar.ofNat .Usize (8 * (w - 1 - k))) := by
      have hwk_val := usize_ofNat_val (w - 1 - k) (by omega)
      have hm_lt : (8#usize).val * (UScalar.ofNat .Usize (w - 1 - k)).val < 2 ^ (UScalarTy.Usize.numBits) := by
        rw [usize_ofNat_val 8 (by decide), hwk_val]; change 8 * (w - 1 - k) < 2 ^ 64; omega
      simp only [hMul_uscalar_eq, hm_lt, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((8#usize).bv * (UScalar.ofNat .Usize (w - 1 - k)).bv).toNat =
        (UScalar.ofNat .Usize (8 * (w - 1 - k))).val
      rw [BitVec.toNat_mul, usize_ofNat_val (8 * (w - 1 - k)) (by omega)]
      change (8 * (UScalar.ofNat .Usize (w - 1 - k)).val) % (2 ^ 64) = 8 * (w - 1 - k)
      rw [hwk_val, Nat.mod_eq_of_lt (by omega)]
    let shU32 : Std.U32 := UScalar.cast .U32 (UScalar.ofNat .Usize (8 * (w - 1 - k)))
    have hsh_val : shU32.val = 8 * (w - 1 - k) := by
      change (((BitVec.ofNat 64 (8 * (w - 1 - k))).setWidth 32)).toNat = 8 * (w - 1 - k)
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hshr : (value >>> shU32 : Result Std.U64) = .ok ⟨value.bv >>> (8 * (w - 1 - k))⟩ := by
      have hslt : shU32.val < UScalarTy.U64.numBits := by rw [hsh_val]; change 8 * (w - 1 - k) < 64; omega
      simp only [hShrU_uscalar_eq, hslt, ite_true]
      rw [hsh_val]
    have hadd1 : (1#usize + iU : Result Std.Usize) = .ok (UScalar.ofNat .Usize (1 + k)) := by
      have ha_lt : (1#usize).val + iU.val < 2 ^ (UScalarTy.Usize.numBits) := by
        rw [usize_ofNat_val 1 (by decide), hiU_val]; change 1 + k < 2 ^ 64; omega
      simp only [hAdd_uscalar_eq, ha_lt, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((1#usize).bv + iU.bv).toNat = (UScalar.ofNat .Usize (1 + k)).val
      rw [BitVec.toNat_add, usize_ofNat_val (1 + k) (by omega)]
      change (1 + iU.val) % (2 ^ 64) = 1 + k
      rw [hiU_val, Nat.mod_eq_of_lt (by omega)]
    have hadd_i := checked_add_ofNat_usize k (by omega)
    let byteK := UScalar.cast .U8 ((⟨value.bv >>> (8 * (w - 1 - k))⟩ : Std.U64) &&& 255#u64)
    have hbyteK : byteK = (beMir value)[k]'(by rw [beMir_length]; exact hk) := by
      rw [beMir_getElem]
      exact mir_shr_byte_eq_be value w k rfl hk
    have hupd : Aeneas.Std.Array.update (arrAt k) (UScalar.ofNat .Usize (1 + k)) byteK =
        .ok (arrAt (k + 1)) := by
      apply array_update_eq
      · rw [usize_ofNat_val (1 + k) (by omega), usize_ofNat_val 9 (by decide)]; omega
      · simp only [arrAt, hkw, hk1w, ↓reduceDIte]
        rw [usize_ofNat_val (1 + k) (by omega), hbyteK]
        let pre := wByte :: (beMir value).take k
        have hpre_len : pre.length = 1 + k := by
          simp [pre, List.length_take, beMir_length, Nat.min_eq_left hkw]; omega
        have hrest_pos : 0 < (buf.val.drop (1 + k)).length := by
          rw [List.length_drop, buf.property, usize_ofNat_val 9 (by decide)]; omega
        have hset := set_prefix_drop pre (buf.val.drop (1 + k))
          ((beMir value)[k]'(by rw [beMir_length]; exact hk)) hrest_pos
        rw [hpre_len, drop_one_drop, show 1 + k + 1 = 1 + (k + 1) by omega] at hset
        simp only [pre, List.cons_append] at hset ⊢
        rw [hset, take_succ_eq_append_getElem (beMir value) k (by rw [beMir_length]; exact hk),
            List.append_assoc]
        rfl
    simp only [body, st, iU, shU32, byteK, obend_keccak.left_encode_loop.body, hlt, ite_true,
      hsub1, hsub2, hmul, hshr, hadd1, hupd, hadd_i, bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  have hdone : body (st w) = .ok (.done (arrAt w)) := by
    have hnot : ¬ (UScalar.ofNat .Usize w < wU) := UScalar.lt_irrefl wU
    simp only [body, st, wU, obend_keccak.left_encode_loop.body, hnot, ite_false]
  have hmax : 64 ≤ loopMaxFuel := by decide
  have hloop : obend_keccak.left_encode_loop value a0 wU 0#usize = .ok (arrAt w) := by
    have h0 : arrAt 0 = a0 := by apply Aeneas.Std.Array.ext; simp [arrAt, a0]
    unfold obend_keccak.left_encode_loop
    rw [← h0]
    exact loop_det_steps body st (arrAt w) w (by omega) hstep hdone
  have hadd_w := checked_add_ofNat_usize w (by omega)
  have htake_full : (beMir value).take w = beMir value :=
    List.take_of_length_le (by rw [beMir_length value]; exact Nat.le_refl w)
  refine ⟨UScalar.ofNat .Usize (w + 1), arrAt w, ?_, ?_⟩
  · unfold obend_keccak.left_encode
    rw [bind_eq_result_bind, hw_mir, result_bind_ok]
    change (lift wByte >>= fun i => Aeneas.Std.Array.update buf 0#usize i >>= fun a =>
      obend_keccak.left_encode_loop value a wU 0#usize >>= fun out1 =>
      (wU + 1#usize) >>= fun i1 => ok (i1, out1)) = _
    rw [bind_eq_result_bind, lift_eq_ok, result_bind_ok,
        bind_eq_result_bind, hupd0, result_bind_ok,
        bind_eq_result_bind, hloop, result_bind_ok,
        bind_eq_result_bind, hadd_w, result_bind_ok]
  · rw [usize_ofNat_val (w + 1) (by omega)]
    have hww : w ≤ w := Nat.le_refl w
    simp only [arrAt, hww, ↓reduceDIte]
    rw [htake_full]
    have htake : (wByte :: (beMir value ++ buf.val.drop (1 + w))).take (w + 1) =
        wByte :: beMir value := by
      simp only [List.take_succ_cons]
      rw [List.take_append_of_le_length (by rw [beMir_length value]; exact Nat.le_refl w), htake_full]
    rw [List.cons_append, htake]
    simp only [mirBytesToUInt8, List.map_cons, hwByte_u8]
    rw [← mirBytesToUInt8, mirBytesToUInt8_beMir]
    rfl

/-- **SP 800-185 `right_encode` Spec Weld (`right_encode_refines_spec`)**:
    For every 64-bit integer `value : Std.U64` and 9-byte stack buffer `buf`, the extracted Rust MIR
    `obend_keccak::right_encode value buf` terminates without panic and writes the exact byte list
    `Obend.Digest.Kmac256.rightEncode value.val` into `out[0 .. len]`. -/
theorem right_encode_refines_spec (value : Std.U64) (buf : Aeneas.Std.Array Std.U8 9#usize) :
    ∃ (len : Std.Usize) (out : Aeneas.Std.Array Std.U8 9#usize),
      obend_keccak.right_encode value buf = .ok (len, out) ∧
      mirBytesToUInt8 (out.val.take len.val) = Obend.Digest.Kmac256.rightEncode value.val := by
  let w := (natBytesBE value.val).length
  obtain ⟨hw1, hw8⟩ := natBytesBE_length_bounds value
  have hw_mir := encoded_width_refines_spec value
  let wU : Std.Usize := UScalar.ofNat .Usize w
  have hwU_val : wU.val = w := usize_ofNat_val w (by omega)
  let wByte : Std.U8 := UScalar.cast .U8 wU
  have hwByte_u8 : UInt8.ofBitVec wByte.bv = UInt8.ofNat w := by
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (wU.bv.setWidth 8).toNat = (BitVec.ofNat 8 w).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change wU.val % 256 = w % 256
    rw [hwU_val]
  have harr_len (k : Nat) (hk : k ≤ w) :
      ((beMir value).take k ++ buf.val.drop k).length = (9#usize).val := by
    have hbl : buf.val.length = 9 := buf.property
    have hbel : (beMir value).length = w := beMir_length value
    rw [usize_ofNat_val 9 (by decide)]
    simp only [List.length_append, List.length_take, List.length_drop, hbl, hbel, Nat.min_eq_left hk]
    omega
  let arrAt (k : Nat) : Aeneas.Std.Array Std.U8 9#usize :=
    if hk : k ≤ w then ⟨(beMir value).take k ++ buf.val.drop k, harr_len k hk⟩
    else buf
  let st (k : Nat) : Aeneas.Std.Array Std.U8 9#usize × Std.Usize :=
    (arrAt k, UScalar.ofNat .Usize k)
  let body := fun (o1, i1) => obend_keccak.right_encode_loop.body value wU o1 i1
  have hstep : ∀ k, k < w → body (st k) = .ok (.cont (st (k + 1))) := by
    intro k hk
    have hkw : k ≤ w := Nat.le_of_lt hk
    have hk1w : k + 1 ≤ w := hk
    let iU : Std.Usize := UScalar.ofNat .Usize k
    have hiU_val : iU.val = k := usize_ofNat_val k (by omega)
    have hlt : iU < wU := by rw [UScalar.lt_iff_val, hiU_val, hwU_val]; exact hk
    have hsub1 : (wU - 1#usize : Result Std.Usize) = .ok (UScalar.ofNat .Usize (w - 1)) := by
      have hle1 : (1#usize).val ≤ wU.val := by rw [hwU_val, usize_ofNat_val 1 (by decide)]; exact hw1
      simp only [hSub_uscalar_eq, hle1, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change (wU.bv - (1#usize).bv).toNat = (UScalar.ofNat .Usize (w - 1)).val
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle1), usize_ofNat_val (w - 1) (by omega)]
      exact congrArg (· - 1) hwU_val
    have hsub2 : (UScalar.ofNat .Usize (w - 1) - iU : Result Std.Usize) =
        .ok (UScalar.ofNat .Usize (w - 1 - k)) := by
      have hw1_val := usize_ofNat_val (w - 1) (by omega)
      have hle2 : iU.val ≤ (UScalar.ofNat .Usize (w - 1)).val := by rw [hiU_val, hw1_val]; omega
      simp only [hSub_uscalar_eq, hle2, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((UScalar.ofNat .Usize (w - 1)).bv - iU.bv).toNat = (UScalar.ofNat .Usize (w - 1 - k)).val
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle2), usize_ofNat_val (w - 1 - k) (by omega)]
      change (UScalar.ofNat .Usize (w - 1)).val - iU.val = w - 1 - k
      rw [hw1_val, hiU_val]
    have hmul : (8#usize * UScalar.ofNat .Usize (w - 1 - k) : Result Std.Usize) =
        .ok (UScalar.ofNat .Usize (8 * (w - 1 - k))) := by
      have hwk_val := usize_ofNat_val (w - 1 - k) (by omega)
      have hm_lt : (8#usize).val * (UScalar.ofNat .Usize (w - 1 - k)).val < 2 ^ (UScalarTy.Usize.numBits) := by
        rw [usize_ofNat_val 8 (by decide), hwk_val]; change 8 * (w - 1 - k) < 2 ^ 64; omega
      simp only [hMul_uscalar_eq, hm_lt, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((8#usize).bv * (UScalar.ofNat .Usize (w - 1 - k)).bv).toNat =
        (UScalar.ofNat .Usize (8 * (w - 1 - k))).val
      rw [BitVec.toNat_mul, usize_ofNat_val (8 * (w - 1 - k)) (by omega)]
      change (8 * (UScalar.ofNat .Usize (w - 1 - k)).val) % (2 ^ 64) = 8 * (w - 1 - k)
      rw [hwk_val, Nat.mod_eq_of_lt (by omega)]
    let shU32 : Std.U32 := UScalar.cast .U32 (UScalar.ofNat .Usize (8 * (w - 1 - k)))
    have hsh_val : shU32.val = 8 * (w - 1 - k) := by
      change (((BitVec.ofNat 64 (8 * (w - 1 - k))).setWidth 32)).toNat = 8 * (w - 1 - k)
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hshr : (value >>> shU32 : Result Std.U64) = .ok ⟨value.bv >>> (8 * (w - 1 - k))⟩ := by
      have hslt : shU32.val < UScalarTy.U64.numBits := by rw [hsh_val]; change 8 * (w - 1 - k) < 64; omega
      simp only [hShrU_uscalar_eq, hslt, ite_true]
      rw [hsh_val]
    have hadd_i := checked_add_ofNat_usize k (by omega)
    let byteK := UScalar.cast .U8 ((⟨value.bv >>> (8 * (w - 1 - k))⟩ : Std.U64) &&& 255#u64)
    have hbyteK : byteK = (beMir value)[k]'(by rw [beMir_length]; exact hk) := by
      rw [beMir_getElem]
      exact mir_shr_byte_eq_be value w k rfl hk
    have hupd : Aeneas.Std.Array.update (arrAt k) iU byteK = .ok (arrAt (k + 1)) := by
      apply array_update_eq
      · rw [hiU_val, usize_ofNat_val 9 (by decide)]; omega
      · simp only [arrAt, hkw, hk1w, ↓reduceDIte, hiU_val, hbyteK]
        have hpre_len : ((beMir value).take k).length = k := by
          rw [List.length_take, beMir_length value]
          exact Nat.min_eq_left hkw
        have hrest_pos : 0 < (buf.val.drop k).length := by
          rw [List.length_drop, buf.property, usize_ofNat_val 9 (by decide)]; omega
        have hset := set_prefix_drop ((beMir value).take k) (buf.val.drop k)
          ((beMir value)[k]'(by rw [beMir_length]; exact hk)) hrest_pos
        rw [hpre_len, drop_one_drop] at hset
        rw [hset, take_succ_eq_append_getElem (beMir value) k (by rw [beMir_length]; exact hk),
            List.append_assoc]
        rfl
    simp only [body, st, iU, shU32, byteK, obend_keccak.right_encode_loop.body, hlt, ite_true,
      hsub1, hsub2, hmul, hshr, hupd, hadd_i, bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  have hdone : body (st w) = .ok (.done (arrAt w)) := by
    have hnot : ¬ (UScalar.ofNat .Usize w < wU) := UScalar.lt_irrefl wU
    simp only [body, st, wU, obend_keccak.right_encode_loop.body, hnot, ite_false]
  have hmax : 64 ≤ loopMaxFuel := by decide
  have hloop : obend_keccak.right_encode_loop value buf wU 0#usize = .ok (arrAt w) := by
    have h0 : arrAt 0 = buf := by apply Aeneas.Std.Array.ext; simp [arrAt]
    unfold obend_keccak.right_encode_loop
    rw [← h0]
    exact loop_det_steps body st (arrAt w) w (by omega) hstep hdone
  have hout2_len : (beMir value ++ wByte :: buf.val.drop (w + 1)).length = (9#usize).val := by
    have hbl : buf.val.length = 9 := buf.property
    rw [usize_ofNat_val 9 (by decide)]
    simp only [List.length_append, beMir_length, List.length_cons, List.length_drop, hbl]
    omega
  let out2 : Aeneas.Std.Array Std.U8 9#usize := ⟨beMir value ++ wByte :: buf.val.drop (w + 1), hout2_len⟩
  have htake_full : (beMir value).take w = beMir value :=
    List.take_of_length_le (by rw [beMir_length value]; exact Nat.le_refl w)
  have hupd_w : Aeneas.Std.Array.update (arrAt w) wU wByte = .ok out2 := by
    apply array_update_eq
    · rw [hwU_val, usize_ofNat_val 9 (by decide)]; omega
    · have hww : w ≤ w := Nat.le_refl w
      simp only [arrAt, out2, hww, ↓reduceDIte, hwU_val]
      rw [htake_full]
      have hrest_pos : 0 < (buf.val.drop w).length := by
        rw [List.length_drop, buf.property, usize_ofNat_val 9 (by decide)]; omega
      have hset := set_prefix_drop (beMir value) (buf.val.drop w) wByte hrest_pos
      rw [beMir_length value, drop_one_drop] at hset
      dsimp only [w] at hset ⊢
      exact hset.symm
  have hadd_w := checked_add_ofNat_usize w (by omega)
  refine ⟨UScalar.ofNat .Usize (w + 1), out2, ?_, ?_⟩
  · unfold obend_keccak.right_encode
    rw [bind_eq_result_bind, hw_mir, result_bind_ok]
    change (obend_keccak.right_encode_loop value buf wU 0#usize >>= fun out1 =>
      lift wByte >>= fun i => Aeneas.Std.Array.update out1 wU i >>= fun out2' =>
      (wU + 1#usize) >>= fun i1 => ok (i1, out2')) = _
    rw [bind_eq_result_bind, hloop, result_bind_ok,
        bind_eq_result_bind, lift_eq_ok, result_bind_ok,
        bind_eq_result_bind, hupd_w, result_bind_ok,
        bind_eq_result_bind, hadd_w, result_bind_ok]
  · rw [usize_ofNat_val (w + 1) (by omega)]
    have htake : (beMir value ++ wByte :: buf.val.drop (w + 1)).take (w + 1) =
        beMir value ++ [wByte] := by
      rw [show w + 1 = (beMir value).length + 1 by rw [beMir_length value]]
      rw [List.take_append]
      simp [List.take_of_length_le (Nat.le_succ (beMir value).length)]
    simp only [out2, htake, mirBytesToUInt8, List.map_append, List.map_cons, List.map_nil, hwByte_u8]
    rw [← mirBytesToUInt8, mirBytesToUInt8_beMir]
    rfl

/-! ## 5. SP 800-185 §3.3 Empty-Customization Fallback & 32-Byte Squeeze Weld -/

/-- **SP 800-185 §3.3 Empty-Customization Fallback on Extracted MIR**:
    When `name` and `customization` are both empty, `Cshake256::new` and `Cshake256::customized`
    evaluate to the exact `Shake256::new` sponge (`suffix = 0x1f`). -/
theorem cshake256_empty_eq_shake256_mir :
    let empty := Aeneas.Std.Array.to_slice (Aeneas.Std.Array.empty Std.U8)
    obend_keccak.Cshake256.new empty empty = obend_keccak.Shake256.new ∧
    obend_keccak.Cshake256.customized empty = obend_keccak.Shake256.new := by
  dsimp only
  have hempty : core.slice.Slice.is_empty (Aeneas.Std.Array.to_slice (Aeneas.Std.Array.empty Std.U8)) =
      .ok true := rfl
  refine ⟨?_, ?_⟩
  · unfold obend_keccak.Cshake256.new obend_keccak.Shake256.new
    simp [hempty]
  · unfold obend_keccak.Cshake256.customized obend_keccak.Cshake256.new obend_keccak.Shake256.new
    simp [hempty]

private theorem stateByte_eq_mir_lane_shift (lanes : Aeneas.Std.Array Std.U64 25#usize)
    (k : Nat) (hk : k < 32) :
    let lane := lanes.val.getD (k / 8) 0#u64
    UScalar.cast .U8 ((⟨lane.bv >>> (8 * (k % 8))⟩ : Std.U64) &&& 255#u64) =
      ⟨(stateByte (mirToSpecState lanes) k).toBitVec⟩ := by
  dsimp only
  apply UScalar.ext
  change (((lanes.val.getD (k / 8) 0#u64).bv >>> (8 * (k % 8)) &&& 255#64).setWidth 8) = _
  rw [bv64_and_255_setWidth8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hdiv4 : k / 8 < 4 := by omega
  have hget : (mirToSpecState lanes).getD (k / 8) zeroLane = (lanes.val.getD (k / 8) 0#u64).bv := by
    match hq : k / 8, hdiv4 with
    | 0, _ => simp [mirToSpecState, mirToKState, KState.toState, UInt64.toBitVec_ofBitVec]
    | 1, _ => simp [mirToSpecState, mirToKState, KState.toState, UInt64.toBitVec_ofBitVec]
    | 2, _ => simp [mirToSpecState, mirToKState, KState.toState, UInt64.toBitVec_ofBitVec]
    | 3, _ => simp [mirToSpecState, mirToKState, KState.toState, UInt64.toBitVec_ofBitVec]
    | n + 4, h => omega
  unfold stateByte
  rw [hget]
  simp [UInt8.toNat_ofNat']

/-- **32-Byte Sponge Squeeze Spec Weld (`squeeze_loop_32_refines_spec`)**:
    For every 25-lane permuted state `lanes`, `KeccakSponge.squeeze_loop` over a 32-byte buffer
    from byte offset `0` produces the exact 32-byte digest `Obend.Digest.Cshake256.squeeze32 (mirToSpecState lanes)`. -/
theorem squeeze_loop_32_refines_spec (lanes : Aeneas.Std.Array Std.U64 25#usize) :
    let initSlice := Aeneas.Std.Array.to_slice (Aeneas.Std.Array.repeat 32#usize 0#u8)
    ∃ outSlice : Slice Std.U8,
      obend_keccak.KeccakSponge.squeeze_loop 136#usize lanes 0#usize initSlice 32#usize 0#usize =
        .ok (lanes, 32#usize, outSlice) ∧
      mirBytesToUInt8 outSlice.val = Obend.Digest.Cshake256.squeeze32 (mirToSpecState lanes) := by
  dsimp only
  let specByte (j : Nat) : Std.U8 := ⟨(stateByte (mirToSpecState lanes) j).toBitVec⟩
  have hslice_len (k : Nat) (hk : k ≤ 32) :
      (((List.range k).map specByte) ++ List.replicate (32 - k) 0#u8).length ≤ Usize.max := by
    have h32max : 32 ≤ Usize.max := by
      simpa only [usize_ofNat_val 32 (by decide)] using Usize.val_le_max 32#usize
    simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
    omega
  let sliceAt (k : Nat) : Slice Std.U8 :=
    if hk : k ≤ 32 then ⟨((List.range k).map specByte) ++ List.replicate (32 - k) 0#u8, hslice_len k hk⟩
    else Aeneas.Std.Array.to_slice (Aeneas.Std.Array.repeat 32#usize 0#u8)
  let st (k : Nat) : Aeneas.Std.Array Std.U64 25#usize × Std.Usize × Slice Std.U8 × Std.Usize :=
    (lanes, UScalar.ofNat .Usize k, sliceAt k, UScalar.ofNat .Usize k)
  let body := fun (a1, i1, out1, w1) =>
    obend_keccak.KeccakSponge.squeeze_loop.body 136#usize 32#usize a1 i1 out1 w1
  have hstep : ∀ k, k < 32 → body (st k) = .ok (.cont (st (k + 1))) := by
    intro k hk
    have hk32 : k ≤ 32 := Nat.le_of_lt hk
    have hk1_32 : k + 1 ≤ 32 := hk
    let kU : Std.Usize := UScalar.ofNat .Usize k
    have hkU_val : kU.val = k := usize_ofNat_val k (by omega)
    have hlt : kU < 32#usize := by rw [UScalar.lt_iff_val, hkU_val, usize_ofNat_val 32 (by decide)]; exact hk
    have hne136 : kU ≠ 136#usize := by
      intro he; have hv := congrArg UScalar.val he; rw [hkU_val, usize_ofNat_val 136 (by decide)] at hv; omega
    have hdiv : (kU / 8#usize : Result Std.Usize) = .ok (UScalar.ofNat .Usize (k / 8)) := by
      simp only [hDiv_uscalar_eq, usize_ofNat_val 8 (by decide)]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change (kU.bv / (8#usize).bv).toNat = (UScalar.ofNat .Usize (k / 8)).val
      rw [BitVec.toNat_udiv, usize_ofNat_val (k / 8) (by omega)]
      change kU.val / 8 = k / 8
      rw [hkU_val]
    have hidx : Aeneas.Std.Array.index_usize lanes (UScalar.ofNat .Usize (k / 8)) =
        .ok (lanes.val.getD (k / 8) 0#u64) := by
      have hv := usize_ofNat_val (k / 8) (by omega)
      have hdlt : (UScalar.ofNat .Usize (k / 8)).val < (25#usize).val := by
        rw [hv, usize_ofNat_val 25 (by decide)]; omega
      have hg := array_index_getD lanes (UScalar.ofNat .Usize (k / 8)) 0#u64 hdlt
      rw [hv] at hg; exact hg
    have hmod : (kU % 8#usize : Result Std.Usize) = .ok (UScalar.ofNat .Usize (k % 8)) := by
      simp only [hMod_uscalar_eq, usize_ofNat_val 8 (by decide)]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change (kU.bv % (8#usize).bv).toNat = (UScalar.ofNat .Usize (k % 8)).val
      rw [BitVec.toNat_umod, usize_ofNat_val (k % 8) (by omega)]
      change kU.val % 8 = k % 8
      rw [hkU_val]
    have hmul : (8#usize * UScalar.ofNat .Usize (k % 8) : Result Std.Usize) =
        .ok (UScalar.ofNat .Usize (8 * (k % 8))) := by
      have hk8_val := usize_ofNat_val (k % 8) (by omega)
      have hm_lt : (8#usize).val * (UScalar.ofNat .Usize (k % 8)).val < 2 ^ (UScalarTy.Usize.numBits) := by
        rw [usize_ofNat_val 8 (by decide), hk8_val]; change 8 * (k % 8) < 2 ^ 64; omega
      simp only [hMul_uscalar_eq, hm_lt, ite_true]
      apply congrArg Result.ok; apply UScalar.eq_of_val_eq
      change ((8#usize).bv * (UScalar.ofNat .Usize (k % 8)).bv).toNat =
        (UScalar.ofNat .Usize (8 * (k % 8))).val
      rw [BitVec.toNat_mul, usize_ofNat_val (8 * (k % 8)) (by omega)]
      change (8 * (UScalar.ofNat .Usize (k % 8)).val) % (2 ^ 64) = 8 * (k % 8)
      rw [hk8_val, Nat.mod_eq_of_lt (by omega)]
    let shU32 : Std.U32 := UScalar.cast .U32 (UScalar.ofNat .Usize (8 * (k % 8)))
    have hsh_val : shU32.val = 8 * (k % 8) := by
      change (((BitVec.ofNat 64 (8 * (k % 8))).setWidth 32)).toNat = 8 * (k % 8)
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hshr : (lanes.val.getD (k / 8) 0#u64 >>> shU32 : Result Std.U64) =
        .ok ⟨(lanes.val.getD (k / 8) 0#u64).bv >>> (8 * (k % 8))⟩ := by
      have hslt : shU32.val < UScalarTy.U64.numBits := by rw [hsh_val]; change 8 * (k % 8) < 64; omega
      simp only [hShrU_uscalar_eq, hslt, ite_true]
      rw [hsh_val]
    let byteK := UScalar.cast .U8 ((⟨(lanes.val.getD (k / 8) 0#u64).bv >>> (8 * (k % 8))⟩ : Std.U64) &&& 255#u64)
    have hbyteK : byteK = specByte k := stateByte_eq_mir_lane_shift lanes k hk
    have hsupd : Slice.update (sliceAt k) kU byteK = .ok (sliceAt (k + 1)) := by
      have hlen_sk : (sliceAt k).val.length = 32 := by
        simp [sliceAt, hk32]
      have hklt_sk : kU.val < (sliceAt k).val.length := by rw [hkU_val, hlen_sk]; exact hk
      unfold Slice.update
      rw [dite_eq_left_of_eq_true (eq_true hklt_sk)]
      apply congrArg Result.ok
      apply Slice.ext
      simp only [sliceAt, hk32, hk1_32, ↓reduceDIte, hkU_val, hbyteK]
      have hpre_len : ((List.range k).map specByte).length = k := by simp
      have hrest_pos : 0 < (List.replicate (32 - k) 0#u8).length := by simp; omega
      have hset := set_prefix_drop ((List.range k).map specByte) (List.replicate (32 - k) 0#u8)
        (specByte k) hrest_pos
      rw [hpre_len] at hset
      have hdrop_rep : (List.replicate (32 - k) 0#u8).drop 1 = List.replicate (32 - (k + 1)) 0#u8 := by
        rw [show 32 - k = (32 - (k + 1)) + 1 by omega, List.replicate_succ]
        rfl
      rw [hset, hdrop_rep, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
      rfl
    have htake1 : obend_keccak.take_one = .ok 1#usize := rfl
    have hadd_k := checked_add_ofNat_usize k (by omega)
    simp only [body, st, kU, shU32, byteK, obend_keccak.KeccakSponge.squeeze_loop.body,
      hlt, ite_true, hne136, ite_false, hdiv, hidx, hmod, hmul, hshr, hsupd, htake1, hadd_k,
      bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  have hdone : body (st 32) = .ok (.done (lanes, 32#usize, sliceAt 32)) := by
    have hnot : ¬ (UScalar.ofNat .Usize 32 < 32#usize) := by decide
    simp only [body, st, obend_keccak.KeccakSponge.squeeze_loop.body, hnot, ite_false]
  refine ⟨sliceAt 32, ?_, ?_⟩
  · have h0 : sliceAt 0 = Aeneas.Std.Array.to_slice (Aeneas.Std.Array.repeat 32#usize 0#u8) := by
      apply Slice.ext
      simp [sliceAt, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.repeat, usize_ofNat_val 32 (by decide)]
    unfold obend_keccak.KeccakSponge.squeeze_loop
    rw [← h0]
    exact loop_det_steps body st (lanes, 32#usize, sliceAt 32) 32 (by decide) hstep hdone
  · have h32 : (32 : Nat) ≤ 32 := Nat.le_refl 32
    simp only [sliceAt, h32, ↓reduceDIte, Nat.sub_self, List.replicate_zero, List.append_nil,
      mirBytesToUInt8, List.map_map, specByte]
    have hid : ((fun b : Std.U8 => UInt8.ofBitVec b.bv) ∘
        (fun j : Nat => (⟨(stateByte (mirToSpecState lanes) j).toBitVec⟩ : Std.U8))) =
        stateByte (mirToSpecState lanes) := by
      funext j; simp
    rw [hid]
    rfl

end ObendKeccak.SpecWeld
