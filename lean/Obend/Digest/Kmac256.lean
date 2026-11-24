module
public import Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Spec

/-!
# NIST SP 800-185 KMAC256 with a 256-bit tag, and resuming a sponge from an absorbed state

  `KMAC256(K, X, 256, S) = cSHAKE256(bytepad(encode_string(K), 136) ‖ X ‖ right_encode(256),
                                     256, "KMAC", S)`

The function-name block and the key block both end on a rate boundary, so a caller can absorb
them once and resume from the 25-word state for each message. `kmac256Bytes_resume` and
`namedBytes_resume` state that this gives the one-shot digest. No PRF claim is made here.
-/

public section
namespace Obend.Digest.Kmac256
open Cshake256
set_option autoImplicit false

/-- ASCII `KMAC`, the SP 800-185 function name. -/
@[expose] def functionName : List UInt8 := [75, 77, 65, 67]

/-- SP 800-185 `right_encode`: the minimal big-endian bytes, then their count. -/
@[expose] def rightEncode (value : Nat) : List UInt8 :=
  let bytes := natBytesBE value
  bytes ++ [UInt8.ofNat bytes.length]

/-- `bytepad(encode_string("KMAC") ‖ encode_string(S), 136)`. -/
@[expose] def kmacPrefix (custom : List UInt8) : List UInt8 :=
  bytepad (encodeString functionName ++ encodeString custom) rateBytes

/-- `bytepad(encode_string(K), 136)`. -/
@[expose] def kmacKeyBlock (key : List UInt8) : List UInt8 :=
  bytepad (encodeString key) rateBytes

/-- KMAC256 with a 32-byte tag. -/
def kmac256Bytes (key custom input : List UInt8) : List UInt8 :=
  squeeze32 (absorbPadded
    (padForRate (kmacPrefix custom ++ (kmacKeyBlock key ++ input ++ rightEncode 256)) 0x04))

/-- Absorb every whole rate block of `bytes` into `state`. -/
def absorbBlocks (state : State) (bytes : List UInt8) : State :=
  absorbFrom (bytes.length / rateBytes) state bytes

/-- Pad `tail` and absorb its blocks into an already absorbed `state`. -/
def resumeFromState (state : State) (tail : List UInt8) (suffix : UInt8) : State :=
  absorbBlocks state (padForRate tail suffix)

/-- The state after the function-name block and the key block. -/
def kmacMidstate (key custom : List UInt8) : State :=
  absorbBlocks zeroState (kmacPrefix custom ++ kmacKeyBlock key)

/-- The state after the cSHAKE256 function-name and customization block. -/
def cshakeMidstate (name custom : List UInt8) : State :=
  absorbBlocks zeroState (bytepad (encodeString name ++ encodeString custom) rateBytes)

theorem rightEncode_256 : rightEncode 256 = [1, 0, 2] := by decide +kernel

theorem bytepad_length_mod (x : List UInt8) : (bytepad x rateBytes).length % rateBytes = 0 := by
  simp only [bytepad, rateBytes, Nat.reduceEqDiff, ite_false, List.length_append,
    List.length_replicate]
  omega

/-- `count` whole blocks of `p`, then the rest of the stream from the state they produce. -/
theorem absorbFrom_append (count : Nat) (state : State) (p rest : List UInt8) (n : Nat)
    (hp : p.length = count * rateBytes) :
    absorbFrom (count + n) state (p ++ rest) = absorbFrom n (absorbFrom count state p) rest := by
  induction count generalizing state p with
  | zero =>
    have empty : p = [] := List.length_eq_zero_iff.mp (by simpa using hp)
    subst empty
    simp [absorbFrom]
  | succ count ih =>
    have hlen : rateBytes ≤ p.length := by
      rw [hp, Nat.add_mul]
      omega
    rw [show count + 1 + n = (count + n) + 1 by omega, absorbFrom, absorbFrom,
      List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen]
    apply ih
    rw [List.length_drop, hp, Nat.add_mul]
    omega

theorem padForRate_append (p tail : List UInt8) (suffix : UInt8)
    (hp : p.length % rateBytes = 0) :
    padForRate (p ++ tail) suffix = p ++ padForRate tail suffix := by
  have hc : (p ++ tail).length % rateBytes = tail.length % rateBytes := by
    simp only [List.length_append, rateBytes] at *
    omega
  unfold padForRate
  simp only [hc]
  split <;> simp [List.append_assoc]

/-- Absorbing a rate-aligned prefix once and resuming on the tail is the one-shot sponge. -/
theorem absorbPadded_resume (p tail : List UInt8) (suffix : UInt8)
    (hp : p.length % rateBytes = 0) :
    absorbPadded (padForRate (p ++ tail) suffix) =
      resumeFromState (absorbBlocks zeroState p) tail suffix := by
  rw [padForRate_append _ _ _ hp]
  unfold absorbPadded resumeFromState absorbBlocks
  have count : (p ++ padForRate tail suffix).length / rateBytes =
      p.length / rateBytes + (padForRate tail suffix).length / rateBytes := by
    simp only [List.length_append, rateBytes] at *
    omega
  rw [count]
  exact absorbFrom_append _ _ _ _ _ (by simp only [rateBytes] at *; omega)

/-- KMAC256 resumed from the state after both static blocks. -/
theorem kmac256Bytes_resume (key custom input : List UInt8) :
    kmac256Bytes key custom input =
      squeeze32 (resumeFromState (kmacMidstate key custom) (input ++ rightEncode 256) 0x04) := by
  have aligned : (kmacPrefix custom ++ kmacKeyBlock key).length % rateBytes = 0 := by
    have a := bytepad_length_mod (encodeString functionName ++ encodeString custom)
    have b := bytepad_length_mod (encodeString key)
    simp only [kmacPrefix, kmacKeyBlock, List.length_append, rateBytes] at *
    omega
  unfold kmac256Bytes kmacMidstate
  rw [← absorbPadded_resume _ _ _ aligned]
  simp only [List.append_assoc]

/-- cSHAKE256 with a nonempty name or customization, resumed from its prefix state. -/
theorem namedBytes_resume (name custom input : List UInt8) (h : ¬(name = [] ∧ custom = [])) :
    namedBytes name custom input =
      squeeze32 (resumeFromState (cshakeMidstate name custom) input 0x04) := by
  unfold namedBytes paddedMessage cshakeMidstate
  rw [ite_eq_right h, absorbPadded_resume _ _ _ (bytepad_length_mod _)]

end Obend.Digest.Kmac256
