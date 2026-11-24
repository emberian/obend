module
public import Obend.Digest.Cshake256.Spec
public import Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast

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

/-! ## Zero-Copy `ByteArray` & Unboxed `KState` KMAC256 Execution (`@[csimp]`) -/

/-- Build `kmacKeyBlock` (`bytepad(encode_string(K), 136)`) directly on `ByteArray`. -/
def kmacKeyBlockBA (key : @& ByteArray) : ByteArray :=
  let hdr := leftEncode rateBytes ++ leftEncode (8 * key.size)
  let pfx := Fast.copySlice key 0 key.size
    (Fast.pushList (ByteArray.emptyWithCapacity (hdr.length + key.size + rateBytes)) hdr)
  let zeroCount := (rateBytes - pfx.size % rateBytes) % rateBytes
  Fast.pushZeros pfx zeroCount

theorem kmacKeyBlockBA_data (key : ByteArray) :
    (kmacKeyBlockBA key).data.toList = kmacKeyBlock key.data.toList := by
  unfold kmacKeyBlockBA kmacKeyBlock bytepad
  have h136 : ¬(rateBytes = 0) := by decide
  simp only [h136, ↓reduceIte]
  let hdr := leftEncode rateBytes ++ leftEncode (8 * key.size)
  let pfx := Fast.copySlice key 0 key.size
    (Fast.pushList (ByteArray.emptyWithCapacity (hdr.length + key.size + rateBytes)) hdr)
  have hpfx : pfx.data.toList = leftEncode rateBytes ++ encodeString key.data.toList := by
    dsimp only [pfx, hdr]
    rw [Fast.copySlice_data key 0 key.size _ (by omega), Fast.pushList_data,
      Fast.emptyWithCapacity_data, List.nil_append, List.drop_zero,
      Fast.size_eq_length, List.take_length]
    simp [encodeString, List.append_assoc]
  change (Fast.pushZeros pfx ((rateBytes - pfx.size % rateBytes) % rateBytes)).data.toList = _
  rw [Fast.pushZeros_data, Fast.size_eq_length, hpfx]

/-- Pre-absorb the static KMAC256 prefix + key blocks into an unboxed 25-word `KState`. -/
def kmacMidstateS (key custom : @& ByteArray) : Fast.KState :=
  let nameBA : ByteArray := Fast.pushList (ByteArray.emptyWithCapacity 4) functionName
  let pfx := Fast.namedPrefixBA nameBA custom
  let s1 := Fast.absorbLoop pfx (pfx.size / rateBytes) 0 Fast.zeroS
  let kb := kmacKeyBlockBA key
  Fast.absorbLoop kb (kb.size / rateBytes) 0 s1

theorem kmacMidstateS_toState (key custom : ByteArray) :
    (kmacMidstateS key custom).toState = kmacMidstate key.data.toList custom.data.toList := by
  unfold kmacMidstateS kmacMidstate absorbBlocks kmacPrefix
  let nameBA : ByteArray := Fast.pushList (ByteArray.emptyWithCapacity 4) functionName
  have hname : nameBA.data.toList = functionName := by
    dsimp only [nameBA]
    rw [Fast.pushList_data, Fast.emptyWithCapacity_data, List.nil_append]
  let pfx := Fast.namedPrefixBA nameBA custom
  have hpfx : pfx.data.toList = bytepad (encodeString functionName ++ encodeString custom.data.toList) rateBytes := by
    simpa [pfx, hname] using Fast.namedPrefixBA_data nameBA custom
  let kb := kmacKeyBlockBA key
  have hkb : kb.data.toList = kmacKeyBlock key.data.toList := kmacKeyBlockBA_data key
  have hpfx_mod : pfx.data.toList.length % rateBytes = 0 := by
    rw [hpfx]; exact bytepad_length_mod _
  have hkb_mod : kb.data.toList.length % rateBytes = 0 := by
    rw [hkb]; exact bytepad_length_mod _
  have hpfx_len : pfx.data.toList.length = (pfx.size / rateBytes) * rateBytes := by
    rw [Fast.size_eq_length]
    have h := Nat.div_add_mod pfx.data.toList.length rateBytes
    rw [hpfx_mod, Nat.add_zero, Nat.mul_comm] at h
    exact h.symm
  change (Fast.absorbLoop kb (kb.size / rateBytes) 0
      (Fast.absorbLoop pfx (pfx.size / rateBytes) 0 Fast.zeroS)).toState = _
  rw [Fast.absorb_fast_eq, Fast.absorb_fast_eq, Fast.zeroS_toState, List.drop_zero, List.drop_zero,
    ← hpfx, ← hkb]
  have hdiv : (pfx.data.toList ++ kb.data.toList).length / rateBytes =
      pfx.size / rateBytes + kb.size / rateBytes := by
    rw [List.length_append, hpfx_len, ← Fast.size_eq_length kb]
    have hpos : 0 < rateBytes := by decide
    rw [Nat.mul_comm _ rateBytes, Nat.mul_add_div hpos]
  rw [hdiv, Fast.absorbFrom_append_exact (pfx.size / rateBytes) (kb.size / rateBytes)
    zeroState _ _ hpfx_len]

/-- Stream `input : @& ByteArray` without copying full rate blocks, append `rightEncode 256` (`[1,0,2]`)
and multi-rate `0x04` padding on the short remainder, and squeeze 32 bytes into `ByteArray`. -/
def kmacResumeByteArray (mid : Fast.KState) (input : @& ByteArray) : ByteArray :=
  let full := input.size / rateBytes
  let rem := input.size % rateBytes
  let s1 := Fast.absorbLoop input full 0 mid
  let tail0 := Fast.copySlice input (full * rateBytes) rem (ByteArray.emptyWithCapacity (2 * rateBytes))
  let tail1 := ((tail0.push 1).push 0).push 2
  let padded := Fast.padBA tail1 0x04
  let s2 := Fast.absorbLoop padded (padded.size / rateBytes) 0 s1
  Fast.squeezeByteArray s2

theorem kmacResumeByteArray_data (mid : Fast.KState) (input : ByteArray) :
    (kmacResumeByteArray mid input).data.toList =
      squeeze32 (resumeFromState mid.toState (input.data.toList ++ rightEncode 256) 0x04) := by
  unfold kmacResumeByteArray resumeFromState absorbBlocks
  let L := input.data.toList
  have hbsize : input.size = L.length := Fast.size_eq_length input
  let full := input.size / rateBytes
  let rem := input.size % rateBytes
  have hdivmod : full * rateBytes + rem = input.size := by
    have h := Nat.div_add_mod input.size rateBytes
    rw [Nat.mul_comm] at h
    exact h
  have hdrop_len : (L.drop (full * rateBytes)).length = rem := by
    rw [List.length_drop, ← hbsize]; omega
  let tail0 := Fast.copySlice input (full * rateBytes) rem (ByteArray.emptyWithCapacity (2 * rateBytes))
  let tail1 := ((tail0.push 1).push 0).push 2
  have htail1 : tail1.data.toList = L.drop (full * rateBytes) ++ rightEncode 256 := by
    dsimp only [tail1, tail0]
    rw [Fast.push_data, Fast.push_data, Fast.push_data,
      Fast.copySlice_data input (full * rateBytes) rem _ (by omega),
      Fast.emptyWithCapacity_data, List.nil_append,
      List.take_of_length_le (by rw [hdrop_len]; exact Nat.le_refl _), rightEncode_256]
    simp only [List.append_assoc, List.singleton_append]
    rfl
  let padded := Fast.padBA tail1 0x04
  have hpadded : padded.data.toList = padForRate (L.drop (full * rateBytes) ++ rightEncode 256) 0x04 := by
    dsimp only [padded]
    rw [Fast.padBA_data, htail1]
  have htake_len : (L.take (full * rateBytes)).length = full * rateBytes :=
    List.length_take_of_le (by rw [← hbsize]; omega)
  have htake_mod : (L.take (full * rateBytes)).length % rateBytes = 0 := by
    rw [htake_len]; exact Nat.mul_mod_left full rateBytes
  have hsplit_all : L ++ rightEncode 256 =
      L.take (full * rateBytes) ++ (L.drop (full * rateBytes) ++ rightEncode 256) := by
    rw [← List.append_assoc, List.take_append_drop]
  have hpad_split : padForRate (L ++ rightEncode 256) 0x04 =
      L.take (full * rateBytes) ++ padded.data.toList := by
    rw [hsplit_all, Fast.padForRate_append_aligned _ _ _ htake_mod, hpadded]
  change (Fast.squeezeByteArray (Fast.absorbLoop padded (padded.size / rateBytes) 0
      (Fast.absorbLoop input full 0 mid))).data.toList =
    squeeze32 (absorbFrom ((padForRate (L ++ rightEncode 256) 0x04).length / rateBytes)
      mid.toState (padForRate (L ++ rightEncode 256) 0x04))
  rw [Fast.squeezeByteArray_data, Fast.squeeze_fast_eq, Fast.absorb_fast_eq, List.drop_zero]
  have hs1 : (Fast.absorbLoop input full 0 mid).toState = absorbFrom full mid.toState L := by
    simpa [L, List.drop_zero] using Fast.absorb_fast_eq input full 0 mid
  rw [hs1, hpad_split]
  have htot_div : (L.take (full * rateBytes) ++ padded.data.toList).length / rateBytes =
      full + padded.size / rateBytes := by
    rw [List.length_append, htake_len, ← Fast.size_eq_length padded]
    have hpos : 0 < rateBytes := by decide
    rw [Nat.mul_comm full rateBytes, Nat.mul_add_div hpos]
  rw [htot_div, Fast.absorbFrom_append_exact full _ mid.toState _ _ htake_len,
    Fast.absorbFrom_take_blocks full mid.toState L (by rw [← hbsize]; omega)]

/-- Zero-copy `ByteArray` KMAC256 (empty intermediate `List UInt8` allocations). -/
def kmac256ByteArrayFast (key custom input : @& ByteArray) : ByteArray :=
  kmacResumeByteArray (kmacMidstateS key custom) input

@[simp] theorem kmac256ByteArrayFast_size (key custom input : ByteArray) :
    (kmac256ByteArrayFast key custom input).size = 32 := by
  simp [kmac256ByteArrayFast, kmacResumeByteArray]

theorem kmac256ByteArrayFast_eq (key custom input : ByteArray) :
    (kmac256ByteArrayFast key custom input).data.toList =
      kmac256Bytes key.data.toList custom.data.toList input.data.toList := by
  rw [kmac256ByteArrayFast, kmacResumeByteArray_data, kmacMidstateS_toState, ← kmac256Bytes_resume]

def kmac256Fast (key custom input : List UInt8) : List UInt8 :=
  (kmac256ByteArrayFast
    (Fast.pushList ByteArray.empty key)
    (Fast.pushList ByteArray.empty custom)
    (Fast.pushList ByteArray.empty input)).data.toList

@[csimp] theorem kmac256Bytes_eq_fast : @kmac256Bytes = @kmac256Fast := by
  funext key custom input
  unfold kmac256Fast
  rw [kmac256ByteArrayFast_eq]
  simp [Fast.pushList_data]

end Obend.Digest.Kmac256
