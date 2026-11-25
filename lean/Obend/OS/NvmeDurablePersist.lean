module
public import Obend.Digest.Cshake256.Seam
public import Obend.Digest.HashBytes
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes

public section
namespace Obend.OS.NvmeDurablePersist

open Obend.Digest.Cshake256
open Obend.Digest.Cshake256.Native
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Parameterized Policy, Turn Records & Pure-`ByteArray` Sector Primitives -/

/-- Parameterized admission & storage policy (no hardcoded 8-turn or 20-unit ceilings). -/
structure Policy where
  maxTurns : Nat
  budgetCap : Nat
  maxPayload : Nat := 4096
  deriving DecidableEq, Repr

structure Record where
  principal : Nat
  nonce : Nat
  nullifier : Nat
  cost : Nat
  payload : ByteArray
  deriving DecidableEq, Inhabited

def Record.fits (pol : Policy) (r : Record) : Prop :=
  r.principal < 2 ^ 64 ∧ r.nonce < 2 ^ 64 ∧ r.nullifier < 2 ^ 64 ∧
  r.cost < 2 ^ 64 ∧ r.payload.size ≤ pol.maxPayload ∧ r.payload.size < 2 ^ 64

def spent (xs : List Record) (principal : Nat) : Nat :=
  ((xs.filter (fun r => r.principal == principal)).map Record.cost).sum

def maxNullifier (xs : List Record) : Nat :=
  xs.foldl (fun acc r => max acc r.nullifier) 0

def remainingWith (pol : Policy) (priorSpent : Nat → Nat) (xs : List Record) (principal : Nat) : Nat :=
  pol.budgetCap - (priorSpent principal + spent xs principal)

def remaining (pol : Policy) (xs : List Record) (principal : Nat) : Nat :=
  pol.budgetCap - spent xs principal

inductive Decision | refuse | fresh | cached (generation : Nat) deriving DecidableEq, Repr

/-- Receipts are one-based global generation numbers (`baseGen + idx + 1`).
The authenticated channel principal is checked before any cached receipt is disclosed. -/
def requestWith (pol : Policy) (baseGen checkpointNullifier : Nat) (priorSpent : Nat → Nat)
    (xs : List Record) (principal : Nat) (r : Record) : Decision :=
  if r.principal ≠ principal then .refuse
  else if r ∈ xs then .cached (baseGen + xs.idxOf r + 1)
  else if decide (xs.length < pol.maxTurns ∧ 0 < r.cost ∧
      r.cost ≤ remainingWith pol priorSpent xs principal ∧
      checkpointNullifier < r.nullifier ∧ 0 < r.nullifier ∧
      r.principal < 2 ^ 64 ∧ r.nonce < 2 ^ 64 ∧ r.nullifier < 2 ^ 64 ∧
      r.cost < 2 ^ 64 ∧ r.payload.size ≤ pol.maxPayload ∧ r.payload.size < 2 ^ 64) &&
    xs.all (fun p => decide (p.nullifier < r.nullifier) &&
      !(p.principal == principal && p.nonce == r.nonce))
  then .fresh else .refuse

def request (pol : Policy) (xs : List Record) (principal : Nat) (r : Record) : Decision :=
  requestWith pol 0 0 (fun _ => 0) xs principal r

theorem replayWith (pol : Policy) (baseGen cpNull : Nat) (priorSpent : Nat → Nat)
    (xs : List Record) {r : Record} (h : r ∈ xs) :
    requestWith pol baseGen cpNull priorSpent xs r.principal r = .cached (baseGen + xs.idxOf r + 1) := by
  simp [requestWith, h]

theorem replay (pol : Policy) (xs : List Record) {r : Record} (h : r ∈ xs) :
    request pol xs r.principal r = .cached (xs.idxOf r + 1) := by
  simpa [request] using replayWith pol 0 0 (fun _ => 0) xs h

/-! ## 2. Real 512-Byte `ByteArray` LBA Sectors & `cSHAKE256` Superblock / WAL Encoding -/

abbrev Sector := ByteArray
def sectorSize : Nat := 512

def byteAt (ba : ByteArray) (i : Nat) : UInt8 :=
  if h : i < ba.size then ba[i] else 0

private theorem ba_length (ba : ByteArray) : ba.data.toList.length = ba.size := rfl

private theorem emptyWithCapacity_toList (n : Nat) :
    (ByteArray.emptyWithCapacity n).data.toList = [] := rfl

def pushZeros : Nat → ByteArray → ByteArray
  | 0, out => out
  | k + 1, out => pushZeros k (out.push 0)

theorem pushZeros_toList (k : Nat) (out : ByteArray) :
    (pushZeros k out).data.toList = out.data.toList ++ List.replicate k 0 := by
  induction k generalizing out with
  | zero => simp [pushZeros]
  | succ k ih =>
    rw [pushZeros, ih, ByteArray.push, Array.toList_push, List.append_assoc,
      List.singleton_append, ← List.replicate_succ]

theorem pushZeros_size (k : Nat) (out : ByteArray) : (pushZeros k out).size = out.size + k := by
  have h := congrArg List.length (pushZeros_toList k out)
  rw [ba_length, List.length_append, ba_length, List.length_replicate] at h
  exact h

def padSector (ba : ByteArray) : Sector :=
  if ba.size ≤ sectorSize then pushZeros (sectorSize - ba.size) ba
  else ba.extract 0 sectorSize

theorem padSector_toList {ba : ByteArray} (h : ba.size ≤ sectorSize) :
    (padSector ba).data.toList = ba.data.toList ++ List.replicate (sectorSize - ba.size) 0 := by
  simp [padSector, h, pushZeros_toList]

theorem padSector_size (ba : ByteArray) : (padSector ba).size = sectorSize := by
  unfold padSector
  split
  · rw [pushZeros_size]; omega
  · simp [ByteArray.size_extract]; omega

def zeroSector : Sector := pushZeros sectorSize (ByteArray.emptyWithCapacity sectorSize)

def readBEU64 (ba : ByteArray) (off : Nat) : UInt64 :=
  let b0 := (byteAt ba off).toUInt64
  let b1 := (byteAt ba (off + 1)).toUInt64
  let b2 := (byteAt ba (off + 2)).toUInt64
  let b3 := (byteAt ba (off + 3)).toUInt64
  let b4 := (byteAt ba (off + 4)).toUInt64
  let b5 := (byteAt ba (off + 5)).toUInt64
  let b6 := (byteAt ba (off + 6)).toUInt64
  let b7 := (byteAt ba (off + 7)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
  (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

private theorem byteAt_eq_list_getD (ba : ByteArray) (i : Nat) :
    byteAt ba i = ba.data.toList.getD i 0 := by
  unfold byteAt
  by_cases hi : i < ba.size
  · have hli : i < ba.data.toList.length := by rw [ba_length]; exact hi
    rw [dite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hli, Option.getD_some]
    rfl
  · have hli : ba.data.toList.length ≤ i := by rw [ba_length]; exact Nat.le_of_not_lt hi
    rw [dite_eq_right hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none hli, Option.getD_none]

private theorem be8_getD (v : UInt64) (i : Nat) (hi : i < 8) :
    (be 8 v.toNat).getD i 0 = (v >>> UInt64.ofNat (8 * (7 - i))).toUInt8 := by
  have h1 : be 8 v.toNat = (pushBEU64 8 v ByteArray.empty).data.toList := by
    rw [pushBEU64_toList 8 (by decide) v ByteArray.empty]
    rfl
  rw [h1]
  have heq : (pushBEU64 8 v ByteArray.empty).data.toList =
      [(v >>> 56).toUInt8, (v >>> 48).toUInt8, (v >>> 40).toUInt8, (v >>> 32).toUInt8,
       (v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, (v >>> 0).toUInt8] := rfl
  rw [heq]
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem byte_lane_getLsbD (v : UInt64) (k i : Nat) (hk : k < 8) (hi : i < 64) :
    (((v >>> UInt64.ofNat (8 * k)).toUInt8.toUInt64 <<< UInt64.ofNat (8 * k)).toBitVec.getLsbD i) =
      (decide (8 * k ≤ i ∧ i < 8 * (k + 1)) && v.toBitVec.getLsbD i) := by
  have hsb : ((UInt64.ofNat (8 * k)).toBitVec % 64#64).toNat = 8 * k := by
    rw [BitVec.toNat_umod]
    change (UInt64.ofNat (8 * k)).toNat % 64 = 8 * k
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * k < 64 by omega)]
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_shiftRight]
  change ((BitVec.setWidth 64 (BitVec.setWidth 8
    (v.toBitVec >>> ((UInt64.ofNat (8 * k)).toBitVec % 64#64).toNat))) <<<
    ((UInt64.ofNat (8 * k)).toBitVec % 64#64).toNat).getLsbD i = _
  rw [hsb, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : 8 * k ≤ i
  · by_cases h2 : i < 8 * (k + 1)
    · simp only [hi, show ¬i < 8 * k by omega, show i - 8 * k < 64 by omega,
        show i - 8 * k < 8 by omega, show 8 * k + (i - 8 * k) = i by omega,
        h1, h2, and_self, decide_true, decide_false, Bool.not_false, Bool.true_and]
    · simp only [show ¬i - 8 * k < 8 by omega, h2, and_false, decide_false,
        Bool.false_and, Bool.and_false]
  · simp only [show i < 8 * k by omega, h1, false_and, decide_true, decide_false,
      Bool.not_true, Bool.false_and, Bool.and_false]

private theorem pack_u64_bytes (v : UInt64) :
    (((v >>> 56).toUInt8.toUInt64 <<< 56) |||
     ((v >>> 48).toUInt8.toUInt64 <<< 48) |||
     ((v >>> 40).toUInt8.toUInt64 <<< 40) |||
     ((v >>> 32).toUInt8.toUInt64 <<< 32) |||
     ((v >>> 24).toUInt8.toUInt64 <<< 24) |||
     ((v >>> 16).toUInt8.toUInt64 <<< 16) |||
     ((v >>> 8).toUInt8.toUInt64 <<< 8) |||
     (v >>> 0).toUInt8.toUInt64) = v := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsh0 : ∀ x : UInt64, x <<< 0 = x := fun x => by
    apply UInt64.eq_of_toBitVec_eq; simp
  have h0 : ((v >>> 0).toUInt8.toUInt64).toBitVec.getLsbD i =
      (decide (0 ≤ i ∧ i < 8) && v.toBitVec.getLsbD i) := by
    have h := byte_lane_getLsbD v 0 i (by decide) hi
    change (((v >>> 0).toUInt8.toUInt64 <<< 0).toBitVec.getLsbD i) =
      (decide (0 ≤ i ∧ i < 8) && v.toBitVec.getLsbD i) at h
    rwa [hsh0] at h
  have h1 : (((v >>> 8).toUInt8.toUInt64 <<< 8).toBitVec.getLsbD i) =
      (decide (8 ≤ i ∧ i < 16) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 1 i (by decide) hi
  have h2 : (((v >>> 16).toUInt8.toUInt64 <<< 16).toBitVec.getLsbD i) =
      (decide (16 ≤ i ∧ i < 24) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 2 i (by decide) hi
  have h3 : (((v >>> 24).toUInt8.toUInt64 <<< 24).toBitVec.getLsbD i) =
      (decide (24 ≤ i ∧ i < 32) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 3 i (by decide) hi
  have h4 : (((v >>> 32).toUInt8.toUInt64 <<< 32).toBitVec.getLsbD i) =
      (decide (32 ≤ i ∧ i < 40) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 4 i (by decide) hi
  have h5 : (((v >>> 40).toUInt8.toUInt64 <<< 40).toBitVec.getLsbD i) =
      (decide (40 ≤ i ∧ i < 48) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 5 i (by decide) hi
  have h6 : (((v >>> 48).toUInt8.toUInt64 <<< 48).toBitVec.getLsbD i) =
      (decide (48 ≤ i ∧ i < 56) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 6 i (by decide) hi
  have h7 : (((v >>> 56).toUInt8.toUInt64 <<< 56).toBitVec.getLsbD i) =
      (decide (56 ≤ i ∧ i < 64) && v.toBitVec.getLsbD i) := byte_lane_getLsbD v 7 i (by decide) hi
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  rw [h7, h6, h5, h4, h3, h2, h1, h0]
  have bandT : ∀ a b : Nat, a ≤ i → i < b → decide (a ≤ i ∧ i < b) = true :=
    fun _ _ h1 h2 => decide_eq_true ⟨h1, h2⟩
  have bandF : ∀ a b : Nat, (i < a ∨ b ≤ i) → decide (a ≤ i ∧ i < b) = false :=
    fun _ _ h => decide_eq_false (by omega)
  by_cases c0 : i < 8
  · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandF 40 48 (by omega),
      bandF 32 40 (by omega), bandF 24 32 (by omega), bandF 16 24 (by omega),
      bandF 8 16 (by omega), bandT 0 8 (by omega) c0,
      Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
  · by_cases c1 : i < 16
    · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandF 40 48 (by omega),
        bandF 32 40 (by omega), bandF 24 32 (by omega), bandF 16 24 (by omega),
        bandT 8 16 (by omega) c1, bandF 0 8 (by omega),
        Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
    · by_cases c2 : i < 24
      · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandF 40 48 (by omega),
          bandF 32 40 (by omega), bandF 24 32 (by omega), bandT 16 24 (by omega) c2,
          bandF 8 16 (by omega), bandF 0 8 (by omega),
          Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
      · by_cases c3 : i < 32
        · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandF 40 48 (by omega),
            bandF 32 40 (by omega), bandT 24 32 (by omega) c3, bandF 16 24 (by omega),
            bandF 8 16 (by omega), bandF 0 8 (by omega),
            Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
        · by_cases c4 : i < 40
          · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandF 40 48 (by omega),
              bandT 32 40 (by omega) c4, bandF 24 32 (by omega), bandF 16 24 (by omega),
              bandF 8 16 (by omega), bandF 0 8 (by omega),
              Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
          · by_cases c5 : i < 48
            · simp only [bandF 56 64 (by omega), bandF 48 56 (by omega), bandT 40 48 (by omega) c5,
                bandF 32 40 (by omega), bandF 24 32 (by omega), bandF 16 24 (by omega),
                bandF 8 16 (by omega), bandF 0 8 (by omega),
                Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
            · by_cases c6 : i < 56
              · simp only [bandF 56 64 (by omega), bandT 48 56 (by omega) c6, bandF 40 48 (by omega),
                  bandF 32 40 (by omega), bandF 24 32 (by omega), bandF 16 24 (by omega),
                  bandF 8 16 (by omega), bandF 0 8 (by omega),
                  Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
              · simp only [bandT 56 64 (by omega) hi, bandF 48 56 (by omega), bandF 40 48 (by omega),
                  bandF 32 40 (by omega), bandF 24 32 (by omega), bandF 16 24 (by omega),
                  bandF 8 16 (by omega), bandF 0 8 (by omega),
                  Bool.false_and, Bool.true_and, Bool.or_false]

theorem readBEU64_of_slice (ba : ByteArray) (off : Nat) (v : UInt64)
    (h : (ba.data.toList.drop off).take 8 = be 8 v.toNat) :
    readBEU64 ba off = v := by
  have hget : ∀ i < 8, byteAt ba (off + i) = (v >>> UInt64.ofNat (8 * (7 - i))).toUInt8 := by
    intro i hi
    rw [byteAt_eq_list_getD, ← be8_getD v i hi, ← h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi]
  unfold readBEU64
  rw [show off = off + 0 by omega, hget 0 (by decide), hget 1 (by decide), hget 2 (by decide),
    hget 3 (by decide), hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide)]
  exact pack_u64_bytes v

/-- Pure `ByteArray` append loop (zero `List` allocation). -/
def appendBytesAux (dst src : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => dst
  | rem + 1 => appendBytesAux (dst.push (byteAt src i)) src (i + 1) rem

def appendBytes (dst src : ByteArray) : ByteArray :=
  appendBytesAux dst src 0 src.size

theorem appendBytesAux_toList (dst src : ByteArray) (i rem : Nat) (h : i + rem ≤ src.size) :
    (appendBytesAux dst src i rem).data.toList =
      dst.data.toList ++ (src.data.toList.drop i).take rem := by
  induction rem generalizing dst i with
  | zero => simp [appendBytesAux]
  | succ rem ih =>
    rw [appendBytesAux, ih (dst.push (byteAt src i)) (i + 1) (by omega),
      ByteArray.push, Array.toList_push, List.append_assoc, List.singleton_append]
    congr 1
    have hlt : i < src.data.toList.length := by rw [ba_length]; omega
    rw [byteAt_eq_list_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some, List.drop_eq_getElem_cons hlt, List.take_succ_cons]

theorem appendBytes_toList (dst src : ByteArray) :
    (appendBytes dst src).data.toList = dst.data.toList ++ src.data.toList := by
  rw [appendBytes, appendBytesAux_toList dst src 0 src.size (by omega), List.drop_zero, ← ba_length, List.take_length]

theorem appendBytes_size (dst src : ByteArray) : (appendBytes dst src).size = dst.size + src.size := by
  have h := congrArg List.length (appendBytes_toList dst src)
  rw [ba_length, List.length_append, ba_length, ba_length] at h
  exact h

def sliceBytes (src : ByteArray) (start len : Nat) : ByteArray :=
  appendBytesAux (ByteArray.emptyWithCapacity len) src start len

theorem sliceBytes_toList (src : ByteArray) (start len : Nat) (h : start + len ≤ src.size) :
    (sliceBytes src start len).data.toList = (src.data.toList.drop start).take len := by
  rw [sliceBytes, appendBytesAux_toList _ src start len h, emptyWithCapacity_toList, List.nil_append]

theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b
  congr 1
  exact Array.ext' h

/-! ### Domain-Separated `cSHAKE256` Commitments -/

def superblockMagic : ByteArray := "OBNVME01".toUTF8
def walMagic : ByteArray := "OBWAL001".toUTF8
def superblockDomain : ByteArray := "OBEND.NVME.SUPERBLOCK/v1".toUTF8
def payloadDomain : ByteArray := "OBEND.NVME.PAYLOAD/v1".toUTF8
def chainDomain : ByteArray := "OBEND.NVME.CHAIN/v1".toUTF8

theorem superblockMagic_size : superblockMagic.size = 8 := by
  unfold superblockMagic; simp only [String.toUTF8_eq_toByteArray]; rfl

theorem walMagic_size : walMagic.size = 8 := by
  unfold walMagic; simp only [String.toUTF8_eq_toByteArray]; rfl

def payloadDigest (payload : ByteArray) : ByteArray :=
  cshake256Kernel payloadDomain payload

theorem payloadDigest_size (payload : ByteArray) : (payloadDigest payload).size = 32 :=
  cshake256Kernel_size payloadDomain payload

/-- Canonical 72-byte committed preimage of a turn record:
`(principal, nonce, nullifier, cost, payload.size)` in 8-byte BE + 32-byte `cSHAKE256` payload digest. -/
def recordPreimage (r : Record) : ByteArray :=
  let out := ByteArray.emptyWithCapacity 72
  let out := pushBEU64 8 (UInt64.ofNat r.principal) out
  let out := pushBEU64 8 (UInt64.ofNat r.nonce) out
  let out := pushBEU64 8 (UInt64.ofNat r.nullifier) out
  let out := pushBEU64 8 (UInt64.ofNat r.cost) out
  let out := pushBEU64 8 (UInt64.ofNat r.payload.size) out
  appendBytes out (payloadDigest r.payload)

theorem recordPreimage_toList (r : Record) :
    (recordPreimage r).data.toList =
      be 8 (UInt64.ofNat r.principal).toNat ++ be 8 (UInt64.ofNat r.nonce).toNat ++
      be 8 (UInt64.ofNat r.nullifier).toNat ++ be 8 (UInt64.ofNat r.cost).toNat ++
      be 8 (UInt64.ofNat r.payload.size).toNat ++ (payloadDigest r.payload).data.toList := by
  simp only [recordPreimage, appendBytes_toList, pushBEU64_toList 8 (by decide),
    emptyWithCapacity_toList, List.nil_append, List.append_assoc]

theorem recordPreimage_size (r : Record) : (recordPreimage r).size = 72 := by
  have h := congrArg List.length (recordPreimage_toList r)
  have hp : (payloadDigest r.payload).data.toList.length = 32 := by
    rw [ba_length]; exact payloadDigest_size r.payload
  rw [ba_length] at h
  simp only [List.length_append, length_be, hp] at h
  exact h

def genesisChainDigest : ByteArray :=
  cshake256Kernel chainDomain ByteArray.empty

theorem genesisChainDigest_size : genesisChainDigest.size = 32 :=
  cshake256Kernel_size chainDomain ByteArray.empty

def stepChainDigest (prev : ByteArray) (r : Record) : ByteArray :=
  cshake256Kernel chainDomain (appendBytes prev (recordPreimage r))

theorem stepChainDigest_size (prev : ByteArray) (r : Record) : (stepChainDigest prev r).size = 32 :=
  cshake256Kernel_size chainDomain _

def logDigest (xs : List Record) : ByteArray :=
  xs.foldl stepChainDigest genesisChainDigest

theorem logDigest_size (xs : List Record) : (logDigest xs).size = 32 := by
  unfold logDigest
  suffices ∀ (acc : ByteArray), acc.size = 32 → (xs.foldl stepChainDigest acc).size = 32 from
    this genesisChainDigest genesisChainDigest_size
  induction xs with
  | nil => intro acc h; exact h
  | cons x xs ih => intro acc _; exact ih _ (stepChainDigest_size _ _)

theorem logDigest_snoc (xs : List Record) (r : Record) :
    logDigest (xs ++ [r]) = stepChainDigest (logDigest xs) r := by
  simp [logDigest, List.foldl_append]

/-! ### Superblock Structure, 512-Byte LBA Encoding, Roundtrip & `CollisionAmong` Binding -/

structure Superblock where
  generation : UInt64
  baseGen : UInt64
  activeCount : UInt64
  highWaterNullifier : UInt64
  chainDigest : ByteArray
  tag : ByteArray
  deriving DecidableEq

def superblockBodyBytes (gen base cnt hw : UInt64) (chainDig : ByteArray) : ByteArray :=
  let out := ByteArray.emptyWithCapacity 72
  let out := appendBytes out superblockMagic
  let out := pushBEU64 8 gen out
  let out := pushBEU64 8 base out
  let out := pushBEU64 8 cnt out
  let out := pushBEU64 8 hw out
  appendBytes out chainDig

theorem superblockBodyBytes_toList (gen base cnt hw : UInt64) (chainDig : ByteArray) :
    (superblockBodyBytes gen base cnt hw chainDig).data.toList =
      superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++
      be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList := by
  simp only [superblockBodyBytes, appendBytes_toList, pushBEU64_toList 8 (by decide),
    emptyWithCapacity_toList, List.nil_append, List.append_assoc]

theorem superblockBodyBytes_size (gen base cnt hw : UInt64) {chainDig : ByteArray}
    (hc : chainDig.size = 32) :
    (superblockBodyBytes gen base cnt hw chainDig).size = 72 := by
  have h := congrArg List.length (superblockBodyBytes_toList gen base cnt hw chainDig)
  have hm : superblockMagic.data.toList.length = 8 := by rw [ba_length]; exact superblockMagic_size
  have hcl : chainDig.data.toList.length = 32 := by rw [ba_length]; exact hc
  rw [ba_length] at h
  simp only [List.length_append, length_be, hm, hcl] at h
  exact h

def superblockTag (gen base cnt hw : UInt64) (chainDig : ByteArray) : ByteArray :=
  cshake256Kernel superblockDomain (superblockBodyBytes gen base cnt hw chainDig)

theorem superblockTag_size (gen base cnt hw : UInt64) (chainDig : ByteArray) :
    (superblockTag gen base cnt hw chainDig).size = 32 :=
  cshake256Kernel_size superblockDomain _

def mkSuperblock (gen base cnt hw : UInt64) (chainDig : ByteArray) : Superblock :=
  ⟨gen, base, cnt, hw, chainDig, superblockTag gen base cnt hw chainDig⟩

def encodeSuperblock (sb : Superblock) : Sector :=
  let body := superblockBodyBytes sb.generation sb.baseGen sb.activeCount sb.highWaterNullifier sb.chainDigest
  padSector (appendBytes body sb.tag)

def zeroTail408 : ByteArray := pushZeros 408 (ByteArray.emptyWithCapacity 408)

def decodeSuperblock (sec : Sector) : Option Superblock :=
  if decide (sec.size = sectorSize ∧
      sliceBytes sec 0 8 = superblockMagic ∧
      sliceBytes sec 104 408 = zeroTail408) then
    let gen := readBEU64 sec 8
    let base := readBEU64 sec 16
    let cnt := readBEU64 sec 24
    let hw := readBEU64 sec 32
    let chainDig := sliceBytes sec 40 32
    let tag := sliceBytes sec 72 32
    if decide (tag = superblockTag gen base cnt hw chainDig) then
      some ⟨gen, base, cnt, hw, chainDig, tag⟩
    else none
  else none

private theorem drop_take_append_exact {α : Type} (a b c : List α) :
    ((a ++ b ++ c).drop a.length).take b.length = b := by
  rw [List.append_assoc, List.drop_left, List.take_left]

theorem decodeSuperblock_encodeSuperblock (gen base cnt hw : UInt64) (chainDig : ByteArray)
    (hc : chainDig.size = 32) :
    decodeSuperblock (encodeSuperblock (mkSuperblock gen base cnt hw chainDig)) =
      some (mkSuperblock gen base cnt hw chainDig) := by
  let sb := mkSuperblock gen base cnt hw chainDig
  let body := superblockBodyBytes gen base cnt hw chainDig
  have hbodySz : body.size = 72 := superblockBodyBytes_size gen base cnt hw hc
  have htagSz : sb.tag.size = 32 := superblockTag_size gen base cnt hw chainDig
  have hrawSz : (appendBytes body sb.tag).size = 104 := by rw [appendBytes_size, hbodySz, htagSz]
  let sec := encodeSuperblock sb
  have hsecSz : sec.size = 512 := padSector_size _
  have hsecList : sec.data.toList =
      superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++
      be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList ++ sb.tag.data.toList ++
      List.replicate 408 0 := by
    change (padSector (appendBytes body sb.tag)).data.toList = _
    rw [padSector_toList (by rw [hrawSz]; decide), appendBytes_toList, superblockBodyBytes_toList, hrawSz]
    simp only [sectorSize, List.append_assoc]
  have hmLen : superblockMagic.data.toList.length = 8 := by rw [ba_length]; exact superblockMagic_size
  have hcLen : chainDig.data.toList.length = 32 := by rw [ba_length]; exact hc
  have htLen : sb.tag.data.toList.length = 32 := by rw [ba_length]; exact htagSz
  have hmagic : sliceBytes sec 0 8 = superblockMagic := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList sec 0 8 (by rw [hsecSz]; decide), hsecList]
    simp only [List.drop_zero, List.append_assoc]
    rw [show (8 : Nat) = superblockMagic.data.toList.length from hmLen.symm, List.take_left]
  have htail : sliceBytes sec 104 408 = zeroTail408 := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList sec 104 408 (by rw [hsecSz]; decide), hsecList, zeroTail408, pushZeros_toList,
      emptyWithCapacity_toList, List.nil_append]
    have hpreLen : (superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++
        be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList ++ sb.tag.data.toList).length = 104 := by
      simp only [List.length_append, length_be, hmLen, hcLen, htLen]
    rw [← hpreLen, List.drop_left, List.take_of_length_le (by rw [List.length_replicate]; exact Nat.le_refl _)]
  have hgen : readBEU64 sec 8 = gen := by
    apply readBEU64_of_slice; rw [hsecList]
    have := drop_take_append_exact superblockMagic.data.toList (be 8 gen.toNat)
      (be 8 base.toNat ++ be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList ++ sb.tag.data.toList ++ List.replicate 408 0)
    simpa only [hmLen, length_be, List.append_assoc] using this
  have hbase : readBEU64 sec 16 = base := by
    apply readBEU64_of_slice; rw [hsecList]
    have := drop_take_append_exact (superblockMagic.data.toList ++ be 8 gen.toNat) (be 8 base.toNat)
      (be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList ++ sb.tag.data.toList ++ List.replicate 408 0)
    simpa only [List.length_append, hmLen, length_be, List.append_assoc] using this
  have hcnt : readBEU64 sec 24 = cnt := by
    apply readBEU64_of_slice; rw [hsecList]
    have := drop_take_append_exact (superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat)
      (be 8 cnt.toNat) (be 8 hw.toNat ++ chainDig.data.toList ++ sb.tag.data.toList ++ List.replicate 408 0)
    simpa only [List.length_append, hmLen, length_be, List.append_assoc] using this
  have hhw : readBEU64 sec 32 = hw := by
    apply readBEU64_of_slice; rw [hsecList]
    have := drop_take_append_exact (superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++ be 8 cnt.toNat)
      (be 8 hw.toNat) (chainDig.data.toList ++ sb.tag.data.toList ++ List.replicate 408 0)
    simpa only [List.length_append, hmLen, length_be, List.append_assoc] using this
  have hcd : sliceBytes sec 40 32 = chainDig := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList sec 40 32 (by rw [hsecSz]; decide), hsecList]
    have := drop_take_append_exact
      (superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++ be 8 cnt.toNat ++ be 8 hw.toNat)
      chainDig.data.toList (sb.tag.data.toList ++ List.replicate 408 0)
    simpa only [List.length_append, hmLen, length_be, hcLen, List.append_assoc] using this
  have htag : sliceBytes sec 72 32 = sb.tag := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList sec 72 32 (by rw [hsecSz]; decide), hsecList]
    have := drop_take_append_exact
      (superblockMagic.data.toList ++ be 8 gen.toNat ++ be 8 base.toNat ++ be 8 cnt.toNat ++ be 8 hw.toNat ++ chainDig.data.toList)
      sb.tag.data.toList (List.replicate 408 0)
    simpa only [List.length_append, hmLen, length_be, hcLen, htLen, List.append_assoc] using this
  change decodeSuperblock sec = some sb
  unfold decodeSuperblock
  simp only [hsecSz, sectorSize, hmagic, htail, hgen, hbase, hcnt, hhw, hcd, htag,
    and_self, decide_true, ↓reduceIte, sb, mkSuperblock]

/-- **256-bit `cSHAKE256` superblock binding**:
two superblock preimages sharing a tag either agree on EVERY field `(gen, base, cnt, hw, chainDig)`
or exhibit a concrete collision in `cshake256Bytes` over the superblock domain. -/
theorem superblock_tag_binds {g1 b1 c1 h1 g2 b2 c2 h2 : UInt64} {d1 d2 : ByteArray}
    (heq : superblockTag g1 b1 c1 h1 d1 = superblockTag g2 b2 c2 h2 d2) :
    (g1 = g2 ∧ b1 = b2 ∧ c1 = c2 ∧ h1 = h2 ∧ d1 = d2) ∨
      CollisionAmong (cshake256Bytes superblockDomain.data.toList)
        (fun x => x = (superblockBodyBytes g1 b1 c1 h1 d1).data.toList ∨
                  x = (superblockBodyBytes g2 b2 c2 h2 d2).data.toList) := by
  let p1 := (superblockBodyBytes g1 b1 c1 h1 d1).data.toList
  let p2 := (superblockBodyBytes g2 b2 c2 h2 d2).data.toList
  if hpre : p1 = p2 then
    left
    simp only [p1, p2, superblockBodyBytes_toList, List.append_assoc] at hpre
    obtain ⟨_, hpre⟩ := List.append_inj hpre rfl
    obtain ⟨hg, hpre⟩ := List.append_inj hpre (by simp)
    obtain ⟨hb, hpre⟩ := List.append_inj hpre (by simp)
    obtain ⟨hc, hpre⟩ := List.append_inj hpre (by simp)
    obtain ⟨hh, hd⟩ := List.append_inj hpre (by simp)
    exact ⟨UInt64.toNat_inj.mp (be_injective g1.toBitVec.isLt g2.toBitVec.isLt hg),
      UInt64.toNat_inj.mp (be_injective b1.toBitVec.isLt b2.toBitVec.isLt hb),
      UInt64.toNat_inj.mp (be_injective c1.toBitVec.isLt c2.toBitVec.isLt hc),
      UInt64.toNat_inj.mp (be_injective h1.toBitVec.isLt h2.toBitVec.isLt hh),
      byteArray_eq_of_toList_eq hd⟩
  else
    right
    have hl : (superblockTag g1 b1 c1 h1 d1).data.toList = (superblockTag g2 b2 c2 h2 d2).data.toList :=
      congrArg (fun b => b.data.toList) heq
    simp only [superblockTag, cshake256Kernel_toList] at hl
    exact ⟨p1, p2, .inl rfl, .inr rfl, hpre, congrArg ofBE hl⟩

/-! ### Multi-Sector WAL Record Encoding & Decoding (512-Byte `ByteArray` LBAs) -/

/-- Namespace-relative LBA geometry. Parameterized over `walSlots` and `dataSectors`. -/
structure Geometry where
  sectors : Nat
  bytesPerLba : Nat
  awupf : UInt16
  ctrlLba : Nat
  walBase : Nat
  walSlots : Nat
  dataSectors : Nat
  deriving DecidableEq, Repr

def entrySectors (g : Geometry) : Nat := 1 + g.dataSectors

def walLba (g : Geometry) (slot k : Nat) : Nat :=
  g.walBase + slot * entrySectors g + k

def Geometry.usable (pol : Policy) (g : Geometry) : Bool :=
  decide (g.bytesPerLba = sectorSize ∧ 1 ≤ g.awupf.toNat + 1 ∧
    0 < g.walSlots ∧ pol.maxTurns ≤ g.walSlots ∧
    pol.maxPayload ≤ g.dataSectors * sectorSize ∧ g.walSlots < 2 ^ 64 ∧
    g.ctrlLba < g.sectors ∧
    g.walBase + g.walSlots * entrySectors g ≤ g.sectors ∧
    (g.ctrlLba < g.walBase ∨ g.walBase + g.walSlots * entrySectors g ≤ g.ctrlLba))

theorem wal_confined {pol : Policy} {g : Geometry} (ok : g.usable pol = true)
    {slot k : Nat} (hs : slot < g.walSlots) (hk : k < entrySectors g) :
    walLba g slot k < g.sectors ∧ walLba g slot k ≠ g.ctrlLba := by
  simp only [Geometry.usable, decide_eq_true_eq] at ok
  unfold walLba
  have hmul : (slot + 1) * entrySectors g ≤ g.walSlots * entrySectors g :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

theorem walLba_inj {g : Geometry} {s1 s2 k1 k2 : Nat}
    (hk1 : k1 < entrySectors g) (hk2 : k2 < entrySectors g)
    (heq : walLba g s1 k1 = walLba g s2 k2) : s1 = s2 ∧ k1 = k2 := by
  unfold walLba at heq
  have hsub : s1 * entrySectors g + k1 = s2 * entrySectors g + k2 := by omega
  have hpos : 0 < entrySectors g := by unfold entrySectors; omega
  have hs : s1 = s2 := by
    have h1 := Nat.mul_add_div hpos s1 k1
    have h2 := Nat.mul_add_div hpos s2 k2
    rw [Nat.mul_comm] at h1 h2
    rw [Nat.div_eq_of_lt hk1, Nat.add_zero] at h1
    rw [Nat.div_eq_of_lt hk2, Nat.add_zero] at h2
    rw [← h1, ← h2, hsub]
  subst hs
  exact ⟨rfl, by omega⟩

/-- Hosted 64-slot × 9-LBA/slot geometry (`1` ctrl + `64 * (1 meta + 8 data)` = 577 sectors, 4096B payloads). -/
def hostedPolicy : Policy := ⟨64, 64, 4096⟩
def hostedGeometry : Geometry := ⟨577, 512, 0, 0, 1, 64, 8⟩

def encodeMetaSector (r : Record) : Sector :=
  let out := ByteArray.emptyWithCapacity 80
  let out := appendBytes out walMagic
  let out := pushBEU64 8 (UInt64.ofNat r.principal) out
  let out := pushBEU64 8 (UInt64.ofNat r.nonce) out
  let out := pushBEU64 8 (UInt64.ofNat r.nullifier) out
  let out := pushBEU64 8 (UInt64.ofNat r.cost) out
  let out := pushBEU64 8 (UInt64.ofNat r.payload.size) out
  let out := appendBytes out (payloadDigest r.payload)
  padSector out

def encodeDataSector (payload : ByteArray) (idx : Nat) : Sector :=
  let start := idx * sectorSize
  if start < payload.size then
    let takeLen := min sectorSize (payload.size - start)
    padSector (sliceBytes payload start takeLen)
  else zeroSector

def encodeWalSector (r : Record) (k : Nat) : Sector :=
  if k = 0 then encodeMetaSector r else encodeDataSector r.payload (k - 1)

def gatherPayload (media : Nat → Sector) (g : Geometry) (slot : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | k + 1, rem, out =>
    let idx := g.dataSectors - (k + 1)
    let take := min rem sectorSize
    let sec := media (walLba g slot (idx + 1))
    gatherPayload media g slot k (rem - take) (appendBytes out (sliceBytes sec 0 take))

def decodeRecordSectors (pol : Policy) (media : Nat → Sector) (g : Geometry) (slot : Nat) : Option Record :=
  let metaSec := media (walLba g slot 0)
  if decide (metaSec.size = sectorSize ∧ sliceBytes metaSec 0 8 = walMagic) then
    let principal := (readBEU64 metaSec 8).toNat
    let nonce := (readBEU64 metaSec 16).toNat
    let nullifier := (readBEU64 metaSec 24).toNat
    let cost := (readBEU64 metaSec 32).toNat
    let payloadLen := (readBEU64 metaSec 40).toNat
    let expectedDig := sliceBytes metaSec 48 32
    if decide (payloadLen ≤ pol.maxPayload ∧ payloadLen ≤ g.dataSectors * sectorSize) then
      let payload := gatherPayload media g slot g.dataSectors payloadLen (ByteArray.emptyWithCapacity payloadLen)
      if decide (payloadDigest payload = expectedDig) then
        some ⟨principal, nonce, nullifier, cost, payload⟩
      else none
    else none
  else none

private theorem gatherPayload_toList (media : Nat → Sector) (g : Geometry) (slot : Nat)
    (payload : ByteArray)
    (hdata : ∀ idx < g.dataSectors, media (walLba g slot (idx + 1)) = encodeDataSector payload idx)
    (k : Nat) (hk : k ≤ g.dataSectors) :
    ∀ (rem : Nat) (out : ByteArray),
      rem ≤ k * sectorSize →
      (g.dataSectors - k) * sectorSize + rem = payload.size →
      (gatherPayload media g slot k rem out).data.toList =
        out.data.toList ++ payload.data.toList.drop ((g.dataSectors - k) * sectorSize) := by
  induction k with
  | zero =>
    intro rem out hrem hsum
    have hpl : payload.data.toList.length = payload.size := ba_length payload
    have hge : payload.data.toList.length ≤ (g.dataSectors - 0) * sectorSize := by
      simp only [Nat.zero_mul] at hrem; omega
    rw [gatherPayload, List.drop_eq_nil_of_le hge, List.append_nil]
  | succ k ih =>
    intro rem out hrem hsum
    dsimp only [gatherPayload]
    let idx := g.dataSectors - (k + 1)
    have hsumIdx : idx * sectorSize + rem = payload.size := hsum
    have hidxLt : idx < g.dataSectors := by omega
    have hnext : (g.dataSectors - k) * sectorSize = idx * sectorSize + sectorSize := by
      have : g.dataSectors - k = idx + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    rw [hdata idx hidxLt]
    let take := min rem sectorSize
    have htakeLeRem : take ≤ rem := Nat.min_le_left ..
    have htakeLeSec : take ≤ sectorSize := Nat.min_le_right ..
    have hslice : (sliceBytes (encodeDataSector payload idx) 0 take).data.toList =
        (payload.data.toList.drop (idx * sectorSize)).take take := by
      unfold encodeDataSector
      by_cases hst : idx * sectorSize < payload.size
      · simp only [hst, ↓reduceIte]
        have htl : take ≤ min sectorSize (payload.size - idx * sectorSize) := by omega
        have htlBound : idx * sectorSize + min sectorSize (payload.size - idx * sectorSize) ≤ payload.size := by omega
        have hslLen : (sliceBytes payload (idx * sectorSize) (min sectorSize (payload.size - idx * sectorSize))).data.toList.length =
            min sectorSize (payload.size - idx * sectorSize) := by
          rw [sliceBytes_toList payload _ _ htlBound, List.length_take, List.length_drop, ba_length]
          omega
        have hsz : (sliceBytes payload (idx * sectorSize) (min sectorSize (payload.size - idx * sectorSize))).size ≤ sectorSize := by
          rw [← ba_length, hslLen]; exact Nat.min_le_left ..
        rw [sliceBytes_toList _ 0 take (by rw [padSector_size]; omega),
          padSector_toList hsz, List.drop_zero,
          List.take_append_of_le_length (by rw [hslLen]; exact htl),
          sliceBytes_toList payload _ _ htlBound, List.take_take, Nat.min_eq_left htl]
      · have hr0 : rem = 0 := by omega
        have ht0 : take = 0 := by omega
        rw [ht0, sliceBytes, appendBytesAux, emptyWithCapacity_toList, List.take_zero]
    by_cases hremLe : rem ≤ sectorSize
    · have htEq : take = rem := Nat.min_eq_left hremLe
      have hremNext : rem - take = 0 := by omega
      have hzero : ∀ (m : Nat) (acc : ByteArray), gatherPayload media g slot m 0 acc = acc := by
        intro m
        induction m with
        | zero => intro acc; rfl
        | succ m ihm =>
          intro acc
          simp only [gatherPayload, Nat.zero_min, Nat.sub_zero, sliceBytes, appendBytesAux]
          have : appendBytes acc (ByteArray.emptyWithCapacity 0) = acc := by
            apply byteArray_eq_of_toList_eq
            rw [appendBytes_toList, emptyWithCapacity_toList, List.append_nil]
          rw [this]; exact ihm acc
      rw [hremNext, hzero, appendBytes_toList, hslice, htEq]
      congr 1
      apply List.take_of_length_le
      rw [List.length_drop, ba_length]
      omega
    · have htEq : take = sectorSize := Nat.min_eq_right (by omega)
      have hih := ih (by omega) (rem - take) (appendBytes out (sliceBytes (encodeDataSector payload idx) 0 take))
        (by rw [Nat.succ_mul] at hrem; omega) (by rw [hnext]; omega)
      rw [hih, appendBytes_toList, hslice, htEq, hnext, List.append_assoc]
      congr 1
      rw [← List.drop_drop, List.take_append_drop]

/-- **Exact multi-sector `ByteArray` LBA roundtrip theorem**:
writing a record's `1 + dataSectors` 512-byte sectors to `media` and decoding them
recovers the exact `Record` (including arbitrary `0..4096`-byte `payload` verified by `cSHAKE256`). -/
theorem decodeRecordSectors_encode {pol : Policy} {g : Geometry} {media : Nat → Sector} {slot : Nat} {r : Record}
    (hfit : r.fits pol) (hcap : pol.maxPayload ≤ g.dataSectors * sectorSize)
    (hsec : ∀ k < entrySectors g, media (walLba g slot k) = encodeWalSector r k) :
    decodeRecordSectors pol media g slot = some r := by
  have hmeta : media (walLba g slot 0) = encodeMetaSector r := hsec 0 (by unfold entrySectors; omega)
  have hdata : ∀ idx < g.dataSectors, media (walLba g slot (idx + 1)) = encodeDataSector r.payload idx := by
    intro idx hidx
    simpa [encodeWalSector] using hsec (idx + 1) (by unfold entrySectors; omega)
  let raw := appendBytes (pushBEU64 8 (UInt64.ofNat r.payload.size)
    (pushBEU64 8 (UInt64.ofNat r.cost) (pushBEU64 8 (UInt64.ofNat r.nullifier)
      (pushBEU64 8 (UInt64.ofNat r.nonce) (pushBEU64 8 (UInt64.ofNat r.principal)
        (appendBytes (ByteArray.emptyWithCapacity 80) walMagic)))))) (payloadDigest r.payload)
  have hrawList : raw.data.toList =
      walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++
      be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat ++
      be 8 (UInt64.ofNat r.cost).toNat ++ be 8 (UInt64.ofNat r.payload.size).toNat ++
      (payloadDigest r.payload).data.toList := by
    simp only [raw, appendBytes_toList, pushBEU64_toList 8 (by decide), emptyWithCapacity_toList,
      List.nil_append, List.append_assoc]
  have hwmLen : walMagic.data.toList.length = 8 := by rw [ba_length]; exact walMagic_size
  have hpdLen : (payloadDigest r.payload).data.toList.length = 32 := by
    rw [ba_length]; exact payloadDigest_size r.payload
  have hrawSz : raw.size = 80 := by
    have h := congrArg List.length hrawList
    rw [ba_length] at h
    simp only [List.length_append, length_be, hwmLen, hpdLen] at h
    exact h
  have hmetaSz : (encodeMetaSector r).size = 512 := padSector_size _
  have hmetaList : (encodeMetaSector r).data.toList =
      walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++
      be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat ++
      be 8 (UInt64.ofNat r.cost).toNat ++ be 8 (UInt64.ofNat r.payload.size).toNat ++
      (payloadDigest r.payload).data.toList ++ List.replicate 432 0 := by
    change (padSector raw).data.toList = _
    rw [padSector_toList (by rw [hrawSz]; decide), hrawList, hrawSz]
    simp only [sectorSize, List.append_assoc]
  have hmagic : sliceBytes (encodeMetaSector r) 0 8 = walMagic := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList _ 0 8 (by rw [hmetaSz]; decide), hmetaList]
    simp only [List.drop_zero, List.append_assoc]
    rw [show (8 : Nat) = walMagic.data.toList.length from hwmLen.symm, List.take_left]
  have hpr : readBEU64 (encodeMetaSector r) 8 = UInt64.ofNat r.principal := by
    apply readBEU64_of_slice; rw [hmetaList]
    have := drop_take_append_exact walMagic.data.toList (be 8 (UInt64.ofNat r.principal).toNat)
      (be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat ++
       be 8 (UInt64.ofNat r.cost).toNat ++ be 8 (UInt64.ofNat r.payload.size).toNat ++
       (payloadDigest r.payload).data.toList ++ List.replicate 432 0)
    simpa only [hwmLen, length_be, List.append_assoc] using this
  have hno : readBEU64 (encodeMetaSector r) 16 = UInt64.ofNat r.nonce := by
    apply readBEU64_of_slice; rw [hmetaList]
    have := drop_take_append_exact (walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat)
      (be 8 (UInt64.ofNat r.nonce).toNat)
      (be 8 (UInt64.ofNat r.nullifier).toNat ++ be 8 (UInt64.ofNat r.cost).toNat ++
       be 8 (UInt64.ofNat r.payload.size).toNat ++ (payloadDigest r.payload).data.toList ++ List.replicate 432 0)
    simpa only [List.length_append, hwmLen, length_be, List.append_assoc] using this
  have hnu : readBEU64 (encodeMetaSector r) 24 = UInt64.ofNat r.nullifier := by
    apply readBEU64_of_slice; rw [hmetaList]
    have := drop_take_append_exact (walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++ be 8 (UInt64.ofNat r.nonce).toNat)
      (be 8 (UInt64.ofNat r.nullifier).toNat)
      (be 8 (UInt64.ofNat r.cost).toNat ++ be 8 (UInt64.ofNat r.payload.size).toNat ++
       (payloadDigest r.payload).data.toList ++ List.replicate 432 0)
    simpa only [List.length_append, hwmLen, length_be, List.append_assoc] using this
  have hco : readBEU64 (encodeMetaSector r) 32 = UInt64.ofNat r.cost := by
    apply readBEU64_of_slice; rw [hmetaList]
    have := drop_take_append_exact (walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++
        be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat)
      (be 8 (UInt64.ofNat r.cost).toNat)
      (be 8 (UInt64.ofNat r.payload.size).toNat ++ (payloadDigest r.payload).data.toList ++ List.replicate 432 0)
    simpa only [List.length_append, hwmLen, length_be, List.append_assoc] using this
  have hpl : readBEU64 (encodeMetaSector r) 40 = UInt64.ofNat r.payload.size := by
    apply readBEU64_of_slice; rw [hmetaList]
    have := drop_take_append_exact (walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++
        be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat ++ be 8 (UInt64.ofNat r.cost).toNat)
      (be 8 (UInt64.ofNat r.payload.size).toNat)
      ((payloadDigest r.payload).data.toList ++ List.replicate 432 0)
    simpa only [List.length_append, hwmLen, length_be, List.append_assoc] using this
  have hdig : sliceBytes (encodeMetaSector r) 48 32 = payloadDigest r.payload := by
    apply byteArray_eq_of_toList_eq
    rw [sliceBytes_toList _ 48 32 (by rw [hmetaSz]; decide), hmetaList]
    have := drop_take_append_exact (walMagic.data.toList ++ be 8 (UInt64.ofNat r.principal).toNat ++
        be 8 (UInt64.ofNat r.nonce).toNat ++ be 8 (UInt64.ofNat r.nullifier).toNat ++
        be 8 (UInt64.ofNat r.cost).toNat ++ be 8 (UInt64.ofNat r.payload.size).toNat)
      (payloadDigest r.payload).data.toList (List.replicate 432 0)
    simpa only [List.length_append, hwmLen, length_be, hpdLen, List.append_assoc] using this
  have hprN : (UInt64.ofNat r.principal).toNat = r.principal := UInt64.toNat_ofNat_of_lt hfit.1
  have hnoN : (UInt64.ofNat r.nonce).toNat = r.nonce := UInt64.toNat_ofNat_of_lt hfit.2.1
  have hnuN : (UInt64.ofNat r.nullifier).toNat = r.nullifier := UInt64.toNat_ofNat_of_lt hfit.2.2.1
  have hcoN : (UInt64.ofNat r.cost).toNat = r.cost := UInt64.toNat_ofNat_of_lt hfit.2.2.2.1
  have hplN : (UInt64.ofNat r.payload.size).toNat = r.payload.size := UInt64.toNat_ofNat_of_lt hfit.2.2.2.2.2
  have hgath : gatherPayload media g slot g.dataSectors r.payload.size (ByteArray.emptyWithCapacity r.payload.size) = r.payload := by
    apply byteArray_eq_of_toList_eq
    have hg := gatherPayload_toList media g slot r.payload hdata g.dataSectors (Nat.le_refl _)
      r.payload.size (ByteArray.emptyWithCapacity r.payload.size) (Nat.le_trans hfit.2.2.2.2.1 hcap) (by simp)
    rw [emptyWithCapacity_toList, Nat.sub_self, Nat.zero_mul, List.nil_append, List.drop_zero] at hg
    exact hg
  have hcap512 : r.payload.size ≤ g.dataSectors * 512 := Nat.le_trans hfit.2.2.2.2.1 hcap
  unfold decodeRecordSectors
  rw [hmeta]
  simp only [hmetaSz, sectorSize, hmagic, and_self, decide_true, ↓reduceIte,
    hpr, hno, hnu, hco, hpl, hdig, hprN, hnoN, hnuN, hcoN, hplN,
    hfit.2.2.2.2.1, hcap512, hgath]

/-! ## 3. Physical `Disk` with Durable LBA Media + Out-of-Order Volatile Write Cache -/

/-- Real block device state: durable non-volatile LBA `media`, controller volatile
write-back `writeCache` (lost on power cut, drained by `FLUSH`), and namespace `geometry`. -/
structure Disk where
  media : Nat → Sector
  writeCache : Nat → Option Sector
  geometry : Geometry

def writeCacheSector (d : Disk) (lba : Nat) (sec : Sector) : Disk :=
  { d with writeCache := fun x => if x = lba then some sec else d.writeCache x }

def evictDirtySector (d : Disk) (lba : Nat) (torn : Sector) : Disk :=
  { d with media := fun x => if x = lba then torn else d.media x }

def flushCache (d : Disk) : Disk :=
  { d with
    media := fun x => (d.writeCache x).getD (d.media x)
    writeCache := fun _ => none }

def writeFuaSector (d : Disk) (lba : Nat) (sec : Sector) : Disk :=
  { d with
    media := fun x => if x = lba then sec else d.media x
    writeCache := fun x => if x = lba then none else d.writeCache x }

def powerReset (d : Disk) : Disk :=
  { d with writeCache := fun _ => none }

private def decodeActiveRange (pol : Policy) (media : Nat → Sector) (g : Geometry) : Nat → Option (List Record)
  | 0 => some []
  | n + 1 => do
    let rest ← decodeActiveRange pol media g n
    let r ← decodeRecordSectors pol media g n
    return rest ++ [r]

/-- Cold recovery reads ONLY durable `d.media` (volatile `writeCache` is invisible to cold boot!).
Validates the 256-bit `cSHAKE256` superblock tag at `ctrlLba` and decodes all active WAL LBA records. -/
def recoverFull (pol : Policy) (d : Disk) : Option (Superblock × List Record) := do
  let sb ← decodeSuperblock (d.media d.geometry.ctrlLba)
  guard (sb.activeCount.toNat ≤ pol.maxTurns ∧ sb.activeCount.toNat ≤ d.geometry.walSlots)
  let recs ← decodeActiveRange pol d.media d.geometry sb.activeCount.toNat
  return (sb, recs)

def recover (pol : Policy) (d : Disk) : Option (List Record) :=
  (recoverFull pol d).map Prod.snd

theorem powerReset_preserves_recoverFull (pol : Policy) (d : Disk) :
    recoverFull pol (powerReset d) = recoverFull pol d := by
  unfold recoverFull powerReset
  rfl

private theorem decodeRecordSectors_congr (pol : Policy) (m1 m2 : Nat → Sector) (g : Geometry) (slot : Nat)
    (h : ∀ k < entrySectors g, m1 (walLba g slot k) = m2 (walLba g slot k)) :
    decodeRecordSectors pol m1 g slot = decodeRecordSectors pol m2 g slot := by
  unfold decodeRecordSectors
  rw [h 0 (by unfold entrySectors; omega)]
  have hgath : ∀ (m rem : Nat) (acc : ByteArray), m ≤ g.dataSectors →
      gatherPayload m1 g slot m rem acc = gatherPayload m2 g slot m rem acc := by
    intro m
    induction m with
    | zero => intro _ _ _; rfl
    | succ m ihm =>
      intro rem acc hm
      simp only [gatherPayload]
      rw [h (g.dataSectors - (m + 1) + 1) (by unfold entrySectors; omega)]
      exact ihm _ _ (by omega)
  simp [hgath g.dataSectors _ _ (Nat.le_refl _)]

private theorem decodeActiveRange_eq (pol : Policy) (media : Nat → Sector) (g : Geometry) (xs : List Record)
    (h : ∀ slot < xs.length, decodeRecordSectors pol media g slot = xs[slot]?) :
    decodeActiveRange pol media g xs.length = some xs := by
  suffices ∀ (n : Nat), n ≤ xs.length → decodeActiveRange pol media g n = some (xs.take n) by
    simpa using this xs.length (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hle
    have hlt : n < xs.length := by omega
    simp only [decodeActiveRange, bind, Option.bind, Option.pure_def]
    rw [ih (by omega), h n hlt, List.getElem?_eq_getElem hlt]
    simp only [Option.some.injEq]
    exact (List.take_succ_eq_append_getElem hlt).symm

/-! ## 4. NVMe Command Classifier, Out-of-Order DMA & Multi-Epoch Checkpoint Trace -/

inductive Phase
  | idle
  | dma (r : Record) (written : List Nat)
  | flushed (r : Record)
  | waitFuaCompletion (r : Record)
  | dispatchable (r : Record)

inductive Opcode | write | flush deriving DecidableEq, Repr

structure Command where
  opcode : Opcode
  nsid : UInt32
  slba : Nat
  nlb : UInt16
  fua : Bool
  deriving DecidableEq, Repr

inductive Action | walSector (k : Nat) | barrier | commit deriving DecidableEq, Repr

def commandFor (g : Geometry) (slot : Nat) : Action → Command
  | .walSector k => ⟨.write, 1, walLba g slot k, 0, false⟩
  | .barrier => ⟨.flush, 1, 0, 0, false⟩
  | .commit => ⟨.write, 1, g.ctrlLba, 0, true⟩

def allSectorsWritten (g : Geometry) (written : List Nat) : Bool :=
  (List.range (entrySectors g)).all fun k => written.contains k

def classify (g : Geometry) (slot : Nat) (p : Phase) (q : Command) : Option Action :=
  match p with
  | .dma _ written =>
    if q.opcode == .write && q.nsid == 1 && q.nlb == 0 && !q.fua then
      let base := walLba g slot 0
      if decide (base ≤ q.slba ∧ q.slba < base + entrySectors g) then
        let k := q.slba - base
        if !written.contains k then some (.walSector k) else none
      else none
    else if allSectorsWritten g written && q == commandFor g slot .barrier then
      some .barrier
    else none
  | .flushed _ =>
    if q == commandFor g slot .commit then some .commit else none
  | _ => none

theorem classification_exact {g : Geometry} {slot : Nat} {p : Phase} {q : Command} {act : Action}
    (h : classify g slot p q = some act) :
    q = commandFor g slot act ∧
    (∀ k, act = .walSector k → k < entrySectors g ∧ ∃ r w, p = .dma r w ∧ k ∉ w) ∧
    (act = .commit → ∃ r, p = .flushed r) ∧
    (act = .barrier → ∃ r w, p = .dma r w ∧ ∀ k < entrySectors g, k ∈ w) := by
  cases p with
  | idle | waitFuaCompletion _ | dispatchable _ => simp [classify] at h
  | flushed r =>
    simp only [classify] at h
    split at h <;> try contradiction
    rename_i hq
    cases h
    exact ⟨beq_iff_eq.mp hq, fun _ he => (by cases he), fun _ => ⟨r, rfl⟩, fun he => (by cases he)⟩
  | dma r written =>
    simp only [classify] at h
    split at h
    · rename_i hw
      split at h <;> try contradiction
      rename_i hrng
      split at h <;> try contradiction
      rename_i hnw
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
      simp only [decide_eq_true_eq] at hrng
      have hnot : q.slba - walLba g slot 0 ∉ written := by
        simpa [List.contains_iff_mem] using hnw
      have hcmd : q = commandFor g slot (.walSector (q.slba - walLba g slot 0)) := by
        cases q with
        | mk op ns sl nlb fua =>
          simp only [commandFor, walLba] at hw hrng ⊢
          obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hw
          congr 1; omega
      exact ⟨hcmd, fun k hk => (by cases hk; exact ⟨by omega, r, written, rfl, hnot⟩),
        fun he => (by cases he), fun he => (by cases he)⟩
    · split at h <;> try contradiction
      rename_i hbar
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, allSectorsWritten, List.all_eq_true] at hbar
      refine ⟨hbar.2, fun _ he => (by cases he), fun he => (by cases he), fun _ => ⟨r, written, rfl, ?_⟩⟩
      intro k hk
      exact List.contains_iff_mem.mp (hbar.1 k (List.mem_range.mpr hk))

/-- Multi-epoch crash-safe NVMe trace:
- Out-of-order sector DMA into controller volatile `writeCache` (`dmaSectorDone`),
- Arbitrary torn write-back of dirty volatile LBAs (`evictDirty`),
- `FLUSH` draining volatile `writeCache` to durable `media` (`flush`),
- Atomic single-LBA `FUA` superblock installation (`fua`),
- Checkpoint compaction advancing `baseGen` and resetting the active WAL ring (`checkpoint`),
- Power cut at ANY phase discarding `writeCache` (`powerCut`). -/
inductive Run (pol : Policy) (permit : List Record → Record → Prop) :
    Disk → Phase → List Record → Nat → List (Nat × Record) → List Nat → Prop
  | boot (g : Geometry) : g.usable pol = true → (junk : Nat → Sector) →
      Run pol permit
        (writeFuaSector ⟨junk, fun _ => none, g⟩ g.ctrlLba
          (encodeSuperblock (mkSuperblock 0 0 0 0 genesisChainDigest)))
        .idle [] 0 [] []
  | beginTurn {d all base tx issues r} :
      Run pol permit d .idle all base tx issues →
      requestWith pol base (maxNullifier (all.take base)) (fun p => spent (all.take base) p)
        (all.drop base) r.principal r = .fresh →
      permit all r →
      all.length + 1 < 2 ^ 64 →
      Run pol permit d (.dma r []) all base tx issues
  | dmaSectorDone {d all base tx issues r written k} :
      Run pol permit d (.dma r written) all base tx issues →
      (q : Command) → classify d.geometry (all.drop base).length (.dma r written) q = some (.walSector k) →
      Run pol permit (writeCacheSector d (walLba d.geometry (all.drop base).length k) (encodeWalSector r k))
        (.dma r (k :: written)) all base tx issues
  | evictDirty {d all base tx issues r written lba} :
      Run pol permit d (.dma r written) all base tx issues →
      (d.writeCache lba).isSome = true →
      (torn : Sector) →
      Run pol permit (evictDirtySector d lba torn) (.dma r written) all base tx issues
  | flush {d all base tx issues r written} :
      Run pol permit d (.dma r written) all base tx issues →
      (q : Command) → classify d.geometry (all.drop base).length (.dma r written) q = some .barrier →
      Run pol permit (flushCache d) (.flushed r) all base tx issues
  | fua {d all base tx issues r} :
      Run pol permit d (.flushed r) all base tx issues →
      (q : Command) → classify d.geometry (all.drop base).length (.flushed r) q = some .commit →
      Run pol permit
        (writeFuaSector d d.geometry.ctrlLba
          (encodeSuperblock (mkSuperblock
            (UInt64.ofNat (all.length + 1))
            (UInt64.ofNat base)
            (UInt64.ofNat ((all.drop base).length + 1))
            (UInt64.ofNat (maxNullifier (all.take base)))
            (stepChainDigest (logDigest all) r))))
        (.waitFuaCompletion r) (all ++ [r]) base tx issues
  | checkpoint {d all base tx issues} :
      Run pol permit d .idle all base tx issues →
      Run pol permit
        (writeFuaSector d d.geometry.ctrlLba
          (encodeSuperblock (mkSuperblock
            (UInt64.ofNat all.length)
            (UInt64.ofNat all.length)
            0
            (UInt64.ofNat (maxNullifier all))
            (logDigest all))))
        .idle all all.length tx issues
  | completion {d all base tx issues r} :
      Run pol permit d (.waitFuaCompletion r) all base tx issues →
      Run pol permit d (.dispatchable r) all base tx issues
  | dispatch {d all base tx issues r} :
      Run pol permit d (.dispatchable r) all base tx issues →
      Run pol permit d .idle all base tx (r.nullifier :: issues)
  | rejectedCommand {d p all base tx issues} :
      Run pol permit d p all base tx issues →
      (q : Command) → classify d.geometry (all.drop base).length p q = none →
      Run pol permit d p all base tx issues
  | powerCut {d p all base tx issues} :
      Run pol permit d p all base tx issues →
      Run pol permit (powerReset d) .idle all base tx issues
  | send {d all base tx issues caller r i} :
      Run pol permit d .idle all base tx issues →
      requestWith pol base (maxNullifier (all.take base)) (fun p => spent (all.take base) p)
        (all.drop base) caller r = .cached (i + 1) →
      Run pol permit d .idle all base ((i, r) :: tx) issues
  | refused {d all base tx issues caller r} :
      Run pol permit d .idle all base tx issues →
      requestWith pol base (maxNullifier (all.take base)) (fun p => spent (all.take base) p)
        (all.drop base) caller r = .refuse →
      Run pol permit d .idle all base tx issues

/-- Global authorized record sequence invariant across all epochs. -/
inductive Accepted (pol : Policy) (permit : List Record → Record → Prop) : List Record → Prop
  | nil : Accepted pol permit []
  | snoc {xs r} : Accepted pol permit xs → permit xs r →
      r.fits pol →
      0 < r.cost → spent xs r.principal + r.cost ≤ pol.budgetCap →
      0 < r.nullifier → (∀ old ∈ xs, old.nullifier < r.nullifier) →
      Accepted pol permit (xs ++ [r])

theorem accepted_nodup {pol permit xs} (h : Accepted pol permit xs) :
    (xs.map Record.nullifier).Nodup ∧ xs.Nodup := by
  induction h with
  | nil => simp
  | @snoc xs r _ _ _ _ _ _ hlt ih =>
    have absent : ∀ a ∈ xs, a.nullifier ≠ r.nullifier := fun a ha => Nat.ne_of_lt (hlt a ha)
    have newId : r.nullifier ∉ xs.map Record.nullifier := by
      intro mem; obtain ⟨a, ha, eq⟩ := List.mem_map.mp mem; exact absent a ha eq
    have newRec : r ∉ xs := fun mem => absent r mem rfl
    simp_all [List.nodup_append]
    intro a ha eq; subst eq; exact newRec ha

theorem accepted_budget {pol permit xs} (h : Accepted pol permit xs) (p : Nat) :
    spent xs p ≤ pol.budgetCap := by
  induction h with
  | nil => simp [spent]
  | @snoc xs r _ _ _ _ hcap _ _ ih =>
    by_cases eq : r.principal = p
    · subst p; simp only [spent, List.filter_append, List.filter_cons, beq_self_eq_true,
        ↓reduceIte, List.filter_nil, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at *; omega
    · simpa [spent, eq] using ih

theorem accepted_nullifier_lt {pol permit xs} (h : Accepted pol permit xs) :
    ∀ r ∈ xs, r.nullifier < 2 ^ 64 := by
  induction h with
  | nil => intro _ hr; cases hr
  | @snoc xs r _ _ hfit _ _ _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact ih x h1
    · simp at h2; subst h2; exact hfit.2.2.1

def receiptHead (xs : List Record) (p : Nat) : Option Nat :=
  (xs.zipIdx.reverse.find? (fun e => e.1.principal == p)).map (fun e => e.2 + 1)

private theorem spent_take_add_drop (xs : List Record) (base p : Nat) :
    spent (xs.take base) p + spent (xs.drop base) p = spent xs p := by
  have h := List.take_append_drop base xs
  conv => rhs; rw [← h]
  unfold spent
  rw [List.filter_append, List.map_append, List.sum_append]

theorem maxNullifier_le_of_mem {xs : List Record} {r : Record} (h : r ∈ xs) :
    r.nullifier ≤ maxNullifier xs := by
  unfold maxNullifier
  suffices ∀ (acc : Nat), r.nullifier ≤ xs.foldl (fun a x => max a x.nullifier) acc from this 0
  induction xs with
  | nil => cases h
  | cons a as ih =>
    intro acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hrest
    · have mono : ∀ (ys : List Record) (init : Nat), init ≤ ys.foldl (fun x y => max x y.nullifier) init := by
        intro ys; induction ys with
        | nil => intro _; exact Nat.le_refl _
        | cons y ys ihy => intro init; exact Nat.le_trans (Nat.le_max_left _ _) (ihy _)
      exact Nat.le_trans (Nat.le_max_right _ _) (mono as _)
    · exact ih hrest _

theorem maxNullifier_lt_of_all_lt {xs : List Record} {b : Nat} (hb : 0 < b)
    (h : ∀ r ∈ xs, r.nullifier < b) : maxNullifier xs < b := by
  unfold maxNullifier
  suffices ∀ (acc : Nat), acc < b → xs.foldl (fun a x => max a x.nullifier) acc < b from this 0 hb
  induction xs with
  | nil => intro acc ha; exact ha
  | cons a as ih =>
    intro acc ha
    simp only [List.foldl_cons]
    exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) (max acc a.nullifier)
      (Nat.max_lt.mpr ⟨ha, h a List.mem_cons_self⟩)

private theorem maxNullifier_append (a b : List Record) :
    maxNullifier (a ++ b) = max (maxNullifier a) (maxNullifier b) := by
  unfold maxNullifier
  rw [List.foldl_append]
  suffices ∀ (ys : List Record) (init : Nat),
      ys.foldl (fun acc r => max acc r.nullifier) init =
      max init (ys.foldl (fun acc r => max acc r.nullifier) 0) from this b _
  intro ys
  induction ys with
  | nil => intro init; simp
  | cons y ys ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih (max init y.nullifier), ih (max 0 y.nullifier), Nat.zero_max, Nat.max_assoc]

private theorem maxNullifier_take_drop (xs : List Record) (base : Nat) :
    max (maxNullifier (xs.take base)) (maxNullifier (xs.drop base)) = maxNullifier xs := by
  conv => rhs; rw [← List.take_append_drop base xs, maxNullifier_append]

private theorem fresh_props {pol base cpNull priorSpent xs p r}
    (h : requestWith pol base cpNull priorSpent xs p r = .fresh) :
    r.principal = p ∧ xs.length < pol.maxTurns ∧ 0 < r.cost ∧
    priorSpent p + spent xs p + r.cost ≤ pol.budgetCap ∧
    cpNull < r.nullifier ∧ 0 < r.nullifier ∧ r.fits pol ∧
    ∀ old ∈ xs, old.nullifier < r.nullifier := by
  unfold requestWith at h
  split at h <;> try contradiction
  rename_i hpr
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hcond
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hcond
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hall⟩ := hcond
  have hpeq : r.principal = p := by omega
  unfold remainingWith at h3
  refine ⟨hpeq, h1, h2, by omega, h4, h5, ⟨h6, h7, h8, h9, h10, h11⟩, fun old hold => (hall old hold).1⟩

private theorem cached_props {pol base cpNull priorSpent xs p r i}
    (h : requestWith pol base cpNull priorSpent xs p r = .cached (i + 1)) :
    base ≤ i ∧ xs[i - base]? = some r := by
  unfold requestWith at h
  split at h <;> try contradiction
  split at h
  · rename_i hmem
    injection h with heq
    have hi : base + xs.idxOf r = i := by omega
    refine ⟨by omega, ?_⟩
    rw [show i - base = xs.idxOf r by omega, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)]
    exact congrArg some (List.getElem_idxOf _)
  · split at h <;> contradiction

private def pending (pol : Policy) (permit : List Record → Record → Prop) (d : Disk)
    (all : List Record) (base : Nat) (issues : List Nat) : Phase → Prop
  | .idle => ∀ lba, d.writeCache lba = none
  | .waitFuaCompletion r | .dispatchable r => r ∈ all ∧ r.nullifier ∉ issues ∧ ∀ lba, d.writeCache lba = none
  | .dma r written =>
      permit all r ∧
      requestWith pol base (maxNullifier (all.take base)) (fun p => spent (all.take base) p)
        (all.drop base) r.principal r = .fresh ∧
      all.length + 1 < 2 ^ 64 ∧
      (∀ lba, (d.writeCache lba).isSome = true →
        ∃ k < entrySectors d.geometry, lba = walLba d.geometry (all.drop base).length k) ∧
      (∀ k ∈ written, k < entrySectors d.geometry ∧
        d.writeCache (walLba d.geometry (all.drop base).length k) = some (encodeWalSector r k))
  | .flushed r =>
      permit all r ∧
      requestWith pol base (maxNullifier (all.take base)) (fun p => spent (all.take base) p)
        (all.drop base) r.principal r = .fresh ∧
      all.length + 1 < 2 ^ 64 ∧
      (∀ lba, d.writeCache lba = none) ∧
      (∀ k < entrySectors d.geometry, d.media (walLba d.geometry (all.drop base).length k) = encodeWalSector r k)

private structure Good (pol : Policy) (permit : List Record → Record → Prop) (d : Disk) (p : Phase)
    (all : List Record) (base : Nat) (tx : List (Nat × Record)) (issues : List Nat) : Prop where
  geometry : d.geometry.usable pol = true
  baseLe : base ≤ all.length
  lenLt : all.length < 2 ^ 64
  activeBound : (all.drop base).length ≤ pol.maxTurns
  superblock : d.media d.geometry.ctrlLba = encodeSuperblock (mkSuperblock
    (UInt64.ofNat all.length) (UInt64.ofNat base) (UInt64.ofNat (all.drop base).length)
    (UInt64.ofNat (maxNullifier (all.take base))) (logDigest all))
  activeMedia : ∀ slot < (all.drop base).length,
    decodeRecordSectors pol d.media d.geometry slot = (all.drop base)[slot]?
  authorized : Accepted pol permit all
  inflight : pending pol permit d all base issues p
  uniqueIssues : issues.Nodup
  issued : ∀ id ∈ issues, id ∈ all.map Record.nullifier
  transmitted : ∀ z ∈ tx, all[z.1]? = some z.2

private theorem run_good {pol permit d p all base tx issues} (trace : Run pol permit d p all base tx issues) :
    Good pol permit d p all base tx issues := by
  induction trace with
  | boot g ok junk =>
    refine ⟨ok, Nat.le_refl _, by decide, by simp, ?_, fun _ h => by simp at h, .nil, ?_, by simp, by simp, by simp⟩
    · simp [writeFuaSector, maxNullifier, logDigest]
    · intro lba; simp [writeFuaSector]
  | @beginTurn d all base tx issues r _ fresh auth hlen ih =>
    refine { ih with inflight := ⟨auth, fresh, hlen, fun lba hlba => ?_, fun _ h => by cases h⟩ }
    rw [ih.inflight lba] at hlba; cases hlba
  | @dmaSectorDone d all base tx issues r written k _ q hcls ih =>
    obtain ⟨_, hwal, _, _⟩ := classification_exact hcls
    obtain ⟨hkLt, _, _, hEqP, _⟩ := hwal k rfl
    cases hEqP
    obtain ⟨hauth, hfresh, hlen, hdirty, hwr⟩ := ih.inflight
    refine { ih with inflight := ⟨hauth, hfresh, hlen, fun lba hlba => ?_, fun j hj => ?_⟩ }
    · simp only [writeCacheSector] at hlba
      by_cases heq : lba = walLba d.geometry (all.drop base).length k
      · exact ⟨k, hkLt, heq⟩
      · simp only [heq, ↓reduceIte] at hlba; exact hdirty lba hlba
    · rcases List.mem_cons.mp hj with rfl | hj'
      · exact ⟨hkLt, by simp only [writeCacheSector, ↓reduceIte]⟩
      · obtain ⟨hjLt, hcache⟩ := hwr j hj'
        refine ⟨hjLt, ?_⟩
        simp only [writeCacheSector]
        by_cases heq : walLba d.geometry (all.drop base).length j = walLba d.geometry (all.drop base).length k
        · obtain ⟨_, hjk⟩ := walLba_inj hjLt hkLt heq
          subst hjk; simp only [↓reduceIte]
        · simp only [heq, ↓reduceIte, hcache]
  | @evictDirty d all base tx issues r written lba _ hdirty torn ih =>
    obtain ⟨hauth, hfresh, hlen, hcache, hwr⟩ := ih.inflight
    obtain ⟨k, hkLt, rfl⟩ := hcache lba hdirty
    have hfp := fresh_props hfresh
    have hgu := ih.geometry
    simp only [Geometry.usable, decide_eq_true_eq] at hgu
    have hconf := wal_confined ih.geometry (slot := (all.drop base).length) (by omega) hkLt
    refine { ih with
      superblock := by simp only [evictDirtySector, hconf.2.symm, ↓reduceIte, ih.superblock]
      activeMedia := fun slot hslot => ?_
      inflight := ⟨hauth, hfresh, hlen, hcache, hwr⟩ }
    dsimp only [evictDirtySector]
    rw [decodeRecordSectors_congr pol _ d.media d.geometry slot]
    · exact ih.activeMedia slot hslot
    · intro j hj
      have hne : walLba d.geometry slot j ≠ walLba d.geometry (all.drop base).length k := by
        intro heq; obtain ⟨hs, _⟩ := walLba_inj hj hkLt heq; omega
      simp only [hne, ↓reduceIte]
  | @flush d all base tx issues r written _ q hcls ih =>
    obtain ⟨_, _, _, hbar⟩ := classification_exact hcls
    obtain ⟨_, _, hEqP, hallW⟩ := hbar rfl
    cases hEqP
    obtain ⟨hauth, hfresh, hlen, hdirty, hwr⟩ := ih.inflight
    have hfp := fresh_props hfresh
    have hgu := ih.geometry
    simp only [Geometry.usable, decide_eq_true_eq] at hgu
    have hctrlNone : d.writeCache d.geometry.ctrlLba = none := by
      cases hc : d.writeCache d.geometry.ctrlLba with
      | none => rfl
      | some _ =>
        obtain ⟨k, hkLt, heq⟩ := hdirty d.geometry.ctrlLba (by simp [hc])
        exact absurd heq.symm (wal_confined ih.geometry (by omega) hkLt).2
    refine { ih with
      superblock := by simp only [flushCache, hctrlNone, Option.getD_none, ih.superblock]
      activeMedia := fun slot hslot => ?_
      inflight := ⟨hauth, hfresh, hlen, fun _ => rfl, fun k hk => ?_⟩ }
    · dsimp only [flushCache]
      rw [decodeRecordSectors_congr pol _ d.media d.geometry slot]
      · exact ih.activeMedia slot hslot
      · intro j hj
        have hnone : d.writeCache (walLba d.geometry slot j) = none := by
          cases hc : d.writeCache (walLba d.geometry slot j) with
          | none => rfl
          | some _ =>
            obtain ⟨k, hkLt, heq⟩ := hdirty _ (by rw [hc]; rfl)
            obtain ⟨hs, _⟩ := walLba_inj hj hkLt heq
            omega
        simp only [hnone, Option.getD_none]
    · obtain ⟨_, hsec⟩ := hwr k (hallW k hk)
      simp only [flushCache, hsec, Option.getD_some]
  | @fua d all base tx issues r _ q hcls ih =>
    obtain ⟨hauth, hfresh, hlen, hwc, hmed⟩ := ih.inflight
    have hfp := fresh_props hfresh
    have hgu := ih.geometry
    simp only [Geometry.usable, decide_eq_true_eq] at hgu
    have hbaseLe := ih.baseLe
    have htake : (all ++ [r]).take base = all.take base := List.take_append_of_le_length hbaseLe
    have hdrop : (all ++ [r]).drop base = all.drop base ++ [r] := by
      rw [List.drop_append_of_le_length hbaseLe]
    have hallOld : ∀ old ∈ all, old.nullifier < r.nullifier := by
      intro old hold
      have hsplit : old ∈ all.take base ∨ old ∈ all.drop base := by
        rw [← List.mem_append, List.take_append_drop]; exact hold
      rcases hsplit with ht | hd
      · exact Nat.lt_of_le_of_lt (maxNullifier_le_of_mem ht) hfp.2.2.2.2.1
      · exact hfp.2.2.2.2.2.2.2 old hd
    have hbudget : spent all r.principal + r.cost ≤ pol.budgetCap := by
      have h1 := hfp.2.2.2.1
      rw [hfp.1, spent_take_add_drop] at h1
      exact h1
    have hAcc : Accepted pol permit (all ++ [r]) :=
      .snoc ih.authorized hauth hfp.2.2.2.2.2.2.1 hfp.2.2.1 hbudget hfp.2.2.2.2.2.1 hallOld
    have hdropRoom : (all.drop base).length < pol.maxTurns := hfp.2.1
    have hdropLen : (all.drop base).length = all.length - base := List.length_drop ..
    refine ⟨ih.geometry, by simp; omega, by simp; omega, by rw [hdrop]; simp; omega, ?_, ?_, hAcc, ?_,
      ih.uniqueIssues, fun id mem => by simp [ih.issued id mem], fun z hz => ?_⟩
    · simp only [writeFuaSector, ↓reduceIte, List.length_append, List.length_singleton,
        htake, hdrop, logDigest_snoc]
    · intro slot hslot
      rw [hdrop] at hslot ⊢
      simp only [List.length_append, List.length_singleton] at hslot
      have hslotW : slot < d.geometry.walSlots := by omega
      have hconf : ∀ k < entrySectors d.geometry, walLba d.geometry slot k ≠ d.geometry.ctrlLba :=
        fun k hk => (wal_confined ih.geometry hslotW hk).2
      dsimp only [writeFuaSector]
      rw [decodeRecordSectors_congr pol _ d.media d.geometry slot (fun k hk => by simp only [hconf k hk, ↓reduceIte])]
      by_cases hlt : slot < (all.drop base).length
      · rw [List.getElem?_append_left hlt]
        exact ih.activeMedia slot hlt
      · have hse : slot = (all.drop base).length := by omega
        subst hse
        rw [List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero]
        exact decodeRecordSectors_encode hfp.2.2.2.2.2.2.1 hgu.2.2.2.2.1 hmed
    · refine ⟨by simp, fun mem => ?_, fun lba => by simp [writeFuaSector, hwc lba]⟩
      obtain ⟨prior, hp, eq⟩ := List.mem_map.mp (ih.issued _ mem)
      exact Nat.ne_of_lt (hallOld prior hp) eq
    · have prev := ih.transmitted z hz
      rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp prev).1), prev]
  | @checkpoint d all base tx issues _ ih =>
    refine ⟨ih.geometry, Nat.le_refl _, ih.lenLt, by simp, ?_, fun _ h => by simp at h,
      ih.authorized, fun lba => by simp [writeFuaSector, ih.inflight lba],
      ih.uniqueIssues, ih.issued, ih.transmitted⟩
    simp [writeFuaSector, List.drop_length, List.take_length]
  | completion _ ih => exact { ih with inflight := ih.inflight }
  | dispatch _ ih =>
    refine { ih with
      inflight := ih.inflight.2.2
      uniqueIssues := List.nodup_cons.mpr ⟨ih.inflight.2.1, ih.uniqueIssues⟩
      issued := fun id mem => by
        rcases List.mem_cons.mp mem with rfl | old
        · exact List.mem_map.mpr ⟨_, ih.inflight.1, rfl⟩
        · exact ih.issued id old }
  | powerCut _ ih => exact { ih with inflight := fun _ => rfl }
  | @send d all base tx issues caller r i _ h ih =>
    refine { ih with transmitted := fun z hz => ?_ }
    rcases List.mem_cons.mp hz with rfl | old
    · obtain ⟨hge, hget⟩ := cached_props h
      rw [List.getElem?_drop, show base + (i - base) = i by omega] at hget
      exact hget
    · exact ih.transmitted z old
  | refused _ _ ih | rejectedCommand _ _ _ ih => exact ih

private theorem recoverFull_of_good {pol permit d p all base tx issues}
    (h : Good pol permit d p all base tx issues) :
    ∃ sb, recoverFull pol d = some (sb, all.drop base) ∧
      sb.generation.toNat = all.length ∧ sb.baseGen.toNat = base ∧
      sb.activeCount.toNat = (all.drop base).length ∧
      sb.highWaterNullifier.toNat = maxNullifier (all.take base) ∧
      sb.chainDigest = logDigest all := by
  have hgu := h.geometry
  simp only [Geometry.usable, decide_eq_true_eq] at hgu
  have hlenLt : all.length < 2 ^ 64 := h.lenLt
  have hbaseLt : base < 2 ^ 64 := Nat.lt_of_le_of_lt h.baseLe hlenLt
  have hdropLe : (all.drop base).length ≤ all.length := by simp
  have hactLt : (all.drop base).length < 2 ^ 64 := Nat.lt_of_le_of_lt hdropLe hlenLt
  have hhwLt : maxNullifier (all.take base) < 2 ^ 64 :=
    maxNullifier_lt_of_all_lt (by decide) fun r hr =>
      accepted_nullifier_lt h.authorized r (List.mem_of_mem_take hr)
  let sb := mkSuperblock (UInt64.ofNat all.length) (UInt64.ofNat base)
    (UInt64.ofNat (all.drop base).length) (UInt64.ofNat (maxNullifier (all.take base))) (logDigest all)
  have hdec : decodeSuperblock (d.media d.geometry.ctrlLba) = some sb := by
    rw [h.superblock]
    exact decodeSuperblock_encodeSuperblock _ _ _ _ _ (logDigest_size all)
  have hact : sb.activeCount.toNat = (all.drop base).length := UInt64.toNat_ofNat_of_lt hactLt
  have hgen : sb.generation.toNat = all.length := UInt64.toNat_ofNat_of_lt hlenLt
  have hbas : sb.baseGen.toNat = base := UInt64.toNat_ofNat_of_lt hbaseLt
  have hhw : sb.highWaterNullifier.toNat = maxNullifier (all.take base) := UInt64.toNat_ofNat_of_lt hhwLt
  have hrange : decodeActiveRange pol d.media d.geometry sb.activeCount.toNat = some (all.drop base) := by
    rw [hact]
    exact decodeActiveRange_eq pol d.media d.geometry (all.drop base) h.activeMedia
  have hactBound : (all.drop base).length ≤ pol.maxTurns := h.activeBound
  refine ⟨sb, ?_, hgen, hbas, hact, hhw, rfl⟩
  unfold recoverFull
  rw [hdec]
  have hguard : sb.activeCount.toNat ≤ pol.maxTurns ∧ sb.activeCount.toNat ≤ d.geometry.walSlots :=
    ⟨by rw [hact]; exact hactBound, by rw [hact]; omega⟩
  simp [hguard, hrange, guard]

/-- **Master multi-epoch crash-safe NVMe theorem**:
after every finite interleaving of out-of-order sector DMAs, torn evictions, FLUSH barriers,
atomic `cSHAKE256`-authenticated FUA superblocks, checkpoint compactions, and repeated power cuts:
1. Cold recovery reads ONLY durable `d.media` and decodes the exact active WAL suffix and 256-bit chain digest.
2. All committed records are authorized, nullifiers & dispatched issues are strictly unique, and per-principal
   spending never exceeds `pol.budgetCap`.
3. Every transmitted TX receipt indexes its exact original record, and every active-window receipt replays
   to `.cached (z.1 + 1)`. -/
theorem durable_appliance {pol permit d p all base tx issues}
    (trace : Run pol permit d p all base tx issues) :
    (∃ sb, recoverFull pol d = some (sb, all.drop base) ∧
      sb.generation.toNat = all.length ∧ sb.baseGen.toNat = base ∧
      sb.chainDigest = logDigest all) ∧
    Accepted pol permit all ∧ issues.Nodup ∧ (all.map Record.nullifier).Nodup ∧
    (∀ who, spent all who ≤ pol.budgetCap) ∧
    ∀ z ∈ tx, all[z.1]? = some z.2 ∧
      (base ≤ z.1 →
        requestWith pol base (maxNullifier (all.take base)) (fun who => spent (all.take base) who)
          (all.drop base) z.2.principal z.2 = .cached (z.1 + 1)) := by
  have h := run_good trace
  obtain ⟨sb, hrec, hgen, hbas, _, _, hcd⟩ := recoverFull_of_good h
  refine ⟨⟨sb, hrec, hgen, hbas, hcd⟩, h.authorized, h.uniqueIssues,
    (accepted_nodup h.authorized).1, accepted_budget h.authorized, fun z hz => ?_⟩
  have atIndex := h.transmitted z hz
  refine ⟨atIndex, fun hge => ?_⟩
  have hdropIdx : (all.drop base)[z.1 - base]? = some z.2 := by
    rw [List.getElem?_drop, show base + (z.1 - base) = z.1 by omega]
    exact atIndex
  have hmem : z.2 ∈ all.drop base := List.mem_of_getElem? hdropIdx
  rw [replayWith pol base _ _ (all.drop base) hmem]
  have hnodupDrop : (all.drop base).Nodup := (accepted_nodup h.authorized).2.drop
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hdropIdx
  rw [← heq, hnodupDrop.idxOf_getElem, show base + (z.1 - base) = z.1 by omega]

theorem cold_recover_highWater {pol permit d p all base tx issues}
    (h : Run pol permit d p all base tx issues) :
    ∃ sb, recoverFull pol d = some (sb, all.drop base) ∧
      maxNullifier all ≤ max sb.highWaterNullifier.toNat (maxNullifier (all.drop base)) := by
  obtain ⟨sb, hrec, _, _, _, hhw, _⟩ := recoverFull_of_good (run_good h)
  refine ⟨sb, hrec, ?_⟩
  rw [hhw, maxNullifier_take_drop]
  exact Nat.le_refl _

theorem cold_account {pol permit d p all tx issues}
    (h : Run pol permit d p all 0 tx issues) (who : Nat) :
    (recover pol d).map (fun log => (log.map Record.nullifier, receiptHead log who, remaining pol log who)) =
      some (all.map Record.nullifier, receiptHead all who, pol.budgetCap - spent all who) ∧
    spent all who ≤ pol.budgetCap := by
  obtain ⟨⟨sb, hrec, _⟩, _, _, _, hbud, _⟩ := durable_appliance h
  refine ⟨?_, hbud who⟩
  unfold recover
  rw [hrec]
  simp [remaining]

theorem live_wal_confined {pol permit d r written all base tx issues}
    (h : Run pol permit d (.dma r written) all base tx issues) {k : Nat} (hk : k < entrySectors d.geometry) :
    walLba d.geometry (all.drop base).length k < d.geometry.sectors ∧
      walLba d.geometry (all.drop base).length k ≠ d.geometry.ctrlLba := by
  have good := run_good h
  have hfp := fresh_props good.inflight.2.1
  have hgu := good.geometry
  simp only [Geometry.usable, decide_eq_true_eq] at hgu
  exact wal_confined good.geometry (by omega) hk

theorem fresh_fits {pol : Policy} (xs : List Record) (r : Record)
    (h : request pol xs r.principal r = .fresh) :
    spent xs r.principal + r.cost ≤ pol.budgetCap := by
  have hfp := fresh_props h
  simpa using hfp.2.2.2.1

/-- **Anti-bricking / unbounded-generations theorem**:
even on a minimal 1-slot WAL ring (`pol.maxTurns = 1`), checkpoint compaction lets the appliance
commit arbitrarily many turns `n` (far beyond `8` or `maxTurns`) with full durability and recovery. -/
theorem unbounded_generations_via_checkpoint (n : Nat) (hn : n < 2 ^ 64) :
    let pol : Policy := ⟨1, n, 4096⟩
    ∃ d all, Run pol (fun _ _ => True) d .idle all n [] [] ∧
      all.length = n ∧ (∀ i < n, (all[i]?).map Record.nullifier = some (i + 1)) := by
  intro pol
  let g : Geometry := ⟨10, 512, 0, 0, 1, 1, 8⟩
  have hgu : g.usable pol = true := by
    unfold Geometry.usable
    simp only [pol, g, entrySectors, sectorSize]
    decide
  suffices ∀ (k : Nat), k ≤ n →
      ∃ d all, Run pol (fun _ _ => True) d .idle all k [] [] ∧ d.geometry = g ∧
        all.length = k ∧ (∀ i < k, (all[i]?).map Record.nullifier = some (i + 1)) ∧
        maxNullifier all = k ∧ spent all 1 = k from by
    obtain ⟨d, all, hrun, _, hlen, hids, _, _⟩ := this n (Nat.le_refl _)
    exact ⟨d, all, hrun, hlen, hids⟩
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨_, [], .boot g hgu (fun _ => zeroSector), rfl, rfl, fun _ h => by omega, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨d, all, hrun, hg0, hlen, hids, hmax, hsp⟩ := ih (by omega)
    let r : Record := ⟨1, k + 1, k + 1, 1, ByteArray.empty⟩
    have hdrop0 : all.drop k = [] := by rw [← hlen]; exact List.drop_length
    have htakeAll : all.take k = all := by rw [← hlen]; exact List.take_length
    have hfresh : requestWith pol k (maxNullifier (all.take k)) (fun p => spent (all.take k) p)
        (all.drop k) r.principal r = .fresh := by
      rw [hdrop0, htakeAll, hmax]
      unfold requestWith remainingWith
      have hsp1 : spent all 1 = k := hsp
      have hrem : 1 ≤ pol.budgetCap - (spent all 1 + 0) := by
        rw [hsp1]; dsimp only [pol]; omega
      have hcond : (0 < pol.maxTurns ∧ 0 < (1 : Nat) ∧ 1 ≤ pol.budgetCap - (spent all 1 + 0) ∧
          k < k + 1 ∧ 0 < k + 1 ∧ (1 : Nat) < 2 ^ 64 ∧ k + 1 < 2 ^ 64 ∧ k + 1 < 2 ^ 64 ∧
          (1 : Nat) < 2 ^ 64 ∧ (0 : Nat) ≤ pol.maxPayload ∧ (0 : Nat) < 2 ^ 64) := by
        refine ⟨by dsimp [pol]; omega, by decide, hrem, by omega, by omega, by decide, by omega,
          by omega, by decide, by dsimp [pol]; omega, by decide⟩
      simp only [r, List.not_mem_nil, ↓reduceIte, ne_eq, not_true_eq_false, List.length_nil,
        show spent [] 1 = 0 from rfl, ByteArray.size_empty, List.all_nil, Bool.and_true,
        decide_eq_true hcond]
    have h0 := Run.beginTurn hrun hfresh trivial (by omega)
    have writeAll : ∀ (m : Nat), m ≤ 9 →
        ∃ d' w', Run pol (fun _ _ => True) d' (.dma r w') all k [] [] ∧
          d'.geometry = g ∧ (∀ j < m, j ∈ w') ∧ (∀ x ∈ w', x < m) := by
      intro m
      induction m with
      | zero =>
        intro _
        exact ⟨d, [], h0, hg0, fun _ h => by omega, fun _ h => by cases h⟩
      | succ m ihm =>
        intro hm
        obtain ⟨d', w', hr', hg', hin, hlt⟩ := ihm (by omega)
        have hnotIn : m ∉ w' := fun h => Nat.lt_irrefl m (hlt m h)
        have hcls : classify d'.geometry (all.drop k).length (.dma r w')
            (commandFor d'.geometry (all.drop k).length (.walSector m)) = some (.walSector m) := by
          have hent : entrySectors d'.geometry = 9 := by rw [hg']; rfl
          simp [classify, commandFor, walLba, hent, hnotIn, show m < 9 by omega]
        refine ⟨_, m :: w', Run.dmaSectorDone hr' _ hcls, hg', fun j hj => ?_, fun x hx => ?_⟩
        · by_cases hjm : j = m
          · subst hjm; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hin j (by omega))
        · rcases List.mem_cons.mp hx with rfl | hx'
          · omega
          · exact Nat.lt_trans (hlt x hx') (Nat.lt_succ_self m)
    obtain ⟨dW, wW, hrW, hgW, hinW, _⟩ := writeAll 9 (Nat.le_refl _)
    have hclsFlush : classify dW.geometry (all.drop k).length (.dma r wW)
        (commandFor dW.geometry (all.drop k).length .barrier) = some .barrier := by
      have hent : entrySectors dW.geometry = 9 := by rw [hgW]; rfl
      have hallW : allSectorsWritten dW.geometry wW = true := by
        rw [allSectorsWritten, hent, List.all_eq_true]
        intro j hj
        exact List.contains_iff_mem.mpr (hinW j (List.mem_range.mp hj))
      simp [classify, commandFor, hallW]
    have hFl := Run.flush hrW _ hclsFlush
    have hclsFua : classify (flushCache dW).geometry (all.drop k).length (.flushed r)
        (commandFor (flushCache dW).geometry (all.drop k).length .commit) = some .commit := by
      simp [classify, commandFor]
    have hFua := Run.fua hFl _ hclsFua
    have hCut := Run.powerCut hFua
    have hCp := Run.checkpoint hCut
    refine ⟨_, all ++ [r], by simpa [hlen] using hCp, by simpa [writeFuaSector, powerReset, flushCache] using hgW,
      by simp [hlen], fun i hi => ?_, ?_, ?_⟩
    · by_cases hik : i < k
      · rw [List.getElem?_append_left (by omega)]; exact hids i hik
      · have heq : i = k := by omega
        subst heq; rw [List.getElem?_append_right (by omega)]; simp [hlen, r]
    · rw [maxNullifier_append, hmax]; simp [maxNullifier, r]
    · simp only [spent, r, List.filter_append, List.filter_cons, beq_self_eq_true, ↓reduceIte,
        List.filter_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      exact congrArg (· + 1) hsp

end Obend.OS.NvmeDurablePersist
