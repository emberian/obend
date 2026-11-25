module
import all Obend.Vault.Log
import all Init.Data.Array.Basic
public import Std.Data.TreeMap
public import Std.Data.TreeSet
public import Obend.Vault.Log
public import Obend.Vault.Json
public import Obend.Ledger.Commit
public import Obend.Vault.Form
public import Obend.Vault.FormCheck
public import Obend.Vault.Transport
public import Obend.Vault.Retention
public import Obend.Vault.DecodeCache
public import Obend.Vault.Cost
public import Obend.Digest.Cshake256.Fast
public import Obend.Reasons
public import Obend.Codec.Hex

public section

/-
# Obend.Vault.ChunkedWorld — Merkleized Sharded World Checkpoints

Splits `Replay.World`'s `store.pages` and `store.tombs` deterministically into `128` hash buckets
by page name, stored as content-addressed JSON shard files `.obend/world/shards/<digest>.json`
together with an authenticated root manifest `.obend/world/root.json`.

* **Universal round-trip (`decodeShardedWorld_encodeShardedWorld`)**: for every `w : World`,
  `decodeShardedWorld (encodeShardedWorld w) = .ok w`, with every shard authenticated by
  cSHAKE256 (`logHash`) and exact `store.pages` / `store.tombs` list order preserved.
* **Checkpoint cache soundness (`decodeManifestWith_manifestBytes`)**: when the shard store holds
  the world's shards, `decodeManifestWith store (manifestBytes w) = some w`, discharging
  `Log.checkpoint_is_cache`'s `hcache` premise universally.
* **Incremental dirty-bucket encoding & per-bucket `DecodeCache`**: a 1-page edit re-encodes,
  hashes, and atomically writes only the changed bucket(s) plus `root.json`, while retaining
  verified per-bucket `DecodeCache.Entry` results in-process and supporting demand-loading of
  metadata or individual page buckets where safe.
-/

namespace Obend.Vault.ChunkedWorld

set_option autoImplicit false

open Lean (Json toJson)
open Obend.Doc Obend.Vault Obend.Vault.Json Obend.Vault.Log
open Obend.Ledger Obend.Ledger.Json
open Obend.Core.Data (Data)
open Obend.Core.Ty (Ty Quantity Reuse)
open Obend.Spec.Law (LawRef LawExpr)
open Obend.Vault.Affordance (Auth)
open Obend.Vault.Form (Form Grant Cell HoleTy PRef NExpr SExpr SetMove Move Assignment CheckKey CheckRecord)
open Obend.Vault.Rehydration (WitnessReceipt)
open Obend.Vault.Transport (Issue Grants Standing Landing Obligation Contract)
open Obend.Digest.Cshake256 (customizationPrefix)
open Obend.Digest.Cshake256.Fast (pushList push_data pushList_data empty_data spongeBytes sponge_fast_eq)
open Obend.Codec.Hex (hexNibbleByte decodeHexNibbleByte? byteToHex bytesToHex bytesToHexAscii bytesToHexAscii_cons
  hexAsciiToBytes? hexCharsToBytes? hexCharsToBytes?_bytesToHex hexAsciiToBytes?_bytesToHexAscii
  hexAsciiToBytes?_of_odd)

/-! ## 1. The World State & Fast ByteArray cSHAKE256 -/

deriving instance DecidableEq for Page
deriving instance DecidableEq for PageWrite
deriving instance DecidableEq for PageConflict
deriving instance DecidableEq for Store
deriving instance DecidableEq for Journal
deriving instance DecidableEq for Obend.Vault.Form.Cell
deriving instance DecidableEq for Obend.Vault.Form.Form

/-- The world beside a vault: the store of its pages and members (with the merges' open conflicts),
the register's journal, the forms it issued, the receipt chain of the proposals it judged, the
forms it received and the proposals it sent, transport state, retention contracts, declared forks
(and optional member attributions `--for MEMBER`), reasons, and form check records. -/
structure World where
  store : Store := {}
  journal : Journal := Journal.empty
  forms : List Form := []
  receipts : List WitnessReceipt := []
  received : List (String × String) := []
  sent : List (String × String) := []
  issues : List Issue := []
  grants : Grants := {}
  landed : List Landing := []
  outstanding : List Obligation := []
  minted : Nat := 0
  retention : List Retention.Contract := []
  forks : List Retention.Fork := []
  reasons : Obend.Reasons.State := {}
  checked : List Form.CheckRecord := []
  /-- Member authority attributions for declared forks (`obend fork DIR --for MEMBER`). -/
  forkMembers : List (String × String) := []
deriving DecidableEq

/-- The log's digest: cSHAKE256 customized `obend-log`. -/
def logHash (b : Bytes) : Bytes :=
  Obend.Digest.Cshake256.cshake256Bytes "obend-log".toUTF8.toList b

/-- Append native buffers directly using Lean's verified array primitive. -/
def appendByteArray (a b : ByteArray) : ByteArray := a ++ b

theorem appendByteArray_data (a b : ByteArray) :
    (appendByteArray a b).data.toList = a.data.toList ++ b.data.toList := by
  simp [appendByteArray, ByteArray.data_append]

/-- Precomputed cSHAKE256 customization block for `"obend-log"`. -/
def logPrefix : ByteArray :=
  pushList ByteArray.empty (customizationPrefix "obend-log".toUTF8.toList)

/-- Hash a `ByteArray` directly without converting through `List UInt8`. -/
def logHashArray (b : ByteArray) : Bytes :=
  if "obend-log".toUTF8.toList = [] then spongeBytes b 0x1f
  else spongeBytes (appendByteArray logPrefix b) 0x04

theorem logHashArray_eq (b : ByteArray) : logHashArray b = logHash b.data.toList := by
  unfold logHashArray logPrefix logHash Obend.Digest.Cshake256.cshake256Bytes
  by_cases h : "obend-log".toUTF8.toList = []
  · simp only [h, ite_true, sponge_fast_eq]
  · simp only [h, ite_false, sponge_fast_eq, appendByteArray_data, pushList_data,
      empty_data, List.nil_append]

/-! ## 2. Verified Prefix-Free Binary Codec with Linear `ByteArray` Fast Path -/

/-- Byte-level codec paired with its linear `ByteArray` writer (`push`) and offset reader (`readAt`). -/
structure RawCodec (α : Type) where
  enc : α → Bytes
  dec : Bytes → Option (α × Bytes)
  push : ByteArray → α → ByteArray
  readAt : ByteArray → Nat → Option (α × Nat)
  push_eq : ∀ (acc : ByteArray) (a : α), (push acc a).data.toList = acc.data.toList ++ enc a
  readAt_eq : ∀ (b : ByteArray) (off : Nat),
    dec (b.data.toList.drop off) = (readAt b off).map (fun p => (p.1, b.data.toList.drop p.2))

/-- A `RawCodec` whose `dec` universally left-inverts `enc` on every suffix. -/
structure FastCodec (α : Type) extends RawCodec α where
  roundtrip : ∀ (a : α) (rest : Bytes), dec (enc a ++ rest) = some (a, rest)

def FastCodec.encodeArray {α : Type} (c : FastCodec α) (a : α) : ByteArray :=
  c.push ByteArray.empty a

theorem FastCodec.encodeArray_eq {α : Type} (c : FastCodec α) (a : α) :
    (c.encodeArray a).data.toList = c.enc a := by
  simp [FastCodec.encodeArray, c.push_eq]

def FastCodec.decodeExact {α : Type} (c : FastCodec α) (bs : Bytes) : Option α :=
  match c.dec bs with
  | some (a, []) => some a
  | _ => none

def FastCodec.decodeExactArray {α : Type} (c : FastCodec α) (b : ByteArray) : Option α :=
  match c.readAt b 0 with
  | some (a, off) => if b.size ≤ off then some a else none
  | none => none

theorem FastCodec.decodeExact_enc {α : Type} (c : FastCodec α) (a : α) :
    c.decodeExact (c.enc a) = some a := by
  have h := c.roundtrip a []
  rw [List.append_nil] at h
  simp [FastCodec.decodeExact, h]

theorem FastCodec.decodeExactArray_eq {α : Type} (c : FastCodec α) (b : ByteArray) :
    c.decodeExactArray b = c.decodeExact b.data.toList := by
  have hr := c.readAt_eq b 0
  simp only [List.drop_zero] at hr
  unfold FastCodec.decodeExactArray FastCodec.decodeExact
  rw [hr]
  cases h : c.readAt b 0 with
  | none => rfl
  | some p =>
    obtain ⟨a, off⟩ := p
    dsimp only [Option.map]
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases ho : b.size ≤ off
    · have hnil : b.data.toList.drop off = [] := List.drop_eq_nil_of_le (by omega)
      simp [ho, hnil]
    · have hne : b.data.toList.drop off ≠ [] := by
        intro hn; rw [List.drop_eq_nil_iff] at hn; omega
      simp only [ho, ↓reduceIte]
      cases hd : b.data.toList.drop off with
      | nil => exact absurd hd hne
      | cons _ _ => rfl

/-! ### Primitive & Combinator Codecs -/

def rawFail {α : Type} : RawCodec α where
  enc _ := []
  dec _ := none
  push acc _ := acc
  readAt _ _ := none
  push_eq _ _ := by simp
  readAt_eq _ _ := rfl

def cUnit : FastCodec Unit where
  enc _ := []
  dec bs := some ((), bs)
  push acc _ := acc
  readAt _ off := some ((), off)
  roundtrip _ _ := rfl
  push_eq _ _ := by simp
  readAt_eq _ _ := rfl

theorem push_u8_data (acc : ByteArray) (x : UInt8) :
    (acc.push x).data.toList = acc.data.toList ++ [x] := by
  simp

def cUInt8 : FastCodec UInt8 where
  enc x := [x]
  dec
    | x :: rest => some (x, rest)
    | [] => none
  push acc x := acc.push x
  readAt b off := if h : off < b.size then some (b[off]'h, off + 1) else none
  roundtrip _ _ := rfl
  push_eq := push_u8_data
  readAt_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases h : off < b.size
    · have hl : off < b.data.toList.length := by omega
      rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
      rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
      rfl

def rawMap {α β : Type} (to : α → β) (of : β → Option α) (c : RawCodec β) : RawCodec α where
  enc a := c.enc (to a)
  dec bs := match c.dec bs with
    | none => none
    | some (b, r) => (of b).map (·, r)
  push acc a := c.push acc (to a)
  readAt b off := match c.readAt b off with
    | none => none
    | some (v, o) => (of v).map (·, o)
  push_eq acc a := c.push_eq acc (to a)
  readAt_eq b off := by
    rw [c.readAt_eq b off]
    cases c.readAt b off with
    | none => rfl
    | some p => dsimp only [Option.map]; cases of p.1 <;> rfl

def cMap {α β : Type} (to : α → β) (of : β → Option α) (of_to : ∀ a, of (to a) = some a)
    (c : FastCodec β) : FastCodec α where
  toRawCodec := rawMap to of c.toRawCodec
  roundtrip a rest := by
    simp [rawMap, c.roundtrip, of_to]

def cBool : FastCodec Bool :=
  cMap (fun b => if b then (1 : UInt8) else 0)
    (fun u => if u == 0 then some false else if u == 1 then some true else none)
    (by intro b; cases b <;> rfl) cUInt8

def rawPair {α β : Type} (c1 : RawCodec α) (c2 : RawCodec β) : RawCodec (α × β) where
  enc p := c1.enc p.1 ++ c2.enc p.2
  dec bs := match c1.dec bs with
    | none => none
    | some (x, r1) => match c2.dec r1 with
      | none => none
      | some (y, r2) => some ((x, y), r2)
  push acc p := c2.push (c1.push acc p.1) p.2
  readAt b off := match c1.readAt b off with
    | none => none
    | some (x, o1) => match c2.readAt b o1 with
      | none => none
      | some (y, o2) => some ((x, y), o2)
  push_eq acc p := by rw [c2.push_eq, c1.push_eq, List.append_assoc]
  readAt_eq b off := by
    rw [c1.readAt_eq b off]
    cases c1.readAt b off with
    | none => rfl
    | some p1 =>
      dsimp only [Option.map]
      rw [c2.readAt_eq b p1.2]
      cases c2.readAt b p1.2 <;> rfl

def cPair {α β : Type} (c1 : FastCodec α) (c2 : FastCodec β) : FastCodec (α × β) where
  toRawCodec := rawPair c1.toRawCodec c2.toRawCodec
  roundtrip p rest := by
    simp [rawPair, List.append_assoc, c1.roundtrip, c2.roundtrip]

def rawOption {α : Type} (c : RawCodec α) : RawCodec (Option α) where
  enc
    | none => [0]
    | some x => 1 :: c.enc x
  dec
    | 0 :: rest => some (none, rest)
    | 1 :: rest => match c.dec rest with
      | none => none
      | some (x, r) => some (some x, r)
    | _ => none
  push acc
    | none => acc.push 0
    | some x => c.push (acc.push 1) x
  readAt b off :=
    if h : off < b.size then
      if b[off]'h == 0 then some (none, off + 1)
      else if b[off]'h == 1 then
        match c.readAt b (off + 1) with
        | none => none
        | some (x, o) => some (some x, o)
      else none
    else none
  push_eq acc
    | none => push_u8_data acc 0
    | some x => by rw [c.push_eq, push_u8_data]; simp
  readAt_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases h : off < b.size
    · have hl : off < b.data.toList.length := by omega
      rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
      have hg : b.data.toList[off]'hl = b[off]'h := rfl
      rw [hg]
      generalize b[off]'h = tag
      by_cases h0 : tag = 0
      · subst h0; rfl
      · have hb0 : (tag == 0) = false := beq_false_of_ne h0
        by_cases h1 : tag = 1
        · subst h1
          have h10 : ((1 : UInt8) == 0) = false := rfl
          have h11 : ((1 : UInt8) == 1) = true := rfl
          simp only [h10, h11, Bool.false_eq_true, ite_false, ite_true, c.readAt_eq b (off + 1)]
          cases c.readAt b (off + 1) <;> rfl
        · have hb1 : (tag == 1) = false := beq_false_of_ne h1
          simp only [hb0, hb1, Bool.false_eq_true, ite_false, Option.map]
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, hv⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | n + 2, _, _ => rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
      rfl

def cOption {α : Type} (c : FastCodec α) : FastCodec (Option α) where
  toRawCodec := rawOption c.toRawCodec
  roundtrip
    | none, _ => rfl
    | some x, rest => by simp [rawOption, c.roundtrip]

def rawSum {α β : Type} (c1 : RawCodec α) (c2 : RawCodec β) : RawCodec (α ⊕ β) where
  enc
    | .inl x => 0 :: c1.enc x
    | .inr y => 1 :: c2.enc y
  dec
    | 0 :: rest => match c1.dec rest with
      | none => none
      | some (x, r) => some (.inl x, r)
    | 1 :: rest => match c2.dec rest with
      | none => none
      | some (y, r) => some (.inr y, r)
    | _ => none
  push acc
    | .inl x => c1.push (acc.push 0) x
    | .inr y => c2.push (acc.push 1) y
  readAt b off :=
    if h : off < b.size then
      if b[off]'h == 0 then
        match c1.readAt b (off + 1) with
        | none => none
        | some (x, o) => some (.inl x, o)
      else if b[off]'h == 1 then
        match c2.readAt b (off + 1) with
        | none => none
        | some (y, o) => some (.inr y, o)
      else none
    else none
  push_eq acc
    | .inl x => by rw [c1.push_eq, push_u8_data]; simp
    | .inr y => by rw [c2.push_eq, push_u8_data]; simp
  readAt_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases h : off < b.size
    · have hl : off < b.data.toList.length := by omega
      rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
      have hg : b.data.toList[off]'hl = b[off]'h := rfl
      rw [hg]
      generalize b[off]'h = tag
      by_cases h0 : tag = 0
      · subst h0
        have h00 : ((0 : UInt8) == 0) = true := rfl
        simp only [h00, ite_true, c1.readAt_eq b (off + 1)]
        cases c1.readAt b (off + 1) <;> rfl
      · have hb0 : (tag == 0) = false := beq_false_of_ne h0
        by_cases h1 : tag = 1
        · subst h1
          have h10 : ((1 : UInt8) == 0) = false := rfl
          have h11 : ((1 : UInt8) == 1) = true := rfl
          simp only [h10, h11, Bool.false_eq_true, ite_false, ite_true, c2.readAt_eq b (off + 1)]
          cases c2.readAt b (off + 1) <;> rfl
        · have hb1 : (tag == 1) = false := beq_false_of_ne h1
          simp only [hb0, hb1, Bool.false_eq_true, ite_false, Option.map]
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, hv⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | n + 2, _, _ => rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
      rfl

def cSum {α β : Type} (c1 : FastCodec α) (c2 : FastCodec β) : FastCodec (α ⊕ β) where
  toRawCodec := rawSum c1.toRawCodec c2.toRawCodec
  roundtrip
    | .inl x, rest => by simp [rawSum, c1.roundtrip]
    | .inr y, rest => by simp [rawSum, c2.roundtrip]

/-! ### Unbounded LEB128 `Nat` Codec -/

def encNat (n : Nat) : Bytes :=
  if n < 128 then [n.toUInt8]
  else (128 + n % 128).toUInt8 :: encNat (n / 128)
termination_by n

def decNat : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else match decNat rest with
      | none => none
      | some (hi, r) => some ((b.toNat - 128) + 128 * hi, r)

def pushNat (acc : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then acc.push n.toUInt8
  else pushNat (acc.push (128 + n % 128).toUInt8) (n / 128)
termination_by n

def readNatAt (b : ByteArray) (off : Nat) : Option (Nat × Nat) :=
  if h : off < b.size then
    let x := b[off]'h
    if x.toNat < 128 then some (x.toNat, off + 1)
    else match readNatAt b (off + 1) with
      | none => none
      | some (hi, o) => some ((x.toNat - 128) + 128 * hi, o)
  else none
termination_by b.size - off

theorem u8_toNat_lt (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem decNat_encNat (n : Nat) (rest : Bytes) : decNat (encNat n ++ rest) = some (n, rest) := by
  rw [encNat]
  by_cases h : n < 128
  · simp only [h, ↓reduceIte, List.singleton_append, decNat, u8_toNat_lt n (by omega)]
  · simp only [h, ↓reduceIte, List.cons_append]
    have hmod : 128 + n % 128 < 256 := by omega
    have hu : (128 + n % 128).toUInt8.toNat = 128 + n % 128 := u8_toNat_lt _ hmod
    have hge : ¬ (128 + n % 128 < 128) := by omega
    unfold decNat
    rw [hu]
    simp only [hge, ↓reduceIte, decNat_encNat (n / 128) rest]
    congr 1; congr 1; omega
termination_by n

theorem pushNat_eq (acc : ByteArray) (n : Nat) :
    (pushNat acc n).data.toList = acc.data.toList ++ encNat n := by
  rw [pushNat, encNat]
  by_cases h : n < 128
  · simp only [h, ↓reduceIte, push_u8_data]
  · simp only [h, ↓reduceIte]
    rw [pushNat_eq _ (n / 128), push_u8_data, List.append_assoc]
    rfl
termination_by n

theorem readNatAt_eq (b : ByteArray) (off : Nat) :
    decNat (b.data.toList.drop off) =
      (readNatAt b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [readNatAt]
  by_cases h : off < b.size
  · have hl : off < b.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
    have hg : b.data.toList[off]'hl = b[off]'h := rfl
    rw [hg]
    dsimp only [decNat]
    by_cases hx : (b[off]'h).toNat < 128
    · simp only [hx, ↓reduceIte, Option.map]
    · simp only [hx, ↓reduceIte, readNatAt_eq b (off + 1)]
      cases readNatAt b (off + 1) <;> rfl
  · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]; rfl
termination_by b.size - off

theorem readNatAt_le (b : ByteArray) (off n o : Nat) (h : readNatAt b off = some (n, o)) :
    o ≤ b.size := by
  rw [readNatAt] at h
  by_cases hb : off < b.size
  · rw [dite_eq_left_of_eq_true (eq_true hb)] at h
    dsimp only at h
    by_cases hx : (b[off]'hb).toNat < 128
    · simp only [hx, ↓reduceIte] at h
      injection h with hp
      injection hp with _ ho
      omega
    · simp only [hx, ↓reduceIte] at h
      cases hr : readNatAt b (off + 1) with
      | none => simp [hr] at h
      | some p =>
        rw [hr] at h
        injection h with hp
        injection hp with _ ho
        have ih := readNatAt_le b (off + 1) p.1 p.2 hr
        omega
  · rw [dite_eq_right_of_eq_false (eq_false hb)] at h
    contradiction
termination_by b.size - off

def cNat : FastCodec Nat where
  enc := encNat
  dec := decNat
  push := pushNat
  readAt := readNatAt
  roundtrip := decNat_encNat
  push_eq := pushNat_eq
  readAt_eq := readNatAt_eq

def cInt : FastCodec Int :=
  cMap
    (fun | .ofNat n => .inl n | .negSucc n => .inr n)
    (fun | .inl n => some (.ofNat n) | .inr n => some (.negSucc n))
    (by intro i; cases i <;> rfl)
    (cSum cNat cNat)

/-! ### Length-Prefixed Lists, Arrays, ByteArrays & Strings -/

def decListN {α : Type} (dec : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs => match dec bs with
    | none => none
    | some (x, r1) => match decListN dec n r1 with
      | none => none
      | some (xs, r2) => some (x :: xs, r2)

def readListN {α : Type} (rd : ByteArray → Nat → Option (α × Nat)) :
    Nat → ByteArray → Nat → Array α → Option (List α × Nat)
  | 0, _, off, acc => some (acc.toList, off)
  | n + 1, b, off, acc => match rd b off with
    | none => none
    | some (x, o1) => readListN rd n b o1 (acc.push x)

theorem readListN_eq {α : Type} (c : RawCodec α) :
    ∀ (n : Nat) (b : ByteArray) (off : Nat) (acc : Array α),
      (decListN c.dec n (b.data.toList.drop off)).map (fun p => (acc.toList ++ p.1, p.2)) =
        (readListN c.readAt n b off acc).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, b, off, acc => by simp [decListN, readListN]
  | n + 1, b, off, acc => by
    simp only [decListN, readListN, c.readAt_eq b off]
    cases c.readAt b off with
    | none => rfl
    | some p1 =>
      have ih := readListN_eq c n b p1.2 (acc.push p1.1)
      cases hd : decListN c.dec n (b.data.toList.drop p1.2) <;>
        cases hr : readListN c.readAt n b p1.2 (acc.push p1.1) <;>
        simp [hd, hr, Option.map, Array.toList_push, List.append_assoc] at ih ⊢ <;>
        exact ih

theorem foldl_push_eq {α : Type} (c : RawCodec α) :
    ∀ (xs : List α) (acc : ByteArray),
      (xs.foldl c.push acc).data.toList = acc.data.toList ++ xs.flatMap c.enc
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.flatMap_cons, foldl_push_eq c xs (c.push acc x),
      c.push_eq, List.append_assoc]

def rawList {α : Type} (c : RawCodec α) : RawCodec (List α) where
  enc xs := encNat xs.length ++ xs.flatMap c.enc
  dec bs := match decNat bs with
    | none => none
    | some (n, r) => decListN c.dec n r
  push acc xs := xs.foldl c.push (pushNat acc xs.length)
  readAt b off := match readNatAt b off with
    | none => none
    | some (n, o) => readListN c.readAt n b o #[]
  push_eq acc xs := by
    rw [foldl_push_eq c xs (pushNat acc xs.length), pushNat_eq, List.append_assoc]
  readAt_eq b off := by
    rw [readNatAt_eq b off]
    cases readNatAt b off with
    | none => rfl
    | some p =>
      have hl := readListN_eq c p.1 b p.2 #[]
      cases hd : decListN c.dec p.1 (b.data.toList.drop p.2) with
      | none =>
        cases hr : readListN c.readAt p.1 b p.2 #[] with
        | none => simp [hd, hr, Option.map]
        | some q => simp [hd, hr, Option.map] at hl
      | some p2 =>
        obtain ⟨xs, r⟩ := p2
        cases hr : readListN c.readAt p.1 b p.2 #[] with
        | none => simp [hd, hr, Option.map] at hl
        | some q =>
          obtain ⟨ys, o2⟩ := q
          simp [hd, hr, Option.map] at hl ⊢
          exact hl

theorem decListN_enc_mem {α : Type} (c : RawCodec α) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ rest, c.dec (c.enc x ++ rest) = some (x, rest)) →
      ∀ (rest : Bytes), decListN c.dec xs.length (xs.flatMap c.enc ++ rest) = some (xs, rest)
  | [], _, _ => rfl
  | x :: xs, h, rest => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decListN,
      h x List.mem_cons_self, decListN_enc_mem c xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) rest]

def cList {α : Type} (c : FastCodec α) : FastCodec (List α) where
  toRawCodec := rawList c.toRawCodec
  roundtrip xs rest := by
    simp only [rawList, List.append_assoc, decNat_encNat]
    exact decListN_enc_mem c.toRawCodec xs (fun x _ r => c.roundtrip x r) rest

def cArray {α : Type} (c : FastCodec α) : FastCodec (Array α) :=
  cMap Array.toList (fun xs => some xs.toArray) (by intro a; simp) (cList c)

def readBytesLoop (b : ByteArray) (i stop : Nat) (acc : Array UInt8) : Bytes :=
  if h : i < stop then
    if hb : i < b.size then
      readBytesLoop b (i + 1) stop (acc.push (b[i]'hb))
    else acc.toList
  else acc.toList
termination_by stop - i

theorem readBytesLoop_eq (b : ByteArray) (i stop : Nat) (acc : Array UInt8) (hstop : stop ≤ b.size) :
    readBytesLoop b i stop acc = acc.toList ++ (b.data.toList.drop i).take (stop - i) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [readBytesLoop]
  by_cases h : i < stop
  · have hb : i < b.size := by omega
    have hl : i < b.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true hb),
      readBytesLoop_eq b (i + 1) stop _ hstop]
    obtain ⟨k, hk⟩ : ∃ k, stop - i = k + 1 := ⟨stop - i - 1, by omega⟩
    have hk' : stop - (i + 1) = k := by omega
    rw [hk, hk', List.drop_eq_getElem_cons hl, List.take_succ_cons]
    have hg : b.data.toList[i]'hl = b[i]'hb := rfl
    rw [hg]
    simp [Array.toList_push, List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have h0 : stop - i = 0 := by omega
    simp [h0]
termination_by stop - i

def cBytes : FastCodec Bytes where
  enc bs := encNat bs.length ++ bs
  dec bs := match decNat bs with
    | none => none
    | some (n, r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  push acc bs := pushList (pushNat acc bs.length) bs
  readAt b off := match readNatAt b off with
    | none => none
    | some (n, o) => if o + n ≤ b.size then some (readBytesLoop b o (o + n) #[], o + n) else none
  roundtrip xs rest := by
    rw [List.append_assoc, decNat_encNat]
    dsimp only
    simp
  push_eq acc bs := by
    rw [pushList_data, pushNat_eq, List.append_assoc]
  readAt_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    rw [readNatAt_eq b off]
    cases hr : readNatAt b off with
    | none => rfl
    | some p =>
      obtain ⟨n, o⟩ := p
      dsimp only [Option.map]
      have ho : o ≤ b.size := readNatAt_le b off n o hr
      by_cases h : o + n ≤ b.size
      · have hle : n ≤ (b.data.toList.drop o).length := by simp [hs]; omega
        simp only [hle, h, ↓reduceIte]
        rw [readBytesLoop_eq b o (o + n) #[] h]
        have hn : o + n - o = n := by omega
        rw [hn, List.drop_drop]
        simp
      · have hgt : ¬ (n ≤ (b.data.toList.drop o).length) := by simp [hs]; omega
        simp only [hgt, h, ↓reduceIte]

/-- Length-framed native byte slices. Only the logical codec projects to a byte list. -/
def cByteArray : FastCodec ByteArray :=
  let spec := cMap (fun (b : ByteArray) => b.data.toList) (fun xs => some ⟨xs.toArray⟩)
    (by intro b; cases b; simp) cBytes
  { spec with
    push := fun acc bytes => appendByteArray (pushNat acc bytes.size) bytes
    readAt := fun b off => match readNatAt b off with
      | none => none
      | some (n, pos) => if pos + n ≤ b.size then some (b.extract pos (pos + n), pos + n) else none
    push_eq := by
      intro acc bytes
      rw [appendByteArray_data, pushNat_eq, List.append_assoc]
      rfl
    readAt_eq := by
      intro b off
      rw [spec.readAt_eq]
      simp only [spec, cMap, rawMap, cBytes]
      cases hr : readNatAt b off with
      | none => rfl
      | some pair =>
        obtain ⟨n, pos⟩ := pair
        by_cases h : pos + n ≤ b.size
        · have hs : (b.extract pos (pos+n)).data.toList =
              (b.data.toList.drop pos).take n := by
            rw [ByteArray.data_extract, Array.toList_extract]
            simp [List.extract]
          have he : (⟨((b.data.toList.drop pos).take n).toArray⟩ : ByteArray) = b.extract pos (pos+n) :=
            ByteArray.ext (Array.toList_inj.mp (by simpa using hs.symm))
          simp only [h, ↓reduceIte, readBytesLoop_eq b pos (pos+n) #[] h, List.nil_append,
            Nat.add_sub_cancel_left, he, Option.map_some]
        · simp only [h, ↓reduceIte] }


def cChar : FastCodec Char :=
  cMap Char.toNat (fun n => some (Char.ofNat n))
    (fun c => congrArg some (Char.ofNat_toNat c)) cNat

def cString : FastCodec String :=
  cMap String.toList (fun cs => some (String.ofList cs))
    (fun _ => congrArg some String.ofList_toList) (cList cChar)

/-! ### Recursive Fuel-Indexed Codec Builder -/

def iterRaw {α : Type} (step : RawCodec α → RawCodec α) : Nat → RawCodec α
  | 0 => rawFail
  | k + 1 => step (iterRaw step k)

def cRec {α : Type} (depth : α → Nat) (step : RawCodec α → RawCodec α)
    (hstep : ∀ (a : α) (k : Nat), depth a ≤ k → ∀ (rest : Bytes),
      (iterRaw step k).dec ((iterRaw step k).enc a ++ rest) = some (a, rest)) : FastCodec α where
  enc a := cNat.enc (depth a) ++ (iterRaw step (depth a)).enc a
  dec bs := match cNat.dec bs with
    | none => none
    | some (k, r) => (iterRaw step k).dec r
  push acc a := (iterRaw step (depth a)).push (cNat.push acc (depth a)) a
  readAt b off := match cNat.readAt b off with
    | none => none
    | some (k, o) => (iterRaw step k).readAt b o
  roundtrip a rest := by
    rw [List.append_assoc, cNat.roundtrip]
    exact hstep a (depth a) (Nat.le_refl _) rest
  push_eq acc a := by
    rw [(iterRaw step (depth a)).push_eq, cNat.push_eq, List.append_assoc]
  readAt_eq b off := by
    rw [cNat.readAt_eq b off]
    cases cNat.readAt b off with
    | none => rfl
    | some p =>
      dsimp only [Option.map]
      exact (iterRaw step p.1).readAt_eq b p.2

/-! ## 3. Codecs for Every Component of `World` -/

/-! ### `Obend.Core.Data` -/

mutual
def dataDepth : Data → Nat
  | .natural _ | .boolean _ | .label _ => 1
  | .variant _ p => dataDepth p + 1
  | .record fs => dataDepth.dataFieldsDepth fs + 1

def dataDepth.dataFieldsDepth : List (String × Data) → Nat
  | [] => 0
  | (_, d) :: rest => max (dataDepth d) (dataDepth.dataFieldsDepth rest)
end

theorem dataDepth_mem_fields :
    ∀ (fs : List (String × Data)) (p : String × Data), p ∈ fs →
      dataDepth p.2 ≤ dataDepth.dataFieldsDepth fs
  | [], _, h => by cases h
  | (_, d) :: rest, p, h => by
    simp only [dataDepth.dataFieldsDepth]
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (dataDepth_mem_fields rest p hm) (Nat.le_max_right _ _)

def dataStep (r : RawCodec Data) : RawCodec Data :=
  rawMap
    (fun
      | .natural n => .inl (.inl n)
      | .boolean b => .inl (.inr (.inl b))
      | .label s => .inl (.inr (.inr s))
      | .record fs => .inr (.inl fs)
      | .variant l p => .inr (.inr (l, p)))
    (fun
      | .inl (.inl n) => some (.natural n)
      | .inl (.inr (.inl b)) => some (.boolean b)
      | .inl (.inr (.inr s)) => some (.label s)
      | .inr (.inl fs) => some (.record fs)
      | .inr (.inr (l, p)) => some (.variant l p))
    (rawSum (rawSum cNat.toRawCodec (rawSum cBool.toRawCodec cString.toRawCodec))
      (rawSum (rawList (rawPair cString.toRawCodec r)) (rawPair cString.toRawCodec r)))

theorem dataIter_roundtrip :
    ∀ (d : Data) (k : Nat), dataDepth d ≤ k → ∀ (rest : Bytes),
      (iterRaw dataStep k).dec ((iterRaw dataStep k).enc d ++ rest) = some (d, rest)
  | .natural n, k + 1, _, rest => by simp [iterRaw, dataStep, rawMap, rawSum, cNat.roundtrip]
  | .boolean b, k + 1, _, rest => by simp [iterRaw, dataStep, rawMap, rawSum, cBool.roundtrip]
  | .label s, k + 1, _, rest => by simp [iterRaw, dataStep, rawMap, rawSum, cString.roundtrip]
  | .variant l p, k + 1, hk, rest => by
    have hp : dataDepth p ≤ k := by simp [dataDepth] at hk; omega
    simp [iterRaw, dataStep, rawMap, rawSum, rawPair, List.append_assoc, cString.roundtrip,
      dataIter_roundtrip p k hp]
  | .record fs, k + 1, hk, rest => by
    have hfs : dataDepth.dataFieldsDepth fs ≤ k := by simp [dataDepth] at hk; omega
    have hmem : ∀ x ∈ fs, ∀ r,
        (rawPair cString.toRawCodec (iterRaw dataStep k)).dec
          ((rawPair cString.toRawCodec (iterRaw dataStep k)).enc x ++ r) = some (x, r) := by
      intro x hx r
      have hx' : dataDepth x.2 ≤ k := Nat.le_trans (dataDepth_mem_fields fs x hx) hfs
      simp [rawPair, List.append_assoc, cString.roundtrip, dataIter_roundtrip x.2 k hx']
    simp [iterRaw, dataStep, rawMap, rawSum, rawList, List.append_assoc, decNat_encNat,
      decListN_enc_mem _ fs hmem]
  | .natural _, 0, hk, _ => by simp [dataDepth] at hk
  | .boolean _, 0, hk, _ => by simp [dataDepth] at hk
  | .label _, 0, hk, _ => by simp [dataDepth] at hk
  | .variant _ _, 0, hk, _ => by simp [dataDepth] at hk
  | .record _, 0, hk, _ => by simp [dataDepth] at hk

def cData : FastCodec Data := cRec dataDepth dataStep dataIter_roundtrip

/-! ### `Obend.Doc` & `Obend.Kind` -/

def cMode : FastCodec Mode :=
  cMap (fun | .pinned => false | .following => true)
    (fun b => some (if b then .following else .pinned))
    (by intro m; cases m <;> rfl) cBool

def cRange : FastCodec Range :=
  cMap (fun r => (r.start, r.len)) (fun (s, l) => some ⟨s, l⟩)
    (by intro r; cases r; rfl) (cPair cNat cNat)

def cSpan : FastCodec Span :=
  cMap
    (fun
      | .identity => .inl false
      | .page => .inl true
      | .block id => .inr (.inl id)
      | .bytes r => .inr (.inr r))
    (fun
      | .inl false => some .identity
      | .inl true => some .page
      | .inr (.inl id) => some (.block id)
      | .inr (.inr r) => some (.bytes r))
    (by intro s; cases s <;> rfl)
    (cSum cBool (cSum cString cRange))

def cCite : FastCodec Cite :=
  cMap (fun c => (c.page, c.span, c.version, c.commitment, c.mode))
    (fun (p, sp, v, cm, m) => some ⟨p, sp, v, cm, m⟩)
    (by intro c; cases c; rfl)
    (cPair cNat (cPair cSpan (cPair cNat (cPair cBytes cMode))))

def cProjectionKind : FastCodec ProjectionKind :=
  cMap ProjectionKind.toLabel ProjectionKind.ofLabel ProjectionKind.ofLabel_toLabel cString

def cContent : FastCodec Content :=
  cMap
    (fun
      | .text s => .inl (.inl s)
      | .cite n c => .inl (.inr (n, c))
      | .field n v => .inr (.inl (n, v))
      | .cell id k ast pins rc => .inr (.inr (id, k, ast, pins, rc)))
    (fun
      | .inl (.inl s) => some (.text s)
      | .inl (.inr (n, c)) => some (.cite n c)
      | .inr (.inl (n, v)) => some (.field n v)
      | .inr (.inr (id, k, ast, pins, rc)) => some (.cell id k ast pins rc))
    (by intro c; cases c <;> rfl)
    (cSum (cSum cString (cPair cString cCite))
      (cSum (cPair cString cString)
        (cPair cString (cPair cProjectionKind (cPair cData
          (cPair (cList (cPair cString cByteArray)) (cOption cByteArray)))))))

def cGraph : FastCodec Graph :=
  cMap (fun G => (G.atoms, G.dead, G.edges))
    (fun (a, d, e) => some ⟨a, d, e⟩)
    (by intro G; cases G; rfl)
    (cPair (cList (cPair cNat cContent)) (cPair (cList cNat) (cList (cPair cNat cNat))))

/-- Prefix check using `DecidableEq` directly (needs no `LawfulBEq` instance). -/
def isPrefixDec {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => decide (x = y) && isPrefixDec xs ys

theorem isPrefixDec_append_drop {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), isPrefixDec xs ys = true → xs ++ ys.drop xs.length = ys
  | [], _, _ => rfl
  | _ :: _, [], h => by simp [isPrefixDec] at h
  | x :: xs, y :: ys, h => by
    simp only [isPrefixDec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hp⟩ := h
    simp [isPrefixDec_append_drop xs ys hp]

/-- Delta-growth encoding of `Page.history`, avoiding quadratic size blow-up on multi-version pages. -/
def encodeHistorySteps.go (prev : Graph) : List Graph → List (Bool × Graph)
  | [] => []
  | G :: rest =>
    if isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead && isPrefixDec prev.edges G.edges then
      (true, ⟨G.atoms.drop prev.atoms.length, G.dead.drop prev.dead.length, G.edges.drop prev.edges.length⟩) ::
        encodeHistorySteps.go G rest
    else
      (false, G) :: encodeHistorySteps.go G rest

def encodeHistorySteps : List Graph → List (Bool × Graph)
  | [] => []
  | G :: rest => (false, G) :: encodeHistorySteps.go G rest

def decodeHistorySteps.go (prev : Graph) : List (Bool × Graph) → Option (List Graph)
  | [] => some []
  | (false, G) :: rest => (decodeHistorySteps.go G rest).map (G :: ·)
  | (true, d) :: rest =>
    let G : Graph := ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩
    (decodeHistorySteps.go G rest).map (G :: ·)

def decodeHistorySteps : List (Bool × Graph) → Option (List Graph)
  | [] => some []
  | (true, _) :: _ => none
  | (false, G) :: rest => (decodeHistorySteps.go G rest).map (G :: ·)

theorem decodeHistorySteps_go :
    ∀ (prev : Graph) (gs : List Graph),
      decodeHistorySteps.go prev (encodeHistorySteps.go prev gs) = some gs
  | _, [] => rfl
  | prev, G :: rest => by
    simp only [encodeHistorySteps.go]
    by_cases h : (isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead &&
        isPrefixDec prev.edges G.edges) = true
    · simp only [h, ↓reduceIte]
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ha, hd⟩, he⟩ := h
      have hG : (⟨prev.atoms ++ G.atoms.drop prev.atoms.length,
          prev.dead ++ G.dead.drop prev.dead.length,
          prev.edges ++ G.edges.drop prev.edges.length⟩ : Graph) = G := by
        cases G
        simp only [Graph.mk.injEq]
        exact ⟨isPrefixDec_append_drop _ _ ha, isPrefixDec_append_drop _ _ hd,
          isPrefixDec_append_drop _ _ he⟩
      simp only [decodeHistorySteps.go, hG, decodeHistorySteps_go G rest, Option.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, decodeHistorySteps.go,
        decodeHistorySteps_go G rest, Option.map]

theorem decodeHistorySteps_encode (gs : List Graph) :
    decodeHistorySteps (encodeHistorySteps gs) = some gs := by
  cases gs with
  | nil => rfl
  | cons G rest =>
    simp [encodeHistorySteps, decodeHistorySteps, decodeHistorySteps_go]

def cHistory : FastCodec (List Graph) :=
  cMap encodeHistorySteps decodeHistorySteps decodeHistorySteps_encode
    (cList (cPair cBool cGraph))

def cKindVersion : FastCodec Obend.Kind.KindVersion :=
  cMap (fun v => (v.name, v.version)) (fun (n, v) => some ⟨n, v⟩)
    (by intro v; cases v; rfl) (cPair cString cNat)

def cKindPin : FastCodec Obend.Kind.KindPin :=
  cMap (fun p => (p.name, p.version, p.ancestors))
    (fun (n, v, a) => some ⟨n, v, a⟩)
    (by intro p; cases p; rfl)
    (cPair cString (cPair cNat (cList cKindVersion)))

/-! ### `Obend.Vault.Store` -/

def cPage : FastCodec Page :=
  cMap (fun p => (p.name, p.id, p.history, p.seen, p.authors, p.note, p.kind))
    (fun (n, id, h, s, au, no, k) => some ⟨n, id, h, s, au, no, k⟩)
    (by intro p; cases p; rfl)
    (cPair cString (cPair cNat (cPair cHistory (cPair (cOption cString)
      (cPair (cList (cPair cNat cString)) (cPair (cOption cString) (cOption cKindPin)))))))

def cMember : FastCodec Member :=
  cMap (fun m => (m.name, m.id, m.grants)) (fun (n, i, g) => some ⟨n, i, g⟩)
    (by intro m; cases m; rfl)
    (cPair cString (cPair cNat (cList (cPair cString cString))))

def cPageWrite : FastCodec PageWrite :=
  cMap (fun w => (w.versions, w.poster)) (fun (vs, po) => some ⟨vs, po⟩)
    (by intro w; cases w; rfl)
    (cPair (cList (cPair cGraph (cList (cPair cNat cString)))) (cOption cString))

def cPageConflict : FastCodec PageConflict :=
  cMap (fun c => (c.page, c.left, c.right)) (fun (p, l, r) => some ⟨p, l, r⟩)
    (by intro c; cases c; rfl)
    (cPair cString (cPair (cPair cString (cPair cString cPageWrite))
      (cPair cString (cPair cString cPageWrite))))

/-! ### `Obend.Ledger` -/

def cMovement : FastCodec Movement :=
  cMap (fun m => (m.account, m.debit, m.credit)) (fun (a, d, c) => some ⟨a, d, c⟩)
    (by intro m; cases m; rfl) (cPair cString (cPair cNat cNat))

def cPosting : FastCodec Posting :=
  cMap (fun p => (p.id, p.doc, p.period, p.reverses, p.lines, p.origin))
    (fun (i, dc, pr, rv, ls, o) => some ⟨i, dc, pr, rv, ls, o⟩)
    (by intro p; cases p; rfl)
    (cPair cString (cPair cString (cPair cNat
      (cPair (cOption cString) (cPair (cList cMovement) cString)))))

def cRow : FastCodec Row :=
  cMap (fun | .post p => .inl p | .close n => .inr n)
    (fun | .inl p => some (.post p) | .inr n => some (.close n))
    (by intro r; cases r <;> rfl) (cSum cPosting cNat)

def cJournal : FastCodec Journal :=
  cMap (fun j => (j.rows, j.head, j.last)) (fun (rs, h, l) => some ⟨rs, h, l⟩)
    (by intro j; cases j; rfl)
    (cPair (cList cRow) (cPair cString cString))

/-! ### `Obend.Vault.Form`, `Transport`, `Retention`, `Reasons`, `FormCheck` -/

def cAuth : FastCodec Auth :=
  cMap
    (fun
      | .read => (0 : UInt8) | .write => 1 | .grant => 2 | .call => 3
      | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7)
    (fun
      | 0 => some .read | 1 => some .write | 2 => some .grant | 3 => some .call
      | 4 => some .reply | 5 => some .reset | 6 => some .control | 7 => some .notify
      | _ => none)
    (by intro a; cases a <;> rfl) cUInt8

def cGrant : FastCodec Grant :=
  cMap (fun g => (g.holder, g.held, g.patterns)) (fun (h, hd, ps) => some ⟨h, hd, ps⟩)
    (by intro g; cases g; rfl)
    (cPair cString (cPair (cList cAuth) (cList cString)))

def cCell : FastCodec Cell :=
  cMap (fun c => (c.name, c.required, c.state)) (fun (n, r, s) => some ⟨n, r, s⟩)
    (by intro c; cases c; rfl)
    (cPair cString (cPair (cList cAuth) cData))

def cHoleTy : FastCodec HoleTy :=
  cMap
    (fun | .nat => (0 : UInt8) | .page => 1 | .label => 2 | .text => 3)
    (fun | 0 => some .nat | 1 => some .page | 2 => some .label | 3 => some .text | _ => none)
    (by intro t; cases t <;> rfl) cUInt8

def cPRef : FastCodec PRef :=
  cMap (fun | .page n => .inl n | .hole h => .inr h)
    (fun | .inl n => some (.page n) | .inr h => some (.hole h))
    (by intro p; cases p <;> rfl) (cSum cString cString)

def nexprDepth : NExpr → Nat
  | .lit _ | .hole _ | .field _ _ => 1
  | .add a b | .sub a b => max (nexprDepth a) (nexprDepth b) + 1

def nexprStep (r : RawCodec NExpr) : RawCodec NExpr :=
  rawMap
    (fun
      | .lit n => .inl (.inl n)
      | .hole h => .inl (.inr (.inl h))
      | .field p f => .inl (.inr (.inr (p, f)))
      | .add a b => .inr (.inl (a, b))
      | .sub a b => .inr (.inr (a, b)))
    (fun
      | .inl (.inl n) => some (.lit n)
      | .inl (.inr (.inl h)) => some (.hole h)
      | .inl (.inr (.inr (p, f))) => some (.field p f)
      | .inr (.inl (a, b)) => some (.add a b)
      | .inr (.inr (a, b)) => some (.sub a b))
    (rawSum (rawSum cNat.toRawCodec (rawSum cString.toRawCodec (rawPair cPRef.toRawCodec cString.toRawCodec)))
      (rawSum (rawPair r r) (rawPair r r)))

theorem nexprIter_roundtrip :
    ∀ (e : NExpr) (k : Nat), nexprDepth e ≤ k → ∀ (rest : Bytes),
      (iterRaw nexprStep k).dec ((iterRaw nexprStep k).enc e ++ rest) = some (e, rest)
  | .lit _, _ + 1, _, _ => by simp [iterRaw, nexprStep, rawMap, rawSum, cNat.roundtrip]
  | .hole _, _ + 1, _, _ => by simp [iterRaw, nexprStep, rawMap, rawSum, cString.roundtrip]
  | .field _ _, _ + 1, _, _ => by
    simp [iterRaw, nexprStep, rawMap, rawSum, rawPair, List.append_assoc,
      cPRef.roundtrip, cString.roundtrip]
  | .add a b, k + 1, hk, _ => by
    have ha : nexprDepth a ≤ k := by simp [nexprDepth] at hk; omega
    have hb : nexprDepth b ≤ k := by simp [nexprDepth] at hk; omega
    simp [iterRaw, nexprStep, rawMap, rawSum, rawPair, List.append_assoc,
      nexprIter_roundtrip a k ha, nexprIter_roundtrip b k hb]
  | .sub a b, k + 1, hk, _ => by
    have ha : nexprDepth a ≤ k := by simp [nexprDepth] at hk; omega
    have hb : nexprDepth b ≤ k := by simp [nexprDepth] at hk; omega
    simp [iterRaw, nexprStep, rawMap, rawSum, rawPair, List.append_assoc,
      nexprIter_roundtrip a k ha, nexprIter_roundtrip b k hb]
  | .lit _, 0, hk, _ => by simp [nexprDepth] at hk
  | .hole _, 0, hk, _ => by simp [nexprDepth] at hk
  | .field _ _, 0, hk, _ => by simp [nexprDepth] at hk
  | .add _ _, 0, hk, _ => by simp [nexprDepth] at hk
  | .sub _ _, 0, hk, _ => by simp [nexprDepth] at hk

def cNExpr : FastCodec NExpr := cRec nexprDepth nexprStep nexprIter_roundtrip

def cSExpr : FastCodec SExpr :=
  cMap
    (fun | .lit s => .inl s | .hole h => .inr (.inl h) | .field p f => .inr (.inr (p, f)))
    (fun | .inl s => some (.lit s) | .inr (.inl h) => some (.hole h) | .inr (.inr (p, f)) => some (.field p f))
    (by intro e; cases e <;> rfl)
    (cSum cString (cSum cString (cPair cPRef cString)))

def cSetMove : FastCodec SetMove :=
  cMap (fun m => (m.page, m.fields)) (fun (p, fs) => some ⟨p, fs⟩)
    (by intro m; cases m; rfl)
    (cPair cPRef (cList (cPair cString cSExpr)))

def cMove : FastCodec Move :=
  cMap (fun m => (m.asset, m.src, m.dst, m.amount)) (fun (a, s, d, am) => some ⟨a, s, d, am⟩)
    (by intro m; cases m; rfl)
    (cPair cString (cPair cPRef (cPair cPRef cNExpr)))

def cForm : FastCodec Form :=
  cMap (fun f => (f.name, f.grants, f.cells, f.refs, f.holes, f.moves, f.sets))
    (fun (n, gs, cs, rs, hs, ms, ss) => some ⟨n, gs, cs, rs, hs, ms, ss⟩)
    (by intro f; cases f; rfl)
    (cPair cString (cPair (cList cGrant) (cPair (cList cCell) (cPair (cList cString)
      (cPair (cList (cPair cString cHoleTy)) (cPair (cList cMove) (cList cSetMove)))))))

def cAssignment : FastCodec Assignment :=
  cMap (fun a => (a.nats, a.pages, a.labels)) (fun (ns, ps, ls) => some ⟨ns, ps, ls⟩)
    (by intro a; cases a; rfl)
    (cPair (cList (cPair cString cNat))
      (cPair (cList (cPair cString cString)) (cList (cPair cString cString))))

def cWitnessReceipt : FastCodec WitnessReceipt :=
  cMap (fun r => (r.prevHash, r.oldCommit, r.newCommit, r.effectsHash))
    (fun (p, o, n, e) => some ⟨p, o, n, e⟩)
    (by intro r; cases r; rfl)
    (cPair cNat (cPair cNat (cPair cNat cNat)))

def cContract : FastCodec Contract :=
  cMap (fun K => (K.hole, K.offer, K.promise)) (fun (h, o, p) => some ⟨h, o, p⟩)
    (by intro K; cases K; rfl)
    (cPair cString (cPair (cList cNat) (cList cNat)))

def cIssue : FastCodec Issue :=
  cMap (fun i => (i.form, i.contract, i.basis)) (fun (f, c, b) => some ⟨f, c, b⟩)
    (by intro i; cases i; rfl)
    (cPair cString (cPair (cOption cContract) (cList (cPair cString (cList cString)))))

def cStanding : FastCodec Standing :=
  cMap (fun s => (s.id, s.grant)) (fun (i, g) => some ⟨i, g⟩)
    (by intro s; cases s; rfl)
    (cPair cString cGrant)

def cGrants : FastCodec Grants :=
  cMap (fun g => (g.standing, g.revoked)) (fun (st, rv) => some ⟨st, rv⟩)
    (by intro g; cases g; rfl)
    (cPair (cList cStanding) (cList cString))

def cObligation : FastCodec Obligation :=
  cMap (fun o => (o.intent, o.form, o.digest, o.vault, o.holder, o.fill))
    (fun (i, f, d, v, h, a) => some ⟨i, f, d, v, h, a⟩)
    (by intro o; cases o; rfl)
    (cPair cString (cPair cString (cPair cString (cPair cString (cPair cString cAssignment)))))

def cLanding : FastCodec Landing :=
  cMap (fun l => (l.intent, l.form, l.holder, l.pages, l.supports, l.receipt))
    (fun (i, f, h, ps, ss, r) => some ⟨i, f, h, ps, ss, r⟩)
    (by intro l; cases l; rfl)
    (cPair cString (cPair cString (cPair cString
      (cPair (cList cString) (cPair (cList cString) cNat)))))

def cRetContract : FastCodec Retention.Contract :=
  cMap (fun c => (c.name, c.retire, c.abandon)) (fun (n, r, a) => some ⟨n, r, a⟩)
    (by intro c; cases c; rfl)
    (cPair cString (cPair (cList cString) (cList cString)))

def cFork : FastCodec Retention.Fork :=
  cMap (fun f => (f.name, f.merged)) (fun (n, m) => some ⟨n, m⟩)
    (by intro f; cases f; rfl)
    (cPair cString cBool)

def cObservation : FastCodec Obend.Reasons.Observation :=
  cMap (fun o => (o.name, o.text, o.source)) (fun (n, t, s) => some ⟨n, t, s⟩)
    (by intro o; cases o; rfl)
    (cPair cString (cPair cString cString))

def cRule : FastCodec Obend.Reasons.Rule :=
  cMap (fun r => (r.name, r.concl, r.pos, r.neg)) (fun (n, c, p, ng) => some ⟨n, c, p, ng⟩)
    (by intro r; cases r; rfl)
    (cPair cString (cPair cString (cPair (cList cString) (cList cString))))

def cDefeater : FastCodec Obend.Reasons.Defeater :=
  cMap (fun d => (d.target, d.by')) (fun (t, b) => some ⟨t, b⟩)
    (by intro d; cases d; rfl)
    (cPair cString cString)

def cAction : FastCodec Obend.Reasons.Action :=
  cMap (fun a => (a.name, a.because)) (fun (n, b) => some ⟨n, b⟩)
    (by intro a; cases a; rfl)
    (cPair cString cString)

def cBase : FastCodec Obend.Reasons.Base :=
  cMap (fun b => (b.observations, b.assumptions, b.withdrawn, b.explanations, b.defeaters, b.actions))
    (fun (ob, as, wd, ex, df, ac) => some ⟨ob, as, wd, ex, df, ac⟩)
    (by intro b; cases b; rfl)
    (cPair (cList cObservation) (cPair (cList cString) (cPair (cList cString)
      (cPair (cList cRule) (cPair (cList cDefeater) (cList cAction))))))

def cReasonsState : FastCodec Obend.Reasons.State :=
  cMap (fun s => (s.base, s.kept)) (fun (b, k) => some ⟨b, k⟩)
    (by intro s; cases s; rfl)
    (cPair cBase (cPair (cList cString) (cList cString)))

def cQuantity : FastCodec Quantity :=
  cMap (fun | .erased => (0 : UInt8) | .affine => 1 | .linear => 2 | .unrestricted => 3)
    (fun | 0 => some .erased | 1 => some .affine | 2 => some .linear | 3 => some .unrestricted | _ => none)
    (by intro q; cases q <;> rfl) cUInt8

def cReuse : FastCodec Reuse :=
  cMap (fun | .once => false | .reusable => true)
    (fun b => some (if b then .reusable else .once))
    (by intro r; cases r <;> rfl) cBool

def tyDepth : Ty → Nat
  | .natural | .label | .boolean | .emptyRow | .variable _ | .custody _ => 1
  | .variant r => tyDepth r + 1
  | .arrow _ _ d c => max (tyDepth d) (tyDepth c) + 1
  | .field _ m t => max (tyDepth m) (tyDepth t) + 1
  | .specification m e => max (tyDepth m) (tyDepth e) + 1
  | .prototype s t => max (tyDepth s) (tyDepth t) + 1
  | .computation p r s => max (tyDepth p) (max (tyDepth r) (tyDepth s)) + 1

def tyStep (r : RawCodec Ty) : RawCodec Ty :=
  rawMap
    (fun
      | .natural => .inl (.inl (.inl false))
      | .label => .inl (.inl (.inl true))
      | .boolean => .inl (.inl (.inr false))
      | .emptyRow => .inl (.inl (.inr true))
      | .variable i => .inl (.inr (.inl i))
      | .custody i => .inl (.inr (.inr i))
      | .variant row => .inr (.inl (.inl row))
      | .arrow ru q d c => .inr (.inl (.inr (ru, q, d, c)))
      | .field n m t => .inr (.inr (.inl (n, m, t)))
      | .specification m e => .inr (.inr (.inr (.inl (m, e))))
      | .prototype s t => .inr (.inr (.inr (.inr (.inl (s, t)))))
      | .computation p q s => .inr (.inr (.inr (.inr (.inr (p, q, s))))))
    (fun
      | .inl (.inl (.inl false)) => some .natural
      | .inl (.inl (.inl true)) => some .label
      | .inl (.inl (.inr false)) => some .boolean
      | .inl (.inl (.inr true)) => some .emptyRow
      | .inl (.inr (.inl i)) => some (.variable i)
      | .inl (.inr (.inr i)) => some (.custody i)
      | .inr (.inl (.inl row)) => some (.variant row)
      | .inr (.inl (.inr (ru, q, d, c))) => some (.arrow ru q d c)
      | .inr (.inr (.inl (n, m, t))) => some (.field n m t)
      | .inr (.inr (.inr (.inl (m, e)))) => some (.specification m e)
      | .inr (.inr (.inr (.inr (.inl (s, t))))) => some (.prototype s t)
      | .inr (.inr (.inr (.inr (.inr (p, q, s))))) => some (.computation p q s))
    (rawSum
      (rawSum (rawSum cBool.toRawCodec cBool.toRawCodec) (rawSum cNat.toRawCodec cNat.toRawCodec))
      (rawSum (rawSum r (rawPair cReuse.toRawCodec (rawPair cQuantity.toRawCodec (rawPair r r))))
        (rawSum (rawPair cString.toRawCodec (rawPair r r))
          (rawSum (rawPair r r) (rawSum (rawPair r r) (rawPair r (rawPair r r)))))))

theorem tyIter_roundtrip :
    ∀ (t : Ty) (k : Nat), tyDepth t ≤ k → ∀ (rest : Bytes),
      (iterRaw tyStep k).dec ((iterRaw tyStep k).enc t ++ rest) = some (t, rest)
  | .natural, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cBool.roundtrip]
  | .label, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cBool.roundtrip]
  | .boolean, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cBool.roundtrip]
  | .emptyRow, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cBool.roundtrip]
  | .variable _, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cNat.roundtrip]
  | .custody _, _ + 1, _, _ => by simp [iterRaw, tyStep, rawMap, rawSum, cNat.roundtrip]
  | .variant row, k + 1, hk, _ => by
    have hr : tyDepth row ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, tyIter_roundtrip row k hr]
  | .arrow _ _ d c, k + 1, hk, _ => by
    have hd : tyDepth d ≤ k := by simp [tyDepth] at hk; omega
    have hc : tyDepth c ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, rawPair, List.append_assoc,
      cReuse.roundtrip, cQuantity.roundtrip, tyIter_roundtrip d k hd, tyIter_roundtrip c k hc]
  | .field _ m t, k + 1, hk, _ => by
    have hm : tyDepth m ≤ k := by simp [tyDepth] at hk; omega
    have ht : tyDepth t ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, rawPair, List.append_assoc,
      cString.roundtrip, tyIter_roundtrip m k hm, tyIter_roundtrip t k ht]
  | .specification m e, k + 1, hk, _ => by
    have hm : tyDepth m ≤ k := by simp [tyDepth] at hk; omega
    have he : tyDepth e ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, rawPair, List.append_assoc,
      tyIter_roundtrip m k hm, tyIter_roundtrip e k he]
  | .prototype s t, k + 1, hk, _ => by
    have hs : tyDepth s ≤ k := by simp [tyDepth] at hk; omega
    have ht : tyDepth t ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, rawPair, List.append_assoc,
      tyIter_roundtrip s k hs, tyIter_roundtrip t k ht]
  | .computation p q s, k + 1, hk, _ => by
    have hp : tyDepth p ≤ k := by simp [tyDepth] at hk; omega
    have hq : tyDepth q ≤ k := by simp [tyDepth] at hk; omega
    have hs : tyDepth s ≤ k := by simp [tyDepth] at hk; omega
    simp [iterRaw, tyStep, rawMap, rawSum, rawPair, List.append_assoc,
      tyIter_roundtrip p k hp, tyIter_roundtrip q k hq, tyIter_roundtrip s k hs]
  | .natural, 0, hk, _ | .label, 0, hk, _ | .boolean, 0, hk, _ | .emptyRow, 0, hk, _
  | .variable _, 0, hk, _ | .custody _, 0, hk, _ | .variant _, 0, hk, _
  | .arrow _ _ _ _, 0, hk, _ | .field _ _ _, 0, hk, _ | .specification _ _, 0, hk, _
  | .prototype _ _, 0, hk, _ | .computation _ _ _, 0, hk, _ => by simp [tyDepth] at hk

def cTy : FastCodec Ty := cRec tyDepth tyStep tyIter_roundtrip

def cLawRef : FastCodec LawRef :=
  cMap
    (fun
      | .field n => .inl (.inl n)
      | .labelConst v => .inl (.inr v)
      | .subject => .inr (0 : UInt8)
      | .caller => .inr 1
      | .height => .inr 2
      | .turn => .inr 3)
    (fun
      | .inl (.inl n) => some (.field n)
      | .inl (.inr v) => some (.labelConst v)
      | .inr 0 => some .subject
      | .inr 1 => some .caller
      | .inr 2 => some .height
      | .inr 3 => some .turn
      | .inr _ => none)
    (by intro r; cases r <;> rfl)
    (cSum (cSum cString cString) cUInt8)

def lawDepth : LawExpr → Nat
  | .eqC _ _ | .leC _ _ | .inC _ _ | .eqR _ _ | .leR _ _ | .leROff _ _ _
  | .monotone _ | .writeOnce _ => 1
  | .not b => lawDepth b + 1
  | .and l r | .or l r | .implies l r => max (lawDepth l) (lawDepth r) + 1

def lawStep (r : RawCodec LawExpr) : RawCodec LawExpr :=
  rawMap
    (fun
      | .eqC rf v => .inl (.inl (.inl (rf, v)))
      | .leC rf v => .inl (.inl (.inr (rf, v)))
      | .inC rf vs => .inl (.inr (.inl (rf, vs)))
      | .eqR a b => .inl (.inr (.inr (.inl (a, b))))
      | .leR a b => .inl (.inr (.inr (.inr (.inl (a, b)))))
      | .leROff a b o => .inl (.inr (.inr (.inr (.inr (a, b, o)))))
      | .monotone f => .inr (.inl (.inl f))
      | .writeOnce f => .inr (.inl (.inr f))
      | .not body => .inr (.inr (.inl body))
      | .and a b => .inr (.inr (.inr (.inl (a, b))))
      | .or a b => .inr (.inr (.inr (.inr (.inl (a, b)))))
      | .implies a b => .inr (.inr (.inr (.inr (.inr (a, b))))))
    (fun
      | .inl (.inl (.inl (rf, v))) => some (.eqC rf v)
      | .inl (.inl (.inr (rf, v))) => some (.leC rf v)
      | .inl (.inr (.inl (rf, vs))) => some (.inC rf vs)
      | .inl (.inr (.inr (.inl (a, b)))) => some (.eqR a b)
      | .inl (.inr (.inr (.inr (.inl (a, b))))) => some (.leR a b)
      | .inl (.inr (.inr (.inr (.inr (a, b, o))))) => some (.leROff a b o)
      | .inr (.inl (.inl f)) => some (.monotone f)
      | .inr (.inl (.inr f)) => some (.writeOnce f)
      | .inr (.inr (.inl body)) => some (.not body)
      | .inr (.inr (.inr (.inl (a, b)))) => some (.and a b)
      | .inr (.inr (.inr (.inr (.inl (a, b))))) => some (.or a b)
      | .inr (.inr (.inr (.inr (.inr (a, b))))) => some (.implies a b))
    (rawSum
      (rawSum
        (rawSum (rawPair cLawRef.toRawCodec cInt.toRawCodec) (rawPair cLawRef.toRawCodec cInt.toRawCodec))
        (rawSum (rawPair cLawRef.toRawCodec (rawList cInt.toRawCodec))
          (rawSum (rawPair cLawRef.toRawCodec cLawRef.toRawCodec)
            (rawSum (rawPair cLawRef.toRawCodec cLawRef.toRawCodec)
              (rawPair cLawRef.toRawCodec (rawPair cLawRef.toRawCodec cInt.toRawCodec))))))
      (rawSum (rawSum cString.toRawCodec cString.toRawCodec)
        (rawSum r (rawSum (rawPair r r) (rawSum (rawPair r r) (rawPair r r))))))

theorem lawIter_roundtrip :
    ∀ (e : LawExpr) (k : Nat), lawDepth e ≤ k → ∀ (rest : Bytes),
      (iterRaw lawStep k).dec ((iterRaw lawStep k).enc e ++ rest) = some (e, rest)
  | .eqC _ _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc, cLawRef.roundtrip, cInt.roundtrip]
  | .leC _ _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc, cLawRef.roundtrip, cInt.roundtrip]
  | .inC _ vs, _ + 1, _, _ => by
    simp [iterRaw, lawStep, rawMap, rawSum, rawPair, rawList, List.append_assoc, cLawRef.roundtrip,
      decNat_encNat, decListN_enc_mem _ vs (fun x _ r => cInt.roundtrip x r)]
  | .eqR _ _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc, cLawRef.roundtrip]
  | .leR _ _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc, cLawRef.roundtrip]
  | .leROff _ _ _, _ + 1, _, _ => by
    simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc, cLawRef.roundtrip, cInt.roundtrip]
  | .monotone _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, cString.roundtrip]
  | .writeOnce _, _ + 1, _, _ => by simp [iterRaw, lawStep, rawMap, rawSum, cString.roundtrip]
  | .not b, k + 1, hk, _ => by
    have hb : lawDepth b ≤ k := by simp [lawDepth] at hk; omega
    simp [iterRaw, lawStep, rawMap, rawSum, lawIter_roundtrip b k hb]
  | .and a b, k + 1, hk, _ => by
    have ha : lawDepth a ≤ k := by simp [lawDepth] at hk; omega
    have hb : lawDepth b ≤ k := by simp [lawDepth] at hk; omega
    simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc,
      lawIter_roundtrip a k ha, lawIter_roundtrip b k hb]
  | .or a b, k + 1, hk, _ => by
    have ha : lawDepth a ≤ k := by simp [lawDepth] at hk; omega
    have hb : lawDepth b ≤ k := by simp [lawDepth] at hk; omega
    simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc,
      lawIter_roundtrip a k ha, lawIter_roundtrip b k hb]
  | .implies a b, k + 1, hk, _ => by
    have ha : lawDepth a ≤ k := by simp [lawDepth] at hk; omega
    have hb : lawDepth b ≤ k := by simp [lawDepth] at hk; omega
    simp [iterRaw, lawStep, rawMap, rawSum, rawPair, List.append_assoc,
      lawIter_roundtrip a k ha, lawIter_roundtrip b k hb]
  | .eqC _ _, 0, hk, _ | .leC _ _, 0, hk, _ | .inC _ _, 0, hk, _ | .eqR _ _, 0, hk, _
  | .leR _ _, 0, hk, _ | .leROff _ _ _, 0, hk, _ | .monotone _, 0, hk, _ | .writeOnce _, 0, hk, _
  | .not _, 0, hk, _ | .and _ _, 0, hk, _ | .or _ _, 0, hk, _ | .implies _ _, 0, hk, _ => by
    simp [lawDepth] at hk

def cLawExpr : FastCodec LawExpr := cRec lawDepth lawStep lawIter_roundtrip

def cCheckKey : FastCodec CheckKey :=
  cMap (fun k => (k.page, k.moved, k.S, k.pkg, k.lin, k.o, k.n, k.linked))
    (fun (pg, mv, S, pk, ln, o, n, lk) => some ⟨pg, mv, S, pk, ln, o, n, lk⟩)
    (by intro k; cases k; rfl)
    (cPair cString (cPair (cList cString) (cPair cTy (cPair cString
      (cPair (cList (cPair cString cLawExpr)) (cPair cData (cPair cData cBool)))))))

def cCheckRecord : FastCodec CheckRecord :=
  cMap (fun r => (r.form, r.key)) (fun (f, k) => some ⟨f, k⟩)
    (by intro r; cases r; rfl)
    (cPair cString cCheckKey)

/-! ### `NonStoreMeta` & `ShardPayload` Codecs -/

structure NonStoreMeta where
  members : List Member := []
  turn : Nat := 0
  environment : Environment := #[]
  conflicts : List PageConflict := []
  journal : Journal := Journal.empty
  forms : List Form := []
  receipts : List WitnessReceipt := []
  received : List (String × String) := []
  sent : List (String × String) := []
  issues : List Issue := []
  grants : Grants := {}
  landed : List Landing := []
  outstanding : List Obligation := []
  minted : Nat := 0
  retention : List Retention.Contract := []
  forks : List Retention.Fork := []
  reasons : Obend.Reasons.State := {}
  checked : List CheckRecord := []
  forkMembers : List (String × String) := []
deriving DecidableEq

def metaOf (w : World) : NonStoreMeta :=
  { members := w.store.members
    turn := w.store.turn
    environment := w.store.environment
    conflicts := w.store.conflicts
    journal := w.journal
    forms := w.forms
    receipts := w.receipts
    received := w.received
    sent := w.sent
    issues := w.issues
    grants := w.grants
    landed := w.landed
    outstanding := w.outstanding
    minted := w.minted
    retention := w.retention
    forks := w.forks
    reasons := w.reasons
    checked := w.checked
    forkMembers := w.forkMembers }

def withMeta (pages tombs : List Page) (m : NonStoreMeta) : World :=
  { store :=
      { pages := pages
        members := m.members
        turn := m.turn
        tombs := tombs
        environment := m.environment
        conflicts := m.conflicts }
    journal := m.journal
    forms := m.forms
    receipts := m.receipts
    received := m.received
    sent := m.sent
    issues := m.issues
    grants := m.grants
    landed := m.landed
    outstanding := m.outstanding
    minted := m.minted
    retention := m.retention
    forks := m.forks
    reasons := m.reasons
    checked := m.checked
    forkMembers := m.forkMembers }

theorem withMeta_metaOf (w : World) : withMeta w.store.pages w.store.tombs (metaOf w) = w := by
  cases w
  rename_i st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  cases st
  rfl

def cNonStoreMeta : FastCodec NonStoreMeta :=
  cMap
    (fun m => (m.members, m.turn, m.environment, m.conflicts, m.journal, m.forms, m.receipts,
      m.received, m.sent, m.issues, m.grants, m.landed, m.outstanding, m.minted, m.retention,
      m.forks, m.reasons, m.checked, m.forkMembers))
    (fun (mb, tn, ev, cf, jn, fm, rc, rv, sn, is, gr, ld, ot, mn, rt, fk, rs, ck, fkm) =>
      some ⟨mb, tn, ev, cf, jn, fm, rc, rv, sn, is, gr, ld, ot, mn, rt, fk, rs, ck, fkm⟩)
    (by intro m; cases m; rfl)
    (cPair (cList cMember) (cPair cNat (cPair (cArray cString) (cPair (cList cPageConflict)
      (cPair cJournal (cPair (cList cForm) (cPair (cList cWitnessReceipt)
        (cPair (cList (cPair cString cString)) (cPair (cList (cPair cString cString))
          (cPair (cList cIssue) (cPair cGrants (cPair (cList cLanding)
            (cPair (cList cObligation) (cPair cNat (cPair (cList cRetContract)
              (cPair (cList cFork) (cPair cReasonsState
                (cPair (cList cCheckRecord) (cList (cPair cString cString))))))))))))))))))))

abbrev ShardPayload := List (Nat × Page) × List (Nat × Page)

def cShardPayload : FastCodec ShardPayload :=
  cPair (cList (cPair cNat cPage)) (cList (cPair cNat cPage))

/-! ## 4. Deterministic 128-Bucket Partitioning & Exact Order Reassembly -/

def numBuckets : Nat := 128

/-- 64-bit FNV-1a hash over UTF-8 bytes, folded into `0 .. numBuckets - 1`. -/
def bucketOf (name : String) : Nat :=
  let h : UInt64 := name.toUTF8.foldl (fun acc b => (acc ^^^ b.toUInt64) * 1099511628211) 14695981039346656037
  ((h ^^^ (h >>> 32)).toNat) % numBuckets

theorem bucketOf_lt (name : String) : bucketOf name < numBuckets :=
  Nat.mod_lt _ (by decide)

def enumGo {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: enumGo (k + 1) xs

def enumList {α : Type} (xs : List α) : List (Nat × α) := enumGo 0 xs

def bucketItems (b : Nat) (es : List (Nat × Page)) : List (Nat × Page) :=
  es.filter fun p => bucketOf p.2.name == b

theorem enumGo_ge {α : Type} : ∀ (k : Nat) (xs : List α) (p : Nat × α),
    p ∈ enumGo k xs → k ≤ p.1
  | _, [], _, h => by cases h
  | k, _ :: xs, (_, _), h => by
    rcases List.mem_cons.mp h with he | hm
    · cases he; exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (enumGo_ge (k + 1) xs _ hm))

/-- Find the first bucket `b ∈ 0..numBuckets-1` whose head has index `k`. -/
def popBucketHead (k : Nat) (bs : Nat → List (Nat × Page)) : Option (Page × (Nat → List (Nat × Page))) :=
  match (List.range numBuckets).find? (fun b => match bs b with | (i, _) :: _ => i == k | [] => false) with
  | none => none
  | some b =>
    match bs b with
    | (_, p) :: rest => some (p, fun b' => if b' == b then rest else bs b')
    | [] => none

def reassembleGo : Nat → Nat → (Nat → List (Nat × Page)) → Option (List Page)
  | _, 0, bs =>
    if (List.range numBuckets).all (fun b => (bs b).isEmpty) then some [] else none
  | k, rem + 1, bs =>
    match popBucketHead k bs with
    | none => none
    | some (p, bs') => (reassembleGo (k + 1) rem bs').map (p :: ·)

def reassemble (total : Nat) (bs : Nat → List (Nat × Page)) : Option (List Page) :=
  reassembleGo 0 total bs

theorem find?_congr_local {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.find? p = xs.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?, h x List.mem_cons_self]
    cases q x with
    | true => rfl
    | false => exact find?_congr_local xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem all_congr_local {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.all p = xs.all q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x List.mem_cons_self,
      all_congr_local xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem popBucketHead_enumGo (k : Nat) (x : Page) (xs : List Page) :
    popBucketHead k (fun b => bucketItems b (enumGo k (x :: xs))) =
      some (x, fun b => bucketItems b (enumGo (k + 1) xs)) := by
  let bx := bucketOf x.name
  let pred : Nat → Bool := fun b =>
    match bucketItems b (enumGo k (x :: xs)) with
    | (i, _) :: _ => i == k
    | [] => false
  have hpred : ∀ b, pred b = (b == bx) := by
    intro b
    by_cases hb : b = bx
    · subst hb
      simp [pred, bucketItems, enumGo, bx]
    · have hne : (bx == b) = false := beq_false_of_ne (Ne.symm hb)
      have hne' : (b == bx) = false := beq_false_of_ne hb
      simp only [pred, bucketItems, enumGo, List.filter_cons, bx, hne, Bool.false_eq_true, ↓reduceIte, hne']
      cases hf : List.filter (fun p : Nat × Page => bucketOf p.2.name == b) (enumGo (k + 1) xs) with
      | nil => rfl
      | cons hd tl =>
        have hmem : hd ∈ enumGo (k + 1) xs := by
          have : hd ∈ List.filter (fun p : Nat × Page => bucketOf p.2.name == b) (enumGo (k + 1) xs) := by simp [hf]
          exact (List.mem_filter.mp this).1
        have hge := enumGo_ge (k + 1) xs hd hmem
        exact beq_false_of_ne (by omega)
  have hfind : (List.range numBuckets).find? pred = some bx := by
    have hlt : bx < numBuckets := bucketOf_lt x.name
    have hcong : List.find? pred (List.range numBuckets) =
        List.find? (fun b => b == bx) (List.range numBuckets) :=
      find?_congr_local _ (fun b _ => hpred b)
    rw [hcong]
    have hmem : bx ∈ List.range numBuckets := List.mem_range.mpr hlt
    cases hf : List.find? (fun b => b == bx) (List.range numBuckets) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf bx hmem
      simp at this
    | some b =>
      have hb := List.find?_some hf
      simp only [beq_iff_eq] at hb
      rw [hb]
  unfold popBucketHead
  change (match List.find? pred (List.range numBuckets) with | none => none | some b => _) = _
  rw [hfind]
  dsimp only
  have hhead : bucketItems bx (enumGo k (x :: xs)) = (k, x) :: bucketItems bx (enumGo (k + 1) xs) := by
    simp [bucketItems, enumGo, bx]
  rw [hhead]
  dsimp only
  congr 1; congr 1
  funext b'
  by_cases hb' : b' = bx
  · subst hb'; simp
  · have hne : (bx == b') = false := beq_false_of_ne (Ne.symm hb')
    have hne' : (b' == bx) = false := beq_false_of_ne hb'
    simp [hne', bucketItems, enumGo, bx, hne]

theorem reassembleGo_congr (k rem : Nat) {f g : Nat → List (Nat × Page)}
    (h : ∀ b, b < numBuckets → f b = g b) : reassembleGo k rem f = reassembleGo k rem g := by
  induction rem generalizing k f g with
  | zero =>
    unfold reassembleGo
    have hall : ((List.range numBuckets).all fun b => (f b).isEmpty) =
        ((List.range numBuckets).all fun b => (g b).isEmpty) :=
      all_congr_local _ (fun b hb => by rw [h b (List.mem_range.mp hb)])
    rw [hall]
  | succ rem ih =>
    unfold reassembleGo popBucketHead
    have hfind : (List.range numBuckets).find? (fun b => match f b with | (i, _) :: _ => i == k | [] => false) =
        (List.range numBuckets).find? (fun b => match g b with | (i, _) :: _ => i == k | [] => false) :=
      find?_congr_local _ (fun b hb => by rw [h b (List.mem_range.mp hb)])
    rw [hfind]
    cases hf : (List.range numBuckets).find? (fun b => match g b with | (i, _) :: _ => i == k | [] => false) with
    | none => rfl
    | some b =>
      have hb : b < numBuckets := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      dsimp only
      rw [h b hb]
      cases g b with
      | nil => rfl
      | cons hd tl =>
        dsimp only
        have hstep := ih (k + 1) (f := fun b' => if b' == b then tl else f b')
          (g := fun b' => if b' == b then tl else g b')
          (fun b' hb' => by by_cases e : b' == b <;> simp [e, h b' hb'])
        rw [hstep]

theorem reassembleGo_enumGo :
    ∀ (xs : List Page) (k : Nat),
      reassembleGo k xs.length (fun b => bucketItems b (enumGo k xs)) = some xs
  | [], k => by simp [reassembleGo, bucketItems, enumGo]
  | x :: xs, k => by
    simp only [List.length_cons, reassembleGo, popBucketHead_enumGo k x xs,
      reassembleGo_enumGo xs (k + 1), Option.map]

/-- **Exact bucket reassembly**: partitioning `enumList ps` across `numBuckets` buckets and
reassembling recovers `ps` in its exact original order, for every `ps : List Page`. -/
theorem reassemble_bucketItems (ps : List Page) :
    reassemble ps.length (fun b => bucketItems b (enumList ps)) = some ps :=
  reassembleGo_enumGo ps 0

/-- Pre-allocated `[0, …, 127]` list so inner loops never re-allocate `List.range numBuckets`. -/
def bucketIndices : List Nat := List.range numBuckets

/-- Linear-time `O(N)` runtime bucket partitioner (1 pass over `es` into an `Array` of 128 lists). -/
def partitionRev (es : List (Nat × Page)) : Array (List (Nat × Page)) :=
  es.foldl (fun (acc : Array (List (Nat × Page))) item =>
    acc.modify (bucketOf item.2.name) (item :: ·)) (Array.replicate numBuckets [])

def partitionAll (es : List (Nat × Page)) : Array (List (Nat × Page)) :=
  (partitionRev es).map List.reverse

theorem partitionRev_fold_inv :
    ∀ (es : List (Nat × Page)) (acc : Array (List (Nat × Page))),
      acc.size = numBuckets →
      (es.foldl (fun (a : Array (List (Nat × Page))) item =>
          a.modify (bucketOf item.2.name) (item :: ·)) acc).size = numBuckets ∧
      ∀ b, b < numBuckets →
        (es.foldl (fun (a : Array (List (Nat × Page))) item =>
            a.modify (bucketOf item.2.name) (item :: ·)) acc)[b]? =
          some ((bucketItems b es).reverse ++ (acc[b]?.getD []))
  | [], acc, hs => by
    refine ⟨hs, fun b hb => ?_⟩
    have hb' : b < acc.size := by omega
    simp [bucketItems, Array.getElem?_eq_getElem hb']
  | item :: rest, acc, hs => by
    let j := bucketOf item.2.name
    have hj : j < acc.size := by rw [hs]; exact bucketOf_lt item.2.name
    let acc' := acc.modify j (item :: ·)
    have hs' : acc'.size = numBuckets := by simp [acc', Array.size_modify, hs]
    obtain ⟨hsz, hget⟩ := partitionRev_fold_inv rest acc' hs'
    refine ⟨hsz, fun b hb => ?_⟩
    simp only [List.foldl_cons]
    rw [hget b hb]
    congr 1
    have hb' : b < acc.size := by omega
    by_cases he : j = b
    · subst he
      have hm : acc'[j]? = some (item :: acc[j]'hj) := by
        rw [Array.getElem?_eq_getElem (by rw [Array.size_modify]; exact hj), Array.getElem_modify_self]
      simp [bucketItems, j, hm, Array.getElem?_eq_getElem hj, List.append_assoc]
    · have hne : (j == b) = false := beq_false_of_ne he
      have hm : acc'[b]? = acc[b]? := by
        rw [Array.getElem?_eq_getElem (by rw [Array.size_modify]; exact hb'),
          Array.getElem?_eq_getElem hb', Array.getElem_modify_of_ne he]
      simp [bucketItems, j, hne, hm]

theorem partitionAll_size (es : List (Nat × Page)) : (partitionAll es).size = numBuckets := by
  have h := (partitionRev_fold_inv es (Array.replicate numBuckets []) (by simp)).1
  simp [partitionAll, partitionRev, h]

theorem partitionAll_getElem (es : List (Nat × Page)) (b : Nat) (hb : b < numBuckets) :
    (partitionAll es)[b]? = some (bucketItems b es) := by
  have h := (partitionRev_fold_inv es (Array.replicate numBuckets []) (by simp)).2 b hb
  simp only [partitionAll, partitionRev, Array.getElem?_map, h, Array.getElem?_replicate, hb,
    ↓reduceIte, Option.getD_some, List.append_nil, Option.map_some, List.reverse_reverse]

/-- Runtime `Array`-backed reassembler proved equivalent to `reassemble`. -/
def reassembleFromArray.go : Nat → Nat → Array (List (Nat × Page)) → Option (List Page)
  | _, 0, a =>
    if bucketIndices.all (fun b => (a[b]?.getD []).isEmpty) then some [] else none
  | k, rem + 1, a =>
    match bucketIndices.find? (fun b => match a[b]?.getD [] with | (i, _) :: _ => i == k | [] => false) with
    | none => none
    | some b =>
      match a[b]?.getD [] with
      | (_, p) :: rest => (reassembleFromArray.go (k + 1) rem (a.set! b rest)).map (p :: ·)
      | [] => none

def reassembleFromArray (total : Nat) (arr : Array (List (Nat × Page))) : Option (List Page) :=
  if arr.size != numBuckets then none else reassembleFromArray.go 0 total arr

theorem reassembleFromArray_go_eq :
    ∀ (rem k : Nat) (arr : Array (List (Nat × Page))), arr.size = numBuckets →
      reassembleFromArray.go k rem arr = reassembleGo k rem (fun b => arr[b]?.getD [])
  | 0, k, arr, _ => rfl
  | rem + 1, k, arr, hs => by
    unfold reassembleFromArray.go reassembleGo popBucketHead bucketIndices
    cases hf : (List.range numBuckets).find? (fun b => match arr[b]?.getD [] with | (i, _) :: _ => i == k | [] => false) with
    | none => rfl
    | some b =>
      have hb : b < arr.size := by rw [hs]; exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
      dsimp only
      cases hg : arr[b]?.getD [] with
      | nil => rfl
      | cons hd tl =>
        dsimp only
        have hs' : (arr.set! b tl).size = numBuckets := by simp [Array.set!, Array.size_setIfInBounds, hs]
        rw [reassembleFromArray_go_eq rem (k + 1) (arr.set! b tl) hs']
        congr 1
        apply reassembleGo_congr
        intro b' hb'
        have hb'' : b' < arr.size := by omega
        by_cases he : b' = b
        · subst he
          simp [Array.set!, hb]
        · have hne : (b' == b) = false := beq_false_of_ne he
          simp [hne, Array.set!, hb'', Ne.symm he]

theorem reassembleFromArray_eq (total : Nat) (arr : Array (List (Nat × Page)))
    (hs : arr.size = numBuckets) :
    reassembleFromArray total arr = reassemble total (fun b => arr[b]?.getD []) := by
  unfold reassembleFromArray reassemble
  have hne : (arr.size != numBuckets) = false := by simp [hs]
  rw [hne]
  exact reassembleFromArray_go_eq total 0 arr hs

/-! ## 5. Hex & RFC-8259 JSON Framing for Shards and Root Manifest -/

def pushHexArray.go (raw : ByteArray) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < raw.size then
    let b := raw[i]'h
    pushHexArray.go raw (i + 1) ((out.push (hexNibbleByte (b.toNat / 16))).push (hexNibbleByte (b.toNat % 16)))
  else out
termination_by raw.size - i

def pushHexArray (acc : ByteArray) (raw : ByteArray) : ByteArray := pushHexArray.go raw 0 acc

theorem pushHexArray_go_eq (raw : ByteArray) (i : Nat) (out : ByteArray) :
    (pushHexArray.go raw i out).data.toList =
      out.data.toList ++ bytesToHexAscii (raw.data.toList.drop i) := by
  have hs : raw.data.toList.length = raw.size := Array.length_toList
  rw [pushHexArray.go]
  by_cases h : i < raw.size
  · have hl : i < raw.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), pushHexArray_go_eq raw (i + 1), List.drop_eq_getElem_cons hl]
    have hg : raw.data.toList[i]'hl = raw[i]'h := rfl
    rw [hg, push_u8_data, push_u8_data]
    simp [bytesToHexAscii_cons, List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
    simp [bytesToHexAscii]
termination_by raw.size - i

theorem pushHexArray_eq (acc raw : ByteArray) :
    (pushHexArray acc raw).data.toList = acc.data.toList ++ bytesToHexAscii raw.data.toList := by
  simpa [pushHexArray] using pushHexArray_go_eq raw 0 acc

def unhexSliceGo (b : ByteArray) (stop : Nat) (hstop : stop ≤ b.size) (i : Nat) (out : ByteArray) :
    Option ByteArray :=
  if h : i + 1 < stop then
    have h0 : i < b.size := by omega
    have h1 : i + 1 < b.size := by omega
    match decodeHexNibbleByte? (b[i]'h0), decodeHexNibbleByte? (b[i + 1]'h1) with
    | some hi, some lo => unhexSliceGo b stop hstop (i + 2) (out.push (hi * 16 + lo).toUInt8)
    | _, _ => none
  else some out
termination_by stop - i

def unhexSlice (b : ByteArray) (start stop : Nat) : Option ByteArray :=
  if hstop : stop ≤ b.size then
    if start ≤ stop && (stop - start) % 2 == 0 then
      unhexSliceGo b stop hstop start (ByteArray.emptyWithCapacity ((stop - start) / 2))
    else none
  else none

theorem unhexSliceGo_eq (b : ByteArray) (stop : Nat) (hstop : stop ≤ b.size)
    (i : Nat) (hle : i ≤ stop) (heven : (stop - i) % 2 = 0) (out : ByteArray) :
    (unhexSliceGo b stop hstop i out).map (fun a => a.data.toList) =
      (hexAsciiToBytes? ((b.data.toList.drop i).take (stop - i))).map (out.data.toList ++ ·) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [unhexSliceGo]
  by_cases h : i + 1 < stop
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    have hl0 : i < b.data.toList.length := by omega
    have hl1 : i + 1 < b.data.toList.length := by omega
    have hsub : (b.data.toList.drop i).take (stop - i) =
        (b[i]'(by omega)) :: (b[i + 1]'(by omega)) :: (b.data.toList.drop (i + 2)).take (stop - (i + 2)) := by
      have hk : stop - i = (stop - (i + 2)) + 2 := by omega
      rw [List.drop_eq_getElem_cons hl0, List.drop_eq_getElem_cons hl1]
      have g0 : b.data.toList[i]'hl0 = b[i]'(by omega) := rfl
      have g1 : b.data.toList[i + 1]'hl1 = b[i + 1]'(by omega) := rfl
      rw [g0, g1, hk]
      rfl
    rw [hsub]
    dsimp only [hexAsciiToBytes?]
    cases decodeHexNibbleByte? (b[i]'(by omega)) with
    | none => rfl
    | some hi =>
      cases decodeHexNibbleByte? (b[i + 1]'(by omega)) with
      | none => rfl
      | some lo =>
        dsimp only [bind, Option.bind]
        rw [unhexSliceGo_eq b stop hstop (i + 2) (by omega) (by omega)]
        rw [push_u8_data]
        cases hexAsciiToBytes? ((b.data.toList.drop (i + 2)).take (stop - (i + 2))) <;>
          simp [List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have h0 : stop - i = 0 := by omega
    simp [h0, hexAsciiToBytes?]
termination_by stop - i

/-! ### Shard JSON Framing: `{"format":"obend-shard-1","hex":"..."}\n` -/

def shardPrefixArray : ByteArray := "{\"format\":\"obend-shard-1\",\"hex\":\"".toUTF8
def shardSuffixArray : ByteArray := "\"}\n".toUTF8

def shardPrefixBytes : Bytes := shardPrefixArray.data.toList
def shardSuffixBytes : Bytes := shardSuffixArray.data.toList

def frameShardBytes (raw : Bytes) : Bytes :=
  shardPrefixBytes ++ bytesToHexAscii raw ++ shardSuffixBytes

def unframeShardBytes (bs : Bytes) : Option Bytes :=
  let plen := shardPrefixBytes.length
  let slen := shardSuffixBytes.length
  if plen + slen ≤ bs.length && bs.take plen == shardPrefixBytes &&
      bs.drop (bs.length - slen) == shardSuffixBytes then
    hexAsciiToBytes? ((bs.drop plen).take (bs.length - plen - slen))
  else none

theorem take_append_exact {α : Type} : ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => by simp [take_append_exact xs ys]

theorem drop_append_exact {α : Type} : ∀ (xs ys : List α), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => by simp [drop_append_exact xs ys]

theorem unframeShardBytes_frameShardBytes (raw : Bytes) :
    unframeShardBytes (frameShardBytes raw) = some raw := by
  unfold unframeShardBytes frameShardBytes
  let p := shardPrefixBytes
  let m := bytesToHexAscii raw
  let s := shardSuffixBytes
  have hlen : (p ++ m ++ s).length = p.length + m.length + s.length := by
    simp [List.length_append, Nat.add_assoc]
  have hle : p.length + s.length ≤ (p ++ m ++ s).length := by omega
  have htake : (p ++ m ++ s).take p.length = p := by
    rw [List.append_assoc]; exact take_append_exact p (m ++ s)
  have hdropSuf : (p ++ m ++ s).drop ((p ++ m ++ s).length - s.length) = s := by
    have heq : (p ++ m ++ s).length - s.length = (p ++ m).length := by
      simp [List.length_append]; omega
    rw [heq]; exact drop_append_exact (p ++ m) s
  have hmid : ((p ++ m ++ s).drop p.length).take ((p ++ m ++ s).length - p.length - s.length) = m := by
    rw [List.append_assoc, drop_append_exact p (m ++ s)]
    have heq : (p ++ (m ++ s)).length - p.length - s.length = m.length := by
      simp [List.length_append]
    rw [heq]; exact take_append_exact m s
  have hcond : (decide (p.length + s.length ≤ (p ++ m ++ s).length) &&
      ((p ++ m ++ s).take p.length == p) &&
      ((p ++ m ++ s).drop ((p ++ m ++ s).length - s.length) == s)) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true hle, beq_iff_eq.mpr htake⟩, beq_iff_eq.mpr hdropSuf⟩
  change (if (decide (p.length + s.length ≤ (p ++ m ++ s).length) &&
      ((p ++ m ++ s).take p.length == p) &&
      ((p ++ m ++ s).drop ((p ++ m ++ s).length - s.length) == s)) = true then _ else _) = _
  dsimp only [p, m, s] at hmid
  simp only [hcond, ↓reduceIte, hmid]
  exact hexAsciiToBytes?_bytesToHexAscii raw

def frameShardArray (raw : ByteArray) : ByteArray :=
  appendByteArray (pushHexArray shardPrefixArray raw) shardSuffixArray

theorem frameShardArray_eq (raw : ByteArray) :
    (frameShardArray raw).data.toList = frameShardBytes raw.data.toList := by
  simp [frameShardArray, frameShardBytes, appendByteArray_data, pushHexArray_eq,
    shardPrefixBytes, shardSuffixBytes, List.append_assoc]

def frameShardArrayFast (raw : ByteArray) : ByteArray :=
  let cap := shardPrefixArray.size + 2 * raw.size + shardSuffixArray.size
  let init := appendByteArray (ByteArray.emptyWithCapacity cap) shardPrefixArray
  appendByteArray (pushHexArray init raw) shardSuffixArray

@[csimp]
theorem frameShardArray_eq_fast : @frameShardArray = @frameShardArrayFast := by
  funext raw
  cases h1 : frameShardArray raw with
  | mk d1 =>
    cases h2 : frameShardArrayFast raw with
    | mk d2 =>
      have hemp : (ByteArray.emptyWithCapacity (shardPrefixArray.size + 2 * raw.size + shardSuffixArray.size)).data.toList = [] := rfl
      have hl1 : d1.toList = frameShardBytes raw.data.toList := by
        rw [← frameShardArray_eq raw, h1]
      have hl2 : d2.toList = frameShardBytes raw.data.toList := by
        have : (frameShardArrayFast raw).data.toList = frameShardBytes raw.data.toList := by
          simp [frameShardArrayFast, frameShardBytes, appendByteArray_data, pushHexArray_eq,
            hemp, shardPrefixBytes, shardSuffixBytes, List.append_assoc]
        rwa [h2] at this
      congr 1
      exact Array.toList_inj.1 (hl1.trans hl2.symm)

def encodeShardPayload (p : ShardPayload) : Bytes :=
  frameShardBytes (cShardPayload.enc p)

def encodeShardPayloadArray (p : ShardPayload) : ByteArray :=
  frameShardArray (cShardPayload.encodeArray p)

theorem encodeShardPayloadArray_eq (p : ShardPayload) :
    (encodeShardPayloadArray p).data.toList = encodeShardPayload p := by
  rw [encodeShardPayloadArray, frameShardArray_eq, cShardPayload.encodeArray_eq, encodeShardPayload]

def decodeShardPayload (bs : Bytes) : Option ShardPayload :=
  (unframeShardBytes bs).bind cShardPayload.decodeExact

def sliceEqGo (b : ByteArray) (off : Nat) (pat : ByteArray) (i : Nat) : Bool :=
  if hp : i < pat.size then
    if hb : off + i < b.size then
      if b[off + i]'hb == pat[i]'hp then sliceEqGo b off pat (i + 1) else false
    else false
  else true
termination_by pat.size - i

def sliceEq (b : ByteArray) (off : Nat) (pat : ByteArray) : Bool :=
  off + pat.size ≤ b.size && sliceEqGo b off pat 0

theorem sliceEqGo_eq (b : ByteArray) (off : Nat) (pat : ByteArray)
    (hbnd : off + pat.size ≤ b.size) (i : Nat) :
    sliceEqGo b off pat i =
      ((b.data.toList.drop (off + i)).take (pat.size - i) == pat.data.toList.drop i) := by
  have hsb : b.data.toList.length = b.size := Array.length_toList
  have hsp : pat.data.toList.length = pat.size := Array.length_toList
  rw [sliceEqGo]
  by_cases hp : i < pat.size
  · have hb : off + i < b.size := by omega
    have hlb : off + i < b.data.toList.length := by omega
    have hlp : i < pat.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true hp), dite_eq_left_of_eq_true (eq_true hb)]
    obtain ⟨k, hk⟩ : ∃ k, pat.size - i = k + 1 := ⟨pat.size - i - 1, by omega⟩
    have hk' : pat.size - (i + 1) = k := by omega
    rw [hk, List.drop_eq_getElem_cons hlb, List.drop_eq_getElem_cons hlp, List.take_succ_cons]
    have gb : b.data.toList[off + i]'hlb = b[off + i]'hb := rfl
    have gp : pat.data.toList[i]'hlp = pat[i]'hp := rfl
    rw [gb, gp]
    by_cases heq : b[off + i]'hb = pat[i]'hp
    · have hbeq : (b[off + i]'hb == pat[i]'hp) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte]
      rw [sliceEqGo_eq b off pat hbnd (i + 1), hk']
      have hadd : off + (i + 1) = off + i + 1 := by omega
      rw [hadd, heq]
      cases htail : ((b.data.toList.drop (off + i + 1)).take k == pat.data.toList.drop (i + 1))
      · symm; apply beq_false_of_ne; intro hc; injection hc with _ ht
        exact absurd (beq_iff_eq.mpr ht) (by simp [htail])
      · symm; rw [beq_iff_eq]; congr 1; exact beq_iff_eq.mp htail
    · have hbeq : (b[off + i]'hb == pat[i]'hp) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      symm; apply beq_false_of_ne; intro hc; injection hc with hh _; exact heq hh
  · rw [dite_eq_right_of_eq_false (eq_false hp)]
    have h0 : pat.size - i = 0 := by omega
    rw [h0, List.take_zero, List.drop_eq_nil_of_le (by omega)]
    rfl
termination_by pat.size - i

def decodeShardPayloadArray (b : ByteArray) : Option ShardPayload :=
  let plen := shardPrefixArray.size
  let slen := shardSuffixArray.size
  if plen + slen ≤ b.size && sliceEq b 0 shardPrefixArray &&
      sliceEq b (b.size - slen) shardSuffixArray then
    (unhexSlice b plen (b.size - slen)).bind cShardPayload.decodeExactArray
  else none

theorem decodeShardPayload_encodeShardPayload (p : ShardPayload) :
    decodeShardPayload (encodeShardPayload p) = some p := by
  simp [decodeShardPayload, encodeShardPayload, unframeShardBytes_frameShardBytes,
    cShardPayload.decodeExact_enc]

theorem decodeShardPayloadArray_eq (b : ByteArray) :
    decodeShardPayloadArray b = decodeShardPayload b.data.toList := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  have hp : shardPrefixArray.data.toList = shardPrefixBytes := rfl
  have hsf : shardSuffixArray.data.toList = shardSuffixBytes := rfl
  have hps : shardPrefixArray.size = shardPrefixBytes.length := by
    rw [← hp, Array.length_toList]; rfl
  have hsfs : shardSuffixArray.size = shardSuffixBytes.length := by
    rw [← hsf, Array.length_toList]; rfl
  unfold decodeShardPayloadArray decodeShardPayload unframeShardBytes
  dsimp only
  by_cases hbnd : shardPrefixArray.size + shardSuffixArray.size ≤ b.size
  · have hbndL : shardPrefixBytes.length + shardSuffixBytes.length ≤ b.data.toList.length := by omega
    have hex0 : sliceEq b 0 shardPrefixArray =
        (b.data.toList.take shardPrefixBytes.length == shardPrefixBytes) := by
      have hp0 : 0 + shardPrefixArray.size ≤ b.size := by omega
      have hpL : 0 + shardPrefixBytes.length ≤ b.size := by omega
      simp only [sliceEq, sliceEqGo_eq b 0 shardPrefixArray hp0 0,
        Nat.add_zero, Nat.sub_zero, List.drop_zero, hps, hp, hpL, decide_true, Bool.true_and]
    have hex1 : sliceEq b (b.size - shardSuffixArray.size) shardSuffixArray =
        (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) == shardSuffixBytes) := by
      have hs0 : (b.size - shardSuffixArray.size) + shardSuffixArray.size ≤ b.size := by omega
      simp only [sliceEq, hs0, decide_true, Bool.true_and,
        sliceEqGo_eq b (b.size - shardSuffixArray.size) shardSuffixArray hs0 0,
        Nat.add_zero, Nat.sub_zero, List.drop_zero, hsf]
      have hd : b.size - shardSuffixArray.size = b.data.toList.length - shardSuffixBytes.length := by omega
      have htake : (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length)).take shardSuffixArray.size =
          b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) := by
        apply List.take_of_length_le; simp [hs, hsfs]; omega
      rw [hd, htake]
    simp only [hbnd, hbndL, decide_true, Bool.true_and, hex0, hex1]
    by_cases hc : ((b.data.toList.take shardPrefixBytes.length == shardPrefixBytes) &&
        (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) == shardSuffixBytes)) = true
    · simp only [hc, ↓reduceIte]
      unfold unhexSlice
      have hstop : b.size - shardSuffixArray.size ≤ b.size := Nat.sub_le _ _
      have hle2 : shardPrefixArray.size ≤ b.size - shardSuffixArray.size := by omega
      rw [dite_eq_left_of_eq_true (eq_true hstop)]
      by_cases hev : ((b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 == 0) = true
      · simp only [hle2, hev, decide_true, Bool.true_and, ↓reduceIte]
        have hev' : (b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 = 0 := by simpa using hev
        have hgo := unhexSliceGo_eq b (b.size - shardSuffixArray.size) hstop shardPrefixArray.size hle2 hev'
          (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2))
        have hemp : (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2)).data.toList = [] := rfl
        have hspan : b.size - shardSuffixArray.size - shardPrefixArray.size =
            b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length := by omega
        cases hu : unhexSliceGo b (b.size - shardSuffixArray.size) hstop shardPrefixArray.size
            (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2)) with
        | none =>
          rw [hu, hemp, hspan, hps] at hgo
          cases hu2 : hexAsciiToBytes? ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
          | none => rfl
          | some _ => rw [hu2] at hgo; simp at hgo
        | some arr =>
          rw [hu, hemp, hspan, hps] at hgo
          cases hu2 : hexAsciiToBytes? ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
          | none => rw [hu2] at hgo; simp at hgo
          | some raw =>
            rw [hu2] at hgo
            simp only [Option.map, List.nil_append, Option.some.injEq] at hgo
            simp [Option.bind, cShardPayload.decodeExactArray_eq, hgo]
      · simp only [hle2, hev, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        have hodd : ((b.data.toList.drop shardPrefixBytes.length).take
            (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)).length % 2 ≠ 0 := by
          have hlen : ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)).length =
              b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length := by
            rw [List.length_take, List.length_drop]; omega
          rw [hlen]
          intro h0
          have : ((b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 == 0) = true := by
            rw [beq_iff_eq]; omega
          exact absurd this (by simpa using hev)
        rw [hexAsciiToBytes?_of_odd _ hodd]
        rfl
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
  · have hbndS : ¬ (shardPrefixBytes.length + shardSuffixBytes.length ≤ b.size) := by omega
    simp [hbnd, hs, hbndS]

/-! ### Root Manifest JSON Framing & Merkle World Commitment -/

def pairsJsonCW (xs : List (String × String)) : Json :=
  Json.arr (xs.map fun (a, b) => Json.arr #[Json.str a, Json.str b]).toArray

def nonStoreMetaJson (m : NonStoreMeta) : Json :=
  let storeMeta := Json.mkObj ([("schema", Json.str schema), ("turn", toJson m.turn),
    ("members", Json.arr (m.members.map memberJson).toArray),
    ("environment", Json.arr (m.environment.map Json.str))] ++
    (if m.conflicts.isEmpty then [] else [("conflicts", Json.arr (m.conflicts.map conflictJson).toArray)]))
  Json.mkObj ([("storeMeta", storeMeta), ("journal", journalJson m.journal),
    ("forms", Json.arr (m.forms.map Form.formJson).toArray),
    ("receipts", Json.arr (m.receipts.map Form.receiptJson).toArray),
    ("received", pairsJsonCW m.received), ("sent", pairsJsonCW m.sent)] ++
    (if m.issues.isEmpty then [] else [("issues", Json.arr (m.issues.map Transport.issueJson).toArray)]) ++
    (if m.grants == {} then [] else [("grants", Transport.grantsJson m.grants)]) ++
    (if m.landed.isEmpty then [] else [("landed", Json.arr (m.landed.map Transport.landingJson).toArray)]) ++
    (if m.outstanding.isEmpty then [] else
      [("outstanding", Json.arr (m.outstanding.map Transport.obligationJson).toArray)]) ++
    (if m.minted == 0 then [] else [("minted", toJson m.minted)]) ++
    (if m.retention.isEmpty then [] else [("retention", Json.arr (m.retention.map Retention.contractJson).toArray)]) ++
    (if m.forks.isEmpty then [] else [("forks", Json.arr (m.forks.map Retention.forkJson).toArray)]) ++
    (if m.reasons == {} then [] else [("reasons", Obend.Reasons.stateJson m.reasons)]) ++
    (if m.checked.isEmpty then [] else [("checked", Json.arr (m.checked.map Form.checkedJson).toArray)]) ++
    (if m.forkMembers.isEmpty then [] else [("forkMembers", pairsJsonCW m.forkMembers)]))

/-- Canonical binary Merkle manifest of a world (`deployed.encW`):
`"OBWM0001"` (8-byte magic) ++ `cManifestCore.enc (meta, totalPages, totalTombs, bucketDigests)`
(`none` for empty buckets so sparse/small vaults emit zero empty shard files and minimal manifest
bytes, while `.obend/world/root.json` carries the human-readable RFC-8259 JSON root manifest). -/
abbrev ManifestCore := NonStoreMeta × Nat × Nat × List (Option String)

def cManifestCore : FastCodec ManifestCore :=
  cPair cNonStoreMeta (cPair cNat (cPair cNat (cList (cOption cString))))

def manifestPrefixArray : ByteArray := "OBWM0001".toUTF8
def manifestPrefixBytes : Bytes := manifestPrefixArray.data.toList

def frameManifest (core : ManifestCore) : Bytes :=
  manifestPrefixBytes ++ cManifestCore.enc core

def unframeManifest (bs : Bytes) : Option ManifestCore :=
  let plen := manifestPrefixBytes.length
  if plen ≤ bs.length && bs.take plen == manifestPrefixBytes then
    cManifestCore.decodeExact (bs.drop plen)
  else none

theorem unframeManifest_frameManifest (core : ManifestCore) :
    unframeManifest (frameManifest core) = some core := by
  unfold unframeManifest frameManifest
  let p := manifestPrefixBytes
  let m := cManifestCore.enc core
  have hle : p.length ≤ (p ++ m).length := by simp [List.length_append]
  have htake : (p ++ m).take p.length = p := take_append_exact p m
  have hdrop : (p ++ m).drop p.length = m := drop_append_exact p m
  have hcond : (decide (p.length ≤ (p ++ m).length) && ((p ++ m).take p.length == p)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hle, beq_iff_eq.mpr htake⟩
  change (if (decide (p.length ≤ (p ++ m).length) && ((p ++ m).take p.length == p)) = true then _ else _) = _
  dsimp only [p, m] at hdrop
  simp only [hcond, ↓reduceIte, hdrop, cManifestCore.decodeExact_enc]

/-! ## 6. Pure Merkleized Sharded World & Universal Round-Trip Theorem -/

/-- Canonical per-bucket content-addressed shard key `<2-hex-bucket>-<cshake256-hex>`.
Prefixing the bucket byte makes shard keys provably distinct across buckets without assuming
cryptographic collision-freedom, while remaining 100% content-addressed within each bucket. -/
def shardKey (b : Nat) (digest : String) : String :=
  byteToHex b.toUInt8 ++ "-" ++ digest

theorem hex_single_len (x : UInt8) : (byteToHex x).toList.length = 2 := by
  simpa using Obend.Codec.Hex.bytesToHexChars_length [x]

theorem shardKey_take2 (b : Nat) (d : String) :
    (shardKey b d).toList.take 2 = (byteToHex b.toUInt8).toList := by
  unfold shardKey
  have happ : (byteToHex b.toUInt8 ++ "-" ++ d).toList =
      (byteToHex b.toUInt8).toList ++ ("-" ++ d).toList := by
    rw [String.append_assoc, String.toList_append]
  rw [happ, ← hex_single_len b.toUInt8]
  exact take_append_exact _ _

theorem shardKey_bucket_inj {b1 b2 : Nat} {d1 d2 : String}
    (h1 : b1 < numBuckets) (h2 : b2 < numBuckets)
    (heq : shardKey b1 d1 = shardKey b2 d2) : b1 = b2 := by
  have ht : (shardKey b1 d1).toList.take 2 = (shardKey b2 d2).toList.take 2 := by rw [heq]
  rw [shardKey_take2, shardKey_take2] at ht
  have hu := congrArg hexCharsToBytes? ht
  rw [hexCharsToBytes?_bytesToHex, hexCharsToBytes?_bytesToHex] at hu
  injection hu with hlist
  injection hlist with hb
  have hnat := congrArg UInt8.toNat hb
  have hm1 : b1.toUInt8.toNat = b1 := by
    change b1 % 256 = b1
    exact Nat.mod_eq_of_lt (by unfold numBuckets at h1; omega)
  have hm2 : b2.toUInt8.toNat = b2 := by
    change b2 % 256 = b2
    exact Nat.mod_eq_of_lt (by unfold numBuckets at h2; omega)
  omega

/-- A world encoded as its root manifest plus its non-empty content-addressed JSON shards `(shardKey, bytes)`. -/
structure ShardedWorld where
  manifest : Bytes
  shards : List (String × Bytes)

def isEmptyShard (p : ShardPayload) : Bool :=
  p.1.isEmpty && p.2.isEmpty

theorem isEmptyShard_iff (p : ShardPayload) :
    isEmptyShard p = true ↔ p = ([], []) := by
  obtain ⟨a, b⟩ := p
  simp [isEmptyShard, List.isEmpty_iff]

def shardSpecOf (p : ShardPayload) : Option (String × Bytes) :=
  if isEmptyShard p then none
  else
    let sb := encodeShardPayload p
    some (bytesToHex (logHash sb), sb)

def shardForBucket (w : World) (b : Nat) : Option (String × Bytes) :=
  shardSpecOf (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))

/-- Canonical Merkle manifest bytes of `w` (`deployed.encW`). -/
def manifestBytes (w : World) : Bytes :=
  let shards := (List.range numBuckets).map (shardForBucket w)
  frameManifest (metaOf w, w.store.pages.length, w.store.tombs.length, shards.map (·.map (·.1)))

/-- Encode `w` into its root manifest and non-empty content-addressed shard JSON payloads. -/
def encodeShardedWorld (w : World) : ShardedWorld :=
  let raw := (List.range numBuckets).map fun b => (b, shardForBucket w b)
  { manifest := frameManifest (metaOf w, w.store.pages.length, w.store.tombs.length, raw.map (·.2.map (·.1)))
    shards := raw.filterMap fun (b, opt) => opt.map fun (d, sb) => (shardKey b d, sb) }

def enumDigestsGo : Nat → List (Option String) → List (Nat × Option String)
  | _, [] => []
  | b, d :: ds => (b, d) :: enumDigestsGo (b + 1) ds

theorem enumDigestsGo_map (f : Nat → Option String) :
    ∀ (k n : Nat), enumDigestsGo k ((List.range' k n).map f) = (List.range' k n).map fun b => (b, f b)
  | _, 0 => rfl
  | k, n + 1 => by simp [List.range'_succ, enumDigestsGo, enumDigestsGo_map f (k + 1) n]

theorem enumDigestsGo_zero_map (f : Nat → Option String) (n : Nat) :
    enumDigestsGo 0 ((List.range n).map f) = (List.range n).map fun b => (b, f b) := by
  rw [List.range_eq_range']
  exact enumDigestsGo_map f 0 n

def decodeAllBuckets (store : String → Option Bytes) :
    List (Nat × Option String) → Except String (List ShardPayload)
  | [] => .ok []
  | (_, none) :: rest =>
    match decodeAllBuckets store rest with
    | .error e => .error e
    | .ok ps => .ok (([], []) :: ps)
  | (b, some d) :: rest =>
    let k := shardKey b d
    match store k with
    | none => .error ("missing world shard " ++ k)
    | some sb =>
      if bytesToHex (logHash sb) != d then
        .error ("corrupt world shard " ++ k ++ ": digest mismatch")
      else match decodeShardPayload sb with
        | none => .error ("malformed world shard " ++ k)
        | some p =>
          match decodeAllBuckets store rest with
          | .error e => .error e
          | .ok ps => .ok (p :: ps)

/-- Decode a world from its manifest bytes against any shard store `store : String → Option Bytes`,
authenticating every non-empty shard's `cSHAKE256` digest before decoding it. -/
def decodeManifestWith (store : String → Option Bytes) (manifest : Bytes) : Except String World :=
  match unframeManifest manifest with
  | none => .error "invalid world manifest"
  | some (m, totalPages, totalTombs, digests) =>
    if digests.length != numBuckets then
      .error "unexpected bucket count in world manifest"
    else match decodeAllBuckets store (enumDigestsGo 0 digests) with
      | .error e => .error e
      | .ok payloads =>
        let arr := payloads.toArray
        match reassemble totalPages (fun b => ((arr[b]?).map (·.1)).getD []) with
        | none => .error "failed to reassemble world pages from shards"
        | some pages =>
          match reassemble totalTombs (fun b => ((arr[b]?).map (·.2)).getD []) with
          | none => .error "failed to reassemble world tombs from shards"
          | some tombs => .ok (withMeta pages tombs m)

def decodeShardedWorld (s : ShardedWorld) : Except String World :=
  decodeManifestWith (fun k => List.lookup k s.shards) s.manifest

theorem decodeAllBuckets_shards_ok (w : World) (store : String → Option Bytes)
    (hstore : ∀ b d sb, b < numBuckets →
      shardForBucket w b = some (d, sb) → store (shardKey b d) = some sb) :
    decodeAllBuckets store ((List.range numBuckets).map (fun b => (b, (shardForBucket w b).map (·.1)))) =
      Except.ok ((List.range numBuckets).map fun b =>
        (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))) := by
  have hgen : ∀ (bs : List Nat), (∀ b ∈ bs, b < numBuckets) →
      decodeAllBuckets store (bs.map (fun b => (b, (shardForBucket w b).map (·.1)))) =
        Except.ok (bs.map fun b =>
          (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))) := by
    intro bs hbs
    induction bs with
    | nil => rfl
    | cons b rest ih =>
      have hb : b < numBuckets := hbs b List.mem_cons_self
      have hrest : ∀ x ∈ rest, x < numBuckets := fun x hx => hbs x (List.mem_cons_of_mem _ hx)
      let pay : ShardPayload := (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))
      by_cases he : isEmptyShard pay = true
      · have hsf : shardForBucket w b = none := by simp [shardForBucket, shardSpecOf, pay, he]
        have hp0 : pay = ([], []) := (isEmptyShard_iff pay).mp he
        simp only [List.map_cons, hsf, Option.map_none, decodeAllBuckets, ih hrest]
        change Except.ok (([], []) :: _) = Except.ok (pay :: _)
        rw [hp0]
      · have hsf : shardForBucket w b =
            some (bytesToHex (logHash (encodeShardPayload pay)), encodeShardPayload pay) := by
          simp [shardForBucket, shardSpecOf, pay, he]
        have hst := hstore b _ _ hb hsf
        simp only [List.map_cons, hsf, Option.map_some, decodeAllBuckets, hst, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, decodeShardPayload_encodeShardPayload, ih hrest]
        rfl
  exact hgen (List.range numBuckets) (fun _ h => List.mem_range.mp h)

/-- **Authenticated Manifest Soundness**: for every `w : World` and every shard store holding `w`'s
shards, `decodeManifestWith store (manifestBytes w) = .ok w`. This directly discharges
`Log.checkpoint_is_cache` for sharded checkpoints. -/
theorem decodeManifestWith_manifestBytes (w : World) (store : String → Option Bytes)
    (hstore : ∀ k sb, (k, sb) ∈ (encodeShardedWorld w).shards → store k = some sb) :
    decodeManifestWith store (manifestBytes w) = .ok w := by
  have hs : ∀ b d sb, b < numBuckets →
      shardForBucket w b = some (d, sb) → store (shardKey b d) = some sb := by
    intro b d sb hb hsf
    apply hstore
    simp only [encodeShardedWorld, List.filterMap_map, List.mem_filterMap, List.mem_range]
    exact ⟨b, hb, by simp [hsf]⟩
  unfold decodeManifestWith manifestBytes
  have hcomp : List.map (Option.map Prod.fst) (List.map (shardForBucket w) (List.range numBuckets)) =
      List.map (fun b => (shardForBucket w b).map (·.1)) (List.range numBuckets) := by
    rw [List.map_map]; rfl
  rw [unframeManifest_frameManifest]
  dsimp only
  have hlenNe : (((List.map (shardForBucket w) (List.range numBuckets)).map (Option.map Prod.fst)).length != numBuckets) = false := by
    simp
  simp only [hlenNe, Bool.false_eq_true, ↓reduceIte]
  rw [hcomp, enumDigestsGo_zero_map (fun b => (shardForBucket w b).map (·.1)) numBuckets,
    decodeAllBuckets_shards_ok w store hs]
  dsimp only
  let payloads := (List.range numBuckets).map fun b =>
    (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))
  have hp1 : reassemble w.store.pages.length (fun b => ((payloads.toArray[b]?).map (·.1)).getD []) =
      some w.store.pages := by
    unfold reassemble
    rw [reassembleGo_congr 0 w.store.pages.length (g := fun b => bucketItems b (enumList w.store.pages))]
    · exact reassemble_bucketItems w.store.pages
    · intro b hb
      have hget : payloads.toArray[b]? = some (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs)) := by
        simp [payloads, hb]
      simp [hget]
  have hp2 : reassemble w.store.tombs.length (fun b => ((payloads.toArray[b]?).map (·.2)).getD []) =
      some w.store.tombs := by
    unfold reassemble
    rw [reassembleGo_congr 0 w.store.tombs.length (g := fun b => bucketItems b (enumList w.store.tombs))]
    · exact reassemble_bucketItems w.store.tombs
    · intro b hb
      have hget : payloads.toArray[b]? = some (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs)) := by
        simp [payloads, hb]
      simp [hget]
  change (match reassemble w.store.pages.length (fun b => ((payloads.toArray[b]?).map (·.1)).getD []) with
    | none => _ | some pages => _) = _
  rw [hp1]
  dsimp only
  rw [hp2]
  dsimp only
  rw [withMeta_metaOf w]

theorem lookup_filterMap_buckets (f : Nat → Option (String × Bytes)) :
    ∀ (bs : List Nat), bs.Nodup → (∀ b ∈ bs, b < numBuckets) →
      ∀ k sb, (k, sb) ∈ bs.filterMap (fun b => (f b).map (fun (d, s) => (shardKey b d, s))) →
        List.lookup k (bs.filterMap (fun b => (f b).map (fun (d, s) => (shardKey b d, s)))) = some sb
  | [], _, _, _, _, h => by cases h
  | b0 :: rest, hnd, hlt, k, sb, hmem => by
    simp only [List.nodup_cons] at hnd
    have hb0 : b0 < numBuckets := hlt b0 List.mem_cons_self
    have hrest : ∀ x ∈ rest, x < numBuckets := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    cases hf0 : f b0 with
    | none =>
      simp only [List.filterMap_cons, hf0, Option.map] at hmem ⊢
      exact lookup_filterMap_buckets f rest hnd.2 hrest k sb hmem
    | some p0 =>
      obtain ⟨d0, sb0⟩ := p0
      simp only [List.filterMap_cons, hf0, Option.map, List.mem_cons] at hmem ⊢
      rcases hmem with heq | hm
      · cases heq
        simp [List.lookup]
      · have hk : ¬ (k == shardKey b0 d0) = true := by
          intro heq
          simp only [beq_iff_eq] at heq
          simp only [List.mem_filterMap] at hm
          obtain ⟨b1, hb1, hp1⟩ := hm
          cases hf1 : f b1 with
          | none => simp [hf1] at hp1
          | some p1 =>
            obtain ⟨d1, sb1⟩ := p1
            simp only [hf1, Option.some.injEq, Prod.mk.injEq] at hp1
            have hbeq := shardKey_bucket_inj (hrest b1 hb1) hb0 (hp1.1.trans heq)
            exact hnd.1 (hbeq ▸ hb1)
        have hk' : (k == shardKey b0 d0) = false := Bool.eq_false_iff.mpr hk
        simp only [List.lookup, hk']
        exact lookup_filterMap_buckets f rest hnd.2 hrest k sb hm

/-- **Universal Sharded World Round-Trip**: for every `w : World`, encoding `w` into its root
manifest + `cSHAKE256`-authenticated shards and decoding recovers `w` exactly. -/
theorem decodeShardedWorld_encodeShardedWorld (w : World) :
    decodeShardedWorld (encodeShardedWorld w) = .ok w := by
  unfold decodeShardedWorld
  have hm : (encodeShardedWorld w).manifest = manifestBytes w := by
    simp [encodeShardedWorld, manifestBytes, List.map_map]; rfl
  rw [hm]
  apply decodeManifestWith_manifestBytes w
  intro k sb hmem
  have hsh : (encodeShardedWorld w).shards =
      (List.range numBuckets).filterMap (fun b => (shardForBucket w b).map (fun (d, s) => (shardKey b d, s))) := by
    simp [encodeShardedWorld, List.filterMap_map]; rfl
  rw [hsh] at hmem ⊢
  exact lookup_filterMap_buckets (shardForBucket w) (List.range numBuckets) List.nodup_range
    (fun _ h => List.mem_range.mp h) k sb hmem

/-- **Demand-Loading Metadata Soundness**: when `manifest` decodes to `w` against `store`, reading
`unframeManifest manifest` alone (0 shard reads) recovers every non-page/non-tomb field of `w`. -/
theorem metaOnly_sound (w : World) (store : String → Option Bytes) (manifest : Bytes)
    (hw : decodeManifestWith store manifest = .ok w) :
    (unframeManifest manifest).map (fun c => withMeta [] [] c.1) =
      some { w with store := { w.store with pages := [], tombs := [] } } := by
  unfold decodeManifestWith at hw
  cases hu : unframeManifest manifest with
  | none => rw [hu] at hw; cases hw
  | some core =>
    obtain ⟨m, nP, nT, ds⟩ := core
    rw [hu] at hw
    dsimp only at hw
    split at hw
    · cases hw
    · cases hm : decodeAllBuckets store (enumDigestsGo 0 ds) with
      | error _ => rw [hm] at hw; cases hw
      | ok payloads =>
        rw [hm] at hw
        dsimp only at hw
        cases hp : reassemble nP (fun b => ((payloads.toArray[b]?).map (·.1)).getD []) with
        | none => rw [hp] at hw; cases hw
        | some pages =>
          rw [hp] at hw
          dsimp only at hw
          cases ht : reassemble nT (fun b => ((payloads.toArray[b]?).map (·.2)).getD []) with
          | none => rw [ht] at hw; cases hw
          | some tombs =>
            rw [ht] at hw
            injection hw with hw'
            subst hw'
            rfl

/-! ## 7. Runtime Incremental Cache, Per-Bucket `DecodeCache`, Disk I/O & Demand-Loading -/

/-- Verified in-process cached bucket: retains payload and optional `(digest, bytes)` (`none` when
the bucket is empty), together with an erased proof matching `shardSpecOf payload`. -/
structure CachedBucket where
  payload : ShardPayload
  entry? : Option (String × ByteArray)
  entry_eq : entry?.map (fun (d, bs) => (d, bs.data.toList)) = shardSpecOf payload

/-- Reuse `prev?` in `O(1)` when `payload` did not change; skip encoding/hashing entirely when
`isEmptyShard p`; otherwise encode & hash linearly. -/
def buildCachedBucket (p : ShardPayload) (prev? : Option CachedBucket) : CachedBucket :=
  match prev? with
  | some cb =>
    if h : cb.payload = p then
      ⟨p, cb.entry?, h ▸ cb.entry_eq⟩
    else if he : isEmptyShard p = true then
      ⟨p, none, by simp [shardSpecOf, he]⟩
    else
      let bs := encodeShardPayloadArray p
      ⟨p, some (bytesToHex (logHashArray bs), bs), by
        simp [bs, shardSpecOf, he, encodeShardPayloadArray_eq, logHashArray_eq]⟩
  | none =>
    if he : isEmptyShard p = true then
      ⟨p, none, by simp [shardSpecOf, he]⟩
    else
      let bs := encodeShardPayloadArray p
      ⟨p, some (bytesToHex (logHashArray bs), bs), by
        simp [bs, shardSpecOf, he, encodeShardPayloadArray_eq, logHashArray_eq]⟩

theorem buildCachedBucket_payload (p : ShardPayload) (prev? : Option CachedBucket) :
    (buildCachedBucket p prev?).payload = p := by
  unfold buildCachedBucket
  cases prev? with
  | none => by_cases he : isEmptyShard p = true <;> simp [he]
  | some cb =>
    by_cases h : cb.payload = p
    · simp [h]
    · by_cases he : isEmptyShard p = true <;> simp [h, he]

/-- Linear `ByteArray` manifest framer, proved equal to `frameManifest`. -/
def frameManifestArray (core : ManifestCore) : ByteArray :=
  appendByteArray manifestPrefixArray (cManifestCore.encodeArray core)

theorem frameManifestArray_eq (core : ManifestCore) :
    (frameManifestArray core).data.toList = frameManifest core := by
  simp [frameManifestArray, frameManifest, appendByteArray_data,
    cManifestCore.encodeArray_eq, manifestPrefixBytes]

/-- Incrementally encode `w` into `(manifestArray, buckets)` by partitioning `w.store.pages` and
`w.store.tombs` in `O(N)` and re-encoding & hashing ONLY non-empty buckets whose `ShardPayload` changed. -/
def encodeWorldIncremental (w : World) (prev : Option (Array CachedBucket)) :
    ByteArray × Array CachedBucket :=
  let pB := partitionAll (enumList w.store.pages)
  let tB := partitionAll (enumList w.store.tombs)
  let bucketsList := (List.range numBuckets).map fun b =>
    let payload : ShardPayload := (pB[b]?.getD [], tB[b]?.getD [])
    buildCachedBucket payload (prev.bind (·[b]?))
  let digests := bucketsList.map fun cb => cb.entry?.map (·.1)
  let manifest := frameManifestArray (metaOf w, w.store.pages.length, w.store.tombs.length, digests)
  (manifest, bucketsList.toArray)

theorem cachedBucket_digest_eq (w : World) (prev : Option (Array CachedBucket)) (b : Nat)
    (hb : b < numBuckets) :
    let pB := partitionAll (enumList w.store.pages)
    let tB := partitionAll (enumList w.store.tombs)
    let cb := buildCachedBucket (pB[b]?.getD [], tB[b]?.getD []) (prev.bind (·[b]?))
    cb.entry?.map (·.1) = (shardForBucket w b).map (·.1) := by
  dsimp only
  have hp : (partitionAll (enumList w.store.pages))[b]?.getD [] = bucketItems b (enumList w.store.pages) := by
    rw [partitionAll_getElem _ b hb]; rfl
  have ht : (partitionAll (enumList w.store.tombs))[b]?.getD [] = bucketItems b (enumList w.store.tombs) := by
    rw [partitionAll_getElem _ b hb]; rfl
  let cb := buildCachedBucket ((partitionAll (enumList w.store.pages))[b]?.getD [],
      (partitionAll (enumList w.store.tombs))[b]?.getD []) (prev.bind (·[b]?))
  have hpay : cb.payload = (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs)) := by
    rw [buildCachedBucket_payload, hp, ht]
  have heq := congrArg (Option.map Prod.fst) cb.entry_eq
  rw [Option.map_map, hpay] at heq
  exact heq

/-- **Incremental Dirty-Bucket Soundness**: for every `w` and every `prev` cache state,
`encodeWorldIncremental w prev` produces the exact canonical `manifestBytes w`! -/
theorem encodeWorldIncremental_manifest_eq (w : World) (prev : Option (Array CachedBucket)) :
    (encodeWorldIncremental w prev).1.data.toList = manifestBytes w := by
  unfold encodeWorldIncremental manifestBytes
  rw [frameManifestArray_eq]
  congr 1; congr 1; congr 1; congr 1
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact cachedBucket_digest_eq w prev b (List.mem_range.mp hb)

/-- Per-bucket `DecodeCache` lookup over native `ByteArray` without `List UInt8` conversion. -/
def readBucketCached (cached : Option (DecodeCache.Entry decodeShardPayload)) (b : ByteArray) :
    DecodeCache.Entry decodeShardPayload :=
  letI : DecidableEq ByteArray := ByteArray.decEq
  match cached with
  | some e => if _ : e.bytes = b then e else ⟨b, decodeShardPayloadArray b, decodeShardPayloadArray_eq b⟩
  | none => ⟨b, decodeShardPayloadArray b, decodeShardPayloadArray_eq b⟩

theorem readBucketCached_bytes (cached : Option (DecodeCache.Entry decodeShardPayload)) (b : ByteArray) :
    (readBucketCached cached b).bytes = b := by
  unfold readBucketCached
  letI : DecidableEq ByteArray := ByteArray.decEq
  cases cached with
  | none => rfl
  | some e => by_cases h : e.bytes = b <;> simp [h]

theorem readBucketCached_eq (cached : Option (DecodeCache.Entry decodeShardPayload)) (b : ByteArray) :
    (readBucketCached cached b).result = decodeShardPayload b.data.toList := by
  have hc := (readBucketCached cached b).correct
  rw [readBucketCached_bytes] at hc
  exact hc

/-- Build an optional verified `DecodeCache.Entry` directly from a `CachedBucket` in `O(1)`. -/
def decodeEntryOfCached (cb : CachedBucket) : Option (DecodeCache.Entry decodeShardPayload) :=
  match h : cb.entry? with
  | none => none
  | some (_, bs) =>
    have heq := cb.entry_eq
    some ⟨bs, some cb.payload, by
      rw [h] at heq
      by_cases he : isEmptyShard cb.payload = true
      · simp [shardSpecOf, he] at heq
      · simp [shardSpecOf, he] at heq
        rw [heq.2, decodeShardPayload_encodeShardPayload]⟩

/-- Fast `ByteArray` unframer for `manifestBytes`. -/
def unframeManifestArray (b : ByteArray) : Option ManifestCore :=
  let plen := manifestPrefixArray.size
  if plen ≤ b.size && sliceEq b 0 manifestPrefixArray then
    cManifestCore.decodeExactArray (b.extract plen b.size)
  else none

/-! ### `.obend/world/` Disk Paths & `.obend/world/root.json` Framing -/

def worldDir (dir : System.FilePath) : System.FilePath := dir / ".obend" / "world"
def shardsDir (dir : System.FilePath) : System.FilePath := worldDir dir / "shards"
def rootPath (dir : System.FilePath) : System.FilePath := worldDir dir / "root.json"
def shardPath (dir : System.FilePath) (key : String) : System.FilePath := shardsDir dir / (key ++ ".json")

/-- Frame `.obend/world/root.json` as compact RFC-8259 JSON storing `logAnchor`, `rootDigest`
(`cSHAKE256` of `manifest`), `nonStoreMetaJson`, and `bucketDigests` (`""` for empty buckets). -/
def frameRootJson (anchor : Nat) (manifest : ByteArray) (m : NonStoreMeta)
    (digests : List (Option String)) : ByteArray :=
  let rootDigest := bytesToHex (logHashArray manifest)
  let dStr := ",".intercalate (digests.map fun d? => "\"" ++ d?.getD "" ++ "\"")
  ("{\"format\":\"obend-world-root-1\",\"logAnchor\":\"" ++ toString anchor ++
    "\",\"rootDigest\":\"" ++ rootDigest ++
    "\",\"nonStoreMetaJson\":" ++ (nonStoreMetaJson m).compress ++
    ",\"bucketDigests\":[" ++ dStr ++ "]}\n").toUTF8

/-! ### In-Process Bucket Caches & Atomic Sharded Checkpoint I/O -/

/-- Process-local cache of `(vaultKey, lastManifestBytes, Array CachedBucket)` for incremental
dirty-bucket encoding and zero-work checkpoint reuse, plus per-bucket `DecodeCache.Entry` table. -/
initialize worldBucketCacheRef : IO.Ref (List (String × ByteArray × Array CachedBucket)) ← IO.mkRef []
initialize worldDecodeCacheRef :
    IO.Ref (List (String × Array (Option (DecodeCache.Entry decodeShardPayload)))) ← IO.mkRef []

def canonKey (dir : System.FilePath) : IO String := do
  if ← dir.pathExists then return (← IO.FS.realPath dir).toString else return dir.toString

def getCachedEntry (dir : System.FilePath) : IO (Option (ByteArray × Array CachedBucket)) := do
  let k ← canonKey dir
  return ((← worldBucketCacheRef.get).find? (·.1 == k)).map (·.2)

def getCachedBuckets (dir : System.FilePath) : IO (Option (Array CachedBucket)) := do
  return (← getCachedEntry dir).map (·.2)

def setCachedBuckets (dir : System.FilePath) (mb : ByteArray) (arr : Array CachedBucket) : IO Unit := do
  let k ← canonKey dir
  worldBucketCacheRef.modify fun xs => (k, mb, arr) :: xs.filter (·.1 != k)
  let decArr := arr.map decodeEntryOfCached
  worldDecodeCacheRef.modify fun xs => (k, decArr) :: xs.filter (·.1 != k)

def getDecodeBuckets (dir : System.FilePath) :
    IO (Array (Option (DecodeCache.Entry decodeShardPayload))) := do
  let k ← canonKey dir
  return (((← worldDecodeCacheRef.get).find? (·.1 == k)).map (·.2)).getD (Array.replicate numBuckets none)

def setDecodeBuckets (dir : System.FilePath)
    (arr : Array (Option (DecodeCache.Entry decodeShardPayload))) : IO Unit := do
  let k ← canonKey dir
  worldDecodeCacheRef.modify fun xs => (k, arr) :: xs.filter (·.1 != k)

/-- Compute `(manifestArray, dig logHash manifestBytes)` incrementally using `dir`'s cached buckets,
and update the in-process bucket cache for `saveCheckpoint`. -/
def commitWorldManifest (dir : System.FilePath) (w : World) : IO (Bytes × Nat) := do
  let prev ← getCachedBuckets dir
  let (mb, buckets, c) ← Obend.Vault.Cost.compute fun _ =>
    let (mb, buckets) := encodeWorldIncremental w prev
    (mb, buckets, unbe (logHashArray mb))
  setCachedBuckets dir mb buckets
  return (mb.data.toList, c)


/-- Pure incremental manifest computation when no vault directory is needed (`committedAs`). -/
def manifestAndCommit (w : World) (prev : Option (Array CachedBucket) := none) :
    Bytes × Nat × Array CachedBucket :=
  let (mb, buckets) := encodeWorldIncremental w prev
  (mb.data.toList, unbe (logHashArray mb), buckets)

def writeFileAtomicArray (f : System.FilePath) (bs : ByteArray) : IO Unit := do
  if let some parent := f.parent then IO.FS.createDirAll parent
  let tmp := System.FilePath.mk (f.toString ++ ".tmp")
  Obend.Vault.Cost.writeBinFile tmp bs
  IO.FS.rename tmp f

/-- Atomically write ONLY missing/dirty non-empty shard files under `.obend/world/shards/<key>.json`,
then atomically publish `.obend/world/root.json`. Reuses `(mb, buckets)` in `O(1)` when
`commitWorldManifest` already encoded this turn's world (`ByteArray.decEq` hit on `knownMb?`).
Returns `(activeShardFiles, needPrune)`. -/
def writeShardedWorld (dir : System.FilePath) (anchor : Nat) (w : World)
    (knownMb? : Option ByteArray := none) : IO (Option (List String × Bool)) := do
  let cached? ← getCachedEntry dir
  let (mb, buckets, hadPrev) ← match cached?, knownMb? with
    | some (cmb, cbuckets), some kmb =>
      letI : DecidableEq ByteArray := ByteArray.decEq
      if cmb = kmb then pure (cmb, cbuckets, true)
      else do
        let (mb, buckets) ← Obend.Vault.Cost.compute fun _ => encodeWorldIncremental w (some cbuckets)
        setCachedBuckets dir mb buckets
        pure (mb, buckets, true)
    | prevEntry?, _ => do
      let (mb, buckets) ← Obend.Vault.Cost.compute fun _ =>
        encodeWorldIncremental w (prevEntry?.map (·.2))
      setCachedBuckets dir mb buckets
      pure (mb, buckets, prevEntry?.isSome)
  let mut active : List String := []
  let mut wroteAny := false
  let mut hasAnyNonEmpty := false
  for b in [0:numBuckets] do
    if let some cb := buckets[b]? then
      if let some (d, bs) := cb.entry? then
        hasAnyNonEmpty := true
        let key := shardKey b d
        active := (key ++ ".json") :: active
        let sf := shardPath dir key
        if !(← sf.pathExists) then
          IO.FS.createDirAll (shardsDir dir)
          writeFileAtomicArray sf bs
          wroteAny := true
  let digests := (List.range numBuckets).map fun b => (buckets[b]?.bind (·.entry?)).map (·.1)
  writeFileAtomicArray (rootPath dir) (frameRootJson anchor mb (metaOf w) digests)
  return some (active, wroteAny || !hadPrev || !hasAnyNonEmpty)

/-- Remove unreferenced shard `.json` files AFTER both `root.json` and `.obend/checkpoint` have been
atomically published, keeping steady-state shard count bounded to non-empty buckets (`≤ 128`). -/
def pruneObsoleteShards (dir : System.FilePath) (active : List String) : IO Unit := do
  let sd := shardsDir dir
  if !(← sd.isDir) then return
  let keep := Std.TreeSet.ofList active compare
  for e in ← sd.readDir do
    if e.fileName.endsWith ".json" && !keep.contains e.fileName then
      try IO.FS.removeFile e.path catch _ => pure ()

/-! ### Canonical Single-Pass Shard Reader (Zero Cold-Load Re-Serialization) & Bucketed Store Lookup -/

/-- Canonical reader for `raw : RawCodec α`: decodes directly from `ByteArray` in one pass while
certifying `bs = raw.enc a ++ rest`. -/
structure RawCanonReader {α : Type} (c : RawCodec α) where
  decC : Bytes → Option (α × Bytes)
  readC : ByteArray → Nat → Option (α × Nat)
  readC_eq : ∀ (b : ByteArray) (off : Nat),
    decC (b.data.toList.drop off) = (readC b off).map (fun p => (p.1, b.data.toList.drop p.2))
  sound : ∀ (bs : Bytes) (a : α) (rest : Bytes),
    decC bs = some (a, rest) → bs = c.enc a ++ rest

abbrev CanonReader {α : Type} (c : FastCodec α) := RawCanonReader c.toRawCodec

def RawCanonReader.decodeExact {α : Type} {c : RawCodec α} (cr : RawCanonReader c) (bs : Bytes) : Option α :=
  match cr.decC bs with
  | some (a, []) => some a
  | _ => none

def decodeExactCanonArray {α : Type} {c : RawCodec α} (cr : RawCanonReader c) (b : ByteArray) : Option α :=
  match cr.readC b 0 with
  | some (a, off) => if b.size ≤ off then some a else none
  | none => none

theorem RawCanonReader.decodeExact_sound {α : Type} {c : RawCodec α} (cr : RawCanonReader c)
    {bs : Bytes} {a : α} (h : cr.decodeExact bs = some a) : c.enc a = bs := by
  unfold RawCanonReader.decodeExact at h
  cases hd : cr.decC bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨x, rest⟩ := p
    rw [hd] at h
    cases rest with
    | nil =>
      injection h with hx
      subst hx
      simpa using (cr.sound bs x [] hd).symm
    | cons _ _ => cases h

theorem decodeExactCanonArray_eq {α : Type} {c : RawCodec α} (cr : RawCanonReader c) (b : ByteArray) :
    decodeExactCanonArray cr b = cr.decodeExact b.data.toList := by
  have hr := cr.readC_eq b 0
  simp only [List.drop_zero] at hr
  unfold decodeExactCanonArray RawCanonReader.decodeExact
  rw [hr]
  cases h : cr.readC b 0 with
  | none => rfl
  | some p =>
    obtain ⟨a, off⟩ := p
    dsimp only [Option.map]
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases ho : b.size ≤ off
    · have hnil : b.data.toList.drop off = [] := List.drop_eq_nil_of_le (by omega)
      simp [ho, hnil]
    · have hne : b.data.toList.drop off ≠ [] := by
        intro hn; rw [List.drop_eq_nil_iff] at hn; omega
      simp only [ho, ↓reduceIte]
      cases hd : b.data.toList.drop off with
      | nil => exact absurd hd hne
      | cons _ _ => rfl

def crFail {α : Type} : RawCanonReader (rawFail (α := α)) where
  decC _ := none
  readC _ _ := none
  readC_eq _ _ := rfl
  sound _ _ _ h := by cases h

def crUInt8 : CanonReader cUInt8 where
  decC := cUInt8.dec
  readC := cUInt8.readAt
  readC_eq := cUInt8.readAt_eq
  sound bs a rest h := by
    cases bs with
    | nil => cases h
    | cons x r =>
      dsimp only [cUInt8] at h ⊢
      injection h with hp
      injection hp with hx hr
      subst hx hr
      rfl

def crRawMapOf {α β : Type} (to : α → β) (of : β → Option α)
    (ofC : β → Option α) (hof : ∀ v a, ofC v = some a → to a = v)
    {c : RawCodec β} (cr : RawCanonReader c) : RawCanonReader (rawMap to of c) where
  decC bs := match cr.decC bs with
    | none => none
    | some (v, r) => (ofC v).map (·, r)
  readC b off := match cr.readC b off with
    | none => none
    | some (v, o) => (ofC v).map (·, o)
  readC_eq b off := by
    rw [cr.readC_eq b off]
    cases cr.readC b off with
    | none => rfl
    | some p => dsimp only [Option.map]; cases ofC p.1 <;> rfl
  sound bs a rest h := by
    cases hd : cr.decC bs with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨v, r⟩ := p
      simp only [hd, Option.map] at h
      cases ho : ofC v with
      | none => simp [ho] at h
      | some a' =>
        simp only [ho, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hv := hof v a' ho
        have hs := cr.sound bs v r hd
        simpa [rawMap, hv] using hs

def crMapInj {α β : Type} (to : α → β) (of : β → Option α) (of_to : ∀ a, of (to a) = some a)
    (h_inj : ∀ v a, of v = some a → to a = v) {c : FastCodec β} (cr : CanonReader c) :
    CanonReader (cMap to of of_to c) :=
  crRawMapOf to of of h_inj cr

def crMapCheck {α β : Type} [DecidableEq β] (to : α → β) (of : β → Option α)
    (of_to : ∀ a, of (to a) = some a) {c : FastCodec β} (cr : CanonReader c) :
    CanonReader (cMap to of of_to c) :=
  crRawMapOf to of
    (fun v => match of v with | some a => if to a = v then some a else none | none => none)
    (fun v a h => by
      cases ho : of v with
      | none => simp [ho] at h
      | some a' =>
        simp only [ho] at h
        by_cases heq : to a' = v
        · simp only [heq, ↓reduceIte, Option.some.injEq] at h
          subst h; exact heq
        · simp [heq] at h)
    cr

def crRawPair {α β : Type} {c1 : RawCodec α} {c2 : RawCodec β}
    (cr1 : RawCanonReader c1) (cr2 : RawCanonReader c2) : RawCanonReader (rawPair c1 c2) where
  decC bs := match cr1.decC bs with
    | none => none
    | some (x, r1) => match cr2.decC r1 with
      | none => none
      | some (y, r2) => some ((x, y), r2)
  readC b off := match cr1.readC b off with
    | none => none
    | some (x, o1) => match cr2.readC b o1 with
      | none => none
      | some (y, o2) => some ((x, y), o2)
  readC_eq b off := by
    rw [cr1.readC_eq b off]
    cases cr1.readC b off with
    | none => rfl
    | some p1 =>
      dsimp only [Option.map]
      rw [cr2.readC_eq b p1.2]
      cases cr2.readC b p1.2 <;> rfl
  sound bs p rest h := by
    cases h1 : cr1.decC bs with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨x, r1⟩ := p1
      simp only [h1] at h
      cases h2 : cr2.decC r1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨y, r2⟩ := p2
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [cr1.sound bs x r1 h1, cr2.sound r1 y r2 h2]
        simp [rawPair, List.append_assoc]

def crPair {α β : Type} {c1 : FastCodec α} {c2 : FastCodec β}
    (cr1 : CanonReader c1) (cr2 : CanonReader c2) : CanonReader (cPair c1 c2) :=
  crRawPair cr1 cr2

def crRawOption {α : Type} {c : RawCodec α} (cr : RawCanonReader c) : RawCanonReader (rawOption c) where
  decC
    | 0 :: rest => some (none, rest)
    | 1 :: rest => match cr.decC rest with
      | none => none
      | some (x, r) => some (some x, r)
    | _ => none
  readC b off :=
    if h : off < b.size then
      if b[off]'h == 0 then some (none, off + 1)
      else if b[off]'h == 1 then
        match cr.readC b (off + 1) with
        | none => none
        | some (x, o) => some (some x, o)
      else none
    else none
  readC_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases h : off < b.size
    · have hl : off < b.data.toList.length := by omega
      rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
      have hg : b.data.toList[off]'hl = b[off]'h := rfl
      rw [hg]
      generalize b[off]'h = tag
      by_cases h0 : tag = 0
      · subst h0; rfl
      · have hb0 : (tag == 0) = false := beq_false_of_ne h0
        by_cases h1 : tag = 1
        · subst h1
          have h10 : ((1 : UInt8) == 0) = false := rfl
          have h11 : ((1 : UInt8) == 1) = true := rfl
          simp only [h10, h11, Bool.false_eq_true, ite_false, ite_true, cr.readC_eq b (off + 1)]
          cases cr.readC b (off + 1) <;> rfl
        · have hb1 : (tag == 1) = false := beq_false_of_ne h1
          simp only [hb0, hb1, Bool.false_eq_true, ite_false, Option.map]
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, _⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | _ + 2, _, _ => rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
      rfl
  sound bs opt rest h := by
    cases bs with
    | nil => cases h
    | cons tag tail =>
      by_cases h0 : tag = 0
      · subst h0
        injection h with hp
        injection hp with ha hr
        subst ha hr; rfl
      · by_cases h1 : tag = 1
        · subst h1
          change (match cr.decC tail with | none => none | some (x, r) => some (some x, r)) = some (opt, rest) at h
          cases hx : cr.decC tail with
          | none => rw [hx] at h; cases h
          | some p =>
            obtain ⟨x, r⟩ := p
            rw [hx] at h
            injection h with hp
            injection hp with ha hr
            subst ha hr
            rw [cr.sound tail x r hx]
            rfl
        · exfalso
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, _⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | _ + 2, _, _ => cases h

def crOption {α : Type} {c : FastCodec α} (cr : CanonReader c) : CanonReader (cOption c) :=
  crRawOption cr

def crRawSum {α β : Type} {c1 : RawCodec α} {c2 : RawCodec β}
    (cr1 : RawCanonReader c1) (cr2 : RawCanonReader c2) : RawCanonReader (rawSum c1 c2) where
  decC
    | 0 :: rest => match cr1.decC rest with
      | none => none
      | some (x, r) => some (.inl x, r)
    | 1 :: rest => match cr2.decC rest with
      | none => none
      | some (y, r) => some (.inr y, r)
    | _ => none
  readC b off :=
    if h : off < b.size then
      if b[off]'h == 0 then
        match cr1.readC b (off + 1) with
        | none => none
        | some (x, o) => some (.inl x, o)
      else if b[off]'h == 1 then
        match cr2.readC b (off + 1) with
        | none => none
        | some (y, o) => some (.inr y, o)
      else none
    else none
  readC_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    by_cases h : off < b.size
    · have hl : off < b.data.toList.length := by omega
      rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
      have hg : b.data.toList[off]'hl = b[off]'h := rfl
      rw [hg]
      generalize b[off]'h = tag
      by_cases h0 : tag = 0
      · subst h0
        have h00 : ((0 : UInt8) == 0) = true := rfl
        simp only [h00, ite_true, cr1.readC_eq b (off + 1)]
        cases cr1.readC b (off + 1) <;> rfl
      · have hb0 : (tag == 0) = false := beq_false_of_ne h0
        by_cases h1 : tag = 1
        · subst h1
          have h10 : ((1 : UInt8) == 0) = false := rfl
          have h11 : ((1 : UInt8) == 1) = true := rfl
          simp only [h10, h11, Bool.false_eq_true, ite_false, ite_true, cr2.readC_eq b (off + 1)]
          cases cr2.readC b (off + 1) <;> rfl
        · have hb1 : (tag == 1) = false := beq_false_of_ne h1
          simp only [hb0, hb1, Bool.false_eq_true, ite_false, Option.map]
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, _⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | _ + 2, _, _ => rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
      rfl
  sound bs s rest h := by
    cases bs with
    | nil => cases h
    | cons tag tail =>
      by_cases h0 : tag = 0
      · subst h0
        change (match cr1.decC tail with | none => none | some (x, r) => some (Sum.inl x, r)) = some (s, rest) at h
        cases hx : cr1.decC tail with
        | none => rw [hx] at h; cases h
        | some p =>
          obtain ⟨x, r⟩ := p
          rw [hx] at h
          injection h with hp
          injection hp with ha hr
          subst ha hr
          rw [cr1.sound tail x r hx]; rfl
      · by_cases h1 : tag = 1
        · subst h1
          change (match cr2.decC tail with | none => none | some (y, r) => some (Sum.inr y, r)) = some (s, rest) at h
          cases hy : cr2.decC tail with
          | none => rw [hy] at h; cases h
          | some p =>
            obtain ⟨y, r⟩ := p
            rw [hy] at h
            injection h with hp
            injection hp with ha hr
            subst ha hr
            rw [cr2.sound tail y r hy]; rfl
        · exfalso
          cases tag with
          | ofBitVec bv =>
            rcases bv with ⟨v, _⟩
            have hv0 : v ≠ 0 := fun e => h0 (by subst e; rfl)
            have hv1 : v ≠ 1 := fun e => h1 (by subst e; rfl)
            match v, hv0, hv1 with
            | _ + 2, _, _ => cases h

def crSum {α β : Type} {c1 : FastCodec α} {c2 : FastCodec β}
    (cr1 : CanonReader c1) (cr2 : CanonReader c2) : CanonReader (cSum c1 c2) :=
  crRawSum cr1 cr2

def crBool : CanonReader cBool := crMapCheck _ _ _ crUInt8

def decNatCanon : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else match decNatCanon rest with
      | none => none
      | some (hi, r) => if hi == 0 then none else some ((b.toNat - 128) + 128 * hi, r)

def readNatCanonAt (b : ByteArray) (off : Nat) : Option (Nat × Nat) :=
  if h : off < b.size then
    let x := b[off]'h
    if x.toNat < 128 then some (x.toNat, off + 1)
    else match readNatCanonAt b (off + 1) with
      | none => none
      | some (hi, o) => if hi == 0 then none else some ((x.toNat - 128) + 128 * hi, o)
  else none
termination_by b.size - off

theorem readNatCanonAt_eq (b : ByteArray) (off : Nat) :
    decNatCanon (b.data.toList.drop off) =
      (readNatCanonAt b off).map (fun p => (p.1, b.data.toList.drop p.2)) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [readNatCanonAt]
  by_cases h : off < b.size
  · have hl : off < b.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), List.drop_eq_getElem_cons hl]
    have hg : b.data.toList[off]'hl = b[off]'h := rfl
    rw [hg]
    dsimp only [decNatCanon]
    by_cases hx : (b[off]'h).toNat < 128
    · simp only [hx, ↓reduceIte, Option.map]
    · simp only [hx, ↓reduceIte, readNatCanonAt_eq b (off + 1)]
      cases readNatCanonAt b (off + 1) with
      | none => rfl
      | some p =>
        dsimp only [Option.map]
        cases p.1 == 0 <;> rfl
  · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]; rfl
termination_by b.size - off

theorem readNatCanonAt_le (b : ByteArray) (off n o : Nat) (h : readNatCanonAt b off = some (n, o)) :
    o ≤ b.size := by
  rw [readNatCanonAt] at h
  by_cases hb : off < b.size
  · rw [dite_eq_left_of_eq_true (eq_true hb)] at h
    dsimp only at h
    by_cases hx : (b[off]'hb).toNat < 128
    · simp only [hx, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      omega
    · simp only [hx, ↓reduceIte] at h
      cases hr : readNatCanonAt b (off + 1) with
      | none => simp [hr] at h
      | some p =>
        rw [hr] at h
        have ih := readNatCanonAt_le b (off + 1) p.1 p.2 hr
        by_cases hp0 : (p.1 == 0) = true
        · simp [hp0] at h
        · simp only [hp0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          omega
  · rw [dite_eq_right_of_eq_false (eq_false hb)] at h
    cases h
termination_by b.size - off

theorem decNatCanon_sound : ∀ (bs : Bytes) (n : Nat) (rest : Bytes),
    decNatCanon bs = some (n, rest) → bs = encNat n ++ rest
  | [], _, _, h => by cases h
  | x :: tail, n, rest, h => by
    unfold decNatCanon at h
    have hxlt : x.toNat < 256 := x.toNat_lt
    by_cases hx : x.toNat < 128
    · simp only [hx, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hn, hr⟩ := h
      subst hn hr
      rw [encNat]
      simp only [hx, ↓reduceIte, List.singleton_append]
      have hu : x.toNat.toUInt8 = x := UInt8.toNat_inj.1 (u8_toNat_lt x.toNat hxlt)
      rw [hu]
    · simp only [hx, ↓reduceIte] at h
      cases ht : decNatCanon tail with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨hi, r⟩ := p
        rw [ht] at h
        by_cases h0 : (hi == 0) = true
        · simp [h0] at h
        · simp only [h0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hn, hr⟩ := h
          subst hn hr
          have hhi : hi ≠ 0 := fun e => h0 (beq_iff_eq.mpr e)
          have hge : ¬ ((x.toNat - 128) + 128 * hi < 128) := by omega
          have hmod : 128 + ((x.toNat - 128) + 128 * hi) % 128 = x.toNat := by omega
          have hdiv : ((x.toNat - 128) + 128 * hi) / 128 = hi := by omega
          have hu : x.toNat.toUInt8 = x := UInt8.toNat_inj.1 (u8_toNat_lt x.toNat hxlt)
          rw [encNat]
          simp only [hge, ↓reduceIte, hmod, hu, hdiv, List.cons_append]
          rw [decNatCanon_sound tail hi r ht]

def crNat : CanonReader cNat where
  decC := decNatCanon
  readC := readNatCanonAt
  readC_eq := readNatCanonAt_eq
  sound := decNatCanon_sound

theorem readListN_canon_eq {α : Type} {c : RawCodec α} (cr : RawCanonReader c) :
    ∀ (n : Nat) (b : ByteArray) (off : Nat) (acc : Array α),
      (decListN cr.decC n (b.data.toList.drop off)).map (fun p => (acc.toList ++ p.1, p.2)) =
        (readListN cr.readC n b off acc).map (fun p => (p.1, b.data.toList.drop p.2))
  | 0, b, off, acc => by simp [decListN, readListN]
  | n + 1, b, off, acc => by
    simp only [decListN, readListN, cr.readC_eq b off]
    cases cr.readC b off with
    | none => rfl
    | some p1 =>
      have ih := readListN_canon_eq cr n b p1.2 (acc.push p1.1)
      cases hd : decListN cr.decC n (b.data.toList.drop p1.2) <;>
        cases hr : readListN cr.readC n b p1.2 (acc.push p1.1) <;>
        simp [hd, hr, Option.map, Array.toList_push, List.append_assoc] at ih ⊢ <;>
        exact ih

theorem decListN_canon_sound {α : Type} {c : RawCodec α} (cr : RawCanonReader c) :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes),
      decListN cr.decC n bs = some (xs, rest) → xs.length = n ∧ bs = xs.flatMap c.enc ++ rest
  | 0, bs, xs, rest, h => by
    simp only [decListN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, bs, xs, rest, h => by
    unfold decListN at h
    cases h1 : cr.decC bs with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨x, r1⟩ := p1
      rw [h1] at h
      dsimp only at h
      cases h2 : decListN cr.decC n r1 with
      | none => rw [h2] at h; cases h
      | some p2 =>
        obtain ⟨ys, r2⟩ := p2
        rw [h2] at h
        injection h with hp
        injection hp with hxs hrest
        subst hxs hrest
        obtain ⟨hlen, hr1⟩ := decListN_canon_sound cr n r1 ys r2 h2
        exact ⟨by simp [hlen], by rw [cr.sound bs x r1 h1, hr1]; simp [List.append_assoc]⟩

def crRawList {α : Type} {c : RawCodec α} (cr : RawCanonReader c) : RawCanonReader (rawList c) where
  decC bs := match decNatCanon bs with
    | none => none
    | some (n, r) => decListN cr.decC n r
  readC b off := match readNatCanonAt b off with
    | none => none
    | some (n, o) => readListN cr.readC n b o #[]
  readC_eq b off := by
    rw [readNatCanonAt_eq b off]
    cases readNatCanonAt b off with
    | none => rfl
    | some p =>
      have hl := readListN_canon_eq cr p.1 b p.2 #[]
      cases hd : decListN cr.decC p.1 (b.data.toList.drop p.2) with
      | none =>
        cases hr : readListN cr.readC p.1 b p.2 #[] with
        | none => simp [hd, hr, Option.map]
        | some q => simp [hd, hr, Option.map] at hl
      | some p2 =>
        obtain ⟨xs, r⟩ := p2
        cases hr : readListN cr.readC p.1 b p.2 #[] with
        | none => simp [hd, hr, Option.map] at hl
        | some q =>
          obtain ⟨ys, o2⟩ := q
          simp [hd, hr, Option.map] at hl ⊢
          exact hl
  sound bs xs rest h := by
    cases hn : decNatCanon bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only [hn] at h
      obtain ⟨hlen, hr⟩ := decListN_canon_sound cr n r xs rest h
      rw [decNatCanon_sound bs n r hn, hr, ← hlen]
      simp [rawList, List.append_assoc]

def crList {α : Type} {c : FastCodec α} (cr : CanonReader c) : CanonReader (cList c) :=
  crRawList cr

def crBytes : CanonReader cBytes where
  decC bs := match decNatCanon bs with
    | none => none
    | some (n, r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  readC b off := match readNatCanonAt b off with
    | none => none
    | some (n, o) => if o + n ≤ b.size then some (readBytesLoop b o (o + n) #[], o + n) else none
  readC_eq b off := by
    have hs : b.data.toList.length = b.size := Array.length_toList
    rw [readNatCanonAt_eq b off]
    cases hr : readNatCanonAt b off with
    | none => rfl
    | some p =>
      obtain ⟨n, o⟩ := p
      dsimp only [Option.map]
      have ho : o ≤ b.size := readNatCanonAt_le b off n o hr
      by_cases h : o + n ≤ b.size
      · have hle : n ≤ (b.data.toList.drop o).length := by simp [hs]; omega
        simp only [hle, h, ↓reduceIte]
        rw [readBytesLoop_eq b o (o + n) #[] h]
        have hn : o + n - o = n := by omega
        rw [hn, List.drop_drop]
        simp
      · have hgt : ¬ (n ≤ (b.data.toList.drop o).length) := by simp [hs]; omega
        simp only [hgt, h, ↓reduceIte]
  sound bs xs rest h := by
    cases hn : decNatCanon bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only [hn] at h
      by_cases hle : n ≤ r.length
      · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen : (r.take n).length = n := List.length_take_of_le hle
        rw [decNatCanon_sound bs n r hn]
        simp [cBytes, hlen, List.append_assoc, List.take_append_drop]
      · simp [hle] at h

def crByteArray : CanonReader cByteArray :=
  let cr := crMapInj (fun (b : ByteArray) => b.data.toList) (fun (xs : Bytes) => some (⟨xs.toArray⟩ : ByteArray))
    (by intro b; cases b; simp)
    (by intro xs b h; injection h with hb; subst hb; simp)
    crBytes
  ⟨cr.decC, cr.readC, cr.readC_eq, cr.sound⟩

def crChar : CanonReader cChar := crMapCheck _ _ _ crNat

def crString : CanonReader cString :=
  crMapInj String.toList (fun cs => some (String.ofList cs))
    (fun _ => congrArg some String.ofList_toList)
    (by intro cs s h; injection h with hs; subst hs; exact String.toList_ofList)
    (crList crChar)

abbrev DataSumTy := (Nat ⊕ (Bool ⊕ String)) ⊕ (List (String × Data) ⊕ (String × Data))

def dataCanonStep {k : Nat} (r : RawCanonReader (iterRaw dataStep k)) :
    RawCanonReader (dataStep (iterRaw dataStep k)) :=
  crRawMapOf (α := Data) (β := DataSumTy)
    (fun
      | .natural n => .inl (.inl n)
      | .boolean b => .inl (.inr (.inl b))
      | .label s => .inl (.inr (.inr s))
      | .record fs => .inr (.inl fs)
      | .variant l p => .inr (.inr (l, p)))
    (fun
      | .inl (.inl n) => some (.natural n)
      | .inl (.inr (.inl b)) => some (.boolean b)
      | .inl (.inr (.inr s)) => some (.label s)
      | .inr (.inl fs) => some (.record fs)
      | .inr (.inr (l, p)) => some (.variant l p))
    (fun
      | .inl (.inl n) => some (.natural n)
      | .inl (.inr (.inl b)) => some (.boolean b)
      | .inl (.inr (.inr s)) => some (.label s)
      | .inr (.inl fs) => some (.record fs)
      | .inr (.inr (l, p)) => some (.variant l p))
    (by
      intro v a h
      rcases v with (n | (b | s)) | (fs | ⟨l, p⟩) <;>
        (dsimp only at h; injection h with ha; subst ha; rfl))
    (crRawSum (crRawSum crNat (crRawSum crBool crString))
      (crRawSum (crRawList (crRawPair crString r)) (crRawPair crString r)))

def iterDataCanon : (k : Nat) → RawCanonReader (iterRaw dataStep k)
  | 0 => crFail
  | k + 1 => dataCanonStep (iterDataCanon k)

def crData : CanonReader cData where
  decC bs := match crNat.decC bs with
    | none => none
    | some (k, r) => match (iterDataCanon k).decC r with
      | none => none
      | some (d, rest) => if dataDepth d == k then some (d, rest) else none
  readC b off := match crNat.readC b off with
    | none => none
    | some (k, o) => match (iterDataCanon k).readC b o with
      | none => none
      | some (d, o2) => if dataDepth d == k then some (d, o2) else none
  readC_eq b off := by
    rw [crNat.readC_eq b off]
    cases crNat.readC b off with
    | none => rfl
    | some p =>
      dsimp only [Option.map]
      rw [(iterDataCanon p.1).readC_eq b p.2]
      cases (iterDataCanon p.1).readC b p.2 with
      | none => rfl
      | some p2 =>
        dsimp only [Option.map]
        cases dataDepth p2.1 == p.1 <;> rfl
  sound bs d rest h := by
    cases hk : crNat.decC bs with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨k, r⟩ := p
      simp only [hk] at h
      cases hd : (iterDataCanon k).decC r with
      | none => simp [hd] at h
      | some p2 =>
        obtain ⟨d', rest'⟩ := p2
        simp only [hd] at h
        by_cases heq : (dataDepth d' == k) = true
        · simp only [heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hdk : dataDepth d' = k := beq_iff_eq.mp heq
          rw [crNat.sound bs k r hk, (iterDataCanon k).sound r d' rest' hd, ← hdk]
          simp [cData, cRec, List.append_assoc]
        · simp [heq] at h

def crMode : CanonReader cMode :=
  crMapInj _ _ (by intro m; cases m <;> rfl)
    (by intro b m h; cases b <;> (injection h with hm; subst hm; rfl)) crBool
def crRange : CanonReader cRange :=
  crMapInj _ _ (by intro r; cases r; rfl)
    (by intro p r h; obtain ⟨s, l⟩ := p; injection h with hr; subst hr; rfl) (crPair crNat crNat)
def crSpan : CanonReader cSpan :=
  crMapInj _ _ (by intro s; cases s <;> rfl)
    (by intro v s h; rcases v with (b | (id | r))
        · cases b <;> (injection h with hs; subst hs; rfl)
        · injection h with hs; subst hs; rfl
        · injection h with hs; subst hs; rfl)
    (crSum crBool (crSum crString crRange))
def crCite : CanonReader cCite :=
  crMapInj _ _ (by intro c; cases c; rfl)
    (by intro v c h; obtain ⟨p, sp, ver, cm, m⟩ := v; injection h with hc; subst hc; rfl)
    (crPair crNat (crPair crSpan (crPair crNat (crPair crBytes crMode))))
def crProjectionKind : CanonReader cProjectionKind := crMapCheck _ _ _ crString
def crContent : CanonReader cContent :=
  crMapInj _ _ (by intro c; cases c <;> rfl)
    (by intro v c h; rcases v with (s | ⟨n, ct⟩) | (⟨n, val⟩ | ⟨id, k, ast, pins, rc⟩) <;>
        (injection h with hc; subst hc; rfl))
    (crSum (crSum crString (crPair crString crCite))
      (crSum (crPair crString crString)
        (crPair crString (crPair crProjectionKind (crPair crData
          (crPair (crList (crPair crString crByteArray)) (crOption crByteArray)))))))
def crGraph : CanonReader cGraph :=
  crMapInj _ _ (by intro G; cases G; rfl)
    (by intro v G h; obtain ⟨a, d, e⟩ := v; injection h with hG; subst hG; rfl)
    (crPair (crList (crPair crNat crContent)) (crPair (crList crNat) (crList (crPair crNat crNat))))

theorem isPrefixDec_append_self {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), isPrefixDec xs (xs ++ ys) = true
  | [], _ => rfl
  | _ :: xs, ys => by simp [isPrefixDec, isPrefixDec_append_self xs ys]

def decodeHistoryStepsCanon.go (prev : Graph) : List (Bool × Graph) → Option (List Graph)
  | [] => some []
  | (false, G) :: rest =>
    if isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead && isPrefixDec prev.edges G.edges then
      none
    else
      (decodeHistoryStepsCanon.go G rest).map (G :: ·)
  | (true, d) :: rest =>
    let G : Graph := ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩
    (decodeHistoryStepsCanon.go G rest).map (G :: ·)

def decodeHistoryStepsCanon : List (Bool × Graph) → Option (List Graph)
  | [] => some []
  | (true, _) :: _ => none
  | (false, G) :: rest => (decodeHistoryStepsCanon.go G rest).map (G :: ·)

theorem decodeHistoryStepsCanon_go_sound :
    ∀ (prev : Graph) (steps : List (Bool × Graph)) (gs : List Graph),
      decodeHistoryStepsCanon.go prev steps = some gs → encodeHistorySteps.go prev gs = steps
  | _, [], gs, h => by
    injection h with hgs; subst hgs; rfl
  | prev, (false, G) :: rest, gs, h => by
    unfold decodeHistoryStepsCanon.go at h
    by_cases hp : (isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead && isPrefixDec prev.edges G.edges) = true
    · simp [hp] at h
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : decodeHistoryStepsCanon.go G rest with
      | none => simp [hr] at h
      | some gs' =>
        simp only [hr, Option.map, Option.some.injEq] at h
        subst h
        simp [encodeHistorySteps.go, hp, decodeHistoryStepsCanon_go_sound G rest gs' hr]
  | prev, (true, d) :: rest, gs, h => by
    unfold decodeHistoryStepsCanon.go at h
    dsimp only at h
    cases hr : decodeHistoryStepsCanon.go ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩ rest with
    | none => rw [hr] at h; cases h
    | some gs' =>
      rw [hr] at h
      dsimp only [Option.map] at h
      injection h with hgs
      subst hgs
      let G : Graph := ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩
      have hp : (isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead && isPrefixDec prev.edges G.edges) = true := by
        simp [G, isPrefixDec_append_self]
      cases d
      simp [encodeHistorySteps.go, G, hp, decodeHistoryStepsCanon_go_sound G rest gs' hr]

theorem decodeHistoryStepsCanon_sound (steps : List (Bool × Graph)) (gs : List Graph)
    (h : decodeHistoryStepsCanon steps = some gs) : encodeHistorySteps gs = steps := by
  cases steps with
  | nil => injection h with hgs; subst hgs; rfl
  | cons hd rest =>
    obtain ⟨b, G⟩ := hd
    cases b with
    | true => cases h
    | false =>
      unfold decodeHistoryStepsCanon at h
      cases hr : decodeHistoryStepsCanon.go G rest with
      | none => simp [hr] at h
      | some gs' =>
        simp only [hr, Option.map, Option.some.injEq] at h
        subst h
        simp [encodeHistorySteps, decodeHistoryStepsCanon_go_sound G rest gs' hr]

example : decodeHistoryStepsCanon [(false, ⟨[(0, .text "ok")], [], []⟩)] =
    some [⟨[(0, .text "ok")], [], []⟩] := rfl
def crHistory : CanonReader cHistory :=
  crRawMapOf encodeHistorySteps decodeHistorySteps decodeHistoryStepsCanon
    decodeHistoryStepsCanon_sound (crList (crPair crBool crGraph))
def crKindVersion : CanonReader cKindVersion :=
  crMapInj _ _ (by intro v; cases v; rfl)
    (by intro p v h; obtain ⟨n, ver⟩ := p; injection h with hv; subst hv; rfl) (crPair crString crNat)
def crKindPin : CanonReader cKindPin :=
  crMapInj _ _ (by intro p; cases p; rfl)
    (by intro t p h; obtain ⟨n, v, a⟩ := t; injection h with hp; subst hp; rfl)
    (crPair crString (crPair crNat (crList crKindVersion)))
def crPage : CanonReader cPage :=
  crMapInj _ _ (by intro p; cases p; rfl)
    (by intro t p h; obtain ⟨n, id, hs, s, au, no, k⟩ := t; injection h with hp; subst hp; rfl)
    (crPair crString (crPair crNat (crPair crHistory (crPair (crOption crString)
      (crPair (crList (crPair crNat crString)) (crPair (crOption crString) (crOption crKindPin)))))))
def crShardPayload : CanonReader cShardPayload :=
  crPair (crList (crPair crNat crPage)) (crList (crPair crNat crPage))

def hexAsciiCanon? : Bytes → Option Bytes
  | [] => some []
  | b0 :: b1 :: rest =>
    match decodeHexNibbleByte? b0, decodeHexNibbleByte? b1 with
    | some hi, some lo =>
      if hi < 16 && lo < 16 && hexNibbleByte hi == b0 && hexNibbleByte lo == b1 then
        (hexAsciiCanon? rest).map ((hi * 16 + lo).toUInt8 :: ·)
      else none
    | _, _ => none
  | [_] => none

theorem hexAsciiCanon?_sound : ∀ (hex raw : Bytes),
    hexAsciiCanon? hex = some raw → bytesToHexAscii raw = hex
  | [], raw, h => by injection h with hr; subst hr; rfl
  | [_], _, h => by cases h
  | b0 :: b1 :: rest, raw, h => by
    unfold hexAsciiCanon? at h
    cases d0 : decodeHexNibbleByte? b0 with
    | none => simp [d0] at h
    | some hi =>
      cases d1 : decodeHexNibbleByte? b1 with
      | none => simp [d0, d1] at h
      | some lo =>
        simp only [d0, d1] at h
        by_cases hc : (decide (hi < 16) && decide (lo < 16) && (hexNibbleByte hi == b0) && (hexNibbleByte lo == b1)) = true
        · simp only [hc, ↓reduceIte] at h
          cases hr : hexAsciiCanon? rest with
          | none => simp [hr] at h
          | some tail =>
            simp only [hr, Option.map, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
            obtain ⟨⟨⟨hhi, hlo⟩, hb0⟩, hb1⟩ := hc
            have hlt : hi * 16 + lo < 256 := by omega
            have hu : (hi * 16 + lo).toUInt8.toNat = hi * 16 + lo := u8_toNat_lt _ hlt
            have hdiv : (hi * 16 + lo) / 16 = hi := by omega
            have hmod : (hi * 16 + lo) % 16 = lo := by omega
            rw [bytesToHexAscii_cons, hu, hdiv, hmod, hb0, hb1, hexAsciiCanon?_sound rest tail hr]
        · simp [hc] at h

def unhexCanonSliceGo (b : ByteArray) (stop : Nat) (hstop : stop ≤ b.size) (i : Nat) (out : ByteArray) :
    Option ByteArray :=
  if h : i + 1 < stop then
    have h0 : i < b.size := by omega
    have h1 : i + 1 < b.size := by omega
    let x0 := b[i]'h0
    let x1 := b[i + 1]'h1
    match decodeHexNibbleByte? x0, decodeHexNibbleByte? x1 with
    | some hi, some lo =>
      if hi < 16 && lo < 16 && hexNibbleByte hi == x0 && hexNibbleByte lo == x1 then
        unhexCanonSliceGo b stop hstop (i + 2) (out.push (hi * 16 + lo).toUInt8)
      else none
    | _, _ => none
  else some out
termination_by stop - i

def unhexCanonSlice (b : ByteArray) (start stop : Nat) : Option ByteArray :=
  if hstop : stop ≤ b.size then
    if start ≤ stop && (stop - start) % 2 == 0 then
      unhexCanonSliceGo b stop hstop start (ByteArray.emptyWithCapacity ((stop - start) / 2))
    else none
  else none

theorem unhexCanonSliceGo_eq (b : ByteArray) (stop : Nat) (hstop : stop ≤ b.size)
    (i : Nat) (hle : i ≤ stop) (heven : (stop - i) % 2 = 0) (out : ByteArray) :
    (unhexCanonSliceGo b stop hstop i out).map (fun a => a.data.toList) =
      (hexAsciiCanon? ((b.data.toList.drop i).take (stop - i))).map (out.data.toList ++ ·) := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [unhexCanonSliceGo]
  by_cases h : i + 1 < stop
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    have hl0 : i < b.data.toList.length := by omega
    have hl1 : i + 1 < b.data.toList.length := by omega
    have hsub : (b.data.toList.drop i).take (stop - i) =
        (b[i]'(by omega)) :: (b[i + 1]'(by omega)) :: (b.data.toList.drop (i + 2)).take (stop - (i + 2)) := by
      have hk : stop - i = (stop - (i + 2)) + 2 := by omega
      rw [List.drop_eq_getElem_cons hl0, List.drop_eq_getElem_cons hl1]
      have g0 : b.data.toList[i]'hl0 = b[i]'(by omega) := rfl
      have g1 : b.data.toList[i + 1]'hl1 = b[i + 1]'(by omega) := rfl
      rw [g0, g1, hk]; rfl
    rw [hsub]
    dsimp only [hexAsciiCanon?]
    cases decodeHexNibbleByte? (b[i]'(by omega)) with
    | none => rfl
    | some hi =>
      cases decodeHexNibbleByte? (b[i + 1]'(by omega)) with
      | none => rfl
      | some lo =>
        dsimp only
        by_cases hc : (decide (hi < 16) && decide (lo < 16) &&
            (hexNibbleByte hi == b[i]'(by omega)) && (hexNibbleByte lo == b[i + 1]'(by omega))) = true
        · simp only [hc, ↓reduceIte]
          rw [unhexCanonSliceGo_eq b stop hstop (i + 2) (by omega) (by omega), push_u8_data]
          cases hexAsciiCanon? ((b.data.toList.drop (i + 2)).take (stop - (i + 2))) <;>
            simp [List.append_assoc]
        · simp [hc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have h0 : stop - i = 0 := by omega
    simp [h0, hexAsciiCanon?]
termination_by stop - i

def decodeShardPayloadCanon (bs : Bytes) : Option ShardPayload :=
  let plen := shardPrefixBytes.length
  let slen := shardSuffixBytes.length
  if plen + slen ≤ bs.length && bs.take plen == shardPrefixBytes &&
      bs.drop (bs.length - slen) == shardSuffixBytes then
    (hexAsciiCanon? ((bs.drop plen).take (bs.length - plen - slen))).bind crShardPayload.decodeExact
  else none

theorem decodeShardPayloadCanon_enc {bs : Bytes} {p : ShardPayload}
    (h : decodeShardPayloadCanon bs = some p) : encodeShardPayload p = bs := by
  unfold decodeShardPayloadCanon at h
  dsimp only at h
  by_cases hc : (decide (shardPrefixBytes.length + shardSuffixBytes.length ≤ bs.length) &&
      (bs.take shardPrefixBytes.length == shardPrefixBytes) &&
      (bs.drop (bs.length - shardSuffixBytes.length) == shardSuffixBytes)) = true
  · rw [ite_eq_left_iff.mpr (fun hne => absurd hc hne)] at h
    cases hh : hexAsciiCanon? ((bs.drop shardPrefixBytes.length).take
        (bs.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
    | none => rw [hh] at h; cases h
    | some raw =>
      rw [hh] at h
      dsimp only [bind, Option.bind] at h
      have henc := crShardPayload.decodeExact_sound h
      have hhex := hexAsciiCanon?_sound _ raw hh
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨hle, hpre⟩, hsuf⟩ := hc
      unfold encodeShardPayload frameShardBytes
      have hsplit1 : bs = bs.take shardPrefixBytes.length ++ bs.drop shardPrefixBytes.length :=
        (List.take_append_drop _ bs).symm
      have hsplit2 : bs.drop shardPrefixBytes.length =
          (bs.drop shardPrefixBytes.length).take (bs.length - shardPrefixBytes.length - shardSuffixBytes.length) ++
          (bs.drop shardPrefixBytes.length).drop (bs.length - shardPrefixBytes.length - shardSuffixBytes.length) :=
        (List.take_append_drop _ _).symm
      have hdrop2 : (bs.drop shardPrefixBytes.length).drop
          (bs.length - shardPrefixBytes.length - shardSuffixBytes.length) =
          bs.drop (bs.length - shardSuffixBytes.length) := by
        rw [List.drop_drop]
        have : shardPrefixBytes.length + (bs.length - shardPrefixBytes.length - shardSuffixBytes.length) =
            bs.length - shardSuffixBytes.length := by omega
        rw [this]
      rw [hdrop2] at hsplit2
      calc shardPrefixBytes ++ bytesToHexAscii (cShardPayload.enc p) ++ shardSuffixBytes
        _ = bs.take shardPrefixBytes.length ++
              ((bs.drop shardPrefixBytes.length).take
                (bs.length - shardPrefixBytes.length - shardSuffixBytes.length)) ++
              bs.drop (bs.length - shardSuffixBytes.length) := by
          rw [henc, hhex, hpre, hsuf]
        _ = bs.take shardPrefixBytes.length ++ bs.drop shardPrefixBytes.length := by
          rw [List.append_assoc, ← hsplit2]
        _ = bs := hsplit1.symm
  · rw [ite_eq_right_iff.mpr (fun heq => absurd heq hc)] at h
    cases h

def decodeShardPayloadCanonArray (b : ByteArray) : Option ShardPayload :=
  let plen := shardPrefixArray.size
  let slen := shardSuffixArray.size
  if plen + slen ≤ b.size && sliceEq b 0 shardPrefixArray &&
      sliceEq b (b.size - slen) shardSuffixArray then
    (unhexCanonSlice b plen (b.size - slen)).bind (decodeExactCanonArray crShardPayload)
  else none

theorem hexAsciiCanon?_of_odd : ∀ (xs : Bytes), xs.length % 2 ≠ 0 → hexAsciiCanon? xs = none
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: _ :: rest, h => by
    unfold hexAsciiCanon?
    cases decodeHexNibbleByte? _ with
    | none => rfl
    | some _ =>
      cases decodeHexNibbleByte? _ with
      | none => rfl
      | some _ =>
        have hrest : rest.length % 2 ≠ 0 := by simp at h; omega
        rw [hexAsciiCanon?_of_odd rest hrest]
        split <;> simp

theorem decodeShardPayloadCanonArray_eq (b : ByteArray) :
    decodeShardPayloadCanonArray b = decodeShardPayloadCanon b.data.toList := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  have hp : shardPrefixArray.data.toList = shardPrefixBytes := rfl
  have hsf : shardSuffixArray.data.toList = shardSuffixBytes := rfl
  have hps : shardPrefixArray.size = shardPrefixBytes.length := by rw [← hp, Array.length_toList]; rfl
  have hsfs : shardSuffixArray.size = shardSuffixBytes.length := by rw [← hsf, Array.length_toList]; rfl
  unfold decodeShardPayloadCanonArray decodeShardPayloadCanon
  dsimp only
  by_cases hbnd : shardPrefixArray.size + shardSuffixArray.size ≤ b.size
  · have hbndL : shardPrefixBytes.length + shardSuffixBytes.length ≤ b.data.toList.length := by omega
    have hex0 : sliceEq b 0 shardPrefixArray =
        (b.data.toList.take shardPrefixBytes.length == shardPrefixBytes) := by
      have hp0 : 0 + shardPrefixArray.size ≤ b.size := by omega
      have hpL : 0 + shardPrefixBytes.length ≤ b.size := by omega
      simp only [sliceEq, sliceEqGo_eq b 0 shardPrefixArray hp0 0,
        Nat.add_zero, Nat.sub_zero, List.drop_zero, hps, hp, hpL, decide_true, Bool.true_and]
    have hex1 : sliceEq b (b.size - shardSuffixArray.size) shardSuffixArray =
        (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) == shardSuffixBytes) := by
      have hs0 : (b.size - shardSuffixArray.size) + shardSuffixArray.size ≤ b.size := by omega
      simp only [sliceEq, hs0, decide_true, Bool.true_and,
        sliceEqGo_eq b (b.size - shardSuffixArray.size) shardSuffixArray hs0 0,
        Nat.add_zero, Nat.sub_zero, List.drop_zero, hsf]
      have hd : b.size - shardSuffixArray.size = b.data.toList.length - shardSuffixBytes.length := by omega
      have htake : (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length)).take shardSuffixArray.size =
          b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) := by
        apply List.take_of_length_le; simp [hs, hsfs]; omega
      rw [hd, htake]
    simp only [hbnd, hbndL, decide_true, Bool.true_and, hex0, hex1]
    by_cases hc : ((b.data.toList.take shardPrefixBytes.length == shardPrefixBytes) &&
        (b.data.toList.drop (b.data.toList.length - shardSuffixBytes.length) == shardSuffixBytes)) = true
    · simp only [hc, ↓reduceIte]
      unfold unhexCanonSlice
      have hstop : b.size - shardSuffixArray.size ≤ b.size := Nat.sub_le _ _
      have hle2 : shardPrefixArray.size ≤ b.size - shardSuffixArray.size := by omega
      rw [dite_eq_left_of_eq_true (eq_true hstop)]
      by_cases hev : ((b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 == 0) = true
      · simp only [hle2, hev, decide_true, Bool.true_and, ↓reduceIte]
        have hev' : (b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 = 0 := by simpa using hev
        have hgo := unhexCanonSliceGo_eq b (b.size - shardSuffixArray.size) hstop shardPrefixArray.size hle2 hev'
          (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2))
        have hemp : (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2)).data.toList = [] := rfl
        have hspan : b.size - shardSuffixArray.size - shardPrefixArray.size =
            b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length := by omega
        cases hu : unhexCanonSliceGo b (b.size - shardSuffixArray.size) hstop shardPrefixArray.size
            (ByteArray.emptyWithCapacity ((b.size - shardSuffixArray.size - shardPrefixArray.size) / 2)) with
        | none =>
          rw [hu, hemp, hspan, hps] at hgo
          cases hu2 : hexAsciiCanon? ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
          | none => rfl
          | some _ => rw [hu2] at hgo; simp at hgo
        | some arr =>
          rw [hu, hemp, hspan, hps] at hgo
          cases hu2 : hexAsciiCanon? ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
          | none => rw [hu2] at hgo; simp at hgo
          | some raw =>
            rw [hu2] at hgo
            simp only [Option.map, List.nil_append, Option.some.injEq] at hgo
            simp [Option.bind, decodeExactCanonArray_eq, hgo]
      · simp only [hle2, hev, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        have hodd : ((b.data.toList.drop shardPrefixBytes.length).take
            (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)).length % 2 ≠ 0 := by
          have hlen : ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)).length =
              b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length := by
            rw [List.length_take, List.length_drop]; omega
          rw [hlen]
          intro h0
          have : ((b.size - shardSuffixArray.size - shardPrefixArray.size) % 2 == 0) = true := by
            rw [beq_iff_eq]; omega
          exact absurd this (by simpa using hev)
        rw [hexAsciiCanon?_of_odd _ hodd]
        rfl
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  · have hbndS : ¬ (shardPrefixBytes.length + shardSuffixBytes.length ≤ b.size) := by omega
    simp [hbnd, hs, hbndS]

theorem decodeShardPayloadCanonArray_sound {b : ByteArray} {p : ShardPayload}
    (h : decodeShardPayloadCanonArray b = some p) :
    encodeShardPayload p = b.data.toList ∧ decodeShardPayload b.data.toList = some p := by
  rw [decodeShardPayloadCanonArray_eq] at h
  have henc := decodeShardPayloadCanon_enc h
  refine ⟨henc, ?_⟩
  rw [← henc, decodeShardPayload_encodeShardPayload]

/-- Verified 128-bucket `Store` index: hashes `bucketOf name` in `O(1)` and scans only the target
bucket (`~N / 128` pages), proved extensionally equal to `Store.page?` and `tombs.find?`. -/
structure BucketedStore where
  pagesByBucket : Array (List (Nat × Page))
  tombsByBucket : Array (List (Nat × Page))

def buildBucketedStore (s : Store) : BucketedStore where
  pagesByBucket := partitionAll (enumList s.pages)
  tombsByBucket := partitionAll (enumList s.tombs)

def BucketedStore.page? (bs : BucketedStore) (name : String) : Option Page :=
  ((bs.pagesByBucket[bucketOf name]?.getD []).find? fun (_, p) => p.name == name).map (·.2)

def BucketedStore.tomb? (bs : BucketedStore) (name : String) : Option Page :=
  ((bs.tombsByBucket[bucketOf name]?.getD []).find? fun (_, p) => p.name == name).map (·.2)

theorem find_bucketItems_enumGo (name : String) :
    ∀ (k : Nat) (ps : List Page),
      ((bucketItems (bucketOf name) (enumGo k ps)).find? fun (_, p) => p.name == name).map (·.2) =
        ps.find? (·.name == name)
  | _, [] => rfl
  | k, p :: rest => by
    simp only [enumGo, bucketItems, List.filter_cons]
    by_cases hpn : (p.name == name) = true
    · have hpEq : p.name = name := beq_iff_eq.mp hpn
      have hb : (bucketOf p.name == bucketOf name) = true := by simp [hpEq]
      simp [hb, hpn]
    · have hpnF : (p.name == name) = false := Bool.eq_false_iff.mpr hpn
      by_cases hb : (bucketOf p.name == bucketOf name) = true
      · simp only [hb, ↓reduceIte, List.find?_cons, hpnF]
        exact find_bucketItems_enumGo name (k + 1) rest
      · have hbF : (bucketOf p.name == bucketOf name) = false := Bool.eq_false_iff.mpr hb
        simp only [hbF, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hpnF]
        exact find_bucketItems_enumGo name (k + 1) rest

theorem BucketedStore.page?_eq (s : Store) (name : String) :
    (buildBucketedStore s).page? name = s.page? name := by
  unfold BucketedStore.page? buildBucketedStore Store.page?
  rw [partitionAll_getElem _ (bucketOf name) (bucketOf_lt name)]
  dsimp only [Option.getD]
  exact find_bucketItems_enumGo name 0 s.pages

theorem BucketedStore.tomb?_eq (s : Store) (name : String) :
    (buildBucketedStore s).tomb? name = s.tombs.find? (·.name == name) := by
  unfold BucketedStore.tomb? buildBucketedStore
  rw [partitionAll_getElem _ (bucketOf name) (bucketOf_lt name)]
  dsimp only [Option.getD]
  exact find_bucketItems_enumGo name 0 s.tombs

def mkCanonicalCachedBucket (payload : ShardPayload) (d : String) (sb : ByteArray)
    (hd : bytesToHex (logHashArray sb) = d) : CachedBucket :=
  if he : isEmptyShard payload = true then
    ⟨payload, none, by simp [shardSpecOf, he]⟩
  else
    letI : DecidableEq ByteArray := ByteArray.decEq
    let cbs := encodeShardPayloadArray payload
    if h : cbs = sb then
      ⟨payload, some (d, sb), by
        simp [cbs, shardSpecOf, he, ← hd, ← h, encodeShardPayloadArray_eq, logHashArray_eq]⟩
    else
      ⟨payload, some (bytesToHex (logHashArray cbs), cbs), by
        simp [cbs, shardSpecOf, he, encodeShardPayloadArray_eq, logHashArray_eq]⟩

/-- Read & authenticate a shard bucket in one pass without re-serializing canonical shards:
1. Hit in-process `DecodeCache` when `e.bytes = sb` in `O(|sb|)` `memcmp`;
2. Otherwise run 1-pass `decodeShardPayloadCanonArray sb`, yielding BOTH `DecodeCache.Entry` and
   `CachedBucket` in `O(1)` extra work (`0` re-serializations on canonical shards);
3. Fall back to `decodeShardPayloadArray` + `mkCanonicalCachedBucket` only on non-canonical shards. -/
def loadBucketZeroReserialize (cached : Option (DecodeCache.Entry decodeShardPayload))
    (d : String) (sb : ByteArray) (hd : bytesToHex (logHashArray sb) = d) :
    Option (ShardPayload × DecodeCache.Entry decodeShardPayload × CachedBucket) :=
  letI : DecidableEq ByteArray := ByteArray.decEq
  match cached with
  | some e =>
    if heq : e.bytes = sb then
      match e.result with
      | none => none
      | some payload =>
        some (payload, e, mkCanonicalCachedBucket payload d sb hd)
    else
      match hdec : decodeShardPayloadCanonArray sb with
      | some payload =>
        have ⟨henc, hpay⟩ := decodeShardPayloadCanonArray_sound hdec
        let ent : DecodeCache.Entry decodeShardPayload := ⟨sb, some payload, hpay.symm⟩
        let cb : CachedBucket :=
          if he : isEmptyShard payload = true then
            ⟨payload, none, by simp [shardSpecOf, he]⟩
          else
            ⟨payload, some (d, sb), by simp [shardSpecOf, he, henc, ← hd, logHashArray_eq]⟩
        some (payload, ent, cb)
      | none =>
        let ent : DecodeCache.Entry decodeShardPayload := ⟨sb, decodeShardPayloadArray sb, decodeShardPayloadArray_eq sb⟩
        match ent.result with
        | none => none
        | some payload => some (payload, ent, mkCanonicalCachedBucket payload d sb hd)
  | none =>
    match hdec : decodeShardPayloadCanonArray sb with
    | some payload =>
      have ⟨henc, hpay⟩ := decodeShardPayloadCanonArray_sound hdec
      let ent : DecodeCache.Entry decodeShardPayload := ⟨sb, some payload, hpay.symm⟩
      let cb : CachedBucket :=
        if he : isEmptyShard payload = true then
          ⟨payload, none, by simp [shardSpecOf, he]⟩
        else
          ⟨payload, some (d, sb), by simp [shardSpecOf, he, henc, ← hd, logHashArray_eq]⟩
      some (payload, ent, cb)
    | none =>
      let ent : DecodeCache.Entry decodeShardPayload := ⟨sb, decodeShardPayloadArray sb, decodeShardPayloadArray_eq sb⟩
      match ent.result with
      | none => none
      | some payload => some (payload, ent, mkCanonicalCachedBucket payload d sb hd)

/-- `O(N)` single-pass array reassembler for `loadShardedWorld`. -/
def reassembleLinear (total : Nat) (arr : Array (List (Nat × Page))) : Option (List Page) := Id.run do
  if arr.size != numBuckets then return none
  let mut slots : Array (Option Page) := Array.replicate total none
  let mut placed : Nat := 0
  for b in [0:numBuckets] do
    for (idx, p) in arr[b]! do
      if idx < total && slots[idx]!.isNone then
        slots := slots.set! idx (some p)
        placed := placed + 1
      else
        return none
  if placed != total then return none
  let mut out : List Page := []
  let mut k := total
  while k > 0 do
    k := k - 1
    match slots[k]! with
    | some p => out := p :: out
    | none => return none
  return some out

/-- Load and authenticate a sharded world from `manifest` + `.obend/world/shards/*.json`,
skipping empty buckets (`0` syscalls for empty buckets!), using per-bucket `DecodeCache`, and
seeding `worldBucketCacheRef` so a subsequent commit re-encodes ONLY buckets whose pages changed. -/
def loadShardedWorld (dir : System.FilePath) (manifest : ByteArray) : IO (Option World) := do
  let some (m, totalPages, totalTombs, digests) := unframeManifestArray manifest
    | return none
  if digests.length != numBuckets then return none
  let decCache ← getDecodeBuckets dir
  let dArr := digests.toArray
  let mut rawShards : Array (Option (String × ByteArray)) := Array.mkEmpty numBuckets
  for b in [0:numBuckets] do
    match dArr[b]! with
    | none => rawShards := rawShards.push none
    | some d =>
      let key := shardKey b d
      let sf := shardPath dir key
      if !(← sf.pathExists) then return none
      let sb ← Obend.Vault.Cost.readBinFile sf
      Obend.Vault.Cost.addCheckpoint sb.size
      rawShards := rawShards.push (some (d, sb))
  let res ← Obend.Vault.Cost.compute fun _ => Id.run do
    let mut pArr : Array (List (Nat × Page)) := Array.mkEmpty numBuckets
    let mut tArr : Array (List (Nat × Page)) := Array.mkEmpty numBuckets
    let mut nextDec := decCache
    let mut builtBuckets : Array CachedBucket := Array.mkEmpty numBuckets
    let emptyBucket : CachedBucket := ⟨([], []), none, by simp [shardSpecOf, isEmptyShard]⟩
    for b in [0:numBuckets] do
      match rawShards[b]! with
      | none =>
        pArr := pArr.push []
        tArr := tArr.push []
        builtBuckets := builtBuckets.push emptyBucket
      | some (d, sb) =>
        if hd : bytesToHex (logHashArray sb) = d then
          match loadBucketZeroReserialize (decCache[b]?.join) d sb hd with
          | none => return none
          | some (payload, ent, cb) =>
            nextDec := nextDec.setIfInBounds b (some ent)
            pArr := pArr.push payload.1
            tArr := tArr.push payload.2
            builtBuckets := builtBuckets.push cb
        else
          return none
    match reassembleLinear totalPages pArr, reassembleLinear totalTombs tArr with
    | some pages, some tombs => return some (withMeta pages tombs m, nextDec, builtBuckets)
    | _, _ => return none
  match res with
  | none => return none
  | some (w, nextDec, builtBuckets) =>
    setDecodeBuckets dir nextDec
    let k ← canonKey dir
    worldBucketCacheRef.modify fun xs => (k, manifest, builtBuckets) :: xs.filter (·.1 != k)
    return some w

/-- Demand-load ONLY `NonStoreMeta` from an authenticated `manifest` without reading any of the
`128` shard files (`0` shard opens, `0` shard bytes read). -/
def loadManifestMetaOnly (manifest : ByteArray) : Option World :=
  (unframeManifestArray manifest).map fun (m, _, _, _) => withMeta [] [] m

/-- Demand-load `NonStoreMeta` plus the single bucket `bucketOf pageName` (`≤ 1` shard file read
instead of `128`), authenticating that shard's `cSHAKE256` digest against `manifest`. -/
def loadManifestSingleBucket (dir : System.FilePath) (manifest : ByteArray) (pageName : String) :
    IO (Option World) := do
  let some (m, _, _, digests) := unframeManifestArray manifest | return none
  if digests.length != numBuckets then return none
  let b := bucketOf pageName
  let some d? := digests[b]? | return none
  match d? with
  | none => return some (withMeta [] [] m)
  | some d =>
    let sf := shardPath dir (shardKey b d)
    if !(← sf.pathExists) then return none
    let sb ← Obend.Vault.Cost.readBinFile sf
    Obend.Vault.Cost.addCheckpoint sb.size
    if bytesToHex (logHashArray sb) != d then return none
    let decCache ← getDecodeBuckets dir
    let ent ← Obend.Vault.Cost.compute fun _ => readBucketCached (decCache[b]?.join) sb
    setDecodeBuckets dir (decCache.setIfInBounds b (some ent))
    match ent.result with
    | none => return none
    | some (ps, ts) => return some (withMeta (ps.map (·.2)) (ts.map (·.2)) m)

end Obend.Vault.ChunkedWorld
