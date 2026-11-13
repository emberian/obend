module
import all Obend.Vault.Log
import all Obend.Polis.BlumRam
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
public import Obend.Polis.BlumRam
public import Obend.Crypto.DualSpine
import all Obend.Crypto.DualSpine
public import Obend.Judge.Class
public import Std.Data.TreeSet.Lemmas
public import Obend.Crypto.FastRing
import all Obend.Crypto.BinaryTower256
import all Init.Data.Array.Basic

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

def appendByteArray (a b : ByteArray) : ByteArray :=
  let rec go (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < b.size then go (i + 1) (acc.push (b[i]'h)) else acc
  termination_by b.size - i
  go 0 a

theorem appendByteArray_go_eq (b : ByteArray) (i : Nat) (acc : ByteArray) :
    (appendByteArray.go b i acc).data.toList = acc.data.toList ++ b.data.toList.drop i := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  rw [appendByteArray.go]
  by_cases h : i < b.size
  · have hl : i < b.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), appendByteArray_go_eq b (i + 1), List.drop_eq_getElem_cons hl]
    have hg : b.data.toList[i]'hl = b[i]'h := rfl
    rw [hg, push_data]
    simp [List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
    simp
termination_by b.size - i

theorem appendByteArray_data (a b : ByteArray) :
    (appendByteArray a b).data.toList = a.data.toList ++ b.data.toList := by
  simpa [appendByteArray] using appendByteArray_go_eq b 0 a

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

def cByteArray : FastCodec ByteArray :=
  cMap (fun b => b.data.toList) (fun xs => some ⟨xs.toArray⟩)
    (by intro b; cases b; simp) cBytes

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

def dataDepth : Data → Nat
  | .natural _ | .boolean _ | .label _ => 1
  | .variant _ p => dataDepth p + 1
  | .record fs => dataFieldsDepth fs + 1
where
  dataFieldsDepth : List (String × Data) → Nat
    | [] => 0
    | (_, d) :: rest => max (dataDepth d) (dataFieldsDepth rest)

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
def encodeHistorySteps : List Graph → List (Bool × Graph)
  | [] => []
  | G :: rest => (false, G) :: go G rest
where
  go (prev : Graph) : List Graph → List (Bool × Graph)
    | [] => []
    | G :: rest =>
      if isPrefixDec prev.atoms G.atoms && isPrefixDec prev.dead G.dead && isPrefixDec prev.edges G.edges then
        (true, ⟨G.atoms.drop prev.atoms.length, G.dead.drop prev.dead.length, G.edges.drop prev.edges.length⟩) ::
          go G rest
      else
        (false, G) :: go G rest

def decodeHistorySteps : List (Bool × Graph) → Option (List Graph)
  | [] => some []
  | (true, _) :: _ => none
  | (false, G) :: rest => (go G rest).map (G :: ·)
where
  go (prev : Graph) : List (Bool × Graph) → Option (List Graph)
    | [] => some []
    | (false, G) :: rest => (go G rest).map (G :: ·)
    | (true, d) :: rest =>
      let G : Graph := ⟨prev.atoms ++ d.atoms, prev.dead ++ d.dead, prev.edges ++ d.edges⟩
      (go G rest).map (G :: ·)

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
def reassembleFromArray (total : Nat) (arr : Array (List (Nat × Page))) : Option (List Page) :=
  if arr.size != numBuckets then none else
  let rec go : Nat → Nat → Array (List (Nat × Page)) → Option (List Page)
    | _, 0, a =>
      if bucketIndices.all (fun b => (a[b]?.getD []).isEmpty) then some [] else none
    | k, rem + 1, a =>
      match bucketIndices.find? (fun b => match a[b]?.getD [] with | (i, _) :: _ => i == k | [] => false) with
      | none => none
      | some b =>
        match a[b]?.getD [] with
        | (_, p) :: rest => (go (k + 1) rem (a.set! b rest)).map (p :: ·)
        | [] => none
  go 0 total arr

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

theorem unhexDigit_hexDigit (n : Nat) (h : n < 16) : Json.unhexDigit (Json.hexDigit n) = some n := by
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem unhex_hex : ∀ (bs : Bytes), Json.unhex (Json.hex bs).toList = some bs
  | [] => rfl
  | b :: bs => by
    have hdiv : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
    have hmod : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hhex : (Json.hex (b :: bs)).toList =
        Json.hexDigit (b.toNat / 16) :: Json.hexDigit (b.toNat % 16) :: (Json.hex bs).toList := by
      simp [Json.hex, String.toList_ofList]
    rw [hhex, Json.unhex]
    dsimp only [bind, Option.bind, pure]
    rw [unhexDigit_hexDigit _ hdiv, unhexDigit_hexDigit _ hmod, unhex_hex bs]
    dsimp only
    congr 1; congr 1
    have hb : (b.toNat / 16 * 16 + b.toNat % 16) = b.toNat := by omega
    rw [hb]
    exact UInt8.ofNat_toNat

def hexNibble (n : Nat) : UInt8 :=
  if n < 10 then (48 + n).toUInt8 else (87 + n).toUInt8

def hexByteHi (b : UInt8) : UInt8 := hexNibble (b.toNat / 16)
def hexByteLo (b : UInt8) : UInt8 := hexNibble (b.toNat % 16)

def unhexNibble (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

theorem unhexNibble_hexNibble (n : Nat) (h : n < 16) : unhexNibble (hexNibble n) = some n := by
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hexNibble_ne_quote (n : Nat) (h : n < 16) : hexNibble n ≠ 34 := by
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def hexAsciiBytes (bs : Bytes) : Bytes :=
  bs.flatMap fun b => [hexByteHi b, hexByteLo b]

def unhexAsciiBytes : Bytes → Option Bytes
  | [] => some []
  | a :: b :: rest => do
    let hi ← unhexNibble a
    let lo ← unhexNibble b
    let tl ← unhexAsciiBytes rest
    some ((hi * 16 + lo).toUInt8 :: tl)
  | [_] => none

theorem unhexNibble_hi (b : UInt8) : unhexNibble (hexByteHi b) = some (b.toNat / 16) :=
  unhexNibble_hexNibble _ (by have := b.toNat_lt; omega)

theorem unhexNibble_lo (b : UInt8) : unhexNibble (hexByteLo b) = some (b.toNat % 16) :=
  unhexNibble_hexNibble _ (Nat.mod_lt _ (by decide))

theorem unhexAscii_hexAscii : ∀ (bs : Bytes), unhexAsciiBytes (hexAsciiBytes bs) = some bs
  | [] => rfl
  | b :: bs => by
    have ih := unhexAscii_hexAscii bs
    simp only [hexAsciiBytes] at ih
    simp only [hexAsciiBytes, List.flatMap_cons, List.cons_append, List.nil_append, unhexAsciiBytes]
    rw [unhexNibble_hi b, unhexNibble_lo b, ih]
    simp only [bind, Option.bind]
    congr 1; congr 1
    have hb : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    rw [hb]; exact UInt8.ofNat_toNat

def pushHexArray (acc : ByteArray) (raw : ByteArray) : ByteArray :=
  let rec go (i : Nat) (out : ByteArray) : ByteArray :=
    if h : i < raw.size then
      let b := raw[i]'h
      go (i + 1) ((out.push (hexByteHi b)).push (hexByteLo b))
    else out
  termination_by raw.size - i
  go 0 acc

theorem pushHexArray_go_eq (raw : ByteArray) (i : Nat) (out : ByteArray) :
    (pushHexArray.go raw i out).data.toList =
      out.data.toList ++ hexAsciiBytes (raw.data.toList.drop i) := by
  have hs : raw.data.toList.length = raw.size := Array.length_toList
  rw [pushHexArray.go]
  by_cases h : i < raw.size
  · have hl : i < raw.data.toList.length := by omega
    rw [dite_eq_left_of_eq_true (eq_true h), pushHexArray_go_eq raw (i + 1), List.drop_eq_getElem_cons hl]
    have hg : raw.data.toList[i]'hl = raw[i]'h := rfl
    rw [hg, push_u8_data, push_u8_data]
    simp [hexAsciiBytes, List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h), List.drop_eq_nil_of_le (by omega)]
    simp [hexAsciiBytes]
termination_by raw.size - i

theorem pushHexArray_eq (acc raw : ByteArray) :
    (pushHexArray acc raw).data.toList = acc.data.toList ++ hexAsciiBytes raw.data.toList := by
  simpa [pushHexArray] using pushHexArray_go_eq raw 0 acc

def unhexSliceGo (b : ByteArray) (stop : Nat) (hstop : stop ≤ b.size) (i : Nat) (out : ByteArray) :
    Option ByteArray :=
  if h : i + 1 < stop then
    have h0 : i < b.size := by omega
    have h1 : i + 1 < b.size := by omega
    match unhexNibble (b[i]'h0), unhexNibble (b[i + 1]'h1) with
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
      (unhexAsciiBytes ((b.data.toList.drop i).take (stop - i))).map (out.data.toList ++ ·) := by
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
    dsimp only [unhexAsciiBytes]
    cases unhexNibble (b[i]'(by omega)) with
    | none => rfl
    | some hi =>
      cases unhexNibble (b[i + 1]'(by omega)) with
      | none => rfl
      | some lo =>
        dsimp only [bind, Option.bind]
        rw [unhexSliceGo_eq b stop hstop (i + 2) (by omega) (by omega)]
        rw [push_u8_data]
        cases unhexAsciiBytes ((b.data.toList.drop (i + 2)).take (stop - (i + 2))) <;>
          simp [List.append_assoc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have h0 : stop - i = 0 := by omega
    simp [h0, unhexAsciiBytes]
termination_by stop - i

/-! ### Shard JSON Framing: `{"format":"obend-shard-1","hex":"..."}\n` -/

def shardPrefixArray : ByteArray := "{\"format\":\"obend-shard-1\",\"hex\":\"".toUTF8
def shardSuffixArray : ByteArray := "\"}\n".toUTF8

def shardPrefixBytes : Bytes := shardPrefixArray.data.toList
def shardSuffixBytes : Bytes := shardSuffixArray.data.toList

def frameShardBytes (raw : Bytes) : Bytes :=
  shardPrefixBytes ++ hexAsciiBytes raw ++ shardSuffixBytes

def unframeShardBytes (bs : Bytes) : Option Bytes :=
  let plen := shardPrefixBytes.length
  let slen := shardSuffixBytes.length
  if plen + slen ≤ bs.length && bs.take plen == shardPrefixBytes &&
      bs.drop (bs.length - slen) == shardSuffixBytes then
    unhexAsciiBytes ((bs.drop plen).take (bs.length - plen - slen))
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
  let m := hexAsciiBytes raw
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
  exact unhexAscii_hexAscii raw

def frameShardArray (raw : ByteArray) : ByteArray :=
  appendByteArray (pushHexArray shardPrefixArray raw) shardSuffixArray

theorem frameShardArray_eq (raw : ByteArray) :
    (frameShardArray raw).data.toList = frameShardBytes raw.data.toList := by
  simp [frameShardArray, frameShardBytes, appendByteArray_data, pushHexArray_eq,
    shardPrefixBytes, shardSuffixBytes, List.append_assoc]

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
          cases hu2 : unhexAsciiBytes ((b.data.toList.drop shardPrefixBytes.length).take
              (b.data.toList.length - shardPrefixBytes.length - shardSuffixBytes.length)) with
          | none => rfl
          | some _ => rw [hu2] at hgo; simp at hgo
        | some arr =>
          rw [hu, hemp, hspan, hps] at hgo
          cases hu2 : unhexAsciiBytes ((b.data.toList.drop shardPrefixBytes.length).take
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
        have hnone : ∀ (xs : Bytes), xs.length % 2 ≠ 0 → unhexAsciiBytes xs = none := by
          intro xs
          induction xs using unhexAsciiBytes.induct with
          | case1 => intro h; simp at h
          | case2 a1 a2 rest ih =>
            intro h
            have hr : rest.length % 2 ≠ 0 := by simp at h; omega
            simp [unhexAsciiBytes, ih hr, bind, Option.bind]
            cases unhexNibble a1 <;> cases unhexNibble a2 <;> rfl
          | case3 _ => intro _; rfl
        rw [hnone _ hodd]
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
  hex [b.toUInt8] ++ "-" ++ digest

theorem hex_single_len (x : UInt8) : (hex [x]).toList.length = 2 := by
  simp [hex]

theorem shardKey_take2 (b : Nat) (d : String) :
    (shardKey b d).toList.take 2 = (hex [b.toUInt8]).toList := by
  unfold shardKey
  have happ : (hex [b.toUInt8] ++ "-" ++ d).toList =
      (hex [b.toUInt8]).toList ++ ("-" ++ d).toList := by
    rw [String.append_assoc, String.toList_append]
  rw [happ, ← hex_single_len b.toUInt8]
  exact take_append_exact _ _

theorem shardKey_bucket_inj {b1 b2 : Nat} {d1 d2 : String}
    (h1 : b1 < numBuckets) (h2 : b2 < numBuckets)
    (heq : shardKey b1 d1 = shardKey b2 d2) : b1 = b2 := by
  have ht : (shardKey b1 d1).toList.take 2 = (shardKey b2 d2).toList.take 2 := by rw [heq]
  rw [shardKey_take2, shardKey_take2] at ht
  have hu := congrArg unhex ht
  rw [unhex_hex, unhex_hex] at hu
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
    some (hex (logHash sb), sb)

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
      if hex (logHash sb) != d then
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
            some (hex (logHash (encodeShardPayload pay)), encodeShardPayload pay) := by
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
      ⟨p, some (hex (logHashArray bs), bs), by
        simp [bs, shardSpecOf, he, encodeShardPayloadArray_eq, logHashArray_eq]⟩
  | none =>
    if he : isEmptyShard p = true then
      ⟨p, none, by simp [shardSpecOf, he]⟩
    else
      let bs := encodeShardPayloadArray p
      ⟨p, some (hex (logHashArray bs), bs), by
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
  let rootDigest := hex (logHashArray manifest)
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

theorem dig_eq_unbe_logHashArray (mb : ByteArray) :
    unbe (logHashArray mb) = dig logHash mb.data.toList := by
  rw [logHashArray_eq]; rfl

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

def mkCanonicalCachedBucket (payload : ShardPayload) (d : String) (sb : ByteArray)
    (hd : hex (logHashArray sb) = d) : CachedBucket :=
  if he : isEmptyShard payload = true then
    ⟨payload, none, by simp [shardSpecOf, he]⟩
  else
    letI : DecidableEq ByteArray := ByteArray.decEq
    let cbs := encodeShardPayloadArray payload
    if h : cbs = sb then
      ⟨payload, some (d, sb), by
        simp [cbs, shardSpecOf, he, ← hd, ← h, encodeShardPayloadArray_eq, logHashArray_eq]⟩
    else
      ⟨payload, some (hex (logHashArray cbs), cbs), by
        simp [cbs, shardSpecOf, he, encodeShardPayloadArray_eq, logHashArray_eq]⟩

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
        if hd : hex (logHashArray sb) = d then
          let ent := readBucketCached (decCache[b]?.join) sb
          nextDec := nextDec.setIfInBounds b (some ent)
          match ent.result with
          | none => return none
          | some payload =>
            pArr := pArr.push payload.1
            tArr := tArr.push payload.2
            builtBuckets := builtBuckets.push (mkCanonicalCachedBucket payload d sb hd)
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
    if hex (logHashArray sb) != d then return none
    let decCache ← getDecodeBuckets dir
    let ent ← Obend.Vault.Cost.compute fun _ => readBucketCached (decCache[b]?.join) sb
    setDecodeBuckets dir (decCache.setIfInBounds b (some ent))
    match ent.result with
    | none => return none
    | some (ps, ts) => return some (withMeta (ps.map (·.2)) (ts.map (·.2)) m)

end Obend.Vault.ChunkedWorld

/- COW snapshots, input-pinned dual commitment binding and crash-safe WAL recovery. -/
namespace Obend.Vault.VerkleSnapshotBridge
open Obend.Digest.HashBytes (Hash be ofBE ofBE_lt)
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness)
open Obend.Crypto (AjtaiParams NonPigeonholeSISParams ModuleSISHard BoundedCollision
  cshake32ByteArray cshake32ByteArray_size encodeListField leb128 Short ShortNormBound
  ajtaiCommit extractShortDiffSISWitness inhabitedAjtaiParams inhabitedAjtaiParams_sisHard)
open Obend.Polis (ExtRam treeCustomization treeHash tagOf leafPreimage nodePreimage
  leafTag nodeTag nibbleAt insertAt insertAt_inj climbStep climb verifyOpening
  encodeFields encodeFields_injective map_toList_injective)
open Obend.Vault
open Obend.Vault.Rehydration (genesisSentinel)
set_option autoImplicit false
/-! ## 1. Dimensions, Full-Width 256-Bit Digest Limbs & Chunk Carriers -/
/-- Number of persistent COW chunks ($K = 16^2 = 256$). -/
def numChunks : Nat := 256
/-- Number of 64-bit `UInt64` slots per chunk ($B = 16$). -/
def chunkSlots : Nat := 16
/-- Number of chunk groups at level 2 (`256 / 16 = 16`). -/
def numGroups : Nat := 16
/-- Total materialized leaf slots across all chunks ($N = K \cdot B = 4{,}096$). -/
def totalSlots : Nat := 4096
/-- Maximum `VerkleUmem` preimage byte length hashed by any well-sized opening (`1 + 16 * 33 = 529`). -/
def verkleMaxPreimageBytes : Nat := 529
/-- One fixed-width chunk of `B = 16` 64-bit `UInt64` slots. -/
structure ChunkData where
  slots : Array UInt64
  size_eq : slots.size = chunkSlots
  deriving DecidableEq
/-- All-zero 16-slot chunk. -/
def zeroChunk : ChunkData := ⟨Array.replicate chunkSlots 0, by simp [chunkSlots]⟩
/-- Read slot `j < 16` from `chunk` (`0` out of range). -/
def ChunkData.getSlot (chunk : ChunkData) (j : Nat) : UInt64 := chunk.slots.getD j 0
/-- Return an updated copy of `chunk` with slot `j` set to `v`. -/
def ChunkData.setSlot (chunk : ChunkData) (j : Nat) (v : UInt64) : ChunkData :=
  ⟨chunk.slots.setIfInBounds j v, by simp [chunk.size_eq]⟩
/-- Map `(chunkIdx, slotIdx)` (`c < 256`, `j < 16`) to its 64-bit `VerkleUmem` key `16 * c + j`. -/
def slotAddr (c j : Nat) : UInt64 := UInt64.ofNat (c * chunkSlots + j)
/-- `slotAddr` is exact (no `2^64` wraparound) whenever `c < n` for a chunk count `16 * n ≤ 2^64`. -/
theorem slotAddr_toNat_of_bound {c j n : Nat} (hc : c < n) (hn : chunkSlots * n ≤ 2 ^ 64)
    (hj : j < chunkSlots) : (slotAddr c j).toNat = c * chunkSlots + j := by
  unfold slotAddr chunkSlots at *; rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
theorem slotAddr_toNat {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    (slotAddr c j).toNat = c * chunkSlots + j := slotAddr_toNat_of_bound hc (by decide) hj
private theorem foldl_be_inj : ∀ (xs ys : List UInt8) (a₁ a₂ : Nat), xs.length = ys.length →
    xs.foldl (fun a b => a * 256 + b.toNat) a₁ = ys.foldl (fun a b => a * 256 + b.toNat) a₂ →
    a₁ = a₂ ∧ xs = ys
  | [], [], a₁, a₂, _, h => ⟨h, rfl⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, a₁, a₂, hlen, h => by
    obtain ⟨ha, htail⟩ := foldl_be_inj xs ys (a₁ * 256 + x.toNat) (a₂ * 256 + y.toNat)
      (Nat.succ.inj hlen) h
    have hx : x.toNat < 256 := x.toNat_lt
    have hy : y.toNat < 256 := y.toNat_lt
    have hxy : x = y := UInt8.toNat_inj.1 (by omega)
    exact ⟨by omega, by rw [hxy, htail]⟩
private theorem uint64_ofBE_8_inj {xs ys : List UInt8} (hx : xs.length = 8) (hy : ys.length = 8)
    (heq : UInt64.ofNat (ofBE xs) = UInt64.ofNat (ofBE ys)) : xs = ys := by
  have hpow : 256 ^ 8 = 2 ^ 64 := by decide
  have hxlt : ofBE xs < 2 ^ 64 := by have := ofBE_lt xs; rw [hx, hpow] at this; exact this
  have hylt : ofBE ys < 2 ^ 64 := by have := ofBE_lt ys; rw [hy, hpow] at this; exact this
  have hnat : (UInt64.ofNat (ofBE xs)).toNat = (UInt64.ofNat (ofBE ys)).toNat :=
    congrArg UInt64.toNat heq
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hnat
  exact (foldl_be_inj xs ys 0 0 (hx.trans hy.symm) hnat).2
/-- Split a 32-byte (256-bit) digest into four big-endian 64-bit `UInt64` limbs without truncation. -/
def digestLimbs256 (d : List UInt8) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (UInt64.ofNat (ofBE (d.take 8)), UInt64.ofNat (ofBE ((d.drop 8).take 8)),
   UInt64.ofNat (ofBE ((d.drop 16).take 8)),
   UInt64.ofNat (ofBE ((d.drop 24).take 8)))
/-- **Full-Width 256-Bit Carrier Injectivity (`digestLimbs256_injective`)**:
    Two 32-byte digests with equal `4 × UInt64` limb tuples are byte-for-byte identical. -/
theorem digestLimbs256_injective {d₁ d₂ : List UInt8} (h₁ : d₁.length = 32) (h₂ : d₂.length = 32)
    (heq : digestLimbs256 d₁ = digestLimbs256 d₂) : d₁ = d₂ := by
  unfold digestLimbs256 at heq
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨e0, e1, e2, e3⟩
  have s0 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e0
  have s1 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e1
  have s2 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e2
  have s3 := uint64_ofBE_8_inj (by simp [h₁]) (by simp [h₂]) e3
  have split32 : ∀ (xs : List UInt8), xs.length = 32 →
      xs = xs.take 8 ++ ((xs.drop 8).take 8 ++ ((xs.drop 16).take 8 ++ (xs.drop 24).take 8)) := by
    intro xs hlen
    have h24 : (xs.drop 24).take 8 = xs.drop 24 := List.take_of_length_le (by simp [hlen])
    have h16 : xs.drop 16 = (xs.drop 16).take 8 ++ xs.drop 24 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (xs.drop 16)).symm
    have h8 : xs.drop 8 = (xs.drop 8).take 8 ++ xs.drop 16 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (xs.drop 8)).symm
    rw [h24, ← h16, ← h8, List.take_append_drop]
  rw [split32 d₁ h₁, split32 d₂ h₂, s0, s1, s2, s3]
/-- Pack four 64-bit digest limbs plus two metadata words into a 16-slot `ChunkData`. -/
def packDigestChunk (limbs : UInt64 × UInt64 × UInt64 × UInt64) (meta0 meta1 : UInt64) : ChunkData where
  slots := #[limbs.1, limbs.2.1, limbs.2.2.1, limbs.2.2.2, meta0, meta1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  size_eq := rfl
/-- Chunk encoding of `ChunkedWorld` bucket `b < 128`. -/
def worldBucketChunk (w : ChunkedWorld.World) (b : Nat) : ChunkData :=
  match ChunkedWorld.shardForBucket w b with
  | none => zeroChunk
  | some (_, sb) =>
    packDigestChunk (digestLimbs256 (ChunkedWorld.logHash sb)) 1 (UInt64.ofNat sb.length)
/-- Chunk `128` encoding the full 256-bit `cSHAKE256` digest of `ChunkedWorld.manifestBytes w`. -/
def worldManifestChunk (w : ChunkedWorld.World) : ChunkData :=
  let mb := ChunkedWorld.manifestBytes w
  packDigestChunk (digestLimbs256 (ChunkedWorld.logHash mb))
    (UInt64.ofNat w.store.pages.length) (UInt64.ofNat w.store.tombs.length)
/-- Materialize all `256` chunks of `w` from scratch (`0..127`: buckets; `128`: manifest; `129..255`: COW). -/
def materializeWorldChunks (w : ChunkedWorld.World) : Array ChunkData :=
  ((List.range numChunks).map fun c =>
    if c < ChunkedWorld.numBuckets then worldBucketChunk w c
    else if c = ChunkedWorld.numBuckets then worldManifestChunk w
    else zeroChunk).toArray
theorem materializeWorldChunks_size (w : ChunkedWorld.World) :
    (materializeWorldChunks w).size = numChunks := by simp [materializeWorldChunks]
/-! ## 2. `VerkleUmem` Tree Specification, Scratch Commit & $O(\log K)$ Incremental Update -/
private theorem leafTag_size (v : UInt64) : (leafTag v).size = 32 := by
  unfold leafTag tagOf; exact cshake32ByteArray_size treeCustomization (leafPreimage v)
private theorem nodeTag_size (children : List ByteArray) : (nodeTag children).size = 32 := by
  unfold nodeTag tagOf; exact cshake32ByteArray_size treeCustomization (nodePreimage children)
private theorem getD_lt {α : Type} (xs : Array α) (i : Nat) (d : α) (hi : i < xs.size) :
    xs.getD i d = xs[i]'hi := by unfold Array.getD; simp [hi]
private theorem map_const_range (n : Nat) (x : ByteArray) :
    (List.range n).map (fun _ => x) = List.replicate n x := by
  apply List.ext_getElem (by simp); intro _ _ _; simp
/-- Canonical all-zero `VerkleUmem` subtree tag of height `lvl`. -/
def zeroTreeTag : Nat → ByteArray
  | 0 => leafTag 0
  | lvl + 1 => nodeTag (List.replicate 16 (zeroTreeTag lvl))
theorem zeroTreeTag_size : ∀ (lvl : Nat), (zeroTreeTag lvl).size = 32
  | 0 => leafTag_size 0
  | lvl + 1 => nodeTag_size (List.replicate 16 (zeroTreeTag lvl))
/-- Level-1 `VerkleUmem` subtree tag of a 16-slot `ChunkData`. -/
def chunkSubtreeTag (c : ChunkData) : ByteArray := nodeTag (c.slots.toList.map leafTag)
theorem chunkSubtreeTag_size (c : ChunkData) : (chunkSubtreeTag c).size = 32 :=
  nodeTag_size (c.slots.toList.map leafTag)
theorem chunkSubtreeTag_zero : chunkSubtreeTag zeroChunk = zeroTreeTag 1 := by
  unfold chunkSubtreeTag zeroChunk zeroTreeTag chunkSlots
  exact congrArg nodeTag (by simp [Array.toList_replicate, zeroTreeTag])
/-- Extract the 16 chunk roots belonging to group `g < 16`. -/
def groupChunkTags (chunkRoots : Array ByteArray) (g : Nat) : List ByteArray :=
  (List.range 16).map fun d => chunkRoots.getD (g * 16 + d) (zeroTreeTag 1)
private theorem groupChunkTags_getElem (cr : Array ByteArray) (g d : Nat) (hd : d < 16) :
    (groupChunkTags cr g)[d]'(by simp [groupChunkTags]; exact hd) =
      cr.getD (g * 16 + d) (zeroTreeTag 1) := by
  unfold groupChunkTags; simp
/-- Level-2 `VerkleUmem` subtree tag for group `g` from `chunkRoots`. -/
def groupSubtreeTag (chunkRoots : Array ByteArray) (g : Nat) : ByteArray :=
  nodeTag (groupChunkTags chunkRoots g)
/-- Lift the level-3 active-prefix root (`4,096` slots) up `steps` levels starting at `lvl`. -/
def liftSpineFrom : Nat → Nat → ByteArray → ByteArray
  | _, 0, cur => cur
  | lvl, steps + 1, cur =>
    liftSpineFrom (lvl + 1) steps (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl)))
theorem liftSpineFrom_size : ∀ (lvl steps : Nat) (cur : ByteArray),
    cur.size = 32 → (liftSpineFrom lvl steps cur).size = 32
  | _, 0, _, hcur => hcur
  | lvl, steps + 1, cur, _ =>
    liftSpineFrom_size (lvl + 1) steps
      (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))) (nodeTag_size _)
/-- Lift a level-3 tag across levels `3..15` (`13` spine hashes) to the level-16 `VerkleUmem` root. -/
def liftActiveToRoot (activeTag : ByteArray) : ByteArray := liftSpineFrom 3 13 activeTag
/-- **Full Materialized Verkle Commit (`fullVerkleCommitChunks`)**:
    Hashes all $N = 4{,}096$ slots across all $K = 256$ chunks from scratch into the 32-byte root. -/
def fullVerkleCommitChunks (chunks : Array ChunkData) : ByteArray :=
  let cRoots := ((List.range numChunks).map fun c =>
    chunkSubtreeTag (chunks.getD c zeroChunk)).toArray
  liftActiveToRoot (nodeTag ((List.range numGroups).map fun g => groupSubtreeTag cRoots g))
/-- Full scratch Verkle root of a `ChunkedWorld.World`. -/
def fullVerkleCommitWorld (w : ChunkedWorld.World) : ByteArray :=
  fullVerkleCommitChunks (materializeWorldChunks w)
theorem fullVerkleCommitChunks_size (chunks : Array ChunkData) :
    (fullVerkleCommitChunks chunks).size = 32 := by
  unfold fullVerkleCommitChunks liftActiveToRoot; dsimp only
  exact liftSpineFrom_size 3 13 _ (nodeTag_size _)
/-- View `chunks` as an `Obend.Polis.ExtRam` over all $2^{64}$ addresses (`0` for `addr ≥ 4096`). -/
def chunksToExtRam (chunks : Array ChunkData) : ExtRam := fun addr =>
  let a := addr.toNat
  if a < totalSlots then (chunks.getD (a / chunkSlots) zeroChunk).getSlot (a % chunkSlots) else 0
/-- Pure mathematical 16-ary tree tag over an arbitrary `ExtRam` at `(lvl, pfx)`. -/
def specExtRamTreeTag (ram : ExtRam) : Nat → Nat → ByteArray
  | 0, pfx => if pfx < 2 ^ 64 then leafTag (ram (UInt64.ofNat pfx)) else leafTag 0
  | lvl + 1, pfx => nodeTag ((List.range 16).map fun d => specExtRamTreeTag ram lvl (pfx * 16 + d))
private theorem specExtRamTreeTag_zero (ram : ExtRam) (pfx : Nat) : specExtRamTreeTag ram 0 pfx =
      if pfx < 2 ^ 64 then leafTag (ram (UInt64.ofNat pfx)) else leafTag 0 := rfl
private theorem specExtRamTreeTag_succ (ram : ExtRam) (lvl pfx : Nat) :
    specExtRamTreeTag ram (lvl + 1) pfx =
      nodeTag ((List.range 16).map fun d => specExtRamTreeTag ram lvl (pfx * 16 + d)) := rfl
private theorem specExtRamTreeTag_zero_above (chunks : Array ChunkData) :
    ∀ (lvl pfx : Nat), totalSlots ≤ pfx * 16 ^ lvl →
      specExtRamTreeTag (chunksToExtRam chunks) lvl pfx = zeroTreeTag lvl
  | 0, pfx, hge => by
    simp only [Nat.pow_zero, Nat.mul_one] at hge
    rw [specExtRamTreeTag_zero]; unfold zeroTreeTag
    split
    · rename_i hlt
      unfold chunksToExtRam; dsimp only
      have hu : (UInt64.ofNat pfx).toNat = pfx := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
      rw [hu]
      have hnot : ¬ pfx < totalSlots := by omega
      simp only [hnot, ↓reduceIte]
    · rfl
  | lvl + 1, pfx, hge => by
    rw [specExtRamTreeTag_succ]; unfold zeroTreeTag
    apply congrArg nodeTag
    rw [← map_const_range 16 (zeroTreeTag lvl)]
    apply List.map_congr_left
    intro d _
    apply specExtRamTreeTag_zero_above chunks lvl (pfx * 16 + d)
    rw [Nat.pow_succ, Nat.mul_comm (16 ^ lvl) 16, ← Nat.mul_assoc] at hge
    exact Nat.le_trans hge (Nat.mul_le_mul_right (16 ^ lvl) (by omega))
private theorem chunkSlots_toList_eq_range (c : ChunkData) :
    c.slots.toList.map leafTag = (List.range 16).map (fun j => leafTag (c.getSlot j)) := by
  have hlen : c.slots.toList.length = 16 := by rw [Array.length_toList, c.size_eq]; rfl
  apply List.ext_getElem (by simp [hlen])
  intro j _ hj2
  simp only [List.getElem_map, List.getElem_range]
  have hjb : j < c.slots.size := by rw [c.size_eq]; simp at hj2; exact hj2
  unfold ChunkData.getSlot; rw [getD_lt c.slots j 0 hjb]; simp
private theorem specExtRamTreeTag_lvl3 (chunks : Array ChunkData) :
    specExtRamTreeTag (chunksToExtRam chunks) 3 0 = nodeTag ((List.range numGroups).map fun g =>
        groupSubtreeTag (((List.range numChunks).map fun c =>
          chunkSubtreeTag (chunks.getD c zeroChunk)).toArray) g) := by
  have hlvl1 : ∀ c < numChunks, specExtRamTreeTag (chunksToExtRam chunks) 1 c =
        chunkSubtreeTag (chunks.getD c zeroChunk) := by
    intro c hc
    rw [specExtRamTreeTag_succ]; unfold chunkSubtreeTag; rw [chunkSlots_toList_eq_range]
    apply congrArg nodeTag; apply List.map_congr_left
    intro j hj
    have hjlt : j < 16 := List.mem_range.mp hj
    rw [specExtRamTreeTag_zero]
    have hlt64 : c * 16 + j < 2 ^ 64 := by unfold numChunks at hc; omega
    have hltTot : c * 16 + j < totalSlots := by unfold numChunks totalSlots at *; omega
    simp only [hlt64, ↓reduceIte]; unfold chunksToExtRam; dsimp only
    have hu : (UInt64.ofNat (c * 16 + j)).toNat = c * 16 + j := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt64
    have hdiv : (c * 16 + j) / chunkSlots = c := by unfold chunkSlots; omega
    have hmod : (c * 16 + j) % chunkSlots = j := by unfold chunkSlots; omega
    rw [hu]; simp only [hltTot, ↓reduceIte, hdiv, hmod]
  rw [specExtRamTreeTag_succ]; unfold numGroups
  apply congrArg nodeTag; apply List.map_congr_left
  intro g hg
  have hglt : g < 16 := List.mem_range.mp hg
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [specExtRamTreeTag_succ]; unfold groupSubtreeTag groupChunkTags
  apply congrArg nodeTag; apply List.map_congr_left
  intro d hd
  have hdlt : d < 16 := List.mem_range.mp hd
  have hclt : g * 16 + d < numChunks := by unfold numChunks; omega
  rw [hlvl1 (g * 16 + d) hclt]
  let arr := ((List.range numChunks).map fun c =>
    chunkSubtreeTag (chunks.getD c zeroChunk)).toArray
  have hsz : arr.size = numChunks := by simp [arr]
  rw [getD_lt arr (g * 16 + d) (zeroTreeTag 1) (by rw [hsz]; exact hclt)]; simp [arr]
private theorem liftSpineFrom_eq_specExtRam (chunks : Array ChunkData) :
    ∀ (steps lvl : Nat), 3 ≤ lvl →
      liftSpineFrom lvl steps (specExtRamTreeTag (chunksToExtRam chunks) lvl 0) =
        specExtRamTreeTag (chunksToExtRam chunks) (lvl + steps) 0 := by
  intro steps
  induction steps with
  | zero => intro lvl _; simp [liftSpineFrom]
  | succ steps ih =>
    intro lvl hlvl
    have hstep : specExtRamTreeTag (chunksToExtRam chunks) (lvl + 1) 0 =
        nodeTag (specExtRamTreeTag (chunksToExtRam chunks) lvl 0 ::
          List.replicate 15 (zeroTreeTag lvl)) := by
      rw [specExtRamTreeTag_succ]; apply congrArg nodeTag
      have hr : List.range 16 = 0 :: (List.range 15).map (· + 1) := by decide
      rw [hr, List.map_cons, List.map_map]
      simp only [Nat.zero_mul, Nat.zero_add, Function.comp_def]
      apply congrArg (specExtRamTreeTag (chunksToExtRam chunks) lvl 0 :: ·)
      rw [← map_const_range 15 (zeroTreeTag lvl)]
      apply List.map_congr_left; intro d _
      apply specExtRamTreeTag_zero_above
      have hpow : 16 ^ 3 ≤ 16 ^ lvl := Nat.pow_le_pow_right (by decide) hlvl
      have htot : totalSlots = 16 ^ 3 := by decide
      rw [htot]; exact Nat.le_trans hpow (Nat.le_mul_of_pos_left _ (by omega))
    unfold liftSpineFrom; rw [← hstep]
    have heq := ih (lvl + 1) (by omega)
    have hadd : lvl + 1 + steps = lvl + (steps + 1) := by omega
    rwa [hadd] at heq
/-- **`fullVerkleCommitChunks` Equals the 16-Level `ExtRam` Root**: materializing the 4,096 chunk
    slots gives the `VerkleUmem` root of `chunksToExtRam chunks` over the $2^{64}$ address space. -/
theorem fullVerkleCommitChunks_eq_specExtRamRoot (chunks : Array ChunkData) :
    fullVerkleCommitChunks chunks = specExtRamTreeTag (chunksToExtRam chunks) 16 0 := by
  unfold fullVerkleCommitChunks liftActiveToRoot; dsimp only
  rw [← specExtRamTreeTag_lvl3 chunks]
  exact liftSpineFrom_eq_specExtRam chunks 13 3 (by decide)
/-! ## 3. Base-$2^{16}$ `UInt64` Gadget Decomposition & Per-Chunk Ajtai Lattice Commitments -/
/-- Decompose a 64-bit `UInt64` word losslessly into four 16-bit integer limbs in `[0, 65535]`. -/
def decomposeUInt64Limbs (u : UInt64) : List Int :=
  let n := u.toNat
  [(((n % 65536) : Nat) : Int), ((((n / 65536) % 65536) : Nat) : Int),
   ((((n / 4294967296) % 65536) : Nat) : Int), (((n / 281474976710656) : Nat) : Int)]
theorem decomposeUInt64Limbs_injective {u₁ u₂ : UInt64}
    (h : decomposeUInt64Limbs u₁ = decomposeUInt64Limbs u₂) : u₁ = u₂ := by
  unfold decomposeUInt64Limbs at h
  simp only [List.cons.injEq, Int.ofNat_inj, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have hb1 : u₁.toNat < 2 ^ 64 := u₁.toNat_lt
  have hb2 : u₂.toNat < 2 ^ 64 := u₂.toNat_lt
  exact UInt64.toNat_inj.1 (by omega)
theorem decomposeUInt64Limbs_short (u : UInt64) :
    ∀ z ∈ decomposeUInt64Limbs u, z.natAbs ≤ 65535 := by
  intro z hz; have hb : u.toNat < 2 ^ 64 := u.toNat_lt
  simp only [decomposeUInt64Limbs, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> omega
/-- Flatten a list of `UInt64` words into `4 * words.length` short 16-bit integer limbs. -/
def wordsToLimbs (words : List UInt64) : List Int := words.flatMap decomposeUInt64Limbs
theorem wordsToLimbs_length (words : List UInt64) :
    (wordsToLimbs words).length = 4 * words.length := by
  unfold wordsToLimbs
  induction words with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, decomposeUInt64Limbs,
      List.cons_append, List.nil_append, List.length_cons, ih]; omega
theorem wordsToLimbs_short (words : List UInt64) : ShortNormBound 65535 (wordsToLimbs words) := by
  unfold ShortNormBound; apply Obend.Crypto.normInf_le_of_forall
  intro z hz; unfold wordsToLimbs at hz
  obtain ⟨u, _, hzu⟩ := List.mem_flatMap.1 hz
  exact decomposeUInt64Limbs_short u z hzu
theorem wordsToLimbs_injective : ∀ {l₁ l₂ : List UInt64},
    wordsToLimbs l₁ = wordsToLimbs l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [wordsToLimbs, decomposeUInt64Limbs] at h
  | _ :: _, [], h => by simp [wordsToLimbs, decomposeUInt64Limbs] at h
  | u :: us, v :: vs, h => by
    simp only [wordsToLimbs, List.flatMap_cons, decomposeUInt64Limbs,
      List.cons_append, List.nil_append, List.cons.injEq] at h
    rcases h with ⟨h0, h1, h2, h3, hrest⟩
    have huv : u = v := decomposeUInt64Limbs_injective (by
      simp [decomposeUInt64Limbs, h0, h1, h2, h3])
    rw [huv, wordsToLimbs_injective hrest]
/-- Convert a 16-slot `ChunkData` to its 64-coordinate short Ajtai witness (`‖w‖_∞ ≤ 65535`). -/
def chunkToLimbs (c : ChunkData) : List Int := wordsToLimbs c.slots.toList
theorem chunkToLimbs_length (c : ChunkData) : (chunkToLimbs c).length = 64 := by
  unfold chunkToLimbs; rw [wordsToLimbs_length, Array.length_toList, c.size_eq]; rfl
theorem chunkToLimbs_short (c : ChunkData) : Short 64 65535 (chunkToLimbs c) :=
  ⟨chunkToLimbs_length c, wordsToLimbs_short c.slots.toList⟩
/-- Compute the modular Ajtai commitment $\mathbf{A} \cdot \text{limbs}(c) \bmod q$ of chunk `c`. -/
def ajtaiChunkCommit (pp : AjtaiParams) (hCols : pp.cols = 64) (c : ChunkData) : List Int :=
  ajtaiCommit pp (chunkToLimbs c) ((chunkToLimbs_length c).trans hCols.symm)
/-- Default concrete `AjtaiParams` (`arity = 4`, `rows = 16`, `cols = 64`, `modulus = 262141^4`). -/
def defaultChunkAjtaiParams : AjtaiParams := inhabitedAjtaiParams 4
theorem defaultChunkAjtaiParams_cols : defaultChunkAjtaiParams.cols = 64 := (inhabitedAjtaiParams_sisHard 4).1
/-- **Inhabitedness / Non-Vacuity Theorem (`dualChunkParams_inhabited_sisHard`)**:
    `defaultChunkAjtaiParams` satisfies `cols = 64`, `NonPigeonholeSISParams`, and `ModuleSISHard` (`0` axioms). -/
theorem dualChunkParams_inhabited_sisHard :
    defaultChunkAjtaiParams.cols = 64 ∧ NonPigeonholeSISParams defaultChunkAjtaiParams ∧
    ModuleSISHard defaultChunkAjtaiParams 131070 := inhabitedAjtaiParams_sisHard 4
/-! ## 4. `AuthenticatedWorldSnapshot`, Incremental Root Update & Point Openings -/
/-- Persistent COW world snapshot pairing `ChunkedWorld.World` with its 256-chunk table,
    cached level-1/level-2 `VerkleUmem` tags, 256-bit `verkleRoot`, and per-chunk Ajtai roots. -/
structure AuthenticatedWorldSnapshot where
  world : ChunkedWorld.World
  branchGen : Nat
  chunks : Array ChunkData
  chunkRoots : Array ByteArray
  groupRoots : Array ByteArray
  activeRoot : ByteArray
  verkleRoot : ByteArray
  ajtaiChunkRoots : Array (List Int)
  deriving DecidableEq
/-- Structural invariant relating cached internal tags of `s` to `s.chunks`. -/
def SnapshotWF (pp : AjtaiParams) (hCols : pp.cols = 64) (s : AuthenticatedWorldSnapshot) : Prop :=
  s.chunks.size = numChunks ∧ s.chunkRoots.size = numChunks ∧
  s.groupRoots.size = numGroups ∧ s.ajtaiChunkRoots.size = numChunks ∧
  (∀ c : Nat, c < numChunks → s.chunkRoots.getD c ByteArray.empty = chunkSubtreeTag (s.chunks.getD c zeroChunk)) ∧
  (∀ g : Nat, g < numGroups → s.groupRoots.getD g ByteArray.empty = groupSubtreeTag s.chunkRoots g) ∧
  s.activeRoot = nodeTag s.groupRoots.toList ∧ s.verkleRoot = liftActiveToRoot s.activeRoot ∧
  (∀ c : Nat, c < numChunks → s.ajtaiChunkRoots.getD c [] = ajtaiChunkCommit pp hCols (s.chunks.getD c zeroChunk))
private theorem snapshotWF_with_world {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) (w' : ChunkedWorld.World) :
    SnapshotWF pp hCols { s with world := w' } := hwf
/-- Build an `AuthenticatedWorldSnapshot` from `chunks` and `w`. -/
def buildSnapshotFromChunks (pp : AjtaiParams) (hCols : pp.cols = 64)
    (w : ChunkedWorld.World) (chunks : Array ChunkData) (gen : Nat := 0) : AuthenticatedWorldSnapshot :=
  let normChunks := ((List.range numChunks).map fun c => chunks.getD c zeroChunk).toArray
  let cRoots := ((List.range numChunks).map fun c => chunkSubtreeTag (normChunks.getD c zeroChunk)).toArray
  let gRoots := ((List.range numGroups).map fun g => groupSubtreeTag cRoots g).toArray
  let act := nodeTag gRoots.toList
  let aRoots := ((List.range numChunks).map fun c => ajtaiChunkCommit pp hCols (normChunks.getD c zeroChunk)).toArray
  { world := w, branchGen := gen, chunks := normChunks, chunkRoots := cRoots,
    groupRoots := gRoots, activeRoot := act, verkleRoot := liftActiveToRoot act, ajtaiChunkRoots := aRoots }
/-- Build the canonical `AuthenticatedWorldSnapshot` of `w : ChunkedWorld.World`. -/
def buildAuthenticatedSnapshot (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    AuthenticatedWorldSnapshot := buildSnapshotFromChunks pp hCols w (materializeWorldChunks w) 0
theorem buildSnapshotFromChunks_wf (pp : AjtaiParams) (hCols : pp.cols = 64)
    (w : ChunkedWorld.World) (chunks : Array ChunkData) (gen : Nat) :
    SnapshotWF pp hCols (buildSnapshotFromChunks pp hCols w chunks gen) := by
  unfold SnapshotWF buildSnapshotFromChunks; dsimp only
  refine ⟨by simp, by simp, by simp, by simp, ?_, ?_, rfl, rfl, ?_⟩
  · intro c hc; rw [getD_lt _ c ByteArray.empty (by simp; exact hc)]; simp
  · intro g hg; rw [getD_lt _ g ByteArray.empty (by simp; exact hg)]; simp
  · intro c hc; rw [getD_lt _ c [] (by simp; exact hc)]; simp
theorem buildAuthenticatedSnapshot_wf (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    SnapshotWF pp hCols (buildAuthenticatedSnapshot pp hCols w) :=
  buildSnapshotFromChunks_wf pp hCols w (materializeWorldChunks w) 0
theorem snapshotWF_verkleRoot_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) :
    s.verkleRoot = fullVerkleCommitChunks s.chunks := by
  obtain ⟨_, hrsz, hgsz, _, hcEq, hgEq, hact, hroot, _⟩ := hwf
  unfold fullVerkleCommitChunks; dsimp only; rw [hroot, hact]
  apply congrArg liftActiveToRoot; apply congrArg nodeTag
  have hcArr : s.chunkRoots = ((List.range numChunks).map fun c =>
      chunkSubtreeTag (s.chunks.getD c zeroChunk)).toArray := by
    apply Array.ext (by simp [hrsz]); intro c hc1 _
    rw [← getD_lt s.chunkRoots c ByteArray.empty hc1, hcEq c (by rw [hrsz] at hc1; exact hc1)]; simp
  rw [← hcArr]
  apply List.ext_getElem (by simp [hgsz]); intro g _ hg2
  have hglt : g < numGroups := by simp at hg2; exact hg2
  rw [Array.getElem_toList, ← getD_lt s.groupRoots g ByteArray.empty (by rw [hgsz]; exact hglt), hgEq g hglt]; simp
theorem buildAuthenticatedSnapshot_verkleRoot (pp : AjtaiParams) (hCols : pp.cols = 64) (w : ChunkedWorld.World) :
    (buildAuthenticatedSnapshot pp hCols w).verkleRoot = fullVerkleCommitWorld w := by
  rw [snapshotWF_verkleRoot_eq_fullCommit (buildAuthenticatedSnapshot_wf pp hCols w)]
  unfold buildAuthenticatedSnapshot buildSnapshotFromChunks fullVerkleCommitWorld; dsimp only
  apply congrArg fullVerkleCommitChunks; apply Array.ext (by simp [materializeWorldChunks_size])
  intro c _ hc2
  rw [List.getElem_toArray, List.getElem_map, List.getElem_range, getD_lt (materializeWorldChunks w) c zeroChunk hc2]
/-- **Incremental Single-Chunk Update**: recomputes only dirty chunk `c`'s tag, its 16-chunk group
    tag, the $O(\log K)$ upper spine, and its Ajtai chunk commitment. -/
def updateChunkVerkleRoot (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (c : Nat) (_hc : c < numChunks)
    (newChunk : ChunkData) : AuthenticatedWorldSnapshot :=
  let chunks' := s.chunks.setIfInBounds c newChunk
  let newChunkTag := chunkSubtreeTag newChunk
  let cRoots' := s.chunkRoots.setIfInBounds c newChunkTag
  let g := c / 16
  let gRoots' := s.groupRoots.setIfInBounds g (groupSubtreeTag cRoots' g)
  let act' := nodeTag gRoots'.toList
  let aRoots' := s.ajtaiChunkRoots.setIfInBounds c (ajtaiChunkCommit pp hCols newChunk)
  { s with chunks := chunks', chunkRoots := cRoots', groupRoots := gRoots',
           activeRoot := act', verkleRoot := liftActiveToRoot act', ajtaiChunkRoots := aRoots' }
private theorem getD_setIfInBounds_eq {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (hi : i < xs.size) : (xs.setIfInBounds i v).getD i d = v := by unfold Array.getD; simp [hi]
private theorem getD_setIfInBounds_ne {α : Type} (xs : Array α) (i j : Nat) (v d : α)
    (hne : j ≠ i) : (xs.setIfInBounds i v).getD j d = xs.getD j d := by
  unfold Array.getD
  by_cases hj : j < xs.size
  · simp [hj, Ne.symm hne]
  · simp [hj]
theorem updateChunkVerkleRoot_wf {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    SnapshotWF pp hCols (updateChunkVerkleRoot pp hCols s c hc newChunk) := by
  obtain ⟨hcsz, hrsz, hgsz, hasz, hcEq, hgEq, _, _, haEq⟩ := hwf
  unfold SnapshotWF updateChunkVerkleRoot; dsimp only
  refine ⟨by simp [hcsz], by simp [hrsz], by simp [hgsz], by simp [hasz], ?_, ?_, rfl, rfl, ?_⟩
  · intro c' hc'
    by_cases heq : c' = c
    · subst heq
      rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hrsz]; exact hc),
          getD_setIfInBounds_eq _ _ _ _ (by rw [hcsz]; exact hc)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ heq, getD_setIfInBounds_ne _ _ _ _ _ heq, hcEq c' hc']
  · intro g' hg'
    have hglt : c / 16 < numGroups := by unfold numChunks numGroups at *; omega
    by_cases hgeq : g' = c / 16
    · subst hgeq; rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hgsz]; exact hglt)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ hgeq, hgEq g' hg']
      unfold groupSubtreeTag groupChunkTags; apply congrArg nodeTag; apply List.map_congr_left
      intro d hd
      have hdlt : d < 16 := List.mem_range.mp hd
      have hne : g' * 16 + d ≠ c := by intro e; apply hgeq; omega
      exact (getD_setIfInBounds_ne _ _ _ _ _ hne).symm
  · intro c' hc'
    by_cases heq : c' = c
    · subst heq
      rw [getD_setIfInBounds_eq _ _ _ _ (by rw [hasz]; exact hc),
          getD_setIfInBounds_eq _ _ _ _ (by rw [hcsz]; exact hc)]
    · rw [getD_setIfInBounds_ne _ _ _ _ _ heq, getD_setIfInBounds_ne _ _ _ _ _ heq, haEq c' hc']
/-- **Headline Theorem 1**: `updateChunkVerkleRoot` on any chunk `c < 256` preserves `SnapshotWF`,
    yields a 32-byte root, and equals `fullVerkleCommitChunks` and `specExtRamTreeTag`. -/
theorem incrementalVerkleSnapshot_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    let s' := updateChunkVerkleRoot pp hCols s c hc newChunk
    SnapshotWF pp hCols s' ∧
    s'.verkleRoot.size = 32 ∧
    s'.verkleRoot = fullVerkleCommitChunks (s.chunks.setIfInBounds c newChunk) ∧
    s'.verkleRoot = specExtRamTreeTag (chunksToExtRam (s.chunks.setIfInBounds c newChunk)) 16 0 := by
  have hwf' := updateChunkVerkleRoot_wf hwf c hc newChunk
  have hfull := snapshotWF_verkleRoot_eq_fullCommit hwf'
  refine ⟨hwf', ?_, hfull, hfull.trans (fullVerkleCommitChunks_eq_specExtRamRoot _)⟩
  rw [hfull]; exact fullVerkleCommitChunks_size _
private def syncStep (pp : AjtaiParams) (hCols : pp.cols = 64)
    (target : Array ChunkData) (acc : AuthenticatedWorldSnapshot) (c : Nat) :
    AuthenticatedWorldSnapshot :=
  if hc : c < numChunks then
    let nextChunk := target.getD c zeroChunk
    if acc.chunks.getD c zeroChunk == nextChunk then acc
    else updateChunkVerkleRoot pp hCols acc c hc nextChunk
  else acc
/-- Sync a snapshot to a new `ChunkedWorld.World` `w'` by updating **only** modified chunks. -/
def syncSnapshotWorld (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (w' : ChunkedWorld.World) : AuthenticatedWorldSnapshot :=
  let s1 := (List.range numChunks).foldl (syncStep pp hCols (materializeWorldChunks w')) s
  { s1 with world := w' }
private theorem syncStep_props {pp : AjtaiParams} {hCols : pp.cols = 64}
    (target : Array ChunkData) {acc : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols acc)
    (idx : Nat) :
    SnapshotWF pp hCols (syncStep pp hCols target acc idx) ∧
    (idx < numChunks →
      (syncStep pp hCols target acc idx).chunks.getD idx zeroChunk = target.getD idx zeroChunk) ∧
    (∀ c, c ≠ idx →
      (syncStep pp hCols target acc idx).chunks.getD c zeroChunk = acc.chunks.getD c zeroChunk) := by
  unfold syncStep
  split
  · rename_i hc
    dsimp only
    split
    · rename_i heq
      exact ⟨hwf, fun _ => beq_iff_eq.mp heq, fun _ _ => rfl⟩
    · refine ⟨updateChunkVerkleRoot_wf hwf idx hc _, fun _ => ?_, fun c hne => ?_⟩
      · unfold updateChunkVerkleRoot
        exact getD_setIfInBounds_eq acc.chunks idx _ zeroChunk (by rw [hwf.1]; exact hc)
      · unfold updateChunkVerkleRoot
        exact getD_setIfInBounds_ne acc.chunks idx c _ zeroChunk hne
  · rename_i hnc
    exact ⟨hwf, fun h => (hnc h).elim, fun _ _ => rfl⟩
private theorem syncFold_preserves {pp : AjtaiParams} {hCols : pp.cols = 64}
    (target : Array ChunkData) (idxs : List Nat) :
    ∀ (acc : AuthenticatedWorldSnapshot), SnapshotWF pp hCols acc →
      SnapshotWF pp hCols (idxs.foldl (syncStep pp hCols target) acc) ∧
      (∀ c ∈ idxs, c < numChunks →
        (idxs.foldl (syncStep pp hCols target) acc).chunks.getD c zeroChunk =
          target.getD c zeroChunk) ∧
      (∀ c, c ∉ idxs → (idxs.foldl (syncStep pp hCols target) acc).chunks.getD c zeroChunk =
          acc.chunks.getD c zeroChunk) := by
  induction idxs with
  | nil =>
    intro acc hwf
    refine ⟨hwf, ?_, ?_⟩
    · intro _ hm; cases hm
    · intro _ _; rfl
  | cons idx rest ih =>
    intro acc hwf
    obtain ⟨hwf1, hEq1, hNe1⟩ := syncStep_props target hwf idx
    obtain ⟨hwf2, hIn2, hOut2⟩ := ih (syncStep pp hCols target acc idx) hwf1
    simp only [List.foldl_cons]
    refine ⟨hwf2, ?_, ?_⟩
    · intro c hmem hclt
      by_cases hcr : c ∈ rest
      · exact hIn2 c hcr hclt
      · rcases List.mem_cons.1 hmem with rfl | hcr'
        · rw [hOut2 c hcr]; exact hEq1 hclt
        · exact (hcr hcr').elim
    · intro c hnot
      have hnotIdx : c ≠ idx := fun e => hnot (List.mem_cons.2 (.inl e))
      have hnotRest : c ∉ rest := fun hm => hnot (List.mem_cons.2 (.inr hm))
      rw [hOut2 c hnotRest, hNe1 c hnotIdx]
theorem syncSnapshotWorld_wf_and_eq_fullCommit {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s) (w' : ChunkedWorld.World) :
    let s' := syncSnapshotWorld pp hCols s w'
    SnapshotWF pp hCols s' ∧ s'.world = w' ∧ s'.verkleRoot = fullVerkleCommitWorld w' := by
  unfold syncSnapshotWorld; dsimp only
  obtain ⟨hwf1, hIn, _⟩ := syncFold_preserves (materializeWorldChunks w') (List.range numChunks) s hwf
  generalize hs1 :
    (List.range numChunks).foldl (syncStep pp hCols (materializeWorldChunks w')) s = s1 at hwf1 hIn ⊢
  have hwf' : SnapshotWF pp hCols { s1 with world := w' } := snapshotWF_with_world hwf1 w'
  refine ⟨hwf', rfl, ?_⟩
  have hchunksEq : s1.chunks = materializeWorldChunks w' := by
    apply Array.ext
    · rw [hwf1.1, materializeWorldChunks_size]
    · intro c hc1 hc2
      have hclt : c < numChunks := by rw [hwf1.1] at hc1; exact hc1
      rw [← getD_lt s1.chunks c zeroChunk hc1, ← getD_lt (materializeWorldChunks w') c zeroChunk hc2]
      exact hIn c (List.mem_range.mpr hclt) hclt
  have hroot := snapshotWF_verkleRoot_eq_fullCommit hwf'
  dsimp only at hroot
  rw [hroot, hchunksEq]; rfl
/-! ### Stateless 16-Level `VerkleUmem` Point Openings From Cached Snapshot Subtrees -/
/-- Read slot `(c, j)` of `s` (`0` out of bounds). -/
def AuthenticatedWorldSnapshot.readSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : UInt64 :=
  (s.chunks.getD c zeroChunk).getSlot j
/-- Build the 16-level `Obend.Polis.verifyOpening` sibling path for slot `(c, j)`. -/
def openSnapshotSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : Array (Array ByteArray) :=
  let chunk := s.chunks.getD c zeroChunk
  let sib0 := ((chunk.slots.toList.map leafTag).eraseIdx j).toArray
  let sib1 := ((groupChunkTags s.chunkRoots (c / 16)).eraseIdx (c % 16)).toArray
  let sib2 := (s.groupRoots.toList.eraseIdx (c / 16)).toArray
  let upper := (List.range 13).map fun k => Array.replicate 15 (zeroTreeTag (3 + k))
  (sib0 :: sib1 :: sib2 :: upper).toArray
private theorem insertAt_eraseIdx : ∀ (xs : List ByteArray) (n : Nat) (hn : n < xs.length),
    insertAt n (xs[n]'hn) (xs.eraseIdx n) = xs
  | [], _, hn => by simp at hn
  | _ :: _, 0, _ => rfl
  | x :: xs, n + 1, hn => by
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, insertAt,
      List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (x :: ·) (insertAt_eraseIdx xs n (Nat.lt_of_succ_lt_succ hn))
private theorem eraseIdx_length_of_lt : ∀ (xs : List ByteArray) (n : Nat),
    n < xs.length → (xs.eraseIdx n).length = xs.length - 1
  | [], _, hn => by simp at hn
  | _ :: _, 0, _ => by simp
  | _ :: xs, n + 1, hn => by
    have ih := eraseIdx_length_of_lt xs n (Nat.lt_of_succ_lt_succ hn)
    have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_succ_lt_succ hn)
    simp only [List.eraseIdx_cons_succ, List.length_cons, ih]; omega
private theorem climb_upper_zeroSpine (addr : UInt64) (haddr : addr.toNat < totalSlots) :
    ∀ (steps lvl : Nat) (cur : ByteArray), 3 ≤ lvl → List.foldlM (climbStep addr) (lvl, cur)
        ((List.range steps).map fun k => Array.replicate 15 (zeroTreeTag (lvl + k))) =
        some (lvl + steps, liftSpineFrom lvl steps cur)
  | 0, lvl, cur, _ => by simp [liftSpineFrom]
  | steps + 1, lvl, cur, hlvl => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    have hshift : (fun x => Array.replicate 15 (zeroTreeTag (lvl + (x + 1)))) =
        (fun k => Array.replicate 15 (zeroTreeTag ((lvl + 1) + k))) := by
      funext k; congr 2; omega
    rw [hshift, Obend.Polis.foldlM_cons_some]
    have hnib : nibbleAt addr lvl = 0 := by
      unfold nibbleAt
      have hpow : totalSlots ≤ 16 ^ lvl := by
        have h3 : totalSlots = 16 ^ 3 := by decide
        rw [h3]; exact Nat.pow_le_pow_right (by decide) hlvl
      have hdiv : addr.toNat / 16 ^ lvl = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le haddr hpow)
      simp [hdiv]
    refine ⟨(lvl + 1, nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))), ?_, ?_⟩
    · unfold climbStep; simp [hnib, insertAt]
    · have ih := climb_upper_zeroSpine addr haddr steps (lvl + 1)
        (nodeTag (cur :: List.replicate 15 (zeroTreeTag lvl))) (by omega)
      have hadd : lvl + 1 + steps = lvl + (steps + 1) := by omega
      rwa [hadd] at ih
/-- **Snapshot Opening Completeness**: every slot `(c, j)` (`c < 256`, `j < 16`) of a well-formed
    snapshot has a 16-level sibling path accepted by `Obend.Polis.verifyOpening`. -/
theorem openSnapshotSlot_valid {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    verifyOpening s.verkleRoot (slotAddr c j) (s.readSlot c j) (openSnapshotSlot s c j) = true := by
  obtain ⟨_, hrsz, hgsz, _, hcEq, hgEq, hact, hroot, _⟩ := hwf
  rw [Obend.Polis.verifyOpening_iff]
  refine ⟨by simp [openSnapshotSlot], 16, ?_⟩
  unfold climb openSnapshotSlot
  rw [← Array.foldlM_toList]
  dsimp only
  have haddrNat := slotAddr_toNat hc hj
  have haddrTot : (slotAddr c j).toNat < totalSlots := by
    rw [haddrNat]; unfold numChunks chunkSlots totalSlots at *; omega
  have hnib0 : nibbleAt (slotAddr c j) 0 = j := by
    unfold nibbleAt; rw [haddrNat]; unfold chunkSlots at *; omega
  have hnib1 : nibbleAt (slotAddr c j) 1 = c % 16 := by
    unfold nibbleAt; rw [haddrNat]; unfold chunkSlots at *; omega
  have hnib2 : nibbleAt (slotAddr c j) 2 = c / 16 := by
    unfold nibbleAt; rw [haddrNat]; unfold numChunks chunkSlots at *; omega
  have hxs0Len : ((s.chunks.getD c zeroChunk).slots.toList.map leafTag).length = 16 := by
    rw [List.length_map, Array.length_toList, (s.chunks.getD c zeroChunk).size_eq]; rfl
  have hjxs0 : j < ((s.chunks.getD c zeroChunk).slots.toList.map leafTag).length := by
    rw [hxs0Len]; exact hj
  have hxs0Get : ((s.chunks.getD c zeroChunk).slots.toList.map leafTag)[j]'hjxs0 =
      leafTag (s.readSlot c j) := by
    rw [List.getElem_map]; apply congrArg leafTag
    unfold AuthenticatedWorldSnapshot.readSlot ChunkData.getSlot
    have hjsz : j < (s.chunks.getD c zeroChunk).slots.size := by
      rw [(s.chunks.getD c zeroChunk).size_eq]; exact hj
    rw [getD_lt _ j 0 hjsz]; simp
  rw [Obend.Polis.foldlM_cons_some]
  refine ⟨(1, s.chunkRoots.getD c ByteArray.empty), ?_, ?_⟩
  · unfold climbStep
    have hsz0 : (((s.chunks.getD c zeroChunk).slots.toList.map leafTag).eraseIdx j).toArray.size = 15 := by
      rw [List.size_toArray, eraseIdx_length_of_lt _ j hjxs0, hxs0Len]
    simp only [hsz0, ↓reduceIte, hnib0, ← hxs0Get]
    rw [insertAt_eraseIdx _ j hjxs0, hcEq c hc]; rfl
  · have hxs1Len : (groupChunkTags s.chunkRoots (c / 16)).length = 16 := by simp [groupChunkTags]
    have hm16 : c % 16 < (groupChunkTags s.chunkRoots (c / 16)).length := by rw [hxs1Len]; omega
    have hxs1Get : (groupChunkTags s.chunkRoots (c / 16))[c % 16]'hm16 =
        s.chunkRoots.getD c ByteArray.empty := by
      rw [groupChunkTags_getElem s.chunkRoots (c / 16) (c % 16) (by omega)]
      have hdivmod : c / 16 * 16 + c % 16 = c := by omega
      rw [hdivmod]
      have hcrLt : c < s.chunkRoots.size := by rw [hrsz]; exact hc
      rw [getD_lt s.chunkRoots c (zeroTreeTag 1) hcrLt, getD_lt s.chunkRoots c ByteArray.empty hcrLt]
    have hglt : c / 16 < numGroups := by unfold numChunks numGroups at *; omega
    rw [Obend.Polis.foldlM_cons_some]
    refine ⟨(2, s.groupRoots.getD (c / 16) ByteArray.empty), ?_, ?_⟩
    · unfold climbStep
      have hsz1 : ((groupChunkTags s.chunkRoots (c / 16)).eraseIdx (c % 16)).toArray.size = 15 := by
        rw [List.size_toArray, eraseIdx_length_of_lt _ (c % 16) hm16, hxs1Len]
      simp only [hsz1, ↓reduceIte, hnib1, ← hxs1Get]
      rw [insertAt_eraseIdx _ (c % 16) hm16, hgEq (c / 16) hglt]; rfl
    · have hxs2Len : s.groupRoots.toList.length = 16 := by rw [Array.length_toList, hgsz]; rfl
      have hgxs2 : c / 16 < s.groupRoots.toList.length := by rw [hxs2Len]; exact hglt
      have hxs2Get : s.groupRoots.toList[c / 16]'hgxs2 =
          s.groupRoots.getD (c / 16) ByteArray.empty := by
        rw [Array.getElem_toList, getD_lt s.groupRoots (c / 16) ByteArray.empty (by rw [hgsz]; exact hglt)]
      rw [Obend.Polis.foldlM_cons_some]
      refine ⟨(3, s.activeRoot), ?_, ?_⟩
      · unfold climbStep
        have hsz2 : (s.groupRoots.toList.eraseIdx (c / 16)).toArray.size = 15 := by
          rw [List.size_toArray, eraseIdx_length_of_lt _ (c / 16) hgxs2, hxs2Len]
        simp only [hsz2, ↓reduceIte, hnib2, ← hxs2Get]
        rw [insertAt_eraseIdx _ (c / 16) hgxs2, hact]
      · rw [hroot]
        exact climb_upper_zeroSpine (slotAddr c j) haddrTot 13 3 s.activeRoot (by decide)
/-! ## 5. $O(1)$ COW Snapshot Forking, Subtree Sharing & Dual-Track Binding -/
/-- Fork `s` in $O(1)$ by bumping `branchGen` while structurally sharing all persistent arrays. -/
def cowForkSnapshot (s : AuthenticatedWorldSnapshot) : AuthenticatedWorldSnapshot :=
  { s with branchGen := s.branchGen + 1 }
/-- Fork `s` and apply a COW update to a single dirty chunk `c < 256` (`O(\log K)` hashes). -/
def cowUpdateChunk (pp : AjtaiParams) (hCols : pp.cols = 64)
    (s : AuthenticatedWorldSnapshot) (c : Nat) (hc : c < numChunks)
    (newChunk : ChunkData) : AuthenticatedWorldSnapshot :=
  updateChunkVerkleRoot pp hCols (cowForkSnapshot s) c hc newChunk
/-- Rebind a pre-branch slot opening's level-0 intra-chunk sibling witness (`prePath[0]`) onto
    `postBranch`'s updated upper spine (`levels 1..15`) without reading `postBranch.chunks[c']`. -/
def rebindPreBranchChunkOpening (prePath : Array (Array ByteArray))
    (postBranch : AuthenticatedWorldSnapshot) (c' : Nat) : Array (Array ByteArray) :=
  let sib0 := prePath.getD 0 #[]
  let sib1 := ((groupChunkTags postBranch.chunkRoots (c' / 16)).eraseIdx (c' % 16)).toArray
  let sib2 := (postBranch.groupRoots.toList.eraseIdx (c' / 16)).toArray
  let upper := (List.range 13).map fun k => Array.replicate 15 (zeroTreeTag (3 + k))
  (sib0 :: sib1 :: sib2 :: upper).toArray
/-- Every sibling tag at every level of `path` has arity `15` and exact byte width `32`. -/
def checkWellSizedVerklePath (path : Array (Array ByteArray)) : Bool :=
  path.size == 16 &&
  path.toList.all fun sibs => sibs.size == 15 && sibs.toList.all fun b => b.size == 32
/-- A bounded witness pinned to the two finite input sets actually hashed. -/
abbrev PathCollision (left right : List (List UInt8)) :=
  { w : HashCollisionWitness treeHash verkleMaxPreimageBytes //
    w.msgA ∈ left ∧ w.msgB ∈ right }
def PathCollision.weaken {a b c d : List (List UInt8)} (w : PathCollision a b)
    (ha : a ⊆ c) (hb : b ⊆ d) : PathCollision c d :=
  ⟨w.val, ha w.property.1, hb w.property.2⟩
theorem PathCollision.toCollisionAmong {a b : List (List UInt8)} (w : PathCollision a b) :
    Obend.Digest.HashBytes.CollisionAmong treeHash (fun x => x ∈ a ∨ x ∈ b) :=
  ⟨w.val.msgA, w.val.msgB, .inl w.property.1, .inr w.property.2,
    w.val.distinct, w.val.sameDigest⟩
/-- All node preimages on the supplied path, in hashing order. -/
def climbPreimages (addr : UInt64) : Nat → ByteArray → List (Array ByteArray) → List (List UInt8)
  | _, _, [] => []
  | lvl, cur, sib :: rest =>
    let p := nodePreimage (insertAt (nibbleAt addr lvl) cur sib.toList)
    p :: climbPreimages addr (lvl + 1) (tagOf p) rest
/-- Two distinct bounded preimages under one `tagOf` are a named `treeHash` collision. -/
private def mkTagCollision {p q : List UInt8} (hp : p.length ≤ verkleMaxPreimageBytes)
    (hq : q.length ≤ verkleMaxPreimageBytes) (hne : p ≠ q) (h : tagOf p = tagOf q) :
    HashCollisionWitness treeHash verkleMaxPreimageBytes where
  msgA := p
  msgB := q
  lenA := hp
  lenB := hq
  distinct := hne
  sameDigest := by
    have hl : (tagOf p).data.toList = (tagOf q).data.toList := congrArg (fun b => b.data.toList) h
    simp only [tagOf, cshake32ByteArray, Obend.Digest.Cshake256.Native.bytesOfList_toList] at hl
    exact congrArg ofBE hl
/-- Snapshot-root header preimage: tag byte `2` (leaves are `0`, nodes `1`), then the length-framed
    8-byte chunk count and the length-framed 32-byte `VerkleUmem` root. -/
def snapshotRootPreimage (n : Nat) (verkleRoot : ByteArray) : List UInt8 :=
  2 :: encodeFields [be 8 n, verkleRoot.data.toList]
/-- The snapshot root: the chunk count `n` and the Verkle root under one `treeHash` tag. -/
def snapshotRootTag (n : Nat) (verkleRoot : ByteArray) : ByteArray :=
  tagOf (snapshotRootPreimage n verkleRoot)
/-- The snapshot root of `s`, committing to its own chunk count. -/
def AuthenticatedWorldSnapshot.snapshotRoot (s : AuthenticatedWorldSnapshot) : ByteArray :=
  snapshotRootTag s.chunks.size s.verkleRoot
theorem snapshotRootPreimage_injective {n₁ n₂ : Nat} {r₁ r₂ : ByteArray}
    (hn₁ : n₁ < 2 ^ 64) (hn₂ : n₂ < 2 ^ 64)
    (h : snapshotRootPreimage n₁ r₁ = snapshotRootPreimage n₂ r₂) : n₁ = n₂ ∧ r₁ = r₂ := by
  simp only [snapshotRootPreimage, List.cons.injEq, true_and] at h
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact ⟨Obend.Digest.HashBytes.be_injective (h8 ▸ hn₁) (h8 ▸ hn₂) hf.1,
    (List.cons.inj (map_toList_injective [r₁] [r₂] (congrArg (fun x => [x]) hf.2))).1⟩
/-- **Snapshot-Root Binding (`0 Classical`)**: equal snapshot roots commit to the same chunk count
    and Verkle root, or their two header preimages are a named `treeHash` collision. -/
def extractSnapshotRootBreak {n₁ n₂ : Nat} {r₁ r₂ : ByteArray}
    (hn₁ : n₁ < 2 ^ 64) (hn₂ : n₂ < 2 ^ 64) (hr₁ : r₁.size = 32) (hr₂ : r₂.size = 32)
    (h : snapshotRootTag n₁ r₁ = snapshotRootTag n₂ r₂) :
    PSum (n₁ = n₂ ∧ r₁ = r₂)
      (PathCollision [snapshotRootPreimage n₁ r₁] [snapshotRootPreimage n₂ r₂]) :=
  have hlen : ∀ (n : Nat) (r : ByteArray), r.size = 32 →
      (snapshotRootPreimage n r).length ≤ verkleMaxPreimageBytes := by
    intro n r hr
    have hr' : r.data.toList.length = 32 := by rw [Array.length_toList]; exact hr
    have h8 : (leb128 8).length = 1 := by decide
    have h32 : (leb128 32).length = 1 := by decide
    simp [snapshotRootPreimage, encodeFields, encodeListField, hr', h8, h32, verkleMaxPreimageBytes]
  if heq : n₁ = n₂ ∧ r₁ = r₂ then .inl heq
  else .inr ⟨mkTagCollision (hlen n₁ r₁ hr₁) (hlen n₂ r₂ hr₂)
    (fun hp => heq (snapshotRootPreimage_injective hn₁ hn₂ hp)) h, .head _, .head _⟩
/-- Stateless dual-authenticated opening of slot `(c, j)` against `(snapshotRoot, ajtaiChunkRoot)`:
    the chunk's slots, the Verkle path, and the opened snapshot-root header `(chunkCount, verkleRoot)`. -/
structure DualChunkSlotOpening where
  chunkSlotsList : List UInt64
  verklePath : Array (Array ByteArray)
  chunkCount : Nat
  verkleRoot : ByteArray
  deriving DecidableEq
/-- Stateless dual verifier: chunk membership, well-sized Verkle path, Ajtai syndrome, the opened
    snapshot-root header, and the index bound `c < chunkCount` with `16 * chunkCount ≤ 2^64`, so
    `slotAddr c j` never wraps (an index `c + 2^60` is refused, not aliased to `c`). -/
def verifyDualChunkOpening (pp : AjtaiParams) (hCols : pp.cols = 64)
    (snapshotRoot : ByteArray) (ajtaiRoot : List Int)
    (c j : Nat) (val : UInt64) (w : DualChunkSlotOpening) : Bool :=
  if hlen : w.chunkSlotsList.length = 16 then
    if hj : j < 16 then
      let hw : (wordsToLimbs w.chunkSlotsList).length = pp.cols := by
        rw [wordsToLimbs_length, hlen, hCols]
      ((w.chunkSlotsList[j]'(by omega) == val) &&
       checkWellSizedVerklePath w.verklePath &&
       verifyOpening w.verkleRoot (slotAddr c j) val w.verklePath &&
       decide (ajtaiCommit pp (wordsToLimbs w.chunkSlotsList) hw = ajtaiRoot)) &&
      (decide (c < w.chunkCount) && decide (chunkSlots * w.chunkCount ≤ 2 ^ 64) &&
       w.verkleRoot.size == 32 &&
       decide (snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot))
    else false
  else false
/-- Produce the honest `DualChunkSlotOpening` for slot `(c, j)` of `s`. -/
def openDualSnapshotSlot (s : AuthenticatedWorldSnapshot) (c j : Nat) : DualChunkSlotOpening where
  chunkSlotsList := (s.chunks.getD c zeroChunk).slots.toList
  verklePath := openSnapshotSlot s c j
  chunkCount := s.chunks.size
  verkleRoot := s.verkleRoot
private theorem all_32_of_eraseIdx : ∀ (xs : List ByteArray) (n : Nat),
    (∀ b ∈ xs, b.size = 32) → ∀ b ∈ xs.eraseIdx n, b.size = 32
  | [], _, _, _, hm => by cases hm
  | _ :: xs, 0, h, b, hb => h b (.tail _ hb)
  | y :: xs, n + 1, h, b, hb => by
    rcases List.mem_cons.1 hb with heq | hb'
    · rw [heq]; exact h y (.head _)
    · exact all_32_of_eraseIdx xs n (fun z hz => h z (.tail _ hz)) b hb'
theorem openDualSnapshotSlot_valid {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {c j : Nat} (hc : c < numChunks) (hj : j < chunkSlots) :
    verifyDualChunkOpening pp hCols s.snapshotRoot (s.ajtaiChunkRoots.getD c [])
      c j (s.readSlot c j) (openDualSnapshotSlot s c j) = true := by
  have hopen := openSnapshotSlot_valid hwf hc hj
  have hroot32 : s.verkleRoot.size = 32 := by
    rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  obtain ⟨hcsz, hrsz, hgsz, _, hcEq, hgEq, _, _, haEq⟩ := hwf
  unfold verifyDualChunkOpening openDualSnapshotSlot AuthenticatedWorldSnapshot.snapshotRoot
  have hlen16 : ((s.chunks.getD c zeroChunk).slots.toList).length = 16 := by
    rw [Array.length_toList, (s.chunks.getD c zeroChunk).size_eq]; rfl
  have hj16 : j < 16 := hj
  simp only [hlen16, hj16, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, hopen⟩, ?_⟩, ⟨⟨hcsz ▸ hc, by rw [hcsz]; decide⟩, hroot32⟩, trivial⟩
  · unfold AuthenticatedWorldSnapshot.readSlot ChunkData.getSlot
    have hjsz : j < (s.chunks.getD c zeroChunk).slots.size := by
      rw [(s.chunks.getD c zeroChunk).size_eq]; exact hj
    rw [getD_lt _ j 0 hjsz]; simp
  · unfold checkWellSizedVerklePath openSnapshotSlot
    simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray, List.length_cons,
      List.length_map, List.length_range, List.all_cons, List.all_eq_true]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [eraseIdx_length_of_lt _ j (by rw [List.length_map, hlen16]; exact hj16),
            List.length_map, hlen16]
      · intro b hb
        apply all_32_of_eraseIdx ((s.chunks.getD c zeroChunk).slots.toList.map leafTag) j _ b hb
        intro y hy; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hy; exact leafTag_size _
    · refine ⟨?_, ?_⟩
      · rw [eraseIdx_length_of_lt _ (c % 16) (by simp [groupChunkTags]; omega)]
        simp [groupChunkTags]
      · intro b hb
        apply all_32_of_eraseIdx (groupChunkTags s.chunkRoots (c / 16)) (c % 16) _ b hb
        intro y hy; unfold groupChunkTags at hy
        obtain ⟨d, _, rfl⟩ := List.mem_map.1 hy
        by_cases hlt : c / 16 * 16 + d < s.chunkRoots.size
        · have hclt : c / 16 * 16 + d < numChunks := by rw [← hrsz]; exact hlt
          rw [getD_lt s.chunkRoots _ (zeroTreeTag 1) hlt,
              ← getD_lt s.chunkRoots _ ByteArray.empty hlt, hcEq _ hclt]
          exact chunkSubtreeTag_size _
        · unfold Array.getD; simp [hlt, zeroTreeTag_size]
    · refine ⟨?_, ?_⟩
      · have hgLen : s.groupRoots.toList.length = 16 := by rw [Array.length_toList, hgsz]; rfl
        have hglt : c / 16 < 16 := by unfold numChunks at hc; omega
        rw [eraseIdx_length_of_lt _ (c / 16) (by rw [hgLen]; exact hglt), hgLen]
      · intro b hb
        apply all_32_of_eraseIdx s.groupRoots.toList (c / 16) _ b hb
        intro y hy
        obtain ⟨g, hg, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hy)
        have hglt : g < numGroups := by rw [← hgsz]; exact hg
        rw [← getD_lt s.groupRoots g ByteArray.empty hg, hgEq g hglt]
        exact nodeTag_size _
    · intro sibs hsibs
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hsibs
      refine ⟨by simp, ?_⟩
      intro b hb
      have hb' : b = zeroTreeTag (3 + k) := by simpa [Array.toList_replicate] using hb
      rw [hb']; exact zeroTreeTag_size _
  · rw [haEq c hc]; rfl
private theorem encodeFields_32_length : ∀ (children : List ByteArray),
    (∀ b ∈ children, b.size = 32) →
    (encodeFields (children.map fun b => b.data.toList)).length = 33 * children.length
  | [], _ => rfl
  | b :: bs, hall => by
    have hb32 : b.data.toList.length = 32 := by rw [Array.length_toList]; exact hall b (.head _)
    have hleb32 : (leb128 32).length = 1 := by decide
    have ih := encodeFields_32_length bs (fun y hy => hall y (.tail _ hy))
    simp only [encodeFields, List.map_cons, List.flatMap_cons, encodeListField,
      List.length_append, hb32, hleb32, List.length_cons]
    change 1 + 32 + (encodeFields (bs.map fun x => x.data.toList)).length = 33 * (bs.length + 1)
    omega
private theorem nodePreimage_16_32_length {children : List ByteArray}
    (hlen : children.length = 16) (hall : ∀ b ∈ children, b.size = 32) :
    (nodePreimage children).length = verkleMaxPreimageBytes := by
  unfold nodePreimage verkleMaxPreimageBytes
  simp only [List.length_cons, encodeFields_32_length children hall, hlen]
private theorem insertAt_15_length_and_32 (n : Nat) {cur : ByteArray} {sibs : List ByteArray}
    (hcur : cur.size = 32) (hsibsLen : sibs.length = 15) (hsibs32 : ∀ b ∈ sibs, b.size = 32) :
    (insertAt n cur sibs).length = 16 ∧ ∀ b ∈ insertAt n cur sibs, b.size = 32 := by
  unfold insertAt
  refine ⟨?_, ?_⟩
  · have htd : (sibs.take n).length + (sibs.drop n).length = sibs.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.length_append, List.length_cons]; omega
  · intro b hb
    rcases List.mem_append.1 hb with hb1 | hb2
    · exact hsibs32 b (List.mem_of_mem_take hb1)
    · rcases List.mem_cons.1 hb2 with rfl | hb3
      · exact hcur
      · exact hsibs32 b (List.mem_of_mem_drop hb3)
private def mkNodeCollisionWitness (n : Nat) {c₁ c₂ : ByteArray} {s₁ s₂ : Array ByteArray}
    (hc1 : c₁.size = 32) (hc2 : c₂.size = 32)
    (hw1 : s₁.size = 15 ∧ ∀ b ∈ s₁.toList, b.size = 32)
    (hw2 : s₂.size = 15 ∧ ∀ b ∈ s₂.toList, b.size = 32) (hne : c₁ ≠ c₂)
    (htag : nodeTag (insertAt n c₁ s₁.toList) = nodeTag (insertAt n c₂ s₂.toList)) :
    PathCollision [nodePreimage (insertAt n c₁ s₁.toList)]
      [nodePreimage (insertAt n c₂ s₂.toList)] :=
  ⟨mkTagCollision
    (by obtain ⟨hl, ha⟩ := insertAt_15_length_and_32 n hc1 (by rw [Array.length_toList, hw1.1]) hw1.2
        exact Nat.le_of_eq (nodePreimage_16_32_length hl ha))
    (by obtain ⟨hl, ha⟩ := insertAt_15_length_and_32 n hc2 (by rw [Array.length_toList, hw2.1]) hw2.2
        exact Nat.le_of_eq (nodePreimage_16_32_length hl ha))
    (by intro hpre; simp only [nodePreimage, List.cons.injEq, true_and] at hpre
        have hch := map_toList_injective _ _ (encodeFields_injective _ _ hpre)
        have hszEq : s₁.toList.length = s₂.toList.length := by
          rw [Array.length_toList, Array.length_toList, hw1.1, hw2.1]
        exact hne (insertAt_inj hszEq hch).1)
    htag, .head _, .head _⟩
private theorem climbStep_tail_some {addr : UInt64} {lvl : Nat} {c : ByteArray}
    {s : Array ByteArray} {t : List (Array ByteArray)} {out : Nat × ByteArray}
    (h : List.foldlM (climbStep addr) (lvl, c) (s :: t) = some out) :
    List.foldlM (climbStep addr)
      (lvl + 1, nodeTag (insertAt (nibbleAt addr lvl) c s.toList)) t = some out := by
  obtain ⟨_, hs, hr⟩ := (Obend.Polis.foldlM_cons_some _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := Obend.Polis.climbStep_eq_some hs
  exact hr
/-- Constructive (`0 Classical`) climb collision extractor over 32-byte well-sized sibling paths. -/
private def extractClimbCollision (addr : UInt64) : ∀ (p₁ p₂ : List (Array ByteArray)) (lvl : Nat)
      (c₁ c₂ : ByteArray) (out₁ out₂ : Nat × ByteArray),
      p₁.length = p₂.length → c₁.size = 32 → c₂.size = 32 →
      (∀ s ∈ p₁, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32) →
      (∀ s ∈ p₂, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32) →
      List.foldlM (climbStep addr) (lvl, c₁) p₁ = some out₁ →
      List.foldlM (climbStep addr) (lvl, c₂) p₂ = some out₂ →
      out₁.2 = out₂.2 → c₁ ≠ c₂ →
      PathCollision (climbPreimages addr lvl c₁ p₁) (climbPreimages addr lvl c₂ p₂)
  | [], [], lvl, c₁, c₂, out₁, out₂, _, _, _, _, _, h₁, h₂, hout, hne =>
    False.elim (by
      have e₁ : some (lvl, c₁) = some out₁ := h₁
      have e₂ : some (lvl, c₂) = some out₂ := h₂
      cases e₁; cases e₂; exact hne hout)
  | [], _ :: _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => False.elim (Nat.noConfusion hlen)
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => False.elim (Nat.noConfusion hlen.symm)
  | s₁ :: t₁, s₂ :: t₂, lvl, c₁, c₂, out₁, out₂, hlen, hc1, hc2, hw1, hw2, h₁, h₂, hout, hne =>
    if htag : nodeTag (insertAt (nibbleAt addr lvl) c₁ s₁.toList) =
              nodeTag (insertAt (nibbleAt addr lvl) c₂ s₂.toList) then
      (mkNodeCollisionWitness (nibbleAt addr lvl) hc1 hc2
        (hw1 s₁ (.head _)) (hw2 s₂ (.head _)) hne htag).weaken
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact .head _)
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact .head _)
    else
      (extractClimbCollision addr t₁ t₂ (lvl + 1)
        (nodeTag (insertAt (nibbleAt addr lvl) c₁ s₁.toList))
        (nodeTag (insertAt (nibbleAt addr lvl) c₂ s₂.toList))
        out₁ out₂ (Nat.succ.inj hlen) (nodeTag_size _) (nodeTag_size _)
        (fun s hs => hw1 s (.tail _ hs)) (fun s hs => hw2 s (.tail _ hs))
        (climbStep_tail_some h₁) (climbStep_tail_some h₂) hout htag).weaken
          (fun _ hx => .tail _ hx) (fun _ hx => .tail _ hx)
private theorem foldlM_climbStep_fst (addr : UInt64) :
    ∀ (ps : List (Array ByteArray)) (lvl : Nat) (cur : ByteArray) (out : Nat × ByteArray),
      List.foldlM (climbStep addr) (lvl, cur) ps = some out → out.1 = lvl + ps.length
  | [], lvl, cur, out, h => by have e : some (lvl, cur) = some out := h; cases e; simp
  | _ :: t, lvl, _, out, h => by
    have ih := foldlM_climbStep_fst addr t (lvl + 1) _ out (climbStep_tail_some h)
    simp only [List.length_cons]; omega
private theorem verifyOpening_some16 {root : ByteArray} {addr val : UInt64}
    {path : Array (Array ByteArray)} (h : verifyOpening root addr val path = true) :
    path.size = 16 ∧
    List.foldlM (climbStep addr) (0, leafTag val) path.toList = some (16, root) := by
  obtain ⟨hsz, n, hc⟩ := (Obend.Polis.verifyOpening_iff root addr val path).1 h
  unfold climb at hc; rw [← Array.foldlM_toList] at hc
  have hn := foldlM_climbStep_fst addr path.toList 0 (leafTag val) (n, root) hc
  simp only [Nat.zero_add, Array.length_toList, hsz] at hn
  subst hn; exact ⟨hsz, hc⟩
private theorem verifyDualChunkOpening_props {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening}
    (hv : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true) :
    w.chunkSlotsList.length = 16 ∧
    j < 16 ∧
    w.chunkSlotsList.getD j 0 = v ∧
    checkWellSizedVerklePath w.verklePath = true ∧
    verifyOpening w.verkleRoot (slotAddr c j) v w.verklePath = true ∧
    (c < w.chunkCount ∧ chunkSlots * w.chunkCount ≤ 2 ^ 64 ∧ w.verkleRoot.size = 32 ∧
      snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot) ∧
    ∃ hw : (wordsToLimbs w.chunkSlotsList).length = pp.cols,
      ajtaiCommit pp (wordsToLimbs w.chunkSlotsList) hw = ajtaiRoot := by
  unfold verifyDualChunkOpening at hv
  by_cases hlen : w.chunkSlotsList.length = 16
  · by_cases hj : j < 16
    · simp only [hlen, hj, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      have hget : w.chunkSlotsList.getD j 0 = v := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact hv.1.1.1.1
      exact ⟨hlen, hj, hget, hv.1.1.1.2, hv.1.1.2,
        ⟨hv.2.1.1.1, hv.2.1.1.2, hv.2.1.2, hv.2.2⟩,
        ⟨by rw [wordsToLimbs_length, hlen, hCols], hv.1.2⟩⟩
    · simp [hlen, hj] at hv
  · simp [hlen] at hv
/-- What an accepted dual opening establishes about its opened snapshot-root header. -/
theorem verifyDualChunkOpening_header {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening} :
    verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true →
    c < w.chunkCount ∧ chunkSlots * w.chunkCount ≤ 2 ^ 64 ∧ w.verkleRoot.size = 32 ∧
    snapshotRootTag w.chunkCount w.verkleRoot = snapshotRoot :=
  fun hv => (verifyDualChunkOpening_props hv).2.2.2.2.2.1
/-- **No `UInt64` Wraparound (`verifyDualChunkOpening_addr_exact`)**: the key an accepted opening
    authenticates is exactly `16 * c + j`; no other chunk index shares it modulo `2^64`. -/
theorem verifyDualChunkOpening_addr_exact {pp : AjtaiParams} {hCols : pp.cols = 64}
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v : UInt64} {w : DualChunkSlotOpening} :
    verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v w = true →
    (slotAddr c j).toNat = c * chunkSlots + j := fun hv =>
  have hh := verifyDualChunkOpening_header hv
  slotAddr_toNat_of_bound hh.1 hh.2.1 (verifyDualChunkOpening_props hv).2.1
/-- **Chunk Index Bound (`0 Classical`)**: an opening accepted against a well-formed `s.snapshotRoot`
    addresses a real chunk (`c < 256`) under `s.verkleRoot`, or the two headers collide. -/
def extractSnapshotIndexBreak {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    {ajtaiRoot : List Int} {c j : Nat} {v : UInt64} {w : DualChunkSlotOpening}
    (hv : verifyDualChunkOpening pp hCols s.snapshotRoot ajtaiRoot c j v w = true) :
    PSum (c < numChunks ∧ w.verkleRoot = s.verkleRoot)
      (PathCollision [snapshotRootPreimage w.chunkCount w.verkleRoot]
        [snapshotRootPreimage s.chunks.size s.verkleRoot]) :=
  have hh := verifyDualChunkOpening_header hv
  have hroot32 : s.verkleRoot.size = 32 := by
    rw [snapshotWF_verkleRoot_eq_fullCommit hwf]; exact fullVerkleCommitChunks_size _
  match extractSnapshotRootBreak (by have := hh.2.1; unfold chunkSlots at this; omega)
      (by rw [hwf.1]; decide) hh.2.2.1 hroot32 hh.2.2.2 with
  | .inl heq => .inl ⟨by have := hh.1; rw [heq.1, hwf.1] at this; exact this, heq.2⟩
  | .inr col => .inr col
/-- Exactly the header, leaf and node preimages hashed for this opening. -/
def openingPreimages (c j : Nat) (v : UInt64) (w : DualChunkSlotOpening) : List (List UInt8) :=
  snapshotRootPreimage w.chunkCount w.verkleRoot :: leafPreimage v ::
    climbPreimages (slotAddr c j) 0 (leafTag v) w.verklePath.toList
def diffLimbs (w₁ w₂ : DualChunkSlotOpening) : List Int :=
  Obend.Crypto.vecSub (wordsToLimbs w₁.chunkSlotsList) (wordsToLimbs w₂.chunkSlotsList)
def SISBreakOn (pp : AjtaiParams) (z : List Int) : Prop :=
  0 < Obend.Judge.Computational.vecInfNorm z ∧
  Obend.Judge.Computational.vecInfNorm z ≤ 131070 ∧
  Obend.Judge.Computational.matVecModZero pp.modulus pp.matrix z = true
/-- **Constructive Dual-Opening Extractor (`0 Classical`)**: two accepted dual openings of slot
    `(c, j)` under one snapshot root agree on the value, or exhibit **both** a bounded `cSHAKE256`
    `HashCollisionWitness` (`≤ 529` bytes) **and** a short `SISShortVecWitness` (`‖z‖_∞ ≤ 131070`). -/
def extractDualChunkOpeningBreak (pp : AjtaiParams) (hCols : pp.cols = 64)
    {snapshotRoot : ByteArray} {ajtaiRoot : List Int} {c j : Nat}
    {v₁ v₂ : UInt64} {w₁ w₂ : DualChunkSlotOpening}
    (hv₁ : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v₁ w₁ = true)
    (hv₂ : verifyDualChunkOpening pp hCols snapshotRoot ajtaiRoot c j v₂ w₂ = true) :
    PSum (v₁ = v₂) (PathCollision (openingPreimages c j v₁ w₁) (openingPreimages c j v₂ w₂) ×
       { z : SISShortVecWitness pp.modulus 131070 pp.matrix // z.shortVec = diffLimbs w₁ w₂ }) :=
  if heq : v₁ = v₂ then .inl heq
  else
    .inr (
      let p₁ := verifyDualChunkOpening_props hv₁
      let p₂ := verifyDualChunkOpening_props hv₂
      let q₁ := verifyDualChunkOpening_header hv₁
      let q₂ := verifyDualChunkOpening_header hv₂
      let hw1 : PathCollision (openingPreimages c j v₁ w₁) (openingPreimages c j v₂ w₂) :=
        match extractSnapshotRootBreak (by have := q₁.2.1; unfold chunkSlots at this; omega)
            (by have := q₂.2.1; unfold chunkSlots at this; omega) q₁.2.2.1 q₂.2.2.1
            (q₁.2.2.2.trans q₂.2.2.2.symm) with
        | .inr col => col.weaken
            (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact .head _)
            (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact .head _)
        | .inl hhdr =>
        if hleaf : leafTag v₁ = leafTag v₂ then
          ⟨mkTagCollision (by simp [leafPreimage, verkleMaxPreimageBytes])
            (by simp [leafPreimage, verkleMaxPreimageBytes])
            (by intro hp; simp only [leafPreimage, List.cons.injEq, true_and] at hp
                have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
                exact heq (UInt64.toNat_inj.1
                  (Obend.Digest.HashBytes.be_injective (h8 ▸ v₁.toNat_lt) (h8 ▸ v₂.toNat_lt) hp)))
            hleaf, .tail _ (.head _), .tail _ (.head _)⟩
        else
          let op₁ := verifyOpening_some16 p₁.2.2.2.2.1
          let op₂ := verifyOpening_some16 (hhdr.2 ▸ p₂.2.2.2.2.1)
          have hwsProp : ∀ {p : Array (Array ByteArray)}, checkWellSizedVerklePath p = true →
              ∀ s ∈ p.toList, s.size = 15 ∧ ∀ b ∈ s.toList, b.size = 32 := by
            intro p hp s hs; unfold checkWellSizedVerklePath at hp
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp
            exact hp.2 s hs
          (extractClimbCollision (slotAddr c j) w₁.verklePath.toList w₂.verklePath.toList 0
            (leafTag v₁) (leafTag v₂) (16, w₁.verkleRoot) (16, w₁.verkleRoot)
            (by rw [Array.length_toList, Array.length_toList, op₁.1, op₂.1])
            (leafTag_size v₁) (leafTag_size v₂)
            (hwsProp p₁.2.2.2.1) (hwsProp p₂.2.2.2.1) op₁.2 op₂.2 rfl hleaf).weaken
              (fun _ hx => .tail _ (.tail _ hx)) (fun _ hx => .tail _ (.tail _ hx))
      let hw2 : { z : SISShortVecWitness pp.modulus 131070 pp.matrix //
          z.shortVec = diffLimbs w₁ w₂ } :=
        have huLen : (wordsToLimbs w₁.chunkSlotsList).length = pp.cols := by
          rw [wordsToLimbs_length, p₁.1, hCols]
        have hvLen : (wordsToLimbs w₂.chunkSlotsList).length = pp.cols := by
          rw [wordsToLimbs_length, p₂.1, hCols]
        have hneLimbs : wordsToLimbs w₁.chunkSlotsList ≠ wordsToLimbs w₂.chunkSlotsList := by
          intro hl; have hlEq := wordsToLimbs_injective hl
          apply heq; rw [← p₁.2.2.1, ← p₂.2.2.1, hlEq]
        ⟨extractShortDiffSISWitness pp
          (wordsToLimbs w₁.chunkSlotsList) (wordsToLimbs w₂.chunkSlotsList)
          huLen hvLen
          (wordsToLimbs_short w₁.chunkSlotsList) (wordsToLimbs_short w₂.chunkSlotsList)
          hneLimbs (by
            obtain ⟨_, h₁⟩ := p₁.2.2.2.2.2.2
            obtain ⟨_, h₂⟩ := p₂.2.2.2.2.2.2
            exact h₁.trans h₂.symm), rfl⟩
      (hw1, hw2))
/-- **Headline Theorem 2**: after a COW fork updating dirty chunk `c < 256`, (1) every chunk
    `c' ≠ c` shares its `ChunkData`, subtree tag, Ajtai commitment and rebound level-0 openings
    without rehashing; (2) two accepted dual openings of any slot against the branch's snapshot
    root agree, or identify a collision on these paths and their exact short difference in the kernel. -/
theorem cowBranch_shares_unchanged_verkleSubtrees {pp : AjtaiParams} {hCols : pp.cols = 64}
    {s : AuthenticatedWorldSnapshot} (hwf : SnapshotWF pp hCols s)
    (c : Nat) (hc : c < numChunks) (newChunk : ChunkData) :
    let branched := cowUpdateChunk pp hCols s c hc newChunk
    SnapshotWF pp hCols branched ∧
    branched.branchGen = s.branchGen + 1 ∧
    (∀ c' : Nat, c' < numChunks → c' ≠ c →
      branched.chunks.getD c' zeroChunk = s.chunks.getD c' zeroChunk ∧
      branched.chunkRoots.getD c' ByteArray.empty = s.chunkRoots.getD c' ByteArray.empty ∧
      branched.ajtaiChunkRoots.getD c' [] = s.ajtaiChunkRoots.getD c' [] ∧
      ∀ j : Nat, j < chunkSlots →
        rebindPreBranchChunkOpening (openSnapshotSlot s c' j) branched c' =
          openSnapshotSlot branched c' j ∧
        verifyOpening branched.verkleRoot (slotAddr c' j) (s.readSlot c' j)
          (rebindPreBranchChunkOpening (openSnapshotSlot s c' j) branched c') = true) ∧
    (∀ (c'' j : Nat), c'' < numChunks → ∀ (v₁ v₂ : UInt64) (w₁ w₂ : DualChunkSlotOpening),
        verifyDualChunkOpening pp hCols branched.snapshotRoot
          (branched.ajtaiChunkRoots.getD c'' []) c'' j v₁ w₁ = true →
        verifyDualChunkOpening pp hCols branched.snapshotRoot
          (branched.ajtaiChunkRoots.getD c'' []) c'' j v₂ w₂ = true →
        v₁ = v₂ ∨
          (Obend.Digest.HashBytes.CollisionAmong treeHash
            (fun x => x ∈ openingPreimages c'' j v₁ w₁ ∨ x ∈ openingPreimages c'' j v₂ w₂) ∧
           SISBreakOn pp (diffLimbs w₁ w₂))) := by
  have hwfFork : SnapshotWF pp hCols (cowForkSnapshot s) := hwf
  have hwfB : SnapshotWF pp hCols (cowUpdateChunk pp hCols s c hc newChunk) :=
    updateChunkVerkleRoot_wf hwfFork c hc newChunk
  refine ⟨hwfB, rfl, ?_, ?_⟩
  · intro c' hc' hne
    have hchEq : (cowUpdateChunk pp hCols s c hc newChunk).chunks.getD c' zeroChunk =
        s.chunks.getD c' zeroChunk :=
      getD_setIfInBounds_ne s.chunks c c' newChunk zeroChunk hne
    have hcrEq : (cowUpdateChunk pp hCols s c hc newChunk).chunkRoots.getD c' ByteArray.empty =
        s.chunkRoots.getD c' ByteArray.empty :=
      getD_setIfInBounds_ne s.chunkRoots c c' _ ByteArray.empty hne
    have harEq : (cowUpdateChunk pp hCols s c hc newChunk).ajtaiChunkRoots.getD c' [] =
        s.ajtaiChunkRoots.getD c' [] :=
      getD_setIfInBounds_ne s.ajtaiChunkRoots c c' _ [] hne
    refine ⟨hchEq, hcrEq, harEq, ?_⟩
    intro j hj
    have hrebind : rebindPreBranchChunkOpening (openSnapshotSlot s c' j)
        (cowUpdateChunk pp hCols s c hc newChunk) c' =
        openSnapshotSlot (cowUpdateChunk pp hCols s c hc newChunk) c' j := by
      unfold rebindPreBranchChunkOpening openSnapshotSlot; rw [hchEq]; rfl
    have hslotEq : (cowUpdateChunk pp hCols s c hc newChunk).readSlot c' j = s.readSlot c' j := by
      unfold AuthenticatedWorldSnapshot.readSlot; rw [hchEq]
    refine ⟨hrebind, ?_⟩
    rw [hrebind, ← hslotEq]; exact openSnapshotSlot_valid hwfB hc' hj
  · intro c'' j _ v₁ v₂ w₁ w₂ hv₁ hv₂
    cases extractDualChunkOpeningBreak pp hCols hv₁ hv₂ with
    | inl heq => exact .inl heq
    | inr hpair =>
      exact .inr ⟨hpair.1.toCollisionAmong, hpair.2.property ▸
        And.intro hpair.2.val.nonZero ⟨hpair.2.val.shortNorm, hpair.2.val.inKernel⟩⟩

/-- A real dual-commitment snapshot admits a child-authenticated opening for every world. -/
theorem snapshotOpening_inhabited (world : ChunkedWorld.World) :
    ∃ (snapshot : AuthenticatedWorldSnapshot) (opening : DualChunkSlotOpening),
      verifyDualChunkOpening defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
        snapshot.snapshotRoot (snapshot.ajtaiChunkRoots.getD 0 [])
        0 0 (snapshot.readSlot 0 0) opening = true := by
  let snapshot := buildAuthenticatedSnapshot defaultChunkAjtaiParams defaultChunkAjtaiParams_cols world
  exact ⟨snapshot, openDualSnapshotSlot snapshot 0 0,
    openDualSnapshotSlot_valid (buildAuthenticatedSnapshot_wf
      defaultChunkAjtaiParams defaultChunkAjtaiParams_cols world) (by decide) (by decide)⟩

end Obend.Vault.VerkleSnapshotBridge

namespace Obend.Vault.ExpVerkleAndOpenHash
open Obend.Digest.HashBytes
open Obend.Polis (encodeFields encodeFields_injective)
set_option autoImplicit false

/-- Digests always carry all 256 bits, independently of the chosen hash implementation. -/
abbrev Digest := { b : ByteArray // b.size = 32 }
abbrev Hash256 := List UInt8 → Digest

def cshakeHash : Hash256 := fun bs =>
  ⟨Obend.Crypto.cshake32ByteArray "OBEND.VAULT.EXPVERKLE/v2".toUTF8.data.toList bs,
    Obend.Crypto.cshake32ByteArray_size _ _⟩

/-- Every domain tag and payload is independently length-framed with unbounded LEB128 lengths. -/
def frameBytes (fields : List (List UInt8)) : List UInt8 := encodeFields fields

theorem frameBytes_injective {a b : List (List UInt8)}
    (h : frameBytes a = frameBytes b) : a = b := encodeFields_injective a b h

/-- Concrete collision data, not a global pigeonhole proposition. -/
structure CollisionPair (H : Hash256) where
  left : List UInt8
  right : List UInt8
  distinct : left ≠ right
  equalHash : H left = H right

/-- Constructive local reduction: both returned messages are certified equal to the compared preimages. -/
def comparePreimages (H : Hash256) (a b : List UInt8) (h : H a = H b) :
    PSum (a = b) { c : CollisionPair H // c.left = a ∧ c.right = b } :=
  if e : a = b then .inl e else .inr ⟨⟨a, b, e, h⟩, rfl, rfl⟩

abbrev Key := BitVec 256
abbrev Val := BitVec 256
abbrev PhysSlot := Nat × Nat
abbrev Slot := Option (Key × Val)

/-- Geometric capacities are fixed at creation; insertion only fills an empty physical slot. -/
structure ElasticOpenTable where
  levels : Array (Array Slot)
  seed : BitVec 256 := 0
  deriving DecidableEq

def emptyTable (base levels : Nat) (seed : BitVec 256 := 0) : ElasticOpenTable :=
  ⟨(Array.range levels).map (fun l => Array.replicate (base / 2 ^ l) none), seed⟩

def getSlot (t : ElasticOpenTable) (p : PhysSlot) : Slot :=
  (t.levels[p.1]?.bind fun row => row[p.2]?).join

/-- Independently framed full-width seed, key, and unbounded level number. -/
def probePreimage (seed : BitVec 256) (k : Key) (level : Nat) : List UInt8 :=
  frameBytes [[20], be 32 seed.toNat, be 32 k.toNat, ChunkedWorld.encNat level]

def probeDigest (H : Hash256) (seed : BitVec 256) (k : Key) (level : Nat) : Digest :=
  H (probePreimage seed k level)

/-- Salt affects all 256 hash bits before capacity reduction. A public salt does not
promise resistance to adaptive grinding; distinct hashes may share a reduced window. -/
def probeSlots (k : Key) (level cap : Nat) (seed : BitVec 256 := 0) : List Nat :=
  let base := ofBE (probeDigest cshakeHash seed k level).val.data.toList
  (List.range (min 4 cap)).map fun j => (base + j) % cap

theorem probe_seed_binding (H : Hash256) (a b : BitVec 256) (k : Key) (l : Nat)
    (hne : a ≠ b) (he : probeDigest H a k l = probeDigest H b k l) :
    H (probePreimage a k l) = H (probePreimage b k l) ∧
      probePreimage a k l ≠ probePreimage b k l := by
  refine ⟨he, ?_⟩
  intro h
  have hf := frameBytes_injective h
  have hs : be 32 a.toNat = be 32 b.toNat := by simpa only [List.cons.injEq, true_and, and_true] using hf
  apply hne
  apply BitVec.eq_of_toNat_eq
  exact be_injective (by simpa using a.isLt) (by simpa using b.isLt) hs

def probeCoords (t : ElasticOpenTable) (k : Key) : List PhysSlot :=
  (List.range t.levels.size).flatMap fun l =>
    (probeSlots k l (t.levels[l]!.size) t.seed).map fun s => (l, s)

def probeBudget (t : ElasticOpenTable) : Nat :=
  ((List.range t.levels.size).map fun l => min 4 (t.levels[l]!.size)).sum

theorem probeSlots_length (k : Key) (l cap : Nat) (seed : BitVec 256) :
    (probeSlots k l cap seed).length = min 4 cap := by simp [probeSlots]

theorem probeCoords_length (t : ElasticOpenTable) (k : Key) :
    (probeCoords t k).length = probeBudget t := by
  simp [probeCoords, probeBudget, List.length_flatMap, probeSlots_length]

theorem probeSlots_bounded {k : Key} {l cap s : Nat} {seed : BitVec 256}
    (h : s ∈ probeSlots k l cap seed) :
    s < cap := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  have hj' := List.mem_range.mp hj
  exact Nat.mod_lt _ (by omega)

def search (t : ElasticOpenTable) (k : Key) : List PhysSlot → Option (PhysSlot × Val)
  | [] => none
  | p :: ps => match getSlot t p with
    | some (key, v) => if key = k then some (p, v) else search t k ps
    | none => search t k ps

def lookup (t : ElasticOpenTable) (k : Key) : Option Val :=
  (search t k (probeCoords t k)).map Prod.snd

theorem search_none_iff (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot) :
    search t k ps = none ↔ ∀ p ∈ ps, ∀ v, getSlot t p ≠ some (k, v) := by
  induction ps with
  | nil => simp [search]
  | cons p ps ih =>
    cases hg : getSlot t p with
    | none => simp [search, hg, ih]
    | some e =>
      obtain ⟨key, v⟩ := e
      by_cases hk : key = k
      · subst key; simp [search, hg]
      · simp [search, hg, hk, ih]

theorem search_complete (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot)
    (p : PhysSlot) (v : Val) (hp : p ∈ ps) (hv : getSlot t p = some (k, v)) :
    ∃ q w, search t k ps = some (q, w) := by
  cases hs : search t k ps with
  | none => exact False.elim (((search_none_iff t k ps).mp hs) p hp v hv)
  | some e => exact ⟨e.1, e.2, rfl⟩

theorem lookup_none_iff (t : ElasticOpenTable) (k : Key) :
    lookup t k = none ↔ ∀ p ∈ probeCoords t k, ∀ v, getSlot t p ≠ some (k, v) := by
  simp [lookup, search_none_iff]

/-- Out-of-range writes are no-ops; occupied slots are also no-ops. -/
def fillSlot (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) : ElasticOpenTable :=
  if getSlot t p = none then
    ⟨t.levels.modify p.1 (fun row => row.setIfInBounds p.2 (some e)), t.seed⟩
  else t

theorem fillSlot_preserves (t : ElasticOpenTable) (p q : PhysSlot) (e old : Key × Val)
    (h : getSlot t q = some old) : getSlot (fillSlot t p e) q = some old := by
  unfold fillSlot
  split
  next hp =>
    have hne : p ≠ q := by intro he; subst q; rw [hp] at h; contradiction
    simp only [getSlot] at *
    obtain ⟨pl, ps⟩ := p
    obtain ⟨ql, qs⟩ := q
    by_cases hl : pl = ql
    · subst ql
      have hs : ps ≠ qs := by intro hs; exact hne (by simp [hs])
      simp only [Array.getElem?_modify, ↓reduceIte]
      cases ht : t.levels[pl]? with
      | none => simp [ht] at h
      | some row => simpa [ht, Array.getElem?_setIfInBounds, hs] using h
    · simp [Array.getElem?_modify, hl, h]
  next => exact h

inductive InsertResult where
  | inserted (slot : PhysSlot)
  | alreadyPresent (slot : PhysSlot)
  | conflict (existing : Val)
  | tableFull
  deriving DecidableEq, Repr

/-- Write-once duplicate policy: even a different value leaves the first binding intact. -/
def insert (t : ElasticOpenTable) (k : Key) (v : Val) : ElasticOpenTable × InsertResult :=
  match search t k (probeCoords t k) with
  | some (p, old) => (t, if old = v then .alreadyPresent p else .conflict old)
  | none => match (probeCoords t k).find? (fun p => (getSlot t p).isNone) with
    | none => (t, .tableFull)
    | some p => (fillSlot t p (k, v), .inserted p)

theorem insert_preserves_all_prior_slots (t : ElasticOpenTable) (k : Key) (v : Val)
    (p : PhysSlot) (old : Key × Val) (h : getSlot t p = some old) :
    getSlot (insert t k v).1 p = some old := by
  unfold insert
  split
  · exact h
  · split
    · exact h
    · exact fillSlot_preserves _ _ _ _ _ h

def insertSeq (t : ElasticOpenTable) : List (Key × Val) → ElasticOpenTable
  | [] => t
  | (k, v) :: xs => insertSeq (insert t k v).1 xs

theorem insertSeq_preserves_all_prior_slots (t : ElasticOpenTable) (xs : List (Key × Val))
    (p : PhysSlot) (old : Key × Val) (h : getSlot t p = some old) :
    getSlot (insertSeq t xs) p = some old := by
  induction xs generalizing t with
  | nil => exact h
  | cons e xs ih => exact ih _ (insert_preserves_all_prior_slots t e.1 e.2 p old h)



def InBounds (t : ElasticOpenTable) (p : PhysSlot) : Prop :=
  ∃ row, t.levels[p.1]? = some row ∧ p.2 < row.size

theorem probeCoords_inBounds (t : ElasticOpenTable) (k : Key) (p : PhysSlot)
    (hp : p ∈ probeCoords t k) : InBounds t p := by
  obtain ⟨l, hl, hs⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  have hl' := List.mem_range.mp hl
  refine ⟨t.levels[l], by simp [hl'], ?_⟩
  simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl'] using
    (probeSlots_bounded hj)

theorem fillSlot_same (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val)
    (hb : InBounds t p) (hn : getSlot t p = none) :
    getSlot (fillSlot t p e) p = some e := by
  obtain ⟨row, hr, hs⟩ := hb
  simp only [fillSlot, hn, ↓reduceIte]
  simp [getSlot, Array.getElem?_modify, hr, hs]

theorem fillSlot_other (t : ElasticOpenTable) (p q : PhysSlot) (e : Key × Val)
    (hne : p ≠ q) : getSlot (fillSlot t p e) q = getSlot t q := by
  unfold fillSlot
  split
  · unfold getSlot
    by_cases hl : p.1 = q.1
    · have hs : p.2 ≠ q.2 := fun he => hne (Prod.ext hl he)
      simp only [Array.getElem?_modify, hl, ↓reduceIte]
      cases t.levels[q.1]? <;> simp [hs]
    · simp [Array.getElem?_modify, hl]
  · rfl

theorem fillSlot_probeCoords (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) (k : Key) :
    probeCoords (fillSlot t p e) k = probeCoords t k := by
  unfold fillSlot
  split
  · simp only [probeCoords, Array.size_modify]
    congr 1
    funext l
    by_cases hl : l < t.levels.size
    · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
        Array.getElem?_eq_getElem hl]
      split <;> simp
    · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
        Array.getElem?_eq_none (Nat.le_of_not_gt hl)]
  · rfl

/-- The physical partition shape is invariant, including geometrically shrinking row capacities. -/
def levelSizes (t : ElasticOpenTable) : Array Nat := t.levels.map Array.size

theorem emptyTable_levelSizes (base levels : Nat) :
    levelSizes (emptyTable base levels) = (Array.range levels).map (fun l => base / 2 ^ l) := by
  simp [levelSizes, emptyTable, Array.map_map]

theorem fillSlot_levelSizes (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) :
    levelSizes (fillSlot t p e) = levelSizes t := by
  unfold fillSlot
  split
  · apply Array.ext
    · simp [levelSizes]
    · intro i hi hj
      simp only [levelSizes, Array.getElem_map] at *
      rw [Array.getElem_modify]
      split <;> simp
  · rfl

theorem insert_levelSizes (t : ElasticOpenTable) (k : Key) (v : Val) :
    levelSizes (insert t k v).1 = levelSizes t := by
  unfold insert
  split
  · rfl
  · split
    · rfl
    · exact fillSlot_levelSizes _ _ _

theorem insertSeq_levelSizes (t : ElasticOpenTable) (xs : List (Key × Val)) :
    levelSizes (insertSeq t xs) = levelSizes t := by
  induction xs generalizing t with
  | nil => rfl
  | cons e xs ih => exact (ih _).trans (insert_levelSizes t e.1 e.2)

theorem search_sound (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot)
    (p : PhysSlot) (v : Val) (h : search t k ps = some (p, v)) :
    p ∈ ps ∧ getSlot t p = some (k, v) := by
  induction ps with
  | nil => simp [search] at h
  | cons q qs ih =>
    cases hg : getSlot t q with
    | none => exact ⟨List.mem_cons_of_mem _ (ih (by simpa [search, hg] using h)).1,
        (ih (by simpa [search, hg] using h)).2⟩
    | some e =>
      obtain ⟨key, value⟩ := e
      by_cases hk : key = k
      · subst key
        simp only [search, hg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hg⟩
      · have ht : search t k qs = some (p, v) := by simpa [search, hg, hk] using h
        exact ⟨List.mem_cons_of_mem _ (ih ht).1, (ih ht).2⟩

theorem insert_then_lookup_eq (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (hs : (insert t k v).2 = .inserted p) : lookup (insert t k v).1 k = some v := by
  unfold insert at hs ⊢
  cases hsearch : search t k (probeCoords t k) with
  | some e => simp only [hsearch] at hs; split at hs <;> cases hs
  | none =>
    simp only [hsearch] at hs ⊢
    cases hf : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
    | none => simp [hf] at hs
    | some q =>
      simp only [hf, InsertResult.inserted.injEq] at hs
      subst q
      have hp : p ∈ probeCoords t k := List.mem_of_find?_eq_some hf
      have hn : getSlot t p = none := Option.isNone_iff_eq_none.mp (show (getSlot t p).isNone = true from List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hf)
      have hb := probeCoords_inBounds t k p hp
      have hfill := fillSlot_same t p (k, v) hb hn
      simp only [lookup, fillSlot_probeCoords]
      cases ho : search (fillSlot t p (k, v)) k (probeCoords t k) with
      | none =>
        exact False.elim (((search_none_iff _ _ _).mp ho) p hp v hfill)
      | some e =>
        obtain ⟨q, w⟩ := e
        have hfound := search_sound _ _ _ q w ho
        by_cases he : p = q
        · subst q
          rw [hfill] at hfound
          have hv : v = w := (Prod.mk.inj (Option.some.inj hfound.2)).2
          simp [hv]
        · rw [fillSlot_other t p q (k, v) he] at hfound
          exact False.elim (((search_none_iff _ _ _).mp hsearch) q hfound.1 w hfound.2)

theorem search_fill_other_key (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) (k : Key)
    (hb : InBounds t p) (hn : getSlot t p = none) (hne : e.1 ≠ k) (ps : List PhysSlot) :
    search (fillSlot t p e) k ps = search t k ps := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    by_cases he : p = q
    · subst q
      simp only [search, fillSlot_same t p e hb hn, hn, hne, ite_false, ih]
    · simp only [search, fillSlot_other t p q e he]
      cases getSlot t q with
      | none => exact ih
      | some e => split <;> simp_all

/-- Logical lookup stability, including malformed starting tables with duplicate keys:
new inserts cannot shadow an earlier hit, because duplicate queries are never written. -/
theorem lookup_stable_insert (t : ElasticOpenTable) (k q : Key) (v w : Val)
    (hl : lookup t q = some w) : lookup (insert t k v).1 q = some w := by
  unfold insert
  split
  · exact hl
  · rename_i hs
    have hk : k ≠ q := by
      intro he; subst k
      simp [lookup, hs] at hl
    split
    · exact hl
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hn := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      simpa only [lookup, fillSlot_probeCoords,
        search_fill_other_key t p (k, v) q (probeCoords_inBounds t k p hm) hn hk] using hl

theorem lookup_stable (t : ElasticOpenTable) (xs : List (Key × Val)) (k : Key) (v : Val)
    (hl : lookup t k = some v) : lookup (insertSeq t xs) k = some v := by
  induction xs generalizing t with
  | nil => exact hl
  | cons e xs ih => exact ih _ (lookup_stable_insert t e.1 k e.2 v hl)

/-- Instrumented search counts the slot inspections actually performed, stopping on a hit. -/
def searchCount (t : ElasticOpenTable) (k : Key) : List PhysSlot → Option (PhysSlot × Val) × Nat
  | [] => (none, 0)
  | p :: ps => match getSlot t p with
    | some (key, v) => if key = k then (some (p, v), 1)
        else let r := searchCount t k ps; (r.1, r.2 + 1)
    | none => let r := searchCount t k ps; (r.1, r.2 + 1)

theorem searchCount_refines (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot) :
    (searchCount t k ps).1 = search t k ps ∧ (searchCount t k ps).2 ≤ ps.length := by
  induction ps with
  | nil => simp [searchCount, search]
  | cons p ps ih =>
    cases hg : getSlot t p with
    | none => simpa [searchCount, search, hg] using ih
    | some e =>
      by_cases hk : e.1 = k
      · simp [searchCount, search, hg, hk]
      · simpa [searchCount, search, hg, hk] using ih

theorem lookup_worst_case (t : ElasticOpenTable) (k : Key) :
    (searchCount t k (probeCoords t k)).1.map Prod.snd = lookup t k ∧
    (searchCount t k (probeCoords t k)).2 ≤ probeBudget t := by
  have h := searchCount_refines t k (probeCoords t k)
  exact ⟨congrArg (Option.map Prod.snd) h.1, by simpa [probeCoords_length] using h.2⟩

theorem insert_succeeds_of_vacancy (t : ElasticOpenTable) (k : Key) (v : Val)
    (hn : lookup t k = none) (p : PhysSlot) (hp : p ∈ probeCoords t k) (he : getSlot t p = none) :
    ∃ q, (insert t k v).2 = .inserted q ∧ lookup (insert t k v).1 k = some v := by
  have hs : search t k (probeCoords t k) = none := by simpa [lookup] using hn
  have hf : (probeCoords t k).find? (fun q => (getSlot t q).isNone) ≠ none := by
    intro h
    have hh := List.find?_eq_none.mp h p hp
    simp [he] at hh
  cases hg : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
  | none => exact False.elim (hf hg)
  | some q =>
    have hr : (insert t k v).2 = .inserted q := by simp [insert, hs, hg]
    exact ⟨q, hr, insert_then_lookup_eq t k v q hr⟩

/-- Physical coordinates are reachable under the occupant's own bounded probe schedule. -/
def TableWF (t : ElasticOpenTable) : Prop :=
  ∀ p k v, getSlot t p = some (k, v) → p ∈ probeCoords t k

def slotBytes (s : Slot) : List UInt8 :=
  encodeFields (match s with | none => [[12]] | some (k, v) => [[13], be 32 k.toNat, be 32 v.toNat])

theorem emptyTable_wf (base levels : Nat) (seed : BitVec 256 := 0) : TableWF (emptyTable base levels seed) := by
  intro p k v h
  simp only [getSlot, emptyTable, Array.getElem?_map, Array.getElem?_range] at h
  split at h <;> simp_all [Array.getElem?_replicate]
  split at h <;> simp_all

theorem insert_wf (t : ElasticOpenTable) (k : Key) (v : Val) (hw : TableWF t) :
    TableWF (insert t k v).1 := by
  unfold insert
  split
  · exact hw
  · rename_i hn
    split
    · exact hw
    · rename_i p hp
      intro q key value hq
      have hm := List.mem_of_find?_eq_some hp
      have he : getSlot t p = none := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      rw [fillSlot_probeCoords]
      by_cases hqp : p = q
      · subst q
        rw [fillSlot_same t p (k, v) (probeCoords_inBounds t k p hm) he] at hq
        have hk := (Prod.mk.inj (Option.some.inj hq)).1
        simpa [hk] using hm
      · exact hw q key value (by simpa [fillSlot_other t p q (k, v) hqp] using hq)

theorem insertSeq_wf (t : ElasticOpenTable) (xs : List (Key × Val)) (hw : TableWF t) :
    TableWF (insertSeq t xs) := by
  induction xs generalizing t with
  | nil => exact hw
  | cons e xs ih => exact ih _ (insert_wf t e.1 e.2 hw)

/-- Each key occupies at most one physical slot in a constructed table. -/
def KeyUnique (t : ElasticOpenTable) : Prop :=
  ∀ p q k v w, getSlot t p = some (k,v) → getSlot t q = some (k,w) → p = q

theorem emptyTable_unique (base levels : Nat) (seed : BitVec 256 := 0) :
    KeyUnique (emptyTable base levels seed) := by
  intro p q k v w h _
  simp only [getSlot, emptyTable, Array.getElem?_map, Array.getElem?_range] at h
  split at h <;> simp_all [Array.getElem?_replicate]
  split at h <;> simp_all

theorem insert_unique (t : ElasticOpenTable) (k : Key) (v : Val) (hw : TableWF t)
    (hu : KeyUnique t) : KeyUnique (insert t k v).1 := by
  unfold insert
  split
  · exact hu
  · rename_i hs
    split
    · exact hu
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hn := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      have hf := fillSlot_same t p (k,v) (probeCoords_inBounds t k p hm) hn
      have absent : ∀ q w, getSlot t q ≠ some (k,w) := by
        intro q w hq
        exact (search_none_iff t k _).mp hs q (hw q k w hq) w hq
      intro q r key x y hq hr
      by_cases heq : p = q
      · subst q
        have hk : k = key := (Prod.mk.inj (Option.some.inj (hf.symm.trans hq))).1
        by_cases her : p = r
        · exact her
        · rw [fillSlot_other t p r (k,v) her] at hr
          exact False.elim (absent r y (by simpa [hk] using hr))
      · rw [fillSlot_other t p q (k,v) heq] at hq
        by_cases her : p = r
        · subst r
          have hk : k = key := (Prod.mk.inj (Option.some.inj (hf.symm.trans hr))).1
          exact False.elim (absent q x (by simpa [hk] using hq))
        · rw [fillSlot_other t p r (k,v) her] at hr
          exact hu q r key x y hq hr

theorem insertSeq_unique (t : ElasticOpenTable) (xs : List (Key × Val))
    (hw : TableWF t) (hu : KeyUnique t) : KeyUnique (insertSeq t xs) := by
  induction xs generalizing t with
  | nil => exact hu
  | cons e xs ih => exact ih _ (insert_wf t e.1 e.2 hw) (insert_unique t e.1 e.2 hw hu)

theorem lookup_probe_bound (t : ElasticOpenTable) (k : Key) :
    (probeCoords t k).length ≤ 4 * t.levels.size := by
  rw [probeCoords_length]
  have hb : ∀ ls : List Nat,
      (ls.map fun l => min 4 (t.levels[l]!.size)).sum ≤ 4 * ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons l ls ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  simpa [probeBudget] using hb (List.range t.levels.size)

theorem lookup_complete_of_wf (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (hw : TableWF t) (hv : getSlot t p = some (k,v)) : ∃ w, lookup t k = some w := by
  obtain ⟨q,w,hs⟩ := search_complete t k _ p v (hw p k v hv) hv
  exact ⟨w, by simp [lookup, hs]⟩

/-- Four inspections per level; whenever the row has more than four slots this is
strictly below a row scan. This bound is independent of key distribution and load. -/
theorem probe_level_sublinear (k : Key) (l cap : Nat) (seed : BitVec 256) (hc : 4 < cap) :
    (probeSlots k l cap seed).length < cap := by rw [probeSlots_length]; omega

/-- Capacity at height zero is one leaf; subsequent capacities are 2, 4, 16, 256, ... . -/
def capacity : Nat → Nat
  | 0 => 1
  | k + 1 => 2 ^ (2 ^ k)

def arity : Nat → Nat
  | 0 => 2
  | k + 1 => capacity (k + 1)

theorem capacity_pos (k : Nat) : 0 < capacity k := by
  cases k <;> simp [capacity, Nat.pow_pos]

theorem capacity_step (k : Nat) : capacity (k + 1) = arity k * capacity k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [capacity, arity, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_comm 2 (2 ^ k), Nat.pow_mul]
    simp [Nat.pow_two]


/-- Canonical exponential height, with two child-authentication levels even for tiny forests. -/
def expVerkleDepth (n : Nat) : Nat :=
  if n ≤ 2 then 2 else (n - 1).log2.log2 + 2

theorem expVerkleDepth_covers (n : Nat) : n ≤ capacity (expVerkleDepth n) := by
  unfold expVerkleDepth
  split
  next h => simp only [capacity]; omega
  next h =>
    have ha := Nat.lt_log2_self (n := n - 1)
    have hb := Nat.lt_log2_self (n := (n - 1).log2)
    have hc := Nat.pow_le_pow_right (n := 2) (by decide)
      (show (n - 1).log2 + 1 ≤ 2 ^ ((n - 1).log2.log2 + 1) by omega)
    simp only [capacity]
    omega

theorem expVerkleDepth_multiLevel (n : Nat) : 2 ≤ expVerkleDepth n := by
  unfold expVerkleDepth; split <;> omega

/-- The two-level minimum is the only overhead over the logarithmic depth bound. -/
theorem expVerkle_depth_le_logLog (n k : Nat) (h : n ≤ 2 ^ (2 ^ k)) :
    expVerkleDepth n ≤ max 2 (k + 1) := by
  unfold expVerkleDepth
  split
  next => omega
  next h2 =>
    have hn : n - 1 ≠ 0 := by omega
    have ha : (n - 1).log2 < 2 ^ k := (Nat.log2_lt hn).mpr (by omega)
    have hb : 1 ≤ (n - 1).log2 := (Nat.le_log2 hn).mpr (by omega)
    have hc : (n - 1).log2.log2 < k := (Nat.log2_lt (by omega)).mpr ha
    omega

structure ExpVerkleSpec where
  entries : List Val
  deriving DecidableEq

def specEntries (s : ExpVerkleSpec) : List Val := s.entries

def specGet? (s : ExpVerkleSpec) (idx : Nat) : Option Val := s.entries[idx]?

/-- Append is an array push. Authentication is materialized on demand at snapshot/open time.
This deliberately does not claim logarithmic hash work: flat node vectors cost their arity. -/
structure ExpVerkleForestExec where
  entries : Array Val
  deriving DecidableEq

abbrev ExpVerkleForest := ExpVerkleForestExec

def appendExpVerkle (f : ExpVerkleForestExec) (v : Val) : ExpVerkleForestExec :=
  ⟨f.entries.push v⟩

def Simulates (s : ExpVerkleSpec) (f : ExpVerkleForestExec) : Prop :=
  f.entries.toList = specEntries s

theorem appendExpVerkle_refines (s : ExpVerkleSpec) (f : ExpVerkleForestExec) (v : Val)
    (h : Simulates s f) : Simulates ⟨s.entries ++ [v]⟩ (appendExpVerkle f v) := by
  simpa [Simulates, specEntries, appendExpVerkle] using congrArg (· ++ [v]) h

theorem appendExpVerkle_preserves (f : ExpVerkleForestExec) (v : Val) (idx : Nat)
    (h : idx < f.entries.size) : (appendExpVerkle f v).entries[idx]? = f.entries[idx]? := by
  simp [appendExpVerkle, Array.getElem?_push, h, Nat.ne_of_lt h]

/-- Natural metadata uses the vault's proven unbounded canonical codec, then a field frame. -/
def natBytes (n : Nat) : List UInt8 := ChunkedWorld.encNat n

theorem natBytes_injective {a b : Nat} (h : natBytes a = natBytes b) : a = b := by
  have ha := ChunkedWorld.decNat_encNat a []
  have hb := ChunkedWorld.decNat_encNat b []
  simp only [List.append_nil] at ha hb
  rw [show ChunkedWorld.encNat a = ChunkedWorld.encNat b from h, hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

def leafBytes (idx : Nat) (v : Option Val) : List UInt8 :=
  frameBytes [[0], natBytes idx, match v with | none => [] | some x => be 32 x.toNat]

def nodeBytes (level : Nat) (children : Array Digest) : List UInt8 :=
  frameBytes ([1] :: natBytes level :: children.toList.map (fun d => d.val.data.toList))

def forestBytes (count height : Nat) (root : Digest) : List UInt8 :=
  frameBytes [[2], natBytes count, natBytes height, root.val.data.toList]

theorem digest_bytes_injective {a b : Digest} (h : a.val.data.toList = b.val.data.toList) :
    a = b := Subtype.ext (Obend.Crypto.byteArray_eq_of_toList_eq h)

theorem leafBytes_injective {i j : Nat} {v w : Val}
    (h : leafBytes i (some v) = leafBytes j (some w)) : i = j ∧ v = w := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, and_true, true_and] at hf
  refine ⟨natBytes_injective hf.1, BitVec.eq_of_toNat_eq ?_⟩
  exact be_injective (by simpa using v.isLt) (by simpa using w.isLt) hf.2

theorem nodeBytes_injective {i j : Nat} {a b : Array Digest}
    (h : nodeBytes i a = nodeBytes j b) : i = j ∧ a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and] at hf
  refine ⟨natBytes_injective hf.1, Array.toList_inj.mp ?_⟩
  exact (List.map_inj_right (fun _ _ he => digest_bytes_injective he)).mp hf.2

theorem forestBytes_injective {n m i j : Nat} {a b : Digest}
    (h : forestBytes n i a = forestBytes m j b) : n = m ∧ i = j ∧ a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨natBytes_injective hf.1, natBytes_injective hf.2.1, digest_bytes_injective hf.2.2⟩


theorem leafBytes_all_fields_injective {i j : Nat} {v w : Option Val}
    (h : leafBytes i v = leafBytes j w) : i = j ∧ v = w := by
  cases v with
  | none =>
    cases w with
    | none =>
      have hf := frameBytes_injective h
      simp only [List.cons.injEq, true_and, and_true] at hf
      exact ⟨natBytes_injective hf, rfl⟩
    | some w =>
      have hf := frameBytes_injective h
      have hs := congrArg (fun fs => (fs[2]?.getD []).length) hf
      simp [length_be] at hs
  | some v =>
    cases w with
    | none =>
      have hf := frameBytes_injective h
      have hs := congrArg (fun fs => (fs[2]?.getD []).length) hf
      simp [length_be] at hs
    | some w =>
      obtain ⟨hi, hv⟩ := leafBytes_injective h
      exact ⟨hi, congrArg some hv⟩

def emptyBytes (height start : Nat) : List UInt8 :=
  frameBytes [[3], natBytes height, natBytes start]

theorem emptyBytes_injective {h k a b : Nat} (he : emptyBytes h a = emptyBytes k b) :
    h = k ∧ a = b := by
  have hf := frameBytes_injective he
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨natBytes_injective hf.1, natBytes_injective hf.2⟩

/-- A sparse prefix, with absent leaves explicitly distinguished from every word value.
The recurrence is the actual exponential-arity tree, not a binary depth relabeling. -/
def rootAt (H : Hash256) (entries : Array Val) : Nat → Nat → Digest
  | 0, start => H (leafBytes start entries[start]?)
  | k + 1, start =>
    if start < entries.size then H (nodeBytes (k + 1)
      ((Array.range (arity k)).map fun j => rootAt H entries k (start + j * capacity k)))
    else H (emptyBytes (k + 1) start)


/-- List specification of the same exponential tree, including explicitly vacant subtrees. -/
def specTreeRoot (H : Hash256) (entries : List Val) : Nat → Nat → Digest
  | 0, start => H (leafBytes start entries[start]?)
  | k + 1, start =>
    if start < entries.length then H (nodeBytes (k + 1)
      (((List.range (arity k)).map fun j => specTreeRoot H entries k
        (start + j * capacity k)).toArray))
    else H (emptyBytes (k + 1) start)

theorem rootAt_refines (H : Hash256) (a : Array Val) (height start : Nat) :
    rootAt H a height start = specTreeRoot H a.toList height start := by
  induction height generalizing start with
  | zero => simp [rootAt, specTreeRoot]
  | succ k ih =>
    simp only [rootAt, specTreeRoot, Array.length_toList]
    split
    · congr 2
      apply Array.toList_inj.mp
      simp [Array.toList_range, ih]
    · rfl

def childrenAt (H : Hash256) (entries : Array Val) (k start : Nat) : Array Digest :=
  (Array.range (arity k)).map fun j => rootAt H entries k (start + j * capacity k)

/-- Top-down child vectors. Every sibling is transmitted; opening bytes are not O(log log N). -/
structure ExpVerkleProof where
  count : Nat
  height : Nat
  treeRoot : Digest
  vectors : List (Array Digest)

def openAt (H : Hash256) (entries : Array Val) : Nat → Nat → Nat → List (Array Digest)
  | 0, _, _ => []
  | k + 1, start, idx =>
    childrenAt H entries k start ::
      openAt H entries k (start + (idx / capacity k) * capacity k) (idx % capacity k)

theorem openAt_length (H : Hash256) (entries : Array Val) (height start idx : Nat) :
    (openAt H entries height start idx).length = height := by
  induction height generalizing start idx with
  | zero => rfl
  | succ k ih => simp [openAt, ih]

/-- Honest accounting: the opening sends every child digest. Small depth does not
imply small bandwidth; already the top vector costs the full exponential arity. -/
theorem opening_size_lower (H : Hash256) (entries : Array Val) (k start idx : Nat) :
    arity k ≤ ((openAt H entries (k+1) start idx).map Array.size).sum := by
  simp [openAt, childrenAt]

def verifyNode (H : Hash256) : Nat → Nat → Nat → Val → Digest → List (Array Digest) → Bool
  | 0, start, idx, v, root, path =>
    decide (idx = 0 ∧ path = [] ∧ H (leafBytes start (some v)) = root)
  | k + 1, start, idx, v, root, path => match path with
    | [] => false
    | children :: rest =>
      decide (children.size = arity k ∧ H (nodeBytes (k + 1) children) = root) &&
      match children[idx / capacity k]? with
      | none => false
      | some child => verifyNode H k (start + (idx / capacity k) * capacity k)
          (idx % capacity k) v child rest

def expVerkleRoot (H : Hash256) (f : ExpVerkleForestExec) (height : Nat) : Digest :=
  H (forestBytes f.entries.size height (rootAt H f.entries height 0))

def proveExpVerkle (H : Hash256) (f : ExpVerkleForestExec) (height idx : Nat) : ExpVerkleProof :=
  ⟨f.entries.size, height, rootAt H f.entries height 0, openAt H f.entries height 0 idx⟩

def verifyExpVerkleOpening (H : Hash256) (root : Digest) (idx : Nat) (v : Val)
    (p : ExpVerkleProof) : Bool :=
  decide (idx < p.count ∧ p.count ≤ capacity p.height ∧ p.height = expVerkleDepth p.count ∧
    H (forestBytes p.count p.height p.treeRoot) = root) &&
  verifyNode H p.height 0 idx v p.treeRoot p.vectors

/-- Accepted recursive openings include exactly one authenticated child vector per level. -/
theorem verifyNode_path_length (H : Hash256) (height start idx : Nat) (v : Val)
    (root : Digest) (path : List (Array Digest))
    (h : verifyNode H height start idx v root path = true) : path.length = height := by
  induction height generalizing start idx root path with
  | zero =>
    simp only [verifyNode, decide_eq_true_eq] at h
    simp [h.2.1]
  | succ k ih =>
    cases path with
    | nil => simp [verifyNode] at h
    | cons children rest =>
      simp only [verifyNode, Bool.and_eq_true] at h
      cases hc : children[idx / capacity k]? with
      | none => simp [hc] at h
      | some child =>
        have hr : verifyNode H k (start + idx / capacity k * capacity k)
            (idx % capacity k) v child rest = true := by simpa [hc] using h.2
        simp only [List.length_cons, ih _ _ _ _ hr]

/-- No accepted opening can replace the authenticated multi-level path with a flat record. -/
theorem verifyExpVerkleOpening_multiLevel (H : Hash256) (root : Digest) (idx : Nat)
    (v : Val) (p : ExpVerkleProof) (h : verifyExpVerkleOpening H root idx v p = true) :
    2 ≤ p.vectors.length := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [verifyNode_path_length H _ _ _ _ _ _ h.2, h.1.2.2.1]
  exact expVerkleDepth_multiLevel p.count

private theorem range_get {n i : Nat} (h : i < (Array.range n).size) :
    (Array.range n)[i] = i :=
  Obend.Crypto.Fast.arrayOfFn_get (fun j : Fin n => j.val) ⟨i, by simpa only [Array.size_range] using h⟩
private theorem range_getOpt {n i : Nat} : (Array.range n)[i]? = if i < n then some i else none := by
  simp only [getElem?_def, Array.size_range, range_get, dite_eq_ite]
attribute [local simp] range_get range_getOpt

theorem verifyNode_complete (H : Hash256) (a : Array Val) (height start idx : Nat) (v : Val)
    (hi : idx < capacity height) (hv : a[start + idx]? = some v) :
    verifyNode H height start idx v (rootAt H a height start) (openAt H a height start idx) = true := by
  have hstart : start < a.size := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    omega
  induction height generalizing start idx with
  | zero =>
    have hz : idx = 0 := by simpa [capacity] using hi
    subst idx
    simp [verifyNode, rootAt, openAt, ← hv]
  | succ k ih =>
    have hdiv : idx / capacity k < arity k := by
      apply (Nat.div_lt_iff_lt_mul (capacity_pos k)).mpr
      simpa [capacity_step] using hi
    have hmod := Nat.mod_lt idx (capacity_pos k)
    have he : start + idx / capacity k * capacity k + idx % capacity k = start + idx := by
      have := Nat.mod_add_div idx (capacity k)
      rw [Nat.mul_comm (capacity k)] at this
      omega
    have ih' := ih (start + idx / capacity k * capacity k) (idx % capacity k) hmod (by simpa [he] using hv) (by
      have := (Array.getElem?_eq_some_iff.mp hv).1
      omega)
    simp only [verifyNode, openAt, rootAt, childrenAt, hstart, ite_true,
      Array.size_map, Array.size_range, true_and, decide_true, Bool.true_and,
      Array.getElem?_map, range_getOpt, hdiv, Option.map_some]
    exact ih'

theorem verifyExpVerkleOpening_complete (H : Hash256) (f : ExpVerkleForestExec)
    (height idx : Nat) (v : Val) (hc : f.entries.size ≤ capacity height)
    (hv : f.entries[idx]? = some v) (hh : height = expVerkleDepth f.entries.size) :
    verifyExpVerkleOpening H (expVerkleRoot H f height) idx v (proveExpVerkle H f height idx) = true := by
  have hi : idx < f.entries.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hn := verifyNode_complete H f.entries height 0 idx v (Nat.lt_of_lt_of_le hi hc) (by simpa using hv)
  simpa [verifyExpVerkleOpening, expVerkleRoot, proveExpVerkle, hi, hc, hh, expVerkleDepth_covers] using hn



/-- Automatic API chooses the canonical bounded height; every present entry has an opening. -/
def commitExpVerkle (H : Hash256) (f : ExpVerkleForestExec) : Digest :=
  expVerkleRoot H f (expVerkleDepth f.entries.size)

def openExpVerkle (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat) : ExpVerkleProof :=
  proveExpVerkle H f (expVerkleDepth f.entries.size) idx

theorem every_index_opens (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat)
    (hi : idx < f.entries.size) :
    verifyExpVerkleOpening H (commitExpVerkle H f) idx f.entries[idx] (openExpVerkle H f idx) = true :=
  verifyExpVerkleOpening_complete H f _ idx _ (expVerkleDepth_covers _)
    (Array.getElem?_eq_getElem hi) rfl

/-- Honest full-width hash openings inhabit the verifier, including its two-level minimum. -/
theorem verifyExpVerkleOpening_inhabited (H : Hash256) :
    ∃ root idx v proof, 2 ≤ proof.vectors.length ∧
      verifyExpVerkleOpening H root idx v proof = true := by
  let forest : ExpVerkleForestExec := ⟨#[0]⟩
  have h := every_index_opens H forest 0 (by decide)
  exact ⟨_, _, _, _, verifyExpVerkleOpening_multiLevel H _ _ _ _ h, h⟩

theorem opening_depth_bound (H : Hash256) (f : ExpVerkleForestExec) (idx k : Nat)
    (h : f.entries.size ≤ 2 ^ (2 ^ k)) : (openExpVerkle H f idx).vectors.length ≤ max 2 (k + 1) := by
  simpa [openExpVerkle, proveExpVerkle, openAt_length] using expVerkle_depth_le_logLog _ k h

theorem forest_commit_refines (H : Hash256) (f : ExpVerkleForestExec) (s : ExpVerkleSpec)
    (h : Simulates s f) : commitExpVerkle H f =
      H (forestBytes (specEntries s).length (expVerkleDepth (specEntries s).length)
        (specTreeRoot H (specEntries s) (expVerkleDepth (specEntries s).length) 0)) := by
  unfold commitExpVerkle expVerkleRoot
  rw [rootAt_refines, h]
  have hs : f.entries.size = (specEntries s).length := by rw [← h]; simp
  rw [hs]

def appendSeq (f : ExpVerkleForestExec) : List Val → ExpVerkleForestExec
  | [] => f
  | v :: vs => appendSeq (appendExpVerkle f v) vs

theorem appendSeq_entries (f : ExpVerkleForestExec) (vs : List Val) :
    (appendSeq f vs).entries.toList = f.entries.toList ++ vs := by
  induction vs generalizing f with
  | nil => simp [appendSeq]
  | cons v vs ih => simp [appendSeq, ih, appendExpVerkle, List.append_assoc]

theorem appendSeq_preserves (f : ExpVerkleForestExec) (vs : List Val) (idx : Nat)
    (hi : idx < f.entries.size) : (appendSeq f vs).entries[idx]? = f.entries[idx]? := by
  rw [← Array.getElem?_toList, appendSeq_entries, List.getElem?_append_left (by simpa using hi)]
  simp

/-- All preimages on the submitted path, retaining absolute leaf position. -/
def nodePreimages : Nat → Nat → Nat → Val → List (Array Digest) → List (List UInt8)
  | 0, start, _, v, _ => [leafBytes start (some v)]
  | _+1, _, _, _, [] => []
  | k+1, start, idx, v, a :: ps => nodeBytes (k+1) a ::
    nodePreimages k (start + idx / capacity k * capacity k) (idx % capacity k) v ps

def openingPreimages (p : ExpVerkleProof) (idx : Nat) (v : Val) : List (List UInt8) :=
  forestBytes p.count p.height p.treeRoot :: nodePreimages p.height 0 idx v p.vectors

abbrev ScopedCollision (H : Hash256) (messages : List (List UInt8)) :=
  { c : CollisionPair H // c.left ∈ messages ∧ c.right ∈ messages }

private def widenCollision {H : Hash256} {small large : List (List UInt8)}
    (c : ScopedCollision H small) (h : ∀ m ∈ small, m ∈ large) : ScopedCollision H large :=
  ⟨c.val, h _ c.property.1, h _ c.property.2⟩

/-- Traverse two accepted paths, returning the first differing preimage with equal digest.
The recursion follows actual submitted vectors, so the collision is local to the openings. -/
def extractNodeCollision (H : Hash256) (v w : Val) (hne : v ≠ w) :
    (height start idx : Nat) → (root : Digest) → (p q : List (Array Digest)) →
    verifyNode H height start idx v root p = true →
    verifyNode H height start idx w root q = true →
      ScopedCollision H (nodePreimages height start idx v p ++ nodePreimages height start idx w q)
  | 0, start, idx, root, p, q, hp, hq => by
    simp only [verifyNode, decide_eq_true_eq] at hp hq
    exact ⟨⟨leafBytes start (some v), leafBytes start (some w),
      fun he => hne (leafBytes_injective he).2, hp.2.2.trans hq.2.2.symm⟩,
      by simp [nodePreimages], by simp [nodePreimages]⟩
  | k + 1, start, idx, root, p, q, hp, hq => by
    cases p with
    | nil => simp [verifyNode] at hp
    | cons a ps =>
      cases q with
      | nil => simp [verifyNode] at hq
      | cons b qs =>
        simp only [verifyNode, Bool.and_eq_true, decide_eq_true_eq] at hp hq
        have he : H (nodeBytes (k + 1) a) = H (nodeBytes (k + 1) b) :=
          hp.1.2.trans hq.1.2.symm
        if hab : nodeBytes (k + 1) a = nodeBytes (k + 1) b then
          have hab' := (nodeBytes_injective hab).2
          subst b
          cases hg : a[idx / capacity k]? with
          | none => simp [hg] at hp
          | some child =>
            apply widenCollision (extractNodeCollision H v w hne k
              (start + idx / capacity k * capacity k) (idx % capacity k) child ps qs
              (by simpa [hg] using hp.2) (by simpa [hg] using hq.2))
            intro m hm
            simp only [nodePreimages, List.mem_append, List.mem_cons] at *
            rcases hm with hm | hm
            · exact .inl (.inr hm)
            · exact .inr (.inr hm)
        else exact ⟨⟨_, _, hab, he⟩, by simp [nodePreimages], by simp [nodePreimages]⟩

/-- Full position-binding extractor, with no choice and no unscoped collision assumption. -/
def extractOpeningCollision (H : Hash256) (root : Digest) (idx : Nat) (v w : Val)
    (p q : ExpVerkleProof) (hne : v ≠ w)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w) := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  have he := hp.1.2.2.2.trans hq.1.2.2.2.symm
  if hf : forestBytes p.count p.height p.treeRoot = forestBytes q.count q.height q.treeRoot then
    have hb := forestBytes_injective hf
    apply widenCollision (extractNodeCollision H v w hne p.height 0 idx p.treeRoot p.vectors q.vectors hp.2
      (by simpa [hb.2.1, hb.2.2] using hq.2))
    intro m hm
    simp only [openingPreimages, List.mem_append, List.mem_cons] at *
    rcases hm with hm | hm
    · exact .inl (.inr hm)
    · exact .inr (.inr (by simpa [hb.2.1] using hm))
  else exact ⟨⟨_, _, hf, he⟩, by simp [openingPreimages], by simp [openingPreimages]⟩

theorem verifyExpVerkleOpening_binds_or_collision (H : Hash256) (root : Digest)
    (idx : Nat) (v w : Val) (p q : ExpVerkleProof)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    v = w ∨ Nonempty (ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w)) := by
  by_cases he : v = w
  · exact .inl he
  · let c := extractOpeningCollision H root idx v w p q he hp hq
    exact .inr ⟨c⟩


theorem opening_binds_count (H : Hash256) (root : Digest) (idx : Nat) (v w : Val)
    (p q : ExpVerkleProof) (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    (p.count = q.count ∧ p.height = q.height) ∨
      Nonempty (ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w)) := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  by_cases he : forestBytes p.count p.height p.treeRoot = forestBytes q.count q.height q.treeRoot
  · have hi := forestBytes_injective he
    exact .inl ⟨hi.1,hi.2.1⟩
  · exact .inr ⟨⟨⟨_,_,he,hp.1.2.2.2.trans hq.1.2.2.2.symm⟩,
      by simp [openingPreimages], by simp [openingPreimages]⟩⟩

theorem slotBytes_injective {a b : Slot} (h : slotBytes a = slotBytes b) : a = b := by
  have hf := encodeFields_injective _ _ h
  cases a with
  | none => cases b <;> simp_all [slotBytes]
  | some a =>
    cases b with
    | none => simp_all [slotBytes]
    | some b =>
      have he : be 32 a.1.toNat = be 32 b.1.toNat ∧ be 32 a.2.toNat = be 32 b.2.toNat := by
        simpa [slotBytes] using hf
      have hk := be_injective (by simpa using a.1.isLt) (by simpa using b.1.isLt) he.1
      have hv := be_injective (by simpa using a.2.isLt) (by simpa using b.2.isLt) he.2
      exact congrArg some (Prod.ext (BitVec.eq_of_toNat_eq hk) (BitVec.eq_of_toNat_eq hv))

/-- Row forests hold all 256 bits of each framed slot digest. -/
def digestWord (d : Digest) : Val := BitVec.ofNat 256 (ofBE d.val.data.toList)

theorem digestWord_injective {a b : Digest} (h : digestWord a = digestWord b) : a = b := by
  open Obend.Crypto.BinaryTower256 in
  have inv (d : Digest) : toBytes32 (digestWord d) = d.val :=
    toBytes32_ofBytes32 d.val _ (by simp [ofBytes32, d.property, digestWord])
  exact Subtype.ext ((inv a).symm.trans ((congrArg _ h).trans (inv b)))

def slotWord (H : Hash256) (s : Slot) : Val := digestWord (H (slotBytes s))
def rowForest (H : Hash256) (row : Array Slot) : ExpVerkleForestExec := ⟨row.map (slotWord H)⟩

structure TableHeader where
  seed : BitVec 256
  rows : Array (Nat × Digest)
  deriving DecidableEq

def tableHeader (H : Hash256) (t : ElasticOpenTable) : TableHeader :=
  ⟨t.seed, t.levels.map fun row => (row.size, commitExpVerkle H (rowForest H row))⟩

def headerBytes (h : TableHeader) : List UInt8 :=
  frameBytes ([10] :: be 32 h.seed.toNat :: h.rows.toList.map fun (n, r) =>
    frameBytes [natBytes n, r.val.data.toList])

theorem headerBytes_injective {a b : TableHeader} (h : headerBytes a = headerBytes b) : a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and] at hf
  have hs : a.seed = b.seed := BitVec.eq_of_toNat_eq
    (be_injective (by simpa using a.seed.isLt) (by simpa using b.seed.isLt) hf.1)
  have hr : a.rows = b.rows := Array.toList_inj.mp ((List.map_inj_right (fun x y he => by
    have hh := frameBytes_injective he
    simp only [List.cons.injEq, and_true] at hh
    exact Prod.ext (natBytes_injective hh.1) (digest_bytes_injective hh.2))).mp hf.2)
  cases a; cases b; cases hs; cases hr; rfl

def tableDigest (H : Hash256) (t : ElasticOpenTable) : Digest := H (headerBytes (tableHeader H t))

def headerCoords (h : TableHeader) (k : Key) : List PhysSlot :=
  (List.range h.rows.size).flatMap fun l =>
    (probeSlots k l ((h.rows[l]?.map Prod.fst).getD 0) h.seed).map fun s => (l, s)

theorem headerCoords_eq (H : Hash256) (t : ElasticOpenTable) (k : Key) :
    headerCoords (tableHeader H t) k = probeCoords t k := by
  simp only [headerCoords, tableHeader, probeCoords, Array.size_map]
  congr 1
  funext l
  by_cases hl : l < t.levels.size
  · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
  · simp only [Array.getElem?_map, Array.getElem?_eq_none (by omega : t.levels.size ≤ l),
      Option.map_none, Option.getD_none, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rfl

structure SlotOpening where
  coordinate : PhysSlot
  state : Slot
  proof : ExpVerkleProof

structure AbsenceCertificate where
  header : TableHeader
  windows : List SlotOpening

def verifySlotOpening (H : Hash256) (header : TableHeader) (o : SlotOpening) : Bool :=
  match header.rows[o.coordinate.1]? with
  | none => false
  | some (n, root) => decide (o.proof.count = n) &&
    verifyExpVerkleOpening H root o.coordinate.2 (slotWord H o.state) o.proof

/-- Root-only authentication: exactly the complete bounded probe window, including
empty slots, is opened. Neither a trusted table nor a trusted slot state is an input. -/
def verifyExpVerkleAbsence (H : Hash256) (root : Digest) (k : Key) (c : AbsenceCertificate) : Bool :=
  decide (H (headerBytes c.header) = root ∧ c.windows.map SlotOpening.coordinate = headerCoords c.header k) &&
  c.windows.all (fun o => verifySlotOpening H c.header o &&
    match o.state with | none => true | some (key, _) => decide (key ≠ k))

def openSlot (H : Hash256) (t : ElasticOpenTable) (p : PhysSlot) : SlotOpening :=
  ⟨p, getSlot t p, openExpVerkle H (rowForest H t.levels[p.1]!) p.2⟩

def proveAbsence (H : Hash256) (t : ElasticOpenTable) (k : Key) : AbsenceCertificate :=
  ⟨tableHeader H t, (probeCoords t k).map (openSlot H t)⟩

theorem openSlot_complete (H : Hash256) (t : ElasticOpenTable) (p : PhysSlot) (hb : InBounds t p) :
    verifySlotOpening H (tableHeader H t) (openSlot H t p) = true := by
  obtain ⟨row, hr, hs⟩ := hb
  have hv : (rowForest H row).entries[p.2]? = some (slotWord H (getSlot t p)) := by
    simp [rowForest, getSlot, hr, Array.getElem?_eq_getElem hs]
  have he := verifyExpVerkleOpening_complete H (rowForest H row) _ p.2 _ (expVerkleDepth_covers _) hv rfl
  simpa [verifySlotOpening, openSlot, tableHeader, Array.getElem?_map, hr,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, openExpVerkle, proveExpVerkle,
    rowForest, commitExpVerkle] using he

theorem verifyAbsence_complete (H : Hash256) (t : ElasticOpenTable) (k : Key) (hn : lookup t k = none) :
    verifyExpVerkleAbsence H (tableDigest H t) k (proveAbsence H t k) = true := by
  have hn := (lookup_none_iff t k).mp hn
  simp only [verifyExpVerkleAbsence, proveAbsence, Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    constructor
    · rfl
    · simp [openSlot, List.map_map, headerCoords_eq, Function.comp_def]
  · apply List.all_eq_true.mpr
    intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
    rw [Bool.and_eq_true]
    refine ⟨openSlot_complete H t p (probeCoords_inBounds t k p hp), ?_⟩
    change (match getSlot t p with | none => true | some (key, _) => decide (key ≠ k)) = true
    cases hg : getSlot t p with
    | none => rfl
    | some e =>
      apply decide_eq_true
      intro he
      exact hn p hp e.2 (hg.trans (congrArg some (Prod.ext he rfl)))

def slotOpeningPreimages (H : Hash256) (t : ElasticOpenTable) (o : SlotOpening) : List (List UInt8) :=
  slotBytes o.state :: slotBytes (getSlot t o.coordinate) ::
    (openingPreimages o.proof o.coordinate.2 (slotWord H o.state) ++
      openingPreimages (openSlot H t o.coordinate).proof o.coordinate.2
        (slotWord H (getSlot t o.coordinate)))

def absencePreimages (H : Hash256) (t : ElasticOpenTable) (c : AbsenceCertificate) : List (List UInt8) :=
  headerBytes c.header :: headerBytes (tableHeader H t) :: c.windows.flatMap (slotOpeningPreimages H t)

/-- A forged slot either agrees with the committed row or yields an explicit
collision from the two openings or the two slot encodings. -/
def extractSlotCollision (H : Hash256) (t : ElasticOpenTable) (o : SlotOpening)
    (hb : InBounds t o.coordinate) (hv : verifySlotOpening H (tableHeader H t) o = true)
    (hne : o.state ≠ getSlot t o.coordinate) : ScopedCollision H (slotOpeningPreimages H t o) := by
  let row := t.levels[o.coordinate.1]!
  have hr : t.levels[o.coordinate.1]? = some row := by
    obtain ⟨r, hr, _⟩ := hb
    simp [row, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hr]
  have hs : o.coordinate.2 < row.size := by
    obtain ⟨r, hr', hs⟩ := hb
    rw [hr] at hr'
    cases Option.some.inj hr'
    exact hs
  have hg : (rowForest H row).entries[o.coordinate.2]? = some (slotWord H (getSlot t o.coordinate)) := by
    simp [rowForest, getSlot, hr, Array.getElem?_eq_getElem hs]
  have honest := verifyExpVerkleOpening_complete H (rowForest H row) _ o.coordinate.2 _
    (expVerkleDepth_covers _) hg rfl
  simp only [verifySlotOpening, tableHeader, Array.getElem?_map, hr, Option.map_some,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  if he : slotWord H o.state = slotWord H (getSlot t o.coordinate) then
    exact ⟨⟨_, _, fun hh => hne (slotBytes_injective hh), digestWord_injective he⟩,
      by simp [slotOpeningPreimages], by simp [slotOpeningPreimages]⟩
  else
    apply widenCollision (extractOpeningCollision H _ _ _ _ o.proof _ he hv.2 honest)
    intro m hm
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

/-- The reduction returns concrete collision data, scoped to the submitted certificate
and the authentic table by the extractor; successful absence covers every scheduled slot. -/
theorem verifyAbsence_sound_or_collision (H : Hash256) (t : ElasticOpenTable) (k : Key)
    (c : AbsenceCertificate) (hc : verifyExpVerkleAbsence H (tableDigest H t) k c = true) :
    lookup t k = none ∨ Nonempty (ScopedCollision H (absencePreimages H t c)) := by
  simp only [verifyExpVerkleAbsence, Bool.and_eq_true, decide_eq_true_eq] at hc
  by_cases hh : c.header = tableHeader H t
  · have coords : c.windows.map SlotOpening.coordinate = probeCoords t k := by
      simpa [hh, headerCoords_eq] using hc.1.2
    by_cases hn : lookup t k = none
    · exact .inl hn
    · right
      cases hs : search t k (probeCoords t k) with
      | none => exact False.elim (hn (by simp [lookup, hs]))
      | some e =>
        have hit := search_sound t k _ e.1 e.2 hs
        have hm : e.1 ∈ c.windows.map SlotOpening.coordinate := coords.symm ▸ hit.1
        obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
        have hv := List.all_eq_true.mp hc.2 o ho
        simp only [Bool.and_eq_true] at hv
        have hne : o.state ≠ getSlot t o.coordinate := by
          intro eq
          have hx : getSlot t o.coordinate = some (k, e.2) := he ▸ hit.2
          rw [eq, hx] at hv
          simp at hv
        refine ⟨widenCollision (extractSlotCollision H t o (he ▸ probeCoords_inBounds t k e.1 hit.1)
          (by simpa [hh] using hv.1) hne) ?_⟩
        intro m hm
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨o, ho, hm⟩))
  · exact .inr ⟨⟨⟨_, _, fun he => hh (headerBytes_injective he), hc.1.1⟩,
      by simp [absencePreimages], by simp [absencePreimages]⟩⟩

/-- The deployed vault wire uses the existing total codec and preserves physical array shape. -/
def wordCodec : ChunkedWorld.FastCodec (BitVec 256) :=
  ChunkedWorld.cMap BitVec.toNat (fun n => if n < 2 ^ 256 then some (BitVec.ofNat 256 n) else none)
    (by intro w; simp [w.isLt]) ChunkedWorld.cNat

def tableCodec : ChunkedWorld.FastCodec ElasticOpenTable :=
  ChunkedWorld.cMap (fun t => (t.levels, t.seed)) (fun a => some ⟨a.1, a.2⟩) (by intro t; rfl)
    (ChunkedWorld.cPair (ChunkedWorld.cArray (ChunkedWorld.cArray
      (ChunkedWorld.cOption (ChunkedWorld.cPair wordCodec wordCodec)))) wordCodec)

def forestCodec : ChunkedWorld.FastCodec ExpVerkleForestExec :=
  ChunkedWorld.cMap ExpVerkleForestExec.entries (fun a => some ⟨a⟩) (by intro f; rfl)
    (ChunkedWorld.cArray wordCodec)

def snapshotPayloadCodec := ChunkedWorld.cPair tableCodec forestCodec

def snapshotWireTag : String := "exp-verkle-openhash@2"

/-- Replace the prior typed snapshot record; preserve unrelated transport records and world data. -/
def exportToChunkedWorld (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) : ChunkedWorld.World :=
  { w with received := (snapshotWireTag, Json.hex (snapshotPayloadCodec.enc (t, f))) :: w.received.filter (fun r => r.1 != snapshotWireTag) }

theorem exportToChunkedWorld_idempotent (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) :
    exportToChunkedWorld (exportToChunkedWorld w t f) t f = exportToChunkedWorld w t f := by
  simp [exportToChunkedWorld, List.filter_filter]

def importFromChunkedWorld (w : ChunkedWorld.World) : Option (ElasticOpenTable × ExpVerkleForestExec) := do
  let (tag, text) ← w.received.head?
  if tag ≠ snapshotWireTag then none else
    let bs ← Json.unhex text.toList
    snapshotPayloadCodec.decodeExact bs

theorem exportToChunkedWorld_roundtrip (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) : importFromChunkedWorld (exportToChunkedWorld w t f) = some (t, f) := by
  simp [importFromChunkedWorld, exportToChunkedWorld, ChunkedWorld.unhex_hex,
    ChunkedWorld.FastCodec.decodeExact_enc]

theorem exported_checkpoint_roundtrip (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) :
    ChunkedWorld.decodeShardedWorld (ChunkedWorld.encodeShardedWorld (exportToChunkedWorld w t f)) =
      .ok (exportToChunkedWorld w t f) := ChunkedWorld.decodeShardedWorld_encodeShardedWorld _

/-- Reuse the existing dirty-bucket cache rather than create a second snapshot format. -/
def exportIncremental (w : ChunkedWorld.World) (t : ElasticOpenTable) (f : ExpVerkleForestExec)
    (previous : Option (Array ChunkedWorld.CachedBucket)) : ByteArray × Array ChunkedWorld.CachedBucket :=
  ChunkedWorld.encodeWorldIncremental (exportToChunkedWorld w t f) previous

theorem exportIncremental_manifest (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (previous : Option (Array ChunkedWorld.CachedBucket)) :
    (exportIncremental w t f previous).1.data.toList =
      ChunkedWorld.manifestBytes (exportToChunkedWorld w t f) :=
  ChunkedWorld.encodeWorldIncremental_manifest_eq _ _

/-- This is the actual full-address-space UMem root supplied by the existing snapshot bridge. -/
def bindVerkleUmemRoot (w : ChunkedWorld.World) : Digest :=
  ⟨VerkleSnapshotBridge.fullVerkleCommitChunks (VerkleSnapshotBridge.materializeWorldChunks w),
    VerkleSnapshotBridge.fullVerkleCommitChunks_size _⟩

def snapshotRam (w : ChunkedWorld.World) : Obend.Polis.ExtRam :=
  VerkleSnapshotBridge.chunksToExtRam (VerkleSnapshotBridge.materializeWorldChunks w)

theorem bindVerkleUmemRoot_preserves (w : ChunkedWorld.World) :
    (bindVerkleUmemRoot w).val = VerkleSnapshotBridge.specExtRamTreeTag (snapshotRam w) 16 0 :=
  VerkleSnapshotBridge.fullVerkleCommitChunks_eq_specExtRamRoot _

/-- Stable pointers contain physical coordinates, not insertion-order indices. -/
structure SlotPointer where
  coordinate : PhysSlot
  key : Key
  value : Val
  deriving DecidableEq

def verifySlotPointer (t : ElasticOpenTable) (p : SlotPointer) : Bool :=
  decide (p.coordinate ∈ probeCoords t p.key ∧ getSlot t p.coordinate = some (p.key, p.value))

theorem verifySlotPointer_sound (t : ElasticOpenTable) (p : SlotPointer)
    (h : verifySlotPointer t p = true) : getSlot t p.coordinate = some (p.key, p.value) := by
  simp only [verifySlotPointer, decide_eq_true_eq] at h
  exact h.2

theorem verifySlotPointer_complete (t : ElasticOpenTable) (p : SlotPointer)
    (hw : TableWF t) (h : getSlot t p.coordinate = some (p.key, p.value)) :
    verifySlotPointer t p = true := by
  simp [verifySlotPointer, hw _ _ _ h, h]

theorem slotPointer_multiTurn (t : ElasticOpenTable) (p : SlotPointer) (xs : List (Key × Val))
    (h : verifySlotPointer t p = true) :
    getSlot (insertSeq t xs) p.coordinate = some (p.key, p.value) :=
  insertSeq_preserves_all_prior_slots _ _ _ _ (verifySlotPointer_sound _ _ h)


/-- A physical slot and its append-log position are distinct coordinates, both retained. -/
structure VaultSlotLink where
  pointer : SlotPointer
  entryIndex : Nat

abbrev VaultState := ElasticOpenTable × ExpVerkleForestExec

def VaultLinkValid (s : VaultState) (link : VaultSlotLink) : Prop :=
  getSlot s.1 link.pointer.coordinate = some (link.pointer.key, link.pointer.value) ∧
  s.2.entries[link.entryIndex]? = some link.pointer.value

/-- Exactly one log append on a new physical insertion; duplicate and full-window refusals
leave both carriers unchanged. The returned physical slot links to the old array size. -/
def appendVault (s : VaultState) (k : Key) (v : Val) : VaultState × InsertResult :=
  let result := insert s.1 k v
  match result.2 with
  | .inserted p => ((result.1, appendExpVerkle s.2 v), .inserted p)
  | other => ((result.1, s.2), other)

theorem insert_placed (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (h : (insert t k v).2 = .inserted p) : getSlot (insert t k v).1 p = some (k, v) := by
  unfold insert at h ⊢
  cases hs : search t k (probeCoords t k) with
  | some e => simp only [hs] at h; split at h <;> cases h
  | none =>
    simp only [hs] at h ⊢
    cases hq : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
    | none => simp [hq] at h
    | some q =>
      simp only [hq, InsertResult.inserted.injEq] at h
      subst q
      have hm := List.mem_of_find?_eq_some hq
      have hn := List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hq
      simpa [hq] using fillSlot_same t p (k, v) (probeCoords_inBounds t k p hm)
        (Option.isNone_iff_eq_none.mp hn)

theorem appendVault_inserted (s : VaultState) (k : Key) (v : Val) (p : PhysSlot)
    (h : (insert s.1 k v).2 = .inserted p) :
    VaultLinkValid (appendVault s k v).1 ⟨⟨p, k, v⟩, s.2.entries.size⟩ := by
  simp only [appendVault, h, VaultLinkValid]
  exact ⟨insert_placed _ _ _ _ h, by simp [appendExpVerkle]⟩

theorem appendVault_preserves_links (s : VaultState) (k : Key) (v : Val) (link : VaultSlotLink)
    (h : VaultLinkValid s link) : VaultLinkValid (appendVault s k v).1 link := by
  have hslot := insert_preserves_all_prior_slots s.1 k v link.pointer.coordinate
    (link.pointer.key, link.pointer.value) h.1
  have hi := (Array.getElem?_eq_some_iff.mp h.2).1
  cases hr : (insert s.1 k v).2 with
  | inserted p =>
    simpa [appendVault, hr, VaultLinkValid] using
      And.intro hslot ((appendExpVerkle_preserves _ v _ hi).trans h.2)
  | alreadyPresent p => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2
  | conflict old => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2
  | tableFull => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2

def appendVaultSeq (s : VaultState) : List (Key × Val) → VaultState
  | [] => s
  | (k, v) :: xs => appendVaultSeq (appendVault s k v).1 xs

theorem appendVaultSeq_preserves_links (s : VaultState) (xs : List (Key × Val))
    (link : VaultSlotLink) (h : VaultLinkValid s link) :
    VaultLinkValid (appendVaultSeq s xs) link := by
  induction xs generalizing s with
  | nil => exact h
  | cons e xs ih => exact ih _ (appendVault_preserves_links s e.1 e.2 link h)

theorem vaultLink_opens (H : Hash256) (s : VaultState) (link : VaultSlotLink)
    (h : VaultLinkValid s link) :
    verifyExpVerkleOpening H (commitExpVerkle H s.2) link.entryIndex link.pointer.value
      (openExpVerkle H s.2 link.entryIndex) = true :=
  verifyExpVerkleOpening_complete H s.2 _ _ _ (expVerkleDepth_covers _) h.2 rfl

/-- The weld commits all three roots, not a truncated limb or an equality between unrelated trees. -/
def weldBytes (forest table umem : Digest) : List UInt8 :=
  frameBytes [[11], forest.val.data.toList, table.val.data.toList, umem.val.data.toList]

theorem weldBytes_injective {a b c x y z : Digest}
    (h : weldBytes a b c = weldBytes x y z) : a = x ∧ b = y ∧ c = z := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨digest_bytes_injective hf.1, digest_bytes_injective hf.2.1,
    digest_bytes_injective hf.2.2⟩

structure ExpVerkleVaultSnapshot where
  world : ChunkedWorld.World
  table : ElasticOpenTable
  forest : ExpVerkleForestExec
  height : Nat
  forestRoot : Digest
  tableRoot : Digest
  umemRoot : Digest
  root : Digest

def allSlotCoords (t : ElasticOpenTable) : List PhysSlot :=
  (List.range t.levels.size).flatMap fun l => (List.range t.levels[l]!.size).map fun j => (l,j)

theorem getSlot_mem_coords (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val)
    (h : getSlot t p = some e) : p ∈ allSlotCoords t := by
  cases hr : t.levels[p.1]? with
  | none => simp [getSlot, hr] at h
  | some row =>
    have hl := (Array.getElem?_eq_some_iff.mp hr).1
    cases hs : row[p.2]? with
    | none => simp [getSlot, hr, hs] at h
    | some state =>
      have hj := (Array.getElem?_eq_some_iff.mp hs).1
      apply List.mem_flatMap.mpr
      refine ⟨p.1, List.mem_range.mpr hl, List.mem_map.mpr ⟨p.2, ?_, Prod.eta _⟩⟩
      simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hr] using List.mem_range.mpr hj

/-- Every live key is reachable, and its value is present in the authenticated append log.
This is a materialized consistency audit, not a proof of a unique historical operation trace. -/
def TableLinked (t : ElasticOpenTable) (f : ExpVerkleForestExec) : Prop :=
  ∀ p k v, getSlot t p = some (k,v) → p ∈ probeCoords t k ∧ v ∈ f.entries.toList

def forestValueIndex (f : ExpVerkleForestExec) : Std.TreeSet Nat :=
  Std.TreeSet.ofList (f.entries.toList.map BitVec.toNat) compare

theorem forestValueIndex_contains (f : ExpVerkleForestExec) (v : Val) :
    (forestValueIndex f).contains v.toNat = true ↔ v ∈ f.entries.toList := by
  simp only [forestValueIndex, Std.TreeSet.contains_ofList, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    exact (BitVec.eq_of_toNat_eq he) ▸ hx
  · intro h; exact ⟨v,h,rfl⟩

/-- Build the balanced value index once, then scan slots with logarithmic value queries. -/
def checkSnapshotTable (t : ElasticOpenTable) (f : ExpVerkleForestExec) : Bool :=
  let values := forestValueIndex f
  (allSlotCoords t).all fun p => match getSlot t p with
    | none => true
    | some (k,v) => decide (p ∈ probeCoords t k) && values.contains v.toNat

theorem checkSnapshotTable_iff (t : ElasticOpenTable) (f : ExpVerkleForestExec) :
    checkSnapshotTable t f = true ↔ TableLinked t f := by
  simp only [checkSnapshotTable, List.all_eq_true]
  constructor
  · intro h p k v hv
    have hh := h p (getSlot_mem_coords t p (k,v) hv)
    simpa only [hv, Bool.and_eq_true, decide_eq_true_eq, forestValueIndex_contains] using hh
  · intro h p _
    cases hg : getSlot t p with
    | none => rfl
    | some e => simpa only [Bool.and_eq_true, decide_eq_true_eq, forestValueIndex_contains] using h p e.1 e.2 hg

theorem TableLinked.wf {t : ElasticOpenTable} {f : ExpVerkleForestExec} (h : TableLinked t f) : TableWF t :=
  fun p k v hv => (h p k v hv).1

/-- Semantic consistency is stated as concrete commitment and capacity equations. -/
def SnapshotMeaning (H : Hash256) (s : ExpVerkleVaultSnapshot) : Prop :=
  TableLinked s.table s.forest ∧ s.forest.entries.size ≤ capacity s.height ∧
  s.forestRoot = expVerkleRoot H s.forest s.height ∧
  s.tableRoot = tableDigest H s.table ∧
  s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest) ∧
  s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot)

def verifySnapshot (H : Hash256) (s : ExpVerkleVaultSnapshot) : Bool :=
  checkSnapshotTable s.table s.forest && decide (s.forest.entries.size ≤ capacity s.height) &&
  decide (s.forestRoot = expVerkleRoot H s.forest s.height) &&
  decide (s.tableRoot = tableDigest H s.table) &&
  decide (s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest)) &&
  decide (s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot))

theorem verifySnapshot_iff (H : Hash256) (s : ExpVerkleVaultSnapshot) :
    verifySnapshot H s = true ↔ SnapshotMeaning H s := by
  simp [verifySnapshot, SnapshotMeaning, checkSnapshotTable_iff, and_assoc]

def buildSnapshot (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) : ExpVerkleVaultSnapshot :=
  let fr := expVerkleRoot H f height
  let tr := tableDigest H t
  let ur := bindVerkleUmemRoot (exportToChunkedWorld w t f)
  ⟨w, t, f, height, fr, tr, ur, H (weldBytes fr tr ur)⟩

theorem buildSnapshot_complete (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) (hc : f.entries.size ≤ capacity height) (hl : TableLinked t f) :
    verifySnapshot H (buildSnapshot H w t f height) = true := by
  simp [verifySnapshot, buildSnapshot, hc, (checkSnapshotTable_iff t f).mpr hl]

inductive SnapshotRefusal where
  | inconsistentCommitment
  deriving DecidableEq, Repr

/-- Total exact audit of a materialized snapshot. Refusal refutes its semantic consistency. -/
@[expose, instance_reducible] def expVerkleVaultJudge (H : Hash256) : Obend.Judge ExpVerkleVaultSnapshot Unit where
  Clause := SnapshotRefusal
  Meaning s _ := SnapshotMeaning H s
  check _ s _ := if verifySnapshot H s then .ok else .refused .inconsistentCommitment []
  sound := by
    intro _ s _ h
    split at h
    next ht => exact (verifySnapshot_iff H s).mp ht
    next => cases h
  refutes := fun _ => true
  refuted := by
    intro _ s _ _ _ h _ _ hm
    have ht := (verifySnapshot_iff H s).mpr hm
    simp [ht] at h
  Fragment := fun _ => True
  complete := by
    intro s _ h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, 0, by simp [(verifySnapshot_iff H s).mpr hc]⟩
  mono := by intros; rfl

theorem snapshot_refusal (H : Hash256) (s : ExpVerkleVaultSnapshot)
    (h : s.umemRoot ≠ bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest))
    (grade : Nat) : (expVerkleVaultJudge H).check grade s () = .refused SnapshotRefusal.inconsistentCommitment [] := by
  change (if verifySnapshot H s = true then Obend.Judge.Verdict.ok else
    Obend.Judge.Verdict.refused SnapshotRefusal.inconsistentCommitment []) = _
  have hf : verifySnapshot H s = false := by simp [verifySnapshot, h]
  rw [hf]
  rfl

end Obend.Vault.ExpVerkleAndOpenHash

end
