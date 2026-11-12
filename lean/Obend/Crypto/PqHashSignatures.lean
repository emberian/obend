module
/-
# Obend.Crypto.PqHashSignatures — Tweakable Hash Suites, `TSW` (`WOTS+C`), `leanSPHINCS`, `leanSig` & `HybridPinnedSig`
Clean-room 0-axiom specification of stateless (`leanSPHINCS` / `SLH-DSA`) and stateful (`leanSig`) hash signatures:
1. Pre-locked 32-byte BE `HashAdrs` framing (`encodeAdrs_injective`);
2. Polymorphic `TweakableHashSuite` (`cshake256Suite`, `poseidon2Suite`, `thCall_binds_or_collision`);
3. Target-Sum Winternitz (`TSW` / `WOTS+C`, `tsw_incomparable_no_chain_forgery`);
4. FORS, XMSS, `evalSingleSign`, `verifyPqHashSig` (`verifyPqHashSig_evalSingleSign`), `0 Classical` `PSum` extractor `extractPqHashForgery`, and `ValidLeanSigBatch`;
5. Committed-identity `HybridPinnedSig` (`hybrid_ucRealizes_if_either_secure`, `selfCarried_pq_key_substitution_refuted`) & tri-state `VerifyReply` (`verifyWire_malformed_iff`).
-/
public import Obend.Digest.Cshake256
public import Obend.Crypto.Poseidon2Goldilocks
public import Obend.Crypto.ThresholdMpcUcGames
public import Obend.Judge.Computational

public section
namespace Obend.Crypto.PqHashSignatures

open Obend
open Obend.Crypto
open Obend.Crypto.ThresholdMpcUcGames
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Judge.Computational

set_option autoImplicit false

/-! ## 1. Pre-Locked 32-Byte Big-Endian `HashAdrs` Framing (`encodeAdrs_injective`) -/

/-- Domain-separation role of a 32-byte hash address inside the hypertree / FORS / WOTS+C hierarchy. -/
inductive AdrsKind where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
  deriving DecidableEq, Repr

/-- Canonical 32-bit wire tag for `AdrsKind`. -/
def AdrsKind.toCode : AdrsKind → UInt32
  | .wotsHash => 0 | .wotsPk => 1 | .tree => 2 | .forsTree => 3
  | .forsRoots => 4 | .wotsPrf => 5 | .forsPrf => 6

theorem AdrsKind.toCode_injective {k₁ k₂ : AdrsKind} (h : k₁.toCode = k₂.toCode) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | cases h

/-- Canonical 32-byte tweakable hash address (`ADRS`):
    `[0..4) layer || [4..8) 0 || [8..16) tree || [16..20) kind || [20..24) keyPair || [24..28) chainIdx || [28..32) hashStep`. -/
structure HashAdrs where
  layer : UInt32
  tree : UInt64
  kind : AdrsKind
  keyPair : UInt32
  chainIdx : UInt32
  hashStep : UInt32
  deriving DecidableEq, Repr

/-- Encode `HashAdrs` into its exact 32-byte big-endian frame. -/
@[expose] def encodeAdrs (a : HashAdrs) : List UInt8 :=
  be 4 a.layer.toNat ++ (be 4 0 ++ (be 8 a.tree.toNat ++
    (be 4 a.kind.toCode.toNat ++ (be 4 a.keyPair.toNat ++
      (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat)))))

theorem encodeAdrs_length (a : HashAdrs) : (encodeAdrs a).length = 32 := by
  simp [encodeAdrs, length_be]

private theorem uint32_eq_of_be4_eq {x y : UInt32} (h : be 4 x.toNat = be 4 y.toNat) : x = y := by
  have hx : x.toNat < 256 ^ 4 := by simpa using x.toBitVec.isLt
  have hy : y.toNat < 256 ^ 4 := by simpa using y.toBitVec.isLt
  exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (be_injective hx hy h))

private theorem uint64_eq_of_be8_eq {x y : UInt64} (h : be 8 x.toNat = be 8 y.toNat) : x = y := by
  have hx : x.toNat < 256 ^ 8 := by simpa using x.toBitVec.isLt
  have hy : y.toNat < 256 ^ 8 := by simpa using y.toBitVec.isLt
  exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (be_injective hx hy h))

/-- **Pre-Locked `ADRS` Framing Injectivity (`encodeAdrs_injective`)**:
    Distinct `HashAdrs` values NEVER collide before hashing; omitting or zeroing any field
    (such as `chainIdx`) breaks this theorem immediately (`#tooth` witness #3). -/
theorem encodeAdrs_injective {a₁ a₂ : HashAdrs} (h : encodeAdrs a₁ = encodeAdrs a₂) : a₁ = a₂ := by
  unfold encodeAdrs at h
  obtain ⟨hLayer, h1⟩ := List.append_inj h (by simp [length_be])
  obtain ⟨_, h2⟩ := List.append_inj h1 (by simp [length_be])
  obtain ⟨hTree, h3⟩ := List.append_inj h2 (by simp [length_be])
  obtain ⟨hKind, h4⟩ := List.append_inj h3 (by simp [length_be])
  obtain ⟨hKp, h5⟩ := List.append_inj h4 (by simp [length_be])
  obtain ⟨hChain, hStep⟩ := List.append_inj h5 (by simp [length_be])
  cases a₁; cases a₂; simp only [HashAdrs.mk.injEq]
  exact ⟨uint32_eq_of_be4_eq hLayer, uint64_eq_of_be8_eq hTree,
         AdrsKind.toCode_injective (uint32_eq_of_be4_eq hKind),
         uint32_eq_of_be4_eq hKp, uint32_eq_of_be4_eq hChain, uint32_eq_of_be4_eq hStep⟩

/-! ## 2. Polymorphic `TweakableHashSuite` (`cshake256Suite` & `poseidon2Suite`) -/

/-- Polymorphic 256-bit tweakable hash suite abstracting `cSHAKE256` and `Poseidon2Goldilocks`. -/
structure TweakableHashSuite where
  suiteId : List UInt8
  rawHash : Hash
  rawHash_len : ∀ msg : List UInt8, (rawHash msg).length = 32

def pqCshakeSuiteCustom : List UInt8 := "OBEND.PQ.SUITE.CSHAKE256/v1".toUTF8.data.toList
def pqPoseidon2SuiteId  : List UInt8 := "OBEND.PQ.SUITE.POSEIDON2/v1".toUTF8.data.toList

/-- NIST SP 800-185 `cSHAKE256` instantiation (`SLH-DSA` / `leanSPHINCS-cSHAKE256`). -/
@[expose] def cshake256Suite : TweakableHashSuite where
  suiteId := pqCshakeSuiteCustom
  rawHash := cshake256Bytes pqCshakeSuiteCustom
  rawHash_len := cshake256Bytes_length pqCshakeSuiteCustom

/-- Width-12 `Poseidon2Goldilocks` algebraic instantiation (`leanSig` / `leanSPHINCS-Poseidon2`). -/
@[expose] def poseidon2Suite : TweakableHashSuite where
  suiteId := pqPoseidon2SuiteId
  rawHash := poseidon2Hash32
  rawHash_len := poseidon2Hash32_length

def tagPrfMsg : List UInt8 := "OBEND.PQ.PRFMSG/v1".toUTF8.data.toList
def tagHMsg   : List UInt8 := "OBEND.PQ.HMSG/v1".toUTF8.data.toList
def tagPrf    : List UInt8 := "OBEND.PQ.PRF/v1".toUTF8.data.toList
def tagThF    : List UInt8 := "OBEND.PQ.TH_F/v1".toUTF8.data.toList
def tagThH    : List UInt8 := "OBEND.PQ.TH_H/v1".toUTF8.data.toList
def tagThTl   : List UInt8 := "OBEND.PQ.TH_TL/v1".toUTF8.data.toList
def tagHPre   : List UInt8 := "OBEND.PQ.PRE/v1".toUTF8.data.toList

/-- Concatenate LEB128 length-prefixed byte fields `leb128(|f_i|) || f_i`. -/
def encodeByteFields : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => encodeListField x ++ encodeByteFields xs

/-- Self-delimiting multi-field byte frame `leb128(count) || encodeByteFields fields`. -/
def encodeMultiFrame (fields : List (List UInt8)) : List UInt8 :=
  leb128 fields.length ++ encodeByteFields fields

private theorem encodeByteFields_inj_of_len :
    ∀ {xs ys : List (List UInt8)},
      xs.length = ys.length → encodeByteFields xs = encodeByteFields ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [encodeByteFields] at hEq
    obtain ⟨hx, hRest⟩ := encodeListField_prefix_inj hEq
    have hTail := encodeByteFields_inj_of_len hLen hRest
    subst hx hTail; rfl

theorem encodeMultiFrame_injective {xs ys : List (List UInt8)}
    (h : encodeMultiFrame xs = encodeMultiFrame ys) : xs = ys := by
  obtain ⟨hLen, hBody⟩ := leb128_prefix_inj h
  exact encodeByteFields_inj_of_len hLen hBody

/-- Self-delimiting preimage for any tweakable hash call `(roleTag, pkSeed, adrs, args)`. -/
def thPreimage (roleTag pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) : List UInt8 :=
  encodeMultiFrame ([roleTag, pkSeed, encodeAdrs adrs] ++ args)

/-- Evaluate a tweakable hash call with full `ADRS` and `pkSeed` domain separation. -/
def thCall (suite : TweakableHashSuite) (roleTag pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) : List UInt8 :=
  suite.rawHash (thPreimage roleTag pkSeed adrs args)

theorem thCall_length (suite : TweakableHashSuite) (roleTag pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) :
    (thCall suite roleTag pkSeed adrs args).length = 32 :=
  suite.rawHash_len _

theorem thPreimage_injective {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (h : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂) :
    t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂ := by
  have hList := encodeMultiFrame_injective h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hList
  rcases hList with ⟨ht, hp, ha, hxs⟩
  exact ⟨ht, hp, encodeAdrs_injective ha, hxs⟩

/-- Constructive `0 Classical` collision binder for `thCall`. -/
def thCall_binds_or_collision (suite : TweakableHashSuite) (maxBytes : Nat)
    {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (hLen₁ : (thPreimage t₁ p₁ a₁ xs₁).length ≤ maxBytes)
    (hLen₂ : (thPreimage t₂ p₂ a₂ xs₂).length ≤ maxBytes)
    (hEq : thCall suite t₁ p₁ a₁ xs₁ = thCall suite t₂ p₂ a₂ xs₂) :
    PSum (t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂)
         (HashCollisionWitness suite.rawHash maxBytes) :=
  if hPre : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂ then
    .inl (thPreimage_injective hPre)
  else
    .inr { msgA := thPreimage t₁ p₁ a₁ xs₁, msgB := thPreimage t₂ p₂ a₂ xs₂,
           lenA := hLen₁, lenB := hLen₂, distinct := hPre, sameDigest := congrArg ofBE hEq }

def thChainF (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (x : List UInt8) : List UInt8 :=
  thCall suite tagThF pkSeed adrs [x]

def thNodeH (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (l r : List UInt8) : List UInt8 :=
  thCall suite tagThH pkSeed adrs [l, r]

def thTweakTl (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (limbs : List (List UInt8)) : List UInt8 :=
  thCall suite tagThTl pkSeed adrs limbs

def thSecretPrf (suite : TweakableHashSuite) (pkSeed skSeed : List UInt8) (adrs : HashAdrs) : List UInt8 :=
  thCall suite tagPrf pkSeed adrs [skSeed]

def zeroAdrs : HashAdrs := ⟨0, 0, .wotsHash, 0, 0, 0⟩

def thPrfMsg (suite : TweakableHashSuite) (skPrf optRand mu : List UInt8) : List UInt8 :=
  thCall suite tagPrfMsg [] zeroAdrs [skPrf, optRand, mu]

def thPreHash (suite : TweakableHashSuite) (pkSeed pkRoot msg : List UInt8) : List UInt8 :=
  thCall suite tagHPre pkSeed zeroAdrs [pkRoot, msg]

def thHashMsg (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (layerIdx : UInt32) (treeIdx : UInt64) (ctr : Nat) : List UInt8 :=
  thCall suite tagHMsg pkSeed ⟨layerIdx, treeIdx, .wotsHash, 0, 0, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr]

/-! ## 3. Target-Sum Winternitz (`TSW` / `WOTS+C`) & Incomparability Theorem -/

/-- Sum of base-`w` message digits. -/
def sumDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + sumDigits ds

/-- Canonical `TSW` target sum `⌊ell1 * (w - 1) / 2⌋` eliminating checksum chains. -/
def canonicalTargetSum (w ell1 : Nat) : Nat :=
  (ell1 * (w - 1)) / 2

/-- **Load-Bearing `TSW` Checker (`checkTargetSum`)**:
    Verifies exact chain count `ell1`, range `∀ d, d < w`, and constant sum `sumDigits digits = target`.
    Mutating this checker to omit `sumDigits digits = target` is caught by `#tooth` witness #1. -/
@[expose] def checkTargetSum (w ell1 target : Nat) (digits : List Nat) : Bool :=
  decide (digits.length = ell1) &&
  digits.all (fun d => decide (d < w)) &&
  decide (sumDigits digits = target)

theorem checkTargetSum_iff (w ell1 target : Nat) (digits : List Nat) :
    checkTargetSum w ell1 target digits = true ↔
      digits.length = ell1 ∧ (∀ d ∈ digits, d < w) ∧ sumDigits digits = target := by
  simp only [checkTargetSum, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

private theorem exists_lt_coord_of_sum_le_and_ne :
    ∀ (d₁ d₂ : List Nat),
      d₁.length = d₂.length →
      sumDigits d₁ ≤ sumDigits d₂ →
      (sumDigits d₁ < sumDigits d₂ ∨ d₁ ≠ d₂) →
      ∃ (r : Nat) (hr₁ : r < d₁.length) (hr₂ : r < d₂.length), d₁[r]'hr₁ < d₂[r]'hr₂
  | [], [], _, hLe, hOr => by
    simp only [sumDigits] at hLe hOr
    rcases hOr with hLt | hNe
    · omega
    · exact False.elim (hNe rfl)
  | x :: xs, y :: ys, hLen, hLe, hOr => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [sumDigits] at hLe hOr
    if hxy : x < y then
      exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, hxy⟩
    else
      have hRestLe : sumDigits xs ≤ sumDigits ys := by omega
      have hRestOr : sumDigits xs < sumDigits ys ∨ xs ≠ ys := by
        if hyx : y < x then
          exact .inl (by omega)
        else
          have hEqXY : x = y := by omega
          subst hEqXY
          rcases hOr with hLt | hNe
          · exact .inl (by omega)
          · exact .inr (fun hEqXs => hNe (congrArg (x :: ·) hEqXs))
      obtain ⟨r, hr1, hr2, hStrict⟩ := exists_lt_coord_of_sum_le_and_ne xs ys hLen hRestLe hRestOr
      exact ⟨r + 1, Nat.succ_lt_succ hr1, Nat.succ_lt_succ hr2, hStrict⟩

/-- **Target-Sum Winternitz Incomparability Theorem (`tsw_incomparable_no_chain_forgery`)**:
    For ANY two distinct `TSW`-valid digit vectors `d₁ ≠ d₂` (`checkTargetSum w ell1 target = true`),
    `d₁` and `d₂` are strictly incomparable componentwise: there exists an index `r` where
    `d₁[r] < d₂[r]` AND an index `r'` where `d₂[r'] < d₁[r']`! -/
theorem tsw_incomparable_no_chain_forgery
    {w ell1 target : Nat} {d₁ d₂ : List Nat}
    (hValid₁ : checkTargetSum w ell1 target d₁ = true)
    (hValid₂ : checkTargetSum w ell1 target d₂ = true)
    (hDistinct : d₁ ≠ d₂) :
    (∃ (r : Nat) (hr₁ : r < d₁.length) (hr₂ : r < d₂.length),
      d₁[r]'hr₁ < d₂[r]'hr₂ ∧ d₂[r]'hr₂ < w) ∧
    (∃ (r' : Nat) (hr₂ : r' < d₂.length) (hr₁ : r' < d₁.length),
      d₂[r']'hr₂ < d₁[r']'hr₁ ∧ d₁[r']'hr₁ < w) := by
  obtain ⟨hLen₁, hBound₁, hSum₁⟩ := (checkTargetSum_iff w ell1 target d₁).mp hValid₁
  obtain ⟨hLen₂, hBound₂, hSum₂⟩ := (checkTargetSum_iff w ell1 target d₂).mp hValid₂
  have hLenEq : d₁.length = d₂.length := hLen₁.trans hLen₂.symm
  have hSumEq : sumDigits d₁ = sumDigits d₂ := hSum₁.trans hSum₂.symm
  obtain ⟨r, hr1, hr2, hLt12⟩ :=
    exists_lt_coord_of_sum_le_and_ne d₁ d₂ hLenEq (Nat.le_of_eq hSumEq) (.inr hDistinct)
  obtain ⟨r', hr2', hr1', hLt21⟩ :=
    exists_lt_coord_of_sum_le_and_ne d₂ d₁ hLenEq.symm (Nat.le_of_eq hSumEq.symm) (.inr hDistinct.symm)
  exact ⟨⟨r, hr1, hr2, hLt12, hBound₂ _ (List.getElem_mem hr2)⟩,
         ⟨r', hr2', hr1', hLt21, hBound₁ _ (List.getElem_mem hr1')⟩⟩

/-- Constructive coordinate finder returning the first index `r` where `d₂[r] < d₁[r]` (`0 Classical`). -/
def findBackwardCoord : List Nat → List Nat → Option Nat
  | x :: xs, y :: ys =>
    if y < x then some 0 else (findBackwardCoord xs ys).map (· + 1)
  | _, _ => none

theorem findBackwardCoord_complete :
    ∀ {d₁ d₂ : List Nat},
      (∃ (r : Nat) (hr₂ : r < d₂.length) (hr₁ : r < d₁.length), d₂[r]'hr₂ < d₁[r]'hr₁) →
      ∃ (r : Nat) (hr₂ : r < d₂.length) (hr₁ : r < d₁.length),
        findBackwardCoord d₁ d₂ = some r ∧ d₂[r]'hr₂ < d₁[r]'hr₁
  | [], _, ⟨_, _, hr₁, _⟩ => by cases hr₁
  | _, [], ⟨_, hr₂, _, _⟩ => by cases hr₂
  | x :: xs, y :: ys, hex => by
    simp only [findBackwardCoord]
    if hyx : y < x then
      exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simp [hyx], hyx⟩
    else
      simp only [hyx, ↓reduceIte]
      have hexTail : ∃ (r : Nat) (hr₂ : r < ys.length) (hr₁ : r < xs.length), ys[r]'hr₂ < xs[r]'hr₁ := by
        obtain ⟨r, hr₂, hr₁, hlt⟩ := hex
        cases r with
        | zero => exact False.elim (hyx hlt)
        | succ r' => exact ⟨r', Nat.lt_of_succ_lt_succ hr₂, Nat.lt_of_succ_lt_succ hr₁, hlt⟩
      obtain ⟨r', hr₂', hr₁', hSome, hlt'⟩ := findBackwardCoord_complete hexTail
      exact ⟨r' + 1, Nat.succ_lt_succ hr₂', Nat.succ_lt_succ hr₁', by simp [hSome], hlt'⟩

/-- Unpack bytes into `ell1` base-`w` digits (`w = 4` -> 2-bit crumbs, general `w` -> modular digits). -/
def extractBaseWDigits (w ell1 : Nat) (digestBytes : List UInt8) : List Nat :=
  let wSafe := if w < 2 then 4 else w
  (List.range ell1).map fun idx =>
    if wSafe = 4 then
      let byteIdx := (idx / 4) % (if digestBytes.length = 0 then 1 else digestBytes.length)
      let shift := (3 - (idx % 4)) * 2
      let b := (digestBytes.getD byteIdx 0).toNat
      (b / (2 ^ shift)) % 4
    else
      let byteIdx := idx % (if digestBytes.length = 0 then 1 else digestBytes.length)
      (digestBytes.getD byteIdx 0).toNat % wSafe

theorem extractBaseWDigits_bounds (w ell1 : Nat) (hw : 2 ≤ w) (digestBytes : List UInt8) :
    (extractBaseWDigits w ell1 digestBytes).length = ell1 ∧
    ∀ d ∈ extractBaseWDigits w ell1 digestBytes, d < w := by
  have hwNotLt : ¬ (w < 2) := by omega
  refine ⟨by simp [extractBaseWDigits], ?_⟩
  intro d hd
  simp only [extractBaseWDigits, hwNotLt, ↓reduceIte, List.mem_map] at hd
  obtain ⟨_, _, rfl⟩ := hd
  by_cases hw4 : w = 4
  · subst hw4
    simp only [↓reduceIte]
    exact Nat.mod_lt _ (by decide)
  · simp only [hw4, ↓reduceIte]
    exact Nat.mod_lt _ (by omega)

/-- Deterministic local CPU `TSW` counter grinder (`0` MPC gates). -/
def grindTswCounterAux (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64)
    (curCtr : Nat) : Nat → Option (Nat × List Nat × List UInt8)
  | 0 => none
  | fuel + 1 =>
    let hmsg := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx curCtr
    let digits := extractBaseWDigits w ell1 hmsg
    if checkTargetSum w ell1 target digits then
      some (curCtr, digits, hmsg)
    else
      grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx (curCtr + 1) fuel

theorem grindTswCounterAux_sound {suite : TweakableHashSuite} {w ell1 target : Nat}
    {rRand pkSeed pkRoot mu : List UInt8} {layerIdx : UInt32} {treeIdx : UInt64}
    {curCtr fuel ctr : Nat} {digits : List Nat} {hmsg : List UInt8}
    (h : grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx curCtr fuel =
          some (ctr, digits, hmsg)) :
    hmsg = thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx ctr ∧
    digits = extractBaseWDigits w ell1 hmsg ∧
    checkTargetSum w ell1 target digits = true := by
  induction fuel generalizing curCtr with
  | zero => cases h
  | succ fuel ih =>
    simp only [grindTswCounterAux] at h
    let hm := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx curCtr
    let dg := extractBaseWDigits w ell1 hm
    cases hChk : checkTargetSum w ell1 target dg
    · rw [show checkTargetSum w ell1 target (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx curCtr)) = false from hChk] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    · rw [show checkTargetSum w ell1 target (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx curCtr)) = true from hChk] at h
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, hChk⟩

private def zeroHashSuite : TweakableHashSuite := ⟨[], fun _ => List.replicate 32 0, fun _ => by simp⟩
example : ∃ out, grindTswCounterAux zeroHashSuite 2 1 0 [] [] [] [] 0 0 0 1 = some out := ⟨_, rfl⟩

/-! ## 4. WOTS+C Chains, FORS, XMSS, `leanSPHINCS` (`THINCS` / `128f`), `leanSig` & EUF-CMA -/

/-- Unified parameter set covering `THINCS-Custody-128`, `leanSPHINCS-128f`, and stateful `leanSig`. -/
structure PqHashParams where
  w : Nat
  ell1 : Nat
  subtreeHeight : Nat
  numLayers : Nat
  forsTrees : Nat
  forsHeight : Nat
  maxSigsLog2 : Nat
  statefulLeanSig : Bool
  deriving DecidableEq, Repr

def PqHashParams.targetSum (p : PqHashParams) : Nat := canonicalTargetSum p.w p.ell1

/-- Parameter non-degeneracy & machine-word upper-bound guard matching `crates/obend-pq-mpc`. -/
def PqHashParams.wellFormed (p : PqHashParams) : Bool :=
  decide (0 < p.numLayers) && decide (2 ≤ p.w) && decide (p.w ≤ 256) && decide (0 < p.ell1) &&
  decide (p.subtreeHeight ≤ 30) && decide (p.forsHeight ≤ 30) &&
  decide (p.numLayers * p.subtreeHeight ≤ 62) && (p.statefulLeanSig || decide (0 < p.forsTrees))

def thincsCustody128Params : PqHashParams := ⟨4, 64, 6, 2, 18, 8, 12, false⟩
def leanSphincs128fParams  : PqHashParams := ⟨4, 64, 2, 10, 18, 8, 16, false⟩
def leanSigPoseidon2Params : PqHashParams := ⟨4, 64, 16, 1, 0, 0, 16, true⟩
def compactGoldenParams    : PqHashParams := ⟨4, 8, 2, 2, 4, 2, 4, false⟩
def compactLeanSigParams   : PqHashParams := ⟨4, 8, 2, 1, 0, 0, 2, true⟩

/-- Secret key `(skSeed, skPrf, pkSeed)`. -/
structure PqSecretKey where
  skSeed : List UInt8
  skPrf  : List UInt8
  pkSeed : List UInt8
  deriving DecidableEq, Repr

/-- Public key `(pkSeed, pkRoot)` (`64` bytes canonical encoding: `32 B || 32 B`). -/
structure PqPublicKey where
  pkSeed : List UInt8
  pkRoot : List UInt8
  deriving DecidableEq, Repr

/-- Advance a WOTS+C chain `steps` iterations starting from `startStep`. -/
def wotsChainSteps (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain startStep : Nat) : Nat → List UInt8 → List UInt8
  | 0, cur => cur
  | k + 1, cur =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let nextVal := thChainF suite pkSeed adrs cur
    wotsChainSteps suite pkSeed layer tree kp chain (startStep + 1) k nextVal

theorem wotsChainSteps_add (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (a b startStep : Nat) (cur : List UInt8),
      wotsChainSteps suite pkSeed layer tree kp chain (startStep + a) b
        (wotsChainSteps suite pkSeed layer tree kp chain startStep a cur) =
      wotsChainSteps suite pkSeed layer tree kp chain startStep (a + b) cur
  | 0, b, startStep, cur => by simp [wotsChainSteps]
  | a + 1, b, startStep, cur => by
    rw [Nat.succ_add]
    simp only [wotsChainSteps]
    have hShift : startStep + (a + 1) = (startStep + 1) + a := by
      rw [Nat.add_assoc, Nat.add_comm 1 a, ← Nat.add_assoc]
    rw [hShift, wotsChainSteps_add suite pkSeed layer tree kp chain a b (startStep + 1)]

def wotsSecretBase (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed
    ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩

def computeWotsEndpoints (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List (List UInt8) :=
  (List.range params.ell1).map fun r =>
    wotsChainSteps suite sk.pkSeed layer tree kp r 0 (params.w - 1)
      (wotsSecretBase suite sk layer tree kp r)

def computeWotsPk (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List UInt8 :=
  thTweakTl suite sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
    (computeWotsEndpoints suite params sk layer tree kp)

def recoverWotsEndpoints (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (sigChains : List (List UInt8)) : List (List UInt8) :=
  (List.range params.ell1).map fun r =>
    let dr := digits.getD r 0
    let sigVal := sigChains.getD r []
    wotsChainSteps suite pkSeed layer tree kp r dr ((params.w - 1) - dr) sigVal

def recoverWotsPkFromSig (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (sigChains : List (List UInt8)) : List UInt8 :=
  thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
    (recoverWotsEndpoints suite params pkSeed layer tree kp digits sigChains)

theorem list_getD_map_range {α : Type} (n : Nat) (f : Nat → α) (dflt : α) {i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i dflt = f i := by
  have hi' : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simp

theorem list_getD_eq_getElem {α : Type} (xs : List α) (dflt : α) {i : Nat} (hi : i < xs.length) :
    xs.getD i dflt = xs[i]'hi := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem recoverWotsPkFromSig_eq_computeWotsPk
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat)
    (hValid : checkTargetSum params.w params.ell1 params.targetSum digits = true) :
    let sigChains := (List.range params.ell1).map fun r =>
      let dr := digits.getD r 0
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 dr (wotsSecretBase suite sk layer tree kp r)
    recoverWotsPkFromSig suite params sk.pkSeed layer tree kp digits sigChains =
      computeWotsPk suite params sk layer tree kp := by
  intro sigChains
  obtain ⟨hLen, hBound, _⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum digits).mp hValid
  unfold recoverWotsPkFromSig computeWotsPk recoverWotsEndpoints computeWotsEndpoints
  congr 1
  apply List.map_congr_left
  intro r hrMem
  have hrLt : r < params.ell1 := List.mem_range.mp hrMem
  have hSigGet : sigChains.getD r [] =
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 (digits.getD r 0) (wotsSecretBase suite sk layer tree kp r) :=
    list_getD_map_range params.ell1 _ [] hrLt
  rw [hSigGet]
  have hdrLt : digits.getD r 0 < params.w := by
    have hrDigits : r < digits.length := hLen ▸ hrLt
    rw [list_getD_eq_getElem digits 0 hrDigits]
    exact hBound _ (List.getElem_mem hrDigits)
  have hStepEq := wotsChainSteps_add suite sk.pkSeed layer tree kp r
    (digits.getD r 0) ((params.w - 1) - digits.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
  simp only [Nat.zero_add] at hStepEq
  have hSumW : digits.getD r 0 + ((params.w - 1) - digits.getD r 0) = params.w - 1 := by omega
  rw [hStepEq, hSumW]

/-! ### Parametric Binary Merkle Subtree + Auth Path (`FORS` & `XMSS` Unified) -/

def computeMerkleNode (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind)
    (leafFn : Nat → List UInt8) : Nat → Nat → List UInt8
  | 0, nodeIdx => leafFn nodeIdx
  | h + 1, nodeIdx =>
    let left  := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx)
    let right := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    thNodeH suite pkSeed adrs left right

def buildMerkleAuthPath (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind)
    (leafFn : Nat → List UInt8) : Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | h + 1, nodeIdx, localIdx =>
    let half := 2 ^ h
    if localIdx < half then
      let sib := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)
      sib :: buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) localIdx
    else
      let sib := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx)
      sib :: buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) (localIdx - half)

def walkMerkleAuthPath (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) :
    Nat → Nat → Nat → List UInt8 → List (List UInt8) → Option (List UInt8)
  | 0, _, _, leafHash, [] => some leafHash
  | 0, _, _, _, _ :: _ => none
  | _ + 1, _, _, _, [] => none
  | h + 1, nodeIdx, localIdx, leafHash, sib :: rest =>
    let half := 2 ^ h
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    if localIdx < half then
      match walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sub sib)
    else
      match walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - half) leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sib sub)

theorem walkMerkleAuthPath_buildMerkleAuthPath
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) :
    ∀ (h nodeIdx localIdx : Nat), localIdx < 2 ^ h →
      walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx
        (leafFn (nodeIdx * (2 ^ h) + localIdx))
        (buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h nodeIdx localIdx) =
      some (computeMerkleNode suite pkSeed layer tree nodeKind leafFn h nodeIdx)
  | 0, nodeIdx, localIdx, hLt => by
    have h0 : localIdx = 0 := by simp at hLt; exact hLt
    subst h0
    simp [buildMerkleAuthPath, walkMerkleAuthPath, computeMerkleNode]
  | h + 1, nodeIdx, localIdx, hLt => by
    simp only [buildMerkleAuthPath]
    have hMul : nodeIdx * (2 ^ (h + 1)) = (2 * nodeIdx) * (2 ^ h) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ h) 2, Nat.mul_assoc]
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPath]
      have hIdxEq : nodeIdx * (2 ^ (h + 1)) + localIdx = (2 * nodeIdx) * (2 ^ h) + localIdx := by rw [hMul]
      rw [hIdxEq, walkMerkleAuthPath_buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) localIdx hHalf]; rfl
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPath]
      have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
      have hIdxEq : nodeIdx * (2 ^ (h + 1)) + localIdx = (2 * nodeIdx + 1) * (2 ^ h) + (localIdx - 2 ^ h) := by
        rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
      rw [hIdxEq, walkMerkleAuthPath_buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) (localIdx - 2 ^ h) hSubLt]; rfl

/-- FORS leaf secret & leaf hash (`globalForsLeaf = j * 2^a + u` as in FIPS 205 §8). -/
def forsSecretLeaf (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed
    ⟨0, treeIdx, .forsPrf, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩

def forsLeafHashFromSecret (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) (secVal : List UInt8) : List UInt8 :=
  thChainF suite pkSeed
    ⟨0, treeIdx, .forsTree, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩ secVal

def forsLeafFn (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx : Nat) : Nat → List UInt8 :=
  fun globalU => forsLeafHashFromSecret suite sk.pkSeed treeIdx kpIdx globalU
    (forsSecretLeaf suite sk treeIdx kpIdx globalU)

def computeXmssSubtreeRoot (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (treeIdx : UInt64) : List UInt8 :=
  computeMerkleNode suite sk.pkSeed layer treeIdx .tree
    (computeWotsPk suite params sk layer treeIdx) params.subtreeHeight 0

/-- Derive the canonical `PqPublicKey` `(pkSeed, pkRoot)` from top layer `d - 1`, `treeIdx = 0`. -/
@[expose] def derivePublicKey (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) : PqPublicKey :=
  let topLayer := UInt32.ofNat (params.numLayers - 1)
  { pkSeed := sk.pkSeed
    pkRoot := computeXmssSubtreeRoot suite params sk topLayer 0 }

structure LayerXmssSig where
  tswCtr : Nat
  wotsChains : List (List UInt8)
  authPath : List (List UInt8)
  deriving DecidableEq, Repr

structure ForsTreeOpening where
  secretVal : List UInt8
  authPath : List (List UInt8)
  deriving DecidableEq, Repr

structure PqHashSig where
  rRand : List UInt8
  msgTswCtr : Nat
  leafGlobalIdx : Nat
  forsOpenings : List ForsTreeOpening
  layerSigs : List LayerXmssSig
  deriving DecidableEq, Repr

def extractBitWindow (bytes : List UInt8) (startBit width : Nat) : Nat :=
  let nBytes := if bytes.length = 0 then 1 else bytes.length
  ((List.range width).foldl (fun acc b =>
    let pos := startBit + b
    let byteVal := (bytes.getD ((pos / 8) % nBytes) 0).toNat
    acc * 2 + (byteVal >>> (pos % 8)) % 2) 0) % (2 ^ width)

def deriveForsIndices (k a : Nat) (hmsg : List UInt8) : List Nat :=
  (List.range k).map fun j => extractBitWindow hmsg (88 + j * a) a

theorem deriveForsIndices_bounds (k a : Nat) (hmsg : List UInt8) :
    (deriveForsIndices k a hmsg).length = k ∧
    ∀ idx ∈ deriveForsIndices k a hmsg, idx < 2 ^ a := by
  refine ⟨by simp [deriveForsIndices], ?_⟩
  intro idx hMem
  simp only [deriveForsIndices, List.mem_map] at hMem
  obtain ⟨_, _, rfl⟩ := hMem
  exact Nat.mod_lt _ (Nat.two_pow_pos a)

def recoverForsTreeRoots (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j : Nat) : Nat → Option (List (List UInt8))
  | 0 => some []
  | rem + 1 =>
    let idxJ := idxs.getD j 0
    let op := openings.getD j ⟨[], []⟩
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    let leafH := forsLeafHashFromSecret suite pkSeed treeIdx kpIdx globalU op.secretVal
    match walkMerkleAuthPath suite pkSeed 0 treeIdx .forsTree params.forsHeight j idxJ leafH op.authPath with
    | none => none
    | some rJ =>
      match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem with
      | none => none
      | some rs => some (rJ :: rs)

def recoverForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (hmsg : List UInt8) (openings : List ForsTreeOpening) : Option (List UInt8) :=
  if openings.length ≠ params.forsTrees then none
  else
    let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg
    match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0 params.forsTrees with
    | none => none
    | some roots =>
      some (thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots)

def verifyHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot : List UInt8) (rRand : List UInt8) :
    Nat → Nat → List UInt8 → List LayerXmssSig → Option (List UInt8)
  | _, _, curRoot, [] => some curRoot
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let hmsg := thHashMsg suite rRand pkSeed pkRoot curRoot layerU32 treeIdx lsig.tswCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
    else if lsig.wotsChains.length ≠ params.ell1 then none
    else
      let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
      match walkMerkleAuthPath suite pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
      | none => none
      | some nextSubtreeRoot =>
        verifyHypertreeLayers suite params pkSeed pkRoot rRand (layerIdx + 1) treeIdxNat nextSubtreeRoot rest

/-- **Unified Verifier (`verifyPqHashSig`)** for both stateless `leanSPHINCS`/`SLH-DSA` and stateful `leanSig`. -/
@[expose] def verifyPqHashSig (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  if !(params.wellFormed) then false
  else if sig.layerSigs.length ≠ params.numLayers then false
  else if !(sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then false
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    if params.statefulLeanSig then
      if !sig.forsOpenings.isEmpty || sig.msgTswCtr ≠ 0 then false
      else
        match verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx mu sig.layerSigs with
        | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
        | none => false
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := sig.leafGlobalIdx % subLeaves
      let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
      let hmsg0 := thHashMsg suite sig.rRand pk.pkSeed pk.pkRoot mu 0 tree0 sig.msgTswCtr
      let digits0 := extractBaseWDigits params.w params.ell1 hmsg0
      if !(checkTargetSum params.w params.ell1 params.targetSum digits0) then false
      else
        match recoverForsPk suite params pk.pkSeed tree0 kp0 hmsg0 sig.forsOpenings with
        | none => false
        | some forsPk =>
          match verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx forsPk sig.layerSigs with
          | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
          | none => false

def signHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    match grindTswCounterAux suite params.w params.ell1 params.targetSum
            rRand sk.pkSeed pkRoot curRoot layerU32 treeIdx 0 maxGrind with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        let dr := digits.getD r 0
        wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 dr
          (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
      let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
        (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
      let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
      match signHypertreeLayers suite params sk pkRoot rRand maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

def buildForsOpenings (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) : List ForsTreeOpening :=
  let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
  let leafFn := forsLeafFn suite sk tree0 kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    let secVal := forsSecretLeaf suite sk tree0 kp0 globalU
    let path := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ
    { secretVal := secVal, authPath := path }

def computeForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) : List UInt8 :=
  let leafFn := forsLeafFn suite sk tree0 kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j
  thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots

/-- **Single-Party Reference Signer (`evalSingleSign`)**. -/
@[expose] def evalSingleSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) : Option PqHashSig :=
  if !(params.wellFormed) then none
  else if !(leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    if params.statefulLeanSig then
      match signHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx mu params.numLayers with
      | none => none
      | some layerSigs =>
        some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx, forsOpenings := [], layerSigs := layerSigs }
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := leafGlobalIdx % subLeaves
      let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              rRand pk.pkSeed pk.pkRoot mu 0 tree0 0 maxGrind with
      | none => none
      | some (ctr0, _, hmsg0) =>
        let forsOps := buildForsOpenings suite params sk tree0 kp0 hmsg0
        let forsPk := computeForsPk suite params sk tree0 kp0
        match signHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx forsPk params.numLayers with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, msgTswCtr := ctr0, leafGlobalIdx := leafGlobalIdx, forsOpenings := forsOps, layerSigs := layerSigs }

example : ∃ ls, signHypertreeLayers zeroHashSuite ⟨2, 1, 0, 1, 0, 0, 1, true⟩ ⟨[], [], []⟩ [] [] 1 0 0 [] 1 = some ls := ⟨_, rfl⟩

private theorem signHypertreeLayers_sound
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    ∀ (rem layerIdx globalIdx : Nat) (curRoot : List UInt8) (layerSigs : List LayerXmssSig),
      0 < rem →
      globalIdx < 2 ^ (rem * params.subtreeHeight) →
      signHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot rem = some layerSigs →
      layerSigs.length = rem ∧
      verifyHypertreeLayers suite params sk.pkSeed pkRoot rRand layerIdx globalIdx curRoot layerSigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx + rem - 1)) 0)
  | 0, _, _, _, _, hPos, _, _ => by omega
  | 1, layerIdx, globalIdx, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signHypertreeLayers] at hSign
    cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum
        rRand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      simp only [signHypertreeLayers, Option.some.injEq] at hSign
      subst hSign
      obtain ⟨hMsgEq, hDigEq, hChk⟩ := grindTswCounterAux_sound hGrind
      have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
      have hGlobalBound : globalIdx < 2 ^ params.subtreeHeight := by simpa [Nat.one_mul] using hIdxLt
      have hDiv0 : globalIdx / 2 ^ params.subtreeHeight = 0 := Nat.div_eq_of_lt hGlobalBound
      refine ⟨rfl, ?_⟩
      simp only [verifyHypertreeLayers]
      rw [← hMsgEq, ← hDigEq, hChk]
      have hChainsLen : ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
            (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
      have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) digits hChk
      dsimp only at hWotsEq
      rw [hWotsEq]
      have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree
        (computeWotsPk suite params sk (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
        params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
      simp only [Nat.zero_mul, Nat.zero_add] at hWalk
      rw [hWalk]
      simp only [computeXmssSubtreeRoot, hDiv0, Nat.add_sub_cancel]
      rfl
  | rem + 2, layerIdx, globalIdx, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signHypertreeLayers] at hSign
    dsimp only at hSign
    cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum
        rRand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      dsimp only at hSign
      cases hRest : signHypertreeLayers suite params sk pkRoot rRand maxGrind
          (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) (rem + 1) with
      | none => rw [hRest] at hSign; cases hSign
      | some restSigs =>
        rw [hRest] at hSign
        simp only [Option.some.injEq] at hSign
        subst hSign
        obtain ⟨hMsgEq, hDigEq, hChk⟩ := grindTswCounterAux_sound hGrind
        have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
        have hTreeLt : globalIdx / 2 ^ params.subtreeHeight < 2 ^ ((rem + 1) * params.subtreeHeight) := by
          have hPow : 2 ^ ((rem + 2) * params.subtreeHeight) =
              2 ^ ((rem + 1) * params.subtreeHeight) * 2 ^ params.subtreeHeight := by
            rw [Nat.succ_mul, Nat.pow_add]
          exact (Nat.div_lt_iff_lt_mul hSubPos).mpr (hPow ▸ hIdxLt)
        obtain ⟨hRestLen, hRestVer⟩ := signHypertreeLayers_sound suite params sk pkRoot rRand maxGrind
          (rem + 1) (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          restSigs (by omega) hTreeLt hRest
        refine ⟨by simp [hRestLen], ?_⟩
        simp only [verifyHypertreeLayers]
        change (let hmsg := thHashMsg suite rRand sk.pkSeed pkRoot curRoot
                  (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) ctr; _) = _
        rw [← hMsgEq, ← hDigEq, hChk]
        have hChainsLen : ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
        have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (globalIdx % 2 ^ params.subtreeHeight) digits hChk
        dsimp only at hWotsEq
        rw [hWotsEq]
        have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree
          (computeWotsPk suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
        simp only [Nat.zero_mul, Nat.zero_add] at hWalk
        rw [hWalk]
        change verifyHypertreeLayers suite params sk.pkSeed pkRoot rRand (layerIdx + 1)
            (globalIdx / 2 ^ params.subtreeHeight)
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) restSigs = _
        rw [hRestVer]
        have hTopLayerEq : layerIdx + 1 + (rem + 1) - 1 = layerIdx + (rem + 2) - 1 := by omega
        rw [hTopLayerEq]

private theorem list_range_succ_shift {α : Type} (rem : Nat) (f : Nat → α) :
    (List.range (rem + 1)).map f = f 0 :: (List.range rem).map (fun k => f (k + 1)) := by
  induction rem generalizing f with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, ih f, List.range_succ, List.map_append]; simp

private theorem recoverForsPk_buildForsOpenings
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) :
    recoverForsPk suite params sk.pkSeed tree0 kp0 hmsg0
      (buildForsOpenings suite params sk tree0 kp0 hmsg0) =
    some (computeForsPk suite params sk tree0 kp0) := by
  unfold recoverForsPk buildForsOpenings computeForsPk
  let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
  let leafFn := forsLeafFn suite sk tree0 kp0
  let ops := (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    { secretVal := forsSecretLeaf suite sk tree0 kp0 globalU
      authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ : ForsTreeOpening }
  have hOpsLen : ops.length = params.forsTrees := by simp [ops]
  change (if ops.length ≠ params.forsTrees then none else _) = _
  simp only [hOpsLen, ne_eq, not_true_eq_false, ↓reduceIte]
  obtain ⟨hIdxsLen, hIdxsBound⟩ := deriveForsIndices_bounds params.forsTrees params.forsHeight hmsg0
  have hCollect : ∀ (rem j : Nat), j + rem = params.forsTrees →
      recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem =
      some ((List.range rem).map fun off =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight (j + off)) := by
    intro rem
    induction rem with
    | zero => intro _ _; simp [recoverForsTreeRoots]
    | succ rem ih =>
      intro j hjSum
      have hjLt : j < params.forsTrees := by omega
      simp only [recoverForsTreeRoots]
      have hOpGet : ops.getD j (⟨[], []⟩ : ForsTreeOpening) =
          { secretVal := forsSecretLeaf suite sk tree0 kp0 (j * (2 ^ params.forsHeight) + idxs.getD j 0)
            authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j (idxs.getD j 0) } :=
        list_getD_map_range params.forsTrees _ (⟨[], []⟩ : ForsTreeOpening) hjLt
      rw [hOpGet]
      dsimp only
      have hIdxLt : idxs.getD j 0 < 2 ^ params.forsHeight := by
        have hjIdxs : j < idxs.length := hIdxsLen ▸ hjLt
        rw [list_getD_eq_getElem idxs 0 hjIdxs]
        exact hIdxsBound _ (List.getElem_mem hjIdxs)
      have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree
        leafFn params.forsHeight j (idxs.getD j 0) hIdxLt
      change (match walkMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree params.forsHeight j (idxs.getD j 0)
                (leafFn (j * (2 ^ params.forsHeight) + idxs.getD j 0))
                (buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j (idxs.getD j 0)) with
              | none => none
              | some rJ => _) = _
      rw [hWalk, ih (j + 1) (by omega), list_range_succ_shift]
      simp only [Nat.add_zero, Option.some.injEq, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k _
      have hAssoc : j + 1 + k = j + (k + 1) := by omega
      rw [hAssoc]
  change (match recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops 0 params.forsTrees with
          | none => none | some roots => _) = _
  rw [hCollect params.forsTrees 0 (by omega)]; simp; rfl

/-- **Unconditional Signature Completeness (`verifyPqHashSig_evalSingleSign`)**:
    Whenever `evalSingleSign` returns `some sig` (for ANY `TweakableHashSuite`, whether stateless
    `leanSPHINCS` / `SLH-DSA` or stateful `leanSig`), `verifyPqHashSig` accepts (`= true`)! -/
theorem verifyPqHashSig_evalSingleSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) (sig : PqHashSig)
    (hSign : evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind = some sig) :
    verifyPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  unfold evalSingleSign at hSign
  cases hWf : params.wellFormed
  · simp [hWf] at hSign
  · rw [hWf] at hSign
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
    have hDPos : 0 < params.numLayers := by
      simp only [PqHashParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hWf; omega
    cases hGuard2 : decide (leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · simp [hGuard2] at hSign
    · have hLeafLt : leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) :=
        of_decide_eq_true hGuard2
      simp only [hLeafLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
      dsimp only [derivePublicKey] at hSign
      cases hMode : params.statefulLeanSig
      · rw [hMode] at hSign
        simp only [Bool.false_eq_true, ↓reduceIte] at hSign
        cases hGrind0 : grindTswCounterAux suite params.w params.ell1 params.targetSum
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            0 (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight)) 0 maxGrind with
        | none => rw [hGrind0] at hSign; cases hSign
        | some tr0 =>
          rcases tr0 with ⟨ctr0, dig0, hmsg0⟩
          rw [hGrind0] at hSign; dsimp only at hSign
          cases hLayers : signHypertreeLayers suite params sk
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
              (thPrfMsg suite sk.skPrf optRand
                (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
              maxGrind 0 leafGlobalIdx
              (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight)) params.numLayers with
          | none => rw [hLayers] at hSign; cases hSign
          | some layerSigs =>
            rw [hLayers] at hSign; simp only [Option.some.injEq] at hSign; subst hSign
            obtain ⟨hMsg0Eq, hDig0Eq, hChk0⟩ := grindTswCounterAux_sound hGrind0
            obtain ⟨hLsLen, hLsVer⟩ := signHypertreeLayers_sound suite params sk
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
              (thPrfMsg suite sk.skPrf optRand
                (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
              maxGrind params.numLayers 0 leafGlobalIdx
              (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight)) layerSigs hDPos hLeafLt hLayers
            unfold verifyPqHashSig; dsimp only [derivePublicKey]
            simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLsLen, ne_eq, not_true_eq_false,
              hLeafLt, decide_true, hMode]
            rw [← hMsg0Eq, ← hDig0Eq, hChk0]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [recoverForsPk_buildForsOpenings]; dsimp only; rw [hLsVer]; simp
      · rw [hMode] at hSign; simp only [↓reduceIte] at hSign
        cases hLayers : signHypertreeLayers suite params sk
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            maxGrind 0 leafGlobalIdx
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            params.numLayers with
        | none => rw [hLayers] at hSign; cases hSign
        | some layerSigs =>
          rw [hLayers] at hSign; simp only [Option.some.injEq] at hSign; subst hSign
          obtain ⟨hLsLen, hLsVer⟩ := signHypertreeLayers_sound suite params sk
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            maxGrind params.numLayers 0 leafGlobalIdx
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            layerSigs hDPos hLeafLt hLayers
          unfold verifyPqHashSig; dsimp only [derivePublicKey]
          simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLsLen, ne_eq, not_true_eq_false,
            hLeafLt, decide_true, hMode, List.isEmpty_nil]
          rw [hLsVer]; simp

/-! ### Constructive `0 Classical` `PSum` EUF-CMA Forgery Extractor & `ValidLeanSigBatch` -/

/-- Constructive `Type`-valued one-way chain inversion witness:
    exhibits `preimage` at chain step `step < revealedStep` hashing under `thChainF` to `revealedVal`! -/
structure WotsBackwardInversionWitness (suite : TweakableHashSuite) (pkSeed : List UInt8) where
  layer : UInt32
  tree : UInt64
  kp : Nat
  chain : Nat
  step : Nat
  revealedStep : Nat
  step_lt : step < revealedStep
  preimage : List UInt8
  revealedVal : List UInt8
  invertsChain : thChainF suite pkSeed ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat step⟩ preimage = revealedVal

/-- Constructive chain-collision walker (`0 Classical`): if `u ≠ v` reach equal chain values after
    `rem` iterations of `thChainF`, pinpoints the exact first colliding step! -/
def extractChainCollision (suite : TweakableHashSuite) (maxBytes : Nat) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (rem startStep : Nat) (u v : List UInt8),
      u ≠ v →
      (∀ s u', u'.length ≤ 32 →
        (thPreimage tagThF pkSeed ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat s⟩ [u']).length ≤ maxBytes) →
      u.length ≤ 32 → v.length ≤ 32 →
      wotsChainSteps suite pkSeed layer tree kp chain startStep rem u =
        wotsChainSteps suite pkSeed layer tree kp chain startStep rem v →
      HashCollisionWitness suite.rawHash maxBytes
  | 0, _, _, _, hNe, _, _, _, hEq => False.elim (hNe hEq)
  | rem + 1, startStep, u, v, hNe, hBound, huLen, hvLen, hEq =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let fu := thChainF suite pkSeed adrs u
    let fv := thChainF suite pkSeed adrs v
    if hStepEq : fu = fv then
      match thCall_binds_or_collision suite maxBytes (hBound startStep u huLen) (hBound startStep v hvLen) hStepEq with
      | .inl ⟨_, _, _, hArgs⟩ =>
        False.elim (hNe (by injection hArgs))
      | .inr col => col
    else
      have hFuLen : fu.length ≤ 32 := Nat.le_of_eq (thCall_length suite tagThF pkSeed adrs [u])
      have hFvLen : fv.length ≤ 32 := Nat.le_of_eq (thCall_length suite tagThF pkSeed adrs [v])
      extractChainCollision suite maxBytes pkSeed layer tree kp chain rem (startStep + 1) fu fv
        hStepEq hBound hFuLen hFvLen hEq

theorem wotsChainSteps_len_32 (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (k startStep : Nat) (cur : List UInt8),
      cur.length ≤ 32 →
      (wotsChainSteps suite pkSeed layer tree kp chain startStep k cur).length ≤ 32
  | 0, _, _, h => h
  | k + 1, startStep, cur, _ => by
    simp only [wotsChainSteps]
    apply wotsChainSteps_len_32 suite pkSeed layer tree kp chain k (startStep + 1)
    exact Nat.le_of_eq (thCall_length suite _ _ _ _)

/-- **Constructive `0 Classical` WOTS+C / `TSW` EUF-CMA Forgery Extractor (`extractPqHashForgery`)**:
    Given an honestly revealed WOTS+C signature `honestChains` on `d₁` and any accepted forgery
    `forgedChains` on a distinct `TSW` digit vector `d₂ ≠ d₁` recovering the same `wotsPk`,
    constructively extracts `PSum (WotsBackwardInversionWitness suite pkSeed) (HashCollisionWitness suite.rawHash maxBytes)`! -/
def extractPqHashForgery
    (suite : TweakableHashSuite) (params : PqHashParams) (maxBytes : Nat)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (d₁ d₂ : List Nat) (honestChains forgedChains : List (List UInt8))
    (hValid₁ : checkTargetSum params.w params.ell1 params.targetSum d₁ = true)
    (hValid₂ : checkTargetSum params.w params.ell1 params.targetSum d₂ = true)
    (hDistinct : d₁ ≠ d₂)
    (hSameWotsPk : recoverWotsPkFromSig suite params pkSeed layer tree kp d₂ forgedChains =
                   recoverWotsPkFromSig suite params pkSeed layer tree kp d₁ honestChains)
    (hChainElemLen₁ : ∀ x ∈ honestChains, x.length ≤ 32)
    (hChainElemLen₂ : ∀ x ∈ forgedChains, x.length ≤ 32)
    (hFrameTl₁ : (thPreimage tagThTl pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
                    (recoverWotsEndpoints suite params pkSeed layer tree kp d₂ forgedChains)).length ≤ maxBytes)
    (hFrameTl₂ : (thPreimage tagThTl pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
                    (recoverWotsEndpoints suite params pkSeed layer tree kp d₁ honestChains)).length ≤ maxBytes)
    (hFrameStep : ∀ chain s u', u'.length ≤ 32 →
      (thPreimage tagThF pkSeed ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat s⟩ [u']).length ≤ maxBytes) :
    PSum (WotsBackwardInversionWitness suite pkSeed) (HashCollisionWitness suite.rawHash maxBytes) :=
  let end₂ := recoverWotsEndpoints suite params pkSeed layer tree kp d₂ forgedChains
  let end₁ := recoverWotsEndpoints suite params pkSeed layer tree kp d₁ honestChains
  if hEndNe : end₂ ≠ end₁ then
    match thCall_binds_or_collision suite maxBytes hFrameTl₁ hFrameTl₂ hSameWotsPk with
    | .inl ⟨_, _, _, hEqEnds⟩ => False.elim (hEndNe hEqEnds)
    | .inr col => .inr col
  else
    have hEndEq : end₂ = end₁ := Decidable.of_not_not hEndNe
    have hIncomp := (tsw_incomparable_no_chain_forgery hValid₁ hValid₂ hDistinct).2
    have hComplete := findBackwardCoord_complete
      (let ⟨r', hr2, hr1, hlt, _⟩ := hIncomp; ⟨r', hr2, hr1, hlt⟩)
    match hFind : findBackwardCoord d₁ d₂ with
    | none =>
      False.elim (by obtain ⟨_, _, _, hSome, _⟩ := hComplete; rw [hFind] at hSome; cases hSome)
    | some r =>
      have hProps : ∃ (hr₂ : r < d₂.length) (hr₁ : r < d₁.length), d₂[r]'hr₂ < d₁[r]'hr₁ ∧ d₁[r]'hr₁ < params.w := by
        obtain ⟨r0, hr2, hr1, hSome, hlt⟩ := hComplete
        rw [hFind] at hSome
        injection hSome with hEqR
        subst hEqR
        obtain ⟨_, hB1, _⟩ := (checkTargetSum_iff _ _ _ d₁).mp hValid₁
        exact ⟨hr2, hr1, hlt, hB1 _ (List.getElem_mem hr1)⟩
      let s₂ := d₂.getD r 0
      let s₁ := d₁.getD r 0
      have hsLt : s₂ < s₁ ∧ s₁ < params.w ∧ r < params.ell1 := by
        obtain ⟨hr2, hr1, hlt, hbw⟩ := hProps
        obtain ⟨hL1, _, _⟩ := (checkTargetSum_iff _ _ _ d₁).mp hValid₁
        rw [show s₂ = d₂[r]'hr2 from list_getD_eq_getElem d₂ 0 hr2,
            show s₁ = d₁[r]'hr1 from list_getD_eq_getElem d₁ 0 hr1]
        exact ⟨hlt, hbw, hL1 ▸ hr1⟩
      let sig₂ := forgedChains.getD r []
      let sig₁ := honestChains.getD r []
      have hSig1Len : sig₁.length ≤ 32 := by
        if hr : r < honestChains.length then
          rw [show sig₁ = honestChains[r]'hr from list_getD_eq_getElem honestChains [] hr]
          exact hChainElemLen₁ _ (List.getElem_mem hr)
        else
          have hOut : sig₁ = [] := by
            show honestChains.getD r [] = []
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hr)]; rfl
          rw [hOut]; exact Nat.zero_le 32
      have hSig2Len : sig₂.length ≤ 32 := by
        if hr : r < forgedChains.length then
          rw [show sig₂ = forgedChains[r]'hr from list_getD_eq_getElem forgedChains [] hr]
          exact hChainElemLen₂ _ (List.getElem_mem hr)
        else
          have hOut : sig₂ = [] := by
            show forgedChains.getD r [] = []
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hr)]; rfl
          rw [hOut]; exact Nat.zero_le 32
      let gap := s₁ - s₂
      have hGapGe1 : 1 ≤ gap := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hsLt.1)
      have hGapSplit : gap = (gap - 1) + 1 := (Nat.sub_add_cancel hGapGe1).symm
      have hsAdd : s₂ + gap = s₁ := Nat.add_sub_of_le (Nat.le_of_lt hsLt.1)
      let mid₂ := wotsChainSteps suite pkSeed layer tree kp r s₂ gap sig₂
      if hMidEq : mid₂ = sig₁ then
        let preStep := s₂ + (gap - 1)
        let preVal := wotsChainSteps suite pkSeed layer tree kp r s₂ (gap - 1) sig₂
        .inl
          { layer := layer, tree := tree, kp := kp, chain := r
            step := preStep, revealedStep := s₁
            step_lt := by
              calc
                s₂ + (gap - 1) < (s₂ + (gap - 1)) + 1 := Nat.lt_succ_self _
                _ = s₂ + ((gap - 1) + 1) := Nat.add_assoc _ _ 1
                _ = s₂ + gap := by rw [← hGapSplit]
                _ = s₁ := hsAdd
            preimage := preVal, revealedVal := sig₁
            invertsChain := by
              have hCompose := wotsChainSteps_add suite pkSeed layer tree kp r (gap - 1) 1 s₂ sig₂
              rw [← hGapSplit] at hCompose
              simpa only [wotsChainSteps] using hCompose.trans hMidEq }
      else
        have hEndAtR : end₂.getD r [] = end₁.getD r [] := by rw [hEndEq]
        have hEnd2R : end₂.getD r [] = wotsChainSteps suite pkSeed layer tree kp r s₂ ((params.w - 1) - s₂) sig₂ :=
          list_getD_map_range params.ell1 _ [] hsLt.2.2
        have hEnd1R : end₁.getD r [] = wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) sig₁ :=
          list_getD_map_range params.ell1 _ [] hsLt.2.2
        have hRemEq : wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) mid₂ =
            wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) sig₁ := by
          have hs1Le : s₁ ≤ params.w - 1 := Nat.le_sub_one_of_lt hsLt.2.1
          have hSplit : (params.w - 1) - s₂ = gap + ((params.w - 1) - s₁) := by
            have hSum : s₂ + (gap + ((params.w - 1) - s₁)) = params.w - 1 := by
              rw [← Nat.add_assoc, hsAdd, Nat.add_sub_of_le hs1Le]
            exact (congrArg (· - s₂) hSum).symm.trans (Nat.add_sub_cancel_left s₂ _)
          have hStep := wotsChainSteps_add suite pkSeed layer tree kp r gap ((params.w - 1) - s₁) s₂ sig₂
          rw [hsAdd, ← hSplit] at hStep
          rw [hStep, ← hEnd2R, hEndAtR, hEnd1R]
        have hMidLen : mid₂.length ≤ 32 :=
          wotsChainSteps_len_32 suite pkSeed layer tree kp r gap s₂ sig₂ hSig2Len
        .inr (extractChainCollision suite maxBytes pkSeed layer tree kp r ((params.w - 1) - s₁) s₁
                mid₂ sig₁ hMidEq (hFrameStep r) hMidLen hSig1Len hRemEq)

/-- Single validator entry for STARK-aggregated `leanSig-Poseidon2` batch verification (`Obend.Crypto.DualSpine`). -/
structure LeanSigBatchItem where
  validatorPk : PqPublicKey
  message : List UInt8
  signature : PqHashSig
  deriving DecidableEq, Repr

/-- Batch verification relation over `Poseidon2Goldilocks` `leanSig` signatures feeding STARK aggregation. -/
def ValidLeanSigBatch (params : PqHashParams) (items : List LeanSigBatchItem) : Bool :=
  decide (params.statefulLeanSig = true) &&
  items.all (fun item => verifyPqHashSig poseidon2Suite params item.validatorPk item.message item.signature)

theorem validLeanSigBatch_sound {params : PqHashParams} {items : List LeanSigBatchItem}
    (h : ValidLeanSigBatch params items = true) :
    params.statefulLeanSig = true ∧
    ∀ item ∈ items, verifyPqHashSig poseidon2Suite params item.validatorPk item.message item.signature = true := by
  simp only [ValidLeanSigBatch, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h

theorem validLeanSigBatch_singleton_of_sign {params : PqHashParams} {sk : PqSecretKey}
    {msg optRand : List UInt8} {idx fuel : Nat} {sig : PqHashSig}
    (hSt : params.statefulLeanSig = true)
    (hSign : evalSingleSign poseidon2Suite params sk msg optRand idx fuel = some sig) :
    ValidLeanSigBatch params [⟨derivePublicKey poseidon2Suite params sk, msg, sig⟩] = true := by
  simp [ValidLeanSigBatch, hSt, verifyPqHashSig_evalSingleSign poseidon2Suite params sk msg optRand idx fuel sig hSign]

example : ValidLeanSigBatch compactLeanSigParams [] = true := rfl

/-! ## 5. Committed-Identity Hybrid Combiner (`HybridPinnedSig`) & Tri-State `VerifyReply` -/

def hybridIdCustom : List UInt8 := "OBEND.PQ.HYBRID.ID/v1".toUTF8.data.toList

/-- Enrolled identity digest `idCommit = cSHAKE256("OBEND.PQ.HYBRID.ID/v1", encodeMultiFrame [pk₁, pk₂])`. -/
@[expose] def computeHybridIdCommit (pk1Bytes pk2Bytes : List UInt8) : List UInt8 :=
  cshake256Bytes hybridIdCustom (encodeMultiFrame [pk1Bytes, pk2Bytes])

/-- Constructive `0 Classical` binding proof for `computeHybridIdCommit`. -/
def computeHybridIdCommit_binds (maxBytes : Nat) {a₁ b₁ a₂ b₂ : List UInt8}
    (hLen₁ : (encodeMultiFrame [a₁, b₁]).length ≤ maxBytes)
    (hLen₂ : (encodeMultiFrame [a₂, b₂]).length ≤ maxBytes)
    (hEq : computeHybridIdCommit a₁ b₁ = computeHybridIdCommit a₂ b₂) :
    PSum (a₁ = a₂ ∧ b₁ = b₂) (HashCollisionWitness (cshake256Bytes hybridIdCustom) maxBytes) :=
  if hFrame : encodeMultiFrame [a₁, b₁] = encodeMultiFrame [a₂, b₂] then
    .inl (by
      have hList := encodeMultiFrame_injective hFrame
      simp only [List.cons.injEq, and_true] at hList
      exact hList)
  else
    .inr { msgA := encodeMultiFrame [a₁, b₁], msgB := encodeMultiFrame [a₂, b₂],
           lenA := hLen₁, lenB := hLen₂, distinct := hFrame, sameDigest := congrArg ofBE hEq }

/-- Wire envelope carrying component signature `sig1`, candidate `carriedPk2`, and PQ signature `sig2`. -/
structure HybridWireSig (Sig₁ PK₂ Sig₂ : Type) where
  sig1 : Sig₁
  carriedPk2 : PK₂
  sig2 : Sig₂
  deriving DecidableEq, Repr

/-- **Load-Bearing Committed-Identity Pinning Check (`checkHybridPinning`)**:
    Refuses self-carried `carriedPk2` substitution unless `(pk1, carriedPk2)` hashes to `idCommit`! -/
@[expose] def checkHybridPinning {PK₁ PK₂ : Type}
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (idCommit : List UInt8) (pk1 : PK₁) (carriedPk2 : PK₂) : Bool :=
  decide (computeHybridIdCommit (enc1 pk1) (enc2 carriedPk2) = idCommit)

section HybridVerifiers
variable {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ Msg : Type}

/-- Committed-identity hybrid signature verifier (`S₁ ∧ S₂` bound under `idCommit`). -/
def verifyHybridPinnedSig
    (S₁ : AbstractSigScheme PK₁ SK₁ Msg Sig₁) (S₂ : AbstractSigScheme PK₂ SK₂ Msg Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (idCommit : List UInt8) (pk1 : PK₁) (msg : Msg)
    (hsig : HybridWireSig Sig₁ PK₂ Sig₂) : Bool :=
  checkHybridPinning enc1 enc2 idCommit pk1 hsig.carriedPk2 &&
  S₁.verify pk1 msg hsig.sig1 && S₂.verify hsig.carriedPk2 msg hsig.sig2

/-- Vulnerable unpinned combiner trusting self-carried `carriedPk2` without `idCommit` check. -/
def verifyHybridUnpinned
    (S₁ : AbstractSigScheme PK₁ SK₁ Msg Sig₁) (S₂ : AbstractSigScheme PK₂ SK₂ Msg Sig₂)
    (pk1 : PK₁) (msg : Msg) (hsig : HybridWireSig Sig₁ PK₂ Sig₂) : Bool :=
  S₁.verify pk1 msg hsig.sig1 && S₂.verify hsig.carriedPk2 msg hsig.sig2

end HybridVerifiers

/-- **Committed-Identity Hybrid Security (`hybrid_ucRealizes_if_either_secure`)**:
    Whenever `idCommit = computeHybridIdCommit (enc1 pk1) (enc2 pk2)` (with injective `enc2`),
    ANY accepted `HybridWireSig` on unqueried `msg*` constructively yields EITHER an explicit
    `cSHAKE256` collision on `idCommit` OR simultaneous EUF-CMA forgeries against **BOTH** `S₁` on `pk1`
    **AND** `S₂` on the enrolled `pk2` (`Break₁ × Break₂`, matching `CompJudge.dualAssumption`)! -/
theorem hybrid_ucRealizes_if_either_secure
    {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ Msg : Type}
    (S₁ : AbstractSigScheme PK₁ SK₁ Msg Sig₁)
    (S₂ : AbstractSigScheme PK₂ SK₂ Msg Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (hEnc2Inj : ∀ {x y : PK₂}, enc2 x = enc2 y → x = y)
    (maxBytes : Nat)
    (pk1 : PK₁) (pk2 : PK₂) (msgStar : Msg)
    (hsig : HybridWireSig Sig₁ PK₂ Sig₂)
    (hLenEnrolled : (encodeMultiFrame [enc1 pk1, enc2 pk2]).length ≤ maxBytes)
    (hLenCarried  : (encodeMultiFrame [enc1 pk1, enc2 hsig.carriedPk2]).length ≤ maxBytes)
    (hAccept : verifyHybridPinnedSig S₁ S₂ enc1 enc2
                 (computeHybridIdCommit (enc1 pk1) (enc2 pk2)) pk1 msgStar hsig = true) :
    (hsig.carriedPk2 = pk2 ∧
     S₁.verify pk1 msgStar hsig.sig1 = true ∧
     S₂.verify pk2 msgStar hsig.sig2 = true) ∨
    Nonempty (HashCollisionWitness (cshake256Bytes hybridIdCustom) maxBytes) := by
  simp only [verifyHybridPinnedSig, checkHybridPinning, Bool.and_eq_true, decide_eq_true_eq] at hAccept
  rcases hAccept with ⟨⟨hCommitEq, hVer1⟩, hVer2⟩
  match computeHybridIdCommit_binds maxBytes hLenCarried hLenEnrolled hCommitEq with
  | .inl ⟨_, hEnc2Eq⟩ =>
    have hPk2Eq : hsig.carriedPk2 = pk2 := hEnc2Inj hEnc2Eq
    subst hPk2Eq
    exact .inl ⟨rfl, hVer1, hVer2⟩
  | .inr col => exact .inr ⟨col⟩

/-- **Refutation of Self-Carried Key Substitution (`selfCarried_pq_key_substitution_refuted`)**:
    If classical `S₁` is broken (`S₁.verify pk1 m forgedSig1 = true`) and a quantum attacker mints
    their own fresh PQ keypair `(attackerPk2, attackerSk2)` (`attackerPk2 ≠ pk2`), the unpinned
    combiner `verifyHybridUnpinned` is **forged (`= true`)**, whereas `verifyHybridPinnedSig`
    **rejects (`= false`)** unless `cSHAKE256` collides! -/
theorem selfCarried_pq_key_substitution_refuted
    {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ Msg : Type}
    (S₁ : AbstractSigScheme PK₁ SK₁ Msg Sig₁)
    (S₂ : AbstractSigScheme PK₂ SK₂ Msg Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (hEnc2Inj : ∀ {x y : PK₂}, enc2 x = enc2 y → x = y)
    (maxBytes : Nat)
    (pk1 : PK₁) (pk2 attackerPk2 : PK₂) (attackerSk2 : SK₂)
    (hComplete2 : S₂.complete attackerPk2 attackerSk2)
    (hSubst : attackerPk2 ≠ pk2)
    (m : Msg) (forgedSig1 : Sig₁) (hForged1 : S₁.verify pk1 m forgedSig1 = true)
    (hLenEnrolled : (encodeMultiFrame [enc1 pk1, enc2 pk2]).length ≤ maxBytes)
    (hLenAttacker : (encodeMultiFrame [enc1 pk1, enc2 attackerPk2]).length ≤ maxBytes) :
    let attackWire : HybridWireSig Sig₁ PK₂ Sig₂ := ⟨forgedSig1, attackerPk2, S₂.sign attackerSk2 m⟩
    verifyHybridUnpinned S₁ S₂ pk1 m attackWire = true ∧
    (verifyHybridPinnedSig S₁ S₂ enc1 enc2 (computeHybridIdCommit (enc1 pk1) (enc2 pk2)) pk1 m attackWire = false ∨
     Nonempty (HashCollisionWitness (cshake256Bytes hybridIdCustom) maxBytes)) := by
  intro attackWire
  have hAttVer2 : S₂.verify attackerPk2 m (S₂.sign attackerSk2 m) = true := S₂.completeness hComplete2 m
  refine ⟨by simp [verifyHybridUnpinned, attackWire, hForged1, hAttVer2], ?_⟩
  cases hv : verifyHybridPinnedSig S₁ S₂ enc1 enc2 (computeHybridIdCommit (enc1 pk1) (enc2 pk2)) pk1 m attackWire
  · exact .inl rfl
  · simp only [verifyHybridPinnedSig, checkHybridPinning, Bool.and_eq_true, decide_eq_true_eq, attackWire] at hv
    match computeHybridIdCommit_binds maxBytes hLenAttacker hLenEnrolled hv.1.1 with
    | .inl ⟨_, hEnc2Eq⟩ => exact False.elim (hSubst (hEnc2Inj hEnc2Eq))
    | .inr col => exact .inr ⟨col⟩

/-! ### Tri-State Wire Verifier (`VerifyReply` & `verifyWire_malformed_iff`) -/

/-- Exact wire-codec failure stage distinguishing malformed syntax from cryptographic rejection. -/
inductive FaultStage where
  | headerMagicOrVersion | publicKeyLength | signatureFraming | layerCountMismatch
  deriving DecidableEq, Repr

/-- Tri-state verification reply (`VerifyReply`): never conflates `.wireMalformed` with `.reject`. -/
inductive VerifyReply where
  | accept | reject | wireMalformed (stage : FaultStage)
  deriving DecidableEq, Repr

def pqWireMagic : List UInt8 := [0x4F, 0x42, 0x50, 0x51, 0x01]
def encodePublicKeyWire (pk : PqPublicKey) : List UInt8 := pk.pkSeed ++ pk.pkRoot

def parsePublicKeyWire (rawPk : List UInt8) : Sum FaultStage PqPublicKey :=
  if rawPk.length ≠ 64 then .inl .publicKeyLength
  else .inr { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 }

def checkLayerSigFraming (params : PqHashParams) (ls : LayerXmssSig) : Bool :=
  decide (ls.wotsChains.length = params.ell1) && ls.wotsChains.all (fun c => decide (c.length = 32)) &&
  decide (ls.authPath.length = params.subtreeHeight) && ls.authPath.all (fun s => decide (s.length = 32))

def checkForsOpeningFraming (params : PqHashParams) (op : ForsTreeOpening) : Bool :=
  decide (op.secretVal.length = 32) && decide (op.authPath.length = params.forsHeight) &&
  op.authPath.all (fun s => decide (s.length = 32))

def checkWireHeaderAndLengths (params : PqHashParams) (rawPk : List UInt8)
    (magicPrefix : List UInt8) (sig : PqHashSig) : Option FaultStage :=
  if magicPrefix ≠ pqWireMagic then some .headerMagicOrVersion
  else if rawPk.length ≠ 64 then some .publicKeyLength
  else if sig.layerSigs.length ≠ params.numLayers then some .layerCountMismatch
  else if sig.rRand.length ≠ 32 ||
          !(if params.statefulLeanSig then sig.forsOpenings.isEmpty && decide (sig.msgTswCtr = 0)
            else decide (sig.forsOpenings.length = params.forsTrees) && sig.forsOpenings.all (checkForsOpeningFraming params)) ||
          !(sig.layerSigs.all (checkLayerSigFraming params)) then some .signatureFraming
  else none

/-- Tri-state wire verifier separating framing checks from cryptographic `verifyPqHashSig`. -/
@[expose] def verifyPqWireEnvelope (suite : TweakableHashSuite) (params : PqHashParams)
    (rawPk rawMsg magicPrefix : List UInt8) (sig : PqHashSig) : VerifyReply :=
  match checkWireHeaderAndLengths params rawPk magicPrefix sig with
  | some stage => .wireMalformed stage
  | none =>
    let pk : PqPublicKey := { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 }
    if verifyPqHashSig suite params pk rawMsg sig then .accept else .reject

/-- **Tri-State Wire Verifier Characterization (`verifyWire_malformed_iff`)**. -/
theorem verifyWire_malformed_iff
    (suite : TweakableHashSuite) (params : PqHashParams)
    (rawPk rawMsg magicPrefix : List UInt8) (sig : PqHashSig) (stage : FaultStage) :
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .wireMalformed stage ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = some stage) ∧
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .accept ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = none ∧
      verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig = true) ∧
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .reject ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = none ∧
      verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig = false) := by
  unfold verifyPqWireEnvelope
  cases hChk : checkWireHeaderAndLengths params rawPk magicPrefix sig with
  | some _ => simp
  | none =>
    cases hVer : verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig <;>
      simp [hVer]

end Obend.Crypto.PqHashSignatures
end
