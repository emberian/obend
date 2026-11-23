module
/-
# Obend.Hardware.PinoutEquiv — IPC-7351B D4 Pinout Bijection, 256-Bit DetCbor Datasheet Citations & Agentic EDA Judge

1. **IPC-7351B $D_4$-Invariant Pad/Electrical/Rail Drop-In Bijection (`checkPinoutIso_iff`)**:
   `PinClass`, `PadGeometry2D`, `ComponentPinSpec`, `FootprintPackageSpec`, 8-element `D4Transform`
   (handling 90°/270° courtyard & aperture axis swap), constructive `0 Classical.choice`
   `verifyPinoutBijection`, signature-bucketed backtracking `findPinoutBijectionExec` / `checkPinoutIso`,
   and unconditional bidirectional soundness & completeness `checkPinoutIso_iff`.
2. **256-Bit `BitVec 256` `DetCbor` Datasheet Block Citation Freshness**:
   Canonical RFC 8949 CBOR encoding of `DatasheetBlockSpec`, 256-bit `BitVec 256` digests, constructive
   scoped binding `datasheetBlockDigest256_binding`, and `staleDatasheetCite256_refused`.
3. **Non-Tautological `pinoutEquivJudge` + Multi-Turn Revision Trace + `EdaVaultPart` Compat API**:
   Inhabited `Fragment`, non-trivial refuting `refutes` + `refuted`, `runPinoutRevisionTrace_sound`,
   `skip_implies_contract_violation`, and full `AgenticEDA` compatibility API.
-/
public import Obend.Core.Data
public import Obend.Vault.Page
public import Obend.Vault.Law
public import Obend.Doc.Merge
public import Obend.Codec.DetCbor
import all Obend.Codec.DetCbor
public import Obend.Digest.HashBytes
public import Obend.Receipt.Merkle
public import Obend.Judge.Class

public section
namespace Obend.Hardware.PinoutEquiv
set_option autoImplicit false

open Obend.Vault
open Obend.Spec.Law (LawExpr Facts)
open Obend.Codec.DetCbor
open Obend.Digest.HashBytes

/-! ## 1. IPC-7351B $D_4$-Invariant Pad/Electrical/Rail Drop-In Bijection -/

/-- DC voltage and current operating envelope of an IC I/O family (millivolts $\text{mV}$, microamps $\mu\text{A}$). -/
structure LogicFamilySpec where
  familyName : String
  vccMinMv   : Int
  vccNomMv   : Int
  vccMaxMv   : Int
  vihMinMv   : Int
  vilMaxMv   : Int
  vohMinMv   : Int
  volMaxMv   : Int
  iihMaxUa   : Int
  iilMaxUa   : Int
  iohMaxUa   : Int
  iolMaxUa   : Int
  deriving DecidableEq, Repr

/-- High-state DC noise margin $\text{NM}_H = (V_{OH,\min}^{\text{drv}} + \Delta V_{\text{pullup}}) - V_{IH,\min}^{\text{rcv}}$ (in $\text{mV}$). -/
@[expose] def noiseMarginHigh (drv rcv : LogicFamilySpec) (pullupBoostMv : Int) : Int :=
  (drv.vohMinMv + pullupBoostMv) - rcv.vihMinMv

/-- Low-state DC noise margin $\text{NM}_L = V_{IL,\max}^{\text{rcv}} - V_{OL,\max}^{\text{drv}}$ (in $\text{mV}$). -/
@[expose] def noiseMarginLow (drv rcv : LogicFamilySpec) : Int :=
  rcv.vilMaxMv - drv.volMaxMv

/-- Verify that driver logic family `drv` safely drives receiver logic family `rcv` with pull-up boost `pullupBoostMv`
and minimum required noise immunity `minMarginMv`. -/
@[expose] def checkLogicInterface (drv rcv : LogicFamilySpec) (pullupBoostMv minMarginMv : Int) : Bool :=
  decide (minMarginMv ≤ noiseMarginHigh drv rcv pullupBoostMv) &&
  decide (minMarginMv ≤ noiseMarginLow drv rcv) &&
  decide (drv.volMaxMv < rcv.vihMinMv)

/-- Whenever `checkLogicInterface drv rcv pullupBoostMv minMarginMv = true`, both high and low noise margins
meet `minMarginMv` and $V_{OL,\max}^{\text{drv}} < V_{IH,\min}^{\text{rcv}}$. -/
theorem checkLogicInterface_guarantees_valid_thresholds
    (drv rcv : LogicFamilySpec) (pullupBoostMv minMarginMv : Int)
    (hOk : checkLogicInterface drv rcv pullupBoostMv minMarginMv = true) :
    rcv.vihMinMv + minMarginMv ≤ drv.vohMinMv + pullupBoostMv ∧
    drv.volMaxMv + minMarginMv ≤ rcv.vilMaxMv ∧
    drv.volMaxMv < rcv.vihMinMv := by
  dsimp only [checkLogicInterface] at hOk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hOk
  rw [decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hOk
  have h1 : minMarginMv ≤ drv.vohMinMv + pullupBoostMv - rcv.vihMinMv := hOk.1.1
  have h2 : minMarginMv ≤ rcv.vilMaxMv - drv.volMaxMv := hOk.1.2
  have h3 : drv.volMaxMv < rcv.vihMinMv := hOk.2
  refine ⟨by omega, by omega, h3⟩

inductive PinClass where
  | powerIn (railMv minMv maxMv : Int) | powerOut (railMv maxLoadMa : Int) | gnd
  | bidirIo (logic : LogicFamilySpec) | diffPos (pairId : Nat) | diffNeg (pairId : Nat)
  | openDrain (vMaxMv iSinkUa : Int) | rfPort (z0MilliOhm : Nat)
  deriving DecidableEq, Repr
structure PadGeometry2D where
  padXNm            : Int
  padYNm            : Int
  apertureWidthNm   : Nat
  apertureLengthNm  : Nat
  toeFilletMarginNm : Nat
  deriving DecidableEq, Repr
structure ComponentPinSpec where
  pinId     : Nat
  pinName   : String
  elecClass : PinClass
  pad       : PadGeometry2D
  deriving DecidableEq, Repr
structure FootprintPackageSpec where
  partNumber        : String
  courtyardWidthNm  : Nat
  courtyardLengthNm : Nat
  pins              : Array ComponentPinSpec
  deriving DecidableEq, Repr
structure D4Transform where
  rot     : Fin 4
  mirrorX : Bool
  deriving DecidableEq, Repr
def D4Transform.apply (g : D4Transform) (x y : Int) : Int × Int :=
  let x' := if g.mirrorX then -x else x
  match g.rot.val with | 0 => (x', y) | 1 => (-y, x') | 2 => (-x', -y) | _ => (y, -x')
def allD4Transforms : List D4Transform :=
  [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩, ⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]
theorem mem_allD4Transforms (g : D4Transform) : g ∈ allD4Transforms := by
  rcases g with ⟨⟨r, hr⟩, m⟩; have hCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  cases m <;> rcases hCases with rfl | rfl | rfl | rfl <;> simp [allD4Transforms]
def courtyardFits (g : D4Transform) (pkgA pkgB : FootprintPackageSpec) : Prop :=
  if g.rot.val % 2 = 1 then pkgB.courtyardWidthNm ≤ pkgA.courtyardLengthNm ∧ pkgB.courtyardLengthNm ≤ pkgA.courtyardWidthNm
  else pkgB.courtyardWidthNm ≤ pkgA.courtyardWidthNm ∧ pkgB.courtyardLengthNm ≤ pkgA.courtyardLengthNm
def checkCourtyardFits (g : D4Transform) (pkgA pkgB : FootprintPackageSpec) : Bool :=
  if g.rot.val % 2 == 1 then decide (pkgB.courtyardWidthNm ≤ pkgA.courtyardLengthNm) && decide (pkgB.courtyardLengthNm ≤ pkgA.courtyardWidthNm)
  else decide (pkgB.courtyardWidthNm ≤ pkgA.courtyardWidthNm) && decide (pkgB.courtyardLengthNm ≤ pkgA.courtyardLengthNm)
theorem checkCourtyardFits_iff (g : D4Transform) (pkgA pkgB : FootprintPackageSpec) :
    checkCourtyardFits g pkgA pkgB = true ↔ courtyardFits g pkgA pkgB := by
  unfold checkCourtyardFits courtyardFits; by_cases h : g.rot.val % 2 = 1 <;> simp [h]
def checkPinClassCompat (minMarginMv : Int) (cA cB : PinClass) : Bool :=
  match cA, cB with
  | .powerIn railA minA maxA, .powerIn railB minB maxB => decide (railA = railB) && decide (minB ≤ minA) && decide (maxA ≤ maxB)
  | .powerOut railA loadA, .powerOut railB loadB => decide (railA = railB) && decide (loadA ≤ loadB)
  | .gnd, .gnd => true
  | .bidirIo logicA, .bidirIo logicB => checkLogicInterface logicB logicA 0 minMarginMv && checkLogicInterface logicA logicB 0 minMarginMv
  | .diffPos idA, .diffPos idB => decide (idA = idB)
  | .diffNeg idA, .diffNeg idB => decide (idA = idB)
  | .openDrain vA iA, .openDrain vB iB => decide (vA ≤ vB) && decide (iA ≤ iB)
  | .rfPort zA, .rfPort zB => decide (zA = zB)
  | _, _ => false
def checkPinPairCompat (minMarginMv : Int) (padTolNm : Nat) (g : D4Transform) (pA pB : ComponentPinSpec) : Bool :=
  let (gx, gy) := g.apply pA.pad.padXNm pA.pad.padYNm
  let (apWA, apLA) := if g.rot.val % 2 == 1 then (pA.pad.apertureLengthNm, pA.pad.apertureWidthNm) else (pA.pad.apertureWidthNm, pA.pad.apertureLengthNm)
  checkPinClassCompat minMarginMv pA.elecClass pB.elecClass &&
  decide ((pB.pad.padXNm - gx).natAbs + padTolNm ≤ pA.pad.toeFilletMarginNm) &&
  decide ((pB.pad.padYNm - gy).natAbs + padTolNm ≤ pA.pad.toeFilletMarginNm) &&
  decide (pB.pad.apertureWidthNm ≤ apWA + pA.pad.toeFilletMarginNm) && decide (apWA ≤ pB.pad.apertureWidthNm + pA.pad.toeFilletMarginNm) &&
  decide (pB.pad.apertureLengthNm ≤ apLA + pA.pad.toeFilletMarginNm) && decide (apLA ≤ pB.pad.apertureLengthNm + pA.pad.toeFilletMarginNm)
def IsBijectionOn (n : Nat) (π : Nat → Nat) : Prop :=
  (∀ i, i < n → π i < n) ∧ (∀ i j, i < n → j < n → π i = π j → i = j) ∧ (∀ j, j < n → ∃ i, i < n ∧ π i = j)
def PinoutDropInEquiv (minMarginMv : Int) (padTolNm : Nat) (pkgA pkgB : FootprintPackageSpec) : Prop :=
  ∃ (g : D4Transform) (π : Nat → Nat),
    courtyardFits g pkgA pkgB ∧ pkgA.pins.size = pkgB.pins.size ∧ IsBijectionOn pkgA.pins.size π ∧
    ∀ (i : Nat) (hi : i < pkgA.pins.size) (hpi : π i < pkgB.pins.size),
      checkPinPairCompat minMarginMv padTolNm g pkgA.pins[i] pkgB.pins[π i] = true
def pinClassSig : PinClass → Nat × Nat
  | .powerIn _ _ _ => (0, 0) | .powerOut _ _ => (1, 0) | .gnd => (2, 0) | .bidirIo _ => (3, 0)
  | .diffPos id => (4, id) | .diffNeg id => (5, id) | .openDrain _ _ => (6, 0) | .rfPort z0 => (7, z0)
private theorem checkPinPairCompat_imp_sig_eq (minMarginMv : Int) (padTolNm : Nat)
    (g : D4Transform) (pA pB : ComponentPinSpec) (h : checkPinPairCompat minMarginMv padTolNm g pA pB = true) :
    pinClassSig pA.elecClass = pinClassSig pB.elecClass := by
  unfold checkPinPairCompat at h; simp only [Bool.and_eq_true] at h
  have hc := h.1.1.1.1.1.1; unfold checkPinClassCompat at hc
  cases hA : pA.elecClass <;> cases hB : pB.elecClass <;> simp [hA, hB, pinClassSig] at hc ⊢ <;> exact hc
private def insertBucket (sig : Nat × Nat) (idx : Nat) : List ((Nat × Nat) × List Nat) → List ((Nat × Nat) × List Nat)
  | [] => [(sig, [idx])]
  | (s, xs) :: rest => if s == sig then (s, idx :: xs) :: rest else (s, xs) :: insertBucket sig idx rest
private def lookupBucket (sig : Nat × Nat) : List ((Nat × Nat) × List Nat) → List Nat
  | [] => []
  | (s, xs) :: rest => if s == sig then xs else lookupBucket sig rest

private theorem mem_lookupBucket_insertBucket (sig s : Nat × Nat) (idx j : Nat)
    (bs : List ((Nat × Nat) × List Nat)) :
    j ∈ lookupBucket s (insertBucket sig idx bs) ↔ (s = sig ∧ j = idx) ∨ j ∈ lookupBucket s bs := by
  induction bs with
  | nil =>
    simp only [insertBucket, lookupBucket, List.not_mem_nil, or_false]
    by_cases h : sig = s
    · subst h; simp
    · simp [beq_false_of_ne h, Ne.symm h]
  | cons hd rest ih =>
    rcases hd with ⟨k, xs⟩
    by_cases hks : k = sig
    · subst hks; simp only [insertBucket, beq_self_eq_true, ↓reduceIte, lookupBucket]
      by_cases hke : k = s
      · subst hke; simp
      · simp [beq_false_of_ne hke, Ne.symm hke]
    · simp only [insertBucket, beq_false_of_ne hks, Bool.false_eq_true, ↓reduceIte, lookupBucket]
      by_cases hke : k = s
      · subst hke; simp [hks]
      · simp only [beq_false_of_ne hke, Bool.false_eq_true, ↓reduceIte]; exact ih
private def buildPinBucketsAux (pins : Array ComponentPinSpec) :
    Nat → List ((Nat × Nat) × List Nat) → List ((Nat × Nat) × List Nat)
  | 0, acc => acc
  | i + 1, acc => buildPinBucketsAux pins i (if h : i < pins.size then insertBucket (pinClassSig pins[i].elecClass) i acc else acc)
private def buildPinBuckets (pins : Array ComponentPinSpec) : List ((Nat × Nat) × List Nat) :=
  buildPinBucketsAux pins pins.size []
private theorem mem_lookupBucket_buildPinBuckets (pins : Array ComponentPinSpec) (s : Nat × Nat) (j : Nat) :
    j ∈ lookupBucket s (buildPinBuckets pins) ↔ ∃ (hj : j < pins.size), pinClassSig pins[j].elecClass = s := by
  have hAux : ∀ (k : Nat) (hk : k ≤ pins.size) (acc : List ((Nat × Nat) × List Nat)),
      j ∈ lookupBucket s (buildPinBucketsAux pins k acc) ↔
        (∃ (hj : j < k), pinClassSig (pins[j]'(by omega)).elecClass = s) ∨ j ∈ lookupBucket s acc := by
    intro k; induction k with
    | zero => intro _ _; simp [buildPinBucketsAux]
    | succ m ih =>
      intro hk acc; have hm : m < pins.size := by omega
      simp only [buildPinBucketsAux, hm, ↓reduceDIte, ih (by omega), mem_lookupBucket_insertBucket]
      refine ⟨by rintro (⟨hj, hs⟩ | ⟨hs, rfl⟩ | ha); exact Or.inl ⟨by omega, hs⟩; exact Or.inl ⟨by omega, hs.symm⟩; exact Or.inr ha,
              by rintro (⟨hj, hs⟩ | ha)
                 · by_cases hjm : j < m
                   · exact Or.inl ⟨hjm, hs⟩
                   · have : j = m := by omega
                     subst this; exact Or.inr (Or.inl ⟨hs.symm, rfl⟩)
                 · exact Or.inr (Or.inr ha)⟩
  unfold buildPinBuckets; rw [hAux pins.size (Nat.le_refl _) []]; simp [lookupBucket]
private theorem getD_set_eq (used : Array Bool) (j k : Nat) (hj : j < used.size) (hk : k < used.size) :
    (used.set j true hj).getD k false = if k = j then true else used.getD k false := by
  have hk' : k < (used.set j true hj).size := by simp [hk]
  simp only [Array.getD, hk, hk', ↓reduceDIte]
  by_cases h : k = j
  · subst h; simp
  · simp [h, Array.getElem_set_ne (by omega) (by omega) (Ne.symm h)]
private theorem getD_push_eq (acc : Array Nat) (j idx d : Nat) (h : idx ≤ acc.size) :
    (acc.push j).getD idx d = if idx = acc.size then j else acc.getD idx d := by
  have h' : idx < (acc.push j).size := by simp; omega
  by_cases he : idx = acc.size
  · subst he; simp [Array.getD, Array.getElem_push_eq]
  · have hlt : idx < acc.size := by omega
    rw [ite_eq_right he]; simp only [Array.getD, hlt, h', ↓reduceDIte]; exact Array.getElem_push_lt hlt
private theorem usedInv_extend (n i j : Nat) (used : Array Bool) (f : Nat → Nat)
    (hUsedSz : used.size = n) (hj : j < used.size) (hFi : f i = j)
    (hInv : ∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ f idx = k)) :
    ∀ k, k < n → ((used.set j true hj).getD k false = true ↔ ∃ idx, idx < i + 1 ∧ f idx = k) := by
  intro k hk; rw [getD_set_eq used j k hj (by omega)]
  by_cases hkj : k = j
  · subst hkj; simp only [↓reduceIte, true_iff]; exact ⟨i, by omega, hFi⟩
  · simp only [hkj, ↓reduceIte, hInv k hk]
    refine ⟨fun ⟨idx, hidx, heq⟩ => ⟨idx, by omega, heq⟩, fun ⟨idx, hidx, heq⟩ => ?_⟩
    by_cases hlt : idx < i
    · exact ⟨idx, hlt, heq⟩
    · have : idx = i := by omega
      subst this; rw [hFi] at heq; exact absurd heq.symm hkj

private def verifyPermLoop (n : Nat) (compat : Nat → Nat → Bool) (perm : Array Nat) : Nat → Nat → Array Bool → Bool
  | 0, _, used => used.toList.all id
  | rem + 1, i, used =>
    if hpi : i < perm.size then
      let j := perm[i]
      if hj : j < used.size then
        if !used[j] && compat i j then verifyPermLoop n compat perm rem (i + 1) (used.set j true) else false
      else false
    else false

def verifyPinoutBijection (minMarginMv : Int) (padTolNm : Nat) (g : D4Transform)
    (pkgA pkgB : FootprintPackageSpec) (perm : Array Nat) : Bool :=
  let n := pkgA.pins.size
  checkCourtyardFits g pkgA pkgB && decide (n = pkgB.pins.size) && decide (perm.size = n) &&
  verifyPermLoop n
    (fun i j => if h : i < pkgA.pins.size ∧ j < pkgB.pins.size then
      checkPinPairCompat minMarginMv padTolNm g pkgA.pins[i] pkgB.pins[j] else false)
    perm n 0 (Array.replicate n false)

private theorem toList_all_id_iff (a : Array Bool) :
    a.toList.all id = true ↔ ∀ (k : Nat) (hk : k < a.size), a[k] = true := by
  rw [List.all_eq_true]; constructor
  · intro h k hk; simpa using h a[k] (Array.mem_toList_iff.mpr (Array.getElem_mem hk))
  · intro h x hx; obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx; simpa using h k (by simpa using hk)

private theorem verifyPermLoop_sound (n : Nat) (compat : Nat → Nat → Bool) (perm : Array Nat) (hPermSz : perm.size = n) :
    ∀ (rem i : Nat) (used : Array Bool), rem + i = n → used.size = n →
      (∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ perm.getD idx n = k)) →
      (∀ a b, a < i → b < i → perm.getD a n = perm.getD b n → a = b) →
      (∀ idx, idx < i → perm.getD idx n < n ∧ compat idx (perm.getD idx n) = true) →
      verifyPermLoop n compat perm rem i used = true →
      IsBijectionOn n (fun idx => perm.getD idx n) ∧ ∀ idx, idx < n → compat idx (perm.getD idx n) = true
  | 0, i, used, hSum, hUsedSz, hInv, hInj, hComp, hOk => by
    have hi : i = n := by omega
    subst hi; unfold verifyPermLoop at hOk; rw [toList_all_id_iff] at hOk
    refine ⟨⟨fun idx h => (hComp idx h).1, hInj, fun j hj => ?_⟩, fun idx h => (hComp idx h).2⟩
    have hj' : j < used.size := by omega
    exact (hInv j hj).mp (by simpa [Array.getD, hj'] using hOk j hj')
  | rem + 1, i, used, hSum, hUsedSz, hInv, hInj, hComp, hOk => by
    unfold verifyPermLoop at hOk; have hi : i < perm.size := by omega
    simp only [hi, ↓reduceDIte] at hOk
    have hGetI : perm.getD i n = perm[i]'hi := by simp [Array.getD, hi]
    by_cases hj : perm[i]'hi < used.size
    · simp only [hj, ↓reduceDIte] at hOk
      cases hUJ : used[perm[i]'hi]'hj with
      | true => simp [hUJ] at hOk
      | false =>
        cases hCI : compat i (perm[i]'hi) with
        | false => simp [hUJ, hCI] at hOk
        | true =>
          simp only [hUJ, Bool.not_false, hCI, Bool.and_self, ↓reduceIte] at hOk
          have hUJd : used.getD (perm[i]'hi) false = false := by simp [Array.getD, hj, hUJ]
          refine verifyPermLoop_sound n compat perm hPermSz rem (i + 1) (used.set (perm[i]'hi) true hj)
            (by omega) (by simp [hUsedSz]) (usedInv_extend n i (perm[i]'hi) used (fun idx => perm.getD idx n) hUsedSz hj hGetI hInv) ?_ ?_ hOk
          · intro a b ha hb heq
            by_cases ha' : a < i <;> by_cases hb' : b < i
            · exact hInj a b ha' hb' heq
            · have : b = i := by omega
              subst this; rw [hGetI] at heq; have hT := (hInv _ (by omega)).mpr ⟨a, ha', heq⟩; rw [hUJd] at hT; cases hT
            · have : a = i := by omega
              subst this; rw [hGetI] at heq; have hT := (hInv _ (by omega)).mpr ⟨b, hb', heq.symm⟩; rw [hUJd] at hT; cases hT
            · omega
          · intro idx hidx
            by_cases hlt : idx < i
            · exact hComp idx hlt
            · have : idx = i := by omega
              subst this; rw [hGetI]; exact ⟨by omega, hCI⟩
    · simp only [hj, ↓reduceDIte] at hOk; cases hOk

private theorem verifyPermLoop_complete (n : Nat) (compat : Nat → Nat → Bool) (perm : Array Nat)
    (hPermSz : perm.size = n) (hBij : IsBijectionOn n (fun idx => perm.getD idx n))
    (hAllComp : ∀ idx, idx < n → compat idx (perm.getD idx n) = true) :
    ∀ (rem i : Nat) (used : Array Bool), rem + i = n → used.size = n →
      (∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ perm.getD idx n = k)) →
      verifyPermLoop n compat perm rem i used = true
  | 0, i, used, hSum, hUsedSz, hInv => by
    have hi : i = n := by omega
    subst hi; unfold verifyPermLoop; rw [toList_all_id_iff]
    intro k hk; simpa [Array.getD, hk] using (hInv k (by omega)).mpr (hBij.2.2 k (by omega))
  | rem + 1, i, used, hSum, hUsedSz, hInv => by
    unfold verifyPermLoop; have hi : i < perm.size := by omega
    simp only [hi, ↓reduceDIte]; have hGetI : perm.getD i n = perm[i]'hi := by simp [Array.getD, hi]
    have hjLt : perm[i]'hi < n := hGetI ▸ hBij.1 i (by omega)
    have hj : perm[i]'hi < used.size := by omega
    simp only [hj, ↓reduceDIte]
    have hUnused : used[perm[i]'hi]'hj = false := by
      cases hU : used[perm[i]'hi]'hj with
      | false => rfl
      | true =>
        obtain ⟨idx, hidx, heq⟩ := (hInv _ hjLt).mp (by simp [Array.getD, hj, hU])
        have := hBij.2.1 idx i (by omega) (by omega) (heq.trans hGetI.symm); omega
    have hCI : compat i (perm[i]'hi) = true := hGetI ▸ hAllComp i (by omega)
    simp only [hUnused, Bool.not_false, hCI, Bool.and_self, ↓reduceIte]
    exact verifyPermLoop_complete n compat perm hPermSz hBij hAllComp rem (i + 1)
      (used.set (perm[i]'hi) true hj) (by omega) (by simp [hUsedSz])
      (usedInv_extend n i (perm[i]'hi) used (fun idx => perm.getD idx n) hUsedSz hj hGetI hInv)

theorem verifyPinoutBijection_iff (minMarginMv : Int) (padTolNm : Nat) (g : D4Transform)
    (pkgA pkgB : FootprintPackageSpec) (perm : Array Nat) :
    verifyPinoutBijection minMarginMv padTolNm g pkgA pkgB perm = true ↔
      courtyardFits g pkgA pkgB ∧ pkgA.pins.size = pkgB.pins.size ∧ perm.size = pkgA.pins.size ∧
      IsBijectionOn pkgA.pins.size (fun i => perm.getD i pkgA.pins.size) ∧
      ∀ (i : Nat) (hi : i < pkgA.pins.size) (hpi : perm.getD i pkgA.pins.size < pkgB.pins.size),
        checkPinPairCompat minMarginMv padTolNm g pkgA.pins[i] pkgB.pins[perm.getD i pkgA.pins.size] = true := by
  unfold verifyPinoutBijection; simp only [Bool.and_eq_true, decide_eq_true_eq, checkCourtyardFits_iff]
  constructor
  · rintro ⟨⟨⟨hCourt, hSz⟩, hPermSz⟩, hLoop⟩
    have hS := verifyPermLoop_sound pkgA.pins.size _ perm hPermSz pkgA.pins.size 0
      (Array.replicate pkgA.pins.size false) (by omega) (by simp)
      (by intro k hk; simp [Array.getD, hk]) (by intro a _ ha; omega) (by intro idx h; omega) hLoop
    refine ⟨hCourt, hSz, hPermSz, hS.1, fun i hi hpi => ?_⟩
    have hc := hS.2 i hi; have hB : i < pkgA.pins.size ∧ perm.getD i pkgA.pins.size < pkgB.pins.size := ⟨hi, hpi⟩
    simp only [hB] at hc; exact hc
  · rintro ⟨hCourt, hSz, hPermSz, hBij, hCompat⟩
    refine ⟨⟨⟨hCourt, hSz⟩, hPermSz⟩, verifyPermLoop_complete pkgA.pins.size _ perm hPermSz hBij ?_
      pkgA.pins.size 0 (Array.replicate pkgA.pins.size false) (by omega) (by simp)
      (by intro k hk; simp [Array.getD, hk])⟩
    intro i hi; have hpi : perm.getD i pkgA.pins.size < pkgB.pins.size := hSz ▸ hBij.1 i hi
    simp only [hi, hpi, and_self, ↓reduceDIte]; exact hCompat i hi hpi
private def tryCandidates (compat : Nat → Nat → Bool) (i : Nat) (used : Array Bool) (acc : Array Nat)
    (recurse : Array Bool → Array Nat → Option (Array Nat)) : List Nat → Option (Array Nat)
  | [] => none
  | j :: js =>
    if hj : j < used.size then
      if !used[j] && compat i j then
        match recurse (used.set j true) (acc.push j) with
        | some res => some res
        | none => tryCandidates compat i used acc recurse js
      else tryCandidates compat i used acc recurse js
    else tryCandidates compat i used acc recurse js
private def backtrackMatch (compat : Nat → Nat → Bool) (cands : Nat → List Nat) :
    Nat → Nat → Array Bool → Array Nat → Option (Array Nat)
  | 0, _, used, acc => if used.toList.all id then some acc else none
  | rem + 1, i, used, acc =>
    tryCandidates compat i used acc (fun u a => backtrackMatch compat cands rem (i + 1) u a) (cands i)
private theorem tryCandidates_sound (compat : Nat → Nat → Bool) (i : Nat) (used : Array Bool)
    (acc : Array Nat) (recurse : Array Bool → Array Nat → Option (Array Nat)) (P : Array Nat → Prop)
    (hRec : ∀ (j : Nat) (hj : j < used.size),
      used[j] = false → compat i j = true → ∀ r, recurse (used.set j true) (acc.push j) = some r → P r) :
    ∀ (js : List Nat) (res : Array Nat), tryCandidates compat i used acc recurse js = some res → P res
  | [], _, h => by simp [tryCandidates] at h
  | j :: js, res, h => by
    unfold tryCandidates at h
    by_cases hj : j < used.size
    · simp only [hj, ↓reduceDIte] at h
      cases hUJ : used[j]'hj with
      | true => simp [hUJ] at h; exact tryCandidates_sound compat i used acc recurse P hRec js res h
      | false =>
        cases hCI : compat i j with
        | false => simp [hUJ, hCI] at h; exact tryCandidates_sound compat i used acc recurse P hRec js res h
        | true =>
          simp only [hUJ, Bool.not_false, hCI, Bool.and_self, ↓reduceIte] at h
          cases hR : recurse (used.set j true hj) (acc.push j) with
          | some r => rw [hR] at h; cases h; exact hRec j hj hUJ hCI res hR
          | none => rw [hR] at h; exact tryCandidates_sound compat i used acc recurse P hRec js res h
    · simp only [hj, ↓reduceDIte] at h; exact tryCandidates_sound compat i used acc recurse P hRec js res h
private theorem tryCandidates_complete (compat : Nat → Nat → Bool) (i : Nat) (used : Array Bool)
    (acc : Array Nat) (recurse : Array Bool → Array Nat → Option (Array Nat)) :
    ∀ (js : List Nat) (j : Nat) (hj : j < used.size),
      j ∈ js → used[j] = false → compat i j = true →
      (recurse (used.set j true) (acc.push j)).isSome = true →
      (tryCandidates compat i used acc recurse js).isSome = true
  | [], _, _, hM, _, _, _ => by cases hM
  | x :: xs, j, hj, hM, hUn, hC, hR => by
    unfold tryCandidates
    by_cases hx : x < used.size
    · simp only [hx, ↓reduceDIte]
      by_cases hOk : (!used[x]'hx && compat i x) = true
      · simp only [hOk]
        cases hRec : recurse (used.set x true hx) (acc.push x) with
        | some _ => simp
        | none =>
          rcases List.mem_cons.mp hM with rfl | hT
          · rw [hRec] at hR; cases hR
          · exact tryCandidates_complete compat i used acc recurse xs j hj hT hUn hC hR
      · simp only [hOk]
        rcases List.mem_cons.mp hM with rfl | hT
        · simp [hUn, hC] at hOk
        · exact tryCandidates_complete compat i used acc recurse xs j hj hT hUn hC hR
    · simp only [hx, ↓reduceDIte]
      rcases List.mem_cons.mp hM with rfl | hT
      · exact absurd hj hx
      · exact tryCandidates_complete compat i used acc recurse xs j hj hT hUn hC hR
private theorem backtrackMatch_sound (n : Nat) (compat : Nat → Nat → Bool) (cands : Nat → List Nat) :
    ∀ (rem i : Nat) (used : Array Bool) (acc res : Array Nat),
      rem + i = n → used.size = n → acc.size = i →
      (∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ acc.getD idx n = k)) →
      (∀ a b, a < i → b < i → acc.getD a n = acc.getD b n → a = b) →
      (∀ idx, idx < i → acc.getD idx n < n ∧ compat idx (acc.getD idx n) = true) →
      backtrackMatch compat cands rem i used acc = some res →
      res.size = n ∧ IsBijectionOn n (fun idx => res.getD idx n) ∧ ∀ idx, idx < n → compat idx (res.getD idx n) = true
  | 0, i, used, acc, res, hSum, hUsedSz, hAccSz, hInv, hInj, hComp, hOk => by
    have hi : i = n := by omega
    subst hi; unfold backtrackMatch at hOk
    cases hAll : used.toList.all id with
    | false => simp only [hAll, Bool.false_eq_true, ↓reduceIte] at hOk; cases hOk
    | true =>
      simp only [hAll, ↓reduceIte, Option.some.injEq] at hOk; subst hOk; rw [toList_all_id_iff] at hAll
      refine ⟨hAccSz, ⟨fun idx h => (hComp idx h).1, hInj, fun j hj => ?_⟩, fun idx h => (hComp idx h).2⟩
      have hj' : j < used.size := by omega
      exact (hInv j hj).mp (by simpa [Array.getD, hj'] using hAll j hj')
  | rem + 1, i, used, acc, res, hSum, hUsedSz, hAccSz, hInv, hInj, hComp, hOk => by
    unfold backtrackMatch at hOk
    refine tryCandidates_sound compat i used acc _
      (fun r => r.size = n ∧ IsBijectionOn n (fun idx => r.getD idx n) ∧ ∀ idx, idx < n → compat idx (r.getD idx n) = true)
      ?_ (cands i) res hOk
    intro j hj hUn hCI r hRec
    have hUJd : used.getD j false = false := by simp [Array.getD, hj, hUn]
    have hPushLt : ∀ idx, idx < i → (acc.push j).getD idx n = acc.getD idx n := fun idx hidx => by
      rw [getD_push_eq acc j idx n (by omega), ite_eq_right (by omega)]
    have hPushEq : (acc.push j).getD i n = j := by rw [getD_push_eq acc j i n (by omega), ite_eq_left hAccSz.symm]
    have hPrevInv : ∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ (acc.push j).getD idx n = k) := fun k hk => by
      rw [hInv k hk]; exact ⟨fun ⟨idx, hidx, heq⟩ => ⟨idx, hidx, (hPushLt idx hidx).trans heq⟩,
        fun ⟨idx, hidx, heq⟩ => ⟨idx, hidx, (hPushLt idx hidx).symm.trans heq⟩⟩
    refine backtrackMatch_sound n compat cands rem (i + 1) (used.set j true hj) (acc.push j) r
      (by omega) (by simp [hUsedSz]) (by simp [hAccSz])
      (usedInv_extend n i j used (fun idx => (acc.push j).getD idx n) hUsedSz hj hPushEq hPrevInv) ?_ ?_ hRec
    · intro a b ha hb heq
      by_cases ha' : a < i <;> by_cases hb' : b < i
      · rw [hPushLt a ha', hPushLt b hb'] at heq; exact hInj a b ha' hb' heq
      · have hbi : b = i := by omega
        subst hbi; rw [hPushLt a ha', hPushEq] at heq
        have hT := (hInv j (by omega)).mpr ⟨a, ha', heq⟩; rw [hUJd] at hT; cases hT
      · have hai : a = i := by omega
        subst hai; rw [hPushEq, hPushLt b hb'] at heq
        have hT := (hInv j (by omega)).mpr ⟨b, hb', heq.symm⟩; rw [hUJd] at hT; cases hT
      · omega
    · intro idx hidx
      by_cases hlt : idx < i
      · rw [hPushLt idx hlt]; exact hComp idx hlt
      · have : idx = i := by omega
        subst this; rw [hPushEq]; exact ⟨by omega, hCI⟩
private theorem backtrackMatch_complete (n : Nat) (compat : Nat → Nat → Bool) (cands : Nat → List Nat)
    (π : Nat → Nat) (hBij : IsBijectionOn n π)
    (hComp : ∀ idx, idx < n → compat idx (π idx) = true) (hCands : ∀ idx, idx < n → π idx ∈ cands idx) :
    ∀ (rem i : Nat) (used : Array Bool) (acc : Array Nat), rem + i = n → used.size = n →
      (∀ k, k < n → (used.getD k false = true ↔ ∃ idx, idx < i ∧ π idx = k)) →
      (backtrackMatch compat cands rem i used acc).isSome = true
  | 0, i, used, acc, hSum, hUsedSz, hInv => by
    have hi : i = n := by omega
    subst hi; unfold backtrackMatch
    have hAll : used.toList.all id = true := (toList_all_id_iff used).mpr (fun k hk => by simpa [Array.getD, hk] using (hInv k (by omega)).mpr (hBij.2.2 k (by omega)))
    simp only [hAll, ↓reduceIte, Option.isSome_some]
  | rem + 1, i, used, acc, hSum, hUsedSz, hInv => by
    unfold backtrackMatch; have hiLt : i < n := by omega
    have hpiLt : π i < used.size := by have := hBij.1 i hiLt; omega
    have hUnused : used[π i]'hpiLt = false := by
      cases hU : used[π i]'hpiLt with
      | false => rfl
      | true =>
        obtain ⟨idx, hidx, heq⟩ := (hInv (π i) (hBij.1 i hiLt)).mp (by simp [Array.getD, hpiLt, hU])
        have := hBij.2.1 idx i (by omega) hiLt heq; omega
    exact tryCandidates_complete compat i used acc _ (cands i) (π i) hpiLt (hCands i hiLt) hUnused (hComp i hiLt)
      (backtrackMatch_complete n compat cands π hBij hComp hCands rem (i + 1)
        (used.set (π i) true hpiLt) (acc.push (π i)) (by omega) (by simp [hUsedSz])
        (usedInv_extend n i (π i) used π hUsedSz hpiLt rfl hInv))
def findBijectionForD4 (minMarginMv : Int) (padTolNm : Nat) (g : D4Transform)
    (pkgA pkgB : FootprintPackageSpec) : Option (Array Nat) :=
  if checkCourtyardFits g pkgA pkgB && decide (pkgA.pins.size = pkgB.pins.size) then
    let n := pkgA.pins.size; let buckets := buildPinBuckets pkgB.pins
    let compat (i j : Nat) : Bool :=
      if h : i < pkgA.pins.size ∧ j < pkgB.pins.size then checkPinPairCompat minMarginMv padTolNm g pkgA.pins[i] pkgB.pins[j] else false
    let cands (i : Nat) : List Nat :=
      if hi : i < pkgA.pins.size then lookupBucket (pinClassSig pkgA.pins[i].elecClass) buckets else []
    backtrackMatch compat cands n 0 (Array.replicate n false) #[]
  else none
def findPinoutBijectionExec (minMarginMv : Int) (padTolNm : Nat)
    (pkgA pkgB : FootprintPackageSpec) : Option (D4Transform × Array Nat) :=
  allD4Transforms.findSome? fun g =>
    match findBijectionForD4 minMarginMv padTolNm g pkgA pkgB with | some p => some (g, p) | none => none
def checkPinoutIso (minMarginMv : Int) (padTolNm : Nat) (pkgA pkgB : FootprintPackageSpec) : Bool :=
  (findPinoutBijectionExec minMarginMv padTolNm pkgA pkgB).isSome
private theorem findSome_isSome_iff {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.findSome? f).isSome = true ↔ ∃ x ∈ xs, (f x).isSome = true := by
  induction xs with | nil => simp | cons a rest ih => simp only [List.findSome?_cons]; cases hfa : f a <;> simp [hfa, ih]
/-- **Unconditional Bidirectional Soundness & Completeness (`checkPinoutIso_iff`)**. -/
theorem checkPinoutIso_iff (minMarginMv : Int) (padTolNm : Nat) (pkgA pkgB : FootprintPackageSpec) :
    checkPinoutIso minMarginMv padTolNm pkgA pkgB = true ↔ PinoutDropInEquiv minMarginMv padTolNm pkgA pkgB := by
  unfold checkPinoutIso findPinoutBijectionExec; rw [findSome_isSome_iff]
  constructor
  · rintro ⟨g, _, hSome⟩
    cases hFind : findBijectionForD4 minMarginMv padTolNm g pkgA pkgB with
    | none => simp [hFind] at hSome
    | some perm =>
      unfold findBijectionForD4 at hFind
      cases hPre : (checkCourtyardFits g pkgA pkgB && decide (pkgA.pins.size = pkgB.pins.size)) with
      | false => simp [hPre] at hFind
      | true =>
        simp only [hPre, ↓reduceIte] at hFind
        simp only [Bool.and_eq_true, decide_eq_true_eq, checkCourtyardFits_iff] at hPre
        have hS := backtrackMatch_sound pkgA.pins.size _ _ pkgA.pins.size 0
          (Array.replicate pkgA.pins.size false) #[] perm (by omega) (by simp) rfl
          (by intro k hk; simp [Array.getD, hk]) (by intro a _ ha; omega) (by intro idx h; omega) hFind
        refine ⟨g, fun i => perm.getD i pkgA.pins.size, hPre.1, hPre.2, hS.2.1, fun i hi hpi => ?_⟩
        have hc := hS.2.2 i hi; have hB : i < pkgA.pins.size ∧ perm.getD i pkgA.pins.size < pkgB.pins.size := ⟨hi, hpi⟩
        simp only [hB] at hc; exact hc
  · rintro ⟨g, π, hCourt, hSz, hBij, hCompat⟩
    refine ⟨g, mem_allD4Transforms g, ?_⟩
    have hPre : (checkCourtyardFits g pkgA pkgB && decide (pkgA.pins.size = pkgB.pins.size)) = true := by
      simp [checkCourtyardFits_iff, hCourt, hSz]
    have hComp : (findBijectionForD4 minMarginMv padTolNm g pkgA pkgB).isSome = true := by
      unfold findBijectionForD4; simp only [hPre, ↓reduceIte]
      refine backtrackMatch_complete pkgA.pins.size _ _ π hBij ?_ ?_ pkgA.pins.size 0
        (Array.replicate pkgA.pins.size false) #[] (by omega) (by simp) (by intro k hk; simp [Array.getD, hk])
      · intro i hi; have hpi : π i < pkgB.pins.size := hSz ▸ hBij.1 i hi
        simp only [hi, hpi, and_self, ↓reduceDIte]; exact hCompat i hi hpi
      · intro i hi; have hpi : π i < pkgB.pins.size := hSz ▸ hBij.1 i hi
        simp only [hi, ↓reduceDIte, mem_lookupBucket_buildPinBuckets]
        exact ⟨hpi, (checkPinPairCompat_imp_sig_eq minMarginMv padTolNm g _ _ (hCompat i hi hpi)).symm⟩
    cases hFind : findBijectionForD4 minMarginMv padTolNm g pkgA pkgB with
    | none => rw [hFind] at hComp; cases hComp
    | some _ => simp

/-! ## 2. 256-Bit `BitVec 256` `DetCbor` Datasheet Block Citation Freshness -/
structure DatasheetBlockSpec where
  datasheetPage : String
  blockAnchor   : String
  revision      : Nat
  vohMinMv      : Int
  vihMinMv      : Int
  volMaxMv      : Int
  vilMaxMv      : Int
  deriving DecidableEq, Repr
private def natToCbor (n : Nat) : CborVal :=
  if n = 0 then .array [.uint 0]
  else .array [.uint 1, .uint (UInt64.ofNat (n % 4294967296)), natToCbor (n / 4294967296)]
termination_by n
private def cborToNat : CborVal → Option Nat
  | .array [.uint 0] => some 0
  | .array [.uint 1, .uint lo, rest] => (cborToNat rest).map (fun hi => lo.toNat + 4294967296 * hi)
  | _ => none
termination_by structural v => v
private theorem natToCbor_wfVal (n : Nat) : wfVal (fun _ => true) false (natToCbor n) = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natToCbor]; split
    · rfl
    · rename_i hn; simpa [wfVal, wfList] using ih (n / 4294967296) (Nat.div_lt_self (by omega) (by decide))
private theorem cborToNat_natToCbor (n : Nat) : cborToNat (natToCbor n) = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natToCbor]; split
    · rename_i hn; subst hn; rfl
    · rename_i hn
      have hh := ih (n / 4294967296) (Nat.div_lt_self (by omega) (by decide))
      simp only [cborToNat, hh, Option.map_some]; congr 1
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := Nat.mod_lt n (by decide : 0 < 4294967296); omega)]; omega
private def intToCbor : Int → CborVal
  | .ofNat n => .array [.uint 0, natToCbor n] | .negSucc n => .array [.uint 1, natToCbor n]
private def cborToInt : CborVal → Option Int
  | .array [.uint 0, v] => (cborToNat v).map Int.ofNat | .array [.uint 1, v] => (cborToNat v).map Int.negSucc | _ => none
private theorem intToCbor_wfVal (z : Int) : wfVal (fun _ => true) false (intToCbor z) = true := by
  cases z <;> simp [intToCbor, wfVal, wfList, natToCbor_wfVal]
private theorem cborToInt_intToCbor (z : Int) : cborToInt (intToCbor z) = some z := by
  cases z <;> simp [intToCbor, cborToInt, cborToNat_natToCbor]
private def charListToCbor : List Char → CborVal
  | [] => .array [.uint 0] | c :: cs => .array [.uint 1, .uint (UInt64.ofNat c.toNat), charListToCbor cs]
private def cborToCharList : CborVal → Option (List Char)
  | .array [.uint 0] => some []
  | .array [.uint 1, .uint n, rest] => (cborToCharList rest).map (fun cs => Char.ofNat n.toNat :: cs)
  | _ => none
termination_by structural v => v
private theorem charListToCbor_wfVal (cs : List Char) : wfVal (fun _ => true) false (charListToCbor cs) = true := by
  induction cs with | nil => rfl | cons c cs ih => simpa [charListToCbor, wfVal, wfList] using ih
private theorem cborToCharList_charListToCbor (cs : List Char) : cborToCharList (charListToCbor cs) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [charListToCbor, cborToCharList, ih, Option.map_some]; congr 1
    have hlt : c.toNat < 18446744073709551616 := by
      have hc : c.val.toNat < 2 ^ 32 := c.val.toBitVec.isLt
      change c.val.toNat < 18446744073709551616; omega
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt, Char.ofNat_toNat]
def datasheetBlockToCbor (b : DatasheetBlockSpec) : CborVal :=
  .array [charListToCbor b.datasheetPage.toList, charListToCbor b.blockAnchor.toList,
    natToCbor b.revision, intToCbor b.vohMinMv, intToCbor b.vihMinMv, intToCbor b.volMaxMv, intToCbor b.vilMaxMv]
private def cborToDatasheetBlock : CborVal → Option DatasheetBlockSpec
  | .array [pg, anc, rev, voh, vih, vol, vil] => do
    let pgCs ← cborToCharList pg; let ancCs ← cborToCharList anc; let r ← cborToNat rev
    let v1 ← cborToInt voh; let v2 ← cborToInt vih; let v3 ← cborToInt vol; let v4 ← cborToInt vil
    pure ⟨String.ofList pgCs, String.ofList ancCs, r, v1, v2, v3, v4⟩
  | _ => none
theorem datasheetBlockToCbor_withinWidth (b : DatasheetBlockSpec) :
    WithinWidth (datasheetBlockToCbor b) = true := by
  simp [datasheetBlockToCbor, WithinWidth, wfVal, wfList, charListToCbor_wfVal, natToCbor_wfVal, intToCbor_wfVal]
theorem datasheetBlockToCbor_injective {b1 b2 : DatasheetBlockSpec}
    (h : datasheetBlockToCbor b1 = datasheetBlockToCbor b2) : b1 = b2 := by
  have hRt : ∀ b, cborToDatasheetBlock (datasheetBlockToCbor b) = some b := fun b => by
    cases b; simp [datasheetBlockToCbor, cborToDatasheetBlock, cborToCharList_charListToCbor,
      cborToNat_natToCbor, cborToInt_intToCbor, String.ofList_toList]
  have h1 := hRt b1; have h2 := hRt b2; rw [h] at h1; rw [h1] at h2; exact Option.some.inj h2
def datasheetBlockCborBytes (b : DatasheetBlockSpec) : List UInt8 := encSpec (datasheetBlockToCbor b)
def datasheetBlockDigest256 (H : Hash) (b : DatasheetBlockSpec) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (H (datasheetBlockCborBytes b)))
/-- Constructive (`0 Classical`) 256-bit scoped binding theorem via `DetCbor.encodeDetCbor_injective`. -/
theorem datasheetBlockDigest256_binding (H : Hash) (hLen : ∀ bs, (H bs).length ≤ 32)
    (b1 b2 : DatasheetBlockSpec) (hEq : datasheetBlockDigest256 H b1 = datasheetBlockDigest256 H b2) :
    b1 = b2 ∨ CollisionAmong H (fun x => x = datasheetBlockCborBytes b1 ∨ x = datasheetBlockCborBytes b2) := by
  if hPre : datasheetBlockCborBytes b1 = datasheetBlockCborBytes b2 then
    have hEncEq : encodeDetCbor (datasheetBlockToCbor b1) = encodeDetCbor (datasheetBlockToCbor b2) := by
      apply byteArray_eq_of_toList; rw [encodeDetCbor_data, encodeDetCbor_data]; exact hPre
    exact Or.inl (datasheetBlockToCbor_injective (encodeDetCbor_injective _ _
      (datasheetBlockToCbor_withinWidth b1) (datasheetBlockToCbor_withinWidth b2) hEncEq))
  else
    have hPow : ∀ k, k ≤ 32 → 256 ^ k ≤ 2 ^ 256 := fun k hk =>
      Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
    have hLt1 := Nat.lt_of_lt_of_le (ofBE_lt _) (hPow _ (hLen (datasheetBlockCborBytes b1)))
    have hLt2 := Nat.lt_of_lt_of_le (ofBE_lt _) (hPow _ (hLen (datasheetBlockCborBytes b2)))
    have hNatEq := congrArg BitVec.toNat hEq
    unfold datasheetBlockDigest256 at hNatEq; simp only [BitVec.toNat_ofNat] at hNatEq
    rw [Nat.mod_eq_of_lt hLt1, Nat.mod_eq_of_lt hLt2] at hNatEq
    exact Or.inr ⟨datasheetBlockCborBytes b1, datasheetBlockCborBytes b2, Or.inl rfl, Or.inr rfl, hPre, hNatEq⟩
structure DatasheetCite256 where
  datasheetPage    : String
  blockAnchor      : String
  pinnedDigest256  : BitVec 256
  currentDigest256 : BitVec 256
  deriving DecidableEq, Repr
abbrev DatasheetCitePin := DatasheetCite256
def checkDatasheetCite256Fresh (cite : DatasheetCite256) : Bool :=
  decide (cite.currentDigest256 ≠ 0#256) && decide (cite.pinnedDigest256 = cite.currentDigest256)
theorem staleDatasheetCite256_refused (cite : DatasheetCite256)
    (hStale : cite.pinnedDigest256 ≠ cite.currentDigest256) :
    checkDatasheetCite256Fresh cite = false := by
  unfold checkDatasheetCite256Fresh; rw [decide_eq_false hStale, Bool.and_false]

/-! ## 3. `EdaVaultPart` Compatibility API, 3-Way Merge & `.obnb` `Core.Data` Roundtrip -/
def edaStateKeys : List String :=
  sortNames ["voh_min_mv", "vih_min_mv", "vol_max_mv", "vil_max_mv", "pkg_width_um", "pkg_length_um",
    "pin_count", "pin_pitch_um", "max_temp_mc", "vswr_milli", "drc_errors", "cost_cents"]
structure EdaVaultPart where
  pageName    : String
  vohMinMv    : Nat
  vihMinMv    : Nat
  volMaxMv    : Nat
  vilMaxMv    : Nat
  pkgWidthUm  : Nat
  pkgLengthUm : Nat
  pinCount    : Nat
  pinPitchUm  : Nat
  maxTempMc   : Nat
  vswrMilli   : Nat
  drcErrors   : Nat
  costCents   : Nat
  deriving DecidableEq, Repr
private def lookupScalarField (fields : List (String × Nat)) (key : String) : Nat := (fields.lookup key).getD 0
def extractEdaVaultPart (pageName : String) (markdownSrc : String) : EdaVaultPart :=
  let fs := scalarFields markdownSrc
  ⟨pageName, lookupScalarField fs "voh_min_mv", lookupScalarField fs "vih_min_mv",
    lookupScalarField fs "vol_max_mv", lookupScalarField fs "vil_max_mv",
    lookupScalarField fs "pkg_width_um", lookupScalarField fs "pkg_length_um",
    lookupScalarField fs "pin_count", lookupScalarField fs "pin_pitch_um",
    lookupScalarField fs "max_temp_mc", lookupScalarField fs "vswr_milli",
    lookupScalarField fs "drc_errors", lookupScalarField fs "cost_cents"⟩
def EdaVaultPart.toScalarFields (p : EdaVaultPart) : List (String × Nat) :=
  [("voh_min_mv", p.vohMinMv), ("vih_min_mv", p.vihMinMv), ("vol_max_mv", p.volMaxMv), ("vil_max_mv", p.vilMaxMv),
   ("pkg_width_um", p.pkgWidthUm), ("pkg_length_um", p.pkgLengthUm), ("pin_count", p.pinCount), ("pin_pitch_um", p.pinPitchUm),
   ("max_temp_mc", p.maxTempMc), ("vswr_milli", p.vswrMilli), ("drc_errors", p.drcErrors), ("cost_cents", p.costCents)]
def EdaVaultPart.toLogicFamilySpec (p : EdaVaultPart) : LogicFamilySpec :=
  ⟨p.pageName, 3000, 3300, 3600, p.vihMinMv, p.vilMaxMv, p.vohMinMv, p.volMaxMv, 1, 1, 4000, 4000⟩
def lvcmos33ReceiverSpec : LogicFamilySpec :=
  ⟨"LVCMOS33_Receiver", 3000, 3300, 3600, 2000, 800, 2900, 200, 1, 1, 4000, 4000⟩
def baselineLdoPart : EdaVaultPart := ⟨"U4_LDO", 2900, 2000, 200, 800, 3000, 3000, 16, 500, 72000, 1350, 0, 145⟩
def secondSourceLdoPart : EdaVaultPart :=
  { baselineLdoPart with vohMinMv := 2950, volMaxMv := 180, maxTempMc := 68000, vswrMilli := 1280, costCents := 120 }
def overbudgetSecondSourcePart : EdaVaultPart := { secondSourceLdoPart with costCents := 320 }
def defaultDatasheetCite256 : DatasheetCite256 :=
  ⟨"TI_TPS7A47", "elec_spec",
   0x9A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C01#256,
   0x9A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C019A4F2C01#256⟩
def defaultEdaLaws : List (String × LawExpr) :=
  [("drc_zero", .eqC (.field "drc_errors") 0), ("thermal_cap", .leC (.field "max_temp_mc") 85000),
   ("rf_vswr_cap", .leC (.field "vswr_milli") 1500), ("bom_budget", .leC (.field "cost_cents") 250)]
def defaultEdaFacts : Facts := { caller := some 1, subject := some 1, height := 1, turn := 1 }
inductive AgenticEdaVerdict where
  | admitted | refusedBySmartContract (lawName reason : String) | refusedByPhysics (checkName : String) | undecided (why : String)
  deriving DecidableEq, Repr
def judgeAgenticEdaProposal (laws : List (String × LawExpr)) (oldPart newPart : EdaVaultPart)
    (downstreamReceiver : LogicFamilySpec) (minNoiseMarginMv : Int)
    (citePin : DatasheetCitePin) (agentName : String) (facts : Facts) : AgenticEdaVerdict :=
  match Obend.Vault.judge (stateTy edaStateKeys) newPart.pageName laws
      (stateOf edaStateKeys oldPart.toScalarFields) (stateOf edaStateKeys newPart.toScalarFields)
      (requestOf agentName .write facts) with
  | .refused lawName reason => .refusedBySmartContract lawName reason
  | .undecided why => .undecided why
  | .admitted =>
    if !checkDatasheetCite256Fresh citePin then .refusedByPhysics "stale-datasheet-cite"
    else if !checkLogicInterface newPart.toLogicFamilySpec downstreamReceiver 0 minNoiseMarginMv then
      .refusedByPhysics "cmos-noise-margin-violation"
    else .admitted
theorem agenticEdaProposal_admits_sound (laws : List (String × LawExpr))
    (oldPart newPart : EdaVaultPart) (downstreamReceiver : LogicFamilySpec)
    (minNoiseMarginMv : Int) (citePin : DatasheetCitePin) (agentName : String) (facts : Facts)
    (hAdmit : judgeAgenticEdaProposal laws oldPart newPart downstreamReceiver
      minNoiseMarginMv citePin agentName facts = .admitted) :
    let oldData := stateOf edaStateKeys oldPart.toScalarFields
    let newData := stateOf edaStateKeys newPart.toScalarFields
    (∀ p ∈ laws, p.2.denote facts (some oldData) newData = true) ∧
    citePin.pinnedDigest256 = citePin.currentDigest256 ∧
    downstreamReceiver.vihMinMv + minNoiseMarginMv ≤ newPart.toLogicFamilySpec.vohMinMv ∧
    newPart.toLogicFamilySpec.volMaxMv + minNoiseMarginMv ≤ downstreamReceiver.vilMaxMv := by
  unfold judgeAgenticEdaProposal at hAdmit
  cases hV : Obend.Vault.judge (stateTy edaStateKeys) newPart.pageName laws
      (stateOf edaStateKeys oldPart.toScalarFields) (stateOf edaStateKeys newPart.toScalarFields)
      (requestOf agentName .write facts) with
  | refused _ _ => rw [hV] at hAdmit; cases hAdmit
  | undecided _ => rw [hV] at hAdmit; cases hAdmit
  | admitted =>
    rw [hV] at hAdmit
    cases hCite : checkDatasheetCite256Fresh citePin with
    | false => simp [hCite] at hAdmit
    | true =>
      simp only [hCite, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAdmit
      cases hLog : checkLogicInterface newPart.toLogicFamilySpec downstreamReceiver 0 minNoiseMarginMv with
      | false => simp [hLog] at hAdmit
      | true =>
        have hLogS := checkLogicInterface_guarantees_valid_thresholds _ _ 0 minNoiseMarginMv hLog
        unfold checkDatasheetCite256Fresh at hCite; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCite
        exact ⟨Obend.Vault.judge_admits (k := .write) hV, hCite.2, by have := hLogS.1; omega, hLogS.2.1⟩
def projectEdaPartToCoreData (p : EdaVaultPart) : Obend.Core.Data.Data :=
  .variant "hardwareSchematic" (.record
    [("page_name", .label p.pageName), ("voh_min_mv", .natural p.vohMinMv), ("vih_min_mv", .natural p.vihMinMv),
     ("vol_max_mv", .natural p.volMaxMv), ("vil_max_mv", .natural p.vilMaxMv), ("pkg_width_um", .natural p.pkgWidthUm),
     ("pkg_length_um", .natural p.pkgLengthUm), ("pin_count", .natural p.pinCount), ("pin_pitch_um", .natural p.pinPitchUm),
     ("max_temp_mc", .natural p.maxTempMc), ("vswr_milli", .natural p.vswrMilli), ("drc_errors", .natural p.drcErrors),
     ("cost_cents", .natural p.costCents)])
def decodeEdaPartFromCoreData : Obend.Core.Data.Data → Option EdaVaultPart
  | .variant _ (.record [(_, .label pn), (_, .natural a), (_, .natural b), (_, .natural c), (_, .natural d),
      (_, .natural e), (_, .natural f), (_, .natural g), (_, .natural h), (_, .natural i), (_, .natural j),
      (_, .natural k), (_, .natural l)]) => some ⟨pn, a, b, c, d, e, f, g, h, i, j, k, l⟩
  | _ => none
theorem decode_project_edaPart_coreData_roundtrip (p : EdaVaultPart) :
    decodeEdaPartFromCoreData (projectEdaPartToCoreData p) = some p := by cases p; rfl
private def fieldConflictTag {α : Type} [DecidableEq α] (fn : String) (b l r : α) : List String :=
  match Obend.Doc.mergeCell3 b l r with | .merged _ => [] | .conflict _ _ _ => [fn]
private def mergeFieldVal3 {α : Type} [DecidableEq α] (b l r : α) : α :=
  match Obend.Doc.mergeCell3 b l r with | .merged v => v | .conflict _ _ _ => b
def edaBoardConflictFields (base left right : EdaVaultPart) : List String :=
  fieldConflictTag "page_name" base.pageName left.pageName right.pageName ++
  fieldConflictTag "voh_min_mv" base.vohMinMv left.vohMinMv right.vohMinMv ++ fieldConflictTag "vih_min_mv" base.vihMinMv left.vihMinMv right.vihMinMv ++
  fieldConflictTag "vol_max_mv" base.volMaxMv left.volMaxMv right.volMaxMv ++ fieldConflictTag "vil_max_mv" base.vilMaxMv left.vilMaxMv right.vilMaxMv ++
  fieldConflictTag "pkg_width_um" base.pkgWidthUm left.pkgWidthUm right.pkgWidthUm ++ fieldConflictTag "pkg_length_um" base.pkgLengthUm left.pkgLengthUm right.pkgLengthUm ++
  fieldConflictTag "pin_count" base.pinCount left.pinCount right.pinCount ++ fieldConflictTag "pin_pitch_um" base.pinPitchUm left.pinPitchUm right.pinPitchUm ++
  fieldConflictTag "max_temp_mc" base.maxTempMc left.maxTempMc right.maxTempMc ++ fieldConflictTag "vswr_milli" base.vswrMilli left.vswrMilli right.vswrMilli ++
  fieldConflictTag "drc_errors" base.drcErrors left.drcErrors right.drcErrors ++ fieldConflictTag "cost_cents" base.costCents left.costCents right.costCents
def mergeEdaPartFields3 (base left right : EdaVaultPart) : EdaVaultPart :=
  ⟨mergeFieldVal3 base.pageName left.pageName right.pageName, mergeFieldVal3 base.vohMinMv left.vohMinMv right.vohMinMv,
   mergeFieldVal3 base.vihMinMv left.vihMinMv right.vihMinMv, mergeFieldVal3 base.volMaxMv left.volMaxMv right.volMaxMv,
   mergeFieldVal3 base.vilMaxMv left.vilMaxMv right.vilMaxMv, mergeFieldVal3 base.pkgWidthUm left.pkgWidthUm right.pkgWidthUm,
   mergeFieldVal3 base.pkgLengthUm left.pkgLengthUm right.pkgLengthUm, mergeFieldVal3 base.pinCount left.pinCount right.pinCount,
   mergeFieldVal3 base.pinPitchUm left.pinPitchUm right.pinPitchUm, mergeFieldVal3 base.maxTempMc left.maxTempMc right.maxTempMc,
   mergeFieldVal3 base.vswrMilli left.vswrMilli right.vswrMilli, mergeFieldVal3 base.drcErrors left.drcErrors right.drcErrors,
   mergeFieldVal3 base.costCents left.costCents right.costCents⟩
structure MultiAgentBoardMergeProposal where
  laws               : List (String × LawExpr)
  baseBoard          : EdaVaultPart
  powerAgentBoard    : EdaVaultPart
  rfLayoutAgentBoard : EdaVaultPart
  downstreamReceiver : LogicFamilySpec := lvcmos33ReceiverSpec
  minNoiseMarginMv   : Int := 400
  citePin            : DatasheetCitePin := defaultDatasheetCite256
  agentName          : String := "multi_agent_codesign"
  facts              : Facts := defaultEdaFacts
  deriving DecidableEq, Repr
def mergeAndJudgeAgenticEdaBoard (prop : MultiAgentBoardMergeProposal) : AgenticEdaVerdict :=
  if !(edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard).isEmpty then
    .refusedByPhysics "concurrent-field-merge-conflict"
  else
    judgeAgenticEdaProposal prop.laws prop.baseBoard
      (mergeEdaPartFields3 prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard)
      prop.downstreamReceiver prop.minNoiseMarginMv prop.citePin prop.agentName prop.facts
theorem mergeAndJudgeAgenticEdaBoard_sound (prop : MultiAgentBoardMergeProposal)
    (hAdmit : mergeAndJudgeAgenticEdaBoard prop = .admitted) :
    let mergedBoard := mergeEdaPartFields3 prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard
    let baseData := stateOf edaStateKeys prop.baseBoard.toScalarFields
    let mergedData := stateOf edaStateKeys mergedBoard.toScalarFields
    edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard = [] ∧
    (∀ p ∈ prop.laws, p.2.denote prop.facts (some baseData) mergedData = true) ∧
    prop.citePin.pinnedDigest256 = prop.citePin.currentDigest256 ∧
    prop.downstreamReceiver.vihMinMv + prop.minNoiseMarginMv ≤ mergedBoard.toLogicFamilySpec.vohMinMv ∧
    mergedBoard.toLogicFamilySpec.volMaxMv + prop.minNoiseMarginMv ≤ prop.downstreamReceiver.vilMaxMv := by
  unfold mergeAndJudgeAgenticEdaBoard at hAdmit
  cases hE : (edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard).isEmpty with
  | false => simp [hE] at hAdmit
  | true =>
    simp only [hE, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAdmit
    exact ⟨List.isEmpty_iff.1 hE, agenticEdaProposal_admits_sound prop.laws prop.baseBoard _
      prop.downstreamReceiver prop.minNoiseMarginMv prop.citePin prop.agentName prop.facts hAdmit⟩
theorem conflictingAgentBoardEdits_refused (prop : MultiAgentBoardMergeProposal)
    (hConflict : edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard ≠ []) :
    mergeAndJudgeAgenticEdaBoard prop = .refusedByPhysics "concurrent-field-merge-conflict" ∧
    mergeAndJudgeAgenticEdaBoard prop ≠ .admitted := by
  have hNE : (edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard).isEmpty = false := by
    cases hE : (edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard).isEmpty
    · rfl
    · exact absurd (List.isEmpty_iff.1 hE) hConflict
  have hV : mergeAndJudgeAgenticEdaBoard prop = .refusedByPhysics "concurrent-field-merge-conflict" := by
    unfold mergeAndJudgeAgenticEdaBoard; rw [hNE]; rfl
  exact ⟨hV, by rw [hV]; intro h; cases h⟩
private theorem fieldConflictTag_comm {α : Type} [DecidableEq α] (fn : String) (b l r : α) :
    fieldConflictTag fn b l r = fieldConflictTag fn b r l := by
  unfold fieldConflictTag Obend.Doc.mergeCell3; by_cases h1 : l = r <;> by_cases h2 : l = b <;> by_cases h3 : r = b <;> simp_all [Ne.symm]
private theorem mergeFieldVal3_comm {α : Type} [DecidableEq α] (b l r : α) :
    mergeFieldVal3 b l r = mergeFieldVal3 b r l := by
  unfold mergeFieldVal3 Obend.Doc.mergeCell3; by_cases h1 : l = r <;> by_cases h2 : l = b <;> by_cases h3 : r = b <;> simp_all [Ne.symm]
theorem mergeAndJudgeAgenticEdaBoard_commutative (prop : MultiAgentBoardMergeProposal) :
    mergeAndJudgeAgenticEdaBoard { prop with powerAgentBoard := prop.rfLayoutAgentBoard, rfLayoutAgentBoard := prop.powerAgentBoard } =
    mergeAndJudgeAgenticEdaBoard prop := by
  have hC : edaBoardConflictFields prop.baseBoard prop.rfLayoutAgentBoard prop.powerAgentBoard =
      edaBoardConflictFields prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard := by
    simp only [edaBoardConflictFields]
    rw [fieldConflictTag_comm "page_name", fieldConflictTag_comm "voh_min_mv", fieldConflictTag_comm "vih_min_mv",
        fieldConflictTag_comm "vol_max_mv", fieldConflictTag_comm "vil_max_mv", fieldConflictTag_comm "pkg_width_um",
        fieldConflictTag_comm "pkg_length_um", fieldConflictTag_comm "pin_count", fieldConflictTag_comm "pin_pitch_um",
        fieldConflictTag_comm "max_temp_mc", fieldConflictTag_comm "vswr_milli", fieldConflictTag_comm "drc_errors", fieldConflictTag_comm "cost_cents"]
  have hM : mergeEdaPartFields3 prop.baseBoard prop.rfLayoutAgentBoard prop.powerAgentBoard =
      mergeEdaPartFields3 prop.baseBoard prop.powerAgentBoard prop.rfLayoutAgentBoard := by
    simp only [mergeEdaPartFields3]
    rw [mergeFieldVal3_comm prop.baseBoard.pageName, mergeFieldVal3_comm prop.baseBoard.vohMinMv, mergeFieldVal3_comm prop.baseBoard.vihMinMv,
        mergeFieldVal3_comm prop.baseBoard.volMaxMv, mergeFieldVal3_comm prop.baseBoard.vilMaxMv, mergeFieldVal3_comm prop.baseBoard.pkgWidthUm,
        mergeFieldVal3_comm prop.baseBoard.pkgLengthUm, mergeFieldVal3_comm prop.baseBoard.pinCount, mergeFieldVal3_comm prop.baseBoard.pinPitchUm,
        mergeFieldVal3_comm prop.baseBoard.maxTempMc, mergeFieldVal3_comm prop.baseBoard.vswrMilli, mergeFieldVal3_comm prop.baseBoard.drcErrors,
        mergeFieldVal3_comm prop.baseBoard.costCents]
  unfold mergeAndJudgeAgenticEdaBoard; simp only [hC, hM]

/-- Commit the 12 scalar fields of an `EdaVaultPart` as a `Receipt.Merkle` value list. -/
def edaBoardScalarValues (p : EdaVaultPart) : List Nat :=
  (p.toScalarFields).map Prod.snd

/-- Compute the Merkle leaf digests (`Obend.Receipt.Merkle.leaves`) of an `EdaVaultPart`'s scalar fields. -/
def edaBoardMerkleLeaves (H : Obend.Digest.HashBytes.Hash) (p : EdaVaultPart) : List Nat :=
  Obend.Receipt.Merkle.leaves H (edaBoardScalarValues p)

/-- Compute the Merkle root (`Obend.Receipt.Merkle.mapRoot`) of an `EdaVaultPart`'s scalar fields. -/
def commitEdaBoardMerkleRoot (H : Obend.Digest.HashBytes.Hash) (p : EdaVaultPart) : Nat :=
  Obend.Receipt.Merkle.mapRoot H (edaBoardScalarValues p)

/-- Construct a `MerkleBatchProof` opening a list of scalar field indices `fieldIndices`
against the committed board root `commitEdaBoardMerkleRoot H p`. -/
def buildEdaBoardBatchProof
    (H : Obend.Digest.HashBytes.Hash) (p : EdaVaultPart) (fieldIndices : List Nat) :
    Obend.Receipt.Merkle.MerkleBatchProof :=
  Obend.Receipt.Merkle.honestBatchProof H (edaBoardMerkleLeaves H p) fieldIndices

/-- Soundness and completeness of EDA board Merkle batch receipts. -/
theorem buildEdaBoardBatchProof_verifies
    {H : Obend.Digest.HashBytes.Hash} (hb : Obend.Receipt.Merkle.Bounded H)
    (p : EdaVaultPart) (fieldIndices : List Nat)
    (hNodup : fieldIndices.Nodup)
    (hBounds : ∀ i ∈ fieldIndices, i < 12) :
    Obend.Receipt.Merkle.verifyMerkleBatchProof H
      (buildEdaBoardBatchProof H p fieldIndices)
      (commitEdaBoardMerkleRoot H p) = true := by
  have hLen : (edaBoardMerkleLeaves H p).length = 12 := by
    simp [edaBoardMerkleLeaves, Obend.Receipt.Merkle.leaves_length,
      edaBoardScalarValues, EdaVaultPart.toScalarFields]
  have hSmall : ∀ x ∈ edaBoardMerkleLeaves H p, x < 2 ^ 256 :=
    Obend.Receipt.Merkle.leaves_small hb (edaBoardScalarValues p)
  have hLenSmall : (edaBoardMerkleLeaves H p).length < 2 ^ 256 := by
    rw [hLen]; decide
  exact Obend.Receipt.Merkle.verifyMerkleBatchProof_honest hb
    (edaBoardMerkleLeaves H p) hSmall hLenSmall fieldIndices hNodup
    (fun i hi => by rw [hLen]; exact hBounds i hi)

/-- Deployed cSHAKE256 instantiation of `buildEdaBoardBatchProof_verifies`. -/
theorem deployed_edaBoardBatchProof_verifies
    (p : EdaVaultPart) (fieldIndices : List Nat)
    (hNodup : fieldIndices.Nodup)
    (hBounds : ∀ i ∈ fieldIndices, i < 12) :
    Obend.Receipt.Merkle.verifyMerkleBatchProof Obend.Core.Digest.deployed
      (buildEdaBoardBatchProof Obend.Core.Digest.deployed p fieldIndices)
      (commitEdaBoardMerkleRoot Obend.Core.Digest.deployed p) = true :=
  buildEdaBoardBatchProof_verifies Obend.Receipt.Merkle.deployed_bounded p fieldIndices hNodup hBounds

/-! ## 4. Non-Tautological `pinoutEquivJudge` & Multi-Turn Revision Trace -/
structure PinoutSwapObj where
  laws        : List (String × LawExpr)
  oldPart     : EdaVaultPart
  newPart     : EdaVaultPart
  pkgA        : FootprintPackageSpec
  pkgB        : FootprintPackageSpec
  minMarginMv : Int
  padTolNm    : Nat
  cite256     : DatasheetCite256
  agentName   : String
  facts       : Facts
  deriving DecidableEq, Repr
structure PinoutSwapCert where
  transform : D4Transform
  pinMap    : Array Nat
  deriving DecidableEq, Repr
inductive PinoutSwapClause where
  | pinCountMismatch | staleDatasheetDigest | vaultLawRefused (lawName reason : String)
  | vaultLawUndecided (why : String) | invalidPinoutWitness
  deriving DecidableEq, Repr
def PinoutSwapMeaning (o : PinoutSwapObj) (c : PinoutSwapCert) : Prop :=
  let oldData := stateOf edaStateKeys o.oldPart.toScalarFields
  let newData := stateOf edaStateKeys o.newPart.toScalarFields
  o.pkgA.pins.size = o.pkgB.pins.size ∧
  o.cite256.currentDigest256 ≠ 0#256 ∧ o.cite256.pinnedDigest256 = o.cite256.currentDigest256 ∧
  (∀ p ∈ o.laws, p.2.denote o.facts (some oldData) newData = true) ∧
  courtyardFits c.transform o.pkgA o.pkgB ∧ c.pinMap.size = o.pkgA.pins.size ∧
  IsBijectionOn o.pkgA.pins.size (fun i => c.pinMap.getD i o.pkgA.pins.size) ∧
  ∀ (i : Nat) (hi : i < o.pkgA.pins.size) (hpi : c.pinMap.getD i o.pkgA.pins.size < o.pkgB.pins.size),
    checkPinPairCompat o.minMarginMv o.padTolNm c.transform o.pkgA.pins[i] o.pkgB.pins[c.pinMap.getD i o.pkgA.pins.size] = true
theorem pinoutSwapMeaning_implies_dropInEquiv (o : PinoutSwapObj) (c : PinoutSwapCert)
    (hm : PinoutSwapMeaning o c) : PinoutDropInEquiv o.minMarginMv o.padTolNm o.pkgA o.pkgB :=
  ⟨c.transform, fun i => c.pinMap.getD i o.pkgA.pins.size, hm.2.2.2.2.1, hm.1, hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2⟩
def checkPinoutSwap (_grade : Nat) (o : PinoutSwapObj) (c : PinoutSwapCert) :
    Obend.Judge.Verdict PinoutSwapClause :=
  if o.pkgA.pins.size != o.pkgB.pins.size then .refused .pinCountMismatch []
  else if !checkDatasheetCite256Fresh o.cite256 then .refused .staleDatasheetDigest []
  else if o.laws.isEmpty then
    if verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap then .ok
    else .refused .invalidPinoutWitness []
  else
    match Obend.Vault.judge (stateTy edaStateKeys) o.newPart.pageName o.laws
        (stateOf edaStateKeys o.oldPart.toScalarFields) (stateOf edaStateKeys o.newPart.toScalarFields)
        (requestOf o.agentName .write o.facts) with
    | .refused lawName reason => .refused (.vaultLawRefused lawName reason) []
    | .undecided why => .refused (.vaultLawUndecided why) []
    | .admitted =>
      if verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap then .ok
      else .refused .invalidPinoutWitness []
def PinoutSwapFragment (o : PinoutSwapObj) : Prop := o.laws = []
instance pinoutEquivJudge : Obend.Judge PinoutSwapObj PinoutSwapCert where
  Clause := PinoutSwapClause
  Meaning := PinoutSwapMeaning
  check := checkPinoutSwap
  sound := by
    intro r o c hOk; unfold checkPinoutSwap at hOk
    by_cases hSz : o.pkgA.pins.size ≠ o.pkgB.pins.size
    · simp [hSz] at hOk
    · have hSzEq : o.pkgA.pins.size = o.pkgB.pins.size := by omega
      simp only [hSzEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hCite : checkDatasheetCite256Fresh o.cite256 with
      | false => simp [hCite] at hOk
      | true =>
        simp only [hCite, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        unfold checkDatasheetCite256Fresh at hCite; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCite
        cases hEmpty : o.laws.isEmpty with
        | true =>
          simp only [hEmpty, ↓reduceIte] at hOk
          cases hVer : verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap with
          | false => simp [hVer] at hOk
          | true =>
            have hV := (verifyPinoutBijection_iff _ _ _ _ _ _).mp hVer; have hNil := List.isEmpty_iff.mp hEmpty
            exact ⟨hSzEq, hCite.1, hCite.2, (fun p hp => by rw [hNil] at hp; cases hp), hV.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2⟩
        | false =>
          simp only [hEmpty, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hJ : Obend.Vault.judge (stateTy edaStateKeys) o.newPart.pageName o.laws
              (stateOf edaStateKeys o.oldPart.toScalarFields) (stateOf edaStateKeys o.newPart.toScalarFields)
              (requestOf o.agentName .write o.facts) with
          | refused _ _ => rw [hJ] at hOk; cases hOk
          | undecided _ => rw [hJ] at hOk; cases hOk
          | admitted =>
            rw [hJ] at hOk
            cases hVer : verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap with
            | false => simp [hVer] at hOk
            | true =>
              have hV := (verifyPinoutBijection_iff _ _ _ _ _ _).mp hVer
              exact ⟨hSzEq, hCite.1, hCite.2, Obend.Vault.judge_admits (k := .write) hJ, hV.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2⟩
  refutes | .pinCountMismatch | .staleDatasheetDigest | .vaultLawRefused _ _ => true | .vaultLawUndecided _ | .invalidPinoutWitness => false
  refuted := by
    intro r o c k p hRef hIsRef c' hm; unfold checkPinoutSwap at hRef
    by_cases hSz : o.pkgA.pins.size ≠ o.pkgB.pins.size
    · exact hSz hm.1
    · have hSzEq : o.pkgA.pins.size = o.pkgB.pins.size := by omega
      simp only [hSzEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hRef
      cases hCite : checkDatasheetCite256Fresh o.cite256 with
      | false => unfold checkDatasheetCite256Fresh at hCite; simp [hm.2.1, hm.2.2.1] at hCite
      | true =>
        simp only [hCite, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
        cases hEmpty : o.laws.isEmpty with
        | true =>
          simp only [hEmpty, ↓reduceIte] at hRef
          cases hVer : verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap <;>
            simp only [hVer, ↓reduceIte, Bool.false_eq_true] at hRef <;> (cases hRef; try cases hIsRef)
        | false =>
          simp only [hEmpty, Bool.false_eq_true, ↓reduceIte] at hRef
          cases hJ : Obend.Vault.judge (stateTy edaStateKeys) o.newPart.pageName o.laws
              (stateOf edaStateKeys o.oldPart.toScalarFields) (stateOf edaStateKeys o.newPart.toScalarFields)
              (requestOf o.agentName .write o.facts) with
          | refused lawName reason =>
            obtain ⟨e, hMem, hF⟩ := Obend.Vault.judge_refuses (k := .write) hJ
            have hT := hm.2.2.2.1 (lawName, e) hMem
            change LawExpr.denote o.facts (some (stateOf edaStateKeys o.oldPart.toScalarFields))
              (stateOf edaStateKeys o.newPart.toScalarFields) e = false at hF
            change LawExpr.denote o.facts (some (stateOf edaStateKeys o.oldPart.toScalarFields))
              (stateOf edaStateKeys o.newPart.toScalarFields) e = true at hT
            rw [hF] at hT; cases hT
          | undecided _ => rw [hJ] at hRef; cases hRef; cases hIsRef
          | admitted =>
            rw [hJ] at hRef
            cases hVer : verifyPinoutBijection o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap <;>
              simp only [hVer, ↓reduceIte, Bool.false_eq_true] at hRef <;> (cases hRef; try cases hIsRef)
  Fragment := PinoutSwapFragment
  complete := by
    intro o hFrag ⟨c, hm⟩; refine ⟨c, 0, ?_⟩; unfold checkPinoutSwap
    have hCite : checkDatasheetCite256Fresh o.cite256 = true := by unfold checkDatasheetCite256Fresh; simp [hm.2.1, hm.2.2.1]
    have hVer := (verifyPinoutBijection_iff o.minMarginMv o.padTolNm c.transform o.pkgA o.pkgB c.pinMap).mpr
      ⟨hm.2.2.2.2.1, hm.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2⟩
    simp [hm.1, hCite, List.isEmpty_iff.mpr hFrag, hVer]
  mono := by intro _ _ _ _ _ _; rfl
theorem pinoutEquivJudge_fragment_inhabited (pkg : FootprintPackageSpec) :
    ∃ o : PinoutSwapObj, PinoutSwapFragment o ∧ o.pkgA = pkg :=
  ⟨⟨[], baselineLdoPart, secondSourceLdoPart, pkg, pkg, 400, 1000, defaultDatasheetCite256, "scout", defaultEdaFacts⟩, rfl, rfl⟩
structure PinoutRevisionState where
  curPart        : EdaVaultPart
  curPkg         : FootprintPackageSpec
  curDigest256   : BitVec 256
  revCount       : Nat
  revokedDigests : List (BitVec 256)
  deriving DecidableEq, Repr
structure PinoutRevisionTurn where
  nextPart       : EdaVaultPart
  nextPkg        : FootprintPackageSpec
  newCite256     : DatasheetCite256
  minMarginMv    : Int
  padTolNm       : Nat
  laws           : List (String × LawExpr)
  agentName      : String
  facts          : Facts
  revokePrevious : Bool
  deriving DecidableEq, Repr
private def checkTurnLawsOk (st : PinoutRevisionState) (t : PinoutRevisionTurn) : Bool :=
  if t.laws.isEmpty then true
  else Obend.Vault.judge (stateTy edaStateKeys) t.nextPart.pageName t.laws
      (stateOf edaStateKeys st.curPart.toScalarFields) (stateOf edaStateKeys t.nextPart.toScalarFields)
      (requestOf t.agentName .write t.facts) == .admitted
def stepPinoutRevision (st : PinoutRevisionState) (t : PinoutRevisionTurn) : Option PinoutRevisionState :=
  if checkDatasheetCite256Fresh t.newCite256 && !(st.revokedDigests.contains t.newCite256.currentDigest256) &&
     checkPinoutIso t.minMarginMv t.padTolNm st.curPkg t.nextPkg && checkTurnLawsOk st t then
    some ⟨t.nextPart, t.nextPkg, t.newCite256.currentDigest256, st.revCount + 1,
      if t.revokePrevious then st.curDigest256 :: st.revokedDigests else st.revokedDigests⟩
  else none
def runPinoutRevisionTrace (st : PinoutRevisionState) : List PinoutRevisionTurn → Option PinoutRevisionState
  | [] => some st
  | t :: ts => match stepPinoutRevision st t with | some st' => runPinoutRevisionTrace st' ts | none => none
inductive ValidPinoutTrace : PinoutRevisionState → List PinoutRevisionTurn → PinoutRevisionState → Prop where
  | nil (st : PinoutRevisionState) : ValidPinoutTrace st [] st
  | cons {st st1 st2 : PinoutRevisionState} {t : PinoutRevisionTurn} {ts : List PinoutRevisionTurn} :
      t.newCite256.currentDigest256 ≠ 0#256 →
      t.newCite256.pinnedDigest256 = t.newCite256.currentDigest256 →
      t.newCite256.currentDigest256 ∉ st.revokedDigests →
      PinoutDropInEquiv t.minMarginMv t.padTolNm st.curPkg t.nextPkg →
      (∀ p ∈ t.laws, p.2.denote t.facts (some (stateOf edaStateKeys st.curPart.toScalarFields))
        (stateOf edaStateKeys t.nextPart.toScalarFields) = true) →
      st1 = ⟨t.nextPart, t.nextPkg, t.newCite256.currentDigest256, st.revCount + 1,
        if t.revokePrevious then st.curDigest256 :: st.revokedDigests else st.revokedDigests⟩ →
      ValidPinoutTrace st1 ts st2 → ValidPinoutTrace st (t :: ts) st2
theorem validPinoutTrace_inhabited (st : PinoutRevisionState) : ValidPinoutTrace st [] st := .nil st
theorem runPinoutRevisionTrace_inhabited (st : PinoutRevisionState) : runPinoutRevisionTrace st [] = some st := by
  unfold runPinoutRevisionTrace; rfl
theorem runPinoutRevisionTrace_sound (st st' : PinoutRevisionState)
    (turns : List PinoutRevisionTurn) (hRun : runPinoutRevisionTrace st turns = some st') :
    ValidPinoutTrace st turns st' ∧ st'.revCount = st.revCount + turns.length ∧
    st'.curPkg.pins.size = st.curPkg.pins.size ∧ ∀ d, d ∈ st.revokedDigests → d ∈ st'.revokedDigests := by
  induction turns generalizing st with
  | nil => unfold runPinoutRevisionTrace at hRun; cases hRun; exact ⟨.nil st', by simp, rfl, fun _ h => h⟩
  | cons t ts ih =>
    unfold runPinoutRevisionTrace at hRun
    cases hStep : stepPinoutRevision st t with
    | none => rw [hStep] at hRun; cases hRun
    | some st1 =>
      rw [hStep] at hRun; unfold stepPinoutRevision at hStep; split at hStep
      · rename_i hCond; cases hStep; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hCond
        obtain ⟨⟨⟨hCite, hNotRevB⟩, hIso⟩, hLawsOk⟩ := hCond
        have hNotRev : t.newCite256.currentDigest256 ∉ st.revokedDigests := fun hM => by
          rw [List.contains_iff_mem.mpr hM] at hNotRevB; cases hNotRevB
        unfold checkDatasheetCite256Fresh at hCite; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCite
        have hEquiv := (checkPinoutIso_iff t.minMarginMv t.padTolNm st.curPkg t.nextPkg).mp hIso
        have hPinEq : t.nextPkg.pins.size = st.curPkg.pins.size := by obtain ⟨_, _, _, hSz, _, _⟩ := hEquiv; exact hSz.symm
        have hLawsDenote : ∀ p ∈ t.laws, p.2.denote t.facts (some (stateOf edaStateKeys st.curPart.toScalarFields))
            (stateOf edaStateKeys t.nextPart.toScalarFields) = true := by
          unfold checkTurnLawsOk at hLawsOk
          cases hEmp : t.laws.isEmpty with
          | true => intro p hp; rw [List.isEmpty_iff.mp hEmp] at hp; cases hp
          | false => simp only [hEmp, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hLawsOk; exact Obend.Vault.judge_admits (k := .write) hLawsOk
        obtain ⟨hTV, hTC, hTP, hTR⟩ := ih _ hRun
        refine ⟨.cons hCite.1 hCite.2 hNotRev hEquiv hLawsDenote rfl hTV,
          by simp only [List.length_cons] at *; omega, by rw [hTP]; exact hPinEq, fun d hd => ?_⟩
        apply hTR d; cases t.revokePrevious <;> simp [hd]
      · cases hStep
theorem skip_implies_contract_violation (st : PinoutRevisionState) (t : PinoutRevisionTurn)
    (hSkip : stepPinoutRevision st t = none) :
    ¬ (t.newCite256.currentDigest256 ≠ 0#256 ∧ t.newCite256.pinnedDigest256 = t.newCite256.currentDigest256) ∨
    t.newCite256.currentDigest256 ∈ st.revokedDigests ∨
    ¬ PinoutDropInEquiv t.minMarginMv t.padTolNm st.curPkg t.nextPkg ∨
    (t.laws ≠ [] ∧
      Obend.Vault.judge (stateTy edaStateKeys) t.nextPart.pageName t.laws
        (stateOf edaStateKeys st.curPart.toScalarFields) (stateOf edaStateKeys t.nextPart.toScalarFields)
        (requestOf t.agentName .write t.facts) ≠ .admitted) := by
  unfold stepPinoutRevision at hSkip; split at hSkip
  · cases hSkip
  · rename_i hNot
    by_cases hCite : checkDatasheetCite256Fresh t.newCite256 = true
    · by_cases hRev : st.revokedDigests.contains t.newCite256.currentDigest256 = true
      · exact Or.inr (Or.inl (List.contains_iff_mem.mp hRev))
      · have hRevF : st.revokedDigests.contains t.newCite256.currentDigest256 = false := Bool.eq_false_iff.mpr hRev
        by_cases hIso : checkPinoutIso t.minMarginMv t.padTolNm st.curPkg t.nextPkg = true
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hLawsF : checkTurnLawsOk st t = false := by
            cases hL : checkTurnLawsOk st t with
            | false => rfl
            | true => exfalso; exact hNot (by rw [hCite, hRevF, hIso, hL]; rfl)
          unfold checkTurnLawsOk at hLawsF
          cases hEmp : t.laws.isEmpty with
          | true => simp [hEmp] at hLawsF
          | false =>
            simp only [hEmp, Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne] at hLawsF
            exact ⟨(fun hNil => by rw [hNil] at hEmp; cases hEmp), hLawsF⟩
        · exact Or.inr (Or.inr (Or.inl fun hEq => hIso ((checkPinoutIso_iff _ _ _ _).mpr hEq)))
    · exact Or.inl (fun ⟨hNz, hEq⟩ => hCite (by unfold checkDatasheetCite256Fresh; simp [hNz, hEq]))

end Obend.Hardware.PinoutEquiv
end

namespace Obend.Hardware.PinoutEquiv
private def samplePkgA : FootprintPackageSpec :=
  ⟨"QFN4_BASE", 2000000, 3000000,
    #[⟨1, "VDD", .powerIn 3300 3000 3600, ⟨-500000, -500000, 300000, 500000, 50000⟩⟩,
      ⟨2, "GND", .gnd, ⟨500000, -500000, 300000, 500000, 50000⟩⟩,
      ⟨3, "DP", .diffPos 1, ⟨500000, 500000, 300000, 500000, 50000⟩⟩,
      ⟨4, "DN", .diffNeg 1, ⟨-500000, 500000, 300000, 500000, 50000⟩⟩]⟩
private def samplePkgB_rot90 : FootprintPackageSpec :=
  ⟨"QFN4_ALT90", 3000000, 2000000,
    #[⟨10, "DN_B", .diffNeg 1, ⟨-500000, -500000, 500000, 300000, 50000⟩⟩,
      ⟨11, "VDD_B", .powerIn 3300 2900 3700, ⟨500000, -500000, 500000, 300000, 50000⟩⟩,
      ⟨12, "GND_B", .gnd, ⟨500000, 500000, 500000, 300000, 50000⟩⟩,
      ⟨13, "DP_B", .diffPos 1, ⟨-500000, 500000, 500000, 300000, 50000⟩⟩]⟩
private def samplePkgB_badDiff : FootprintPackageSpec :=
  { samplePkgB_rot90 with pins := samplePkgB_rot90.pins.set! 3 ⟨13, "DP_BAD", .diffPos 2, ⟨-500000, 500000, 500000, 300000, 50000⟩⟩ }
example : PinoutDropInEquiv 400 10000 samplePkgA samplePkgB_rot90 :=
  (checkPinoutIso_iff 400 10000 samplePkgA samplePkgB_rot90).mp (by decide)
example : ¬ PinoutDropInEquiv 400 10000 samplePkgA samplePkgB_badDiff := by
  intro h; have hT := (checkPinoutIso_iff 400 10000 samplePkgA samplePkgB_badDiff).mpr h
  have hF : checkPinoutIso 400 10000 samplePkgA samplePkgB_badDiff = false := by decide
  rw [hF] at hT; cases hT
example : (∃ k, pinoutEquivJudge.refutes k = true) ∧ (∃ k, pinoutEquivJudge.refutes k = false) :=
  ⟨⟨.pinCountMismatch, rfl⟩, ⟨.invalidPinoutWitness, rfl⟩⟩
end Obend.Hardware.PinoutEquiv
