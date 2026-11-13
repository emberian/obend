module
/-
# Obend.Trailblaze.ClusterGov — Organ O6: Wrap-Free Modular Dot Products, Exact Integer-Sliced Collectives & Physical Compute Envelopes

Concrete executable Silver/Gold spine and kernel-checked algebraic, relational, and physical
conservation theorems for Organ O6 (`ClusterGov` — Verifiable AI Cluster Governance):

1. **Wrap-Free Integer Dot-Product / Linear Layer Envelope (`koalaBearPrime`) + `Array Int` `Exec` Fast Path**:
   Defines `IntTensorBound`, `checkSableNoWrap` (`2 * dim * maxAbsWeight * maxAbsAct < modulusP`),
   `intDot`, `intDotExec` (`Array Int` tight index loop), `embedModP`, and `decodeSignedModP`.
   Proves unconditionally (`intDotExec_eq_intDot`, `sable_dot_exact_no_wrap`,
   `embedModP_injective_of_no_wrap`) that `Exec` refines `Spec` and bounded integer dot products
   reconstruct modulo `p` with zero wraparound error.
2. **Bit-Exact Integer-Sliced Collectives (`Ozaki`), `Array` `Exec` Fast Path & `HyperLaw2` Non-Interference**:
   Defines fixed-radix integer slice vectors (`sliceVecAdd`, `ozakiSliceSum`) alongside unboxed
   `Array Int` fast paths (`sliceVecAddExec`, `ozakiSliceSumExec`) with proved `Spec ↔ Exec`
   refinement (`ozakiSliceSumExec_eq_ozakiSliceSum`), worker-permutation invariance
   (`ozakiSliceSum_perm`), arbitrary binary AllReduce tree re-association invariance
   (`ozaki_tree_schedule_invariant`), and `HyperLaw2NonInterference` covert-channel closure
   (`ozaki_closes_schedule_covert_channel`).
3. **Lineage (`AriadneStep`), Authority-Pinned RTT & Lower-Curve Energy Conservation (`PhysicalEnergyEnvelope`)**:
   Audits weight/batch Merkle lineage, compute caps, authority-pinned round-trip latency, and
   metered lower-curve energy conservation (`energy_conservation_bounds_hidden_ops`), bounding
   unproved shadow FLOPs with `0` `Classical.choice` and `0` tautological Stage-A obligations.
-/
public import Obend.Run.HyperLaw
public import Obend.Reasons

public section
namespace Obend.Trailblaze.ClusterGov

open Obend.Run.HyperLaw (LowView HyperLaw2NonInterference checkHyperLaw2NonInterference
  checkHyperLaw2NonInterference_sound checkHyperLaw2Step checkLowEquiv)

set_option autoImplicit false

/-! ## §1. Overflow-Free Integer Dot-Product, `Array Int` `Exec` Fast Path & Centered $\mathbb{F}_p$ Reconstruction -/

/-- KoalaBear 31-bit prime `p = 2^31 - 2^24 + 1` (`2130706433`) for wrap-free integer inference. -/
def koalaBearPrime : Nat := 2130706433

/-- Certified integer dot-product / linear layer envelope over prime field modulus `modulusP`. -/
structure IntTensorBound where
  dim          : Nat
  maxAbsWeight : Nat
  maxAbsAct    : Nat
  modulusP     : Nat
  deriving DecidableEq, Repr

/-- Wrap-freedom guard: `2 * dim * maxAbsWeight * maxAbsAct < modulusP` guarantees
    every signed accumulator `z` lies strictly inside `(-modulusP / 2, modulusP / 2)`. -/
@[expose] def checkSableNoWrap (b : IntTensorBound) : Bool :=
  decide (2 * b.dim * b.maxAbsWeight * b.maxAbsAct < b.modulusP)

/-- Exact integer inner product `∑ᵢ wᵢ xᵢ` (`List Int` specification). -/
def intDot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | w :: ws, x :: xs => w * x + intDot ws xs

/-- Structural index loop for the `Array Int` inner-product `Exec` fast path. -/
def intDotExecLoop (ws xs : Array Int) (idx : Nat) : Nat → Int → Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hw : idx < ws.size then
      if hx : idx < xs.size then
        intDotExecLoop ws xs (idx + 1) rem (acc + ws[idx] * xs[idx])
      else
        acc
    else
      acc
termination_by structural rem => rem

/-- Tight `Array Int` inner-product `Exec` fast path (`O(min |ws| |xs|)` with zero list allocation). -/
def intDotExec (ws xs : Array Int) : Int :=
  intDotExecLoop ws xs 0 (min ws.size xs.size) 0

theorem intDotExecLoop_eq_intDot (ws xs : Array Int) (idx rem : Nat)
    (hRem : idx + rem = min ws.size xs.size) (acc : Int) :
    intDotExecLoop ws xs idx rem acc =
      acc + intDot (ws.toList.drop idx) (xs.toList.drop idx) := by
  induction rem generalizing idx acc with
  | zero =>
    have hMin : min ws.size xs.size = idx := by omega
    unfold intDotExecLoop
    if hW : idx < ws.size then
      have hX : xs.toList.length ≤ idx := by
        rw [Array.length_toList]
        omega
      have hDropX : xs.toList.drop idx = [] := List.drop_eq_nil_of_le hX
      rw [hDropX]
      cases ws.toList.drop idx <;> simp [intDot]
    else
      have hWLe : ws.toList.length ≤ idx := by
        rw [Array.length_toList]
        omega
      have hDropW : ws.toList.drop idx = [] := List.drop_eq_nil_of_le hWLe
      rw [hDropW]
      simp [intDot]
  | succ r ih =>
    have hW : idx < ws.size := by omega
    have hX : idx < xs.size := by omega
    have hWL : idx < ws.toList.length := by rw [Array.length_toList]; exact hW
    have hXL : idx < xs.toList.length := by rw [Array.length_toList]; exact hX
    have hDropW : ws.toList.drop idx = ws[idx] :: ws.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hWL]; rfl
    have hDropX : xs.toList.drop idx = xs[idx] :: xs.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hXL]; rfl
    unfold intDotExecLoop
    simp only [hW, hX, ↓reduceDIte]
    have hNext : (idx + 1) + r = min ws.size xs.size := by omega
    rw [ih (idx + 1) hNext (acc + ws[idx] * xs[idx]), hDropW, hDropX]
    dsimp only [intDot]
    omega

/-- **`Spec ↔ Exec` Dot-Product Equivalence**: `intDotExec ws xs` computes the exact same integer
    inner product as `intDot ws.toList xs.toList`. -/
theorem intDotExec_eq_intDot (ws xs : Array Int) :
    intDotExec ws xs = intDot ws.toList xs.toList := by
  unfold intDotExec
  have h := intDotExecLoop_eq_intDot ws xs 0 (min ws.size xs.size) (Nat.zero_add _) 0
  simpa using h

/-- Canonical residue embedding into `[0, p)` modulo `p`. -/
def embedModP (p : Nat) (z : Int) : Int :=
  z % (p : Int)

/-- Centered signed representative reconstruction from a field residue modulo `p`. -/
def decodeSignedModP (p : Nat) (r : Int) : Int :=
  if decide (2 * (r % (p : Int)) < (p : Int)) then
    r % (p : Int)
  else
    r % (p : Int) - (p : Int)

/-- Declarative L∞ bound on an integer vector. -/
def VecAbsBounded (bound : Nat) (xs : List Int) : Prop :=
  ∀ x ∈ xs, x.natAbs ≤ bound

/-- Executable boolean L∞ bound checker on an integer vector. -/
@[expose] def checkVecAbsBounded (bound : Nat) (xs : List Int) : Bool :=
  xs.all (fun x => decide (x.natAbs ≤ bound))

theorem checkVecAbsBounded_sound {bound : Nat} {xs : List Int}
    (h : checkVecAbsBounded bound xs = true) :
    VecAbsBounded bound xs := by
  intro x hx
  have hAll := List.all_eq_true.mp h x hx
  exact of_decide_eq_true hAll

/-- Cauchy–Schwarz / L1–L∞ accumulator bound: `|∑ᵢ wᵢ xᵢ| ≤ dim * maxW * maxX`. -/
theorem intDot_natAbs_le (ws xs : List Int) (dim maxW maxX : Nat)
    (hLen : ws.length ≤ dim)
    (hW : VecAbsBounded maxW ws)
    (hX : VecAbsBounded maxX xs) :
    (intDot ws xs).natAbs ≤ dim * maxW * maxX := by
  induction ws generalizing xs dim with
  | nil =>
    simp [intDot]
  | cons w wsRest ih =>
    cases xs with
    | nil => simp [intDot]
    | cons x xsRest =>
      cases dim with
      | zero =>
        simp at hLen
      | succ d =>
        have hw : w.natAbs ≤ maxW := hW w (List.mem_cons_self ..)
        have hx : x.natAbs ≤ maxX := hX x (List.mem_cons_self ..)
        have hProd : (w * x).natAbs ≤ maxW * maxX := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul hw hx
        have hTailLen : wsRest.length ≤ d := by
          simp at hLen
          omega
        have hTail : (intDot wsRest xsRest).natAbs ≤ d * maxW * maxX :=
          ih xsRest d hTailLen
            (fun u hu => hW u (List.mem_cons_of_mem _ hu))
            (fun v hv => hX v (List.mem_cons_of_mem _ hv))
        have hTri : (w * x + intDot wsRest xsRest).natAbs ≤
            (w * x).natAbs + (intDot wsRest xsRest).natAbs :=
          Int.natAbs_add_le (w * x) (intDot wsRest xsRest)
        have hStep : (d + 1) * maxW * maxX = maxW * maxX + d * maxW * maxX := by
          rw [Nat.succ_mul, Nat.add_mul, Nat.add_comm]
        dsimp only [intDot]
        omega

/-- **Centered Modular Exactness**: Any integer `z` with `2 * |z| < p` embeds into `ℤ/pℤ` and
    reconstructs via `decodeSignedModP` to `z` with zero wraparound error. -/
theorem decodeSignedModP_embedModP_exact (p : Nat) (z : Int)
    (hNoWrap : 2 * z.natAbs < p) :
    decodeSignedModP p (embedModP p z) = z := by
  unfold decodeSignedModP embedModP
  if hz : 0 ≤ z then
    have hLtP : z < (p : Int) := by omega
    have hMod1 : z % (p : Int) = z := Int.emod_eq_of_lt hz hLtP
    rw [hMod1, hMod1]
    have hTwoLt : 2 * z < (p : Int) := by omega
    have hDec : decide (2 * z < (p : Int)) = true := decide_eq_true hTwoLt
    rw [hDec]
    rfl
  else
    have hPosShift : 0 ≤ z + (p : Int) := by omega
    have hLtShift : z + (p : Int) < (p : Int) := by omega
    have hModNeg : z % (p : Int) = z + (p : Int) := by
      have hAddMod : (z + (p : Int) * 1) % (p : Int) = z % (p : Int) :=
        Int.add_mul_emod_self_left z (p : Int) 1
      rw [Int.mul_one] at hAddMod
      rw [← hAddMod]
      exact Int.emod_eq_of_lt hPosShift hLtShift
    rw [hModNeg, Int.emod_eq_of_lt hPosShift hLtShift]
    have hNotLt : ¬ (2 * (z + (p : Int)) < (p : Int)) := by omega
    have hDecFalse : decide (2 * (z + (p : Int)) < (p : Int)) = false :=
      decide_eq_false hNotLt
    rw [hDecFalse]
    change (z + (p : Int)) - (p : Int) = z
    omega

/-- **Modular Injectivity on the No-Wrap Envelope**: Distinct integers inside `(-p/2, p/2)`
    never collide modulo `p`. -/
theorem embedModP_injective_of_no_wrap {p : Nat} {z₁ z₂ : Int}
    (h₁ : 2 * z₁.natAbs < p) (h₂ : 2 * z₂.natAbs < p)
    (hEq : embedModP p z₁ = embedModP p z₂) :
    z₁ = z₂ := by
  have e₁ := decodeSignedModP_embedModP_exact p z₁ h₁
  have e₂ := decodeSignedModP_embedModP_exact p z₂ h₂
  rw [← e₁, ← e₂, hEq]

/-- **Overflow-Free Dot-Product Exactness Theorem (`sable_dot_exact_no_wrap`)**:
    Whenever `checkSableNoWrap b = true`, every weight vector `ws` and activation vector `xs`
    within `b` satisfies `2 * |⟨ws, xs⟩| < b.modulusP` and exact modular round-trip reconstruction. -/
theorem sable_dot_exact_no_wrap (b : IntTensorBound) (ws xs : List Int)
    (hGuard : checkSableNoWrap b = true)
    (hLen : ws.length ≤ b.dim)
    (hW : VecAbsBounded b.maxAbsWeight ws)
    (hX : VecAbsBounded b.maxAbsAct xs) :
    2 * (intDot ws xs).natAbs < b.modulusP ∧
      decodeSignedModP b.modulusP (embedModP b.modulusP (intDot ws xs)) = intDot ws xs := by
  have hBoundLt : 2 * b.dim * b.maxAbsWeight * b.maxAbsAct < b.modulusP :=
    of_decide_eq_true hGuard
  have hAbsLe : (intDot ws xs).natAbs ≤ b.dim * b.maxAbsWeight * b.maxAbsAct :=
    intDot_natAbs_le ws xs b.dim b.maxAbsWeight b.maxAbsAct hLen hW hX
  have hTwoMul :
      2 * (b.dim * b.maxAbsWeight * b.maxAbsAct) =
        2 * b.dim * b.maxAbsWeight * b.maxAbsAct := by
    simp [Nat.mul_assoc]
  have hStrict : 2 * (intDot ws xs).natAbs < b.modulusP := by
    have hMulLe := Nat.mul_le_mul_left 2 hAbsLe
    omega
  exact ⟨hStrict, decodeSignedModP_embedModP_exact b.modulusP (intDot ws xs) hStrict⟩

/-- `Array Int` `Exec` corollary of `sable_dot_exact_no_wrap`. -/
theorem sable_dotExec_exact_no_wrap (b : IntTensorBound) (ws xs : Array Int)
    (hGuard : checkSableNoWrap b = true)
    (hLen : ws.size ≤ b.dim)
    (hW : VecAbsBounded b.maxAbsWeight ws.toList)
    (hX : VecAbsBounded b.maxAbsAct xs.toList) :
    2 * (intDotExec ws xs).natAbs < b.modulusP ∧
      decodeSignedModP b.modulusP (embedModP b.modulusP (intDotExec ws xs)) =
        intDot ws.toList xs.toList := by
  rw [intDotExec_eq_intDot]
  have hLenList : ws.toList.length ≤ b.dim := by rw [Array.length_toList]; exact hLen
  exact sable_dot_exact_no_wrap b ws.toList xs.toList hGuard hLenList hW hX


/-! ## §2. Bit-Exact Integer-Sliced Collectives (`Ozaki`), `Array` `Exec` Fast Path & `HyperLaw2` -/

/-- Componentwise exact integer addition on fixed-radix mantissa slices (zero-extended). -/
def sliceVecAdd : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: sliceVecAdd xs ys

@[simp] theorem sliceVecAdd_nil_left (ys : List Int) :
    sliceVecAdd [] ys = ys := by
  cases ys <;> rfl

@[simp] theorem sliceVecAdd_nil_right (xs : List Int) :
    sliceVecAdd xs [] = xs := by
  cases xs <;> rfl

/-- Commutativity of integer-slice vector addition. -/
theorem sliceVecAdd_comm (xs ys : List Int) :
    sliceVecAdd xs ys = sliceVecAdd ys xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs' ih =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      dsimp only [sliceVecAdd]
      rw [Int.add_comm, ih ys']

/-- Associativity of integer-slice vector addition (fails for IEEE-754 floats!). -/
theorem sliceVecAdd_assoc (xs ys zs : List Int) :
    sliceVecAdd (sliceVecAdd xs ys) zs = sliceVecAdd xs (sliceVecAdd ys zs) := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x xs' ih =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      cases zs with
      | nil => rfl
      | cons z zs' =>
        dsimp only [sliceVecAdd]
        rw [Int.add_assoc, ih ys' zs']

/-- Multi-worker integer-slice reduction across GPU workers (`List` specification). -/
def ozakiSliceSum (workers : List (List Int)) : List Int :=
  workers.foldr sliceVecAdd []

/-- Structural index loop for componentwise `Array Int` slice addition (zero-extended). -/
def sliceVecAddExecLoop (xs ys : Array Int) (idx : Nat) : Nat → Array Int → Array Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hx : idx < xs.size then
      if hy : idx < ys.size then
        sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push (xs[idx] + ys[idx]))
      else
        sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push xs[idx])
    else if hy : idx < ys.size then
      sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push ys[idx])
    else
      acc
termination_by structural rem => rem

/-- Tight `Array Int` `Exec` fast path for componentwise integer-slice addition. -/
def sliceVecAddExec (xs ys : Array Int) : Array Int :=
  let n := max xs.size ys.size
  sliceVecAddExecLoop xs ys 0 n (Array.emptyWithCapacity n)

theorem sliceVecAddExecLoop_eq_spec (xs ys : Array Int) (idx rem : Nat)
    (hRem : idx + rem = max xs.size ys.size) (acc : Array Int) :
    (sliceVecAddExecLoop xs ys idx rem acc).toList =
      acc.toList ++ sliceVecAdd (xs.toList.drop idx) (ys.toList.drop idx) := by
  induction rem generalizing idx acc with
  | zero =>
    have hXLe : xs.toList.length ≤ idx := by rw [Array.length_toList]; omega
    have hYLe : ys.toList.length ≤ idx := by rw [Array.length_toList]; omega
    rw [List.drop_eq_nil_of_le hXLe, List.drop_eq_nil_of_le hYLe]
    simp [sliceVecAddExecLoop, sliceVecAdd]
  | succ r ih =>
    have hNext : (idx + 1) + r = max xs.size ys.size := by omega
    unfold sliceVecAddExecLoop
    if hx : idx < xs.size then
      have hxL : idx < xs.toList.length := by rw [Array.length_toList]; exact hx
      have hDropX : xs.toList.drop idx = xs[idx] :: xs.toList.drop (idx + 1) := by
        rw [List.drop_eq_getElem_cons hxL]; rfl
      if hy : idx < ys.size then
        have hyL : idx < ys.toList.length := by rw [Array.length_toList]; exact hy
        have hDropY : ys.toList.drop idx = ys[idx] :: ys.toList.drop (idx + 1) := by
          rw [List.drop_eq_getElem_cons hyL]; rfl
        simp only [hx, hy, ↓reduceDIte]
        rw [ih (idx + 1) hNext (acc.push (xs[idx] + ys[idx])), hDropX, hDropY]
        simp [Array.toList_push, sliceVecAdd, List.append_assoc]
      else
        have hyLe : ys.toList.length ≤ idx := by rw [Array.length_toList]; omega
        have hyLeNext : ys.toList.length ≤ idx + 1 := by omega
        have hDropY : ys.toList.drop idx = [] := List.drop_eq_nil_of_le hyLe
        have hDropYNext : ys.toList.drop (idx + 1) = [] := List.drop_eq_nil_of_le hyLeNext
        simp only [hx, hy, ↓reduceDIte]
        rw [ih (idx + 1) hNext (acc.push xs[idx]), hDropX, hDropY, hDropYNext]
        simp [Array.toList_push, sliceVecAdd, List.append_assoc]
    else
      have hy : idx < ys.size := by omega
      have hyL : idx < ys.toList.length := by rw [Array.length_toList]; exact hy
      have hDropY : ys.toList.drop idx = ys[idx] :: ys.toList.drop (idx + 1) := by
        rw [List.drop_eq_getElem_cons hyL]; rfl
      have hxLe : xs.toList.length ≤ idx := by rw [Array.length_toList]; omega
      have hxLeNext : xs.toList.length ≤ idx + 1 := by omega
      have hDropX : xs.toList.drop idx = [] := List.drop_eq_nil_of_le hxLe
      have hDropXNext : xs.toList.drop (idx + 1) = [] := List.drop_eq_nil_of_le hxLeNext
      simp only [hx, hy, ↓reduceDIte]
      rw [ih (idx + 1) hNext (acc.push ys[idx]), hDropX, hDropXNext, hDropY]
      simp [Array.toList_push, sliceVecAdd, List.append_assoc]

/-- **`Spec ↔ Exec` Slice Addition Equivalence**: `sliceVecAddExec` refines `sliceVecAdd`. -/
theorem sliceVecAddExec_eq_sliceVecAdd (xs ys : Array Int) :
    (sliceVecAddExec xs ys).toList = sliceVecAdd xs.toList ys.toList := by
  unfold sliceVecAddExec
  have h := sliceVecAddExecLoop_eq_spec xs ys 0 (max xs.size ys.size) (Nat.zero_add _)
    (Array.emptyWithCapacity (max xs.size ys.size))
  simpa using h

/-- Structural worker loop for `ozakiSliceSumExec`. -/
def ozakiSliceSumExecLoop (workers : Array (Array Int)) (idx : Nat) :
    Nat → Array Int → Array Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hw : idx < workers.size then
      ozakiSliceSumExecLoop workers (idx + 1) rem (sliceVecAddExec acc workers[idx])
    else
      acc
termination_by structural rem => rem

/-- Tight `Array (Array Int)` `Exec` fast path for multi-worker Ozaki slice reduction. -/
def ozakiSliceSumExec (workers : Array (Array Int)) : Array Int :=
  ozakiSliceSumExecLoop workers 0 workers.size #[]

theorem ozakiSliceSumExecLoop_eq_spec (workers : Array (Array Int)) (idx rem : Nat)
    (hRem : idx + rem = workers.size) (acc : Array Int) :
    (ozakiSliceSumExecLoop workers idx rem acc).toList =
      sliceVecAdd acc.toList (ozakiSliceSum ((workers.toList.drop idx).map Array.toList)) := by
  induction rem generalizing idx acc with
  | zero =>
    have hLe : workers.toList.length ≤ idx := by rw [Array.length_toList]; omega
    rw [List.drop_eq_nil_of_le hLe]
    simp [ozakiSliceSumExecLoop, ozakiSliceSum]
  | succ r ih =>
    have hw : idx < workers.size := by omega
    have hwL : idx < workers.toList.length := by rw [Array.length_toList]; exact hw
    have hDrop : workers.toList.drop idx = workers[idx] :: workers.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hwL]; rfl
    have hNext : (idx + 1) + r = workers.size := by omega
    unfold ozakiSliceSumExecLoop
    simp only [hw, ↓reduceDIte]
    rw [ih (idx + 1) hNext (sliceVecAddExec acc workers[idx]),
        sliceVecAddExec_eq_sliceVecAdd, hDrop]
    dsimp only [List.map, ozakiSliceSum, List.foldr]
    rw [sliceVecAdd_assoc]

/-- **`Spec ↔ Exec` Multi-Worker Ozaki Equivalence**: `ozakiSliceSumExec` over `Array (Array Int)`
    produces the exact same integer slice vector as `ozakiSliceSum`. -/
theorem ozakiSliceSumExec_eq_ozakiSliceSum (workers : Array (Array Int)) :
    (ozakiSliceSumExec workers).toList = ozakiSliceSum (workers.toList.map Array.toList) := by
  unfold ozakiSliceSumExec
  have h := ozakiSliceSumExecLoop_eq_spec workers 0 workers.size (Nat.zero_add _) #[]
  simpa using h

theorem ozakiSliceSum_append (w₁ w₂ : List (List Int)) :
    ozakiSliceSum (w₁ ++ w₂) = sliceVecAdd (ozakiSliceSum w₁) (ozakiSliceSum w₂) := by
  induction w₁ with
  | nil => rfl
  | cons s rest ih =>
    dsimp only [List.cons_append, ozakiSliceSum, List.foldr] at ih ⊢
    rw [ih, sliceVecAdd_assoc]

/-- **Worker-Order / Permutation Invariance (`ozakiSliceSum_perm`)**:
    Permuting GPU worker arrival order leaves `ozakiSliceSum` bit-for-bit identical. -/
theorem ozakiSliceSum_perm {w₁ w₂ : List (List Int)}
    (hPerm : List.Perm w₁ w₂) :
    ozakiSliceSum w₁ = ozakiSliceSum w₂ := by
  induction hPerm with
  | nil => rfl
  | cons s _ ih =>
    dsimp only [ozakiSliceSum, List.foldr] at ih ⊢
    rw [ih]
  | swap s₁ s₂ rest =>
    dsimp only [ozakiSliceSum, List.foldr]
    rw [← sliceVecAdd_assoc, sliceVecAdd_comm s₂ s₁, sliceVecAdd_assoc]
  | trans _ _ ih₁ ih₂ =>
    exact ih₁.trans ih₂

/-- Arbitrary binary AllReduce reduction tree schedule (ring, butterfly, straggler tree). -/
inductive AllReduceTree where
  | empty : AllReduceTree
  | leaf (slices : List Int) : AllReduceTree
  | node (left right : AllReduceTree) : AllReduceTree
  deriving DecidableEq, Repr

/-- Reduce an `AllReduceTree` according to its exact parenthesization / tree topology. -/
def evalAllReduceTree : AllReduceTree → List Int
  | .empty => []
  | .leaf s => s
  | .node l r => sliceVecAdd (evalAllReduceTree l) (evalAllReduceTree r)

/-- Left-to-right leaf frontier of an `AllReduceTree`. -/
def flattenAllReduceTree : AllReduceTree → List (List Int)
  | .empty => []
  | .leaf s => [s]
  | .node l r => flattenAllReduceTree l ++ flattenAllReduceTree r

/-- **Tree-Topology / Re-Association Invariance (`ozaki_tree_schedule_invariant`)**:
    Every binary reduction tree over a sequence of GPU worker slices computes the exact same
    slice vector as canonical `ozakiSliceSum`. -/
theorem ozaki_tree_schedule_invariant (t : AllReduceTree) :
    evalAllReduceTree t = ozakiSliceSum (flattenAllReduceTree t) := by
  induction t with
  | empty => rfl
  | leaf s =>
    dsimp only [evalAllReduceTree, flattenAllReduceTree, ozakiSliceSum, List.foldr]
    rw [sliceVecAdd_nil_right]
  | node l r ihl ihr =>
    dsimp only [evalAllReduceTree, flattenAllReduceTree]
    rw [ihl, ihr, ozakiSliceSum_append]

/-- Reconstruct an exact scaled integer from radix-`B` Ozaki slices (`s₀ + B·s₁ + B²·s₂ + …`). -/
def evalRadixSlices (radix : Int) : List Int → Int
  | [] => 0
  | s :: ss => s + radix * evalRadixSlices radix ss

/-- `sliceVecAdd` is an exact homomorphism for radix evaluation at any radix `B`. -/
theorem evalRadixSlices_sliceVecAdd (radix : Int) (xs ys : List Int) :
    evalRadixSlices radix (sliceVecAdd xs ys) =
      evalRadixSlices radix xs + evalRadixSlices radix ys := by
  induction xs generalizing ys with
  | nil => simp [evalRadixSlices]
  | cons x xs' ih =>
    cases ys with
    | nil => simp [evalRadixSlices]
    | cons y ys' =>
      dsimp only [sliceVecAdd, evalRadixSlices]
      rw [ih ys', Int.mul_add]
      omega

/-- Multi-tenant cluster AllReduce world: `publicReducedSlices` is visible to low-security
    tenant outputs while `secretScheduleTag` records high-security co-tenant scheduling decisions. -/
structure ClusterReduceWorld where
  publicReducedSlices : List Int
  secretScheduleTag   : Nat
  deriving DecidableEq, Repr

/-- Low-security observer sees only the reduced slice vector, never the secret schedule tag. -/
def clusterPublicView : LowView ClusterReduceWorld (List Int) where
  observe w := w.publicReducedSlices

/-- Execute one cluster collective step from a tree schedule `t` and secret co-tenant tag `sec`. -/
def runScheduledAllReduce (t : AllReduceTree) (sec : Nat) : ClusterReduceWorld where
  publicReducedSlices := evalAllReduceTree t
  secretScheduleTag   := sec

/-- **Covert-Channel Closure Theorem (`ozaki_closes_schedule_covert_channel`)**:
    For any two AllReduce tree schedules `t₁, t₂` whose worker leaves are permutations of each
    other (`List.Perm (flattenAllReduceTree t₁) (flattenAllReduceTree t₂)`), varying the secret
    co-tenant schedule tag (`sec₁` vs `sec₂`) and tree parenthesization preserves `HyperLaw2`
    observational non-interference (`HyperLaw2NonInterference clusterPublicView`). -/
theorem ozaki_closes_schedule_covert_channel
    (init₁ init₂ : ClusterReduceWorld)
    (t₁ t₂ : AllReduceTree) (sec₁ sec₂ : Nat)
    (hPerm : List.Perm (flattenAllReduceTree t₁) (flattenAllReduceTree t₂)) :
    HyperLaw2NonInterference clusterPublicView
      [(init₁, init₂), (runScheduledAllReduce t₁ sec₁, runScheduledAllReduce t₂ sec₂)] := by
  apply checkHyperLaw2NonInterference_sound
  dsimp only [checkHyperLaw2NonInterference]
  cases checkLowEquiv clusterPublicView init₁ init₂
  · rfl
  · simp only [List.all_cons, List.all_nil, Bool.and_true, checkHyperLaw2Step, checkLowEquiv,
      clusterPublicView, runScheduledAllReduce]
    rw [ozaki_tree_schedule_invariant t₁, ozaki_tree_schedule_invariant t₂,
        ozakiSliceSum_perm hPerm]
    exact decide_eq_true rfl


/-! ## §3. `AriadneStep` Lineage, Authority-Pinned RTT & Lower-Curve Energy Conservation -/

/-- Lineage & compute-cap commitment for one verifiable AI training/inference step (`AriadneStep`). -/
structure AriadneStep where
  prevWeightsRoot   : Nat
  batchCallTreeRoot : Nat
  nextWeightsRoot   : Nat
  flopsUsed         : Nat
  flopsCap          : Nat
  deriving DecidableEq, Repr

/-- Authority-pinned physical round-trip latency and lower-curve metered energy envelope:
    - `authorityBudgetMicros` is pinned by the verifier hardware class (never prover-chosen;
      `proverClaimedBudgetMicros` is untrusted metadata ignored by acceptance).
    - `lowerCurveProvenMilliJ` (`E_lo`) and `idleEnergyMilliJ` (`E_idle`) credit only the minimum
      physically necessary energy of proven compute, preventing upper-curve subtraction masking.
    - `minHiddenOpMilliJ` (`e_min > 0`) bounds unproved shadow FLOPs via metered residual energy. -/
structure PhysicalEnergyEnvelope where
  measuredRttMicros         : Nat
  authorityBudgetMicros     : Nat
  proverClaimedBudgetMicros : Nat := 0
  meterEnergyMilliJ         : Nat
  lowerCurveProvenMilliJ    : Nat
  idleEnergyMilliJ          : Nat
  toleranceMilliJ           : Nat
  minHiddenOpMilliJ         : Nat
  hiddenOpsCap              : Nat
  deriving DecidableEq, Repr

/-- Metered residual energy above the proven lower curve and idle baseline:
    `meter + η - E_lo - E_idle`. -/
def physicalResidualMilliJ (env : PhysicalEnergyEnvelope) : Nat :=
  (env.meterEnergyMilliJ + env.toleranceMilliJ) - env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ

/-- Executable verifier check for `PhysicalEnergyEnvelope`: enforces positive `minHiddenOpMilliJ`,
    authority-pinned RTT `measuredRttMicros ≤ authorityBudgetMicros`, and residual energy ceiling
    `physicalResidualMilliJ env ≤ minHiddenOpMilliJ * hiddenOpsCap`. -/
def checkPhysicalEnergyEnvelope (env : PhysicalEnergyEnvelope) : Bool :=
  decide (0 < env.minHiddenOpMilliJ ∧
    env.measuredRttMicros ≤ env.authorityBudgetMicros ∧
    env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ ∧
    physicalResidualMilliJ env ≤ env.minHiddenOpMilliJ * env.hiddenOpsCap)

/-- Accepted metering covers the baseline before tolerance is added or naturals
are subtracted. Tolerance cannot conceal an under-metered baseline. -/
theorem checkPhysicalEnergyEnvelope_no_underflow (env : PhysicalEnergyEnvelope)
    (h : checkPhysicalEnergyEnvelope env = true) :
    env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ := by
  exact (of_decide_eq_true h).2.2.1

/-- **Unconditional Lower-Curve Energy Conservation & Authority-Pinned RTT Theorem**:
    Whenever `checkPhysicalEnergyEnvelope env = true`:
    1. `env.measuredRttMicros ≤ env.authorityBudgetMicros`, and mutating the prover's claimed
       RTT budget never alters verifier acceptance;
    2. For any unproved shadow operation count `hiddenOps` satisfying metered energy conservation
       `e_min * hiddenOps ≤ meter + η - E_lo - E_idle`, `hiddenOps ≤ env.hiddenOpsCap`;
    3. Equivalently, any shadow FLOP count `hiddenOps > env.hiddenOpsCap` strictly violates
       metered physical energy conservation. -/
theorem energy_conservation_bounds_hidden_ops
    (env : PhysicalEnergyEnvelope) (hiddenOps : Nat)
    (hEnv : checkPhysicalEnergyEnvelope env = true) :
    env.measuredRttMicros ≤ env.authorityBudgetMicros ∧
      (∀ claimed : Nat,
        checkPhysicalEnergyEnvelope { env with proverClaimedBudgetMicros := claimed } = true) ∧
      (env.minHiddenOpMilliJ * hiddenOps ≤
        (env.meterEnergyMilliJ + env.toleranceMilliJ) -
          env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ →
        hiddenOps ≤ env.hiddenOpsCap) ∧
      (env.hiddenOpsCap < hiddenOps →
        ¬ (env.minHiddenOpMilliJ * hiddenOps ≤
          (env.meterEnergyMilliJ + env.toleranceMilliJ) -
            env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ)) := by
  have hDec := of_decide_eq_true hEnv
  rcases hDec with ⟨hPos, hRtt, _hBaseline, hRes⟩
  unfold physicalResidualMilliJ at hRes
  have hBound :
      env.minHiddenOpMilliJ * hiddenOps ≤
        (env.meterEnergyMilliJ + env.toleranceMilliJ) -
          env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ →
      hiddenOps ≤ env.hiddenOpsCap := by
    intro hPhys
    have hChain : env.minHiddenOpMilliJ * hiddenOps ≤ env.minHiddenOpMilliJ * env.hiddenOpsCap :=
      Nat.le_trans hPhys hRes
    exact Nat.le_of_mul_le_mul_left hChain hPos
  refine ⟨hRtt, fun _ => hEnv, hBound, ?_⟩
  intro hGt hPhys
  have hLe := hBound hPhys
  omega

/-- **Universal Upper-Curve vs Lower-Curve Subtraction Theorem**:
    For any proven lower-curve energy `eLo`, positive per-op energy `0 < eMin`, and positive covert
    shadow operation count `0 < covertOps`: subtracting an inflated upper calibration curve
    `eHi = eLo + eMin * covertOps` from `meter = eHi` masks the entire `eMin * covertOps` covert
    budget (`eHi - eHi = 0`), whereas `PhysicalEnergyEnvelope` subtracting `lowerCurveProvenMilliJ = eLo`
    exposes `physicalResidualMilliJ env = eMin * covertOps` and refuses `hiddenOpsCap = 0`. -/
theorem upper_curve_subtraction_masks_covert_ops
    (eLo covertOps eMin rtt authBudget : Nat)
    (hMin : 0 < eMin) (hCovert : 0 < covertOps) :
    let eHi := eLo + eMin * covertOps
    let env : PhysicalEnergyEnvelope := {
      measuredRttMicros      := rtt
      authorityBudgetMicros  := authBudget
      meterEnergyMilliJ      := eHi
      lowerCurveProvenMilliJ := eLo
      idleEnergyMilliJ       := 0
      toleranceMilliJ        := 0
      minHiddenOpMilliJ      := eMin
      hiddenOpsCap           := 0
    }
    eHi - eHi = 0 ∧
    physicalResidualMilliJ env = eMin * covertOps ∧
    checkPhysicalEnergyEnvelope env = false := by
  dsimp only
  have hRes : (eLo + eMin * covertOps + 0) - eLo - 0 = eMin * covertOps := by omega
  have hPosProd : 0 < eMin * covertOps := Nat.mul_pos hMin hCovert
  refine ⟨Nat.sub_self _, hRes, ?_⟩
  unfold checkPhysicalEnergyEnvelope physicalResidualMilliJ
  dsimp only
  rw [hRes]
  apply decide_eq_false
  intro h
  have hBad := h.2.2.2
  omega

/-- Full cluster step audit context bundling `Sable`, `Ozaki`, `AriadneStep`, and `Reasons` policy. -/
structure ClusterStepContext where
  tensorBound   : IntTensorBound
  sampleWeights : List Int
  sampleActs    : List Int
  workerSlices  : List (List Int)
  step          : AriadneStep
  govProgram    : Obend.Reasons.Program
  targetConcl   : String

/-- Named refusal diagnostic for `ClusterGov` step auditing. -/
inductive ClusterGovRefusal where
  | sableModulusWrap (twoMaxAcc modulusP : Nat)
  | dimExceeded (actualLen maxDim : Nat)
  | weightBoundExceeded
  | activationBoundExceeded
  | flopsCapExceeded (flopsUsed flopsCap : Nat)
  | missingBatchCallTreeRoot
  | policyUnsupported (conclusion : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Deterministic `ClusterGov` step auditor: checks `Sable` no-wrap envelope, vector norms,
    `flopsCap` ceiling, non-zero `batchCallTreeRoot` lineage, and `Obend.Reasons.wf` admission,
    returning the canonical `ozakiSliceSum` collective output on `.ok`. -/
@[expose] def auditClusterStep (ctx : ClusterStepContext) :
    Except ClusterGovRefusal (List Int) :=
  let twoMax := 2 * ctx.tensorBound.dim * ctx.tensorBound.maxAbsWeight * ctx.tensorBound.maxAbsAct
  if !checkSableNoWrap ctx.tensorBound then
    .error (.sableModulusWrap twoMax ctx.tensorBound.modulusP)
  else if !decide (ctx.sampleWeights.length ≤ ctx.tensorBound.dim) then
    .error (.dimExceeded ctx.sampleWeights.length ctx.tensorBound.dim)
  else if !checkVecAbsBounded ctx.tensorBound.maxAbsWeight ctx.sampleWeights then
    .error .weightBoundExceeded
  else if !checkVecAbsBounded ctx.tensorBound.maxAbsAct ctx.sampleActs then
    .error .activationBoundExceeded
  else if !decide (ctx.step.flopsUsed ≤ ctx.step.flopsCap) then
    .error (.flopsCapExceeded ctx.step.flopsUsed ctx.step.flopsCap)
  else if ctx.step.batchCallTreeRoot == 0 then
    .error .missingBatchCallTreeRoot
  else
    let st := Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram) ctx.targetConcl
    if st == .supported then
      .ok (ozakiSliceSum ctx.workerSlices)
    else
      .error (.policyUnsupported ctx.targetConcl st)

/-- Boolean decision wrapper for `auditClusterStep`. -/
@[expose] def verifyClusterStep (ctx : ClusterStepContext) : Bool :=
  (auditClusterStep ctx).isOk

/-- Extended physical + algebraic cluster step context pairing `ClusterStepContext` with
    `PhysicalEnergyEnvelope`. -/
structure PhysicalClusterStepContext where
  base     : ClusterStepContext
  physical : PhysicalEnergyEnvelope

/-- Named refusal diagnostic for `auditPhysicalClusterStep`. -/
inductive PhysicalClusterRefusal where
  | baseRefusal (err : ClusterGovRefusal)
  | zeroMinHiddenOpEnergy
  | energyBaselineUnderflow (meterMilliJ baselineMilliJ : Nat)
  | rttBudgetExceeded (measuredMicros authorityBudgetMicros : Nat)
  | energyResidualExceeded (residualMilliJ maxAllowedMilliJ : Nat)
  deriving DecidableEq, Repr

/-- Audit both algebraic `ClusterStepContext` invariants and physical RTT/energy conservation,
    returning the unboxed `Array Int` `ozakiSliceSumExec` collective result. -/
def auditPhysicalClusterStep (pctx : PhysicalClusterStepContext) :
    Except PhysicalClusterRefusal (Array Int) :=
  match auditClusterStep pctx.base with
  | .error e => .error (.baseRefusal e)
  | .ok _ =>
    let env := pctx.physical
    if !decide (0 < env.minHiddenOpMilliJ) then
      .error .zeroMinHiddenOpEnergy
    else if !decide (env.measuredRttMicros ≤ env.authorityBudgetMicros) then
      .error (.rttBudgetExceeded env.measuredRttMicros env.authorityBudgetMicros)
    else if !decide (env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ) then
      .error (.energyBaselineUnderflow env.meterEnergyMilliJ
        (env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ))
    else
      let res := physicalResidualMilliJ env
      let cap := env.minHiddenOpMilliJ * env.hiddenOpsCap
      if !decide (res ≤ cap) then
        .error (.energyResidualExceeded res cap)
      else
        .ok (ozakiSliceSumExec (pctx.base.workerSlices.map List.toArray).toArray)


/-! ## §4. Hardware & Sealed-VRAM Stage-A Obligations (`ClusterGovObligations`) & Apex Theorem -/

/-- RDNA2 GFX1030 compute shader wavefront dispatch trace for collective/tensor reduction. -/
structure Rdna2WavefrontDispatch where
  shaderIsaWords  : Array UInt32
  waveSize        : Nat
  workgroupSlices : Array (Array Int)
  hwReducedOut    : Array Int
  statusTrap      : Bool
  deriving DecidableEq, Repr

/-- Structural validity check on an `Rdna2WavefrontDispatch`. -/
def checkRdna2DispatchEnvelope (d : Rdna2WavefrontDispatch) : Bool :=
  (d.waveSize == 32 || d.waveSize == 64) &&
  decide (0 < d.shaderIsaWords.size) &&
  !d.statusTrap &&
  decide (0 < d.workgroupSlices.size)

/-- Verifier-challenged sealed-VRAM Merkle page-opening claim over `BitVec 256` roots. -/
structure SealedVramOpeningClaim where
  sealedRoot256     : BitVec 256
  challengeSeed256  : BitVec 256
  totalPages        : Nat
  sampledOffsets    : Array Nat
  openedPageDigests : Array (BitVec 256)
  deriving DecidableEq, Repr

/-- Structural validity check on a `SealedVramOpeningClaim`. -/
def checkSealedVramClaimEnvelope (c : SealedVramOpeningClaim) : Bool :=
  decide (0 < c.totalPages) &&
  decide (8 ≤ c.sampledOffsets.size) &&
  decide (c.sampledOffsets.size = c.openedPageDigests.size) &&
  c.sampledOffsets.all (fun idx => decide (idx < c.totalPages))

/-- Explicit Stage-A hardware & physical-memory obligations for Organ O6 (`ClusterGov`):
    1. `rdna2WavefrontIsaSimulatesOzaki`: RDNA2 WGSL-to-ISA wavefront reduction execution over
       bounded workgroup slices produces the exact integer vector `ozakiSliceSumExec d.workgroupSlices`
       within dimension `b.dim`;
    2. `sealedVramRandomOpeningSound`: accepting a random-offset `SealedVramOpeningClaim` bound to
       `step.prevWeightsRoot` extracts a full resident VRAM page table matching all sampled
       challenge openings and non-zero weight-lineage roots. -/
class ClusterGovObligations : Prop where
  rdna2WavefrontIsaSimulatesOzaki :
    ∀ (d : Rdna2WavefrontDispatch) (b : IntTensorBound),
      checkRdna2DispatchEnvelope d = true →
      checkSableNoWrap b = true →
      (∀ row ∈ d.workgroupSlices.toList,
        row.size ≤ b.dim ∧ checkVecAbsBounded b.maxAbsAct row.toList = true) →
      d.hwReducedOut = ozakiSliceSumExec d.workgroupSlices ∧
        d.hwReducedOut.size ≤ b.dim
  sealedVramRandomOpeningSound :
    ∀ (c : SealedVramOpeningClaim) (step : AriadneStep),
      checkSealedVramClaimEnvelope c = true →
      c.sealedRoot256.toNat = step.prevWeightsRoot →
      step.flopsUsed ≤ step.flopsCap →
      ∃ residentPages : Array (BitVec 256),
        residentPages.size = c.totalPages ∧
        c.sampledOffsets[0]? = some (c.challengeSeed256.toNat % c.totalPages) ∧
        (∀ k : Nat, k < c.sampledOffsets.size →
          residentPages[c.sampledOffsets[k]?.getD 0]? = c.openedPageDigests[k]?) ∧
        step.prevWeightsRoot ≠ 0 ∧
        step.nextWeightsRoot ≠ 0

/-- **Organ O6 Unconditional Apex Step Theorem (`apex_verifiable_ai_cluster_step`)**:
    With **zero open obligations** and **zero `Classical.choice`**, whenever
    `auditClusterStep ctx = .ok reducedSlices`, Lean's kernel establishes:
    1. Exact `Sable` $F_O$ modular dot-product round-trip (`decodeSignedModP ... = intDot ...`)
       matching `intDotExec`,
    2. Permutation-invariant bit-exact `Ozaki` collective output (`ozakiSliceSum workers' = reducedSlices`),
    3. Enforced `flopsUsed ≤ flopsCap` compute cap and non-zero `batchCallTreeRoot` lineage, and
    4. Supported `Obend.Reasons.wf` governance judgment. -/
theorem apex_verifiable_ai_cluster_step
    (ctx : ClusterStepContext) (reducedSlices : List Int)
    (workers' : List (List Int))
    (hAudit : auditClusterStep ctx = .ok reducedSlices)
    (hPerm : List.Perm ctx.workerSlices workers') :
    2 * (intDot ctx.sampleWeights ctx.sampleActs).natAbs < ctx.tensorBound.modulusP ∧
      decodeSignedModP ctx.tensorBound.modulusP
        (embedModP ctx.tensorBound.modulusP (intDot ctx.sampleWeights ctx.sampleActs)) =
        intDot ctx.sampleWeights ctx.sampleActs ∧
      ozakiSliceSum workers' = reducedSlices ∧
      ctx.step.flopsUsed ≤ ctx.step.flopsCap ∧
      ctx.step.batchCallTreeRoot ≠ 0 ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram) ctx.targetConcl = .supported := by
  unfold auditClusterStep at hAudit
  cases hSable : checkSableNoWrap ctx.tensorBound
  · rw [hSable] at hAudit; cases hAudit
  · rw [hSable] at hAudit
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
    cases hDimDec : decide (ctx.sampleWeights.length ≤ ctx.tensorBound.dim)
    · rw [hDimDec] at hAudit; cases hAudit
    · rw [hDimDec] at hAudit
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
      have hDim : ctx.sampleWeights.length ≤ ctx.tensorBound.dim := of_decide_eq_true hDimDec
      cases hW : checkVecAbsBounded ctx.tensorBound.maxAbsWeight ctx.sampleWeights
      · rw [hW] at hAudit; cases hAudit
      · rw [hW] at hAudit
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
        cases hX : checkVecAbsBounded ctx.tensorBound.maxAbsAct ctx.sampleActs
        · rw [hX] at hAudit; cases hAudit
        · rw [hX] at hAudit
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
          cases hFlopsDec : decide (ctx.step.flopsUsed ≤ ctx.step.flopsCap)
          · rw [hFlopsDec] at hAudit; cases hAudit
          · rw [hFlopsDec] at hAudit
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
            have hFlops : ctx.step.flopsUsed ≤ ctx.step.flopsCap := of_decide_eq_true hFlopsDec
            cases hBatchZero : (ctx.step.batchCallTreeRoot == 0)
            · rw [hBatchZero] at hAudit
              simp only [Bool.false_eq_true, ↓reduceIte] at hAudit
              have hBatchNe : ctx.step.batchCallTreeRoot ≠ 0 := by
                intro hEq0
                have hTrue : (ctx.step.batchCallTreeRoot == 0) = true := beq_iff_eq.mpr hEq0
                exact Bool.false_ne_true (hBatchZero.symm.trans hTrue)
              cases hSt : (Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram)
                  ctx.targetConcl == .supported)
              · rw [hSt] at hAudit; cases hAudit
              · rw [hSt] at hAudit
                simp only [↓reduceIte] at hAudit
                injection hAudit with hOut
                have hExact := sable_dot_exact_no_wrap ctx.tensorBound
                  ctx.sampleWeights ctx.sampleActs hSable hDim
                  (checkVecAbsBounded_sound hW)
                  (checkVecAbsBounded_sound hX)
                have hPermEq : ozakiSliceSum workers' = reducedSlices := by
                  rw [← ozakiSliceSum_perm hPerm, hOut]
                exact ⟨hExact.1, hExact.2, hPermEq, hFlops, hBatchNe, beq_iff_eq.mp hSt⟩
            · rw [hBatchZero] at hAudit; cases hAudit


/-! ## §5. Concrete Cluster Governance Fixtures & Silver Smoke Runner -/

/-- Valid KoalaBear (`p = 2130706433`) 4-dim tensor bound (`2 * 4 * 1024 * 1024 = 8,388,608 < p`). -/
def defaultKoalaBound : IntTensorBound where
  dim          := 4
  maxAbsWeight := 1024
  maxAbsAct    := 1024
  modulusP     := koalaBearPrime

/-- Valid `ClusterStepContext` within `Sable` no-wrap bounds and `flopsCap = 10_000_000`. -/
@[expose] def validClusterStepCtx : ClusterStepContext where
  tensorBound   := {
    dim          := 4
    maxAbsWeight := 1024
    maxAbsAct    := 1024
    modulusP     := 2130706433
  }
  sampleWeights := [512, -256, 128, -64]
  sampleActs    := [300, 400, -500, 100]
  workerSlices  := [[100, -20, 3], [50, 40, -1], [-30, 10, 5]]
  step := {
    prevWeightsRoot   := 0x11112222
    batchCallTreeRoot := 0x9999AAAA
    nextWeightsRoot   := 0x33334444
    flopsUsed         := 7500000
    flopsCap          := 10000000
  }
  govProgram := {
    facts := ["cluster_quorum_signed", "corrigibility_watchdog_armed"]
    rules := [{
      name  := "admit_training_step"
      concl := "step_admitted"
      pos   := ["cluster_quorum_signed", "corrigibility_watchdog_armed"]
      neg   := ["kill_switch_tripped"]
    }]
  }
  targetConcl := "step_admitted"

/-- Default authority-pinned `PhysicalEnergyEnvelope` for rack-local cluster verification:
    `measuredRttMicros = 1200 ≤ 3000 = authorityBudgetMicros`, residual energy
    `(450 + 10) - 400 - 40 = 20 ≤ 5 * 4 = 20` mJ (`hiddenOpsCap = 4`). -/
def defaultPhysicalEnvelope : PhysicalEnergyEnvelope where
  measuredRttMicros         := 1200
  authorityBudgetMicros     := 3000
  proverClaimedBudgetMicros := 999999
  meterEnergyMilliJ         := 450
  lowerCurveProvenMilliJ    := 400
  idleEnergyMilliJ          := 40
  toleranceMilliJ           := 10
  minHiddenOpMilliJ         := 5
  hiddenOpsCap              := 4

/-- Planted bad context #1: `Sable` modulus wraparound (`2 * 4 * 50000 * 10000 = 4,000,000,000 ≥ p`). -/
def wrapOverflowClusterCtx : ClusterStepContext :=
  { validClusterStepCtx with
    tensorBound := {
      dim          := 4
      maxAbsWeight := 50000
      maxAbsAct    := 10000
      modulusP     := koalaBearPrime
    } }

/-- Planted bad context #2: `flopsUsed` (`12,500,000`) breaches `flopsCap` (`10,000,000`). -/
def flopsBreachClusterCtx : ClusterStepContext :=
  { validClusterStepCtx with
    step := { validClusterStepCtx.step with flopsUsed := 12500000 } }

/-- Executable Silver end-to-end smoke runner for Organ O6 (`ClusterGov`). -/
def silverClusterGovSmoke : Bool :=
  let validOk :=
    match auditClusterStep validClusterStepCtx with
    | .ok slices => slices == [120, 30, 7]
    | .error _ => false
  let execDotOk :=
    intDotExec #[512, -256, 128, -64] #[300, 400, -500, 100] == -19200
  let execOzakiOk :=
    ozakiSliceSumExec #[#[100, -20, 3], #[50, 40, -1], #[-30, 10, 5]] == #[120, 30, 7]
  let physOk := checkPhysicalEnergyEnvelope defaultPhysicalEnvelope
  let physRelayRefused :=
    !checkPhysicalEnergyEnvelope { defaultPhysicalEnvelope with measuredRttMicros := 52000 }
  let physEnergyRefused :=
    !checkPhysicalEnergyEnvelope { defaultPhysicalEnvelope with meterEnergyMilliJ := 500 }
  let treeLeft : AllReduceTree :=
    .node (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1])) (.leaf [-30, 10, 5])
  let treeRight : AllReduceTree :=
    .node (.leaf [-30, 10, 5]) (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1]))
  let hyperLawOk :=
    checkHyperLaw2NonInterference clusterPublicView
      [(⟨[0, 0, 0], 1⟩, ⟨[0, 0, 0], 2⟩),
       (runScheduledAllReduce treeLeft 1, runScheduledAllReduce treeRight 2)]
  let wrapRefused :=
    match auditClusterStep wrapOverflowClusterCtx with
    | .error e => e == .sableModulusWrap 4000000000 koalaBearPrime
    | .ok _ => false
  let flopsRefused :=
    match auditClusterStep flopsBreachClusterCtx with
    | .error e => e == .flopsCapExceeded 12500000 10000000
    | .ok _ => false
  validOk && execDotOk && execOzakiOk && physOk && physRelayRefused && physEnergyRefused &&
    hyperLawOk && wrapRefused && flopsRefused

example : checkVecAbsBounded 1024 [512, -256, 128, -64] = true := rfl

example : silverClusterGovSmoke = true := by
  decide

end Obend.Trailblaze.ClusterGov
end
