module
/-
# Obend.Crypto.Sumcheck — Fenzi-Bound Multilinear Sumcheck PIOP & LFKN Soundness Reduction

Polymorphic interactive/Fiat–Shamir Sumcheck PIOP over `[LawfulCommRing R]` paired with
`Transcript .relationBound`:
1. `TranscriptChallenge R` typeclass connecting `Transcript .relationBound` challenge squeezing
   and canonical element serialization for both `Goldilocks` and `GoldilocksExt2` (128-bit security).
2. `RoundPoly R` univariate round polynomials with Horner evaluation, formal polynomial
   subtraction `RoundPoly.sub`, and degree-bound enforcement `degLe`.
3. `verifySumcheck` reducing $\sum_{\mathbf{x} \in \{0,1\}^v} \tilde{f}(\mathbf{x}) = S$ over
   a `.relationBound` transcript to a single multilinear evaluation claim `EvalClaim R v`.
4. `honestSumcheckProver` and `honestSumcheckProver_completeness` proving exact completeness
   and `claim.expectedVal = mleEval tbl claim.point`.
5. `verifySumcheck_round_sound` and the full multi-round LFKN soundness dichotomy
   `verifySumcheck_sound_dichotomy`: any accepted proof of a false hypercube sum either
   produces a false final `EvalClaim` (caught by `MultilinearPCS.verifyEval`) or forces a
   Fiat–Shamir challenge `r_i` to vanish on a non-zero round discrepancy polynomial `p_i - p_i^*`.
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript

@[expose] public section
namespace Obend.Crypto

open Obend.Digest.Cshake256

set_option autoImplicit false

/-! ## 1. Transcript Challenge Interface (`Goldilocks` & `GoldilocksExt2`) -/

/-- Bridges a ring/field `R` to the Fenzi-bound 256-bit Fiat–Shamir `Transcript .relationBound`. -/
class TranscriptChallenge (R : Type) where
  encodeElem : R → ByteArray
  squeezeChallenge : Transcript .relationBound → R × Transcript .relationBound

instance : TranscriptChallenge Goldilocks where
  encodeElem := encodeGoldilocksBytes
  squeezeChallenge := squeezeGoldilocks

instance : TranscriptChallenge GoldilocksExt2 where
  encodeElem := encodeGoldilocksExt2Bytes
  squeezeChallenge := squeezeGoldilocksExt2

/-! ## 2. Univariate Round Polynomials (`RoundPoly R`) -/

/-- Univariate polynomial in monomial basis `coeffs = [c₀, c₁, …, c_d]`. -/
structure RoundPoly (R : Type) where
  coeffs : List R
  deriving DecidableEq, Repr

namespace RoundPoly

/-- Horner evaluation $c_0 + x (c_1 + x (\cdots))$. -/
def evalCoeffs {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero
  | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x))

def eval {R : Type} [CommRingOps R] (p : RoundPoly R) (x : R) : R :=
  evalCoeffs p.coeffs x

/-- Check formal degree bound `coeffs.length ≤ maxDeg + 1`. -/
def degLe {R : Type} (maxDeg : Nat) (p : RoundPoly R) : Bool :=
  decide (p.coeffs.length ≤ maxDeg + 1)

/-- Coefficient-wise polynomial subtraction `p - q`. -/
def subCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], [] => []
  | c :: cs, [] => c :: subCoeffs cs []
  | [], d :: ds => CommRingOps.neg d :: subCoeffs [] ds
  | c :: cs, d :: ds => CommRingOps.sub c d :: subCoeffs cs ds

def sub {R : Type} [CommRingOps R] (p q : RoundPoly R) : RoundPoly R :=
  ⟨subCoeffs p.coeffs q.coeffs⟩

theorem evalCoeffs_sub {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      evalCoeffs (subCoeffs cs ds) x = CommRingOps.sub (evalCoeffs cs x) (evalCoeffs ds x)
  | [], [], _ => by
    simp [subCoeffs, evalCoeffs, LawfulCommRing.sub_self]
  | c :: cs, [], x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs [] x]
    rw [LawfulCommRing.sub_zero, LawfulCommRing.sub_zero]
  | [], d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub [] ds x]
    rw [LawfulCommRing.sub_eq_add_neg CommRingOps.zero (evalCoeffs ds x),
        LawfulCommRing.zero_add, LawfulCommRing.mul_neg,
        LawfulCommRing.sub_eq_add_neg CommRingOps.zero _,
        LawfulCommRing.zero_add]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs ds x]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

theorem eval_sub {R : Type} [LawfulCommRing R] (p q : RoundPoly R) (x : R) :
    (sub p q).eval x = CommRingOps.sub (p.eval x) (q.eval x) :=
  evalCoeffs_sub p.coeffs q.coeffs x

theorem eval_linear_zero {R : Type} [LawfulCommRing R] (c₀ c₁ : R) :
    eval ⟨[c₀, c₁]⟩ CommRingOps.zero = c₀ := by
  simp [eval, evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem eval_linear_one {R : Type} [LawfulCommRing R] (c₀ c₁ : R) :
    eval ⟨[c₀, c₁]⟩ CommRingOps.one = CommRingOps.add c₀ c₁ := by
  simp [eval, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.one_mul]

theorem eval_linear {R : Type} [LawfulCommRing R] (c₀ c₁ r : R) :
    eval ⟨[c₀, c₁]⟩ r = CommRingOps.add c₀ (CommRingOps.mul r c₁) := by
  simp [eval, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

end RoundPoly

/-! ## 3. Sumcheck Evaluation Claim, Transcript Absorption & Verifier -/

/-- Final evaluation claim reduced by a $v$-round Sumcheck execution:
    asserts $\tilde{g}(\text{point}) = \text{expectedVal}$ with `point.length = numVars`. -/
structure EvalClaim (R : Type) (numVars : Nat) where
  point : List R
  point_len : point.length = numVars
  expectedVal : R
  deriving DecidableEq, Repr

/-- `"SUMCHECK.ROUND"` domain label bytes. -/
def sumcheckRoundLabel : ByteArray :=
  Native.bytesOfList [0x53, 0x55, 0x4d, 0x43, 0x48, 0x45, 0x43, 0x4b,
                      0x2e, 0x52, 0x4f, 0x55, 0x4e, 0x44]

/-- Serialize a `RoundPoly R` as length-prefixed canonical element bytes. -/
def encodeRoundPoly {R : Type} [TranscriptChallenge R] (p : RoundPoly R) : ByteArray :=
  Native.bytesOfList
    (leb128 p.coeffs.length ++
      (p.coeffs.flatMap fun c => encodeListField (TranscriptChallenge.encodeElem c).data.toList))

/-- Absorb a round polynomial into a `.relationBound` transcript and squeeze challenge `r`. -/
def absorbAndSqueezeRound {R : Type} [TranscriptChallenge R]
    (p : RoundPoly R) (tr : Transcript .relationBound) : R × Transcript .relationBound :=
  let trAbs := absorbMsg sumcheckRoundLabel (encodeRoundPoly p) tr
  TranscriptChallenge.squeezeChallenge trAbs

/-- Verify one Sumcheck round: checks `deg(p) ≤ maxDeg` and `p(0) + p(1) = claimedSum`,
    absorbs `p` into the Fenzi-bound transcript, squeezes `r`, and outputs `(r, p(r), tr')`. -/
def verifySumcheckRound {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    (maxDeg : Nat) (claimedSum : R) (p : RoundPoly R) (tr : Transcript .relationBound) :
    Option (R × R × Transcript .relationBound) :=
  if p.degLe maxDeg &&
     decide (CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum) then
    let (r, tr') := absorbAndSqueezeRound p tr
    some (r, p.eval r, tr')
  else
    none

/-- **Complete Fiat–Shamir Sumcheck Verifier (`verifySumcheck`)**:
    Reduces $\sum_{\mathbf{x} \in \{0,1\}^{\text{numVars}}} g(\mathbf{x}) = \text{claimedSum}$
    over `Transcript .relationBound` to `EvalClaim R numVars`. -/
def verifySumcheck {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    (maxDeg : Nat) :
    (numVars : Nat) → (claimedSum : R) → (rounds : List (RoundPoly R)) →
    Transcript .relationBound → Option (EvalClaim R numVars × Transcript .relationBound)
  | 0, claimedSum, [], tr =>
    some (⟨[], rfl, claimedSum⟩, tr)
  | v + 1, claimedSum, p :: ps, tr =>
    match verifySumcheckRound maxDeg claimedSum p tr with
    | none => none
    | some (r, nextClaim, tr') =>
      match verifySumcheck maxDeg v nextClaim ps tr' with
      | none => none
      | some (subClaim, trFinal) =>
        some (⟨r :: subClaim.point, congrArg Nat.succ subClaim.point_len, subClaim.expectedVal⟩,
              trFinal)
  | _, _, _, _ => none

/-! ## 4. Honest Multilinear Sumcheck Prover & Completeness -/

/-- Honest degree-1 round polynomial $p^*(X) = s_0 + (s_1 - s_0) X$ for `v + 1` variables. -/
def honestRoundPoly {R : Type} [CommRingOps R] (v : Nat) (tbl : List R) : RoundPoly R :=
  let s₀ := hypercubeSum v (foldFirstVar tbl CommRingOps.zero)
  let s₁ := hypercubeSum v (foldFirstVar tbl CommRingOps.one)
  ⟨[s₀, CommRingOps.sub s₁ s₀]⟩

theorem honestRoundPoly_sum {R : Type} [LawfulCommRing R] (v : Nat) (tbl : List R) :
    CommRingOps.add ((honestRoundPoly v tbl).eval CommRingOps.zero)
                    ((honestRoundPoly v tbl).eval CommRingOps.one) =
      hypercubeSum (v + 1) tbl := by
  unfold honestRoundPoly
  rw [RoundPoly.eval_linear_zero, RoundPoly.eval_linear_one,
      LawfulCommRing.add_sub_cancel_left, hypercubeSum_succ]

theorem honestRoundPoly_eval {R : Type} [LawfulCommRing R] (v : Nat) (tbl : List R) (r : R) :
    (honestRoundPoly v tbl).eval r = hypercubeSum v (foldFirstVar tbl r) := by
  unfold honestRoundPoly
  rw [RoundPoly.eval_linear]
  exact (hypercubeSum_foldFirstVar v tbl r).symm

/-- Honest Fiat–Shamir Sumcheck prover folding `tbl` round-by-round via `foldFirstVar`. -/
def honestSumcheckProver {R : Type} [CommRingOps R] [TranscriptChallenge R] :
    (numVars : Nat) → List R → Transcript .relationBound →
    List (RoundPoly R) × EvalClaim R numVars × Transcript .relationBound
  | 0, tbl, tr =>
    ([], ⟨[], rfl, mleEval tbl []⟩, tr)
  | v + 1, tbl, tr =>
    let p := honestRoundPoly v tbl
    let (r, tr') := absorbAndSqueezeRound p tr
    let tbl' := foldFirstVar tbl r
    let (restPolys, subClaim, trFinal) := honestSumcheckProver v tbl' tr'
    (p :: restPolys,
     ⟨r :: subClaim.point, congrArg Nat.succ subClaim.point_len, subClaim.expectedVal⟩,
     trFinal)

/-- Single-round completeness witness for `verifySumcheckRound`: honest linear round polynomials
    are accepted for every `maxDeg ≥ 1`. -/
theorem verifySumcheckRound_complete
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {maxDeg : Nat} (v : Nat) (tbl : List R)
    (tr : Transcript .relationBound) :
    1 ≤ maxDeg →
    verifySumcheckRound (R := R) maxDeg (hypercubeSum (v + 1) tbl)
      (honestRoundPoly v tbl) tr =
      some ((absorbAndSqueezeRound (honestRoundPoly v tbl) tr).1,
            hypercubeSum v (foldFirstVar tbl (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).1),
            (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).2) := by
  intro hDeg
  unfold verifySumcheckRound
  have hLen : (honestRoundPoly v tbl).degLe maxDeg = true := by
    unfold RoundPoly.degLe honestRoundPoly
    rw [decide_eq_true_eq]
    simp only [List.length_cons, List.length_nil]
    omega
  have hSum : decide (CommRingOps.add ((honestRoundPoly v tbl).eval CommRingOps.zero)
      ((honestRoundPoly v tbl).eval CommRingOps.one) =
      hypercubeSum (v + 1) tbl) = true := by
    rw [decide_eq_true_eq]
    exact honestRoundPoly_sum v tbl
  rw [hLen, hSum]
  simp only [Bool.true_and, ↓reduceIte, honestRoundPoly_eval]

/-- **Honest Sumcheck Prover Completeness (`honestSumcheckProver_completeness`)**:
    For every `maxDeg ≥ 1`, variable count `v`, table `tbl`, and Fenzi-bound transcript `tr`,
    `honestSumcheckProver` produces a proof accepted by `verifySumcheck` whose final
    `EvalClaim` equals the true multilinear evaluation `mleEval tbl claim.point`. -/
theorem honestSumcheckProver_completeness
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {maxDeg : Nat} (hDeg : 1 ≤ maxDeg) :
    ∀ (v : Nat) (tbl : List R) (tr : Transcript .relationBound),
      let (rounds, claim, trOut) := honestSumcheckProver v tbl tr
      verifySumcheck (R := R) maxDeg v (hypercubeSum v tbl) rounds tr = some (claim, trOut) ∧
      claim.expectedVal = mleEval tbl claim.point
  | 0, tbl, tr => by
    simp [honestSumcheckProver, verifySumcheck, hypercubeSum_zero]
  | v + 1, tbl, tr => by
    dsimp only [honestSumcheckProver]
    have hRound := verifySumcheckRound_complete v tbl tr hDeg
    obtain ⟨ihVer, ihEval⟩ :=
      honestSumcheckProver_completeness hDeg v
        (foldFirstVar tbl (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).1)
        (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).2
    refine ⟨?_, ?_⟩
    · simp only [verifySumcheck, hRound, ihVer]
    · rw [ihEval, mleEval_foldFirstVar]

/-! ## 5. Round-by-Round & Multi-Round LFKN Algebraic Soundness -/

/-- Witness that Fiat–Shamir challenge `r` hit a root of a non-identically-zero round
    discrepancy polynomial `diff = p - p^*` (`diff(r) = 0` while `diff(0) ≠ 0 ∨ diff(1) ≠ 0`). -/
def RoundDiscrepancyRootHit {R : Type} [CommRingOps R] (p pStar : RoundPoly R) (r : R) : Prop :=
  (p.sub pStar).eval r = CommRingOps.zero ∧
  ((p.sub pStar).eval CommRingOps.zero ≠ CommRingOps.zero ∨
   (p.sub pStar).eval CommRingOps.one ≠ CommRingOps.zero)

theorem eq_of_sub_eq_zero {R : Type} [LawfulCommRing R] {a b : R}
    (h : CommRingOps.sub a b = CommRingOps.zero) : a = b := by
  have h1 := congrArg (fun z => CommRingOps.add z b) h
  rw [LawfulCommRing.zero_add, LawfulCommRing.sub_eq_add_neg,
      LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg, LawfulCommRing.add_zero] at h1
  exact h1

/-- **Single-Round Sumcheck Soundness (`verifySumcheck_round_sound`)**:
    If `verifySumcheckRound` accepts `p` on a false `claimedSum ≠ hypercubeSum (v + 1) tbl`,
    then `deg(p) ≤ maxDeg`, `p(0) + p(1) = claimedSum`, and **either** the next-round claim
    `nextClaim` remains false for the folded table `foldFirstVar tbl r`, **or** challenge `r`
    hit an exact algebraic root of the non-zero discrepancy polynomial `p - honestRoundPoly v tbl`. -/
theorem verifySumcheck_round_sound
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {maxDeg v : Nat} {claimedSum : R} {p : RoundPoly R} {tr : Transcript .relationBound}
    {r nextClaim : R} {tr' : Transcript .relationBound}
    (tbl : List R)
    (hAcc : verifySumcheckRound maxDeg claimedSum p tr = some (r, nextClaim, tr'))
    (hFalse : claimedSum ≠ hypercubeSum (v + 1) tbl) :
    p.coeffs.length ≤ maxDeg + 1 ∧
    CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum ∧
    tr' = (absorbAndSqueezeRound p tr).2 ∧
    (nextClaim ≠ hypercubeSum v (foldFirstVar tbl r) ∨
     RoundDiscrepancyRootHit (R := R) p (honestRoundPoly v tbl) r) := by
  unfold verifySumcheckRound at hAcc
  split at hAcc
  · rename_i hCond
    simp only [Bool.and_eq_true, RoundPoly.degLe, decide_eq_true_eq] at hCond
    simp only [Option.some.injEq, Prod.mk.injEq] at hAcc
    rcases hAcc with ⟨hr, hNext, hTr⟩
    subst hr hNext
    refine ⟨hCond.1, hCond.2, hTr.symm, ?_⟩
    let pStar := honestRoundPoly v tbl
    let ch := (absorbAndSqueezeRound p tr).1
    by_cases hAgree : p.eval ch = hypercubeSum v (foldFirstVar tbl ch)
    · right
      have hAgreePoly : p.eval ch = pStar.eval ch := by
        rw [hAgree]; exact (honestRoundPoly_eval v tbl ch).symm
      have hRoot : (p.sub pStar).eval ch = CommRingOps.zero := by
        rw [RoundPoly.eval_sub, hAgreePoly, LawfulCommRing.sub_self]
      refine ⟨hRoot, ?_⟩
      by_cases h0 : (p.sub pStar).eval CommRingOps.zero = CommRingOps.zero
      · right
        intro h1
        have eq0 : p.eval CommRingOps.zero = pStar.eval CommRingOps.zero := by
          rw [RoundPoly.eval_sub] at h0
          exact eq_of_sub_eq_zero h0
        have eq1 : p.eval CommRingOps.one = pStar.eval CommRingOps.one := by
          rw [RoundPoly.eval_sub] at h1
          exact eq_of_sub_eq_zero h1
        have hEqSum : claimedSum = hypercubeSum (v + 1) tbl := by
          rw [← hCond.2, eq0, eq1]
          exact honestRoundPoly_sum v tbl
        exact hFalse hEqSum
      · exact .inl h0
    · exact .inl hAgree
  · cases hAcc

/-- Inductive predicate witnessing that at least one Sumcheck round encountered a
    Fiat–Shamir challenge landing on a root of a non-zero bounded-degree discrepancy polynomial. -/
def ExistsRoundRootHit {R : Type} [CommRingOps R] [TranscriptChallenge R] :
    (numVars : Nat) → List R → List (RoundPoly R) → Transcript .relationBound → Prop
  | 0, _, _, _ => False
  | _ + 1, _, [], _ => False
  | v + 1, tbl, p :: ps, tr =>
    let (r, tr') := absorbAndSqueezeRound p tr
    RoundDiscrepancyRootHit p (honestRoundPoly v tbl) r ∨
    ExistsRoundRootHit v (foldFirstVar tbl r) ps tr'

/-- **Multi-Round LFKN Sumcheck Soundness Dichotomy (`verifySumcheck_sound_dichotomy`)**:
    Whenever `verifySumcheck` accepts a proof `rounds` for a false hypercube sum
    `claimedSum ≠ hypercubeSum v tbl`, **either** the final evaluation claim is false
    (`claim.expectedVal ≠ mleEval tbl claim.point`), **or** at least one Fiat–Shamir
    round challenge hit an algebraic root of a non-zero degree-`≤ maxDeg` discrepancy polynomial. -/
theorem verifySumcheck_sound_dichotomy
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    (maxDeg : Nat) :
    ∀ (v : Nat) (tbl : List R) (claimedSum : R) (rounds : List (RoundPoly R))
      (tr : Transcript .relationBound) (claim : EvalClaim R v) (trFinal : Transcript .relationBound),
      verifySumcheck maxDeg v claimedSum rounds tr = some (claim, trFinal) →
      claimedSum ≠ hypercubeSum v tbl →
      claim.expectedVal ≠ mleEval tbl claim.point ∨
      ExistsRoundRootHit v tbl rounds tr
  | 0, tbl, claimedSum, [], tr, claim, trFinal, hVer, hFalse => by
    simp only [verifySumcheck, Option.some.injEq, Prod.mk.injEq] at hVer
    rcases hVer with ⟨rfl, rfl⟩
    left
    simpa [hypercubeSum_zero] using hFalse
  | 0, _, _, _ :: _, _, _, _, hVer, _ => by
    cases hVer
  | _ + 1, _, _, [], _, _, _, hVer, _ => by
    cases hVer
  | v + 1, tbl, claimedSum, p :: ps, tr, claim, trFinal, hVer, hFalse => by
    simp only [verifySumcheck] at hVer
    cases hRound : verifySumcheckRound maxDeg claimedSum p tr with
    | none => rw [hRound] at hVer; cases hVer
    | some stepOut =>
      rcases stepOut with ⟨r, nextClaim, tr'⟩
      rw [hRound] at hVer
      dsimp only at hVer
      cases hRec : verifySumcheck maxDeg v nextClaim ps tr' with
      | none => rw [hRec] at hVer; cases hVer
      | some recOut =>
        rcases recOut with ⟨subClaim, trEnd⟩
        rw [hRec] at hVer
        simp only [Option.some.injEq, Prod.mk.injEq] at hVer
        rcases hVer with ⟨rfl, rfl⟩
        have hStepEq : (r, tr') = absorbAndSqueezeRound p tr := by
          unfold verifySumcheckRound at hRound
          split at hRound
          · simp only [Option.some.injEq, Prod.mk.injEq] at hRound
            exact Prod.ext hRound.1.symm hRound.2.2.symm
          · cases hRound
        obtain ⟨_, _, _, hDich⟩ := verifySumcheck_round_sound tbl hRound hFalse
        rcases hDich with hNextFalse | hHit0
        · rcases verifySumcheck_sound_dichotomy maxDeg v (foldFirstVar tbl r)
              nextClaim ps tr' subClaim trEnd hRec hNextFalse with hEvalFalse | hLaterHit
          · left
            simpa only [mleEval_foldFirstVar] using hEvalFalse
          · right
            dsimp only [ExistsRoundRootHit]
            rw [← hStepEq]
            exact .inr hLaterHit
        · right
          dsimp only [ExistsRoundRootHit]
          rw [← hStepEq]
          exact .inl hHit0

end Obend.Crypto
end
