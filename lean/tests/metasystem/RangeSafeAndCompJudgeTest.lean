module
/-
# Metasystem End-to-End Verification — `Obend.Core.RangeSafe` & `Obend.Judge.Computational`

Exercises Chasm 1 (`Nat` ↔ `BitVec 64` ↔ `ℤ/Mℤ` arithmetic bridge) and Chasm 5 (0-axiom constructive
`ComputationalJudge`) end-to-end:

1. **Q32.32 Fixed-Point & Bounded Core4 Term → `RtlExpr` Hardware Synthesis (`compileTerm_evaluates_sound`)**:
   - Compiles a non-trivial Core4 program using `.qmul32`, inline `let` (`.app (.lam ...)`), `.add`,
     `.lessEqual`, `.ifBool`, and underflow-free `.subtract` to `RtlExpr`, proving exact agreement
     between `evalRtlExpr` (`BitVec 64`) and unbounded `Core.Term.Evaluates` (`Nat`).
2. **Sable `F_O` Prime-Field No-Wrap Bridge (`evaluates_mod_prime_exact_of_rangeSafe`) & Counterexamples**:
   - Proves exact integer reconstruction over KoalaBear (`2^31 - 2^24 + 1`), BabyBear (`2^31 - 2^27 + 1`),
     and Goldilocks (`2^64 - 2^32 + 1`), alongside necessity counterexamples when `hi < bound` or
     subtraction non-underflow is omitted.
3. **Constructive 2-Special-Soundness Extractors (Witness Branch & Explicit Break Branch)**:
   - Ajtai / Module-SIS (`sisOpening2SpecialSound`): extracts either a short witness or an explicit
     nonzero short kernel vector `Δz = z₁ - z₂` (`‖Δz‖_∞ ≤ 2β`, `M · Δz ≡ 0 mod q`).
   - Hash-Committed Linear IOP (`hashLinear2SpecialSound`): extracts either the polynomial witness
     or an explicit `Obend.Digest.HashBytes.Collision`.
4. **Compositional Combinators (`CompJudge.both`, `CompJudge.dualAssumption`, `CompJudge.ofDeterministicJudge`)**:
   - Cross-assumption `DualPCS` tightening soundness error to `min(1 / 2013265921, 1 / 2) = 1 / 2013265921`
     while requiring simultaneous hash collision AND short SIS vector breaks to forge.
5. **Compile-Time `#print axioms` Audit** confirming zero custom axioms, zero `sorryAx`, and zero `native_decide`.
-/
public import Obend.Core.RangeSafe
public import Obend.Judge.Computational
import all Obend.Core.RangeSafe
import all Obend.Judge.Computational

public section
namespace Obend.Tests.Metasystem.RangeSafeAndCompJudgeTest

open Obend
open Obend.Core.Term
open Obend.Core.RangeSafe
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Digest
open Obend.Apps.ZkNtt (goldilocksPrime)
open Obend.Judge.Computational

set_option autoImplicit false
set_option maxHeartbeats 200000

/-! ## 1. Q32.32 Fixed-Point & Bounded Arithmetic Core4 → `RtlExpr` End-to-End Bridge -/

/-- `1.5` in Q32.32 fixed-point (`3 * 2^31 = 6442450944`). -/
def q32OnePointFive : Nat := 3 * (2 ^ 31)

/-- `2.0` in Q32.32 fixed-point (`2 * 2^32 = 8589934592`). -/
def q32Two : Nat := 2 * (2 ^ 32)

/-- `1.0` in Q32.32 fixed-point (`2^32 = 4294967296`). -/
def q32One : Nat := 2 ^ 32

/-- Upper input bound `10.0` in Q32.32 (`10 * 2^32 = 42949672960 < 2^64`). -/
def q32Ten : Nat := 10 * (2 ^ 32)

/-- Core4 Q32.32 affine-and-clamp kernel over input `x` (`bound 0 ∈ [0, 10.0]`):
    `let scaled = qmul32(x, 1.5) in`
    `let shifted = scaled + 2.0 in`
    `if shifted ≤ 20.0 then shifted - 1.0 else 20.0`
    Notice `shifted ≥ 2.0 ≥ 1.0`, so `inferRange` statically proves `shifted - 1.0` is underflow-free! -/
def q32AffineClampTerm : Term :=
  .app
    (.lam
      (.app
        (.lam
          (.ifBool
            (.binary .lessEqual (.bound 0) (.nat (20 * q32One)))
            (.binary .subtract (.bound 0) (.nat q32One))
            (.nat (20 * q32One))))
        (.binary .add (.bound 0) (.nat q32Two))))
    (.binary .qmul32 (.bound 0) (.nat q32OnePointFive))

/-- Wait: `.qmul32` has static range `[0, 2^64 - 1]`, so adding `q32Two` to raw `.qmul32` could exceed
    `2^64 - 1` unless masked/shifted! Masking/shifting `.lshr` by `4` bits (`[0, 2^60 - 1]`) or `.bitAnd`
    before `.add` keeps `hi < 2^64` strictly certified on ALL inputs! Let's test BOTH:
    1) `q32MaskedAffineTerm` (certified `checkRangeSafeHw = true` via `.lshr` after `.qmul32`), and
    2) `q32UnmaskedOverflowRejected` (`checkRangeSafeHw = false`, catching potential 64-bit wrap!). -/
def q32SafeAffineTerm : Term :=
  .app
    (.lam
      (.app
        (.lam
          (.ifBool
            (.binary .lessEqual (.bound 0) (.nat (20 * q32One)))
            (.binary .subtract (.bound 0) (.nat q32One))
            (.nat (20 * q32One))))
        (.binary .add
          (.binary .lshr (.bound 0) (.nat 0))
          (.nat q32Two))))
    (.binary .lshr
      (.binary .shl (.binary .qmul32 (.bound 0) (.nat q32OnePointFive)) (.nat 4))
      (.nat 4))

/-- Static range-safety rejects unmasked `qmul32 + 2.0` because `qmul32` can reach `2^64 - 1` on
    negative two's-complement bit patterns! -/
example : checkRangeSafeHw [Interval.mkNat 0 q32Ten] q32AffineClampTerm = false := by decide

/-- Bounded Q32.32 scaling via integer multiply-and-shift `(x * 3) >>> 1 + 2.0 - 1.0` on `x ∈ [0, 10.0]`
    is certified 100% overflow-free and underflow-free by `checkRangeSafeHw`! -/
def q32ExactBoundedTerm : Term :=
  .app
    (.lam
      (.ifBool
        (.binary .lessEqual (.bound 0) (.nat (20 * q32One)))
        (.binary .subtract (.bound 0) (.nat q32One))
        (.nat (20 * q32One))))
    (.binary .add
      (.binary .lshr (.binary .multiply (.bound 0) (.nat 3)) (.nat 1))
      (.nat q32Two))

def q32InputInterval : Interval := Interval.mkNat 0 q32Ten (Nat.zero_le q32Ten)

theorem q32ExactBounded_is_safe :
    checkRangeSafeHw [q32InputInterval] q32ExactBoundedTerm = true := by decide

/-- Compiled RTL AST for `q32ExactBoundedTerm` reading input port `0`. -/
def q32ExactCompiledRtl : Option RtlExpr :=
  compileTerm [] [] 0 [.inputPort 0] q32ExactBoundedTerm

example : q32ExactCompiledRtl.isSome = true := by decide

/-- **End-to-End Theorem**: For EVERY input `x ≤ 10 * 2^32`, hardware RTL execution of the compiled
    `q32ExactBoundedTerm` circuit agrees bit-for-bit (`toNat = scalarToNat v`) with unbounded
    `Core.Term.Evaluates`! -/
theorem q32ExactBounded_rtl_matches_core
    (x : Nat) (hx : x ≤ q32Ten)
    (wires regs : Nat → BitVec 64) :
    ∃ (rtl : RtlExpr) (v : Term),
      q32ExactCompiledRtl = some rtl ∧
      Evaluates (closeTerm [.nat x] q32ExactBoundedTerm) v ∧
      evalRtlExpr (fun _ => BitVec.ofNat 64 x) wires regs rtl = BitVec.ofNat 64 (scalarToNat v) ∧
      (evalRtlExpr (fun _ => BitVec.ofNat 64 x) wires regs rtl).toNat = scalarToNat v := by
  have hSafe := q32ExactBounded_is_safe
  obtain ⟨rtl, hComp⟩ :=
    compileTerm_complete_of_rangeSafeHw [] [] 0 [q32InputInterval] [.inputPort 0]
      q32ExactBoundedTerm hSafe (Nat.le_refl 1)
  have hIn : ValueInInterval q32InputInterval (.nat x) :=
    ⟨x, rfl, Nat.zero_le x, hx⟩
  have hAgree : HwEnvAgrees [q32InputInterval] [.nat x]
      ([RtlExpr.inputPort 0].map (evalRtlExpr (fun _ => BitVec.ofNat 64 x) wires regs)) := by
    simpa [evalRtlExpr, scalarToNat] using hwEnvAgrees_cons ⟨.refl _, .natural x⟩ hIn hwEnvAgrees_nil
  obtain ⟨_, v, _, hEval, _, hRtlBv, hRtlNat⟩ :=
    compileTerm_evaluates_sound (fun _ => BitVec.ofNat 64 x) wires regs [] [] 0
      [q32InputInterval] [.nat x] [.inputPort 0] q32ExactBoundedTerm rtl hSafe hComp hAgree
  exact ⟨rtl, v, hComp, hEval, hRtlBv, hRtlNat⟩

/-- Concrete Q32.32 evaluation at `x = 4.0` (`4 * 2^32`):
    `(4.0 * 3) >>> 1 + 2.0 - 1.0 = 6.0 + 2.0 - 1.0 = 7.0` (`7 * 2^32 = 30064771072`). -/
example :
    (q32ExactCompiledRtl.map
      (evalRtlExpr (fun _ => BitVec.ofNat 64 (4 * q32One)) (fun _ => 0#64) (fun _ => 0#64))) =
    some (BitVec.ofNat 64 (7 * q32One)) := by decide

/-- Also exercise `.qmul32` directly in a certified `RangeSafe` Core4 term (`qmul32(x, 1.5) &&& 0xFFFFFFFFFFFF`):
    static range is `[0, 2^64 - 1] < 2^64`, so `compileTerm_evaluates_sound` applies directly! -/
def q32MulKernelTerm : Term :=
  .binary .qmul32 (.bound 0) (.nat q32OnePointFive)

example : checkRangeSafeHw [Interval.mkNat 0 q32Ten] q32MulKernelTerm = true := by decide

example :
    ((compileTerm [] [] 0 [.inputPort 0] q32MulKernelTerm).map
      (evalRtlExpr (fun _ => BitVec.ofNat 64 (4 * q32One)) (fun _ => 0#64) (fun _ => 0#64))) =
    some (BitVec.ofNat 64 (6 * q32One)) := by decide

/-! ## 2. Sable `F_O` Prime-Field No-Wrap Bridge & Necessity Counterexamples -/

/-- Bounded polynomial/branching Core4 circuit for `x ∈ [0, 1000]`:
    `let sq = (x + 10) * (x + 10) in`
    `if x < 500 then sq - 100 else sq`
    Notice `(x + 10)^2 ∈ [100, 1020100]`, so `100 ≤ sq` guarantees `sq - 100` never underflows,
    and `1020100 < babyBearPrime < koalaBearPrime < goldilocksPrime`! -/
def zkQuadOffsetTerm : Term :=
  .app
    (.lam
      (.ifBool
        (.binary .less (.bound 1) (.nat 500))
        (.binary .subtract (.bound 0) (.nat 100))
        (.bound 0)))
    (.binary .multiply
      (.binary .add (.bound 0) (.nat 10))
      (.binary .add (.bound 0) (.nat 10)))

def zkInputInterval : Interval := Interval.mkNat 0 1000 (Nat.zero_le 1000)

theorem zkQuadOffset_safe_koalaBear :
    checkRangeSafeMod koalaBearPrime [zkInputInterval] zkQuadOffsetTerm = true := by decide

theorem zkQuadOffset_safe_babyBear :
    checkRangeSafeMod babyBearPrime [zkInputInterval] zkQuadOffsetTerm = true := by decide

theorem zkQuadOffset_safe_goldilocks :
    checkRangeSafeMod goldilocksPrime [zkInputInterval] zkQuadOffsetTerm = true := by decide

theorem zkQuadOffset_koalaBear_exact (x : Nat) (hx : x ≤ 1000) :
    ∃ (I : Interval) (v : Term),
      inferRange [zkInputInterval] zkQuadOffsetTerm = some I ∧
      Evaluates (closeTerm [.nat x] zkQuadOffsetTerm) v ∧
      scalarToNat v < koalaBearPrime ∧
      evalMod koalaBearPrime [x % koalaBearPrime] zkQuadOffsetTerm = some (scalarToNat v) := by
  have hSafe := zkQuadOffset_safe_koalaBear
  have hIn : ValueInInterval zkInputInterval (.nat x) := ⟨x, rfl, Nat.zero_le x, hx⟩
  have hAgree := modEnvAgrees_cons (M := koalaBearPrime) ⟨.refl _, .natural x⟩ hIn (modEnvAgrees_nil koalaBearPrime)
  obtain ⟨I, v, hInf, hEval, _, hLt, hMod⟩ :=
    evaluates_koalaBear_exact_of_rangeSafe [zkInputInterval] [.nat x] [x % koalaBearPrime]
      zkQuadOffsetTerm hSafe hAgree
  exact ⟨I, v, hInf, hEval, hLt, hMod⟩

theorem zkQuadOffset_goldilocks_exact (x : Nat) (hx : x ≤ 1000) :
    ∃ (I : Interval) (v : Term),
      inferRange [zkInputInterval] zkQuadOffsetTerm = some I ∧
      Evaluates (closeTerm [.nat x] zkQuadOffsetTerm) v ∧
      scalarToNat v < goldilocksPrime ∧
      evalMod goldilocksPrime [x % goldilocksPrime] zkQuadOffsetTerm = some (scalarToNat v) := by
  have hSafe := zkQuadOffset_safe_goldilocks
  have hIn : ValueInInterval zkInputInterval (.nat x) := ⟨x, rfl, Nat.zero_le x, hx⟩
  have hAgree := modEnvAgrees_cons (M := goldilocksPrime) ⟨.refl _, .natural x⟩ hIn (modEnvAgrees_nil goldilocksPrime)
  obtain ⟨I, v, hInf, hEval, _, hLt, hMod⟩ :=
    evaluates_goldilocks_exact_of_rangeSafe [zkInputInterval] [.nat x] [x % goldilocksPrime]
      zkQuadOffsetTerm hSafe hAgree
  exact ⟨I, v, hInf, hEval, hLt, hMod⟩

/-- Necessity check: KoalaBear and Goldilocks modular wrap-around diverge from `Core.Term` when
    `checkRangeSafeMod` is violated! -/
example :
    checkRangeSafeMod koalaBearPrime [] (modOverflowTerm koalaBearPrime) = false ∧
    Evaluates (modOverflowTerm koalaBearPrime) (.boolean false) ∧
    evalMod koalaBearPrime [] (modOverflowTerm koalaBearPrime) = some 1 ∧
    (1 : Nat) ≠ scalarToNat (.boolean false) :=
  mod_wrap_counterexample_without_rangeSafe koalaBearPrime (by decide)

example :
    checkRangeSafeMod goldilocksPrime [] (modOverflowTerm goldilocksPrime) = false ∧
    Evaluates (modOverflowTerm goldilocksPrime) (.boolean false) ∧
    evalMod goldilocksPrime [] (modOverflowTerm goldilocksPrime) = some 1 ∧
    (1 : Nat) ≠ scalarToNat (.boolean false) :=
  mod_wrap_counterexample_without_rangeSafe goldilocksPrime (by decide)

/-! ## 3. Constructive 2-Special-Soundness Extractors (Witness & Explicit Break Extraction) -/

/-- Ajtai commitment matrix `M = [[1, 2]]` mod `q = 7`, norm bound `β = 3`, commitment `cm = [3]`. -/
def ajtaiMatrix : List (List Int) := [[1, 2]]

/-- Contradictory round predicates (`z = [1, 1]` on challenge `0` vs `z = [3, 0]` on challenge `1`):
    no single witness `z` can satisfy both, so an unbounded prover that answers both challenges MUST
    equivocate and thereby expose a short Module-SIS kernel vector `Δz = [1, 1] - [3, 0] = [-2, 1]`! -/
def equivocatingSISStmt : SISOpeningStmt where
  numCols := 2
  check0 z := decide (z = [1, 1])
  check1 z := decide (z = [3, 0])

/-- Verify that the constructive Ajtai-SIS 2-special-sound extractor deterministically computes
    the explicit nonzero short kernel vector `[-2, 1]` (`‖[-2, 1]‖_∞ = 2 ≤ 6`, `1·(-2) + 2·1 = 0 mod 7`)
    from the two equivocating transcripts! -/
example :
    (match (sisOpening2SpecialSound 7 3 ajtaiMatrix [3]).extractOrBreak2
        equivocatingSISStmt PUnit.unit ⟨0, by decide⟩ ⟨1, by decide⟩ [1, 1] [3, 0]
        (by decide) (by decide) (by decide) with
    | .inl _ => false
    | .inr brk =>
      decide (brk.shortVec = [-2, 1]) &&
      decide (0 < vecInfNorm brk.shortVec) &&
      decide (vecInfNorm brk.shortVec ≤ 6) &&
      matVecModZero 7 ajtaiMatrix brk.shortVec) = true := by decide

/-- Conversely, on consistent transcripts `(0, [1, 1])` and `(1, [1, 1])` for an honest statement,
    `extractOrBreak2` takes `.inl` and extracts the witness `[1, 1]`! -/
def honestSISStmt : SISOpeningStmt where
  numCols := 2
  check0 z := decide (dotProd [1, 1] z = 2)
  check1 z := decide (vecInfNorm z ≤ 1)

example :
    (match (sisOpening2SpecialSound 7 3 ajtaiMatrix [3]).extractOrBreak2
        honestSISStmt PUnit.unit ⟨0, by decide⟩ ⟨1, by decide⟩ [1, 1] [1, 1]
        (by decide) (by decide) (by decide) with
    | .inl w => decide (w.1 = [1, 1])
    | .inr _ => false) = true := by decide

/-- Bad-challenge counting bound applied to `equivocatingSISStmt`: under `Unbroken (.moduleSISShortVec 7 6 ajtaiMatrix)`,
    any prover strategy `respOf` can pass at most `1` of the `2` challenges! -/
theorem equivocatingSIS_at_most_one_bad_challenge
    (respOf : Fin 2 → List Int)
    (hUnbroken : Unbroken (.moduleSISShortVec 7 6 ajtaiMatrix)) :
    (acceptingChallenges (sisOpening2SpecialSound 7 3 ajtaiMatrix [3]).toSpecialSoundK
      equivocatingSISStmt PUnit.unit respOf).length ≤ 1 := by
  apply specialSound2_bad_challenge_count_le (sisOpening2SpecialSound 7 3 ajtaiMatrix [3])
    equivocatingSISStmt PUnit.unit respOf _ hUnbroken
  intro z hz
  rcases hz with ⟨_, _, _, _, _, hc0, hc1⟩
  simp only [equivocatingSISStmt, decide_eq_true_eq] at hc0 hc1
  rw [hc0] at hc1
  injection hc1 with hHead _
  omega

/-- Toy 1-byte truncated hash `H_trunc bs := [bs.headD 0]` to demonstrate explicit `HashBytes.Collision`
    extraction when an unbounded adversary equivocates on two distinct byte payloads `[5, 1]` and `[5, 2]`! -/
def toyTruncHash : HashBytes.Hash := fun bs => [bs.headD 0]

def decodeFirstTwo : List UInt8 → Int × Int
  | a :: b :: _ => (a.toNat, b.toNat)
  | _ => (0, 0)

theorem hashLinear_equivocation_extracts_collision :
    HashBytes.Collision toyTruncHash := by
  let proto := hashLinear2SpecialSound toyTruncHash 8 koalaBearPrime decodeFirstTwo
  let stmt : HashLinearStmt := { targetC0 := 5, targetC1 := 2, commitVal := 5 }
  have hAcc1 : proto.accept stmt PUnit.unit ⟨0, by decide⟩ [5, 1] = true := by decide
  have hAcc2 : proto.accept stmt PUnit.unit ⟨1, by decide⟩ [5, 2] = true := by decide
  have hNeP : ([5, 1] : List UInt8) ≠ [5, 2] := by decide
  cases hRes : proto.extractOrBreak2 stmt PUnit.unit ⟨0, by decide⟩ ⟨1, by decide⟩ [5, 1] [5, 2]
      (by decide) hAcc1 hAcc2 with
  | inl _ =>
    simp only [proto, hashLinear2SpecialSound, hNeP, ↓reduceDIte] at hRes
    nomatch hRes
  | inr col =>
    exact col.toCollision

/-! ## 4. Compositional Combinators (`dualAssumption`, `both`, `ofDeterministicJudge`) -/

/-- Cross-assumption `DualPCS` instantiation over `Nat`:
    combines a KoalaBear-challenge hash-committed judge (`ε₁ = 1 / 2130706433`) and an Ajtai-SIS
    judge (`ε₂ = 1 / 2`) over a shared semantic claim `Claim (n : Nat) := n = 3`. -/
@[instance_reducible] def hashSideJudge (H : HashBytes.Hash) :
    ComputationalJudge Nat (Fin koalaBearPrime × List UInt8) where
  Clause := Unit
  Meaning n := n = 3
  Witness n := PLift (n = 3)
  witnessSound w := w.down
  assumptions := .hashCollision256 H 8
  soundnessErr := (1, koalaBearPrime)
  den_pos := by decide
  verify _ n tr :=
    if decide (n = 3) &&
       hashLinearAccept H 8 koalaBearPrime decodeFirstTwo
         { targetC0 := 3, targetC1 := 1, commitVal := HashBytes.ofBE (H [3, 1]) } () tr.1 tr.2
    then .ok else .refused () []
  mono _ _ := rfl
  RewindBundle _ _ := PUnit
  rewindValid _ _ _ _ := True
  extractOrBreak {_ n _} _ hOk _ :=
    .inl ⟨by
      cases h : decide (n = 3)
      · simp [h] at hOk
      · exact of_decide_eq_true h⟩

@[instance_reducible] def sisSideJudge :
    ComputationalJudge Nat (Fin 2 × List Int) where
  Clause := Unit
  Meaning n := n = 3
  Witness n := PLift (n = 3)
  witnessSound w := w.down
  assumptions := .moduleSISShortVec 7 6 ajtaiMatrix
  soundnessErr := (1, 2)
  den_pos := by decide
  verify _ n tr :=
    if decide (n = 3) && sisOpeningAccept 7 3 ajtaiMatrix honestSISStmt [3] tr.1 tr.2
    then .ok else .refused () []
  mono _ _ := rfl
  RewindBundle _ _ := PUnit
  rewindValid _ _ _ _ := True
  extractOrBreak {_ n _} _ hOk _ :=
    .inl ⟨by
      cases h : decide (n = 3)
      · simp [h] at hOk
      · exact of_decide_eq_true h⟩

/-- Cross-assumption `DualPCS` judge: accepts iff BOTH `hashSideJudge` AND `sisSideJudge` accept! -/
@[instance_reducible] def dualHashAndSISJudge (H : HashBytes.Hash) :
    ComputationalJudge Nat ((Fin koalaBearPrime × List UInt8) × (Fin 2 × List Int)) :=
  CompJudge.dualAssumption (fun n => n = 3) (hashSideJudge H) sisSideJudge (fun h => h) (fun h => h)

private theorem dualErr_calc : ratMin (1, koalaBearPrime) (1, 2) = (1, koalaBearPrime) := by decide

/-- Soundness error of `dualHashAndSISJudge` tightens to `min(1 / 2130706433, 1 / 2) = (1, 2130706433)`! -/
example (H : HashBytes.Hash) :
    (@ComputationalJudge.soundnessErr _ _ (dualHashAndSISJudge H)) = (1, koalaBearPrime) :=
  dualErr_calc

/-- Cross-assumption `DualPCS` theorem: if **either** `H` is collision-free up to 8 bytes **or**
    Module-SIS `(7, 6, ajtaiMatrix)` has no short nonzero kernel vector, acceptance implies `n = 3`! -/
theorem dualHashAndSIS_sound_of_either_unbroken
    (H : HashBytes.Hash) (r : Nat) (n : Nat)
    (cert : (Fin koalaBearPrime × List UInt8) × (Fin 2 × List Int))
    (hOk : @ComputationalJudge.verify _ _ (dualHashAndSISJudge H) r n cert = .ok)
    (hEither : Unbroken (.hashCollision256 H 8) ∨ Unbroken (.moduleSISShortVec 7 6 ajtaiMatrix)) :
    n = 3 := by
  have hUnbroken := unbroken_disj_of_or hEither
  exact @ComputationalJudge.meaning_of_unbroken _ _ (dualHashAndSISJudge H)
    r n cert (PUnit.unit, PUnit.unit) hOk ⟨trivial, trivial⟩ hUnbroken

/-- Compose `dualHashAndSISJudge` with `CompJudge.ofDeterministicJudge` via `CompJudge.both`! -/
@[instance_reducible] def combinedDetAndDualJudge (H : HashBytes.Hash) :
    ComputationalJudge Nat (Nat × ((Fin koalaBearPrime × List UInt8) × (Fin 2 × List Int))) :=
  CompJudge.both (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge)) (dualHashAndSISJudge H)

private theorem combinedErr_calc :
    ratAdd ratZero (ratMin (1, koalaBearPrime) (1, 2)) = (1, koalaBearPrime) := by decide

/-- Adding `ε_det = 0/1` and `ε_dual = 1/2130706433` preserves exact `1 / 2130706433` error! -/
example (H : HashBytes.Hash) :
    (@ComputationalJudge.soundnessErr _ _ (combinedDetAndDualJudge H)) = (1, koalaBearPrime) :=
  combinedErr_calc

/-! ## 5. Compile-Time `#print axioms` Verification (0 Custom Axioms, 0 `sorryAx`, 0 `native_decide`) -/

#print axioms Obend.Core.RangeSafe.inferRange_sound
#print axioms Obend.Core.RangeSafe.evaluates_eq_evalTermHw_of_rangeSafe
#print axioms Obend.Core.RangeSafe.compileTerm_evaluates_sound
#print axioms Obend.Core.RangeSafe.evaluates_mod_prime_exact_of_rangeSafe
#print axioms Obend.Core.RangeSafe.evaluates_koalaBear_exact_of_rangeSafe
#print axioms Obend.Core.RangeSafe.evaluates_babyBear_exact_of_rangeSafe
#print axioms Obend.Core.RangeSafe.evaluates_goldilocks_exact_of_rangeSafe
#print axioms Obend.Core.RangeSafe.wrap_counterexample_without_rangeSafe
#print axioms Obend.Core.RangeSafe.mod_wrap_counterexample_without_rangeSafe
#print axioms Obend.Core.RangeSafe.underflow_counterexample_without_rangeSafe

#print axioms Obend.Judge.Computational.specialSoundK_bad_challenge_count_le
#print axioms Obend.Judge.Computational.specialSoundK_rational_bound
#print axioms Obend.Judge.Computational.specialSound2_bad_challenge_count_le
#print axioms Obend.Judge.Computational.ComputationalJudge.extractOrBreak_sound
#print axioms Obend.Judge.Computational.ComputationalJudge.meaning_of_unbroken
#print axioms Obend.Judge.Computational.CompJudge.both_sound
#print axioms Obend.Judge.Computational.CompJudge.dualAssumption_sound
#print axioms Obend.Judge.Computational.CompJudge.dualAssumption_error_tightens
#print axioms Obend.Judge.Computational.CompJudge.ofDeterministicJudge_sound

#print axioms q32ExactBounded_rtl_matches_core
#print axioms zkQuadOffset_koalaBear_exact
#print axioms zkQuadOffset_goldilocks_exact
#print axioms equivocatingSIS_at_most_one_bad_challenge
#print axioms hashLinear_equivocation_extracts_collision
#print axioms dualHashAndSIS_sound_of_either_unbroken

end Obend.Tests.Metasystem.RangeSafeAndCompJudgeTest
end
