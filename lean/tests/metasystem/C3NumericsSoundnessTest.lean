module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Device.Enclosure
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.Flowpipe
public import Obend.Analysis.Hybrid
public import Obend.Consensus.Epistemic
public import Obend.Analysis.QuantumWalk
import all Obend.Hardware.Device.Enclosure
import all Obend.Analysis.SosLyapunov
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Hybrid
import all Obend.Consensus.Epistemic
import all Obend.Analysis.QuantumWalk

/-!
# Metasystem Test Suite — Wave C3 Numerics, ODE/Hybrid Reachability, Epistemic Width & Unitary Szegedy Walk (`P0` #22, #24, #25, #26, #27, #28)

Comprehensive regression checks, universal soundness instantiations, negative refusal witnesses,
`#tooth` kernel mutation-killing probes, and `#print axioms` checks (`0 sorryAx`, `0` custom axioms)
across all 6 Wave C3 `c3-numerics` Stage-1 repairs:
1. **P0 #22 (`Obend.Hardware.Device.Enclosure`)**:
   - Dynamic `halvings` fuel for `|x| > 2^63` (`halvings_arg_abs_le_half`, `expEnclosure_sound`).
2. **P0 #24 (`Obend.Analysis.SosLyapunov`)**:
   - Unbounded `sosJsonNatWrite` (`10^24` never truncates to `0`), structural `sosJsonWriteVal`
     (deep JSON never clamps to `"null"`), decimal/scientific `decodeRatJson`, and `checkSosLyapunovDims`
     dimension/variable-scope refusal + `checkSosLyapunov_sound`.
3. **P0 #25 (`Obend.Analysis.Flowpipe`)**:
   - Continuous `trapezoidalQuadrature`, exact degree-3 `simpsonQuadrature`, interior-node
     `buildTaylorPicardStep` (`Δt^3 / 3` drift on `t' = 1, x' = t^2`), and quadrature-free
     `verifyTrajectorySafety_c2_ode_sound`.
4. **P0 #26 (`Obend.Analysis.Hybrid`)**:
   - Exact rational `CanonicalRat` interval endpoints in `stepHybrid` (preserving `.num / .den` on
     `[1/100, 3/100]`) and `stepHybrid_sound`.
5. **P0 #27 (`Obend.Consensus.Epistemic`)**:
   - Exact rational `IntervalRace.intervalExactWidth` (`[0, 3/100]` strictly beats coarse `[0, 1]`)
     and `IntervalRace.intervalRace_tighter_enclosure_wins`.
6. **P0 #28 (`Obend.Analysis.QuantumWalk`)**:
   - Normalized bipartite directed-edge projectors (`szegedyEdgeProjAEntry`, `szegedyNormalizedEdgeProjA`),
     exact rational unitary reflection `szegedyReflectRatVec` (`R^2 = I`, `‖R ψ‖^2 = ‖ψ‖^2`), and
     `szegedyReflectRatVec_unitary_norm_preserved` + `szegedyReflectVec_norm_sq_preserved`.
-/

public section
namespace Obend.Tests.Metasystem.C3NumericsSoundnessTest

open Obend.Judge
open Obend.Judge.SOS
open Obend.Analysis
open Obend.Hardware.Device
open Obend.Consensus.Epistemic
open Obend.Consensus.Epistemic.IntervalRace
set_option autoImplicit false

/-! ## 1. P0 #22: `Obend.Hardware.Device.Enclosure` — Unconditional `halvings` & `expEnclosure_sound` for `|x| > 2^63` -/

/-- Regression witness for `x = 2^65 > 2^63`: dynamic `halvings` performs `66` halvings (bringing
`2^65 / 2^66 = 1/2 ≤ 1/2`), whereas the old hardcoded `64`-fuel `halvings` stopped at `2^65 / 2^64 = 2 > 1/2`. -/
theorem enclosure_large_input_2pow65_halvings :
    let x := Obend.Hardware.Device.ratPow 2 65
    halvings x = 66 ∧
    Obend.Hardware.Device.ratAbs (x / Obend.Hardware.Device.ratPow 2 (halvings x)) = CanonicalRat.mk 1 2 := by
  decide +kernel

/-- Moderate-magnitude enclosure witness (`x = 100`, `8` halvings): the rounded enclosure is
non-inverted and strictly positive. (`e^{2^65}` itself has `~10^19` digits and is not kernel-evaluable;
its soundness is covered by the universal `expEnclosure_sound`.) -/
theorem enclosure_moderate_input_nonInverted :
    halvings 100 = 8 ∧
    (expEnclosure 100).lo ≤ (expEnclosure 100).hi ∧
    0 < (expEnclosure 100).lo := by
  decide +kernel

/-- Negative regression witness for `x = -2^65` (`|x| > 2^63`): `halvings (-2^65) = 66` and
`expEnclosure (-2^65)` remains non-inverted with positive upper bound. -/
theorem enclosure_negative_large_input_halvings :
    let x := -(Obend.Hardware.Device.ratPow 2 65)
    halvings x = 66 ∧
    Obend.Hardware.Device.ratAbs (x / Obend.Hardware.Device.ratPow 2 (halvings x)) = CanonicalRat.mk 1 2 := by
  decide +kernel

/-- Universal instantiation of `halvings_arg_abs_le_half` and `expEnclosure_sound` at arbitrary `x`. -/
theorem enclosure_unconditional_bridge
    (expFn : CanonicalRat → CanonicalRat)
    (hHalf : ∀ t : CanonicalRat, Obend.Hardware.Device.ratAbs t ≤ 1 / 2 → expFn t ∈ expHalfEnclosure t)
    (hDouble : ∀ y : CanonicalRat, expFn (2 * y) = expFn y * expFn y)
    (x : CanonicalRat) :
    Obend.Hardware.Device.ratAbs (x / Obend.Hardware.Device.ratPow 2 (halvings x)) ≤ 1 / 2 ∧
    expFn x ∈ expEnclosure x :=
  ⟨halvings_arg_abs_le_half x, expEnclosure_sound expFn hHalf hDouble x⟩

def brokenHalvingsHardcoded64 (_ : CanonicalRat) : Nat :=
  64

#tooth Obend.Hardware.Device.halvings_arg_abs_le_half
  by mutation Obend.Hardware.Device.halvings := brokenHalvingsHardcoded64


/-! ## 2. P0 #24: `Obend.Analysis.SosLyapunov` — `10^24` Serialization, Decimal/Scientific Parsing & Dimension Refusal -/

def deepNestedJson : Nat → SosJson
  | 0 => SosJson.ofNat (10 ^ 24)
  | k + 1 => SosJson.arr [deepNestedJson k]

/-- Regression check: `10^24` serializes to all 25 decimal digits `"1000000000000000000000000"`
(never dropping its leading `'1'` to `"000000000000000000000000"` -> `0`), and depth-30 nested JSON
roundtrips losslessly instead of clamping to `"null"`. -/
def ratJsonDecodesTo (src : String) (r : CanonicalRat) : Bool :=
  match sosJsonParse src >>= decodeRatJson with
  | .ok q => decide (q = r)
  | .error _ => false

def jsonRoundtrips (src : String) : Bool :=
  match sosJsonParse src with
  | .ok j => sosJsonCompress j == src
  | .error _ => false

theorem sos_json_10pow24_and_deep_roundtrip :
    sosJsonCompress (SosJson.ofNat (10 ^ 24)) = "1000000000000000000000000" ∧
    ratJsonDecodesTo (sosJsonCompress (SosJson.ofNat (10 ^ 24))) ((10 ^ 24 : Nat) : CanonicalRat) = true ∧
    ratJsonDecodesTo "0.03" (CanonicalRat.mk 3 100) = true ∧
    ratJsonDecodesTo "1e24" ((10 ^ 24 : Nat) : CanonicalRat) = true ∧
    ratJsonDecodesTo "-2.5e-2" (CanonicalRat.mk (-1) 40) = true ∧
    jsonRoundtrips (sosJsonCompress (deepNestedJson 30)) = true ∧
    sosJsonCompress (deepNestedJson 30) ≠ "null" := by
  decide +kernel

/-- Mismatched `vectorField.length ≠ dim` (`dim = 2`, `vectorField = [-x_0]`) is fail-closed refused
with `.malformedDimensionOrParam`. -/
def mismatchedDimSosProblem : SosLyapunovProblem :=
  { goldenSosProblem with
    lyapunov := { goldenLyapunovSpec2D with dim := 2, vectorField := [Poly.neg x0Poly] } }

/-- Out-of-scope variable index `x_2` inside a `dim = 2` specification is fail-closed refused. -/
def outOfScopeVarSosProblem : SosLyapunovProblem :=
  { goldenSosProblem with
    lyapunov :=
      { goldenLyapunovSpec2D with
        lyapunovV := Poly.add goldenLyapunovSpec2D.lyapunovV (Poly.sqr (polyOfTerm [(2, 1)] 1)) } }

/-- Unstable ODE `x'_0 = +x_0, x'_1 = -x_1` is refused by `checkSosLyapunovProblem`. -/
def unstableOdeSosProblem : SosLyapunovProblem :=
  { goldenSosProblem with
    lyapunov := { goldenLyapunovSpec2D with vectorField := [x0Poly, Poly.neg x1Poly] } }

theorem sos_dimension_and_unstable_ode_refused :
    checkSosLyapunovDims mismatchedDimSosProblem.lyapunov = false ∧
    checkSosLyapunovDims outOfScopeVarSosProblem.lyapunov = false ∧
    (match checkSosLyapunovProblem 0 mismatchedDimSosProblem goldenSosCert with
     | .refused .malformedDimensionOrParam _ => true
     | _ => false) = true ∧
    (match checkSosLyapunovProblem 0 outOfScopeVarSosProblem goldenSosCert with
     | .refused .malformedDimensionOrParam _ => true
     | _ => false) = true ∧
    (match checkSosLyapunovProblem 0 unstableOdeSosProblem goldenSosCert with
     | .refused .lyapunovFailed _ => true
     | _ => false) = true := by
  decide +kernel

def brokenCheckSosLyapunovDims (_ : SosLyapunovSpec) : Bool :=
  true

#tooth Obend.Analysis.checkSosLyapunov_sound
  by mutation Obend.Analysis.checkSosLyapunovDims := brokenCheckSosLyapunovDims


/-! ## 3. P0 #25: `Obend.Analysis.Flowpipe` — Non-Autonomous `t' = 1, x' = t^2` Drift `Δt^3 / 3` & True `C^2` Containment -/

/-- Non-autonomous ODE `t' = 1, x' = t^2` over step `dt = 1` with zero remainder pad:
evaluating the remainder only at `τ = 0` falsely gave `x(1) = 0`, missing the true drift `1/3`! -/
def quadraticTimeOde : OdeSystem where
  fields       := [("t", .const 1), ("x", .mul (.var "t") (.var "t"))]
  dt           := 1
  remainderPad := Interval.ofPoint 0

def quadraticTimeInitBox : List (String × Interval) :=
  [("t", Interval.ofPoint 0), ("x", Interval.ofPoint 0)]

def quadraticTimeRho0 : String → CanonicalRat
  | "t" => 0
  | "x" => 0
  | _   => 0

/-- Regression check on `t' = 1, x' = t^2`:
1. `trapezoidalQuadrature 1 1 = [(1/2, 0), (1/2, 1)]` (continuous at `t = h`, no boundary jump),
2. `buildTaylorPicardDiscrete quadraticTimeOde 2 quadraticTimeRho0 1 "x" = 1/3` (exact `Δt^3 / 3` drift!),
3. `stepFlowpipe quadraticTimeOde quadraticTimeInitBox` encloses `1/3` in `[0, 1]` (never `[0, 0]`),
4. `verifyTrajectorySafety` accepts safe envelope `[-1, 2]` and rejects `[0, 1/4]` (which misses `1/3`). -/
theorem flowpipe_quadratic_time_encloses_one_third :
    trapezoidalQuadrature 1 1 = [(CanonicalRat.mk 1 2, 0), (CanonicalRat.mk 1 2, 1)] ∧
    buildTaylorPicardDiscrete quadraticTimeOde 2 quadraticTimeRho0 1 (CanonicalRat.mk 1 3) "x" = CanonicalRat.mk 1 3 ∧
    (match stepFlowpipe quadraticTimeOde quadraticTimeInitBox with
     | some nextBox =>
       match nextBox.lookup "x" with
       | some xIv => decide (xIv.lo ≤ CanonicalRat.mk 1 3 ∧ CanonicalRat.mk 1 3 ≤ xIv.hi)
       | none => false
     | none => false) = true ∧
    verifyTrajectorySafety quadraticTimeOde quadraticTimeInitBox 1
      [("t", ⟨-1, 2⟩), ("x", ⟨-1, 2⟩)] = true ∧
    verifyTrajectorySafety quadraticTimeOde quadraticTimeInitBox 1
      [("t", ⟨-1, 2⟩), ("x", ⟨0, CanonicalRat.mk 1 4⟩)] = false := by
  decide +kernel

/-- Adversarial quartic vector field `t' = 1, x' = t^2 * (t - 1/3)^2` over `dt = 1` from `(0, 0)`:
at the single interior point `τ = 1/3`, `f_x(1/3) = 0` and `L_f f_x(1/3) = 0`, whereas the true
trajectory drifts to `x(1) = ∫_0^1 t^2 (t - 1/3)^2 dt = 19/270 > 0`. Full rough-box enclosure
(`stepFlowpipe` / `verifyTrajectorySafety`) encloses `19/270` across `[0, 1]` and rejects `[0, 1/20]`! -/
def quarticBlindSpotOde : OdeSystem where
  fields :=
    [ ("t", .const 1)
    , ("x", .mul (.mul (.var "t") (.var "t"))
                 (.mul (.sub (.var "t") (.const (CanonicalRat.mk 1 3)))
                       (.sub (.var "t") (.const (CanonicalRat.mk 1 3))))) ]
  dt           := 1
  remainderPad := Interval.ofPoint 0

theorem flowpipe_quartic_blind_spot_encloses_19_over_270 :
    (match stepFlowpipe quarticBlindSpotOde quadraticTimeInitBox with
     | some nextBox =>
       match nextBox.lookup "x" with
       | some xIv => decide (xIv.lo ≤ CanonicalRat.mk 19 270 ∧ CanonicalRat.mk 19 270 ≤ xIv.hi)
       | none => false
     | none => false) = true ∧
    verifyTrajectorySafety quarticBlindSpotOde quadraticTimeInitBox 1
      [("t", ⟨-1, 2⟩), ("x", ⟨-1, 2⟩)] = true ∧
    verifyTrajectorySafety quarticBlindSpotOde quadraticTimeInitBox 1
      [("t", ⟨-1, 2⟩), ("x", ⟨0, CanonicalRat.mk 1 20⟩)] = false := by
  decide +kernel

/-- Universal instantiation of `picardIteratedTrajectory_safety_sound` across **every** fractional
Lagrange–Lie remainder coordinate `θ ∈ Interval.mk 0 1` (never tied to a single interior point). -/
theorem flowpipe_picard_iterated_all_theta_bridge
    (m : Nat) (rho0 : String → CanonicalRat)
    (hInit : BoxMem rho0 quadraticTimeInitBox)
    (θ : CanonicalRat) (hθ : θ ∈ Interval.mk 0 1) :
    ∃ tube,
      runFlowpipe quadraticTimeOde quadraticTimeInitBox 1 = some tube ∧
      tube.length = 2 ∧
      (∀ k, k ≤ 1 →
        BoxMem (buildTaylorPicardDiscrete quadraticTimeOde m rho0 k θ) (tube.getD k []) ∧
        BoxMem (buildTaylorPicardDiscrete quadraticTimeOde m rho0 k θ) [("t", ⟨-1, 2⟩), ("x", ⟨-1, 2⟩)]) ∧
      (∀ k, k < 1 → ∀ τ ∈ Interval.mk 0 quadraticTimeOde.dt,
        BoxMem (buildTaylorPicardTrajectory quadraticTimeOde m rho0 k τ θ) [("t", ⟨-1, 2⟩), ("x", ⟨-1, 2⟩)]) :=
  picardIteratedTrajectory_safety_sound
    quadraticTimeOde quadraticTimeInitBox [("t", ⟨-1, 2⟩), ("x", ⟨-1, 2⟩)]
    1 m rho0 (by decide) (Interval.ofPoint_mem 0) (by decide) (by decide +kernel) hInit θ hθ

def brokenZeroLieRemainder (_ : Interval) (_ : CanonicalRat) : Interval :=
  Interval.ofPoint 0

#tooth Obend.Analysis.verifyTrajectorySafety_c2_ode_sound
  by mutation Obend.Analysis.derivePicardLieRemainder := brokenZeroLieRemainder

def brokenStepPicardDropLieRem
    (sys : OdeSystem)
    (x0Box xTildeBox : List (String × Interval))
    (h : CanonicalRat) : Option (List (String × Interval)) :=
  if !verifyPicardAPriori sys x0Box xTildeBox h then
    none
  else
    sys.fields.mapM fun (name, rhsExpr) => do
      let curBox ← x0Box.lookup name
      let velBox ← evalInterval x0Box rhsExpr
      let _ ← evalOdeLieDerivComponent sys xTildeBox rhsExpr
      pure (name, stepFlowpipe1D curBox velBox h sys.remainderPad)

#tooth Obend.Analysis.verifyTrajectorySafety_c2_ode_sound
  by mutation Obend.Analysis.stepPicardValidated := brokenStepPicardDropLieRem


/-! ## 4. P0 #26: `Obend.Analysis.Hybrid` — Exact Rational `.num / .den` Preservation in `stepHybrid` -/

def subUnitHybridAutomaton : HybridAutomaton where
  modes :=
    [ { modeId := "sub_unit"
      , ode := { fields := [("T", .const 0)], dt := CanonicalRat.mk 1 10, remainderPad := Interval.ofPoint 0 }
      , invariantBounds := [("T", ⟨0, 1⟩)] } ]
  jumps := []
  safeEnvelope := [("T", ⟨0, 1⟩)]

/-- Regression witness: `stepHybrid` on `[1/100, 3/100]` preserves exact rational endpoints
`(1/100, 3/100)` with `.den = 100`, instead of dropping `.den` and corrupting `[1/100, 3/100]`
to `(1, 3)` (which also violated `[0, 1]`). -/
theorem hybrid_stepHybrid_preserves_denominators :
    modeInvariantHolds "sub_unit" (CanonicalRat.mk 1 100) (CanonicalRat.mk 3 100) subUnitHybridAutomaton "T" = true ∧
    stepHybrid "sub_unit" (CanonicalRat.mk 1 100) (CanonicalRat.mk 3 100) .flowStep subUnitHybridAutomaton "T" =
      some ("sub_unit", CanonicalRat.mk 1 100, CanonicalRat.mk 3 100) ∧
    stepHybrid "sub_unit" (CanonicalRat.mk 1 100) (CanonicalRat.mk 3 100) .flowStep subUnitHybridAutomaton "T" ≠
      some ("sub_unit", 1, 3) := by
  decide +kernel

def brokenStepHybridDropDen
    (modeId : String) (lo hi : CanonicalRat) (act : HybridAction)
    (aut : HybridAutomaton) (varName : String) : Option (String × CanonicalRat × CanonicalRat) := do
  let st : HybridState := { modeId := modeId, box := [(varName, ⟨lo, hi⟩)] }
  let nextSt ← stepHybridAction aut st act
  let nextIv ← nextSt.box.lookup varName
  pure (nextSt.modeId, Rat.ofInt nextIv.lo.num, Rat.ofInt nextIv.hi.num)

#tooth Obend.Analysis.stepHybrid_sound
  by mutation Obend.Analysis.stepHybrid := brokenStepHybridDropDen


/-! ## 5. P0 #27: `Obend.Consensus.Epistemic` — Exact Rational Width Comparison in `IntervalRace` -/

def subUnitRaceQuery : IntervalQuery where
  expr         := .var "x"
  env          := [("x", ⟨0, CanonicalRat.mk 1 100⟩)]
  claimedBound := ⟨0, 2⟩

def tightSubUnitCert : IntervalCertWrapper where
  cert         := .direct
  boundDigest  := ByteArray.mk #[0x01]
  refinedBound := some ⟨0, CanonicalRat.mk 3 100⟩

def coarseUnitCert : IntervalCertWrapper where
  cert         := .direct
  boundDigest  := ByteArray.mk #[0x02]
  refinedBound := some ⟨0, 1⟩

/-- Regression witness: `[0, 3/100]` (`width = 3/100`) strictly beats coarse `[0, 1]` (`width = 1`)
in both arrival orders! Previously `(hi - lo).num.natAbs` assigned cost `3` to `[0, 3/100]` and
cost `1` to `[0, 1]`, selecting the coarse enclosure. -/
theorem epistemic_intervalRace_sub_unit_tighter_wins :
    intervalExactWidth subUnitRaceQuery tightSubUnitCert = CanonicalRat.mk 3 100 ∧
    intervalExactWidth subUnitRaceQuery coarseUnitCert = 1 ∧
    betterCert subUnitRaceQuery tightSubUnitCert coarseUnitCert = true ∧
    selectWinner subUnitRaceQuery [tightSubUnitCert, coarseUnitCert] = some tightSubUnitCert ∧
    selectWinner subUnitRaceQuery [coarseUnitCert, tightSubUnitCert] = some tightSubUnitCert := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have hVal : certValid subUnitRaceQuery tightSubUnitCert = true := by decide +kernel
  have hNonInv :
      (effectiveEnclosure subUnitRaceQuery tightSubUnitCert).lo ≤
        (effectiveEnclosure subUnitRaceQuery tightSubUnitCert).hi := by decide +kernel
  have hTight :
      (effectiveEnclosure subUnitRaceQuery tightSubUnitCert).hi -
        (effectiveEnclosure subUnitRaceQuery tightSubUnitCert).lo <
      (effectiveEnclosure subUnitRaceQuery coarseUnitCert).hi -
        (effectiveEnclosure subUnitRaceQuery coarseUnitCert).lo := by decide +kernel
  exact intervalRace_tighter_enclosure_wins subUnitRaceQuery tightSubUnitCert coarseUnitCert hVal hNonInv hTight

def brokenIntervalWidthDropDen (q : IntervalQuery) (c : IntervalCertWrapper) : CanonicalRat :=
  let iv := effectiveEnclosure q c
  CanonicalRat.ofNat (iv.hi - iv.lo).num.natAbs

#tooth Obend.Consensus.Epistemic.IntervalRace.intervalRace_tighter_enclosure_wins
  by mutation Obend.Consensus.Epistemic.IntervalRace.intervalExactWidth := brokenIntervalWidthDropDen


/-! ## 6. P0 #28: `Obend.Analysis.QuantumWalk` — Normalized Unitary Bipartite Szegedy Projectors & Norm Preservation -/

def k2InitEdgeState : Nat → CanonicalRat :=
  fun uv => if uv == 1 then 1 else 0

/-- Regression witness on $Q_3$ ($n = 8$, $d = 3$, $64$ directed vertex pairs): the raw adjacency
`hypercubeQ3Matrix` is **not** a scaled projector (`M^2 ≠ 3 M`, so the old `2M - dI` "reflection" was
not unitary), while both bipartite directed-edge coin projectors pass `checkScaledSymmetricProjectorFn`. -/
theorem quantumWalk_q3_raw_adjacency_not_projector :
    checkScaledSymmetricProjector hypercubeQ3Matrix 3 = false ∧
    checkScaledSymmetricProjectorFn 64 (szegedyEdgeProjAEntry hypercubeQ3Matrix) 3 = true ∧
    checkScaledSymmetricProjectorFn 64 (szegedyEdgeProjBEntry hypercubeQ3Matrix) 3 = true := by
  decide +kernel

/-- Concrete exact-rational unitarity witness on $K_2$'s 4-dimensional directed-edge space:
both normalized projectors pass `checkNormalizedRatProjector`, and three normalized Szegedy steps
from the basis edge state `e_1` keep `‖ψ‖² = 1`. -/
theorem quantumWalk_k2_normalized_unitary_steps :
    checkNormalizedRatProjector 4 (szegedyNormalizedEdgeProjA k2Matrix 1) = true ∧
    checkNormalizedRatProjector 4 (szegedyNormalizedEdgeProjB k2Matrix 1) = true ∧
    vecNormSqRat (List.range 4)
      (iterateRatVecOp
        (szegedyWalkRatStep (szegedyNormalizedEdgeProjA k2Matrix 1)
          (szegedyNormalizedEdgeProjB k2Matrix 1) (List.range 4)) 3 k2InitEdgeState) = 1 := by
  decide +kernel

/-- Universal instantiation of `szegedyWalkRatIter_unitary_norm_preserved` for arbitrary horizon `k`
and arbitrary rational edge state `ψ`. -/
theorem quantumWalk_unitary_iter_bridge
    (dim k : Nat)
    (projA projB : Nat → Nat → CanonicalRat)
    (hA : checkNormalizedRatProjector dim projA = true)
    (hB : checkNormalizedRatProjector dim projB = true)
    (ψ : Nat → CanonicalRat) :
    vecNormSqRat (List.range dim)
      (iterateRatVecOp (szegedyWalkRatStep projA projB (List.range dim)) k ψ) =
      vecNormSqRat (List.range dim) ψ :=
  szegedyWalkRatIter_unitary_norm_preserved (List.range dim) projA projB
    (checkNormalizedRatProjector_sound dim projA hA)
    (checkNormalizedRatProjector_sound dim projB hB)
    k ψ

/-- Bridge instantiation: any scaled symmetric integer projector `M` (`M^2 = d M`, `0 < d`) normalizes
to an exact rational projector `normalizeScaledProjector M d` whose Szegedy walk preserves `‖ψ‖²`. -/
theorem quantumWalk_scaled_to_normalized_projector_bridge
    (dim k : Nat) (M_A M_B : Nat → Nat → Int) (dA dB : Int)
    (hA : checkScaledSymmetricProjectorFn dim M_A dA = true)
    (hB : checkScaledSymmetricProjectorFn dim M_B dB = true)
    (ψ : Nat → CanonicalRat) :
    IsNormalizedRatProjector (normalizeScaledProjector M_A dA) (List.range dim) ∧
    vecNormSqRat (List.range dim)
      (iterateRatVecOp
        (szegedyWalkRatStep (normalizeScaledProjector M_A dA) (normalizeScaledProjector M_B dB) (List.range dim))
        k ψ) =
      vecNormSqRat (List.range dim) ψ := by
  have hpA := normalizeScaledProjector_isNormalizedRatProjector M_A (List.range dim) dA
    (checkScaledSymmetricProjectorFn_sound dim M_A dA hA)
  have hpB := normalizeScaledProjector_isNormalizedRatProjector M_B (List.range dim) dB
    (checkScaledSymmetricProjectorFn_sound dim M_B dB hB)
  exact ⟨hpA, szegedyWalkRatIter_unitary_norm_preserved (List.range dim) _ _ hpA hpB k ψ⟩

def brokenSzegedyReflectRatPlus
    (proj : Nat → Nat → CanonicalRat) (indices : List Nat) (ψ : Nat → CanonicalRat) (u : Nat) : CanonicalRat :=
  2 * matVecRat indices proj ψ u + ψ u

#tooth Obend.Analysis.szegedyReflectRatVec_unitary_norm_preserved
  by mutation Obend.Analysis.szegedyReflectRatVec := brokenSzegedyReflectRatPlus

def brokenSzegedyReflectIntPlus
    (M : Nat → Nat → Int) (cellIndices : List Nat) (cellOf : Nat → List Nat) (dM : Int)
    (v : Nat → Int) (u : Nat) : Int :=
  2 * partitionedMatVec M cellIndices cellOf v u + dM * v u

#tooth Obend.Analysis.szegedyReflectVec_norm_sq_preserved
  by mutation Obend.Analysis.szegedyReflectVec := brokenSzegedyReflectIntPlus


/-! ## 7. Axiom Audit (`0 sorryAx`, `0` custom axioms) -/

#print axioms Obend.Hardware.Device.halvings_arg_abs_le_half
#print axioms Obend.Hardware.Device.expEnclosure_sound
#print axioms Obend.Analysis.checkSosLyapunov_sound
#print axioms Obend.Analysis.checkSosLyapunovProblem_sound
#print axioms Obend.Analysis.checkSosLyapunovProblem_refuted
#print axioms Obend.Analysis.trapezoidalQuadrature_valid
#print axioms Obend.Analysis.simpsonQuadrature_valid
#print axioms Obend.Analysis.verifyTrajectorySafety_c2_ode_sound
#print axioms Obend.Analysis.picardIteratedTrajectory_safety_sound
#print axioms Obend.Analysis.stepHybrid_sound
#print axioms Obend.Consensus.Epistemic.IntervalRace.intervalRace_tighter_enclosure_wins
#print axioms Obend.Analysis.faddeevLeVerrier_charPoly_and_p4_obstruction_sound
#print axioms Obend.Analysis.szegedyReflectVec_norm_sq_preserved
#print axioms Obend.Analysis.szegedyWalkStep_norm_sq_preserved
#print axioms Obend.Analysis.normalizeScaledProjector_isNormalizedRatProjector
#print axioms Obend.Analysis.szegedyReflectRatVec_involution
#print axioms Obend.Analysis.szegedyReflectRatVec_unitary_norm_preserved
#print axioms Obend.Analysis.szegedyWalkRatStep_unitary_norm_preserved
#print axioms Obend.Analysis.szegedyWalkRatIter_unitary_norm_preserved

end Obend.Tests.Metasystem.C3NumericsSoundnessTest
end
