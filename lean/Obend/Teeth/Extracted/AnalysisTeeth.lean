module
/-
# `Obend.Teeth.Extracted.AnalysisTeeth` — Analysis & AutoCert Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (24 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Analysis.Coverage
import all Obend.Analysis.Diff
import all Obend.Analysis.EqSatHypergraph
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.Hybrid
import all Obend.Analysis.Impact
import all Obend.Analysis.QuantumWalk
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.Setup
import all Obend.Analysis.SosLyapunov
import all Obend.Analysis.TaylorModel
import all Obend.Core.Brand
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Elab.AutoCert
import all Obend.Fold
import all Obend.Hardware.AgenticEDA
import all Obend.Hardware.Analog
import all Obend.Hardware.Circuits
import all Obend.Hardware.Codec
import all Obend.Hardware.Compiler
import all Obend.Hardware.DRC
import all Obend.Hardware.DSP
import all Obend.Hardware.Datasheet
import all Obend.Hardware.HDL
import all Obend.Hardware.Judge
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Retiming
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Lrat
import all Obend.Judge.RealAnalysis
import all Obend.Law.Contract
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Std
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.UpTo
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.Obligation
import all Obend.Lower.Judge
import all Obend.Lower.Proofs.Sound
import all Obend.Lower.Typing
import all Obend.Receipt
import all Obend.Slot
import all Obend.Slot.World
import all Obend.Spec.Annotated
import all Obend.Spec.C4
import all Obend.Spec.Contract
import all Obend.Spec.DataWire
import all Obend.Spec.Elaborate
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.Parse
import all Obend.Spec.Syntax
import all Obend.Spec.Types

public section
end

namespace Obend.Teeth.Extracted.AnalysisTeeth
/-! ## Extracted from `Obend.Analysis.Coverage` (1 teeth) -/
section Obend_Analysis_Coverage
open Obend.Analysis.Coverage

#tooth check_covers by mutation Report.run := fun R rows => rows.dropLast.foldl R.step ⟨[], R.init⟩

end Obend_Analysis_Coverage

/-! ## Extracted from `Obend.Analysis.EqSatHypergraph` (4 teeth) -/
section Obend_Analysis_EqSatHypergraph
open Obend.Analysis
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.HDL

/-- Broken `extractClassEdge` emitting a bogus constant `-1` for `#tooth` mutation verification. -/
private def extractClassEdgeBroken (_costModel : HyperCostModel) (c : EClass) : HyperEdge :=
  { opIdx := c.origEdge.opIdx, op := .const (-1), srcWires := [], dstWire := c.classId }

#tooth saturate_and_extract_preserves_eval by mutation
  extractClassEdge := extractClassEdgeBroken

/-- Broken `pruneDeadEdges` that skips liveness pruning and leaves all dead cotangent edges intact. -/
private def pruneDeadEdgesBroken (_boundaryOut : List Nat) (edges : List HyperEdge) : List HyperEdge :=
  edges

#tooth goldenDiamondAdjoint_eqSat_strict_cost_reduction by mutation
  pruneDeadEdges := pruneDeadEdgesBroken

#tooth rnea2Link_adjoint_eqSat_sound by mutation
  pruneDeadEdges := pruneDeadEdgesBroken

#tooth statorCoupledLoss_adjoint_eqSat_sound by mutation
  pruneDeadEdges := pruneDeadEdgesBroken

end Obend_Analysis_EqSatHypergraph

/-! ## Extracted from `Obend.Analysis.Equitable` (2 teeth) -/
section Obend_Analysis_Equitable
open Obend.Analysis Obend.Analysis.GaussianInt Obend.Analysis.GaussianRat Obend.Analysis.IntMatrix Obend.Analysis.GaussianMatrix

/-- Broken `computeLagrangeDenominator` that adds instead of multiplying eigenvalue differences. -/
private def computeLagrangeDenominatorAddBug (eigs : List Int) (k : Nat) : Int :=
  let lamK := listGetInt eigs k
  (List.range eigs.length).foldl (fun acc j =>
    if j == k then acc else acc + (lamK - listGetInt eigs j)) 0

#tooth computeLagrangeProjector_2x2_and_3x3_universal by mutation computeLagrangeDenominator := computeLagrangeDenominatorAddBug

/-- Broken `wlRefineStep` that always returns the constant zero coloring `fun _ => 0`. -/
private def wlRefineStepConstZeroBug (_A : IntMatrix) (_n : Nat) (_color : Nat → Nat) : Nat → Nat :=
  fun _ => 0

#tooth wlStabilize_fixedPoint_iff_equitable by mutation wlRefineStep := wlRefineStepConstZeroBug

end Obend_Analysis_Equitable

/-! ## Extracted from `Obend.Analysis.Hybrid` (2 teeth) -/
section Obend_Analysis_Hybrid
open Obend.Analysis
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds CellTrace cellContract_trace_sound)

#tooth verifyFlowpipe_sound by mutation
  verifyFlowpipe := fun _ _ => true

#tooth badHybridCert_rejected by mutation
  verifyFlowpipe := fun _ _ => true

end Obend_Analysis_Hybrid

/-! ## Extracted from `Obend.Analysis.Impact` (1 teeth) -/
section Obend_Analysis_Impact
open Obend.Analysis
open Obend.Slot Obend.Fold

#tooth affected_exact by mutation indexReads := fun {_} d => d.reads.dropLast

end Obend_Analysis_Impact

/-! ## Extracted from `Obend.Analysis.QuantumWalk` (7 teeth) -/
section Obend_Analysis_QuantumWalk
open Obend.Analysis Obend.Analysis.PolyMatrix
open Obend.Judge.SOS

/-- Broken `szegedyQuotientReflectVec` that uses `+` instead of `-` for the identity reflection term. -/
private def szegedyQuotientReflectVecPlusBug
    (QM : Nat → Nat → Int)
    (cellIndices : List Nat)
    (dM : Int)
    (w : Nat → Int)
    (i : Nat) : Int :=
  2 * quotientMatVec QM cellIndices w i + dM * w i

#tooth szegedy_intertwining_step by mutation szegedyQuotientReflectVec := szegedyQuotientReflectVecPlusBug

#tooth szegedy_intertwining_power by mutation szegedyQuotientReflectVec := szegedyQuotientReflectVecPlusBug

#tooth cellUniformSzegedyPST_iff_quotient by mutation szegedyQuotientReflectVec := szegedyQuotientReflectVecPlusBug

/-- Broken `intMatrixInfNorm` that always returns `0`. -/
private def intMatrixInfNormZeroBug (_A : IntMatrix) (_dim : Nat) : Nat := 0

/-- Broken `evalScaledMatrixTaylorImag` that uses `.re` instead of `.im`. -/
private def evalScaledMatrixTaylorImagReBug
    (A : IntMatrix)
    (tNum tDen : Int)
    (order : Nat)
    (v : Nat → Int)
    (u : Nat) : Int :=
  sumIntOver
    (fun k =>
      (matrixTaylorScaledWeight tNum tDen order k).re *
        iterateVecOp (matVec (List.range A.dim) A.entry) k v u)
    (List.range (order + 1))

#tooth intMatrixInfNorm_submultiplicative_vec by mutation intMatrixInfNorm := intMatrixInfNormZeroBug

#tooth matrixTaylorPropagator_intertwines_quotient by mutation evalScaledMatrixTaylorImag := evalScaledMatrixTaylorImagReBug

#tooth matrixTaylorPropagator_encloses_k2_and_q3_pst by mutation intMatrixInfNorm := intMatrixInfNormZeroBug

#tooth matrixTaylorPropagator_encloses_k2_and_q3_pst by mutation evalScaledMatrixTaylorImag := evalScaledMatrixTaylorImagReBug

end Obend_Analysis_QuantumWalk

/-! ## Extracted from `Obend.Analysis.RealAnalysis` (3 teeth) -/
section Obend_Analysis_RealAnalysis
open Obend.Analysis Obend.Analysis.CanonicalRat Obend.Analysis.Interval
open Obend.Core.Data (Data)

/-- Broken `Interval.add` that drops `b` and returns `a`. -/
private def intervalAddDropB (a _b : Interval) : Interval := a

#tooth Interval.add_mem by mutation Interval.add := intervalAddDropB

/-- Broken `Interval.mul` that only multiplies endpoints `(a.lo * b.lo, a.hi * b.hi)` instead of 4-corner min/max. -/
private def intervalMulNaiveEndpoints (a b : Interval) : Interval :=
  ⟨a.lo * b.lo, a.hi * b.hi⟩

#tooth Interval.mul_mem by mutation Interval.mul := intervalMulNaiveEndpoints

/-- Broken `evalInterval` that maps `.sub` to `Interval.add` instead of `Interval.sub`. -/
private def evalIntervalSubAsAdd (env : List (String × Interval)) : RealExpr → Option Interval
  | .const c => some (Interval.ofPoint c)
  | .var name => (env.find? (·.1 == name)).map (·.2)
  | .add l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.add il ir)
  | .sub l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.add il ir)
  | .mul l r => do
      let il ← evalIntervalSubAsAdd env l
      let ir ← evalIntervalSubAsAdd env r
      pure (Interval.mul il ir)
  | .sqr a => do
      let ia ← evalIntervalSubAsAdd env a
      pure (Interval.sqr ia)

#tooth evalInterval_sound by mutation evalInterval := evalIntervalSubAsAdd

end Obend_Analysis_RealAnalysis

/-! ## Extracted from `Obend.Analysis.Setup` (1 teeth) -/
section Obend_Analysis_Setup
open Obend.Analysis Obend.Analysis.Setup
open Obend.Slot

-- Tooth: a reading that calls every support known true is unsound; the bracket's proof is refused.
#tooth read3_sound by mutation Setup.holds3 := fun {_ _} [_] [_] [_] _ _ => .known true

end Obend_Analysis_Setup

/-! ## Extracted from `Obend.Analysis.SosLyapunov` (1 teeth) -/
section Obend_Analysis_SosLyapunov
open Obend.Analysis Obend.Analysis.SosJson
open Obend.Judge
open Obend.Judge.SOS

#tooth sosLyapunovFormat_refuses_empty_json by mutation
  decodeSosLyapunovProblem := fun _ => .ok goldenSosProblem

end Obend_Analysis_SosLyapunov

/-! ## Extracted from `Obend.Analysis.TaylorModel` (1 teeth) -/
section Obend_Analysis_TaylorModel
open Obend.Analysis Obend.Analysis.TaylorModel

#tooth analyticModel_domain_guard_rejects_out_of_domain by mutation
  Obend.Analysis.Interval.subset := fun _ _ => true

end Obend_Analysis_TaylorModel

/-! ## Extracted from `Obend.Elab.AutoCert` (1 teeth) -/
section Obend_Elab_AutoCert
open Obend.Elab.AutoCert
open Lean (Json toJson)
open Obend.Judge
open Obend.Judge.SOS
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Judge
open Obend.Leaf
open Obend.Logic
open Obend.Spec
open Obend.Core.Term (Term)

#tooth checkGroebnerJudge_refuses_unit_basis_on_empty_ideal by mutation
  checkGroebnerJudge := fun _ _ _ => .ok

end Obend_Elab_AutoCert
end Obend.Teeth.Extracted.AnalysisTeeth
