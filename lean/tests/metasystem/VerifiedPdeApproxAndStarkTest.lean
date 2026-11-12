module
public import Obend.Analysis.PdeSexprAndApprox
public import Obend.SymbolicZk.VerifiedStencilStark
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Analysis.Diff
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.RealAnalysis
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RangeSafe
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.Compiler
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.HDL
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.UpTo
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.SymbolicZk.VerifiedStencilStark
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
meta import all Obend.Analysis.PdeSexprAndApprox
meta import all Obend.SymbolicZk.VerifiedStencilStark

public section
namespace Obend.Tests.PdeApproxAndStark
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox
open Obend.SymbolicZk.VerifiedStencilStark
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

#guard (compilePdeText maxwell1DSpecSexpr).isSome
#guard (compilePdeText munzPhmSpecSexpr).isSome
#guard (compilePdeText linearAdvectionSpecSexpr).isSome

example : (parseSexpr "(\"a)\\\"b\" x)").isSome = true := by decide +kernel
example : (parseSexpr "(\"a\\\"").isSome = false := by decide +kernel
example : (parseSexpr "(x))").isSome = false := by decide +kernel
example : (parseSexpr "(\"x\"smuggled)").isSome = false := by decide +kernel
example : (parsePdeSpecSexpr "(pde-spec (name broken))").isSome = false := by decide +kernel
example : approxFormatName = "pde-approx-defect@1" := rfl
example : Obend.Analysis.HyperbolicPde.formatName = "hyperbolic-fvm@1" := rfl

example : parseSexpr (renderPdeSpecSexpr (.list [.atom "x) (\\\"", .list []])) =
    some (.list [.atom "x) (\\\"", .list []]) := parseSexpr_renderPdeSpecSexpr_roundtrip _

example : check { maxwellSystem with cfl := 1 } maxwellCert = .refused .cflViolation [] := by decide +kernel
example : check maxwellSystem { maxwellCert with sym := [[1, 1], [0, 9/4]] } =
    .refused .symmetrizerMismatch [0, 1] := by decide +kernel

def maxwellSurrogate : ApproxQuery where
  system := maxwellSystem
  certificate := maxwellCert
  cells := 2
  steps := 2
  eta := 2
  tolerance := 10
  initial := [[0, 0], [0, 0]]
  trajectory := [[[0, 0], [0, 0]], [[1/10, 0], [0, 1/10]], [[0, 1/10], [1/10, 0]]]

def phmSurrogate : ApproxQuery where
  system := phmSystem
  certificate := phmCert
  cells := 2
  steps := 2
  eta := 2
  tolerance := 10
  initial := [[0, 0, 0, 0], [0, 0, 0, 0]]
  trajectory := [[[0, 0, 0, 0], [0, 0, 0, 0]],
    [[1/10, 0, 0, 1/10], [0, 1/10, 1/10, 0]],
    [[0, 1/10, 1/10, 0], [1/10, 0, 0, 1/10]]]

example : checkApprox maxwellSurrogate = .ok := by decide +kernel
example : checkApprox phmSurrogate = .ok := by decide +kernel
example : checkApprox { maxwellSurrogate with tolerance := 0 } = .refused .tube [] := by decide +kernel
example : checkApprox { phmSurrogate with system := { phmSystem with cfl := 1 } } =
    .refused .geometry [] := by decide +kernel
example : pdeApproxDefectJudge.refutes .tube = true := rfl
example : pdeApproxDefectJudge.Fragment maxwellSurrogate := by
  change maxwellSurrogate.shape = true
  decide +kernel
example : maxwellSurrogate.actualError ≤ maxwellSurrogate.tolerance :=
  (checkApprox_sound _ (by decide +kernel)).trueErrorWithin
example : phmSurrogate.actualError ≤ phmSurrogate.tolerance :=
  (checkApprox_sound _ (by decide +kernel)).trueErrorWithin

def cancellationSurrogate : ApproxQuery where
  system := advectionSystem
  certificate := advectionCert
  cells := 1
  steps := 2
  eta := 2
  tolerance := 0
  initial := [[0]]
  trajectory := [[[0]], [[1]], [[0]]]

-- The conservative tube can fail even when the final true error is exactly zero.
example : cancellationSurrogate.actualError = 0 := by decide +kernel
example : checkApprox cancellationSurrogate = .refused .tube [] := by decide +kernel

#guard [maxwell1DSpecSexpr, munzPhmSpecSexpr, linearAdvectionSpecSexpr].all fun text =>
  match parseSexpr text with
  | none => false
  | some tree => parseSexpr (renderPdeSpecSexpr tree) == some tree

def packet : WordGrid := [140737488355329#64, 140737488355333#64, 140737488355330#64, 140737488355328#64]
example : InRange packet := by
  intro x hx
  simp only [packet, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel
example : gpuRollout 4 packet = q32StencilRollout 4 packet := by decide +kernel
example : q32StencilRollout 2 [1#64, 5#64, 2#64, 0#64] = [0#64, 1#64, 3#64, 2#64] := by decide +kernel
example : Obend.Core.RangeSafe.checkRangeSafeMod Obend.Apps.ZkNtt.goldilocksPrime
    stencilBounds stencilNumerator = true := by decide +kernel
example : discreteHEnergy 1 packet.length (fun _ _ => 1)
    (gridSub (decodeGrid (gpuRollout 4 packet))
      (exactTrajectory (rationalAdvection packet.length) (decodeGrid packet) 4)) <
    aprioriErrorTubeRec 4 0 (q32DefectBudget packet.length) 4 := by decide +kernel

-- Universal theorem mutations replay the stored proof, rather than testing a replacement fixture.
def alteredRender (_ : PdeSexpr) : List SexprToken := []
#tooth parseSexpr_renderPdeSpecSexpr_roundtrip by mutation renderPdeSpecSexpr := fun _ => ""

def alteredLex (_ : List Char) (_ : LexMode) (_ : List Char) (_ : List SexprToken) : Option (List SexprToken) := none
#tooth parseSexpr_renderPdeSpecSexpr_roundtrip by mutation lexChars := alteredLex

def alteredCompile (s : PdeSymbolicSpec) : Option (HyperbolicSystem × HyperbolicCert) := some (s.system, s.certificate)
#tooth compilePdeSpec_sound by mutation compilePdeSpec := alteredCompile

def acceptApprox (_ : ApproxQuery) : Obend.Judge.Verdict ApproxClause := .ok
#tooth checkApprox_sound by mutation checkApprox := acceptApprox

def eraseTube (_ _ : Rat) (_ : Nat → Rat) (_ : Nat) : Rat := 0
#tooth untrusted_surrogate_aposteriori_error_tube by mutation defectTube := eraseTube

def shiftedStep (w : WordGrid) : WordGrid := w
#tooth q32Stencil_gpu_arraySource_sound by mutation q32StencilStep := shiftedStep

def emptyProgram (_ : Nat) : Obend.Hardware.Gpu.ArraySource.Program := .ret []
#tooth q32Stencil_gpu_arraySource_sound by mutation compileQ32StencilGpu := emptyProgram

def inflatedDefect (_ : Nat) : Rat := 0
#tooth q32_defect_energy by mutation q32DefectBudget := inflatedDefect

open Obend.SymbolicZk.CompileToPiop Obend.Crypto

#guard checkStencilRow ⟨1, 5, 3, 0⟩ (compileStencilRowBits ⟨1, 5, 3, 0⟩)
#guard !(checkStencilRow ⟨1, 5, 4, 0⟩ (compileStencilRowBits ⟨1, 5, 4, 0⟩))
#guard !(checkStencilRow ⟨1, 5, 2, 2⟩ (compileStencilRowBits ⟨1, 5, 2, 2⟩))
example : checkStencilRow ⟨Obend.Apps.ZkNtt.goldilocksPrime + 1, 5, 3, 0⟩
    (compileStencilRowBits ⟨Obend.Apps.ZkNtt.goldilocksPrime + 1, 5, 3, 0⟩) = false := by decide +kernel

example (s : PhysicsStatement) : physicsStatementBytes {s with observation := s.observation + 1} ≠
    physicsStatementBytes s := by
  intro h
  have he := congrArg PhysicsStatement.observation (physicsStatementBytes_injective _ _ h)
  simp only at he; omega

example (s : PhysicsStatement) : physicsStatementBytes {s with steps := s.steps + 1} ≠
    physicsStatementBytes s := by
  intro h
  have he := congrArg PhysicsStatement.steps (physicsStatementBytes_injective _ _ h)
  simp only at he; omega

example : (q32StencilStepExec packet.toArray).toList = q32StencilStep packet :=
  q32StencilStepExec_eq_spec _

def eraseFieldEq (_ : StencilRow) : Bool := true
#tooth checkStencilRow_sound by mutation stencilRowFieldEq := eraseFieldEq

#guard physicsProtocolBytes == physicsProtocol.toUTF8

def constantHash : Hash32 where
  eval := fun _ => List.replicate 32 0
  len_eq := fun _ => List.length_replicate

def singularParams : AjtaiParams where
  rows := 1
  cols := 4
  rows_pos := by decide +kernel
  modulus := 2
  modulus_pos := by decide +kernel
  matrix := [[0, 0, 0, 0]]
  matrix_rows := rfl
  matrix_cols := by intro row h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst row; rfl

def bindingStatement : PhysicsStatement :=
  let comm := commitPhysicsTable constantHash singularParams 0 [Goldilocks.ofNat 0]
  ⟨1, 2, 0, 7, 10, 1, comm, comm, comm⟩

-- Weak primitives deliberately inhabit the concrete break branches.
example : Nonempty (Obend.Judge.Computational.HashCollisionWitness constantHash.eval
    (max (physicsStatementPreimage bindingStatement).length
      (physicsStatementPreimage { bindingStatement with observation := 8 }).length)) := by
  have hd : physicsStatementDigest constantHash bindingStatement =
      physicsStatementDigest constantHash { bindingStatement with observation := 8 } := rfl
  cases extractPhysicsStatementOrCollision constantHash bindingStatement
      { bindingStatement with observation := 8 } hd with
  | inl he =>
    have hh := congrArg PhysicsStatement.observation he
    exact False.elim ((by decide +kernel : (7 : Nat) ≠ 8) hh)
  | inr witness => exact ⟨witness⟩

example : Nonempty (Obend.Judge.Computational.SISShortVecWitness 2 131070 [[0, 0, 0, 0]]) := by
  exact ⟨extractPhysicsCommitmentBreaks constantHash singularParams 0
    [Goldilocks.ofNat 0] [Goldilocks.ofNat 1] rfl rfl rfl
    (by decide +kernel) (by rfl)⟩

def maxwellPlus : WordGrid := [140741783322624#64, 140737488355328#64]
def maxwellMinus : WordGrid := [140737488488399#64, 140737488355328#64]
def testParams (v : Nat) : AjtaiParams where
  rows := 1
  rows_pos := by decide +kernel
  cols := 4 * 2^v
  modulus := 2
  modulus_pos := by decide +kernel
  matrix := [List.replicate (4 * 2^v) 0]
  matrix_rows := rfl
  matrix_cols := by intro row h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst row; simp

def rolloutStatement (H : Hash32) : ZkPdeRolloutStmt :=
  let w := q32MaxwellRollout 2 maxwellPlus maxwellMinus
  ⟨1, 2, 0, (w.1.getD 0 0#64).toNat, (w.2.getD 0 0#64).toNat, 1, 1,
    commitPhysicsTable H (testParams 2) 2 (encodeMaxwellInit maxwellPlus maxwellMinus), 5,
    commitPhysicsTable H (testParams 5) 5 (List.replicate 32 CommRingOps.zero)⟩
def rolloutReceipt (H : Hash32) : ZkPdeRolloutReceipt :=
  proveZkPdeRolloutReceipt H (testParams 2) (testParams 5) (rolloutStatement H) maxwellPlus maxwellMinus

theorem maxwellPlus_range (i : Obend.Hardware.ArrayHypergraph.Word) (hi : i ∈ maxwellPlus) : i.toNat < amplitudeLimit := by
  simp only [maxwellPlus, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> decide +kernel
theorem maxwellMinus_range (i : Obend.Hardware.ArrayHypergraph.Word) (hi : i ∈ maxwellMinus) : i.toNat < amplitudeLimit := by
  simp only [maxwellMinus, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> decide +kernel

theorem rolloutReceipt_complete (H : Hash32) :
    verifyZkPdeRolloutReceipt H (testParams 2) (testParams 5) (rolloutStatement H) (rolloutReceipt H) = true := by
  apply proveZkPdeRolloutReceipt_complete H (testParams 2) (testParams 5) (rolloutStatement H) maxwellPlus maxwellMinus
    maxwellPlus_range maxwellMinus_range
  · exact ⟨rfl, rfl⟩
  · change (0 : Nat) < 2 ∧ 0 < 1
    decide +kernel
  · exact ⟨rfl, rfl⟩
  · change discreteHEnergy 2 2 (matOf unitMaxwellCert.sym) (decodeMaxwellGrid maxwellPlus maxwellMinus) ≤ 1 / 1
    decide +kernel
  · exact ⟨rfl, rfl⟩
  · rfl
  · simp only [rolloutResiduals, rolloutReceiptData, (dualOpen_tables H (testParams 2) _ _ _ _).1,
      List.length_append, List.length_map, List.length_zip, encodeMaxwellInit]
    change (30 : Nat) ≤ 32
    decide +kernel
  · rfl

example : (compileQ32MaxwellGpu 2).eval (maxwellEnv maxwellPlus maxwellMinus) =
    [(q32MaxwellRollout 1 maxwellPlus maxwellMinus).1, (q32MaxwellRollout 1 maxwellPlus maxwellMinus).2] := by decide +kernel
example : gpuMaxwellRollout 2 maxwellPlus maxwellMinus = q32MaxwellRollout 2 maxwellPlus maxwellMinus := by decide +kernel
example : discreteHEnergy 2 2 (matOf unitMaxwellCert.sym)
    (gridSub (q32MaxwellTrajectory maxwellPlus maxwellMinus 2)
      (exactTrajectory (rationalMaxwell 2) (decodeMaxwellGrid maxwellPlus maxwellMinus) 2)) ≤
      aprioriErrorTubeRec 2 0 (maxwellDefectBudget 2) 2 := by decide +kernel

#guard verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5) (rolloutStatement constantHash) (rolloutReceipt constantHash)
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5)
  { rolloutStatement constantHash with claimedPlus := (rolloutStatement constantHash).claimedPlus + 1 } (rolloutReceipt constantHash))
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5)
  { rolloutStatement constantHash with energyMaxNum := -1 } (rolloutReceipt constantHash))
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5)
  { rolloutStatement constantHash with energyMaxNum := 0 } (rolloutReceipt constantHash))

def wrongDigestStatement : ZkPdeRolloutStmt :=
  let s := rolloutStatement constantHash
  { s with initCommitment := ({ s.initCommitment.1 with root := ⟨⟨Array.replicate 32 1⟩, by decide +kernel⟩ }, s.initCommitment.2) }
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5) wrongDigestStatement (rolloutReceipt constantHash))

def wrappedReceipt : ZkPdeRolloutReceipt :=
  let r := rolloutReceipt constantHash
  let row : StencilRow := ⟨Obend.Apps.ZkNtt.goldilocksPrime + 1, 5, 3, 0⟩
  { r with stepRowsPlus := [[(row, compileStencilRowBits row), (row, compileStencilRowBits row)],
    (r.stepRowsPlus.getD 1 [])] }
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5) (rolloutStatement constantHash) wrappedReceipt)

#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5)
  { rolloutStatement constantHash with sensorCell := 2 } (rolloutReceipt constantHash))
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5)
  { rolloutStatement constantHash with energyMaxDen := 0 } (rolloutReceipt constantHash))
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5) (rolloutStatement constantHash)
  { rolloutReceipt constantHash with initOpening := ((rolloutReceipt constantHash).initOpening.1, ⟨[]⟩) })
#guard !(verifyZkPdeRolloutReceipt constantHash (testParams 2) (testParams 5) (rolloutStatement constantHash)
  { rolloutReceipt constantHash with residualPadding := [Goldilocks.ofNat 1] })

-- Both concrete cryptographic failures are extractable for the same accepted
-- receipt when deliberately singular test primitives bind two distinct tables.
def extractedRolloutBreak (latticeFirst : Bool) :=
  extractZkPdeRolloutAgainstCommitted_or_dualBreak constantHash (testParams 2) (testParams 5)
    (rolloutStatement constantHash) (rolloutReceipt constantHash) (List.replicate 4 (Goldilocks.ofNat 1))
    rfl rfl (by decide +kernel) (rolloutReceipt_complete constantHash) latticeFirst
#guard match extractedRolloutBreak false with | .inr (.inl _) => true | _ => false
#guard match extractedRolloutBreak true with | .inr (.inr _) => true | _ => false

example : Nonempty (ValidMaxwellRolloutWitness constantHash (testParams 2) (rolloutStatement constantHash)) :=
  ⟨acceptedRolloutWitness constantHash (testParams 2) (testParams 5) _ _ (rolloutReceipt_complete constantHash)⟩

def acceptReceipt (_ : Hash32) (_ _ : AjtaiParams) (_ : ZkPdeRolloutStmt) (_ : ZkPdeRolloutReceipt) : Bool := true
def refuseReceipt (_ : Hash32) (_ _ : AjtaiParams) (_ : ZkPdeRolloutStmt) (_ : ZkPdeRolloutReceipt) : Bool := false
#tooth verifyZkPdeRolloutReceipt_sound_or_dualBreak by mutation verifyZkPdeRolloutReceipt := acceptReceipt
#tooth proveZkPdeRolloutReceipt_complete by mutation verifyZkPdeRolloutReceipt := refuseReceipt
#tooth q32Maxwell_gpu_arraySource_sound by mutation compileQ32MaxwellGpu := emptyProgram
#tooth checkWaveLayer_sound by mutation checkStencilRow := fun _ _ => true

/-- Audit executable dependencies, excluding erased proofs and proposition/type
annotations. Imported rational canonicality and analysis proofs may use classical
logic; none may supply a computational witness through choice. -/
private meta partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [`Obend.Analysis.PdeSexprAndApprox, `Obend.SymbolicZk.VerifiedStencilStark]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  Lean.Elab.Command.liftTermElabM do
    let rejected ← try
      let _ ← (auditComputationalChoice (Lean.mkConst ``Classical.choice [.succ .zero])).run {}
      pure false
    catch _ => pure true
    unless rejected do throwError "Choice audit failed its negative control"
  for name in [``extractPhysicsStatementOrCollision, ``extractPhysicsCommitmentBreaks,
      ``verifyZkPdeRolloutReceipt, ``acceptedRolloutWitness,
      ``extractZkPdeRollout_or_dualBreak, ``extractZkPdeRolloutAgainstCommitted_or_dualBreak] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "Owned declarations: zero compiler-trust dependencies; zero closed theorems; extractors have zero computational choice dependencies (erased proofs excluded)."

#assert_axioms_tree
end Obend.Tests.PdeApproxAndStark
