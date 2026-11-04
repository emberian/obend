/-
# `Obend/Teeth/Analysis/Fixtures.lean` — the closed fixtures that left tier 1 (2026-11-04)

Each `example` here was a `theorem` in a tier-1 module of `Obend/Analysis/`: a closed statement, proved by
`decide +kernel` on literal data, that nothing cites. The triage of 2026-11-04 (`Obend/Census.lean`,
`review/DECISIONS-20261031.md`) keeps them as what they are, end-to-end runs worth doing before a
push and not on every library build. Each carries the module it came from and why it is kept. This
file is tier 2: `lake build Teeth`; a plain file, so it sees every definition with its body.
-/

import Obend.Analysis.Format
import Obend.Analysis.QuantumWalk

set_option autoImplicit false

-- from Obend/Analysis/Format.lean:165: a 9-line closed evaluation; worth a pre-push run
namespace Obend.Analysis
open Obend.Slot Lean
/-- **The tooth**: an index that drops the dependent's last read predicts nothing for the embed,
and the checker refuses that prediction: the embed that goes behind is missing. -/
example :
    affectedWith (fun d => d.reads.dropLast) embedQuestion = [] ∧
      ¬ Meaning embedQuestion (affectedWith (fun d => d.reads.dropLast) embedQuestion) := by
  have h : affectedWith (fun d => d.reads.dropLast) embedQuestion = [] := by decide +kernel
  refine ⟨h, fun hm => ?_⟩
  rw [h] at hm
  have := check_complete (r := 0) hm
  have e : check 0 embedQuestion [] = .refused (.missing "Alpha: ![[Beta]]") [] := by decide +kernel
  rw [e] at this; cases this
end Obend.Analysis

-- from Obend/Analysis/QuantumWalk.lean:712: end-to-end run on a fixture (33 lines); worth a pre-push run, not every library build
namespace Obend.Analysis
open Obend.Judge.SOS
/-- **Theorem (`ctqw_p3_end_to_end_pst_algebraic`)**:
**Symbolic Algebraic Certificate for End-to-End PST on $P_3$ over $\mathbb{Q}(\alpha)/\langle \alpha^2 - 2 \rangle$**:
1. The minimal polynomial basis $G = [\alpha^2 - 2]$ satisfies Buchberger's criterion (`checkGroebnerBasis 4 G = true`).
2. Over $\mathbb{Q}[\alpha]/\langle \alpha^2 - 2 \rangle$ (via `PolyMatrix.mulMod G 6`):
   - Completeness holds: $4 P_0 + 4 P_+ + 4 P_- = 4 I_3$,
   - Spectral reconstruction holds modulo $\alpha^2 - 2$:
     $0 \cdot (4 P_0) + \alpha (4 P_+) + (-\alpha)(4 P_-) \equiv 4 H_{P_3} \pmod{\alpha^2 - 2}$,
   - Exact idempotence holds modulo $\alpha^2 - 2$:
     $(4 P_0)^2 = 4(4 P_0)$, $(4 P_+)^2 \equiv 4(4 P_+)$, $(4 P_-)^2 \equiv 4(4 P_-)$,
   - Pairwise orthogonality holds modulo $\alpha^2 - 2$:
     $(4 P_0)(4 P_+) \equiv 0$, $(4 P_+)(4 P_-) \equiv 0$.
3. At transfer time $\tau = \pi/\sqrt{2} = \pi/\alpha$, the mode phases are $\phi_0 = +1$,
   $\phi_+ = e^{-i\alpha(\pi/\alpha)} = -1$, and $\phi_- = e^{+i\alpha(\pi/\alpha)} = -1$.
   In the propagator $4 U(\pi/\alpha) = (+1)(4 P_0) + (-1)(4 P_+) + (-1)(4 P_-)$, all irrational
   $\pm\alpha$ terms cancel identically, mapping source vertex $0$ to $(0, 0, -4)^T$ (100% end-to-end
   state transfer to vertex $2$, `0` leakage at vertices $0$ and $1$).
4. Contrastingly, on $P_4$, the eigenvalue ratio satisfies $r^2 - 3r + 1 = 0$ and fails rational
   parity alignment (`checkP4IrrationalRatioObstruction = true`). -/
example :
    let G := [p3MinPolyAlphaSqMinus2]
    let alpha := polyVarPow 0 1
    let negAlpha := polyOfTerm [(0, 1)] (-1)
    let negOne := polyOfTerm [] (-1)
    let sumProj := PolyMatrix.add p3AlgebraicProj0 (PolyMatrix.add p3AlgebraicProjPlus p3AlgebraicProjMinus)
    let idScaled4 := PolyMatrix.ofIntMatrix (IntMatrix.scaledIdentity 3 4)
    let hScaled4 := PolyMatrix.ofIntMatrix (path3Matrix.scale 4)
    let specRecon := PolyMatrix.add
      (PolyMatrix.scalePolyMod G 6 alpha p3AlgebraicProjPlus)
      (PolyMatrix.scalePolyMod G 6 negAlpha p3AlgebraicProjMinus)
    -- Propagator 4*U(pi / sqrt(2)) = (+1)*(4*P0) + (-1)*(4*P+) + (-1)*(4*P-)
    let propTau := PolyMatrix.add p3AlgebraicProj0
      (PolyMatrix.add
        (PolyMatrix.scalePolyMod G 6 negOne p3AlgebraicProjPlus)
        (PolyMatrix.scalePolyMod G 6 negOne p3AlgebraicProjMinus))
    checkGroebnerBasis 4 G = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.sub sumProj idScaled4) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.sub specRecon hScaled4) = true ∧
    PolyMatrix.isZeroMod G 6
      (PolyMatrix.sub (PolyMatrix.mulMod G 6 p3AlgebraicProjPlus p3AlgebraicProjPlus)
                      (PolyMatrix.scalePolyMod G 6 (polyOfTerm [] 4) p3AlgebraicProjPlus)) = true ∧
    PolyMatrix.isZeroMod G 6
      (PolyMatrix.sub (PolyMatrix.mulMod G 6 p3AlgebraicProjMinus p3AlgebraicProjMinus)
                      (PolyMatrix.scalePolyMod G 6 (polyOfTerm [] 4) p3AlgebraicProjMinus)) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.mulMod G 6 p3AlgebraicProj0 p3AlgebraicProjPlus) = true ∧
    PolyMatrix.isZeroMod G 6 (PolyMatrix.mulMod G 6 p3AlgebraicProjPlus p3AlgebraicProjMinus) = true ∧
    -- End-to-end PST from vertex 0 to vertex 2: column 0 is [0, 0, -4]
    (propTau.entry 0 0).isZero = true ∧
    (propTau.entry 1 0).isZero = true ∧
    propTau.entry 2 0 = polyOfTerm [] (-4) ∧
    checkP4IrrationalRatioObstruction = true := by
  decide +kernel
end Obend.Analysis

-- from Obend/Analysis/QuantumWalk.lean:848: end-to-end run on a fixture (14 lines); worth a pre-push run, not every library build
namespace Obend.Analysis
open Obend.Judge.SOS
/-- **Theorem (`ctqw_hypercube_factorization_exact`)**:
1. The Hamming-weight partition of $Q_3$ ($8$ vertices $\to 4$ cells of sizes $1, 3, 3, 1$) is
   strictly equitable (`checkEquitablePartition = true`), 1-WL bisimulation-stable
   (`checkWl1ColorRefinementStable = true`), satisfies the symmetrizability handshake identity
   $\binom{3}{i} Q_{i,j} = \binom{3}{j} Q_{j,i}$ (`checkHandshakeIdentity = true`), and has zero
   equitable residual (`evalEquitableResidualNormSq = 0`).
2. Its quotient matrix matches `krawtchoukQuotientEntry 3` across all $0 \le i, j < 4$, has
   Faddeev–LeVerrier characteristic polynomial $(\lambda^2 - 9)(\lambda^2 - 1) = \lambda^4 - 10\lambda^2 + 9$,
   and its synthesized Lagrange–Sylvester projectors pass `checkSpectralDecomposition = true`!
3. By Cartesian tensor factorization $U_{Q_d}(\pi/2) = U_{K_2}(\pi/2)^{\otimes d}$, the antipodal
   state transfer amplitude $(-i)^d$ has exact unit norm (`normSq = 1`) for every dimension $d \in \mathbb{N}$
   (with `hypercubeAntipodalPhase 3 = ⟨0, 1⟩`, i.e., $(-i)^3 = +i$). -/
example :
    let cells := [0, 1, 2, 3]
    hypercubeQ3Matrix.isSymmetric = true ∧
    checkEquitablePartition hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient = true ∧
    checkWl1ColorRefinementStable hypercubeQ3Matrix 4 hypercubeQ3Part = true ∧
    checkHandshakeIdentity 8 4 hypercubeQ3Part hypercubeQ3Quotient = true ∧
    evalEquitableResidualNormSq hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient = 0 ∧
    (cells.all fun i => cells.all fun j =>
      decide (hypercubeQ3Quotient i j = krawtchoukQuotientEntry 3 i j)) = true ∧
    faddeevLeVerrierCoeffs hypercubeQ3QuotientMatrix = [1, 0, -10, 0, 9] ∧
    checkSpectralDecomposition hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3] q3QuotientSylvesterProjectors = true ∧
    hypercubeAntipodalPhase 3 = ⟨0, 1⟩ ∧
    (hypercubeAntipodalPhase 3).normSq = 1 := by
  decide +kernel
end Obend.Analysis

-- from Obend/Analysis/QuantumWalk.lean:1100: end-to-end run on a fixture (32 lines); worth a pre-push run, not every library build
namespace Obend.Analysis
open Obend.Judge.SOS
/-- **Theorem (`ctqw_validated_flowpipe_and_taylor_unitarity`)**:
1. **Validated Taylor-Model Unitary Phase Conservation**:
   Over $\theta \in [-1/10, 1/10]$, the degree-4 Taylor model `tmUnitaryNormSq` for
   $|e^{-i\theta}|^2 = \cos^2(\theta) + (-\sin(\theta))^2$ cancels all polynomial drift of degrees
   $1, 2, 3, 4$ (`coeffs = [1, 0, 0, 0, 0]`) and rigorously encloses exact unit probability $1$.
2. **Validated Symplectic Schrödinger & Lindblad Flowpipes (Positive Poles)**:
   - Over 3 steps with $\Delta t = 1/10$, the symplectic eigenmode ODE `schrodingerEigenmodeOde 1 (1/10)`
     and coupled 2-site walk `schrodingerK2CoupledOde (1/10)` starting from $|0\rangle$ stay strictly
     inside the unitary amplitude envelope (`verifyTrajectorySafety = true`).
   - Open-system Lindblad dephasing `lindbladDephasingOde (1/2) (1/2)` monotonically contracts coherence
     inside $[0, 1]$ (`verifyTrajectorySafety = true`).
3. **Non-Hermitian Runaway Refusal (Negative Pole)**:
   - The non-Hermitian anti-damped generator `nonHermitianGainRunawayOde` breaches the unitary envelope
     $[-2, 2]$ on step 1 and is refused (`verifyTrajectorySafety = false`).
4. **Hybrid Quantum Pulse Schedule Verification**:
   - Driving in `"rabi_drive"` from $p_0 \in [2/5, 9/20]$ into the $[4/5, 1]$ target window followed
     by `.jumpTo "idle_readout"` and readout relaxation passes `verifyHybridScheduleSafety = true`,
     whereas a premature readout jump before reaching the excited guard is refused (`= false`). -/
example :
    let dom : Interval := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
    let normTM := tmUnitaryNormSq dom
    let dtSmall := CanonicalRat.mk 1 10
    let remSmall : Interval := ⟨CanonicalRat.mk (-1) 100, CanonicalRat.mk 1 100⟩
    let eigenOde := schrodingerEigenmodeOde 1 dtSmall remSmall
    let k2Ode := schrodingerK2CoupledOde dtSmall remSmall
    let lindbladOde := lindbladDephasingOde (CanonicalRat.mk 1 2) (CanonicalRat.mk 1 2) remSmall
    let initEigen := [("x", Interval.ofPoint 1), ("y", Interval.ofPoint 0)]
    let safeEigen := [("x", (⟨-2, 2⟩ : Interval)), ("y", (⟨-2, 2⟩ : Interval))]
    let initK2 :=
      [ ("x0", Interval.ofPoint 1), ("y0", Interval.ofPoint 0)
      , ("x1", Interval.ofPoint 0), ("y1", Interval.ofPoint 0) ]
    let safeK2 :=
      [ ("x0", (⟨-2, 2⟩ : Interval)), ("y0", (⟨-2, 2⟩ : Interval))
      , ("x1", (⟨-2, 2⟩ : Interval)), ("y1", (⟨-2, 2⟩ : Interval)) ]
    let initPulse : HybridState :=
      { modeId := "rabi_drive"
      , box    := [("p", ⟨CanonicalRat.mk 2 5, CanonicalRat.mk 9 20⟩)] }
    -- 1. Taylor model unitary phase identity cos^2(theta) + (-sin(theta))^2 = 1
    normTM.coeffs = [1, 0, 0, 0, 0] ∧
    Interval.containsRat (evalTaylorModelRange normTM) 1 = true ∧
    -- 2. Symplectic Schrodinger & Lindblad flowpipe safety (positive poles)
    verifyTrajectorySafety eigenOde initEigen 3 safeEigen = true ∧
    verifyTrajectorySafety k2Ode initK2 3 safeK2 = true ∧
    verifyTrajectorySafety lindbladOde [("c", ⟨CanonicalRat.mk 4 5, 1⟩)] 3 [("c", ⟨0, 1⟩)] = true ∧
    -- 3. Non-Hermitian gain runaway refusal (negative pole)
    verifyTrajectorySafety nonHermitianGainRunawayOde [("x", Interval.ofPoint 1)] 2 [("x", ⟨-2, 2⟩)] = false ∧
    -- 4. Hybrid quantum pulse schedule safety vs premature jump refusal
    verifyHybridScheduleSafety quantumPulseHybridAutomaton initPulse [.flowStep, .jumpTo "idle_readout", .flowStep] = true ∧
    verifyHybridScheduleSafety quantumPulseHybridAutomaton initPulse [.jumpTo "idle_readout"] = false := by
  decide +kernel
end Obend.Analysis
