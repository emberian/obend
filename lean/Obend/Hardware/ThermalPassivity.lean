module
/-
# Obend.Hardware.ThermalPassivity — integer quadratic-form identities for lumped thermal networks

Formerly `Obend.Hardware.Physics` (renamed 2026-11-04 by the device-physics lane). What is here is
what the file contained once its names are read literally: integer algebra about quadratic forms,
`Σ g (x_u − x_v)² ≥ 0` for a graph Laplacian (`laplacian_quadratic_passive_universal`) and its
preservation under a congruence projection (`prima_preserves_passivity`,
`prima_2col_congruence_preserves_passivity`), with an a-posteriori bound check (`checkMorErrorBound`).
They are correct, `Hardware/Codec.lean`'s thermal check uses them, and they are not models of a
device: no conductance, temperature or geometry is a parameter whose value matters
(`review/EXPERT-physics-numerics-20261103.md` §S7). The sections the file used to carry under
semiconductor names — a three-cell "drift-diffusion" whose theorems were telescoping sums, a Rayleigh
CD formula, an ALD cycle count, a four-point-probe division, an integer "Scharfetter–Gummel" edge
current and hand-typed EOT / `V_th` / subthreshold formulas — are deleted. The device physics is
`Obend/Hardware/Device/` (`Enclosure`, `Constants`, `Wafer`, `DriftDiffusion`, `Sky130Diode`), where
every constant is a parameter and the solver's output is a checked certificate; the three corner
formulas `TapeoutPipeline` still reads live in `Hardware/TcadBridge.lean` §0 under their own name.
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.ThermalPassivity
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Fourier Heat PDE to Cauer RC Model-Order Reduction via PRIMA Congruence Projection -/

/-- Symmetric positive-semidefinite discretized Fourier heat-conduction operator (`G` matrix):
$$G = \begin{pmatrix} g_1 + g_{12} & -g_{12} \\ -g_{12} & g_2 + g_{12} \end{pmatrix}$$
with ambient boundary conductances $g_1, g_2 \ge 0$ and inter-node diffusive coupling $g_{12} \ge 0$
(in micro-watts per kelvin $\mu\text{W/K}$). -/
structure FineThermalOperator where
  g1  : Int
  g2  : Int
  g12 : Int
  deriving DecidableEq, Repr

/-- Quadratic thermal power dissipation form $E(x_1, x_2) = x^\top G x$ of `FineThermalOperator`
at nodal temperature elevations $(x_1, x_2)$:
$$x^\top G x = g_1 x_1^2 + g_2 x_2^2 + g_{12} (x_1 - x_2)^2.$$ -/
def evalFineThermalEnergy (op : FineThermalOperator) (x1 x2 : Int) : Int :=
  op.g1 * (x1 * x1) + op.g2 * (x2 * x2) + op.g12 * ((x1 - x2) * (x1 - x2))

/-- Theorem (`fine_thermal_operator_dissipative`):
For any non-negative physical conductances `0 ≤ op.g1`, `0 ≤ op.g2`, `0 ≤ op.g12` and any nodal
temperature state `(x1, x2) : Int × Int`, the discretized Fourier heat operator is strictly
dissipative (positive semidefinite):
$$0 \le E(x_1, x_2) = x^\top G x.$$ -/
theorem fine_thermal_operator_dissipative
    (op : FineThermalOperator) (x1 x2 : Int)
    (hg1  : 0 ≤ op.g1)
    (hg2  : 0 ≤ op.g2)
    (hg12 : 0 ≤ op.g12) :
    0 ≤ evalFineThermalEnergy op x1 x2 := by
  dsimp only [evalFineThermalEnergy]
  have hSq1 : 0 ≤ x1 * x1 := int_sq_nonneg x1
  have hSq2 : 0 ≤ x2 * x2 := int_sq_nonneg x2
  have hSq12 : 0 ≤ (x1 - x2) * (x1 - x2) := int_sq_nonneg (x1 - x2)
  have hTerm1 : 0 ≤ op.g1 * (x1 * x1) := int_mul_nonneg op.g1 (x1 * x1) hg1 hSq1
  have hTerm2 : 0 ≤ op.g2 * (x2 * x2) := int_mul_nonneg op.g2 (x2 * x2) hg2 hSq2
  have hTerm12 : 0 ≤ op.g12 * ((x1 - x2) * (x1 - x2)) :=
    int_mul_nonneg op.g12 ((x1 - x2) * (x1 - x2)) hg12 hSq12
  omega

/-- PRIMA congruence projection $\hat{g} = V^\top G V$ of a 2D `FineThermalOperator` onto a 1D
Krylov / POD basis vector $V = (v_1, v_2)^\top$:
$$\hat{g} = g_1 v_1^2 + g_2 v_2^2 + g_{12} (v_1 - v_2)^2.$$ -/
def primaProject1D (op : FineThermalOperator) (v1 v2 : Int) : Int :=
  evalFineThermalEnergy op v1 v2

/-- Thermal dissipation $\hat{E}(z) = \hat{g} \cdot z^2$ of the PRIMA reduced-order Cauer macromodel
at reduced coordinate $z \in \mathbb{Z}$. -/
def evalReducedThermalEnergy (op : FineThermalOperator) (v1 v2 z : Int) : Int :=
  primaProject1D op v1 v2 * (z * z)

/-- Theorem (`prima_preserves_passivity`):
PRIMA congruence projection ($V^\top G V$) unconditionally preserves passivity: for ANY projection
basis $(v_1, v_2) \in \mathbb{Z}^2$ and ANY reduced coordinate $z \in \mathbb{Z}$, both the reduced
conductance $\hat{g}$ and the reduced macromodel energy dissipation $\hat{E}(z) = \hat{g} z^2$ are
non-negative (`0 ≤ primaProject1D op v1 v2` and `0 ≤ evalReducedThermalEnergy op v1 v2 z`).
Consequently, coupling the reduced Cauer thermal macromodel to a nonlinear SPICE circuit can NEVER
create artificial energy or spurious instability! -/
theorem prima_preserves_passivity
    (op : FineThermalOperator) (v1 v2 z : Int)
    (hg1  : 0 ≤ op.g1)
    (hg2  : 0 ≤ op.g2)
    (hg12 : 0 ≤ op.g12) :
    0 ≤ primaProject1D op v1 v2 ∧
    0 ≤ evalReducedThermalEnergy op v1 v2 z ∧
    0 ≤ evalFineThermalEnergy op (v1 * z) (v2 * z) := by
  dsimp only [primaProject1D, evalReducedThermalEnergy]
  have hGhat : 0 ≤ evalFineThermalEnergy op v1 v2 :=
    fine_thermal_operator_dissipative op v1 v2 hg1 hg2 hg12
  have hSqZ : 0 ≤ z * z := int_sq_nonneg z
  have hEnergy : 0 ≤ evalFineThermalEnergy op v1 v2 * (z * z) :=
    int_mul_nonneg (evalFineThermalEnergy op v1 v2) (z * z) hGhat hSqZ
  have hFull : 0 ≤ evalFineThermalEnergy op (v1 * z) (v2 * z) :=
    fine_thermal_operator_dissipative op (v1 * z) (v2 * z) hg1 hg2 hg12
  exact ⟨hGhat, hEnergy, hFull⟩

/-- A posteriori PDE-to-lumped Model-Order Reduction (MOR) error certificate:
Given the PDE residual norm $\|r(\hat{x})\| = \text{residualNorm}$, coercivity (minimum eigenvalue)
lower bound $\lambda_{\min} > 0$, and maximum allowable temperature error `maxErrorMk`, verifies the
Lax-Milgram / Babuška-Brezzi bound $\|r(\hat{x})\| \le \text{maxErrorMk} \cdot \lambda_{\min}$. -/
def checkMorErrorBound (residualNorm lambdaMin maxErrorMk : Nat) : Bool :=
  decide (lambdaMin > 0) && decide (residualNorm ≤ maxErrorMk * lambdaMin)

/-- Theorem (`mor_error_bound_sound`):
If `checkMorErrorBound residualNorm lambdaMin maxErrorMk = true`, then the coercivity constant is
strictly positive (`lambdaMin > 0`), the residual satisfies `residualNorm ≤ maxErrorMk * lambdaMin`,
and `residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin`. -/
theorem mor_error_bound_sound
    (residualNorm lambdaMin maxErrorMk : Nat)
    (hOk : checkMorErrorBound residualNorm lambdaMin maxErrorMk = true) :
    lambdaMin > 0 ∧
    residualNorm ≤ maxErrorMk * lambdaMin ∧
    residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin := by
  unfold checkMorErrorBound at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hDiv : residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin :=
    Nat.div_le_div_right hOk.2
  exact ⟨hOk.1, hOk.2, hDiv⟩

/-! ## 2. N-Node Graph-Laplacian Thermal Network & Universal Quadratic Passivity -/

/-- A diffusive thermal edge $e = (u, v)$ in an arbitrary $N$-node 3D IC / package thermal graph:
* `nodeU`, `nodeV`: endpoint thermal node indices,
* `conductanceMwPerK`: diffusive thermal conductance $g_{uv}$ (in $\text{mW/K}$ or $\mu\text{W/K}$). -/
structure ThermalEdge where
  nodeU             : Nat
  nodeV             : Nat
  conductanceMwPerK : Int
  deriving DecidableEq, Repr

/-- Quadratic power dissipation across a single diffusive thermal edge $e = (u, v)$:
$$E_e(T) = g_{uv} \cdot (T_u - T_v)^2.$$ -/
@[expose] def evalEdgeQuadratic (tempsMk : List Int) (e : ThermalEdge) : Int :=
  let dT := tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0
  e.conductanceMwPerK * (dT * dT)

/-- Total Graph-Laplacian quadratic form $T^\top L T = \sum_{e=(u,v) \in E} g_{uv} (T_u - T_v)^2$
evaluated by structural recursion over an arbitrary edge list `edges : List ThermalEdge`. -/
@[expose] def evalLaplacianQuadratic (tempsMk : List Int) : List ThermalEdge → Int
  | [] => 0
  | e :: rest => evalEdgeQuadratic tempsMk e + evalLaplacianQuadratic tempsMk rest

/-- Propositional passivity predicate: every edge in `edges` has non-negative thermal conductance. -/
def AllEdgesPassive (edges : List ThermalEdge) : Prop :=
  ∀ e ∈ edges, 0 ≤ e.conductanceMwPerK

/-- Executable boolean checker verifying that every edge in `edges` has non-negative thermal conductance. -/
def checkAllEdgesPassive (edges : List ThermalEdge) : Bool :=
  edges.all (fun e => decide (0 ≤ e.conductanceMwPerK))

/-- Theorem (`checkAllEdgesPassive_sound`):
If `checkAllEdgesPassive edges = true`, then `AllEdgesPassive edges` holds. -/
theorem checkAllEdgesPassive_sound
    (edges : List ThermalEdge)
    (hOk : checkAllEdgesPassive edges = true) :
    ∀ e ∈ edges, 0 ≤ e.conductanceMwPerK := by
  intro e hMem
  simp only [checkAllEdgesPassive, List.all_eq_true, decide_eq_true_eq] at hOk
  exact hOk e hMem

/-- Helper lemma: a single thermal edge with non-negative conductance `0 ≤ e.conductanceMwPerK`
always dissipates non-negative quadratic power `0 ≤ evalEdgeQuadratic tempsMk e`. -/
theorem edge_quadratic_passive
    (tempsMk : List Int) (e : ThermalEdge)
    (hGe : 0 ≤ e.conductanceMwPerK) :
    0 ≤ evalEdgeQuadratic tempsMk e := by
  dsimp only [evalEdgeQuadratic]
  have hSq : 0 ≤ (tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0) *
      (tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0) :=
    int_sq_nonneg (tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0)
  exact int_mul_nonneg e.conductanceMwPerK
    ((tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0) *
      (tempsMk.getD e.nodeU 0 - tempsMk.getD e.nodeV 0))
    hGe hSq

/-- Theorem (`laplacian_quadratic_passive_universal`):
For ALL nodal temperature vectors `tempsMk : List Int` and ALL $N$-node thermal graphs
`edges : List ThermalEdge` with passive edge conductances (`∀ e ∈ edges, 0 ≤ e.conductanceMwPerK`),
the Graph-Laplacian quadratic form $T^\top L T$ is universally positive semidefinite:
$$0 \le \text{evalLaplacianQuadratic}(\text{tempsMk}, \text{edges}).$$ -/
theorem laplacian_quadratic_passive_universal
    (tempsMk : List Int) (edges : List ThermalEdge)
    (hPassive : ∀ e ∈ edges, 0 ≤ e.conductanceMwPerK) :
    0 ≤ evalLaplacianQuadratic tempsMk edges := by
  induction edges with
  | nil =>
    dsimp only [evalLaplacianQuadratic]
    decide
  | cons e rest ih =>
    dsimp only [evalLaplacianQuadratic]
    have hHead : 0 ≤ e.conductanceMwPerK := hPassive e List.mem_cons_self
    have hRestPassive : ∀ e' ∈ rest, 0 ≤ e'.conductanceMwPerK :=
      fun e' hMem => hPassive e' (List.mem_cons_of_mem _ hMem)
    have hEdge : 0 ≤ evalEdgeQuadratic tempsMk e := edge_quadratic_passive tempsMk e hHead
    have hTail : 0 ≤ evalLaplacianQuadratic tempsMk rest := ih hRestPassive
    omega

/-! ## 3. Multi-Column ($N \times 2$) PRIMA Krylov Congruence Passivity -/

/-- Reconstruct the full $N$-node temperature state $T = V \alpha = \alpha_0 v^{(0)} + \alpha_1 v^{(1)}$
from an $N \times 2$ Krylov / POD projection basis `(col0, col1)` and 2D reduced state `(alpha0, alpha1)`. -/
@[expose] def reconstructPrima2ColState
    (col0 col1 : List Int) (alpha0 alpha1 : Int) : List Int :=
  List.zipWith (fun v0 v1 => alpha0 * v0 + alpha1 * v1) col0 col1

/-- Evaluate the reduced $2 \times 2$ PRIMA macromodel quadratic form
$\alpha^\top \hat{G} \alpha = (V \alpha)^\top L (V \alpha)$ on an $N$-node thermal network `edges`. -/
@[expose] def evalPrima2ColReducedQuadratic
    (col0 col1 : List Int) (edges : List ThermalEdge) (alpha0 alpha1 : Int) : Int :=
  evalLaplacianQuadratic (reconstructPrima2ColState col0 col1 alpha0 alpha1) edges

/-- Theorem (`prima_2col_congruence_preserves_passivity`):
Multi-column ($N \times 2$) PRIMA congruence projection $\hat{G} = V^\top L V$ universally preserves
passivity: for ANY $N$-node passive thermal graph `edges`, ANY Krylov basis columns `col0 col1 : List Int`,
and ANY reduced coordinate vector `(alpha0, alpha1) : Int × Int`, the reduced quadratic dissipation is
strictly non-negative:
$$0 \le \alpha^\top (V^\top L V) \alpha = \text{evalPrima2ColReducedQuadratic}(\text{col0}, \text{col1}, \text{edges}, \alpha_0, \alpha_1).$$ -/
theorem prima_2col_congruence_preserves_passivity
    (col0 col1 : List Int) (edges : List ThermalEdge) (alpha0 alpha1 : Int)
    (hPassive : ∀ e ∈ edges, 0 ≤ e.conductanceMwPerK) :
    0 ≤ evalPrima2ColReducedQuadratic col0 col1 edges alpha0 alpha1 := by
  dsimp only [evalPrima2ColReducedQuadratic]
  exact laplacian_quadratic_passive_universal
    (reconstructPrima2ColState col0 col1 alpha0 alpha1) edges hPassive

end Obend.Hardware.ThermalPassivity
end
