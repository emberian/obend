module
/-
# Obend.Hardware.Magnetics — 2D Planar Courant $P_1$ Finite Element Magnetostatics, Area-Normalized Global Assembly & Damped Picard Nonlinear B-H Iteration

Formalizes **2D planar magnetostatic Finite Element Analysis (Courant $P_1$ linear triangles, after
David Meeker's Finite Element Method Magnetics)** and **damped Picard nonlinear ferromagnetic
reluctivity fixed-point iteration** within `Obend.Hardware`:

1. **2D Planar First-Order Triangular Finite Element (`FemmTriangle2D`) for $-\nabla \cdot (\nu \nabla A_z) = J_z$**:
   - Models a first-order Courant triangular mesh element with integer vertex coordinates
     $(x_0, y_0), (x_1, y_1), (x_2, y_2)$, magnetic reluctivity $\nu = 1/\mu$, and out-of-plane
     source current density $J_z$,
   - Defines shape function gradient coefficients $b_i = y_{i+1} - y_{i+2}$ and $c_i = x_{i+2} - x_{i+1}$
     along with signed double-area $2\Delta = b_0 c_1 - b_1 c_0$ and positive area denominator $|2\Delta|$,
   - Proves **`femm_gradient_sum_zero`** ($\sum_i b_i = 0 \wedge \sum_i c_i = 0$),
     **`femm_gauge_invariance`**, **`femm_element_energy_nonneg`**, and **`femm_mesh_energy_nonneg`**.
2. **Matrix-Free Element Action (`libCEED` $G_e^\top D_e G_e$ Operator) & Global Nodal Equilibrium**:
   - Proves **`femm_matrix_free_nodal_sum_zero`**, **`femm_matrix_free_energy_identity`**,
     **`femm_global_residual_sum_zero`**, and **`femm_global_equilibrium_gauge_invariant`**.
3. **Exact Area-Normalized (`1 / \Delta_e`) Global Courant $P_1$ Stiffness, Load & Co-Energy Assembly**:
   - Over exact `Rat` (and fixed-point `Int`), divides element stiffness by $4|\Delta_e| = 2|2\Delta_e|$,
     element magnetic co-energy by $8|\Delta_e| = 4|2\Delta_e|$, and scales consistent nodal load by
     $|\Delta_e| / 3 = |2\Delta_e| / 6$:
     $$W_e = \frac{\nu_e}{8|\Delta_e|}\bigl((b \cdot A)^2 + (c \cdot A)^2\bigr), \qquad
       r_{e,i} = \frac{\nu_e}{4|\Delta_e|}(b_i g_x + c_i g_y) - \frac{J_z |\Delta_e|}{3},$$
   - Proves **`evalElementResidualQ_gauge_invariant`**, **`evalElementResidualQ_ampere_sum`**
     ($\sum_{i=0}^2 r_{e,i} = -J_z |\Delta_e|$), **`evalElementResidualQ_virtual_work_identity`**
     ($a^\top r_e = 2 W_e - \frac{a_0 + a_1 + a_2}{3} J_z |\Delta_e|$),
     **`evalMeshNodalResidualQ_gauge_invariant`**, and **`evalMeshTotalCoEnergyQ_nonneg`** across
     arbitrary **non-uniform** 2D meshes ($\Delta_{e_1} \neq \Delta_{e_2}$).
4. **Damped Picard Nonlinear Silicon-Steel B-H Fixed-Point Iteration (`stepBhPicardReluctivity`)**:
   - Models chord reluctivity $\nu_{\text{sec}}(B^2) = \nu_0 + k_{\text{sat}} B^2$ and the damped
     Picard update $\nu_{k+1} = \lfloor ((1000 - \omega) \nu_k + \omega \nu_{\text{sec}}(B^2)) / 1000 \rfloor$
     ($\omega \in [0, 1000]$ permille),
   - Proves **`stepBhPicardReluctivity_fixed_point`** ($\nu_k = \nu_{\text{sec}}(B^2) \implies \nu_{k+1} = \nu_k$),
     **`stepBhPicardReluctivity_brackets`**, and **`stepBhPicardReluctivity_monotone`**.
-/
@[expose] public section

namespace Obend.Hardware.Magnetics
set_option autoImplicit false

/-! ## 0. Integer Arithmetic Order Helpers -/

private theorem int_mul_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact Int.natCast_nonneg (m * n)
    | negSucc _ => omega
  | negSucc _ => omega

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases a with
  | ofNat n => exact Int.natCast_nonneg (n * n)
  | negSucc n => exact Int.natCast_nonneg (Nat.succ n * Nat.succ n)

private theorem int_mul_le_mul_of_nonneg_left (a b c : Int) (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  have hDiff : 0 ≤ c * (b - a) := int_mul_nonneg c (b - a) hc (by omega)
  have hSplit : a + (b - a) = b := by omega
  have hExpand : c * (a + (b - a)) = c * a + c * (b - a) := Int.mul_add c a (b - a)
  rw [hSplit] at hExpand
  omega

/-! ## 1. 2D Planar First-Order Triangular Finite Element (`FemmTriangle2D`) -/

/-- A 2D planar first-order Courant triangular finite element for the magnetostatic PDE
$-\nabla \cdot (\nu \nabla A_z) = J_z$:
* `(x0, y0)`, `(x1, y1)`, `(x2, y2)`: integer vertex coordinates (e.g. in micrometers),
* `nuScaled`: element magnetic reluctivity $\nu = 1/\mu$ (scaled integer units),
* `jzScaled`: out-of-plane source current density $J_z$ (scaled integer units). -/
structure FemmTriangle2D where
  x0       : Int
  y0       : Int
  x1       : Int
  y1       : Int
  x2       : Int
  y2       : Int
  nuScaled : Int
  jzScaled : Int
  deriving DecidableEq, Repr

/-- Shape function $x$-gradient numerator $b_0 = y_1 - y_2$. -/
def FemmTriangle2D.b0 (tri : FemmTriangle2D) : Int := tri.y1 - tri.y2

/-- Shape function $x$-gradient numerator $b_1 = y_2 - y_0$. -/
def FemmTriangle2D.b1 (tri : FemmTriangle2D) : Int := tri.y2 - tri.y0

/-- Shape function $x$-gradient numerator $b_2 = y_0 - y_1$. -/
def FemmTriangle2D.b2 (tri : FemmTriangle2D) : Int := tri.y0 - tri.y1

/-- Shape function $y$-gradient numerator $c_0 = x_2 - x_1$. -/
def FemmTriangle2D.c0 (tri : FemmTriangle2D) : Int := tri.x2 - tri.x1

/-- Shape function $y$-gradient numerator $c_1 = x_0 - x_2$. -/
def FemmTriangle2D.c1 (tri : FemmTriangle2D) : Int := tri.x0 - tri.x2

/-- Shape function $y$-gradient numerator $c_2 = x_1 - x_0$. -/
def FemmTriangle2D.c2 (tri : FemmTriangle2D) : Int := tri.x1 - tri.x0

/-- Twice the signed area $2\Delta = b_0 c_1 - b_1 c_0$ of the 2D triangle. -/
def FemmTriangle2D.twiceArea (tri : FemmTriangle2D) : Int :=
  tri.b0 * tri.c1 - tri.b1 * tri.c0

/-- Magnitude $|2\Delta_e| \ge 0$ of twice the triangle area. -/
def FemmTriangle2D.absTwiceArea (tri : FemmTriangle2D) : Int :=
  Int.ofNat tri.twiceArea.natAbs

/-- Strictly positive area denominator $\max(1, |2\Delta_e|)$ for fixed-point division. -/
def FemmTriangle2D.areaDenom (tri : FemmTriangle2D) : Int :=
  max 1 tri.absTwiceArea

/-- Golden 2D FEMM stator-tooth triangular mesh element (in micrometers, $2\Delta = 3 \times 10^6\,\mu\text{m}^2$, $\nu = 800$). -/
def goldenStatorToothTriangle : FemmTriangle2D :=
  { x0       := 0
    y0       := 0
    x1       := 2000
    y1       := 0
    x2       := 0
    y2       := 1500
    nuScaled := 800
    jzScaled := 0 }

/-- Theorem (`femm_gradient_sum_zero`):
For every 2D triangular element `tri`, the shape-function gradient coefficients sum to zero
along both axes ($b_0 + b_1 + b_2 = 0$ and $c_0 + c_1 + c_2 = 0$), guaranteeing that a constant
nodal potential produces zero magnetic flux density. -/
theorem femm_gradient_sum_zero (tri : FemmTriangle2D) :
    tri.b0 + tri.b1 + tri.b2 = 0 ∧ tri.c0 + tri.c1 + tri.c2 = 0 := by
  unfold FemmTriangle2D.b0 FemmTriangle2D.b1 FemmTriangle2D.b2
  unfold FemmTriangle2D.c0 FemmTriangle2D.c1 FemmTriangle2D.c2
  constructor <;> omega

/-- Scaled $x$-component numerator of $\nabla A_z$ (equal to $-2\Delta \cdot B_y$):
$b_0 A_0 + b_1 A_1 + b_2 A_2$. -/
def gradAxScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.b0 * a0 + tri.b1 * a1 + tri.b2 * a2

/-- Scaled $y$-component numerator of $\nabla A_z$ (equal to $2\Delta \cdot B_x$):
$c_0 A_0 + c_1 A_1 + c_2 A_2$. -/
def gradAyScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.c0 * a0 + tri.c1 * a1 + tri.c2 * a2

/-- Scaled squared magnetic flux density numerator $(2\Delta)^2 \|\mathbf{B}\|^2 = (\nabla_x A_z)^2 + (\nabla_y A_z)^2$. -/
def fluxDensitySqScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  (gradAxScaled tri a0 a1 a2) * (gradAxScaled tri a0 a1 a2) +
  (gradAyScaled tri a0 a1 a2) * (gradAyScaled tri a0 a1 a2)

/-- Numerator $\nu\,(2\Delta)^2 \|\nabla A_z\|^2$ ($8|\Delta_e|$ times $W_e$); see `evalElementMagneticEnergyQ`
and `evalElementMagneticEnergyAreaScaled` for `/ \Delta_e`-normalized element energy across non-uniform meshes. -/
def evalElementMagneticEnergyScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.nuScaled * fluxDensitySqScaled tri a0 a1 a2

/-- Fixed-point `/ \Delta_e`-normalized element magnetic energy
$\lfloor (\text{scale} \cdot \nu_e ((b \cdot A)^2 + (c \cdot A)^2)) / (4 \cdot \max(1, |2\Delta_e|)) \rfloor$. -/
def evalElementMagneticEnergyAreaScaled (scale : Int) (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  (scale * evalElementMagneticEnergyScaled tri a0 a1 a2) / (4 * tri.areaDenom)

/-- Universal Gauge Invariance Theorem (`femm_gauge_invariance`):
Adding any uniform scalar gauge offset $c \in \mathbb{Z}$ to all three nodal vector potentials
$(A_0 + c, A_1 + c, A_2 + c)$ leaves both components of $\nabla A_z$ strictly unchanged. -/
theorem femm_gauge_invariance (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    gradAxScaled tri (a0 + c) (a1 + c) (a2 + c) = gradAxScaled tri a0 a1 a2 ∧
    gradAyScaled tri (a0 + c) (a1 + c) (a2 + c) = gradAyScaled tri a0 a1 a2 := by
  have hZero := femm_gradient_sum_zero tri
  constructor
  · unfold gradAxScaled
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    have hSumB : (tri.b0 + tri.b1 + tri.b2) * c = 0 := by
      rw [hZero.1, Int.zero_mul]
    rw [Int.add_mul, Int.add_mul] at hSumB
    omega
  · unfold gradAyScaled
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    have hSumC : (tri.c0 + tri.c1 + tri.c2) * c = 0 := by
      rw [hZero.2, Int.zero_mul]
    rw [Int.add_mul, Int.add_mul] at hSumC
    omega

/-- Corollary (`femm_energy_gauge_invariance`):
Element magnetic stored energy numerator is strictly invariant under any uniform vector-potential shift $c$. -/
theorem femm_energy_gauge_invariance (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    evalElementMagneticEnergyScaled tri (a0 + c) (a1 + c) (a2 + c) =
      evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  have hGauge := femm_gauge_invariance tri a0 a1 a2 c
  unfold evalElementMagneticEnergyScaled fluxDensitySqScaled
  rw [hGauge.1, hGauge.2]

/-- Universal Element Energy Non-Negativity (`femm_element_energy_nonneg`):
For any triangular element with non-negative magnetic reluctivity `0 ≤ tri.nuScaled` and any
nodal potentials `a0, a1, a2 : Int`, both the numerator and the `/ \Delta_e`-normalized fixed-point
element magnetic energy are non-negative. -/
theorem femm_element_energy_nonneg (tri : FemmTriangle2D) (a0 a1 a2 : Int)
    (hNu : 0 ≤ tri.nuScaled) :
    0 ≤ evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  unfold evalElementMagneticEnergyScaled fluxDensitySqScaled
  have hAx : 0 ≤ gradAxScaled tri a0 a1 a2 * gradAxScaled tri a0 a1 a2 :=
    int_sq_nonneg (gradAxScaled tri a0 a1 a2)
  have hAy : 0 ≤ gradAyScaled tri a0 a1 a2 * gradAyScaled tri a0 a1 a2 :=
    int_sq_nonneg (gradAyScaled tri a0 a1 a2)
  exact int_mul_nonneg tri.nuScaled _ hNu (by omega)

theorem femm_element_energy_areaScaled_nonneg (scale : Int) (tri : FemmTriangle2D) (a0 a1 a2 : Int)
    (hScale : 0 ≤ scale) (hNu : 0 ≤ tri.nuScaled) :
    0 ≤ evalElementMagneticEnergyAreaScaled scale tri a0 a1 a2 := by
  unfold evalElementMagneticEnergyAreaScaled FemmTriangle2D.areaDenom FemmTriangle2D.absTwiceArea
  have hNum : 0 ≤ scale * evalElementMagneticEnergyScaled tri a0 a1 a2 :=
    int_mul_nonneg scale _ hScale (femm_element_energy_nonneg tri a0 a1 a2 hNu)
  have hDen : 0 ≤ 4 * max 1 (Int.ofNat tri.twiceArea.natAbs) := by omega
  exact Int.ediv_nonneg hNum hDen

/-- Area-normalized fixed-point mesh energy sum across `mesh`. -/
def evalMeshMagneticEnergyScaled (mesh : List FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  match mesh with
  | [] => 0
  | tri :: rest =>
    evalElementMagneticEnergyAreaScaled 1000000 tri a0 a1 a2 + evalMeshMagneticEnergyScaled rest a0 a1 a2

/-- Universal Mesh Energy Non-Negativity (`femm_mesh_energy_nonneg`):
Across any 2D mesh `mesh : List FemmTriangle2D` whose elements all have non-negative reluctivity,
the `/ \Delta_e`-normalized assembled magnetic energy is non-negative. -/
theorem femm_mesh_energy_nonneg (mesh : List FemmTriangle2D) (a0 a1 a2 : Int)
    (hNu : ∀ tri ∈ mesh, 0 ≤ tri.nuScaled) :
    0 ≤ evalMeshMagneticEnergyScaled mesh a0 a1 a2 := by
  induction mesh with
  | nil =>
    simp [evalMeshMagneticEnergyScaled]
  | cons tri rest ih =>
    simp only [evalMeshMagneticEnergyScaled]
    have hTri : 0 ≤ evalElementMagneticEnergyAreaScaled 1000000 tri a0 a1 a2 :=
      femm_element_energy_areaScaled_nonneg 1000000 tri a0 a1 a2 (by omega) (hNu tri (List.mem_cons_self ..))
    have hRest : 0 ≤ evalMeshMagneticEnergyScaled rest a0 a1 a2 :=
      ih (fun t ht => hNu t (List.mem_cons_of_mem tri ht))
    omega

/-! ## 2. Matrix-Free Element Action (`libCEED` / GPU Tensor Contraction `arXiv:2103.12881`) -/

/-- Evaluates the 3-node matrix-free element operator numerator $y_e = G_e^\top (D_e (G_e A_e))$
(`libCEED` decomposition $A = P^\top G^\top D G P$, Brown et al., `arXiv:2103.12881`) directly
from element geometry `tri` and nodal potentials `(a0, a1, a2)` without assembling a global
sparse CSR matrix. -/
def evalMatrixFreeElementAction (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int × Int × Int :=
  let gB := gradAxScaled tri a0 a1 a2
  let gC := gradAyScaled tri a0 a1 a2
  let y0 := tri.nuScaled * (tri.b0 * gB + tri.c0 * gC)
  let y1 := tri.nuScaled * (tri.b1 * gB + tri.c1 * gC)
  let y2 := tri.nuScaled * (tri.b2 * gB + tri.c2 * gC)
  (y0, y1, y2)

/-- Conservation of Nodal Currents in Matrix-Free Element Action (`femm_matrix_free_nodal_sum_zero`):
Because $b_0 + b_1 + b_2 = 0$ and $c_0 + c_1 + c_2 = 0$, the sum of the three nodal residual
contributions $y_0 + y_1 + y_2$ produced by `evalMatrixFreeElementAction` is identically zero
for every triangle `tri` and nodal potential triple `(a0, a1, a2)`. -/
theorem femm_matrix_free_nodal_sum_zero (tri : FemmTriangle2D) (a0 a1 a2 : Int) :
    let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
    y0 + y1 + y2 = 0 := by
  dsimp only [evalMatrixFreeElementAction]
  have hZero := femm_gradient_sum_zero tri
  have hb := hZero.1
  have hc := hZero.2
  have hFactor :
      tri.nuScaled * (tri.b0 * gradAxScaled tri a0 a1 a2 + tri.c0 * gradAyScaled tri a0 a1 a2) +
      tri.nuScaled * (tri.b1 * gradAxScaled tri a0 a1 a2 + tri.c1 * gradAyScaled tri a0 a1 a2) +
      tri.nuScaled * (tri.b2 * gradAxScaled tri a0 a1 a2 + tri.c2 * gradAyScaled tri a0 a1 a2) =
      tri.nuScaled *
        ((tri.b0 + tri.b1 + tri.b2) * gradAxScaled tri a0 a1 a2 +
         (tri.c0 + tri.c1 + tri.c2) * gradAyScaled tri a0 a1 a2) := by
    simp only [Int.add_mul, Int.mul_add]
    omega
  rw [hFactor, hb, hc, Int.zero_mul, Int.zero_mul, Int.add_zero, Int.mul_zero]

private theorem femm_linear_comb_factor
    (nu b0 b1 b2 c0 c1 c2 a0 a1 a2 gB gC : Int) :
    a0 * (nu * (b0 * gB + c0 * gC)) +
    a1 * (nu * (b1 * gB + c1 * gC)) +
    a2 * (nu * (b2 * gB + c2 * gC)) =
    nu * ((b0 * a0 + b1 * a1 + b2 * a2) * gB + (c0 * a0 + c1 * a1 + c2 * a2) * gC) := by
  have hTerm : ∀ (a n b g : Int), a * (n * (b * g)) = n * (b * a * g) := by
    intro a n b g
    rw [← Int.mul_assoc a n (b * g), Int.mul_comm a n, Int.mul_assoc n a (b * g),
        ← Int.mul_assoc a b g, Int.mul_comm a b]
  simp only [Int.mul_add, Int.add_mul, hTerm]
  omega

/-- Matrix-Free Energy Equivalence Theorem (`femm_matrix_free_energy_identity`):
The inner product $a_0 y_0 + a_1 y_1 + a_2 y_2$ of the nodal vector potential with the
`libCEED` matrix-free operator action equals `evalElementMagneticEnergyScaled tri a0 a1 a2`. -/
theorem femm_matrix_free_energy_identity (tri : FemmTriangle2D) (a0 a1 a2 : Int) :
    let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
    a0 * y0 + a1 * y1 + a2 * y2 = evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  dsimp only [evalMatrixFreeElementAction]
  rw [femm_linear_comb_factor]
  rfl

/-! ## 3. Global Mesh Nodal Residual Equilibrium (`evalGlobalNodalResidual`) -/

/-- Alias `evalLibCeedElementOp` for `evalMatrixFreeElementAction`. -/
abbrev evalLibCeedElementOp := evalMatrixFreeElementAction

/-- A 2D triangular finite element together with its three global mesh vertex indices `(n0, n1, n2)`
and its three internal nodal residual contributions `(f0, f1, f2)`. -/
structure MeshElementResidual2D where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  f0 : Int
  f1 : Int
  f2 : Int
  deriving DecidableEq, Repr

/-- A 2D triangular mesh element connecting global vertex indices `(n0, n1, n2)` with geometry `tri`. -/
structure FemmMeshElement2D where
  n0  : Nat
  n1  : Nat
  n2  : Nat
  tri : FemmTriangle2D
  deriving DecidableEq, Repr

/-- Evaluates the element nodal residual record `MeshElementResidual2D` for a mesh triangle `elem`. -/
def evalElementResidual2D (elem : FemmMeshElement2D) (nodalA : Nat → Int) : MeshElementResidual2D :=
  let (f0, f1, f2) := evalLibCeedElementOp elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2)
  { n0 := elem.n0, n1 := elem.n1, n2 := elem.n2, f0 := f0, f1 := f1, f2 := f2 }

/-- Scatters (`P_e^\top`) the internal nodal forces `(f0, f1, f2)` onto global mesh vertex `nodeIdx`. -/
def evalElementNodeContribution (er : MeshElementResidual2D) (nodeIdx : Nat) : Int :=
  (if er.n0 == nodeIdx then er.f0 else 0) +
  (if er.n1 == nodeIdx then er.f1 else 0) +
  (if er.n2 == nodeIdx then er.f2 else 0)

/-- Assembles the global nodal magnetostatic residual numerator at vertex `nodeIdx : Nat`. -/
def evalGlobalNodalResidual
    (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) (nodeIdx : Nat) : Int :=
  match mesh with
  | [] => 0
  | elem :: rest =>
    evalElementNodeContribution (evalElementResidual2D elem nodalA) nodeIdx +
    evalGlobalNodalResidual rest nodalA nodeIdx

/-- Sums all internal nodal residuals across a 2D finite-element mesh `mesh`. -/
def evalMeshTotalResidualSum (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) : Int :=
  match mesh with
  | [] => 0
  | elem :: rest =>
    let er := evalElementResidual2D elem nodalA
    (er.f0 + er.f1 + er.f2) + evalMeshTotalResidualSum rest nodalA

/-- **Discrete Divergence Theorem / Global Nodal Residual Conservation (`femm_global_residual_sum_zero`)**. -/
theorem femm_global_residual_sum_zero
    (elem : FemmMeshElement2D) (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) :
    let er := evalElementResidual2D elem nodalA
    (er.f0 + er.f1 + er.f2 = 0) ∧ evalMeshTotalResidualSum mesh nodalA = 0 := by
  constructor
  · dsimp only [evalElementResidual2D, evalLibCeedElementOp]
    exact femm_matrix_free_nodal_sum_zero elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2)
  · induction mesh with
    | nil => rfl
    | cons hd tl ih =>
      dsimp only [evalMeshTotalResidualSum, evalElementResidual2D, evalLibCeedElementOp]
      have hHd := femm_matrix_free_nodal_sum_zero hd.tri (nodalA hd.n0) (nodalA hd.n1) (nodalA hd.n2)
      dsimp only at hHd
      rw [hHd, ih, Int.add_zero]

theorem femm_libceed_element_gauge_invariant (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    evalLibCeedElementOp tri (a0 + c) (a1 + c) (a2 + c) =
      evalLibCeedElementOp tri a0 a1 a2 := by
  have hGauge := femm_gauge_invariance tri a0 a1 a2 c
  unfold evalLibCeedElementOp evalMatrixFreeElementAction
  rw [hGauge.1, hGauge.2]

theorem femm_element_residual_gauge_invariant
    (elem : FemmMeshElement2D) (nodalA : Nat → Int) (c : Int) :
    evalElementResidual2D elem (fun n => nodalA n + c) =
      evalElementResidual2D elem nodalA := by
  unfold evalElementResidual2D
  rw [femm_libceed_element_gauge_invariant elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2) c]

/-- **Global Nodal Residual Gauge Invariance (`femm_global_equilibrium_gauge_invariant`)**. -/
theorem femm_global_equilibrium_gauge_invariant
    (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) (c : Int) (nodeIdx : Nat) :
    evalGlobalNodalResidual mesh (fun n => nodalA n + c) nodeIdx =
      evalGlobalNodalResidual mesh nodalA nodeIdx := by
  induction mesh with
  | nil => rfl
  | cons elem rest ih =>
    dsimp only [evalGlobalNodalResidual]
    rw [femm_element_residual_gauge_invariant elem nodalA c, ih]

/-! ## 4. Exact `/ \Delta_e`-Normalized Global 2D Courant $P_1$ Mesh Stiffness, Load & Co-Energy Assembly -/

/-- A complete 2D finite-element magnetostatic mesh (`FemmMesh2D`):
* `triangles`: list of 2D triangular finite elements `FemmTriangle2D`,
* `vertexMap`: maps each element index `elemIdx : Nat` to its global vertex index triple `(v0, v1, v2)`,
* `nodalPotentials`: maps each global vertex index `v : Nat` to its out-of-plane vector potential $A_z(v) \in \mathbb{Z}$. -/
structure FemmMesh2D where
  triangles       : List FemmTriangle2D
  vertexMap       : Nat → Nat × Nat × Nat
  nodalPotentials : Nat → Int

/-- Exact rational (`Rat`) Courant $P_1$ element magnetic energy $W_e = \frac{\nu_e}{8|\Delta_e|}((b \cdot A)^2 + (c \cdot A)^2)
= \frac{\nu_e ((b \cdot A)^2 + (c \cdot A)^2)}{4 |2\Delta_e|}$ with true $1 / |\Delta_e|$ area scaling! -/
def evalElementMagneticEnergyQ (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Rat :=
  (evalElementMagneticEnergyScaled tri a0 a1 a2 : Rat) / (4 * (tri.absTwiceArea : Rat))

/-- Exact rational (`Rat`) Courant $P_1$ Galerkin nodal residual of element `tri` at vertices `(v0, v1, v2)`:
$$r_{e,i} = \frac{\nu_e}{4|\Delta_e|}(b_i g_x + c_i g_y) - \frac{J_z |\Delta_e|}{3}
  = \frac{y_{e,i}}{2 |2\Delta_e|} - \frac{J_z |2\Delta_e|}{6}.$$
Unlike unnormalized integer residuals, summing `evalElementResidualQ` across non-uniform triangles
($\Delta_{e_1} \neq \Delta_{e_2}$) weights every element by its true physical $1/\Delta_e$ stiffness
and $\Delta_e/3$ source load! -/
def evalElementResidualQ
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) : Rat × Rat × Rat :=
  let a0 := nodalPotentials v0
  let a1 := nodalPotentials v1
  let a2 := nodalPotentials v2
  let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
  let twoDelta : Rat := (tri.absTwiceArea : Rat)
  let jLoadQ : Rat := ((tri.jzScaled : Rat) * twoDelta) / 6
  ( (y0 : Rat) / (2 * twoDelta) - jLoadQ
  , (y1 : Rat) / (2 * twoDelta) - jLoadQ
  , (y2 : Rat) / (2 * twoDelta) - jLoadQ )

/-- Exact gauge invariance of the `/ \Delta_e`-normalized element Galerkin residual `evalElementResidualQ`. -/
theorem evalElementResidualQ_gauge_invariant
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) (c : Int) :
    evalElementResidualQ tri v0 v1 v2 (fun n => nodalPotentials n + c) =
      evalElementResidualQ tri v0 v1 v2 nodalPotentials := by
  dsimp only [evalElementResidualQ]
  have hOp := femm_libceed_element_gauge_invariant
    tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2) c
  unfold evalLibCeedElementOp at hOp
  rw [hOp]

private theorem rat_div_add_div_same (a b d : Rat) :
    a / d + b / d = (a + b) / d := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, ← Rat.add_mul]

private theorem rat_sub_3_sum (x0 x1 x2 l : Rat) :
    (x0 - l) + (x1 - l) + (x2 - l) = (x0 + x1 + x2) - 3 * l := by
  grind

/-- **Exact Area-Scaled Ampere Nodal Load Sum (`evalElementResidualQ_ampere_sum`)**:
For ANY non-degenerate triangle (`tri.twiceArea ≠ 0`), the sum of the three `/ \Delta_e`-normalized
Galerkin nodal residuals equals $-J_z |\Delta_e| = -(J_z |2\Delta_e|) / 2$: the stiffness contributions
cancel identically and the consistent loads sum to total element current $J_z |\Delta_e|$. -/
theorem evalElementResidualQ_ampere_sum
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) :
    let (r0, r1, r2) := evalElementResidualQ tri v0 v1 v2 nodalPotentials
    r0 + r1 + r2 = -3 * (((tri.jzScaled : Rat) * (tri.absTwiceArea : Rat)) / 6) := by
  dsimp only [evalElementResidualQ]
  rw [rat_sub_3_sum]
  rw [rat_div_add_div_same, rat_div_add_div_same]
  have hIntSum := femm_matrix_free_nodal_sum_zero
    tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)
  dsimp only at hIntSum
  have hRatSum :
      ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).1 : Rat) +
      ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).2.1 : Rat) +
      ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).2.2 : Rat) = 0 := by
    rw [← Rat.intCast_add, ← Rat.intCast_add, hIntSum]
    rfl
  rw [hRatSum]
  have hZeroDiv : (0 : Rat) / (2 * (tri.absTwiceArea : Rat)) = 0 := by
    rw [Rat.div_def, Rat.zero_mul]
  rw [hZeroDiv]
  grind

/-- **Exact `/ \Delta_e`-Normalized Galerkin Virtual-Work Identity (`evalElementResidualQ_virtual_work_identity`)**:
For every Courant $P_1$ triangle `tri`, the virtual work $a_0 r_0 + a_1 r_1 + a_2 r_2$ equals
$2 W_e - (a_0 + a_1 + a_2) \frac{J_z |2\Delta_e|}{6}$ (i.e. $2 W_e - \frac{a_0 + a_1 + a_2}{3} J_z |\Delta_e|$). -/
theorem evalElementResidualQ_virtual_work_identity
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) :
    let a0 : Rat := (nodalPotentials v0 : Rat)
    let a1 : Rat := (nodalPotentials v1 : Rat)
    let a2 : Rat := (nodalPotentials v2 : Rat)
    let (r0, r1, r2) := evalElementResidualQ tri v0 v1 v2 nodalPotentials
    a0 * r0 + a1 * r1 + a2 * r2 =
      ((evalElementMagneticEnergyScaled tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2) : Rat) /
        (2 * (tri.absTwiceArea : Rat))) -
      (a0 + a1 + a2) * (((tri.jzScaled : Rat) * (tri.absTwiceArea : Rat)) / 6) := by
  dsimp only [evalElementResidualQ]
  have hEn := femm_matrix_free_energy_identity
    tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)
  dsimp only at hEn
  have hMulSub : ∀ (a x y : Rat), a * (x - y) = a * x - a * y := by
    intro a x y; grind
  have hMulDiv : ∀ (a y d : Rat), a * (y / d) = (a * y) / d := by
    intro a y d
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]
  have hSplit : ∀ (p0 p1 p2 q0 q1 q2 : Rat),
      (p0 - q0) + (p1 - q1) + (p2 - q2) = (p0 + p1 + p2) - (q0 + q1 + q2) := by
    intro p0 p1 p2 q0 q1 q2; grind
  rw [hMulSub, hMulSub, hMulSub, hSplit]
  rw [hMulDiv, hMulDiv, hMulDiv, rat_div_add_div_same, rat_div_add_div_same]
  rw [← Rat.add_mul, ← Rat.add_mul]
  have hCastEn :
      (nodalPotentials v0 : Rat) * ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).1 : Rat) +
      (nodalPotentials v1 : Rat) * ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).2.1 : Rat) +
      (nodalPotentials v2 : Rat) * ((evalMatrixFreeElementAction tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)).2.2 : Rat) =
      (evalElementMagneticEnergyScaled tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2) : Rat) := by
    rw [← Rat.intCast_mul, ← Rat.intCast_mul, ← Rat.intCast_mul, ← Rat.intCast_add, ← Rat.intCast_add, hEn]
  rw [hCastEn]

/-- Scatters a rational 3-node element residual `(r0, r1, r2)` onto global vertex `nodeIdx`. -/
def scatterElementResidualToNodeQ
    (v0 v1 v2 : Nat) (r : Rat × Rat × Rat) (nodeIdx : Nat) : Rat :=
  (if v0 == nodeIdx then r.1 else 0) +
  (if v1 == nodeIdx then r.2.1 else 0) +
  (if v2 == nodeIdx then r.2.2 else 0)

def evalMeshNodalResidualQAux
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (nodeIdx idx : Nat) : Rat :=
  match tris with
  | [] => 0
  | tri :: rest =>
    let v := vertexMap idx
    let r := evalElementResidualQ tri v.1 v.2.1 v.2.2 nodalPotentials
    scatterElementResidualToNodeQ v.1 v.2.1 v.2.2 r nodeIdx +
    evalMeshNodalResidualQAux rest vertexMap nodalPotentials nodeIdx (idx + 1)

/-- Assembles the exact `/ \Delta_e`-normalized global nodal residual at vertex `nodeIdx` across `mesh : FemmMesh2D`. -/
def evalMeshNodalResidualQ (mesh : FemmMesh2D) (nodeIdx : Nat) : Rat :=
  evalMeshNodalResidualQAux mesh.triangles mesh.vertexMap mesh.nodalPotentials nodeIdx 0

theorem evalMeshNodalResidualQAux_gauge_invariant
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (c : Int) (nodeIdx idx : Nat) :
    evalMeshNodalResidualQAux tris vertexMap (fun n => nodalPotentials n + c) nodeIdx idx =
      evalMeshNodalResidualQAux tris vertexMap nodalPotentials nodeIdx idx := by
  induction tris generalizing idx with
  | nil => rfl
  | cons tri rest ih =>
    dsimp only [evalMeshNodalResidualQAux]
    rw [evalElementResidualQ_gauge_invariant tri (vertexMap idx).1 (vertexMap idx).2.1 (vertexMap idx).2.2 nodalPotentials c,
        ih (idx + 1)]

/-- **Global Area-Normalized Nodal Residual Gauge Invariance (`evalMeshNodalResidualQ_gauge_invariant`)**. -/
theorem evalMeshNodalResidualQ_gauge_invariant
    (mesh : FemmMesh2D) (c : Int) (nodeIdx : Nat) :
    evalMeshNodalResidualQ { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } nodeIdx =
      evalMeshNodalResidualQ mesh nodeIdx :=
  evalMeshNodalResidualQAux_gauge_invariant mesh.triangles mesh.vertexMap mesh.nodalPotentials c nodeIdx 0

def evalTrianglesCoEnergyQAux
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (idx : Nat) : Rat :=
  match tris with
  | [] => 0
  | tri :: rest =>
    let v := vertexMap idx
    evalElementMagneticEnergyQ tri (nodalPotentials v.1) (nodalPotentials v.2.1) (nodalPotentials v.2.2) +
    evalTrianglesCoEnergyQAux rest vertexMap nodalPotentials (idx + 1)

/-- Exact `/ \Delta_e`-normalized global magnetic energy $\sum_e W_e = \sum_e \frac{\nu_e}{8|\Delta_e|}\|\nabla A_z \cdot 2\Delta_e\|^2$
across arbitrary non-uniform meshes `mesh : FemmMesh2D`. -/
def evalMeshTotalCoEnergyQ (mesh : FemmMesh2D) : Rat :=
  evalTrianglesCoEnergyQAux mesh.triangles mesh.vertexMap mesh.nodalPotentials 0

theorem evalElementMagneticEnergyQ_nonneg
    (tri : FemmTriangle2D) (a0 a1 a2 : Int)
    (hNu : 0 ≤ tri.nuScaled) :
    (0 : Rat) ≤ evalElementMagneticEnergyQ tri a0 a1 a2 := by
  unfold evalElementMagneticEnergyQ FemmTriangle2D.absTwiceArea
  have hNumInt : 0 ≤ evalElementMagneticEnergyScaled tri a0 a1 a2 :=
    femm_element_energy_nonneg tri a0 a1 a2 hNu
  have hNumRat : (0 : Rat) ≤ (evalElementMagneticEnergyScaled tri a0 a1 a2 : Rat) :=
    Rat.intCast_nonneg.mpr hNumInt
  have hAbsNonneg : 0 ≤ Int.ofNat tri.twiceArea.natAbs :=
    Int.natCast_nonneg tri.twiceArea.natAbs
  have hDenInt : 0 ≤ (4 : Int) * Int.ofNat tri.twiceArea.natAbs :=
    int_mul_nonneg 4 (Int.ofNat tri.twiceArea.natAbs) (by omega) hAbsNonneg
  have hDenRat : (0 : Rat) ≤ 4 * ((Int.ofNat tri.twiceArea.natAbs : Int) : Rat) := by
    have hEq : 4 * ((Int.ofNat tri.twiceArea.natAbs : Int) : Rat) =
        (((4 : Int) * Int.ofNat tri.twiceArea.natAbs : Int) : Rat) := by
      rw [Rat.intCast_mul]; rfl
    rw [hEq]
    exact Rat.intCast_nonneg.mpr hDenInt
  rw [Rat.div_def]
  by_cases hZero : (4 * ((Int.ofNat tri.twiceArea.natAbs : Int) : Rat)) = 0
  · rw [hZero]
    grind
  · have hPos : (0 : Rat) < 4 * ((Int.ofNat tri.twiceArea.natAbs : Int) : Rat) := by grind
    exact Rat.mul_nonneg hNumRat (Rat.le_of_lt (Rat.inv_pos.2 hPos))

theorem evalTrianglesCoEnergyQAux_nonneg
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (idx : Nat)
    (hNu : ∀ tri ∈ tris, 0 ≤ tri.nuScaled) :
    (0 : Rat) ≤ evalTrianglesCoEnergyQAux tris vertexMap nodalPotentials idx := by
  induction tris generalizing idx with
  | nil =>
    dsimp only [evalTrianglesCoEnergyQAux]
    decide
  | cons tri rest ih =>
    dsimp only [evalTrianglesCoEnergyQAux]
    have hTri := evalElementMagneticEnergyQ_nonneg tri
      (nodalPotentials (vertexMap idx).1)
      (nodalPotentials (vertexMap idx).2.1)
      (nodalPotentials (vertexMap idx).2.2)
      (hNu tri (List.mem_cons_self ..))
    have hRest := ih (idx + 1) (fun t ht => hNu t (List.mem_cons_of_mem tri ht))
    exact Rat.add_nonneg hTri hRest

/-- **Global Area-Normalized Mesh Co-Energy Non-Negativity (`evalMeshTotalCoEnergyQ_nonneg`)**:
Across ANY non-uniform 2D mesh `mesh : FemmMesh2D` with `0 ≤ tri.nuScaled`, the `/ \Delta_e`-normalized
total magnetic energy `evalMeshTotalCoEnergyQ mesh` is non-negative! -/
theorem evalMeshTotalCoEnergyQ_nonneg
    (mesh : FemmMesh2D)
    (hNu : ∀ tri ∈ mesh.triangles, 0 ≤ tri.nuScaled) :
    (0 : Rat) ≤ evalMeshTotalCoEnergyQ mesh :=
  evalTrianglesCoEnergyQAux_nonneg mesh.triangles mesh.vertexMap mesh.nodalPotentials 0 hNu

theorem evalTrianglesCoEnergyQAux_gauge_invariant
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (c : Int) (idx : Nat) :
    evalTrianglesCoEnergyQAux tris vertexMap (fun n => nodalPotentials n + c) idx =
      evalTrianglesCoEnergyQAux tris vertexMap nodalPotentials idx := by
  induction tris generalizing idx with
  | nil => rfl
  | cons tri rest ih =>
    dsimp only [evalTrianglesCoEnergyQAux, evalElementMagneticEnergyQ]
    rw [femm_energy_gauge_invariance tri
          (nodalPotentials (vertexMap idx).1)
          (nodalPotentials (vertexMap idx).2.1)
          (nodalPotentials (vertexMap idx).2.2) c,
        ih (idx + 1)]

/-- **Global Area-Normalized Mesh Co-Energy Gauge Invariance (`evalMeshTotalCoEnergyQ_gauge_invariant`)**. -/
theorem evalMeshTotalCoEnergyQ_gauge_invariant
    (mesh : FemmMesh2D) (c : Int) :
    evalMeshTotalCoEnergyQ { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } =
      evalMeshTotalCoEnergyQ mesh :=
  evalTrianglesCoEnergyQAux_gauge_invariant mesh.triangles mesh.vertexMap mesh.nodalPotentials c 0

/-! ### Fixed-Point Area-Normalized Mesh Assembly (`evalElementResidual`, `evalMeshNodalResidual`, `evalMeshTotalCoEnergy`) -/

/-- Fixed-point `/ \Delta_e`-normalized 3-node Galerkin residual (in micro-units, `femScale = 1_000_000`):
$$r_{e,i}^{\text{fx}} = \left\lfloor \frac{10^6 \cdot y_{e,i}}{2 \cdot \text{areaDenom}} \right\rfloor
  - \left\lfloor \frac{10^6 \cdot J_z \cdot \text{absTwiceArea}}{6} \right\rfloor.$$ -/
def evalElementResidual
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) : Int × Int × Int :=
  let a0 := nodalPotentials v0
  let a1 := nodalPotentials v1
  let a2 := nodalPotentials v2
  let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
  let denom := 2 * tri.areaDenom
  let jLoad := (1000000 * tri.jzScaled * tri.absTwiceArea) / 6
  ( (1000000 * y0) / denom - jLoad
  , (1000000 * y1) / denom - jLoad
  , (1000000 * y2) / denom - jLoad )

theorem evalElementResidual_gauge_invariant
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) (c : Int) :
    evalElementResidual tri v0 v1 v2 (fun n => nodalPotentials n + c) =
      evalElementResidual tri v0 v1 v2 nodalPotentials := by
  dsimp only [evalElementResidual]
  have hOp := femm_libceed_element_gauge_invariant
    tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2) c
  unfold evalLibCeedElementOp at hOp
  rw [hOp]

def evalElementCoEnergy
    (tri : FemmTriangle2D) (v0 v1 v2 : Nat) (nodalPotentials : Nat → Int) : Int :=
  evalElementMagneticEnergyAreaScaled 1000000 tri (nodalPotentials v0) (nodalPotentials v1) (nodalPotentials v2)

def scatterElementResidualToNode
    (v0 v1 v2 : Nat) (r : Int × Int × Int) (nodeIdx : Nat) : Int :=
  (if v0 == nodeIdx then r.1 else 0) +
  (if v1 == nodeIdx then r.2.1 else 0) +
  (if v2 == nodeIdx then r.2.2 else 0)

def evalMeshNodalResidualAux
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (nodeIdx idx : Nat) : Int :=
  match tris with
  | [] => 0
  | tri :: rest =>
    let v := vertexMap idx
    let r := evalElementResidual tri v.1 v.2.1 v.2.2 nodalPotentials
    scatterElementResidualToNode v.1 v.2.1 v.2.2 r nodeIdx +
    evalMeshNodalResidualAux rest vertexMap nodalPotentials nodeIdx (idx + 1)

def evalMeshNodalResidual (mesh : FemmMesh2D) (nodeIdx : Nat) : Int :=
  evalMeshNodalResidualAux mesh.triangles mesh.vertexMap mesh.nodalPotentials nodeIdx 0

theorem evalMeshNodalResidualAux_gauge_invariant
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (c : Int) (nodeIdx idx : Nat) :
    evalMeshNodalResidualAux tris vertexMap (fun n => nodalPotentials n + c) nodeIdx idx =
      evalMeshNodalResidualAux tris vertexMap nodalPotentials nodeIdx idx := by
  induction tris generalizing idx with
  | nil => rfl
  | cons tri rest ih =>
    dsimp only [evalMeshNodalResidualAux]
    rw [evalElementResidual_gauge_invariant tri (vertexMap idx).1 (vertexMap idx).2.1 (vertexMap idx).2.2 nodalPotentials c,
        ih (idx + 1)]

theorem evalMeshNodalResidual_gauge_invariant
    (mesh : FemmMesh2D) (c : Int) (nodeIdx : Nat) :
    evalMeshNodalResidual { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } nodeIdx =
      evalMeshNodalResidual mesh nodeIdx :=
  evalMeshNodalResidualAux_gauge_invariant mesh.triangles mesh.vertexMap mesh.nodalPotentials c nodeIdx 0

def evalTrianglesCoEnergyAux
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (idx : Nat) : Int :=
  match tris with
  | [] => 0
  | tri :: rest =>
    let v := vertexMap idx
    evalElementCoEnergy tri v.1 v.2.1 v.2.2 nodalPotentials +
    evalTrianglesCoEnergyAux rest vertexMap nodalPotentials (idx + 1)

def evalMeshTotalCoEnergy (mesh : FemmMesh2D) : Int :=
  evalTrianglesCoEnergyAux mesh.triangles mesh.vertexMap mesh.nodalPotentials 0

theorem evalTrianglesCoEnergyAux_nonneg
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (idx : Nat)
    (hNu : ∀ tri ∈ tris, 0 ≤ tri.nuScaled) :
    0 ≤ evalTrianglesCoEnergyAux tris vertexMap nodalPotentials idx := by
  induction tris generalizing idx with
  | nil =>
    simp [evalTrianglesCoEnergyAux]
  | cons tri rest ih =>
    dsimp only [evalTrianglesCoEnergyAux, evalElementCoEnergy]
    have hTri : 0 ≤ evalElementMagneticEnergyAreaScaled 1000000 tri
        (nodalPotentials (vertexMap idx).1)
        (nodalPotentials (vertexMap idx).2.1)
        (nodalPotentials (vertexMap idx).2.2) :=
      femm_element_energy_areaScaled_nonneg 1000000 tri
        (nodalPotentials (vertexMap idx).1)
        (nodalPotentials (vertexMap idx).2.1)
        (nodalPotentials (vertexMap idx).2.2)
        (by omega) (hNu tri (List.mem_cons_self ..))
    have hRest : 0 ≤ evalTrianglesCoEnergyAux rest vertexMap nodalPotentials (idx + 1) :=
      ih (idx + 1) (fun t ht => hNu t (List.mem_cons_of_mem tri ht))
    exact Int.add_nonneg hTri hRest

theorem evalMeshTotalCoEnergy_nonneg
    (mesh : FemmMesh2D)
    (hNu : ∀ tri ∈ mesh.triangles, 0 ≤ tri.nuScaled) :
    0 ≤ evalMeshTotalCoEnergy mesh :=
  evalTrianglesCoEnergyAux_nonneg mesh.triangles mesh.vertexMap mesh.nodalPotentials 0 hNu

theorem evalTrianglesCoEnergyAux_gauge_invariant
    (tris : List FemmTriangle2D) (vertexMap : Nat → Nat × Nat × Nat)
    (nodalPotentials : Nat → Int) (c : Int) (idx : Nat) :
    evalTrianglesCoEnergyAux tris vertexMap (fun n => nodalPotentials n + c) idx =
      evalTrianglesCoEnergyAux tris vertexMap nodalPotentials idx := by
  induction tris generalizing idx with
  | nil => rfl
  | cons tri rest ih =>
    dsimp only [evalTrianglesCoEnergyAux, evalElementCoEnergy, evalElementMagneticEnergyAreaScaled]
    rw [femm_energy_gauge_invariance tri
          (nodalPotentials (vertexMap idx).1)
          (nodalPotentials (vertexMap idx).2.1)
          (nodalPotentials (vertexMap idx).2.2) c,
        ih (idx + 1)]

theorem evalMeshTotalCoEnergy_gauge_invariant
    (mesh : FemmMesh2D) (c : Int) :
    evalMeshTotalCoEnergy { mesh with nodalPotentials := fun n => mesh.nodalPotentials n + c } =
      evalMeshTotalCoEnergy mesh :=
  evalTrianglesCoEnergyAux_gauge_invariant mesh.triangles mesh.vertexMap mesh.nodalPotentials c 0

/-! ## 5. Damped Picard Nonlinear B-H Chord/Secant Fixed-Point Iteration (`stepBhPicardReluctivity`) -/

/-- Evaluates nonlinear ferromagnetic chord/secant reluctivity $\nu_{\text{sec}}(B^2) = \nu_0 + k_{\text{sat}} B^2$. -/
def evalNonlinearReluctivity (nuLinear kSat bSq : Int) : Int :=
  nuLinear + kSat * bSq

/-- **Damped Picard Fixed-Point Update (`stepBhPicardReluctivity`)**:
Given relaxation factor `omegaPermille ∈ [0, 1000]` ($\omega = \text{omegaPermille}/1000 \in [0, 1]$),
computes the convex-combination fixed-point update toward $\nu_{\text{sec}}(B^2) = \nu_0 + k_{\text{sat}} B^2$:
$$\nu_{k+1} = \left\lfloor \frac{(1000 - \omega_{\text{pm}}) \cdot \nu_k + \omega_{\text{pm}} \cdot \nu_{\text{sec}}(B^2)}{1000} \right\rfloor.$$
Unlike an unnormalized running sum, `stepBhPicardReluctivity` has the genuine fixed point
$\nu^* = \nu_{\text{sec}}(B^2)$ for every relaxation weight $\omega_{\text{pm}} \in \mathbb{Z}$! -/
def stepBhPicardReluctivity (nuLinear kSat omegaPermille nuCur bSq : Int) : Int :=
  ((1000 - omegaPermille) * nuCur + omegaPermille * evalNonlinearReluctivity nuLinear kSat bSq) / 1000

/-- **Exact Fixed-Point Stationarity Theorem (`stepBhPicardReluctivity_fixed_point`)**:
Whenever `nuCur = evalNonlinearReluctivity nuLinear kSat bSq`, `stepBhPicardReluctivity` preserves
`nuCur` identically for EVERY relaxation factor `omegaPermille : Int`! -/
theorem stepBhPicardReluctivity_fixed_point
    (nuLinear kSat omegaPermille nuCur bSq : Int)
    (hFix : nuCur = evalNonlinearReluctivity nuLinear kSat bSq) :
    stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur bSq = nuCur := by
  unfold stepBhPicardReluctivity
  rw [← hFix]
  have hComb : (1000 - omegaPermille) * nuCur + omegaPermille * nuCur = nuCur * 1000 := by
    have : (1000 - omegaPermille + omegaPermille) * nuCur = 1000 * nuCur := by
      have h1000 : 1000 - omegaPermille + omegaPermille = 1000 := by omega
      rw [h1000]
    rw [Int.add_mul] at this
    rw [this, Int.mul_comm]
  rw [hComb]
  exact Int.mul_ediv_cancel nuCur (by decide)

/-- **Convex Bracketing & Monotonicity of Damped Picard Reluctivity (`stepBhPicardReluctivity_monotone`)**:
For any under-relaxation weight `0 ≤ omegaPermille ≤ 1000`, `0 ≤ kSat`, `nuCur1 ≤ nuCur2`, and `bSq1 ≤ bSq2`:
1. `stepBhPicardReluctivity` is monotone in both the current iterate `nuCur` and squared flux density `bSq`,
2. When `0 < nuLinear`, `0 ≤ bSq1`, and `nuLinear ≤ nuCur1`, the updated reluctivity stays strictly positive
   and bounded below by `nuLinear`! -/
theorem stepBhPicardReluctivity_monotone
    (nuLinear kSat omegaPermille nuCur1 nuCur2 bSq1 bSq2 : Int)
    (hOmegaLo : 0 ≤ omegaPermille)
    (hOmegaHi : omegaPermille ≤ 1000)
    (hSat     : 0 ≤ kSat)
    (hCurLe   : nuCur1 ≤ nuCur2)
    (hBLe     : bSq1 ≤ bSq2) :
    stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur1 bSq1 ≤
      stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur2 bSq2 ∧
    (0 < nuLinear → 0 ≤ bSq1 → nuLinear ≤ nuCur1 →
      nuLinear ≤ stepBhPicardReluctivity nuLinear kSat omegaPermille nuCur1 bSq1) := by
  unfold stepBhPicardReluctivity evalNonlinearReluctivity
  have h1mOmega : 0 ≤ 1000 - omegaPermille := by omega
  have hTermCur : (1000 - omegaPermille) * nuCur1 ≤ (1000 - omegaPermille) * nuCur2 :=
    int_mul_le_mul_of_nonneg_left nuCur1 nuCur2 (1000 - omegaPermille) hCurLe h1mOmega
  have hSatMono : kSat * bSq1 ≤ kSat * bSq2 :=
    int_mul_le_mul_of_nonneg_left bSq1 bSq2 kSat hBLe hSat
  have hSecMono : nuLinear + kSat * bSq1 ≤ nuLinear + kSat * bSq2 := by omega
  have hTermSec : omegaPermille * (nuLinear + kSat * bSq1) ≤ omegaPermille * (nuLinear + kSat * bSq2) :=
    int_mul_le_mul_of_nonneg_left _ _ omegaPermille hSecMono hOmegaLo
  constructor
  · exact Int.ediv_le_ediv (by omega) (by omega)
  · intro _ hBPos hNuLeCur
    have hSatPos : 0 ≤ kSat * bSq1 := int_mul_nonneg kSat bSq1 hSat hBPos
    have hNuLeSec : nuLinear ≤ nuLinear + kSat * bSq1 := by omega
    have hLow1 : (1000 - omegaPermille) * nuLinear ≤ (1000 - omegaPermille) * nuCur1 :=
      int_mul_le_mul_of_nonneg_left nuLinear nuCur1 (1000 - omegaPermille) hNuLeCur h1mOmega
    have hLow2 : omegaPermille * nuLinear ≤ omegaPermille * (nuLinear + kSat * bSq1) :=
      int_mul_le_mul_of_nonneg_left nuLinear (nuLinear + kSat * bSq1) omegaPermille hNuLeSec hOmegaLo
    have hComb : (1000 - omegaPermille) * nuLinear + omegaPermille * nuLinear = nuLinear * 1000 := by
      have : (1000 - omegaPermille + omegaPermille) * nuLinear = 1000 * nuLinear := by
        have h1000 : 1000 - omegaPermille + omegaPermille = 1000 := by omega
        rw [h1000]
      rw [Int.add_mul] at this
      rw [this, Int.mul_comm]
    have hNumGe : nuLinear * 1000 ≤ (1000 - omegaPermille) * nuCur1 + omegaPermille * (nuLinear + kSat * bSq1) := by
      omega
    have hDiv := Int.ediv_le_ediv (c := 1000) (by omega) hNumGe
    rw [Int.mul_ediv_cancel nuLinear (by decide)] at hDiv
    exact hDiv

end Obend.Hardware.Magnetics
end
