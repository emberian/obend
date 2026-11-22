# Continuum Physics, Relativistic PDE Compilation, Open-Hypergraph Symmetry, and Silicon Verification

This document summarizes the mathematical specifications, machine-checked theorems, and hardware/GPU artifacts in `Obend` covering:

- hyperbolic balance laws, 1+1 Bona–Massó ADM/Z4c solvers, and a 3+1 Z4c constraint-propagation solver compiled by `#pde_solver` (§1.1, §1.2, §1.5);
- continuum-to-discrete truncation order, periodic summation by parts, and Lax–Wendroff weak-form residual bounds for the compiled schemes, carried through to the Q32.32 word trajectory (§1.3);
- $d$-dimensional Friedrichs symmetric-hyperbolic energy estimates with Kreiss–Oliger dissipation (§1.4);
- Kung–Leiserson systolic retiming and time-multiplexed stencil marching, and GPU/RTL lowering with logic-equivalence checks (§1.6, §1.7);
- discrete exterior calculus, the discrete Hodge decomposition, Whitney forms, and Dirac open systems (§2);
- open-hypergraph symmetry quotients and adjoint equality saturation (§3);
- validated continuous analysis and Gröbner-basis completion (§4).

The continuum estimates use rational grid data. Spatial regularity enters the truncation bounds through the finite-difference hypotheses on the samples. The weak-form estimates below concern finite meshes and finite time intervals.

---

## 1. Balance-Law Compilation, 1+1 Relativity and 3+1 Constraint Propagation

`#pde_solver` (`lean/Obend/Elab/PdeSolverElab.lean`) parses a declarative system $\partial_t U + \sum_d \partial_d F_d(U) = S(U)$ — spatial coordinates, conserved state variables, exact rational parameters, positivity domain, directional flux expressions, algebraic source terms, declared state box, scaling weights, wavespeed bound $a_{\max}$, Courant number $\nu$, and slope limiter — and elaborates a single `ConservationLawSpec` (`lean/Obend/Analysis/NonlinearMultiDPde.lean`) together with its continuum, numerical, fixed-point, GPU, and RTL theorems checked by the Lean 4 kernel at declaration time (`checkPdeSolverSpec_sound`, `validatePdeSolverSexpr_refuses_invalid`, `checkPdeSolverSpec_refuses_cfl_violation`).

### 1.1 Six-Rung Vertical Certificate on One `ConservationLawSpec` (`EndToEndPdeCert`)

For each accepted specification `S : ConservationLawSpec`, `#pde_solver` synthesizes `<Name>.endToEnd_certified : EndToEndPdeCert <Name>.spec` via `buildEndToEndPdeCert` (`lean/Obend/Hardware/MultiDStencilCorrect.lean`), uniting six proved rungs over the same object `S`:

1. **Continuum Symbolic Fréchet Differentiation, Derived Gershgorin Spectral Radius & Constructive Lipschitz Bound (`lean/Obend/Analysis/NonlinearMultiDPde.lean`, `lean/Obend/Analysis/HyperbolicBalanceLaws.lean`, `lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `symJacobian_frechet_taylor`: for every directional flux entry whose denominators are certified nonzero on the declared domain (`DomainValid`, `checkExprDomainSafe`), exact multivariable symbolic differentiation over $\mathbb{Q}$ satisfies $F_d(U + hV) - F_d(U) = h\,J_d(U)V + h^2 R_d(U, V, h)$ with explicit rational remainder `symDirectionalRem` and zero floating-point truncation.
   - `verifyWavespeedGershgorin_sound`: interval enclosure of every symbolic Jacobian entry over `effectiveStateBox S` and scaled Gershgorin row-sum verification (`verifyWavespeedGershgorin`) bound both the weighted $\ell_\infty$ operator norm $\lVert J_d(U) \rVert_{w,\infty} \le a_{\max}$ and every rational eigenvalue $|\lambda| \le a_{\max}$ across the state box.
   - `evalFluxLip_sound` and `verifyFluxLipschitz_sound`: constructive interval-derivative propagation (`verifyFluxLipschitz`) derives `FluxLipOn S d (effectiveStateBox S)` with zero external Lipschitz axioms.

2. **Conservative Rational MUSCL/Rusanov Schemes, Hydrostatic Balance & Z4c Constraint Damping (`lean/Obend/Analysis/NonlinearMultiDPde.lean`, `lean/Obend/Tactic/SymDiffAndFlux.lean`, `lean/Obend/Analysis/HyperbolicBalanceLaws.lean`, `lean/Obend/Analysis/NonlinearPdeCli.lean`)**:
   - `fluctuationConservation_of_reflective` and `symmetrizerReflective_sound`: clearing denominators into canonical multivariate polynomials (`checkFluxEqReflective_sound`) proves exact two-state Rusanov fluctuation conservation $A^-\Delta Q + A^+\Delta Q = F_d(U_R) - F_d(U_L)$ and Friedrichs symmetry of $H(U)J_d(U)$.
   - `tvd_rusanov_minmod_step_nonincreasing` and `tadmor_rusanov_entropy_dissipative`: the scalar minmod–Rusanov step for an $a_{\max}$-Lipschitz flux is total-variation diminishing for $a_{\max},\nu\ge0$ under $2\nu a_{\max} \le 1$, and Tadmor entropy-conservative fluxes with monotone entropy variables and nonnegative Rusanov dissipation satisfy the discrete entropy inequality on periodic grids.
   - `evalSchemeStepRat_conserves_sourceless_component`, `rolloutRat_periodic_conserves_integral`, and `rolloutRat_reflective_conserves_component`: multi-dimensional Lie and Strang operator-split steps (`evalSchemeStepRat`) conserve exact discrete integrals on sourceless components across periodic grids and parity-reflected impermeable walls.
   - `z4c_theta_constraint_strict_damped`, `dedner_glm_psi_energy_damped`, and `audusseBouchut_lakeAtRest_wellBalanced`: strict per-step contraction $|\Theta^{n+1}| < |\Theta^n|$ of the Z4c constraint-damping variable for $\Theta^n\ne0$ under $0 < \Delta t\,\kappa_1 \alpha < 2$, non-increase of the Dedner source-update energy $\psi^2$ when $0\le\Delta t\,\mathrm{damp}\le2$, and exact lake-at-rest preservation $h + b = \text{const},\, q = 0$ under Audusse–Bouchut hydrostatic reconstruction.

3. **Signed Q32.32 Guard-Bit Overflow Freedom, LUT-Free Systolic Reciprocal & Quantitative Step Defect (`lean/Obend/Hardware/MultiDStencilTile.lean`, `lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `specializeFluxSweep_sound` and `compileFluxSsaDag_sound`: Futamura parameter specialization and common-subexpression elimination lower `S` to `FluxSsaDag` without increasing operation count.
   - `evalQ32Reciprocal_residual_bound`: a table-free 4-step Newton–Raphson reciprocal (`evalQ32Reciprocal`, seeded with $48/17 - (32/17)d$ after shift normalization) satisfies $|r \cdot d - 2^{64}| \le 6 \cdot 2^{32} + |d|$ across every 64-bit signed word with $16 \le |d| \le 2^{60}$, with zero signed wrap at any intermediate node.
   - `inferSsaDagQ32Intervals_encloses_eval`, `propagateSsaInterval_encloses`, and `checkPdeQ32Intervals_sound`: every evaluated Q32.32 wire stays strictly inside the guard-bit range $(-2^{62}, 2^{62})$ and equals its unbounded-integer meaning (`propagateSsaInterval_refuses_zero_crossing`, `ratToQ32Checked_refuses_overflow`).
   - `stepQ32Axis_rat_defect_bound`: `computeStepQ32ErrorBound` computes a concrete rational bound $\varepsilon_{\text{step}}$ on $|{\text{decodeQ32}}(\text{evalNonlinearFluxCellQ32}) - \text{evalAxisCellRat}|$ across every five-point stencil in the declared Q32 state box.

4. **Multi-Step Nonlinear Error Tubes (`lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `nonlinear_aposteriori_error_tube`: discrete Gronwall / Lady Windermere error-tube recursion $e_{k+1} \le L_{\text{scheme}} e_k + \delta_k$ bounding the distance between any untrusted floating-point or ML surrogate trajectory and the exact rational `evalSchemeStepRat` rollout.
   - `q32_trajectory_error_tube_derived` and `q32_scheme_trajectory_error_tube`: *a priori* multi-step error tubes for in-box stages under the CFL condition between decoded Q32.32 rollouts (both single-axis sweeps and multi-dimensional Lie/Strang + inhomogeneous source rollouts) and exact rational trajectories, using the derived `verifyFluxLipschitz` and `computeSourceLip` bounds.

5. **Bit-Exact GPU Kernel Lowering & Multi-D Brick Halo Tiling (`lean/Obend/Hardware/MultiDStencilGpuSource.lean`, `lean/Obend/Hardware/MultiDStencilCorrect.lean`, `lean/Obend/Hardware/MultiDStencilTile.lean`)**:
   - `scalarQmul32_eval_eq_qmul32`: the four 32-bit-limb WGSL product equals signed floor Q32.32 multiplication modulo $2^{64}$ on every word pair.
   - `spec_fusedGpuKernel_eq_stepQ32Axis` and `spec_fusedGpuKernel_preserves_constant_state`: the lowered GPU kernel (`compileMultiDNonlinearFluxSweepSource` / `buildSpecFusedGpuKernel`) evaluates bit-for-bit identically to `stepQ32Axis` on every grid and boundary policy for a valid specification and declared axis, and preserves spatially constant states on positive grid extents.
   - `multiDBrickTiled_eq_global_sweep` and `multiDBrickHbmReads_lt_global`: multi-dimensional shared-memory halo brick tiling (including non-multiple tail bricks and radius-2 MUSCL stencils) equals the global sweep. For positive halo radius and brick extents $2\le B_d\le N_d$ on a nonempty grid shape, the brick read count is strictly below the full neighborhood read count.

6. **Universal Systolic RTL Refinement & Yosys SMT-LIB2 Logic Equivalence (`lean/Obend/Hardware/MultiDStencilCorrect.lean`, `lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Hardware/HDL.lean`)**:
   - `spec_systolicRtl_refines_q32` and `spec_systolicRtl_yosysLec_faithful`: the emitted pipelined systolic `RtlModule` (`buildSpecSystolicRtl`, inlining the 29-wire combinational `reciprocalRtlExprs`) passes `checkRtlModule`, satisfies `moduleFaithful` for SMT-LIB2 miter generation (`emitYosysLecSmt2`, `lecScript_unsat_of_step`), and evaluates bit-identically to `evalFluxSsaDagQ32` across all $2^{64}$ input words per variable.

### 1.2 Canonical Compiled Solver Catalog (`lean/Obend/Hardware/PdeSolvers.lean`)

`lookupCanonicalPdeSolver` resolves the ten entries in `canonicalPdeSolvers` for `obend pde solve`. The final row gives the 3+1 specification compiled separately in §1.5. The defect column bounds one axis update on an in-box five-point stencil at the declared Courant ratio. The entries are the generated rational bounds rounded up to whole units of $2^{-32}$ (ULP). For `BssnZ4cConstraint3D` the bound is exactly $2560874250231/53687091200$ ULP (`BssnZ4cConstraint3D.q32ErrorBound`, `BssnZ4cConstraint3D.q32_step_defect_bound`).

| Solver | Coordinates & State Variables | Physical Regime & Key Verified Properties | Certified Q32 Step Defect $\varepsilon_{\text{step}}$ |
| :--- | :--- | :--- | :--- |
| `Burgers1D` | $x$; $(u)$ | Inviscid nonlinear advection $\partial_t u + \partial_x(\tfrac{1}{2}u^2) = 0$ | 4 ULP |
| `EulerGas3D` | $x, y, z$; $(\rho, \rho u, \rho v, \rho w, E)$ | 3D compressible ideal gas ($\gamma = 7/5$, $\rho \in [1, 2]$); CSE shares kinetic energy and pressure across flux rows | 6 ULP |
| `IdealMhd8Wave` | $x, y$; $(\rho, \rho\mathbf{u}, \mathbf{B}, E, \psi)$ | 2D 9-variable ideal magnetohydrodynamics ($\gamma = 5/3$, $c_h = 2$) | 28 ULP |
| `DednerGlmMhd2D` | $x, y$; $(\rho, \rho\mathbf{u}, \mathbf{B}, E, \psi)$ | 2D GLM MHD with mixed hyperbolic/parabolic divergence-cleaning source $-\text{damp}\cdot\psi$ (`dedner_glm_psi_energy_damped`) | 28 ULP |
| `CurvedSpacetimeMaxwell` | $x, y, z$; $(\mathbf{D}, \mathbf{B})$ | 3+1 curved-spacetime ADM electrodynamics with nontrivial lapse $\alpha = 4/5$ and shift $\boldsymbol{\beta}$ | 12 ULP |
| `VlasovPoissonPhase` | $x, v_x$; $(f, E_x)$ | $1\text{x}1\text{v}$ kinetic Vlasov–Ampère phase-space advection | 47 ULP |
| `BonaMasso1DPrincipal` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx})$ | Source-free principal operator of 1+1 Bona–Massó hyperbolic ADM relativity ($f = 2$, $\beta = 1/5$, shared $\text{tr}\,K = K_{xx}/g_{xx}$) | 303 ULP |
| `BonaMasso1D` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx})$ | Inhomogeneous 1+1 Bona–Massó ADM balance law with sources $-\alpha^2 f K_{xx}/g_{xx}$, $-2\alpha K_{xx}$, $\alpha(A_x D_x - K_{xx}^2/g_{xx})$ | 48 ULP |
| `BonaMassoZ4c1D` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx}, \Theta)$ | 1+1 Bona–Massó / Z4c formulation coupling $\hat{K} = K_{xx}/g_{xx} - 2\Theta$ and algebraic constraint damping $-\kappa_1 \alpha \Theta$ (`z4c_theta_constraint_strict_damped`) | 48 ULP |
| `ShallowWater1D` | $x$; $(h, q, b_x)$ | 1D Saint-Venant shallow water with bathymetry source $-g h b_x$. The hydrostatic update `abStep` preserves resting water of constant surface height (`audusseBouchut_lakeAtRest_wellBalanced`) | 4 ULP |
| `BssnZ4cConstraint3D` | $x, y, z$; $(\alpha, g_{xx}, A_x, D_x, K_{xx}, \Theta, Z_x, Z_y, Z_z, H_{\text{ham}})$ | 3+1 Bona–Massó gauge sector coupled to the five-field conformal Z4c constraint-propagation system ($f = 2$, $\boldsymbol{\beta} = (1/5, 1/10, -1/10)$, $\kappa_1 = 1/2$, $\kappa_2 = -1$, $a_{\max} = 9$, $\nu = 1/10$); constraint-sector Jacobian identified with the symmetric-hyperbolic model of §1.5 (`bssnZ4cConstraint3D_constraint_sector_eq_z4c3d`) | 48 ULP |

### 1.3 Continuum-to-Discrete Consistency, Summation by Parts & Lax–Wendroff Weak-Form Residual Bounds (`lean/Obend/Analysis/LaxWendroffDefs.lean`, `lean/Obend/Analysis/LaxWendroffConvergence.lean`)

Fix `S : ConservationLawSpec` with $m$ components, positive scaling weights $w_k$ (`weightOf`), certified wavespeed bound $a_{\max}$, symbolic directional Jacobian $J_d$ (`jacMat`), and the exact rational Taylor remainder `symDirectionalRem` of rung 1. $\hat F_d$ denotes a numerical face flux and $F_d$ the continuum flux of `S`.

**Local truncation order.** For both flux-divergence bounds assume `ConservationLawSpec.checkValid S = true` and `verifyWavespeedGershgorin S = true`. Take a declared axis and component, a central state in `effectiveStateBox S`, and samples equal to the central state outside the declared components.

- `rusanov_first_order_spatial_truncation`: let $(u_{-1}, u_0, u_1)$ be a three-point sample at spacing $\Delta x > 0$ whose forward and backward divided differences lie within $\tfrac12 M_2 w_k \Delta x$ of a vector $u_x$ in each component $k$ (`C2GridSample`), with $M_2 \ge 0$. If all three states satisfy `DomainValid` and both directional remainders have absolute value at most $R_{\max}$, then

  $$\left| \frac{\hat F^{\text{Rus}}_{d,i}(u_0, u_1) - \hat F^{\text{Rus}}_{d,i}(u_{-1}, u_0)}{\Delta x} - \big(J_d(u_0)\,u_x\big)_i \right| \le \big(a_{\max}\, w_i\, M_2 + R_{\max}\big)\,\Delta x .$$

  `c2GridSample_quadratic_inhabited` shows that exact quadratic Taylor polynomials satisfy the sample hypothesis with bound vector $|u_{xx,k}|$.
- `muscl_nonextrema_second_order_truncation`: let $s_{-2}, \dots, s_2$ be a five-point sample with $s_0 = u_0$ that agrees with the quadratic Taylor polynomial of $(u_0, u_x, u_{xx})$ to within $M_3 w_k \Delta x^3$ at offsets $\pm 1, \pm 2$, and on which the slope limiter of `S` selects the same one-sided difference in cells $-1, 0, 1$ of every component (`C3NonExtremaStencil5`). Assume $M_3 \ge 0$ and domain validity at $u_0$ and all four reconstructed states. If the directional remainders at the two interfaces differ on each reconstruction branch by at most $K_{\text{rem}} \Delta x$, then

  $$\left| \frac{\hat F^{\text{MUSCL}}_{d,i}(s_{-1}, s_0, s_1, s_2) - \hat F^{\text{MUSCL}}_{d,i}(s_{-2}, s_{-1}, s_0, s_1)}{\Delta x} - \big(J_d(u_0)\,u_x\big)_i \right| \le \big(3\, a_{\max}\, w_i\, M_3 + \tfrac14 K_{\text{rem}}\big)\,\Delta x^2 .$$

  For the minmod limiter, `muscl_nonextrema_face_second_order` bounds the errors of the two face reconstructions relative to $u_0 \pm \tfrac12 \Delta x\,u_x$ by $\tfrac14 M_{2,k}\Delta x^2$ on a `C2GridSample` with strictly same-signed adjacent slopes in component $k$. A linear profile with nonzero slope in each component satisfies the five-point branch hypothesis (`c3NonExtremaStencil5_linear_inhabited`).
- `strang_local_commutator_second_order`: for linear grid operators $L_1, L_2$ (`IsLinearGridOp`) with commutator $[L_1, L_2]$ (`commutatorGrid`) and second-order Taylor substeps $\Psi_i(\tau) = I + \tau L_i + \tfrac{\tau^2}{2} L_i^2$, measured against the joint step $T(\Delta t) = I + \Delta t (L_1 + L_2) + \tfrac{\Delta t^2}{2}(L_1 + L_2)^2$:

  $$\Psi_2(\Delta t)\Psi_1(\Delta t)\,U - T(\Delta t)\,U = -\tfrac{\Delta t^2}{2}\,[L_1, L_2]\,U + \tfrac{\Delta t^3}{2}\big(L_2 L_1^2 + L_2^2 L_1\big)U + \tfrac{\Delta t^4}{4}\, L_2^2 L_1^2\, U ,$$

  whereas the Strang composition $\Psi_1(\tfrac{\Delta t}{2})\Psi_2(\Delta t)\Psi_1(\tfrac{\Delta t}{2})\,U - T(\Delta t)\,U$ is an explicit polynomial in $\Delta t$ of degree at most six with operator-word coefficients independent of $\Delta t$ and no term below $\Delta t^3$. With forward-Euler substeps the two Lie orderings differ by exactly $-\Delta t^2 [L_1, L_2] U$. `noncommuting_linearGridOps_inhabited` gives $L_1, L_2, U$ with $[L_1, L_2] U \ne 0$.

**Exact periodic summation by parts.**

- `evalAxisStepRat_summation_by_parts`: on a periodic grid with positive extents, for every grid function $\psi$, Courant ratio $\mu$, and $\Delta x \ne 0$, the single-axis conservative update $\mathcal{A}_{d,\mu}$ (`evalAxisStepRat`) satisfies the identity

  $$\sum_{x} \big(\mathcal{A}_{d,\mu} G - G\big)_{x,c}\; \psi_{x,c} = \mu\, \Delta x \sum_{x} \hat F_{d,c}(G)_{x + \frac12 e_d}\; \big(D^{+}_{d} \psi\big)_{x,c},$$

  with $\hat F$ the scheme's own face flux (`gridFaceFlux`) and $D^+_d$ the forward difference quotient (`spatialDiffTest`). There is no remainder term.
- `evalSchemeStepRat_summation_by_parts`: the same identity for one full Lie or Strang step with sources, whose right-hand side is the sum of the flux pairing over the axis schedule (`schemeWeakFluxPairing`) and the source pairing (`schemeWeakSourcePairing`). `time_summation_by_parts` is the corresponding Abel identity in the time index.

**Weak-form residual.** For a discrete trajectory $U^n$ and a grid test function $\varphi^n$ over $K$ steps and $K+1$ time levels (`SpaceTimeTestFn`), cell volume $V = \Delta x^{D}$, `discreteWeakResidual` is

$$\mathcal{R}(U, \varphi) = \sum_{c < m} \Big[ V \sum_{x} \big( U^{K}_{x,c} \varphi^{K}_{x,c} - U^{0}_{x,c} \varphi^{0}_{x,c} \big) - \Delta t\, V \sum_{n < K} \sum_{x} \Big( U^{n+1}_{x,c}\, D_t \varphi^{n}_{x,c} + \sum_{d < D} F_{d,c}(U^{n}_{x})\, D^{+}_{d} \varphi^{n}_{x,c} + S_c(U^{n}_{x})\, \varphi^{n}_{x,c} \Big) \Big],$$

where $D_t\varphi^n=(\varphi^{n+1}-\varphi^n)/\Delta t$ and $F_d$ is the continuum flux. The endpoint terms vanish for `CompactInTime` test functions (`discreteWeakResidualComp_compactInTime`).

- `lax_wendroff_weak_residual_bound`: let $U^n$ be the exact rational rollout of `evalSchemeStepRat` on a periodic grid (Lie or Strang, Courant ratio $\Delta t / \Delta x$) that remains in the certified state box (`SchemeStepInBox`). Take positive grid extents, $D$ at most the number of declared axes, $\Delta x,\Delta t>0$, and $a_{\max}\ge0$. Assume `verifyFluxLipschitz S = true`, `computeSourceLip S = some Lsrc`, $|D^+_d \varphi| \le M_x$, and $|\varphi| \le M_\varphi$. Then

  $$|\mathcal{R}(U, \varphi)| \le C_{\text{LW}} \cdot \operatorname{Osc}(U), \qquad C_{\text{LW}} = \sum_{c < m} \max\big(a_{\max} M_x,\; L_{\text{src}} M_\varphi\big)\, w_c ,$$

  where $C_{\text{LW}}$ is `laxWendroffConst` and $\operatorname{Osc}(U) = V \sum_{n < K}$ `stepOscillation` $(U^n)$ is `totalOscillation`: each sweep with ratio $\mu$ contributes $\mu\Delta x$ times the cell sum of $\tfrac32$ times the forward jump plus the drift from the initial grid of that step, both in the weighted $\ell_\infty$ norm. A nonempty source adds the cell sum of the post-sweep drift from the start of the step, weighted by $\Delta t$ (Lie) or $\Delta t/2$ (Strang). The hypothesis `S.sources.isEmpty = true ∨ dx = 1` is required: the scheme scales its source update by the Courant ratio, so with a nonempty source the estimate holds at unit mesh width only.
- `lax_wendroff_1d_tvd_shock_rate`: for a scalar ($m = 1$), source-free law on a one-dimensional periodic grid under Lie splitting, retain the preceding mesh, box, Lipschitz and test-function hypotheses with $M_x\ge0$. If $\operatorname{TV}(U^n) \le B_{\text{TV}}$ for all $n < K$ (`totalVariation1D`), then

  $$|\mathcal{R}(U, \varphi)| \le C_{\text{LW}} \cdot \frac{3}{2 w_0}\,(K \Delta t)\, B_{\text{TV}}\; \Delta x ,$$

  with $C_{\text{LW}}$ evaluated at $L_{\text{src}} = 0$: linear in $\Delta x$ at fixed elapsed time $K \Delta t$, with no smoothness hypothesis on $U$. The variation non-increase theorem `tvd_rusanov_minmod_step_nonincreasing` concerns the standalone scalar step `musclMinmodRusanov1DStep`.
- `endToEnd_q32_silicon_weak_form_bound`: given `cert : EndToEndPdeCert S`, the CFL condition $(\Delta t / \Delta x)\, a_{\max} \le 1$, positive extents and mesh sizes, $D$ at most the number of declared axes, an empty source or $\Delta x=1$, and `computeSchemeQ32ErrorBound` returning `some` $\varepsilon$, assume the word and rational stages satisfy their box conditions at every step. With the test bounds above (including $|\varphi^K|\le M_\varphi$) and initial data within `initErr` in the weighted norm (`GridClose`), the decoded Q32.32 trajectory $U_{\text{Q32}}$ (`q32SchemeTrajectory`) satisfies

  $$|\mathcal{R}(U_{\text{Q32}}, \varphi)| \le C_{\text{LW}} \cdot \operatorname{Osc}(U_{\text{exact}}) + \Big(\sum_{c} w_c\Big)\, V\, N_{\text{cells}} \Big[ (E_K + E_0)\, M_\varphi + \Delta t \sum_{n < K} \big( E_{n+1} M_t + E_n ( D\, a_{\max} M_x + L_{\text{src}} M_\varphi ) \big) \Big],$$

  for some $L_{\text{src}}$ returned by `computeSourceLip`. Here $E_n$ is the rung-4 defect tube `nonlinearDefectTube` driven by `schemeLip` and $\varepsilon$, $M_t$ bounds $|D_t \varphi|$, and the second summand is `q32WeakPerturbationBound`. On per-component lists indexed by `pdeNeighborIdx`, each fused GPU sweep equals `stepQ32Axis` at that sweep’s Courant ratio. The residual estimate uses `stepQ32AxisAt` on the `axisNeighbor` grid. On each grid axis the RTL module for the flux DAG `stepDag` passes `checkRtlModule` and `moduleFaithful`, and reproduces `evalFluxSsaDagQ32` one clock after sampling its inputs.
- `checkLaxWendroffAudit_sound`, `checkLaxWendroffAudit_complete`, `checkLaxWendroffAudit_refuted`: the decidable audit `checkLaxWendroffAudit` computes $\mathcal{R}$ exactly for a finite query (specification, grid, mesh, step count, initial data, test function, tolerance) and returns `.ok` if and only if the query is `LaxWendroffAuditQuery.WellPosed` and $|\mathcal{R}| \le$ tolerance (`CertifiedLaxWendroffAudit`); the two refusal clauses are `invalidQueryShape` and `residualExceedsTolerance`. `laxWendroffWeakJudge` packages it as an `Obend.Judge` whose fragment is `LaxWendroffAuditQuery.WellPosed`, inhabited at mesh widths $1$ and $\tfrac12$ by `laxWendroffWeakJudge_fragment_inhabited`.
- `runMeshRefinementTrace_sound`: a refinement turn is accepted when its query passes the audit and at least halves the current mesh width ($2 \Delta x_{\text{new}} \le \Delta x_{\text{cur}}$; `stepMeshRefinement_none_iff_violation` characterizes rejection exactly). For any accepted list of $k$ turns from state $s_0$ to $s_F$: every turn is certified with tolerance at most the accumulated maximum, $2^{k}\, \Delta x_F \le \Delta x_0$, and the accepted-level count increases by $k$.

### 1.4 $d$-Dimensional Friedrichs Symmetric-Hyperbolic Energy Theory & Kreiss–Oliger Dissipation (`lean/Obend/Analysis/SymmetricHyperbolicEnergy.lean`)

A `SymmetricHyperbolicSystem` is a constant-coefficient system $\partial_t U + \sum_{d < D} A_d\, \partial_{x_d} U = B U$ over $\mathbb{Q}^m$ together with a symmetric matrix $H_0$, a constant $\mu > 0$ with $\langle v, H_0 v \rangle \ge \mu \lVert v \rVert_2^2$, and symmetry of every $H_0 A_d$. Write $\langle u, v \rangle_{H_0} = u^{T} H_0 v$ (`h0Inner`) and $E(U) = \sum_x \langle U_x, U_x \rangle_{H_0}$ (`multiDH0Energy`) on a periodic grid with positive extents. The Rusanov sweep and rollout use one grid dimension per system axis.

- `checkSpdGramCoercive_sound`: if the checker accepts a certificate $(\mu, G, d)$ with $\mu > 0$, $d_k \ge 0$, and entrywise $H_0 = \mu I + G^{T} \operatorname{diag}(d)\, G$, then $H_0$ is symmetric, $\langle v, H_0 v \rangle \ge \mu \lVert v \rVert_2^2$ for all $v$, and $\langle v, H_0 v \rangle > 0$ whenever some $v_k \ne 0$. `computeShiftedLdl` attempts the factorization for a supplied shift and `findIndefiniteWitness` searches for a vector refuting positivity.
- `symmetricHyperbolicOfConservationLaw`: a `ConservationLawSpec` with at least one spatial axis whose constant symmetrizer passes the reflective check of rung 2 on every axis (`verifyConservationLawSymmetrizerReflective`, via `symmetrizerReflective_sound`) and the Gram check above lifts, at any `DomainValid` state $u_0$, to the `SymmetricHyperbolicSystem` with $A_d = J_d(u_0)$ and $B$ the source Jacobian at $u_0$. The result is the frozen-coefficient linearization at $u_0$.
- `centeredDiff_h0_skew_adjoint`: for the centered difference $D_{0,d}$ on any periodic grid with positive extents, $\sum_x \langle U_x, A_d (D_{0,d} U)_x \rangle_{H_0} = 0$ identically.
- `rusanov_symmetric_energy_dissipative`: let $a \ge 0$, $\nu \ge 0$, $\nu a \le 1$, and $\langle A_d v, A_d v \rangle_{H_0} \le a^2 \langle v, v \rangle_{H_0}$ for all $v$ and $d$. One Rusanov axis step $\mathcal{S}_d$ (`rusanovSymmetricAxisStep`) satisfies

  $$E(\mathcal{S}_d U) \le E(U) - \nu a\,(1 - \nu a)\; E(D_{+,d} U),$$

  and the full dimension-by-dimension sweep (`rusanovSymmetricMultiDSweep`) satisfies $E(\mathcal{S} U) \le E(U)$.
- `kreissOliger4_energy_nonpositive`: for $\sigma \ge 0$, with $D_{\pm,d}$ the undivided forward and backward differences,

  $$-\sigma \sum_x \big\langle U_x, (D_{+,d}^2 D_{-,d}^2 U)_x \big\rangle_{H_0} = -\sigma\, E(D_{+,d} D_{-,d} U) \le -\sigma \mu \sum_x \big\lVert  (D_{+,d} D_{-,d} U)_x \big \rVert_2^2 \le 0 .$$

- `symmetricHyperbolic_gronwall_stability`: for the full step (Rusanov sweep followed by the explicit source update, `symHypFullStep`) under the preceding flux-speed bound, $a,m_B,\Delta t\ge0$, $\Delta x>0$, $\Delta t\, a \le \Delta x$, and $\langle B v, B v \rangle_{H_0} \le m_B \langle v, v \rangle_{H_0}$: (i) if $\langle v, (H_0 B + B^{T} H_0) v \rangle \le 2\gamma \langle v, v \rangle_{H_0}$ with $\gamma \ge 0$ and $\Delta t \le 1$, then $E(U^n) \le (1 + (2\gamma + m_B) \Delta t)^n E(U^0)$; (ii) if instead the bound holds with $-2\eta$ for some $\eta > 0$, and $\Delta t > 0$, $\Delta t\, m_B \le \eta$, $\eta \Delta t \le 1$, then $E(U^n) \le (1 - \eta \Delta t)^n E(U^0)$, with strict decrease $E(U^n) < E(U^0)$ for $n > 0$ and $U^0 \ne 0$.
- `checkSymHyp_sound`, `checkSymHyp_complete`, `checkSymHyp_refuted`: the decidable checker `checkSymHyp` on a finite object (dimensions, $H_0$, $A_d$, $B$, $a_{\max}$, $\Delta t$, $\Delta x$) and certificate $(\mu, G, d)$ returns `.ok` only if `CertifiedSymHyp` holds; every certified object is accepted with the canonicalized certificate `canonicalSymHypCert`; and each of the refusal clauses `shapeOrCflInvalid`, `h0NotSymmetric`, `h0NotPositiveDefinite`, `fluxNotSymmetrized` implies that no certificate whatsoever certifies the object. The fifth clause, `certGramMismatch`, rejects the supplied certificate without refuting the object (`symHypRefutes`). `symmetricHyperbolicJudge` is the resulting `Obend.Judge` instance.
- `runSymHypRolloutTrace_dissipative_sound`: for an adaptive rollout in which each turn proposes its own $\Delta t$ and is accepted exactly when $0 \le \Delta t$, $\Delta t\, a \le \Delta x$, and $0 < \Delta x$ (`stepSymHypRolloutTurn_none_iff_violation`), under the same flux-speed and source-norm bounds, the dissipative source bound with rate $\eta$, and $\Delta t\, m_B \le 2\eta$ on every turn: the final energy is at most the initial energy, elapsed time is non-decreasing, and the accepted-step count equals the number of turns.

### 1.5 3+1 Conformal Z4c Constraint Propagation, Light-Cone Eigenstructure & the 10-Variable `BssnZ4cConstraint3D` Solver (`lean/Obend/Analysis/RelativityBssnZ4c3D.lean`)

The model evolves five symmetrized constraint fields with flat spatial derivatives, constant lapse $\alpha$ and constant shift $\boldsymbol\beta$ (`Z4c3DParams`). In the coordinates $C = (\Theta, Z_x, Z_y, Z_z, H_{\text{ham}})$ the equations are

$$\partial_t \Theta - \beta^i \partial_i \Theta = -\alpha\, \partial_i Z^i - \kappa_1 (2 + \kappa_2)\, \alpha\, \Theta, \qquad \partial_t Z_i - \beta^j \partial_j Z_i = -\tfrac12 \alpha\, \partial_i \Theta - \tfrac14 \alpha\, \partial_i H_{\text{ham}} - \kappa_1 \alpha\, Z_i, \qquad \partial_t H_{\text{ham}} - \beta^i \partial_i H_{\text{ham}} = -2 \alpha\, \partial_i Z^i - 2 \kappa_1 \alpha\, H_{\text{ham}} .$$

- `z4c3d_conformal_symmetrization_conjugates`: the invertible map $(\Theta_{\text{phys}}, Z_i, H_{\text{phys}}) \mapsto (2 \Theta_{\text{phys}}, Z_i, -2 H_{\text{phys}})$ (`toSymmetrizedZ4cState`, inverse by `symmetrizedZ4cState_roundtrip`) intertwines the physical flux matrices `z4c3dRawFluxMat` with the symmetrized ones `z4c3dFluxMat` on every axis and commutes with the damping source matrix `z4c3dSourceMat`.
- `z4c3d_constraint_symmetric_hyperbolic`: for every parameter tuple, with $H_{\text{Z4c}} = \operatorname{diag}(4, 8, 8, 8, 1)$: $\lVert v \rVert_2^2 \le \langle v, H_{\text{Z4c}} v \rangle$; $H_{\text{Z4c}} A_d$ is symmetric for $d \in \lbrace x, y, z \rbrace$; the centered-difference pairing of §1.4 vanishes and the Kreiss–Oliger term is non-positive on periodic grids with positive extents and $\sigma\ge0$. For any $a_{\max} > 0$, $\Delta t \ge 0$, $\Delta x > 0$ with $\Delta t\, a_{\max} \le \Delta x$ the judge `symmetricHyperbolicJudge` accepts the system with the explicit certificate $\mu = 1$, $G = I$, $d = (3, 7, 7, 7, 0)$ (`z4c3dSymHypCert`).
- `z4c3d_characteristic_eigenpairs`: for every rational unit normal $n$ ($n_x^2 + n_y^2 + n_z^2 = 1$), with $\beta_n = n \cdot \boldsymbol\beta$ and principal symbol $A(n) = n_x A_x + n_y A_y + n_z A_z$ (`z4c3dPrincipalSymbol`):

  $$A(n)\,(1, \pm n, 2)^{T} = (-\beta_n \pm \alpha)\,(1, \pm n, 2)^{T}, \qquad A(n)\,(1, 0, -2)^{T} = -\beta_n\,(1, 0, -2)^{T}, \qquad A(n)\,(0, w, 0)^{T} = -\beta_n\,(0, w, 0)^{T} \ \text{ for } w \cdot n = 0 ,$$

  so the characteristic speeds are $\lbrace -\beta_n, -\beta_n \pm \alpha \rbrace$: two modes on the light cone of the lapse and three advected along the shift.
- `z4c3d_axis_isEigenSystem`: along each coordinate axis, explicit rational matrices $(R_d, R_d^{-1})$ and eigenvalues $(-\beta_d + \alpha, -\beta_d - \alpha, -\beta_d, -\beta_d, -\beta_d)$ form a complete `IsEigenSystem`, and $R_d^{-T} \operatorname{diag}(16, 16, 8, 8, 8)\, R_d^{-1} = H_{\text{Z4c}}$.
- `z4c3d_cyclic_axis_equivariant`: the cyclic permutation of $(Z_x, Z_y, Z_z)$ fixing $(\Theta, H_{\text{ham}})$ (`permuteZ4cVec`) is a $C_3$ action that preserves $\langle \cdot, \cdot \rangle_{H_{\text{Z4c}}}$, commutes with the source matrix under the matching permutation of the shift (`cycleZ4cParams`), and reduces each $A_d$ to $A_x$ by conjugation.
- `z4c3dSemiDiscreteRhs_energy_dissipative`: for $\alpha > 0$, $\kappa_1 > 0$, $\kappa_2 \ge -1$, the semi-discrete right-hand side $R(C) = B C - \sum_d A_d D_{0,d} C$ on a periodic grid with positive extents satisfies $2 \sum_x \langle C_x, R(C)_x \rangle_{H_{\text{Z4c}}} \le -2 \kappa_1 \alpha\, E(C)$.
- `z4c3d_total_constraint_energy_damped`: for the fully discrete rollout of §1.4 on a three-dimensional periodic grid of positive extents, assume $\alpha,\kappa_1,\Delta t,\Delta x>0$, $\kappa_2\ge-1$, $|\beta^i| + \alpha \le a$, $\Delta t\, a \le \Delta x$, $\Delta t\, r_{\max}^2 \le \kappa_1 \alpha$ for $r_{\max} = (2 + \max(0, \kappa_2))\, \kappa_1 \alpha$ (`z4c3dMaxDampRate`), and $\kappa_1 \alpha\, \Delta t \le 1$:

  $$E(C^n) \le (1 - \kappa_1 \alpha\, \Delta t)^n\, E(C^0), \qquad E(C^n) < E(C^0) \ \text{ for } n > 0,\ C^0 \ne 0 .$$

  With $\kappa_1 = 0$ every spatially uniform constraint violation is a fixed point of the rollout, with positive energy when nonzero: the decay is due to the damping terms.
- `BssnZ4cConstraint3D.spec`, `BssnZ4cConstraint3D.endToEnd_certified`: the ten-variable specification of §1.2 passes the same six-rung pipeline as the catalog solvers, yielding `EndToEndPdeCert BssnZ4cConstraint3D.spec`.
- `bssnZ4cConstraint3D_constraint_sector_eq_z4c3d`: at every state $u$, the $5 \times 5$ block of the symbolic flux and source Jacobians of `BssnZ4cConstraint3D.spec` on the constraint variables equals `z4c3dFluxMat` and `z4c3dSourceMat` at lapse $\alpha = u_0$ with the solver's parameters (`bssnZ4c3dSolverParams`); and on any background with vanishing constraint variables the coupling block from the gauge variables into the constraint rows vanishes. Freezing a spatially uniform, constraint-free background thus gives the autonomous five-field linear system of the energy estimate.
- `z4c3d_slab_reduction_matches_1d`: on a periodic grid of positive extents $[N_x, N_y, N_z]$, embedding a 1+1 `BonaMassoZ4c1D` state with $Z_i = H_{\text{ham}} = 0$ as a $(y, z)$-independent slab (`embedZ4cPlanarSlab`): the $x$-fluxes of the two specifications agree on the six shared components; one full three-dimensional Lie step agrees with one one-dimensional step on those components for arbitrary slab data; and if additionally $\Theta = 0$ initially, the $n$-step three-dimensional rollout equals the embedded $n$-step one-dimensional rollout in every component, for all $n$.

### 1.6 Kung–Leiserson Systolic Retiming, Wavefront Throughput & Single-Cell Time-Multiplexed Marching (`lean/Obend/Hardware/SystolicDataflowThroughput.lean`)

A `SystolicDataflowNet` is a synchronous graph (`SyncGraph` of `lean/Obend/Hardware/Retiming.lean`, edges weighted by register counts) with a word operation per node. Its clock-indexed stream semantics `streamValue` is defined by well-founded recursion on (time, topological rank) and is the unique solution of the local stream equations (`streamValue_unique`).

- `positive_cycle_weight_preserved_and_deadlock_free`: if a rank function strictly increases along every zero-register edge (`checkZeroWeightTopological`), then every nonempty cycle carries at least one register, and its register count is unchanged by any retiming lag assignment. The first conjunct excludes combinational loops; the second is the Leiserson–Saxe cycle invariant.
- `systolic_retiming_preserves_stream_semantics`: for a retiming with non-negative lags $r(v)$ and non-negative retimed edge weights, identical primary-input streams with zero input lag, common lag $L$ on primary outputs, and both the original and the retimed graph passing `checkZeroWeightTopological`, the retimed stream is the original stream delayed pointwise by the lag: $\operatorname{ret}(t + r(v), v) = \operatorname{orig}(t, v)$ at every node, hence $\operatorname{ret}(t + L, v) = \operatorname{orig}(t, v)$ at every output. The retimed network gates each node until its start cycle $r(v)$.
- `systolic_wavefront_latency_and_throughput`: for $D>0$ and $s,x,\delta\in\mathbb{N}^D$, the schedule $t(x)=s\cdot x$ satisfies $t(x+\delta)\ge t(x)+1$ whenever every $s_i\ge1$ and $\sum_i\delta_i\ge1$. On the index box $0\le x_i\le K$ in $D$ dimensions the all-ones schedule reaches the far corner at $D K$, and with an $L$-stage pipeline the output latency is $D K + L$ (face corner: $(D - 1) K + L$). The $L$-stage pipeline `stepSystolicPipeline` has empty output before cycle $L$. For a nonempty input list, stage $j\le L$ contains item $k$ after $j$ stage operations at cycle $k+j$. The output delivers one transformed item per cycle from $L$ through $L+|xs|-1$, then drains.
- `multiplexed_single_cell_matches_unrolled_array`: for an `AxisCell` (one shared RTL module with per-axis input encoding and output decoding, versus one dedicated module per axis) satisfying the one-step law `Equivariant`, issuing the $d N^d$ axis-major jobs of a $d$-dimensional cube to the single shared cell yields the same output stream as the bank of $d$ dedicated cells, equal to the specification flux at each job, in $d N^d + 1$ clock samples including the initial fill. The result is independent of initial register contents.
- `euler_cube_stream`, `mhd_cube_stream`: the instances for `EulerGas3D` ($3 N^3 + 1$ samples) and `IdealMhd8Wave` ($2 N^2 + 1$ samples), with `Equivariant` discharged from `euler3d_single_systolic_cell_serves_all_3_axes` and `mhd8wave_single_systolic_cell_serves_both_axes` of §3.
- `multiplexed_systolic_time_march_sound`: if the cell is equivariant, its flux equals the specification flux for every supported axis and input, and the specification covers all $d$ axes, then for any list of split-axis schedules, the sequence of all intermediate grids produced by driving the single multiplexed cell (carrying its actual register file across axis and step boundaries) equals the sequence produced by the dedicated bank, and equals the Lie-split word-level reference `lieMarch` built from `stepQ32Axis`. `euler_time_march` and `mhd_time_march` instantiate it for `EulerGas3D.spec` and `IdealMhd8Wave.spec` under every boundary policy.

The cycle counts use the synchronous stream model.

### 1.7 Silicon, Vulkan GPU, and Yosys+Bitwuzla LEC Verification

Stage 5 of `hardware/gpu/verify_gpu.sh` executes end-to-end hardware and shader checks against the compiled `Obend.Hardware.PdeSolvers` artifacts:

- **Vulkan / AMD RDNA2 Execution**: Runs the emitted Q32.32 compute shaders (`burgers-1d-q32`, `euler-3d-q32`, `mhd-8wave-q32`, `bona-masso-1d-q32`) on an AMD Radeon RX 6750 XT (`gfx1030`, RADV) with `0 ULP` disagreement against Lean's `evalFluxSsaDagQ32`, and verifies that planted `addAsSub` and `mulHighZero` shader mutations are rejected. RDNA2 ISA binaries are independently translation-validated by `certifyDump_sound` and `certifyBlockDump_sound` (`lean/Obend/Hardware/Gpu/Rdna2/CertSound.lean`).
- **Verilator 5.020 Cycle-Accurate Simulation**: Compiles all seven systolic SystemVerilog modules (`EulerGas3D` axes 0–2, `IdealMhd8Wave` axes 0–1, and axis 0 of `BonaMasso1DPrincipal.spec` and `BonaMassoZ4c1D.spec`) in Verilator 5.020 with `0 ULP` difference across multi-state testbenches.
- **Yosys + Bitwuzla SMT-LIB2 Formal Equivalence**: Runs Yosys synthesis and Bitwuzla bit-precise equivalence checking between the emitted SystemVerilog (`emitModuleSV`) and Lean's `RtlModule` transition relation (`emitYosysLecSmt2`), proving `unsat` on `EulerGas3D_axis0` and `BonaMassoZ4c1D_axis0` and `sat` on a planted bit-0 fault. During Stage-5 bringup, this miter caught a genuine IEEE 1800-2017 §11.6.1 context-determined width propagation bug in `emitExprSV` (`lean/Obend/Hardware/HDL.lean`): `$signed(a)` inside `128'($signed(a))` widened compound 64-bit subtractions such as `64'd8589934592 - 64'(q)` in `reciprocalRtlExprs` to 128 bits *prior* to sign interpretation whenever `q[63] = 1`; enforcing inner self-determined width `128'($signed(64'(a)))` restored unconditional 64-bit equivalence.
- **End-to-End 1+1 Bona–Massó / Z4c Relativity Application (`apps/relativity-z4c/`, `lean/Obend/Apps/RelativityZ4cApp.lean`)**: Connects a three-layer open-recursive `.obend` gauge/slicing specification (`BonaMassoSlicing.obend`, `Z4cConstraintDamping.obend`, `RelativityZ4cTop.obend`) via `#import_obend` directly to `BonaMassoZ4c1D.spec` and `BonaMassoZ4c1D.endToEnd_certified` (`relativityZ4c_obend_welds_to_bonaMassoZ4c1D`, `z4c_constraint_damping_contraction_sound`), bundled with Apples-with-Apples gauge-wave benchmarks, WGSL shaders, Yosys SMT2 LEC, Verilator cycle-accurate `wave.vcd` simulation (`apps/relativity-z4c/verify_relativity_z4c.sh`), and `crates/obend-gui` waveform inspection.

### 1.8 Standalone CLI Rollouts, Receipts, and Artifact Emission (`lean/Obend/Analysis/NonlinearPdeCli.lean`)

`obend pde solve` and `obend pde check` (`runPdeCli`) execute exact rational (`"rat"`) or Q32.32 (`"q32"`) multi-D rollouts for any catalog solver or inline `(conservation-law ...)` S-expression under `periodic`, `transmissive`, or `reflective` boundaries, emit 256-bit `cSHAKE256` trajectory receipts (`pdeTrajectoryDigest_binding` with LEB128 length framing over every statement field), check untrusted surrogate trajectories against the `nonlinear_aposteriori_error_tube` bound, and write out WGSL kernels, SystemVerilog RTL, and Yosys SMT2 miters:

```bash
cat > z4c_pulse.json <<'EOF'
{
  "format": "nonlinear-conservation@1",
  "solver": "BonaMassoZ4c1D",
  "dims": [16],
  "steps": 8,
  "backend": "q32",
  "compareQ32": true,
  "recordTrajectory": true,
  "boundary": "periodic",
  "initial": [
    [1, 1, 0, 0, "1/16", "1/8"], [1, 1, 0, 0, "1/16", "1/8"],
    [1, 1, 0, 0, "1/16", "1/16"], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, "1/16", "-1/16"],
    [1, 1, 0, 0, "1/16", "-1/8"], [1, 1, 0, 0, "1/16", "-1/8"]
  ]
}
EOF

obend pde solve z4c_pulse.json --out z4c_solved.json \
  --emit-wgsl ./z4c_wgsl --emit-sv ./bona_masso_z4c.sv --emit-lec ./bona_masso_z4c.smt2
obend pde check z4c_solved.json
```

---

## 2. Discrete Differential Geometry, Exterior Calculus, Hodge Decomposition, Dirac Systems & Coupled Maxwell Radiation

- **Oriented 3-Skeleton DEC, Gauge Holonomy & Exact Poynting Energy Balance (`lean/Obend/Geometry/CochainAndGauge.lean`)**:
  - Over exact `CanonicalRat` cochains on an oriented 3-complex `CellComplex3D`, `coboundary_sq_zero` proves $d_1 \circ d_0 = 0$ and $d_2 \circ d_1 = 0$, and `discrete_stokes_exact` proves $\langle d_k \alpha, c_{k+1} \rangle = \langle \alpha, \partial_{k+1} c_{k+1} \rangle$.
  - `decMaxwell_divB_invariant` and `decMaxwell_charge_continuity` prove exact preservation of $\nabla \cdot B = 0$ and discrete Gauss charge continuity across arbitrary multi-step Yee trajectories without auxiliary divergence cleaning; `hodgeLaplacian0_psd` proves positive semidefiniteness of the scalar Hodge Laplacian.
  - `dec_maxwell_poynting_energy_balance` and `stepDecMaxwell_yee_bilinear_balance` prove the exact discrete Poynting identity over arbitrary 3-cells: the discrete electromagnetic energy difference across any valid Maxwell step equals $-\Delta t \langle E, J \rangle$ minus the boundary Poynting 2-cochain flux summed over $\partial c_3$.
  - `covariant_commutator_eq_curvature` and `discrete_bianchi_identity` prove $[D_x, D_y] = F_\square$, abelian curvature exactness $d_2 d_1 A = 0$, and the non-abelian six-face cube holonomy Bianchi identity for invertible $2 \times 2$ link transports.
- **Simplicial Finite Element Exterior Calculus (`lean/Obend/Analysis/SimplicialFeecFem.lean`)**:
  - Whitney 1-forms and lowest-order Raviart–Thomas elements with Dirichlet-free SPD stiffness (`stiffnessMatrix_spd_on_dirichlet_free`), global flux equilibration (`rt0_global_greens_equilibration_p1`), the Prager–Synge hypercircle identity and constant-free *a posteriori* continuum error bound (`pragerSynge_hypercircle_identity`, `pragerSynge_continuum_error_bound`), and two-sided Thomson–Dirichlet capacitance brackets (`thomsonDirichlet_capacitance_bracket`).
- **Discrete De Rham Complex, Codifferentials & Three-Way Hodge Decomposition (`lean/Obend/Geometry/DeRhamHodgeComplex.lean`)**:
  - On a `CellComplex3D` $K$ with positive diagonal Hodge stars $\star_0, \dots, \star_3$ (`PosHodgeStar`, accepted by `checkPosHodgeStar`), let $\langle \alpha, \beta \rangle_{\star_k} = \sum_i (\star_k)_i\, \alpha_i \beta_i$ (`hodgeInner`) and $\delta_k = \star_{k-1}^{-1}\, \partial_k\, \star_k : C^k \to C^{k-1}$ (`codiff1`, `codiff2`, `codiff3`). `d0_delta1_adjoint`, `d1_delta2_adjoint`, and `d2_delta3_adjoint` prove $\langle d_{k-1} \alpha, \beta \rangle_{\star_k} = \langle \alpha, \delta_k \beta \rangle_{\star_{k-1}}$ for $k = 1, 2, 3$, each a consequence of `discrete_stokes_exact`; `codiff_sq_zero` proves $\delta_1 \delta_2 = 0$ and $\delta_2 \delta_3 = 0$ on every complex passing `checkComplexExact`.
  - With $\Delta_0 = \delta_1 d_0$, $\Delta_1 = d_0 \delta_1 + \delta_2 d_1$, $\Delta_2 = d_1 \delta_2 + \delta_3 d_2$ (`hodgeLap0`, `hodgeLap1`, `hodgeLap2`): `hodgeLap0_weld_and_psd` proves $\langle \phi, \Delta_0 \phi \rangle_{\star_0} = \lVert d_0 \phi \rVert_{\star_1}^2 \ge 0$ and identifies this form with `hodgeLaplacian0` of `lean/Obend/Geometry/CochainAndGauge.lean`; `hodgeLaplacian1_psd` proves $\langle u, \Delta_1 v \rangle_{\star_1} = \langle d_1 u, d_1 v \rangle_{\star_2} + \langle \delta_1 u, \delta_1 v \rangle_{\star_0} = \langle \Delta_1 u, v \rangle_{\star_1}$, hence $\langle \omega, \Delta_1 \omega \rangle_{\star_1} = \lVert d_1 \omega \rVert_{\star_2}^2 + \lVert \delta_1 \omega \rVert_{\star_0}^2 \ge 0$; `hodgeLaplacian2_psd` proves $\langle \beta, \Delta_2 \beta \rangle_{\star_2} = \lVert d_2 \beta \rVert_{\star_3}^2 + \lVert \delta_2 \beta \rVert_{\star_1}^2 \ge 0$.
  - `harmonic1_iff_closed_and_coclosed`: $\Delta_1 \omega = 0$ if and only if $d_1 \omega = 0$ and $\delta_1 \omega = 0$.
  - `exact_coexact_harmonic_orthogonal` and `hodge_decomposition_unique_and_pythagorean`: on a complex passing `checkComplexExact`, for $\phi \in C^0$, $\psi \in C^2$, and $h \in \ker \Delta_1$, the cochains $d_0 \phi$, $\delta_2 \psi$, $h$ are pairwise $\star_1$-orthogonal; $\lVert d_0 \phi + \delta_2 \psi + h \rVert_{\star_1}^2 = \lVert d_0 \phi \rVert_{\star_1}^2 + \lVert \delta_2 \psi \rVert_{\star_1}^2 + \lVert h \rVert_{\star_1}^2$; and if $d_0 \phi_1 + \delta_2 \psi_1 + h_1 = d_0 \phi_2 + \delta_2 \psi_2 + h_2$ with both $h_i$ harmonic and of length equal to the edge count, then $d_0 \phi_1 = d_0 \phi_2$, $\delta_2 \psi_1 = \delta_2 \psi_2$, and $h_1 = h_2$.
  - `verifyHodgeDecomposition1_sound`: if the decidable verifier accepts a certificate $(\phi, \psi, h)$ for a 1-cochain $\omega$, then $\omega = d_0 \phi + \delta_2 \psi + h$ with $h$ closed and coclosed, the three orthogonality relations and the norm identity hold, and every other accepted certificate for $\omega$ has the same three components. Certificates are exercised on `houseLoopComplex` (all three components nonzero) and on the contractible `tetComplex3D` and `unitCubeComplex3D`.
  - `whitney_exterior_derivative_commutes`: on the reference tetrahedron `tetComplex3D`, with affine coefficients in degrees 0–2 and a constant coefficient in degree 3 (`AffineForm0`, `AffineForm1`, `AffineForm2`, `AffineForm3`), Whitney maps $\mathcal{W}_k$ (`whitney0`, `whitney1`, `whitney2`, `whitney3`), formal exterior derivative $\mathrm{d}$ (`extDeriv0`, `extDeriv1`, `extDeriv2`), and de Rham integration maps $\mathcal{R}_k$ (`deRham0`, `deRham1`, `deRham2`, `deRham3`): $\mathrm{d} \circ \mathrm{d} = 0$; $\mathrm{d}\, \mathcal{W}_k = \mathcal{W}_{k+1}\, d_k$ and $\mathcal{R}_{k+1}\, \mathrm{d} = d_k\, \mathcal{R}_k$ for $k = 0, 1, 2$; $\mathcal{R}_k \mathcal{W}_k = \mathrm{id}$ on cochains of the correct length for $k = 0, \dots, 3$; and the projector $\Pi_k = \mathcal{W}_k \mathcal{R}_k$ satisfies $\mathrm{d}\, \Pi_k = \Pi_{k+1}\, \mathrm{d}$ for $k = 0, 1, 2$ and $\Pi_k^2 = \Pi_k$ for $k = 1, 2, 3$.
  - `whitney_tet_physical_grad_matches_feec`: on every tetrahedron of a mesh passing `checkTetMeshOriented`, the volume is positive and the pullback of $\mathcal{W}_1(d_0 u)$ through the affine Jacobian (`pullbackRefCovec3D`) equals the piecewise-linear gradient `p1TetGrad3D` of `lean/Obend/Analysis/SimplicialFeecFem.lean`.
- **Dirac Structures & Multiscale Double Categories (`lean/Obend/Geometry/DiracDoubleCat.lean`)**:
  - Kernel-represented Dirac structures (`dirac_self_orthogonal_iff`, `dirac_power_conservation`), passive resistive termination (`resistiveDirac_dissipative_power`), power-preserving horizontal interconnection (`horizComp_preserves_power_balance`), cochain-commuting vertical coarse-graining (`coarseGrain_preserves_cohomology_and_conservation`), and the double-category interchange law (`doubleCat_interchange_law`).
- **Hardware Switching Currents Coupled to 3D DEC Maxwell (`lean/Obend/Hardware/GlitchAndTempestSafe.lean`, `lean/Obend/Apps/CyberneticRadioNode.lean`)**:
  - Rather than treating electromagnetic side-channel emission as an uncoupled scalar formula, `switching_current_bounds_radiated_flux` and `dualRail_decMaxwell_poynting_tempest_sound` inject gate-level rail switching currents as 1-cochain sources $J$ into `CellComplex3D` Maxwell steps, bounding radiated boundary Poynting flux and receiver SNR while `balanced_wddl_bus_ssn_secret_independent` proves secret-independent Hamming switching noise on dual-rail WDDL buses (`cybernetic_radio_node_multi_turn_sound`).

---

## 3. Open Hypergraphs, Equitable Symmetry Quotients, Adjoint E-Graphs & Interaction Nets

- **Symmetric Monoidal Open Hypergraphs & Dual RTL/GPU Lowering (`lean/Obend/Hardware/OpenHypergraph.lean`, `lean/Obend/Hardware/Square.lean`)**:
  - `StrictOpenHypergraph` represents multi-input/multi-output dataflow morphisms with whole-graph reverse-mode differentiation (`compileGraphAdjoint`). `compileHypergraphToRtl_sound`, `rtl_eq_gpu`, and `pipelined_eq_comb` prove exact denotational agreement across combinational evaluation, retimed pipelines, synchronous RTL, and GPU kernels.
- **1-WL Color Refinement, Equitable Intertwining & Quotient Adjoints (`lean/Obend/Analysis/Equitable.lean`, `lean/Obend/Hardware/QuantumMatter.lean`)**:
  - `checkEquitablePartition_sound`, `checkWl1ColorRefinementStable`, `equitable_handshake_identity`, and `equitable_intertwining_power` mechanize 1-dimensional Weisfeiler–Leman bisimulation, bipartite symmetrizability $|C_i| Q_{i,j} = |C_j| Q_{j,i}$, and polynomial/power intertwining $H^k S = S Q^k$ over $\mathbb{Z}$ and $\mathbb{Z}[i]$ with zero noncomputable reals.
  - On `StrictOpenHypergraph`, `quotientOpenHypergraph_intertwines_eval_and_adjoint` proves that both forward evaluation and reverse-mode `compileGraphAdjoint` differentiation of `buildSymmetric4LaneHypergraph` factor exactly through its compressed quotient `quotientOpenHypergraph`, and `symmetry_preserving_noise_zero_leakage` proves zero leakage out of the symmetric subspace under equivariant perturbations.
  - **Multi-D PDE Axis Equivariance & Single-Cell Systolic Reuse (`lean/Obend/Hardware/PdeHypergraphSymmetry.lean`)**: `euler3d_cyclic_axis_equivariance` and `mhd8wave_planar_axis_equivariance` prove exact $C_3$ cyclic and planar reflection symmetry of `EulerGas3D.spec` and `IdealMhd8Wave.spec`; `euler3d_single_systolic_cell_serves_all_3_axes` and `mhd8wave_single_systolic_cell_serves_both_axes` prove over `stepModuleRegs` / `evalModuleOutputs` that a single axis-0 systolic RTL module serves all spatial axes bit-for-bit across all $2^{64}$ words via wire permutation, while `fluxSsaDagToOpenHypergraph_sound` and `quadInvariant_equitable_quotient_intertwining` quotient shared $S_3$-invariant kinetic and magnetic energy sub-DAGs under 1-WL color refinement.
- **Equality-Saturated Adjoint Hypergraphs (`lean/Obend/Analysis/EqSatHypergraph.lean`)**:
  - Lifts primal and `compileGraphAdjoint` hypergraphs into `HyperEGraph`, proves consistency preservation across 16 algebraic and MAC-fusion rules (`saturateHyperEGraph_preserves_consistency`), and proves semantic, cotangent, pipelined-RTL, and discrete Pontryagin ODE adjoint preservation under minimum-cost extraction (`eqSat_preserves_eval_and_adjoint`, `optimizeAdjointHypergraph_preserves_cotangents`, `eqSat_pipelined_rtl_sound`, `pontryagin_flowpipe_adjoint_eqSat_sound`).
- **Commuting Interaction-Net Reductions (`lean/Obend/Hardware/HvmConfluence.lean`)**:
  - `diamond_of_disjoint` and `batch_schedule_invariant` prove strong commutation of disjoint active pairs and schedule invariance of parallel interaction-combinator batches lowered from `Obend.Leaf.Book` (`lean/Obend/Hardware/Hvm/Lower.lean`, `lowerBookToHvm_sound`).

---

## 4. Validated Continuous Analysis, Gröbner Completion & Succinct Hardware Stencil Proofs

- **Taylor Models, Picard ODE Flowpipes & SOS Barriers (`lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Analysis/Flowpipe.lean`, `lean/Obend/Analysis/SosLyapunov.lean`)**:
  - Polynomial-plus-interval Taylor models with semantic soundness (`taylorModel_picard_sound`, `verifyFlowpipe_sound`) and sparse Sum-of-Squares / Positivstellensatz certificates for nonlinear Lyapunov functions, control barrier functions, and DAE invariant manifolds (`checkSosLyapunov_sound`, `checkSosCbf_sound`, `checkDaeManifold_sound`).
- **Monomial Orders, Multivariate Division & Bounded Buchberger Completion (`lean/Obend/Analysis/BuchbergerCompletion.lean`)**:
  - Polynomials are sparse term lists over `CanonicalRat` with monomials as (variable, exponent) lists (`lean/Obend/Judge/RealAnalysis.lean`); S-polynomials, fuel-bounded reduction, and `checkGroebnerBasis` are those of `lean/Obend/Analysis/Groebner.lean`. `monoNormalize_idem` proves idempotence of the canonical form. For pure lexicographic order `lexLt` and graded order `Monomial.grlexLt`: irreflexivity, transitivity (`lexLt_trans`, `grlexLt_trans`), trichotomy up to normalization (`lexLt_trichotomy`, `grlexLt_trichotomy`), minimality of the unit monomial (`lexLt_unit_min`, `grlexLt_unit_min`), and compatibility with multiplication (`lexLt_mul_left`, `grlexLt_mul_left`). Division and completion terminate by explicit fuel.
  - `polyDivMod_sound_and_irreducible`: if fuel-bounded division returns `polyDivMod fuel f G = some (qs, r)`, then $|qs| = |G|$, $f(\rho) = \sum_i q_i(\rho)\, g_i(\rho) + r(\rho)$ at every rational point $\rho$, and every monomial of $r$ is canonical and divisible by the leading monomial of no $g \in G$ with nonzero leading coefficient. `polyDivMod_zero_rem_cert`: when `r.isZero = true` the quotients form an `IdealMembershipCert` whose expansion evaluates to $f$, and $f$ vanishes on the common zero locus of $G$.
  - `buchberger_first_criterion_coprime` (Cox–Little–O'Shea, Ch. 2 §9, Prop. 4): for canonical $f, g$ with coprime leading monomials, $\operatorname{lcm}(\operatorname{LM} f, \operatorname{LM} g) = \operatorname{LM} f \cdot \operatorname{LM} g$, and with $q_f = -\tfrac{1}{\operatorname{LC} f \cdot \operatorname{LC} g}(g - \operatorname{LT} g)$, $q_g = \tfrac{1}{\operatorname{LC} f \cdot \operatorname{LC} g}(f - \operatorname{LT} f)$ one has $S(f, g) = q_f f + q_g g$ pointwise with every monomial of $q_f f$ and of $q_g g$ strictly below the lcm in `Monomial.grlexLt`.
  - `buchbergerComplete_same_ideal_and_groebner`: if `buchbergerComplete fuel G = some G'`, then $G \subseteq G'$; every element of $G'$ is a polynomial combination of $G$ and conversely (`InEvalIdeal`, membership witnessed by quotients and equality of evaluations at all rational points), so the two lists generate the same ideal in this sense and have the same common zeros in $\mathbb{Q}^n$; and `checkGroebnerBasis fuel G' = true`, i.e. every S-polynomial of $G'$ reduces to zero within the fuel bound. The completion returns `none` when its round budget is exhausted with an unreduced S-polynomial remaining. With fuel 8 the twisted cubic $\langle x_0^2 - x_1,\ x_0^3 - x_2 \rangle$ completes to four generators.
- **Range-Safe Stencil PIOPs & 4-Tile Hypercube Hardware Prover (`lean/Obend/SymbolicZk/StencilRolloutStark.lean`, `lean/Obend/Hardware/OspcProver.lean`, `lean/Obend/Trailblaze/CathedralApex.lean`)**:
  - `stencil_numerator_mod_exact` and `q32Stencil_gpu_arraySource_sound` bridge `Obend.Core.RangeSafe` interval bounds to Goldilocks prime ($p = 2^{64} - 2^{32} + 1$) quotient/remainder constraints without field-inversion wraparound, backed by dual-track Canopy Merkle + Ajtai MSIS polynomial commitments (`lean/Obend/Crypto/DualSpine.lean`, `canopyAjtaiDualPCS_sound_of_hash_or_sis`).
  - `Obend.Hardware.OspcProver` synthesizes a 4-tile $Q_2$ hypercube hardware prover (`FaceIdeal4` cubical ternary registers with `faceIdeal4_boundary_ne_top`, discrimination-tree LUT, delta-net, and streaming LRAT tiles) with 2-hop XOR-butterfly Sumcheck/Merkle folding (`ospc_four_tile_prover_multi_cycle_sound`, `apex_cathedral_ospc_multi_turn_sound`).

---

## 5. Kernel Soundness & Reproducible Verification

- `#assert_axioms_tree` checks the loaded package declarations for axiom dependencies and reports compiler-trust dependencies separately. `#assert_compiled` reruns the closed Boolean oracle claims used by a named declaration (`lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`).
- `Obend.Census` runs `#check_docs_census` on paths and subsystem names, and `#docs_census` on paths, identifiers, and documented constructors. Its thirteen governed files include `README.md`. The same checks accept an explicit document list for `LANYON.md` (`lean/Obend/Tactic/DocsCensus.lean`).
- The test suites use `#tooth` to check sensitivity to specific mutations. For example, replacing the centered difference with a one-sided difference breaks `centeredDiff_h0_skew_adjoint` (`lean/tests/metasystem/RelativityBssnZ4c3DTest.lean`).

From the repository root on a designated Linux build host, run the suites under the project’s memory and time limits.

```bash
cd lean
bounded() { SWARM_MEM_MAX=12G swarm-build timeout --kill-after=10s 600s "$@"; }
bounded lake build Obend obend obend-emit-gpu obend-emit-sv Obend.Census Teeth

# §1.1, §1.2, §1.7, §1.8, §4: compiler, accelerator bridge, CLI, OSPC prover
bounded lake build metasystem.MetaprogPdeCompilerTest metasystem.PdeAcceleratorBridgeTest \
  metasystem.NonlinearPdeCliTest metasystem.CyberneticRadioAndOspcTest

# §1.3: truncation order, summation by parts, weak residual, Q32 weak-form bound, audit judge
bounded lake build Obend.Analysis.LaxWendroffDefs Obend.Analysis.LaxWendroffConvergence \
  metasystem.LaxWendroffConvergenceTest

# §1.4, §1.5: symmetric-hyperbolic energy, 3+1 Z4c, BssnZ4cConstraint3D
bounded lake build Obend.Analysis.SymmetricHyperbolicEnergy Obend.Analysis.RelativityBssnZ4c3D \
  metasystem.RelativityBssnZ4c3DTest

# §1.6: systolic retiming and time-multiplexed marching
bounded lake build Obend.Hardware.SystolicDataflowThroughput metasystem.SystolicDataflowThroughputTest

# §2, §4: discrete Hodge decomposition, Whitney forms, Buchberger completion
bounded lake build Obend.Geometry.DeRhamHodgeComplex Obend.Analysis.BuchbergerCompletion \
  metasystem.DeRhamHodgeAndBuchbergerTest

bounded python3 tests/cli/run_live_subcommands.py

# On the GPU host with Verilator 5.020, Yosys and the SMT tools installed
bounded cargo build --release --manifest-path ../hardware/gpu/runner/Cargo.toml
bounded bash ../hardware/gpu/verify_gpu.sh --stage 5
```

The eight `metasystem` modules live in `lean/tests/metasystem/`. The `Tests` library in `lean/lakefile.toml` includes them all.
