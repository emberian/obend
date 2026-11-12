# Continuous, Semiconductor Device, and Manufacturing Verification

Obend verifies continuous-math, semiconductor device physics, radio-frequency DSP, and CNC manufacturing invariants by pairing exact rational interval/polynomial arithmetic in Lean 4 (`CanonicalRat`, `Interval`, `TaylorModel`, `SOSPoly`) with byte-decoded certificate judges in `Obend.Judge.registry`.

---

## 1. Validated Real, Taylor-Model, SOS, and Hybrid Flowpipe Judges

Continuous enclosures rest on exact dyadic/canonical rational arithmetic (`lean/Obend/Analysis/RealAnalysis.lean`, `lean/Obend/Judge/RealAnalysis.lean`, `lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean`):

- **Interval Bisection (`interval-bound@1`)**: `Obend.Judge.intervalCheck` (`lean/Obend/Judge/RealAnalysis.lean`) and `Obend.Elab.AutoCert.intervalFormat` (`lean/Obend/Elab/AutoCert.lean`) evaluate rational interval trees over arithmetic and transcendental bounds, backed by `intervalCheck_sound`.
- **Taylor Models (`taylor-model@1`)**: `TaylorModelExpr` and `evalTaylorModelExpr` (`lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean`) bound polynomial-plus-remainder enclosures over compact intervals, with `evalTaylorModelExpr_models` and `taylorModelJudge_semantic` proving semantic soundness over any `AnalyticModel`.
- **Sum-of-Squares & Gröbner Certificates (`groebner-ideal@1`, `sos-lyapunov-cbf@1`)**:
  - `lean/Obend/Judge/RealAnalysis.lean` proves `sosCheck_sound` for sparse multivariate `SOSPoly` decompositions.
  - `Obend.Elab.AutoCert` (`lean/Obend/Elab/AutoCert.lean`) verifies Buchberger S-polynomial ideal membership and Positivstellensatz non-negativity witnesses (`checkGroebnerJudge_sound`, `checkGroebnerJudge_sound_membership`, `badGroebnerCert_refused`).
  - `Obend.Analysis` (`lean/Obend/Analysis/SosLyapunov.lean`) verifies polynomial Lyapunov functions, control barrier functions (`checkSosLyapunov_sound`, `checkSosCbf_sound`), and DAE manifold invariance (`checkDaeManifold_sound`, `checkSosLyapunovProblem_sound`, `sosLyapunov_bad_refused`).
- **Hybrid Automata Flowpipes (`hybrid-flowpipe@1`)**: `Obend.Analysis` (`lean/Obend/Analysis/Flowpipe.lean`, `lean/Obend/Analysis/Hybrid.lean`) checks discrete guard/reset jumps (`HybridAutomaton`, `HybridProblem`, `HybridCert`) and continuous flowpipe safety (`hybrid_flowpipe_safety_admits_contract`, `hybridFlowpipe_bad_refused`).

---

## 2. Semiconductor Drift-Diffusion Judge (`devsim-dd1d@1`)

`lean/Obend/Hardware/Device` (`lean/Obend/Hardware/Device/Constants.lean`, `lean/Obend/Hardware/Device/Enclosure.lean`, `lean/Obend/Hardware/Device/DriftDiffusion.lean`, `lean/Obend/Hardware/Device/Sky130Diode.lean`) certifies 1D steady-state semiconductor device solutions produced by external TCAD solvers such as DEVSIM:

- **Validated Exponential & Scharfetter–Gummel Enclosures (`lean/Obend/Hardware/Device/Enclosure.lean`)**: Bounds exponential, Bernoulli (`bernOf_mem`), fractional-power (`powBracket_agree`), and square-root (`sqrtBracket_bounds`) functions in exact `CanonicalRat` intervals (`within_sound`, `expEnclosure_of_half`).
- **Poisson & Continuity Residual Checker (`lean/Obend/Hardware/Device/DriftDiffusion.lean`)**:
  - `DdSpec` specifies mesh nodes, doping profiles, boundary potentials, recombination parameters, and residual tolerances; `DdSolution` carries candidate electrostatic potential and electron/hole quasi-Fermi or carrier profiles.
  - `checkDd` verifies mesh monotonicity, boundary conditions, doping consistency, Gauss-law Poisson residuals, and Scharfetter–Gummel electron/hole continuity equations, returning pinpointed `DdClause` refusals (`bad_refused_doping`, `bad_refused`).
  - `ddFormat` registers `devsim-dd1d@1` in `Obend.Judge.registry` with byte-level soundness theorem `ddFormat_sound` (`DdMeaning`).
- **SkyWater 130 nm Junction Specification (`lean/Obend/Hardware/Device/Sky130Diode.lean`)**: `sky130DiodeRecipe` and `sky130DiodeSpec` instantiate `DdSpec` for a physical Sky130 p-well / n+ junction diode across bias sweeps.

---

## 3. Certified CNC Toolpath Gouge Verification (`cam-gouge@1`)

`Obend.Hardware.GeometryCAM` (`lean/Obend/Hardware/GeometryCAM.lean`) and `Obend.Apps.FidgetCam` (`lean/Obend/Apps/FidgetCam.lean`, `lean/Obend/Apps/FidgetCamCert.lean`) verify that multi-pass CNC milling toolpaths never gouge the target functional-representation (`FRepExpr`) solid:

- **Swept-Volume Subdivision Certificates (`lean/Obend/Hardware/GeometryCAM.lean`)**:
  - Target parts are represented as signed-distance / implicit `FRepExpr` trees evaluated over rational 3D boxes (`QBox`, `QIv`).
  - For each cutter-location segment `(CLPoint × CLPoint)` and `ToolAxis`, `CamPassCert` supplies a spatial subdivision cover proving that the swept cutter envelope stays strictly outside the finished part (`CamGougeMeaning`).
  - `camGougeFormat` registers `cam-gouge@1` in `Obend.Judge.registry`, backed by planted refusal `camGougeBad_refused`.
- **Continuous No-Gouge Proof (`lean/Obend/Apps/FidgetCam.lean`, `lean/Obend/Apps/FidgetCamCert.lean`)**:
  - `fidget_post_rotarySafe` and `fidgetCam_liverps_bore_radius` verify rotary post-processor and bore geometry invariants.
  - `fidgetCertAccepted_true`, `fidgetCamObj_meaning`, and `fidget_toolpath_no_gouge_continuous` prove continuous gouge freedom across every pass of `fidgetParams`.
  - Resulting RS-274 `.ngc` G-code and `.stl` meshes parse directly via `NgcToolpath` and `StlMesh` in `crates/obend-gui/src/apps.rs`.

---

## 4. Mixed-Signal Quadrature SDR Verification (`lean/Obend/Apps/SdrFt8Rx.lean`)

`lean/Obend/Apps/SdrFt8.lean` and `lean/Obend/Apps/SdrFt8Rx.lean` combine bit-accurate RTL semantics with continuous Taylor-model and interval judges for a digital FT8 shortwave receiver:

- **Fixed-Point NCO Phasor Bound**: `nco_fixed_point_ok` and `nco_phasor_error` bound quantized lookup-table phasor error across every phase accumulator state of `sdrNcoModule` (`nco_tt_le`).
- **Image-Rejection Ratio ($\ge 63\,\text{dB}$)**: `irrCos_judge_ok` (`checkTaylorModelJudge`) and `irr_judge_ok` (`Obend.Judge.intervalCheck`) discharge the trigonometric and rational inequalities required by `sdr_irr_ge_63dB` over any `AnalyticModel`.
