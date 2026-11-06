# Physical

If [`AMBITION.md`](AMBITION.md) states what Objective Bend is as a symbolic, analytic, and
coordination calculus—what comes after Mathematica and smart contract languages—this document states
its physical counterpart: **what comes after CAD, CAM, FEA, and EDA when physical parts,
continuous-time multiphysics, machine tools, and semiconductor/mechanical fabrication live inside the
same open-recursive, proof-carrying kernel.**

Our physical ambition, coherently extrapolated, is to close the loop between **formal mathematical
proof**, **in-silico evolutionary design search**, **self-accelerating silicon**, and **physical
manufacturing in the real world**:

1. Every physical component—from a 180nm mixed-signal die on [`WaferSpace`](lean/Obend/Hardware/WaferSpace.lean)
   or a 40m FT8 transceiver PCB ([`RF.lean`](lean/Obend/Hardware/RF.lean), [`PCB.lean`](lean/Obend/Hardware/PCB.lean))
   to an **LC Drives** direct in-slot liquid-cooled permanent-magnet traction motor
   ([`Magnetics.lean`](lean/Obend/Hardware/Magnetics.lean), [`FluidThermal.lean`](lean/Obend/Hardware/FluidThermal.lean)),
   a **Mission Power `MS350`** 350 kW 7-level Flying-Capacitor Multilevel (`FCML`) SiC solar inverter
   ([`PowerElectronics.lean`](lean/Obend/Hardware/PowerElectronics.lean)), or a 5-axis CNC milling
   cell ([`GeometryCAM.lean`](lean/Obend/Hardware/GeometryCAM.lean), [`Mechanics.lean`](lean/Obend/Hardware/Mechanics.lean))—is
   an open-recursive `Obend` object whose geometry, material laws, datasheet envelopes, toolpaths,
   and temporal lifecycle (`timeSamples`) are first-class values.
2. We model **the machinery itself**—ballscrew servo lag, cantilever end-mill deflection,
   Yusuf Altintas's regenerative chatter stability lobes, plasma-etch aspect-ratio-dependent bread-loafing,
   and thermal rotor growth—so that **the simulator predicts the physical cut or etch more faithfully
   than the machine controller executes its own G-code or recipe.**
3. Because [`Obend/Lower`](lean/Obend/Lower/Proofs/Hardware.lean) lowers verified Lean 4 and `Core4`
   kernels into `Leaf.Book` supercombinators and from there into synthesized FPGA RTL, and
   [`Obend/Hardware/Gpu.lean`](lean/Obend/Hardware/Gpu.lean) lowers array hypergraphs into compute
   shaders that run on the GPUs we own (`HARDWARE.md`), **the physics and geometry kernels can be run
   on the substrate that accelerates the design searches, with the run itself as the gate.**

---

## 1. The Claim: Why Twentieth-Century CAD, CAM, FEA, and EDA Cannot Close the Loop

Industrial physical engineering is currently fractured across four incompatible, unverified silos:

1. **Fragile B-Rep Geometry Kernels Crash Under Evolutionary Search**:
   Legacy C++ Boundary-Representation (`B-Rep` / NURBS) kernels (`Parasolid`, `ACIS`, `OpenCASCADE`)
   represent solids as mutable pointer graphs of trimmed surfaces and topological half-edges glued
   together by floating-point tolerances. When an automated evolutionary or gradient-based search
   mutates a cooling channel or fillets a stator tooth, 10–30% of candidate geometries fail with
   non-manifold edge exceptions or self-intersecting boolean crashes.
2. **CAM Simulates Idealized Teleporters, Not Physical Machine Tools**:
   Conventional CAM post-processors emit `G01`/`G02` coordinates assuming an infinitely stiff spindle
   tracing a zero-lag polyline. In reality, high-speed 5-axis milling is governed by **servo tracking
   lag** ($\tau_{\text{servo}} v_{\text{feed}}$), **cantilever end-mill bending** ($\delta = F_r L^3 / 3EI$),
   **cutter-workpiece engagement (`CWE`) transients**, and **regenerative chatter** (Altintas–Budak
   stability lobes). Because the CAM tool does not model the machine's compliance and dynamics, human
   machinists must babysit prove-outs at 20% feed override.
3. **Siloed Multiphysics Solvers With No Compositional Certificates**:
   Designing a high-torque-density electric machine or a 350 kW multilevel inverter requires coupling
   2D/3D nonlinear magnetostatics ($\nabla \cdot (\nu(\|\mathbf{B}\|^2) \nabla A_z) + J_z = 0$),
   conjugate microchannel fluid-thermal convection, high-$dI/dt$ commutation-loop inductances, and
   high-speed carbon-fiber rotor containment. Existing tools (from single-maintainer 2D magnetics codes
   like David Meeker's `FEMM` to commercial multiphysics suites) pass untyped meshes and CSV tables
   across boundaries with zero machine-checkable proof that thermal growth does not close the magnetic
   air gap or demagnetize the NdFeB rotor magnets.
4. **No Temporal Persistence or Compositional Scene Metatheory**:
   A physical part is not a static `.step` or `.stl` file; it is an evolving entity across time—from
   raw billet (`t = 0`), roughing and finishing toolpaths (`t = 1..k`), sub-assembly mating, and
   dyno calibration to years of field telemetry and wear. Pixar/Apple's **OpenUSD** (`Universal Scene
   Description`) solved non-destructive multi-layer scene composition (`LIVERPS`) and temporal
   `timeSamples` for visual effects and `UsdPhysics`, but its C++ `Pcp` engine lacks a formal
   metatheory, cannot execute open-recursive physical laws (`self`/`super`) when a layer overrides a
   parameter, and represents geometry as static polygon meshes rather than verified implicit solids.

---

## 2. Solids, scenes and tool paths: what the CAD/CAM tier is

The CAD/CAM tier is four modules and one application. What each holds, as of 2026-11-04 (the CAD
review, `review/EXPERT-cad-cam-20261104.md`):

- **One solid representation, two forms.** `FRepExpr` ([`GeometryCAM.lean`](lean/Obend/Hardware/GeometryCAM.lean))
  is an integer implicit solid (`f ≤ 0` inside) with interval enclosure (`frep_interval_enclosure_sound`),
  a dual-interval Lipschitz bound and CSG. The SSA tape (`SsaTapeOp`) is the form pruning, compaction
  and the RTL compiler use. `FRepExpr.toTape` compiles the first to the second and `toTape_eval` proves
  they agree at every point, so an application writes its solid once.
- **Region certificates.** `kdAll` splits a box until a leaf test settles each piece; `kdAll_sound`
  turns a sound leaf test into a statement about every lattice point of the box. Two leaf tests use it:
  `checkDisjoint_sound` (no point is in both the part and the cutter, the gouge check) and
  `checkWall_sound` (every point within a given distance of a cavity is material, the wall check over
  the whole cavity, replacing three probe-point functions that bounded the distance from one point).
- **Cutters.** `frepBallEndMill` is a ball end mill with its shank on an integer tool axis whose length
  is an integer (`(0,0,1)`, `(3,0,4)`, …), so every cutter is a polynomial F-Rep without square roots.
  The motion certificate is a judge, `cam-gouge@1` (`camGougeFormat`, §10): its certificate is a
  k-d tree per move over a part box × the box of tool positions the move sweeps, replayed in
  integers (`checkKdZ_sound`); `checkCamGouge_sound` says an accepted certificate means that at
  every rational time of every move the cutter at its true size contains no rational point of the
  part.
- **The post.** [`Kinematics.lean`](lean/Obend/Hardware/Kinematics.lean) §8 turns 3+2 operations into
  a Fanuc 30i program for an A/C trunnion with tool centre point management (`G43.4`).
  `postMoves_rotarySafe` holds for every list of operations: no feed changes the tool axis, and every
  re-orientation is a rapid on or above the clearance plane.
- **OpenUSD** ([`OpenUSD.lean`](lean/Obend/Hardware/OpenUSD.lean)) is one model: `SdfLayer`/`PrimSpec`
  opinions tagged with an arc kind, sorted by `LIVERPS` strength and lowered to `Term.mix`/`Term.fix`
  (`composePrimToTerm`, `liverps_stronger_arc_dominates_term`); an `xformOp` stack of translations,
  quarter turns and scalings over `FRepExpr`; affine-arithmetic enclosures. The arc kinds rank opinions
  for value resolution; the Pcp graph of arcs (a reference pointing at another layer stack, inherits at
  a class path, variant selection, list editing) is not modelled, and `timeSamples` here is a part
  lifecycle track, not USD's per-attribute time samples.
- **The fidget part** ([`Apps/FidgetCam.lean`](lean/Obend/Apps/FidgetCam.lean), `apps/fidget-cam/*.obend`):
  four `.obend` parameter records with overrides (hub, cooling bore, mounting lug, process) compose the
  values; Lean builds one solid from them (`fidgetParams_eq_obend`), certifies the bore wall
  (`fidget_bore_wall_sound`, 2.0 mm), generates Z-level contours and four 3+2 top-edge passes,
  certifies every lattice point of every segment including plunges and retracts with the shank
  at every rational time of every move with the cutter at its true size
  (`Apps/FidgetCamCert.lean`, `fidget_toolpath_no_gouge_continuous`, from the committed certificate
  `apps/fidget-cam/cam/impeller_5axis.cert` that `lake exe obend-emit-cam` writes), and posts the program
  (`impeller5AxisNgc`). The RTL voxel evaluator is compiled from the same tape.

What is not there: blades (the part is a hub, a lug and a bore), the tool holder, simultaneous
five-axis motion, the machine's own kinematic chain and travel limits, arcs (`G02`/`G03`) in the
output, a theorem relating the RTL to `evalFRepPoint` for every input, and mesh extraction with a
manifold check.

## 3. Simulating the Machinery Better Than the Tool Runs Itself

To evolve physical designs *in silico* and have the first physical article work out of the box,
we cannot treat manufacturing equipment as an idealized geometry printer. We model the **physics of the
manufacturing machine itself**:

### 3.1 Machining dynamics ([`GeometryCAM.lean`](lean/Obend/Hardware/GeometryCAM.lean) §4)
- `machining_material_monotone_removal`: subtracting a swept volume never adds material.
- `evalActualCutterPosNm`, `machining_governor_bounds_surface_error`: servo lag `v·τ` plus a linear
  cantilever deflection under `F_r = k_r a_p h`, as a scalar model with the constants as inputs.
- `checkAltintasChatterStable`, `altintas_chatter_depth_monotone`: a stability inequality on axial
  depth with the real part of the tool-point FRF as a given number, not a computed lobe diagram.

These are models with their constants supplied; none is identified from a machine, and none feeds
the tool-path certificate of §2.

### 3.2 Semiconductor & Nanofab Process Physics ([`FabuBlox.lean`](lean/Obend/Hardware/FabuBlox.lean), [`DRC.lean`](lean/Obend/Hardware/DRC.lean), [`WaferSpace.lean`](lean/Obend/Hardware/WaferSpace.lean))
- Just as G-code is not the physical part, a GDSII polygon is not the silicon wafer. `Obend` models:
  - **RIE Selectivity & Over-Etch Barrier Punch-Through** (`checkFacilityStep` in [`FabuBlox.lean`](lean/Obend/Hardware/FabuBlox.lean)),
  - **PVD Bread-Loafing & Keyhole Pinch-Off vs. Conformal ALD Trench Fill** (`pvd_high_ar_keyhole_refused` in [`DRC.lean`](lean/Obend/Hardware/DRC.lean)),
  - **FEOL Copper/Gold Cross-Contamination Interlocks** (`facilityCheck_prevents_feol_contamination`),
  - **2D Prouhet–Thue–Morse Common-Centroid Oxide Curvature ($\nabla^2 P$) Cancellation** (`prouhetThueMorse_cancels_linear_and_quadratic_bow` in [`Analog.lean`](lean/Obend/Hardware/Analog.lean)), and
  - **Plasma-Etch Antenna Gate-Oxide Charging & CMP Dishing Density** (`checkWaferSpaceSignoff` in [`WaferSpace.lean`](lean/Obend/Hardware/WaferSpace.lean) for `gf180mcuD`, `sky130A`, and `ihpSg13g2`).

---

## 4. Deep Multiphysics: Magnetics, Direct In-Slot Liquid Cooling, and Multilevel Power

Our physical domain library is built around real, extreme-power hardware systems rather than toy textbook
examples. Two things to hold on to while reading this section (the expert review of 2026-11-03,
`review/EXPERT-physics-numerics-20261103.md`, and the work of 2026-11-04):

- **Where the physics enters.** Nothing here is a real number. The device parameters enter the theorems
  either as free rational variables (the universal theorems) or as integer literals in `golden*`
  fixtures discharged by `decide`; the one place a physical *law* enters is as a named hypothesis, e.g.
  `ZohRl.Spec` in [`CurrentLoop.lean`](lean/Obend/Hardware/CurrentLoop.lean) (the ZOH pole lies in the
  exponential's enclosure) and `AnalyticModel` in [`TaylorModel.lean`](lean/Obend/Analysis/TaylorModel.lean).
  A sentence below that quotes a number is quoting a fixture; the fixture's units are now named.
- **The one device done end to end.** The LC Drives stator current loop is a chain of theorems with
  `R`, `L`, `Ts`, `Kp`, `Ki` free: the exact ZOH plant (`stepZoh`), the PI step the RTL computes
  (`stepLoop`), the closed-loop error map (`stepLoop_error_dynamics`), a discrete Lyapunov certificate
  checked by interval arithmetic over a parameter box (`checkLoopLyapunovBox_sound`), and the
  end-to-end bound `lc_drives_current_loop_converges` ([`CurrentLoop.lean`](lean/Obend/Hardware/CurrentLoop.lean)).
  What it still lacks is listed in that file's header: the inverter between `v` and the winding, the
  mechanical equation, and the input-to-state version that absorbs the RTL's 1 mV truncation.

1. **2D FEMM-Style Magnetics FEA, Newton-Raphson B-H Saturation & `libCEED` Matrix-Free Contraction ([`Magnetics.lean`](lean/Obend/Hardware/Magnetics.lean))**:
   - Mechanizes first-order triangular finite elements (`FemmTriangle2D`) for $\nabla \cdot (\nu \nabla A_z) + J_z = 0$
     with proved gauge invariance ([`femm_gauge_invariance`](lean/Obend/Hardware/Magnetics.lean#L119-L135)),
     co-energy convexity ([`femm_mesh_energy_nonneg`](lean/Obend/Hardware/Magnetics.lean#L166-L176)),
     Newton-Raphson nonlinear ferromagnetic B-H tangent stiffness positive semi-definiteness
     ([`femm_newton_raphson_tangent_psd`](lean/Obend/Hardware/Magnetics.lean#L357-L367)), and
     **`libCEED` (`arXiv:2103.12881`) matrix-free element operator evaluation** $y_e = G_e^\top (D_e (G_e A_e))$
     ([`femm_matrix_free_nodal_sum_zero`](lean/Obend/Hardware/Magnetics.lean#L386-L401),
     [`femm_matrix_free_energy_identity`](lean/Obend/Hardware/Magnetics.lean#L420-L425))—plus Park/Clarke
     $dq0$ IPM reluctance torque boost ([`ipm_reluctance_torque_boost`](lean/Obend/Hardware/Magnetics.lean#L236-L257))
     and Steinmetz core-loss signoff. Units were named on 2026-11-04: torque is
     `evalIpmTorqueTwiceMicroNm` (twice µN·m; the golden LC Drives point at $i_d = -100$ A, $i_q = 250$ A is
     304.5 N·m, 34.5 N·m of it reluctance; the previous function added mWb to µH and reported a 128:1
     reluctance:PM ratio), core loss is `evalSteinmetzCoreLossMw` with $f$ in Hz, $B$ in mT and
     $k_h, k_e$ in mW/(Hz·T²), mW/(Hz²·T²) (the golden point is 599 W at 1.65 T, 400 Hz), and the
     element residual is the Galerkin residual scaled by $12\Delta$ with the consistent load $J\Delta/3$.
     The FEM here is element algebra (gauge invariance, energy non-negativity, the Newton–Raphson tangent);
     there is no assembled solve and no boundary condition.
2. **LC Drives (Potsdam, NY) Direct In-Slot Microchannel Stator Cooling ([`FluidThermal.lean`](lean/Obend/Hardware/FluidThermal.lean))**:
   - Models hydraulic manifold mass conservation, Darcy–Weisbach microchannel pressure drop, and
     conjugate heat transfer—proving why **LC Drives' direct in-slot microchannel cooling** (placing
     coolant channels directly inside the stator slot in contact with the conductors, bypassing the
     slot liner and laminated iron tooth/yoke thermal barrier) achieves a $224^\circ\text{C}$ lower
     winding temperature at $8\,\text{kW}$ stator copper loss than a conventional outer water jacket
     *in a one-node series thermal network whose five resistances are inputs* ($224 = 8000 \cdot (12 + 18 - 2)$ mK/W;
     the identity is `lc_drives_in_slot_temp_drop_identity`, the numbers are inputs)
     ([`lc_drives_in_slot_temp_drop_identity`](lean/Obend/Hardware/FluidThermal.lean#L274-L281),
     [`lc_drives_in_slot_cooler_than_outer_jacket`](lean/Obend/Hardware/FluidThermal.lean#L288-L298));
     the fixture that checked the $346^\circ\text{C}$ / $122^\circ\text{C}$ dyno numbers by kernel evaluation was
     deleted in the fixture triage of 2026-11-04, so those two temperatures are checked nowhere.
3. **Mission Power / Mission Sun `MS350` 350 kW Flying-Capacitor Multilevel (`FCML`) Solar Inverter ([`PowerElectronics.lean`](lean/Obend/Hardware/PowerElectronics.lean))**:
   - Mechanizes the 7-level ($M = 6$ cell) wide-bandgap SiC/GaN `FCML` phase leg. Its $6\times$
     switch voltage stress reduction ($1500\,\text{V} \to 250\,\text{V}$) and $M^2 = 36\times$ output
     filter inductance reduction are a closed check on those numbers, kept as an `example` in
     [`Fixtures.lean`](lean/Obend/Teeth/Hardware/Fixtures.lean) and run before a push; the universal
     statement is that the $M^2$ factor is at least 1 and grows with $M$ ([`fcml_level_sq_divisor_mono`](lean/Obend/Hardware/PowerElectronics.lean#L324-L340)),
     Phase-Shifted PWM natural flying-capacitor charge balance ([`fcml_pspwm_natural_balance`](lean/Obend/Hardware/PowerElectronics.lean#L334-L339)),
     active balancing quadratic Lyapunov contraction ([`fcml_active_balancing_lyapunov_contraction`](lean/Obend/Hardware/PowerElectronics.lean#L367-L382)),
     incremental-conductance MPPT global optimality ([`mppt_incremental_conductance_global_max`](lean/Obend/Hardware/PowerElectronics.lean#L73-L98)),
     laminated busbar $L_{\text{loop}} dI/dt$ surge bounds, and autonomous grid-forming $P\text{--}\omega$
     frequency droop sharing ([`distributed_droop_proportional_power_sharing`](lean/Obend/Hardware/PowerElectronics.lean#L194-L202)).
4. **High-Speed Rotordynamics, Carbon-Fiber Containment & Von Neumann Closure ([`Mechanics.lean`](lean/Obend/Hardware/Mechanics.lean))**:
   - Mechanizes thin-ring centrifugal hoop stress $\sigma_\theta = \rho \omega^2 r^2$ for carbon-fiber
     IPM retention sleeves, Jeffcott supercritical rotor-bearing whirl margin, hot running air-gap
     clearance under combined thermal + centrifugal radial growth ([`hot_air_gap_no_rub_sound`](lean/Obend/Hardware/Mechanics.lean#L156-L163)),
     and self-reproducing robotic factory cell closure ([`von_neumann_reflexive_closure_sound`](lean/Obend/Hardware/Mechanics.lean#L219-L234)).
5. **Featherstone 6D Spatial Vector Algebra ($se(3)/se^*(3)$) & Ruckig Jerk-Limited Trajectory Profiles ([`Kinematics.lean`](lean/Obend/Hardware/Kinematics.lean))**:
   - Mechanizes Featherstone's 6D spatial vectors over integers (`SpatialTwist6D` $\in se(3)$,
     `SpatialWrench6D` $\in se^*(3)$, the pairing `spatialPower`, the cross products `spatialCrossMotion`
     and `spatialCrossForce`; there are no frame transforms) with machine-checked proofs of the
     adjoint identity of the two cross products ([`featherstone_spatial_adjoint_duality`](lean/Obend/Hardware/Kinematics.lean#L194-L201):
     $\langle f, u \times_m v \rangle + \langle u \times_f f, v \rangle = 0$) and of the `RNEA` fact that the
     Coriolis wrench does no work along the link's own twist ([`rnea_gyroscopic_coriolis_power_zero`](lean/Obend/Hardware/Kinematics.lean#L210-L218)).
   - Mechanizes **Ruckig (`arXiv:2105.04830`) third-order jerk-limited ($C^2$) trajectory segments**
     (`stepRuckigSegment`) and proves that symmetric jerk-pulse (`+j`, `-j`) S-curve transitions return
     acceleration to zero while advancing velocity by $j \cdot \Delta t^2$, eliminating step-acceleration
     excitation of machine-tool structural modes ([`ruckig_symmetric_pulse_exact`](lean/Obend/Hardware/Kinematics.lean#L242-L252)).
6. **Persistent OpenUSD Assemblies, `timeSamples`, & Affine Arithmetic CSG Tape Pruning ([`OpenUSD.lean`](lean/Obend/Hardware/OpenUSD.lean))**:
   - Mechanizes OpenUSD `timeSamples` chains of a part's physical state, proving that a lifecycle
     invariant checked at the first sample and at every checked transition holds at the last
     ([`usd_lifecycle_invariant_preserved`](lean/Obend/Hardware/OpenUSD.lean#L723-L741)); nothing orders or
     inserts time samples. 1st-order **Affine Arithmetic** (`AffineForm1D`: $c_0 + c_1 \epsilon_1 + c_2 \epsilon_2$;
     `AffineForm3D` adds an error term $r_{\text{err}} \epsilon_e$; $\epsilon_i \in [-1, 1]$) tracks correlated
     spatial variations across CSG trees and cancels self-subtraction: a 1D form minus itself encloses
     exactly $[0, 0]$ (`affine_sub_self_exact_zero`), and a 3D form does when its error term is zero
     (`affine3d_sub_self_zero_linear`), unlike naive interval arithmetic, where $a - a$ has twice $a$'s width.
7. **Idiomatic `.obend` Userspace Physical Engineering & Hardware Lowering ([`UserspacePhysical.lean`](lean/Obend/Hardware/UserspacePhysical.lean))**:
   - Physical assemblies are authored directly in idiomatic `.obend` userspace using `spec`, `def`,
     `super`, `self`, and `#law` contracts ([`LcDrivesStatorUsd.obend`](lean/tests/obend-source/world/physical/LcDrivesStatorUsd.obend),
     [`Cnc5AxisMill.obend`](lean/tests/obend-source/world/physical/Cnc5AxisMill.obend)).
   - The compiled parts' closed RTL checks are `example`s in `lean/Obend/Teeth/Hardware/Fixtures.lean`
     (`checkRtlModule` and one input's outputs per part), run before a push, not on every build.

---

## 5. Accelerator Arithmetic, and the Device That Runs It

[`Accelerators.lean`](lean/Obend/Hardware/Accelerators.lean) holds integer identities that accelerator
designs rest on, labelled as such: polynomial identities in Ozaki base-13 limbs
(`ozaki_base13_2limb_product_exact`, `ozaki_base13_klimb_mul_exact`, `ozaki_base13_klimb_dot_exact`,
`arXiv:2608.06812`), the Kulisch accumulator's fold identity (`kulisch_dot_append_exact`,
`arXiv:2607.13898`), an interval enclosure for rounded addition (`interval_add_encloses_true_sum`), and
three folds over `Int` lists being the same fold (`systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot`). None
of these is a model of a device.

The device model is [`Obend/Hardware/Gpu.lean`](lean/Obend/Hardware/Gpu.lean) with
[`ArrayHypergraph.lean`](lean/Obend/Hardware/ArrayHypergraph.lean): wires carrying vectors, one compute
shader per wavefront stage, `lowerArrayToGpu_sound`, and a gate (`hardware/gpu/verify_gpu.sh`) that
runs every graph, among them a 64-point Goldilocks NTT, on hbox's RDNA2 card under two drivers and on
the Mac's GPU, with planted faults and the final ISA captured. Until 2026-11-05 this section described
an AMD `CDNA3` instruction interpreter, "six-stage self-acceleration" theorems and GPU co-execution
certificates in several apps; the council (`review/FABLE-COUNCIL-20261101.md` §2.4) found them to be
evaluating one number several ways on a device nobody ran, and they were removed when the real path
landed (`review/GPU-PROGRAM-20261105.md`).

---

## 6. In-Silico Evolutionary Co-Design & The Von Neumann Loop

Because every physical domain in `Obend.Hardware` exposes a total, deterministic kernel `Judge`
backed by compact 39-byte **RFC 8949 Binary CBOR (`Tag 0x0BED`)** and **`.obnb` (`Obend.Core.Data`)**
certificates ([`Codec.lean`](lean/Obend/Hardware/Codec.lean)) across a zero-JSON Rust FFI bridge
([`hardware/rust-ffi`](hardware/rust-ffi/src/lib.rs)):

1. **Swarm Evolutionary Search Under `EpistemicConsensus`**:
   Untrusted evolutionary, genetic, CMA-ES, and gradient-guided agents running on the Rust/GPU host
   propose thousands of candidate mutations to an OpenUSD/`Obend` assembly—varying stator tooth taper,
   in-slot microchannel aspect ratio, `FCML` switching frequency, and 5-axis roughing/finishing
   toolpaths.
2. **Kernel Gatekeeping (`evolutionary_search_emits_only_verified_designs`)**:
   Every candidate is filtered by [`checkCandidateManufacturingSafe`](lean/Obend/Hardware/GeometryCAM.lean#L376-L380)
   and [`checkBinaryHwCert`](lean/Obend/Hardware/Judge.lean): gouging toolpaths, chattering axial cuts,
   excessive end-mill deflections, saturating stator teeth, overheating windings, and over-budget BOM
   swaps ([`AgenticEDA.lean`](lean/Obend/Hardware/AgenticEDA.lean)) are deterministically refused with a
   named `HwClause` witness, while valid Pareto improvements commit into the `Vault` with a
   cSHAKE256 `Receipt.Dated`.
3. **Closing the Real-World Loop (`von_neumann_reflexive_closure_sound`)**:
   Certified designs emit directly as synthesizable SystemVerilog-2012, open-foundry GDSII/OASIS
   signoff packages (`WaferSpace`), Gerber/ODB++ stackups (`PCB`), and deflection/chatter-compensated
   5-axis G-code (`GeometryCAM`). Metrology and dynamometer telemetry from the manufactured part flow
   back into the part's OpenUSD `timeSamples` track in the `Vault`, narrowing the interval enclosures
   for the next evolutionary generation—and laying the formal foundations for a self-improving,
   self-manufacturing physical engineering loop.

---

## 7. Wave 6 Overhaul: Data-Parallel Open Hypergraphs, `catgrad` Optics, `fidget` Tape Pruning, Coupled PDEs & The Quantum Matter Compiler

Wave 6 unifies the hardware, geometric, kinematic, multiphysics, and quantum subsystems around a common categorical and algebraic spine:

1. **Data-Parallel `StrictOpenHypergraph` & Syntactic `catgrad` Reverse-Mode AD ([`OpenHypergraph.lean`](lean/Obend/Hardware/OpenHypergraph.lean))**:
   - Mechanizes pointer-free `FiniteFunction`, `IndexedCoproduct`, and `StrictOpenHypergraph` (`arXiv:2305.01041`, `~/hellas/open-hypergraphs`), with Kahn/Coffman–Graham topological wavefront layering (`layerHypergraph`) and synchronous snapshot equivalence (`layerHypergraph_sound`, `evalHypergraph_pipelined_eq_comb`).
   - Mechanizes `catgrad` syntactic `Optic` reverse-mode AD (`OpticOp`, `compileOpticAdjoint`, `optic_reverse_ad_sound`, `optic_comp_chain_rule_sound`, `compileOpticToHypergraph_sound`) with zero runtime dynamic tape allocation, and lowers hypergraphs directly to `Obend.Hardware.HDL.RtlModule` (`compileHypergraphToRtl`, the one-element instance of `compileArrayGraphToRtl`; `compileHypergraphToRtl_sound`).
2. **Multi-Argument Hardware Compilation, Pipelined `Book` Synthesis & Executable Calyx Control ([`Compiler.lean`](lean/Obend/Hardware/Compiler.lean), [`ReductionMachine.lean`](lean/Obend/Hardware/ReductionMachine.lean))**:
   - Extends `Compiler.lean` with multi-argument port compilation (`compileMultiArgTerm_sound`), non-inlined pipelined inter-slot `Book` synthesis (`compileLeafDefPipelined_sound`), and executable Calyx (`arXiv:2102.09713`) `go`/`done` group FSMs (`evalCalyxControl`, `calyx_group_go_done_handshake_sound`, `calyx_seq_two_group_pipeline_sound`).
   - Upgrades `ReductionMachine.lean` with a multi-cycle `BendTT` Interaction-Net PE (`stepInteractionNetPe`, `resolveTwoWireSplices`, `inet_dynamic_splice_cascading_reduction`) that dynamically resolves principal-port wire splices into cascading active pairs.
3. **`fidget` Interval `Choice` CSG Tape Specialization & Full 3D Affine Arithmetic ([`GeometryCAM.lean`](lean/Obend/Hardware/GeometryCAM.lean), [`OpenUSD.lean`](lean/Obend/Hardware/OpenUSD.lean))**:
   - Mechanizes Matt Keeter's `fidget` 4-valued `FidgetChoice` (`unknown`, `left`, `right`, `both`) interval selector (`ivMinChoice`, `ivMaxChoice`) and recursive CSG tape compaction (`pruneFRepTape`), proving universal point-evaluation preservation (`pruneFRepTape_sound`) and monotonic AST size reduction (`pruneFRepTape_size_le`).
   - Mechanizes full 3D Stolfi–de Figueiredo Affine Arithmetic (`AffineForm3D`, `evalFRepAffine3D_encloses_point`) and connects OpenUSD lifecycle invariants to `Obend.Law.CellContract` `Narrows` forever-crowns (`usd_lifecycle_contract_narrows_sound`).
4. **Multi-Link Featherstone `RNEA`, 7-Phase Ruckig Profiles & Coupled Electro-Thermal/FEMM PDEs ([`Kinematics.lean`](lean/Obend/Hardware/Kinematics.lean), [`Magnetics.lean`](lean/Obend/Hardware/Magnetics.lean), [`FluidThermal.lean`](lean/Obend/Hardware/FluidThermal.lean))**:
   - Proves multi-link articulated Coriolis power neutrality (`multi_link_rnea_total_coriolis_power_zero`, `forward_chain_rnea_coriolis_power_zero`) and exact closed-form rest-to-rest integration for 7-phase `UDDU`/`UDUD` Ruckig trajectories (`ruckig_7phase_symmetric_rest_to_rest_identity`).
   - Proves global 2D FEMM nodal residual equilibrium (`femm_global_residual_sum_zero`), Maxwell Stress Tensor air-gap torque bilinearity (`maxwell_stress_torque_bilinear_scale`), and coupled temperature-dependent copper resistivity $I^2 R(T)$ thermal-runaway prevention (`electro_thermal_contraction_identity`, `lc_drives_in_slot_prevents_thermal_runaway`).
5. **Variable-Length RFC 8949 Binary CBOR (`0x9A`), Real Rust Solvers & Live Verilator 5.050 Co-Simulation ([`Codec.lean`](lean/Obend/Hardware/Codec.lean), [`Judge.lean`](lean/Obend/Hardware/Judge.lean), [`hardware/rust-ffi`](hardware/rust-ffi/src/lib.rs), [`run-hardware.py`](lean/tests/run-hardware.py))**:
   - Proves universal round-trip soundness for variable-length CBOR `UInt32` arrays/tapes (`cborDecodeU32List_encode_exact`, `decode_encode_binaryTapeCert`) with kernel replay of evolutionary candidates (`evalEvolutionCandidatePeakTemp`).
   - Implements, in Rust (not Lean, so none of it is a theorem here), 2D FEMM Newton-Raphson on a 6-element stator slot mesh (`obend_hw_ffi::solve_femm_mesh`), 3D octree `Choice` tape pruning (`obend_hw_ffi::eval_octree_frep_pruned`), and 80-candidate Pareto optimization (`obend_hw_ffi::evolve_physical_design`), plus live `obend hardware emit-sv` + Verilator `-Wall` C++ co-simulation in `run-hardware.py`.
6. **Hybrid Symbolic-Numeric Quantum Walks & The Physical Matter Compiler ([`Equitable.lean`](lean/Obend/Analysis/Equitable.lean), [`QuantumWalk.lean`](lean/Obend/Analysis/QuantumWalk.lean), [`QuantumMatter.lean`](lean/Obend/Hardware/QuantumMatter.lean))**:
   - Mechanizes 100% computable equitable partitions, 1-WL color refinement, the integer handshake identity $|C_i| Q_{i,j} = |C_j| Q_{j,i}$ (`equitable_handshake_identity`), and universal $k$-step walk intertwining $H^k \Pi = \Pi Q^k$ (`equitable_intertwining_power`).
   - Unifies Godsil spectral projectors and Buchberger Gröbner normal forms (`Groebner.lean`) for Bachman–Tamon quotient PST (`bachman_tamon_quotient_pst_iff`). Exact algebraic $P_3$ Perfect State Transfer and the interval-flowpipe and Taylor-unitarity checks over $\mathbb{Q}$ are closed checks on fixed data, kept as `example`s in [`Fixtures.lean`](lean/Obend/Teeth/Analysis/Fixtures.lean) and run before a push.
     The integrator (`Flowpipe.lean`) is a second-order interval Taylor step, not a symplectic method; its
     universal theorems are the interval-arithmetic half of a validated step (`picard_step_encloses_trajectory`),
     and the analytic half, existence of the ODE solution and its membership in the a-priori box, is not
     proved in this library. The Taylor models' transcendental remainders are relative to `AnalyticModel`,
     whose only instance is polynomial (`TaylorModel.lean` §5).
   - Synthesizes multi-waveguide photonic CTQW arrays with open-foundry DRC and exact $\mathbb{Z}[i]$ CMT power conservation (`photonic_ctqw_array_power_conserved`, `photonic_matter_compiler_drc_sound`), and proves zero computational leakage under symmetry-preserving noise on IBM Heavy-Hex $C_{12}$ lattices and Microsoft Majorana-1 tetron parity sectors (`symmetry_preserving_noise_zero_leakage`).
