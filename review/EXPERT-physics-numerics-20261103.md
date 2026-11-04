# Sitting next to the physicist: validated numerics, multiphysics, motor drives, photonics (2026-11-03)

Slug `physics-numerics`. The persona: validated numerics (intervals, Taylor models, verified ODE
enclosures), finite-element magnetics, motor-drive and power-electronics design, with photonics and
quantum-hardware colleagues. Working tree as of 2026-11-03, not HEAD; nothing edited but this file.

Tags: **READ** (file opened, `path:line` cited), **INFERRED** (deduced from READ facts), **PROPOSED**.
Every number has the command or the arithmetic that produced it. No Lean or Rust was built. Runs:
`verilator --lint-only -Wall` on one `.sv`; `lean/.lake/build/bin/obend check|run|prove` on a scratch
module in the session scratchpad; `grep`/`wc`.

Files read in full or by theorem statement: `lean/Obend/Analysis/{RealAnalysis,TaylorModel,Flowpipe,
Hybrid,Diff,Groebner,SosLyapunov,Equitable,QuantumWalk,EqSatHypergraph}.lean`,
`lean/Obend/Judge/RealAnalysis.lean`, `lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Hardware/{Magnetics,
FluidThermal,PowerElectronics,Thermal,Physics,Photonics,QuantumMatter,Analog,RF,DSP,Accelerators,
FabuBlox,TcadBridge,DigitalTwin}.lean`, `lean/Obend/Apps/{FocHil,SdrFt8,QuantumPhotonicMatter}.lean`,
`apps/foc-hil/**`, `apps/sdr-ft8/verilator/*`, `apps/quantum-photonic-matter/verilator/*_tb.cpp`,
`stdlib/physical/*.obend`, `PHYSICAL.md` (30,403 lines by `wc -l` over the list in the brief).

---

## 0. Verdict

**READ/INFERRED.** The arithmetic core is now genuinely verified and the council's "zero theorems in
`RealAnalysis.lean`" finding is obsolete in the working tree: `Interval.add_mem/sub_mem/mul_mem/sqr_mem`,
`evalInterval_sound`, three `#tooth` probes (`RealAnalysis.lean:184-307,402-464,471-499`), the Taylor-model
algebra (`TaylorModel.add_models/sub_models/scale_models/mul_models`, `evalTaylorModelRange_encloses`,
`TaylorModel.lean:451-713`), forward-mode interval AD (`Diff.lean:313`), the SOS/Positivstellensatz
family (`Judge/RealAnalysis.lean:943`, `SosLyapunov.lean:413,501,672`) and the interval judge
(`Judge/RealAnalysis.lean:83-119`) are universally quantified over `ℚ` and their proofs are structural.
A numerical analyst would sign those pages.

Everything that *names a device* sits on top of that core without touching it. Physical constants enter
as integer literals inside `def golden…` records and `decide +kernel` theorems; no theorem has a device
parameter as a free variable whose *value* matters, and in the two places a model enters as a hypothesis
(`AnalyticModel`, `TaylorModel.lean:935`; `perturbative_disorder_leakage_bound`, `QuantumMatter.lean:1786`)
the only instance is a polynomial or the hypothesis is the conclusion's own recurrence. The FOC
"closed loop" is open in Lean (the sensor is never updated) and plant-free in the HIL (no inverter, no
mechanics, thermal state moves 0.4 K in the whole run). The automatic certificate synthesizer certifies a
claim over a domain it chose, not the domain the claim states. Three of the four golden "multiphysics"
numbers are unit mismatches a motor-drive engineer would catch in the first minute.

The referee's one-line summary: *correct interval arithmetic over the rationals, wearing the names of
machines it has never been connected to.*

---

## 1. Where does any physical constant or device parameter enter a theorem?

I asked this first of every module. The table is exhaustive for the files in the brief.

| Module | How a parameter enters | Is it a hypothesis a proof depends on? |
|---|---|---|
| `TaylorModel.lean` | Lagrange constants `1/40, 1/720, 1/120, 32/5, 5/8` typed into `lagrangeRem*` (`:200-221`); validity domains `[-1,1]`, `[-1/2,1/2]` (`:717-734`) | Only via `AnalyticModel` (`:935-970`), whose single instance (`:976`) defines `expFn := expPartialSum 8`, `sinFn := sinDegree7Odd`, etc. **READ**: `grep -rn AnalyticModel lean/Obend --include='*.lean' \| grep -v TaylorModel.lean` is empty. No consumer. |
| `Flowpipe.lean` | `OdeSystem.remainderPad : Interval := ofPoint 0` (`:44`); concrete pads `[-1/10,1/10]` (`:308`), `[0,1]` (`:315`) | Input, never derived. `picard_step_encloses_trajectory` (`:620`) takes `r_pad ∈ sys.remainderPad` as a hypothesis. |
| `Hybrid.lean` | Mode ODEs `Ṫ = 4`, `Ṫ = -2`, `Ṫ = 20 - T`, guards, resets (`:184-226`) | Literals inside `decide +kernel` (`:253-268`). |
| `QuantumWalk.lean` | `remSmall = ±1/100` (`:1104`), unitary envelope `[-2,2]` (`:1109-1116`), `t = 157/100` | Literals; the envelope is wider than any amplitude can be. |
| `Magnetics.lean` | `goldenLiquidIpmMotor` (`ψ=180 mWb, Ld=150 µH, Lq=380 µH, p=4`, `:306-310`), triangle `(0,0),(2000,0),(0,1500)`, `ν=800` (`:313-321`), `kh=2, ke=1, f=400, B=16` (`:339`) | Literals inside `golden_femm_liquid_motor_magnetics_verified` (`:327-341`). The universal theorems (`:90-181,204-257,356-366,386-425,487-532`) are over all `Int`; no value matters. |
| `FluidThermal.lean` | `R = 2, 5, 12, 18, 2 mK/W`, `P = 8000 W`, `T_in = 50 °C` (`:323-324`) | Literals. The "224 °C" of `PHYSICAL.md:212` is `8000·(12+18-2)` = `224000 m°C` (`:290-297` identity). |
| `PowerElectronics.lean` | `goldenMs350Inverter` (`800 V, 15 nH, 8 A/ns, 1200 V, 500/180/40/100 ns`, `:273-289`); `ms350Fcml350kWSolarInverter` (`:445-461`); `goldenCoupledDriveTrainSpec` (`:647-676`) | Literals inside `golden_*_verified`. |
| `Thermal.lean` | none concrete in the electro-thermal section (`:395-577`) | Universal over `Int`, see §3 S5 for what it misses. |
| `DigitalTwin.lean` | `goldenMs350IpmPlantSpec` (`:322-351`), `goldenTwinState0` (`:359-370`) | Literals inside `golden_ms350_ipm_digital_twin_trajectory_verified` (`:386-406`). `slopeBetaCu := 0`, `alphaThermalUmPerK := 0` (`:332,338`): the two coupling coefficients are switched off. |
| `Photonics.lean` | `g = 157, 56, 60 mrad/µm`, `L = 5, 14, 11 µm`, gaps `200/225 nm` (`:857-879`) | Literals; no mode solver, no index, no wavelength anywhere in the CMT section (`:690-995`). |
| `QuantumMatter.lean` | `hypercubeQ3Quotient` (3:4:3), coupler table `[375000,500000,375000]` ppm (`:292-310`) | The one universal theorem (`:325`) says the synthesizer's output satisfies the synthesizer's own ratio check. |
| `apps/foc-hil/verilator/rk4_pmsm_plant.hpp` | `Ld=150 µH, Lq=380 µH, Rs=12 mΩ, ψ=0.18 Wb, p=4, Rth=0.045 K/W, Cth=120 J/K, C=45 µF` (`:27-36`) | C++ constants; no Lean theorem mentions this file or these values (see §3 S2). |

**INFERRED.** There is no theorem in the brief's scope whose statement is false for a different motor,
inverter, coupler or coolant. That is the operational meaning of "the physics is not in the proofs".

---

## 2. What is real, so it is not thrown out with the rest (READ)

- `Interval.mul_mem` (`RealAnalysis.lean:255`) is the four-corner product proved by case split on sign;
  `sqr_mem` (`:276`) handles the zero-straddling case. `evalInterval_sound` (`:402`) is the fundamental
  theorem of interval arithmetic for `RealExpr`. Division is absent (no `.div` constructor, `:314-321`),
  so no interval ever contains zero in a denominator; fine, and limiting.
- `TaylorModel.mul_models` (`TaylorModel.lean:662-713`) does the truncation and the three cross terms
  correctly; `evalPolyTermsInterval_mem` (`:567`) is a clean Horner-vs-interval lemma.
- `evalDualInterval_sound` (`Diff.lean:313`) and `meanValueEnclosure_sound` (`:407`) are the right
  statements for a mean-value form. `symbolicDeriv_agrees_with_dual` (`:202`) and the reverse-mode
  agreement theorems are universal.
- `sosCheck_sound` (`Judge/RealAnalysis.lean:943`): Putinar-form certificate with diagonal Gram, checked
  by exact polynomial identity (`Poly.sub … .isZero`) and evaluated semantics `Poly.eval`. Sound.
- `checkSosLyapunov_sound` (`SosLyapunov.lean:413`): `V(0)=0`, `V ≥ ε‖x‖²`, `L_f V ≤ -γV` on a
  semialgebraic domain, with `lieDerivativePoly` symbolic and tied to the AD (`:270`). `checkSosCbf_sound`
  (`:501`) gives strict separation from the unsafe set plus Nagumo. `checkDaeManifold_sound` (`:672`)
  gives tangency by ideal membership and a symbolic index-1 Jacobian. These are the best pages in
  `Analysis/` and the only ones a control theorist would cite.
- `picard_step_encloses_trajectory` (`Flowpipe.lean:620-684`): the universal half is correct interval
  arithmetic for a second-order Taylor–Lie step; `verifyPicardAPriori_encloses` (`:546`) is the right
  inclusion check. What is missing is in §3 S4.
- `foc_drive_top.sv` lints clean: `verilator --lint-only -Wall foc_drive_top.sv` (Verilator 5.050)
  prints no warnings. The 64-bit sign extension, anti-windup clamp and write-once latch are competent RTL.
- `apps/sdr-ft8/verilator/iq_synthesizer.hpp` is a real signal-level test: 79-symbol continuous-phase
  8-FSK with Costas `{3,1,4,0,6,5,2}` at symbols 0/36/72 (`:5-9,36-49`) and a +40 dB opposite-sideband
  jammer; the testbench measures IRR and symbol recovery (`sdr_ft8_tb.cpp:60-120`). It is the one place in
  scope where the thing under test is exercised by a signal rather than by `decide`.

---

## 3. Suspicions, evidence, verdicts (ranked by embarrassment in front of my kind)

### S1. The automatic certificate synthesizer proves a claim over a domain it picked, not the one stated

*What made me suspicious.* `apps/foc-hil/FocDriveTop.obend:42` reads
`claim stator_temp_interval_cbf(lossWatt: Nat) by judge("interval@1"): 45n + lossWatt * 4n <= 180n`.
That is false at `lossWatt = 34`. Yet `foc_hil_all_accepted_and_claims_hold` (`FocHil.lean:1104`) says it holds.

*Evidence.* **READ** `AutoCert.lean:1952-1972`, `extractIntervalEnvFromHyps envVars defaultIv hyps`:
a variable with no `given` bound gets `(v, defaultIv)`; `extractIntervalObjFromSyntax` (`:1985-2028`)
calls it with `⟨0, 1⟩`. So the kernel-checked query for the FOC claim is `45 + 4x ≤ 180` on `x ∈ [0,1]`.
`extractTaylorModelQueryFromSyntax` (`:2056-2091`) does the same with `[-1/10, 1/10]`.
**READ** `FocHil.lean:978-1006`: the FOC app does not even use that path. Its private `synthExternalJudge`
tries `candDoms := [250, 30, 15, 8, 7, 1]` and takes the *first* upper bound for which `intervalCheck` passes
(`:985-991`); for `taylor-model@1` it ignores the claim body entirely and substitutes the fixed query
`cos+sin on [-1/10,1/10] ⊆ [4/5, 6/5]` (`:996-1001`); for `sos-lyapunov-cbf@1` it substitutes
`goldenSosProblem` (`:1002-1005`). The `taylor-model@1` claim it "certifies" is
`claim cordic_trig_taylor_enclosure(thetaMrad: Nat) by judge("taylor-model@1"): thetaMrad <= 1000n`
(`ClarkePark.obend:33`), which mentions no trigonometry at all.
**READ** `obligationMeaningWithJudges focAutoCertFormats obj just` (`FocHil.lean:1104-1120`) is the judge's
meaning of the *substituted* object; the theorem's docstring calls these "4 compile-time AutoCert claims".
**READ** the general path is the same machine: `Elab/Workbook.lean:511-519` falls through to
`synthesizeClaimExternalJudge` when derivation fails, which calls the `[0,1]` extractor.

*Reproduction.* I wrote `/private/tmp/claude-501/-Users-ember-dev-obend/a43ef565-cc2f-412d-8808-6f075bdeea89/scratchpad/autocert/BoxDefault.obend`
with the same claim shape; `obend run BoxDefault.obend heatAt34` returns `181` (the claim is false at 34).
`obend check --obligations`/`obend prove --ground 1,34` answered `no-object` for a one-layer
`fix(compose(ProbeBase), seed)` knot, so I could not drive the CLI path to the certificate; the
`[0,1]` default is established from the code, not from a run. The CLI's own ground checker would have
refuted this claim at 34 had it reached the object (`Main.lean:570-590`), which is the right instinct in
the wrong tool.

*Verdict.* **Confirmed.** `synthesizeClaimExternalJudge_sound` (`AutoCert.lean:2369`) is true and
irrelevant: it proves the synthesized justification passes the check of the query the synthesizer
built. Nothing relates that query to the claim's own quantifier. This is the certificate boundary the
council warned about (§1.6 of `FABLE-COUNCIL-20261101.md`), now at the `.obend` surface.

### S2. The FOC controller and its plant are related by nothing but a 50 ms run, and the Lean "closed loop" is open

*What made me suspicious.* The brief's own question. A drive engineer wants to see `Ld`, `Rs`, `ω_e` and
the sample time in the stability theorem, and a PWM inverter between controller and motor.

*Evidence, Lean side.* **READ** `DigitalTwin.lean:189-209` `stepSampledDataDigitalTwin`: the measured
current is `runSarAdcN 4 0 st.iPhaseSenseMv 100 * 25` and the next state carries
`iPhaseSenseMv := st.iPhaseSenseMv` (`:202`). The sensor never sees `iqAmp`. With
`iPhaseSenseMv = 950 mV` the code is `9`, the "measurement" is a constant `225 A`, the error is a constant
`25 A`, and `iq` ramps `230 → 242 → 254` (`:392-393`) and would ramp forever. The golden theorem
(`:386-406`) certifies the ramp. `slopeBetaCu := 0` and `alphaThermalUmPerK := 0` (`:332,338`) zero the
electro-thermal and thermo-mechanical couplings, so `tWinding` and `hotAirGap` are constants in the
"coupled" trajectory (`:397-400`). `pCuBaseW := 7638` (`:331`) is chosen so that `7638 + 362 = 8000` lands
`T` exactly on `122000` (`FluidThermal.lean:324`). A 4-bit ADC at `25 A/code` (`:342-344`) is not a current
loop sensor. **READ** `sampled_data_current_loop_iss_contraction` (`:233-264`) is about
`x⁺ = x(1000-κ) + κ(r - δ)`: no inductance, no resistance, no back-EMF coupling, no integrator, no
saturation, no sample time; it is "a scalar affine map with gain `1-κ` contracts", plus the SAR bound.
`foc_hil_closed_loop_iss_and_thermal_safe` (`FocHil.lean:1273`) is that theorem re-exported.

*Evidence, HIL side.* **READ** `rk4_pmsm_plant.hpp:49-89`: the dq electrical equations are right
(`:66-68`), but `omega_e_rads` is never integrated (no `J`, no load torque; `electromagnetic_torque_nm`
`:138` is never called by `foc_hil_tb.cpp`), so there is no mechanical loop. The inverter is a wire: the
plant receives `vd_cmd_mv, vq_cmd_mv` as average voltages (`foc_hil_tb.cpp:174-178`); the RTL's
`fcml_duty_permille` output (`foc_drive_top.sv:178-185`) is connected to nothing. No PWM, no dead time,
no sensor delay, offset, noise or quantization (`llround(amp*1000)`, `tb:94-95`). The "6-level FCML
flying-capacitor" is one scalar with dynamics `-5·u - 800·cmd + ripple` (`plant:77-80`): a made-up linear
response to the controller's own command, where the command is `0.8 × last error` (`sv:162,176`), and the
test asserts the resulting decay (`tb:213,226`). Thermal: at `id=-100, iq=250` the copper loss is
`1.5·72500·0.012·1.157 ≈ 1510 W`, cooling `(65-45)/0.045 = 444 W`, so `dT/dt ≈ 8.9 K/s` and in 50 ms the
winding moves **0.44 K** (`plant:82-87,27,33-35`); the 155 °C trip is *assigned* (`tb:120-124`). The
over-temperature test tests a comparator and a latch, which is fine, and should say so. RK4 at 100 ns on
a system whose fastest time constant is `Ld/Rs = 12.5 ms` is 500× oversampled and, with constant `ω` and
ZOH voltages, the plant between ticks is LTI with a closed form; RK4 validates nothing.

*Three controllers.* **READ** integral gains: `PiCurrentLoop.obend:25,45` `50/65`; Lean
`focHilSequentialRtlModule` `65` for both axes (`FocHil.lean:1447,1457`); hand-written SV `20/25`
(`foc_drive_top.sv:79-80`). The LEC (`foc_drive_lec.smt2`) compares two hand-written SMT restatements
(`spec_*` `:26-55`, `rtl_*` `:58-105`) in which `vq_active = iq_err·kp + int_q` with no `/1000`, no
feed-forward, no anti-windup, no skid register, against an SV that has all four (`sv:88-129,159-164`).
Neither side is extracted from the `.sv` or from Lean; the single `assert` is a miter of the two copies.
Z3 `unsat` says the two hand copies agree.

*Verdict.* **Confirmed.** Nothing in Lean constrains the RK4 plant or the SV; nothing in the HIL exercises
an inverter or a mechanical load. "Closed-loop 20 kHz FOC + 6-level SiC FCML HIL" is a current-loop
regression test against an idealized dq plant, and the Lean twin's loop is physically open.

### S3. Units: the golden multiphysics numbers are dimensionally wrong

*What made me suspicious.* `minShaftTorqueScaled := 20000000` (`DigitalTwin.lean:349`).

*Evidence.* **READ** `evalIpmTorqueScaled m id iq = p·(ψ_mWb·iq + (Ld_µH - Lq_µH)·id·iq)`
(`Magnetics.lean:228-229`) adds a milliweber term to a microhenry term. Golden:
`4·(180·250 + (150-380)·(-100)·250) = 4·(45,000 + 5,750,000) = 23,180,000`, a reluctance:PM ratio of
128:1. In SI: `1.5·4·(0.18·250 + 230e-6·100·250) = 6·(45 + 5.75) ≈ 305 N·m`, ratio 7.8:1. The threshold
was chosen to pass the scaled number. `ipm_reluctance_torque_boost` (`:236`) is fine symbolically; every
golden torque is meaningless. **READ** `evalSteinmetzCoreLossMw 2 1 400 16 = 2·400·16² + 1·400²·16² =
41,164,800` "mW" (`:339`): 41 kW of core loss at `B_pk = 16 mT`, against a `50,000,000` budget, while the
saturation check in the same call uses `1650 ≤ 1850` mT. **READ** `evalSicInverterTotalLoss`
(`PowerElectronics.lean:497-499`) sums `3·I²·R_mΩ` (mW) with `k·f_kHz·V·I`; golden `600,000 + 3,200,000 ≤
4,000,000` (`:658-662`). **READ** `evalFcmlCellBlockingVoltageV 1500 6 = 250` with integer division
(`:308-309`); `ms350Fcml350kWSolarInverter.vDcBusV := 250` then checks `250 + 50 ≤ 650` (`:447-450`) and
the docstring says "233 A (350 kW)" while the spec has `mpptI := 300` (`:443,457`). **READ** the FEM
load vector: `evalElementResidual` subtracts `J·2Δ` from each node (`Magnetics.lean:630-631`); the
consistent load for a linear triangle is `J·Δ/3` per node, and the stiffness part omits `1/(4Δ)`, so the
"discrete Ampère's law" `r0+r1+r2 = -3·J·2Δ = -6JΔ` (`:648-651`) should read `-JΔ`. On the golden triangle
(`2Δ = 3·10⁶ µm²`) the two terms are mis-weighted by `24Δ ≈ 3.6·10⁷`; it is invisible only because `J = 0`
in the golden case (`:321`).

*Verdict.* **Confirmed.** None of these break a proof, because the proofs are about `Int`; they break
every sentence in `PHYSICAL.md` §4 that quotes a number.

### S4. The validated-numerics stack: what a referee would strike

*(a) Transcendental functions are polynomials by definition.* **READ** `AnalyticModel CanonicalRat`
(`TaylorModel.lean:976-981`): `expFn := expPartialSum 8`, `sinFn := sinDegree7Odd`,
`cosFn := cosDegree6Even`, `ln1pFn := ln1pDegree6Alt`, `sqrt1pFn := sqrt1pDegree5Binom`. The
"Lagrange remainder" hypotheses (`:941-970`) are discharged for these polynomials with witnesses like
`c = -x/5040` (`:991`). I checked the typed constants against the real functions: `e/120 < 1/40`,
`|sin⁽⁶⁾|/720 ≤ 1/720`, `|cos⁽⁵⁾|/120 ≤ 1/120`, `32/5` for `(1+ξ)⁻⁵` on `[-1/2,1/2]`, and
`(15/16)·2^{3.5}/24 ≈ 0.44 < 5/8`. They are right. Nothing in the tree says so, nothing can without `ℝ`,
and nothing uses the class. The docstring "Verified Transcendental Enclosures" (`:15`) is an overclaim;
the class itself is the correct architecture (the function model enters as a hypothesis) and deserves a
Mathlib `Real.exp` instance.

*(b) The `taylor-model@1` judge has no semantics.* **READ** `taylorModelJudge.Meaning q tm :=
verifyTaylorModelCert q tm = true ∧ …` (`AutoCert.lean:791-794`) and the FOC copy (`FocHil.lean:370-374`):
the meaning *is* the checker. Compare `intervalJudge.Meaning := IntervalQuery.SemanticMeaning`
(`Judge/RealAnalysis.lean:75-78,110-112`), which quantifies over all rational points. The composition cases
`.exp a` etc. (`AutoCert.lean:734-758`) are plausibly sound by `evalTaylorModelRange_encloses`, and that is
exactly the theorem that is not stated.

*(c) The flowpipe proves the arithmetic half of a validated step and omits the analytic half.* **READ**
`picard_step_encloses_trajectory` (`Flowpipe.lean:620-640`): the "trajectory point" is *defined* as
`x₀ + h f(x₀) + (h²/2)(L_f f)(ξ) + r_pad` with `ξ` in the rough box (`IsPicardSegmentState`, `:569-579`).
That is the conclusion of Taylor's theorem with Lagrange remainder plus the Picard a-priori enclosure,
taken as a definition. Existence of the solution, that it lies in `X̃` on `[0,h]`, and that its value at
`h` has that form, are the content of a validated ODE step (Lohner 1987; Nedialkov–Jackson–Corliss 1999)
and are absent. `rho : String → ℚ` (`:49`), so the actual solution `20 + 10e^{-t}` of
`thermalCoolingOde` is never a `rho`; the theorem enclosing `260653/10000` (`:647,659`) encloses a
rational that someone looked up. The N-D step (`stepPicardValidated`, `:162-175`) is Moore's naive
interval Taylor method of order 2 (no mean-value/QR/Lohner coordinate change): it blows up exponentially
on rotations, which is why `coupledOscillatorOde` is run for one step (`:661-666`). The "elimination of the
wrapping effect" (`taylorModel_picard_sound`, `:361-384`) is on the scalar ODE `ẋ = -x`; a scalar has no
wrapping effect, that is the dependency problem.

*(d) Names.* `schrodingerEigenmodeOde` is called "symplectic" (`QuantumWalk.lean:1003,1017`); the
integrator is the non-symplectic Taylor step above. Its "unitary envelope" is `[-2,2]` on each quadrature
(`:1109-1116`) for three steps of `0.1`; any method passes, and it says nothing about norm preservation.
`lindbladDephasingOde` is `ċ = -γc` (`:1040-1045`). The degree-4 "matrix Taylor PST amplitude"
`9287743200` shipped to the RTL testbench (`quantum_photonic_tb.cpp:21`, `QuantumPhotonicMatter.lean:647`)
is, after dividing by `4!·100⁴ = 2.4·10⁹`, an amplitude of **3.87** at `t = 1.57` with
`matrixTaylorRemainderBound = (3·157)⁵/(120·100⁵) ≈ 19.3` (`:1574-1580`). The "validated probability
tube" that encloses 1 (`:1656-1662`) is `sin⁶(t)` from the hypercube closed form via half-angle, not from
the propagator; the propagator is only validated at `t = 1/10` (`:1713-1716`).

*(e) Taylor models cannot be composed.* There is no `tmCompose`, no multivariate `TaylorModel`, no
division, no integration operator on a `TaylorModel` (the Picard operator `picardLinearStep` `:328` is for
`ẋ = λx + b` only). `.exp a` for non-variable `a` falls back to a range-wrapped constant model
(`AutoCert.lean:672-679,734-739`), i.e. to interval arithmetic.

*Verdict.* The core is sound and the library is a univariate polynomial-with-remainder algebra over `ℚ`
plus a first-order interval ODE stepper. Every word beyond that in the docstrings is to be struck.

### S5. The electro-thermal "contraction" is one-sided and the fixed-point iteration is an accumulator

**READ** `electroThermal_step_diff_identity` (`Thermal.lean:450-458`):
`step(T₁) - step(T₂) = (1 - dt·(G - β))(T₁ - T₂)`. The dichotomy theorem (`:475`) and the
"steady state unique and contraction" theorem (`:528`) conclude `step(T₁) - step(T₂) < T₁ - T₂` when
`G > β`. That inequality also holds when `dt·(G - β) = 10`, where the explicit-Euler map oscillates and
diverges (`|1 - 10| = 9`). Contraction of the discrete map requires `0 < dt·(G-β) < 2`; `dt` appears in
no hypothesis but `0 < dt`. **READ** `stepBhSecantReluctivity ν₀ k νcur B² = νcur + (ν₀ + k B²)`
(`Magnetics.lean:890-891`), described as a "damped Picard / chord-secant fixed-point update": it has no
fixed point for `ν₀ > 0` and the theorem (`:902`) proves it grows. **READ** `maxwell_stress_agrees_with_dq0_pm_torque`
(`:867-881`) sets `B_r := ψ + (Ld - Lq)·id`, `B_θ := iq`, weight `p` and multiplies; it renames the
dq formula. **READ** `evalMeshMagneticEnergyScaled` (`:160-164`) and `evalMeshTotalCoEnergy` (`:741`) sum
`ν·(Σ bᵢAᵢ)² + …` = `8Δ × (element energy)` per element, so a mesh sum weights each element by its own
area; non-negativity survives, "co-energy" does not.

*Verdict.* **Confirmed** for the three items; the positive statements (gauge invariance, element energy
`≥ 0`, Newton–Raphson tangent PSD) are correct and should be kept.

### S6. The photonic "matter compiler" relates a Hamiltonian to a splitter table by a ratio

**READ** `synthesizeKrawtchoukPhotonicCouplers` (`QuantumMatter.lean:292-310`) emits directional couplers
with `κ² = scale · Q_{j,j+1}Q_{j+1,j}`; `couplerRealizesQuotientRatio` (`:276-289`) checks the ratios; the
universal theorem (`:325`) is that the emitter satisfies its own check. The 3:4:3 chain is the right
Krawtchouk/Christandl PST chain for `Q₃`, but PST is a property of `e^{-iHt}` at `t = π/2` for a
*continuously* coupled array with coupling rates `∝ J_j`, not of a two-layer mesh of discrete power
splitters with `κ² ∝ J_j²` (`evalPlanarClements4Mesh`, `:133-145`). No theorem in the file relates the
mesh's transfer matrix to `e^{-iHt}`; the one physical theorem is power conservation of `2×2` couplers over
`ℤ[i]` (`:219`), which holds for any `(t, κ)`. **READ** `Photonics.lean:729-769`: the CMT enclosures evaluate
the degree-4/5 integer polynomials at `θ_min, θ_max` only and take min/max plus a remainder, which is an
enclosure only where `cos`/`sin` are monotone; it is unstated and unproved (true for the `≤ 0.8 rad`
examples). The coupling rate `g` is a literal; there is no waveguide index, wavelength or gap model. The
Majorana section is a correct `Cl₄` presentation of Ivanov braids and parity (`:848-1471`), and the
"Duhamel leakage bound" (`:1786`) assumes the Duhamel recurrence as a hypothesis on an arbitrary `Nat`
sequence.

*Verdict.* **Confirmed.** A photonics engineer reads the table at `:302-309` (gap 200/225 nm, `L` 14/11
µm, `t = 707/791`) as a design intent, not a design.

### S7. Checkers that are their own specification, and physical names on identities

**READ** `checkDriveTrainCoDesign`/`driveTrainCoDesign_sound` (`PowerElectronics.lean:582-643`),
`checkInverterSignoff_sound` (`:254`), `checkMagneticsSignoff_sound` (`Magnetics.lean:298`),
`checkLiquidThermalSignoff_sound` (`FluidThermal.lean:231`), `checkPowertrainTwinSafety`/
`sampled_data_closed_loop_powertrain_safety_invariant` (`DigitalTwin.lean:267-316`): each conclusion is
the unfolded hypothesis. `fcml_active_balancing_lyapunov_contraction` (`PowerElectronics.lean:426-433`)
assumes `0 ≤ c(2e - c)` and concludes `(e-c)² ≤ e²`, which is the same inequality.
`fcml_pspwm_natural_balance` (`:375`) says equal duties leave the error *unchanged*; in the literature
(McGrath–Holmes) natural balancing means the error *decays* through the load impedance at the switching
harmonics. `mppt_incremental_conductance_global_max` (`:113`) is the maximum-power-transfer theorem for a
*linear* source `I = I_sc - G_s V`; a PV cell is exponential, which is the whole reason the InC algorithm
exists. The FCML is "6-level" in the SV and `.obend` (`SicFcmlInverterLeg.obend:27`, `sv:2`) and "7-level,
`M = 6`" in `PowerElectronics.lean:435-437`. `statorCoupledLossHypergraph` (`EqSatHypergraph.lean:1555-1585`)
computes `T_peak = I²(w + a) + w·f - 2a + 25`; the e-graph theorem (`:1677`) is a correct equality-saturation
preservation result about an integer DAG that is not a thermal model. The five `stdlib/physical/*.obend`
objects are affine integer formulas (`gateDelayPs = fanout·8 + 20`, `transferredPowerMw = p·weight + dim`,
`peakWindingTemp = 50 + loss·R`): correct `.obend` demonstrations of `self`/`super`, carrying names.

*Verdict.* **Confirmed**, and consistent with the council's §2.4; I add only that in this domain the
pattern is uniform: not one checker in scope is checked against a model it did not define.

### S8. Teeth

**READ** per-file counts (`grep -c '^#tooth'`, `grep -c 'decide +kernel'`, `grep -cE '^theorem'`):

| file | `#tooth` | `decide +kernel` | `theorem` |
|---|---|---|---|
| `Analysis/RealAnalysis` | 3 | 0 | 22 |
| `Analysis/TaylorModel` | 1 | 4 | 37 |
| `Analysis/Flowpipe` | 0 | 3 | 13 |
| `Analysis/Hybrid` | 1 | 6 | 11 |
| `Analysis/QuantumWalk` | 7 | 8 | 29 |
| `Hardware/Photonics` | 4 | 4 | 28 |
| `Hardware/QuantumMatter` | 5 | 16 | 31 |
| `Hardware/{Magnetics,FluidThermal,PowerElectronics,Thermal,Physics,Analog,RF,DSP,Accelerators,FabuBlox,TcadBridge,DigitalTwin}` | 0 | 20 | 200 |
| `Apps/FocHil`, `Apps/SdrFt8` | 0, 0 | 18, 18 | 20, 20 |

`lean/Obend/Teeth/` has no file for any Analysis or physics module. Teeth landed where the proofs are
already universal (`RealAnalysis`) and nowhere a mutation would be informative.

---

## 4. Who refuses to sign what, and why

**The motor-drive engineer refuses** `Hardware/DigitalTwin.lean`, `Hardware/PowerElectronics.lean` §6–7,
`Hardware/Magnetics.lean` §3,8,11, `Apps/FocHil.lean` §6, and `apps/foc-hil/verilator/*` as a HIL:
the sensor is frozen (S2), the torque mixes mWb and µH (S3), the inverter is a wire, the mechanics are
absent, the thermal state does not move, three different `Ki` exist, and the LEC compares two hand
copies. He would sign `foc_drive_top.sv` as competent RTL and the Verilator lint, and nothing else.

**The photonics engineer refuses** `Hardware/QuantumMatter.lean` §2 and `Hardware/Photonics.lean` §8
as a compiler: splitter ratios are not Hamiltonian couplings (S6), coupling rates are literals, the CMT
enclosure's monotonicity assumption is unstated, and the "PST amplitude" in the RTL testbench is 3.87.
She would sign the `ℤ[i]` power-conservation lemmas and the `Cl₄` braid algebra as mathematics.

**The numerical analyst refuses** the words "validated", "verified transcendental", "symplectic", and
"eliminates the wrapping effect" in `TaylorModel.lean`, `Flowpipe.lean`, `QuantumWalk.lean` (S4), the
one-sided Euler contraction in `Thermal.lean:450-577` (S5), the `taylor-model@1` judge's tautological
meaning, and every `remainderPad` that is typed rather than derived. He would sign `RealAnalysis.lean`,
`Diff.lean`, the `TaylorModel` algebra (`:388-713`), `Judge/RealAnalysis.lean`, and `SosLyapunov.lean`
after the docstrings are rewritten to say "over `ℚ`, for the polynomial models defined herein".

**All three refuse** `Elab/AutoCert.lean:1952-2028` and `Apps/FocHil.lean:978-1006` (S1): a certificate
for a domain the prover chose is not a certificate for the claim.

---

## 5. What a validated-numerics referee would strike, in order

1. Every "encloses the trajectory" / "validated flowpipe": no existence theorem, no connection from the
   interval step to an ODE solution, points only in `ℚ` (S4c).
2. "Verified transcendental enclosures": the functions are the polynomials (S4a).
3. "Symplectic", "unitary envelope", "Lindblad", "PST amplitude" in `QuantumWalk.lean` §6,8 (S4d).
4. "Eliminates the interval dependency and wrapping effect" (`TaylorModel.lean:10`) for a scalar ODE (S4c).
5. `remainderPad` as an input to a "validated" integrator (`Flowpipe.lean:44`).
6. `taylorModelJudge.Meaning` equal to the checker (S4b).
7. Explicit-Euler "strict contraction" without a step-size condition (S5).
8. All "`decide +kernel`" theorems whose statement is a list of numbers (`flowpipe_step_encloses_euler`,
   `taylorModel_transcendental_enclosure_sound`, `ctqw_validated_flowpipe_and_taylor_unitarity`, every
   `golden_*`): keep them as tests, retitle them.

---

## 6. Three changes first

1. **Make the claim the query (S1).** In `AutoCert.lean:1952-1972` and `:2056-2091`, replace the default
   box with a refusal: a claim variable with no `given` bound is not synthesizable, and the refusal names
   the missing bound (the system's own "every refusal names what would pass"). Delete the `candDoms` search
   in `FocHil.lean:985-991` and the fixed TM/SOS substitutions (`:996-1005`); let the four FOC claims go
   red and fix the `.obend` text (`given lossWatt <= 30n`, and a trig claim that mentions trig). Give
   `taylorModelJudge` a `Meaning` of the `IntervalQuery.SemanticMeaning` shape via
   `evalTaylorModelRange_encloses`. **Cost:** one or two days; four theorems in `FocHil.lean` and the
   `#import_obend` refusal path change; `foc_hil_all_accepted_and_claims_hold` is rewritten. **PROPOSED.**

2. **Close one real loop, in one place, with the parameters as variables (S2, S3).** Replace
   `stepQuantizedCurrentLoop` with the exact ZOH discretization of `L di/dt = v - R i` at sample time
   `T_s` (a rational `a = e^{-RT_s/L}` enters as a hypothesis-bounded interval, not a literal), a PI
   controller with the gains from `PiCurrentLoop.obend`, and feedback from the state; prove
   `|e_{k+1}| ≤ ρ|e_k|` with `ρ < 1` as a function of `(R, L, T_s, K_p, K_i)` under stated bounds, and
   instantiate it at the LC Drives numbers. Make `iPhaseSenseMv` a function of `iqAmp`. Fix
   `evalIpmTorqueScaled` to one unit (µWb and µH, or SI rationals) and recompute the golden thresholds.
   Make one `Ki` (pick `.obend`'s, regenerate the SV from `emitModuleSV focHilSequentialRtlModule`
   instead of hand-writing it, and generate the SMT miter from the same module). **Cost:** a week for the
   theorem; a day for the units; the HIL testbench then needs an inverter model (even an ideal PWM with
   dead time) and a mechanical equation before "HIL" is honest, which is another week. **PROPOSED.**

3. **Derive one remainder and state one existence theorem (S4).** For `thermalCoolingOde` and the 2-D
   oscillator, replace `remainderPad` by the computed `derivePicardLieRemainder` only (set the pad to
   `[0,0]` everywhere and delete the field), and add, over Mathlib `ℝ` in a separate module that imports
   `Mathlib.Analysis.ODE.PicardLindelof` and `Mathlib.Analysis.Calculus.Taylor`, the theorem: if
   `verifyPicardAPriori sys x0 X̃ h = true` and `f` is the real polynomial denoted by `sys.fields`, then
   the unique solution with `x(0) ∈ x0` exists on `[0,h]`, stays in `X̃`, and `x(h) ∈ stepPicardValidated …`.
   Give `AnalyticModel` its `Real.exp/sin/cos` instance from `Real.exp_bound` and
   `taylor_mean_remainder_lagrange`. **Cost:** this is the real work of the "validated numerics pillar";
   two to three weeks for someone who knows Mathlib's ODE library, and it is the only change on this list
   that would make the word "validated" true. **PROPOSED.**

---

## 7. The one question for Ember

You said the test is "proving that the multiphysics is a valid approximation starting from some absurdly
low level physical model". Which single device do you want that done for first, end to end — the LC Drives
current loop (ODE → ZOH → PI → RTL, with `R, L, T_s` as variables), or the `Q₃` Krawtchouk array
(Hamiltonian → coupled-mode PDE → coupler lengths)? Both are a month of honest work; doing both at once is
how the current tree happened.
