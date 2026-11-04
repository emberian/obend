# CAD/CAM, OpenUSD and the five-axis post: what an engineer who has written a post would sus at (2026-11-04)

Remit: `lean/Obend/Hardware/{GeometryCAM,OpenUSD,Kinematics,PCB}.lean`, `lean/Obend/Apps/FidgetCam.lean`,
`apps/fidget-cam/*.obend`, `stdlib/usd/`, the CAD sections of `PHYSICAL.md`. No reviewer on the
11-03 panel covered this tier; Gemini's chair 4 (`A C4-1..C4-4`, `C1-11`) did, and the panel diff
(`review/PANEL-DIFF-20261104.md` §2 item 7) confirmed its findings at HEAD. This lane reviewed and
fixed in place. Tags: **READ** (opened, `path:line`), **INFERRED**, **PROPOSED**. Line numbers are
after the commits listed in "What landed" unless marked HEAD.

Verdict: the tier had the right primitives (an integer F-Rep with a proved interval enclosure, a
proved Lipschitz bound, a proved SSA-tape pruner) and none of them reached the part. The fidget
theorem certified a tool the program never used, at a place the program never went; the G-code was
written by a C++ testbench; the wall was probed at one point; two F-Rep forms and two USD models
stood side by side. After this lane the part is built once from the `.obend` values, certified
against the program the post emits, and the post is rotary-safe for every input. The lattice-to-
continuum step is argued, not proved.

## 1. Suspicion list, written before digging

1. The no-gouge theorem checks the tool against the part, at the program's tool positions.
2. The program is posted from the certified path, with TCPM, and never re-orients in the cut.
3. Wall thickness is a property of the cavity, not of a point.
4. One F-Rep, one USD model; the RTL computes the same solid the theorems are about.
5. The `.obend` files carry geometry, not arithmetic with geometric names.
6. Microstrip `Z₀` has a square root and a logarithm in it.
7. Affine arithmetic's radius is a radius.
8. The kinematics that the docs call 21-parameter and Ruckig are what those names mean.

## 2. Findings, ranked by embarrassment

### 2.1 The gouge theorem certified nothing about the part (suspicion 1): confirmed, fixed

- **READ** (HEAD) `Apps/FidgetCam.lean:340-390`: `fidgetCam_dual_interval_lipschitz_and_no_gouge_sound`
  calls `synthesizeCertifiedSweptVolume impellerFinishBox impellerBallEndmillTool [(0, 0, 0)] 1`: one
  waypoint at the origin, checked against the box `[6,11]×[6,11]×[2,10]`, which a radius-2 ball at the
  origin cannot reach. `fStock` is a free variable that the conclusion never constrains
  (`GeometryCAM.lean:1857`, `continuous_swept_volume_no_gouge_sound`: the conclusion follows from the
  tool's positivity on `B` alone).
- **READ** (HEAD) `apps/fidget-cam/verilator/fidget_voxel_tb.cpp:367-372`: the posted path is at
  `R = 29`, `Z = 18..22` around a part of radius 12 and height ±6; it cuts air.
- **INFERRED**: the theorem's tool, positions and box are three independent choices; none is the
  program. A machinist would call this "the simulation of a different job".
- Fix (**READ**, now): `GeometryCAM.lean:2989-3045` `kdAll`/`kdAll_sound` and `checkDisjoint_sound`
  (no lattice point in both part and cutter over a box, k-d split until intervals separate);
  `:3147` `frepBallEndMill` (ball and shank on an integer axis, polynomial, no square roots);
  `:3181` `checkPathNoGouge_sound`. `Apps/FidgetCam.lean:437` `fidget_toolpath_no_gouge`: for every
  pass the post emits and every lattice point of every segment including plunges and retracts
  (`certPath`), the cutter grown by 100 µm contains no point of the part, anywhere
  (`FidgetParams.part_in_box`, `:293`). Discharged by `native_decide` (4,739 cutter locations,
  `#assert_compiled`).
- What is still argued, not proved: the continuum. The theorem is over lattice points of space and
  lattice tool positions; `fidget_certPath_unit_steps` (`:454`) gives unit steps, and with the
  one-unit growth every point of a segment the control interpolates lies in the checked union
  (docstring at `GeometryCAM.lean:3168-3180`). Mechanising it needs the reals.

### 2.2 The G-code would crash a real machine (suspicion 2): confirmed, fixed on the Lean side

- **READ** (HEAD) `fidget_voxel_tb.cpp:360-400`: `G49` in the modal line and no `G43.4`/RTCP, so X/Y/Z
  are pivot coordinates on a trunnion and the tip goes wherever the rotaries put it; `C` steps 345 → 0
  between passes under `G01` at cutting depth (the table unwinds with the tool in the part); no
  retract between passes; the header comment claims `L_box=72` and `stepPad=144`, which nothing
  computes.
- Fix (**READ**): `Kinematics.lean:706-960` §8. Typed moves; `passMoves` is rapid to above the first
  point (re-orienting there), plunge, cut, rapid up; `postNgc` prints the Fanuc 30i dialect with
  `G43.4 H1` and cancels it only after the final rapid. `postMoves_rotarySafe` (`:868`) holds for
  every list of operations: a feed never changes the tool axis, any move that does is a rapid on or
  above the clearance plane; a `#tooth` (`:889`) with a post that re-orients on the plunge confirms
  the proof needs it. `Apps/FidgetCam.lean:465` `impeller5AxisNgc` is the fidget program (1,314 lines:
  four Z-level contours and four 3+2 top-edge passes at A = 36.870°, C = 0/90/180/−90).
- **INFERRED**: open for a real controller: arcs (`G02/G03`) instead of polylines, the machine's travel
  and rotary limits, the C winding choice (it takes `atan2`, so 180 → −90 is a 270° table move, at the
  clearance plane), and the per-machine sign conventions (`axisAngles`, `:919`) a real post
  configures. The feed is `G94` mm/min, which is what TCPM controls want; `G93` is for non-TCPM
  five-axis.
- Not done (FPGA lane's files): the testbench still writes its own `.ngc` and re-implements the
  part's interval evaluation in C++ (`fidget_voxel_tb.cpp:60-68`, a third copy of the geometry).

### 2.3 Wall thickness from one point (suspicion 3): confirmed, fixed

- **READ** (HEAD) `OpenUSD.lean:1432-1730`: three functions (`computeShellWallThicknessUm` with a
  caller's Lipschitz bound, an affine variant, `computeCertifiedShellWallThicknessUm`) each bound the
  distance from one chosen probe point to the outer surface; the fidget used two planes `x = 800`,
  `x = 3400` and probed `(800, 0, 0)`.
- Fix (**READ**): `GeometryCAM.lean:3067` `checkWall_sound`: every lattice point within `(tx, ty, tz)`
  of any cavity point in the box is inside the outer solid (leaf test: the box grown by the wall is
  inside). `Apps/FidgetCam.lean:321` `fidget_bore_wall_sound` certifies 2.0 mm in X and Y around the
  whole cooling bore. The three probe-point functions are deleted (`OpenUSD.lean:1458` says where
  the wall went). The XY wall is the honest one for a through-bore; an L∞ wall in Z would fail at the
  bore's mouths.

### 2.4 Two F-Reps, two USD models, an RTL beside them (suspicion 4): confirmed, fixed

- **READ** (HEAD): the tree `FRepExpr` (`GeometryCAM.lean:61`) carried the enclosure and gradient
  theorems; the tape `SsaTapeOp` carried pruning and the RTL; `FidgetCam.lean:200-215` (HEAD) wrote the
  impeller tape by hand beside the tree. The council's (§2.3, P5) "tree has no unary neg" is moot: the
  tape has `neg`, and the tree expresses it as `csgDiff`/`sub`.
- Fix (**READ**): `GeometryCAM.lean:2702` `FRepExpr.toTapeFrom`, `:2907` `toTape_eval`
  (the tape computes the tree at every point); the fidget's tape and its three pruned tapes are
  compiled from the solid (`FidgetCam.lean:312`, `:552` `compactFor_sound`), and the RTL voxel
  evaluator compiles that tape (`:561`).
- **READ**: the "two OpenUSD models" of 11-01 are one at HEAD: a later lane had already deleted
  `GeometryCAM.lean:849-1003` except the `UsdArcKind` enum, which now lives in `OpenUSD.lean:922`.
  `composePrimToTerm` (`OpenUSD.lean:1019`) does fold `Term.fix (composeTerm …)` over the
  strength-sorted specs.
- **INFERRED** (USD in anger): what is modelled is a strength-ordered opinion stack for value
  resolution, which is the right consequence of LIVERPS for one attribute; Pcp's graph (a reference
  arc pointing at another layer stack and its opinions, inherits at a class path, variant selection,
  list-editing ops) is not. `UsdPhysicalState`'s "timeSamples" (`:692`) is a lifecycle track, not
  per-attribute time samples. `XformOp3D` (`:1295`) has quarter turns only. `stdlib/usd/ScenePrim.obend`'s
  `worldTransformMm(parent) = parent + offset` is a 1D translation. All said in `PHYSICAL.md` §2.

### 2.5 The `.obend` files were arithmetic with geometric names (suspicion 5): confirmed, replaced

- **READ** (HEAD + S-6 dirty): `BaseImpellerBody.obend` `evalHubBladeFRep = x²+y²+z² + thickness` on
  `Nat` (nothing is ever inside); `ImpellerPartTop.obend` `crossModuleAssemblySummary` summed
  micrometres, milliwatts, G-code steps and voxel counts (6704).
- Fix: four parameter records with overrides; FidgetCam builds the solid from the composed values and
  decides the link (`FidgetCam.lean:129` `fidgetParams_eq_obend`). `fidgetCam_liverps_bore_radius`
  (`:486`) lowers the bore's two opinions through `composePrimToTerm` and gets the value the `.obend`
  composition reduced.

### 2.6 Microstrip `Z₀` was linear (suspicion 6): confirmed, fixed

- **READ** (HEAD) `PCB.lean:468-472`: `87000·(4H+W)/((εr+1410)(W+2H))`; for 80 µm on 500 µm PTFE it said
  48.7 Ω (`:486`); the closed form gives 171 Ω. The trace check trusted an "extracted" field.
- Fix (**READ**): `PCB.lean:172` `microstripZ0MilliOhm`, Hammerstad–Jensen with Wheeler/Bahl–Garg
  thickness correction in fixed point (`Nat.sqrt`, an atanh-series log); `checkSingleEndedZ0`
  (`:188`) also requires the closed form from the trace's own geometry. Golden RO4350B: 47.9 Ω in a
  50 ± 2.5 band (command: `example` at `PCB.lean:544`, kernel-decided).
- **INFERRED**, not done: `evalDiffImpedanceMilliOhm` (`:236`) is `2·Z_odd` with `Z_odd` a linear
  coupling discount, the same kind of formula.

### 2.7 Affine radius was the full width (suspicion 7): confirmed, fixed

- **READ** (HEAD) `OpenUSD.lean:245-248`: `err := |hi − mid| + |mid − lo|`. Now the larger of the two
  (`:248`); every crease `min`/`max` fell back on had been doubled.

### 2.8 Names bigger than the models (suspicion 8): confirmed, said

- **READ** `Kinematics.lean:275` `evalVolumetricError3D = δ + ε × L`: one carriage's six constant
  small-angle errors; the header called it the 21-parameter model (now corrected). `:242`
  `ruckig_symmetric_pulse_exact` is one jerk pulse, not Ruckig's time-optimal profile.
  `GeometryCAM.lean:2587` chatter is a given scalar inequality, not a lobe diagram (`PHYSICAL.md` §3.1).

## 3. What landed

| commit | what |
|---|---|
| `cf3efad` | `GeometryCAM`: `toTape`/`toTape_eval`, `kdAll`, `checkDisjoint_sound`, `checkWall_sound` (+ tooth), cutters, `checkPathNoGouge_sound`; `OpenUSD`: half-width `fromInterval`, `UsdArcKind` moved in, probe-point walls deleted; metasystem test §2.3 |
| `5a74100` | `Kinematics` §8: TCPM post, `postMoves_rotarySafe` (+ tooth), `postNgc`; header corrected |
| `0da8645` | `PCB`: Hammerstad–Jensen `Z₀`, the signoff gates on it |
| `6db42e8` | `apps/fidget-cam/*.obend` as parameters; `FidgetCam`: one solid, wall, certified path, post, RTL from the tape |
| `023cdc4` | `PHYSICAL.md` §2 and §3.1 |

Built in `bb2:~/lane-cad` (HEAD plus these files): the four Hardware modules, `Apps.FidgetCam`,
`obend-emit-sv`, and every module importing them except `Teeth/Hardware/SiliconTeeth`, which is red
at HEAD for an unrelated reason (`:594` tooths a theorem `UserspacePhysical` no longer has).

Needs another lane (FPGA): regenerate `apps/fidget-cam/verilator/fidget_impeller_voxel_cam.sv` with
`obend-emit-sv fidget` (the module changed: ports `in_step_dist`, `in_subdiv_level`,
`in_liverps_override_en` and the constant outputs are gone; lattice unit 100 µm); rewrite the
testbench to drive the new ports, drop its C++ copy of the geometry, and read the program from Lean
(a `fidget-ngc` target in `tools/emitsv` printing `Obend.Apps.FidgetCam.impeller5AxisNgc` to
`apps/fidget-cam/build/impeller_5axis.ngc`) instead of writing one. `fidget_cam_lec.smt2` compares
constants (`A C4-2`) and should be regenerated or retired. `Hardware/Judge.lean`'s
`extractNatField_token_boundary_and_decoders_verified` no longer matches
`tests/metasystem/OpenUsdAndSsaTapeTest.lean:359`.

## 4. The three next changes

1. **The RTL theorem** (PROPOSED, a day): `compileSsaTapeToRtlWires` agrees with `evalSsaTape` for
   inputs whose intermediate values fit in 64 bits, with the bound computed by interval evaluation
   of the tape over the part box. Then the voxel evaluator is the solid, not a fixture.
2. **Simultaneous five-axis** (PROPOSED, two to three days): orientation interpolated between cutter
   locations. Needs the cutter's swept volume under rotation; the honest first step is a grown cutter
   covering the axis cone between consecutive axes, checked like translation is now.
3. **Blades and a real stock** (PROPOSED, a day): radial blades as slabs, a billet as stock, and the
   in-process workpiece after each pass, so "cuts air" and "leaves stock" become measured quantities.

## 5. The question for Ember

The certificate is over a 100 µm lattice with the cutter grown by one unit, discharged by
`native_decide`; a finer lattice or the kernel would cost minutes per pass. Is compiled trust the
right home for the tool-path certificate, or do you want it re-checked by the kernel (or by a Rust
checker the FFI calls) before anything is cut on a real machine?
