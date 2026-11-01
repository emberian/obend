# Verified Hardware, Untrusted EDA Certificates & FabuBlox Silicon Processes for Objective Bend

2026-11-01. Orientation, literature synthesis, and full-scale architecture for `Obend.Hardware`
(Workstream 16). Claims are tagged **READ** (from a mechanized HDL / EDA verification paper or a
file in this tree), **INFERRED** (a mathematical/architectural consequence we defend), or
**PROPOSED** (a concrete design for `Obend.Hardware`).

---

## 0. The orientation in one paragraph

**INFERRED.** Thirty years of verified hardware and CAD research (Hanna's Veritas, Gordon's HOL,
BlueSpec/Kami, MIT's Kôika, Google's SilverOak/Cava, UW's Lakeroad, and Leiserson–Saxe retiming)
converge on a single architectural split that is *already* Objective Bend's core law
([`AMBITION.md`](file:///Users/ember/dev/obend/AMBITION.md) §"What we hold to": *"The kernel admits
by re-execution and checks certificates it never searched for"*):
1. **Language-to-RTL & Guarded Rule Compilation lives inside the kernel** (`Obend.Hardware.Types`,
   `Obend.Hardware.HDL`, `Obend.Hardware.Rules`, `Obend.Hardware.FSM`, `Obend.Hardware.Compiler`):
   records, tagged unions (`inject`/`case`), linear/affine SRAM capability tokens, multi-cycle
   fuel-bounded state machines (`fix`), and concurrent guarded rules are compiled with universal
   simulation theorems against `Obend.Core.Term` and `Obend.Leaf.Emit.Book`.
2. **NP-hard EDA & Cleanroom Synthesis/Optimization passes are untrusted external certificate
   producers** (`Obend.Hardware.Retiming`, `Obend.Hardware.TechMap`, `Obend.Hardware.PlaceRoute`,
   `Obend.Hardware.Bitstream`, `Obend.Hardware.FabuBlox`, `Obend.Hardware.DRC`): we never trust
   Vivado, Yosys, nextpnr, OpenROAD/OpenLane, or an AI process agent (`FabAgent`). Instead, every
   backend pass emits a compact **witness certificate** (a Leiserson–Saxe integer lag vector, a
   topological cut-equivalence witness, a physical BEL/switch-box routing tree, a bitstream frame
   image, or a FabuBlox cleanroom recipe + 2D GDS cutline cross-section trace) that a small, linear-
   or quadratic-time **verified checker in `Obend.Judge`** validates and records in an
   `Obend.Receipt` re-checkable via `obend verify` with zero producer state.

---

## 1. The properties the hardware & nanofabrication literature isolated

### 1.1 Bit-level representation of algebraic types, records, and brands (`HwType`)

* **READ.** Choi et al., *Kami: A Platform for High-Level Parametric Hardware Specification and its
  Modular Verification* (ICFP 2017); Bourgeat et al., *The Essence of Bluespec: A Core Language for
  Rule-Based Hardware Design* (PLDI 2020, Kôika). Hardware wires are flat `BitVec W`, while source
  programs manipulate structured rows (`Term.record`), nominal brands (`#kind`), and tagged sums
  (`Term.inject` / `Term.case`).
* **INFERRED.** A toy HDL that only models `BitVec 64` scalars cannot compile real Objective Bend
  objects whose methods pass records, return tagged sums (`Ok`/`Refused`), or dispatch on `#kind`.
* **PROPOSED (`Obend.Hardware.Types`, ~900 lines).**
  - Recursive hardware type algebra `HwType`:
    * `.bits (w : Nat)` — raw bitvector of width `w`,
    * `.struct (fields : List (String × HwType))` — packed record (fields concatenated in row order
      at static bit offsets `fieldOffset fields name`),
    * `.taggedUnion (tagBits : Nat) (arms : List (String × HwType))` — tagged sum `[tag : tagBits |
      payload : maxArmWidth arms]`, directly lowering `Term.inject` and `Term.case`,
    * `.array (len : Nat) (elem : HwType)` — fixed-size vector/bus.
  - Total bit-width function `HwType.bitWidth : HwType → Nat`, typed value denotation `HwVal :
    HwType → Type`, and bit-packing isomorphism:
    * `packHwVal : {ty : HwType} → HwVal ty → BitVec ty.bitWidth`
    * `unpackHwVal : (ty : HwType) → BitVec ty.bitWidth → HwVal ty`
  - **Mechanized Theorems**:
    1. `unpack_pack_id`: `∀ (ty : HwType) (v : HwVal ty), unpackHwVal ty (packHwVal v) = v`.
    2. `struct_slice_extract_sound`: hardware bit-slicing `extractLsb (offset + width - 1) offset`
       on a packed `.struct` bitvector equals `packHwVal` of the projected field (`getField`).
    3. `struct_slice_update_noninterference`: updating field `f₁` via bit-mask/insert preserves
       every other field `f₂ ≠ f₁` (`getField_setField_ne`).
    4. `taggedUnion_case_mux_sound`: hardware tag-comparison + payload slice extraction implements
       exact sum elimination (`Term.case`).

### 1.2 One-Rule-At-A-Time (ORAAT) Guarded Atomic Actions & Conflict-Free Scheduling (`Obend.Hardware.Rules`)

* **READ.** Bourgeat et al., *Kôika: A Core Language for Rule-Based Hardware Design* (PLDI 2020).
  Designing multi-unit hardware (e.g. an AXI4-Stream DMA ingress, a Merkle receipt climber, a
  capability-guarded register bank, and an eFPGA frame loader sharing state) with raw `always_ff`
  blocks causes subtle race conditions when multiple state machines fire in the same cycle. Kôika
  solves this by giving every rule a dynamic action log (`readPort0`, `writePort0`, `readPort1`,
  `writePort1`) and proving that a static conflict-free schedule refines atomic One-Rule-At-A-Time
  (ORAAT) semantics.
* **PROPOSED (`Obend.Hardware.Rules`, ~950 lines).**
  - `RegFileSpec`, `RuleAction` (`readReg`, `writeReg`, `guard`, `alu`, `letBind`, `ifElse`),
    and dynamic `ActionLog` tracking `reads0`, `writes0`, `reads1`, `writes1` per register.
  - Operational semantics:
    * `evalRuleAtomic : RegEnv → HwRule → Option RegEnv` (atomic single-rule step),
    * `evalScheduleORAAT : RegEnv → List HwRule → RegEnv` (sequential one-rule-at-a-time spec),
    * `evalScheduleSync : RegEnv → List HwRule → Option RegEnv` (simultaneous single-cycle hardware
      execution with conflict detection).
  - Static footprint analyzer `footprintOf : HwRule → RuleFootprint` (`mustNotWriteBeforeRead`,
    `disjointWriteSet`) and decidable static scheduler check `checkConflictFreeSchedule :
    List HwRule → Bool`.
  - **Mechanized Theorems**:
    1. `conflictFree_two_rules_commute`: if `disjointFootprint r₁ r₂ = true`, executing `r₁` and
       `r₂` in parallel in a single clock cycle equals executing `r₁` then `r₂` atomically
       (`evalScheduleORAAT`).
    2. `schedule_oraat_refinement`: for any list of rules `rs`, if `checkConflictFreeSchedule rs =
       true`, the synthesized single-cycle synchronous transition function is bit-identical to
       `evalScheduleORAAT` across all register states.

### 1.3 Multi-Cycle FSMs, Fuel-Bounded Recursion (`fix`), and Activity Handshakes (`Obend.Hardware.FSM`)

* **READ.** Interactive & recursive constructs in Objective Bend (`Term.fix`, `Term.ifZero`,
  `Term.perform`, `Term.done`) take multiple steps on the demand machine. In hardware, a tail-
  recursive loop or `perform` suspension compiles to a **Valid/Ready Finite State Machine (FSM)**
  with states `IDLE`, `COMPUTE`, `YIELD_WAIT` (asserting `plan_valid` and waiting for `resume_valid`
  from the host/kernel!), and `DONE`.
* **PROPOSED (`Obend.Hardware.FSM`, ~1,000 lines).**
  - `FsmPhase` (`.idle`, `.busy`, `.yielded`, `.done`), `FsmConfig` (loop state registers, fuel
    counter, continuation tag, step transition expression, termination condition, yield plan
    expression), and `FsmState`.
  - Cycle-accurate step function `stepFsm : FsmConfig → FsmState → FsmInputs → FsmState × FsmOutputs`
    with AXI-style `in_valid`/`in_ready`, `out_valid`/`out_ready`, and `yield_valid`/`resume_valid`.
  - Compiler `compileLoopToFsm : LoopSpec → FsmConfig` that lowers bounded iterative/tail-recursive
    computations and `perform` yields into a hardware FSM.
  - **Mechanized Theorems**:
    1. `fsm_no_overwrite_while_busy`: when `st.phase ≠ .idle`, `in_ready = false` and external
       inputs cannot corrupt in-flight loop registers (`loopRegs` invariant under input noise).
    2. `fsm_fuel_monotone_termination`: from any `.busy` state with `fuel = k` (and no unresumed
       yield), the FSM reaches `.done` or `.yielded` within at most `k + 1` clock cycles.
    3. `fsm_refines_tailrec`: for any `LoopSpec` and fuel `k`, running `stepFsm` for `k` cycles from
       `.idle` produces the exact mathematical fixed-point `evalTailRec k initAcc`.
    4. `fsm_yield_resume_sound`: when a computation executes `perform plan`, the FSM transitions to
       `.yielded`, holds all live registers stable across arbitrary host latency $L \ge 1$ cycles
       while `resume_valid = false`, and upon `resume_valid = true` resumes with the host's
       response in the empty environment (matching `Core/Machine.lean`'s `resume_keeps_heap_and_stack`).

### 1.4 Leiserson–Saxe Retiming & Untrusted Synthesis Certificates (`Obend.Hardware.Retiming`)

* **READ.** Leiserson & Saxe, *Retiming Synchronous Circuitry* (Algorithmica 1991); Nigam et al.,
  *Step-by-Step: Verified Pipelining of Hardware* (Filament / Calyx). Finding an optimal register
  placement that minimizes clock period $T_{\text{clk}}$ is solved by linear programming / min-cost
  network flow outside the kernel, producing an integer lag vector $r : V \to \mathbb{Z}$.
* **INFERRED.** We never need to verify the LP solver! The kernel only needs to check the
  **Leiserson–Saxe edge validity certificate**:
  1. For every edge $u \xrightarrow{w(e)} v$ with initial register weight $w(e) \in \mathbb{N}$,
     the retimed register weight $w_r(e) = w(e) + r(v) - r(u)$ satisfies $w_r(e) \ge 0$;
  2. For every combinational path $u \leadsto v$ with $w_r(p) = 0$, the cumulative path delay
     $D(p) \le T_{\text{clk}} - T_{\text{setup}} - T_{\text{skew}}$;
  3. Every primary input $i$ and primary output $o$ has uniform boundary lag ($r(i) = 0$,
     $r(o) = L$), shifting external I/O latency by exactly $L$ cycles.
* **PROPOSED (`Obend.Hardware.Retiming`, ~900 lines).**
  - Synchronous dataflow graph `SyncGraph` (vertices with combinational operator + gate delay,
    directed edges with register count $w(e) \in \mathbb{N}$), integer lag assignment
    `RetimingCert : Nat → Int`, and retimed graph transformer `applyRetiming : SyncGraph →
    RetimingCert → Option SyncGraph`.
  - Certificate checker `checkRetimingCert : SyncGraph → RetimingCert → ProcessCorner → Nat → Bool`
    verifying non-negative retimed edge weights, I/O boundary uniformity, and per-stage timing
    closure.
  - **Mechanized Theorems**:
    1. `retimed_weights_nonneg`: if `checkRetimingCert G r c T = true`, every edge in `applyRetiming G r`
       has $\ge 0$ registers.
    2. `path_weight_telescopes`: along any path $v_0 \to v_1 \to \dots \to v_k$, the sum of retimed
       edge weights telescopes to $\sum_{i} w(e_i) + r(v_k) - r(v_0)$.
    3. `cycle_weight_invariant`: around any directed cycle $v_0 \to \dots \to v_0$, total register
       count is strictly invariant under retiming ($\sum w_r(e) = \sum w(e)$).
    4. `leiserson_saxe_shift_sound`: for any DAG pipeline with boundary lag $L$, the retimed circuit
       evaluated at cycle $t + L$ equals the un-retimed circuit evaluated at cycle $t$!

### 1.5 Verified Place-and-Route (PnR), Switch-Box Routing Trees & Bitstream Decoding (`Obend.Hardware.PlaceRoute`)

* **READ.** Nextpnr / VPR place-and-route outputs a physical placement map $\pi : \text{CellId} \to
  (\text{TileCoord} \times \text{BelSlot})$ and a set of enabled Programmable Interconnect Points
  (PIPs) on the chip's routing graph. Almost all academic HDLs stop at Verilog emission and trust
  Vivado/nextpnr PnR and `fasm2frames` bitstream generation blindly—where routing shorts, open nets,
  lut-pin permutations, and SLR timing violations actually occur.
* **PROPOSED (`Obend.Hardware.PlaceRoute`, ~1,000 lines).**
  - Physical device grid model `DeviceGrid` (tiles, BEL slots, wire nodes, directional PIPs
    `PipEdge : WireNode → WireNode` with physical capacitance $C_{\text{fF}}$ and resistance
    $R_{\Omega}$).
  - Untrusted PnR certificate `PnrCertificate` (placement table + per-net routed PIP trees + raw
    bitstream frame words).
  - **Kernel Certificate Checker (`checkPnrCertificate`)**:
    1. `checkPlacementInjective`: no two distinct cells occupy the same `(TileCoord, BelSlot)`.
    2. `checkRoutingDisjoint`: no two distinct nets use the same `WireNode` (zero short circuits!).
    3. `checkNetConnectivity`: for every net `(srcPin, sinkPins)`, the enabled PIPs form a valid
       directed path from `srcPin` to every `sinkPin` (zero open nets!).
    4. `checkElmoreDelayTiming`: computes the **Elmore RC tree delay**
       $T_{\text{Elmore}} = \sum_{e \in \text{path}} R_e \cdot C_{\text{downstream}}(e)$ for every
       routed net and verifies setup + hold closure at the target `ProcessCorner`.
    5. `decodeBitstreamFrames`: decodes raw FABulous / UltraScale-style configuration SRAM frames
       back into the placed BEL truth tables and enabled PIPs, checking `decoded == pnrCert`!
  - **Mechanized Theorems**:
    1. `placement_injective_no_collision`: if `checkPlacementInjective p = true`, distinct cell IDs
       never map to the same physical `(TileCoord, BelSlot)`.
    2. `routing_disjoint_no_short`: if `checkRoutingDisjoint nets = true`, no wire node is driven by
       two different nets.
    3. `bitstream_decode_roundtrip_sound`: if `checkBitstreamMatchesPnr frames cert = true`, the
       configured physical fabric evaluates identically to the placed-and-routed netlist.

### 1.6 Deep FabuBlox (`fabublox.com`) 2D/3D Nanofabrication Physics, DRC/LVS & Cleanroom `Facility OS` (`Obend.Hardware.FabuBlox`)

* **READ.** FabuBlox (`fabublox.com`, MIT Palacios Group / MTL spinout) replaces cleanroom "tribal
  know-how" with version-controlled process flows, physics-informed 2D/3D GDS cutline cross-section
  emulation (`StackSimulator`), and `Facility OS` cleanroom constraint checking.
* **INFERRED.** A real semiconductor process flow is far richer than a 6-step toy list:
  - **Deposition physics** depends on conformality / step coverage $\eta \in [0, 100]\%$:
    * **ALD (Atomic Layer Deposition, e.g. $\text{HfO}_2$, $\text{TiN}$)** has $\eta \approx 100\%$
      (conformal on vertical sidewalls and trench bottoms),
    * **PECVD / LPCVD ($\text{SiO}_2$, $\text{Si}_3\text{N}_4$, $\text{W}$)** has $\eta \approx 60\text{--}85\%$,
    * **Directional PVD / E-Beam Evaporation ($\text{Al}$, $\text{Cu}$ seed, $\text{Au}$)** has
      low sidewall step coverage ($\eta \approx 15\text{--}30\%$)—which makes **lift-off** work on
      negative/undercut resist profiles, but causes **pinch-off keyhole voids** if used to fill a
      high-aspect-ratio via trench ($\text{AR} = H/W > 2$)!
  - **Etch physics** distinguishes:
    * **Anisotropic ICP-RIE / RIE** (vertical etch rate $R_v \gg$ lateral undercut rate $R_{\text{lat}}$,
      governed by material selectivity matrix $S(m_1, m_2)$ and polymer passivation),
    * **Isotropic Wet Etch (BOE / HF / KOH / Piranha)** ($R_{\text{lat}} \approx R_v$, creating
      undercuts beneath mask edges—essential for MEMS release or lift-off overhang, fatal if it
      undercuts adjacent minimum-pitch gates!),
    * **Bosch Deep-Rie (DRIE)** alternating $\text{SF}_6$ etch cycles and $\text{C}_4\text{F}_8$
      fluorocarbon passivation cycles.
  - **Lithography & Design Rule Checking (DRC)**:
    * Minimum critical dimension ($\text{CD}_{\min}$ based on wavelength $\lambda / \text{NA}$:
      contact aligner $2000\text{ nm}$, i-line stepper $350\text{ nm}$, DUV $193\text{ nm}$ immersion
      $40\text{ nm}$, EUV $13.5\text{ nm}$ $12\text{ nm}$, E-beam direct write $10\text{ nm}$),
    * Overlay / alignment tolerance $\Delta_{\text{ovl}}$ between mask layers (via must land inside
      bottom metal pad with enclosure $\ge \Delta_{\text{ovl}}$ on both left and right edges, or
      borderless via misalignment causes substrate short!),
    * Aspect-ratio limit for trench fill and resist collapse ($\text{AR}_{\text{resist}} \le 4$).
  - **Cleanroom `Facility OS` Contamination & Tool-Zone Matrix**:
    * Cleanroom tools are partitioned into strict contamination levels:
      1. `Zone.feolCmosClean` (Si, $\text{SiO}_2$, $\text{Si}_3\text{N}_4$, PolySi, $\text{HfO}_2$ only),
      2. `Zone.meolBarrier` (allows $\text{Ti}$, $\text{TiN}$, $\text{W}$, $\text{Co}$),
      3. `Zone.beolMetals` (allows $\text{Al}$, $\text{Cu}$ with barrier),
      4. `Zone.nobleAndIIIV` (allows $\text{Au}$, $\text{Pt}$, $\text{GaN}$, $\text{InP}$ — strictly
         one-way: once a wafer enters `Zone.nobleAndIIIV`, it can NEVER return to Zones 1–3!).
* **PROPOSED (`Obend.Hardware.FabuBlox` expanded to ~1,200 lines + `Obend.Hardware.DRC` ~800 lines).**
  - Full cleanroom zone hierarchy (`CleanroomZone`), material contamination lattice
    (`materialMinZone : FabMaterial → CleanroomZone`, `waferZone : WaferState → CleanroomZone`),
    and monotonicity law (`waferZone` only moves up the contamination lattice, and no tool in zone
    $z_{\text{tool}}$ accepts a wafer with `waferZone w > z_{\text{tool}}`).
  - Step-coverage & void-formation model (`checkTrenchFillVoidFree`: verifies whether a trench of
    depth $H$ and width $W$ filled by a deposition method with step coverage $\eta$ pinches off
    into a keyhole void before the bottom fills).
  - Isotropic vs anisotropic lateral undercut & mask enclosure verifier (`checkLithoOverlayAndUndercut`:
    verifies that mask window $[x_L, x_R]$ plus worst-case alignment error $\pm \Delta_{\text{ovl}}$
    and lateral wet/dry etch undercut $u_{\text{lat}}$ remains strictly inside the underlying landing
    pad $[p_L, p_R]$).
  - Multi-layer GDS cutline DRC & Parasitic RC Extractor (`checkCutlineDRC`, `extractLayerRC`):
    verifies minimum width, minimum spacing, minimum via enclosure, and extracts parallel-plate +
    fringe capacitance $C = \varepsilon_{\text{ox}} A / d + C_{\text{fringe}}$ and sheet resistance
    $R = \rho L / (W \cdot t)$ directly into `ProcessCorner`.

### 1.7 `Obend.Judge` & `Obend.Receipt` Integration + `obend` CLI (`Obend.Hardware.Judge`, `Obend.Hardware.Cli`)

* **INFERRED.** In Objective Bend, no subsystem is complete until its certificates are first-class
  `Obend.Judge.Format` instances, its receipts verify through `Obend.Receipt`, and the `obend`
  executable exposes stranger-usable commands tested by an end-to-end Python suite.
* **PROPOSED (`Obend.Hardware.Judge` ~750 lines + `Obend.Hardware.Cli` ~650 lines).**
  - Registered hardware & nanofabrication certificate formats:
    1. `hw-rtl-synth@1`: checks that an emitted `RtlModule` matches `compileBookToRtl` of a pinned
       `Obend.Leaf.Book` digest and passes `checkRtlModule` (DAG + CDC + fanout).
    2. `hw-retime-sta@1`: checks a Leiserson–Saxe retiming lag certificate and multi-corner
       (SS setup + FF hold) static timing closure.
    3. `hw-pnr-bitstream@1`: checks physical placement injectivity, PIP routing disjointness, net
       connectivity, Elmore delay closure, and bitstream frame decode round-trip.
    4. `fabublox-run@1`: checks a multi-step cleanroom recipe against `Facility OS` zone
       monotonicity, thermal budget, resist thermal limits, DRC overlay/undercut rules, void-free
       trench fill, and target layer-stack spec.
  - CLI subcommands in `obend`:
    * `obend hardware synth --package PACKAGE.json --object ENTRY [--corner 7nm|16nm|130nm] [--period-ps N] [--out-sv FILE.sv] [--out-receipt RECEIPT.json]`
    * `obend hardware verify-pnr PNR_CERT.json [--out-receipt RECEIPT.json]`
    * `obend fabublox check FLOW.json [--out-receipt RECEIPT.json]`
    * Full integration with `obend verify RECEIPT.json`!

---

## 2. Module Map & Target Scale (`Obend/Hardware/`)

| Module | Responsibility | Key Theorems (`0 sorry`) | Est. Lines |
|---|---|---|---|
| `Obend/Hardware/Types.lean` | `HwType` (`.bits`, `.struct`, `.taggedUnion`, `.array`), bit-packing isomorphism, field slice lenses, sum muxing | `unpack_pack_id`, `struct_slice_extract_sound`, `struct_slice_update_noninterference`, `taggedUnion_case_mux_sound` | ~900 |
| `Obend/Hardware/HDL.lean` | Core synchronous RTL AST, topological DAG checker, multi-clock CDC verifier, hierarchical submodule instances, SystemVerilog-2012 emitter | `evalRtlExpr_dag_locality`, `cdcSafe_no_unsynchronized_crossing`, `instPortMap_sound` | ~850 |
| `Obend/Hardware/Rules.lean` | Kôika/Kami-style guarded atomic actions (`HwRule`), dynamic action logs, static conflict matrix, ORAAT refinement | `conflictFree_two_rules_commute`, `schedule_oraat_refinement` | ~900 |
| `Obend/Hardware/FSM.lean` | Multi-cycle Valid/Ready FSMs, fuel-bounded `fix` loop synthesis, `perform`/`resume` activity handshakes | `fsm_no_overwrite_while_busy`, `fsm_fuel_monotone_termination`, `fsm_refines_tailrec`, `fsm_yield_resume_sound` | ~950 |
| `Obend/Hardware/Compiler.lean` | General `Obend.Core.Term` & `Obend.Leaf.Book` → `RtlModule` + `FsmConfig` compiler (records, sums, `let`, `self.m`, `ifZero`, loops) | `substInputPort0_sound`, `compilePrim_sound`, `compileTerm_sound`, `compileBook_sound` | ~900 |
| `Obend/Hardware/Synth.lean` | Gate-level `LUT2`/`LUT3`/`LUT6` & `CARRY8` adder/subtractor/comparator tech-mapping, Wallace/CSA multiplier trees | `lut2_or_sound`, `lut3_mux_sound`, `evalLut3MuxBits_sound`, `carrySubBel_eq_fullSubStageSpec`, `csa3to2_sum_sound` | ~800 |
| `Obend/Hardware/Retiming.lean` | Leiserson–Saxe synchronous graph retiming, integer lag certificates, cycle weight invariance, latency-shifted equivalence | `retimed_weights_nonneg`, `path_weight_telescopes`, `cycle_weight_invariant`, `leiserson_saxe_shift_sound` | ~850 |
| `Obend/Hardware/PlaceRoute.lean` | Physical device grid, untrusted PnR certificate checker (placement injectivity, PIP routing disjointness, Elmore RC delay, bitstream frame decoder) | `placement_injective_no_collision`, `routing_disjoint_no_short`, `bitstream_decode_roundtrip_sound` | ~950 |
| `Obend/Hardware/FabuBlox.lean` | FabuBlox (`fabublox.com`) 2D GDS cutline `StackSimulator`, 4-zone cleanroom `Facility OS` contamination lattice, ALD/CVD/PVD step coverage & keyhole void checker, isotropic/anisotropic etch & overlay enclosure | `zone_monotonicity_sound`, `facilityCheck_prevents_scorched_resist`, `facilityCheck_prevents_feol_contamination`, `conformal_ald_void_free`, `overlay_enclosure_prevents_short`, `rie_selective_via_landing_sound` | ~1,100 |
| `Obend/Hardware/DRC.lean` | Multi-layer GDS cutline Design Rule Checker (min width/spacing/enclosure/aspect ratio) & parasitic $RC$ extraction to `ProcessCorner` | `drc_clean_implies_min_pitch`, `drc_clean_implies_via_landed`, `extracted_corner_monotone_in_oxide` | ~750 |
| `Obend/Hardware/Analog.lean` | Analog & Mixed-Signal (AMS) Kirchhoff networks, 4-terminal MOSFET/MIM-cap/resistor SPICE primitives, `ABBA` common-centroid gradient-cancellation theorem, multi-voltage UPF (`5V`/`3.3V`/`1.8V`) oxide-breakdown & isolation checker, mixed-signal SAR ADC + DAC convergence proof, `.spice` & `SV-RNM` emitter | `commonCentroid_cancels_linear_gradient`, `powerSafe_no_oxide_overvoltage`, `sarAdc4_exact_quantization`, `switchedCap_charge_conserved` | ~1,000 |
| `Obend/Hardware/WaferSpace.lean` | `wafer.space` (`GF180MCU` 180nm 3.3V/5V, `Sky130` 130nm, `IHP SG13G2` BiCMOS) MPW shuttle signoff: IO padring + ESD clamp continuity, plasma-etch antenna ratio + diode checker, CMP metal density $[30\%, 70\%]$, LVS schematic-vs-layout checker, LibreLane/OpenLane GF180MCU generator | `padring_esd_and_power_complete`, `antennaSafe_no_gate_oxide_damage`, `cmpDensity_within_foundry_window`, `lvsMatch_sound` | ~900 |
| `Obend/Hardware/Judge.lean` | `Obend.Judge` & `Obend.Receipt` certificate formats (`hw-rtl-synth@1`, `hw-retime-sta@1`, `hw-pnr-bitstream@1`, `fabublox-run@1`, `waferspace-signoff@1`) | `hwSynthFormat_sound`, `hwRetimeFormat_sound`, `hwPnrFormat_sound`, `fabubloxFormat_sound`, `waferSpaceFormat_sound` | ~750 |
| `Obend/Hardware/Cli.lean` | `obend hardware ...` and `obend fabublox ...` CLI commands wired into `Obend.Main` | CLI JSON/SV/Receipt emission & exit-code contract | ~600 |
| `Obend/Hardware/{Silicon,Process,Fabric}.lean` | Demand wave chip, `DSP48E2`, `URAM288`, AXI4-Stream skid buffer, FABulous 2×2 eFPGA mesh, Merkle receipt engine, `DeosCounter` + `Vault.Law`, 3-tier `HwCandidate` slot | 25+ existing silicon theorems | ~1,365 |
| `Obend/Teeth/Hardware/SiliconTeeth.lean` | Comprehensive positive/negative refusal poles, end-to-end compilation & PnR/FabuBlox certificates, and 20+ `#tooth` kernel mutations | 20+ `#tooth` mutation checks & refusal theorems | ~650 |

**Total `Obend.Hardware` + `Teeth` + `hardware/` Footprint**: **~12,000+ lines of zero-`sorry` Lean 4, SystemVerilog-2012, Z3 SMT-LIB2, and Verilator C++ co-simulation.**
