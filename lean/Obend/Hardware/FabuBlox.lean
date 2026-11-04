module
/-
# Obend.Hardware.FabuBlox — cleanroom facility rules and a layer-stack bookkeeping of a process flow

A process flow as a checked sequence of steps, in the style of FabuBlox's `Facility OS`: a wafer
(`WaferState`: cutline columns of film thicknesses, exposed-metal contamination flag, thermal budget
used) and steps (`FabStep`: anneal, litho window, RIE, strip, deposit, CMP), each step refused by
`checkFacilityStep` when it would scorch unstripped resist, contaminate a FEOL furnace with exposed
Cu/Au, exceed the thermal budget, or under/over-etch a via. `runFabFlow` is the flow, `cmosDamasceneFlow`
one flow, `extractCornerFromWafer` and `extractInterconnectRCFromCutline` the integer bookkeeping
`WaferSpace` and `TapeoutPipeline` read from the final wafer.

**What this is and is not** (device-physics lane, 2026-11-04). The rules are real cleanroom rules
and the theorems about them (`facilityCheck_prevents_scorched_resist`,
`facilityCheck_prevents_feol_contamination`, `rie_masked_column_invariant`,
`rie_selective_via_landing_sound`) say exactly what the checker refuses. The steps carry no physics:
an anneal here spends thermal budget, it does not diffuse anything; a deposition adds nanometres.
The physics of implant, diffusion, oxidation and the device they make is `Obend/Hardware/Device/`
(`Wafer.lean` for the operators, `DriftDiffusion.lean` for the device). Deleted from this file on
that date: the "thicker metal, lower resistance" theorems of §6 (integer division monotonicity) and
all of §7 (an isqrt "Fickian depth", CMP dishing, step coverage, GAA release: affine integer formulas
under process names).
-/
public import Obend.Hardware.Process
@[expose] public section

namespace Obend.Hardware.FabuBlox
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Cleanroom Materials, Equipment Classes & 2D Cutline Cross-Sections -/

/-- Semiconductor fabrication materials tracked across the wafer layer stack. -/
inductive FabMaterial where
  | siSubstrate
  | sio2
  | si3n4
  | hfo2
  | polySi
  | tiN
  | wPlug
  | alMetal
  | cuMetal
  | auMetal
  deriving DecidableEq, Repr

/-- Sacrificial $\text{Si}_{1-x}\text{Ge}_x$ epitaxial superlattice layer for Gate-All-Around (GAA)
nanosheet selective release etching (mapped to the FEOL non-channel spacer class so all existing
`FabMaterial` zone classifiers remain exhaustive). -/
abbrev FabMaterial.siGe : FabMaterial := .si3n4

/-- Cleanroom facility equipment classes managed by `Facility OS`. -/
inductive ToolClass where
  | feolFurnace    -- High-temp CMOS oxidation / diffusion / spike anneal tube (no Cu/Au allowed!)
  | aldChamber     -- Atomic Layer Deposition (100% conformal step coverage, FEOL-clean)
  | pecvdChamber   -- Plasma-Enhanced CVD dielectric deposition
  | pvdSputter     -- Directional PVD metal sputter
  | lithoStepper   -- Spin-coat + UV/EUV mask cutline exposure + puddle develop
  | icpRieEtcher   -- Anisotropic ICP-RIE plasma etcher
  | ashStripper    -- O2 plasma photoresist stripper
  | cmpPolisher    -- Chemical-Mechanical Planarization platen
  deriving DecidableEq, Repr

/-- Vertical film stack at a single lateral coordinate `xCoordNm` along a GDS layout cutline. -/
structure CutlineColumn where
  xCoordNm          : Nat
  siThicknessNm     : Nat
  gateOxideNm       : Nat
  tiNBarrierNm      : Nat
  ildOxideNm        : Nat
  metalThicknessNm  : Nat
  resistThicknessNm : Nat
  sidewallAngleDeg  : Nat
  deriving DecidableEq, Repr

/-- Total vertical height (in nm) of a cutline column (excluding sacrificial photoresist). -/
def columnHeightNm (c : CutlineColumn) : Nat :=
  c.siThicknessNm + c.gateOxideNm + c.tiNBarrierNm + c.ildOxideNm + c.metalThicknessNm

/-- Complete wafer state tracked along a 2D cutline during a cleanroom run. -/
structure WaferState where
  columns               : List CutlineColumn
  hasExposedCuOrAu      : Bool
  thermalBudgetUsedCMin : Nat
  maxThermalBudgetCMin  : Nat
  deriving DecidableEq, Repr

/-! ## 2. Nanofabrication Process Steps & Cleanroom `Facility OS` Rules -/

/-- Individual cleanroom fabrication step in a FabuBlox process flow. -/
inductive FabStep where
  /-- Spin-coat photoresist (`resistNm`) and expose/develop open the mask window `[xStartNm, xEndNm]`. -/
  | lithoWindow (xStartNm xEndNm resistNm : Nat)
  /-- Anisotropic ICP-RIE oxide etch of nominal depth `etchDepthNm` with oxide-to-TiN selectivity `sel`. -/
  | anisotropicRieOxide (etchDepthNm selectivityToTiN : Nat)
  /-- Strip all remaining photoresist in O2 plasma (`tempC = 110°C`). -/
  | stripPhotoresist
  /-- Deposit metal film of `thicknessNm` at temperature `tempC` in `tool`. -/
  | depositMetal (mat : FabMaterial) (thicknessNm tempC : Nat) (tool : ToolClass)
  /-- Chemical-Mechanical Planarization polishing metal down to cap `maxMetalNm`. -/
  | cmpMetal (maxMetalNm : Nat)
  /-- High-temperature FEOL furnace anneal at `tempC` for `durationMin` minutes. -/
  | feolThermalAnneal (tempC durationMin : Nat)
  deriving DecidableEq, Repr

/-- Extract the cleanroom tool used by a `FabStep`. -/
def stepTool : FabStep → ToolClass
  | .lithoWindow _ _ _       => .lithoStepper
  | .anisotropicRieOxide _ _ => .icpRieEtcher
  | .stripPhotoresist        => .ashStripper
  | .depositMetal _ _ _ tool => tool
  | .cmpMetal _              => .cmpPolisher
  | .feolThermalAnneal _ _   => .feolFurnace

/-- Extract the peak process temperature (in °C) of a `FabStep`. -/
def stepTempC : FabStep → Nat
  | .lithoWindow _ _ _       => 110
  | .anisotropicRieOxide _ _ => 60
  | .stripPhotoresist        => 110
  | .depositMetal _ _ temp _ => temp
  | .cmpMetal _              => 40
  | .feolThermalAnneal t _   => t

/-- Cleanroom facility & process-integration violations caught by FabuBlox before wafer execution. -/
inductive FacilityError where
  | feolMetalContamination (tool : ToolClass)
  | photoresistScorched (tempC : Nat)
  | thermalBudgetExceeded (used limit : Nat)
  | zeroSelectivity
  | viaUnderEtchUnopened (xCoordNm etchDepthNm ildOxideNm : Nat)
  | viaOverEtchPunchThrough (xCoordNm overEtchTiNNm tiNBarrierNm : Nat)
  deriving DecidableEq, Repr

/-- Check whether any column on the wafer currently carries unstripped photoresist. -/
def hasPhotoresist (st : WaferState) : Bool :=
  st.columns.any (fun c => c.resistThicknessNm > 0)

/-- Check that every unmasked cutline column clears its ILD oxide without punching through TiN. -/
def checkRieColumns (depth sel : Nat) : List CutlineColumn → Option FacilityError
  | [] => none
  | c :: rest =>
    if c.resistThicknessNm == 0 then
      if depth < c.ildOxideNm then
        some (.viaUnderEtchUnopened c.xCoordNm depth c.ildOxideNm)
      else
        let overEtchTiN := (depth - c.ildOxideNm) / sel
        if overEtchTiN ≥ c.tiNBarrierNm then
          some (.viaOverEtchPunchThrough c.xCoordNm overEtchTiN c.tiNBarrierNm)
        else
          checkRieColumns depth sel rest
    else
      checkRieColumns depth sel rest

/-- Verify a single `FabStep` against `Facility OS` cleanroom contamination, thermal, and etch rules.
Returns `none` when the step is safe, or `some err` naming the exact facility violation. -/
def checkFacilityStep (st : WaferState) (step : FabStep) : Option FacilityError :=
  let tool := stepTool step
  let temp := stepTempC step
  if (tool == .feolFurnace || tool == .aldChamber) && st.hasExposedCuOrAu then
    some (.feolMetalContamination tool)
  else if temp > 150 && hasPhotoresist st then
    some (.photoresistScorched temp)
  else
    match step with
    | .feolThermalAnneal t dur =>
      let newBudget := st.thermalBudgetUsedCMin + t * dur
      if newBudget > st.maxThermalBudgetCMin then
        some (.thermalBudgetExceeded newBudget st.maxThermalBudgetCMin)
      else
        none
    | .anisotropicRieOxide depth sel =>
      if sel == 0 then
        some .zeroSelectivity
      else
        checkRieColumns depth sel st.columns
    | _ => none

/-! ## 3. 2D Cutline Layer-Stack Emulator (`stepColumn`, `stepWafer`, `runFabFlow`) -/

/-- Transform a single `CutlineColumn` under a `FabStep`. -/
def stepColumn (step : FabStep) (c : CutlineColumn) : CutlineColumn :=
  match step with
  | .lithoWindow xStart xEnd resistNm =>
    if xStart ≤ c.xCoordNm && c.xCoordNm ≤ xEnd then
      { c with resistThicknessNm := 0 }
    else
      { c with resistThicknessNm := resistNm }
  | .anisotropicRieOxide depth sel =>
    if c.resistThicknessNm > 0 then
      -- Masked by photoresist: underlying dielectric & TiN landing pad are protected
      c
    else
      -- Unmasked window: anisotropic RIE clears oxide and over-etches into TiN scaled by 1/sel
      let remOxide := c.ildOxideNm - depth
      let overEtch := (depth - c.ildOxideNm) / sel
      { c with
        ildOxideNm       := remOxide
        tiNBarrierNm     := c.tiNBarrierNm - overEtch
        sidewallAngleDeg := 88 }
  | .stripPhotoresist =>
    { c with resistThicknessNm := 0 }
  | .depositMetal _ thicknessNm _ _ =>
    { c with metalThicknessNm := c.metalThicknessNm + thicknessNm }
  | .cmpMetal maxMetalNm =>
    { c with metalThicknessNm := Nat.min c.metalThicknessNm maxMetalNm }
  | .feolThermalAnneal _ _ =>
    c

/-- Result of executing a cleanroom fabrication step or flow. -/
inductive FabResult (α : Type) where
  | ok (val : α)
  | error (err : FacilityError)
  deriving DecidableEq, Repr

/-- Apply a checked `FabStep` to the entire `WaferState`. -/
def stepWafer (st : WaferState) (step : FabStep) : FabResult WaferState :=
  match checkFacilityStep st step with
  | some err => .error err
  | none =>
    let nextCols := st.columns.map (stepColumn step)
    let nextCuAu :=
      match step with
      | .depositMetal mat _ _ _ => st.hasExposedCuOrAu || mat == .cuMetal || mat == .auMetal
      | _ => st.hasExposedCuOrAu
    let nextBudget :=
      match step with
      | .feolThermalAnneal t dur => st.thermalBudgetUsedCMin + t * dur
      | _ => st.thermalBudgetUsedCMin
    .ok {
      columns               := nextCols
      hasExposedCuOrAu      := nextCuAu
      thermalBudgetUsedCMin := nextBudget
      maxThermalBudgetCMin  := st.maxThermalBudgetCMin
    }

/-- Run a sequence of `FabStep`s, halting immediately if any `Facility OS` or process rule fails. -/
def runFabFlow (init : WaferState) : List FabStep → FabResult WaferState
  | [] => .ok init
  | s :: rest =>
    match stepWafer init s with
    | .ok st' => runFabFlow st' rest
    | .error err => .error err

/-! ## 4. Formal Soundness Theorems for Cleanroom Rules & Etch Selectivity -/

/-- Theorem 1 (`facilityCheck_prevents_scorched_resist`):
If `checkFacilityStep st step = none` and the step temperature exceeds `150°C`, then NO column on
the wafer has unstripped photoresist (`hasPhotoresist st = false`). -/
theorem facilityCheck_prevents_scorched_resist
    (st : WaferState) (step : FabStep)
    (hOk : checkFacilityStep st step = none)
    (hHot : stepTempC step > 150) :
    hasPhotoresist st = false := by
  unfold checkFacilityStep at hOk
  by_cases hContam : (stepTool step == .feolFurnace || stepTool step == .aldChamber) && st.hasExposedCuOrAu
  · simp [hContam] at hOk
  · simp only [hContam, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hPr : hasPhotoresist st
    · rfl
    · simp [hPr, hHot] at hOk

/-- Theorem 2 (`facilityCheck_prevents_feol_contamination`):
If `checkFacilityStep st (.feolThermalAnneal t dur) = none`, then the wafer is guaranteed free of
exposed Copper or Gold (`st.hasExposedCuOrAu = false`). -/
theorem facilityCheck_prevents_feol_contamination
    (st : WaferState) (t dur : Nat)
    (hOk : checkFacilityStep st (.feolThermalAnneal t dur) = none) :
    st.hasExposedCuOrAu = false := by
  unfold checkFacilityStep stepTool at hOk
  cases hCu : st.hasExposedCuOrAu
  · rfl
  · simp [hCu] at hOk

/-- Theorem 3 (`rie_masked_column_invariant`):
During `.anisotropicRieOxide`, any cutline column covered by photoresist (`c.resistThicknessNm > 0`)
preserves its exact `ildOxideNm` and `tiNBarrierNm` thicknesses. -/
theorem rie_masked_column_invariant
    (depth sel : Nat) (c : CutlineColumn)
    (hMasked : c.resistThicknessNm > 0) :
    stepColumn (.anisotropicRieOxide depth sel) c = c := by
  simp [stepColumn, hMasked]

/-- Theorem 4 (`rie_selective_via_landing_sound`):
On an unmasked cutline column (`c.resistThicknessNm = 0`), if `depth ≥ c.ildOxideNm` and the
selectivity-attenuated over-etch `(depth - c.ildOxideNm) / sel < c.tiNBarrierNm`, then after
`.anisotropicRieOxide depth sel`:
1. The inter-layer dielectric is completely cleared (`ildOxideNm = 0`), AND
2. The underlying `TiN` landing pad remains strictly positive (`tiNBarrierNm > 0`)! -/
theorem rie_selective_via_landing_sound
    (depth sel : Nat) (c : CutlineColumn)
    (hUnmasked : c.resistThicknessNm = 0)
    (hClear : depth ≥ c.ildOxideNm)
    (hLand : (depth - c.ildOxideNm) / sel < c.tiNBarrierNm) :
    let c' := stepColumn (.anisotropicRieOxide depth sel) c
    c'.ildOxideNm = 0 ∧ c'.tiNBarrierNm > 0 := by
  dsimp only
  simp only [stepColumn, hUnmasked, Nat.lt_irrefl, ↓reduceIte]
  constructor
  · omega
  · omega

/-! ## 5. Verified CMOS Damascene Contact-Via Flow & Process-to-Timing Extraction -/

/-- Initial 3-column wafer cutline ($x = 0\text{ nm}, 100\text{ nm}, 200\text{ nm}$) prior to contact-via
patterning: 500 nm Si substrate, 2 nm $\text{HfO}_2$ gate dielectric, 20 nm $\text{TiN}$ barrier/landing
layer, and 100 nm $\text{SiO}_2$ inter-layer dielectric. -/
def initialCmosWafer : WaferState :=
  let mkCol (x : Nat) : CutlineColumn :=
    { xCoordNm          := x
    , siThicknessNm     := 500
    , gateOxideNm       := 2
    , tiNBarrierNm      := 20
    , ildOxideNm        := 100
    , metalThicknessNm  := 0
    , resistThicknessNm := 0
    , sidewallAngleDeg  := 90 }
  { columns               := [mkCol 0, mkCol 100, mkCol 200]
  , hasExposedCuOrAu      := false
  , thermalBudgetUsedCMin := 0
  , maxThermalBudgetCMin  := 10000 }

/-- 6-step FabuBlox CMOS contact-via & copper damascene flow:
1. FEOL RTA dopant activation anneal (`950°C` for `5 min`, while wafer is still Cu-free),
2. Lithography opening contact window at $x \in [80, 120]\text{ nm}$ (`200 nm` photoresist outside),
3. Anisotropic ICP-RIE oxide etch (`120 nm` nominal depth, `10:1` selectivity to $\text{TiN}$),
4. $\text{O}_2$ plasma photoresist ash strip (`110°C`),
5. PVD/electroplated Copper fill (`250 nm` at `180°C` — safe now that photoresist is stripped!),
6. CMP copper planarization to `150 nm` thickness. -/
def cmosDamasceneFlow : List FabStep :=
  [ .feolThermalAnneal 950 5
  , .lithoWindow 80 120 200
  , .anisotropicRieOxide 120 10
  , .stripPhotoresist
  , .depositMetal .cuMetal 250 180 .pvdSputter
  , .cmpMetal 150
  ]

/-- Theorem 5b: Attempting to load the wafer back into `.feolFurnace` AFTER copper deposition is
refused by `Facility OS` with `.feolMetalContamination .feolFurnace`! -/
-- fixture kept (2026-11-04): refusal witness: `runFabFlow` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    runFabFlow initialCmosWafer (cmosDamasceneFlow ++ [.feolThermalAnneal 600 10]) =
      .error (.feolMetalContamination .feolFurnace) := by
  decide +kernel

/-- Theorem 5c: Omitting `.stripPhotoresist` before the `180°C` metal deposition is refused by
`Facility OS` with `.photoresistScorched 180`! -/
-- fixture kept (2026-11-04): refusal witness: `runFabFlow` says no to a forged/ill-formed input; no soundness theorem shows a checker can refuse
example :
    runFabFlow initialCmosWafer
      [ .lithoWindow 80 120 200
      , .anisotropicRieOxide 120 10
      , .depositMetal .cuMetal 250 180 .pvdSputter ] =
      .error (.photoresistScorched 180) := by
  decide +kernel

/-- Extract a physical PDK `ProcessCorner` library model from the fabricated wafer cross-section:
thinner `gateOxideNm` improves transistor drive (`tGateMaxPs`), and thicker `metalThicknessNm`
reduces sheet resistance $R_\square$ (`tWireHopPs`). -/
def extractCornerFromWafer (w : WaferState) : ProcessCorner :=
  match w.columns.head? with
  | none => corner130nm_SS
  | some c =>
    { name        := "FabuBlox-Extracted-FinFET-SS"
    , nodeNm      := 7
    , voltageMv   := 680
    , tempC       := 125
    , tCqMaxPs    := 45
    , tCqMinPs    := 22
    , tGateMaxPs  := 65 + 15 * c.gateOxideNm
    , tGateMinPs  := 38
    , tCarryMaxPs := 12 + 5 * c.gateOxideNm
    , tWireHopPs  := if c.metalThicknessNm ≥ 100 then 120 else 350
    , tSetupPs    := 35
    , tHoldPs     := 18
    , tSkewPs     := 25 }

/-! ## 6. Cleanroom Cutline Interconnect RC Extraction (`extractInterconnectRCFromCutline`) -/

/-- Extract physical interconnect `(sheetResMilliOhm, plateCapFf)` from a fabricated `CutlineColumn`:
* Sheet resistance $R_\square = \lfloor 18000 / \max(t_{\text{metal}}, 1) \rfloor$ ($\text{m}\Omega/\square$),
* Parallel-plate capacitance $C_{\text{plate}} = \lfloor 400 / \max(t_{\text{ILD}}, 1) \rfloor$ ($\text{fF}$). -/
def extractInterconnectRCFromCutline (c : CutlineColumn) : Nat × Nat :=
  let effMetalNm := max c.metalThicknessNm 1
  let effIldNm   := max c.ildOxideNm 1
  (18000 / effMetalNm, 400 / effIldNm)

end Obend.Hardware.FabuBlox
end
