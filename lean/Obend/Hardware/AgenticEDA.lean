module
/-
# Obend.Hardware.AgenticEDA — Smart-Contract Markdown Vaults & Multi-Agent CAD/EDA Coordination

Realizes Objective Bend's vision of **"what comes after Mathematica + replacing smart-contract languages
for agentic CAD/EDA coordination"** by bridging `Obend.Vault.Page`, `Obend.Vault.Law`, and
`Obend.Spec.Law` directly with `Obend.Hardware.Datasheet`, `Obend.Hardware.PCB`, and `Obend.Hardware.RF`:

1. **Markdown Vault Component & Board Specification Parser (`EdaVaultPart`, `extractEdaVaultPart`)**:
   - Reads a Markdown component or PCB board page (`--- ... ---`) via `Obend.Vault.scalarFields` and
     `Obend.Vault.lawLines`, extracting electrical CMOS/TTL levels (`voh_min_mv`, `vih_min_mv`,
     `vol_max_mv`, `vil_max_mv`), 2D package courtyard & pin geometry (`pkg_width_um`, `pkg_length_um`,
     `pin_count`, `pin_pitch_um`), electro-thermal limits (`max_temp_mc`), RF match (`vswr_milli`),
     layout DRC violations (`drc_errors`), BOM cost (`cost_cents`), and embedded `law:` smart-contract
     invariants (`parseVaultPageLaws`).
2. **2D Geometric Courtyard / Footprint Drop-In Verification & Datasheet Block-Cite Freshness**:
   - Formalizes `checkFootprintDropIn` and proves `footprintDropIn_sound`: an agent's proposed alternate
     part is mechanically drop-in compatible on a PCB footprint only if its pin count and pin pitch
     match exactly and its 2D package body fits inside the courtyard envelope,
   - Formalizes `DatasheetCitePin` (`[[VendorDatasheet#^elec_table]]`) and proves `staleDatasheetCite_refused`:
     if a vendor datasheet block hash advances while an agent's BOM swap still pins an older revision,
     the proposal is deterministically refused until `recite` re-verifies the electrical spec.
3. **Smart-Contract Multi-Agent EDA Proposal Judge (`judgeAgenticEdaProposal`, `agenticEda_admits_sound`)**:
   - Compiles the Markdown page's `law:` smart contracts via `Obend.Spec.LawCompile.compile` and
     executes them in the `Core4` reference evaluator via `Obend.Vault.judge`, combined with physical
     CMOS noise-margin (`checkLogicInterfaceCompatibility`), 2D footprint drop-in, and datasheet-cite
     freshness gates,
   - Proves `agenticEda_admits_sound`: whenever `judgeAgenticEdaProposal` admits an agent's write,
     every `.obend` smart-contract law holds by `Obend.Vault.judge_admits` AND the physical footprint,
     electrical noise margins, and datasheet block citations are verified!
-/
public import Obend.Vault.Page
public import Obend.Vault.Law
public import Obend.Hardware.Datasheet
public import Obend.Hardware.PCB
@[expose] public section

namespace Obend.Hardware.AgenticEDA

open Obend.Vault
open Obend.Spec.Law (LawExpr Facts)
open Obend.Hardware.Datasheet
open Obend.Hardware.PCB

/-! ## 1. Markdown Vault Component & Board Specification Parser -/

/-- Canonical frontmatter scalar field schema for an `Obend.Vault` hardware component / PCB board page. -/
def edaStateKeys : List String :=
  sortNames
    [ "voh_min_mv", "vih_min_mv", "vol_max_mv", "vil_max_mv"
    , "pkg_width_um", "pkg_length_um", "pin_count", "pin_pitch_um"
    , "max_temp_mc", "vswr_milli", "drc_errors", "cost_cents" ]

/-- Structured hardware component / PCB board specification extracted from a Markdown Vault page. -/
structure EdaVaultPart where
  pageName : String
  vohMinMv : Nat
  vihMinMv : Nat
  volMaxMv : Nat
  vilMaxMv : Nat
  pkgWidthUm : Nat
  pkgLengthUm : Nat
  pinCount : Nat
  pinPitchUm : Nat
  maxTempMc : Nat
  vswrMilli : Nat
  drcErrors : Nat
  costCents : Nat
  deriving DecidableEq, Repr

/-- Look up a natural scalar field in `scalarFields src`, defaulting to `0`. -/
def lookupScalarField (fields : List (String × Nat)) (key : String) : Nat :=
  (fields.lookup key).getD 0

/-- Extract an `EdaVaultPart` from a Markdown page's YAML frontmatter via `Obend.Vault.scalarFields`. -/
def extractEdaVaultPart (pageName : String) (markdownSrc : String) : EdaVaultPart :=
  let fs := scalarFields markdownSrc
  { pageName := pageName
    vohMinMv := lookupScalarField fs "voh_min_mv"
    vihMinMv := lookupScalarField fs "vih_min_mv"
    volMaxMv := lookupScalarField fs "vol_max_mv"
    vilMaxMv := lookupScalarField fs "vil_max_mv"
    pkgWidthUm := lookupScalarField fs "pkg_width_um"
    pkgLengthUm := lookupScalarField fs "pkg_length_um"
    pinCount := lookupScalarField fs "pin_count"
    pinPitchUm := lookupScalarField fs "pin_pitch_um"
    maxTempMc := lookupScalarField fs "max_temp_mc"
    vswrMilli := lookupScalarField fs "vswr_milli"
    drcErrors := lookupScalarField fs "drc_errors"
    costCents := lookupScalarField fs "cost_cents" }

/-- Convert an `EdaVaultPart` into the canonical `(key, Nat)` association list for `Obend.Vault.stateOf`. -/
def EdaVaultPart.toScalarFields (p : EdaVaultPart) : List (String × Nat) :=
  [ ("voh_min_mv", p.vohMinMv)
  , ("vih_min_mv", p.vihMinMv)
  , ("vol_max_mv", p.volMaxMv)
  , ("vil_max_mv", p.vilMaxMv)
  , ("pkg_width_um", p.pkgWidthUm)
  , ("pkg_length_um", p.pkgLengthUm)
  , ("pin_count", p.pinCount)
  , ("pin_pitch_um", p.pinPitchUm)
  , ("max_temp_mc", p.maxTempMc)
  , ("vswr_milli", p.vswrMilli)
  , ("drc_errors", p.drcErrors)
  , ("cost_cents", p.costCents) ]

/-- Extract the electrical logic-family spec (`LogicFamilySpec`) from an `EdaVaultPart`. -/
def EdaVaultPart.toLogicFamilySpec (p : EdaVaultPart) : LogicFamilySpec :=
  { familyName := p.pageName
    vccMinMv   := 3000
    vccNomMv   := 3300
    vccMaxMv   := 3600
    vihMinMv   := (p.vihMinMv : Int)
    vilMaxMv   := (p.vilMaxMv : Int)
    vohMinMv   := (p.vohMinMv : Int)
    volMaxMv   := (p.volMaxMv : Int)
    iihMaxUa   := 1
    iilMaxUa   := 1
    iohMaxUa   := 4000
    iolMaxUa   := 4000 }

/-- Standard 3.3V LVCMOS receiver specification ($V_{IH,\min} = 2000\,\text{mV}$, $V_{IL,\max} = 800\,\text{mV}$). -/
def lvcmos33ReceiverSpec : LogicFamilySpec :=
  { familyName := "LVCMOS33_Receiver"
    vccMinMv   := 3000
    vccNomMv   := 3300
    vccMaxMv   := 3600
    vihMinMv   := 2000
    vilMaxMv   := 800
    vohMinMv   := 2900
    volMaxMv   := 200
    iihMaxUa   := 1
    iilMaxUa   := 1
    iohMaxUa   := 4000
    iolMaxUa   := 4000 }

/-- Parse all `law NAME: EXPR` frontmatter lines of a Markdown Vault page into `(name, LawExpr)`. -/
def parseVaultPageLaws (markdownSrc : String) : Except String (List (String × LawExpr)) :=
  (lawLines markdownSrc).mapM fun (name, exprTxt) =>
    match Obend.Spec.Law.parse exprTxt with
    | .ok e => .ok (name, e)
    | .error err => .error ("law " ++ name ++ ": " ++ err)

/-! ## 2. 2D Geometric Footprint Drop-In Verification & Datasheet Block-Cite Freshness -/

/-- 2D PCB land-pattern courtyard & pin-grid receptor specification on a board layout. -/
structure FootprintCourtyardSpec where
  footprintName : String
  requiredPinCount : Nat
  requiredPinPitchUm : Nat
  maxCourtyardWidthUm : Nat
  maxCourtyardLengthUm : Nat
  deriving DecidableEq, Repr

/-- Check whether an agent-proposed component `part` is a valid 2D mechanical drop-in replacement
for `fp`:
1. Exact positive pin count match (`part.pinCount = fp.requiredPinCount > 0`),
2. Exact positive pin pitch match (`part.pinPitchUm = fp.requiredPinPitchUm > 0`),
3. Package width and length fit within the PCB courtyard envelope (`pkgWidthUm ≤ maxCourtyardWidthUm`
   and `pkgLengthUm ≤ maxCourtyardLengthUm`). -/
def checkFootprintDropIn (fp : FootprintCourtyardSpec) (part : EdaVaultPart) : Bool :=
  decide (0 < fp.requiredPinCount) &&
  decide (0 < fp.requiredPinPitchUm) &&
  decide (part.pinCount = fp.requiredPinCount) &&
  decide (part.pinPitchUm = fp.requiredPinPitchUm) &&
  decide (0 < part.pkgWidthUm ∧ part.pkgWidthUm ≤ fp.maxCourtyardWidthUm) &&
  decide (0 < part.pkgLengthUm ∧ part.pkgLengthUm ≤ fp.maxCourtyardLengthUm)

/-- Theorem (`footprintDropIn_sound`):
If `checkFootprintDropIn fp part = true`, then the candidate part's pin count and pitch match the
land pattern identically and its 2D physical body is strictly contained within the PCB courtyard. -/
theorem footprintDropIn_sound (fp : FootprintCourtyardSpec) (part : EdaVaultPart)
    (hOk : checkFootprintDropIn fp part = true) :
    part.pinCount = fp.requiredPinCount ∧
    part.pinPitchUm = fp.requiredPinPitchUm ∧
    part.pkgWidthUm ≤ fp.maxCourtyardWidthUm ∧
    part.pkgLengthUm ≤ fp.maxCourtyardLengthUm := by
  dsimp only [checkFootprintDropIn] at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  omega

/-- A content-addressed datasheet block citation (`[[DatasheetPage#^blockId]]`) pinned at a
version/content digest `pinnedBlockHash` and checked against the vault's current datasheet digest
`currentDatasheetHash`. -/
structure DatasheetCitePin where
  datasheetPage : String
  blockAnchor : String
  pinnedBlockHash : Nat
  currentDatasheetHash : Nat
  deriving DecidableEq, Repr

/-- Check that a datasheet block citation is fresh (`pinnedBlockHash = currentDatasheetHash > 0`),
ensuring no stale electrical or thermal parameter table is silently used after a vendor errata update. -/
def checkDatasheetCiteFresh (cite : DatasheetCitePin) : Bool :=
  decide (0 < cite.currentDatasheetHash) &&
  decide (cite.pinnedBlockHash = cite.currentDatasheetHash)

/-- Theorem (`staleDatasheetCite_refused`):
Whenever a vendor datasheet block is revised (`cite.pinnedBlockHash ≠ cite.currentDatasheetHash`),
`checkDatasheetCiteFresh cite` evaluates to `false`, blocking any un-recited agentic BOM/layout commit. -/
theorem staleDatasheetCite_refused (cite : DatasheetCitePin)
    (hStale : cite.pinnedBlockHash ≠ cite.currentDatasheetHash) :
    checkDatasheetCiteFresh cite = false := by
  dsimp only [checkDatasheetCiteFresh]
  have hFalse : decide (cite.pinnedBlockHash = cite.currentDatasheetHash) = false :=
    decide_eq_false hStale
  rw [hFalse, Bool.and_false]

/-! ## 3. Smart-Contract Multi-Agent EDA Proposal Judge (`Obend.Vault.judge` + Physical Sign-Off) -/

/-- Outcome of judging an autonomous EDA agent's proposed component/board revision. -/
inductive AgenticEdaVerdict where
  | admitted
  | refusedBySmartContract (lawName reason : String)
  | refusedByPhysics (checkName : String)
  | undecided (why : String)
  deriving DecidableEq, Repr

/-- **Full Multi-Agent Smart-Contract + Physical EDA Judge**:
Given:
* `laws`: the board/part Markdown page's `law:` smart contracts (`List (String × LawExpr)`),
* `oldPart`, `newPart`: previous and agent-proposed component/board specifications,
* `downstreamReceiver`: downstream IC input logic specification driven by `newPart`,
* `minNoiseMarginMv`: required high/low CMOS static noise margin ($\text{mV}$),
* `courtyard`: 2D PCB land-pattern footprint receptor,
* `citePin`: content-addressed datasheet block citation pin (`[[Datasheet#^spec]]`),
* `agentName`, `facts`: proposing agent identity and ledger request facts,

evaluates:
1. All `.obend` frontmatter `law:` smart contracts via `Obend.Vault.judge` (compiled to `Core4` and
   executed by `Obend.Law.run`),
2. Physical CMOS static noise-margin compatibility (`checkLogicInterface`),
3. 2D PCB courtyard & pin-pitch drop-in compatibility (`checkFootprintDropIn`),
4. Content-addressed datasheet block citation freshness (`checkDatasheetCiteFresh`). -/
def judgeAgenticEdaProposal
    (laws : List (String × LawExpr))
    (oldPart newPart : EdaVaultPart)
    (downstreamReceiver : LogicFamilySpec)
    (minNoiseMarginMv : Int)
    (courtyard : FootprintCourtyardSpec)
    (citePin : DatasheetCitePin)
    (agentName : String)
    (facts : Facts) : AgenticEdaVerdict :=
  let S := stateTy edaStateKeys
  let oldData := stateOf edaStateKeys oldPart.toScalarFields
  let newData := stateOf edaStateKeys newPart.toScalarFields
  let reqData := requestOf agentName .write facts
  match judge S newPart.pageName laws oldData newData reqData with
  | .refused lawName reason => .refusedBySmartContract lawName reason
  | .undecided why => .undecided why
  | .admitted =>
    if !checkDatasheetCiteFresh citePin then
      .refusedByPhysics "stale-datasheet-cite"
    else if !checkFootprintDropIn courtyard newPart then
      .refusedByPhysics "footprint-courtyard-mismatch"
    else if !checkLogicInterface newPart.toLogicFamilySpec downstreamReceiver 0 minNoiseMarginMv then
      .refusedByPhysics "cmos-noise-margin-violation"
    else
      .admitted

/-- Theorem (`agenticEdaProposal_admits_sound`):
If `judgeAgenticEdaProposal` admits an autonomous agent's hardware proposal, then:
1. **Smart-Contract Soundness**: Every `.obend` frontmatter `law:` on `laws` holds of the state
   transition `(oldData, newData)` by `Obend.Vault.judge_admits`,
2. **Datasheet Provenance**: The cited vendor datasheet block hash is fresh (`pinnedBlockHash = currentDatasheetHash`),
3. **2D Geometric Drop-In**: The component's pin count, pin pitch, width, and length fit the PCB courtyard,
4. **Electrical Noise Margin**: Both high-level and low-level CMOS static noise margins against
   `downstreamReceiver` are at least `minNoiseMarginMv`! -/
theorem agenticEdaProposal_admits_sound
    (laws : List (String × LawExpr))
    (oldPart newPart : EdaVaultPart)
    (downstreamReceiver : LogicFamilySpec)
    (minNoiseMarginMv : Int)
    (courtyard : FootprintCourtyardSpec)
    (citePin : DatasheetCitePin)
    (agentName : String)
    (facts : Facts)
    (hAdmit : judgeAgenticEdaProposal laws oldPart newPart downstreamReceiver
      minNoiseMarginMv courtyard citePin agentName facts = .admitted) :
    let oldData := stateOf edaStateKeys oldPart.toScalarFields
    let newData := stateOf edaStateKeys newPart.toScalarFields
    (∀ p ∈ laws, p.2.denote facts (some oldData) newData = true) ∧
    citePin.pinnedBlockHash = citePin.currentDatasheetHash ∧
    newPart.pinCount = courtyard.requiredPinCount ∧
    newPart.pinPitchUm = courtyard.requiredPinPitchUm ∧
    newPart.pkgWidthUm ≤ courtyard.maxCourtyardWidthUm ∧
    newPart.pkgLengthUm ≤ courtyard.maxCourtyardLengthUm ∧
    downstreamReceiver.vihMinMv + minNoiseMarginMv ≤ newPart.toLogicFamilySpec.vohMinMv ∧
    newPart.toLogicFamilySpec.volMaxMv + minNoiseMarginMv ≤ downstreamReceiver.vilMaxMv := by
  dsimp only [judgeAgenticEdaProposal] at hAdmit
  split at hAdmit
  · cases hAdmit
  · cases hAdmit
  · rename_i hVaultAdmit
    cases hCite : checkDatasheetCiteFresh citePin
    · rw [hCite] at hAdmit; cases hAdmit
    · rw [hCite] at hAdmit
      cases hFp : checkFootprintDropIn courtyard newPart
      · rw [hFp] at hAdmit; cases hAdmit
      · rw [hFp] at hAdmit
        cases hLogic : checkLogicInterface newPart.toLogicFamilySpec downstreamReceiver 0 minNoiseMarginMv
        · rw [hLogic] at hAdmit; cases hAdmit
        · have hLaws := judge_admits (k := .write) hVaultAdmit
          have hFpSound := footprintDropIn_sound courtyard newPart hFp
          have hLogicSound := checkLogicInterface_guarantees_valid_thresholds
            newPart.toLogicFamilySpec downstreamReceiver 0 minNoiseMarginMv hLogic
          have hHi : downstreamReceiver.vihMinMv + minNoiseMarginMv ≤ newPart.toLogicFamilySpec.vohMinMv := by
            have h1 := hLogicSound.1
            omega
          dsimp only [checkDatasheetCiteFresh] at hCite
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hCite
          exact ⟨hLaws, hCite.2, hFpSound.1, hFpSound.2.1, hFpSound.2.2.1, hFpSound.2.2.2,
            hHi, hLogicSound.2.1⟩

/-! ## 4. Concrete Multi-Agent Markdown Vault BOM & Layout Coordination Certificate -/

/-- Golden Markdown Vault page for an SDR / GF180MCU companion LDO + Level-Shifter stage:
embeds four executable `.obend` smart-contract laws (`drc_zero`, `thermal_cap`, `rf_vswr_cap`,
`bom_budget`) alongside electrical, 2D package, thermal, and BOM scalar fields. -/
def goldenEdaPartMarkdown : String :=
  "---\n" ++
  "voh_min_mv: 2900\n" ++
  "vih_min_mv: 2000\n" ++
  "vol_max_mv: 200\n" ++
  "vil_max_mv: 800\n" ++
  "pkg_width_um: 3000\n" ++
  "pkg_length_um: 3000\n" ++
  "pin_count: 16\n" ++
  "pin_pitch_um: 500\n" ++
  "max_temp_mc: 72000\n" ++
  "vswr_milli: 1350\n" ++
  "drc_errors: 0\n" ++
  "cost_cents: 145\n" ++
  "law drc_zero: new.drc_errors == 0\n" ++
  "law thermal_cap: new.max_temp_mc <= 85000\n" ++
  "law rf_vswr_cap: new.vswr_milli <= 1500\n" ++
  "law bom_budget: new.cost_cents <= 250\n" ++
  "---\n" ++
  "# U4: Low-Noise RF LDO & CMOS Level-Shifter (`[[TI_TPS7A47#^elec_spec]]`)\n"

/-- Agent `procurement_scout`'s proposed second-source swap that lowers cost to `120` cents,
reduces peak temperature to `68000` mC, and preserves the 16-pin QFN-16 ($3\text{mm} \times 3\text{mm}$,
$0.5\text{mm}$ pitch) courtyard and $3.3\text{V}$ CMOS noise margins. -/
def goldenSecondSourceMarkdown : String :=
  "---\n" ++
  "voh_min_mv: 2950\n" ++
  "vih_min_mv: 2000\n" ++
  "vol_max_mv: 180\n" ++
  "vil_max_mv: 800\n" ++
  "pkg_width_um: 3000\n" ++
  "pkg_length_um: 3000\n" ++
  "pin_count: 16\n" ++
  "pin_pitch_um: 500\n" ++
  "max_temp_mc: 68000\n" ++
  "vswr_milli: 1280\n" ++
  "drc_errors: 0\n" ++
  "cost_cents: 120\n" ++
  "---\n"

/-- Over-budget / thermally excessive agent proposal (`cost_cents: 320 > 250`). -/
def overbudgetSecondSourceMarkdown : String :=
  "---\n" ++
  "voh_min_mv: 2950\n" ++
  "vih_min_mv: 2000\n" ++
  "vol_max_mv: 180\n" ++
  "vil_max_mv: 800\n" ++
  "pkg_width_um: 3000\n" ++
  "pkg_length_um: 3000\n" ++
  "pin_count: 16\n" ++
  "pin_pitch_um: 500\n" ++
  "max_temp_mc: 68000\n" ++
  "vswr_milli: 1280\n" ++
  "drc_errors: 0\n" ++
  "cost_cents: 320\n" ++
  "---\n"

/-- Baseline U4 Low-Noise RF LDO & CMOS Level-Shifter part specification (`[[TI_TPS7A47#^elec_spec]]`). -/
def goldenBaselinePart : EdaVaultPart :=
  { pageName := "U4_LDO"
    vohMinMv := 2900
    vihMinMv := 2000
    volMaxMv := 200
    vilMaxMv := 800
    pkgWidthUm := 3000
    pkgLengthUm := 3000
    pinCount := 16
    pinPitchUm := 500
    maxTempMc := 72000
    vswrMilli := 1350
    drcErrors := 0
    costCents := 145 }

/-- Agent `procurement_scout`'s proposed second-source part specification (`costCents = 120 ≤ 250`,
`maxTempMc = 68000 ≤ 85000`, QFN-16 $3\text{mm} \times 3\text{mm}$ $0.5\text{mm}$ pitch). -/
def goldenSecondSourcePart : EdaVaultPart :=
  { goldenBaselinePart with
    vohMinMv := 2950
    volMaxMv := 180
    maxTempMc := 68000
    vswrMilli := 1280
    costCents := 120 }

/-- Over-budget agent proposal (`costCents = 320 > 250`). -/
def overbudgetSecondSourcePart : EdaVaultPart :=
  { goldenSecondSourcePart with
    costCents := 320 }

/-- Standard QFN-16 ($3\text{mm} \times 3\text{mm}$, $0.5\text{mm}$ pitch) PCB courtyard receptor. -/
def goldenQfn16Courtyard : FootprintCourtyardSpec :=
  { footprintName := "QFN-16_3x3mm_P0.5mm"
    requiredPinCount := 16
    requiredPinPitchUm := 500
    maxCourtyardWidthUm := 3200
    maxCourtyardLengthUm := 3200 }

/-- Fresh content-addressed datasheet block citation for `[[TI_TPS7A47#^elec_spec]]`. -/
def goldenFreshDatasheetCite : DatasheetCitePin :=
  { datasheetPage := "TI_TPS7A47"
    blockAnchor := "elec_spec"
    pinnedBlockHash := 0x9A4F2C01
    currentDatasheetHash := 0x9A4F2C01 }

/-- Canonical `.obend` smart-contract laws from `goldenEdaPartMarkdown`:
* `drc_zero`: `new.drc_errors == 0`,
* `thermal_cap`: `new.max_temp_mc <= 85000`,
* `rf_vswr_cap`: `new.vswr_milli <= 1500`,
* `bom_budget`: `new.cost_cents <= 250`. -/
def goldenEdaLaws : List (String × LawExpr) :=
  [ ("drc_zero", .eqC (.field "drc_errors") 0)
  , ("thermal_cap", .leC (.field "max_temp_mc") 85000)
  , ("rf_vswr_cap", .leC (.field "vswr_milli") 1500)
  , ("bom_budget", .leC (.field "cost_cents") 250) ]

/-- Default empty ledger request facts for agentic BOM/layout proposals. -/
def defaultEdaFacts : Facts :=
  { caller := some 1, subject := some 1, height := 1, turn := 1 }

/-- Theorem (`goldenAgenticBomSwap_admitted_and_overbudget_refused`):
1. `goldenEdaLaws` enforces 4 `.obend` smart-contract invariants (`drc_zero`, `thermal_cap`,
   `rf_vswr_cap`, `bom_budget`),
2. `judgeAgenticEdaProposal` **admits** `procurement_scout`'s valid QFN-16 second-source swap
   (`goldenSecondSourcePart`) after executing the compiled `Core4` smart contracts and verifying
   datasheet freshness, QFN-16 courtyard fit, and $400\,\text{mV}$ CMOS noise margins,
3. `judgeAgenticEdaProposal` **refuses** `overbudgetSecondSourcePart` by blaming the exact
   smart-contract law `"bom_budget"` (`new.cost_cents <= 250`),
4. `judgeAgenticEdaProposal` **refuses** a stale datasheet citation (`pinnedBlockHash ≠ currentDatasheetHash`)
   with `.refusedByPhysics "stale-datasheet-cite"`. -/
theorem goldenAgenticBomSwap_admitted_and_overbudget_refused :
    goldenEdaLaws.length = 4 ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      goldenSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenQfn16Courtyard
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .admitted ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      overbudgetSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenQfn16Courtyard
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts = .refusedBySmartContract "bom_budget" "bom_budget" ∧
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      goldenSecondSourcePart
      lvcmos33ReceiverSpec
      400
      goldenQfn16Courtyard
      { goldenFreshDatasheetCite with currentDatasheetHash := 0x9A4F2C02 }
      "procurement_scout"
      defaultEdaFacts = .refusedByPhysics "stale-datasheet-cite" := by
  decide +kernel

end Obend.Hardware.AgenticEDA
end
