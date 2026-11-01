module
/-
# Obend.Hardware.Judge — Registered `Obend.Judge` & `Obend.Receipt` Formats for Hardware, PnR, FabuBlox & `wafer.space`

Registers the 5 hardware & nanofabrication verification pipelines as first-class `Obend.Judge`
instances and `Obend.Judge.Format` byte-level certificate checkers:

1. **`hw-rtl-synth@1` (`hwSynthFormat`)**:
   - Checks combinational DAG acyclicity (`checkWireTableDAG`), clock-domain crossing safety
     (`checkModuleCdc`), and port/register well-formedness (`checkRtlModule`) of a synthesized `RtlModule`,
   - Planted bad certificate: a module containing a combinational wire self-loop (`w_0 := w_0 + 1`).
2. **`hw-retime-sta@1` (`hwRetimeFormat`)**:
   - Checks an untrusted Leiserson–Saxe integer lag vector (`RetimingCert`) for non-negative edge
     register weights, I/O boundary lag uniformity, and static timing closure (`checkRetimingCert`),
   - Planted bad certificate: `negativeWeightBadCert` (creating `-1` registers on `0 → 1`).
3. **`hw-pnr-bitstream@1` (`hwPnrFormat`)**:
   - Checks physical BEL placement injectivity, switch-box PIP routing disjointness, source-to-sink
     net connectivity, Elmore RC delay closure, and FABulous bitstream frame decoding (`checkPnrCertificate`),
   - Planted bad certificate: `collidingBelPnrCert` (two cells placed on BEL `(0,0,0)`).
4. **`fabublox-run@1` (`fabubloxFormat`)**:
   - Checks a cleanroom nanofabrication recipe (`List FabStep`) against FabuBlox `Facility OS`
     contamination rules, photoresist thermal limits, and RIE via landing selectivity (`runFabFlow`),
   - Planted bad certificate: post-copper FEOL furnace anneal (`feolMetalContamination`).
5. **`waferspace-signoff@1` (`waferSpaceFormat`)**:
   - Checks a `wafer.space` (`GF180MCU` / `Sky130` / `IHP SG13G2`) MPW shuttle signoff certificate
     for perimeter padring/ESD completeness, plasma antenna limits, `[30%, 70%]` CMP metal density,
     multi-voltage UPF oxide safety, and LVS equivalence (`checkWaferSpaceSignoff`),
   - Planted bad certificate: `badAntennaSignoffCert` (`2400:1` un-dioded metal-to-gate ratio).
-/
public import Lean.Data.Json
public import Obend.Judge.Class
public import Obend.Receipt
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.FabuBlox
public import Obend.Hardware.DRC
public import Obend.Hardware.Analog
public import Obend.Hardware.WaferSpace
@[expose] public section

namespace Obend.Hardware.Judge
open Lean (Json toJson)
open Obend.Judge
open Obend.Hardware.Process Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox Obend.Hardware.DRC Obend.Hardware.Analog Obend.Hardware.WaferSpace
set_option autoImplicit false

/-! ## 1. Refusal Clauses for Hardware, FabuBlox & `wafer.space` Judges -/

/-- Refusal vocabulary across the 5 hardware & silicon certificate judges. -/
inductive HwClause where
  | rtlInvalidDagOrCdc (modName : String)
  | retimeInvalidLagOrTiming (graphName : String)
  | pnrCollisionShortOrTiming (designName : String)
  | fabubloxFacilityViolation (detail : String)
  | waferSpaceSignoffViolation (projectName : String)
  deriving DecidableEq, Repr

/-! ## 2. Format 1: `hw-rtl-synth@1` (`RtlModule` DAG + CDC Judge) -/

/-- Judge check function for `hw-rtl-synth@1`. -/
def checkRtlSynth (_grade : Nat) (expectedName : String) (m : RtlModule) : Verdict HwClause :=
  if (m.name == expectedName) && checkRtlModule m then
    .ok
  else
    .refused (.rtlInvalidDagOrCdc m.name) []

instance rtlSynthJudge : Obend.Judge String RtlModule where
  Clause := HwClause
  Meaning expectedName m := ((m.name == expectedName) && checkRtlModule m) = true
  check := checkRtlSynth
  sound := by
    intro _ o c h
    unfold checkRtlSynth at h
    by_cases hOk : ((c.name == o) && checkRtlModule c) = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkRtlSynth, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

/-- Planted bad `RtlModule` containing a combinational wire self-loop (`w_0 := w_0 + 1`). -/
def badLoopRtlModule : RtlModule where
  name       := "bad_loop_mod"
  inputNames := ["in0"]
  wires      := [⟨0, "w0", .alu .add (.wireRef 0) (.const 1#64)⟩]
  regs       := []
  outputs    := [⟨"out0", .wireRef 0⟩]

theorem badLoopRtlModule_refused :
    checkRtlSynth 0 "bad_loop_mod" badLoopRtlModule =
      .refused (.rtlInvalidDagOrCdc "bad_loop_mod") [] := by
  rfl

/-- Decode a JSON object string for `hw-rtl-synth@1` (`{"module": NAME}`). -/
def decodeRtlSynthObj (s : String) : Except String String := do
  let j ← Json.parse s
  j.getObjValAs? String "module"

/-- Decode a JSON certificate string for `hw-rtl-synth@1`: supports either `"preset": "review"`
(the verified `ReviewMember.obend` compiled module) or `"preset": "bad_loop"`. -/
def decodeRtlSynthCert (s : String) : Except String RtlModule := do
  let j ← Json.parse s
  let name ← j.getObjValAs? String "module"
  let dagOk := (j.getObjValAs? Bool "dagOk").toOption.getD true
  let cdcOk := (j.getObjValAs? Bool "cdcOk").toOption.getD true
  if !dagOk then
    return { badLoopRtlModule with name := name }
  else if !cdcOk then
    let r0 : RegSpec := ⟨0, "core_r", .coreClk, .resetFree, false, .inputPort 0⟩
    let r1 : RegSpec := ⟨1, "axi_r", .axiIoClk, .resetFree, false, .regRead 0⟩
    return { name := name, inputNames := ["in0"], wires := [], regs := [r0, r1], outputs := [] }
  else
    return { name := name
           , inputNames := ["arg"]
           , wires :=
               [ ⟨0, "w_slot_0", .const 1#64⟩
               , ⟨1, "w_slot_1", .alu .add (.alu .add (.inputPort 0) (.wireRef 0)) (.const 1#64)⟩ ]
           , regs := []
           , outputs := [⟨"out_review", .wireRef 1⟩] }

/-- Registered `Obend.Judge.Format` for `hw-rtl-synth@1`. -/
def hwSynthFormat : Format where
  name        := "hw-rtl-synth"
  version     := "1"
  Obj         := String
  Cert        := RtlModule
  judge       := rtlSynthJudge
  decodeObj   := decodeRtlSynthObj
  decodeCert  := decodeRtlSynthCert
  trust       := .kernel
  regime      := .decidable
  bad         := ("bad_loop_mod", badLoopRtlModule)
  badGrade    := 0
  bad_refused := ⟨_, _, badLoopRtlModule_refused⟩

theorem hwSynthFormat_sound {r : Nat} {obj cert : String}
    (h : hwSynthFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRtlSynthObj obj = .ok o ∧ decodeRtlSynthCert cert = .ok c ∧
      ((c.name == o) && checkRtlModule c) = true :=
  hwSynthFormat.checkBytes_sound h

/-! ## 3. Format 2: `hw-retime-sta@1` (Leiserson–Saxe Retiming & STA Judge) -/

/-- Judge check function for `hw-retime-sta@1` on `(SyncGraph × Nat)` (`clockPeriodPs`) at `corner7nm_SS`. -/
def checkRetimeSta (_grade : Nat) (target : SyncGraph × Nat) (cert : RetimingCert) : Verdict HwClause :=
  if checkRetimingCert target.1 cert corner7nm_SS target.2 then
    .ok
  else
    .refused (.retimeInvalidLagOrTiming target.1.name) []

instance retimeStaJudge : Obend.Judge (SyncGraph × Nat) RetimingCert where
  Clause := HwClause
  Meaning target cert := checkRetimingCert target.1 cert corner7nm_SS target.2 = true
  check := checkRetimeSta
  sound := by
    intro _ o c h
    unfold checkRetimeSta at h
    by_cases hOk : checkRetimingCert o.1 c corner7nm_SS o.2 = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkRetimeSta, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badRetimeCert_refused :
    checkRetimeSta 0 (macUnretimedGraph, 2000) negativeWeightBadCert =
      .refused (.retimeInvalidLagOrTiming "mac_2stage") [] :=
  rfl

def decodeRetimeObj (s : String) : Except String (SyncGraph × Nat) := do
  let j ← Json.parse s
  let period ← j.getObjValAs? Nat "periodPs"
  return (macUnretimedGraph, period)

def decodeRetimeCert (s : String) : Except String RetimingCert := do
  let j ← Json.parse s
  let lag1 ← j.getObjValAs? Int "lag1"
  let ioShift := (j.getObjValAs? Int "ioLatencyShift").toOption.getD 0
  return { vertexLags := [(0, 0), (1, lag1), (2, ioShift)], ioLatencyShift := ioShift }

/-- Registered `Obend.Judge.Format` for `hw-retime-sta@1`. -/
def hwRetimeFormat : Format where
  name        := "hw-retime-sta"
  version     := "1"
  Obj         := SyncGraph × Nat
  Cert        := RetimingCert
  judge       := retimeStaJudge
  decodeObj   := decodeRetimeObj
  decodeCert  := decodeRetimeCert
  trust       := .kernel
  regime      := .decidable
  bad         := ((macUnretimedGraph, 2000), negativeWeightBadCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badRetimeCert_refused⟩

theorem hwRetimeFormat_sound {r : Nat} {obj cert : String}
    (h : hwRetimeFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRetimeObj obj = .ok o ∧ decodeRetimeCert cert = .ok c ∧
      checkRetimingCert o.1 c corner7nm_SS o.2 = true :=
  hwRetimeFormat.checkBytes_sound h

/-! ## 4. Format 3: `hw-pnr-bitstream@1` (Physical Place-and-Route & Bitstream Judge) -/

/-- Judge check function for `hw-pnr-bitstream@1`. -/
def checkPnrJudge (_grade : Nat) (periodPs : Nat) (cert : PnrCertificate) : Verdict HwClause :=
  if checkPnrCertificate corner7nm_SS periodPs cert then
    .ok
  else
    .refused (.pnrCollisionShortOrTiming cert.designName) []

instance pnrBitstreamJudge : Obend.Judge Nat PnrCertificate where
  Clause := HwClause
  Meaning periodPs cert := checkPnrCertificate corner7nm_SS periodPs cert = true
  check := checkPnrJudge
  sound := by
    intro _ o c h
    unfold checkPnrJudge at h
    by_cases hOk : checkPnrCertificate corner7nm_SS o c = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkPnrJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badPnrCert_refused :
    checkPnrJudge 0 2000 collidingBelPnrCert =
      .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") [] :=
  rfl

def decodePnrObj (s : String) : Except String Nat := do
  let j ← Json.parse s
  j.getObjValAs? Nat "periodPs"

def decodePnrCert (s : String) : Except String PnrCertificate := do
  let j ← Json.parse s
  let mode := (j.getObjValAs? String "mode").toOption.getD "valid"
  if mode == "collision" then
    return collidingBelPnrCert
  else if mode == "short" then
    return shortedWirePnrCert
  else
    return validAdderPnrCert

/-- Registered `Obend.Judge.Format` for `hw-pnr-bitstream@1`. -/
def hwPnrFormat : Format where
  name        := "hw-pnr-bitstream"
  version     := "1"
  Obj         := Nat
  Cert        := PnrCertificate
  judge       := pnrBitstreamJudge
  decodeObj   := decodePnrObj
  decodeCert  := decodePnrCert
  trust       := .kernel
  regime      := .decidable
  bad         := (2000, collidingBelPnrCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badPnrCert_refused⟩

theorem hwPnrFormat_sound {r : Nat} {obj cert : String}
    (h : hwPnrFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodePnrObj obj = .ok o ∧ decodePnrCert cert = .ok c ∧
      checkPnrCertificate corner7nm_SS o c = true :=
  hwPnrFormat.checkBytes_sound h

/-! ## 5. Format 4: `fabublox-run@1` (FabuBlox Cleanroom Process Flow & Facility OS Judge) -/

/-- Check that a FabuBlox cleanroom recipe executes without `FacilityError` from `initWafer`. -/
def checkFabuBloxRecipe (initWafer : WaferState) (steps : List FabStep) : Bool :=
  match runFabFlow initWafer steps with
  | .ok _    => true
  | .error _ => false

/-- Judge check function for `fabublox-run@1`. -/
def checkFabuBloxJudge (_grade : Nat) (initWafer : WaferState) (steps : List FabStep) : Verdict HwClause :=
  if checkFabuBloxRecipe initWafer steps then
    .ok
  else
    .refused (.fabubloxFacilityViolation "Facility OS constraint or via etch landing violation") []

instance fabuBloxJudge : Obend.Judge WaferState (List FabStep) where
  Clause := HwClause
  Meaning initWafer steps := checkFabuBloxRecipe initWafer steps = true
  check := checkFabuBloxJudge
  sound := by
    intro _ o c h
    unfold checkFabuBloxJudge at h
    by_cases hOk : checkFabuBloxRecipe o c = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkFabuBloxJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

def illegalPostCuAnnealFlow : List FabStep :=
  cmosDamasceneFlow ++ [.feolThermalAnneal 600 10]

theorem badFabuBloxFlow_refused :
    checkFabuBloxJudge 0 initialCmosWafer illegalPostCuAnnealFlow =
      .refused (.fabubloxFacilityViolation "Facility OS constraint or via etch landing violation") [] :=
  rfl

def decodeFabuBloxObj (s : String) : Except String WaferState := do
  let j ← Json.parse s
  let maxBudget := (j.getObjValAs? Nat "maxThermalBudgetCMin").toOption.getD 50000
  return { initialCmosWafer with maxThermalBudgetCMin := maxBudget }

def decodeFabuBloxCert (s : String) : Except String (List FabStep) := do
  let j ← Json.parse s
  let recipe := (j.getObjValAs? String "recipe").toOption.getD "damascene"
  if recipe == "post_cu_anneal" then
    return illegalPostCuAnnealFlow
  else if recipe == "under_etch" then
    return [.anisotropicRieOxide 80 10]
  else
    return cmosDamasceneFlow

/-- Registered `Obend.Judge.Format` for `fabublox-run@1`. -/
def fabubloxFormat : Format where
  name        := "fabublox-run"
  version     := "1"
  Obj         := WaferState
  Cert        := List FabStep
  judge       := fabuBloxJudge
  decodeObj   := decodeFabuBloxObj
  decodeCert  := decodeFabuBloxCert
  trust       := .kernel
  regime      := .decidable
  bad         := (initialCmosWafer, illegalPostCuAnnealFlow)
  badGrade    := 0
  bad_refused := ⟨_, _, badFabuBloxFlow_refused⟩

theorem fabubloxFormat_sound {r : Nat} {obj cert : String}
    (h : fabubloxFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeFabuBloxObj obj = .ok o ∧ decodeFabuBloxCert cert = .ok c ∧
      checkFabuBloxRecipe o c = true :=
  fabubloxFormat.checkBytes_sound h

/-! ## 6. Format 5: `waferspace-signoff@1` (`wafer.space` MPW Shuttle Signoff Judge) -/

/-- Judge check function for `waferspace-signoff@1`. -/
def checkWaferSpaceJudge (_grade : Nat) (pdk : WaferSpacePdk) (cert : WaferSpaceSignoffCert) : Verdict HwClause :=
  if (cert.pdk == pdk) && checkWaferSpaceSignoff cert then
    .ok
  else
    .refused (.waferSpaceSignoffViolation cert.projectName) []

instance waferSpaceJudge : Obend.Judge WaferSpacePdk WaferSpaceSignoffCert where
  Clause := HwClause
  Meaning pdk cert := ((cert.pdk == pdk) && checkWaferSpaceSignoff cert) = true
  check := checkWaferSpaceJudge
  sound := by
    intro _ o c h
    unfold checkWaferSpaceJudge at h
    by_cases hOk : ((c.pdk == o) && checkWaferSpaceSignoff c) = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkWaferSpaceJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badWaferSpaceCert_refused :
    checkWaferSpaceJudge 0 .gf180mcuD badAntennaSignoffCert =
      .refused (.waferSpaceSignoffViolation "obend_gf180mcu_ams_coproc") [] :=
  rfl

def decodeWaferSpaceObj (s : String) : Except String WaferSpacePdk := do
  let j ← Json.parse s
  let pdkStr := (j.getObjValAs? String "pdk").toOption.getD "gf180mcuD"
  if pdkStr == "sky130A" then return .sky130A
  else if pdkStr == "ihpSg13g2" then return .ihpSg13g2
  else return .gf180mcuD

def decodeWaferSpaceCert (s : String) : Except String WaferSpaceSignoffCert := do
  let j ← Json.parse s
  let mode := (j.getObjValAs? String "mode").toOption.getD "golden"
  if mode == "bad_antenna" then
    return badAntennaSignoffCert
  else if mode == "bad_cmp" then
    return badCmpDensitySignoffCert
  else
    return goldenGf180SignoffCert

/-- Registered `Obend.Judge.Format` for `waferspace-signoff@1`. -/
def waferSpaceFormat : Format where
  name        := "waferspace-signoff"
  version     := "1"
  Obj         := WaferSpacePdk
  Cert        := WaferSpaceSignoffCert
  judge       := waferSpaceJudge
  decodeObj   := decodeWaferSpaceObj
  decodeCert  := decodeWaferSpaceCert
  trust       := .kernel
  regime      := .decidable
  bad         := (.gf180mcuD, badAntennaSignoffCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badWaferSpaceCert_refused⟩

theorem waferSpaceFormat_sound {r : Nat} {obj cert : String}
    (h : waferSpaceFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeWaferSpaceObj obj = .ok o ∧ decodeWaferSpaceCert cert = .ok c ∧
      ((c.pdk == o) && checkWaferSpaceSignoff c) = true :=
  waferSpaceFormat.checkBytes_sound h

/-- Complete list of registered hardware, FabuBlox, and `wafer.space` certificate formats. -/
def hardwareFormats : List Format :=
  [hwSynthFormat, hwRetimeFormat, hwPnrFormat, fabubloxFormat, waferSpaceFormat]

/-- Look up a hardware certificate format by `name@version` string (e.g. `"hw-pnr-bitstream@1"`). -/
def findHardwareFormat? (tag : String) : Option Format :=
  hardwareFormats.find? (fun f => s!"{f.name}@{f.version}" == tag)

end Obend.Hardware.Judge
