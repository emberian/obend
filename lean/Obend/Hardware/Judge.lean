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
public import Obend.Hardware.Thermal
public import Obend.Hardware.Datasheet
public import Obend.Hardware.Circuits
public import Obend.Hardware.RF
public import Obend.Hardware.Physics
public import Obend.Hardware.Photonics
public import Obend.Hardware.PCB
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.DSP
public import Obend.Hardware.AgenticEDA
public import Obend.Hardware.Codec
@[expose] public section

namespace Obend.Hardware.Judge
open Lean (Json toJson)
open Obend.Judge
open Obend.Hardware.Process Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox Obend.Hardware.DRC Obend.Hardware.Analog Obend.Hardware.WaferSpace
open Obend.Hardware.Thermal Obend.Hardware.Datasheet Obend.Hardware.Circuits Obend.Hardware.RF
open Obend.Hardware.Physics Obend.Hardware.Photonics Obend.Hardware.PCB
open Obend.Hardware.ReductionMachine Obend.Hardware.DSP Obend.Hardware.AgenticEDA
open Obend.Hardware.Codec
set_option autoImplicit false

/-! ## 1. Refusal Clauses for Hardware, FabuBlox, `wafer.space`, Datasheet, RF, Photonics, PCB & Agentic EDA Judges -/

/-- Refusal vocabulary across the 11 hardware, silicon, photonics, PCB, agentic EDA & binary CBOR certificate judges. -/
inductive HwClause where
  | rtlInvalidDagOrCdc (modName : String)
  | retimeInvalidLagOrTiming (graphName : String)
  | pnrCollisionShortOrTiming (designName : String)
  | fabubloxFacilityViolation (detail : String)
  | waferSpaceSignoffViolation (projectName : String)
  | datasheetCalibrationOrMarginViolation (suiteName : String)
  | rfTransceiverSignoffViolation (rigName : String)
  | photonicsPicSignoffViolation (ringName : String)
  | pcbBoardSignoffViolation (netName : String)
  | agenticEdaSwapViolation (partName : String)
  | binaryCborCertViolation (domainId : Nat)
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

/-- Parse leading decimal digits from a `List Char`. -/
def parseLeadingDigitsAux : List Char → Nat → Bool → Option Nat
  | [], acc, true => some acc
  | [], _, false => none
  | c :: cs, acc, seen =>
    if '0' ≤ c && c ≤ '9' then
      parseLeadingDigitsAux cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else if seen then
      some acc
    else
      none

/-- True if `c` is an ASCII identifier character (`a-z`, `A-Z`, `0-9`, `'_'`). -/
def isWireIdentChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'

/-- True if `c` is a field separator (`'"'`, `':'`, `'='`, `' '`, `'\t'`). -/
def isFieldSepChar (c : Char) : Bool :=
  c == '"' || c == ':' || c == '=' || c == ' ' || c == '\t'

/-- True if `cs` starts with at least one field separator character (`'"'`, `':'`, `'='`, `' '`, `'\t'`). -/
def hasFieldSepHead : List Char → Bool
  | [] => false
  | c :: _ => isFieldSepChar c

/-- Skip optional separators (`'"'`, `':'`, `'='`, `' '`, `'\t'`) before a field value. -/
def skipFieldSep : List Char → List Char
  | [] => []
  | c :: cs =>
    if isFieldSepChar c then
      skipFieldSep cs
    else
      c :: cs

/-- Parse a leading string token (alphanumeric, `'_'`, `'-'`, `'.'`) until a delimiter. -/
def parseLeadingStringTokenAux : List Char → List Char → Option String
  | [], acc => if acc.isEmpty then none else some (String.ofList acc.reverse)
  | c :: cs, acc =>
    if isWireIdentChar c || c == '-' || c == '.' then
      parseLeadingStringTokenAux cs (c :: acc)
    else if acc.isEmpty then
      none
    else
      some (String.ofList acc.reverse)

/-- Check whether `pat` is a prefix of `cs`, returning the suffix after `pat`. -/
def stripCharPrefix : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p == c then stripCharPrefix ps cs else none
  | _ :: _, [] => none

/-- Scan `cs` for `pat` at a left/right token boundary followed by separators and a `Nat`. -/
def scanNatAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option Nat
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match parseLeadingDigitsAux (skipFieldSep rest) 0 false with
          | some n => some n
          | none => scanNatAfterPatternAux pat nextPrev cs
        else
          scanNatAfterPatternAux pat nextPrev cs
      | none => scanNatAfterPatternAux pat nextPrev cs
    else
      scanNatAfterPatternAux pat nextPrev cs

def scanNatAfterPattern (pat : List Char) (cs : List Char) : Option Nat :=
  scanNatAfterPatternAux pat false cs

/-- Scan `cs` for `pat` at a left/right token boundary followed by separators and an `Int`. -/
def scanIntAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option Int
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match skipFieldSep rest with
          | '-' :: digits =>
            match parseLeadingDigitsAux digits 0 false with
            | some n => some (-Int.ofNat n)
            | none => scanIntAfterPatternAux pat nextPrev cs
          | digits =>
            match parseLeadingDigitsAux digits 0 false with
            | some n => some (Int.ofNat n)
            | none => scanIntAfterPatternAux pat nextPrev cs
        else
          scanIntAfterPatternAux pat nextPrev cs
      | none => scanIntAfterPatternAux pat nextPrev cs
    else
      scanIntAfterPatternAux pat nextPrev cs

def scanIntAfterPattern (pat : List Char) (cs : List Char) : Option Int :=
  scanIntAfterPatternAux pat false cs

/-- Scan `cs` for `pat` at a left/right token boundary followed by separators and a string token. -/
def scanStringAfterPatternAux (pat : List Char) (prevIsIdent : Bool) : List Char → Option String
  | [] => none
  | c :: cs =>
    let nextPrev := isWireIdentChar c
    if !prevIsIdent then
      match stripCharPrefix pat (c :: cs) with
      | some rest =>
        if hasFieldSepHead rest || pat.getLast? == some '"' then
          match parseLeadingStringTokenAux (skipFieldSep rest) [] with
          | some s => some s
          | none => scanStringAfterPatternAux pat nextPrev cs
        else
          scanStringAfterPatternAux pat nextPrev cs
      | none => scanStringAfterPatternAux pat nextPrev cs
    else
      scanStringAfterPatternAux pat nextPrev cs

def scanStringAfterPattern (pat : List Char) (cs : List Char) : Option String :=
  scanStringAfterPatternAux pat false cs

/-- Extract a string field `field` from a JSON or key-value wire string `s`.
    100% reducible in the Lean 4 kernel (`decide +kernel`). -/
def extractStringField (s : String) (field : String) : Option String :=
  match scanStringAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some v => some v
  | none => scanStringAfterPattern field.toList s.toList

/-- Extract a natural-number field `field` from a JSON or key-value wire string `s`.
    100% reducible in the Lean 4 kernel (`decide +kernel`). -/
def extractNatField (s : String) (field : String) : Option Nat :=
  match scanNatAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some n => some n
  | none => scanNatAfterPattern field.toList s.toList

/-- Extract a signed-integer field `field` from a JSON or key-value wire string `s`.
    100% reducible in the Lean 4 kernel (`decide +kernel`). -/
def extractIntField (s : String) (field : String) : Option Int :=
  match scanIntAfterPattern (("\"" ++ field ++ "\"").toList) s.toList with
  | some v => some v
  | none => scanIntAfterPattern field.toList s.toList

/-- Validate that a wire string `s` is non-empty and contains a `:` / `=` / `{` delimiter. -/
def ensureWireFrame (s : String) : Except String Unit :=
  let cs := s.toList
  if cs.contains ':' || cs.contains '=' || cs.contains '{' then
    .ok ()
  else
    .error "invalid wire frame: expected JSON object or key=value wire string"

def decodePnrObj (s : String) : Except String Nat := do
  match extractNatField s "periodPs" with
  | some p => return p
  | none =>
    let j ← Json.parse s
    j.getObjValAs? Nat "periodPs"

def decodePnrCert (s : String) : Except String PnrCertificate := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "valid"
  let base :=
    if mode == "collision" then collidingBelPnrCert
    else if mode == "short" then shortedWirePnrCert
    else validAdderPnrCert
  let sinkCap := (extractNatField s "sinkCapFf").getD base.sinkCapFf
  return { base with sinkCapFf := sinkCap }

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
  ensureWireFrame s
  let pdkStr := (extractStringField s "pdk").getD "gf180mcuD"
  if pdkStr == "sky130A" then return .sky130A
  else if pdkStr == "ihpSg13g2" then return .ihpSg13g2
  else return .gf180mcuD

def decodeWaferSpaceCert (s : String) : Except String WaferSpaceSignoffCert := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "golden"
  let base :=
    if mode == "bad_antenna" then badAntennaSignoffCert
    else if mode == "bad_cmp" then badCmpDensitySignoffCert
    else goldenGf180SignoffCert
  let base' := match extractNatField s "antennaRatio" with
    | some ratio =>
      { base with antennaNets := [⟨"m4_long_clk_spine", ratio * 10, 10, false⟩] }
    | none => base
  let base'' := match extractNatField s "metalDensityPct" with
    | some pct =>
      { base' with metalLayers := [⟨"Metal1", pct, 0, 100⟩] }
    | none => base'
  return base''

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

/-! ## 7. Format 6: `datasheet-fit@1` (Automated Datasheet Calibration, `74LS00` + `74HCT00` + INA + Buck Judge) -/

/-- Judge check function for `datasheet-fit@1`. -/
def checkDatasheetFitJudge (_grade : Nat) (expectedSuite : String) (cert : DatasheetFitCert) : Verdict HwClause :=
  if (cert.suiteName == expectedSuite) && checkDatasheetFitSignoff cert then
    .ok
  else
    .refused (.datasheetCalibrationOrMarginViolation cert.suiteName) []

instance datasheetFitJudge : Obend.Judge String DatasheetFitCert where
  Clause := HwClause
  Meaning expectedSuite cert := ((cert.suiteName == expectedSuite) && checkDatasheetFitSignoff cert) = true
  check := checkDatasheetFitJudge
  sound := by
    intro _ o c h
    unfold checkDatasheetFitJudge at h
    by_cases hOk : ((c.suiteName == o) && checkDatasheetFitSignoff c) = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkDatasheetFitJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badDatasheetFitCert_refused :
    checkDatasheetFitJudge 0 "obend_74ls_hct_ina_calibrated" badDirect74HcFitCert =
      .refused (.datasheetCalibrationOrMarginViolation "obend_74ls_hct_ina_calibrated") [] :=
  rfl

def decodeDatasheetFitObj (s : String) : Except String String := do
  ensureWireFrame s
  return (extractStringField s "suite").getD "obend_74ls_hct_ina_calibrated"

def decodeDatasheetFitCert (s : String) : Except String DatasheetFitCert := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "calibrated"
  let base :=
    if mode == "74ls_to_74hc_direct" then badDirect74HcFitCert
    else if mode == "uncalibrated_drift" then badUncalibratedDriftFitCert
    else goldenDatasheetFitCert
  let pullup := (extractIntField s "pullupBoostMv").getD base.pullupBoostMv
  let minMargin := (extractIntField s "minMarginMv").getD base.minMarginMv
  let fanout := (extractNatField s "fanout").getD base.fanout
  let maxCalErr := (extractIntField s "maxCalErrMv").getD base.maxCalErrMv
  return { base with
    pullupBoostMv := pullup
    minMarginMv := minMargin
    fanout := fanout
    maxCalErrMv := maxCalErr }

/-- Registered `Obend.Judge.Format` for `datasheet-fit@1`. -/
def datasheetFitFormat : Format where
  name        := "datasheet-fit"
  version     := "1"
  Obj         := String
  Cert        := DatasheetFitCert
  judge       := datasheetFitJudge
  decodeObj   := decodeDatasheetFitObj
  decodeCert  := decodeDatasheetFitCert
  trust       := .kernel
  regime      := .decidable
  bad         := ("obend_74ls_hct_ina_calibrated", badDirect74HcFitCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badDatasheetFitCert_refused⟩

theorem datasheetFitFormat_sound {r : Nat} {obj cert : String}
    (h : datasheetFitFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeDatasheetFitObj obj = .ok o ∧ decodeDatasheetFitCert cert = .ok c ∧
      ((c.suiteName == o) && checkDatasheetFitSignoff c) = true :=
  datasheetFitFormat.checkBytes_sound h

theorem datasheetFitFormat_complete {o : String}
    (h : ∃ c : DatasheetFitCert, ((c.suiteName == o) && checkDatasheetFitSignoff c) = true) :
    ∃ c r, datasheetFitJudge.check r o c = .ok :=
  datasheetFitJudge.complete trivial h

/-! ## 8. Format 7: `rf-transceiver-signoff@1` (40m FT8 Ham Radio Transceiver, Tayloe IQ, VSWR & FCC Part 97 Judge) -/

/-- Judge check function for `rf-transceiver-signoff@1`. -/
def checkRfTransceiverJudge (_grade : Nat) (expectedBand : HamBand) (cert : RfTransceiverCert) : Verdict HwClause :=
  if (cert.band == expectedBand) && checkRfTransceiverSignoff cert then
    .ok
  else
    .refused (.rfTransceiverSignoffViolation cert.rigName) []

instance rfTransceiverJudge : Obend.Judge HamBand RfTransceiverCert where
  Clause := HwClause
  Meaning expectedBand cert := ((cert.band == expectedBand) && checkRfTransceiverSignoff cert) = true
  check := checkRfTransceiverJudge
  sound := by
    intro _ o c h
    unfold checkRfTransceiverJudge at h
    by_cases hOk : ((c.band == o) && checkRfTransceiverSignoff c) = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkRfTransceiverJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badRfTransceiverCert_refused :
    checkRfTransceiverJudge 0 .band40m unfilteredPaTransceiverCert =
      .refused (.rfTransceiverSignoffViolation "obend_qcx_unfiltered_pa") [] :=
  rfl

def decodeRfTransceiverObj (s : String) : Except String HamBand := do
  ensureWireFrame s
  let bandStr := (extractStringField s "band").getD "40m"
  if bandStr == "160m" then return .band160m
  else if bandStr == "80m" then return .band80m
  else if bandStr == "20m" then return .band20m
  else if bandStr == "2m" then return .band2m
  else if bandStr == "70cm" then return .band70cm
  else return .band40m

def decodeRfTransceiverCert (s : String) : Except String RfTransceiverCert := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "ft8_40m_golden"
  let base :=
    if mode == "unfiltered_pa_harmonics" then unfilteredPaTransceiverCert
    else if mode == "high_vswr_mismatch" then highVswrTransceiverCert
    else golden40mFt8TransceiverCert
  let freq := (extractNatField s "carrierFreqKhz").getD base.carrierFreqKhz
  let iqRej := (extractNatField s "iqRejectionTenthDb").getD base.iqRejectionTenthDb
  let rxNf := (extractNatField s "rxCascadedMilliNf").getD base.rxCascadedMilliNf
  let tjMk := (extractIntField s "paSteadyTjMk").getD base.paSteadyTjMk
  return { base with
    carrierFreqKhz := freq
    iqRejectionTenthDb := iqRej
    rxCascadedMilliNf := rxNf
    paSteadyTjMk := tjMk }

/-- Registered `Obend.Judge.Format` for `rf-transceiver-signoff@1`. -/
def rfTransceiverFormat : Format where
  name        := "rf-transceiver-signoff"
  version     := "1"
  Obj         := HamBand
  Cert        := RfTransceiverCert
  judge       := rfTransceiverJudge
  decodeObj   := decodeRfTransceiverObj
  decodeCert  := decodeRfTransceiverCert
  trust       := .kernel
  regime      := .decidable
  bad         := (.band40m, unfilteredPaTransceiverCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badRfTransceiverCert_refused⟩

theorem rfTransceiverFormat_sound {r : Nat} {obj cert : String}
    (h : rfTransceiverFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRfTransceiverObj obj = .ok o ∧ decodeRfTransceiverCert cert = .ok c ∧
      ((c.band == o) && checkRfTransceiverSignoff c) = true :=
  rfTransceiverFormat.checkBytes_sound h

theorem rfTransceiverFormat_complete {o : HamBand}
    (h : ∃ c : RfTransceiverCert, ((c.band == o) && checkRfTransceiverSignoff c) = true) :
    ∃ c r, rfTransceiverJudge.check r o c = .ok :=
  rfTransceiverJudge.complete trivial h

/-! ## 9. Format 8: `photonics-pic-signoff@1` (`SiEPIC 220nm SOI` / `IHP SG13G2 EPIC` Photonic IC Judge) -/

/-- Judge check function for `photonics-pic-signoff@1`: verifies waveguide geometry, 3 dB coupler
unitarity, critical microring coupling ($r = a$), minimum bend radius, and Free Spectral Range. -/
def checkPhotonicsPicJudge (_grade : Nat) (minFsrPm : Nat) (mrr : MicroringResonator) : Verdict HwClause :=
  if checkPhotonicDrc soi220StripWaveguide1550 coupler3dB mrr minFsrPm then
    .ok
  else
    .refused (.photonicsPicSignoffViolation mrr.ringName) []

instance photonicsPicJudge : Obend.Judge Nat MicroringResonator where
  Clause := HwClause
  Meaning minFsrPm mrr := checkPhotonicDrc soi220StripWaveguide1550 coupler3dB mrr minFsrPm = true
  check := checkPhotonicsPicJudge
  sound := by
    intro _ o c h
    unfold checkPhotonicsPicJudge at h
    by_cases hOk : checkPhotonicDrc soi220StripWaveguide1550 coupler3dB c o = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkPhotonicsPicJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badPhotonicsPic_refused :
    checkPhotonicsPicJudge 0 15000 leakyTightBendMicroring =
      .refused (.photonicsPicSignoffViolation "mrr_leaky_r2um") [] :=
  rfl

def decodePhotonicsObj (s : String) : Except String Nat := do
  match extractNatField s "minFsrPm" with
  | some v => return v
  | none =>
    let j ← Json.parse s
    return (j.getObjValAs? Nat "minFsrPm").toOption.getD 15000

def decodePhotonicsCert (s : String) : Except String MicroringResonator := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "golden"
  let base :=
    if mode == "tight_bend" then leakyTightBendMicroring
    else goldenSoi220Microring
  let bendNm := (extractNatField s "bendRadiusNm").getD base.bendRadiusNm
  let circUm := (extractNatField s "circumferenceUm").getD base.circumferenceUm
  let rSelf := (extractIntField s "rSelfPermille").getD base.rSelfPermille
  let aRt := (extractIntField s "aRoundTripPermille").getD base.aRoundTripPermille
  return { base with
    bendRadiusNm := bendNm
    circumferenceUm := circUm
    rSelfPermille := rSelf
    aRoundTripPermille := aRt }

/-- Registered `Obend.Judge.Format` for `photonics-pic-signoff@1`. -/
def photonicsPicFormat : Format where
  name        := "photonics-pic-signoff"
  version     := "1"
  Obj         := Nat
  Cert        := MicroringResonator
  judge       := photonicsPicJudge
  decodeObj   := decodePhotonicsObj
  decodeCert  := decodePhotonicsCert
  trust       := .kernel
  regime      := .decidable
  bad         := (15000, leakyTightBendMicroring)
  badGrade    := 0
  bad_refused := ⟨_, _, badPhotonicsPic_refused⟩

theorem photonicsPicFormat_sound {r : Nat} {obj cert : String}
    (h : photonicsPicFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodePhotonicsObj obj = .ok o ∧ decodePhotonicsCert cert = .ok c ∧
      checkPhotonicDrc soi220StripWaveguide1550 coupler3dB c o = true :=
  photonicsPicFormat.checkBytes_sound h

/-! ## 10. Format 9: `pcb-board-signoff@1` (4-Layer `Rogers RO4350B` + `FR-4` SDR / FPGA Carrier PCB Judge) -/

/-- Planted bad serpentine meander with uncompensated $6\,\text{mm}$ length mismatch ($36\,\text{ps}$ flight skew). -/
def badUnmatchedDdrMeander : SerpentineMeander :=
  { goldenDdrMeander with numSegments := 0 }

/-- Judge check function for `pcb-board-signoff@1`. -/
def checkPcbBoardJudge (_grade : Nat) (maxSkewFs : Nat) (meander : SerpentineMeander) : Verdict HwClause :=
  if checkPcbBoardSignoff goldenRf50OhmTrace goldenLvds100OhmPair meander 30000 maxSkewFs
      goldenPaSupplyRail goldenGndViaStitch goldenBoardClearance then
    .ok
  else
    .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") []

instance pcbBoardJudge : Obend.Judge Nat SerpentineMeander where
  Clause := HwClause
  Meaning maxSkewFs meander :=
    checkPcbBoardSignoff goldenRf50OhmTrace goldenLvds100OhmPair meander 30000 maxSkewFs
      goldenPaSupplyRail goldenGndViaStitch goldenBoardClearance = true
  check := checkPcbBoardJudge
  sound := by
    intro _ o c h
    unfold checkPcbBoardJudge at h
    by_cases hOk : checkPcbBoardSignoff goldenRf50OhmTrace goldenLvds100OhmPair c 30000 o
        goldenPaSupplyRail goldenGndViaStitch goldenBoardClearance = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkPcbBoardJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badPcbBoard_refused :
    checkPcbBoardJudge 0 50 badUnmatchedDdrMeander =
      .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") [] :=
  rfl

def decodePcbBoardObj (s : String) : Except String Nat := do
  match extractNatField s "maxSkewFs" with
  | some v => return v
  | none =>
    let j ← Json.parse s
    return (j.getObjValAs? Nat "maxSkewFs").toOption.getD 50

def decodePcbBoardCert (s : String) : Except String SerpentineMeander := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "golden"
  let base :=
    if mode == "skew_mismatch" then badUnmatchedDdrMeander
    else goldenDdrMeander
  let baseLen := (extractNatField s "baseLengthUm").getD base.baseLengthUm
  let nSeg := (extractNatField s "numSegments").getD base.numSegments
  let ampUm := (extractNatField s "meanderAmplitudeUm").getD base.meanderAmplitudeUm
  let spcUm := (extractNatField s "minLoopSpacingUm").getD base.minLoopSpacingUm
  return {
    baseLengthUm := baseLen
    numSegments := nSeg
    meanderAmplitudeUm := ampUm
    minLoopSpacingUm := spcUm }

/-- Registered `Obend.Judge.Format` for `pcb-board-signoff@1`. -/
def pcbBoardFormat : Format where
  name        := "pcb-board-signoff"
  version     := "1"
  Obj         := Nat
  Cert        := SerpentineMeander
  judge       := pcbBoardJudge
  decodeObj   := decodePcbBoardObj
  decodeCert  := decodePcbBoardCert
  trust       := .kernel
  regime      := .decidable
  bad         := (50, badUnmatchedDdrMeander)
  badGrade    := 0
  bad_refused := ⟨_, _, badPcbBoard_refused⟩

theorem pcbBoardFormat_sound {r : Nat} {obj cert : String}
    (h : pcbBoardFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodePcbBoardObj obj = .ok o ∧ decodePcbBoardCert cert = .ok c ∧
      checkPcbBoardSignoff goldenRf50OhmTrace goldenLvds100OhmPair c 30000 o
        goldenPaSupplyRail goldenGndViaStitch goldenBoardClearance = true :=
  pcbBoardFormat.checkBytes_sound h

/-! ## 11. Format 10: `agentic-eda-swap@1` (Smart-Contract Markdown Vault + 2D Footprint BOM Swap Judge) -/

/-- Boolean wrapper checking whether `judgeAgenticEdaProposal` admits `candidatePart` at `minMarginMv`. -/
def checkAgenticEdaSwapBool (minMarginMv : Int) (candidatePart : EdaVaultPart) : Bool :=
  judgeAgenticEdaProposal
    goldenEdaLaws
    goldenBaselinePart
    candidatePart
    lvcmos33ReceiverSpec
    minMarginMv
    goldenQfn16Courtyard
    goldenFreshDatasheetCite
    "procurement_scout"
    defaultEdaFacts == .admitted

/-- Judge check function for `agentic-eda-swap@1`. -/
def checkAgenticEdaJudge (_grade : Nat) (minMarginMv : Int) (candidatePart : EdaVaultPart) : Verdict HwClause :=
  if checkAgenticEdaSwapBool minMarginMv candidatePart then
    .ok
  else
    .refused (.agenticEdaSwapViolation candidatePart.pageName) []

instance agenticEdaJudge : Obend.Judge Int EdaVaultPart where
  Clause := HwClause
  Meaning minMarginMv candidatePart := checkAgenticEdaSwapBool minMarginMv candidatePart = true
  check := checkAgenticEdaJudge
  sound := by
    intro _ o c h
    unfold checkAgenticEdaJudge at h
    by_cases hOk : checkAgenticEdaSwapBool o c = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkAgenticEdaJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

theorem badAgenticEdaSwap_refused :
    checkAgenticEdaJudge 0 400 overbudgetSecondSourcePart =
      .refused (.agenticEdaSwapViolation "U4_LDO") [] := by
  decide +kernel

def decodeAgenticEdaObj (s : String) : Except String Int := do
  match extractIntField s "minMarginMv" with
  | some v => return v
  | none =>
    let j ← Json.parse s
    return (j.getObjValAs? Int "minMarginMv").toOption.getD 400

def decodeAgenticEdaCert (s : String) : Except String EdaVaultPart := do
  ensureWireFrame s
  let mode := (extractStringField s "mode").getD "golden"
  let base :=
    if mode == "overbudget" then overbudgetSecondSourcePart
    else goldenSecondSourcePart
  let voh := (extractNatField s "vohMinMv").getD base.vohMinMv
  let vih := (extractNatField s "vihMinMv").getD base.vihMinMv
  let vol := (extractNatField s "volMaxMv").getD base.volMaxMv
  let vil := (extractNatField s "vilMaxMv").getD base.vilMaxMv
  let tempMc := (extractNatField s "maxTempMc").getD base.maxTempMc
  let drcErr := (extractNatField s "drcErrors").getD base.drcErrors
  let cost := (extractNatField s "costCents").getD base.costCents
  return { base with
    vohMinMv := voh
    vihMinMv := vih
    volMaxMv := vol
    vilMaxMv := vil
    maxTempMc := tempMc
    drcErrors := drcErr
    costCents := cost }

/-- Registered `Obend.Judge.Format` for `agentic-eda-swap@1`. -/
def agenticEdaFormat : Format where
  name        := "agentic-eda-swap"
  version     := "1"
  Obj         := Int
  Cert        := EdaVaultPart
  judge       := agenticEdaJudge
  decodeObj   := decodeAgenticEdaObj
  decodeCert  := decodeAgenticEdaCert
  trust       := .kernel
  regime      := .decidable
  bad         := (400, overbudgetSecondSourcePart)
  badGrade    := 0
  bad_refused := ⟨_, _, badAgenticEdaSwap_refused⟩

theorem agenticEdaFormat_sound {r : Nat} {obj cert : String}
    (h : agenticEdaFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeAgenticEdaObj obj = .ok o ∧ decodeAgenticEdaCert cert = .ok c ∧
      checkAgenticEdaSwapBool o c = true :=
  agenticEdaFormat.checkBytes_sound h

/-! ## 12. Format 11: `hw-binary-cbor@1` (RFC 8949 Binary CBOR Hardware Certificate Judge via `BinaryCodec`) -/

/-- Judge check function for `hw-binary-cbor@1`: checks domain match and runs `verifyBinaryHwCert`
    on the decoded binary CBOR parameters `(p0 .. p5)`. -/
def checkBinaryCborJudge (_grade : Nat) (expectedDom : HwCertDomain) (cert : BinaryHwCert) : Verdict HwClause :=
  if (cert.domain == expectedDom) && verifyBinaryHwCert cert then
    .ok
  else
    .refused (.binaryCborCertViolation cert.domain.toCode) []

instance binaryCborJudge : Obend.Judge HwCertDomain BinaryHwCert where
  Clause := HwClause
  Meaning expectedDom cert := ((cert.domain == expectedDom) && verifyBinaryHwCert cert) = true
  check := checkBinaryCborJudge
  sound := by
    intro _ o c h
    unfold checkBinaryCborJudge at h
    by_cases hOk : ((c.domain == o) && verifyBinaryHwCert c) = true
    · exact hOk
    · simp [hOk] at h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkBinaryCborJudge, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

/-- Planted bad binary CBOR certificate: PnR with 100ps clock period (fails STA slack). -/
def badBinaryPnrCert : BinaryHwCert :=
  { goldenBinaryPnrCert with p5 := 100 }

theorem badBinaryCborCert_refused :
    checkBinaryCborJudge 0 .pnr badBinaryPnrCert =
      .refused (.binaryCborCertViolation 1) [] := by
  decide +kernel

/-- Decode hex-encoded byte string (`"d90bed87..."`) into `List UInt8` for text-bridged Format tests,
    while `verifyBinaryCborBytes` operates directly on raw `ByteArray` / `List UInt8`. -/
def hexCharVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest =>
    match hexCharVal hi, hexCharVal lo, decodeHexChars rest with
    | some h, some l, some tail => some (UInt8.ofNat (h * 16 + l) :: tail)
    | _, _, _ => none
  | [_] => none

def encodeHexBytes (bytes : List UInt8) : String :=
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList (bytes.flatMap fun b =>
    let n := b.toNat
    [hexDigits.getD (n / 16) '0', hexDigits.getD (n % 16) '0'])

def decodeBinaryCborObj (s : String) : Except String HwCertDomain :=
  match s.trimAscii.toString.toNat? with
  | some n =>
    match HwCertDomain.fromCode n with
    | some d => .ok d
    | none => .error s!"unknown binary CBOR domain id: {n}"
  | none => .ok .pnr

def decodeBinaryCborCert (s : String) : Except String BinaryHwCert := do
  let trimmed := s.trimAscii.toString
  match decodeHexChars trimmed.toList with
  | some rawBytes =>
    match decodeBinaryHwCert rawBytes with
    | some cert => .ok cert
    | none => .error "invalid RFC 8949 CBOR BinaryHwCert frame"
  | none => .error "invalid hex-encoded CBOR byte stream"

/-- Judge check function for variable-length RFC 8949 CBOR tape/mesh certificates (`BinaryTapeCert`). -/
def checkBinaryTapeCert (_grade : Nat) (expectedDom : HwCertDomain) (cert : BinaryTapeCert) : Verdict HwClause :=
  if (cert.domain == expectedDom) && verifyBinaryTapeCert cert then
    .ok
  else
    .refused (.binaryCborCertViolation cert.domain.toCode) []

theorem checkBinaryTapeCert_sound {grade : Nat} {expectedDom : HwCertDomain} {cert : BinaryTapeCert}
    (h : checkBinaryTapeCert grade expectedDom cert = .ok) :
    ((cert.domain == expectedDom) && verifyBinaryTapeCert cert) = true := by
  unfold checkBinaryTapeCert at h
  by_cases hOk : ((cert.domain == expectedDom) && verifyBinaryTapeCert cert) = true
  · exact hOk
  · simp [hOk] at h

instance binaryTapeJudge : Obend.Judge HwCertDomain BinaryTapeCert where
  Clause := HwClause
  Meaning expectedDom cert := ((cert.domain == expectedDom) && verifyBinaryTapeCert cert) = true
  check := checkBinaryTapeCert
  sound := by
    intro _ _ _ h
    exact checkBinaryTapeCert_sound h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ hRef
    cases hRef
  Fragment _ := True
  complete := by
    intro o _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkBinaryTapeCert, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

def badBinaryTapeCert : BinaryTapeCert :=
  { goldenBinaryFemmTapeCert with metric0 := 999 }

theorem badBinaryTapeCert_refused :
    checkBinaryTapeCert 0 .magnetics badBinaryTapeCert =
      .refused (.binaryCborCertViolation 10) [] := by
  decide +kernel

def decodeBinaryTapeCertHex (s : String) : Except String BinaryTapeCert := do
  let trimmed := s.trimAscii.toString
  match decodeHexChars trimmed.toList with
  | some rawBytes =>
    match decodeBinaryTapeCert rawBytes with
    | some cert => .ok cert
    | none => .error "invalid RFC 8949 CBOR BinaryTapeCert frame"
  | none => .error "invalid hex-encoded CBOR byte stream"

def binaryTapeFormat : Format where
  name        := "hw-binary-tape-cbor"
  version     := "1"
  Obj         := HwCertDomain
  Cert        := BinaryTapeCert
  judge       := binaryTapeJudge
  decodeObj   := decodeBinaryCborObj
  decodeCert  := decodeBinaryTapeCertHex
  trust       := .kernel
  regime      := .decidable
  bad         := (.magnetics, badBinaryTapeCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badBinaryTapeCert_refused⟩

theorem binaryTapeFormat_sound {r : Nat} {obj cert : String}
    (h : binaryTapeFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeBinaryCborObj obj = .ok o ∧ decodeBinaryTapeCertHex cert = .ok c ∧
      ((c.domain == o) && verifyBinaryTapeCert c) = true :=
  binaryTapeFormat.checkBytes_sound h

/-- Direct raw-byte binary CBOR judge entry point (supports both 39-byte `BinaryHwCert` `0x87`
    and variable-length `BinaryTapeCert` `0x9A` frames, with zero JSON). -/
def verifyRawBinaryCborCert (expectedDom : HwCertDomain) (raw : ByteArray) : Verdict HwClause :=
  match decodeFromByteArray (α := BinaryHwCert) raw with
  | some cert => checkBinaryCborJudge 0 expectedDom cert
  | none =>
    match decodeFromByteArray (α := BinaryTapeCert) raw with
    | some tapeCert => checkBinaryTapeCert 0 expectedDom tapeCert
    | none => .refused (.binaryCborCertViolation expectedDom.toCode) []

/-- Registered `Obend.Judge.Format` for `hw-binary-cbor@1`. -/
def binaryCborFormat : Format where
  name        := "hw-binary-cbor"
  version     := "1"
  Obj         := HwCertDomain
  Cert        := BinaryHwCert
  judge       := binaryCborJudge
  decodeObj   := decodeBinaryCborObj
  decodeCert  := decodeBinaryCborCert
  trust       := .kernel
  regime      := .decidable
  bad         := (.pnr, badBinaryPnrCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badBinaryCborCert_refused⟩

theorem binaryCborFormat_sound {r : Nat} {obj cert : String}
    (h : binaryCborFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeBinaryCborObj obj = .ok o ∧ decodeBinaryCborCert cert = .ok c ∧
      ((c.domain == o) && verifyBinaryHwCert c) = true :=
  binaryCborFormat.checkBytes_sound h

/-- Complete list of registered hardware, FabuBlox, `wafer.space`, datasheet-fit, RF, photonics, PCB, agentic EDA, and binary CBOR formats. -/
def hardwareFormats : List Format :=
  [ hwSynthFormat
  , hwRetimeFormat
  , hwPnrFormat
  , fabubloxFormat
  , waferSpaceFormat
  , datasheetFitFormat
  , rfTransceiverFormat
  , photonicsPicFormat
  , pcbBoardFormat
  , agenticEdaFormat
  , binaryCborFormat
  , binaryTapeFormat ]

/-- Look up a hardware certificate format by `name@version` string (e.g. `"hw-pnr-bitstream@1"`). -/
def findHardwareFormat? (tag : String) : Option Format :=
  hardwareFormats.find? (fun f => s!"{f.name}@{f.version}" == tag)

/-- **No-Bypass Verification for `verifyRawBinaryCborCert` on Fixed-Arity `.pnr` (`verifyRawBinaryCborCert_refuses_pnr_tape_bypass`)**:
Submitting a 1-word variable-length `BinaryTapeCert` claiming `.pnr` to `verifyRawBinaryCborCert .pnr`
is strictly refused (`.refused (.binaryCborCertViolation 1) []`). -/
theorem verifyRawBinaryCborCert_refuses_pnr_tape_bypass :
    let fakePnrTape : BinaryTapeCert := { domain := .pnr, metric0 := 100, metric1 := 100, words := [1] }
    let rawBytes := ByteArray.mk (encodeBinaryTapeCert fakePnrTape).toArray
    verifyRawBinaryCborCert .pnr rawBytes = .refused (.binaryCborCertViolation 1) [] := by
  decide +kernel

/-- **Kernel Verification of Numeric Wire Field Extraction (`extractNatField_and_extractIntField_verified`)**:
Verifies that `extractNatField` and `extractIntField` extract unsigned and signed numeric parameters
from JSON and key-value wire strings, and that overriding numeric fields in `decodeWaferSpaceCert`,
`decodePhotonicsCert`, `decodePcbBoardCert`, and `decodeAgenticEdaCert` triggers judge refusal on
out-of-spec numeric values even when `"mode": "golden"` is set! -/
theorem extractNatField_and_extractIntField_verified :
    extractNatField "{\"mode\": \"golden\", \"antennaRatio\": 2400}" "antennaRatio" = some 2400 ∧
    extractIntField "{\"mode\": \"golden\", \"minMarginMv\": -150}" "minMarginMv" = some (-150) ∧
    extractNatField "bendRadiusNm=2000,circumferenceUm=50" "bendRadiusNm" = some 2000 ∧
    (let mrr : MicroringResonator :=
       { goldenSoi220Microring with
         bendRadiusNm := (extractNatField "{\"mode\": \"golden\", \"bendRadiusNm\": 2000}" "bendRadiusNm").getD goldenSoi220Microring.bendRadiusNm }
     checkPhotonicsPicJudge 0 15000 mrr = .refused (.photonicsPicSignoffViolation goldenSoi220Microring.ringName) []) ∧
    (let meander : SerpentineMeander :=
       { goldenDdrMeander with
         numSegments := (extractNatField "{\"mode\": \"golden\", \"numSegments\": 0}" "numSegments").getD goldenDdrMeander.numSegments }
     checkPcbBoardJudge 0 50 meander = .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") []) := by
  decide +kernel

/-- **Identifier-Boundary Non-Collision & End-to-End Decoder Verification
(`extractNatField_token_boundary_and_decoders_verified`)**:
1. `"fanout"` does *not* match the suffix of `"max_fanout"` in JSON or key-value wire strings,
2. `decodePhotonicsCert` and `decodePcbBoardCert` decode both JSON and key-value wire strings
   directly in the Lean 4 kernel (`decide +kernel`) and reject out-of-spec numeric parameters even
   when `mode=golden` is specified. -/
theorem extractNatField_token_boundary_and_decoders_verified :
    extractNatField "{\"max_fanout\": 99, \"mode\": \"calibrated\"}" "fanout" = none ∧
    extractNatField "max_fanout=99,mode=calibrated" "fanout" = none ∧
    extractIntField "{\"extra_minMarginMv\": -500}" "minMarginMv" = none ∧
    (match decodePhotonicsCert "mode=golden,bendRadiusNm=2000,circumferenceUm=50" with
     | .ok c => c.bendRadiusNm == 2000 && c.circumferenceUm == 50 &&
       checkPhotonicsPicJudge 0 15000 c == .refused (.photonicsPicSignoffViolation goldenSoi220Microring.ringName) []
     | .error _ => false) = true ∧
    (match decodePcbBoardCert "mode=golden,numSegments=0" with
     | .ok c => c.numSegments == 0 &&
       checkPcbBoardJudge 0 50 c == .refused (.pcbBoardSignoffViolation "DDR_CLK_MEANDER") []
     | .error _ => false) = true := by
  decide +kernel

end Obend.Hardware.Judge
