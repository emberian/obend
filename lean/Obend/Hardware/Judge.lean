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
import all Obend.Judge.Class
public import Obend.Receipt
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.DRC
public import Obend.Hardware.Analog
public import Obend.Hardware.Datasheet
public import Obend.Hardware.Circuits
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
open Obend.Hardware.DRC Obend.Hardware.Analog
open Obend.Hardware.Datasheet Obend.Hardware.Circuits
open Obend.Hardware.ReductionMachine Obend.Hardware.DSP Obend.Hardware.AgenticEDA
open Obend.Hardware.Codec
set_option autoImplicit false

/-! ## 1. Refusal Clauses for Hardware, Datasheet, Agentic EDA & Binary CBOR Judges -/

/-- Refusal vocabulary across the surviving hardware, datasheet, agentic EDA & binary CBOR certificate judges. -/
inductive HwClause where
  | rtlInvalidDagOrCdc (modName : String)
  | retimeInvalidLagOrTiming (graphName : String)
  | pnrCollisionShortOrTiming (designName : String)
  | datasheetCalibrationOrMarginViolation (suiteName : String)
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
  wires      := [{ wireIdx := 0, name := "w0", expr := .alu .add (.wireRef 0) (.const 1#64) }]
  regs       := []
  outputs    := [{ name := "out0", expr := .wireRef 0 }]

theorem badLoopRtlModule_refused :
    checkRtlSynth 0 "bad_loop_mod" badLoopRtlModule =
      .refused (.rtlInvalidDagOrCdc "bad_loop_mod") [] := by
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

/-- Require a string field `field` in wire string `s`, returning `.error` if absent. -/
def requireStringField (s field : String) : Except String String :=
  match extractStringField s field with
  | some v => .ok v
  | none   => .error s!"missing required string field '{field}'"

/-- Require a natural-number field `field` in wire string `s`, returning `.error` if absent. -/
def requireNatField (s field : String) : Except String Nat :=
  match extractNatField s field with
  | some n => .ok n
  | none   => .error s!"missing required nat field '{field}'"

/-- Require a signed-integer field `field` in wire string `s`, returning `.error` if absent. -/
def requireIntField (s field : String) : Except String Int :=
  match extractIntField s field with
  | some v => .ok v
  | none   => .error s!"missing required int field '{field}'"

/-- Decode a JSON or wire object string for `hw-rtl-synth@1` (`{"module": NAME}`). -/
def decodeRtlSynthObj (s : String) : Except String String := do
  ensureWireFrame s
  requireStringField s "module"

/-- Decode a single `RtlExpr` operand from `<prefix>Kind` and `<prefix>Val`. -/
def decodeRtlOperand (s prefixStr : String) : Except String RtlExpr := do
  let kind ← requireStringField s (prefixStr ++ "Kind")
  let val  ← requireNatField s (prefixStr ++ "Val")
  if kind == "const" then return .const (BitVec.ofNat 64 val)
  else if kind == "inputPort" then return .inputPort val
  else if kind == "wireRef" then return .wireRef val
  else if kind == "regRead" then return .regRead val
  else if kind == "addInputWire" then return .alu .add (.inputPort 0) (.wireRef val)
  else .error s!"unknown RtlExpr operand kind '{kind}'"

/-- Decode an `RtlAluOp` from its wire string token. -/
def decodeRtlAluOp (opStr : String) : Except String RtlAluOp :=
  if opStr == "add" then .ok .add
  else if opStr == "sub" then .ok .sub
  else if opStr == "mul" then .ok .mul
  else if opStr == "bitAnd" then .ok .bitAnd
  else if opStr == "bitOr" then .ok .bitOr
  else if opStr == "bitXor" then .ok .bitXor
  else if opStr == "shl" then .ok .shl
  else if opStr == "lshr" then .ok .lshr
  else if opStr == "ashr" then .ok .ashr
  else if opStr == "eq" then .ok .eq
  else if opStr == "ult" then .ok .ult
  else if opStr == "slt" then .ok .slt
  else if opStr == "qmul32" then .ok .qmul32
  else .error s!"unknown RtlAluOp '{opStr}'"

/-- Decode a `ClkDomain` from its wire string token. -/
def decodeClockDomain (domStr : String) : Except String ClkDomain :=
  if domStr == "coreClk" then .ok .coreClk
  else if domStr == "axiIoClk" then .ok .axiIoClk
  else if domStr == "cfgJtagClk" then .ok .cfgJtagClk
  else .error s!"unknown ClkDomain '{domStr}'"

/-- Kernel-reducible decimal digit character for `d < 10`. -/
def rtlDigitChar (d : Nat) : Char :=
  Char.ofNat ('0'.toNat + d)

/-- Kernel-reducible fuel-bounded base-10 digit converter on `Nat`. -/
def rtlNatToDigitsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let acc' := rtlDigitChar (n % 10) :: acc
    let q := n / 10
    if q == 0 then acc' else rtlNatToDigitsAux fuel q acc'

/-- Kernel-reducible `Nat → String` conversion (`@[expose]`). -/
def rtlNatToStr (n : Nat) : String :=
  String.ofList (rtlNatToDigitsAux (n + 1) n [])

/-- Kernel-reducible comma-join on `List String` (`@[expose]`). -/
def rtlJoinComma : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "," ++ rtlJoinComma rest

/-- Decode `numWires` wire assignments (`wire0Idx`, `wire0Name`, `wire0Op`, ...) from `s`. -/
def decodeRtlWiresAux (s : String) (idx fuel : Nat) (acc : List WireAssign) :
    Except String (List WireAssign) :=
  match fuel with
  | 0 => .ok acc
  | k + 1 => do
    let pfx := "wire" ++ rtlNatToStr idx
    let wIdx  ← requireNatField s (pfx ++ "Idx")
    let wName ← requireStringField s (pfx ++ "Name")
    let wOp   ← requireStringField s (pfx ++ "Op")
    let expr ←
      if wOp == "const" then do
        let v ← requireNatField s (pfx ++ "Val")
        pure (.const (BitVec.ofNat 64 v))
      else if wOp == "inputPort" then do
        let v ← requireNatField s (pfx ++ "Val")
        pure (.inputPort v)
      else if wOp == "wireRef" then do
        let v ← requireNatField s (pfx ++ "Val")
        pure (.wireRef v)
      else if wOp == "regRead" then do
        let v ← requireNatField s (pfx ++ "Val")
        pure (.regRead v)
      else do
        let aluOp ← decodeRtlAluOp wOp
        let lhs   ← decodeRtlOperand s (pfx ++ "Lhs")
        let rhs   ← decodeRtlOperand s (pfx ++ "Rhs")
        pure (.alu aluOp lhs rhs)
    decodeRtlWiresAux s (idx + 1) k (acc ++ [{ wireIdx := wIdx, name := wName, expr := expr }])

/-- Decode `numRegs` register specifications (`reg0Idx`, `reg0Name`, `reg0Domain`, `reg0Sync`,
`reg0NextKind`, `reg0NextVal`) from `s`. -/
def decodeRtlRegsAux (s : String) (idx fuel : Nat) (acc : List RegSpec) :
    Except String (List RegSpec) :=
  match fuel with
  | 0 => .ok acc
  | k + 1 => do
    let pfx := "reg" ++ rtlNatToStr idx
    let rIdx    ← requireNatField s (pfx ++ "Idx")
    let rName   ← requireStringField s (pfx ++ "Name")
    let domStr  ← requireStringField s (pfx ++ "Domain")
    let dom     ← decodeClockDomain domStr
    let syncNat ← requireNatField s (pfx ++ "Sync")
    let nextExp ← decodeRtlOperand s (pfx ++ "Next")
    let r : RegSpec :=
      { regIdx         := rIdx
      , name           := rName
      , domain         := dom
      , resetKind      := .resetFree
      , isSynchronizer := syncNat != 0
      , nextExpr       := nextExp }
    decodeRtlRegsAux s (idx + 1) k (acc ++ [r])

/-- Decode a certificate string for `hw-rtl-synth@1`: parses explicit `RtlModule` wire,
register, clock-domain, and output definitions, failing with `.error` if any required field
is absent (zero hardcoded `golden` module fallback!). -/
def decodeRtlSynthCert (s : String) : Except String RtlModule := do
  ensureWireFrame s
  let name      ← requireStringField s "module"
  let inputPort ← requireStringField s "inputPort"
  let numWires  ← requireNatField s "numWires"
  let wires     ← decodeRtlWiresAux s 0 numWires []
  let numRegs   ← requireNatField s "numRegs"
  let regs      ← decodeRtlRegsAux s 0 numRegs []
  let outName   ← requireStringField s "outputName"
  let outWire   ← requireNatField s "outputWire"
  return {
    name       := name
    inputNames := [inputPort]
    wires      := wires
    regs       := regs
    outputs    := [{ name := outName, expr := .wireRef outWire }]
  }

/-- Encode a module name `modName` into a canonical JSON wire object string for `hw-rtl-synth@1` / `rtl-synth@1`. -/
def encodeRtlSynthObj (modName : String) : String :=
  "{\"module\":\"" ++ modName ++ "\"}"

/-- Encode an `RtlAluOp` to its canonical wire string token inverting `decodeRtlAluOp`. -/
def encodeRtlAluOp : RtlAluOp → String
  | .add    => "add"
  | .sub    => "sub"
  | .mul    => "mul"
  | .bitAnd => "bitAnd"
  | .bitOr  => "bitOr"
  | .bitXor => "bitXor"
  | .shl    => "shl"
  | .lshr   => "lshr"
  | .ashr   => "ashr"
  | .eq     => "eq"
  | .ult    => "ult"
  | .slt    => "slt"
  | .qmul32 => "qmul32"

@[simp] theorem decodeRtlAluOp_encodeRtlAluOp (op : RtlAluOp) :
    decodeRtlAluOp (encodeRtlAluOp op) = .ok op := by
  cases op <;> rfl

/-- Encode a `ClkDomain` to its canonical wire string token inverting `decodeClockDomain`. -/
def encodeClockDomain : ClkDomain → String
  | .coreClk    => "coreClk"
  | .axiIoClk   => "axiIoClk"
  | .cfgJtagClk => "cfgJtagClk"

@[simp] theorem decodeClockDomain_encodeClockDomain (dom : ClkDomain) :
    decodeClockDomain (encodeClockDomain dom) = .ok dom := by
  cases dom <;> rfl

/-- Encode a single `RtlExpr` operand as `<prefix>Kind` and `<prefix>Val` JSON fields inverting `decodeRtlOperand`. -/
def encodeRtlOperand (prefixStr : String) : RtlExpr → String
  | .const v       => "\"" ++ prefixStr ++ "Kind\":\"const\",\"" ++ prefixStr ++ "Val\":" ++ rtlNatToStr v.toNat
  | .inputPort idx => "\"" ++ prefixStr ++ "Kind\":\"inputPort\",\"" ++ prefixStr ++ "Val\":" ++ rtlNatToStr idx
  | .wireRef idx   => "\"" ++ prefixStr ++ "Kind\":\"wireRef\",\"" ++ prefixStr ++ "Val\":" ++ rtlNatToStr idx
  | .regRead idx   => "\"" ++ prefixStr ++ "Kind\":\"regRead\",\"" ++ prefixStr ++ "Val\":" ++ rtlNatToStr idx
  | .alu .add (.inputPort 0) (.wireRef idx) =>
    "\"" ++ prefixStr ++ "Kind\":\"addInputWire\",\"" ++ prefixStr ++ "Val\":" ++ rtlNatToStr idx
  | _              => "\"" ++ prefixStr ++ "Kind\":\"const\",\"" ++ prefixStr ++ "Val\":0"

/-- Encode a single `WireAssign` at wire table position `idx` inverting `decodeRtlWiresAux`. -/
def encodeRtlWire (idx : Nat) (w : WireAssign) : String :=
  let pfx := "wire" ++ rtlNatToStr idx
  let base := "\"" ++ pfx ++ "Idx\":" ++ rtlNatToStr w.wireIdx ++ ",\"" ++ pfx ++ "Name\":\"" ++ w.name ++ "\""
  match w.expr with
  | .const v =>
    base ++ ",\"" ++ pfx ++ "Op\":\"const\",\"" ++ pfx ++ "Val\":" ++ rtlNatToStr v.toNat
  | .inputPort p =>
    base ++ ",\"" ++ pfx ++ "Op\":\"inputPort\",\"" ++ pfx ++ "Val\":" ++ rtlNatToStr p
  | .wireRef r =>
    base ++ ",\"" ++ pfx ++ "Op\":\"wireRef\",\"" ++ pfx ++ "Val\":" ++ rtlNatToStr r
  | .regRead r =>
    base ++ ",\"" ++ pfx ++ "Op\":\"regRead\",\"" ++ pfx ++ "Val\":" ++ rtlNatToStr r
  | .alu op lhs rhs =>
    base ++ ",\"" ++ pfx ++ "Op\":\"" ++ encodeRtlAluOp op ++ "\"," ++
      encodeRtlOperand (pfx ++ "Lhs") lhs ++ "," ++ encodeRtlOperand (pfx ++ "Rhs") rhs
  | _ =>
    base ++ ",\"" ++ pfx ++ "Op\":\"const\",\"" ++ pfx ++ "Val\":0"

/-- Encode a list of `WireAssign` entries starting at index `idx`. -/
def encodeRtlWiresAux (idx : Nat) : List WireAssign → List String
  | [] => []
  | w :: ws => encodeRtlWire idx w :: encodeRtlWiresAux (idx + 1) ws

/-- Encode a single `RegSpec` at register table position `idx` inverting `decodeRtlRegsAux`. -/
def encodeRtlReg (idx : Nat) (r : RegSpec) : String :=
  let pfx := "reg" ++ rtlNatToStr idx
  let syncVal : Nat := if r.isSynchronizer then 1 else 0
  "\"" ++ pfx ++ "Idx\":" ++ rtlNatToStr r.regIdx ++
  ",\"" ++ pfx ++ "Name\":\"" ++ r.name ++
  "\",\"" ++ pfx ++ "Domain\":\"" ++ encodeClockDomain r.domain ++
  "\",\"" ++ pfx ++ "Sync\":" ++ rtlNatToStr syncVal ++
  "," ++ encodeRtlOperand (pfx ++ "Next") r.nextExpr

/-- Encode a list of `RegSpec` entries starting at index `idx`. -/
def encodeRtlRegsAux (idx : Nat) : List RegSpec → List String
  | [] => []
  | r :: rs => encodeRtlReg idx r :: encodeRtlRegsAux (idx + 1) rs

/-- True if `e` is an atomic operand directly representable by `encodeRtlOperand` / `decodeRtlOperand`. -/
def isFlatRtlOperand : RtlExpr → Bool
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .alu .add (.inputPort 0) (.wireRef _) => true
  | _ => false

/-- True if `w.expr` is directly representable as a single flat wire entry in `decodeRtlWiresAux`. -/
def isFlatWireAssign (w : WireAssign) : Bool :=
  match w.expr with
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .alu _ lhs rhs => isFlatRtlOperand lhs && isFlatRtlOperand rhs
  | _ => false

/-- Flatten a potentially nested `RtlExpr` into topological 3-address `WireAssign` entries,
returning `(updatedWires, rootWireIdx)`. -/
def flattenRtlExprAux (numInputs numRegs : Nat) (wireMap : List (Nat × Nat)) :
    RtlExpr → List WireAssign → (List WireAssign × Nat)
  | .const v, acc =>
    let idx := acc.length
    (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .const v }], idx)
  | .inputPort p, acc =>
    let pSafe := if p < numInputs then p else 0
    let idx := acc.length
    (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .inputPort pSafe }], idx)
  | .wireRef r, acc =>
    let mapped := (wireMap.lookup r).getD 0
    let safeRef := if mapped < acc.length then mapped else 0
    if acc.isEmpty then
      (acc ++ [{ wireIdx := 0, name := "w0", expr := .const 0#64 }], 0)
    else
      (acc, safeRef)
  | .regRead r, acc =>
    let idx := acc.length
    if r < numRegs then
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .regRead r }], idx)
    else
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .const 0#64 }], idx)
  | .alu op lhs rhs, acc =>
    let (acc1, lIdx) := flattenRtlExprAux numInputs numRegs wireMap lhs acc
    let (acc2, rIdx) := flattenRtlExprAux numInputs numRegs wireMap rhs acc1
    let idx := acc2.length
    (acc2 ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .alu op (.wireRef lIdx) (.wireRef rIdx) }], idx)
  | .mux c t f, acc =>
    let (acc1, cIdx) := flattenRtlExprAux numInputs numRegs wireMap c acc
    let (acc2, tIdx) := flattenRtlExprAux numInputs numRegs wireMap t acc1
    let (acc3, fIdx) := flattenRtlExprAux numInputs numRegs wireMap f acc2
    let idx1 := acc3.length
    let w1 : WireAssign := { wireIdx := idx1, name := "w" ++ rtlNatToStr idx1, expr := .alu .bitOr (.wireRef cIdx) (.wireRef tIdx) }
    let idx2 := idx1 + 1
    let w2 : WireAssign := { wireIdx := idx2, name := "w" ++ rtlNatToStr idx2, expr := .alu .bitXor (.wireRef idx1) (.wireRef fIdx) }
    (acc3 ++ [w1, w2], idx2)
  | .bitNot a, acc =>
    let (acc1, aIdx) := flattenRtlExprAux numInputs numRegs wireMap a acc
    let idx := acc1.length
    (acc1 ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := .alu .bitXor (.wireRef aIdx) (.const 0xFFFFFFFFFFFFFFFF#64) }], idx)
  | .resize op a, acc =>
    -- A width operator as 3-address ALU wires: masks, a shift, and for `sext` the
    -- `((x & m_f) ^ s) - s` sign-extension identity with `s = 2^(f-1)`.
    let (acc1, aIdx) := flattenRtlExprAux numInputs numRegs wireMap a acc
    let mkW (acc : List WireAssign) (e : RtlExpr) : List WireAssign × Nat :=
      let idx := acc.length
      (acc ++ [{ wireIdx := idx, name := "w" ++ rtlNatToStr idx, expr := e }], idx)
    let mask (w : Nat) : RtlExpr := .const (BitVec.ofNat 64 (2 ^ (min w 64) - 1))
    match op with
    | .zext _ => (acc1, aIdx)
    | .trunc w => mkW acc1 (.alu .bitAnd (.wireRef aIdx) (mask w))
    | .slice hi lo =>
      let (acc2, sIdx) := mkW acc1 (.alu .lshr (.wireRef aIdx) (.const (BitVec.ofNat 64 lo)))
      mkW acc2 (.alu .bitAnd (.wireRef sIdx) (mask (hi + 1 - lo)))
    | .sext f t =>
      let s : RtlExpr := .const (BitVec.ofNat 64 (2 ^ (f - 1)))
      let (acc2, i1) := mkW acc1 (.alu .bitAnd (.wireRef aIdx) (mask f))
      let (acc3, i2) := mkW acc2 (.alu .bitXor (.wireRef i1) s)
      let (acc4, i3) := mkW acc3 (.alu .sub (.wireRef i2) s)
      mkW acc4 (.alu .bitAnd (.wireRef i3) (mask t))

/-- Flatten a list of `WireAssign` entries into topological 3-address `WireAssign` entries. -/
def flattenWireListAux (numInputs numRegs : Nat) :
    List WireAssign → List (Nat × Nat) → List WireAssign → (List WireAssign × List (Nat × Nat))
  | [], wireMap, acc => (acc, wireMap)
  | w :: ws, wireMap, acc =>
    let (acc', rootIdx) := flattenRtlExprAux numInputs numRegs wireMap w.expr acc
    flattenWireListAux numInputs numRegs ws ((w.wireIdx, rootIdx) :: wireMap) acc'

/-- Normalize an `RtlModule` so that all wire expressions are flat 3-address operations,
it has a single primary input name and single primary output port, and it is ready for
exact wire encoding/decoding via `encodeRtlSynthCert` / `decodeRtlSynthCert`.
If `m` is already in flat wire-frame form, returns `m` unchanged. -/
def normalizeRtlModuleForWire (m : RtlModule) : RtlModule :=
  let alreadyFlat :=
    m.inputNames.length == 1 &&
    m.wires.all isFlatWireAssign &&
    (match m.outputs with
     | [⟨_, .wireRef w, _⟩] => (m.wires.isEmpty && w == 0) || w < m.wires.length
     | _ => false)
  if alreadyFlat then
    m
  else
    let inPort := match m.inputNames with | h :: _ => h | [] => "arg"
    let (flatWires0, wireMap) := flattenWireListAux 1 m.regs.length m.wires [] []
    let flatWires :=
      if flatWires0.isEmpty then
        [{ wireIdx := 0, name := "w0", expr := .inputPort 0 }]
      else
        flatWires0
    let outName :=
      match m.outputs.getLast? with
      | some o => o.name
      | none   => "out"
    let outWire := flatWires.length - 1
    let flatRegs := m.regs.zipIdx.map fun (r, idx) =>
      let nextW :=
        match r.nextExpr with
        | .wireRef w => (wireMap.lookup w).getD outWire
        | _          => outWire
      { regIdx         := idx
      , name           := r.name
      , domain         := r.domain
      , resetKind      := .resetFree
      , isSynchronizer := r.isSynchronizer
      , nextExpr       := .wireRef (if nextW < flatWires.length then nextW else outWire) }
    { name       := m.name
    , inputNames := [inPort]
    , wires      := flatWires
    , regs       := flatRegs
    , outputs    := [{ name := outName, expr := .wireRef outWire }] }

/-- Encode an `RtlModule` into a canonical JSON wire certificate string for `hw-rtl-synth@1` / `rtl-synth@1`,
inverting `decodeRtlSynthCert`. -/
def encodeRtlSynthCert (m : RtlModule) : String :=
  let mNorm := normalizeRtlModuleForWire m
  let inputPort := match mNorm.inputNames with | h :: _ => h | [] => "arg"
  let (outName, outWire) :=
    match mNorm.outputs with
    | ⟨n, .wireRef w, _⟩ :: _ => (n, w)
    | ⟨n, _, _⟩ :: _          => (n, 0)
    | []                   => ("out", 0)
  let wireFields := encodeRtlWiresAux 0 mNorm.wires
  let regFields  := encodeRtlRegsAux 0 mNorm.regs
  let headerFields : List String :=
    [ "\"module\":\"" ++ mNorm.name ++ "\""
    , "\"inputPort\":\"" ++ inputPort ++ "\""
    , "\"numWires\":" ++ rtlNatToStr mNorm.wires.length ]
  let midFields : List String :=
    [ "\"numRegs\":" ++ rtlNatToStr mNorm.regs.length ]
  let tailFields : List String :=
    [ "\"outputName\":\"" ++ outName ++ "\""
    , "\"outputWire\":" ++ rtlNatToStr outWire ]
  "{" ++ rtlJoinComma (headerFields ++ wireFields ++ midFields ++ regFields ++ tailFields) ++ "}"

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

/-- Registered `Obend.Judge.Format` alias `rtl-synth@1` sharing the exact `rtlSynthJudge` and wire codec. -/
def rtlSynthFormat : Format where
  name        := "rtl-synth"
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

theorem rtlSynthFormat_sound {r : Nat} {obj cert : String}
    (h : rtlSynthFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeRtlSynthObj obj = .ok o ∧ decodeRtlSynthCert cert = .ok c ∧
      ((c.name == o) && checkRtlModule c) = true :=
  rtlSynthFormat.checkBytes_sound h

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun hEq => by cases hEq; exact h rfl)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun hEq => by cases hEq; exact h rfl)
  | .error _, .ok _ => isFalse (fun hEq => by cases hEq)
  | .ok _, .error _ => isFalse (fun hEq => by cases hEq)

def _root_.Obend.Judge.Verdict.isOk {C : Type} : Verdict C → Bool
  | .ok => true
  | _   => false

theorem verdict_eq_ok_of_isOk {C : Type} {v : Verdict C} (h : v.isOk = true) : v = .ok := by
  cases v <;> simp [Obend.Judge.Verdict.isOk] at h ⊢

theorem verdict_ne_ok_of_isOk_false {C : Type} {v : Verdict C} (h : v.isOk = false) : v ≠ .ok := by
  intro hEq; subst hEq; cases h

/-- Canonical flat `RtlModule` fixture for roundtrip verification (`out_y := arg * 2 + 1`). -/
def goldenFlatRtlModule : RtlModule where
  name       := "test_rtl_synth"
  inputNames := ["arg"]
  wires      :=
    [ { wireIdx := 0, name := "w0", expr := .alu .mul (.inputPort 0) (.const 2#64) }
    , { wireIdx := 1, name := "w1", expr := .alu .add (.wireRef 0) (.const 1#64) } ]
  regs       :=
    [ { regIdx := 0, name := "reg_y", domain := .coreClk, resetKind := .resetFree, isSynchronizer := false, nextExpr := .wireRef 1 } ]
  outputs    := [{ name := "out_y", expr := .wireRef 1 }]

/-- Roundtrip theorem for `encodeRtlSynthObj` / `decodeRtlSynthObj`. -/
-- fixture kept (2026-11-04): codec round trip on both certificate kinds, cited by the AutoCert tests
theorem decodeRtlSynthObj_encodeRtlSynthObj_roundtrip :
    decodeRtlSynthObj (encodeRtlSynthObj "test_rtl_synth") = .ok "test_rtl_synth" ∧
    decodeRtlSynthObj (encodeRtlSynthObj "bad_loop_mod") = .ok "bad_loop_mod" := by
  decide +kernel

set_option maxHeartbeats 800000 in
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem decodeRtlSynthCert_encodeRtlSynthCert_golden :
    decodeRtlSynthCert (encodeRtlSynthCert goldenFlatRtlModule) = .ok goldenFlatRtlModule := by
  decide +kernel

set_option maxHeartbeats 800000 in
-- fixture kept (2026-11-04): consumed by a proof in this file
theorem decodeRtlSynthCert_encodeRtlSynthCert_bad :
    decodeRtlSynthCert (encodeRtlSynthCert badLoopRtlModule) = .ok badLoopRtlModule := by
  decide +kernel

set_option maxHeartbeats 1600000 in
/-- Roundtrip theorem for `encodeRtlSynthCert` / `decodeRtlSynthCert` and `hwSynthFormat.checkBytes` / `rtlSynthFormat.checkBytes`. -/
-- fixture kept (2026-11-04): used by tests/metasystem/AutoCertTest.lean
theorem decodeRtlSynthCert_encodeRtlSynthCert_roundtrip :
    decodeRtlSynthCert (encodeRtlSynthCert goldenFlatRtlModule) = .ok goldenFlatRtlModule ∧
    decodeRtlSynthCert (encodeRtlSynthCert badLoopRtlModule) = .ok badLoopRtlModule ∧
    hwSynthFormat.checkBytes 0 (encodeRtlSynthObj goldenFlatRtlModule.name) (encodeRtlSynthCert goldenFlatRtlModule) = .ok ∧
    rtlSynthFormat.checkBytes 0 (encodeRtlSynthObj goldenFlatRtlModule.name) (encodeRtlSynthCert goldenFlatRtlModule) = .ok ∧
    hwSynthFormat.checkBytes 0 (encodeRtlSynthObj badLoopRtlModule.name) (encodeRtlSynthCert badLoopRtlModule) ≠ .ok := by
  refine ⟨decodeRtlSynthCert_encodeRtlSynthCert_golden,
          decodeRtlSynthCert_encodeRtlSynthCert_bad,
          verdict_eq_ok_of_isOk (by decide +kernel),
          verdict_eq_ok_of_isOk (by decide +kernel),
          verdict_ne_ok_of_isOk_false (by decide +kernel)⟩

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
  ensureWireFrame s
  let period ← requireNatField s "periodPs"
  return (macUnretimedGraph, period)

def decodeRetimeCert (s : String) : Except String RetimingCert := do
  ensureWireFrame s
  let lag0    ← requireIntField s "lag0"
  let lag1    ← requireIntField s "lag1"
  let ioShift ← requireIntField s "ioLatencyShift"
  return { vertexLags := [(0, lag0), (1, lag1), (2, ioShift)], ioLatencyShift := ioShift }

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

/-- Judge check function for `hw-pnr-bitstream@1` bound to `validAdderBelNetlist`. -/
def checkPnrJudge (_grade : Nat) (periodPs : Nat) (cert : PnrCertificate) : Verdict HwClause :=
  if checkPnrCertificate validAdderBelNetlist corner7nm_SS periodPs cert then
    .ok
  else
    .refused (.pnrCollisionShortOrTiming cert.designName) []

instance pnrBitstreamJudge : Obend.Judge Nat PnrCertificate where
  Clause := HwClause
  Meaning periodPs cert := checkPnrCertificate validAdderBelNetlist corner7nm_SS periodPs cert = true
  check := checkPnrJudge
  sound := by
    intro _ o c h
    unfold checkPnrJudge at h
    by_cases hOk : checkPnrCertificate validAdderBelNetlist corner7nm_SS o c = true
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
  ensureWireFrame s
  requireNatField s "periodPs"

def decodePnrCert (s : String) : Except String PnrCertificate := do
  ensureWireFrame s
  let designName  ← requireStringField s "designName"
  let sinkCap     ← requireNatField s "sinkCapFf"
  let cell1TileY  ← requireNatField s "cell1TileY"
  let cell0Bel    ← requireNatField s "cell0BelSlot"
  let cell1Bel    ← requireNatField s "cell1BelSlot"
  let net0DstWire ← requireNatField s "net0DstWire"
  let net1DstWire ← requireNatField s "net1DstWire"
  return {
    designName  := designName
    placedCells :=
      [ { cellId := 0, tileX := 0, tileY := 0, belSlot := cell0Bel, lutInit := 0x6 }
      , { cellId := 1, tileX := 0, tileY := cell1TileY, belSlot := cell1Bel, lutInit := 0x6 } ]
    routedNets  :=
      [ { netId := 0, srcWire := 10, dstWire := net0DstWire
        , hops := [ { srcWire := 10, dstWire := 11, resOhm := 50, capFf := 4 }
                  , { srcWire := 11, dstWire := net0DstWire, resOhm := 50, capFf := 4 } ] }
      , { netId := 1, srcWire := 20, dstWire := net1DstWire
        , hops := [ { srcWire := 20, dstWire := net1DstWire, resOhm := 40, capFf := 3 } ] } ]
    expectedConfigs := validAdderPnrCert.expectedConfigs
    bitstreamFrames := validAdderPnrCert.bitstreamFrames
    sinkCapFf       := sinkCap
  }

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
      checkPnrCertificate validAdderBelNetlist corner7nm_SS o c = true :=
  hwPnrFormat.checkBytes_sound h

/-! ## 5. Format 4: `datasheet-fit@1` (Automated Datasheet Calibration, `74LS00` + `74HCT00` + INA + Buck Judge) -/

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
  requireStringField s "suite"

def decodeDatasheetFitCert (s : String) : Except String DatasheetFitCert := do
  ensureWireFrame s
  let suiteName   ← requireStringField s "suiteName"
  let pullup      ← requireIntField s "pullupBoostMv"
  let minMargin   ← requireIntField s "minMarginMv"
  let rcvVihMinMv ← requireIntField s "rcvVihMinMv"
  let rcvVilMaxMv ← requireIntField s "rcvVilMaxMv"
  let fanout      ← requireNatField s "fanout"
  let maxCalErr   ← requireIntField s "maxCalErrMv"
  let buckLoadMa  ← requireNatField s "buckLoadMa"
  return {
    suiteName       := suiteName
    driverSpec      := sn74ls00Datasheet.logic
    receiverSpec    := { cd74hct00Datasheet.logic with vihMinMv := rcvVihMinMv, vilMaxMv := rcvVilMaxMv }
    pullupBoostMv   := pullup
    minMarginMv     := minMargin
    ttlParams       := sn74ls00TotemParams
    fanout          := fanout
    modelPreds      := calibrated74ls00ModelPreds
    datasheetPoints := sn74ls00Datasheet.transferCurve
    maxCalErrMv     := maxCalErr
    inaSpec         := precisionMatchedIna
    buckStage       := { golden5vBuckSpec with iLoadMa := buckLoadMa }
  }

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

/-! ## 6. Format 5: `agentic-eda-swap@1` (Smart-Contract Markdown Vault BOM Swap Judge) -/

/-- Boolean wrapper checking whether `judgeAgenticEdaProposal` admits `candidatePart` at `minMarginMv`. -/
def checkAgenticEdaSwapBool (minMarginMv : Int) (candidatePart : EdaVaultPart) : Bool :=
  judgeAgenticEdaProposal
    goldenEdaLaws
    goldenBaselinePart
    candidatePart
    lvcmos33ReceiverSpec
    minMarginMv
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

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badAgenticEdaSwap_refused :
    checkAgenticEdaJudge 0 400 overbudgetSecondSourcePart =
      .refused (.agenticEdaSwapViolation "U4_LDO") [] := by
  decide +kernel

def decodeAgenticEdaObj (s : String) : Except String Int := do
  ensureWireFrame s
  requireIntField s "minMarginMv"

def decodeAgenticEdaCert (s : String) : Except String EdaVaultPart := do
  ensureWireFrame s
  let pageName ← requireStringField s "pageName"
  let voh      ← requireNatField s "vohMinMv"
  let vih      ← requireNatField s "vihMinMv"
  let vol      ← requireNatField s "volMaxMv"
  let vil      ← requireNatField s "vilMaxMv"
  let pkgW     ← requireNatField s "pkgWidthUm"
  let pkgL     ← requireNatField s "pkgLengthUm"
  let pins     ← requireNatField s "pinCount"
  let pitch    ← requireNatField s "pinPitchUm"
  let tempMc   ← requireNatField s "maxTempMc"
  let vswr     ← requireNatField s "vswrMilli"
  let drcErr   ← requireNatField s "drcErrors"
  let cost     ← requireNatField s "costCents"
  return {
    pageName     := pageName
    vohMinMv     := voh
    vihMinMv     := vih
    volMaxMv     := vol
    vilMaxMv     := vil
    pkgWidthUm   := pkgW
    pkgLengthUm  := pkgL
    pinCount     := pins
    pinPitchUm   := pitch
    maxTempMc    := tempMc
    vswrMilli    := vswr
    drcErrors    := drcErr
    costCents    := cost }

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

-- fixture kept (2026-11-04): consumed by a proof in this file
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
  | none =>
    match extractNatField s "domainId" with
    | some n =>
      match HwCertDomain.fromCode n with
      | some d => .ok d
      | none => .error s!"unknown binary CBOR domain id: {n}"
    | none => .error s!"missing required binary CBOR domain id in '{s}'"

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

-- fixture kept (2026-11-04): consumed by a proof in this file
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

/-- Complete list of registered hardware, datasheet-fit, agentic EDA, and binary CBOR formats. -/
def hardwareFormats : List Format :=
  [ hwSynthFormat
  , rtlSynthFormat
  , hwRetimeFormat
  , hwPnrFormat
  , datasheetFitFormat
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
from JSON and key-value wire strings, and that overriding numeric fields in `decodePnrCert` and
`decodeAgenticEdaCert` triggers judge refusal on out-of-spec numeric values! -/
theorem extractNatField_and_extractIntField_verified :
    extractNatField "{\"mode\": \"golden\", \"costCents\": 320}" "costCents" = some 320 ∧
    extractIntField "{\"mode\": \"golden\", \"minMarginMv\": -150}" "minMarginMv" = some (-150) ∧
    extractNatField "cell1TileY=0,sinkCapFf=5" "cell1TileY" = some 0 ∧
    (let pnr : PnrCertificate :=
       { validAdderPnrCert with
         placedCells :=
           [ { cellId := 0, tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6 }
           , { cellId := 1, tileX := 0,
               tileY := (extractNatField "{\"cell1TileY\": 0}" "cell1TileY").getD 1,
               belSlot := 0, lutInit := 0x6 } ] }
     checkPnrJudge 0 2000 pnr = .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") []) ∧
    (let cand : EdaVaultPart :=
       { goldenBaselinePart with
         costCents := (extractNatField "{\"costCents\": 320}" "costCents").getD 120 }
     checkAgenticEdaJudge 0 400 cand = .refused (.agenticEdaSwapViolation "U4_LDO") []) := by
  decide +kernel

/-- **Identifier-Boundary Non-Collision & End-to-End Strict Decoder Verification
(`extractNatField_token_boundary_and_decoders_verified`)**:
1. `"fanout"` does *not* match the suffix of `"max_fanout"` in JSON or key-value wire strings,
2. `decodeDatasheetFitCert`, `decodeAgenticEdaCert`, `decodeRtlSynthCert`, and `decodePnrCert`
   require all explicit fields (returning `.error` when fields are omitted) and reject out-of-spec
   numeric parameters in the Lean 4 kernel (`decide +kernel`). -/
theorem extractNatField_token_boundary_and_decoders_verified :
    extractNatField "{\"max_fanout\": 99, \"mode\": \"calibrated\"}" "fanout" = none ∧
    extractNatField "max_fanout=99,mode=calibrated" "fanout" = none ∧
    extractIntField "{\"extra_minMarginMv\": -500}" "minMarginMv" = none ∧
    (decodeDatasheetFitCert "mode=calibrated").isOk = false ∧
    (decodeAgenticEdaCert "mode=golden").isOk = false ∧
    (decodeRtlSynthCert "{\"module\": \"m\"}").isOk = false ∧
    (decodePnrCert "{\"mode\": \"valid\"}").isOk = false ∧
    (match decodePnrCert "designName=obend_routed_adder2,sinkCapFf=5,cell1TileY=0,cell0BelSlot=0,cell1BelSlot=0,net0DstWire=12,net1DstWire=21" with
     | .ok c => c.sinkCapFf == 5 &&
       checkPnrJudge 0 2000 c == .refused (.pnrCollisionShortOrTiming "obend_routed_adder2") []
     | .error _ => false) = true := by
  decide +kernel

end Obend.Hardware.Judge
