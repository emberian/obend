/-
# Obend.Hardware.Gpu.Rdna2.Decode — RDNA2 machine code read by AMD's own specification

`decodeInst` reads one instruction from a dword stream the way GPUOpen's `IsaDecoder`
(`isa_spec_manager/source/isa_decoder/isa_decoder.cpp`, `GetEncodingIterator`) reads it from the XML:
the first dword masked with an encoding's identifier mask must be one of that encoding's identifiers,
encodings tried in their `Order`; the instruction is the one whose entry names that encoding and whose
opcode is the `OP` field; the entry's *condition* (an expression over the fields, `Cond`, e.g. `has_lit_0`
is `SRC0 == 255`) is what selects a variant and its width (a literal dword, DPP, SDWA). Every table
here is `Obend.Hardware.Gpu.Rdna2.Encodings`/`Insts`, generated from the XML and never typed.

`Inst.render` writes the instruction in LLVM's AMDGPU assembler syntax (AMDGPUUsage, "Syntax of
AMDGPU Instruction Operands" and "Modifiers"; `_e32`/`_e64` suffixes when an instruction has both a
32-bit and a VOP3 form), for `hardware/gpu/isa_check.sh`, which holds it to `llvm-mc --disassemble`
(LLVM 19, gfx1031, wave64) on every instruction of every dump under `hardware/gpu/isa/`. It renders the
scalar, vector-ALU, scalar-memory and buffer encodings; a DPP, SDWA, DS, FLAT, image, export or
interpolation word decodes but renders as `none`, which the gate reports rather than guesses at.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Spec
public import Obend.Hardware.Gpu.Rdna2.Encodings
public import Obend.Hardware.Gpu.Rdna2.Insts
public import Std.Data.HashMap
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. Fields -/

/-- The dwords of an instruction as one number, the first dword lowest: bit `i` of the encoding is bit
`i` of this number (the XML's `BitOffset` counts from the first dword's LSB). -/
def wordsToNat (ws : List UInt32) : Nat := ws.foldr (fun w acc => (acc <<< 32) ||| w.toNat) 0

def extractRange (n : Nat) (r : FieldRange) : Nat := (n >>> r.offset) % (2 ^ r.count)

/-- A field's value: its ranges concatenated, the first range lowest (MUBUF's `OP` is bits 18..24 then
bit 25). -/
def fieldValue (n : Nat) (f : EncField) : Nat :=
  (f.ranges.foldl (fun (acc : Nat × Nat) r => (acc.1 ||| (extractRange n r <<< acc.2), acc.2 + r.count)) (0, 0)).1

def fieldsOf (e : Encoding) (ws : List UInt32) : List (String × Nat) :=
  let n := wordsToNat ws
  e.fields.map fun f => (f.name, fieldValue n f)

def lookupField (fs : List (String × Nat)) (name : String) : Option Nat :=
  (fs.find? (·.1 == name)).map (·.2)

/-- The XML's condition expression over the fields read from the words. -/
def Cond.eval (fs : List (String × Nat)) : Cond → Bool
  | .lit b => b
  | .eq f v => lookupField fs f == some v
  | .ne f v => match lookupField fs f with | some x => x != v | none => false
  | .within f vs => match lookupField fs f with | some x => vs.contains x | none => false
  | .notWithin f vs => match lookupField fs f with | some x => !vs.contains x | none => false
  | .and a b => a.eval fs && b.eval fs

/-! ## 2. Decoding -/

/-- A decoded instruction: the XML instruction, the encoding whose fields were read (the base one or a
variant), the instruction's entry for it, the field values, and the dwords consumed. -/
structure Inst where
  inst : Instruction
  enc : Encoding
  ie : InstEncoding
  fields : List (String × Nat)
  words : List UInt32
  deriving Repr

def Inst.name (i : Inst) : String := i.inst.name
def Inst.field (i : Inst) (name : String) : Nat := (lookupField i.fields name).getD 0
def Inst.field? (i : Inst) (name : String) : Option Nat := lookupField i.fields name

/-- `(encoding name, opcode) ↦ the instruction entries with that encoding and opcode`. -/
def instIndex : Std.HashMap (String × Nat) (List (Instruction × InstEncoding)) :=
  instructions.foldl (init := {}) fun m i =>
    i.encodings.foldl (init := m) fun m ie =>
      m.insert (ie.encoding, ie.opcode) ((i, ie) :: (m.getD (ie.encoding, ie.opcode) []))

/-- The encodings in decode order. -/
def encodingsInOrder : List Encoding :=
  encodings.toArray.qsort (fun a b => a.order < b.order) |>.toList

def encodingMatches (w0 : UInt32) (e : Encoding) : Bool := e.identifiers.contains (w0 &&& e.mask)

/-- Decode one instruction at the head of `ws`; the number of dwords it took comes with it. `none` when
no encoding's identifier matches, the opcode names no instruction in that encoding, or no entry's
condition holds (the XML has no reading of these dwords). -/
def decodeInst (ws : List UInt32) : Option (Inst × Nat) :=
  match ws with
  | [] => none
  | w0 :: _ =>
    let rec go : List Encoding → Option (Inst × Nat)
      | [] => none
      | e :: es =>
        if !encodingMatches w0 e then go es else
        let k := e.bitCount / 32
        if ws.length < k then go es else
        let taken := ws.take k
        let fs := fieldsOf e taken
        match lookupField fs "OP" with
        | none => go es
        | some op =>
          let entries := instIndex.getD (e.name, op) []
          let hit := entries.find? fun (_, ie) =>
            match e.conditions.find? (·.name == ie.condition) with
            | some c => c.expr.eval fs
            | none => false
          match hit with
          | some (i, ie) => some (⟨i, e, ie, fs, taken⟩, k)
          | none => go es
    go encodingsInOrder

/-- A whole program: `prog[d]` is the instruction starting at dword `d`, `none` inside a multi-dword
instruction. Fails at the first dword the XML cannot read. -/
def decodeProgram (ws : Array UInt32) : Except String (Array (Option Inst)) := Id.run do
  let mut out : Array (Option Inst) := Array.replicate ws.size none
  let mut d := 0
  while d < ws.size do
    match decodeInst (ws.extract d (min ws.size (d + 5))).toList with
    | none => return .error s!"dword {d} (0x{hexOf ws[d]!.toNat 8}) decodes to no RDNA2 instruction"
    | some (i, k) =>
      out := out.set! d (some i)
      d := d + k
  return .ok out
where
  hexOf (n : Nat) (width : Nat) : String :=
    let s := String.ofList (Nat.toDigits 16 n)
    "".pushn '0' (width - s.length) ++ s

/-! ## 3. Rendering in LLVM's syntax -/

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A register name over `k` consecutive registers: `s4` or `s[4:7]`, `v3` or `v[2:3]`. -/
def regName (pre : String) (n k : Nat) : String :=
  if k ≤ 1 then pre ++ toString n else s!"{pre}[{n}:{n + k - 1}]"

/-- Table 10 / Table 20 of the manual (scalar and vector operand codes), in LLVM's spelling: `vcc` for the
pair at 106 when the operand is 64-bit and `vcc_lo` when 32-bit (wave64), likewise `exec`; inline
integers as decimals, inline floats as LLVM prints them, `src_scc`, `src_vccz`, `src_execz`; 256..511
the VGPRs. `lit` is the literal dword when the operand is 255. -/
def srcName (code : Nat) (bits : Nat) (lit : Option UInt32) : Option String :=
  let k := (bits + 31) / 32
  if code ≤ 105 then some (regName "s" code k)
  else if code == 106 then some (if k ≥ 2 then "vcc" else "vcc_lo")
  else if code == 107 then some "vcc_hi"
  else if code ≤ 123 then some (regName "ttmp" (code - 108) k)
  else if code == 124 then some "m0"
  else if code == 125 then some "null"
  else if code == 126 then some (if k ≥ 2 then "exec" else "exec_lo")
  else if code == 127 then some "exec_hi"
  else if code == 128 then some "0"
  else if code ≤ 192 then some (toString (code - 128))
  else if code ≤ 208 then some ("-" ++ toString (code - 192))
  else if code == 235 then some "src_shared_base"
  else if code == 236 then some "src_shared_limit"
  else if code == 237 then some "src_private_base"
  else if code == 238 then some "src_private_limit"
  else if code == 239 then some "src_pops_exiting_wave_id"
  else if code == 240 then some "0.5"
  else if code == 241 then some "-0.5"
  else if code == 242 then some "1.0"
  else if code == 243 then some "-1.0"
  else if code == 244 then some "2.0"
  else if code == 245 then some "-2.0"
  else if code == 246 then some "4.0"
  else if code == 247 then some "-4.0"
  else if code == 248 then some "0.15915494"
  else if code == 251 then some "src_vccz"
  else if code == 252 then some "src_execz"
  else if code == 253 then some "src_scc"
  else if code == 255 then lit.map fun l => hex l.toNat
  else if 256 ≤ code && code ≤ 511 then some (regName "v" (code - 256) k)
  else none

/-- The families whose operands this renderer writes. -/
def family (encName : String) : String :=
  if encName.startsWith "ENC_" then (encName.drop 4).toString else (encName.takeWhile (· != '_')).toString

/-- `_e32`/`_e64`: LLVM suffixes the 32-bit form when a VOP3 form of the instruction exists and the VOP3
form when a 32-bit form exists; an instruction with one form gets no suffix. -/
def mnemonic (i : Inst) : String :=
  let fam := family i.enc.name
  let has (p : String → Bool) := i.inst.encodings.any fun ie => p (family ie.encoding)
  let isVop32 (f : String) := f == "VOP1" || f == "VOP2" || f == "VOPC"
  let isVop3 (f : String) := f == "VOP3"
  let base := i.inst.name.toLower
  if isVop32 fam && has isVop3 then base ++ "_e32"
  else if isVop3 fam && has isVop32 then base ++ "_e64"
  else base

/-- S_WAITCNT's counters (manual 12.5 `S_WAITCNT`: vmcnt `{SIMM16[15:14], SIMM16[3:0]}`, expcnt
`SIMM16[6:4]`, lgkmcnt `SIMM16[13:8]`); LLVM names only the counters below their maximum. -/
def waitcntText (simm : Nat) : String :=
  let vm := (simm % 16) ||| (((simm >>> 14) % 4) <<< 4)
  let exp := (simm >>> 4) % 8
  let lgkm := (simm >>> 8) % 64
  let parts := (if vm != 63 then [s!"vmcnt({vm})"] else []) ++ (if exp != 7 then [s!"expcnt({exp})"] else [])
    ++ (if lgkm != 63 then [s!"lgkmcnt({lgkm})"] else [])
  if parts.isEmpty then hex simm else " ".intercalate parts

def signed16 (n : Nat) : Int := if n ≥ 32768 then (n : Int) - 65536 else n

/-- A signed 21-bit SMEM offset. -/
def signed21 (n : Nat) : Int := if n ≥ 2 ^ 20 then (n : Int) - 2 ^ 21 else n

def Inst.literal (i : Inst) : Option UInt32 :=
  match i.field? "LITERAL" with
  | some v => some (UInt32.ofNat v)
  | none => none

/-- VOP3 input modifiers on source `k` (`NEG`, `ABS` bit `k`): `-|v1|`. -/
def withMods (i : Inst) (k : Nat) (s : String) : String :=
  let neg := (i.field "NEG" >>> k) % 2 == 1
  let abs := (i.field "ABS" >>> k) % 2 == 1
  let s := if abs then s!"|{s}|" else s
  if neg then "-" ++ s else s

/-- One operand of a scalar/vector ALU entry, in LLVM's spelling, or `none` for a kind this renderer does
not write. `k` counts the source operands seen so far (for VOP3 modifiers). -/
def renderAluOperand (i : Inst) (op : Operand) (k : Nat) : Option String :=
  let fam := family i.enc.name
  let isCmpx := i.inst.name.startsWith "V_CMPX"
  if op.type == "OPR_EXEC" && isCmpx then some "" else
  if op.type == "OPR_SDST_EXEC" && op.implicit then some "" else
  if op.implicit then some "" else
  match op.field with
  | "" =>
    -- VOP2/VOPC's implicit VCC: LLVM writes it (`v_add_co_ci_u32_e32 v7, vcc, v3, v5, vcc`).
    if op.type == "OPR_VCC" then some "vcc" else none
  | "LITERAL" => (i.literal.map fun l => hex l.toNat).map (withMods i k)
  | "SIMM16" =>
    let v := i.field "SIMM16"
    if op.type == "OPR_LABEL" then some (toString (signed16 v))
    else if op.type == "OPR_WAITCNT" then some (waitcntText v)
    else if fam == "SOPK" || op.type == "OPR_CLAUSE" then some (hex v)
    else some (toString v)
  | f =>
    let v := i.field f
    if op.type == "OPR_VGPR" then some (regName "v" v ((op.size + 31) / 32))
    else if fam == "VOP3" && (f == "SRC0" || f == "SRC1" || f == "SRC2") then (srcName v op.size i.literal).map (withMods i k)
    else srcName v op.size i.literal

/-- The VOP3 output modifiers, as LLVM appends them. -/
def vop3Suffix (i : Inst) : String :=
  let clamp := if i.field "CLAMP" == 1 then " clamp" else ""
  let omod := match i.field "OMOD" with | 1 => " mul:2" | 2 => " mul:4" | 3 => " div:2" | _ => ""
  let opsel := i.field "OP_SEL"
  let opselS := if opsel != 0 then s!" op_sel:[{opsel % 2},{(opsel >>> 1) % 2},{(opsel >>> 2) % 2},{(opsel >>> 3) % 2}]" else ""
  clamp ++ omod ++ opselS

/-- The scalar and vector ALU families: operands in the XML's order, separated by `, `. -/
def renderAlu (i : Inst) : Option String := do
  let fam := family i.enc.name
  let mut parts : List String := []
  let mut k := 0
  for op in i.ie.operands do
    let s ← renderAluOperand i op k
    if op.input && op.field != "" then k := k + 1
    if s != "" then parts := parts ++ [s]
  let tail := if fam == "VOP3" then vop3Suffix i else ""
  let m := mnemonic i
  if parts.isEmpty then m ++ tail else m ++ " " ++ ", ".intercalate parts ++ tail

/-- SMEM (manual 7.1): `sdata, sbase, soffset`, where the offset is `null`, the immediate in hex, an
SGPR, or `sN offset:0x..` when both are present; then `glc`/`dlc`. SBASE's LSB is implied zero and the
operand is a pair, or four SGPRs for the buffer loads. -/
def renderSmem (i : Inst) : Option String := do
  let sdata ← i.ie.operands.find? (·.field == "SDATA")
  let sbase ← i.ie.operands.find? (·.field == "SBASE")
  let soff := i.field "SOFFSET"
  let imm := i.field "OFFSET"
  let sdataS := regName "s" (i.field "SDATA") ((sdata.size + 31) / 32)
  let sbaseS := regName "s" (2 * i.field "SBASE") ((sbase.size + 31) / 32)
  let offS :=
    if soff == 125 then (if imm == 0 then "null" else hex imm)
    else
      let r := (srcName soff 32 none).getD "?"
      if imm == 0 then r else s!"{r} offset:{hex imm}"
  let glc := if i.field "GLC" == 1 then " glc" else ""
  let dlc := if i.field "DLC" == 1 then " dlc" else ""
  pure s!"{mnemonic i} {sdataS}, {sbaseS}, {offS}{glc}{dlc}"

/-- MUBUF (manual 8.1.2, Table 30): `vdata, vaddr, srsrc, soffset` then `idxen offen offset:N glc slc
dlc lds tfe`; `vaddr` is `off`, one VGPR or a pair by IDXEN+OFFEN; SRSRC is in units of four SGPRs. -/
def renderMubuf (i : Inst) : Option String := do
  let vdata ← i.ie.operands.find? (·.field == "VDATA")
  let idxen := i.field "IDXEN" == 1
  let offen := i.field "OFFEN" == 1
  let nAddr := (if idxen then 1 else 0) + (if offen then 1 else 0)
  let vaddrS := if nAddr == 0 then "off" else regName "v" (i.field "VADDR") nAddr
  let vdataS := regName "v" (i.field "VDATA") ((vdata.size + 31) / 32)
  let srsrcS := regName "s" (4 * i.field "SRSRC") 4
  let soffS ← srcName (i.field "SOFFSET") 32 none
  let flags := (if idxen then " idxen" else "") ++ (if offen then " offen" else "")
    ++ (if i.field "OFFSET" != 0 then s!" offset:{i.field "OFFSET"}" else "")
    ++ (if i.field "GLC" == 1 then " glc" else "") ++ (if i.field "SLC" == 1 then " slc" else "")
    ++ (if i.field "DLC" == 1 then " dlc" else "") ++ (if i.field "LDS" == 1 then " lds" else "")
    ++ (if i.field "TFE" == 1 then " tfe" else "")
  pure s!"{mnemonic i} {vdataS}, {vaddrS}, {srsrcS}, {soffS}{flags}"

/-- The instruction in LLVM's syntax, or `none` for a family this renderer does not write. -/
def Inst.render (i : Inst) : Option String :=
  match i.enc.name with
  | "ENC_SOP1" | "ENC_SOP2" | "ENC_SOPC" | "ENC_SOPP" | "ENC_SOPK" | "ENC_VOP1" | "ENC_VOP2" | "ENC_VOPC"
  | "ENC_VOP3" | "VOP3_SDST_ENC" | "SOP1_INST_LITERAL" | "SOP2_INST_LITERAL" | "SOPC_INST_LITERAL"
  | "SOPK_INST_LITERAL" | "VOP1_INST_LITERAL" | "VOP2_INST_LITERAL" | "VOPC_INST_LITERAL"
  | "VOP3_INST_LITERAL" | "VOP3_SDST_ENC_INST_LITERAL" => renderAlu i
  | "ENC_SMEM" => renderSmem i
  | "ENC_MUBUF" => renderMubuf i
  | _ => none

end Obend.Hardware.Gpu.Rdna2
