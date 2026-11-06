/-
# Obend.Hardware.Gpu.Rdna2.Spec — the shape of AMD's machine-readable ISA, as Lean data

The types the generated modules `Obend.Hardware.Gpu.Rdna2.Encodings` and `Obend.Hardware.Gpu.Rdna2.Insts`
instantiate from `hardware/gpu/rdna2/amdgpu_isa_rdna2.xml` (`hardware/gpu/rdna2/gen_encodings.py`; the
provenance is in `hardware/gpu/rdna2/README.md`). One Lean structure per XML element the schema documents
(`isa_spec_manager/documentation/spec_documentation.md`): `Encoding` with its identifier mask, identifiers,
conditions and bit fields; `Instruction` with its flags and `InstEncoding`s, each with its operands;
`OperandType` with its predefined values. The encoding conditions are the XML's `CondtionExpression`
trees over the base encoding's fields (`Cond`), evaluated by the decoder, so that which variant a word
is (literal, DPP, SDWA) is the XML's decision and not ours.
-/
module
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-- A contiguous bit range of a field: `count` bits starting at `offset`, LSB 0 of the encoding. -/
structure FieldRange where
  offset : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- One field of an encoding's `MicrocodeFormat/BitMap`; the XML lists `OP` for MUBUF as two ranges. -/
structure EncField where
  name : String
  ranges : List FieldRange
  deriving Repr, DecidableEq

/-- An `EncodingCondition`'s expression, over the fields of the base encoding (`.fieldderef INST.ENC.F`). -/
inductive Cond where
  | lit (b : Bool)
  | eq (field : String) (v : Nat)
  | ne (field : String) (v : Nat)
  | within (field : String) (vs : List Nat)
  | notWithin (field : String) (vs : List Nat)
  | and (a b : Cond)
  deriving Repr, DecidableEq

structure EncCondition where
  name : String
  expr : Cond
  deriving Repr, DecidableEq

/-- An `Encoding`: `mask` and `identifiers` are the XML's binary strings read on the first dword (the
generator checks every set bit of every mask lies in the first 32 bits). `order` is the XML's `Order`,
the sequence in which a decoder tries encodings; `bitCount` the width of the whole instruction. -/
structure Encoding where
  name : String
  order : Int
  bitCount : Nat
  mask : UInt32
  identifiers : List UInt32
  conditions : List EncCondition
  fields : List EncField
  deriving Repr

/-- An operand of one `InstructionEncoding`: `field` is `""` when the XML gives none (an implicit operand,
or one the type implies: `IsBinaryMicrocodeRequired`). -/
structure Operand where
  field : String
  type : String
  format : String
  size : Nat
  input : Bool
  output : Bool
  implicit : Bool
  binaryRequired : Bool
  deriving Repr, DecidableEq

structure InstEncoding where
  encoding : String
  condition : String
  opcode : Nat
  operands : List Operand
  deriving Repr, DecidableEq

structure Instruction where
  name : String
  isBranch : Bool
  isConditionalBranch : Bool
  isTerminator : Bool
  isImmediatelyExecuted : Bool
  encodings : List InstEncoding
  deriving Repr, DecidableEq

/-- A run of predefined register names `pre ++ toString i` for `i` from `first`, `count` of them, whose
encoded values are `value + (i - first)`: how the generator keeps `s0..s105`, `v0..v255` (the generator
verifies every run against the XML's list). -/
structure RegRun where
  pre : String
  first : Nat
  count : Nat
  value : Nat
  deriving Repr, DecidableEq

structure OperandType where
  name : String
  partitioned : Bool
  subtypes : List String
  runs : List RegRun
  specials : List (String × Nat)
  deriving Repr, DecidableEq

/-- The name of a predefined value, if the type has one for `v`. -/
def OperandType.nameOf (t : OperandType) (v : Nat) : Option String :=
  match t.specials.find? (·.2 == v) with
  | some (n, _) => some n
  | none =>
    match t.runs.find? (fun r => r.value ≤ v && v < r.value + r.count) with
    | some r => some (r.pre ++ toString (r.first + (v - r.value)))
    | none => none

end Obend.Hardware.Gpu.Rdna2
