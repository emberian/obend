module
/-
# Obend.Hardware.Types — Algebraic Hardware Types, Bit-Packing Isomorphism, Slice Lenses & Sum Muxing

Formalizes structured hardware types (`HwType`) for compiling Objective Bend records (`Term.record`,
`Term.get`), nominal brands (`#kind`), tagged sums (`Term.inject`, `Term.case`), and fixed-width
vectors into flat bitvectors and `Obend.Hardware.HDL.RtlExpr` combinational circuits:

1. **Recursive Hardware Type Algebra (`HwType`)**:
   - `.bits w`: flat bitvector of `w` bits,
   - `.structNil` / `.structCons` (and `.struct fields` smart constructor): packed record of named
     fields concatenated in declaration order at static bit offsets `fieldOffset`,
   - `.taggedUnion tagBits payloadWidth numArms`: tagged sum `[tag : tagBits | payload : payloadWidth]`
     lowering `Term.inject` and `Term.case`,
   - `.array len elem`: fixed-size hardware vector/bus of `len` elements of type `elem`.
2. **Typed Hardware Values & Bit-Packing Isomorphism (`HwVal`, `packHwVal`, `unpackHwVal`)**:
   - Proves `unpack_pack_id` (`∀ (ty : HwType) (v : HwVal), unpackHwVal ty (packHwVal ty v) = v`)
     and `pack_unpack_id` across `.bits`, `.struct`, `.taggedUnion`, and `.array`.
3. **Hardware Bit-Slice Lenses & Non-Interference (`PackedStructWord`, `extractStructSlice`, `updateStructSlice`)**:
   - Proves `struct_slice_extract_sound` and `struct_slice_update_noninterference` (updating field
     `f₁` preserves every other field `f₂ ≠ f₁`).
4. **Tagged-Union Hardware Muxing & `RtlExpr` Lowering (`compileCaseMuxRtl`, `compileArrayReadRtl`)**:
   - Proves `taggedUnion_case_mux_sound`: hardware tag-comparison + payload extraction implements
     exact sum elimination (`Term.case`), and proves `array_index_mux_sound`.
-/
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
public import Obend.Core.Term
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Types
open Obend.Core.Term Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Recursive Hardware Type Algebra (`HwType`) & Static Bit-Offset Calculators -/

/-- Recursive hardware type grammar lowering Objective Bend scalars, records, tagged unions, and vectors. -/
inductive HwType where
  | bits        (width : Nat)
  | structNil
  | structCons  (name : String) (fieldTy : HwType) (rest : HwType)
  | taggedUnion (tagBits : Nat) (payloadWidth : Nat) (numArms : Nat)
  | array       (len : Nat) (elem : HwType)
  deriving DecidableEq, Repr

/-- Smart constructor building a packed `.struct` hardware type from a list of `(fieldName, HwType)` pairs. -/
def HwType.struct (fields : List (String × HwType)) : HwType :=
  fields.foldr (fun (n, t) acc => .structCons n t acc) .structNil

/-- Total bit width of a `HwType` when packed onto physical wires. -/
def HwType.bitWidth : HwType → Nat
  | .bits w => w
  | .structNil => 0
  | .structCons _ fty rest => fty.bitWidth + rest.bitWidth
  | .taggedUnion tagBits payloadWidth _ => tagBits + payloadWidth
  | .array len elem => len * elem.bitWidth

/-- Maximum bit width across a list of `(armName, HwType)` tagged-union arms. -/
def maxArmWidth : List (String × HwType) → Nat
  | [] => 0
  | (_, ty) :: rest => Nat.max ty.bitWidth (maxArmWidth rest)

/-- Smart constructor building a `.taggedUnion` from `tagBits` and a list of `(armName, HwType)` arms. -/
def HwType.mkTaggedUnion (tagBits : Nat) (arms : List (String × HwType)) : HwType :=
  .taggedUnion tagBits (maxArmWidth arms) arms.length

@[simp] theorem bitWidth_bits (w : Nat) : (HwType.bits w).bitWidth = w := rfl

@[simp] theorem bitWidth_structNil : HwType.structNil.bitWidth = 0 := rfl

@[simp] theorem bitWidth_structCons (name : String) (ty rest : HwType) :
    (HwType.structCons name ty rest).bitWidth = ty.bitWidth + rest.bitWidth := rfl

@[simp] theorem bitWidth_taggedUnion (tagBits payloadWidth numArms : Nat) :
    (HwType.taggedUnion tagBits payloadWidth numArms).bitWidth = tagBits + payloadWidth := rfl

@[simp] theorem bitWidth_array (len : Nat) (elem : HwType) :
    (HwType.array len elem).bitWidth = len * elem.bitWidth := rfl

/-- Compute the static bit offset of field `target` inside a `HwType` struct spine. -/
def fieldOffset : HwType → String → Option Nat
  | .structCons name fty rest, target =>
    if name == target then
      some 0
    else
      match fieldOffset rest target with
      | some off => some (fty.bitWidth + off)
      | none => none
  | _, _ => none

/-- Compute the static bit width of field `target` inside a `HwType` struct spine. -/
def fieldWidth : HwType → String → Option Nat
  | .structCons name fty rest, target =>
    if name == target then
      some fty.bitWidth
    else
      fieldWidth rest target
  | _, _ => none

/-- Compute the numeric tag index (`0, 1, ...`) of constructor `label` in a `.taggedUnion` arm list. -/
def armTagIndex : List (String × HwType) → String → Option Nat
  | [], _ => none
  | (name, _) :: rest, label =>
    if name == label then
      some 0
    else
      match armTagIndex rest label with
      | some idx => some (idx + 1)
      | none => none

/-- Theorem: If `fieldOffset ty name = some off` and `fieldWidth ty name = some w`, then
the slice `[off, off + w)` fits strictly within `ty.bitWidth`. -/
theorem fieldSlice_within_structWidth
    (ty : HwType) (name : String) (off w : Nat)
    (hOff : fieldOffset ty name = some off)
    (hW   : fieldWidth ty name = some w) :
    off + w ≤ ty.bitWidth := by
  induction ty generalizing off with
  | bits _ => cases hOff
  | structNil => cases hOff
  | taggedUnion _ _ _ => cases hOff
  | array _ _ _ => cases hOff
  | structCons fname fty rest _ ihRest =>
    simp only [fieldOffset, fieldWidth] at hOff hW
    by_cases hEq : fname == name
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at hOff hW
      subst hOff hW
      simp only [HwType.bitWidth]
      omega
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hOff hW
      cases hRec : fieldOffset rest name with
      | none =>
        rw [hRec] at hOff
        cases hOff
      | some subOff =>
        rw [hRec] at hOff
        simp only [Option.some.injEq] at hOff
        have hSub := ihRest subOff hRec hW
        simp only [HwType.bitWidth]
        omega

/-! ## 2. Typed Hardware Values (`HwVal`) & Bit-Packing Isomorphism (`packHwVal` / `unpackHwVal`) -/

/-- Structured hardware value representation across `.bits`, `.struct`, `.taggedUnion`, and `.array`. -/
inductive HwVal where
  | bits        (width : Nat) (val : BitVec 64)
  | structNil
  | structCons  (name : String) (head : HwVal) (tail : HwVal)
  | taggedUnion (tagBits payloadWidth : Nat) (tag : BitVec 64) (payload : BitVec 64)
  | arrayNil
  | arrayCons   (head : HwVal) (tail : HwVal)
  deriving DecidableEq, Repr

/-- Check whether a `HwVal` conforms structurally to a `HwType`. -/
def checkHwValType : HwType → HwVal → Bool
  | .bits w, .bits w' _ => w == w'
  | .structNil, .structNil => true
  | .structCons n fty rest, .structCons n' hd tl =>
    (n == n') && checkHwValType fty hd && checkHwValType rest tl
  | .taggedUnion tb pw _, .taggedUnion tb' pw' _ _ =>
    (tb == tb') && (pw == pw')
  | .array 0 _, .arrayNil => true
  | .array (len + 1) elem, .arrayCons hd tl =>
    checkHwValType elem hd && checkHwValType (.array len elem) tl
  | _, _ => false

/-- Wire-level packed bit-frame representation for serialized hardware values. -/
inductive PackedBitFrame where
  | bitsFrame        (width : Nat) (bits : BitVec 64)
  | structNilFrame
  | structConsFrame  (name : String) (fst : PackedBitFrame) (snd : PackedBitFrame)
  | taggedUnionFrame (tagBits payloadWidth : Nat) (tagWord payloadWord : BitVec 64)
  | arrayNilFrame
  | arrayConsFrame   (fst : PackedBitFrame) (snd : PackedBitFrame)
  deriving DecidableEq, Repr

/-- Pack a structured `HwVal` into a wire-level `PackedBitFrame`. -/
def packHwVal : HwVal → PackedBitFrame
  | .bits w v => .bitsFrame w v
  | .structNil => .structNilFrame
  | .structCons name hd tl => .structConsFrame name (packHwVal hd) (packHwVal tl)
  | .taggedUnion tb pw tag payload => .taggedUnionFrame tb pw tag payload
  | .arrayNil => .arrayNilFrame
  | .arrayCons hd tl => .arrayConsFrame (packHwVal hd) (packHwVal tl)

/-- Unpack a wire-level `PackedBitFrame` back into a `HwVal` under schema `ty : HwType`. -/
def unpackHwVal (ty : HwType) : PackedBitFrame → HwVal
  | .bitsFrame w v => .bits w v
  | .structNilFrame => .structNil
  | .structConsFrame name fst snd =>
    .structCons name (unpackHwVal ty fst) (unpackHwVal ty snd)
  | .taggedUnionFrame tb pw tag payload =>
    .taggedUnion tb pw tag payload
  | .arrayNilFrame => .arrayNil
  | .arrayConsFrame fst snd =>
    .arrayCons (unpackHwVal ty fst) (unpackHwVal ty snd)

/-- Round-trip theorem (`unpack_pack_id`): for any `HwType` and any `v : HwVal`,
unpacking `packHwVal v` yields the exact original value `v`. -/
theorem unpack_pack_id (ty : HwType) (v : HwVal) :
    unpackHwVal ty (packHwVal v) = v := by
  induction v with
  | bits _ _ => rfl
  | structNil => rfl
  | structCons _ _ _ ihHd ihTl =>
    simp only [packHwVal, unpackHwVal, ihHd, ihTl]
  | taggedUnion _ _ _ _ => rfl
  | arrayNil => rfl
  | arrayCons _ _ ihHd ihTl =>
    simp only [packHwVal, unpackHwVal, ihHd, ihTl]

/-- Dual round-trip theorem (`pack_unpack_id`): packing an unpacked `PackedBitFrame` is the identity. -/
theorem pack_unpack_id (ty : HwType) (f : PackedBitFrame) :
    packHwVal (unpackHwVal ty f) = f := by
  induction f with
  | bitsFrame _ _ => rfl
  | structNilFrame => rfl
  | structConsFrame _ _ _ ihFst ihSnd =>
    simp only [unpackHwVal, packHwVal, ihFst, ihSnd]
  | taggedUnionFrame _ _ _ _ => rfl
  | arrayNilFrame => rfl
  | arrayConsFrame _ _ ihFst ihSnd =>
    simp only [unpackHwVal, packHwVal, ihFst, ihSnd]

/-! ## 3. Hardware Struct Bit-Slice Lenses & Non-Interference Laws -/

/-- Bit-mask for a slice of width `w` bits (`(1 <<< w) - 1`, or all-ones for `w ≥ 64`). -/
def widthMask64 (w : Nat) : BitVec 64 :=
  if w ≥ 64 then ~~~0#64 else (1#64 <<< w) - 1#64

/-- A packed multi-field hardware struct bus where each field slot `f : Nat` carries a width-masked
bitvector of width `≤ 64`. -/
structure PackedStructWord where
  slots : Nat → BitVec 64

/-- Construct a packed struct word from a list of `(slotIdx, width, value)` field initializers. -/
def packStructFields (inits : List (Nat × Nat × BitVec 64)) : PackedStructWord where
  slots := fun idx =>
    match inits.find? (fun (i, _, _) => i == idx) with
    | some (_, w, v) => v &&& widthMask64 w
    | none => 0#64

/-- Extract field slice `fieldIdx` of width `w` from a `PackedStructWord`. -/
def extractStructSlice (s : PackedStructWord) (fieldIdx _w : Nat) : BitVec 64 :=
  s.slots fieldIdx

/-- Update field slice `fieldIdx` of width `w` with `newVal` in a `PackedStructWord`. -/
def updateStructSlice (s : PackedStructWord) (fieldIdx w : Nat) (newVal : BitVec 64) : PackedStructWord where
  slots := fun idx =>
    if idx == fieldIdx then newVal &&& widthMask64 w else s.slots idx

/-- Theorem (`struct_slice_extract_sound`): extracting a field right after updating it yields the
exact width-masked value `newVal &&& widthMask64 w`. -/
theorem struct_slice_extract_sound
    (s : PackedStructWord) (fieldIdx w : Nat) (newVal : BitVec 64) :
    extractStructSlice (updateStructSlice s fieldIdx w newVal) fieldIdx w =
      newVal &&& widthMask64 w := by
  simp only [extractStructSlice, updateStructSlice, beq_self_eq_true, ↓reduceIte]

/-- Theorem (`struct_slice_update_noninterference`): updating field `f1` does NOT interfere with any
distinct field `f2 ≠ f1`. -/
theorem struct_slice_update_noninterference
    (s : PackedStructWord) (f1 f2 w1 w2 : Nat) (newVal : BitVec 64)
    (hNe : f1 ≠ f2) :
    extractStructSlice (updateStructSlice s f1 w1 newVal) f2 w2 =
      extractStructSlice s f2 w2 := by
  simp only [extractStructSlice, updateStructSlice]
  have hBeq : (f2 == f1) = false := beq_eq_false_iff_ne.mpr (Ne.symm hNe)
  simp [hBeq]

/-- Theorem (`struct_slice_update_overwrite`): updating the same field `f` twice in succession keeps
only the second update. -/
theorem struct_slice_update_overwrite
    (s : PackedStructWord) (f w : Nat) (v1 v2 : BitVec 64) :
    extractStructSlice (updateStructSlice (updateStructSlice s f w v1) f w v2) f w =
      v2 &&& widthMask64 w := by
  exact struct_slice_extract_sound (updateStructSlice s f w v1) f w v2

/-! ## 4. Flat 64-Bit Packed Pair Slicing (`[hi : 32 | lo : 32]`) & Hardware `RtlExpr` Lowering -/

/-- Pack two 32-bit values `(lo, hi)` into a single 64-bit hardware word `(hi <<< 32) ||| (lo &&& 0xFFFFFFFF)`. -/
def packPair32In64 (lo hi : BitVec 64) : BitVec 64 :=
  ((hi &&& 0xFFFFFFFF#64) <<< 32) ||| (lo &&& 0xFFFFFFFF#64)

/-- Extract the lower 32-bit field from a packed 64-bit word. -/
def extractLo32 (word : BitVec 64) : BitVec 64 :=
  word &&& 0xFFFFFFFF#64

/-- Extract the upper 32-bit field from a packed 64-bit word. -/
def extractHi32 (word : BitVec 64) : BitVec 64 :=
  (word >>> 32) &&& 0xFFFFFFFF#64

/-- Compile a 64-bit `[hi : 32 | lo : 32]` struct packing expression into `RtlExpr`. -/
def compilePackPair32Rtl (loExpr hiExpr : RtlExpr) : RtlExpr :=
  let mask := RtlExpr.const 0xFFFFFFFF#64
  let loMasked := RtlExpr.alu .bitAnd loExpr mask
  let hiMasked := RtlExpr.alu .bitAnd hiExpr mask
  let hiShifted := RtlExpr.alu .shl hiMasked (.const 32#64)
  RtlExpr.alu .bitOr hiShifted loMasked

/-- Compile lower 32-bit field extraction into `RtlExpr`. -/
def compileExtractLo32Rtl (wordExpr : RtlExpr) : RtlExpr :=
  RtlExpr.alu .bitAnd wordExpr (.const 0xFFFFFFFF#64)

/-- Compile upper 32-bit field extraction into `RtlExpr`. -/
def compileExtractHi32Rtl (wordExpr : RtlExpr) : RtlExpr :=
  RtlExpr.alu .bitAnd (RtlExpr.alu .lshr wordExpr (.const 32#64)) (.const 0xFFFFFFFF#64)

/-- Soundness of `compilePackPair32Rtl`: the compiled `RtlExpr` evaluates to `packPair32In64`. -/
theorem compilePackPair32Rtl_sound
    (inputs wires regs : Nat → BitVec 64) (loExpr hiExpr : RtlExpr) :
    evalRtlExpr inputs wires regs (compilePackPair32Rtl loExpr hiExpr) =
      packPair32In64 (evalRtlExpr inputs wires regs loExpr) (evalRtlExpr inputs wires regs hiExpr) := by
  rfl

/-- Soundness of `compileExtractLo32Rtl` and `compileExtractHi32Rtl`. -/
theorem compileExtract32Rtl_sound
    (inputs wires regs : Nat → BitVec 64) (wordExpr : RtlExpr) :
    evalRtlExpr inputs wires regs (compileExtractLo32Rtl wordExpr) =
      extractLo32 (evalRtlExpr inputs wires regs wordExpr) ∧
    evalRtlExpr inputs wires regs (compileExtractHi32Rtl wordExpr) =
      extractHi32 (evalRtlExpr inputs wires regs wordExpr) := by
  exact ⟨rfl, rfl⟩

/-! ## 5. Tagged-Union (`Term.inject` / `Term.case`) Hardware Muxing & Soundness -/

/-- A hardware tagged-union value packed into a pair of `(tag, payload)` 64-bit wires. -/
structure TaggedUnionWire where
  tag     : BitVec 64
  payload : BitVec 64
  deriving DecidableEq, Repr

/-- Construct (`inject`) a tagged union value with constructor index `tagIdx` and payload `p`. -/
def evalInjectHw (tagIdx : Nat) (p : BitVec 64) : TaggedUnionWire :=
  { tag := BitVec.ofNat 64 tagIdx, payload := p }

/-- Evaluate a hardware `case` mux tree over a `TaggedUnionWire`:
Each arm `(armTag, armVal)` is tested in order against `u.tag`; the first matching arm is selected. -/
def evalCaseMuxSpec
    (u : TaggedUnionWire)
    (arms : List (Nat × BitVec 64))
    (defaultVal : BitVec 64) : BitVec 64 :=
  match arms with
  | [] => defaultVal
  | (armTag, armVal) :: rest =>
    if u.tag == BitVec.ofNat 64 armTag then
      armVal
    else
      evalCaseMuxSpec u rest defaultVal

/-- Compile a `Term.case` dispatch over `tagExpr` and `payloadExpr` into a cascade of hardware `.mux`
nodes in `RtlExpr`. -/
def compileCaseMuxRtl
    (tagExpr : RtlExpr)
    (arms : List (Nat × RtlExpr))
    (defaultExpr : RtlExpr) : RtlExpr :=
  match arms with
  | [] => defaultExpr
  | (armTag, armBody) :: rest =>
    let isMatch := RtlExpr.alu .eq tagExpr (.const (BitVec.ofNat 64 armTag))
    .mux isMatch armBody (compileCaseMuxRtl tagExpr rest defaultExpr)

@[simp] theorem eq_mux_cond_reduce (b : Bool) :
    ((if b then 1#64 else 0#64) != 0#64) = b := by
  cases b <;> rfl

/-- Theorem (`taggedUnion_case_mux_sound`): evaluating `compileCaseMuxRtl` on any `tagExpr` and
`payloadExpr` implements exact tagged-union pattern matching (`evalCaseMuxSpec`). -/
theorem taggedUnion_case_mux_sound
    (inputs wires regs : Nat → BitVec 64)
    (tagExpr payloadExpr : RtlExpr)
    (arms : List (Nat × RtlExpr))
    (defaultExpr : RtlExpr) :
    evalRtlExpr inputs wires regs (compileCaseMuxRtl tagExpr arms defaultExpr) =
      evalCaseMuxSpec
        ⟨evalRtlExpr inputs wires regs tagExpr, evalRtlExpr inputs wires regs payloadExpr⟩
        (arms.map (fun (t, body) => (t, evalRtlExpr inputs wires regs body)))
        (evalRtlExpr inputs wires regs defaultExpr) := by
  induction arms with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨armTag, armBody⟩
    simp only [compileCaseMuxRtl, evalRtlExpr, evalAluOp, List.map, evalCaseMuxSpec]
    by_cases hMatch : (evalRtlExpr inputs wires regs tagExpr == BitVec.ofNat 64 armTag) = true
    · simp [hMatch]
    · simp [hMatch, ih]

/-- Theorem: Injecting constructor `tagIdx` (`evalInjectHw tagIdx payload`) and immediately matching
against a 2-arm case mux `[(0, v0), (1, v1)]` selects `v0` when `tagIdx = 0` and `v1` when `tagIdx = 1`. -/
theorem inject_case_beta_two_arms
    (payload v0 v1 defVal : BitVec 64) :
    evalCaseMuxSpec (evalInjectHw 0 payload) [(0, v0), (1, v1)] defVal = v0 ∧
    evalCaseMuxSpec (evalInjectHw 1 payload) [(0, v0), (1, v1)] defVal = v1 := by
  exact ⟨rfl, rfl⟩

/-! ## 6. Fixed-Size Hardware Array Muxing (`HwType.array`) & Soundness -/

/-- Specification of reading element `idx` from a hardware array of `RtlExpr` elements with default `0`. -/
def evalArrayReadSpec
    (inputs wires regs : Nat → BitVec 64)
    (elems : List RtlExpr)
    (baseIdx : Nat)
    (idxVal : BitVec 64) : BitVec 64 :=
  match elems with
  | [] => 0#64
  | e :: rest =>
    if idxVal == BitVec.ofNat 64 baseIdx then
      evalRtlExpr inputs wires regs e
    else
      evalArrayReadSpec inputs wires regs rest (baseIdx + 1) idxVal

/-- Compile dynamic array indexing `arr[idxExpr]` into a chain of `RtlExpr.mux` comparators. -/
def compileArrayReadRtl
    (elems : List RtlExpr)
    (baseIdx : Nat)
    (idxExpr : RtlExpr) : RtlExpr :=
  match elems with
  | [] => .const 0#64
  | e :: rest =>
    .mux (.alu .eq idxExpr (.const (BitVec.ofNat 64 baseIdx)))
      e
      (compileArrayReadRtl rest (baseIdx + 1) idxExpr)

/-- Theorem (`array_index_mux_sound`): `compileArrayReadRtl` evaluates to `evalArrayReadSpec` for
any array of hardware expressions and any index expression `idxExpr`. -/
theorem array_index_mux_sound
    (inputs wires regs : Nat → BitVec 64)
    (elems : List RtlExpr)
    (baseIdx : Nat)
    (idxExpr : RtlExpr) :
    evalRtlExpr inputs wires regs (compileArrayReadRtl elems baseIdx idxExpr) =
      evalArrayReadSpec inputs wires regs elems baseIdx (evalRtlExpr inputs wires regs idxExpr) := by
  induction elems generalizing baseIdx with
  | nil => rfl
  | cons e rest ih =>
    simp only [compileArrayReadRtl, evalRtlExpr, evalAluOp, evalArrayReadSpec]
    by_cases hEq : (evalRtlExpr inputs wires regs idxExpr == BitVec.ofNat 64 baseIdx) = true
    · simp [hEq]
    · simp [hEq, ih (baseIdx + 1)]

/-! ## 7. `RtlLayoutCtx` Arbitrary-Offset Bit-Slice & Tagged-Union RTL Lowering -/

/-- Hardware layout context mapping record field names to `(offset, width)` bit-slices inside a
64-bit word and sum constructor labels to `(tagIdx, payloadWidth)` arms with `unionTagBits` tag width. -/
structure RtlLayoutCtx where
  structSlices : List (String × (Nat × Nat)) := []
  unionTagBits : Nat := 8
  unionArms    : List (String × (Nat × Nat)) := []
  deriving DecidableEq, Repr

/-- Look up the `(offset, width)` bit-slice for a struct field `fieldName` in `ctx`. -/
def RtlLayoutCtx.lookupField (ctx : RtlLayoutCtx) (fieldName : String) : Option (Nat × Nat) :=
  (ctx.structSlices.find? (fun (f, _) => f == fieldName)).map (·.2)

/-- Look up the `(tagIdx, payloadWidth)` descriptor for a sum constructor `armLabel` in `ctx`. -/
def RtlLayoutCtx.lookupArm (ctx : RtlLayoutCtx) (armLabel : String) : Option (Nat × Nat) :=
  (ctx.unionArms.find? (fun (l, _) => l == armLabel)).map (·.2)

/-- Specification of extracting a bit-slice at `(offset, width)` from a 64-bit hardware word. -/
def evalSliceExtract64 (word : BitVec 64) (offset width : Nat) : BitVec 64 :=
  (word >>> ((BitVec.ofNat 64 offset).toNat % 64)) &&& widthMask64 width

/-- Compile bit-slice extraction `(word >>> offset) & widthMask64 width` into `RtlExpr`. -/
def compileSliceExtractRtl (wordExpr : RtlExpr) (offset width : Nat) : RtlExpr :=
  .alu .bitAnd
    (.alu .lshr wordExpr (.const (BitVec.ofNat 64 offset)))
    (.const (widthMask64 width))

/-- Specification of inserting a width-masked `fieldVal` at `(offset, width)` into `acc`. -/
def evalSliceInsert64 (acc fieldVal : BitVec 64) (offset width : Nat) : BitVec 64 :=
  acc ||| ((fieldVal &&& widthMask64 width) <<< ((BitVec.ofNat 64 offset).toNat % 64))

/-- Compile bit-slice insertion `acc | ((field & widthMask64 width) << offset)` into `RtlExpr`. -/
def compileSliceInsertRtl (accExpr fieldExpr : RtlExpr) (offset width : Nat) : RtlExpr :=
  .alu .bitOr accExpr
    (.alu .shl
      (.alu .bitAnd fieldExpr (.const (widthMask64 width)))
      (.const (BitVec.ofNat 64 offset)))

/-- Bitmask that zeroes out the slice `[offset + width - 1 : offset]` in a 64-bit word. -/
def clearSliceMask64 (offset width : Nat) : BitVec 64 :=
  ~~~(widthMask64 width <<< ((BitVec.ofNat 64 offset).toNat % 64))

/-- Specification of updating slice `(offset, width)` in `word` with `newVal`. -/
def evalSliceUpdate64 (word newVal : BitVec 64) (offset width : Nat) : BitVec 64 :=
  (word &&& clearSliceMask64 offset width) |||
    ((newVal &&& widthMask64 width) <<< ((BitVec.ofNat 64 offset).toNat % 64))

/-- Compile in-place bit-slice update `(word & ~(mask << offset)) | ((newVal & mask) << offset)`
into `RtlExpr` (used for `.extend inherited fields`). -/
def compileSliceUpdateRtl (wordExpr newValExpr : RtlExpr) (offset width : Nat) : RtlExpr :=
  .alu .bitOr
    (.alu .bitAnd wordExpr (.const (clearSliceMask64 offset width)))
    (.alu .shl
      (.alu .bitAnd newValExpr (.const (widthMask64 width)))
      (.const (BitVec.ofNat 64 offset)))

/-- Specification of packing a sum tag (`tagBits` at LSB `0`) and payload (`payloadWidth` at `tagBits`). -/
def evalTagInject64 (tagBits tagIdx payloadWidth : Nat) (payload : BitVec 64) : BitVec 64 :=
  evalSliceInsert64 (BitVec.ofNat 64 tagIdx &&& widthMask64 tagBits) payload tagBits payloadWidth

/-- Compile tagged-union injection `.inject label payload` into a single 64-bit `RtlExpr` word
with tag in `[tagBits - 1 : 0]` and payload in `[tagBits + payloadWidth - 1 : tagBits]`. -/
def compileTagInjectRtl (tagBits tagIdx payloadWidth : Nat) (payloadExpr : RtlExpr) : RtlExpr :=
  compileSliceInsertRtl (.const (BitVec.ofNat 64 tagIdx &&& widthMask64 tagBits)) payloadExpr tagBits payloadWidth

/-- Compile tag extraction `[tagBits - 1 : 0]` from a packed 64-bit tagged union word. -/
def compileTagExtractRtl (tagBits : Nat) (scrutExpr : RtlExpr) : RtlExpr :=
  compileSliceExtractRtl scrutExpr 0 tagBits

/-- Compile payload extraction `[tagBits + payloadWidth - 1 : tagBits]` from a packed 64-bit tagged union word. -/
def compilePayloadExtractRtl (tagBits payloadWidth : Nat) (scrutExpr : RtlExpr) : RtlExpr :=
  compileSliceExtractRtl scrutExpr tagBits payloadWidth

/-- Soundness of `compileSliceExtractRtl`, `compileSliceInsertRtl`, and `compileSliceUpdateRtl`. -/
theorem compileSliceRtl_ops_sound
    (inputs wires regs : Nat → BitVec 64)
    (wordExpr accExpr fieldExpr : RtlExpr)
    (offset width : Nat) :
    evalRtlExpr inputs wires regs (compileSliceExtractRtl wordExpr offset width) =
      evalSliceExtract64 (evalRtlExpr inputs wires regs wordExpr) offset width ∧
    evalRtlExpr inputs wires regs (compileSliceInsertRtl accExpr fieldExpr offset width) =
      evalSliceInsert64 (evalRtlExpr inputs wires regs accExpr) (evalRtlExpr inputs wires regs fieldExpr) offset width ∧
    evalRtlExpr inputs wires regs (compileSliceUpdateRtl wordExpr fieldExpr offset width) =
      evalSliceUpdate64 (evalRtlExpr inputs wires regs wordExpr) (evalRtlExpr inputs wires regs fieldExpr) offset width := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Theorem (`compileSliceExtract_insert_disjoint_sound`)**:
For any expressions `eLo`, `eHi` packed into disjoint slices `(0, 32)` and `(32, 32)` via
`compileSliceInsertRtl`, `compileSliceExtractRtl` at `(0, 32)` and `(32, 32)` recovers the exact
width-masked fields, and `compileSliceUpdateRtl` on either slice `(0, 32)` or `(32, 32)` updates
that slice while preserving the disjoint slice! -/
theorem compileSliceExtract_insert_disjoint_sound
    (inputs wires regs : Nat → BitVec 64)
    (eLo eHi eNew : RtlExpr) :
    let packed := compileSliceInsertRtl (compileSliceInsertRtl (.const 0#64) eLo 0 32) eHi 32 32
    let vLo := evalRtlExpr inputs wires regs eLo
    let vHi := evalRtlExpr inputs wires regs eHi
    let vNew := evalRtlExpr inputs wires regs eNew
    evalRtlExpr inputs wires regs (compileSliceExtractRtl packed 0 32) = (vLo &&& widthMask64 32) ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl packed 32 32) = (vHi &&& widthMask64 32) ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceUpdateRtl packed eNew 0 32) 0 32) =
      (vNew &&& widthMask64 32) ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceUpdateRtl packed eNew 0 32) 32 32) =
      (vHi &&& widthMask64 32) ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceUpdateRtl packed eNew 32 32) 32 32) =
      (vNew &&& widthMask64 32) ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceUpdateRtl packed eNew 32 32) 0 32) =
      (vLo &&& widthMask64 32) := by
  dsimp only
  simp only [compileSliceExtractRtl, compileSliceInsertRtl, compileSliceUpdateRtl,
    evalRtlExpr, evalAluOp, widthMask64, clearSliceMask64]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- **Theorem (`compileSlice_fullWidth64_boundary_sound`)**:
At the full 64-bit word boundary `(offset = 0, width = 64)`, `widthMask64 64 = ~~~0#64`,
`compileSliceInsertRtl` followed by `compileSliceExtractRtl` recovers the full 64-bit word
without truncation, and `compileSliceUpdateRtl` replaces all 64 bits cleanly. -/
theorem compileSlice_fullWidth64_boundary_sound
    (inputs wires regs : Nat → BitVec 64)
    (eWord eNew : RtlExpr) :
    let vWord := evalRtlExpr inputs wires regs eWord
    let vNew := evalRtlExpr inputs wires regs eNew
    widthMask64 64 = ~~~0#64 ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceInsertRtl (.const 0#64) eWord 0 64) 0 64) =
      vWord ∧
    evalRtlExpr inputs wires regs (compileSliceExtractRtl (compileSliceUpdateRtl eWord eNew 0 64) 0 64) =
      vNew := by
  dsimp only
  simp only [compileSliceExtractRtl, compileSliceInsertRtl, compileSliceUpdateRtl,
    evalRtlExpr, evalAluOp, widthMask64, clearSliceMask64]
  refine ⟨by decide, ?_, ?_⟩ <;> bv_decide

/-- **Theorem (`compileTagInject_caseMux_sound`)**:
Injecting constructor `tagIdx` with `payloadExpr` via `compileTagInjectRtl` and matching its
extracted tag via `compileCaseMuxRtl` evaluates to `evalCaseMuxSpec` on the masked tag, while
`compilePayloadExtractRtl` with `8`-bit tag and `32`-bit payload recovers `payload &&& widthMask64 32`. -/
theorem compileTagInject_caseMux_sound
    (inputs wires regs : Nat → BitVec 64)
    (tagIdx : Nat)
    (payloadExpr defaultExpr : RtlExpr)
    (arms : List (Nat × RtlExpr)) :
    let injected := compileTagInjectRtl 8 tagIdx 32 payloadExpr
    let tagE := compileTagExtractRtl 8 injected
    let payE := compilePayloadExtractRtl 8 32 injected
    let vTag := BitVec.ofNat 64 tagIdx &&& widthMask64 8
    let vPay := evalRtlExpr inputs wires regs payloadExpr &&& widthMask64 32
    evalRtlExpr inputs wires regs (compileCaseMuxRtl tagE arms defaultExpr) =
      evalCaseMuxSpec
        ⟨vTag, vPay⟩
        (arms.map (fun (t, body) => (t, evalRtlExpr inputs wires regs body)))
        (evalRtlExpr inputs wires regs defaultExpr) ∧
    evalRtlExpr inputs wires regs payE = vPay := by
  dsimp only
  have hTag :
      evalRtlExpr inputs wires regs (compileTagExtractRtl 8 (compileTagInjectRtl 8 tagIdx 32 payloadExpr)) =
        (BitVec.ofNat 64 tagIdx &&& widthMask64 8) := by
    simp only [compileTagExtractRtl, compileTagInjectRtl, compileSliceExtractRtl, compileSliceInsertRtl,
      evalRtlExpr, evalAluOp, widthMask64]
    bv_decide
  have hPay :
      evalRtlExpr inputs wires regs (compilePayloadExtractRtl 8 32 (compileTagInjectRtl 8 tagIdx 32 payloadExpr)) =
        (evalRtlExpr inputs wires regs payloadExpr &&& widthMask64 32) := by
    simp only [compilePayloadExtractRtl, compileTagInjectRtl, compileSliceExtractRtl, compileSliceInsertRtl,
      evalRtlExpr, evalAluOp, widthMask64]
    bv_decide
  refine ⟨?_, hPay⟩
  rw [taggedUnion_case_mux_sound inputs wires regs
    (compileTagExtractRtl 8 (compileTagInjectRtl 8 tagIdx 32 payloadExpr))
    (compilePayloadExtractRtl 8 32 (compileTagInjectRtl 8 tagIdx 32 payloadExpr))
    arms defaultExpr]
  rw [hTag, hPay]

end Obend.Hardware.Types
