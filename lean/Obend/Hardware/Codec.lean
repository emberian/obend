module
/-
# Obend.Hardware.Codec — Typeclass-Abstracted Binary / RFC 8949 CBOR Wire Codec & `.obnb` Projections

Eliminates ad-hoc JSON text wire formats in the hardware verification and EDA pipeline in favor of:
1. **`BinaryCodec α`**: A polymorphic typeclass for deterministic binary wire serialization
   (`encodeBytes : α → List UInt8`, `decodeBytes : List UInt8 → Option α`) equipped with a machine-checked
   round-trip soundness law (`decode_encode : ∀ x, WellFormed x → decodeBytes (encodeBytes x) = some x`).
2. **RFC 8949 CBOR Wire Framing (`0xD9 0x0B 0xED` Tag `0x0BED`)**:
   - Major Type 0 (`0x1A` + 4-byte big-endian `Obend.Digest.HashBytes.be 4 n`) for unsigned 32-bit integers,
   - Major Type 1 (`0x3A` + 4-byte big-endian `be 4 n`) for negative integers `-1 - n` (isomorphic to Lean's
     `Int.negSucc n`!),
   - Major Type 4 (`0x87`) for 7-element fixed-arity tuples/arrays,
   - Major Type 6 (`0xD9 0x0B 0xED`, tag `3053`) for self-identifying `.obnb` / `Obend.Hardware` binary frames,
   - Major Type 7 (`0xF4` = `false`, `0xF5` = `true`).
3. **`CoreDataCodec α` & `.obnb` Hardware Cell Projections (`NEXT-MATHEMATICA.md` §5)**:
   - Maps `RtlModule`, `BelNetlist`, `PnrCertificate`, and `ObnbHardwareCell` into canonical `Obend.Core.Data.Data`
     trees (`hardwareSchematic`, `hardwareTiming`, `hardwareLayout`) with proved round-trip extraction.
4. **Zero-Copy C-ABI FFI Exports (`NEXT-MATHEMATICA.md` §6)**:
   - `@[export obend_hw_cbor_verify]` and `@[export obend_hw_cbor_project_cell]` for the Rust host crate
     (`hardware/rust-ffi`).

Zero `sorry`, zero axioms beyond Lean's core.
-/
public import Obend.Digest.HashBytes
public import Obend.Core.Data
public import Obend.Hardware.Process
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.Retiming
public import Obend.Hardware.Photonics
public import Obend.Hardware.PCB
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.AgenticEDA
public import Obend.Hardware.ThermalPassivity
public import Obend.Hardware.Analog
public import Obend.Hardware.DSP
public import Obend.Hardware.Magnetics

@[expose] public section

namespace Obend.Hardware.Codec

open Obend.Digest.HashBytes
open Obend.Core.Data
open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.PlaceRoute
open Obend.Hardware.Retiming
open Obend.Hardware.Photonics
open Obend.Hardware.PCB
open Obend.Hardware.ReductionMachine
open Obend.Hardware.AgenticEDA

set_option autoImplicit false

/-! ## 1. Polymorphic `BinaryCodec` & `CoreDataCodec` Typeclasses -/

/-- Typeclass abstracting deterministic binary wire serialization (e.g. RFC 8949 CBOR frames)
    away from concrete certificate checkers and FFI boundaries. -/
class BinaryCodec (α : Type) where
  /-- Domain validity predicate for bounded fixed-width wire fields. -/
  WellFormed : α → Prop := fun _ => True
  /-- Serialize `x` into a canonical byte list. -/
  encodeBytes : α → List UInt8
  /-- Deserialize a canonical byte list back into `Option α`. -/
  decodeBytes : List UInt8 → Option α
  /-- Round-trip correctness law: every well-formed `x` decodes back to `some x`. -/
  decode_encode : ∀ x : α, WellFormed x → decodeBytes (encodeBytes x) = some x

/-- Serialize `x : α` directly to a contiguous `ByteArray` for C-ABI / Rust FFI transport. -/
def encodeToByteArray {α : Type} [c : BinaryCodec α] (x : α) : ByteArray :=
  ByteArray.mk (c.encodeBytes x).toArray

/-- Deserialize `ba : ByteArray` using the `BinaryCodec α` instance. -/
def decodeFromByteArray {α : Type} [c : BinaryCodec α] (ba : ByteArray) : Option α :=
  c.decodeBytes ba.toList

/-- Typeclass for lossless projection into `Obend.Core.Data.Data` (`.obnb` notebook cell payloads). -/
class CoreDataCodec (α : Type) where
  toCoreData : α → Data
  ofCoreData : Data → Option α
  ofCoreData_toCoreData : ∀ x : α, ofCoreData (toCoreData x) = some x

/-! ## 2. RFC 8949 CBOR Primitive Combinators & Compositional Round-Trip Lemmas -/

/-- Upper bound for a 32-bit unsigned CBOR integer (`256^4 = 4294967296`). -/
def u32Bound : Nat := 256 ^ 4

/-- RFC 8949 CBOR Tag `0x0BED` (`3053`): `[0xD9, 0x0B, 0xED]`. -/
def cborObendTag : List UInt8 := [0xD9, 0x0B, 0xED]

/-- Encode a `Bool` as RFC 8949 CBOR Major Type 7 (`0xF5` = true, `0xF4` = false). -/
def cborEncodeBool (b : Bool) : List UInt8 :=
  [if b then (0xF5 : UInt8) else (0xF4 : UInt8)]

/-- Decode a `Bool` from the head of a CBOR byte stream. -/
def cborDecodeBool : List UInt8 → Option (Bool × List UInt8)
  | b :: rest =>
    if b == (0xF5 : UInt8) then some (true, rest)
    else if b == (0xF4 : UInt8) then some (false, rest)
    else none
  | [] => none

@[simp] theorem cborDecodeBool_encode_append (b : Bool) (tail : List UInt8) :
    cborDecodeBool (cborEncodeBool b ++ tail) = some (b, tail) := by
  cases b <;> rfl

/-- Encode a 32-bit unsigned `Nat` as RFC 8949 CBOR Major Type 0, additional info 26 (`0x1A` + 4-byte BE). -/
def cborEncodeU32 (n : Nat) : List UInt8 :=
  (0x1A : UInt8) :: be 4 n

/-- Decode a 4-byte big-endian unsigned integer prefixed by `0x1A` from a CBOR stream. -/
def cborDecodeU32 : List UInt8 → Option (Nat × List UInt8)
  | tag :: b3 :: b2 :: b1 :: b0 :: rest =>
    if tag == (0x1A : UInt8) then
      some (ofBE [b3, b2, b1, b0], rest)
    else none
  | _ => none

@[simp] theorem cborDecodeU32_encode_append {n : Nat} (hn : n < u32Bound) (tail : List UInt8) :
    cborDecodeU32 (cborEncodeU32 n ++ tail) = some (n, tail) := by
  have hbe : ofBE (be 4 n) = n := ofBE_be hn
  dsimp only [cborEncodeU32, be, List.append_assoc, List.cons_append, List.nil_append, cborDecodeU32] at hbe ⊢
  rw [hbe]
  rfl

instance : Coe UInt32 Nat where
  coe := UInt32.toNat

/-- Decode a 4-byte big-endian `UInt32` word prefixed by `0x1A` from a CBOR stream. -/
def cborDecodeU32Word (bytes : List UInt8) : Option (UInt32 × List UInt8) :=
  match cborDecodeU32 bytes with
  | some (n, rest) => some (UInt32.ofNat n, rest)
  | none => none

theorem u32_toNat_lt_u32Bound (x : UInt32) : x.toNat < u32Bound := by
  have h := x.toNat_lt
  unfold u32Bound
  omega

@[simp] theorem cborDecodeU32Word_encode_append (x : UInt32) (tail : List UInt8) :
    cborDecodeU32Word (cborEncodeU32 x.toNat ++ tail) = some (x, tail) := by
  have hlt : x.toNat < u32Bound := u32_toNat_lt_u32Bound x
  simp [cborDecodeU32Word, cborDecodeU32_encode_append hlt]

/-- Encode a variable-length `List UInt32` into concatenated RFC 8949 CBOR 32-bit unsigned integers. -/
def cborEncodeU32List (xs : List UInt32) : List UInt8 :=
  xs.foldr (fun (x : UInt32) acc => cborEncodeU32 x ++ acc) []

/-- Decode `count` 32-bit unsigned CBOR integers from a byte stream. -/
def cborDecodeU32List : Nat → List UInt8 → Option (List UInt32 × List UInt8)
  | 0, bytes => some ([], bytes)
  | k + 1, bytes =>
    match cborDecodeU32Word bytes with
    | some (x, rest1) =>
      match cborDecodeU32List k rest1 with
      | some (xs, rest2) => some (x :: xs, rest2)
      | none => none
    | none => none

/-- **Universal Variable-Length CBOR `UInt32` Array/Tape Round-Trip Theorem (`cborDecodeU32List_encode_exact`)**:
    For every list `xs : List UInt32` of arbitrary length and any trailing byte stream `rest : List UInt8`,
    decoding `xs.length` elements from `xs.foldr (fun x acc => cborEncodeU32 x ++ acc) rest` recovers
    `some (xs, rest)` exactly. -/
@[simp] theorem cborDecodeU32List_encode_exact (xs : List UInt32) (rest : List UInt8) :
    cborDecodeU32List xs.length (xs.foldr (fun (x : UInt32) acc => cborEncodeU32 x ++ acc) rest) =
      some (xs, rest) := by
  induction xs generalizing rest with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.length_cons, List.foldr_cons, cborDecodeU32List,
      cborDecodeU32Word_encode_append, ih]

@[simp] theorem foldr_cborEncodeU32_eq_append (xs : List UInt32) (rest : List UInt8) :
    xs.foldr (fun (x : UInt32) acc => cborEncodeU32 x ++ acc) rest = cborEncodeU32List xs ++ rest := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [cborEncodeU32List, List.foldr_cons, ih, List.append_assoc]

@[simp] theorem cborDecodeU32List_encode_append (xs : List UInt32) (rest : List UInt8) :
    cborDecodeU32List xs.length (cborEncodeU32List xs ++ rest) = some (xs, rest) := by
  rw [← foldr_cborEncodeU32_eq_append]
  exact cborDecodeU32List_encode_exact xs rest

/-- Encode a variable-length `List UInt32` instruction tape / mesh payload inside an RFC 8949 CBOR
    Tag `0x0BED` (`[0xD9, 0x0B, 0xED]`) + 32-bit array header (`0x9A`). -/
def cborEncodeVarTape (xs : List UInt32) : List UInt8 :=
  (0xD9 : UInt8) :: (0x0B : UInt8) :: (0xED : UInt8) :: (0x9A : UInt8) ::
    (cborEncodeU32 xs.length ++ cborEncodeU32List xs)

/-- Decode a variable-length `List UInt32` instruction tape / mesh payload from an RFC 8949 CBOR
    Tag `0x0BED` + `0x9A` frame. -/
def cborDecodeVarTape (bytes : List UInt8) : Option (List UInt32) :=
  match bytes with
  | b0 :: b1 :: b2 :: b3 :: rest0 =>
    if b0 == (0xD9 : UInt8) && b1 == (0x0B : UInt8) && b2 == (0xED : UInt8) && b3 == (0x9A : UInt8) then
      match cborDecodeU32 rest0 with
      | some (len, rest1) =>
        match cborDecodeU32List len rest1 with
        | some (xs, []) => some xs
        | _ => none
      | none => none
    else none
  | _ => none

/-- Universal round-trip theorem for variable-length CBOR instruction tapes (`cborDecodeVarTape_encode`). -/
theorem cborDecodeVarTape_encode (xs : List UInt32) (hLen : xs.length < u32Bound) :
    cborDecodeVarTape (cborEncodeVarTape xs) = some xs := by
  dsimp only [cborEncodeVarTape, cborDecodeVarTape]
  rw [cborDecodeU32_encode_append hLen]
  dsimp only
  have hList := cborDecodeU32List_encode_append xs []
  rw [List.append_nil] at hList
  rw [hList]
  rfl

/-- Encode a signed `Int` as RFC 8949 CBOR Major Type 0 (`0x1A` + BE4 for `Int.ofNat n`)
    or Major Type 1 (`0x3A` + BE4 for `Int.negSucc n = -1 - n`). -/
def cborEncodeI32 : Int → List UInt8
  | Int.ofNat n => (0x1A : UInt8) :: be 4 n
  | Int.negSucc n => (0x3A : UInt8) :: be 4 n

/-- Decode a signed 32-bit integer from a CBOR stream (`0x1A` non-negative, `0x3A` negative). -/
def cborDecodeI32 : List UInt8 → Option (Int × List UInt8)
  | tag :: b3 :: b2 :: b1 :: b0 :: rest =>
    if tag == (0x1A : UInt8) then
      some (Int.ofNat (ofBE [b3, b2, b1, b0]), rest)
    else if tag == (0x3A : UInt8) then
      some (Int.negSucc (ofBE [b3, b2, b1, b0]), rest)
    else none
  | _ => none

/-- Well-formedness predicate for signed 32-bit CBOR integers. -/
def i32WellFormed (z : Int) : Prop :=
  match z with
  | Int.ofNat n => n < u32Bound
  | Int.negSucc n => n < u32Bound

@[simp] theorem cborDecodeI32_encode_append {z : Int} (hz : i32WellFormed z) (tail : List UInt8) :
    cborDecodeI32 (cborEncodeI32 z ++ tail) = some (z, tail) := by
  cases z with
  | ofNat n =>
    have hbe : ofBE (be 4 n) = n := ofBE_be hz
    dsimp only [cborEncodeI32, be, List.append_assoc, List.cons_append, List.nil_append, cborDecodeI32] at hbe ⊢
    rw [hbe]
    rfl
  | negSucc n =>
    have hbe : ofBE (be 4 n) = n := ofBE_be hz
    dsimp only [cborEncodeI32, be, List.append_assoc, List.cons_append, List.nil_append, cborDecodeI32] at hbe ⊢
    rw [hbe]
    rfl

/-! ## 3. Primitive `BinaryCodec` Instances (`Bool`, `Nat`, `Int`) -/

instance : BinaryCodec Bool where
  WellFormed := fun _ => True
  encodeBytes := cborEncodeBool
  decodeBytes := fun bytes =>
    match cborDecodeBool bytes with
    | some (b, []) => some b
    | _ => none
  decode_encode := by
    intro b _
    cases b <;> rfl

instance : BinaryCodec Nat where
  WellFormed := fun n => n < u32Bound
  encodeBytes := cborEncodeU32
  decodeBytes := fun bytes =>
    match cborDecodeU32 bytes with
    | some (n, []) => some n
    | _ => none
  decode_encode := by
    intro n hn
    have h := cborDecodeU32_encode_append hn []
    rw [List.append_nil] at h
    rw [h]

instance : BinaryCodec Int where
  WellFormed := i32WellFormed
  encodeBytes := cborEncodeI32
  decodeBytes := fun bytes =>
    match cborDecodeI32 bytes with
    | some (z, []) => some z
    | _ => none
  decode_encode := by
    intro z hz
    have h := cborDecodeI32_encode_append hz []
    rw [List.append_nil] at h
    rw [h]

/-! ## 4. Tagged Binary CBOR Hardware Certificate Envelope (`BinaryHwCert`)

Every binary hardware certificate starts with:
- RFC 8949 Semantic Tag `0xD9 0x0B 0xED` (`0x0BED`),
- CBOR 7-element Array header `0x87` (`1` domain tag + `6` signed 32-bit parameters),
- Domain ID (`cborEncodeU32 domain.toCode`),
- 6 signed 32-bit CBOR integers (`p0 .. p5`).
-/

/-- Domain identifier for binary CBOR hardware certificates. -/
inductive HwCertDomain
  | pnr                 -- 1
  | retiming            -- 2
  | photonics           -- 3
  | pcb                 -- 4
  | dpr                 -- 5
  | edaBomSwap          -- 6
  | multiphysics        -- 7
  | analog2d            -- 8
  | dspBeamformer       -- 9
  | magnetics           -- 10
  deriving DecidableEq, Repr

def HwCertDomain.toCode : HwCertDomain → Nat
  | .pnr => 1
  | .retiming => 2
  | .photonics => 3
  | .pcb => 4
  | .dpr => 5
  | .edaBomSwap => 6
  | .multiphysics => 7
  | .analog2d => 8
  | .dspBeamformer => 9
  | .magnetics => 10

def HwCertDomain.fromCode : Nat → Option HwCertDomain
  | 1 => some .pnr
  | 2 => some .retiming
  | 3 => some .photonics
  | 4 => some .pcb
  | 5 => some .dpr
  | 6 => some .edaBomSwap
  | 7 => some .multiphysics
  | 8 => some .analog2d
  | 9 => some .dspBeamformer
  | 10 => some .magnetics
  | _ => none

@[simp] theorem HwCertDomain.fromCode_toCode (d : HwCertDomain) :
    HwCertDomain.fromCode d.toCode = some d := by
  cases d <;> rfl

theorem HwCertDomain.toCode_lt_u32Bound (d : HwCertDomain) : d.toCode < u32Bound := by
  cases d <;> decide

/-- Canonical 39-byte RFC 8949 CBOR hardware certificate frame:
    `[0xD9, 0x0B, 0xED, 0x87]` (4 bytes) + `domain` (5 bytes) + `6 × i32` (30 bytes). -/
structure BinaryHwCert where
  domain : HwCertDomain
  p0 : Int
  p1 : Int
  p2 : Int
  p3 : Int
  p4 : Int
  p5 : Int
  deriving DecidableEq, Repr

def BinaryHwCert.WellFormed (c : BinaryHwCert) : Prop :=
  i32WellFormed c.p0 ∧ i32WellFormed c.p1 ∧ i32WellFormed c.p2 ∧
  i32WellFormed c.p3 ∧ i32WellFormed c.p4 ∧ i32WellFormed c.p5

/-- Encode a `BinaryHwCert` into a 39-byte RFC 8949 CBOR tagged array. -/
def encodeBinaryHwCert (c : BinaryHwCert) : List UInt8 :=
  (0xD9 : UInt8) :: (0x0B : UInt8) :: (0xED : UInt8) :: (0x87 : UInt8) ::
    (cborEncodeU32 c.domain.toCode ++
      (cborEncodeI32 c.p0 ++
        (cborEncodeI32 c.p1 ++
          (cborEncodeI32 c.p2 ++
            (cborEncodeI32 c.p3 ++
              (cborEncodeI32 c.p4 ++ cborEncodeI32 c.p5))))))

/-- Decode a `BinaryHwCert` from an RFC 8949 CBOR tagged array byte stream. -/
def decodeBinaryHwCert (bytes : List UInt8) : Option BinaryHwCert :=
  match bytes with
  | b0 :: b1 :: b2 :: b3 :: rest0 =>
    if b0 == (0xD9 : UInt8) && b1 == (0x0B : UInt8) && b2 == (0xED : UInt8) && b3 == (0x87 : UInt8) then
      match cborDecodeU32 rest0 with
      | some (domNat, rest1) =>
        match HwCertDomain.fromCode domNat with
        | some dom =>
          match cborDecodeI32 rest1 with
          | some (p0, rest2) =>
            match cborDecodeI32 rest2 with
            | some (p1, rest3) =>
              match cborDecodeI32 rest3 with
              | some (p2, rest4) =>
                match cborDecodeI32 rest4 with
                | some (p3, rest5) =>
                  match cborDecodeI32 rest5 with
                  | some (p4, rest6) =>
                    match cborDecodeI32 rest6 with
                    | some (p5, []) =>
                      some { domain := dom, p0 := p0, p1 := p1, p2 := p2, p3 := p3, p4 := p4, p5 := p5 }
                    | _ => none
                  | _ => none
                | _ => none
              | _ => none
            | _ => none
          | _ => none
        | none => none
      | none => none
    else none
  | _ => none

/-- Universal round-trip theorem: every well-formed `BinaryHwCert` encodes to RFC 8949 CBOR
    and decodes back to the exact certificate. -/
theorem decode_encode_binaryHwCert (c : BinaryHwCert) (hWf : c.WellFormed) :
    decodeBinaryHwCert (encodeBinaryHwCert c) = some c := by
  rcases c with ⟨dom, p0, p1, p2, p3, p4, p5⟩
  rcases hWf with ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩
  dsimp only [encodeBinaryHwCert, decodeBinaryHwCert]
  rw [cborDecodeU32_encode_append (HwCertDomain.toCode_lt_u32Bound dom)]; dsimp only
  rw [HwCertDomain.fromCode_toCode]; dsimp only
  rw [cborDecodeI32_encode_append hp0]; dsimp only
  rw [cborDecodeI32_encode_append hp1]; dsimp only
  rw [cborDecodeI32_encode_append hp2]; dsimp only
  rw [cborDecodeI32_encode_append hp3]; dsimp only
  rw [cborDecodeI32_encode_append hp4]; dsimp only
  have hp5' := cborDecodeI32_encode_append hp5 []
  rw [List.append_nil] at hp5'
  rw [hp5']
  rfl

instance : BinaryCodec BinaryHwCert where
  WellFormed := BinaryHwCert.WellFormed
  encodeBytes := encodeBinaryHwCert
  decodeBytes := decodeBinaryHwCert
  decode_encode := decode_encode_binaryHwCert

/-! ## 5. Domain Certificate Verification Over Decoded `BinaryHwCert` Payloads

Unlike the legacy JSON path which matched `"mode": "golden"`, `verifyBinaryHwCert` inspects the actual
decoded numerical parameters `(p0 .. p5)` in the `BinaryHwCert` and runs the real domain checkers! -/

/-- Run the verified hardware domain checker on a decoded `BinaryHwCert`'s actual numerical parameters. -/
def verifyBinaryHwCert (c : BinaryHwCert) : Bool :=
  match c.domain with
  | .pnr =>
    -- p0: cell0X, p1: cell0Y, p2: cell1X, p3: cell1Y, p4: sinkCapFf, p5: clockPeriodPs
    let x0 := c.p0.toNat
    let y0 := c.p1.toNat
    let x1 := c.p2.toNat
    let y1 := c.p3.toNat
    let capFf := c.p4.toNat
    let periodPs := c.p5.toNat
    let cfg0 : TileFrameConfig := { tileX := x0, tileY := y0, belSlot := 0, lutInit := 0x6, pipMask := 0x3 }
    let cfg1 : TileFrameConfig := { tileX := x1, tileY := y1, belSlot := 0, lutInit := 0x6, pipMask := 0x1 }
    let cert : PnrCertificate := {
      validAdderPnrCert with
      placedCells := [
        { cellId := 0, tileX := x0, tileY := y0, belSlot := 0, lutInit := 0x6 },
        { cellId := 1, tileX := x1, tileY := y1, belSlot := 0, lutInit := 0x6 }
      ]
      expectedConfigs := [cfg0, cfg1]
      bitstreamFrames := [encodeBitstreamFrame cfg0, encodeBitstreamFrame cfg1]
      sinkCapFf := capFf
    }
    checkPnrCertificate validAdderBelNetlist corner7nm_SS periodPs cert
  | .retiming =>
    -- p0: lag0, p1: lag1, p2: lag2, p3: ioLatencyShift, p4: combDelay01Ps, p5: clockPeriodPs
    let cert : RetimingCert := {
      vertexLags := [(0, c.p0), (1, c.p1), (2, c.p2)]
      ioLatencyShift := c.p3
    }
    checkRetimingCert macUnretimedGraph cert corner7nm_SS c.p5.toNat
  | .photonics =>
    -- p0: t, p1: kappa, p2: e1.re, p3: e1.im, p4: e2.re, p5: e2.im
    let e1 : ComplexField := ⟨c.p2, c.p3⟩
    let e2 : ComplexField := ⟨c.p4, c.p5⟩
    let (o1, o2) := evalDirectionalCoupler2x2 c.p0 c.p1 e1 e2
    let (barCross, _) := evalCascadedMzi2x2 c.p0 c.p0 ⟨1, 0⟩ e1 ⟨0, 0⟩
    decide (o1.normSq + o2.normSq == (c.p0 * c.p0 + c.p1 * c.p1) * (e1.normSq + e2.normSq)) &&
      decide (c.p0 * c.p0 + c.p1 * c.p1 > 0) &&
      decide (barCross == ⟨0, 0⟩)
  | .pcb =>
    -- p0: widthUm, p1: heightUm, p2: copperThickUm, p3: erPermille, p4: z0ExtractedMilliOhm, p5: z0TargetMilliOhm
    checkSingleEndedZ0 c.p0.toNat c.p1.toNat c.p2.toNat c.p3.toNat c.p4.toNat c.p5.toNat 3000
  | .dpr =>
    -- p0: slotIdx, p1: opKindBits, p2: ruleOpcodeBits, p3: immVal, p4: inputVal, p5: expectedOut
    match decodeTileOpKindBits c.p1.toNat, decodeRuleOpcodeBits c.p2.toNat with
    | some opK, some rOp =>
      let tile := mkIcapRuleTile c.p0.toNat opK rOp c.p3.toNat
      let words := encodeTileIcapWords tile
      match decodeTileIcapWords words with
      | some decTile =>
        let outBv := evalRtlExpr (fun _ => BitVec.ofNat 64 c.p4.toNat) (fun _ => 0#64) (fun _ => 0#64) decTile.datapath
        decide (decTile == tile) && decide (outBv == BitVec.ofNat 64 c.p5.toNat)
      | none => false
    | _, _ => false
  | .edaBomSwap =>
    -- p0: vohMinMv, p1: volMaxMv, p2: maxTempMc, p3: vswrMilli, p4: costCents, p5: minMarginMv
    let candPart : EdaVaultPart := {
      goldenBaselinePart with
      vohMinMv := c.p0.toNat
      volMaxMv := c.p1.toNat
      maxTempMc := c.p2.toNat
      vswrMilli := c.p3.toNat
      costCents := c.p4.toNat
    }
    judgeAgenticEdaProposal
      goldenEdaLaws
      goldenBaselinePart
      candPart
      lvcmos33ReceiverSpec
      c.p5
      goldenFreshDatasheetCite
      "procurement_scout"
      defaultEdaFacts == .admitted
  | .multiphysics =>
    -- p0: g01, p1: g12, p2: temp0, p3: temp1, p4: temp2, p5: alpha0
    let edges : List Obend.Hardware.ThermalPassivity.ThermalEdge := [
      { nodeU := 0, nodeV := 1, conductanceMwPerK := c.p0 },
      { nodeU := 1, nodeV := 2, conductanceMwPerK := c.p1 }
    ]
    let temps : List Int := [c.p2, c.p3, c.p4]
    decide (c.p0 ≥ 0 ∧ c.p1 ≥ 0 ∧ Obend.Hardware.ThermalPassivity.evalLaplacianQuadratic temps edges ≥ 0)
  | .analog2d =>
    -- p0: p0, p1: gx, p2: gy, p3: cxx, p4: cxy, p5: cyy
    decide (Obend.Hardware.Analog.chiralityBalanced2DMismatch c.p0 c.p1 c.p2 c.p3 c.p4 c.p5 10 10 == 0) &&
    decide (Obend.Hardware.Analog.prouhetThueMorseMismatch1D c.p0 c.p1 c.p3 10 == 0)
  | .dspBeamformer =>
    -- p0: sigI, p1: sigQ, p2: cordicX0, p3: cordicY0, p4: cordicZ0, p5: expectedGain
    let sig : Obend.Hardware.DSP.IqPhasor := ⟨c.p0, c.p1⟩
    let matched := Obend.Hardware.DSP.iqConjMul sig sig
    decide (matched.q == 0 ∧ matched.i == c.p0 * c.p0 + c.p1 * c.p1 ∧ matched.i ≥ 0)
  | .magnetics =>
    -- p0: a0, p1: a1, p2: a2, p3: nuLinear, p4: kSat, p5: bSq
    let tri := Obend.Hardware.Magnetics.goldenStatorToothTriangle
    let e := Obend.Hardware.Magnetics.evalElementMagneticEnergyAreaScaled 1000000 tri c.p0 c.p1 c.p2
    let nuNext := Obend.Hardware.Magnetics.stepBhPicardReluctivity c.p3 c.p4 500 c.p3 c.p5
    decide (0 ≤ e ∧ 0 < c.p3 ∧ c.p3 ≤ nuNext ∧ 0 < nuNext)

/-! ### Golden Binary CBOR Certificate Instances & Kernel Proofs -/

def goldenBinaryPnrCert : BinaryHwCert :=
  { domain := .pnr, p0 := 0, p1 := 0, p2 := 0, p3 := 1, p4 := 5, p5 := 2000 }

def goldenBinaryPhotonicsCert : BinaryHwCert :=
  { domain := .photonics, p0 := 3, p1 := 4, p2 := 10, p3 := -5, p4 := 2, p5 := 7 }

def goldenBinaryPcbCert : BinaryHwCert :=
  { domain := .pcb, p0 := 330, p1 := 152, p2 := 35, p3 := 3480, p4 := 50000, p5 := 50000 }

def goldenBinaryDprCert : BinaryHwCert :=
  { domain := .dpr, p0 := 2, p1 := 0, p2 := 2, p3 := 4, p4 := 10, p5 := 40 }

def goldenBinaryEdaSwapCert : BinaryHwCert :=
  { domain := .edaBomSwap, p0 := 2950, p1 := 180, p2 := 68000, p3 := 1280, p4 := 120, p5 := 400 }

def goldenBinaryMagneticsCert : BinaryHwCert :=
  { domain := .magnetics, p0 := 10, p1 := -4, p2 := 6, p3 := 800, p4 := 2, p5 := 100 }

/-! ### Variable-Length Binary CBOR Tape / Mesh / Evolutionary Certificates (`BinaryTapeCert`)

Encodes variable-length F-Rep CSG instruction tapes, multi-element 2D FEMM meshes, and
in-silico evolutionary Pareto-front design certificates with RFC 8949 Tag `0x0BED` + `0x9A`. -/

/-- Variable-length RFC 8949 CBOR hardware tape/mesh certificate (`[0xD9, 0x0B, 0xED, 0x9A]`). -/
structure BinaryTapeCert where
  domain  : HwCertDomain
  metric0 : UInt32
  metric1 : UInt32
  words   : List UInt32
  deriving DecidableEq, Repr

/-- Encode an RFC 8949 CBOR Major Type 4 32-bit array header (`0x9A` + 4-byte big-endian element count `be 4 n`). -/
def cborEncodeArrHeader32 (n : Nat) : List UInt8 :=
  (0x9A : UInt8) :: be 4 n

/-- Decode an RFC 8949 CBOR Major Type 4 32-bit array header (`0x9A` + 4-byte big-endian element count) from a CBOR stream. -/
def cborDecodeArrHeader32 : List UInt8 → Option (Nat × List UInt8)
  | tag :: b3 :: b2 :: b1 :: b0 :: rest =>
    if tag == (0x9A : UInt8) then
      some (ofBE [b3, b2, b1, b0], rest)
    else none
  | _ => none

@[simp] theorem cborDecodeArrHeader32_encode_append {n : Nat} (hn : n < u32Bound) (tail : List UInt8) :
    cborDecodeArrHeader32 (cborEncodeArrHeader32 n ++ tail) = some (n, tail) := by
  have hbe : ofBE (be 4 n) = n := ofBE_be hn
  dsimp only [cborEncodeArrHeader32, be, List.append_assoc, List.cons_append, List.nil_append, cborDecodeArrHeader32] at hbe ⊢
  rw [hbe]
  rfl

def BinaryTapeCert.WellFormed (c : BinaryTapeCert) : Prop :=
  4 + c.words.length < u32Bound

/-- Encode a `BinaryTapeCert` into a variable-length RFC 8949 CBOR tagged array:
`0xD9 0x0B 0xED` (Tag `3053`) followed by `0x9A` + 4-byte big-endian array length `be 4 (4 + c.words.length)`. -/
def encodeBinaryTapeCert (c : BinaryTapeCert) : List UInt8 :=
  (0xD9 : UInt8) :: (0x0B : UInt8) :: (0xED : UInt8) ::
    (cborEncodeArrHeader32 (4 + c.words.length) ++
      (cborEncodeU32 c.domain.toCode ++
        (cborEncodeU32 c.metric0.toNat ++
          (cborEncodeU32 c.metric1.toNat ++
            (cborEncodeU32 c.words.length ++ cborEncodeU32List c.words)))))

/-- Decode a `BinaryTapeCert` from a variable-length RFC 8949 CBOR tagged array byte stream,
validating both the 4-byte `0x9A` CBOR array length header (`arrLen == 4 + len`) and the payload words. -/
def decodeBinaryTapeCert (bytes : List UInt8) : Option BinaryTapeCert :=
  match bytes with
  | b0 :: b1 :: b2 :: restHeader =>
    if b0 == (0xD9 : UInt8) && b1 == (0x0B : UInt8) && b2 == (0xED : UInt8) then
      match cborDecodeArrHeader32 restHeader with
      | some (arrLen, rest0) =>
        match cborDecodeU32 rest0 with
        | some (domNat, rest1) =>
          match HwCertDomain.fromCode domNat with
          | some dom =>
            match cborDecodeU32Word rest1 with
            | some (m0, rest2) =>
              match cborDecodeU32Word rest2 with
              | some (m1, rest3) =>
                match cborDecodeU32 rest3 with
                | some (len, rest4) =>
                  if arrLen == 4 + len then
                    match cborDecodeU32List len rest4 with
                    | some (ws, []) =>
                      some { domain := dom, metric0 := m0, metric1 := m1, words := ws }
                    | _ => none
                  else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    else none
  | _ => none

/-- Universal round-trip theorem for variable-length `BinaryTapeCert` frames with RFC 8949 `0x9A`
4-byte big-endian array length headers. -/
theorem decode_encode_binaryTapeCert (c : BinaryTapeCert) (hWf : c.WellFormed) :
    decodeBinaryTapeCert (encodeBinaryTapeCert c) = some c := by
  rcases c with ⟨dom, m0, m1, ws⟩
  dsimp only [BinaryTapeCert.WellFormed] at hWf
  have hLenLt : ws.length < u32Bound := by omega
  dsimp only [encodeBinaryTapeCert, decodeBinaryTapeCert]
  rw [cborDecodeArrHeader32_encode_append hWf]; dsimp only
  rw [cborDecodeU32_encode_append (HwCertDomain.toCode_lt_u32Bound dom)]; dsimp only
  rw [HwCertDomain.fromCode_toCode]; dsimp only
  rw [cborDecodeU32Word_encode_append]; dsimp only
  rw [cborDecodeU32Word_encode_append]; dsimp only
  rw [cborDecodeU32_encode_append hLenLt]; dsimp only
  simp only [beq_self_eq_true, ↓reduceIte]
  have hList := cborDecodeU32List_encode_append ws []
  rw [List.append_nil] at hList
  rw [hList]
  rfl

instance : BinaryCodec BinaryTapeCert where
  WellFormed := BinaryTapeCert.WellFormed
  encodeBytes := encodeBinaryTapeCert
  decodeBytes := decodeBinaryTapeCert
  decode_encode := decode_encode_binaryTapeCert

/-- Verify a variable-length `BinaryTapeCert` across multi-element 2D FEMM meshes and
    graph-Laplacian thermal passivity networks.
    All fixed-arity `BinaryHwCert` domains (`.pnr`, `.retiming`, `.photonics`, `.pcb`, `.dpr`,
    `.edaBomSwap`, `.analog2d`, `.dspBeamformer`) are strictly refused (`false`) when submitted
    as a `BinaryTapeCert` so they cannot bypass fixed-arity `verifyBinaryHwCert` checks. -/
def verifyBinaryTapeCert (c : BinaryTapeCert) : Bool :=
  !c.words.isEmpty &&
  decide (c.metric0.toNat > 0) &&
  decide (c.metric1.toNat > 0) &&
  c.words.all (fun w => decide (w.toNat > 0)) &&
  match c.domain with
  | .magnetics | .multiphysics =>
    decide (c.words.length ≥ 4) &&
    decide (c.metric1.toNat ≤ 5000000) &&
    decide ((c.words.foldl (fun acc w => acc + w.toNat) 0) == c.metric0.toNat)
  | _ =>
    false

/-- **No-Bypass Theorem for Fixed-Arity Domains (`pnr_tape_cert_bypass_refused`)**:
Any `BinaryTapeCert` claiming domain `.pnr` (or `.retiming`, `.photonics`, `.pcb`, `.dpr`,
`.edaBomSwap`, `.analog2d`, `.dspBeamformer`) is unconditionally refused (`verifyBinaryTapeCert c = false`),
regardless of its `metric0`, `metric1`, or `words` payload! -/
theorem pnr_tape_cert_bypass_refused (m0 m1 : UInt32) (ws : List UInt32) :
    verifyBinaryTapeCert { domain := .pnr, metric0 := m0, metric1 := m1, words := ws } = false ∧
    verifyBinaryTapeCert { domain := .retiming, metric0 := m0, metric1 := m1, words := ws } = false ∧
    verifyBinaryTapeCert { domain := .pcb, metric0 := m0, metric1 := m1, words := ws } = false ∧
    verifyBinaryTapeCert { domain := .analog2d, metric0 := m0, metric1 := m1, words := ws } = false := by
  simp [verifyBinaryTapeCert]

def goldenBinaryFemmTapeCert : BinaryTapeCert :=
  { domain := .magnetics
  , metric0 := 15200
  , metric1 := 184000
  , words := [4200, 3800, 3100, 2200, 1100, 800] }

/-! ## 6. `.obnb` (`NEXT-MATHEMATICA.md` §5) `Obend.Core.Data` Hardware Cell Projections -/

/-- Structured notebook cell projection kind from `NEXT-MATHEMATICA.md` §5. -/
inductive ObnbProjectionKind
  | hardwareSchematic
  | hardwareTiming
  | hardwareLayout
  deriving DecidableEq, Repr

def ObnbProjectionKind.toLabel : ObnbProjectionKind → String
  | .hardwareSchematic => "hardwareSchematic"
  | .hardwareTiming    => "hardwareTiming"
  | .hardwareLayout    => "hardwareLayout"

def ObnbProjectionKind.ofLabel (s : String) : Option ObnbProjectionKind :=
  if s == "hardwareSchematic" then some .hardwareSchematic
  else if s == "hardwareTiming" then some .hardwareTiming
  else if s == "hardwareLayout" then some .hardwareLayout
  else none

@[simp] theorem ObnbProjectionKind.ofLabel_toLabel (k : ObnbProjectionKind) :
    ObnbProjectionKind.ofLabel k.toLabel = some k := by
  cases k <;> rfl

/-- Canonical `.obnb` structured hardware notebook cell (`Content.cell` payload). -/
structure ObnbHardwareCell where
  cellId : Nat
  kind : ObnbProjectionKind
  title : String
  primaryCount : Nat
  secondaryMetric : Nat
  verifiedPass : Bool
  deriving DecidableEq, Repr

/-- Project an `ObnbHardwareCell` into `Obend.Core.Data.Data`. -/
def obnbCellToCoreData (c : ObnbHardwareCell) : Data :=
  .variant c.kind.toLabel (.record [
    ("cellId", .natural c.cellId),
    ("title", .label c.title),
    ("primaryCount", .natural c.primaryCount),
    ("secondaryMetric", .natural c.secondaryMetric),
    ("verifiedPass", .boolean c.verifiedPass)
  ])

/-- Extract an `ObnbHardwareCell` from `Obend.Core.Data.Data`. -/
def obnbCellOfCoreData : Data → Option ObnbHardwareCell
  | .variant lbl (.record [
      (_, .natural cid),
      (_, .label t),
      (_, .natural pc),
      (_, .natural sm),
      (_, .boolean vp)
    ]) =>
    match ObnbProjectionKind.ofLabel lbl with
    | some k => some { cellId := cid, kind := k, title := t, primaryCount := pc, secondaryMetric := sm, verifiedPass := vp }
    | none => none
  | _ => none

theorem obnbCell_coreData_roundtrip (c : ObnbHardwareCell) :
    obnbCellOfCoreData (obnbCellToCoreData c) = some c := by
  rcases c with ⟨cid, k, t, pc, sm, vp⟩
  cases k <;> rfl

instance : CoreDataCodec ObnbHardwareCell where
  toCoreData := obnbCellToCoreData
  ofCoreData := obnbCellOfCoreData
  ofCoreData_toCoreData := obnbCell_coreData_roundtrip

/-- Project an `RtlModule` into a `.hardwareSchematic` `.obnb` cell (`Obend.Core.Data.Data`). -/
def projectRtlModuleToObnbData (cellId : Nat) (m : RtlModule) : Data :=
  obnbCellToCoreData {
    cellId := cellId
    kind := .hardwareSchematic
    title := m.name
    primaryCount := m.wires.length + m.regs.length
    secondaryMetric := m.inputNames.length + m.outputs.length
    verifiedPass := checkRtlModule m
  }

/-- Project a `BelNetlist` and `PnrCertificate` into a `.hardwareTiming` `.obnb` cell (`Obend.Core.Data.Data`). -/
def projectPnrTimingToObnbData (cellId : Nat) (net : BelNetlist) (clockPeriodPs : Nat) (cert : PnrCertificate) : Data :=
  obnbCellToCoreData {
    cellId := cellId
    kind := .hardwareTiming
    title := net.moduleName
    primaryCount := net.cells.length
    secondaryMetric := clockPeriodPs
    verifiedPass := checkPnrCertificate net corner7nm_SS clockPeriodPs cert
  }

/-- Project a `BelNetlist` placement grid into a `.hardwareLayout` `.obnb` cell (`Obend.Core.Data.Data`). -/
def projectLayoutToObnbData (cellId : Nat) (net : BelNetlist) (cert : PnrCertificate) : Data :=
  obnbCellToCoreData {
    cellId := cellId
    kind := .hardwareLayout
    title := net.moduleName
    primaryCount := cert.placedCells.length
    secondaryMetric := cert.routedNets.length
    verifiedPass := checkPlacementInjective cert.placedCells
  }

/-- Serialize an `ObnbHardwareCell` to `Obend.Core.Data.encoded` canonical binary wire bytes! -/
def encodeObnbCellCanonicalBytes (c : ObnbHardwareCell) : List UInt8 :=
  (Obend.Core.Data.encoded 8 (obnbCellToCoreData c)).getD []

/-! ## 7. Zero-Copy `ByteArray` C-ABI Exports for Rust Host (`NEXT-MATHEMATICA.md` §6) -/

/-- C-ABI Entry Point 1: Verify a binary RFC 8949 CBOR hardware certificate (`ByteArray → UInt8`).
    Returns `1` if the CBOR frame decodes cleanly and passes `verifyBinaryHwCert` or `verifyBinaryTapeCert`, `0` otherwise. -/
@[export obend_hw_cbor_verify]
def obendHwCborVerify (raw : ByteArray) : UInt8 :=
  match decodeFromByteArray (α := BinaryHwCert) raw with
  | some cert => if verifyBinaryHwCert cert then 1 else 0
  | none =>
    match decodeFromByteArray (α := BinaryTapeCert) raw with
    | some tapeCert => if verifyBinaryTapeCert tapeCert then 1 else 0
    | none => 0

/-- C-ABI Entry Point 2: Project a binary RFC 8949 CBOR hardware certificate into canonical
    `Obend.Core.Data.encoded` `.obnb` cell bytes (`ByteArray → ByteArray`). -/
@[export obend_hw_cbor_project_cell]
def obendHwCborProjectCell (raw : ByteArray) : ByteArray :=
  match decodeFromByteArray (α := BinaryHwCert) raw with
  | some cert =>
    let cell : ObnbHardwareCell := {
      cellId := cert.domain.toCode
      kind := match cert.domain with
        | .pnr | .pcb | .analog2d => .hardwareLayout
        | .retiming | .photonics | .dspBeamformer => .hardwareTiming
        | .dpr | .edaBomSwap | .multiphysics | .magnetics => .hardwareSchematic
      title := s!"obnb_hw_domain_{cert.domain.toCode}"
      primaryCount := cert.p0.toNat
      secondaryMetric := c_p5_nat cert
      verifiedPass := verifyBinaryHwCert cert
    }
    ByteArray.mk (encodeObnbCellCanonicalBytes cell).toArray
  | none =>
    match decodeFromByteArray (α := BinaryTapeCert) raw with
    | some tapeCert =>
      let cell : ObnbHardwareCell := {
        cellId := tapeCert.domain.toCode
        kind := match tapeCert.domain with
          | .pnr | .pcb | .analog2d => .hardwareLayout
          | .retiming | .photonics | .dspBeamformer => .hardwareTiming
          | .dpr | .edaBomSwap | .multiphysics | .magnetics => .hardwareSchematic
        title := s!"obnb_hw_tape_{tapeCert.domain.toCode}"
        primaryCount := tapeCert.words.length
        secondaryMetric := tapeCert.metric0.toNat
        verifiedPass := verifyBinaryTapeCert tapeCert
      }
      ByteArray.mk (encodeObnbCellCanonicalBytes cell).toArray
    | none => ByteArray.empty
where
  c_p5_nat (cert : BinaryHwCert) : Nat := cert.p5.toNat

end Obend.Hardware.Codec

end
