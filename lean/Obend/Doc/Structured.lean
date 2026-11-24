module
/-
# Obend.Doc.Structured — Structured non-markdown cells, ProjectionKind, and .obnb format

Addresses Milestone 5 Features 34 & 35 (Requirements R5 and R6):
1. Feature 34: `ProjectionKind` (10 distinct categories, decider, wire serialization to/from Core.Data).
2. Feature 35: `Content.cell` in `Doc.Graph` carrying `Core.Data`, footprint pins, and Merkle receipts.
3. Round-trip serialization soundness, projection preservation, and pin validity metatheorems.
4. `.obnb` notebook serialization format (JSON and binary Core.Data quotations).
-/
public import Obend.Doc.Graph
public import Obend.Doc.Patch
public import Obend.Core.Data
public import Obend.Run.Core4
public import Obend.Spec.DataWire
public import Obend.Codec.Hex

public section

namespace Obend.Doc

open Obend.Core.Data (Data)
open Obend.Codec.Hex (hexNibbleChar bytesToHexChars byteArrayToHex hexCharsToBytesAnyCase?
  decodeHexNibbleAnyCase?_hexNibbleChar hexCharsToBytesAnyCase?_bytesToHexChars)

set_option autoImplicit false

/-! ## 1. Feature 34: ProjectionKind Enumeration, Decider & Wire Codecs -/

/-- Exhaustive list of all 16 distinct projection kinds. -/
@[expose] def ProjectionKind.all : List ProjectionKind :=
  [ .prose
  , .obendCode
  , .casSymbolic
  , .leanBridge
  , .lawContract
  , .deosAffordance
  , .hardwareSchematic
  , .hardwareTiming
  , .hardwareLayout
  , .ledgerSeat
  , .pdeConservation
  , .feecSimplicialFem
  , .pcbMultiphysicsDfm
  , .vehicle6DofTrajectory
  , .zkCustodyReceipt
  , .frustumRedactedView ]

theorem ProjectionKind.all_length : ProjectionKind.all.length = 16 := rfl

/-- Canonical string discriminant representation for wire and .obnb serialization. -/
@[expose] def ProjectionKind.toLabel : ProjectionKind → String
  | .prose                 => "prose"
  | .obendCode             => "obendCode"
  | .casSymbolic           => "casSymbolic"
  | .leanBridge            => "leanBridge"
  | .lawContract           => "lawContract"
  | .deosAffordance        => "deosAffordance"
  | .hardwareSchematic     => "hardwareSchematic"
  | .hardwareTiming        => "hardwareTiming"
  | .hardwareLayout        => "hardwareLayout"
  | .ledgerSeat            => "ledgerSeat"
  | .pdeConservation       => "pdeConservation"
  | .feecSimplicialFem     => "feecSimplicialFem"
  | .pcbMultiphysicsDfm    => "pcbMultiphysicsDfm"
  | .vehicle6DofTrajectory => "vehicle6DofTrajectory"
  | .zkCustodyReceipt      => "zkCustodyReceipt"
  | .frustumRedactedView   => "frustumRedactedView"

/-- Parse a string discriminant into a `ProjectionKind`. Rejects unknown or malformed strings. -/
@[expose] def ProjectionKind.ofLabel : String → Option ProjectionKind
  | "prose"                 => some .prose
  | "obendCode"             => some .obendCode
  | "casSymbolic"           => some .casSymbolic
  | "leanBridge"            => some .leanBridge
  | "lawContract"           => some .lawContract
  | "deosAffordance"        => some .deosAffordance
  | "hardwareSchematic"     => some .hardwareSchematic
  | "hardwareTiming"        => some .hardwareTiming
  | "hardwareLayout"        => some .hardwareLayout
  | "ledgerSeat"            => some .ledgerSeat
  | "pdeConservation"       => some .pdeConservation
  | "feecSimplicialFem"     => some .feecSimplicialFem
  | "pcbMultiphysicsDfm"    => some .pcbMultiphysicsDfm
  | "vehicle6DofTrajectory" => some .vehicle6DofTrajectory
  | "zkCustodyReceipt"      => some .zkCustodyReceipt
  | "frustumRedactedView"   => some .frustumRedactedView
  | _                       => none

@[simp] theorem ProjectionKind.ofLabel_toLabel (k : ProjectionKind) :
    ProjectionKind.ofLabel k.toLabel = some k := by
  cases k <;> rfl

theorem ProjectionKind.toLabel_injective {a b : ProjectionKind} (h : a.toLabel = b.toLabel) : a = b := by
  have h1 : ProjectionKind.ofLabel a.toLabel = ProjectionKind.ofLabel b.toLabel := congrArg ProjectionKind.ofLabel h
  rw [ProjectionKind.ofLabel_toLabel, ProjectionKind.ofLabel_toLabel] at h1
  injection h1

/-- Complete membership witness: every `ProjectionKind` appears in `ProjectionKind.all`. -/
theorem ProjectionKind.mem_all (k : ProjectionKind) : k ∈ ProjectionKind.all := by
  cases k <;> decide

/-- Structural decider for `ProjectionKind` equality. -/
def ProjectionKind.decideEq (a b : ProjectionKind) : Decidable (a = b) :=
  inferInstance

/-- Classification: whether a kind belongs to physical/hardware CAD/EDA/CAE projections. -/
@[expose] def ProjectionKind.isHardware : ProjectionKind → Bool
  | .hardwareSchematic | .hardwareTiming | .hardwareLayout
  | .pcbMultiphysicsDfm | .vehicle6DofTrajectory => true
  | _ => false

/-- Classification: whether a kind represents executable computation or PDE/FEM solvers. -/
@[expose] def ProjectionKind.isExecutable : ProjectionKind → Bool
  | .obendCode | .casSymbolic | .leanBridge
  | .pdeConservation | .feecSimplicialFem => true
  | _ => false

/-- Classification: whether a kind represents smart contract, custody, or capability views. -/
@[expose] def ProjectionKind.isContractual : ProjectionKind → Bool
  | .lawContract | .deosAffordance | .ledgerSeat
  | .zkCustodyReceipt | .frustumRedactedView => true
  | _ => false

theorem ProjectionKind.hardware_count :
    (ProjectionKind.all.filter ProjectionKind.isHardware).length = 5 := rfl

theorem ProjectionKind.executable_count :
    (ProjectionKind.all.filter ProjectionKind.isExecutable).length = 5 := rfl

theorem ProjectionKind.contractual_count :
    (ProjectionKind.all.filter ProjectionKind.isContractual).length = 5 := rfl

/-- Serialize `ProjectionKind` to canonical `Core.Data`. -/
@[expose] def ProjectionKind.toData (k : ProjectionKind) : Data :=
  .label k.toLabel

/-- Deserialize `ProjectionKind` from `Core.Data`. -/
@[expose] def ProjectionKind.ofData? : Data → Option ProjectionKind
  | .label s => ProjectionKind.ofLabel s
  | .variant s _ => ProjectionKind.ofLabel s
  | _ => none

@[simp] theorem ProjectionKind.ofData_toData (k : ProjectionKind) :
    ProjectionKind.ofData? (ProjectionKind.toData k) = some k := by
  simp only [toData, ofData?, ofLabel_toLabel]


/-! ## 2. Feature 35: StructuredCell & Content.cell Carrier -/

/-- Drops a leading `0x` or `0X`. -/
def stripHexPrefix : List Char → List Char
  | '0' :: 'x' :: rest => rest
  | '0' :: 'X' :: rest => rest
  | cs => cs

/-- A pin hash in hex, read in either case, with or without a `0x` prefix; it is written by
`Obend.Codec.Hex.byteArrayToHex`. -/
def hexToByteArray (s : String) : Option ByteArray := do
  let bytes ← hexCharsToBytesAnyCase? (stripHexPrefix s.toList)
  return ByteArray.mk bytes.toArray

private theorem stripHexPrefix_cons2 (c1 c2 : Char) (rest : List Char)
    (hx : c2 ≠ 'x') (hX : c2 ≠ 'X') :
    stripHexPrefix (c1 :: c2 :: rest) = c1 :: c2 :: rest := by
  cases h1 : (c1 == '0')
  · unfold stripHexPrefix
    split
    · rename_i rest' heq
      injection heq with hc1 _
      rw [hc1] at h1
      cases h1
    · rename_i rest' heq
      injection heq with hc1 _
      rw [hc1] at h1
      cases h1
    · rfl
  · unfold stripHexPrefix
    split
    · rename_i rest' heq
      injection heq with _ htail
      injection htail with hc2 _
      exact absurd hc2 hx
    · rename_i rest' heq
      injection heq with _ htail
      injection htail with hc2 _
      exact absurd hc2 hX
    · rfl

/-- A hex digit is not the `x` of a `0x` prefix. -/
private theorem hexNibbleChar_ne_x (n : Nat) : hexNibbleChar n ≠ 'x' ∧ hexNibbleChar n ≠ 'X' := by
  have h := decodeHexNibbleAnyCase?_hexNibbleChar n
  constructor
  · intro hx; rw [hx] at h; cases h
  · intro hX; rw [hX] at h; cases h

private theorem stripHexPrefix_bytesToHexChars :
    ∀ bs : List UInt8, stripHexPrefix (bytesToHexChars bs) = bytesToHexChars bs
  | [] => rfl
  | b :: bs => by
    obtain ⟨hnx, hnX⟩ := hexNibbleChar_ne_x (b.toNat % 16)
    exact stripHexPrefix_cons2 _ _ _ hnx hnX

/-- Round-trip soundness of `byteArrayToHex` and `hexToByteArray`. -/
@[simp] theorem hexToByteArray_byteArrayToHex (b : ByteArray) :
    hexToByteArray (byteArrayToHex b) = some b := by
  cases b with
  | mk arr =>
    unfold hexToByteArray
    rw [String.toList_ofList, stripHexPrefix_bytesToHexChars, hexCharsToBytesAnyCase?_bytesToHexChars]
    simp only [bind, Option.bind, pure, Array.toArray_toList]

/-- Structured non-markdown cell record inside a notebook. -/
structure StructuredCell where
  id : String
  kind : ProjectionKind
  ast : Data
  pins : List (String × ByteArray) := []
  receipt : Option ByteArray := none
deriving DecidableEq, Repr

/-- Embed a `StructuredCell` into `Doc.Content`. -/
@[expose] def StructuredCell.toContent (c : StructuredCell) : Content :=
  .cell c.id c.kind c.ast c.pins c.receipt

/-- Extract a `StructuredCell` from `Doc.Content`. -/
@[expose] def Content.toCell? : Content → Option StructuredCell
  | .cell id k ast pins receipt => some { id := id, kind := k, ast := ast, pins := pins, receipt := receipt }
  | _ => none

@[simp] theorem Content.toCell_toContent (c : StructuredCell) :
    (StructuredCell.toContent c).toCell? = some c := rfl


/-! ## 3. Core.Data Wire Codecs & Metatheorems -/

def pinToData (p : String × ByteArray) : Data :=
  .record [("name", .label p.1), ("hash", .label (byteArrayToHex p.2))]

def pinsToData (ps : List (String × ByteArray)) : Data :=
  .record (ps.mapIdx fun i p => (toString i, pinToData p))

def pinOfData : Data → Option (String × ByteArray)
  | .record [(_, .label name), (_, .label h)] => do
    let b ← hexToByteArray h
    return (name, b)
  | _ => none

def pinsOfData : Data → Option (List (String × ByteArray))
  | .record fields => fields.mapM (fun f => pinOfData f.2)
  | _ => none

def receiptToData : Option ByteArray → Data
  | some r => .variant "some" (.label (byteArrayToHex r))
  | none => .variant "none" (.label "")

def receiptOfData : Data → Option (Option ByteArray)
  | .variant "none" _ => some none
  | .variant "some" (.label h) => (hexToByteArray h).map some
  | _ => none

/-- Serialize a `StructuredCell` into canonical `Obend.Core.Data`. -/
def cellToCoreData (c : StructuredCell) : Data :=
  .record [
    ("id", .label c.id),
    ("kind", ProjectionKind.toData c.kind),
    ("ast", c.ast),
    ("pins", pinsToData c.pins),
    ("receipt", receiptToData c.receipt)
  ]

/-- Deserialize a `StructuredCell` from `Obend.Core.Data`. -/
def cellOfCoreData : Data → Option StructuredCell
  | .record [
      (_, .label cid),
      (_, kd),
      (_, ast),
      (_, pd),
      (_, rd)
    ] => do
    let k ← ProjectionKind.ofData? kd
    let ps ← pinsOfData pd
    let r ← receiptOfData rd
    return { id := cid, kind := k, ast := ast, pins := ps, receipt := r }
  | _ => none

@[simp] theorem pinOfData_pinToData (p : String × ByteArray) :
    pinOfData (pinToData p) = some p := by
  rcases p with ⟨name, bytes⟩
  simp [pinToData, pinOfData, bind, Option.bind, pure]

private theorem mapM_pinOfData_zipIdx :
    ∀ (ps : List (String × ByteArray)) (idx : Nat),
      ((ps.zipIdx idx).map fun (p, i) => (toString i, pinToData p)).mapM (fun f => pinOfData f.2) =
        some ps
  | [], _ => rfl
  | p :: ps, idx => by
    simp only [List.zipIdx_cons, List.map_cons, List.mapM_cons, pinOfData_pinToData,
      mapM_pinOfData_zipIdx ps (idx + 1), bind, Option.bind, pure]

@[simp] theorem pinsOfData_pinsToData (ps : List (String × ByteArray)) :
    pinsOfData (pinsToData ps) = some ps := by
  unfold pinsToData pinsOfData
  rw [List.mapIdx_eq_zipIdx_map]
  exact mapM_pinOfData_zipIdx ps 0

@[simp] theorem receiptOfData_receiptToData (r : Option ByteArray) :
    receiptOfData (receiptToData r) = some r := by
  cases r <;> simp [receiptToData, receiptOfData]

/-- Full `Core.Data` round-trip soundness for `StructuredCell`. -/
@[simp] theorem cellOfCoreData_cellToCoreData (c : StructuredCell) :
    cellOfCoreData (cellToCoreData c) = some c := by
  cases c
  simp [cellToCoreData, cellOfCoreData, bind, Option.bind, pure]

/-- Metatheorem: Unconditional projection preservation under `Core.Data` serialization. -/
theorem projection_preservation (c : StructuredCell) :
    (cellOfCoreData (cellToCoreData c)).map StructuredCell.kind = some c.kind := by
  rw [cellOfCoreData_cellToCoreData]
  rfl


/-! ## 4. .obnb Document Graph Representation & CRDT Merge -/

/-- Structured .obnb notebook document representation. -/
structure ObnbDocument where
  version : Nat := 1
  title : String
  cells : List StructuredCell
  edges : List (String × String) := []
deriving DecidableEq, Repr

/-- Convert an `ObnbDocument` into a `Doc.Graph` patch sequence. -/
def documentToPatch (doc : ObnbDocument) : Patch :=
  doc.cells.zipIdx.map fun (c, i) =>
    Op.add (i + 1) (StructuredCell.toContent c) i

/-- Look up a structured cell in a document graph by its cell ID. -/
def findCellById (G : Graph) (cellId : String) : Option StructuredCell :=
  G.atoms.findSome? fun (_, content) =>
    match content with
    | .cell id k ast pins receipt =>
      if id == cellId then some { id := id, kind := k, ast := ast, pins := pins, receipt := receipt }
      else none
    | _ => none

/-- Metatheorem: Appending a cell atom preserves an existing atom's label. -/
theorem cell_preserved_under_add (G : Graph) (a i : AtomId) (c : StructuredCell) (content' : Content) (prev : AtomId)
    (h_label : G.label a = some (StructuredCell.toContent c)) :
    (G.step (Op.add i content' prev)).label a = some (StructuredCell.toContent c) := by
  unfold Graph.step Graph.label at *
  dsimp only
  rw [Graph.lookup_append_single]
  rw [h_label]


/-! ## 5. Cryptographic Pin Validity & Stale Support Invalidation -/

/-- Result of footprint pin verification. -/
inductive PinStatus where
  | valid
  | stale (pinName : String) (expected actual : String)
  | missing (pinName : String)
deriving DecidableEq, Repr

/-- Verify a single footprint pin against an active environment. -/
def verifyPin (pin : String × ByteArray) (env : String → Option ByteArray) : PinStatus :=
  match env pin.1 with
  | none => .missing pin.1
  | some actual =>
    if actual == pin.2 then .valid
    else .stale pin.1 (byteArrayToHex pin.2) (byteArrayToHex actual)

/-- Verify all footprint pins of a cell. -/
def verifyCellPins (c : StructuredCell) (env : String → Option ByteArray) : List PinStatus :=
  c.pins.map (verifyPin · env)

/-- Whether all footprint pins of a cell are verified and active. -/
@[expose] def allPinsValid (c : StructuredCell) (env : String → Option ByteArray) : Bool :=
  c.pins.all fun (name, hash) =>
    match env name with
    | some actual => decide (actual = hash)
    | none => false

/-- Metatheorem: Overriding any pinned dependency invalidates the cell's validity. -/
theorem stale_pin_invalidates (c : StructuredCell) (env : String → Option ByteArray)
    (pinName : String) (expected actual : ByteArray)
    (h_mem : (pinName, expected) ∈ c.pins)
    (h_env : env pinName = some actual)
    (h_diff : actual ≠ expected) :
    allPinsValid c env = false := by
  cases h_all : allPinsValid c env with
  | false => rfl
  | true =>
    have h_each := List.all_eq_true.mp h_all (pinName, expected) h_mem
    dsimp only at h_each
    rw [h_env] at h_each
    dsimp only at h_each
    have h_eq : actual = expected := of_decide_eq_true h_each
    exact False.elim (h_diff h_eq)

end Obend.Doc
end
