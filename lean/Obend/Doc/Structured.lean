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

public section

namespace Obend.Doc

open Obend.Core.Data (Data)

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

/-- Hex encoding helper for byte arrays. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def byteToHex (b : UInt8) : String :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  String.ofList [hexDigit hi, hexDigit lo]

def byteArrayToHex (b : ByteArray) : String :=
  (b.data.toList.map byteToHex).foldl (· ++ ·) ""

def unhexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexToBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← unhexDigit a
    let y ← unhexDigit b
    let r ← hexToBytes rest
    return (x * 16 + y).toUInt8 :: r
  | [_] => none

def stripHexPrefix : List Char → List Char
  | '0' :: 'x' :: rest => rest
  | '0' :: 'X' :: rest => rest
  | cs => cs

def hexToByteArray (s : String) : Option ByteArray := do
  let bytes ← hexToBytes (stripHexPrefix s.toList)
  return ByteArray.mk bytes.toArray

private theorem unhexDigit_hexDigit_fin : ∀ n : Fin 16, unhexDigit (hexDigit n.val) = some n.val := by
  decide

private theorem hexDigit_ne_x_fin : ∀ n : Fin 16, hexDigit n.val ≠ 'x' ∧ hexDigit n.val ≠ 'X' := by
  decide

theorem unhexDigit_hexDigit {n : Nat} (hn : n < 16) : unhexDigit (hexDigit n) = some n :=
  unhexDigit_hexDigit_fin ⟨n, hn⟩

theorem hexDigit_ne_x {n : Nat} (hn : n < 16) : hexDigit n ≠ 'x' ∧ hexDigit n ≠ 'X' :=
  hexDigit_ne_x_fin ⟨n, hn⟩

def bytesToHexChars : List UInt8 → List Char
  | [] => []
  | b :: bs => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: bytesToHexChars bs

private theorem byteToHex_toList (b : UInt8) :
    (byteToHex b).toList = [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)] := by
  simp [byteToHex]

private theorem foldl_byteToHex_toList :
    ∀ (bs : List UInt8) (acc : String),
      ((bs.map byteToHex).foldl (· ++ ·) acc).toList = acc.toList ++ bytesToHexChars bs
  | [], acc => by simp [bytesToHexChars]
  | b :: bs, acc => by
    simp only [List.map_cons, List.foldl_cons, bytesToHexChars]
    rw [foldl_byteToHex_toList bs (acc ++ byteToHex b), String.toList_append, byteToHex_toList]
    simp [List.append_assoc]

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

private theorem stripHexPrefix_bytesToHexChars :
    ∀ bs : List UInt8, stripHexPrefix (bytesToHexChars bs) = bytesToHexChars bs
  | [] => rfl
  | b :: bs => by
    have hlo : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨hnx, hnX⟩ := hexDigit_ne_x hlo
    exact stripHexPrefix_cons2 _ _ _ hnx hnX

private theorem uint8_div_mod_reconstruct (b : UInt8) :
    ((b.toNat / 16) * 16 + b.toNat % 16).toUInt8 = b := by
  have hsum : (b.toNat / 16) * 16 + b.toNat % 16 = b.toNat := by omega
  rw [hsum]
  cases b with
  | ofBitVec v =>
    cases v with
    | ofFin f =>
      cases f with
      | mk n hn =>
        simp [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hn]

private theorem hexToBytes_bytesToHexChars :
    ∀ bs : List UInt8, hexToBytes (bytesToHexChars bs) = some bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hhi : b.toNat / 16 < 16 := by omega
    have hlo : b.toNat % 16 < 16 := by omega
    simp only [bytesToHexChars, hexToBytes, bind, Option.bind]
    rw [unhexDigit_hexDigit hhi, unhexDigit_hexDigit hlo, hexToBytes_bytesToHexChars bs]
    dsimp only [pure]
    rw [uint8_div_mod_reconstruct b]

/-- Round-trip soundness of `byteArrayToHex` and `hexToByteArray`. -/
@[simp] theorem hexToByteArray_byteArrayToHex (b : ByteArray) :
    hexToByteArray (byteArrayToHex b) = some b := by
  cases b with
  | mk arr =>
    cases arr with
    | mk bs =>
      unfold hexToByteArray byteArrayToHex
      simp only [bind, Option.bind, pure]
      rw [foldl_byteToHex_toList bs ""]
      simp only [String.toList_empty, List.nil_append]
      rw [stripHexPrefix_bytesToHexChars bs, hexToBytes_bytesToHexChars bs]

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
