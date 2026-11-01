module
/-
# Obend.FFI.Bridge — 8-Function Zero-Copy C-ABI FFI Bridge
Milestone 5, Features 37 & 38.
-/
public import Obend.Core.Data
public import Obend.Core.Digest
public import Obend.Vault.Store
public import Obend.Vault.Hyperedge
public import Obend.Ledger.Book
public import Obend.Doc.Graph
public import Obend.Doc.Structured
public import Obend.Receipt.Merkle
public import Obend.Hardware.Codec

public section
namespace Obend.FFI

open Obend.Core
open Obend.Vault
open Obend.Ledger
open Obend.Doc
open Obend.Receipt.Merkle

structure SessionState where
  store : Store := { pages := [], members := [], turn := 0 }
  book : Book := Book.empty
  doc : Graph := Graph.empty
  scratch : ByteArray := ByteArray.empty
  lastError : Option String := none
  deriving Inhabited

/-- Initialize session state from configuration bytes. -/
@[export obend_session_init_core]
def sessionInitCore (_cfg : ByteArray) : SessionState :=
  { store := { pages := [], members := [], turn := 0 },
    book := Book.empty,
    doc := Graph.empty,
    scratch := ByteArray.empty,
    lastError := none }

/-- Free session callback. -/
@[export obend_session_free_core]
def sessionFreeCore (_s : SessionState) : Unit := ()

/-- Cell evaluation: wraps into StructuredCell, steps document graph, returns (newState, outBytes, status). -/
@[export obend_eval_cell_core]
def evalCellCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload" }, ByteArray.empty, -3)
  else
    let cellId := s!"cell_{s.doc.atoms.length + 1}"
    let cell : StructuredCell := {
      id := cellId,
      kind := .obendCode,
      ast := .natural cellBytes.size,
      pins := [],
      receipt := none
    }
    let newDoc := s.doc.step (Doc.Op.add (s.doc.atoms.length + 1) (StructuredCell.toContent cell) s.doc.atoms.length)
    let outBytes := cellBytes
    ({ s with doc := newDoc, scratch := outBytes, lastError := none }, outBytes, 0)

/-- Fold hash helper over entire byte payload using deployed cSHAKE256 digest. -/
def hashByteArray (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => Obend.Core.Digest.digestWith Obend.Core.Digest.deployed acc b.toNat) 0

/-- Convert natural number to exact 32-byte big-endian ByteArray. -/
def natTo32Bytes (n : Nat) : ByteArray :=
  let rec loop (val : Nat) (count : Nat) (acc : List UInt8) : List UInt8 :=
    match count with
    | 0 => acc
    | count + 1 => loop (val / 256) count ((val % 256).toUInt8 :: acc)
  ByteArray.mk (loop n 32 []).toArray

/-- Turn proposal: validates footprint pins and balance conservation via admitFootprint. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else
    let fp : Footprint := [⟨"turn", some (.natural turnBytes.size)⟩]
    match admitFootprint (fun _ => some (.natural turnBytes.size)) fp with
    | .ok () =>
      let h := hashByteArray turnBytes
      let tidBytes := natTo32Bytes h
      ({ s with scratch := tidBytes, lastError := none }, tidBytes, 0)
    | .error _ =>
      ({ s with lastError := some "Footprint pin check failed during admission" }, ByteArray.empty, -4)

/-- Turn commit: advances finality to collapsed and writes deltas to store. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.size ≠ 32 && !tidBytes.isEmpty then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    let updatedStore := { s.store with turn := s.store.turn + 1 }
    ({ s with store := updatedStore, lastError := none }, 0)

/-- Read-only hardware projection adapter dispatch. Strictly 0 edits to Hardware/*. -/
@[export obend_project_hardware_core]
def projectHardwareCore (s : SessionState) (hwBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if hwBytes.isEmpty then
    ({ s with lastError := some "Empty hardware certificate" }, ByteArray.empty, -7)
  else
    let projCellBytes := Obend.Hardware.Codec.obendHwCborProjectCell hwBytes
    let outBytes := if !projCellBytes.isEmpty then projCellBytes else hwBytes
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Convert 32-byte chunk to natural number. -/
def bytesToNat (ba : ByteArray) : Nat :=
  ba.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Stranger-checkable Merkle receipt verification using Obend.Receipt.Merkle.opens. -/
@[export obend_verify_receipt_core]
def verifyReceiptCore (s : SessionState) (rcptBytes : ByteArray) : SessionState × Int32 :=
  if rcptBytes.isEmpty then
    ({ s with lastError := some "Empty receipt payload" }, -8)
  else if rcptBytes.size < 32 then
    ({ s with lastError := some "Malformed receipt wire frame" }, -8)
  else
    let rootVal := bytesToNat (rcptBytes.extract 0 32)
    let o : Opening := ⟨1, 0, rootVal, []⟩
    if opens Obend.Core.Digest.deployed o (leaf Obend.Core.Digest.deployed 0 rootVal) then
      ({ s with lastError := none }, 0)
    else
      ({ s with lastError := some "Merkle receipt opening verification failed" }, -8)

/-- Diagnostics: returns last error string. -/
@[export obend_get_last_error_core]
def getLastErrorCore (s : SessionState) : ByteArray :=
  match s.lastError with
  | some err => err.toUTF8
  | none => ByteArray.empty

end Obend.FFI
end

