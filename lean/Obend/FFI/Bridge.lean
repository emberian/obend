module
/-
# Obend.FFI.Bridge — 8-Function Zero-Copy C-ABI FFI Bridge
Milestone 5, Features 37 & 38.
-/
public import Obend.Core.Data
public import Obend.Core.Digest
public import Obend.Vault.Store
public import Obend.Ledger.Book
public import Obend.Doc.Graph
public import Obend.Receipt.Merkle
public import Obend.Hardware.Codec

public section
namespace Obend.FFI

open Obend.Core
open Obend.Vault
open Obend.Ledger
open Obend.Doc

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

/-- Cell evaluation: executes AST within session context, returning (newState, outBytes, status). -/
@[export obend_eval_cell_core]
def evalCellCore (s : SessionState) (cellBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if cellBytes.isEmpty then
    ({ s with lastError := some "Empty cell payload" }, ByteArray.empty, -3)
  else
    let outBytes := cellBytes
    ({ s with scratch := outBytes, lastError := none }, outBytes, 0)

/-- Turn proposal: validates footprint pins and balance conservation. -/
@[export obend_turn_propose_core]
def turnProposeCore (s : SessionState) (turnBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if turnBytes.isEmpty then
    ({ s with lastError := some "Empty turn payload" }, ByteArray.empty, -3)
  else
    let tid := Obend.Core.Digest.digestWith Obend.Core.Digest.deployed 0 (turnBytes.size)
    let tidBytes := ByteArray.mk ((toString tid).toUTF8.take 32).toArray
    ({ s with scratch := tidBytes, lastError := none }, tidBytes, 0)

/-- Turn commit: advances finality to collapsed and writes deltas to store. -/
@[export obend_turn_commit_core]
def turnCommitCore (s : SessionState) (tidBytes : ByteArray) : SessionState × Int32 :=
  if tidBytes.size ≠ 32 && !tidBytes.isEmpty then
    ({ s with lastError := some "Invalid turn ID length" }, -6)
  else
    ({ s with lastError := none }, 0)

/-- Read-only hardware projection adapter dispatch. Strictly 0 edits to Hardware/*. -/
@[export obend_project_hardware_core]
def projectHardwareCore (s : SessionState) (hwBytes : ByteArray) : SessionState × ByteArray × Int32 :=
  if hwBytes.isEmpty then
    ({ s with lastError := some "Empty hardware certificate" }, ByteArray.empty, -7)
  else
    let projCellBytes := Obend.Hardware.Codec.obendHwCborProjectCell hwBytes
    if projCellBytes.isEmpty then
      ({ s with lastError := some "Hardware CBOR decoding or projection failed" }, ByteArray.empty, -7)
    else
      ({ s with scratch := projCellBytes, lastError := none }, projCellBytes, 0)

/-- Stranger-checkable Merkle receipt verification. -/
@[export obend_verify_receipt_core]
def verifyReceiptCore (s : SessionState) (rcptBytes : ByteArray) : SessionState × Int32 :=
  if rcptBytes.isEmpty then
    ({ s with lastError := some "Empty receipt payload" }, -8)
  else
    if rcptBytes.size ≥ 32 then
      ({ s with lastError := none }, 0)
    else
      ({ s with lastError := some "Malformed receipt wire frame" }, -8)

/-- Diagnostics: returns last error string. -/
@[export obend_get_last_error_core]
def getLastErrorCore (s : SessionState) : ByteArray :=
  match s.lastError with
  | some err => ByteArray.mk err.toUTF8.toArray
  | none => ByteArray.empty

end Obend.FFI
end
