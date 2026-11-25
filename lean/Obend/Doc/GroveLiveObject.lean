module
public import Obend.Doc.Patch
public import Obend.Core.HeapImage
public import Obend.Core.Proofs.Preservation.Cases.Activities
public import Obend.Codec.Hex

public section
namespace Obend.Doc.LiveObject
open Obend.Core.Term Obend.Core.Ty Obend.Core.Check Obend.Core.Machine
open Obend.Core.MachineTyping Obend.Core.HeapImage Obend.Codec.Hex
set_option autoImplicit false

private theorem nibble_utf8 (n : Nat) :
    [hexNibbleChar n].utf8Encode.data.toList = [hexNibbleByte n] := by
  have table : ∀ d : Fin 16, [hexNibbleChar d.val].utf8Encode.data.toList = [hexNibbleByte d.val] := by decide
  simpa only [hexNibbleChar_mod, hexNibbleByte_mod] using table ⟨n % 16, Nat.mod_lt _ (by decide)⟩

private theorem hex_utf8 (bs : List UInt8) :
    (bytesToHexChars bs).utf8Encode.data.toList = bytesToHexAscii bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [bytesToHexChars_cons, bytesToHexAscii_cons, List.utf8Encode_cons,
      ByteArray.toList_data_append, List.utf8Encode_cons (l := bytesToHexChars bs),
      ByteArray.toList_data_append, nibble_utf8, nibble_utf8, ih]
    rfl

/-- Decode the strict lowercase wire spelling directly from UTF-8 bytes. -/
def decodeImageText (hex : String) : Option State := do
  let bytes ← hexByteArrayStrict? hex.toUTF8
  decodeHeapImage bytes

@[simp] theorem decodeImageText_encode (s : State) :
    decodeImageText (byteArrayToHex (encodeHeapImage s)) = some s := by
  let bytes := encodeHeapImage s
  have read := hexByteArrayStrict?_toList (byteArrayToHex bytes).toUTF8
  have spelling : (byteArrayToHex bytes).toUTF8.data.toList = bytesToHexAscii bytes.data.toList := by
    simpa only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList] using hex_utf8 bytes.data.toList
  rw [spelling, hexAsciiToBytes?_bytesToHexAscii] at read
  unfold decodeImageText
  change (hexByteArrayStrict? (byteArrayToHex bytes).toUTF8).bind decodeHeapImage = _
  cases h : hexByteArrayStrict? (byteArrayToHex bytes).toUTF8 with
  | none => rw [h] at read; contradiction
  | some b =>
    rw [h] at read
    have eq : b = bytes := ByteArray.ext (Array.toList_inj.mp (Option.some.inj read))
    subst b
    exact decodeHeapImage_encodeHeapImage s

/-- An executable cell on the existing Vault wire. The tag distinguishes a checkpoint
from ordinary source. Its payload includes the heap, control, environments and stack. -/
def checkpointCell (name : String) (s : State) : Content :=
  .cell name .obendCode (.variant "core4.heap/1" (.label (byteArrayToHex (encodeHeapImage s)))) [] none

def restore : Content → Option State
  | .cell _ .obendCode (.variant "core4.heap/1" (.label hex)) _ _ => decodeImageText hex
  | _ => none

private theorem restore_content (name : String) (s : State) : restore (checkpointCell name s) = some s := by
  simp [restore, checkpointCell]

/-- Only unused atom identities can be allocated. A tombstone cannot be reused. -/
def allocate (g : Graph) (atId parent : AtomId) (name : String) (s : State) : Option Graph :=
  if atId == root || g.isDead atId || (g.label atId).isSome then none
  else if parent != root && !g.alive parent then none
  else some (g.step (.add atId (checkpointCell name s) parent))

/-- Producer evidence is erased. Its indices tie it to this exact machine state. -/
structure Checkpoint (A : Assumptions) (types : AddressTypes) (result : Ty) where
  state : State
  typed : Nonempty (StateTyping A types state result)

def save {A : Assumptions} {types : AddressTypes} {result : Ty}
    (g : Graph) (atId parent : AtomId) (name : String) (c : Checkpoint A types result) : Option Graph :=
  allocate g atId parent name c.state

def load (g : Graph) (atId : AtomId) : Option State :=
  if g.isDead atId then none else (g.label atId).bind restore

theorem load_allocate
    {g saved : Graph} {atId parent : AtomId} {name : String} {s : State}
    (ok : allocate g atId parent name s = some saved) :
    load saved atId = some s := by
  unfold allocate at ok
  split at ok
  · contradiction
  · rename_i fresh
    simp only [Bool.or_eq_true, Option.isSome_iff_exists, not_or] at fresh
    split at ok
    · contradiction
    cases ok
    have vacant : g.label atId = none := by cases h : g.label atId <;> simp_all
    unfold load
    rw [show (g.step (.add atId (checkpointCell name s) parent)).isDead atId = false from
      Bool.eq_false_iff.mpr fresh.1.2, Graph.label_add, vacant]
    simpa using restore_content name s

def resumeAt (g : Graph) (atId : AtomId) (reply : Term) : Option State :=
  (load g atId).bind (resume reply)

theorem resumeAt_typed {A : Assumptions} {types : AddressTypes} {P R T : Ty}
    {g saved : Graph} {atId parent plan : Nat} {name : String} {s : State}
    (typed : StateTyping A types s (.computation P R T))
    (ok : save g atId parent name ⟨s, ⟨typed⟩⟩ = some saved)
    (yielded : s.control = .yielded plan) {reply : Term} {uses : Uses}
    (checked : PartialTyping A [] reply R uses) :
    ∃ next, resumeAt saved atId reply = some next ∧ resume reply s = some next ∧
      Nonempty (StateTyping A types next (.computation P R T)) := by
  have resumed : resume reply s = some {s with control := .evaluate reply []} := by
    simp [resume, yielded]
  exact ⟨_, by simp [resumeAt, load_allocate ok, resumed], resumed,
    Obend.Core.Proofs.Preservation.typed_resume_preserved typed yielded checked resumed⟩

end Obend.Doc.LiveObject
