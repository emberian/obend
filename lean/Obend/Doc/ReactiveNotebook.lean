module
public import Obend.Doc.Structured
public import Obend.Slot.SupportSheaf
public import Obend.Vault.FrustumMembrane
public import Std.Data.String.ToNat
public import Std.Data.TreeMap.Lemmas
public import Std.Data.TreeSet.Lemmas

/-!
Reactive notebook admission, deterministic support-local evaluation, exact downstream invalidation,
and lossless JSON. IDs encode the supplied topological schedule; body edits retain that interface.
Use `admitNotebook` at ingress. Cache copies take constant time per object; publishing cached exports
and reading inputs use balanced tables. Total sweep work is O((cells + bindings) log symbols), plus
kernel and receipt work for dirty cells only. The executable refinements are selected by `csimp`.

A cell is a `Doc.Graph` atom: `CellId` is `AtomId`, and `cellAddress` is its one address in a
`FrustumMembrane` world (`atomOfAddress` inverts it, and accepts nothing else). A receipt is the
256-bit cSHAKE256 of the cell, its inputs and its outputs, every field length-framed, under its own
customization (`receipt_binds`). `Vault.TransclusionAndMirror` snips a viewer's frustum out of a
notebook.
-/
public section
namespace Obend.Doc.Reactive
open Lean (Json)
open Obend.Vault.FrustumMembrane (utf8_injective)
open Obend.Crypto (leb128 leb128_prefix_inj encodeListField encodeListField_prefix_inj)
open Obend.Digest.Cshake256 (cshake256Bytes cshake256Bytes_length)
open Obend.Digest.HashBytes (CollisionAmong ofBE ofBE_lt)
set_option autoImplicit false

/-- A notebook cell is an atom of the document graph. -/
abbrev CellId := AtomId
abbrev SymbolName := String
abbrev Environment := SymbolName → Int

/-- **The address of an atom in a membrane world**: its decimal numeral. -/
def cellAddress (a : CellId) : Obend.Vault.FrustumMembrane.CellId := Nat.repr a

/-- The atom a membrane cell id addresses. Only the canonical numeral of an atom is an address. -/
def atomOfAddress (s : Obend.Vault.FrustumMembrane.CellId) : Option CellId :=
  match s.toNat? with
  | some a => if Nat.repr a = s then some a else none
  | none => none

theorem atomOfAddress_cellAddress (a : CellId) : atomOfAddress (cellAddress a) = some a := by
  simp [atomOfAddress, cellAddress]

/-- A membrane id that addresses an atom is that atom's address: the two id spaces correspond one
to one on the image of `cellAddress`. -/
theorem cellAddress_of_atomOfAddress {s : Obend.Vault.FrustumMembrane.CellId} {a : CellId}
    (h : atomOfAddress s = some a) : cellAddress a = s := by
  unfold atomOfAddress at h
  cases hn : s.toNat? with
  | none => simp [hn] at h
  | some n =>
    simp only [hn] at h
    by_cases hr : Nat.repr n = s
    · simp only [hr, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      exact hr
    · simp [hr] at h

theorem cellAddress_injective {a b : CellId} (h : cellAddress a = cellAddress b) : a = b := by
  have ha := atomOfAddress_cellAddress a
  rw [h, atomOfAddress_cellAddress] at ha
  exact (Option.some.inj ha).symm

/-- Integer and fixed-unit arithmetic. Inputs index the declared support, never the world. -/
inductive Opcode where
  | literal | input | add | sub | mul | div
  deriving DecidableEq, Repr
structure Instruction where
  op : Opcode
  arg : Int := 0
  deriving DecidableEq, Repr
abbrev CellBody := List (List Instruction)

structure ReactiveCell where
  id : CellId
  kind : ProjectionKind
  reads : List SymbolName
  defs : List SymbolName
  body : CellBody
  note : String := ""
  deriving DecidableEq, Repr

structure CellResult where
  values : List Int
  receipt : BitVec 256
  deriving DecidableEq, Repr

structure CachedCell where
  cell : ReactiveCell
  result : CellResult
  deriving DecidableEq, Repr

/-- The list is an explicit schedule. IDs are stable topological ranks, with gaps allowed. -/
structure ReactiveNotebook where
  cells : List CachedCell
  deriving DecidableEq, Repr

def dependency (p u : ReactiveCell) : Prop := ∃ s ∈ p.defs, s ∈ u.reads
instance (p u : ReactiveCell) : Decidable (dependency p u) :=
  inferInstanceAs (Decidable (∃ s ∈ p.defs, s ∈ u.reads))

def uniqueExports (cs : List ReactiveCell) : Bool := decide ((cs.flatMap ReactiveCell.defs).Nodup)
def scheduleCheck (cs : List ReactiveCell) : Bool :=
  decide (cs.Pairwise (fun a b => a.id < b.id)) &&
  cs.all (fun p => cs.all (fun u => decide (dependency p u → p.id < u.id)))
def checkNotebookDag (cs : List ReactiveCell) : Bool := uniqueExports cs && scheduleCheck cs

/-- The accepted schedule has unique IDs and exports and a strict rank on every edge. -/
theorem checkNotebookDag_acyclic_sound (cs : List ReactiveCell)
    (h : checkNotebookDag cs = true) :
    (cs.map ReactiveCell.id).Nodup ∧ (cs.flatMap ReactiveCell.defs).Nodup ∧
    ∃ rank : CellId → Nat, ∀ p ∈ cs, ∀ u ∈ cs, dependency p u → rank p.id < rank u.id := by
  simp only [checkNotebookDag, uniqueExports, scheduleCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨?_, h.1, id, h.2.2⟩
  change List.Pairwise (· ≠ ·) (cs.map ReactiveCell.id)
  rw [List.pairwise_map]
  exact h.2.1.imp (fun hab => Nat.ne_of_lt hab)

theorem checkNotebookDag_complete (cs : List ReactiveCell)
    (hs : cs.Pairwise (fun a b => a.id < b.id))
    (hd : (cs.flatMap ReactiveCell.defs).Nodup)
    (he : ∀ p ∈ cs, ∀ u ∈ cs, dependency p u → p.id < u.id) :
    checkNotebookDag cs = true := by
  simp only [checkNotebookDag, uniqueExports, scheduleCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  exact ⟨hd, hs, he⟩

/-- Nonempty dependency paths; rank strictly grows at every step. -/
inductive DependencyPath (cs : List ReactiveCell) : ReactiveCell → ReactiveCell → Prop where
  | edge {p u} : p ∈ cs → u ∈ cs → dependency p u → DependencyPath cs p u
  | trans {p m u} : DependencyPath cs p m → DependencyPath cs m u → DependencyPath cs p u

theorem path_rank (cs : List ReactiveCell) (h : checkNotebookDag cs = true)
    {p u : ReactiveCell} (hp : DependencyPath cs p u) : p.id < u.id := by
  have he : ∀ p ∈ cs, ∀ u ∈ cs, dependency p u → p.id < u.id := by
    simp only [checkNotebookDag, scheduleCheck, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq] at h
    exact h.2.2
  induction hp with
  | edge a b e => exact he _ a _ b e
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

theorem cyclic_refused (cs : List ReactiveCell) {c : ReactiveCell}
    (h : DependencyPath cs c c) : checkNotebookDag cs = false := by
  cases hc : checkNotebookDag cs with
  | false => rfl
  | true => exact False.elim (Nat.lt_irrefl _ (path_rank cs hc h))

theorem duplicateExports_refused (cs : List ReactiveCell)
    (h : ¬ (cs.flatMap ReactiveCell.defs).Nodup) : checkNotebookDag cs = false := by
  simp [checkNotebookDag, uniqueExports, h]

/-! Canonical positional JSON: arrays frame every field, including every full-width receipt bit.
Numbers use integral JSON mantissas, avoiding host floating-point conversions. -/
def intJson (n : Int) : Json := .num ⟨n, 0⟩
def intOfJson : Json → Except String Int
  | .num ⟨n, 0⟩ => .ok n
  | _ => .error "expected integral number"
def natJson (n : Nat) : Json := .num ⟨.ofNat n, 0⟩
def natOfJson : Json → Except String Nat
  | .num ⟨.ofNat n, 0⟩ => .ok n
  | _ => .error "expected natural number"
@[simp] theorem nat_roundtrip (n : Nat) : natOfJson (natJson n) = .ok n := by rfl

def stringOfJson : Json → Except String String
  | .str s => .ok s
  | _ => .error "expected string"
def listJson {α : Type} (f : α → Json) (xs : List α) : Json := .arr (xs.map f).toArray
def listOfJson {α : Type} (f : Json → Except String α) : Json → Except String (List α)
  | .arr a => a.toList.mapM f
  | _ => .error "expected array"

theorem list_json_roundtrip {α : Type} (enc : α → Json) (dec : Json → Except String α)
    (h : ∀ x, dec (enc x) = .ok x) (xs : List α) :
    listOfJson dec (listJson enc xs) = .ok xs := by
  simp only [listJson, listOfJson]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h, ih, List.mapM_cons, bind, Except.bind, pure, Except.pure]

@[simp] theorem strings_roundtrip (xs : List String) :
    listOfJson stringOfJson (listJson Json.str xs) = .ok xs :=
  list_json_roundtrip Json.str stringOfJson (fun _ => rfl) xs

def opcodeTag : Opcode → Nat
  | .literal => 0 | .input => 1 | .add => 2 | .sub => 3 | .mul => 4 | .div => 5

def opcodeOfTag : Nat → Except String Opcode
  | 0 => .ok .literal | 1 => .ok .input | 2 => .ok .add
  | 3 => .ok .sub | 4 => .ok .mul | 5 => .ok .div
  | _ => .error "unknown arithmetic opcode"

def instructionJson (i : Instruction) : Json :=
  .arr #[natJson (opcodeTag i.op), intJson i.arg]
def jsonFields : Json → List Json
  | .arr a => a.toList
  | _ => []
def instructionOfJson (j : Json) : Except String Instruction :=
  match jsonFields j with
  | [a, b] => do return ⟨← opcodeOfTag (← natOfJson a), ← intOfJson b⟩
  | _ => .error "expected instruction"

@[simp] theorem instruction_roundtrip (i : Instruction) :
    instructionOfJson (instructionJson i) = .ok i := by
  rcases i with ⟨op, arg⟩; cases op <;> rfl

def bodyJson := listJson (listJson instructionJson)
def bodyOfJson := listOfJson (listOfJson instructionOfJson)
@[simp] theorem body_roundtrip (b : CellBody) : bodyOfJson (bodyJson b) = .ok b :=
  list_json_roundtrip _ _ (list_json_roundtrip _ _ instruction_roundtrip) b

def kindJson (k : ProjectionKind) : Json := .str k.toLabel
def kindOfJson : Json → Except String ProjectionKind
  | .str s => match ProjectionKind.ofLabel s with
    | some k => .ok k
    | none => .error "unknown projection kind"
  | _ => .error "expected projection kind"
@[simp] theorem kind_roundtrip (k : ProjectionKind) : kindOfJson (kindJson k) = .ok k := by
  simp [kindJson, kindOfJson]

def cellJson (c : ReactiveCell) : Json := .arr #[natJson c.id, kindJson c.kind,
  listJson Json.str c.reads, listJson Json.str c.defs, bodyJson c.body, .str c.note]
def cellOfJson (j : Json) : Except String ReactiveCell :=
  match jsonFields j with
  | [a, b, c, d, e, f] => do
    return ⟨← natOfJson a, ← kindOfJson b, ← listOfJson stringOfJson c,
      ← listOfJson stringOfJson d, ← bodyOfJson e, ← stringOfJson f⟩
  | _ => .error "expected reactive cell"
@[simp] theorem cell_roundtrip (c : ReactiveCell) : cellOfJson (cellJson c) = .ok c := by
  cases c
  simp [cellJson, cellOfJson, jsonFields, stringOfJson, bind, Except.bind, pure, Except.pure]

def receiptOfJson (j : Json) : Except String (BitVec 256) := do
  let n ← natOfJson j
  if n < 2^256 then return BitVec.ofNat 256 n else .error "receipt exceeds 256 bits"
@[simp] theorem receipt_roundtrip (r : BitVec 256) :
    receiptOfJson (natJson r.toNat) = .ok r := by
  simp [receiptOfJson, r.isLt, bind, Except.bind, pure, Except.pure]

def resultJson (r : CellResult) : Json :=
  .arr #[listJson intJson r.values, natJson r.receipt.toNat]
def resultOfJson (j : Json) : Except String CellResult :=
  match jsonFields j with
  | [a, b] => do return ⟨← listOfJson intOfJson a, ← receiptOfJson b⟩
  | _ => .error "expected cached result"
@[simp] theorem result_roundtrip (r : CellResult) : resultOfJson (resultJson r) = .ok r := by
  cases r
  simp [resultJson, resultOfJson, jsonFields, list_json_roundtrip, intJson, intOfJson,
    bind, Except.bind, pure, Except.pure]

def cachedJson (c : CachedCell) : Json := .arr #[cellJson c.cell, resultJson c.result]
def cachedOfJson (j : Json) : Except String CachedCell :=
  match jsonFields j with
  | [a, b] => do return ⟨← cellOfJson a, ← resultOfJson b⟩
  | _ => .error "expected cached cell"
@[simp] theorem cached_roundtrip (c : CachedCell) : cachedOfJson (cachedJson c) = .ok c := by
  cases c; simp [cachedJson, cachedOfJson, jsonFields, bind, Except.bind, pure, Except.pure]

def encodeNotebookObnbJson (nb : ReactiveNotebook) : Json :=
  .arr #[.str "obnb-reactive-1", listJson cachedJson nb.cells]
def decodeNotebookObnbJson (j : Json) : Except String ReactiveNotebook :=
  match jsonFields j with
  | [.str "obnb-reactive-1", cells] => do return ⟨← listOfJson cachedOfJson cells⟩
  | _ => .error "expected obnb-reactive-1 notebook"

theorem notebook_roundtrip_obnb_json (nb : ReactiveNotebook) :
    decodeNotebookObnbJson (encodeNotebookObnbJson nb) = .ok nb := by
  cases nb
  simp [encodeNotebookObnbJson, decodeNotebookObnbJson, jsonFields, list_json_roundtrip,
    bind, Except.bind, pure, Except.pure]

/-! Receipt preimages. Every field is self-delimiting, so the preimage determines the cell, its
inputs and its outputs (`cellReceiptPreimage_injective`). -/

/-- A self-delimiting encoder: equal encodings, whatever follows them, are of equal values. -/
def Framed {α : Type} (enc : α → List UInt8) : Prop :=
  ∀ a b r₁ r₂, enc a ++ r₁ = enc b ++ r₂ → a = b ∧ r₁ = r₂

/-- Each element tagged and framed; the list closed by a zero tag. -/
def frameList {α : Type} (enc : α → List UInt8) : List α → List UInt8
  | [] => [0]
  | x :: xs => 1 :: (enc x ++ frameList enc xs)

theorem frameList_framed {α : Type} {enc : α → List UInt8} (h : Framed enc) :
    Framed (frameList enc) := by
  intro a
  induction a with
  | nil =>
    intro b r₁ r₂ e
    cases b with
    | nil => exact ⟨rfl, by simpa [frameList] using e⟩
    | cons y ys => simp [frameList] at e
  | cons x xs ih =>
    intro b r₁ r₂ e
    cases b with
    | nil => simp [frameList] at e
    | cons y ys =>
      simp only [frameList, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
      obtain ⟨hxy, e₁⟩ := h _ _ _ _ e
      obtain ⟨hrest, e₂⟩ := ih _ _ _ e₁
      exact ⟨by rw [hxy, hrest], e₂⟩

/-- Integers as naturals: non-negatives even, negatives odd. -/
def intCode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem intCode_injective {a b : Int} (h : intCode a = intCode b) : a = b := by
  cases a <;> cases b <;> simp only [intCode] at h <;> first | omega | (congr 1; omega)

def frameInt (v : Int) : List UInt8 := leb128 (intCode v)
def frameStr (s : String) : List UInt8 := encodeListField (Obend.Vault.FrustumMembrane.utf8 s)
def frameInstr (i : Instruction) : List UInt8 := leb128 (opcodeTag i.op) ++ frameInt i.arg

theorem frameInt_framed : Framed frameInt := fun _ _ _ _ e =>
  ⟨intCode_injective (leb128_prefix_inj e).1, (leb128_prefix_inj e).2⟩

theorem frameInt_injective {a b : Int} (h : frameInt a = frameInt b) : a = b :=
  (frameInt_framed a b [] [] (by simpa using h)).1

theorem frameStr_framed : Framed frameStr := fun _ _ _ _ e =>
  ⟨utf8_injective (encodeListField_prefix_inj e).1, (encodeListField_prefix_inj e).2⟩

theorem opcodeTag_injective {a b : Opcode} (h : opcodeTag a = opcodeTag b) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [opcodeTag] at h

theorem frameInstr_framed : Framed frameInstr := by
  intro a b r₁ r₂ e
  simp only [frameInstr, List.append_assoc] at e
  obtain ⟨ho, e₁⟩ := leb128_prefix_inj e
  obtain ⟨ha, e₂⟩ := frameInt_framed _ _ _ _ e₁
  obtain ⟨op₁, arg₁⟩ := a
  obtain ⟨op₂, arg₂⟩ := b
  have h₁ : op₁ = op₂ := opcodeTag_injective ho
  have h₂ : arg₁ = arg₂ := ha
  exact ⟨by rw [h₁, h₂], e₂⟩

/-- What a receipt hashes: the cell's id, kind, reads, exports, code and note, then the inputs it
read and the outputs it computed, each framed. -/
def cellReceiptPreimage (c : ReactiveCell) (inputs values : List Int) : List UInt8 :=
  leb128 c.id ++ (frameStr c.kind.toLabel ++ (frameList frameStr c.reads ++
    (frameList frameStr c.defs ++ (frameList (frameList frameInstr) c.body ++
      (frameStr c.note ++ (frameList frameInt inputs ++ frameList frameInt values))))))

theorem cellReceiptPreimage_injective {c₁ c₂ : ReactiveCell} {i₁ i₂ v₁ v₂ : List Int}
    (h : cellReceiptPreimage c₁ i₁ v₁ = cellReceiptPreimage c₂ i₂ v₂) :
    c₁ = c₂ ∧ i₁ = i₂ ∧ v₁ = v₂ := by
  unfold cellReceiptPreimage at h
  obtain ⟨hid, h⟩ := leb128_prefix_inj h
  obtain ⟨hk, h⟩ := frameStr_framed _ _ _ _ h
  obtain ⟨hr, h⟩ := frameList_framed frameStr_framed _ _ _ _ h
  obtain ⟨hd, h⟩ := frameList_framed frameStr_framed _ _ _ _ h
  obtain ⟨hb, h⟩ := frameList_framed (frameList_framed frameInstr_framed) _ _ _ _ h
  obtain ⟨hn, h⟩ := frameStr_framed _ _ _ _ h
  obtain ⟨hi, h⟩ := frameList_framed frameInt_framed _ _ _ _ h
  obtain ⟨hv, _⟩ := frameList_framed frameInt_framed _ _ [] [] (by simpa using h)
  cases c₁
  cases c₂
  simp only [ReactiveCell.mk.injEq]
  exact ⟨⟨hid, ProjectionKind.toLabel_injective hk, hr, hd, hb, hn⟩, hi, hv⟩

/-- Customization string of the notebook receipt hash. -/
def cellReceiptCustomization : List UInt8 := "OBEND.DOC.NOTEBOOK.RECEIPT/v1".toUTF8.data.toList

/-- The 256-bit receipt of a preimage: all 32 bytes of cSHAKE256 under the receipt customization. -/
def cshakeReceipt (preimage : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes cellReceiptCustomization preimage))

/-- A Type-valued witness whose two messages are pinned to this comparison. -/
structure ReceiptCollision (p q : List UInt8) : Type where
  distinct : p ≠ q
  sameDigest : ofBE (cshake256Bytes cellReceiptCustomization p) =
    ofBE (cshake256Bytes cellReceiptCustomization q)

def extractReceiptPreimageBreak {p₁ p₂ : List UInt8}
    (h : cshakeReceipt p₁ = cshakeReceipt p₂) : PSum (p₁ = p₂) (ReceiptCollision p₁ p₂) :=
  if hp : p₁ = p₂ then .inl hp else .inr ⟨hp, by
    have hw : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
    have h₁ := ofBE_lt (cshake256Bytes cellReceiptCustomization p₁)
    have h₂ := ofBE_lt (cshake256Bytes cellReceiptCustomization p₂)
    rw [cshake256Bytes_length, hw] at h₁ h₂
    have hn := congrArg BitVec.toNat h
    simp only [cshakeReceipt, BitVec.toNat_ofNat] at hn
    rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hn⟩

theorem ReceiptCollision.toCollisionAmong {p q : List UInt8} (w : ReceiptCollision p q) :
    CollisionAmong (cshake256Bytes cellReceiptCustomization) (fun x => x = p ∨ x = q) :=
  ⟨p, q, .inl rfl, .inr rfl, w.distinct, w.sameDigest⟩

/-- Equal receipts bind precisely the two preimages compared. -/
theorem cshakeReceipt_binds {p₁ p₂ : List UInt8} (h : cshakeReceipt p₁ = cshakeReceipt p₂) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes cellReceiptCustomization)
      (fun x => x = p₁ ∨ x = p₂) :=
  match extractReceiptPreimageBreak h with
  | .inl he => .inl he
  | .inr w => .inr w.toCollisionAmong

/-- The executable kernel can only see the ordered restriction to declared reads. -/
structure CellKernel where
  run : ProjectionKind → List Instruction → List Int → Int
  hash : List UInt8 → BitVec 256

def arithmeticStep (inputs : List Int) (stack : List Int) (i : Instruction) : List Int :=
  let a := stack.headD 0
  let b := stack.tail.headD 0
  match i.op with
  | .literal => i.arg :: stack
  | .input => inputs[i.arg.toNat]?.getD 0 :: stack
  | .add => (b + a) :: stack.drop 2
  | .sub => (b - a) :: stack.drop 2
  | .mul => (b * a) :: stack.drop 2
  | .div => (b / a) :: stack.drop 2

def arithmeticRun (_kind : ProjectionKind) (code : List Instruction) (inputs : List Int) : Int :=
  (code.foldl (arithmeticStep inputs) []).headD 0

def scientificKernel : CellKernel := ⟨arithmeticRun, cshakeReceipt⟩

def restrict (c : ReactiveCell) (env : Environment) : List Int := c.reads.map env

def evalCell (k : CellKernel) (c : ReactiveCell) (env : Environment) : CellResult :=
  let inputs := restrict c env
  let values := c.defs.zipIdx.map fun (_, i) => k.run c.kind (c.body[i]?.getD []) inputs
  ⟨values, k.hash (cellReceiptPreimage c inputs values)⟩

/-- **A receipt binds the cell, the inputs it read and the outputs it computed.** Under the cSHAKE256
receipt, two evaluations with one receipt are of the same cell on the same inputs with the same
outputs, or their two preimages collide. -/
theorem receipt_binds (run : ProjectionKind → List Instruction → List Int → Int)
    {c₁ c₂ : ReactiveCell} {a b : Environment}
    (h : (evalCell ⟨run, cshakeReceipt⟩ c₁ a).receipt = (evalCell ⟨run, cshakeReceipt⟩ c₂ b).receipt) :
    (c₁ = c₂ ∧ restrict c₁ a = restrict c₂ b ∧
      (evalCell ⟨run, cshakeReceipt⟩ c₁ a).values = (evalCell ⟨run, cshakeReceipt⟩ c₂ b).values) ∨
    CollisionAmong (cshake256Bytes cellReceiptCustomization) (fun x =>
      x = cellReceiptPreimage c₁ (restrict c₁ a) (evalCell ⟨run, cshakeReceipt⟩ c₁ a).values ∨
      x = cellReceiptPreimage c₂ (restrict c₂ b) (evalCell ⟨run, cshakeReceipt⟩ c₂ b).values) :=
  (cshakeReceipt_binds h).imp cellReceiptPreimage_injective id

/-- Constructive semantic receipt binding; the right branch retains the exact pair. -/
def extractReceiptBreak (run : ProjectionKind → List Instruction → List Int → Int)
    {c₁ c₂ : ReactiveCell} {a b : Environment}
    (h : (evalCell ⟨run, cshakeReceipt⟩ c₁ a).receipt = (evalCell ⟨run, cshakeReceipt⟩ c₂ b).receipt) :
    PSum (c₁ = c₂ ∧ restrict c₁ a = restrict c₂ b ∧
      (evalCell ⟨run, cshakeReceipt⟩ c₁ a).values = (evalCell ⟨run, cshakeReceipt⟩ c₂ b).values)
      (ReceiptCollision
        (cellReceiptPreimage c₁ (restrict c₁ a) (evalCell ⟨run, cshakeReceipt⟩ c₁ a).values)
        (cellReceiptPreimage c₂ (restrict c₂ b) (evalCell ⟨run, cshakeReceipt⟩ c₂ b).values)) :=
  match extractReceiptPreimageBreak h with
  | .inl he => .inl (cellReceiptPreimage_injective he)
  | .inr w => .inr w

theorem evalCell_frame (k : CellKernel) (c : ReactiveCell) (a b : Environment)
    (h : ∀ s ∈ c.reads, a s = b s) : evalCell k c a = evalCell k c b := by
  have hr : restrict c a = restrict c b := List.map_congr_left h
  simp only [evalCell, hr]

/-- Pins use the same equality facts as the shared support sheaf. -/
structure CellPins where
  facts : List (Obend.Slot.SupportSheaf.KeyedFact SymbolName Int)

instance cellSupportSheaf : Obend.Slot.SupportSheaf.SupportSheaf
    (Obend.Slot.SupportSheaf.KeyedWorld SymbolName Int)
    (Obend.Slot.SupportSheaf.KeyedFact SymbolName Int) CellPins where
  supports p := p.facts
  holds := Obend.Slot.SupportSheaf.keyedHolds
  usable w p := p.facts.all (Obend.Slot.SupportSheaf.keyedHolds w)
  usable_supports _ _ h := List.all_eq_true.mp h
  holds_frame h := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro hu f hf; rw [← h f hf]; exact hu f hf
    · intro hu f hf; rw [h f hf]; exact hu f hf

/-- Publishing only declared definitions makes writes as local as reads. -/
def publish (c : ReactiveCell) (r : CellResult) (env : Environment) : Environment :=
  fun s => if s ∈ c.defs then r.values[c.defs.idxOf s]?.getD 0 else env s

def evalSchedule (k : CellKernel) : List ReactiveCell → Environment → List CachedCell
  | [], _ => []
  | c :: cs, env =>
    let r := evalCell k c env
    ⟨c, r⟩ :: evalSchedule k cs (publish c r env)

def evalFromScratch (k : CellKernel) (cs : List ReactiveCell) : ReactiveNotebook :=
  ⟨evalSchedule k cs (fun _ => 0)⟩

def notebookEnvironment (nb : ReactiveNotebook) : Environment :=
  nb.cells.foldl (fun env c => publish c.cell c.result env) (fun _ => 0)

/-- Body edits preserve the dependency interface and stable rank. -/
structure NotebookAction where
  target : CellId
  body : CellBody
  deriving DecidableEq, Repr

def editCell (a : NotebookAction) (c : ReactiveCell) : ReactiveCell :=
  if c.id = a.target then {c with body := a.body} else c

def applyEdit (a : NotebookAction) (cs : List ReactiveCell) := cs.map (editCell a)

def isDirty (target : CellId) (changed : List SymbolName) (c : ReactiveCell) : Bool :=
  decide (c.id = target) || c.reads.any (fun s => decide (s ∈ changed))

def nextChanged (target : CellId) (changed : List SymbolName) (c : ReactiveCell) :=
  if isDirty target changed c then c.defs ++ changed else changed

/-- A topological forward sweep computes transitive dependencies, including the root. -/
def coneScan (target : CellId) : List ReactiveCell → List SymbolName → List CellId
  | [], _ => []
  | c :: cs, changed =>
    let rest := coneScan target cs (nextChanged target changed c)
    if isDirty target changed c then c.id :: rest else rest

def dirtyCone (cs : List ReactiveCell) (target : CellId) : List CellId := coneScan target cs []

/-- The clean branch copies the existing result without calling the kernel or hashing. -/
def reuseOrEval (k : CellKernel) (dirty : Bool) (old : CellResult)
    (c : ReactiveCell) (env : Environment) : CellResult :=
  if dirty then evalCell k c env else old

def recompute (k : CellKernel) (a : NotebookAction) :
    List CachedCell → Environment → List SymbolName → List CachedCell
  | [], _, _ => []
  | old :: cs, env, changed =>
    let c := editCell a old.cell
    let dirty := isDirty a.target changed c
    let r := reuseOrEval k dirty old.result c env
    ⟨c, r⟩ :: recompute k a cs (publish c r env) (nextChanged a.target changed c)

def editCellAndRecompute (k : CellKernel) (nb : ReactiveNotebook) (a : NotebookAction) :
    ReactiveNotebook := ⟨recompute k a nb.cells (fun _ => 0) []⟩

@[simp] theorem editCell_id (a : NotebookAction) (c : ReactiveCell) :
    (editCell a c).id = c.id := by unfold editCell; split <;> rfl
@[simp] theorem editCell_reads (a : NotebookAction) (c : ReactiveCell) :
    (editCell a c).reads = c.reads := by unfold editCell; split <;> rfl
@[simp] theorem editCell_defs (a : NotebookAction) (c : ReactiveCell) :
    (editCell a c).defs = c.defs := by unfold editCell; split <;> rfl
@[simp] theorem dirty_edit (a : NotebookAction) (changed : List SymbolName) (c : ReactiveCell) :
    isDirty a.target changed (editCell a c) = isDirty a.target changed c := by
  simp [isDirty]
@[simp] theorem nextChanged_edit (a : NotebookAction) (changed : List SymbolName) (c : ReactiveCell) :
    nextChanged a.target changed (editCell a c) = nextChanged a.target changed c := by
  simp [nextChanged]

theorem clean_support (target : CellId) (changed : List SymbolName) (c : ReactiveCell)
    (h : isDirty target changed c = false) :
    c.id ≠ target ∧ ∀ s ∈ c.reads, s ∉ changed := by
  simpa [isDirty, List.any_eq_false] using h

def AgreeOutside (changed : List SymbolName) (a b : Environment) : Prop :=
  ∀ s, s ∉ changed → a s = b s

theorem publish_frame (c d : ReactiveCell) (r t : CellResult) (a b : Environment)
    (hdefs : c.defs = d.defs) (changed : List SymbolName)
    (h : AgreeOutside changed a b) :
    AgreeOutside (c.defs ++ changed) (publish c r a) (publish d t b) := by
  intro s hs
  simp only [List.mem_append, not_or] at hs
  simp [publish, ← hdefs, hs.1, h s hs.2]

theorem publish_same (c : ReactiveCell) (r : CellResult) (a b : Environment)
    (changed : List SymbolName) (h : AgreeOutside changed a b) :
    AgreeOutside changed (publish c r a) (publish c r b) := by
  intro s hs; simp only [publish]; split
  · rfl
  · exact h s hs

/-- Simultaneous old/new evaluation: only symbols exported by dirty predecessors may differ. -/
theorem recompute_eq_schedule (k : CellKernel) (a : NotebookAction)
    (cs : List ReactiveCell) (oldEnv newEnv : Environment) (changed : List SymbolName)
    (h : AgreeOutside changed oldEnv newEnv) :
    recompute k a (evalSchedule k cs oldEnv) newEnv changed =
      evalSchedule k (applyEdit a cs) newEnv := by
  induction cs generalizing oldEnv newEnv changed with
  | nil => rfl
  | cons c cs ih =>
    by_cases hd : isDirty a.target changed c = true
    · simp only [evalSchedule, recompute, applyEdit, List.map_cons, dirty_edit,
        reuseOrEval, hd, ↓ite_true, nextChanged, editCell_defs]
      congr 1
      apply ih
      exact publish_frame c (editCell a c) _ _ oldEnv newEnv (editCell_defs a c).symm changed h
    · have hf : isDirty a.target changed c = false := Bool.eq_false_iff.mpr hd
      obtain ⟨hne, hs⟩ := clean_support a.target changed c hf
      have he : editCell a c = c := by simp [editCell, hne]
      have hr : evalCell k c oldEnv = evalCell k c newEnv :=
        evalCell_frame k c oldEnv newEnv (fun s hm => h s (hs s hm))
      simp only [evalSchedule, recompute, applyEdit, List.map_cons, he, hf,
        reuseOrEval, Bool.false_eq_true, ↓ite_false, nextChanged, hr]
      congr 1
      apply ih
      exact publish_same c (evalCell k c newEnv) oldEnv newEnv changed h

/-- Exact equality includes all caches, receipts, and consequently the final symbol environment.
The stronger schedule lemma works even before admission; DAG admission supplies causal meaning. -/
theorem incrementalRecompute_eq_fromScratch (k : CellKernel) (cs : List ReactiveCell)
    (a : NotebookAction) :
    editCellAndRecompute k (evalFromScratch k cs) a =
      evalFromScratch k (applyEdit a cs) := by
  unfold editCellAndRecompute evalFromScratch
  congr 1
  exact recompute_eq_schedule k a cs _ _ [] (fun _ _ => rfl)


/-- The frame fast path is independent of *every* possible kernel implementation. -/
theorem reuseOrEval_clean (k : CellKernel) (old : CellResult) (c : ReactiveCell)
    (env : Environment) : reuseOrEval k false old c env = old := by rfl

theorem checkNotebookDag_edit (a : NotebookAction) (cs : List ReactiveCell) :
    checkNotebookDag (applyEdit a cs) = checkNotebookDag cs := by
  simp [checkNotebookDag, uniqueExports, scheduleCheck, applyEdit, List.pairwise_map,
    List.flatMap_map, List.all_map, Function.comp_def, dependency]

theorem coneScan_edit (a : NotebookAction) (cs : List ReactiveCell) (changed : List SymbolName) :
    coneScan a.target (applyEdit a cs) changed = coneScan a.target cs changed := by
  induction cs generalizing changed with
  | nil => rfl
  | cons c cs ih =>
    simp only [applyEdit, List.map_cons, coneScan, dirty_edit, editCell_id, nextChanged_edit]
    rw [show coneScan a.target (List.map (editCell a) cs)
      (nextChanged a.target changed c) = coneScan a.target cs
      (nextChanged a.target changed c) from ih _]

theorem recompute_untouched (k : CellKernel) (a : NotebookAction) (cs : List CachedCell)
    (env : Environment) (changed : List SymbolName) (u : CachedCell)
    (hu : u ∈ cs) (hn : u.cell.id ∉ coneScan a.target (cs.map CachedCell.cell) changed) :
    u ∈ recompute k a cs env changed := by
  induction cs generalizing env changed with
  | nil => cases hu
  | cons c cs ih =>
    simp only [List.mem_cons] at hu
    by_cases hd : isDirty a.target changed c.cell = true
    · have hn' : u.cell.id ≠ c.cell.id ∧
          u.cell.id ∉ coneScan a.target (cs.map CachedCell.cell)
            (nextChanged a.target changed c.cell) := by
        simpa only [List.map_cons, coneScan, hd, ite_true, List.mem_cons, not_or] using hn
      have hut : u ∈ cs := hu.resolve_left (fun he => hn'.1 (congrArg (fun x => x.cell.id) he))
      simp only [recompute, dirty_edit, nextChanged_edit, List.mem_cons]
      exact Or.inr (ih _ _ hut hn'.2)
    · have hf : isDirty a.target changed c.cell = false := Bool.eq_false_iff.mpr hd
      have hn' : u.cell.id ∉ coneScan a.target (cs.map CachedCell.cell)
          (nextChanged a.target changed c.cell) := by
        simpa only [List.map_cons, coneScan, hf, Bool.false_eq_true, ite_false] using hn
      have he : editCell a c.cell = c.cell := by
        simp [editCell, (clean_support _ _ _ hf).1]
      simp only [recompute, he, hf, reuseOrEval, Bool.false_eq_true, ite_false, List.mem_cons]
      rcases hu with rfl | hut
      · exact Or.inl (by cases u; rfl)
      · exact Or.inr (ih _ _ hut hn')

/-- The entire cached object survives unchanged, including every receipt bit and value. -/
theorem untouchedCells_preserve_receipts (k : CellKernel) (nb : ReactiveNotebook)
    (a : NotebookAction) (u : CachedCell) (hu : u ∈ nb.cells)
    (hn : u.cell.id ∉ dirtyCone (applyEdit a (nb.cells.map CachedCell.cell)) a.target) :
    u ∈ (editCellAndRecompute k nb a).cells := by
  apply recompute_untouched k a nb.cells _ [] u hu
  simpa only [dirtyCone, coneScan_edit] using hn

/-- A session retains the initial raw notebook, rather than resetting its state after each edit. -/
def runNotebookSession (k : CellKernel) : ReactiveNotebook → List NotebookAction → ReactiveNotebook
  | nb, [] => nb
  | nb, a :: rest => runNotebookSession k (editCellAndRecompute k nb a) rest

def editTrace : List ReactiveCell → List NotebookAction → List ReactiveCell
  | cs, [] => cs
  | cs, a :: rest => editTrace (applyEdit a cs) rest

inductive ValidNotebookSession (k : CellKernel) :
    List ReactiveCell → List NotebookAction → ReactiveNotebook → Prop where
  | start (cs) : checkNotebookDag cs = true → ValidNotebookSession k cs [] (evalFromScratch k cs)
  | step {cs acts nb} (a : NotebookAction) : ValidNotebookSession k cs acts nb →
      ValidNotebookSession k cs (acts ++ [a]) (editCellAndRecompute k nb a)

theorem runNotebookSession_eq_fromScratch (k : CellKernel) (cs : List ReactiveCell)
    (actions : List NotebookAction) :
    runNotebookSession k (evalFromScratch k cs) actions =
      evalFromScratch k (editTrace cs actions) := by
  induction actions generalizing cs with
  | nil => rfl
  | cons a rest ih =>
    simp only [runNotebookSession, incrementalRecompute_eq_fromScratch, editTrace, ih]

theorem editTrace_append (cs : List ReactiveCell) (as bs : List NotebookAction) :
    editTrace cs (as ++ bs) = editTrace (editTrace cs as) bs := by
  induction as generalizing cs with
  | nil => rfl
  | cons a rest ih => simpa only [List.cons_append, editTrace] using ih (applyEdit a cs)

theorem validSession_invariant (k : CellKernel) (cs : List ReactiveCell)
    (actions : List NotebookAction) (nb : ReactiveNotebook)
    (h : ValidNotebookSession k cs actions nb) :
    checkNotebookDag (editTrace cs actions) = true ∧
      nb = evalFromScratch k (editTrace cs actions) := by
  induction h with
  | start hc => exact ⟨hc, rfl⟩
  | step a _ ih =>
    simp only [editTrace_append, editTrace, checkNotebookDag_edit]
    exact ⟨ih.1, by rw [ih.2, incrementalRecompute_eq_fromScratch]⟩


theorem changed_subset (target : CellId) (changed : List SymbolName) (c : ReactiveCell) :
    ∀ s ∈ changed, s ∈ nextChanged target changed c := by
  intro s hs; unfold nextChanged; split
  · exact List.mem_append_right _ hs
  · exact hs

theorem coneScan_member (target : CellId) (cs : List ReactiveCell)
    (changed : List SymbolName) (i : CellId) (h : i ∈ coneScan target cs changed) :
    ∃ c ∈ cs, c.id = i := by
  induction cs generalizing changed with
  | nil => cases h
  | cons c cs ih =>
    simp only [coneScan] at h
    split at h
    · rcases List.mem_cons.mp h with he | ht
      · exact ⟨c, .head _, he.symm⟩
      · obtain ⟨u, hu, he⟩ := ih _ ht; exact ⟨u, .tail _ hu, he⟩
    · obtain ⟨u, hu, he⟩ := ih _ h; exact ⟨u, .tail _ hu, he⟩

theorem coneScan_root (target : CellId) (cs : List ReactiveCell)
    (changed : List SymbolName) (u : ReactiveCell) (hu : u ∈ cs) (he : u.id = target) :
    u.id ∈ coneScan target cs changed := by
  induction cs generalizing changed with
  | nil => cases hu
  | cons c cs ih =>
    rcases List.mem_cons.mp hu with rfl | ht
    · simp [coneScan, isDirty, he]
    · have hh := ih (nextChanged target changed c) ht
      unfold coneScan; split
      · exact .tail _ hh
      · exact hh

theorem coneScan_read (target : CellId) (cs : List ReactiveCell)
    (changed : List SymbolName) (u : ReactiveCell) (hu : u ∈ cs)
    (s : SymbolName) (hs : s ∈ changed) (hr : s ∈ u.reads) :
    u.id ∈ coneScan target cs changed := by
  induction cs generalizing changed with
  | nil => cases hu
  | cons c cs ih =>
    rcases List.mem_cons.mp hu with rfl | ht
    · have hd : isDirty target changed u = true := by
        simp only [isDirty, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨s, hr, hs⟩
      simp only [coneScan, hd, ite_true]; exact .head _
    · have hh := ih _ ht (changed_subset target changed c s hs)
      unfold coneScan; split
      · exact .tail _ hh
      · exact hh

/-- Forward closure uses the schedule's strict ordering, not a bounded reachability guess. -/
theorem coneScan_closed (target : CellId) (cs : List ReactiveCell)
    (hs : cs.Pairwise (fun a b => a.id < b.id)) (changed : List SymbolName)
    (p u : ReactiveCell) (hp : p ∈ cs) (hu : u ∈ cs)
    (he : dependency p u) (hlt : p.id < u.id)
    (hm : p.id ∈ coneScan target cs changed) : u.id ∈ coneScan target cs changed := by
  induction cs generalizing changed with
  | nil => cases hp
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hu with rfl | hut
    · rcases List.mem_cons.mp hp with rfl | hpt
      · exact False.elim (Nat.lt_irrefl _ hlt)
      · exact False.elim (Nat.lt_asymm hlt (hhead p hpt))
    · rcases List.mem_cons.mp hp with rfl | hpt
      · have hd : isDirty target changed p = true := by
          cases hh : isDirty target changed p with
          | true => rfl
          | false =>
            have hm' : p.id ∈ coneScan target cs (nextChanged target changed p) := by
              simpa only [coneScan, hh, Bool.false_eq_true, ite_false] using hm
            obtain ⟨v, hv, hvp⟩ := coneScan_member target cs _ _ hm'
            exact False.elim (Nat.ne_of_lt (hhead v hv) hvp.symm)
        obtain ⟨s, hsp, hsu⟩ := he
        have hc : s ∈ nextChanged target changed p := by simp [nextChanged, hd, hsp]
        have hh := coneScan_read target cs _ u hut s hc hsu
        simp only [coneScan, hd, ite_true]; exact .tail _ hh
      · have hm' : p.id ∈ coneScan target cs (nextChanged target changed c) := by
          unfold coneScan at hm; split at hm
          · exact (List.mem_cons.mp hm).resolve_left (Nat.ne_of_gt (hhead p hpt))
          · exact hm
        have hh := ih htail _ hpt hut hm'
        unfold coneScan; split
        · exact .tail _ hh
        · exact hh

/-- Minimality: every dependency-closed set containing the edited cell contains the sweep. -/
theorem coneScan_least (whole cs : List ReactiveCell) (target : CellId)
    (P : CellId → Prop) (hsub : ∀ c ∈ cs, c ∈ whole)
    (hroot : ∀ c ∈ whole, c.id = target → P c.id)
    (hclose : ∀ p ∈ whole, ∀ u ∈ whole, dependency p u → P p.id → P u.id)
    (changed : List SymbolName)
    (hchanged : ∀ s ∈ changed, ∃ p ∈ whole, P p.id ∧ s ∈ p.defs)
    (i : CellId) (hi : i ∈ coneScan target cs changed) : P i := by
  induction cs generalizing changed with
  | nil => cases hi
  | cons c cs ih =>
    have hc := hsub c (.head _)
    have htail : ∀ d ∈ cs, d ∈ whole := fun d hd => hsub d (.tail _ hd)
    by_cases hd : isDirty target changed c = true
    · have hpc : P c.id := by
        simp only [isDirty, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hd
        rcases hd with hr | ⟨s, hs, hm⟩
        · exact hroot c hc hr
        · obtain ⟨p, hp, hpp, hsp⟩ := hchanged s hm
          exact hclose p hp c hc ⟨s, hsp, hs⟩ hpp
      have hnext : ∀ s ∈ nextChanged target changed c,
          ∃ p ∈ whole, P p.id ∧ s ∈ p.defs := by
        intro s hs
        simp only [nextChanged, hd, ite_true, List.mem_append] at hs
        rcases hs with hx | hx
        · exact ⟨c, hc, hpc, hx⟩
        · exact hchanged s hx
      simp only [coneScan, hd, ite_true, List.mem_cons] at hi
      rcases hi with rfl | ht
      · exact hpc
      · exact ih htail _ hnext ht
    · have hf : isDirty target changed c = false := Bool.eq_false_iff.mpr hd
      simp only [coneScan, hf, Bool.false_eq_true, ite_false, nextChanged] at hi
      exact ih htail changed hchanged hi

def Downstream (cs : List ReactiveCell) (target : CellId) (u : ReactiveCell) : Prop :=
  u.id = target ∨ ∃ p ∈ cs, p.id = target ∧ DependencyPath cs p u

theorem id_injective (cs : List ReactiveCell) (h : (cs.map ReactiveCell.id).Nodup)
    (p u : ReactiveCell) (hp : p ∈ cs) (hu : u ∈ cs) (he : p.id = u.id) : p = u := by
  induction cs with
  | nil => cases hp
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hp with rfl | hpt
    · rcases List.mem_cons.mp hu with rfl | hut
      · rfl
      · exact False.elim (h.1 (List.mem_map.mpr ⟨u, hut, he.symm⟩))
    · rcases List.mem_cons.mp hu with rfl | hut
      · exact False.elim (h.1 (List.mem_map.mpr ⟨p, hpt, he⟩))
      · exact ih h.2 hpt hut

/-- Exact reflexive-transitive downstream cone, for every admitted notebook and every cell. -/
theorem dirtyCone_exact (cs : List ReactiveCell) (target : CellId)
    (h : checkNotebookDag cs = true) (u : ReactiveCell) (hu : u ∈ cs) :
    u.id ∈ dirtyCone cs target ↔ Downstream cs target u := by
  have hc := h
  simp only [checkNotebookDag, scheduleCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hc
  constructor
  · intro hm
    have hi : ∃ v ∈ cs, v.id = u.id ∧ Downstream cs target v := by
      apply coneScan_least cs cs target
        (fun i => ∃ v ∈ cs, v.id = i ∧ Downstream cs target v)
        (fun _ hm => hm) ?_ ?_ [] (by simp) u.id hm
      · intro c hcm he; exact ⟨c, hcm, rfl, Or.inl he⟩
      · intro p hp v hv he ⟨q, hq, hqp, hqd⟩
        have eqp : q = p := by
          have hn := (checkNotebookDag_acyclic_sound cs h).1
          exact id_injective cs hn q p hq hp hqp
        subst q
        refine ⟨v, hv, rfl, Or.inr ?_⟩
        rcases hqd with ht | ⟨r, hr, ht, path⟩
        · exact ⟨p, hp, ht, .edge hp hv he⟩
        · exact ⟨r, hr, ht, .trans path (.edge hp hv he)⟩
    obtain ⟨v, hv, he, hd⟩ := hi
    have eqv : v = u := id_injective cs
      (checkNotebookDag_acyclic_sound cs h).1 v u hv hu he
    simpa only [eqv] using hd
  · intro hd
    rcases hd with ht | ⟨p, hp, ht, path⟩
    · exact coneScan_root target cs [] u hu ht
    · have root := coneScan_root target cs [] p hp ht
      have reach : ∀ {p v}, DependencyPath cs p v →
          p.id ∈ dirtyCone cs target → v.id ∈ dirtyCone cs target := by
        intro p v path
        induction path with
        | edge hp hv he =>
          exact coneScan_closed target cs hc.2.1 [] _ _ hp hv he (hc.2.2 _ hp _ hv he)
        | trans _ _ ih₁ ih₂ => exact fun hh => ih₂ (ih₁ hh)
      exact reach path root


/-! Executable refinement. Balanced symbol tables avoid scanning all prior definitions or dirty
symbols on each read. Lists specify semantics; the compiled entry points use these tree sweeps.
Each unchanged cache is copied as one object and never passed to the kernel. -/
abbrev SymbolTable := Std.TreeMap SymbolName Int
abbrev ChangedSet := Std.TreeSet SymbolName

def tableEnvironment (t : SymbolTable) : Environment := fun s => t.getD s 0

def publishTable : List SymbolName → List Int → SymbolTable → SymbolTable
  | [], _, t => t
  | s :: ss, vs, t => (publishTable ss vs.tail t).insert s (vs.headD 0)

theorem publishTable_refines (ss : List SymbolName) (vs : List Int) (t : SymbolTable)
    (s : SymbolName) :
    (publishTable ss vs t).getD s 0 =
      if s ∈ ss then vs[ss.idxOf s]?.getD 0 else t.getD s 0 := by
  induction ss generalizing vs with
  | nil => simp [publishTable]
  | cons d ds ih =>
    by_cases he : s = d
    · subst s
      cases vs <;> simp [publishTable]
    · simp [publishTable, Std.TreeMap.getD_insert, Ne.symm he,
        he, List.idxOf_cons, ih, List.getElem?_tail]

theorem publishTable_cell (c : ReactiveCell) (r : CellResult) (t : SymbolTable) :
    tableEnvironment (publishTable c.defs r.values t) = publish c r (tableEnvironment t) := by
  funext s; exact publishTable_refines c.defs r.values t s

def dirtyTree (target : CellId) (changed : ChangedSet) (c : ReactiveCell) : Bool :=
  decide (c.id = target) || c.reads.any changed.contains

def nextTree (target : CellId) (changed : ChangedSet) (c : ReactiveCell) : ChangedSet :=
  if dirtyTree target changed c then changed.insertMany c.defs else changed

def SetRepresents (t : ChangedSet) (xs : List SymbolName) : Prop :=
  ∀ s, t.contains s = decide (s ∈ xs)

theorem dirtyTree_refines (target : CellId) (t : ChangedSet) (xs : List SymbolName)
    (h : SetRepresents t xs) (c : ReactiveCell) : dirtyTree target t c = isDirty target xs c := by
  change ∀ s, _ at h
  have hh : t.contains = fun s => decide (s ∈ xs) := funext h
  simp only [dirtyTree, isDirty, hh]

theorem nextTree_refines (target : CellId) (t : ChangedSet) (xs : List SymbolName)
    (h : SetRepresents t xs) (c : ReactiveCell) :
    SetRepresents (nextTree target t c) (nextChanged target xs c) := by
  intro s
  simp only [nextTree, nextChanged, dirtyTree_refines target t xs h]
  split
  · simp [h s, List.mem_append, Bool.or_comm]
  · exact h s

def coneTree (target : CellId) : List ReactiveCell → ChangedSet → List CellId
  | [], _ => []
  | c :: cs, changed =>
    let rest := coneTree target cs (nextTree target changed c)
    if dirtyTree target changed c then c.id :: rest else rest

theorem coneTree_refines (target : CellId) (cs : List ReactiveCell)
    (t : ChangedSet) (xs : List SymbolName) (h : SetRepresents t xs) :
    coneTree target cs t = coneScan target cs xs := by
  induction cs generalizing t xs with
  | nil => rfl
  | cons c cs ih =>
    simp only [coneTree, coneScan, dirtyTree_refines target t xs h,
      ih _ _ (nextTree_refines target t xs h c)]

def dirtyConeExec (cs : Array ReactiveCell) (target : CellId) : Array CellId :=
  (coneTree target cs.toList ∅).toArray

theorem dirtyCone_exec_eq (cs : List ReactiveCell) (target : CellId) :
    (dirtyConeExec cs.toArray target).toList = dirtyCone cs target := by
  apply coneTree_refines target cs ∅ []
  intro s; simp

def dirtyConeFast (cs : List ReactiveCell) (target : CellId) : List CellId :=
  (dirtyConeExec cs.toArray target).toList
@[csimp] theorem dirtyCone_eq_fast : dirtyCone = dirtyConeFast := by
  funext cs target; exact (dirtyCone_exec_eq cs target).symm

def evalTable (k : CellKernel) : List ReactiveCell → SymbolTable → List CachedCell
  | [], _ => []
  | c :: cs, env =>
    let r := evalCell k c (tableEnvironment env)
    ⟨c, r⟩ :: evalTable k cs (publishTable c.defs r.values env)

theorem evalTable_refines (k : CellKernel) (cs : List ReactiveCell) (env : SymbolTable) :
    evalTable k cs env = evalSchedule k cs (tableEnvironment env) := by
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih => simp only [evalTable, evalSchedule, ih, publishTable_cell]

def evalFromScratchExec (k : CellKernel) (cs : List ReactiveCell) : ReactiveNotebook :=
  ⟨evalTable k cs ∅⟩
@[csimp] theorem evalFromScratch_eq_exec : evalFromScratch = evalFromScratchExec := by
  funext k cs
  unfold evalFromScratch evalFromScratchExec
  rw [evalTable_refines]
  congr 2

def recomputeTable (k : CellKernel) (a : NotebookAction) :
    List CachedCell → SymbolTable → ChangedSet → List CachedCell
  | [], _, _ => []
  | old :: cs, env, changed =>
    let c := editCell a old.cell
    let r := reuseOrEval k (dirtyTree a.target changed c) old.result c (tableEnvironment env)
    ⟨c, r⟩ :: recomputeTable k a cs (publishTable c.defs r.values env)
      (nextTree a.target changed c)

theorem recomputeTable_refines (k : CellKernel) (a : NotebookAction) (cs : List CachedCell)
    (env : SymbolTable) (t : ChangedSet) (xs : List SymbolName) (h : SetRepresents t xs) :
    recomputeTable k a cs env t = recompute k a cs (tableEnvironment env) xs := by
  induction cs generalizing env t xs with
  | nil => rfl
  | cons c cs ih =>
    simp only [recomputeTable, recompute, dirtyTree_refines a.target t xs h,
      ih _ _ _ (nextTree_refines a.target t xs h (editCell a c.cell)), publishTable_cell]

def editCellAndRecomputeExec (k : CellKernel) (nb : ReactiveNotebook) (a : NotebookAction) :
    ReactiveNotebook := ⟨recomputeTable k a nb.cells ∅ ∅⟩
@[csimp] theorem editCellAndRecompute_eq_exec :
    editCellAndRecompute = editCellAndRecomputeExec := by
  funext k nb a
  unfold editCellAndRecompute editCellAndRecomputeExec
  rw [recomputeTable_refines k a nb.cells ∅ ∅ [] (by intro s; simp)]
  congr 2


/-- Pins carry values, not merely the presence of a symbol. -/
def cellPins (c : ReactiveCell) (env : Environment) : CellPins :=
  ⟨c.reads.map (fun s => ⟨s, some (env s)⟩)⟩
def pinWorld (env : Environment) : Obend.Slot.SupportSheaf.KeyedWorld SymbolName Int :=
  ⟨fun s => some (env s)⟩

theorem cellPins_inhabited (c : ReactiveCell) (env : Environment) :
    Obend.Slot.SupportSheaf.SupportSheaf.usable (pinWorld env) (cellPins c env) = true := by
  simp [Obend.Slot.SupportSheaf.SupportSheaf.usable,
    cellPins, pinWorld, List.all_map, List.all_eq_true, Obend.Slot.SupportSheaf.keyedHolds]

/-- The shared sheaf's pin validity entails equality of both the value and the receipt. -/
theorem supportSheaf_receipt_reuse (k : CellKernel) (c : ReactiveCell) (old new : Environment)
    (h : Obend.Slot.SupportSheaf.SupportSheaf.usable (pinWorld new) (cellPins c old) = true) :
    evalCell k c new = evalCell k c old := by
  apply evalCell_frame
  simpa [Obend.Slot.SupportSheaf.SupportSheaf.usable, cellSupportSheaf,
    cellPins, pinWorld, List.all_map, List.all_eq_true, Obend.Slot.SupportSheaf.keyedHolds] using h

/-- Array input addressing is constant time per instruction. The stack has constant-time pops. -/
def arithmeticStepExec (inputs : Array Int) (stack : List Int) (i : Instruction) : List Int :=
  let a := stack.headD 0
  let b := stack.tail.headD 0
  match i.op with
  | .literal => i.arg :: stack
  | .input => inputs[i.arg.toNat]?.getD 0 :: stack
  | .add => (b + a) :: stack.drop 2
  | .sub => (b - a) :: stack.drop 2
  | .mul => (b * a) :: stack.drop 2
  | .div => (b / a) :: stack.drop 2

theorem arithmeticStep_exec_eq (inputs : List Int) (stack : List Int) (i : Instruction) :
    arithmeticStepExec inputs.toArray stack i = arithmeticStep inputs stack i := by
  cases i with
  | mk op arg => cases op <;> simp [arithmeticStepExec, arithmeticStep]

def arithmeticRunExec (_kind : ProjectionKind) (code : List Instruction) (inputs : List Int) : Int :=
  let values := inputs.toArray
  (code.toArray.foldl (arithmeticStepExec values) []).headD 0

@[csimp] theorem arithmeticRun_eq_exec : arithmeticRun = arithmeticRunExec := by
  funext kind code inputs
  have h : arithmeticStepExec inputs.toArray = arithmeticStep inputs := by
    funext stack i; exact arithmeticStep_exec_eq inputs stack i
  simp [arithmeticRun, arithmeticRunExec, h]

/-- Each output body is indexed in an array, avoiding repeated scans of a long cell's source. -/
def evalCellExec (k : CellKernel) (c : ReactiveCell) (env : Environment) : CellResult :=
  let inputs := restrict c env
  let bodies := c.body.toArray
  let values := c.defs.zipIdx.map fun (_, i) => k.run c.kind (bodies[i]?.getD []) inputs
  ⟨values, k.hash (cellReceiptPreimage c inputs values)⟩
@[csimp] theorem evalCell_eq_exec : evalCell = evalCellExec := by
  funext k c env; simp [evalCell, evalCellExec]

/-- Operational call trace: a clean step has no kernel evaluation premise or event. -/
inductive RecomputeExecution (k : CellKernel) (a : NotebookAction) :
    List CachedCell → Environment → List SymbolName → List CachedCell → List CellId → Prop where
  | done (env changed) : RecomputeExecution k a [] env changed [] []
  | clean (old : CachedCell) (cs env changed out calls)
      (hc : isDirty a.target changed old.cell = false)
      (rest : RecomputeExecution k a cs (publish old.cell old.result env) changed out calls) :
      RecomputeExecution k a (old :: cs) env changed (old :: out) calls
  | dirty (old : CachedCell) (cs env changed out calls)
      (hc : isDirty a.target changed old.cell = true)
      (rest : RecomputeExecution k a cs
        (publish (editCell a old.cell) (evalCell k (editCell a old.cell) env) env)
        (old.cell.defs ++ changed) out calls) :
      RecomputeExecution k a (old :: cs) env changed
        (⟨editCell a old.cell, evalCell k (editCell a old.cell) env⟩ :: out)
        (old.cell.id :: calls)

theorem recompute_execution (k : CellKernel) (a : NotebookAction) (cs : List CachedCell)
    (env : Environment) (changed : List SymbolName) :
    RecomputeExecution k a cs env changed (recompute k a cs env changed)
      (coneScan a.target (cs.map CachedCell.cell) changed) := by
  induction cs generalizing env changed with
  | nil => exact .done env changed
  | cons old cs ih =>
    by_cases hd : isDirty a.target changed old.cell = true
    · simp only [recompute, dirty_edit, reuseOrEval, hd, ite_true,
        nextChanged, editCell_defs, List.map_cons, coneScan]
      exact .dirty old cs env changed _ _ hd (ih _ _)
    · have hf : isDirty a.target changed old.cell = false := Bool.eq_false_iff.mpr hd
      have he : editCell a old.cell = old.cell := by
        simp [editCell, (clean_support _ _ _ hf).1]
      simp only [recompute, he, hf, reuseOrEval, Bool.false_eq_true, ite_false,
        nextChanged, List.map_cons, coneScan]
      exact .clean old cs env changed _ _ hf (ih _ _)

theorem untouchedCells_zero_kernel_calls (k : CellKernel) (nb : ReactiveNotebook)
    (a : NotebookAction) (i : CellId)
    (h : i ∉ dirtyCone (nb.cells.map CachedCell.cell) a.target) :
    ∃ calls, RecomputeExecution k a nb.cells (fun _ => 0) []
      (editCellAndRecompute k nb a).cells calls ∧ i ∉ calls := by
  exact ⟨dirtyCone (nb.cells.map CachedCell.cell) a.target, recompute_execution k a nb.cells _ [], h⟩

/-- Admission is separate from pure evaluation and never runs a kernel on a refused graph. -/
def admitNotebook (k : CellKernel) (cs : List ReactiveCell) : Except String ReactiveNotebook :=
  if checkNotebookDag cs then .ok (evalFromScratch k cs)
  else .error "duplicate identity/export or invalid topological schedule"

theorem admitNotebook_complete (k : CellKernel) (cs : List ReactiveCell)
    (h : checkNotebookDag cs = true) : admitNotebook k cs = .ok (evalFromScratch k cs) := by
  simp [admitNotebook, h]


/-! Admission also has a balanced-table implementation. A producer table stores one plus the
maximum producer rank for each symbol. This catches every backward edge, including self edges,
without a quadratic all-pairs scan. -/
abbrev ProducerTable := Std.TreeMap SymbolName Nat

def addProducers : List SymbolName → CellId → ProducerTable → ProducerTable
  | [], _, t => t
  | s :: ss, rank, t => addProducers ss rank (t.insert s (max (rank + 1) (t.getD s 0)))

theorem addProducers_bound (ss : List SymbolName) (rank : CellId) (t : ProducerTable)
    (s : SymbolName) (bound : Nat) :
    (addProducers ss rank t).getD s 0 ≤ bound ↔
      t.getD s 0 ≤ bound ∧ (s ∈ ss → rank < bound) := by
  induction ss generalizing t with
  | nil => simp [addProducers]
  | cons d ds ih =>
    rw [addProducers, ih, Std.TreeMap.getD_insert]
    by_cases he : d = s
    · subst d
      simp [Nat.max_le, Nat.succ_le_iff, and_assoc, and_comm]
      exact fun h _ _ => h
    · simp [he, Ne.symm he]

def producerTable : List ReactiveCell → ProducerTable
  | [] => ∅
  | c :: cs => addProducers c.defs c.id (producerTable cs)

theorem producerTable_bound (cs : List ReactiveCell) (s : SymbolName) (bound : Nat) :
    (producerTable cs).getD s 0 ≤ bound ↔ ∀ c ∈ cs, s ∈ c.defs → c.id < bound := by
  induction cs with
  | nil => simp [producerTable]
  | cons c cs ih => simp [producerTable, addProducers_bound, ih, and_comm]

def edgesTree (cs : List ReactiveCell) : Bool :=
  let producers := producerTable cs
  cs.all fun c => c.reads.all fun s => decide (producers.getD s 0 ≤ c.id)

theorem edgesTree_refines (cs : List ReactiveCell) :
    edgesTree cs = cs.all (fun p => cs.all (fun u => decide (dependency p u → p.id < u.id))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgesTree, List.all_eq_true, decide_eq_true_eq, producerTable_bound]
  constructor
  · intro h p hp u hu ⟨s, hsp, hsu⟩; exact h u hu s hsu p hp hsp
  · intro h u hu s hsu p hp hsp; exact h p hp u hu ⟨s, hsp, hsu⟩

def increasing : List ReactiveCell → Bool
  | [] => true
  | c :: cs => (match cs with | [] => true | d :: _ => decide (c.id < d.id)) && increasing cs

theorem increasing_refines (cs : List ReactiveCell) :
    increasing cs = true ↔ cs.Pairwise (fun a b => a.id < b.id) := by
  induction cs with
  | nil => simp [increasing]
  | cons c cs ih =>
    cases cs with
    | nil => simp [increasing]
    | cons d ds =>
      change (decide (c.id < d.id) && increasing (d :: ds) = true) ↔ _
      rw [Bool.and_eq_true, decide_eq_true_eq, List.pairwise_cons]
      constructor
      · intro h; refine ⟨?_, ih.mp h.2⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hm
        · exact h.1
        · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp (ih.mp h.2)).1 u hm)
      · intro h; exact ⟨h.1 d (.head _), ih.mpr h.2⟩

def uniqueTree : List SymbolName → ChangedSet → Bool
  | [], _ => true
  | s :: ss, t => !t.contains s && uniqueTree ss (t.insert s)

theorem uniqueTree_refines (ss : List SymbolName) (t : ChangedSet) :
    uniqueTree ss t = true ↔ ss.Nodup ∧ ∀ s ∈ ss, t.contains s = false := by
  induction ss generalizing t with
  | nil => simp [uniqueTree]
  | cons s ss ih =>
    simp only [uniqueTree, Bool.and_eq_true, Bool.not_eq_true', ih,
      List.nodup_cons, List.forall_mem_cons]
    simp only [Std.TreeSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · intro ⟨hs, hn, ht⟩
      refine ⟨⟨?_, hn⟩, hs, ?_⟩
      · intro hm; have := (ht s hm).1; simp at this
      · intro v hv; exact (ht v hv).2
    · intro ⟨⟨hn, hnd⟩, hs, ht⟩
      refine ⟨hs, hnd, ?_⟩
      intro v hv
      exact ⟨by intro he; have hev : s = v := Std.LawfulEqOrd.eq_of_compare he
                subst v; exact hn hv, ht v hv⟩

def checkNotebookDagExec (cs : List ReactiveCell) : Bool :=
  uniqueTree (cs.flatMap ReactiveCell.defs) ∅ && increasing cs && edgesTree cs

@[csimp] theorem checkNotebookDag_eq_exec : checkNotebookDag = checkNotebookDagExec := by
  funext cs
  apply Bool.eq_iff_iff.mpr
  simp only [checkNotebookDag, uniqueExports, scheduleCheck, checkNotebookDagExec,
    Bool.and_eq_true, decide_eq_true_eq, uniqueTree_refines, increasing_refines, edgesTree_refines]
  simp [and_assoc]


/-- Lookup by stable identity, shared by raw and recomputed cache views. -/
def cacheLookup : List CachedCell → CellId → Option CachedCell
  | [], _ => none
  | c :: cs, i => if c.cell.id = i then some c else cacheLookup cs i

theorem recompute_lookup_untouched (k : CellKernel) (a : NotebookAction) (cs : List CachedCell)
    (env : Environment) (changed : List SymbolName) (i : CellId)
    (h : i ∉ coneScan a.target (cs.map CachedCell.cell) changed) :
    cacheLookup (recompute k a cs env changed) i = cacheLookup cs i := by
  induction cs generalizing env changed with
  | nil => rfl
  | cons old cs ih =>
    by_cases hd : isDirty a.target changed old.cell = true
    · have hn : i ≠ old.cell.id ∧
          i ∉ coneScan a.target (cs.map CachedCell.cell) (old.cell.defs ++ changed) := by
        simpa only [List.map_cons, coneScan, hd, ite_true, nextChanged,
          List.mem_cons, not_or] using h
      simp only [recompute, dirty_edit, hd, reuseOrEval, ite_true, cacheLookup,
        editCell_id, Ne.symm hn.1, ite_false, nextChanged, editCell_defs]
      exact ih _ _ hn.2
    · have hf : isDirty a.target changed old.cell = false := Bool.eq_false_iff.mpr hd
      have he : editCell a old.cell = old.cell := by simp [editCell, (clean_support _ _ _ hf).1]
      have hn : i ∉ coneScan a.target (cs.map CachedCell.cell) changed := by
        simpa only [List.map_cons, coneScan, hf, Bool.false_eq_true, ite_false, nextChanged] using h
      simp only [recompute, he, hf, reuseOrEval, Bool.false_eq_true, ite_false, nextChanged,
        cacheLookup]
      split
      · rfl
      · exact ih _ _ hn

theorem untouchedCells_receipt_lookup (k : CellKernel) (nb : ReactiveNotebook)
    (a : NotebookAction) (i : CellId)
    (h : i ∉ dirtyCone (applyEdit a (nb.cells.map CachedCell.cell)) a.target) :
    (cacheLookup (editCellAndRecompute k nb a).cells i).map (fun c => c.result) =
      (cacheLookup nb.cells i).map (fun c => c.result) := by
  rw [show (editCellAndRecompute k nb a).cells = recompute k a nb.cells (fun _ => 0) [] from rfl]
  rw [recompute_lookup_untouched k a nb.cells _ [] i]
  simpa only [dirtyCone, coneScan_edit] using h

/-! The part of a notebook a viewer holds: the cells whose ids are in `V`, in schedule order. An
edit to a visible cell, when no redacted cell reads a visible one (`frustumClosed`), dirties the
same cells with or without the redacted ones (`dirtyCone_snip`) and leaves every redacted cached
cell as it was (`redact_schedule_edit`). `Vault.TransclusionAndMirror` seals the boundary. -/

/-- The cells of a schedule a viewer holds. -/
def snipCells (V : List CellId) (cs : List ReactiveCell) : List ReactiveCell :=
  cs.filter fun c => V.contains c.id

/-- Removing cells from an admitted schedule cannot introduce a cycle or duplicate export. -/
theorem checkNotebookDag_snip (V : List CellId) (cs : List ReactiveCell)
    (h : checkNotebookDag cs = true) : checkNotebookDag (snipCells V cs) = true := by
  have hc := h
  simp only [checkNotebookDag, uniqueExports, scheduleCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hc
  have sub : ((snipCells V cs).flatMap ReactiveCell.defs).Sublist (cs.flatMap ReactiveCell.defs) := by
    clear h hc
    induction cs with
    | nil => exact .refl _
    | cons c cs ih =>
      unfold snipCells at *
      rw [List.filter_cons]
      split
      · exact List.Sublist.append (.refl _) ih
      · exact ih.trans (List.sublist_append_right _ _)
  exact checkNotebookDag_complete _ (List.Pairwise.filter _ hc.2.1) (sub.nodup hc.1)
    (fun p hp u hu => hc.2.2 p (List.mem_filter.mp hp).1 u (List.mem_filter.mp hu).1)

/-- The cached cells a viewer holds. -/
def snipCache (V : List CellId) (xs : List CachedCell) : List CachedCell :=
  xs.filter fun x => V.contains x.cell.id

/-- The cached cells a viewer does not hold. -/
def redactCache (V : List CellId) (xs : List CachedCell) : List CachedCell :=
  xs.filter fun x => !V.contains x.cell.id

/-- No redacted cell reads a symbol a visible cell exports: the visible set is closed downstream. -/
def frustumClosed (V : List CellId) (cs : List ReactiveCell) : Bool :=
  decide (∀ p ∈ cs, p.id ∈ V → ∀ u ∈ cs, dependency p u → u.id ∈ V)

theorem evalSchedule_cells (k : CellKernel) (cs : List ReactiveCell) (env : Environment) :
    (evalSchedule k cs env).map CachedCell.cell = cs := by
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih => simp only [evalSchedule, List.map_cons, ih]

theorem evalSchedule_cell_mem {k : CellKernel} {cs : List ReactiveCell} {env : Environment}
    {x : CachedCell} (hx : x ∈ evalSchedule k cs env) : x.cell ∈ cs := by
  have hm : x.cell ∈ (evalSchedule k cs env).map CachedCell.cell := List.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [evalSchedule_cells] at hm

theorem redactCache_cell_mem {k : CellKernel} {V : List CellId} {cs : List ReactiveCell}
    {env : Environment} {x : CachedCell}
    (hx : x ∈ redactCache V (evalSchedule k cs env)) : x.cell ∈ cs :=
  evalSchedule_cell_mem (List.mem_filter.mp hx).1

theorem cacheLookup_snipCache (V : List CellId) {i : CellId} (hi : i ∈ V) (xs : List CachedCell) :
    cacheLookup (snipCache V xs) i = cacheLookup xs i := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold snipCache at ih ⊢
    rw [List.filter_cons]
    by_cases hx : x.cell.id = i
    · have hc : V.contains x.cell.id = true := by rw [hx]; simpa using hi
      simp only [hc, ↓reduceIte]
      simp only [cacheLookup, hx, ↓reduceIte]
    · split
      · simp only [cacheLookup, hx, ↓reduceIte]
        exact ih
      · simp only [cacheLookup, hx, ↓reduceIte]
        exact ih

theorem coneScan_snip (V : List CellId) (target : CellId) (ht : target ∈ V)
    (cs : List ReactiveCell) (changed : List SymbolName)
    (hcl : ∀ p ∈ cs, p.id ∈ V → ∀ u ∈ cs, dependency p u → u.id ∈ V)
    (hred : ∀ u ∈ cs, u.id ∉ V → ∀ s ∈ u.reads, s ∉ changed) :
    coneScan target (snipCells V cs) changed = coneScan target cs changed := by
  induction cs generalizing changed with
  | nil => rfl
  | cons c cs ih =>
    have hcl' : ∀ p ∈ cs, p.id ∈ V → ∀ u ∈ cs, dependency p u → u.id ∈ V :=
      fun p hp hv u hu => hcl p (.tail _ hp) hv u (.tail _ hu)
    by_cases hv : c.id ∈ V
    · have hs : snipCells V (c :: cs) = c :: snipCells V cs := by simp [snipCells, hv]
      have hnext : ∀ u ∈ cs, u.id ∉ V → ∀ s ∈ u.reads, s ∉ nextChanged target changed c := by
        intro u hu huv s hsu hmem
        unfold nextChanged at hmem
        split at hmem
        · rcases List.mem_append.mp hmem with h | h
          · exact huv (hcl c (.head _) hv u (.tail _ hu) ⟨s, h, hsu⟩)
          · exact hred u (.tail _ hu) huv s hsu h
        · exact hred u (.tail _ hu) huv s hsu hmem
      rw [hs]
      simp only [coneScan, ih _ hcl' hnext]
    · have hs : snipCells V (c :: cs) = snipCells V cs := by simp [snipCells, hv]
      have hd : isDirty target changed c = false := by
        simp only [isDirty, Bool.or_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false]
        exact ⟨fun h => hv (by rw [h]; exact ht),
          fun s hsr => by simpa using hred c (.head _) hv s hsr⟩
      rw [hs, ih changed hcl' (fun u hu => hred u (.tail _ hu))]
      simp [coneScan, hd, nextChanged]

/-- **A visible edit has the same cone in the snipped notebook.** When the visible set is closed
downstream, the cells an edit to a visible cell dirties are the same list on both sides, and all of
them are visible. -/
theorem dirtyCone_snip (V : List CellId) (cs : List ReactiveCell) (target : CellId)
    (hclosed : frustumClosed V cs = true) (ht : target ∈ V) :
    dirtyCone (snipCells V cs) target = dirtyCone cs target ∧
    ∀ i ∈ dirtyCone cs target, i ∈ V := by
  have h : dirtyCone (snipCells V cs) target = dirtyCone cs target :=
    coneScan_snip V target ht cs [] (of_decide_eq_true hclosed) (fun _ _ _ _ _ => List.not_mem_nil)
  refine ⟨h, fun i hi => ?_⟩
  rw [← h] at hi
  obtain ⟨c, hc, rfl⟩ := coneScan_member target _ [] i hi
  simpa using (List.mem_filter.mp hc).2

theorem redact_schedule_edit (k : CellKernel) (V : List CellId) (a : NotebookAction)
    (ht : a.target ∈ V) (cs : List ReactiveCell) (e e' : Environment) (changed : List SymbolName)
    (hcl : ∀ p ∈ cs, p.id ∈ V → ∀ u ∈ cs, dependency p u → u.id ∈ V)
    (hred : ∀ u ∈ cs, u.id ∉ V → ∀ s ∈ u.reads, s ∉ changed)
    (hag : AgreeOutside changed e e') :
    redactCache V (evalSchedule k (applyEdit a cs) e') = redactCache V (evalSchedule k cs e) := by
  induction cs generalizing e e' changed with
  | nil => rfl
  | cons c cs ih =>
    have hcl' : ∀ p ∈ cs, p.id ∈ V → ∀ u ∈ cs, dependency p u → u.id ∈ V :=
      fun p hp hv u hu => hcl p (.tail _ hp) hv u (.tail _ hu)
    by_cases hv : c.id ∈ V
    · have h₁ : redactCache V (evalSchedule k (applyEdit a (c :: cs)) e') =
          redactCache V (evalSchedule k (applyEdit a cs)
            (publish (editCell a c) (evalCell k (editCell a c) e') e')) := by
        simp [redactCache, evalSchedule, applyEdit, hv]
      have h₂ : redactCache V (evalSchedule k (c :: cs) e) =
          redactCache V (evalSchedule k cs (publish c (evalCell k c e) e)) := by
        simp [redactCache, evalSchedule, hv]
      rw [h₁, h₂]
      refine ih _ _ (c.defs ++ changed) hcl' ?_
        (publish_frame c (editCell a c) _ _ e e' (editCell_defs a c).symm changed hag)
      intro u hu huv s hsu hmem
      rcases List.mem_append.mp hmem with h | h
      · exact huv (hcl c (.head _) hv u (.tail _ hu) ⟨s, h, hsu⟩)
      · exact hred u (.tail _ hu) huv s hsu h
    · have hne : c.id ≠ a.target := fun h => hv (by rw [h]; exact ht)
      have hedit : editCell a c = c := by simp [editCell, hne]
      have hr : evalCell k c e = evalCell k c e' :=
        evalCell_frame k c e e' (fun s hs => hag s (hred c (.head _) hv s hs))
      have h₁ : redactCache V (evalSchedule k (applyEdit a (c :: cs)) e') =
          ⟨c, evalCell k c e'⟩ :: redactCache V (evalSchedule k (applyEdit a cs)
            (publish c (evalCell k c e') e')) := by
        simp [redactCache, evalSchedule, applyEdit, hedit, hv]
      have h₂ : redactCache V (evalSchedule k (c :: cs) e) =
          ⟨c, evalCell k c e'⟩ ::
            redactCache V (evalSchedule k cs (publish c (evalCell k c e') e)) := by
        simp [redactCache, evalSchedule, hr, hv]
      rw [h₁, h₂]
      congr 1
      exact ih _ _ changed hcl' (fun u hu => hred u (.tail _ hu))
        (publish_same c _ e e' changed hag)

end Obend.Doc.Reactive
