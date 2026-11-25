module
public import Obend.Doc.Patch
public import Obend.Core.HeapImage
public import Obend.Core.Bidirectional
public import Obend.Core.Code
public import Obend.Core.Proofs.Preservation.Cases.Activities
public import Obend.Codec.Hex
import all Obend.Core.Code
import all Obend.Codec.Hex

public section
namespace Obend.Doc.LiveObject
open Obend.Core.Term Obend.Core.Ty Obend.Core.Check Obend.Core.Machine
open Obend.Core.MachineTyping Obend.Core.HeapImage Obend.Codec.Hex
open Obend.Core.Bidirectional Obend.Core.Data Obend.Core.Code Obend.Core.Invariant
set_option autoImplicit false

/-! ## 1. Zero-`List UInt8` `ByteArray` Hex Wire Codec -/

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

private theorem validUTF8_push_nibble {dst : ByteArray} (h : dst.IsValidUTF8) (n : Nat) :
    (dst.push (hexNibbleByte n)).IsValidUTF8 := by
  obtain ⟨cs, rfl⟩ := h
  refine .intro (cs ++ [hexNibbleChar n]) ?_
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [List.utf8Encode_append, ByteArray.toList_data_append, nibble_utf8]
  cases cs.utf8Encode
  simp [ByteArray.push]

private theorem byteArrayToHexAsciiLoop_validUTF8 (src : ByteArray) :
    ∀ (fuel i : Nat) (dst : ByteArray), dst.IsValidUTF8 →
      (byteArrayToHexAsciiLoop src fuel i dst).IsValidUTF8
  | 0, _, _, h => h
  | fuel + 1, i, dst, h => by
    unfold byteArrayToHexAsciiLoop
    split
    · exact byteArrayToHexAsciiLoop_validUTF8 src fuel (i + 1) _
        (validUTF8_push_nibble (validUTF8_push_nibble h _) _)
    · exact h

private theorem byteArrayToHexAscii_validUTF8 (bs : ByteArray) :
    (byteArrayToHexAscii bs).IsValidUTF8 :=
  byteArrayToHexAsciiLoop_validUTF8 bs bs.size 0 _ (.intro [] rfl)

/-- Encode raw bytes directly to lowercase hex UTF-8 `String` via `byteArrayToHexAscii`
(`0` intermediate `List UInt8` or `List Char` allocations). -/
def encodeImageHex (bs : ByteArray) : String :=
  String.fromUTF8 (byteArrayToHexAscii bs) (byteArrayToHexAscii_validUTF8 bs)

/-- Decode a strict lowercase hex UTF-8 string directly into `ByteArray` via `hexByteArrayStrict?`
(`0` intermediate `List UInt8` or `List Char` allocations). -/
def decodeImageHex (hex : String) : Option ByteArray :=
  hexByteArrayStrict? hex.toUTF8

@[simp] theorem decodeImageHex_encode (bs : ByteArray) :
    decodeImageHex (encodeImageHex bs) = some bs := by
  unfold decodeImageHex encodeImageHex
  have hutf : (String.fromUTF8 (byteArrayToHexAscii bs) (byteArrayToHexAscii_validUTF8 bs)).toUTF8 =
      byteArrayToHexAscii bs := by
    rw [String.toUTF8_eq_toByteArray]
    rfl
  rw [hutf]
  have read := hexByteArrayStrict?_toList (byteArrayToHexAscii bs)
  rw [byteArrayToHexAscii_toList, hexAsciiToBytes?_bytesToHexAscii] at read
  cases h : hexByteArrayStrict? (byteArrayToHexAscii bs) with
  | none => rw [h] at read; cases read
  | some b =>
    rw [h] at read
    exact congrArg some (ByteArray.ext (Array.toList_inj.mp (Option.some.inj read)))

/-- Encode a `Core.Machine.State` directly to strict lowercase hex over `ByteArray`. -/
def encodeImageText (s : State) : String :=
  encodeImageHex (encodeHeapImage s)

/-- Decode the strict lowercase wire spelling directly from UTF-8 `ByteArray` into `State`. -/
def decodeImageText (hex : String) : Option State :=
  (decodeImageHex hex).bind decodeHeapImage

@[simp] theorem decodeImageText_encode (s : State) :
    decodeImageText (encodeImageText s) = some s := by
  simp [decodeImageText, encodeImageText, decodeHeapImage_encodeHeapImage]

/-! ## 2. Executable Machine-State Well-Formedness & Typing Certificate Verifier -/

mutual
private def checkScoped (n : Nat) : Term → Bool
  | .hole _ σ => checkScopedList n σ
  | .bound i => decide (i < n)
  | .lam body => checkScoped (n + 1) body
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b
  | .binary _ a b | .split a _ b => checkScoped n a && checkScoped n b
  | .reflect t | .metadata t | .project t | .get t _ | .inject _ t | .perform t | .done t =>
    checkScoped n t
  | .nat _ | .boolean _ | .label _ => true
  | .extend t fs => checkScoped n t && checkScopedFields n fs
  | .record fs => checkScopedFields n fs
  | .ifZero v z s => checkScoped n v && checkScoped n z && checkScoped (n + 1) s
  | .case t arms => checkScoped n t && checkScopedFields (n + 1) arms
  | .ifBool c t f => checkScoped n c && checkScoped n t && checkScoped n f

private def checkScopedList (n : Nat) : List Term → Bool
  | [] => true
  | t :: ts => checkScoped n t && checkScopedList n ts

private def checkScopedFields (n : Nat) : List (String × Term) → Bool
  | [] => true
  | (_, t) :: fs => checkScoped n t && checkScopedFields n fs
end

mutual
private theorem checkScoped_holds : ∀ (n : Nat) (t : Term), checkScoped n t = true → Scoped n t
  | n, .hole _ σ, h => .hole (checkScopedList_holds n σ h)
  | n, .bound i, h => .bound (of_decide_eq_true h)
  | n, .lam body, h => .lam (checkScoped_holds (n + 1) body h)
  | n, .app a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .app (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .mix a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .mix (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .fix a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .fix (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .specification a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .specification (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .prototype a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .prototype (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .reflect t, h => .reflect (checkScoped_holds n t h)
  | n, .metadata t, h => .metadata (checkScoped_holds n t h)
  | n, .project t, h => .project (checkScoped_holds n t h)
  | n, .nat v, _ => .natural v
  | n, .boolean v, _ => .boolean v
  | n, .label v, _ => .label v
  | n, .binary _ a b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .binary (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)
  | n, .extend t fs, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .extend (checkScoped_holds n t h.1) (checkScopedFields_holds n fs h.2)
  | n, .record fs, h => .record (checkScopedFields_holds n fs h)
  | n, .get t _, h => .get (checkScoped_holds n t h)
  | n, .ifZero v z s, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .condition (checkScoped_holds n v h.1.1) (checkScoped_holds n z h.1.2) (checkScoped_holds (n + 1) s h.2)
  | n, .inject _ p, h => .inject (checkScoped_holds n p h)
  | n, .case t arms, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .case (checkScoped_holds n t h.1) (checkScopedFields_holds (n + 1) arms h.2)
  | n, .ifBool c t f, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .ifBool (checkScoped_holds n c h.1.1) (checkScoped_holds n t h.1.2) (checkScoped_holds n f h.2)
  | n, .perform p, h => .perform (checkScoped_holds n p h)
  | n, .done v, h => .done (checkScoped_holds n v h)
  | n, .split a _ b, h => by
    simp only [checkScoped, Bool.and_eq_true] at h
    exact .split (checkScoped_holds n a h.1) (checkScoped_holds n b h.2)

private theorem checkScopedList_holds :
    ∀ (n : Nat) (ts : List Term), checkScopedList n ts = true → ∀ t ∈ ts, Scoped n t
  | _, [], _, _, hm => by cases hm
  | n, t :: ts, h, x, hm => by
    simp only [checkScopedList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with hxt | hrest
    · rw [hxt]; exact checkScoped_holds n t h.1
    · exact checkScopedList_holds n ts h.2 x hrest

private theorem checkScopedFields_holds :
    ∀ (n : Nat) (fs : List (String × Term)), checkScopedFields n fs = true → ∀ f ∈ fs, Scoped n f.2
  | _, [], _, _, hm => by cases hm
  | n, (k, t) :: fs, h, f, hm => by
    simp only [checkScopedFields, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with hft | hrest
    · rw [hft]; exact checkScoped_holds n t h.1
    · exact checkScopedFields_holds n fs h.2 f hrest
end

private def checkEnvValid (bound : Nat) (env : Environment) : Bool :=
  env.all (fun addr => decide (addr < bound))

private theorem checkEnvValid_holds {bound : Nat} {env : Environment}
    (h : checkEnvValid bound env = true) : EnvironmentValid bound env := by
  intro addr hmem
  exact of_decide_eq_true (List.all_eq_true.mp h addr hmem)

private def checkClosureValid (bound : Nat) (c : Closure) : Bool :=
  checkScoped c.environment.length c.term && checkEnvValid bound c.environment

private theorem checkClosureValid_holds {bound : Nat} {c : Closure}
    (h : checkClosureValid bound c = true) : ClosureValid bound c := by
  simp only [checkClosureValid, Bool.and_eq_true] at h
  exact ⟨checkScoped_holds _ _ h.1, checkEnvValid_holds h.2⟩

private def checkRuntimeValueValid (bound : Nat) : RuntimeValue → Bool
  | .closure body env => checkScoped (env.length + 1) body && checkEnvValid bound env
  | .natural _ | .boolean _ | .label _ => true
  | .record fields => fields.all (fun f => decide (f.2 < bound))
  | .specification m e => decide (m < bound) && decide (e < bound)
  | .prototype s t => decide (s < bound) && decide (t < bound)
  | .variant _ p => decide (p < bound)

private theorem checkRuntimeValueValid_holds {bound : Nat} {v : RuntimeValue}
    (h : checkRuntimeValueValid bound v = true) : RuntimeValueValid bound v := by
  cases v with
  | closure body env =>
    simp only [checkRuntimeValueValid, Bool.and_eq_true] at h
    exact ⟨checkScoped_holds _ _ h.1, checkEnvValid_holds h.2⟩
  | natural _ | boolean _ | label _ => trivial
  | record fields =>
    intro f hf
    exact of_decide_eq_true (List.all_eq_true.mp h f hf)
  | specification m e | prototype m e =>
    simp only [checkRuntimeValueValid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  | variant _ p =>
    dsimp only [RuntimeValueValid]
    exact of_decide_eq_true h

private def checkCellValid (bound : Nat) : Cell → Bool
  | .suspended o | .evaluating o => checkClosureValid bound o
  | .cached o v => checkClosureValid bound o && checkRuntimeValueValid bound v

private theorem checkCellValid_holds {bound : Nat} {c : Cell}
    (h : checkCellValid bound c = true) : CellValid bound c := by
  cases c with
  | suspended _ | evaluating _ => exact checkClosureValid_holds h
  | cached _ _ =>
    simp only [checkCellValid, Bool.and_eq_true] at h
    exact ⟨checkClosureValid_holds h.1, checkRuntimeValueValid_holds h.2⟩

private def checkFrameValid (bound : Nat) : Frame → Bool
  | .argument t env | .binaryLeft _ t env => checkClosureValid bound ⟨t, env⟩
  | .update addr => decide (addr < bound)
  | .field _ | .reflect | .metadata | .project => true
  | .extend fields env => checkEnvValid bound env && fields.all (fun f => checkScoped env.length f.2)
  | .condition z s env => checkEnvValid bound env && checkScoped env.length z && checkScoped (env.length + 1) s
  | .binaryRight _ v => checkRuntimeValueValid bound v
  | .case arms env => checkEnvValid bound env && arms.all (fun a => checkScoped (env.length + 1) a.2)
  | .ifBool wt wf env => checkEnvValid bound env && checkScoped env.length wt && checkScoped env.length wf
  | .split _ fn env => checkEnvValid bound env && checkScoped env.length fn

private theorem checkFrameValid_holds {bound : Nat} {f : Frame}
    (h : checkFrameValid bound f = true) : FrameValid bound f := by
  cases f with
  | argument _ _ | binaryLeft _ _ _ => exact checkClosureValid_holds h
  | update _ =>
    dsimp only [FrameValid]
    exact of_decide_eq_true h
  | field _ | reflect | metadata | project => trivial
  | extend fields env =>
    simp only [checkFrameValid, Bool.and_eq_true] at h
    exact ⟨checkEnvValid_holds h.1, fun fld hfld => checkScoped_holds _ _ (List.all_eq_true.mp h.2 fld hfld)⟩
  | condition _ _ _ =>
    simp only [checkFrameValid, Bool.and_eq_true] at h
    exact ⟨checkEnvValid_holds h.1.1, checkScoped_holds _ _ h.1.2, checkScoped_holds _ _ h.2⟩
  | binaryRight _ _ => exact checkRuntimeValueValid_holds h
  | case arms env =>
    simp only [checkFrameValid, Bool.and_eq_true] at h
    exact ⟨checkEnvValid_holds h.1, fun arm harm => checkScoped_holds _ _ (List.all_eq_true.mp h.2 arm harm)⟩
  | ifBool _ _ _ =>
    simp only [checkFrameValid, Bool.and_eq_true] at h
    exact ⟨checkEnvValid_holds h.1.1, checkScoped_holds _ _ h.1.2, checkScoped_holds _ _ h.2⟩
  | split _ _ _ =>
    simp only [checkFrameValid, Bool.and_eq_true] at h
    exact ⟨checkEnvValid_holds h.1, checkScoped_holds _ _ h.2⟩

private def checkControlValid (bound : Nat) : Control → Bool
  | .evaluate t env => checkClosureValid bound ⟨t, env⟩
  | .enter addr | .blackhole addr | .yielded addr => decide (addr < bound)
  | .returned v | .complete v => checkRuntimeValueValid bound v
  | .refused _ => true

private theorem checkControlValid_holds {bound : Nat} {c : Control}
    (h : checkControlValid bound c = true) : ControlValid bound c := by
  cases c with
  | evaluate _ _ => exact checkClosureValid_holds h
  | enter _ | blackhole _ | yielded _ =>
    dsimp only [ControlValid]
    exact of_decide_eq_true h
  | returned _ | complete _ => exact checkRuntimeValueValid_holds h
  | refused _ => trivial

/-- Executable checker for `Obend.Core.Invariant.LexicalInvariant`. -/
def checkLexical (s : State) : Bool :=
  s.heap.toList.all (checkCellValid s.heap.size) &&
  checkControlValid s.heap.size s.control &&
  s.stack.all (checkFrameValid s.heap.size)

theorem checkLexical_inhabited : ∃ s : State, checkLexical s = true :=
  ⟨initial (.nat 7), by decide⟩

theorem checkLexical_sound {s : State} (h : checkLexical s = true) : LexicalInvariant s := by
  simp only [checkLexical, Bool.and_eq_true] at h
  refine ⟨?_, checkControlValid_holds h.1.2, ?_⟩
  · intro addr cell hget
    have hmem : cell ∈ s.heap.toList := by
      have ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hget
      subst heq
      exact Array.getElem_mem_toList hlt
    exact checkCellValid_holds (List.all_eq_true.mp h.1.1 cell hmem)
  · intro f hf
    exact checkFrameValid_holds (List.all_eq_true.mp h.2 f hf)

private def nodupNatB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupNatB xs

private theorem nodupNatB_holds : ∀ {xs : List Nat}, nodupNatB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNatB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, nodupNatB_holds h.2⟩
    intro hm
    rw [List.contains_iff_mem.mpr hm] at h
    cases h.1

private def isEvaluatingCell : Option Cell → Bool
  | some (.evaluating _) => true
  | _ => false

private def checkEvaluatingMarked (updates : List Address) (heap : Array Cell) : Nat → Bool
  | 0 => true
  | n + 1 =>
    (!isEvaluatingCell heap[n]? || updates.contains n) && checkEvaluatingMarked updates heap n

private theorem checkEvaluatingMarked_holds (updates : List Address) (heap : Array Cell) :
    ∀ n, checkEvaluatingMarked updates heap n = true →
      ∀ addr, addr < n → isEvaluatingCell heap[addr]? = true → addr ∈ updates
  | 0, _, _, hlt, _ => by omega
  | n + 1, h, addr, hlt, heval => by
    simp only [checkEvaluatingMarked, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    by_cases heq : addr = n
    · subst heq
      rcases h.1 with hne | hmem
      · rw [heval] at hne; cases hne
      · exact List.contains_iff_mem.mp hmem
    · exact checkEvaluatingMarked_holds updates heap n h.2 addr (by omega) heval

/-- Executable checker for `Obend.Core.Invariant.BusyInvariant`. -/
def checkBusy (s : State) : Bool :=
  let ups := stackUpdates s.stack
  nodupNatB ups &&
  ups.all (fun addr => isEvaluatingCell s.heap[addr]?) &&
  checkEvaluatingMarked ups s.heap s.heap.size

theorem checkBusy_inhabited : ∃ s : State, checkBusy s = true :=
  ⟨initial (.nat 7), by decide⟩

theorem checkBusy_sound {s : State} (h : checkBusy s = true) : BusyInvariant s := by
  simp only [checkBusy, Bool.and_eq_true] at h
  refine ⟨nodupNatB_holds h.1.1, fun addr => ?_⟩
  constructor
  · intro hmem
    have hev := List.all_eq_true.mp h.1.2 addr hmem
    cases hget : s.heap[addr]? with
    | none => simp [hget, isEvaluatingCell] at hev
    | some c =>
      cases c with
      | evaluating o => exact ⟨o, rfl⟩
      | suspended _ | cached _ _ => simp [hget, isEvaluatingCell] at hev
  · rintro ⟨o, hget⟩
    have hlt : addr < s.heap.size := (Array.getElem?_eq_some_iff.mp hget).1
    exact checkEvaluatingMarked_holds _ _ _ h.2 addr hlt (by simp [hget, isEvaluatingCell])

/-- Executable checker for `Obend.Core.Invariant.FinalStackInvariant`. -/
def checkFinalStack (s : State) : Bool :=
  match s.control with
  | .complete _ => s.stack.isEmpty
  | _ => true

theorem checkFinalStack_inhabited : ∃ s : State, checkFinalStack s = true :=
  ⟨initial (.nat 7), by decide⟩

theorem checkFinalStack_sound {s : State} (h : checkFinalStack s = true) : FinalStackInvariant s := by
  intro v hc
  simp only [checkFinalStack, hc, List.isEmpty_iff] at h
  exact h

/-- Finite association table encoding `Obend.Core.Check.Annotations`. -/
abbrev AnnTable := List (List Nat × LambdaAnnotation)

def AnnTable.toAnnotations (t : AnnTable) : Annotations := fun p => t.lookup p

/-- Serializable typing certificate for a `Closure`. -/
structure ClosureCert where
  context : Context
  annotations : AnnTable
  deriving Repr, DecidableEq

/-- Serializable typing certificate for a `RuntimeValue`. -/
inductive ValueCert where
  | direct
  | closure (context : Context) (annotation : LambdaAnnotation) (annotations : AnnTable)
  | record (row : Ty)
  | variant (row : Ty) (tag : String) (payloadTy : Ty)
  | convert (actual : Ty) (inner : ValueCert)
  deriving Repr, DecidableEq

/-- Serializable typing certificate for one heap `Cell`. -/
structure CellCert where
  type : Ty
  origin : ClosureCert
  value : Option ValueCert := none
  deriving Repr, DecidableEq

/-- Serializable typing certificate for `Control`. -/
inductive ControlCert where
  | evaluate (closure : ClosureCert)
  | enter
  | blackhole
  | returned (value : ValueCert)
  | complete (value : ValueCert)
  | yielded (planType response : Ty)
  deriving Repr, DecidableEq

/-- Serializable typing certificate for one `Frame`. -/
inductive FrameCert where
  | argument (arg : ClosureCert) (functionType : Ty) (reuse : Reuse) (quantity : Quantity)
      (domain codomain : Ty)
  | update (address : Address) (type : Ty)
  | field (name : String) (row member : Ty)
  | reflect (specType targetType : Ty)
  | metadata (metadataType extensionType : Ty)
  | project (specType targetType : Ty)
  | extend (context : Context) (annotations : AnnTable) (row inherited : Ty)
  | condition (zero : ClosureCert) (succContext : Context) (succAnns : AnnTable) (result : Ty)
  | binaryLeft (right : ClosureCert)
  | binaryRight (left : ValueCert)
  | case (context : Context) (annotations : AnnTable) (q : Quantity) (row result : Ty)
  | effectCase (context : Context) (annotations : AnnTable) (q : Quantity)
      (planType response row result : Ty)
  | ifBool (whenTrue whenFalse : ClosureCert) (result : Ty)
  | split (fn : ClosureCert) (row functionType result : Ty)
  deriving Repr, DecidableEq

/-- Serializable typing certificate for one step of `StackTyping`. -/
inductive StackStepCert where
  | frame (input middle : Ty) (cert : FrameCert)
  | convert (expected : Ty)
  | returns (planType response : Ty)
  deriving Repr, DecidableEq

/-- Full serializable typing certificate for a `Core.Machine.State`. -/
structure StateCert where
  assumptions : Assumptions
  cells : List CellCert
  current : Ty
  control : ControlCert
  stack : List StackStepCert
  result : Ty

def StateCert.addressTypes (c : StateCert) : AddressTypes :=
  c.cells.map CellCert.type

/-- Build a canonical `StateCert` for a closed initial state `initial term`. -/
def StateCert.ofInitial (assumptions : Assumptions) (ty : Ty) (anns : AnnTable) : StateCert :=
  { assumptions := assumptions
    cells := []
    current := ty
    control := .evaluate ⟨[], anns⟩
    stack := []
    result := ty }

@[simp] theorem StateCert.ofInitial_assumptions (a : Assumptions) (ty : Ty) (anns : AnnTable) :
    (StateCert.ofInitial a ty anns).assumptions = a := by
  simp [StateCert.ofInitial]

@[simp] theorem StateCert.ofInitial_addressTypes (a : Assumptions) (ty : Ty) (anns : AnnTable) :
    (StateCert.ofInitial a ty anns).addressTypes = [] := by
  simp [StateCert.ofInitial, StateCert.addressTypes]

@[simp] theorem StateCert.ofInitial_result (a : Assumptions) (ty : Ty) (anns : AnnTable) :
    (StateCert.ofInitial a ty anns).result = ty := by
  simp [StateCert.ofInitial]

private def verifyEnvTyping (types : AddressTypes) :
    (ctx : Context) → (env : Environment) → Except String (PLift (EnvironmentTyping types ctx env))
  | [], [] => .ok ⟨EnvironmentTyping.empty types⟩
  | b :: ctx, a :: env => do
    let ⟨hrest⟩ ← verifyEnvTyping types ctx env
    match hty : types[a]? with
    | some t =>
      if hEq : t = b.type then
        .ok ⟨hrest.cons (by rw [hty, hEq])⟩
      else .error "environment binding type mismatch"
    | none => .error "environment address out of bounds"
  | _, _ => .error "environment/context length mismatch"

private def verifyClosure (assumptions : Assumptions) (types : AddressTypes)
    (cert : ClosureCert) (c : Closure) (expected : Ty) :
    Except String (ClosureTyping assumptions types c expected) := do
  let ⟨henv⟩ ← verifyEnvTyping types cert.context c.environment
  match checkAt assumptions cert.annotations.toAnnotations cert.context [] c.term expected with
  | .error _ => .error "closure term failed bidirectional type check"
  | .ok against =>
    if hsafe : safeUses cert.context against.uses = true then
      if hvalid : validContext assumptions.shareableVariables cert.context = true then
        .ok ⟨cert.context, against.uses, henv, against.derivation, hsafe, hvalid⟩
      else .error "closure context invalid"
    else .error "closure uses unsafe"

private def verifyClosedRecordRow (assumptions : Assumptions) (types : AddressTypes)
    (fields : List (String × Address)) :
    (row : Ty) →
    Except String (PLift (
      (∃ fuel, row.isRow assumptions.bounds fuel = true) ∧
      (∀ (fuel : Nat) (name : String) (member : Ty), row.lookup assumptions.bounds fuel name = some member →
        ∃ address actual, fields.find? (fun field => field.1 == name) = some (name, address) ∧
          types[address]? = some actual ∧ ConversionPath assumptions actual member)))
  | .emptyRow =>
    .ok ⟨⟨⟨1, rfl⟩, fun fuel _ _ h => by cases fuel <;> simp [Ty.lookup] at h⟩⟩
  | .field prior m tail => do
    let ⟨hrest⟩ ← verifyClosedRecordRow assumptions types fields tail
    match hfind : fields.find? (fun field => field.1 == prior) with
    | none => .error s!"record value missing field {prior}"
    | some (foundName, addr) =>
      if hne : foundName = prior then
        match hty : types[addr]? with
        | none => .error s!"record field {prior} address out of bounds"
        | some actual =>
          if hsame : sameType assumptions actual m = true then
            .ok ⟨⟨by obtain ⟨f, hf⟩ := hrest.1; exact ⟨f + 1, hf⟩,
              fun fuel name member hlook => by
                cases fuel with
                | zero => simp [Ty.lookup] at hlook
                | succ fuel' =>
                  simp only [Ty.lookup] at hlook
                  by_cases hnm : prior = name
                  · subst hnm
                    simp only [↓reduceIte, Option.some.injEq] at hlook
                    subst hlook; subst hne
                    exact ⟨addr, actual, hfind, hty, .step (.refl _) hsame⟩
                  · simp only [hnm, ↓reduceIte] at hlook
                    exact hrest.2 fuel' name member hlook⟩⟩
          else .error s!"record field {prior} type mismatch"
      else .error "record field label mismatch"
  | _ => .error "expected explicit closed record row"

private def verifyValue (assumptions : Assumptions) (types : AddressTypes) :
    (cert : ValueCert) → (v : RuntimeValue) → (expected : Ty) →
    Except String (PLift (ValueTyping assumptions types v expected))
  | .convert actual inner, v, expected => do
    let ⟨hv⟩ ← verifyValue assumptions types inner v actual
    if hsame : sameType assumptions actual expected = true then
      .ok ⟨.conversion hv hsame⟩
    else .error "value conversion failed sameType"
  | .direct, .natural n, .natural => .ok ⟨.natural n⟩
  | .direct, .boolean b, .boolean => .ok ⟨.boolean b⟩
  | .direct, .label s, .label => .ok ⟨.label s⟩
  | .direct, .specification m e, .specification mt et =>
    match hm : types[m]?, he : types[e]? with
    | some mt', some et' =>
      if h1 : mt' = mt then
        if h2 : et' = et then .ok ⟨.specification (h1 ▸ hm) (h2 ▸ he)⟩
        else .error "specification extension type mismatch"
      else .error "specification metadata type mismatch"
    | _, _ => .error "specification address out of bounds"
  | .direct, .prototype sp tg, .prototype st tt =>
    match hs : types[sp]?, ht : types[tg]? with
    | some st', some tt' =>
      if h1 : st' = st then
        if h2 : tt' = tt then .ok ⟨.prototype (h1 ▸ hs) (h2 ▸ ht)⟩
        else .error "prototype target type mismatch"
      else .error "prototype spec type mismatch"
    | _, _ => .error "prototype address out of bounds"
  | .closure ctx ann anns, .closure body env, .arrow reuse param dom cod => do
    let ⟨henv⟩ ← verifyEnvTyping types ctx env
    if hann : ann = ⟨dom, cod, param, reuse⟩ then
      match checkAt assumptions anns.toAnnotations (⟨dom, param⟩ :: ctx) [] body cod with
      | .error _ => .error "closure value body failed type check"
      | .ok against =>
        if hsafe : safeUses (⟨dom, param⟩ :: ctx) against.uses = true then
          if hvalid : validContext assumptions.shareableVariables (⟨dom, param⟩ :: ctx) = true then
            if hreuse : reusableAllowed assumptions reuse ctx against.uses.tail = true then
              .ok ⟨.closure (annotation := ⟨dom, cod, param, reuse⟩) henv against.derivation hsafe hvalid hreuse⟩
            else .error "closure value captures not reusable"
          else .error "closure value context invalid"
        else .error "closure value uses unsafe"
    else .error "closure value annotation mismatch"
  | .record row, .record fields, expected => do
    if hrow : row = expected then
      let ⟨hrec⟩ ← verifyClosedRecordRow assumptions types fields row
      .ok ⟨hrow ▸ .record hrec.1 hrec.2⟩
    else .error "record value row mismatch"
  | .variant row tag payloadTy, .variant tag' addr, .variant row' => do
    if h1 : row = row' then
      if h2 : tag = tag' then
        match hlook : lookupV assumptions.bounds [] row tag with
        | none => .error "variant tag missing from row"
        | some member =>
          if hm : member = payloadTy then
            match hty : types[addr]? with
            | none => .error "variant payload address out of bounds"
            | some actual =>
              if hsame : sameType assumptions actual member = true then
                .ok ⟨by
                  subst h1; subst h2; subst hm
                  obtain ⟨fuel, hfl⟩ := (lookupV_iff assumptions.bounds row tag member).mp hlook
                  exact .variant hfl hty (.step (.refl _) hsame)⟩
              else .error "variant payload type mismatch"
          else .error "variant payload annotation mismatch"
      else .error "variant tag mismatch"
    else .error "variant row mismatch"
  | _, _, _ => .error "value certificate shape mismatch"

private def verifyCell (assumptions : Assumptions) (types : AddressTypes)
    (cert : CellCert) : (cell : Cell) → Except String (PLift (CellTyping assumptions types cell cert.type))
  | .suspended o => do
    if hpure : cert.type.isComputation = false then
      let ho ← verifyClosure assumptions types cert.origin o cert.type
      .ok ⟨.suspended ho hpure⟩
    else .error "heap cell cannot hold computation type"
  | .evaluating o => do
    if hpure : cert.type.isComputation = false then
      let ho ← verifyClosure assumptions types cert.origin o cert.type
      .ok ⟨.evaluating ho hpure⟩
    else .error "heap cell cannot hold computation type"
  | .cached o v => do
    if hpure : cert.type.isComputation = false then
      let some vc := cert.value | .error "cached cell missing value certificate"
      let ho ← verifyClosure assumptions types cert.origin o cert.type
      let ⟨hv⟩ ← verifyValue assumptions types vc v cert.type
      .ok ⟨.cached ho hv hpure⟩
    else .error "heap cell cannot hold computation type"

private def verifyCellsFrom (assumptions : Assumptions) (types : AddressTypes)
    (heap : Array Cell) : (idx : Nat) → (certs : List CellCert) →
    Except String (PLift (∀ (k : Nat) (c : CellCert), certs[k]? = some c →
      ∃ stored, heap[idx + k]? = some stored ∧ CellTyping assumptions types stored c.type))
  | _, [] => .ok ⟨fun _ _ h => by simp at h⟩
  | idx, cert :: rest => do
    match hget : heap[idx]? with
    | none => .error "heap cell index out of bounds"
    | some cell =>
      let ⟨hcell⟩ ← verifyCell assumptions types cert cell
      let ⟨hrest⟩ ← verifyCellsFrom assumptions types heap (idx + 1) rest
      .ok ⟨fun k c hk => by
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact ⟨cell, by simpa using hget, hcell⟩
        | succ k' =>
          simp only [List.getElem?_cons_succ] at hk
          have ⟨stored, hst, hct⟩ := hrest k' c hk
          exact ⟨stored, by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hst, hct⟩⟩

private def verifyHeap (assumptions : Assumptions) (certs : List CellCert) (heap : Array Cell) :
    Except String (PLift (HeapTyping assumptions (certs.map CellCert.type) heap)) := do
  if hlen : (certs.map CellCert.type).length = heap.size then
    let ⟨hcells⟩ ← verifyCellsFrom assumptions (certs.map CellCert.type) heap 0 certs
    .ok ⟨⟨hlen, fun addr ty hty => by
      rw [List.getElem?_map] at hty
      cases hc : certs[addr]? with
      | none => simp [hc] at hty
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq] at hty
        subst hty
        have ⟨stored, hst, hct⟩ := hcells addr c hc
        exact ⟨stored, by simpa using hst, hct⟩⟩⟩
  else .error "heap size does not match certificate cell count"

private def verifyControl (assumptions : Assumptions) (types : AddressTypes)
    (cert : ControlCert) (ctrl : Control) (current : Ty) :
    Except String (PLift (ControlTyping assumptions types ctrl current)) :=
  match cert, ctrl with
  | .evaluate cc, .evaluate term env => do
    let hc ← verifyClosure assumptions types cc ⟨term, env⟩ current
    .ok ⟨.evaluate hc⟩
  | .enter, .enter addr =>
    match h : types[addr]? with
    | some t => if heq : t = current then .ok ⟨.enter (heq ▸ h)⟩ else .error "enter type mismatch"
    | none => .error "enter address out of bounds"
  | .blackhole, .blackhole addr =>
    match h : types[addr]? with
    | some t => if heq : t = current then .ok ⟨.blackhole (heq ▸ h)⟩ else .error "blackhole type mismatch"
    | none => .error "blackhole address out of bounds"
  | .returned vc, .returned v => do
    let ⟨hv⟩ ← verifyValue assumptions types vc v current
    .ok ⟨.returned hv⟩
  | .complete vc, .complete v => do
    let ⟨hv⟩ ← verifyValue assumptions types vc v current
    .ok ⟨.complete hv⟩
  | .yielded planTy respTy, .yielded plan =>
    if hcur : current = .computation planTy respTy respTy then
      match h : types[plan]? with
      | some t =>
        if ht : t = planTy then
          if hplan : planTy.isPlan = true then
            if hresp : respTy.isData = true then
              .ok ⟨hcur ▸ .yielded (ht ▸ h) hplan hresp⟩
            else .error "yielded response type is not first-order data"
          else .error "yielded plan type is not a Plan"
        else .error "yielded plan cell type mismatch"
      | none => .error "yielded plan address out of bounds"
    else .error "yielded control current type mismatch"
  | _, .refused _ => .error "refused machine state cannot be certified"
  | _, _ => .error "control certificate mismatch"

private def verifyFrame (assumptions : Assumptions) (types : AddressTypes)
    (cert : FrameCert) (frame : Frame) (input middle : Ty) :
    Except String (PLift (FrameTyping assumptions types frame input middle)) :=
  match cert, frame with
  | .argument argCert fnTy reuse qty dom cod, .argument arg env => do
    if h1 : fnTy = input then
      if h2 : cod = middle then
        let harg ← verifyClosure assumptions types argCert ⟨arg, env⟩ dom
        if hcall : callable fnTy = .arrow reuse qty dom cod then
          if hallow : argumentAllowed assumptions qty harg.context dom harg.uses = true then
            .ok ⟨by subst h1; subst h2; exact .argument harg hcall hallow⟩
          else .error "argument frame violates argumentAllowed"
        else .error "argument frame function not callable at declared arrow"
      else .error "argument frame codomain mismatch"
    else .error "argument frame input mismatch"
  | .update addr ty, .update addr' =>
    if h1 : addr = addr' then
      if h2 : ty = input then
        if h3 : ty = middle then
          match hget : types[addr]? with
          | some t =>
            if ht : t = ty then
              if hpure : ty.isComputation = false then
                .ok ⟨by subst h1; subst h2; subst h3; exact .update (ht ▸ hget) hpure⟩
              else .error "update frame cannot have computation type"
            else .error "update frame address type mismatch"
          | none => .error "update frame address out of bounds"
        else .error "update frame middle mismatch"
      else .error "update frame input mismatch"
    else .error "update frame address mismatch"
  | .field name row member, .field name' =>
    if h1 : name = name' then
      if h2 : row = input then
        if h3 : member = middle then
          match hlook : lookupV assumptions.bounds [] row name with
          | some found =>
            if hf : found = member then
              .ok ⟨by
                subst h1; subst h2; subst h3; subst hf
                obtain ⟨fuel, hfl⟩ := (lookupV_iff assumptions.bounds row name found).mp hlook
                exact .field hfl⟩
            else .error "field frame member mismatch"
          | none => .error "field frame label not found"
        else .error "field frame middle mismatch"
      else .error "field frame input mismatch"
    else .error "field frame name mismatch"
  | .reflect st tt, .reflect =>
    if h1 : input = .prototype st tt then
      if h2 : middle = st then .ok ⟨by rw [h1, h2]; exact .reflect st tt⟩
      else .error "reflect frame middle mismatch"
    else .error "reflect frame input mismatch"
  | .metadata mt et, .metadata =>
    if h1 : input = .specification mt et then
      if h2 : middle = mt then .ok ⟨by rw [h1, h2]; exact .metadata mt et⟩
      else .error "metadata frame middle mismatch"
    else .error "metadata frame input mismatch"
  | .project st tt, .project =>
    if h1 : input = .prototype st tt then
      if h2 : middle = tt then .ok ⟨by rw [h1, h2]; exact .project st tt⟩
      else .error "project frame middle mismatch"
    else .error "project frame input mismatch"
  | .extend ctx anns row inh, .extend fields env => do
    if h1 : inh = input then
      if h2 : overlay row inh = middle then
        let ⟨henv⟩ ← verifyEnvTyping types ctx env
        match checkFields assumptions anns.toAnnotations ctx [] 0 fields row with
        | .error _ => .error "extend frame fields failed type check"
        | .ok fagainst =>
          if hsafe : safeUses ctx fagainst.uses = true then
            if hvalid : validContext assumptions.shareableVariables ctx = true then
              if hrow : isRowV assumptions.bounds [] inh = true then
                .ok ⟨by
                  subst h1; subst h2
                  obtain ⟨fuel, hrf⟩ := (isRowV_iff assumptions.bounds inh).mp hrow
                  exact .extend henv fagainst.derivation hsafe hvalid hrf⟩
              else .error "extend frame inherited type is not a row"
            else .error "extend frame context invalid"
          else .error "extend frame uses unsafe"
      else .error "extend frame output mismatch"
    else .error "extend frame input mismatch"
  | .condition zeroCert succCtx succAnns res, .condition z s env => do
    if h1 : input = .natural then
      if h2 : res = middle then
        let hz ← verifyClosure assumptions types zeroCert ⟨z, env⟩ res
        let ⟨henv⟩ ← verifyEnvTyping types succCtx env
        match checkAt assumptions succAnns.toAnnotations (⟨.natural, .unrestricted⟩ :: succCtx) [] s res with
        | .error _ => .error "condition successor branch failed type check"
        | .ok sagainst =>
          if hsafe : safeUses (⟨.natural, .unrestricted⟩ :: succCtx) sagainst.uses = true then
            if hvalid : validContext assumptions.shareableVariables succCtx = true then
              .ok ⟨by subst h1; subst h2; exact .condition hz henv sagainst.derivation hsafe hvalid⟩
            else .error "condition successor context invalid"
          else .error "condition successor uses unsafe"
      else .error "condition frame output mismatch"
    else .error "condition frame input mismatch"
  | .binaryLeft rCert, .binaryLeft prim right env => do
    if h1 : input = (primitiveTypes prim).1 then
      if h2 : middle = (primitiveTypes prim).2 then
        let hr ← verifyClosure assumptions types rCert ⟨right, env⟩ (primitiveTypes prim).1
        .ok ⟨h1 ▸ h2 ▸ .binaryLeft hr⟩
      else .error "binaryLeft output mismatch"
    else .error "binaryLeft input mismatch"
  | .binaryRight lCert, .binaryRight prim left => do
    if h1 : input = (primitiveTypes prim).1 then
      if h2 : middle = (primitiveTypes prim).2 then
        let ⟨hl⟩ ← verifyValue assumptions types lCert left (primitiveTypes prim).1
        .ok ⟨h1 ▸ h2 ▸ .binaryRight hl⟩
      else .error "binaryRight output mismatch"
    else .error "binaryRight input mismatch"
  | .case ctx anns q row res, .case arms env => do
    if h1 : input = .variant row then
      if h2 : res = middle then
        let ⟨henv⟩ ← verifyEnvTyping types ctx env
        match checkArms assumptions anns.toAnnotations ctx q [] 0 row res arms with
        | .error _ => .error "case frame arms failed type check"
        | .ok armsAgainst =>
          if hrow : armsAgainst.row = row then
            if hvalid : validContext assumptions.shareableVariables ctx = true then
              .ok ⟨by subst h1; subst h2; exact .case henv (hrow ▸ armsAgainst.derivation) hvalid⟩
            else .error "case frame context invalid"
          else .error "case frame arm row mismatch"
      else .error "case frame result mismatch"
    else .error "case frame input mismatch"
  | .effectCase ctx anns q planTy respTy row res, .case arms env => do
    if h1 : input = .computation planTy respTy (.variant row) then
      if h2 : middle = .computation planTy respTy res then
        let ⟨henv⟩ ← verifyEnvTyping types ctx env
        match checkArms assumptions anns.toAnnotations ctx q [] 0 row (.computation planTy respTy res) arms with
        | .error _ => .error "effectCase frame arms failed type check"
        | .ok armsAgainst =>
          if hrow : armsAgainst.row = row then
            if hvalid : validContext assumptions.shareableVariables ctx = true then
              if hpure : res.isComputation = false then
                .ok ⟨by subst h1; subst h2; exact .effectCase henv (hrow ▸ armsAgainst.derivation) hvalid hpure⟩
              else .error "effectCase result cannot be a computation"
            else .error "effectCase context invalid"
          else .error "effectCase arm row mismatch"
      else .error "effectCase output mismatch"
    else .error "effectCase input mismatch"
  | .ifBool wtCert wfCert res, .ifBool wt wf env => do
    if h1 : input = .boolean then
      if h2 : res = middle then
        let hwt ← verifyClosure assumptions types wtCert ⟨wt, env⟩ res
        let hwf ← verifyClosure assumptions types wfCert ⟨wf, env⟩ res
        .ok ⟨by subst h1; subst h2; exact .ifBool hwt hwf⟩
      else .error "ifBool output mismatch"
    else .error "ifBool input mismatch"
  | .split fnCert row fnTy res, .split names fn env => do
    if h1 : row = input then
      if h2 : res = middle then
        let hfn ← verifyClosure assumptions types fnCert ⟨fn, env⟩ fnTy
        if htail : row.tail = .emptyRow then
          match checkSpine assumptions [] [] [] row names fnTy with
          | .error _ => .error "split frame spine failed check"
          | .ok ⟨spRes, hspine⟩ =>
            if hres : spRes = res then
              .ok ⟨by
                subst h1; subst h2
                obtain ⟨_, hshape⟩ := SplitSpine.shape (hres ▸ hspine)
                exact .split hfn htail hshape⟩
            else .error "split frame result mismatch"
        else .error "split frame row must be closed"
      else .error "split frame output mismatch"
    else .error "split frame input mismatch"
  | _, _ => .error "frame certificate shape mismatch"

private def verifyStack (assumptions : Assumptions) (types : AddressTypes) :
    (steps : List StackStepCert) → (stack : List Frame) → (input result : Ty) →
    Except String (PLift (StackTyping assumptions types stack input result))
  | [], [], input, result =>
    if h : input = result then .ok ⟨h ▸ .nil input⟩
    else .error "empty stack input/result type mismatch"
  | .convert expected :: rest, stack, input, result => do
    if hsame : sameType assumptions input expected = true then
      let ⟨hrest⟩ ← verifyStack assumptions types rest stack expected result
      .ok ⟨.conversion hsame hrest⟩
    else .error "stack conversion failed sameType"
  | .returns planTy respTy :: rest, stack, input, result => do
    if hpure : input.isComputation = false then
      let ⟨hrest⟩ ← verifyStack assumptions types rest stack (.computation planTy respTy input) result
      .ok ⟨.returns hpure hrest⟩
    else .error "returns step requires non-computation input"
  | .frame fin fmid fcert :: rest, f :: fs, input, result => do
    if hin : fin = input then
      let ⟨hf⟩ ← verifyFrame assumptions types fcert f fin fmid
      let ⟨hrest⟩ ← verifyStack assumptions types rest fs fmid result
      .ok ⟨by subst hin; exact .cons hf hrest⟩
    else .error "stack frame input mismatch"
  | _, _, _, _ => .error "stack certificate length/shape mismatch"

/-- Executable kernel-checked verifier reconstructing a full `StateTyping` derivation from
a `StateCert` and raw `Core.Machine.State`. Rejects any refused, ill-scoped, busy-corrupt,
or ill-typed state. -/
def verifyStateCert (cert : StateCert) (s : State) :
    Except String (StateTyping cert.assumptions cert.addressTypes s cert.result) := do
  if hasm : cert.assumptions.valid = true then
    if hlex : checkLexical s = true then
      if hbusy : checkBusy s = true then
        if hfin : checkFinalStack s = true then
          let ⟨hheap⟩ ← verifyHeap cert.assumptions cert.cells s.heap
          let ⟨hctrl⟩ ← verifyControl cert.assumptions cert.addressTypes cert.control s.control cert.current
          let ⟨hstk⟩ ← verifyStack cert.assumptions cert.addressTypes cert.stack s.stack cert.current cert.result
          .ok ⟨cert.current, hheap, hctrl, hstk, hasm,
            checkLexical_sound hlex, checkBusy_sound hbusy, checkFinalStack_sound hfin⟩
        else .error "state failed FinalStackInvariant"
      else .error "state failed BusyInvariant"
    else .error "state failed LexicalInvariant"
  else .error "certificate assumptions invalid"

/-- Boolean wrapper over `verifyStateCert` for concise wire admission predicates. -/
def checkStateCert (cert : StateCert) (s : State) : Bool :=
  (verifyStateCert cert s).isOk

/-- Constructive inhabitedness witness for `checkStateCert`. -/
theorem checkStateCert_inhabited :
    ∃ (cert : StateCert) (s : State), checkStateCert cert s = true :=
  ⟨StateCert.ofInitial {} .natural [], initial (.nat 7), by decide⟩

/-- Soundness of `checkStateCert`: every accepted `(cert, s)` pair yields a genuine
kernel `StateTyping` derivation (including `LexicalInvariant`, `BusyInvariant`,
`FinalStackInvariant`, and exclusion of all `.refused` control states). -/
theorem checkStateCert_sound {cert : StateCert} {s : State} (h : checkStateCert cert s = true) :
    Nonempty (StateTyping cert.assumptions cert.addressTypes s cert.result) := by
  unfold checkStateCert at h
  cases hv : verifyStateCert cert s with
  | error _ => simp [hv, Except.isOk, Except.toBool] at h
  | ok pf => exact ⟨pf⟩

/-! ## 3. Canonical `Core.Data` Serialization for `StateCert` (Exact Round-Trip) -/

private def natListData (xs : List Nat) : Data := listWith Data.natural xs
private def natListOf (d : Data) : Option (List Nat) := listOfWith naturalOf d

private theorem natListOf_natListData (xs : List Nat) : natListOf (natListData xs) = some xs :=
  listOfWith_listWith naturalOf Data.natural (fun _ => rfl) xs

private def annEntryData (e : List Nat × LambdaAnnotation) : Data :=
  .record [("path", natListData e.1), ("ann", annotationData e.2)]

private def annEntryOf : Data → Option (List Nat × LambdaAnnotation)
  | .record [("path", p), ("ann", a)] => do pure (← natListOf p, ← annotationOf a)
  | _ => none

private theorem annEntryOf_annEntryData (e : List Nat × LambdaAnnotation) :
    annEntryOf (annEntryData e) = some e := by
  simp [annEntryData, annEntryOf, natListOf_natListData, annotationOf_annotationData]

private def closureCertData (c : ClosureCert) : Data :=
  .record [("context", listWith bindingData c.context), ("annotations", listWith annEntryData c.annotations)]

private def closureCertOf : Data → Option ClosureCert
  | .record [("context", ctx), ("annotations", anns)] => do
    pure ⟨← listOfWith bindingOf ctx, ← listOfWith annEntryOf anns⟩
  | _ => none

private theorem closureCertOf_closureCertData (c : ClosureCert) :
    closureCertOf (closureCertData c) = some c := by
  simp [closureCertData, closureCertOf,
    listOfWith_listWith bindingOf bindingData bindingOf_bindingData,
    listOfWith_listWith annEntryOf annEntryData annEntryOf_annEntryData]

private def valueCertData : ValueCert → Data
  | .direct => .variant "direct" (.record [])
  | .closure ctx ann anns => .variant "closure" (.record [
      ("context", listWith bindingData ctx),
      ("ann", annotationData ann),
      ("annotations", listWith annEntryData anns)])
  | .record row => .variant "record" (tyData row)
  | .variant row tag payload => .variant "variant" (.record [
      ("row", tyData row), ("tag", .label tag), ("payload", tyData payload)])
  | .convert actual inner => .variant "convert" (.record [
      ("actual", tyData actual), ("inner", valueCertData inner)])

private def valueCertOf : Data → Option ValueCert
  | .variant "direct" (.record []) => some .direct
  | .variant "closure" (.record [("context", ctx), ("ann", ann), ("annotations", anns)]) => do
    pure (.closure (← listOfWith bindingOf ctx) (← annotationOf ann) (← listOfWith annEntryOf anns))
  | .variant "record" r => (tyOf r).map .record
  | .variant "variant" (.record [("row", r), ("tag", .label t), ("payload", p)]) => do
    pure (.variant (← tyOf r) t (← tyOf p))
  | .variant "convert" (.record [("actual", a), ("inner", i)]) => do
    pure (.convert (← tyOf a) (← valueCertOf i))
  | _ => none

private theorem valueCertOf_valueCertData : ∀ v : ValueCert, valueCertOf (valueCertData v) = some v
  | .direct => rfl
  | .closure ctx ann anns => by
    simp [valueCertData, valueCertOf,
      listOfWith_listWith bindingOf bindingData bindingOf_bindingData,
      annotationOf_annotationData,
      listOfWith_listWith annEntryOf annEntryData annEntryOf_annEntryData]
  | .record r => by simp [valueCertData, valueCertOf, tyOf_tyData]
  | .variant r t p => by simp [valueCertData, valueCertOf, tyOf_tyData]
  | .convert a i => by simp [valueCertData, valueCertOf, tyOf_tyData, valueCertOf_valueCertData i]

private def cellCertData (c : CellCert) : Data :=
  .record [("type", tyData c.type), ("origin", closureCertData c.origin),
    ("value", optionData valueCertData c.value)]

private def cellCertOf : Data → Option CellCert
  | .record [("type", t), ("origin", o), ("value", v)] => do
    pure ⟨← tyOf t, ← closureCertOf o, ← optionOf valueCertOf v⟩
  | _ => none

private theorem cellCertOf_cellCertData (c : CellCert) : cellCertOf (cellCertData c) = some c := by
  simp [cellCertData, cellCertOf, tyOf_tyData, closureCertOf_closureCertData,
    optionOf_optionData valueCertOf valueCertData valueCertOf_valueCertData]

private def controlCertData : ControlCert → Data
  | .evaluate c => .variant "evaluate" (closureCertData c)
  | .enter => .variant "enter" (.record [])
  | .blackhole => .variant "blackhole" (.record [])
  | .returned v => .variant "returned" (valueCertData v)
  | .complete v => .variant "complete" (valueCertData v)
  | .yielded p r => .variant "yielded" (.record [("plan", tyData p), ("response", tyData r)])

private def controlCertOf : Data → Option ControlCert
  | .variant "evaluate" c => (closureCertOf c).map .evaluate
  | .variant "enter" (.record []) => some .enter
  | .variant "blackhole" (.record []) => some .blackhole
  | .variant "returned" v => (valueCertOf v).map .returned
  | .variant "complete" v => (valueCertOf v).map .complete
  | .variant "yielded" (.record [("plan", p), ("response", r)]) => do
    pure (.yielded (← tyOf p) (← tyOf r))
  | _ => none

private theorem controlCertOf_controlCertData (c : ControlCert) :
    controlCertOf (controlCertData c) = some c := by
  cases c <;> simp [controlCertData, controlCertOf, closureCertOf_closureCertData,
    valueCertOf_valueCertData, tyOf_tyData]

private def frameCertData : FrameCert → Data
  | .argument a ft r q d c => .variant "argument" (.record [
      ("arg", closureCertData a), ("fnTy", tyData ft), ("reuse", reuseData r),
      ("qty", quantityData q), ("dom", tyData d), ("cod", tyData c)])
  | .update addr t => .variant "update" (.record [("addr", .natural addr), ("ty", tyData t)])
  | .field n r m => .variant "field" (.record [("name", .label n), ("row", tyData r), ("member", tyData m)])
  | .reflect s t => .variant "reflect" (.record [("spec", tyData s), ("target", tyData t)])
  | .metadata m e => .variant "metadata" (.record [("meta", tyData m), ("ext", tyData e)])
  | .project s t => .variant "project" (.record [("spec", tyData s), ("target", tyData t)])
  | .extend ctx anns r i => .variant "extend" (.record [
      ("ctx", listWith bindingData ctx), ("anns", listWith annEntryData anns),
      ("row", tyData r), ("inh", tyData i)])
  | .condition z sc sa r => .variant "condition" (.record [
      ("zero", closureCertData z), ("sctx", listWith bindingData sc),
      ("sanns", listWith annEntryData sa), ("res", tyData r)])
  | .binaryLeft r => .variant "binaryLeft" (closureCertData r)
  | .binaryRight l => .variant "binaryRight" (valueCertData l)
  | .case ctx anns q row res => .variant "case" (.record [
      ("ctx", listWith bindingData ctx), ("anns", listWith annEntryData anns),
      ("q", quantityData q), ("row", tyData row), ("res", tyData res)])
  | .effectCase ctx anns q p resp row res => .variant "effectCase" (.record [
      ("ctx", listWith bindingData ctx), ("anns", listWith annEntryData anns),
      ("q", quantityData q), ("plan", tyData p), ("resp", tyData resp),
      ("row", tyData row), ("res", tyData res)])
  | .ifBool wt wf res => .variant "ifBool" (.record [
      ("wt", closureCertData wt), ("wf", closureCertData wf), ("res", tyData res)])
  | .split fn row ft res => .variant "split" (.record [
      ("fn", closureCertData fn), ("row", tyData row), ("ft", tyData ft), ("res", tyData res)])

private def frameCertOf : Data → Option FrameCert
  | .variant "argument" (.record [("arg", a), ("fnTy", ft), ("reuse", r), ("qty", q), ("dom", d), ("cod", c)]) => do
    pure (.argument (← closureCertOf a) (← tyOf ft) (← reuseOf r) (← quantityOf q) (← tyOf d) (← tyOf c))
  | .variant "update" (.record [("addr", .natural addr), ("ty", t)]) => do
    pure (.update addr (← tyOf t))
  | .variant "field" (.record [("name", .label n), ("row", r), ("member", m)]) => do
    pure (.field n (← tyOf r) (← tyOf m))
  | .variant "reflect" (.record [("spec", s), ("target", t)]) => do
    pure (.reflect (← tyOf s) (← tyOf t))
  | .variant "metadata" (.record [("meta", m), ("ext", e)]) => do
    pure (.metadata (← tyOf m) (← tyOf e))
  | .variant "project" (.record [("spec", s), ("target", t)]) => do
    pure (.project (← tyOf s) (← tyOf t))
  | .variant "extend" (.record [("ctx", ctx), ("anns", anns), ("row", r), ("inh", i)]) => do
    pure (.extend (← listOfWith bindingOf ctx) (← listOfWith annEntryOf anns) (← tyOf r) (← tyOf i))
  | .variant "condition" (.record [("zero", z), ("sctx", sc), ("sanns", sa), ("res", r)]) => do
    pure (.condition (← closureCertOf z) (← listOfWith bindingOf sc) (← listOfWith annEntryOf sa) (← tyOf r))
  | .variant "binaryLeft" r => (closureCertOf r).map .binaryLeft
  | .variant "binaryRight" l => (valueCertOf l).map .binaryRight
  | .variant "case" (.record [("ctx", ctx), ("anns", anns), ("q", q), ("row", row), ("res", res)]) => do
    pure (.case (← listOfWith bindingOf ctx) (← listOfWith annEntryOf anns) (← quantityOf q) (← tyOf row) (← tyOf res))
  | .variant "effectCase" (.record [("ctx", ctx), ("anns", anns), ("q", q), ("plan", p), ("resp", resp), ("row", row), ("res", res)]) => do
    pure (.effectCase (← listOfWith bindingOf ctx) (← listOfWith annEntryOf anns) (← quantityOf q)
      (← tyOf p) (← tyOf resp) (← tyOf row) (← tyOf res))
  | .variant "ifBool" (.record [("wt", wt), ("wf", wf), ("res", res)]) => do
    pure (.ifBool (← closureCertOf wt) (← closureCertOf wf) (← tyOf res))
  | .variant "split" (.record [("fn", fn), ("row", row), ("ft", ft), ("res", res)]) => do
    pure (.split (← closureCertOf fn) (← tyOf row) (← tyOf ft) (← tyOf res))
  | _ => none

private theorem frameCertOf_frameCertData (f : FrameCert) : frameCertOf (frameCertData f) = some f := by
  cases f <;> simp [frameCertData, frameCertOf, closureCertOf_closureCertData,
    valueCertOf_valueCertData, tyOf_tyData, reuseOf_reuseData, quantityOf_quantityData,
    listOfWith_listWith bindingOf bindingData bindingOf_bindingData,
    listOfWith_listWith annEntryOf annEntryData annEntryOf_annEntryData]

private def stackStepCertData : StackStepCert → Data
  | .frame i m fc => .variant "frame" (.record [("in", tyData i), ("mid", tyData m), ("cert", frameCertData fc)])
  | .convert e => .variant "convert" (tyData e)
  | .returns p r => .variant "returns" (.record [("plan", tyData p), ("resp", tyData r)])

private def stackStepCertOf : Data → Option StackStepCert
  | .variant "frame" (.record [("in", i), ("mid", m), ("cert", fc)]) => do
    pure (.frame (← tyOf i) (← tyOf m) (← frameCertOf fc))
  | .variant "convert" e => (tyOf e).map .convert
  | .variant "returns" (.record [("plan", p), ("resp", r)]) => do
    pure (.returns (← tyOf p) (← tyOf r))
  | _ => none

private theorem stackStepCertOf_stackStepCertData (s : StackStepCert) :
    stackStepCertOf (stackStepCertData s) = some s := by
  cases s <;> simp [stackStepCertData, stackStepCertOf, tyOf_tyData, frameCertOf_frameCertData]

/-- Encode a `StateCert` into canonical `Obend.Core.Data.Data`. -/
def stateCertData (c : StateCert) : Data :=
  .record [
    ("assumptions", assumptionsData c.assumptions),
    ("cells", listWith cellCertData c.cells),
    ("current", tyData c.current),
    ("control", controlCertData c.control),
    ("stack", listWith stackStepCertData c.stack),
    ("result", tyData c.result)
  ]

/-- Decode a `StateCert` from canonical `Obend.Core.Data.Data`. -/
def stateCertOf : Data → Option StateCert
  | .record [("assumptions", a), ("cells", cs), ("current", cur), ("control", ctrl), ("stack", stk), ("result", res)] => do
    pure ⟨← assumptionsOf a, ← listOfWith cellCertOf cs, ← tyOf cur,
      ← controlCertOf ctrl, ← listOfWith stackStepCertOf stk, ← tyOf res⟩
  | _ => none

@[simp] theorem stateCertOf_stateCertData (c : StateCert) :
    stateCertOf (stateCertData c) = some c := by
  simp [stateCertData, stateCertOf, assumptionsOf_assumptionsData,
    listOfWith_listWith cellCertOf cellCertData cellCertOf_cellCertData,
    tyOf_tyData, controlCertOf_controlCertData,
    listOfWith_listWith stackStepCertOf stackStepCertData stackStepCertOf_stackStepCertData]

/-! ## 4. Living Checkpoint Cells in `Obend.Doc.Graph` (Raw `ByteArray` & In-Place Turn Superseding) -/

/-- An executable checkpoint cell on `Doc.Graph`:
- `ast` carries the versioned `core4.heap/1` tag and serialized `StateCert`;
- `pins` carries the 256-bit `cSHAKE256` `heapImageCidBytes` binding;
- `receipt` carries the raw `encodeHeapImage` `ByteArray` directly (`0` hex inside `Doc.Graph`!). -/
def checkpointCell (name : String) (s : State) (cert : StateCert) : Content :=
  .cell name .obendCode (.variant "core4.heap/1" (stateCertData cert))
    [("core4.cid/1", heapImageCidBytes s)] (some (encodeHeapImage s))

/-- Choice-free raw restore: verifies `decodeHeapImage`, 256-bit `cSHAKE256` CID binding,
and certificate syntax without running bidirectional type-checking. -/
def restoreRaw : Content → Option (State × StateCert)
  | .cell _ .obendCode (.variant "core4.heap/1" certData) [("core4.cid/1", cid)] (some img) => do
    let s ← decodeHeapImage img
    if heapImageCidBytes s = cid then
      let cert ← stateCertOf certData
      some (s, cert)
    else none
  | _ => none

private theorem restoreRaw_content (name : String) (s : State) (cert : StateCert) :
    restoreRaw (checkpointCell name s cert) = some (s, cert) := by
  simp [restoreRaw, checkpointCell, decodeHeapImage_encodeHeapImage]

/-- Full verified restore: decodes the raw `ByteArray` image, verifies the 256-bit CID,
and re-verifies `checkStateCert cert s = true`. -/
def restore (c : Content) : Option State := do
  let (s, cert) ← restoreRaw c
  if checkStateCert cert s then some s else none

private theorem restore_content (name : String) (s : State) (cert : StateCert)
    (hok : checkStateCert cert s = true) :
    restore (checkpointCell name s cert) = some s := by
  simp [restore, restoreRaw_content, hok]

/-- A certified live object checkpoint carries an executable `StateCert` re-verified by
`checkStateCert`, rather than an erased untrusted ghost proof. -/
structure Checkpoint (A : Assumptions) (types : AddressTypes) (result : Ty) where
  state : State
  cert : StateCert
  assumptions_eq : cert.assumptions = A
  types_eq : cert.addressTypes = types
  result_eq : cert.result = result
  verified : checkStateCert cert state = true

theorem Checkpoint.typed {A : Assumptions} {types : AddressTypes} {result : Ty}
    (c : Checkpoint A types result) : Nonempty (StateTyping A types c.state result) := by
  obtain ⟨st, cert, ha, ht, hr, hv⟩ := c
  subst ha; subst ht; subst hr
  exact checkStateCert_sound hv

/-- Allocate a living checkpoint cell at a fresh atom OR advance/supersede an existing live
checkpoint cell in place across turns at `atId`. Tombstoned atoms and non-checkpoint atoms
at `atId` are refused. -/
def allocate (g : Graph) (atId parent : AtomId) (name : String)
    (s : State) (cert : StateCert) : Option Graph :=
  if atId == root || g.isDead atId then none
  else match g.label atId with
    | none =>
      if parent != root && !g.alive parent then none
      else some (g.step (.add atId (checkpointCell name s cert) parent))
    | some existing =>
      if (restoreRaw existing).isSome then
        some { g with atoms := g.atoms.map fun e =>
          if e.1 == atId then (atId, checkpointCell name s cert) else e }
      else none

/-- Explicitly advance an already-live checkpoint atom in place to a successor state. -/
def advance (g : Graph) (atId : AtomId) (name : String)
    (s : State) (cert : StateCert) : Option Graph :=
  if atId == root || g.isDead atId then none
  else match g.label atId with
    | some existing =>
      if (restoreRaw existing).isSome then
        some { g with atoms := g.atoms.map fun e =>
          if e.1 == atId then (atId, checkpointCell name s cert) else e }
      else none
    | none => none

def save {A : Assumptions} {types : AddressTypes} {result : Ty}
    (g : Graph) (atId parent : AtomId) (name : String) (c : Checkpoint A types result) : Option Graph :=
  allocate g atId parent name c.state c.cert

/-- Choice-free raw state load (verifies `ByteArray` decode + 256-bit CID). -/
def loadRaw (g : Graph) (atId : AtomId) : Option State :=
  if g.isDead atId then none else (g.label atId).bind (fun c => (restoreRaw c).map Prod.fst)

/-- Verified state load: checks `ByteArray` decode, 256-bit CID, AND `checkStateCert`. -/
def load (g : Graph) (atId : AtomId) : Option State :=
  if g.isDead atId then none else (g.label atId).bind restore

private theorem lookup_map_replace (atoms : List (AtomId × Content)) (atId : AtomId)
    (c : Content) (k : AtomId) :
    (atoms.map fun e => if e.1 == atId then (atId, c) else e).lookup k =
      if k = atId then (atoms.lookup atId).map (fun _ => c) else atoms.lookup k := by
  induction atoms with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    obtain ⟨a, v⟩ := hd
    simp only [List.map_cons]
    by_cases ha : a = atId
    · subst ha
      simp only [beq_self_eq_true, ↓reduceIte, List.lookup]
      by_cases hk : k = a
      · subst hk; simp
      · have hne : (k == a) = false := beq_eq_false_iff_ne.mpr hk
        simp only [hne, hk, ↓reduceIte]
        rw [ih]
        simp [hk]
    · have hab : (a == atId) = false := beq_eq_false_iff_ne.mpr ha
      simp only [hab, Bool.false_eq_true, ↓reduceIte, List.lookup]
      by_cases hk : k = a
      · subst hk
        simp [ha]
      · have hne : (k == a) = false := beq_eq_false_iff_ne.mpr hk
        have hna : (atId == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm ha)
        simp only [hne, hna]
        exact ih

theorem loadRaw_allocate
    {g saved : Graph} {atId parent : AtomId} {name : String} {s : State} {cert : StateCert}
    (ok : allocate g atId parent name s cert = some saved) :
    loadRaw saved atId = some s := by
  unfold allocate at ok
  by_cases hbad : (atId == root || g.isDead atId) = true
  · simp [hbad] at ok
  · have hbadF : (atId == root || g.isDead atId) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte] at ok
    have hnd : g.isDead atId = false := by
      cases hd : g.isDead atId
      · rfl
      · simp [hd] at hbadF
    cases hlbl : g.label atId with
    | none =>
      rw [hlbl] at ok
      by_cases hp : (parent != root && !g.alive parent) = true
      · simp [hp] at ok
      · have hpF : (parent != root && !g.alive parent) = false := Bool.eq_false_iff.mpr hp
        simp only [hpF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold loadRaw
        rw [show (g.step (.add atId (checkpointCell name s cert) parent)).isDead atId = false from hnd,
          Graph.label_add, hlbl]
        simp [restoreRaw_content]
    | some existing =>
      rw [hlbl] at ok
      by_cases hr : (restoreRaw existing).isSome = true
      · simp only [hr, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold Graph.label at hlbl
        unfold Graph.isDead at hnd
        unfold loadRaw Graph.label Graph.isDead
        rw [hnd]
        simp only [Bool.false_eq_true, ↓reduceIte, lookup_map_replace, hlbl, Option.map_some,
          Option.bind_some, restoreRaw_content]
      · simp [hr] at ok

theorem load_allocate
    {g saved : Graph} {atId parent : AtomId} {name : String} {s : State} {cert : StateCert}
    (hok : checkStateCert cert s = true)
    (ok : allocate g atId parent name s cert = some saved) :
    load saved atId = some s := by
  unfold allocate at ok
  by_cases hbad : (atId == root || g.isDead atId) = true
  · simp [hbad] at ok
  · have hbadF : (atId == root || g.isDead atId) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte] at ok
    have hnd : g.isDead atId = false := by
      cases hd : g.isDead atId
      · rfl
      · simp [hd] at hbadF
    cases hlbl : g.label atId with
    | none =>
      rw [hlbl] at ok
      by_cases hp : (parent != root && !g.alive parent) = true
      · simp [hp] at ok
      · have hpF : (parent != root && !g.alive parent) = false := Bool.eq_false_iff.mpr hp
        simp only [hpF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold load
        rw [show (g.step (.add atId (checkpointCell name s cert) parent)).isDead atId = false from hnd,
          Graph.label_add, hlbl]
        simp [restore_content name s cert hok]
    | some existing =>
      rw [hlbl] at ok
      by_cases hr : (restoreRaw existing).isSome = true
      · simp only [hr, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold Graph.label at hlbl
        unfold Graph.isDead at hnd
        unfold load Graph.label Graph.isDead
        rw [hnd]
        simp only [Bool.false_eq_true, ↓reduceIte, lookup_map_replace, hlbl, Option.map_some,
          Option.bind_some, restore_content name s cert hok]
      · simp [hr] at ok

/-- Frame theorem: allocating or advancing `atId` leaves every other atom `other ≠ atId` unchanged. -/
theorem load_allocate_ne
    {g saved : Graph} {atId parent other : AtomId} {name : String} {s : State} {cert : StateCert}
    (ok : allocate g atId parent name s cert = some saved) (hne : other ≠ atId) :
    load saved other = load g other := by
  unfold allocate at ok
  by_cases hbad : (atId == root || g.isDead atId) = true
  · simp [hbad] at ok
  · have hbadF : (atId == root || g.isDead atId) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte] at ok
    cases hlbl : g.label atId with
    | none =>
      rw [hlbl] at ok
      by_cases hp : (parent != root && !g.alive parent) = true
      · simp [hp] at ok
      · have hpF : (parent != root && !g.alive parent) = false := Bool.eq_false_iff.mpr hp
        simp only [hpF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold load
        simp only [Graph.isDead_add, Graph.label_add, hne, ↓reduceIte]
        cases g.label other <;> rfl
    | some existing =>
      rw [hlbl] at ok
      by_cases hr : (restoreRaw existing).isSome = true
      · simp only [hr, ↓reduceIte, Option.some.injEq] at ok
        subst ok
        unfold load Graph.label Graph.isDead
        rw [lookup_map_replace]
        simp [hne]
      · simp [hr] at ok

/-- Advancing an already-live checkpoint cell at `atId` succeeds in place and yields the new state. -/
theorem allocate_advances_live
    {g : Graph} {atId parent : AtomId} {name : String} {prev next : State} {cert : StateCert}
    (hroot : atId ≠ root) (hlive : loadRaw g atId = some prev) :
    ∃ saved, allocate g atId parent name next cert = some saved ∧ loadRaw saved atId = some next := by
  unfold loadRaw at hlive
  cases hd : g.isDead atId with
  | true => simp [hd] at hlive
  | false =>
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hlive
    cases hlbl : g.label atId with
    | none => simp [hlbl] at hlive
    | some existing =>
      simp only [hlbl, Option.bind_some] at hlive
      cases hr : restoreRaw existing with
      | none => simp [hr] at hlive
      | some p =>
        have halloc : allocate g atId parent name next cert =
            some { g with atoms := g.atoms.map fun e =>
              if e.1 == atId then (atId, checkpointCell name next cert) else e } := by
          simp [allocate, hroot, hd, hlbl, hr]
        exact ⟨_, halloc, loadRaw_allocate halloc⟩

/-- A non-checkpoint atom at `atId` is never silently clobbered by `allocate`. -/
theorem allocate_refuses_non_checkpoint
    {g : Graph} {atId parent : AtomId} {name : String} {c : Content} {s : State} {cert : StateCert}
    (hlbl : g.label atId = some c) (hnc : restoreRaw c = none) :
    allocate g atId parent name s cert = none := by
  unfold allocate
  split
  · rfl
  · simp [hlbl, hnc]

def resumeAtRaw (g : Graph) (atId : AtomId) (reply : Term) : Option State :=
  (loadRaw g atId).bind (resume reply)

def resumeAt (g : Graph) (atId : AtomId) (reply : Term) : Option State :=
  (load g atId).bind (resume reply)

theorem resumeAt_typed {A : Assumptions} {types : AddressTypes} {P R T : Ty}
    {g saved : Graph} {atId parent plan : Nat} {name : String}
    (c : Checkpoint A types (.computation P R T))
    (ok : save g atId parent name c = some saved)
    (yielded : c.state.control = .yielded plan) {reply : Term} {uses : Uses}
    (checked : PartialTyping A [] reply R uses) :
    ∃ next, resumeAt saved atId reply = some next ∧ resume reply c.state = some next ∧
      Nonempty (StateTyping A types next (.computation P R T)) := by
  obtain ⟨typed⟩ := c.typed
  have resumed : resume reply c.state = some { c.state with control := .evaluate reply [] } := by
    simp [resume, yielded]
  exact ⟨_, by simp [resumeAt, load_allocate c.verified ok, resumed], resumed,
    Obend.Core.Proofs.Preservation.typed_resume_preserved typed yielded checked resumed⟩

end Obend.Doc.LiveObject
