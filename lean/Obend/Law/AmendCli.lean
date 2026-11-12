module
public import Obend.Law.PointwiseRevise
public import Lean.Data.Json
import all Obend.Law.PointwiseRevise
import all Obend.Hardware.SiliconOuroboros
import all Obend.Hardware.DprStutter
import all Obend.Judge.SvenvsCorrigibility
import all Obend.Judge.CertifierRatchet
import all Obend.Logic.SeparationFrame

public section
namespace Obend.Law.AmendCli
open PointwiseRevise Lean
open Obend.Hardware.DprStutter Obend.Hardware.SiliconOuroboros
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet
open Obend.Logic
set_option autoImplicit false

/-! Workflow engine, callable without changing the executable's command dispatcher.
The concrete demo has sixteen transition configurations: fee bit, recovery bit,
production bit, and unbacked-mint bit. JSON contains truth tables over these
configurations. Protocol meanings and the immutable floor are compiled code.
DPR receipts contain the existing canonical transport frames, not vendor bytes. -/
def recoveryEnabled (v : Fin 16) : Bool := decide (v.val / 2 % 2 = 1)
def productionEnabled (v : Fin 16) : Bool := decide (v.val / 4 % 2 = 1)
def backedValue (v : Fin 16) : Bool := decide (v.val < 8)
def checkBedrock (v : Fin 16) : Bool := recoveryEnabled v && productionEnabled v && backedValue v

example : ∃ v : Fin 16, checkBedrock v = true := ⟨6, by decide⟩
example : checkBedrock 14 = false := by decide

def bedrock : Bedrock 16 := ⟨checkBedrock, 6, by decide⟩
def fee (v : Fin 16) : Nat := 1 + v.val % 2

def protocolStep (v : Fin 16) (s : HWState) (a : HWAct) : HWState :=
  if productionEnabled v then hwStep s a else 3

def protocolRecovery (v : Fin 16) (s : HWState) : HWAct :=
  if recoveryEnabled v then hwRoot s else 0

/-- Canonical two-account ledger for the cumulative settled fee. The proofs
are structural and do not import a choice-dependent sorting implementation. -/
def feeLedger (amount : Nat) : ConservedValue :=
  if h : amount = 0 then ⟨[], ⟨.nil, fun _ hm => by cases hm⟩, rfl⟩
  else
    { entries := [(0, -(Int.ofNat amount)), (1, Int.ofNat amount)]
      wf := by
        constructor
        · apply List.Pairwise.cons
          · intro p hp
            cases hp with
            | head => exact Nat.zero_lt_succ 0
            | tail _ hp => cases hp
          · exact .cons (fun _ hp => by cases hp) .nil
        · intro p hp
          cases hp with
          | head =>
            change -(Int.ofNat amount) ≠ 0
            exact fun hz => h (Int.ofNat_eq_zero.mp (Int.neg_eq_zero.mp hz))
          | tail _ hp =>
            cases hp with
            | head =>
              change Int.ofNat amount ≠ 0
              exact Int.ofNat_ne_zero.mpr h
            | tail _ hp => cases hp
      conserved := by change -(Int.ofNat amount) + (Int.ofNat amount + 0) = 0; omega }

def rawValue (v : Fin 16) : List (Nat × Int) :=
  if backedValue v then (feeLedger (fee v)).entries else [(0, 1)]

theorem bedrock_components (v : Fin 16) (h : checkBedrock v = true) :
    recoveryEnabled v = true ∧ productionEnabled v = true ∧ backedValue v = true := by
  simpa [checkBedrock, Bool.and_eq_true, and_assoc] using h

theorem bedrock_recovery (v : Fin 16) (h : checkBedrock v = true) (s : HWState) :
    DemonicRecovWithin (Det (protocolStep v)) (protocolRecovery v) (fun x => x = 0) 1 s := by
  have hc := bedrock_components v h
  have he : protocolStep v = hwStep := by funext t a; simp [protocolStep, hc.2.1]
  have hr : protocolRecovery v = hwRoot := by funext t; simp [protocolRecovery, hc.1]
  rw [he, hr]
  exact hw_root_recovery s

theorem bedrock_viable (v : Fin 16) (h : checkBedrock v = true) (s : HWState)
    (hs : hwSafe s) : ViableKernel (protocolStep v) hwSafe s := by
  refine ⟨hwSafe, hs, fun _ ht => ht, ?_⟩
  intro t _
  refine ⟨1, ?_⟩
  simp [protocolStep, (bedrock_components v h).2.1, hwStep, hwSafe]

theorem bedrock_conserved (v : Fin 16) (h : checkBedrock v = true) : sumDeltas (rawValue v) = 0 := by
  simpa [rawValue, (bedrock_components v h).2.2] using
    (feeLedger (fee v)).conserved

def protocolMeaning : ProtocolMeaning bedrock HWState HWAct where
  step := protocolStep
  safe := hwSafe
  home := fun s => s = 0
  recover := protocolRecovery
  latency := 1
  recovery v hv s _ := bedrock_recovery v hv s
  viable := bedrock_viable
  value v := feeLedger (fee v)

/-- Bit zero selects whether the ordinary transaction action is enabled.
Recovery action 1 remains executable; action 0 at state 0 advances to state 1. -/
def modelPolicy (v : Fin 16) (s : HWState) (a : HWAct) : Bool :=
  decide (a = 1 ∨ (v.val % 2 = 1 ∧ s = 0 ∧ a = 0))

theorem modelPolicy_safe (v : Fin 16) : SoundPolicy hwStep hwSafe (modelPolicy v) := by
  intro s a hs hp
  have hh := of_decide_eq_true hp
  rcases hh with rfl | ⟨_, rfl, rfl⟩ <;> simp [hwStep, hwSafe]

def modelTiles (v : Fin 16) : Array TechmappedTile := lowerPolicyToTiles (modelPolicy v)
def modelFrames (v : Fin 16) : Array TileFrame := encodeTileFrames (modelTiles v)

theorem modelFrames_decode (v : Fin 16) :
    decodeTileFrames (modelTiles v).size (modelFrames v) = some (modelTiles v) :=
  decodeTileFrames_encodeTileFrames _

/-- Bounded schema parser. Fuel is derived from input length; every recursive
call consumes fuel. Strings track escapes explicitly, including surrogate pairs.
The bundle grammar uses natural numbers, strings, objects and arrays only. -/
inductive BundleValue where
  | text (s : String)
  | nat (n : Nat)
  | array (xs : List BundleValue)
  | object (xs : List (String × BundleValue))

def jsonSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'
def skipSpace (xs : List Char) : List Char := xs.dropWhile jsonSpace

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def requireSome {α : Type} (x : Option α) (err : String) : Except String α :=
  match x with | some a => .ok a | none => .error err

def hexQuad : List Char → Except String (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    let a ← requireSome (hexDigit a) "bad unicode escape"
    let b ← requireSome (hexDigit b) "bad unicode escape"
    let c ← requireSome (hexDigit c) "bad unicode escape"
    let d ← requireSome (hexDigit d) "bad unicode escape"
    return (4096*a + 256*b + 16*c + d, rest)
  | _ => .error "short unicode escape"

def unicodeEscape (xs : List Char) : Except String (Char × List Char) := do
  let (u, rest) ← hexQuad xs
  if 0xD800 ≤ u ∧ u < 0xDC00 then
    match rest with
    | '\\' :: 'u' :: tail =>
      let (lo, tail) ← hexQuad tail
      if 0xDC00 ≤ lo ∧ lo < 0xE000 then
        return (Char.ofNat (0x10000 + (u - 0xD800)*1024 + lo - 0xDC00), tail)
      else throw "invalid low surrogate"
    | _ => throw "missing low surrogate"
  else if 0xDC00 ≤ u ∧ u < 0xE000 then throw "unpaired low surrogate"
  else return (Char.ofNat u, rest)

def quotedString : Nat → List Char → List Char → Except String (String × List Char)
  | 0, _, _ => .error "string limit"
  | _+1, [], _ => .error "unterminated string"
  | fuel+1, c :: rest, acc =>
    if c == '"' then .ok (String.ofList acc.reverse, rest)
    else if c == '\\' then
      match rest with
      | [] => .error "unterminated escape"
      | e :: tail => do
        let (decoded, tail) ← match e with
          | '"' => pure ('"', tail)
          | '\\' => pure ('\\', tail)
          | '/' => pure ('/', tail)
          | 'b' => pure (Char.ofNat 8, tail)
          | 'f' => pure (Char.ofNat 12, tail)
          | 'n' => pure ('\n', tail)
          | 'r' => pure ('\r', tail)
          | 't' => pure ('\t', tail)
          | 'u' => unicodeEscape tail
          | _ => .error "invalid escape"
        quotedString fuel tail (decoded :: acc)
    else if c.toNat < 32 then .error "unescaped control character"
    else quotedString fuel rest (c :: acc)

mutual
  def bundleValue : Nat → List Char → Except String (BundleValue × List Char)
    | 0, _ => .error "nesting limit"
    | fuel+1, input =>
      match skipSpace input with
      | '"' :: rest => do
        let (v, tail) ← quotedString (fuel+1) rest []
        return (.text v, tail)
      | '[' :: rest =>
        match skipSpace rest with
        | ']' :: tail => .ok (.array [], tail)
        | more => bundleArray fuel more []
      | '{' :: rest =>
        match skipSpace rest with
        | '}' :: tail => .ok (.object [], tail)
        | more => bundleObject fuel more []
      | c :: rest =>
        if c.isDigit then
          let digits := rest.takeWhile Char.isDigit
          if c == '0' && !digits.isEmpty then .error "leading zero"
          else .ok (.nat ((c :: digits).foldl (fun n d => n*10 + d.toNat - '0'.toNat) 0),
            rest.dropWhile Char.isDigit)
        else .error "expected bundle value"
      | [] => .error "missing value"
  def bundleArray : Nat → List Char → List BundleValue → Except String (BundleValue × List Char)
    | 0, _, _ => .error "array limit"
    | fuel+1, input, acc => do
      let (v, tail) ← bundleValue fuel input
      match skipSpace tail with
      | ']' :: rest => return (.array (v :: acc).reverse, rest)
      | ',' :: rest => bundleArray fuel rest (v :: acc)
      | _ => throw "expected comma or array close"
  def bundleObject : Nat → List Char → List (String × BundleValue) → Except String (BundleValue × List Char)
    | 0, _, _ => .error "object limit"
    | fuel+1, input, acc =>
      match skipSpace input with
      | '"' :: rest => do
        if acc.length ≥ 3 then throw "bundle objects have at most three fields"
        let (key, tail) ← quotedString fuel rest []
        if acc.any (fun p => p.1 == key) then throw "duplicate object key"
        match skipSpace tail with
        | ':' :: more =>
          let (v, tail) ← bundleValue fuel more
          match skipSpace tail with
          | '}' :: rest => return (.object ((key,v) :: acc).reverse, rest)
          | ',' :: rest => bundleObject fuel rest ((key,v) :: acc)
          | _ => throw "expected comma or object close"
        | _ => throw "expected colon"
      | _ => .error "expected object key"
end

def bundleField (j : BundleValue) (key : String) : Except String BundleValue :=
  match j with
  | .object xs => requireSome ((xs.find? (fun p => p.1 == key)).map Prod.snd) ("missing " ++ key)
  | _ => .error "expected object"
def bundleNat : BundleValue → Except String Nat
  | .nat n => .ok n
  | _ => .error "expected natural number"
def bundleText : BundleValue → Except String String
  | .text s => .ok s
  | _ => .error "expected string"
def bundleList : BundleValue → Except String (List BundleValue)
  | .array xs => .ok xs
  | _ => .error "expected array"

def clauseOfBundle (j : BundleValue) : Except String (Clause 16) := do
  let name ← bundleText (← bundleField j "name")
  let priority ← bundleNat (← bundleField j "priority")
  let mask ← bundleNat (← bundleField j "allowed")
  if mask < 65536 then return ⟨name, priority, BitVec.ofNat 16 mask⟩
  else throw "allowed must be a 16-bit truth table"

/-- UTF-8 decoding from bytes uses explicit scalar bounds, including overlong
and surrogate rejection. No partial decoder or classical witness extraction. -/
def utf8Scalar (bytes : ByteArray) (pos : Nat) : Option (Char × Nat) :=
  let a := (bytes[pos]?.getD 0).toNat
  let b := (bytes[pos+1]?.getD 0).toNat
  let c := (bytes[pos+2]?.getD 0).toNat
  let d := (bytes[pos+3]?.getD 0).toNat
  let cont := fun x => 128 ≤ x ∧ x < 192
  if pos ≥ bytes.size then none
  else if a < 128 then some (Char.ofNat a, 1)
  else if 194 ≤ a ∧ a < 224 ∧ cont b then
    some (Char.ofNat ((a-192)*64 + b-128), 2)
  else if 224 ≤ a ∧ a < 240 ∧ cont b ∧ cont c then
    let u := (a-224)*4096 + (b-128)*64 + c-128
    if 2048 ≤ u ∧ (u < 0xD800 ∨ 0xE000 ≤ u) then some (Char.ofNat u, 3) else none
  else if 240 ≤ a ∧ a < 245 ∧ cont b ∧ cont c ∧ cont d then
    let u := (a-240)*262144 + (b-128)*4096 + (c-128)*64 + d-128
    if 65536 ≤ u ∧ u ≤ 0x10FFFF then some (Char.ofNat u, 4) else none
  else none

def decodeBundleChars (bytes : ByteArray) : Nat → Nat → List Char → Except String (List Char)
  | 0, _, _ => .error "UTF-8 limit"
  | fuel+1, pos, acc =>
    if pos < bytes.size then
      match utf8Scalar bytes pos with
      | none => .error "invalid UTF-8"
      | some (c, width) => decodeBundleChars bytes fuel (pos + width) (c :: acc)
    else .ok acc.reverse

def parseAmendBundleJson (text : String) : Except String (AmendmentTurn 16) := do
  let input ← decodeBundleChars text.toByteArray (text.utf8ByteSize + 1) 0 []
  let (j, tail) ← bundleValue (4 * input.length + 16) input
  if !(skipSpace tail).isEmpty then throw "trailing content"
  let version ← bundleNat (← bundleField j "version")
  if version != 1 then throw "unsupported amendment bundle version"
  let slot ← bundleNat (← bundleField j "slot")
  let clauses ← (← bundleList (← bundleField j "clauses")).mapM clauseOfBundle
  return ⟨slot, clauses⟩

def clauseJson (c : Clause 16) : Json := Json.mkObj
  [("name", toJson c.name), ("priority", toJson c.priority), ("allowed", toJson c.allowed.toNat)]

def renderAmendBundleJson (t : AmendmentTurn 16) : String := (Json.mkObj
  [("version", toJson (1 : Nat)), ("slot", toJson t.slot),
   ("clauses", .arr (t.clauses.toArray.map clauseJson))]).compress

structure LiveState where
  world : World 16
  fabric : Nat → DprFabric
  transferred : Nat
  generations : Nat

def LiveState.value (st : LiveState) : ConservedValue := feeLedger st.transferred

structure AmendReceipt where
  slot : Nat
  revision : Revision 16
  evicted : SpecTheory 16
  skipped : List String
  frames : Array TileFrame
  deriving Repr

def checkedSkip (w : World 16) (t : AmendmentTurn 16) (c : ModuleCert 16) : Option (ModuleCert 16) :=
  if moduleUsable w c then skipModule t c else none

theorem checkedSkip_complete (w : World 16) (t : AmendmentTurn 16) (c : ModuleCert 16)
    (hu : moduleUsable w c = true) (hd : t.slot ∉ c.footprint) :
    checkedSkip w t c = some c := by simp [checkedSkip, skipModule, hu, hd]

theorem checkedSkip_sound (w : World 16) (t : AmendmentTurn 16) (c out : ModuleCert 16)
    (h : checkedSkip w t c = some out) :
    out = c ∧ moduleUsable (applyTurn bedrock w t) out = true ∧
    ∀ k ∈ out.footprint, (applyTurn bedrock w t k).clauses = (w k).clauses := by
  unfold checkedSkip at h
  split at h
  · next hu =>
    unfold skipModule at h
    split at h
    · cases h
    · next hd =>
      have he := Option.some.inj h
      subst out
      have hf := pointwiseRevise_supportSheaf_frame_skip bedrock w t c hd hu
      exact ⟨rfl, hf.2.1, hf.2.2⟩
  · cases h

def skippedModules (w : World 16) (t : AmendmentTurn 16) (certs : List (ModuleCert 16)) : List String :=
  certs.filterMap fun c => (checkedSkip w t c).map ModuleCert.payload

def executeLiveAmendment (st : LiveState) (t : AmendmentTurn 16)
    (certs : List (ModuleCert 16)) : LiveState × AmendReceipt :=
  let result := pointwiseRevise bedrock (st.world t.slot).clauses t.clauses
  match result with
  | .accepted v R =>
    let frames := modelFrames v
    let next : LiveState :=
      { world := applyTurn bedrock st.world t
        fabric := fun k => if k = t.slot then siliconDoInstall (st.fabric k) frames else st.fabric k
        transferred := st.transferred + fee v
        generations := st.generations + 1 }
    (next, ⟨t.slot, .accepted v R,
      (st.world t.slot).clauses.filter (fun c => !holds c v), skippedModules st.world t certs, frames⟩)
  | .refused v R cost => (st, ⟨t.slot, .refused v R cost, [], [], #[]⟩)

def renderAmendReceiptJson (r : AmendReceipt) : String :=
  let common := [("slot", toJson r.slot), ("skippedModules", toJson r.skipped)]
  let fields := match r.revision with
    | .accepted v R =>
      [("status", toJson "accepted"), ("witness", toJson v.val),
       ("bedrockViable", toJson true), ("certificate", toJson "bedrock_recovery+bedrock_viable+bedrock_conserved"),
       ("preserved", .arr (R.toArray.map clauseJson)),
       ("evicted", .arr (r.evicted.toArray.map clauseJson)),
       ("frames", .arr (r.frames.map fun f => Json.mkObj
         [("payload", toJson f.payload.toNat), ("crc", toJson f.crc.toNat)]))]
    | .refused v R cost =>
      [("status", toJson "refused"), ("bedrockViable", toJson false),
       ("counterWitness", toJson v.val), ("counterBedrockViable", toJson true),
       ("counterAmendment", .arr (R.toArray.map clauseJson)),
       ("minimumCost", toJson cost), ("certificate", toJson "pointwiseRevise_refusal_optimal")]
  (Json.mkObj (common ++ fields)).compress

theorem execute_revision (st : LiveState) (t : AmendmentTurn 16) (cs : List (ModuleCert 16)) :
    (executeLiveAmendment st t cs).2.revision =
      pointwiseRevise bedrock (st.world t.slot).clauses t.clauses := by
  unfold executeLiveAmendment
  cases pointwiseRevise bedrock (st.world t.slot).clauses t.clauses <;> rfl

theorem execute_acceptance_sound (st : LiveState) (t : AmendmentTurn 16)
    (cs : List (ModuleCert 16)) (v : Fin 16) (R : SpecTheory 16)
    (h : (executeLiveAmendment st t cs).2.revision = .accepted v R) :
    checkBedrock v = true ∧ models t.clauses v = true ∧
    (executeLiveAmendment st t cs).2.frames = modelFrames v := by
  have hr := (execute_revision st t cs).symm.trans h
  refine ⟨pointwiseRevise_entails_bedrock hr, pointwiseRevise_entails_amendment hr, ?_⟩
  simp [executeLiveAmendment, hr]

theorem execute_refusal_sound (st : LiveState) (t : AmendmentTurn 16)
    (cs : List (ModuleCert 16)) (v : Fin 16) (R : SpecTheory 16) (cost : Nat)
    (h : (executeLiveAmendment st t cs).2.revision = .refused v R cost) :
    (executeLiveAmendment st t cs).1 = st ∧ checkBedrock v = true ∧ models R v = true ∧
    ∀ T, T.Sublist t.clauses → ∀ u, checkBedrock u = true → models T u = true →
      cost ≤ weight t.clauses - weight T := by
  have hr := (execute_revision st t cs).symm.trans h
  have ho := pointwiseRevise_refusal_optimal hr
  exact ⟨by simp [executeLiveAmendment, hr], ho.2.1, ho.2.2.1, ho.2.2.2.2.2⟩

structure LiveSafe (st : LiveState) : Prop where
  bedrock : ∀ k, checkBedrock (st.world k).model = true
  active : ∀ k, (st.fabric k).phase = .active
  bank : ∀ k, (st.fabric k).activeTiles = modelTiles (st.world k).model

/-- An accepted installation executes all three physical clock edges. Neighbors
continue clocking during isolation/loading; the target boundary is latched. -/
theorem execute_install_safe (st : LiveState) (t : AmendmentTurn 16)
    (cs : List (ModuleCert 16)) (hs : LiveSafe st) (v : Fin 16) (R : SpecTheory 16)
    (h : (executeLiveAmendment st t cs).2.revision = .accepted v R) :
    (executeLiveAmendment st t cs).1.fabric t.slot = siliconDoInstall (st.fabric t.slot) (modelFrames v) ∧
    Obend.Category.StepTrace abstractNeighborStepSys (st.fabric t.slot).neighbors
      (installActions (st.fabric t.slot) (modelFrames v))
      ((executeLiveAmendment st t cs).1.fabric t.slot).neighbors ∧
    observedBoundaryPort (stepDprFabric (stepDprFabric (st.fabric t.slot) .isolateClamped)
      (.loadFrames (modelFrames v))) = observedBoundaryPort (st.fabric t.slot) := by
  have hr := (execute_revision st t cs).symm.trans h
  have size : (modelTiles v).size = (st.fabric t.slot).activeTiles.size := by
    rw [hs.bank]; rfl
  have hi := silicon_do_install_stutter_safe (st.fabric t.slot) (modelTiles v) (hs.active _) size
  refine ⟨by simp [executeLiveAmendment, hr], ?_, hi.2.2.1⟩
  simpa [executeLiveAmendment, hr, modelFrames] using hi.2.2.2.1

theorem execute_preserves (st : LiveState) (t : AmendmentTurn 16)
    (cs : List (ModuleCert 16)) (hs : LiveSafe st) : LiveSafe (executeLiveAmendment st t cs).1 := by
  unfold executeLiveAmendment
  cases hr : pointwiseRevise bedrock (st.world t.slot).clauses t.clauses with
  | refused v R cost => exact hs
  | accepted v R =>
    have size : (modelTiles v).size = (st.fabric t.slot).activeTiles.size := by
      rw [hs.bank]; rfl
    have hi := silicon_do_install_stutter_safe (st.fabric t.slot) (modelTiles v) (hs.active _) size
    refine ⟨applyTurn_safe bedrock st.world t hs.bedrock, ?_, ?_⟩
    · intro k
      by_cases hk : k = t.slot
      · subst k; simpa [modelFrames] using hi.1
      · simpa [hk] using hs.active k
    · intro k
      by_cases hk : k = t.slot
      · subst k; simpa [applyTurn, hr, modelFrames] using hi.2.1
      · simpa [hk, applyTurn_frame bedrock st.world t k hk] using hs.bank k

def executeTrace (st : LiveState) : List (AmendmentTurn 16) → LiveState
  | [] => st
  | t :: ts => executeTrace (executeLiveAmendment st t []).1 ts

theorem executeTrace_safe (st : LiveState) (ts : List (AmendmentTurn 16))
    (hs : LiveSafe st) : LiveSafe (executeTrace st ts) := by
  induction ts generalizing st with
  | nil => exact hs
  | cons t ts ih => exact ih _ (execute_preserves st t [] hs)

/-- At every count, generation counters, actual banks, and accumulated ledger
value are carried forward. Refusal performs no install and no ledger write. -/
theorem executeTrace_protocol_safe (st : LiveState) (ts : List (AmendmentTurn 16))
    (hs : LiveSafe st) (count k : Nat) (s : HWState) (hstate : hwSafe s) :
    let next := executeTrace st (ts.take count)
    ViableKernel (protocolStep (next.world k).model) hwSafe s ∧
    DemonicRecovWithin (Det (protocolStep (next.world k).model))
      (protocolRecovery (next.world k).model) (fun x => x = 0) 1 s ∧
    sumDeltas next.value.entries = 0 ∧ (next.fabric k).phase = .active ∧
    (next.fabric k).activeTiles = modelTiles (next.world k).model := by
  have h := executeTrace_safe st (ts.take count) hs
  exact ⟨bedrock_viable _ (h.bedrock k) s hstate, bedrock_recovery _ (h.bedrock k) s,
    (executeTrace st (ts.take count)).value.conserved, h.active k, h.bank k⟩

/-- Physical action log projected onto a chosen slot. Other slots and refused
amendments contribute no clock edges to this fabric. -/
def executeActions (st : LiveState) (t : AmendmentTurn 16) (k : Nat) : List FabricAction :=
  match pointwiseRevise bedrock (st.world t.slot).clauses t.clauses with
  | .accepted v _ => if k = t.slot then installActions (st.fabric k) (modelFrames v) else []
  | .refused _ _ _ => []

theorem execute_neighbors (st : LiveState) (t : AmendmentTurn 16) (k : Nat) :
    Obend.Category.StepTrace abstractNeighborStepSys (st.fabric k).neighbors
      (executeActions st t k) ((executeLiveAmendment st t []).1.fabric k).neighbors := by
  unfold executeActions executeLiveAmendment
  cases pointwiseRevise bedrock (st.world t.slot).clauses t.clauses with
  | refused v R cost => exact .nil _
  | accepted v R =>
    by_cases hk : k = t.slot
    · simpa [hk] using install_neighbors (st.fabric k) (modelFrames v)
    · simpa [hk] using (Obend.Category.StepTrace.nil (sys := abstractNeighborStepSys) (st.fabric k).neighbors)

def traceActions (st : LiveState) (k : Nat) : List (AmendmentTurn 16) → List FabricAction
  | [] => []
  | t :: ts => executeActions st t k ++ traceActions (executeLiveAmendment st t []).1 k ts

private theorem append_neighbor_trace {s t u : NeighborState} {xs ys : List FabricAction}
    (h₁ : Obend.Category.StepTrace abstractNeighborStepSys s xs t)
    (h₂ : Obend.Category.StepTrace abstractNeighborStepSys t ys u) :
    Obend.Category.StepTrace abstractNeighborStepSys s (xs ++ ys) u := by
  induction h₁ with
  | nil => exact h₂
  | cons edge _ ih => exact .cons edge (ih h₂)

theorem executeTrace_neighbors (st : LiveState) (ts : List (AmendmentTurn 16)) (k : Nat) :
    Obend.Category.StepTrace abstractNeighborStepSys (st.fabric k).neighbors
      (traceActions st k ts) ((executeTrace st ts).fabric k).neighbors := by
  induction ts generalizing st with
  | nil => exact .nil _
  | cons t ts ih => exact append_neighbor_trace (execute_neighbors st t k) (ih _)

theorem executeTrace_atomic (st : LiveState) (ts : List (AmendmentTurn 16)) (k : Nat)
    (hs : LiveSafe st) :
    LiveSafe (executeTrace st ts) ∧
    Obend.Category.StepTrace abstractNeighborStepSys (st.fabric k).neighbors
      (traceActions st k ts) ((executeTrace st ts).fabric k).neighbors :=
  ⟨executeTrace_safe st ts hs, executeTrace_neighbors st ts k⟩

end Obend.Law.AmendCli
