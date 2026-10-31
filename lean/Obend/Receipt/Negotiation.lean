module
/-
# Obend.Receipt.Negotiation — the receipt of an admitted World transition

The runner's negotiation (`Obend.Run.Negotiation`): its accepted log, judged by `Legal` as the
audited fold `legalAdmission` (`Obend.Run.Fold`). Row 4 of the log is the dispatch of the commitment
to `p2`, admitted at the view where `p1`'s grant is revoked; its receipt is issued here and re-checked
by a consumer holding no producer state.

- Canonical JSON for everything a row and the accumulator's rest carry (protocol trees are unfolded
  over the signature's listed responses, `finite`), decoders for each, and the digest naming roots,
  rows and the law (cSHAKE256, `Obend.Digest`).
- `realize`: a view a stranger builds from the receipt's pins and token opening. Its reads are
  `holdsOfPin` of the recorded pins (`realize_reads`).
- `row4_admitted`, `row4_openings`, `row4_recheck`: the row is admitted; its receipt's openings are
  exactly those the pins compute; at the realized view the stranger's `recheck` accepts it
  (`Obend.Receipt.recheck_issued`, an instance of `Obend.Fold.receipt_sufficient`).
- The view is committed (`nreading`): a Merkle map (cSHAKE256, `Obend.Receipt.Merkle`) over the
  three fact cells, each at its pin (`pinCode`), and the capability's liveness. The receipt is dated
  by its root and carries an opening proof per read: `receipt4_checks` (the stranger's checks pass)
  and `receipt4_dated_verdict` (the verdict is the dated view's, or cSHAKE256 collides). The view
  support is `checked`.
- `envelope`: the protocol envelope judge (`Obend.Judge.Instances.envelope`) on the negotiation's
  template: accepted with the one capability, refused (a refutation: no derivation exists) without it.
-/
public import Obend.Receipt
public import Obend.Run.Negotiation
public import Obend.Run.Fold
public import Obend.Judge.Instances
public import Obend.Digest.Cshake256
public import Lean.Data.Json
import all Obend.Run.Runner
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Negotiation

public section
namespace Obend.Receipt.Negotiation
open Lean (Json ToJson toJson)
open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run Obend.Run.Negotiation
set_option autoImplicit false

/-! ## The fold being receipted -/

abbrev NRest := Obend.Run.Rest sig HoleN Res Tok Fact
abbrev NRow := Event sig HoleN Res Fact Wv
abbrev NRead := Fact ⊕ Tok

/-- `Legal` over the negotiation, as the audited fold. -/
def admission : Obend.Fold.Admission Wv NRest NRow NRead Obend.Run.Clause :=
  legalAdmission host spec O₀.template

/-- The start: the object's substitution, the world where everything holds, nothing cited. -/
def start : Wv × NRest := (acc₀ O₀.σ everything (fun _ _ => [])).toPair

/-- The accepted log of the stranger's example. -/
def log : List NRow := final.cfg.log

/-! ## Digests -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def hex (bytes : List UInt8) : String :=
  String.mk (bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- `OBEND.RECEIPT/v1` -/
def customization : List UInt8 := "OBEND.RECEIPT/v1".toUTF8.toList

/-- The digest of a canonical text. -/
def digest (s : String) : Digest := hex (Obend.Digest.Cshake256.cshake256Bytes customization s.toUTF8.toList)

/-- The digest of a JSON value's canonical form (object keys sorted, no whitespace). -/
def digestJson (j : Json) : Digest := digest j.compress

/-! ## Canonical JSON -/

def providerName : Provider → String
  | .p1 => "p1"
  | .p2 => "p2"

def providerOf : String → Except String Provider
  | "p1" => .ok .p1
  | "p2" => .ok .p2
  | s => .error s!"unknown provider {s}"

def phaseName : Phase → String
  | .idle => "idle"
  | .reserved => "reserved"
  | .done => "done"

def factName : Fact → String
  | .auth p => s!"auth {providerName p}"
  | .beforeDeadline => "beforeDeadline"

def factOf : String → Except String Fact
  | "auth p1" => .ok (.auth .p1)
  | "auth p2" => .ok (.auth .p2)
  | "beforeDeadline" => .ok .beforeDeadline
  | s => .error s!"unknown fact {s}"

def tokName : Tok → String
  | .cap => "cap"

def tokOf : String → Except String Tok
  | "cap" => .ok .cap
  | s => .error s!"unknown token {s}"

def opName : (Σ i, sig.Op i) → String
  | ⟨_, .reserve⟩ => "reserve"
  | ⟨_, .commit p⟩ => s!"commit {providerName p}"
  | ⟨_, .cancel⟩ => "cancel"

def opOf : String → Except String (Σ i, sig.Op i)
  | "reserve" => .ok ⟨.idle, .reserve⟩
  | "commit p1" => .ok ⟨.reserved, .commit .p1⟩
  | "commit p2" => .ok ⟨.reserved, .commit .p2⟩
  | "cancel" => .ok ⟨.reserved, .cancel⟩
  | s => .error s!"unknown operation {s}"

def entryJson : Entry sig → Json
  | ⟨_, .reserve, _⟩ => Json.arr #["reserve", Json.null]
  | ⟨_, .commit p, b⟩ => Json.arr #[toJson s!"commit {providerName p}", toJson (show Bool from b)]
  | ⟨_, .cancel, _⟩ => Json.arr #["cancel", Json.null]

def entryOf (j : Json) : Except String (Entry sig) := do
  let a ← j.getArr?
  let some n := a[0]? | throw "entry: no operation"
  let n ← n.getStr?
  match n with
  | "reserve" => pure ⟨.idle, .reserve, ()⟩
  | "cancel" => pure ⟨.reserved, .cancel, ()⟩
  | _ =>
    let ⟨i, op⟩ ← opOf n
    match i, op with
    | _, .commit p =>
      let some b := a[1]? | throw "entry: no response"
      let b ← b.getBool?
      pure ⟨.reserved, .commit p, (b : Bool)⟩
    | _, _ => throw s!"entry: {n}"

def optJson {α : Type} (f : α → Json) : Option α → Json
  | none => Json.null
  | some a => f a

/-- A protocol tree, unfolded over the listed responses (`finite`). -/
def protJson : {i : Phase} → Prot sig HoleN Res i → Json
  | _, .ret a => Json.mkObj [("ret", toJson (show Bool from a))]
  | i, .call op k => Json.mkObj [("call", toJson (opName ⟨i, op⟩)),
      ("k", Json.arr ((finite.resps op).map fun r => protJson (k r)).toArray)]
  | i, .hole _ => Json.mkObj [("hole", toJson (phaseName i))]

def protOfDone (j : Json) : Except String (Prot sig HoleN Res .done) := do
  if let .ok b := j.getObjValAs? Bool "ret" then return .ret b
  throw "done: only a result"

def protOfReserved (j : Json) : Except String (Prot sig HoleN Res .reserved) := do
  if let .ok b := j.getObjValAs? Bool "ret" then return .ret b
  if let .ok h := j.getObjValAs? String "hole" then
    if h == "reserved" then return .hole (i := Phase.reserved) () else throw "hole: wrong index"
  let n ← j.getObjValAs? String "call"
  let ks ← (← j.getObjVal? "k").getArr?
  match n with
  | "cancel" =>
    let some c := ks[0]? | throw "cancel: no continuation"
    let k ← protOfDone c
    return .call (S := sig) Op.cancel fun _ => k
  | "commit p1" | "commit p2" =>
    let p ← providerOf (n.drop 7).toString
    let some ct := ks[0]? | throw "commit: no continuation"
    let some cf := ks[1]? | throw "commit: no continuation"
    let kt ← protOfDone ct
    let kf ← protOfDone cf
    return .call (S := sig) (Op.commit p) fun b => match (show Bool from b) with
      | true => kt
      | false => kf
  | _ => throw s!"call {n}: not at reserved"

def protOfIdle (j : Json) : Except String (Prot sig HoleN Res .idle) := do
  if let .ok b := j.getObjValAs? Bool "ret" then return .ret b
  let n ← j.getObjValAs? String "call"
  let ks ← (← j.getObjVal? "k").getArr?
  match n with
  | "reserve" =>
    let some c := ks[0]? | throw "reserve: no continuation"
    let k ← protOfReserved c
    return .call (S := sig) Op.reserve fun _ => k
  | _ => throw s!"call {n}: not at idle"

/-- Its decoder. -/
def protOf : (i : Phase) → Json → Except String (Prot sig HoleN Res i)
  | .idle => protOfIdle
  | .reserved => protOfReserved
  | .done => protOfDone

def wvJson (v : Wv) : Json :=
  Json.mkObj [("grant1", toJson v.grant1), ("grant2", toJson v.grant2),
    ("beforeDeadline", toJson v.beforeDeadline), ("capLive", toJson v.capLive), ("clock", toJson v.clock)]

def wvOf (j : Json) : Except String Wv := do
  pure ⟨← j.getObjValAs? Bool "grant1", ← j.getObjValAs? Bool "grant2", ← j.getObjValAs? Bool "beforeDeadline",
    ← j.getObjValAs? Bool "capLive", ← j.getObjValAs? Nat "clock"⟩

/-- The accumulator's rest, canonically. -/
def restJson (r : NRest) : Json :=
  Json.mkObj [
    ("spent", Json.arr (r.spent.map fun t => toJson (tokName t)).toArray),
    ("answered", Json.arr (r.hist.answered.map entryJson).toArray),
    ("inflight", optJson (fun o => toJson (opName o)) r.hist.inflight),
    ("ended", optJson (fun o => toJson (opName o)) r.ended),
    ("plan", optJson protJson (r.plan .reserved ())),
    ("cites", Json.arr ((r.cites .reserved ()).map fun f => toJson (factName f)).toArray)]

def optOf {α : Type} (f : Json → Except String α) : Json → Except String (Option α)
  | .null => .ok none
  | j => (f j).map some

def substOf (p : Option (Prot sig HoleN Res .reserved)) : Subst sig HoleN Res := fun
  | .reserved, () => p
  | .idle, h => nomatch h
  | .done, h => nomatch h

def citesOf' (cs : List Fact) : (j : Phase) → HoleN j → List Fact := fun
  | .reserved, () => cs
  | .idle, h => nomatch h
  | .done, h => nomatch h

def restOf (j : Json) : Except String NRest := do
  let spent ← (← (← j.getObjVal? "spent").getArr?).toList.mapM fun t => do tokOf (← t.getStr?)
  let answered ← (← (← j.getObjVal? "answered").getArr?).toList.mapM entryOf
  let inflight ← optOf (fun o => do opOf (← o.getStr?)) (← j.getObjVal? "inflight")
  let ended ← optOf (fun o => do opOf (← o.getStr?)) (← j.getObjVal? "ended")
  let plan ← optOf (protOf .reserved) (← j.getObjVal? "plan")
  let cites ← (← (← j.getObjVal? "cites").getArr?).toList.mapM fun f => do factOf (← f.getStr?)
  pure ⟨spent, ⟨answered, inflight⟩, ended, substOf plan, citesOf' cites⟩

/-- A row, canonically. -/
def rowJson : NRow → Json
  | .world v => Json.mkObj [("world", wvJson v)]
  | .replan (j := j) _ f cs => match j, f with
    | .reserved, f => Json.mkObj [("replan", Json.mkObj [("hole", toJson "reserved"), ("plan", protJson f),
        ("cites", Json.arr (cs.map fun c => toJson (factName c)).toArray)])]
  | .dispatch o => Json.mkObj [("dispatch", toJson (opName o))]
  | .respond e => Json.mkObj [("respond", entryJson e)]
  | .abandon o => Json.mkObj [("abandon", toJson (opName o))]

def rowOf (j : Json) : Except String NRow := do
  if let .ok w := j.getObjVal? "world" then return .world (← wvOf w)
  if let .ok r := j.getObjVal? "replan" then
    let f ← protOf .reserved (← r.getObjVal? "plan")
    let cs ← (← (← r.getObjVal? "cites").getArr?).toList.mapM fun c => do factOf (← c.getStr?)
    return .replan (j := Phase.reserved) () f cs
  if let .ok o := j.getObjValAs? String "dispatch" then return .dispatch (← opOf o)
  if let .ok e := j.getObjVal? "respond" then return .respond (← entryOf e)
  if let .ok o := j.getObjValAs? String "abandon" then return .abandon (← opOf o)
  throw "unknown row"

def readName : NRead → String
  | .inl f => factName f
  | .inr t => s!"token {tokName t}"

def readOf (s : String) : Except String NRead :=
  match s with
  | "token cap" => .ok (.inr .cap)
  | _ => (factOf s).map .inl

def clauseName : Obend.Run.Clause → String
  | .worldSteps => "worldSteps" | .authorized => "authorized" | .decided => "decided" | .once => "once"
  | .paired => "paired" | .final => "final" | .frozen => "frozen"

def clauseOf : String → Except String Obend.Run.Clause
  | "worldSteps" => .ok .worldSteps | "authorized" => .ok .authorized | "decided" => .ok .decided
  | "once" => .ok .once | "paired" => .ok .paired | "final" => .ok .final | "frozen" => .ok .frozen
  | s => .error s!"unknown clause {s}"

/-! ## Naming -/

/-- The law's identity: the specification and the template, by name and revision. -/
def lawId : String := "obend.run.negotiation: Legal(host, spec, template) / Obend.Run.Fold.legalAdmission v1"

/-- The pins of the world facts a row reads (a token's liveness is the host's, not a pin). -/
def pinsOfReads (w : Wv) (rs : List NRead) : List (Fact × Option (Nat × Bool)) :=
  rs.filterMap fun
    | .inl f => some (f, World.pin (Fact := Fact) w (World.cell f))
    | .inr _ => none

/-! ## The committed view -/

/-- A pin as a number: none is 0, `(clock, value)` is `2·clock + value + 1`. -/
def pinCode : Option (Nat × Bool) → Nat
  | none => 0
  | some (c, b) => 2 * c + (if b then 1 else 0) + 1

def pinDecode : Nat → Option (Nat × Bool)
  | 0 => none
  | n + 1 => some (n / 2, n % 2 == 1)

theorem pinDecode_code (p : Option (Nat × Bool)) : pinDecode (pinCode p) = p := by
  match p with
  | none => rfl
  | some (c, false) =>
    show some ((2 * c + 0) / 2, (2 * c + 0) % 2 == 1) = some (c, false)
    have h1 : (2 * c + 0) / 2 = c := by omega
    have h2 : (2 * c + 0) % 2 = 0 := by omega
    rw [h1, h2]; rfl
  | some (c, true) =>
    show some ((2 * c + 1) / 2, (2 * c + 1) % 2 == 1) = some (c, true)
    have h1 : (2 * c + 1) / 2 = c := by omega
    have h2 : (2 * c + 1) % 2 = 1 := by omega
    rw [h1, h2]; rfl

/-- The schema of the view: the three fact cells and the capability. -/
def viewKeys : List NRead := [.inl (.auth .p1), .inl (.auth .p2), .inl .beforeDeadline, .inr .cap]

/-- **The committed view**: each fact cell at its pin, the capability at its liveness; a committed
value reads as an opening through `holdsOfPin` of the decoded pin, or as the liveness bit. -/
def nreading : Reading Wv NRead NRead where
  C := ⟨viewKeys, fun w k => match k with
    | .inl f => pinCode (World.pin (Fact := Fact) w (World.cell f))
    | .inr _ => if w.capLive then 1 else 0⟩
  key := id
  bit k v := match k with
    | .inl f => World.holdsOfPin (V := Wv) (World.cell f) (pinDecode v) f
    | .inr _ => v == 1

theorem nreading_coherent : nreading.Coherent admission.look := by
  intro w k
  cases k with
  | inl f =>
    show World.holdsOfPin (V := Wv) (World.cell f) (pinDecode (pinCode (World.pin (Fact := Fact) w (World.cell f)))) f =
      admission.look w (.inl f)
    rw [pinDecode_code]; rfl
  | inr t =>
    show ((if w.capLive then 1 else 0) == 1) = w.capLive
    cases w.capLive <;> rfl

def naming : Naming Wv NRest NRow NRead Fact (Nat × Bool) :=
  Naming.ofReading Obend.Core.Digest.deployed nreading (fun r => digestJson (restJson r))
    (fun r => digestJson (rowJson r)) (digest lawId) pinsOfReads

/-! ## The receipt of row 4 -/

/-- The accumulator after the first four rows. -/
def acc4 : Wv × NRest :=
  match admission.run start (log.take 4) with
  | .ok a => a
  | .error _ => start

def row4 : NRow := .dispatch (commitOp .p2)

theorem log_row4 : log[4]? = some row4 := by rfl

theorem prefix_runs : admission.run start (log.take 4) = .ok acc4 := by rfl

/-- **The dispatch of the commitment to `p2` is admitted.** -/
theorem row4_admitted : (admission.step acc4 row4).toBool = true := by rfl

/-- The supports of the receipt: the fold's verdict is a checked re-execution; the view it read is
checked against the dated root (each opening's proof, cSHAKE256 run as compiled code). -/
def trust4 : List (String × Trust) :=
  [("legal-fold", .checked "obend.legal-fold" "1" .compiled), ("view", .checked "obend.merkle-view" "1" .compiled)]

/-- The receipt. `prev` is supplied by the producer's chain. -/
def receipt4 (prev : Digest) : Receipt Fact (Nat × Bool) NRead Obend.Run.Clause :=
  issue admission naming acc4 row4 .existsRun trust4 prev

/-- What it read: `p2`'s grant and the deadline (from the pins), and the capability's liveness. -/
theorem row4_reads : admission.reads acc4 row4 = [.inl (.auth .p2), .inl .beforeDeadline, .inl (.auth .p2),
    .inl .beforeDeadline, .inr .cap] := by rfl

/-! ## The stranger's view, from the pins -/

/-- A view built from pins and a token opening: each world fact takes the value its pin reads by
`holdsOfPin`; unread facts are false; the clock is the pins' clock. -/
def realize (pins : List (Fact × Option (Nat × Bool))) (capLive : Bool) : Wv :=
  let val (f : Fact) : Bool := match pins.lookup f with
    | some p => World.holdsOfPin (V := Wv) f p f
    | none => false
  let clock := match pins.head? with
    | some (_, some (c, _)) => c
    | _ => 0
  ⟨val (.auth .p1), val (.auth .p2), val .beforeDeadline, capLive, clock⟩

/-- The pins of row 4's receipt. -/
def pins4 : List (Fact × Option (Nat × Bool)) := pinsOfReads acc4.1 (admission.reads acc4 row4)

theorem receipt4_pins (prev : Digest) : (receipt4 prev).pins = pins4 := by rfl

theorem pins4_eq : pins4 = [(.auth .p2, some (1, true)), (.beforeDeadline, some (1, true)),
    (.auth .p2, some (1, true)), (.beforeDeadline, some (1, true))] := by rfl

/-- **The realized view's reads are the pins'**: every world fact the receipt pins reads, at the
realized view, as `holdsOfPin` of its recorded pin. -/
theorem realize_reads (prev : Digest) :
    ∀ fp ∈ (receipt4 prev).pins, World.holdsAt (realize (receipt4 prev).pins true) fp.1 =
      World.holdsOfPin (V := Wv) fp.1 fp.2 fp.1 := by
  rw [receipt4_pins]; decide

theorem realize_openings (prev : Digest) :
    ∀ o ∈ (receipt4 prev).openings, admission.look (realize (receipt4 prev).pins true) o.1 = o.2 := by
  rw [receipt4_pins]
  show ∀ o ∈ admission.openings acc4 row4, admission.look (realize pins4 true) o.1 = o.2
  decide

/-- **The stranger's check passes** at the view realized from the receipt's pins (with the token
opening it carries): the verdict and the post root are recomputed from the receipt and the rest. -/
theorem row4_recheck (prev : Digest) :
    recheck admission naming acc4.2 row4 (realize (receipt4 prev).pins true) (receipt4 prev) = true :=
  recheck_issued admission naming acc4 row4 rfl _ _ _ _ (realize_openings prev) (by rw [receipt4_pins]; rfl)

/-- **The stranger's checks of the dated root pass** for the receipt of row 4. -/
theorem receipt4_checks (prev : Digest) :
    datedOpens Obend.Core.Digest.deployed (receipt4 prev) = true ∧ nreading.matched (receipt4 prev) = true :=
  issue_checks Obend.Receipt.Merkle.deployed_bounded admission nreading nreading_coherent (by decide) _ _ _ _
    acc4 row4 (by intro f hf; rw [row4_reads] at hf; simp [nreading, viewKeys] at hf ⊢; rcases hf with h | h | h <;> simp [h])
    _ _ _

/-- **The receipt's verdict is the dated view's**: at any world whose committed view has the
receipt's dated root, row 4 has the receipt's verdict and post root, or cSHAKE256 collides. -/
theorem receipt4_dated_verdict (prev : Digest) (w : Wv) (hd : (receipt4 prev).dated = nreading.C.dated Obend.Core.Digest.deployed w) :
    (Outcome.ofExcept (admission.step (w, acc4.2) row4) = (receipt4 prev).verdict ∧
      postOf admission naming (w, acc4.2) row4 = (receipt4 prev).post) ∨
      Obend.Digest.HashBytes.Collision Obend.Core.Digest.deployed :=
  dated_verdict Obend.Receipt.Merkle.deployed_bounded admission naming nreading nreading_coherent acc4 row4 rfl w hd
    (receipt4_checks prev).1 (receipt4_checks prev).2

/-! ## Astra's outcomes, where they apply -/

section Control
open Obend.Run.Control
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {P Cand Tok' Fact' : Type}

/-- A controlled session's refusal as a receipt outcome: the selection's own outcomes become
Astra's constructors (a chooser-required wait is not a failed support; a kept preference forges no
failure; a frozen execution names its recorded dispatch); every other refusal is refused by its
clause. -/
def controlOutcome : CRefusal S Hole P Cand Tok' Fact' → Outcome (CRefusal S Hole P Cand Tok' Fact')
  | .nothingAdmissible .. => .noAdmissible
  | .awaiting .. => .awaitingChoice
  | .noOverride .. => .preferenceKept
  | .unusable .. | .notPermitted .. => .candidateRejected
  | .run (.unsupported ..) => .staleEvidence
  | .run (.replacesInflight ..) | .run (.replacesAnswered ..) | .run (.abandoned ..) => .executionFrozen
  | k => .refused k []

end Control

/-- **The stranger's example, as outcomes**: the refused commitment on `p1` is refused by its clause;
the three re-plans while the commitment to `p2` is in flight and the three events after it is
abandoned are `executionFrozen`, not failures of the candidates. -/
theorem script_outcomes :
    ((nsession spec c₀ script).2.map fun r => r.map controlOutcome).map (fun o => o.map Outcome.isOk) =
      [none, none, none, some false, none, none, none, some false, some false, some false, some false,
        some false, none, some false, none, some false, some false, some false, none] ∧
    ((nsession spec c₀ script).2.filterMap id |>.map controlOutcome |>.filter
      (fun o => match o with | .executionFrozen => true | _ => false)).length = 6 := by
  decide

/-! ## The protocol envelope on the negotiation's template -/

/-- The negotiation's envelope: its finite responses, every result allowed. -/
def env : Obend.Judge.Instances.Envelope sig HoleN Res Tok Fact Ob where
  fin := finite
  ixs := [.idle, .reserved, .done]
  ixs_complete j := by cases j <;> simp
  res _ := [true, false]
  res_complete _ a := by cases a <;> simp
  sp := spec
  Ω := Ω
  Γ := Γ₀
  Qb _ _ := true
  Φ := Φ₀
  postB _ _ _ _ := true
  post_iff i h I hI j a := by
    cases i with
    | reserved => cases h; simp only [Ω, Option.some.injEq] at hI; subst hI; simp [iface]
    | idle => exact nomatch h
    | done => exact nomatch h

theorem template_checks : Obend.Judge.Instances.checkProt env Δ₀ template = true := by decide

theorem template_fails : Obend.Judge.Instances.checkProt env [] template = false := by decide

/-- The template with the capability: typed. -/
theorem template_enveloped :
    (Obend.Judge.Instances.envelope env).check 0 ⟨Δ₀, .idle, template⟩ () = .ok := by
  change (if Obend.Judge.Instances.checkProt env Δ₀ template = true then _ else _) = _
  rw [template_checks]; rfl

/-- Without the capability the hole's interface (which may spend it) is refused, and the refusal is a
refutation: no derivation exists. -/
theorem template_refused :
    (Obend.Judge.Instances.envelope env).check 0 ⟨[], .idle, template⟩ () = .refused .untyped [] := by
  change (if Obend.Judge.Instances.checkProt env [] template = true then _ else _) = _
  rw [template_fails]; rfl

theorem template_untyped : ¬ env.Typed [] template :=
  (Obend.Judge.Instances.envelope env).refuted template_refused rfl ()

end Obend.Receipt.Negotiation
end
