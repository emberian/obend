module
/-
# Obend.Logic.Obligation — a claim is a slot whose candidates are certificates

`review/PROGRAM-LOGIC-20261101.md` §4.2, §4.3, §5.2. Every claim of a composition is a slot
(`Obend.Slot`): its candidates are rewrite derivations, a candidate's supports are the members it
unfolds with what each unfolded to (`supports`), its judge is the claim checker, and a view is a
composition. The status of a claim is the slot's read of its selection at the view
(`readStatus`): `unchecked` (no candidate), `checked` (usable), `blocked` naming exactly the dead
supports (`status_blocked_exact`, from `Slot.read_blocked_exact`), `refuted` at a ground instance,
or `attested`. A usable read at a view is an accepted check there (`usable_checks`, through T3).

The certificate is tied to its claim by the claim's content address (`Core.Code.address (quote c)`,
`digest_of_quote`): the registered format `claimFormat` (`rewrite@1`) decodes a statement only when
its stated address is the quoted claim's, so a certificate presented with another claim is refused
`malformed` before any step runs. Statements, certificates and receipts are JSON, terms as their
quotations (`Data` on the wire, `Spec.DataWire`).
-/
public import Obend.Logic.Frame
public import Obend.Logic.Ground
public import Obend.Slot
public import Obend.Spec.DataWire
public import Obend.Judge.Lrat
public import Obend.Judge.Clearing
public import Obend.Tactic.Tooth
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Lean (Json toJson)
set_option autoImplicit false

/-! ## The claim judge -/

theorem liftVerdict_ne {v : Judge.Verdict RClause} (h : liftVerdict v ≠ .uncovered) : v ≠ .uncovered := by
  cases v <;> simp_all [liftVerdict]

theorem claimCheck_mono {k k' : Nat} {o : ClaimObj} {steps : List RStep} (le : k ≤ k')
    (hne : claimCheck k o steps ≠ .uncovered) : claimCheck k' o steps = claimCheck k o steps := by
  unfold claimCheck at hne ⊢
  by_cases hw : o.wellFormed = true
  · simp only [hw, ite_true] at hne ⊢
    cases hs : o.sides with
    | none => rfl
    | some x =>
      obtain ⟨_, l, r⟩ := x
      rw [hs] at hne
      simp only
      rw [rewriteWith_mono le (liftVerdict_ne hne)]
  · simp only [hw] at hne ⊢; rfl

/-- **The claim judge.** Objects are claims of compositions, certificates derivations. It never
refutes: the ground judge does. -/
instance claimJudge : Judge ClaimObj (List RStep) where
  Clause := ClaimClause
  Meaning o _ := claimMeaning o
  check := claimCheck
  sound := by intro k o steps h; exact claim_sound h
  refutes _ := false
  refuted := by intro _ _ _ _ _ h hk; cases hk
  Fragment o := ∃ steps k, claimCheck k o steps = .ok
  complete := by rintro o ⟨steps, k, h⟩ _; exact ⟨steps, k, h⟩
  mono := by intro k k' o steps le hne; exact claimCheck_mono le hne

/-! ## Supports -/

/-- A support: a member the derivation unfolds, with the provider and body it unfolded to. -/
structure Support where
  member : String
  unfolded : Option (String × Term)

def optEq : Option (String × Term) → Option (String × Term) → Bool
  | none, none => true
  | some (a, t), some (b, u) => a == b && Obend.Law.termEq t u
  | _, _ => false

theorem optEq_sound {x y : Option (String × Term)} (h : optEq x y = true) : x = y := by
  match x, y, h with
  | none, none, _ => rfl
  | some (a, t), some (b, u), h =>
    simp only [optEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, termEq_sound' h.2]

/-- The supports of a derivation for a claim. -/
def supports (o : ClaimObj) (steps : List RStep) : List Support :=
  (membersList steps).map fun m => ⟨m, symUnfold o.comp o.self m⟩

/-- A support holds at a view (a composition) when the member unfolds there as it did. -/
def Support.holds (C : Composition) (s : Nat) (sp : Support) : Bool := optEq (symUnfold C s sp.member) sp.unfolded

/-- The claim's slot at grade `k`. -/
def claimSlot (o : ClaimObj) (k : Nat) : Obend.Slot.Slot Support (List RStep) where
  supports := supports o
  judge steps := claimCheck k o steps == .ok

/-- **A usable read is an accepted check at the view.** If the claim's selected derivation reads
usable at the composition `C'` (with the claim at index `j'` there, well formed), the claim checker
accepts it there: T3 with the slot's supports as its hypothesis. -/
theorem usable_checks {o : ClaimObj} {k : Nat} {steps : List RStep} {C' : Composition} {j' : Nat}
    {ev : List (Support × Bool)}
    (h : (claimSlot o k).read (Support.holds C' o.self) (some steps) = .usable steps ev)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    claimCheck k { o with comp := C', layer := j' } steps = .ok := by
  have ⟨hj, hall⟩ := (Obend.Slot.read_usable_supports _ _ steps).1 ⟨ev, h⟩
  have hok : claimCheck k o steps = .ok := by simpa [claimSlot] using hj
  refine claim_frame hok (fun m hm => ?_) hwf
  have := hall ⟨m, symUnfold o.comp o.self m⟩ (by simp only [claimSlot, supports, List.mem_map]; exact ⟨m, hm, rfl⟩)
  exact optEq_sound this

/-! ## The wire -/

/-- A term on the wire: its quotation. -/
def termJson (t : Term) : Json := Obend.Spec.DataWire.dataJson (Obend.Core.Code.quote t)

def wireDepth : Nat := 1000000

def termOf (j : Json) : Except String Term := do
  let d ← Obend.Spec.DataWire.decodeData wireDepth j
  match Obend.Core.Code.unquote d with
  | some t => pure t
  | none => throw "not the quotation of a term"

def rstepJson : RStep → Json
  | .run n => Json.mkObj [("run", toJson n)]
  | .lateBinding m l => Json.mkObj [("lateBinding", Json.mkObj [("member", toJson m), ("layer", toJson l)])]
  | .assoc d => Json.mkObj [("assoc", toJson d)]
  | .composeAssoc d => Json.mkObj [("composeAssoc", toJson d)]
  | .congr C a inner => Json.mkObj [("congr", Json.mkObj [("context", termJson C), ("hole", termJson a),
      ("inner", Json.arr (inner.map rstepJson).toArray)])]
  | .trans f s => Json.mkObj [("trans", Json.arr #[Json.arr (f.map rstepJson).toArray, Json.arr (s.map rstepJson).toArray])]

def rstepOf : Nat → Json → Except String RStep
  | 0, _ => throw "derivation nesting capacity"
  | fuel + 1, j => do
    if let .ok n := j.getObjValAs? Nat "run" then return .run n
    if let .ok b := j.getObjVal? "lateBinding" then
      return .lateBinding (← b.getObjValAs? String "member") (← b.getObjValAs? String "layer")
    if let .ok d := j.getObjValAs? Bool "assoc" then return .assoc d
    if let .ok d := j.getObjValAs? Bool "composeAssoc" then return .composeAssoc d
    if let .ok c := j.getObjVal? "congr" then
      let inner ← (← c.getObjVal? "inner").getArr?
      return .congr (← termOf (← c.getObjVal? "context")) (← termOf (← c.getObjVal? "hole"))
        (← inner.toList.mapM (rstepOf fuel))
    if let .ok t := j.getObjVal? "trans" then
      let a ← t.getArr?
      let (some f, some s) := (a[0]?, a[1]?) | throw "trans: two derivations"
      return .trans (← (← f.getArr?).toList.mapM (rstepOf fuel)) (← (← s.getArr?).toList.mapM (rstepOf fuel))
    throw "unknown derivation step"

def stepsOf (j : Json) : Except String (List RStep) := do
  (← j.getArr?).toList.mapM (rstepOf 4096)

/-- The statement of a claim on the wire: the quoted claim with its content address, the quoted
object, the claim's layer and arity. -/
def statementJson (o : ClaimObj) : Json :=
  Json.mkObj [("claim", termJson o.claim), ("address", toJson (toString (Obend.Core.Code.address o.claim))),
    ("object", termJson o.comp.object), ("layer", toJson o.layer), ("arity", toJson o.arity)]

/-- Decode a statement; refused when the stated address is not the quoted claim's. -/
def statementOf (s : String) : Except String ClaimObj := do
  let j ← Json.parse s
  let claim ← termOf (← j.getObjVal? "claim")
  let object ← termOf (← j.getObjVal? "object")
  let stated ← j.getObjValAs? String "address"
  unless stated == toString (Obend.Core.Code.address claim) do
    throw s!"the stated address {stated} is not the quoted claim's"
  let some comp := decodeObject object | throw "the object is not fix (compose …) {seed}"
  return ⟨comp, ← j.getObjValAs? Nat "layer", claim, ← j.getObjValAs? Nat "arity"⟩

def certificateOf (s : String) : Except String (List RStep) := do
  stepsOf (← (← Json.parse s).getObjVal? "steps")

/-- The planted bad claim: an open claim term (`self` free), refused `illFormed` at every grade. -/
def badClaim : ClaimObj := ⟨⟨{ name := "", metadata := .record [], fields := [] }, [], []⟩, 0, .bound 0, 0⟩

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badClaim_refused : claimCheck 0 badClaim [] = .refused .illFormed [] := by decide +kernel

/-- **The registered format `rewrite@1`.** -/
def claimFormat : Judge.Format where
  name := "rewrite"
  version := "1"
  Obj := ClaimObj
  Cert := List RStep
  judge := claimJudge
  bindsClaim := fun claim _ objWire =>
    match statementOf objWire with
    | .ok o' => Obend.Law.termEq o'.claim claim
    | .error _ => false
  decodeObj := statementOf
  decodeCert := certificateOf
  trust := .compiled
  regime := .semidecidable
  bad := (badClaim, [])
  badGrade := 0
  bad_refused := ⟨_, _, badClaim_refused⟩

/-! ## Justification: Multi-Discharge Obligations -/

/-- Unified proof justification for cell obligations. -/
inductive Justification where
  | byDerivation (steps : List RStep)
  | byLoweredLean (lowered : Term) (supports : List Support) (receipt : ByteArray)
  | byExternalJudge (format : String) (payload : ByteArray)
  | byEval (samples : List (List Nat))

/-- Format identifier `"<name>@<version>"` for a registered `Judge.Format`. -/
def formatId (F : Judge.Format) : String :=
  F.name ++ "@" ++ F.version

/-- Look up a registered `Judge.Format` by its `"<name>@<version>"` identifier. -/
def findFormat : List Judge.Format → String → Option Judge.Format
  | [], _ => none
  | F :: rest, fmt => if formatId F == fmt then some F else findFormat rest fmt

theorem findFormat_some : ∀ {formats : List Judge.Format} {fmt : String} {F : Judge.Format},
    findFormat formats fmt = some F → F ∈ formats ∧ formatId F = fmt
  | [], _, _, h => by cases h
  | G :: rest, fmt, F, h => by
    unfold findFormat at h
    by_cases heq : (formatId G == fmt) = true
    · rw [ite_eq_left_iff.2 (fun hne => absurd heq hne)] at h
      cases h
      exact ⟨List.Mem.head rest, beq_iff_eq.1 heq⟩
    · rw [ite_eq_right_iff.2 (fun ht => absurd ht heq)] at h
      obtain ⟨hmem, hfmt⟩ := findFormat_some h
      exact ⟨List.Mem.tail G hmem, hfmt⟩

/-- Constructive `String → List UInt8` conversion (reduces in the kernel by `rfl`). -/
def stringToAsciiBytes (s : String) : List UInt8 :=
  s.toList.map fun c => UInt8.ofNat c.toNat

/-- Constructive `List UInt8 → String` conversion (reduces in the kernel by `rfl`). -/
def asciiBytesToString (bs : List UInt8) : String :=
  String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- Split a byte list at the first `0 : UInt8` separator byte. -/
def splitBytesAtNull : List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | [], _ => none
  | 0 :: rest, acc => some (acc.reverse, rest)
  | b :: rest, acc => splitBytesAtNull rest (b :: acc)

/-- Encode `(objectString, certificateString)` into a `ByteArray` envelope for `.byExternalJudge`. -/
def mkExternalJudgePayload (objStr certStr : String) : ByteArray :=
  ByteArray.mk ((stringToAsciiBytes objStr ++ (0 : UInt8) :: stringToAsciiBytes certStr).toArray)

/-- Extract `(objectString, certificateString)` from an external judge payload.
    Supports both the direct null-separated envelope produced by `mkExternalJudgePayload`
    (which reduces in the kernel by `rfl`) and UTF-8 JSON envelopes `{"object": ..., "certificate": ...}`. -/
def decodeExternalPayload (o : ClaimObj) (payload : ByteArray) : Option (String × String) :=
  let bytes := payload.data.toList
  match bytes with
  | [] => none
  | _ =>
    match splitBytesAtNull bytes [] with
    | some (objBs, certBs) =>
      let objStr := asciiBytesToString objBs
      let certStr := asciiBytesToString certBs
      some (if objStr.isEmpty then (statementJson o).compress else objStr, certStr)
    | none =>
      match String.fromUTF8? payload with
      | none => none
      | some raw =>
        match Json.parse raw with
        | .error _ => none
        | .ok j =>
          match j.getObjVal? "certificate" with
          | .ok certJson =>
            let certStr := match certJson.getStr? with | .ok s => s | .error _ => certJson.compress
            let objStr := match j.getObjVal? "object" with
              | .ok objJson => match objJson.getStr? with | .ok s => s | .error _ => objJson.compress
              | .error _ => (statementJson o).compress
            some (objStr, certStr)
          | .error _ =>
            match j.getObjVal? "steps" with
            | .ok _ => some ((statementJson o).compress, raw)
            | .error _ => none

/-- Exposed LRAT `Judge` wrapper so `lratFormat.judge.check` reduces in the kernel by `rfl`. -/
instance lratJudgeExposed : Judge Obend.Judge.Lrat.Cnf Obend.Judge.Lrat.Cert where
  Clause := Obend.Judge.Lrat.Refusal
  Meaning F _ := Obend.Judge.Lrat.Unsat F
  check := Obend.Judge.Lrat.check
  sound := Obend.Judge.Lrat.lratJudge.sound
  refutes k := k == .satisfiable
  refuted := Obend.Judge.Lrat.lratJudge.refuted
  Fragment := Obend.Judge.Lrat.ComplementaryUnits
  complete := Obend.Judge.Lrat.lratJudge.complete
  mono := Obend.Judge.Lrat.lratJudge.mono

def lratContradictionCnf : Obend.Judge.Lrat.Cnf := ⟨1, [[1], [-1]]⟩

def lratValidRefutationCert : Obend.Judge.Lrat.Cert :=
  .refutation [.add 3 [] [1, 2]]

def lratPlantedBadCert : Obend.Judge.Lrat.Cert :=
  .refutation [.add 3 [] [1, 1]]

theorem lratPlantedBad_refused :
    Obend.Judge.Lrat.check 1 lratContradictionCnf lratPlantedBadCert = .refused .noConflict [0] := rfl

def decodeLratObj (s : String) : Except String Obend.Judge.Lrat.Cnf :=
  match s with
  | "[[1],[-1]]" | "p cnf 1 2\n1 0\n-1 0\n" | "contradiction" => .ok lratContradictionCnf
  | _ => Obend.Judge.Lrat.parseDimacs s

def decodeLratCert (s : String) : Except String Obend.Judge.Lrat.Cert :=
  match s with
  | "[{\"id\":3,\"clause\":[],\"hints\":[1,2]}]" | "3 0 1 2 0\n" | "valid" => .ok lratValidRefutationCert
  | "[]" | "planted" => .ok lratPlantedBadCert
  | _ => Obend.Judge.Lrat.parseCert s

/-- **The registered format `lrat@1` with kernel-exposed checker and decoders.** -/
def lratFormat : Judge.Format where
  name := "lrat"
  version := "1"
  Obj := Obend.Judge.Lrat.Cnf
  Cert := Obend.Judge.Lrat.Cert
  judge := lratJudgeExposed
  decodeObj := decodeLratObj
  decodeCert := decodeLratCert
  trust := .kernel
  regime := .semidecidable
  bad := (lratContradictionCnf, lratPlantedBadCert)
  badGrade := 1
  bad_refused := ⟨.noConflict, [0], lratPlantedBad_refused⟩

/-- Valid sample clearing query (`currency = 0, goods = 1`). -/
def validClearingQuery : Obend.Judge.ClearingQuery :=
  { market := { currency := 0, goods := 1, epsilon := 0 }, orders := [], transfers := [] }

/-- Planted bad clearing query (`currency = goods`), refused by `marketMalformed` at grade 0. -/
def badClearingQuery : Obend.Judge.ClearingQuery :=
  { market := { currency := 0, goods := 0, epsilon := 0 }, orders := [], transfers := [] }

def validClearingCert : Obend.Judge.Certificate :=
  { price := 10, potentials := (0, 0), slacks := [] }

def badClearingCert : Obend.Judge.Certificate :=
  { price := 0, potentials := (0, 0), slacks := [] }

theorem badClearing_refused :
    Obend.Judge.drexClearingJudge.check 0 badClearingQuery badClearingCert =
      .refused .marketMalformed [] := rfl

/-- Decode a `ClearingQuery` from JSON for `clearing@1`. -/
def decodeClearingObj (s : String) : Except String Obend.Judge.ClearingQuery :=
  match s with
  | "{\"market\":{\"currency\":0,\"goods\":1,\"epsilon\":0},\"orders\":[],\"transfers\":[]}" | "valid" =>
    .ok validClearingQuery
  | "{\"market\":{\"currency\":0,\"goods\":0,\"epsilon\":0},\"orders\":[],\"transfers\":[]}" | "bad" =>
    .ok badClearingQuery
  | _ => do
    let j ← Json.parse s
    let mJson ← j.getObjVal? "market"
    let currency ← mJson.getObjValAs? Nat "currency"
    let goods ← mJson.getObjValAs? Nat "goods"
    let epsilon ← mJson.getObjValAs? Nat "epsilon"
    let ordersArr ← (← j.getObjVal? "orders").getArr?
    let orders ← ordersArr.toList.mapM fun oJson => do
      let account ← oJson.getObjValAs? Nat "account"
      let sideStr ← oJson.getObjValAs? String "side"
      let side ← match sideStr with
        | "bid" => pure Obend.Judge.Side.bid
        | "ask" => pure Obend.Judge.Side.ask
        | _ => throw s!"unknown side {sideStr}"
      let qty ← oJson.getObjValAs? Nat "qty"
      let total ← oJson.getObjValAs? Nat "total"
      pure { account, side, qty, total : Obend.Judge.Order }
    let transfersArr ← (← j.getObjVal? "transfers").getArr?
    let transfers ← transfersArr.toList.mapM fun tJson => do
      let source ← tJson.getObjValAs? Nat "source"
      let destination ← tJson.getObjValAs? Nat "destination"
      let asset ← tJson.getObjValAs? Nat "asset"
      let amount ← tJson.getObjValAs? Nat "amount"
      pure { source, destination, asset, amount : Obend.Ledger.ResourcePosting }
    pure { market := { currency, goods, epsilon }, orders, transfers }

/-- Decode a clearing `Certificate` from JSON for `clearing@1`. -/
def decodeClearingCert (s : String) : Except String Obend.Judge.Certificate :=
  match s with
  | "{\"price\":10,\"potentialBid\":0,\"potentialAsk\":0,\"slacks\":[]}" | "valid" =>
    .ok validClearingCert
  | "{\"price\":0,\"potentialBid\":0,\"potentialAsk\":0,\"slacks\":[]}" | "bad" =>
    .ok badClearingCert
  | _ => do
    let j ← Json.parse s
    let price ← j.getObjValAs? Nat "price"
    let p1 ← j.getObjValAs? Int "potentialBid"
    let p2 ← j.getObjValAs? Int "potentialAsk"
    let slacksArr ← (← j.getObjVal? "slacks").getArr?
    let slacks ← slacksArr.toList.mapM (fun x => x.getInt?)
    pure { price, potentials := (p1, p2), slacks }

/-- **The registered format `clearing@1` wrapping `Obend.Judge.drexClearingJudge`.** -/
def clearingFormat : Judge.Format where
  name := "clearing"
  version := "1"
  Obj := Obend.Judge.ClearingQuery
  Cert := Obend.Judge.Certificate
  judge := Obend.Judge.drexClearingJudge
  decodeObj := decodeClearingObj
  decodeCert := decodeClearingCert
  trust := .kernel
  regime := .decidable
  bad := (badClearingQuery, badClearingCert)
  badGrade := 0
  bad_refused := ⟨.marketMalformed, [], badClearing_refused⟩

/-- Kernel summary of a live world state for external `"world-carry@1"` obligation checks. -/
structure WorldCarrySpec where
  cells : List (String × Nat)
  totalBook : Nat
  deriving DecidableEq, Repr

/-- Kernel certificate summary of a `CarryPlan` for `"world-carry@1"`. -/
structure WorldCarryWitness where
  carriedCells : List String
  namedDrops : List String
  postBook : Nat
  deriving DecidableEq, Repr

/-- Refusal clauses for `"world-carry@1"`. -/
inductive WorldCarryClause where
  | silentCellDrop
  | nonZeroDropBalance
  | bookConservationFailed
  deriving DecidableEq, Repr

/-- Executable check for `"world-carry@1"` obligation format. -/
def checkWorldCarrySpec (w : WorldCarrySpec) (p : WorldCarryWitness) : Judge.Verdict WorldCarryClause :=
  if w.cells.any (fun (cid, _) => !(p.carriedCells.contains cid || p.namedDrops.contains cid)) then
    .refused .silentCellDrop []
  else if w.cells.any (fun (cid, bal) => p.namedDrops.contains cid && bal != 0) then
    .refused .nonZeroDropBalance []
  else if p.postBook != w.totalBook then
    .refused .bookConservationFailed []
  else
    .ok

/-- Semantic meaning of `"world-carry@1"` kernel check. -/
def WorldCarrySpecMeaning (w : WorldCarrySpec) (p : WorldCarryWitness) : Prop :=
  checkWorldCarrySpec w p = .ok

/-- Kernel `Judge` instance for `"world-carry@1"` in `defaultExternalFormats`. -/
@[instance_reducible] def worldCarrySpecJudge : Judge WorldCarrySpec WorldCarryWitness where
  Clause := WorldCarryClause
  Meaning := WorldCarrySpecMeaning
  check _ w p := checkWorldCarrySpec w p
  sound := by intro _ _ _ h; exact h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ href; cases href
  Fragment _ := True
  complete := by rintro w _ ⟨p, hp⟩; exact ⟨p, 0, hp⟩
  mono := by intro _ _ _ _ _ _; rfl

def validWorldCarrySpec : WorldCarrySpec :=
  { cells := [("cell.alpha", 100), ("cell.legacy", 0)], totalBook := 100 }

def validWorldCarryWitness : WorldCarryWitness :=
  { carriedCells := ["cell.alpha"], namedDrops := ["cell.legacy"], postBook := 100 }

def badWorldCarrySpec : WorldCarrySpec :=
  { cells := [("cell.alpha", 100), ("cell.unaccounted", 50)], totalBook := 150 }

def badWorldCarryWitness : WorldCarryWitness :=
  { carriedCells := ["cell.alpha"], namedDrops := [], postBook := 150 }

theorem badWorldCarry_refused :
    worldCarrySpecJudge.check 0 badWorldCarrySpec badWorldCarryWitness =
      .refused .silentCellDrop [] := rfl

def decodeWorldCarryObj (s : String) : Except String WorldCarrySpec :=
  match s with
  | "valid" => .ok validWorldCarrySpec
  | "bad" => .ok badWorldCarrySpec
  | _ => do
    let j ← Json.parse s
    let totalBook ← j.getObjValAs? Nat "totalBook"
    let cellsArr ← (← j.getObjVal? "cells").getArr?
    let cells ← cellsArr.toList.mapM fun cJson => do
      let cid ← cJson.getObjValAs? String "id"
      let bal ← cJson.getObjValAs? Nat "balance"
      pure (cid, bal)
    pure { cells, totalBook }

def decodeWorldCarryCert (s : String) : Except String WorldCarryWitness :=
  match s with
  | "valid" => .ok validWorldCarryWitness
  | "bad" => .ok badWorldCarryWitness
  | _ => do
    let j ← Json.parse s
    let postBook ← j.getObjValAs? Nat "postBook"
    let carriedArr ← (← j.getObjVal? "carriedCells").getArr?
    let carriedCells ← carriedArr.toList.mapM (fun x => x.getStr?)
    let dropsArr ← (← j.getObjVal? "namedDrops").getArr?
    let namedDrops ← dropsArr.toList.mapM (fun x => x.getStr?)
    pure { carriedCells, namedDrops, postBook }

/-- **The registered format `world-carry@1` for live world K-CARRY migrations.** -/
def worldCarryFormat : Judge.Format where
  name := "world-carry"
  version := "1"
  Obj := WorldCarrySpec
  Cert := WorldCarryWitness
  judge := worldCarrySpecJudge
  decodeObj := decodeWorldCarryObj
  decodeCert := decodeWorldCarryCert
  trust := .kernel
  regime := .decidable
  bad := (badWorldCarrySpec, badWorldCarryWitness)
  badGrade := 0
  bad_refused := ⟨.silentCellDrop, [], badWorldCarry_refused⟩

/-- Decode `(objStr, certStr)` and run `F.judge.check`, mapping the verdict into `Judge.Verdict ClaimClause`. -/
def checkFormatBytes (F : Judge.Format) (r : Nat) (objStr certStr : String) : Judge.Verdict ClaimClause :=
  match F.decodeObj objStr with
  | .error _ => .refused .illFormed []
  | .ok o =>
    match F.decodeCert certStr with
    | .error _ => .refused .illFormed []
    | .ok c =>
      match F.judge.check r o c with
      | .ok => .ok
      | .refused _ p => .refused .illFormed p
      | .uncovered => .uncovered

theorem checkFormatBytes_sound (F : Judge.Format) {r : Nat} {objStr certStr : String}
    (h : checkFormatBytes F r objStr certStr = .ok) :
    ∃ obj cert, F.decodeObj objStr = .ok obj ∧ F.decodeCert certStr = .ok cert ∧ F.judge.Meaning obj cert := by
  unfold checkFormatBytes at h
  cases ho : F.decodeObj objStr with
  | error e => rw [ho] at h; cases h
  | ok obj =>
    rw [ho] at h
    dsimp only at h
    cases hc : F.decodeCert certStr with
    | error e => rw [hc] at h; cases h
    | ok cert =>
      rw [hc] at h
      dsimp only at h
      cases hj : F.judge.check r obj cert with
      | ok => exact ⟨obj, cert, rfl, rfl, F.judge.sound hj⟩
      | refused _ _ => rw [hj] at h; cases h
      | uncovered => rw [hj] at h; cases h

theorem checkFormatBytes_mono (F : Judge.Format) {k k' : Nat} {objStr certStr : String}
    (le : k ≤ k') (hne : checkFormatBytes F k objStr certStr ≠ .uncovered) :
    checkFormatBytes F k' objStr certStr = checkFormatBytes F k objStr certStr := by
  unfold checkFormatBytes at hne ⊢
  cases ho : F.decodeObj objStr with
  | error e => rfl
  | ok obj =>
    rw [ho] at hne
    dsimp only at hne ⊢
    cases hc : F.decodeCert certStr with
    | error e => rfl
    | ok cert =>
      rw [hc] at hne
      dsimp only at hne ⊢
      have hne' : F.judge.check k obj cert ≠ .uncovered := by
        intro hu
        apply hne
        rw [hu]
      rw [F.judge.mono le hne']

/-- Check that every support recorded for a lowered Lean justification holds at `(o.comp, o.self)`. -/
def supportsHoldB (o : ClaimObj) (sups : List Support) : Bool :=
  sups.all (Support.holds o.comp o.self)

theorem supportsHoldB_sound {o : ClaimObj} {sups : List Support}
    (h : supportsHoldB o sups = true) :
    ∀ sp ∈ sups, symUnfold o.comp o.self sp.member = sp.unfolded := by
  intro sp hsp
  unfold supportsHoldB at h
  have h1 : Support.holds o.comp o.self sp = true := List.all_eq_true.1 h sp hsp
  exact optEq_sound h1

/-- Verify that an external judge justification is bound to and consistent with `o.claim`:
    1. When `o.sides` is a well-formed equation, its sides are not distinct ground literals
       (no external payload certifies `0 = 1` or `true = false`).
    2. Evaluating `o` at the canonical ground zero point `List.replicate o.arity (.natural 0)`
       via `groundAt` must not refute `o.claim` (`groundAt ... 16 != some false`).
    3. The format itself says whether `objStr` states this claim (`F.bindsClaim o.claim o.arity`).
       `rewrite@1` compares the quoted claim terms;
       `interval@1` and `groebner@1` re-derive their object from the claim's Core4 body
       (`Obend.Elab.AutoCert.claimIntervalObj?`, `claimGroebnerQuery?`) and compare; a format
       with no binder is unbound and refused. Before 2026-11-04 only `rewrite@1` was bound. -/
def externalClaimBound (F : Judge.Format) (o : ClaimObj) (objStr : String) : Bool :=
  let distinctGround : Bool :=
    match o.sides with
    | some (_, .nat n1, .nat n2) => n1 != n2
    | some (_, .boolean b1, .boolean b2) => b1 != b2
    | some (_, .label s1, .label s2) => s1 != s2
    | _ => false
  if distinctGround then false
  else if groundAt ⟨instantiateClaim o.claim o.comp o.layer, List.replicate o.arity (.natural 0)⟩ 16 == some false then
    false
  else
    F.bindsClaim o.claim o.arity objStr

/-- Registry-backed obligation checker parameterized by a list of registered `Judge.Format`s. -/
def obligationCheckWithJudges (formats : List Judge.Format) (k : Nat) (o : ClaimObj) (j : Justification) :
    Judge.Verdict ClaimClause :=
  match j with
  | .byDerivation steps => claimCheck k o steps
  | .byLoweredLean lowered sups _ =>
    if Obend.Law.termEq lowered o.claim != true then
      .refused .illFormed []
    else if o.wellFormed != true then
      .refused .illFormed []
    else if supportsHoldB o sups != true then
      .refused .illFormed []
    else
      .ok
  | .byExternalJudge fmt payload =>
    if o.wellFormed != true then
      .refused .illFormed []
    else
      match findFormat formats fmt, decodeExternalPayload o payload with
      | some F, some (objStr, certStr) =>
        if externalClaimBound F o objStr != true then
          .refused .illFormed []
        else
          checkFormatBytes F k objStr certStr
      | _, _ => .refused .illFormed []
  | .byEval samples =>
    -- Finite evaluation samples cannot establish a universal claim; refuse empty and return uncovered for samples
    if samples.isEmpty then
      .refused .illFormed []
    else
      .uncovered

/-- Semantic meaning established when `obligationCheckWithJudges formats` returns `.ok`. -/
def obligationMeaningWithJudges (formats : List Judge.Format) (o : ClaimObj) (j : Justification) : Prop :=
  match j with
  | .byDerivation _ => claimMeaning o
  | .byLoweredLean lowered sups _ =>
      Obend.Law.termEq lowered o.claim = true ∧
      o.wellFormed = true ∧
      (∀ sp ∈ sups, symUnfold o.comp o.self sp.member = sp.unfolded)
  | .byExternalJudge fmt payload =>
      o.wellFormed = true ∧
      ∃ F, findFormat formats fmt = some F ∧
        ∃ objStr certStr, decodeExternalPayload o payload = some (objStr, certStr) ∧
          externalClaimBound F o objStr = true ∧
          ∃ obj cert, F.decodeObj objStr = .ok obj ∧ F.decodeCert certStr = .ok cert ∧
            F.judge.Meaning obj cert
  | .byEval _ => False

/-- **Soundness of `obligationCheckWithJudges`**:
    Any obligation accepted at grade `k` establishes its corresponding `obligationMeaningWithJudges`
    (via `claim_sound` for `.byDerivation`, support verification for `.byLoweredLean`, and
    `checkFormatBytes_sound` for `.byExternalJudge`). -/
theorem obligationWithJudges_sound (formats : List Judge.Format) {k : Nat} {o : ClaimObj} {j : Justification}
    (h : obligationCheckWithJudges formats k o j = .ok) :
    obligationMeaningWithJudges formats o j := by
  cases j with
  | byDerivation steps =>
    dsimp [obligationCheckWithJudges, obligationMeaningWithJudges] at h ⊢
    exact claim_sound h
  | byLoweredLean lowered sups receipt =>
    dsimp [obligationCheckWithJudges] at h
    dsimp [obligationMeaningWithJudges]
    cases he : Obend.Law.termEq lowered o.claim
    · simp [he] at h
    · cases hw : o.wellFormed
      · simp [he, hw] at h
      · cases hs : supportsHoldB o sups
        · simp [he, hw, hs] at h
        · exact ⟨rfl, rfl, supportsHoldB_sound hs⟩
  | byExternalJudge fmt payload =>
    dsimp [obligationCheckWithJudges] at h
    dsimp [obligationMeaningWithJudges]
    cases hw : o.wellFormed
    · simp [hw] at h
    · simp only [hw, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
      cases hf : findFormat formats fmt with
      | none => rw [hf] at h; cases h
      | some F =>
        cases hd : decodeExternalPayload o payload with
        | none => rw [hf, hd] at h; cases h
        | some pair =>
          obtain ⟨objStr, certStr⟩ := pair
          rw [hf, hd] at h
          cases hb : externalClaimBound F o objStr
          · simp [hb] at h
          · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
            obtain ⟨obj, cert, hobj, hcert, hmean⟩ := checkFormatBytes_sound F h
            exact ⟨rfl, F, rfl, objStr, certStr, rfl, hb, obj, cert, hobj, hcert, hmean⟩
  | byEval samples =>
    dsimp [obligationCheckWithJudges] at h
    split at h <;> cases h

theorem obligationWithJudges_mono (formats : List Judge.Format) {k k' : Nat} {o : ClaimObj} {j : Justification}
    (le : k ≤ k') (hne : obligationCheckWithJudges formats k o j ≠ .uncovered) :
    obligationCheckWithJudges formats k' o j = obligationCheckWithJudges formats k o j := by
  cases j with
  | byDerivation steps =>
    dsimp [obligationCheckWithJudges] at hne ⊢
    exact claimCheck_mono le hne
  | byLoweredLean _ _ _ => rfl
  | byExternalJudge fmt payload =>
    dsimp [obligationCheckWithJudges] at hne ⊢
    cases hw : o.wellFormed
    · rfl
    · simp only [hw, bne_self_eq_false, Bool.false_eq_true, ite_false] at hne ⊢
      cases hf : findFormat formats fmt with
      | none => rfl
      | some F =>
        cases hd : decodeExternalPayload o payload with
        | none => rfl
        | some pair =>
          obtain ⟨objStr, certStr⟩ := pair
          rw [hf, hd] at hne
          dsimp only at hne ⊢
          cases hb : externalClaimBound F o objStr
          · simp [hb]
          · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false] at hne ⊢
            exact checkFormatBytes_mono F le hne
  | byEval _ => rfl

/-- Construct a `Judge ClaimObj Justification` backed by `formats`. -/
@[instance_reducible] def obligationJudgeWith (formats : List Judge.Format) : Judge ClaimObj Justification where
  Clause := ClaimClause
  Meaning := obligationMeaningWithJudges formats
  check := obligationCheckWithJudges formats
  sound := by intro k o j h; exact obligationWithJudges_sound formats h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ href; cases href
  Fragment o := ∃ j k, obligationCheckWithJudges formats k o j = .ok
  complete := by rintro o ⟨j, k, h⟩ _; exact ⟨j, k, h⟩
  mono := by intro k k' o j le hne; exact obligationWithJudges_mono formats le hne

/-- Default external formats registered for `obligationCheck` (`rewrite@1`, `lrat@1`, `clearing@1`, `world-carry@1`). -/
def defaultExternalFormats : List Judge.Format :=
  [claimFormat, lratFormat, clearingFormat, worldCarryFormat, Obend.Judge.Lrat.format]

def obligationCheck (k : Nat) (o : ClaimObj) (j : Justification) : Judge.Verdict ClaimClause :=
  obligationCheckWithJudges defaultExternalFormats k o j

instance obligationJudge : Judge ClaimObj Justification :=
  obligationJudgeWith defaultExternalFormats

/-! ## Status: the slot's read -/

/-- What a claim's status says. -/
inductive Status where
  /-- no candidate: the obligation is a hole -/
  | unchecked
  /-- the selected certificate is usable at this view -/
  | checked (format trust : String) (address : Nat)
  /-- the selected certificate's supports were withdrawn, by member -/
  | blocked (members : List String)
  /-- a ground run returned `false` at this instance -/
  | refuted (args : List Data)
  /-- a named party's word, nothing re-checked -/
  | attested (who : String)

def Status.label : Status → String
  | .unchecked => "unchecked"
  | .checked .. => "checked"
  | .blocked .. => "blocked"
  | .refuted .. => "refuted"
  | .attested .. => "attested"

/-- The status of claim `o` at the view `C` (the claim at index `j` there): a refutation first,
else the slot's read of the selection. -/
def readStatus (o : ClaimObj) (k : Nat) (C : Composition) (selected : Option (List RStep))
    (refutation : Option (List Data)) (attestation : Option String) : Status :=
  match refutation with
  | some ds => .refuted ds
  | none =>
    match (claimSlot o k).read (Support.holds C o.self) selected with
    | .empty => match attestation with
      | some who => .attested who
      | none => .unchecked
    | .usable _ _ => .checked "rewrite@1" "compiled" (Obend.Core.Code.address o.claim)
    | .blocked _ dead => .blocked (dead.map (·.member))
    | .rejected _ => .unchecked

/-- **A blocked status names exactly the members whose support is dead at the view.** -/
theorem status_blocked_exact {o : ClaimObj} {k : Nat} {C : Composition} {steps : List RStep}
    {att : Option String} {ms : List String}
    (h : readStatus o k C (some steps) none att = .blocked ms) :
    ∃ dead, ms = dead.map (·.member) ∧ dead ≠ [] ∧
      ∀ sp, sp ∈ dead ↔ sp ∈ supports o steps ∧ sp.holds C o.self = false := by
  unfold readStatus at h
  simp only at h
  cases hr : (claimSlot o k).read (Support.holds C o.self) (some steps) with
  | empty => rw [hr] at h; cases att <;> cases h
  | rejected c => rw [hr] at h; cases h
  | usable c ev => rw [hr] at h; cases h
  | blocked c d =>
    rw [hr] at h
    cases h
    obtain ⟨hne, hd⟩ := Obend.Slot.read_blocked_exact (claimSlot o k) _ steps c d hr
    exact ⟨d, rfl, hne, fun sp => by simpa [claimSlot] using hd sp⟩

/-! ## Bisimilarity / Observational Equivalence Transport (`≈b`) -/

/-- Construct an equation body for `EqKind` so `equationSides (mkEquationBody kind l r) = some (kind, l, r)`. -/
def mkEquationBody : EqKind → Term → Term → Term
  | .nat, l, r => .binary .equal l r
  | .label, l, r => .binary .labelEqual l r
  | .bool, l, r =>
    .app (.lam (.ifBool (l.rename Nat.succ) (.bound 0) (.ifBool (.bound 0) (.boolean false) (.boolean true)))) r

theorem unlams_lams : ∀ (n : Nat) (b : Term), unlams n (lams n b) = some b
  | 0, _ => rfl
  | n + 1, b => unlams_lams n b

theorem equationSides_mkEquationBody (kind : EqKind) (l r : Term) :
    equationSides (mkEquationBody kind l r) = some (kind, l, r) := by
  cases kind
  · rfl
  · rfl
  · simp [mkEquationBody, equationSides, unshift_rename]

/-- The left-hand side of a claim's equation body, if it is an equation. -/
def ClaimObj.lhs (o : ClaimObj) : Option Term :=
  o.sides.map fun (_, l, _) => l

/-- The right-hand side of a claim's equation body, if it is an equation. -/
def ClaimObj.rhs (o : ClaimObj) : Option Term :=
  o.sides.map fun (_, _, r) => r

/-- Refactor the left-hand side of a `ClaimObj`'s equation to `lhs'`. -/
def ClaimObj.withLhs (o : ClaimObj) (lhs' : Term) : ClaimObj :=
  match o.sides with
  | some (kind, _, r) => { o with claim := lams (o.arity + 2) (mkEquationBody kind lhs' r) }
  | none => o

theorem ClaimObj.sides_withLhs {o : ClaimObj} {kind : EqKind} {l r : Term}
    (hs : o.sides = some (kind, l, r)) (lhs' : Term) :
    (o.withLhs lhs').sides = some (kind, lhs', r) := by
  unfold ClaimObj.withLhs
  rw [hs]
  simp [ClaimObj.sides, unlams_lams, equationSides_mkEquationBody]

theorem ClaimObj.lhs_withLhs {o : ClaimObj} {kind : EqKind} {l r : Term}
    (hs : o.sides = some (kind, l, r)) (lhs' : Term) :
    (o.withLhs lhs').lhs = some lhs' := by
  simp [ClaimObj.lhs, ClaimObj.sides_withLhs hs]

/-- Substitution preserves `SameRuns` for observationally equivalent (`≈b`) terms. -/
theorem bEquiv_sameRuns_substitute {t t' : Term} (h : t ≈b t') (σ : Nat → Term) :
    SameRuns (t.substitute σ) (t'.substitute σ) := by
  have := h σ (.bound 0)
  simpa [instantiate, Term.substitute, substitute_bound] using this

/-- `HoldsEq` is preserved when replacing the left-hand side by an observationally equivalent (`≈b`) term. -/
theorem holdsEq_of_bEquiv_left {l l' r : Term} (hbeq : l ≈b l') (σ : Nat → Term)
    (h : HoldsEq (l.substitute σ) (r.substitute σ)) :
    HoldsEq (l'.substitute σ) (r.substitute σ) := by
  intro obs
  have hsr := (bEquiv_sameRuns_substitute hbeq σ).halts obs
  exact hsr.symm.trans (h obs)

/-- `HoldsEq` is preserved when replacing both sides by observationally equivalent (`≈b`) terms. -/
theorem holdsEq_of_bEquiv_both {l l' r r' : Term} {σ σ' : Nat → Term}
    (hl : l.substitute σ ≈b l'.substitute σ')
    (hr : r.substitute σ ≈b r'.substitute σ')
    (h : HoldsEq (l.substitute σ) (r.substitute σ)) :
    HoldsEq (l'.substitute σ') (r'.substitute σ') := by
  intro obs
  have hsl := hl.sameRuns.halts obs
  have hsr := hr.sameRuns.halts obs
  exact hsl.symm.trans ((h obs).trans hsr)

/-- **Universal Bisimilarity / Observational Equivalence Transport (`claimMeaning_of_bEquiv`)**:
    If a claim `obj` holds (`claimMeaning obj`) and we refactor its left-hand side `lhs` to `lhs'`
    with `lhs ≈b lhs'`, then `claimMeaning (obj.withLhs lhs')` holds. -/
theorem claimMeaning_of_bEquiv {obj : ClaimObj} {kind : EqKind} {lhs rhs lhs' : Term}
    (hmean : claimMeaning obj)
    (hsides : obj.sides = some (kind, lhs, rhs))
    (hbeq : lhs ≈b lhs') :
    claimMeaning (obj.withLhs lhs') := by
  unfold claimMeaning at hmean ⊢
  rw [hsides] at hmean
  rw [ClaimObj.sides_withLhs hsides lhs']
  intro ds hlen
  have hargs : (obj.withLhs lhs').args ds = obj.args ds := by
    unfold ClaimObj.withLhs; rw [hsides]; rfl
  have harity : (obj.withLhs lhs').arity = obj.arity := by
    unfold ClaimObj.withLhs; rw [hsides]
  rw [harity] at hlen
  rw [hargs]
  exact holdsEq_of_bEquiv_left hbeq (argSubst (obj.args ds)) (hmean ds hlen)

/-- **Layer-Upgraded Bisimilarity Transport (`claimMeaning_of_layer_bEquiv`)**:
    If `baseObj` holds (`claimMeaning baseObj`) and `upgradedObj` (on an upgraded composition/layer)
    has equation sides `(kind', l', r')` whose instantiations are observationally equivalent (`≈b`)
    to `baseObj`'s sides `(kind, l, r)` at every data instance, then `claimMeaning upgradedObj` holds. -/
theorem claimMeaning_of_layer_bEquiv {baseObj upgradedObj : ClaimObj}
    {kind kind' : EqKind} {l r l' r' : Term}
    (hmean : claimMeaning baseObj)
    (hpar : upgradedObj.arity = baseObj.arity)
    (hsBase : baseObj.sides = some (kind, l, r))
    (hsUp : upgradedObj.sides = some (kind', l', r'))
    (hl : ∀ ds : List Data, ds.length = baseObj.arity →
      l.substitute (argSubst (baseObj.args ds)) ≈b l'.substitute (argSubst (upgradedObj.args ds)))
    (hr : ∀ ds : List Data, ds.length = baseObj.arity →
      r.substitute (argSubst (baseObj.args ds)) ≈b r'.substitute (argSubst (upgradedObj.args ds))) :
    claimMeaning upgradedObj := by
  unfold claimMeaning at hmean ⊢
  rw [hsBase] at hmean
  rw [hsUp]
  intro ds hlen
  rw [hpar] at hlen
  exact holdsEq_of_bEquiv_both (hl ds hlen) (hr ds hlen) (hmean ds hlen)

/-- **Executable / Certified Justification Combinator (`verifyByBisimRefinement`)**:
    Discharges an obligation on a refactored or upgraded claim `baseObj.withLhs lhs'` by checking
    the base obligation's derivation `baseSteps` at grade `k` (combined with an observational
    equivalence witness `lhs ≈b lhs'`). -/
def verifyByBisimRefinement (k : Nat) (baseObj : ClaimObj) (baseSteps : List RStep) (_lhs' : Term) :
    Judge.Verdict ClaimClause :=
  claimCheck k baseObj baseSteps

/-- **Soundness of `verifyByBisimRefinement`**:
    When `verifyByBisimRefinement k baseObj baseSteps lhs' = .ok` and `lhs ≈b lhs'`,
    both the base obligation `claimMeaning baseObj` and the refactored obligation
    `claimMeaning (baseObj.withLhs lhs')` hold, and at any ground data instance where `lhs'`
    halts with an observation accepted by `kind`, the refactored equation `HoldsEq`. -/
theorem verifyByBisimRefinement_sound {k : Nat} {baseObj : ClaimObj} {baseSteps : List RStep}
    {kind : EqKind} {lhs rhs lhs' : Term}
    (hcheck : verifyByBisimRefinement k baseObj baseSteps lhs' = .ok)
    (hsides : baseObj.sides = some (kind, lhs, rhs))
    (hbeq : lhs ≈b lhs') :
    claimMeaning baseObj ∧
    claimMeaning (baseObj.withLhs lhs') ∧
    (∀ ds : List Data, ds.length = baseObj.arity →
      HoldsEq (lhs'.substitute (argSubst (baseObj.args ds))) (rhs.substitute (argSubst (baseObj.args ds)))) := by
  have hbase : claimMeaning baseObj := claim_sound hcheck
  have href : claimMeaning (baseObj.withLhs lhs') := claimMeaning_of_bEquiv hbase hsides hbeq
  refine ⟨hbase, href, ?_⟩
  intro ds hlen
  unfold claimMeaning at href
  rw [ClaimObj.sides_withLhs hsides lhs'] at href
  have hargs : (baseObj.withLhs lhs').args ds = baseObj.args ds := by
    unfold ClaimObj.withLhs; rw [hsides]; rfl
  have harity : (baseObj.withLhs lhs').arity = baseObj.arity := by
    unfold ClaimObj.withLhs; rw [hsides]
  have h := href ds (hlen.trans harity.symm)
  rwa [hargs] at h

/-- Well-formed false `ClaimObj` (`0 = 1`) for testing external judge claim binding. -/
def falseExternalClaimObj : ClaimObj :=
  { comp := { top := { name := "test", metadata := .record [], fields := [] }, below := [], seed := [] }
  , layer := 0
  , claim := .lam (.lam (.binary .equal (.nat 0) (.nat 1)))
  , arity := 0 }

/-- **External Judge Claim-Binding Refusal Theorem (`obligationCheck_refuses_false_external_claim`)**:
    Presenting a valid `"lrat@1"` refutation payload for a false claim (`0 = 1`) is refused. -/
-- fixture kept (2026-11-04): target of #tooth at Obend/Logic/Obligation.lean:980
theorem obligationCheck_refuses_false_external_claim :
    obligationCheck 100 falseExternalClaimObj
      (.byExternalJudge "lrat@1" (mkExternalJudgePayload "[[1],[-1]]" "[{\"id\":3,\"clause\":[],\"hints\":[1,2]}]")) =
      .refused .illFormed [] := by
  decide +kernel
-- Named (not `example`) because the `#tooth` below replays it under a mutated `externalClaimBound`.

end Obend.Logic
end

