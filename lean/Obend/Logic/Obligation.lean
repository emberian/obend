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
import all Obend.Logic.Frame
public import Obend.Logic.Ground
public import Obend.Slot
public import Obend.Spec.DataWire
public import Obend.Judge.Lrat
public import Obend.Judge.Clearing
public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Lean (Json toJson)
set_option autoImplicit false

/-! ## The claim judge -/

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

/-- Reflexive syntactic equations, independently of any checker or certificate. -/
def ClaimFragment (o : ClaimObj) : Prop :=
  o.wellFormed = true ∧ ∃ kind t, o.sides = some (kind, t, t)

theorem claimFragment_complete {o : ClaimObj} (h : ClaimFragment o) :
    claimCheck 0 o [] = .ok := by
  obtain ⟨hw, kind, t, hs⟩ := h
  simp [claimCheck, hw, hs, rewriteWith, replay, sizeList, termEq_refl', liftVerdict]

theorem claimCheck_wellFormed {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : claimCheck k o steps = .ok) : o.wellFormed = true := by
  unfold claimCheck at h
  split at h
  · assumption
  · cases h

theorem claimCheck_illFormed {k : Nat} {o : ClaimObj} {steps : List RStep} {p : List Nat}
    (h : claimCheck k o steps = .refused .illFormed p) : o.wellFormed ≠ true := by
  intro hw
  simp only [claimCheck, hw, ite_true] at h
  cases hs : o.sides with
  | none => simp [hs] at h
  | some x =>
    obtain ⟨kind, l, r⟩ := x
    simp only [hs] at h
    cases hv : rewriteWith (claimResolver o.comp o.self) k l r steps <;>
      simp [hv, liftVerdict] at h

/-- The claim judge refuses malformed objects and is complete on reflexive equations. -/
instance claimJudge : Judge ClaimObj (List RStep) where
  Clause := ClaimClause
  Meaning o _ := o.wellFormed = true ∧ claimMeaning o
  check := claimCheck
  sound h := ⟨claimCheck_wellFormed h, claim_sound h⟩
  refutes k := k == .illFormed
  refuted := by
    intro k o steps clause p h hk c hm
    have : clause = .illFormed := beq_iff_eq.mp hk
    subst clause
    exact claimCheck_illFormed h hm.1
  Fragment := ClaimFragment
  complete := by intro o hf _; exact ⟨[], 0, claimFragment_complete hf⟩
  mono := by intro k k' o steps le hne; exact claimCheck_mono le hne

/-- A closed reflexive equation gives a constructive, nonempty fragment. -/
def reflexiveClaimObj : ClaimObj :=
  ⟨⟨{ name := "reflexive", metadata := .record [], fields := [] }, [], []⟩,
    0, .lam (.lam (.binary .equal (.nat 0) (.nat 0))), 0⟩

theorem claimJudge_fragment_inhabited : ∃ o, claimJudge.Fragment o := by
  refine ⟨reflexiveClaimObj, ?_, .nat, .nat 0, rfl⟩
  decide +kernel

/-! ## Supports -/

/-- A support: a member the derivation unfolds, with the provider and body it unfolded to. -/
structure Support where
  member : String
  unfolded : Option (String × Term)

@[expose] def optEq : Option (String × Term) → Option (String × Term) → Bool
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
@[expose] def supports (o : ClaimObj) (steps : List RStep) : List Support :=
  (membersList steps).map fun m => ⟨m, symUnfold o.comp o.self m⟩

/-- A support holds at a view (a composition) when the member unfolds there as it did. -/
@[expose] def Support.holds (C : Composition) (s : Nat) (sp : Support) : Bool := optEq (symUnfold C s sp.member) sp.unfolded

/-- The claim's slot at grade `k`. -/
@[expose] def claimSlot (o : ClaimObj) (k : Nat) : Obend.Slot.Slot Support (List RStep) where
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

theorem claimJudge_refusal_inhabited : ∃ o steps clause p,
    claimJudge.check 0 o steps = .refused clause p ∧ claimJudge.refutes clause = true :=
  ⟨badClaim, [], .illFormed, [], badClaim_refused, rfl⟩

/-- **The registered format `rewrite@1`.** -/
@[expose] def claimFormat : Judge.Format where
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
    Obend.Judge.Lrat.check 1 lratContradictionCnf lratPlantedBadCert = .refused .noConflict [0] := by decide +kernel

/-- Accept DIMACS or a JSON array of clauses, deriving the variable bound from the literals. -/
def decodeLratObj (s : String) : Except String Obend.Judge.Lrat.Cnf := do
  if s.trimAscii.toString.startsWith "[" then
    let rows ← (← Json.parse s).getArr?
    let clauses ← rows.toList.mapM fun row => do
      let lits ← row.getArr?
      lits.toList.mapM (·.getInt?)
    let vars := clauses.foldl (fun n clause => clause.foldl (fun n lit => max n lit.natAbs) n) 0
    pure ⟨vars, clauses⟩
  else Obend.Judge.Lrat.parseDimacs s

/-- Accept LRAT text or JSON addition steps; both forms carry the complete proof. -/
def decodeLratCert (s : String) : Except String Obend.Judge.Lrat.Cert := do
  if s.trimAscii.toString.startsWith "[" then
    let rows ← (← Json.parse s).getArr?
    let steps ← rows.toList.mapM fun row => do
      let id ← row.getObjValAs? Nat "id"
      let clause ← (← (← row.getObjVal? "clause").getArr?).toList.mapM (·.getInt?)
      let hints ← (← (← row.getObjVal? "hints").getArr?).toList.mapM (·.getInt?)
      pure (Obend.Judge.Lrat.Step.add id clause hints)
    pure (.refutation steps)
  else Obend.Judge.Lrat.parseCert s

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
      .refused .marketMalformed [] := by
  change (match Obend.Judge.judge badClearingQuery.market badClearingQuery.orders
      badClearingQuery.transfers badClearingCert with
    | .ok () => Judge.Verdict.ok
    | .error r => .refused r []) = (.refused .marketMalformed [] : Judge.Verdict Obend.Judge.ClearingRefusal)
  decide +kernel

/-- Decode the order-side tag inside a clearing order. -/
def parseClearingSide (side : String) : Except String Obend.Judge.Side :=
  match side with
  | "bid" => .ok .bid
  | "ask" => .ok .ask
  | _ => .error s!"unknown side {side}"

/-- Decode a `ClearingQuery` from JSON for `clearing@1`. -/
def decodeClearingObj (s : String) : Except String Obend.Judge.ClearingQuery := do
  let j ← Json.parse s
  let mJson ← j.getObjVal? "market"
  let currency ← mJson.getObjValAs? Nat "currency"
  let goods ← mJson.getObjValAs? Nat "goods"
  let epsilon ← mJson.getObjValAs? Nat "epsilon"
  let ordersArr ← (← j.getObjVal? "orders").getArr?
  let orders ← ordersArr.toList.mapM fun oJson => do
    let account ← oJson.getObjValAs? Nat "account"
    let sideStr ← oJson.getObjValAs? String "side"
    let side ← parseClearingSide sideStr
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
def decodeClearingCert (s : String) : Except String Obend.Judge.Certificate := do
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
  | malformedBook
  deriving DecidableEq, Repr

/-- Semantic coverage, zero-balance drops, and conservation of the live ledger. -/
def WorldCarrySpecMeaning (w : WorldCarrySpec) (p : WorldCarryWitness) : Prop :=
  w.totalBook = (w.cells.map Prod.snd).sum ∧
  (∀ c ∈ w.cells, c.1 ∈ p.carriedCells ∨ c.1 ∈ p.namedDrops) ∧
  (∀ c ∈ w.cells, c.1 ∈ p.namedDrops → c.2 = 0) ∧
  p.postBook = w.totalBook

/-- Executable check for `"world-carry@1"` obligation format. -/
def checkWorldCarrySpec (w : WorldCarrySpec) (p : WorldCarryWitness) : Judge.Verdict WorldCarryClause :=
  if w.totalBook = (w.cells.map Prod.snd).sum then
    if ∀ c ∈ w.cells, c.1 ∈ p.carriedCells ∨ c.1 ∈ p.namedDrops then
      if ∀ c ∈ w.cells, c.1 ∈ p.namedDrops → c.2 = 0 then
        if p.postBook = w.totalBook then .ok else .refused .bookConservationFailed []
      else .refused .nonZeroDropBalance []
    else .refused .silentCellDrop []
  else .refused .malformedBook []

theorem checkWorldCarrySpec_iff (w : WorldCarrySpec) (p : WorldCarryWitness) :
    checkWorldCarrySpec w p = .ok ↔ WorldCarrySpecMeaning w p := by
  constructor
  · intro h
    unfold checkWorldCarrySpec at h
    split at h
    next hb =>
      split at h
      next hc =>
        split at h
        next hd =>
          split at h
          next hp => exact ⟨hb, hc, hd, hp⟩
          next => cases h
        next => cases h
      next => cases h
    next => cases h
  · intro h
    rw [checkWorldCarrySpec, if_pos h.1, if_pos h.2.1, if_pos h.2.2.1, if_pos h.2.2.2]

/-- Refusal of a malformed ledger is independent of the supplied carry certificate. -/
@[expose, instance_reducible] def worldCarrySpecJudge : Judge WorldCarrySpec WorldCarryWitness where
  Clause := WorldCarryClause
  Meaning := WorldCarrySpecMeaning
  check _ w p := checkWorldCarrySpec w p
  sound := by intro _ w p h; exact (checkWorldCarrySpec_iff w p).mp h
  refutes c := c == .malformedBook
  refuted := by
    intro _ w p clause path h hc p' hm
    have he : clause = .malformedBook := beq_iff_eq.mp hc
    subst clause
    rw [checkWorldCarrySpec, if_pos hm.1] at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h
  Fragment w := w.totalBook = (w.cells.map Prod.snd).sum
  complete := by
    rintro w _ ⟨p, hp⟩
    exact ⟨p, 0, (checkWorldCarrySpec_iff w p).mpr hp⟩
  mono := by intro _ _ _ _ _ _; rfl

def validWorldCarrySpec : WorldCarrySpec :=
  { cells := [("cell.alpha", 100), ("cell.legacy", 0)], totalBook := 100 }

def validWorldCarryWitness : WorldCarryWitness :=
  { carriedCells := ["cell.alpha"], namedDrops := ["cell.legacy"], postBook := 100 }

theorem worldCarrySpecJudge_fragment_inhabited : ∃ w, worldCarrySpecJudge.Fragment w :=
  ⟨validWorldCarrySpec, by
    change validWorldCarrySpec.totalBook = (validWorldCarrySpec.cells.map Prod.snd).sum
    decide +kernel⟩

theorem worldCarrySpecJudge_refusal_inhabited : ∃ w p clause path,
    worldCarrySpecJudge.check 0 w p = .refused clause path ∧
      worldCarrySpecJudge.refutes clause = true := by
  refine ⟨⟨[("cell", 1)], 0⟩, ⟨["cell"], [], 0⟩, .malformedBook, [], ?_, rfl⟩
  change checkWorldCarrySpec ⟨[("cell", 1)], 0⟩ ⟨["cell"], [], 0⟩ = .refused .malformedBook []
  decide +kernel

def badWorldCarrySpec : WorldCarrySpec :=
  { cells := [("cell.alpha", 100), ("cell.unaccounted", 50)], totalBook := 150 }

def badWorldCarryWitness : WorldCarryWitness :=
  { carriedCells := ["cell.alpha"], namedDrops := [], postBook := 150 }

theorem badWorldCarry_refused :
    worldCarrySpecJudge.check 0 badWorldCarrySpec badWorldCarryWitness =
      .refused WorldCarryClause.silentCellDrop [] := by
  change checkWorldCarrySpec badWorldCarrySpec badWorldCarryWitness = .refused .silentCellDrop []
  decide +kernel

def decodeWorldCarryObj (s : String) : Except String WorldCarrySpec := do
  let j ← Json.parse s
  let totalBook ← j.getObjValAs? Nat "totalBook"
  let cellsArr ← (← j.getObjVal? "cells").getArr?
  let cells ← cellsArr.toList.mapM fun cJson => do
    let cid ← cJson.getObjValAs? String "id"
    let bal ← cJson.getObjValAs? Nat "balance"
    pure (cid, bal)
  pure { cells, totalBook }

def decodeWorldCarryCert (s : String) : Except String WorldCarryWitness := do
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
  if o.wellFormed then
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

  else .refused .malformedObject []

/-- Semantic meaning established when `obligationCheckWithJudges formats` returns `.ok`. -/
def obligationMeaningWithJudges (formats : List Judge.Format) (o : ClaimObj) (j : Justification) : Prop :=
  match j with
  | .byDerivation _ => o.wellFormed = true ∧ claimMeaning o
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
  unfold obligationCheckWithJudges at h
  split at h
  next hw =>
   cases j with
   | byDerivation steps =>
    exact ⟨hw, claim_sound h⟩
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

  next hw => cases h

theorem obligationWithJudges_mono (formats : List Judge.Format) {k k' : Nat} {o : ClaimObj} {j : Justification}
    (le : k ≤ k') (hne : obligationCheckWithJudges formats k o j ≠ .uncovered) :
    obligationCheckWithJudges formats k' o j = obligationCheckWithJudges formats k o j := by
  unfold obligationCheckWithJudges at hne ⊢
  split
  next hw =>
   simp only [hw, ite_true] at hne ⊢
   cases j with
   | byDerivation steps =>
     dsimp [obligationCheckWithJudges] at hne ⊢
     exact claimCheck_mono le hne
   | byLoweredLean _ _ _ => rfl
   | byExternalJudge fmt payload =>
     dsimp [obligationCheckWithJudges] at hne ⊢
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

  next hw => simp [hw]

theorem obligationMeaning_wellFormed (formats : List Judge.Format) {o : ClaimObj} {j : Justification}
    (h : obligationMeaningWithJudges formats o j) : o.wellFormed = true := by
  cases j with
  | byDerivation _ => exact h.1
  | byLoweredLean _ _ _ => exact h.2.1
  | byExternalJudge _ _ => exact h.1
  | byEval _ => exact False.elim h

theorem obligation_malformedObject_refutes (formats : List Judge.Format)
    {k : Nat} {o : ClaimObj} {j : Justification} {p : List Nat}
    (h : obligationCheckWithJudges formats k o j = .refused .malformedObject p) :
    ∀ j', ¬ obligationMeaningWithJudges formats o j' := by
  intro j' hm
  have hw := obligationMeaning_wellFormed formats hm
  simp only [obligationCheckWithJudges, hw, ite_true] at h
  cases j <;>
    simp only [claimCheck, hw, ite_true, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
  all_goals
    repeat first | split at h | simp_all [liftVerdict, checkFormatBytes]

/-- Construct a `Judge ClaimObj Justification` backed by `formats`. -/
@[instance_reducible] def obligationJudgeWith (formats : List Judge.Format) : Judge ClaimObj Justification where
  Clause := ClaimClause
  Meaning := obligationMeaningWithJudges formats
  check := obligationCheckWithJudges formats
  sound := by intro k o j h; exact obligationWithJudges_sound formats h
  refutes k := k == .malformedObject
  refuted := by
    intro k o j clause p h hk
    have : clause = .malformedObject := beq_iff_eq.mp hk
    subst clause
    exact obligation_malformedObject_refutes formats h
  Fragment := ClaimFragment
  complete := by
    intro o hf _
    refine ⟨.byDerivation [], 0, ?_⟩
    simp only [obligationCheckWithJudges, hf.1, ite_true]
    exact claimFragment_complete hf
  mono := by intro k k' o j le hne; exact obligationWithJudges_mono formats le hne

theorem obligationJudgeWith_fragment_inhabited (formats : List Judge.Format) :
    ∃ o, (obligationJudgeWith formats).Fragment o := claimJudge_fragment_inhabited

theorem obligationJudgeWith_refusal_inhabited (formats : List Judge.Format) :
    ∃ o j clause p, (obligationJudgeWith formats).check 0 o j = .refused clause p ∧
      (obligationJudgeWith formats).refutes clause = true :=
  ⟨badClaim, .byDerivation [], .malformedObject, [], by
    change obligationCheckWithJudges formats 0 badClaim (.byDerivation []) = .refused .malformedObject []
    simp [obligationCheckWithJudges,
      show badClaim.wellFormed = false from by decide +kernel], rfl⟩

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

@[expose] def Status.label : Status → String
  | .unchecked => "unchecked"
  | .checked .. => "checked"
  | .blocked .. => "blocked"
  | .refuted .. => "refuted"
  | .attested .. => "attested"

/-- The status of claim `o` at the view `C` (the claim at index `j` there): a refutation first,
else the slot's read of the selection. -/
@[expose] def readStatus (o : ClaimObj) (k : Nat) (C : Composition) (selected : Option (List RStep))
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
    the base obligation's derivation `baseSteps` at grade `k`. The target term is a phantom
    interface argument: its observational equivalence is supplied separately to the soundness
    theorem, rather than decided by this checker. -/
def verifyByBisimRefinement (k : Nat) (baseObj : ClaimObj) (baseSteps : List RStep) (_ : Term) :
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
  have hbase : claimMeaning baseObj := claim_sound (k := k) (steps := baseSteps) hcheck
  have href : claimMeaning (baseObj.withLhs lhs') := claimMeaning_of_bEquiv (kind := kind) (lhs := lhs) hbase hsides hbeq
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

/-- **The vertical-refinement claim checker (`superClaimCheck`).** -/
@[expose] def superClaimCheck (k : Nat) (o : ClaimObj) (steps : List RStep) :
    Judge.Verdict ClaimClause :=
  if o.wellFormed then
    match o.sides with
    | some (_, l, r) =>
      liftVerdict (rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps)
    | none => .refused .notAnEquation []
  else .refused .illFormed []


/-- **`superClaim_sound`**: An accepted `superClaimCheck` certificate establishes `claimMeaning o`
across all ground data instances `ds` of length `o.arity`. -/
theorem superClaim_sound {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok) : claimMeaning o := by
  unfold superClaimCheck at h
  split at h
  · rename_i hw
    unfold claimMeaning
    cases hs : o.sides with
    | none => rw [hs] at h; cases h
    | some triple =>
      obtain ⟨kind, l, r⟩ := triple
      rw [hs] at h
      intro ds hl
      obtain ⟨_, _, _, _, _, hoO, hoS⟩ := wellFormed_parts hw
      have hfree : SubstFree (argSubst (o.args ds)) := argSubst_obsFree (by
        intro a ha
        simp only [ClaimObj.args, List.mem_cons, List.mem_map] at ha
        rcases ha with rfl | rfl | ⟨d, _, rfl⟩
        · exact obsFree_of_observes _ hoO
        · exact obsFree_of_observes _ hoS
        · exact data_obsFree d)
      have hr := rewriteWith_ok (liftVerdict_ok h)
      exact holdsEq_of_observed (replay_sound _ (k := .b) ⟨.inl rfl, fun _ => hfree⟩
        (superClaimResolver_sound o hw ds hl) steps (fun e => by cases e) hr)
  · cases h

/-- **`superClaim_holds`**: Together with a ground observation of the claim's left side at `ds`,
an accepted `superClaimCheck` derivation establishes `Holds (instantiateClaim o.claim o.comp o.layer) ds`. -/
theorem superClaim_holds {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {kind : EqKind} {l r : Term} (hs : o.sides = some (kind, l, r))
    (ds : List Data) (hl : ds.length = o.arity)
    {obs : Observation} (hk : kind.accepts obs = true)
    (hlo : Halts (l.substitute (argSubst (o.args ds))) obs) :
    Holds (instantiateClaim o.claim o.comp o.layer) ds := by
  have hm := superClaim_sound h
  unfold claimMeaning at hm
  rw [hs] at hm
  have hw : o.wellFormed = true := by
    unfold superClaimCheck at h
    split at h
    · assumption
    · cases h
  obtain ⟨_, hO, hS, _, _, _, _⟩ := wellFormed_parts hw
  unfold ClaimObj.sides at hs
  obtain ⟨body, hb, he⟩ := Option.bind_eq_some_iff.1 hs
  have hcl := unlams_some hb
  have hargs : ∀ a ∈ o.args ds, Closed a := by
    intro a ha
    simp only [ClaimObj.args, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | rfl | ⟨d, _, rfl⟩
    · exact hO
    · exact hS
    · exact data_closed d
  have hlen : (o.args ds).length = o.arity + 2 := by simp [ClaimObj.args, hl]
  have hβ := betaAll_lams (o.args ds) body hargs
  rw [hlen, ← hcl] at hβ
  have e : apps (instantiateClaim o.claim o.comp o.layer) (ds.map Data.term) =
      apps o.claim (o.args ds) := rfl
  have he' : equationSides (body.substitute (argSubst (o.args ds))) =
      some (kind, l.substitute (argSubst (o.args ds)), r.substitute (argSubst (o.args ds))) := by
    unfold equationSides at he
    split at he
    · cases he; simp [equationSides]
    · cases he; simp [equationSides]
    · obtain ⟨l0, hu, eq0⟩ := Option.map_eq_some_iff.1 he
      cases eq0
      have := unshift_some hu
      subst this
      simp only [Term.substitute, equationSides, liftSubstitution]
      rw [rename_lift_subst, unshift_rename]
      rfl
    · cases he
  exact holds_of_holdsEq (e ▸ hβ) he' (hm ds hl) hk hlo

theorem superClaimCheck_mono {k k' : Nat} {o : ClaimObj} {steps : List RStep} (le : k ≤ k')
    (hne : superClaimCheck k o steps ≠ .uncovered) :
    superClaimCheck k' o steps = superClaimCheck k o steps := by
  unfold superClaimCheck at hne ⊢
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


/-- **Conservative Extension (`superClaimCheck_of_claimCheck`)**:
Every derivation accepted by `claimCheck` is accepted unchanged by `superClaimCheck`. -/
theorem superClaimCheck_of_claimCheck {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : claimCheck k o steps = .ok) : superClaimCheck k o steps = .ok := by
  unfold claimCheck at h
  unfold superClaimCheck
  split at h
  · rename_i hw
    simp only [hw, ite_true]
    cases hs : o.sides with
    | none => rw [hs] at h; cases h
    | some triple =>
      obtain ⟨kind, l, r⟩ := triple
      rw [hs] at h
      have hrw := liftVerdict_ok h
      have hrep := rewriteWith_ok hrw
      unfold rewriteWith at hrw ⊢
      split at hrw
      · rename_i hsz
        simp only [hsz, ite_true]
        have hext : ∀ X m v, claimResolver o.comp o.self X m = some v →
            superClaimResolver o.comp o.self o.layer X m = some v := by
          intro X m v hv
          cases X with
          | bound i =>
            simp only [claimResolver, superClaimResolver] at hv ⊢
            split at hv
            · rename_i hi; simp [hi, hv]
            · cases hv
          | _ => simp [claimResolver] at hv
        simp only [replay_of_resolver_extends hext steps hrep, termEq_refl', ite_true]
        rfl
      · cases hrw
  · cases h



/-- **`superClaimJudge`**: Complete `Judge` instance for vertical-refinement claims. -/
instance superClaimJudge : Judge ClaimObj (List RStep) where
  Clause := ClaimClause
  -- Structural admissibility accompanies the independent ground-equation semantics.
  -- Bool's Prop coercion states the same admissibility as the base claim judge.
  Meaning o _ := o.wellFormed ∧ claimMeaning o
  check := superClaimCheck
  sound := by
    intro k o steps h
    refine ⟨?_, superClaim_sound h⟩
    unfold superClaimCheck at h
    split at h
    · assumption
    · cases h
  refutes k := k == .illFormed
  refuted := by
    intro k o steps clause p h hk c hm
    have : clause = .illFormed := beq_iff_eq.mp hk
    subst clause
    simp only [superClaimCheck, hm.1, ite_true] at h
    cases hs : o.sides with
    | none => simp [hs] at h
    | some x =>
      obtain ⟨kind, l, r⟩ := x
      simp only [hs] at h
      cases hv : rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps <;>
        simp [hv, liftVerdict] at h
  Fragment := ClaimFragment
  complete := by
    intro o hf _
    exact ⟨[], 0, superClaimCheck_of_claimCheck (claimFragment_complete hf)⟩
  mono := by intro k k' o steps le hne; exact superClaimCheck_mono le hne

/-- Which receiver a late-binding support belongs to (`self` vs `super`). -/
inductive ReceiverKind where
  | selfReceiver
  | superReceiver
  deriving DecidableEq, Repr

/-- A receiver-qualified late-binding support: records whether `self.m` or `super.m` was unfolded,
along with the provider layer name and unfolded body `Option (String × Term)`. -/
structure SuperSupport where
  receiver : ReceiverKind
  member   : String
  unfolded : Option (String × Term)

-- Exact trace of `(X, m)` resolver queries performed during `replay R steps t`.
mutual
def traceReplay (R : Resolver) : List RStep → Term → List (Term × String)
  | [], _ => []
  | s :: rest, t =>
    let q1 := traceApply R s t
    match apply R s t with
    | .ok t' => q1 ++ traceReplay R rest t'
    | .error _ => q1

def traceApply (R : Resolver) : RStep → Term → List (Term × String)
  | .run _, _ => []
  | .assoc _, _ => []
  | .composeAssoc _, _ => []
  | .lateBinding m _, t =>
    match t with
    | .get X m' => if m' == m then [(X, m)] else []
    | _ => []
  | .congr C a inner, t =>
    if Obend.Law.termEq t (instantiate C a) && !observes C then
      traceReplay R inner a
    else []
  | .trans first second, t =>
    let q1 := traceReplay R first t
    match replay R first t with
    | .ok t' => q1 ++ traceReplay R second t'
    | .error _ => q1
end

-- Exact Query-Trace Frame Lemma (`traceReplay_frame`):
-- Two resolvers that agree on every `(X, m)` pair in `traceReplay R steps t` produce the exact
-- same `replay` result AND the exact same query trace.
mutual
theorem traceReplay_frame {R R' : Resolver} :
    ∀ (steps : List RStep) (t : Term),
      (∀ p ∈ traceReplay R steps t, R p.1 p.2 = R' p.1 p.2) →
      replay R steps t = replay R' steps t ∧ traceReplay R steps t = traceReplay R' steps t
  | [], _, _ => ⟨rfl, rfl⟩
  | s :: rest, t, h => by
    have h1 : ∀ p ∈ traceApply R s t, R p.1 p.2 = R' p.1 p.2 := by
      intro p hp
      apply h p
      simp only [traceReplay]
      split
      · exact List.mem_append_left _ hp
      · exact hp
    obtain ⟨happ, htr1⟩ := traceApply_frame s t h1
    simp only [replay, traceReplay, ← happ, ← htr1]
    cases ha : apply R s t with
    | error e => exact ⟨rfl, rfl⟩
    | ok t' =>
      have h2 : ∀ p ∈ traceReplay R rest t', R p.1 p.2 = R' p.1 p.2 := by
        intro p hp
        apply h p
        simp only [traceReplay, ha]
        exact List.mem_append_right _ hp
      obtain ⟨hrep, htr2⟩ := traceReplay_frame rest t' h2
      simp [hrep, htr2]

theorem traceApply_frame {R R' : Resolver} :
    ∀ (s : RStep) (t : Term),
      (∀ p ∈ traceApply R s t, R p.1 p.2 = R' p.1 p.2) →
      apply R s t = apply R' s t ∧ traceApply R s t = traceApply R' s t
  | .run _, _, _ => ⟨rfl, rfl⟩
  | .assoc _, _, _ => ⟨rfl, rfl⟩
  | .composeAssoc _, _, _ => ⟨rfl, rfl⟩
  | .lateBinding m lay, t, h => by
    refine ⟨?_, rfl⟩
    simp only [apply]
    cases t with
    | get X m' =>
      simp only [unfoldAt]
      by_cases hm : (m' == m) = true
      · simp only [hm, ite_true]
        have hq : (X, m) ∈ traceApply R (.lateBinding m lay) (.get X m') := by
          simp [traceApply, hm]
        rw [h (X, m) hq]
      · simp [hm]
    | _ => rfl
  | .congr C a inner, t, h => by
    simp only [apply, traceApply] at h ⊢
    by_cases hc : (Obend.Law.termEq t (instantiate C a) && !observes C) = true
    · simp only [hc, ite_true] at h ⊢
      obtain ⟨hrep, htr⟩ := traceReplay_frame inner a h
      simp [hrep, htr]
    · simp [hc]
  | .trans first second, t, h => by
    have h1 : ∀ p ∈ traceReplay R first t, R p.1 p.2 = R' p.1 p.2 := by
      intro p hp
      apply h p
      simp only [traceApply]
      split
      · exact List.mem_append_left _ hp
      · exact hp
    obtain ⟨hrep1, htr1⟩ := traceReplay_frame first t h1
    simp only [apply, traceApply, ← hrep1, ← htr1]
    cases hr1 : replay R first t with
    | error e => exact ⟨rfl, rfl⟩
    | ok t' =>
      have h2 : ∀ p ∈ traceReplay R second t', R p.1 p.2 = R' p.1 p.2 := by
        intro p hp
        apply h p
        simp only [traceApply, hr1]
        exact List.mem_append_right _ hp
      obtain ⟨hrep2, htr2⟩ := traceReplay_frame second t' h2
      simp [hrep2, htr2]
end

/-- Classify a queried `(X, m)` pair at claim arity `arity` (`selfIdx = arity + 1`) into a
`SuperSupport`, ignoring non-`self`/non-`super` variables (where `superClaimResolver` is `none`). -/
def queryToSuperSupport (C : Composition) (arity layer : Nat) : Term × String → Option SuperSupport
  | (.bound i, m) =>
    let selfIdx := arity + 1
    if i == selfIdx then
      some ⟨.selfReceiver, m, symUnfold C selfIdx m⟩
    else if i == arity then
      some ⟨.superReceiver, m, superSymUnfold C selfIdx layer m⟩
    else none
  | _ => none

/-- Extract the exact receiver-qualified `SuperSupport` list of `(o, steps)`. -/
def superSupports (o : ClaimObj) (steps : List RStep) : List SuperSupport :=
  match o.sides with
  | some (_, l, _) =>
    (traceReplay (superClaimResolver o.comp o.self o.layer) steps l).filterMap
      (queryToSuperSupport o.comp o.arity o.layer)
  | none => []

/-- Whether a `SuperSupport` holds at composition `C'` and layer index `j'` for claim arity `arity`. -/
@[expose] def SuperSupport.holds (C' : Composition) (arity j' : Nat) (sp : SuperSupport) : Bool :=
  let selfIdx := arity + 1
  match sp.receiver with
  | .selfReceiver  => optEq (symUnfold C' selfIdx sp.member) sp.unfolded
  | .superReceiver => optEq (superSymUnfold C' selfIdx j' sp.member) sp.unfolded

/-- Packaged vertical-refinement claim certificate recording its `selfSupports` and `superSupports`
explicitly for $O(1)$ support-sheaf transport (`Obend.Slot.SupportSheaf`). -/
structure SuperClaimCert where
  claim         : Term
  arity         : Nat
  grade         : Nat
  steps         : List RStep
  selfSupports  : List Support
  superSupports : List Support

/-- Build a `SuperClaimCert` from a `ClaimObj` and `steps`, splitting `superSupports o steps`
into explicit `selfSupports` and `superSupports` lists. -/
def mkSuperClaimCert (k : Nat) (o : ClaimObj) (steps : List RStep) : SuperClaimCert :=
  let sps := superSupports o steps
  { claim := o.claim
    arity := o.arity
    grade := k
    steps := steps
    selfSupports := sps.filterMap fun sp =>
      match sp.receiver with
      | .selfReceiver => some ⟨sp.member, sp.unfolded⟩
      | .superReceiver => none
    superSupports := sps.filterMap fun sp =>
      match sp.receiver with
      | .selfReceiver => none
      | .superReceiver => some ⟨sp.member, sp.unfolded⟩ }

/-- Combined receiver-qualified support list of a `SuperClaimCert`. -/
@[expose] def SuperClaimCert.allSupports (cert : SuperClaimCert) : List SuperSupport :=
  (cert.selfSupports.map fun s => ⟨.selfReceiver, s.member, s.unfolded⟩) ++
  (cert.superSupports.map fun s => ⟨.superReceiver, s.member, s.unfolded⟩)

theorem mkSuperClaimCert_arity (k : Nat) (o : ClaimObj) (steps : List RStep) :
    (mkSuperClaimCert k o steps).arity = o.arity := by
  unfold mkSuperClaimCert; rfl

theorem mkSuperClaimCert_steps (k : Nat) (o : ClaimObj) (steps : List RStep) :
    (mkSuperClaimCert k o steps).steps = steps := by
  unfold mkSuperClaimCert; rfl

theorem mem_allSupports_of_mem_superSupports {k : Nat} {o : ClaimObj} {steps : List RStep}
    {sp : SuperSupport} (h : sp ∈ superSupports o steps) :
    sp ∈ (mkSuperClaimCert k o steps).allSupports := by
  simp only [SuperClaimCert.allSupports, mkSuperClaimCert, List.mem_append, List.mem_map,
    List.mem_filterMap]
  cases sp with
  | mk rcv m unf =>
    cases rcv with
    | selfReceiver =>
      left
      exact ⟨⟨m, unf⟩, ⟨⟨.selfReceiver, m, unf⟩, h, rfl⟩, rfl⟩
    | superReceiver =>
      right
      exact ⟨⟨m, unf⟩, ⟨⟨.superReceiver, m, unf⟩, h, rfl⟩, rfl⟩

theorem mem_superSupports_of_mem_allSupports {k : Nat} {o : ClaimObj} {steps : List RStep}
    {sp : SuperSupport} (h : sp ∈ (mkSuperClaimCert k o steps).allSupports) :
    sp ∈ superSupports o steps := by
  simp only [SuperClaimCert.allSupports, mkSuperClaimCert, List.mem_append, List.mem_map] at h
  rcases h with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · simp only [List.mem_filterMap] at hs
    obtain ⟨sp0, h0, hmap⟩ := hs
    cases sp0 with
    | mk rcv m unf =>
      cases rcv <;> simp at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h0
  · simp only [List.mem_filterMap] at hs
    obtain ⟨sp0, h0, hmap⟩ := hs
    cases sp0 with
    | mk rcv m unf =>
      cases rcv <;> simp at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h0

theorem optEq_refl (x : Option (String × Term)) : optEq x x = true := by
  cases x with
  | none => rfl
  | some p => simp [optEq, termEq_refl']

theorem superSupports_holds_self (o : ClaimObj) (steps : List RStep) :
    ∀ sp ∈ superSupports o steps, SuperSupport.holds o.comp o.arity o.layer sp = true := by
  intro sp hsp
  simp only [superSupports] at hsp
  split at hsp
  · simp only [List.mem_filterMap] at hsp
    obtain ⟨q, _, hq⟩ := hsp
    cases q with
    | mk X m =>
      cases X with
      | bound i =>
        simp only [queryToSuperSupport] at hq
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true, Option.some.injEq] at hq
          subst hq
          simp [SuperSupport.holds, optEq_refl]
        · simp only [hi1, Bool.false_eq_true, ite_false] at hq
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true, Option.some.injEq] at hq
            subst hq
            simp [SuperSupport.holds, optEq_refl]
          · simp [hi2] at hq
      | _ => simp [queryToSuperSupport] at hq
  · cases hsp

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.filterMap f = xs.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **Coarse Member-List Frame Rule (`superClaim_frame_members`)**:
If both `symUnfold` and `superSymUnfold` agree on every member named in `membersList steps`,
an accepted `superClaimCheck` derivation remains accepted unchanged at `(C', j')`. -/
theorem superClaim_frame_members {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat}
    (hself : ∀ m ∈ membersList steps, symUnfold C' o.self m = symUnfold o.comp o.self m)
    (hsuper : ∀ m ∈ membersList steps,
      superSymUnfold C' o.self j' m = superSymUnfold o.comp o.self o.layer m)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok := by
  unfold superClaimCheck at h ⊢
  rw [hwf]
  split at h
  · simp only [ite_true]
    have hside : ({ o with comp := C', layer := j' } : ClaimObj).sides = o.sides := rfl
    rw [hside]
    split at h
    · rename_i kind l r hs
      change liftVerdict (rewriteWith (superClaimResolver C' o.self j') k l r steps) = .ok
      have hsame : rewriteWith (superClaimResolver C' o.self j') k l r steps =
          rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps := by
        unfold rewriteWith
        rw [replay_frame steps (R := superClaimResolver C' o.self j')
          (R' := superClaimResolver o.comp o.self o.layer) (by
          intro X m hm
          cases X with
          | bound i =>
            simp only [superClaimResolver]
            rw [hself m hm, hsuper m hm]
          | _ => rfl) l]
      rw [hsame]
      exact h
    · cases h
  · cases h

/-- **`T3_super_claim_frame` (Exact Receiver-Qualified Vertical + Horizontal Frame Transport)**:
An accepted `superClaimCheck` certificate remains accepted **unchanged** (and traces the exact
same `superSupports`) in ANY well-formed composition `C'` at layer `j'` where every traced
`SuperSupport` holds — even if outer layers above `j'` in `C'` override members in `superSupports`! -/
theorem T3_super_claim_frame {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat}
    (hsup : ∀ sp ∈ superSupports o steps, SuperSupport.holds C' o.arity j' sp = true)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok ∧
    superSupports { o with comp := C', layer := j' } steps = superSupports o steps := by
  have hw0 : o.wellFormed = true := by
    unfold superClaimCheck at h
    split at h
    · assumption
    · cases h
  unfold superClaimCheck at h ⊢
  simp only [hw0, hwf, ite_true] at h ⊢
  have hside : ({ o with comp := C', layer := j' } : ClaimObj).sides = o.sides := rfl
  rw [hside]
  cases hs : o.sides with
  | none => rw [hs] at h; cases h
  | some triple =>
    obtain ⟨kind, l, r⟩ := triple
    rw [hs] at h
    have hq_agree : ∀ p ∈ traceReplay (superClaimResolver o.comp o.self o.layer) steps l,
        superClaimResolver o.comp o.self o.layer p.1 p.2 =
          superClaimResolver C' o.self j' p.1 p.2 := by
      intro ⟨X, m⟩ hp
      cases X with
      | bound i =>
        simp only [superClaimResolver, ClaimObj.self]
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true]
          have hmem : (⟨.selfReceiver, m, symUnfold o.comp (o.arity + 1) m⟩ : SuperSupport) ∈
              superSupports o steps := by
            simp only [superSupports, hs, List.mem_filterMap]
            exact ⟨(.bound i, m), hp, by simp [queryToSuperSupport, hi1]⟩
          exact (optEq_sound (hsup _ hmem)).symm
        · simp only [hi1, Bool.false_eq_true, ite_false]
          have hpos : o.arity + 1 > 0 := Nat.zero_lt_succ o.arity
          simp only [hpos, decide_true, Bool.true_and, Nat.add_sub_cancel]
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true]
            have hmem : (⟨.superReceiver, m, superSymUnfold o.comp (o.arity + 1) o.layer m⟩ : SuperSupport) ∈
                superSupports o steps := by
              simp only [superSupports, hs, List.mem_filterMap]
              exact ⟨(.bound i, m), hp, by simp [queryToSuperSupport, hi1, hi2]⟩
            exact (optEq_sound (hsup _ hmem)).symm
          · simp [hi2]
      | _ => rfl
    obtain ⟨hrep, htr⟩ := traceReplay_frame steps l hq_agree
    refine ⟨?_, ?_⟩
    · change liftVerdict (rewriteWith (superClaimResolver C' o.self j') k l r steps) = .ok
      have hrw : rewriteWith (superClaimResolver C' o.self j') k l r steps =
          rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps := by
        unfold rewriteWith
        rw [← hrep]
      rw [hrw]
      exact h
    · simp only [superSupports, hside, hs] at htr ⊢
      have hself_eq : ({ o with comp := C', layer := j' } : ClaimObj).self = o.self := rfl
      rw [hself_eq, ← htr]
      apply filterMap_congr_mem
      intro ⟨X, m⟩ hp
      cases X with
      | bound i =>
        simp only [queryToSuperSupport]
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true]
          have heq := hq_agree (.bound i, m) hp
          simp only [superClaimResolver, ClaimObj.self, hi1, ite_true] at heq
          rw [heq]
        · simp only [hi1, Bool.false_eq_true, ite_false]
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true]
            have heq := hq_agree (.bound i, m) hp
            have hpos : o.arity + 1 > 0 := Nat.zero_lt_succ o.arity
            simp only [superClaimResolver, ClaimObj.self, hi1, Bool.false_eq_true, ite_false,
              hpos, decide_true, Bool.true_and, Nat.add_sub_cancel, hi2, ite_true] at heq
            rw [heq]
          · simp [hi2]
      | _ => rfl

/-- Slot formulation of `superClaimCheck` over `SuperSupport`. -/
def superClaimSlot (o : ClaimObj) (k : Nat) : Obend.Slot.Slot SuperSupport (List RStep) where
  supports := superSupports o
  judge steps := superClaimCheck k o steps == .ok

/-- Reading `.usable` from `superClaimSlot` at `(C', j')` guarantees `superClaimCheck = .ok` at `(C', j')`. -/
theorem superUsable_checks {o : ClaimObj} {k : Nat} {steps : List RStep}
    {C' : Composition} {j' : Nat} {ev : List (SuperSupport × Bool)}
    (h : (superClaimSlot o k).read (SuperSupport.holds C' o.arity j') (some steps) = .usable steps ev)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok := by
  have ⟨hj, hall⟩ := (Obend.Slot.read_usable_supports _ _ steps).1 ⟨ev, h⟩
  have hok : superClaimCheck k o steps = .ok := by simpa [superClaimSlot] using hj
  exact (T3_super_claim_frame hok hall hwf).1

/-! ## 4. Concrete 2-Layer & 3-Layer Vertical Refinement Witnesses & Old-`claimCheck` Impossibility -/

/-- Base layer `"Base"`: `limit = 10`, `scale = 2`, `apply = λx. self.scale * x` (open recursion). -/
def verticalBaseLayer : Layer where
  name := "Base"
  metadata := .inject "declared" (.record [("name", .label "Base")])
  fields :=
    [ ("limit", .nat 10)
    , ("scale", .nat 2)
    , ("apply", .lam (.binary .multiply (.get (.bound 2) "scale") (.bound 0))) ]

/-- Refined layer `"Refined"`: overrides `limit = 20`, `scale = 3`, and refines `apply` via `super.apply`. -/
def verticalRefinedLayer : Layer where
  name := "Refined"
  metadata := .inject "declared" (.record [("name", .label "Refined")])
  fields :=
    [ ("limit", .nat 20)
    , ("scale", .nat 3)
    , ("apply", .lam (.binary .add (.app (.get (.bound 1) "apply") (.bound 0)) (.nat 1))) ]

/-- Two-layer composition `⟨Refined, [Base], []⟩`. -/
def verticalComp : Composition :=
  ⟨verticalRefinedLayer, [verticalBaseLayer], []⟩

/-- Vertical spec-refinement claim (`arity = 0`) on `"Refined"` (`layer = 0`):
`λself. λsuper. (self.limit - super.limit) == 10`. -/
def verticalLimitClaimObj : ClaimObj where
  comp := verticalComp
  layer := 0
  claim := .lam (.lam
    (.binary .equal
      (.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit"))
      (.nat 10)))
  arity := 0

/-- Derivation proving `self.limit - super.limit == 10` under `superClaimCheck`:
unfold `self.limit` in `"Refined"` (`20`), unfold `super.limit` in `"Base"` (`10`), step `20 - 10 → 10`. -/
def verticalLimitSteps : List RStep :=
  [ .congr (.binary .subtract (.bound 0) (.get (.bound 1) "limit")) (.get (.bound 1) "limit")
      [.lateBinding "limit" "Refined"]
  , .congr (.binary .subtract (.nat 20) (.bound 0)) (.get (.bound 0) "limit")
      [.lateBinding "limit" "Base"]
  , .run 1 ]

def optTermEqB : Option Term → Option Term → Bool
  | none, none => true
  | some a, some b => Obend.Law.termEq a b
  | _, _ => false

theorem optTermEqB_sound {x y : Option Term} (h : optTermEqB x y = true) : x = y := by
  cases x with
  | none => cases y <;> simp [optTermEqB] at h; rfl
  | some a =>
    cases y with
    | none => simp [optTermEqB] at h
    | some b =>
      simp only [optTermEqB] at h
      exact congrArg some (termEq_sound' h)

/-- **Inhabited Witness 1 (`superClaimCheck` accepts vertical `super.limit` claim)**:
`verticalLimitSteps` is accepted by `superClaimCheck` and establishes `Holds` at `[]`. -/
theorem verticalLimit_superClaim_accepted :
    superClaimCheck 10 verticalLimitClaimObj verticalLimitSteps = .ok ∧
    Holds (instantiateClaim verticalLimitClaimObj.claim verticalComp 0) [] := by
  have hok : superClaimCheck 10 verticalLimitClaimObj verticalLimitSteps = .ok := by
    decide +kernel
  have hrun : Obend.Law.run 100
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute
        (argSubst (verticalLimitClaimObj.args []))) = some (.nat 10) :=
    optTermEqB_sound (by decide +kernel)
  have hhalts : Halts
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute
        (argSubst (verticalLimitClaimObj.args []))) (.natural 10) :=
    ⟨.nat 10, Obend.Law.run_sound 100 hrun, .natural 10⟩
  exact ⟨hok, superClaim_holds hok rfl [] rfl rfl hhalts⟩

/-- Countermodel substitution fixing `self := verticalComp.object` (`limit = 20`) while varying
`super := { limit = 0 }`, witnessing that `claimResolver` is completely blind to `super`. -/
def altSuperSubst : Nat → Term
  | 0 => .record [("limit", .nat 0)]
  | 1 => verticalComp.object
  | n + 2 => .bound n

theorem altSuperSubst_free : SubstFree altSuperSubst := by
  intro n
  match n with
  | 0 => exact obsFree_of_observes (.record [("limit", .nat 0)]) (by decide +kernel)
  | 1 => exact obsFree_of_observes verticalComp.object (by decide +kernel)
  | k + 2 => exact .bound k

theorem altSuperSubst_claimResolver_witness :
    RSound (claimResolver verticalComp 1) altSuperSubst := by
  have hw : verticalLimitClaimObj.wellFormed = true := by decide +kernel
  obtain ⟨_, _, _, hct, hseed, _, _⟩ := wellFormed_parts hw
  intro X m layer u h
  cases X with
  | bound i =>
    simp only [claimResolver] at h
    split at h
    · rename_i hi
      have hi1 : i = 1 := beq_iff_eq.1 hi
      subst hi1
      obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      have hs := steps_substitute altSuperSubst
        (unfoldIn_steps (.bound 1) verticalComp.seed m _ verticalComp.layers hu)
      have hctEq : (composeTerm verticalComp.top verticalComp.below).substitute altSuperSubst =
          composeTerm verticalComp.top verticalComp.below :=
        closed_subst hct altSuperSubst
      have hseedEq : (Term.record verticalComp.seed).substitute altSuperSubst =
          .record verticalComp.seed :=
        closed_subst hseed altSuperSubst
      have e1 : (Term.get (superBelow (.bound 1) verticalComp.seed verticalComp.layers) m).substitute
          altSuperSubst =
          .get (superBelow verticalComp.object verticalComp.seed verticalComp.layers) m := by
        rw [show verticalComp.layers = verticalComp.top :: verticalComp.below from rfl]
        simp only [superBelow, Term.substitute]
        have hrecNil : List.map (fun field : String × Term => (field.1, field.2.substitute altSuperSubst))
            verticalComp.seed = verticalComp.seed := by
          have := hseedEq
          simpa only [Term.substitute, Term.record.injEq] using this
        rw [hctEq, hrecNil]
        rfl
      rw [e1] at hs
      simpa only [Term.substitute, altSuperSubst] using steps_trans (object_get verticalComp m) hs
    · cases h
  | _ => simp [claimResolver] at h

/-- **Universal Separation Theorem (`verticalLimit_impossible_claimCheck`)**:
For EVERY grade `k` and EVERY derivation `steps`, old `claimCheck` CANNOT accept
`verticalLimitClaimObj` (`claimCheck k verticalLimitClaimObj steps ≠ .ok`), whereas
`superClaimCheck` proves it in 3 steps! -/
theorem verticalLimit_impossible_claimCheck (k : Nat) (steps : List RStep) :
    claimCheck k verticalLimitClaimObj steps ≠ .ok := by
  intro hok
  have hw : verticalLimitClaimObj.wellFormed = true := by decide +kernel
  have hside : verticalLimitClaimObj.sides =
      some (.nat, .binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit"), .nat 10) := rfl
  unfold claimCheck at hok
  simp only [hw, ite_true, hside, ClaimObj.self] at hok
  have hrep := rewriteWith_ok (liftVerdict_ok hok)
  have heq : HoldsEq
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst)
      ((Term.nat 10).substitute altSuperSubst) :=
    holdsEq_of_observed (replay_sound (claimResolver verticalComp 1) (k := .b)
      ⟨.inl rfl, fun _ => altSuperSubst_free⟩ altSuperSubst_claimResolver_witness steps
      (fun e => by cases e) hrep)
  have hrun20 : Obend.Law.run 100
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst) =
      some (.nat 20) := optTermEqB_sound (by decide +kernel)
  have hhalts20 : Halts
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst)
      (.natural 20) :=
    ⟨.nat 20, Obend.Law.run_sound 100 hrun20, .natural 20⟩
  obtain ⟨v, hvEval, hvObs⟩ := (heq (.natural 20)).1 hhalts20
  cases hvObs
  simp only [Term.substitute] at hvEval
  have h10_eq_20 : Term.nat 10 = Term.nat 20 :=
    Obend.Law.evaluates_unique ⟨.refl _, .natural 10⟩ hvEval
  cases h10_eq_20

/-- Open-recursion + vertical-refinement claim (`arity = 1`) on `"Refined"` (`layer = 0`):
`∀ x, (super.apply x) + 1 == (3 * x) + 1`, where `Base.apply` calls `self.scale` (overridden to `3`
in `"Refined"`!). -/
def verticalOpenRecClaimObj : ClaimObj where
  comp := verticalComp
  layer := 0
  claim := .lam (.lam (.lam
    (.binary .equal
      (.binary .add (.app (.get (.bound 1) "apply") (.bound 0)) (.nat 1))
      (.binary .add (.binary .multiply (.nat 3) (.bound 0)) (.nat 1)))))
  arity := 1

/-- Derivation proving `∀ x, (super.apply x) + 1 == (3 * x) + 1`:
1. unfold `super.apply` in `"Base"` (yielding `λx. self.scale * x` with `self` kept at `.bound 2`),
2. symbolically β-reduce `(λx. self.scale * x) x` to `self.scale * x`,
3. unfold `self.scale` in `"Refined"` (`3`). -/
def verticalOpenRecSteps : List RStep :=
  [ .congr (.binary .add (.app (.bound 0) (.bound 1)) (.nat 1))
      (.get (.bound 1) "apply")
      [.lateBinding "apply" "Base"]
  , .congr (.binary .add (.bound 0) (.nat 1))
      (.app (.lam (.binary .multiply (.get (.bound 3) "scale") (.bound 0))) (.bound 0))
      [.run 1]
  , .congr (.binary .add (.binary .multiply (.bound 0) (.bound 1)) (.nat 1))
      (.get (.bound 2) "scale")
      [.lateBinding "scale" "Refined"] ]

/-- The `selfSupports` member footprint of `verticalOpenRecClaimObj` is `[ "scale" ]`
(`"apply"` is recorded in `superSupports`, NOT `selfSupports`!). -/
theorem verticalOpenRec_selfSupport_members :
    (mkSuperClaimCert 15 verticalOpenRecClaimObj verticalOpenRecSteps).selfSupports.map (·.member) =
      ["scale"] := by
  decide +kernel

/-- Outer wrapper layer `"AuditWrapper"` overriding `"apply"` (`λx. 999`) while leaving `"scale"` alone. -/
def auditWrapperLayer : Layer where
  name := "AuditWrapper"
  metadata := .inject "declared" (.record [("name", .label "AuditWrapper")])
  fields :=
    [ ("apply", .lam (.nat 999))
    , ("auditTag", .label "v1") ]

/-- Extended 3-layer composition `⟨AuditWrapper, [Refined, Base], []⟩` shifting `"Refined"` to `layer = 1`. -/
def wrappedVerticalComp : Composition :=
  ⟨auditWrapperLayer, [verticalRefinedLayer, verticalBaseLayer], []⟩

/-- **Inhabited Witness 2 (`T3_super_claim_frame` across `"apply"`-overriding wrapper)**:
1. `verticalOpenRecSteps` is accepted at `verticalComp` (`layer = 0`), establishing `claimMeaning`
   across ALL data instances `ds`, and
2. `T3_super_claim_frame` transports `verticalOpenRecSteps` **unchanged** to `wrappedVerticalComp`
   at `layer = 1`, even though `auditWrapperLayer` overrides `"apply"` (`symUnfold` of `"apply"` changed,
   while `superSymUnfold` of `"apply"` at `layer = 1` and `symUnfold` of `"scale"` remain intact!). -/
theorem verticalOpenRec_frame_transport_accepted :
    superClaimCheck 15 verticalOpenRecClaimObj verticalOpenRecSteps = .ok ∧
    symUnfold wrappedVerticalComp 2 "apply" ≠ symUnfold verticalComp 2 "apply" ∧
    superClaimCheck 15 { verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 }
      verticalOpenRecSteps = .ok := by
  have hok0 : superClaimCheck 15 verticalOpenRecClaimObj verticalOpenRecSteps = .ok := by
    decide +kernel
  have hdiff : symUnfold wrappedVerticalComp 2 "apply" ≠ symUnfold verticalComp 2 "apply" := by
    intro heq
    have hneq : optEq (symUnfold wrappedVerticalComp 2 "apply")
        (symUnfold verticalComp 2 "apply") = false := by decide +kernel
    rw [heq] at hneq
    have hrefl : optEq (symUnfold verticalComp 2 "apply")
        (symUnfold verticalComp 2 "apply") = true := by decide +kernel
    rw [hrefl] at hneq
    cases hneq
  have hsup : ∀ sp ∈ superSupports verticalOpenRecClaimObj verticalOpenRecSteps,
      SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1 sp = true := by
    have hall : (superSupports verticalOpenRecClaimObj verticalOpenRecSteps).all
        (SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1) = true := by
      decide +kernel
    exact List.all_eq_true.1 hall
  have hwf : ({ verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 } : ClaimObj).wellFormed = true := by
    decide +kernel
  exact ⟨hok0, hdiff, (T3_super_claim_frame hok0 hsup hwf).1⟩

/-- **Refutation Tooth (`wrongSuperProvider_refused`)**:
Naming `"Refined"` instead of `"Base"` when unfolding `super.limit` is refused with `.stepMismatch`! -/
def wrongSuperProviderSteps : List RStep :=
  [ .congr (.binary .subtract (.nat 20) (.bound 0)) (.get (.bound 0) "limit")
      [.lateBinding "limit" "Refined"] ]

theorem wrongSuperProvider_refused :
    superClaimCheck 10 verticalLimitClaimObj wrongSuperProviderSteps =
      .refused (.rewrite .stepMismatch) [0] := by
  decide +kernel


end Obend.Logic
end

