module
/-
# Obend.Receipt.Export — receipts as JSON, and the consumer that re-checks them

Two receipts, chained:

- an IDENTITY receipt: a conditional identity (`Obend.Judge.Identity`, the statement as data), the
  digest of its CNF encoding, and an LRAT certificate (CaDiCaL's, embedded). Its support is the
  certificate, `checked lrat@1` with trust base `compiled` (the kernel-proved checker run as
  compiled code); its quantifier is `forAll`.
- a WORLD-TRANSITION receipt (`Obend.Receipt.Negotiation`): the admitted dispatch of the commitment
  to `p2`, at the `cited` setting of the dial (the accumulator's rest and the row disclosed, the view
  only through pins), or at `full` (the whole log, replayed); `prev` is the identity receipt's digest.

`verify` is what `obend verify RECEIPT [--prev PREV] [--root ROOT]` runs. It holds no producer state,
and it reads no assurance the producer chose: the quantifier is checked against the law's (`forAll` for
an identity, `existsRun` for a transition), the trust line is the `ceiling` of the supports it ran, and
a transition is checked against an expected root the verifier supplies, never the receipt's own. It decodes the
statement, re-encodes it (`encode`), re-runs the checker on the certificate; for a transition it
decodes the rest and the row, checks their digests against `pre` and `row`, computes each world
opening from its pin by `holdsOfPin`, builds a view from the pins (`realize`; an absent capability
opening is not live), checks that the openings are exactly the row's reads there, and runs `recheck`
(`Obend.Receipt.recheck_sound` says what that establishes); then it re-checks every opening against
the receipt's `dated` root: each proof opens against it (`datedOpens`, cSHAKE256 run as compiled
code), each opening is the value its proof commits (`Reading.matched`), and each pin is the pin the
view committed (`pinCode`). `Obend.Receipt.dated_sound` says what that establishes of any receipt it
accepts: the verdict is the expected view's, or cSHAKE256 collides. `verifyIdentityCore_sound`: an accepted
identity receipt's statement holds.
-/
public import Obend.Receipt.Negotiation
public import Obend.Judge.Identity

public section
namespace Obend.Receipt.Export
open Lean (Json toJson)
open Obend.Receipt.Negotiation
open Obend.Judge.Identity
open Obend.Slot (World)
open Obend.Slot.Protocol.Negotiation (Fact Tok)
open Obend.Run.Negotiation (Wv)
set_option autoImplicit false

/-! ## Common fields -/

def shapeName : Shape → String
  | .existsRun => "existsRun" | .planForAll => "planForAll" | .policyForAll => "policyForAll"
  | .forAllPlan => "forAllPlan" | .forAll => "forAll"

def shapeOf : String → Except String Shape
  | "existsRun" => .ok .existsRun | "planForAll" => .ok .planForAll | "policyForAll" => .ok .policyForAll
  | "forAllPlan" => .ok .forAllPlan | "forAll" => .ok .forAll
  | s => .error s!"unknown quantifier {s}"

def baseJson : Judge.TrustBase → Json
  | .kernel => "kernel"
  | .compiled => "compiled"
  | .external who => Json.mkObj [("external", toJson who)]

def baseOf (j : Json) : Except String Judge.TrustBase :=
  match j.getStr? with
  | .ok "kernel" => .ok .kernel
  | .ok "compiled" => .ok .compiled
  | _ => do pure (.external (← j.getObjValAs? String "external"))

def trustJson : Trust → Json
  | .checked f v b => Json.mkObj [("checked", Json.mkObj [("format", toJson f), ("version", toJson v), ("base", baseJson b)])]
  | .attested p r => Json.mkObj [("attested", Json.mkObj [("principal", toJson p), ("revision", toJson r)])]

def trustOf (j : Json) : Except String Trust := do
  if let .ok c := j.getObjVal? "checked" then
    return .checked (← c.getObjValAs? String "format") (← c.getObjValAs? String "version") (← baseOf (← c.getObjVal? "base"))
  let a ← j.getObjVal? "attested"
  return .attested (← a.getObjValAs? String "principal") (← a.getObjValAs? String "revision")

def supportsJson (ts : List (String × Trust)) : Json :=
  Json.arr (ts.map fun (s, t) => Json.mkObj [("support", toJson s), ("trust", trustJson t)]).toArray

def supportsOf (j : Json) : Except String (List (String × Trust)) := do
  (← j.getArr?).toList.mapM fun e => do pure (← e.getObjValAs? String "support", ← trustOf (← e.getObjVal? "trust"))

def outcomeJson {Clause : Type} (name : Clause → String) : Outcome Clause → Json
  | .ok => "ok"
  | .refused k p => Json.mkObj [("refused", toJson (name k)), ("path", toJson p)]
  | .uncovered => "uncovered"
  | .noAdmissible => "noAdmissible"
  | .awaitingChoice => "awaitingChoice"
  | .preferenceKept => "preferenceKept"
  | .candidateRejected => "candidateRejected"
  | .staleEvidence => "staleEvidence"
  | .executionFrozen => "executionFrozen"

def outcomeOf {Clause : Type} (clauseOf : String → Except String Clause) (j : Json) : Except String (Outcome Clause) :=
  match j.getStr? with
  | .ok "ok" => .ok .ok
  | .ok "uncovered" => .ok .uncovered
  | .ok "noAdmissible" => .ok .noAdmissible
  | .ok "awaitingChoice" => .ok .awaitingChoice
  | .ok "preferenceKept" => .ok .preferenceKept
  | .ok "candidateRejected" => .ok .candidateRejected
  | .ok "staleEvidence" => .ok .staleEvidence
  | .ok "executionFrozen" => .ok .executionFrozen
  | .ok s => .error s!"unknown outcome {s}"
  | .error _ => do
    let k ← clauseOf (← j.getObjValAs? String "refused")
    pure (.refused k (← j.getObjValAs? (List Nat) "path"))

/-- The genesis of a producer's chain. -/
def genesis : Digest := String.mk (List.replicate 64 '0')

/-- A receipt's digest: of its canonical JSON. -/
def receiptDigest (j : Json) : Digest := digestJson j

/-! ## The identity receipt -/

partial def bexpJson : BExp → Json
  | .var i => Json.mkObj [("var", toJson i)]
  | .const b => Json.mkObj [("const", toJson b)]
  | .not a => Json.mkObj [("not", bexpJson a)]
  | .and a b => Json.mkObj [("and", Json.arr #[bexpJson a, bexpJson b])]
  | .or a b => Json.mkObj [("or", Json.arr #[bexpJson a, bexpJson b])]
  | .xor a b => Json.mkObj [("xor", Json.arr #[bexpJson a, bexpJson b])]

partial def bexpOf (j : Json) : Except String BExp := do
  if let .ok i := j.getObjValAs? Nat "var" then return .var i
  if let .ok b := j.getObjValAs? Bool "const" then return .const b
  if let .ok a := j.getObjVal? "not" then return .not (← bexpOf a)
  let two (key : String) : Except String (BExp × BExp) := do
    let a ← (← j.getObjVal? key).getArr?
    let (some x, some y) := (a[0]?, a[1]?) | throw s!"{key}: two operands"
    pure (← bexpOf x, ← bexpOf y)
  if let .ok (a, b) := two "and" then return .and a b
  if let .ok (a, b) := two "or" then return .or a b
  if let .ok (a, b) := two "xor" then return .xor a b
  throw "unknown expression"

def identityJson (d : Identity) : Json :=
  Json.mkObj [("name", toJson d.name), ("inputs", toJson d.inputs), ("hyp", bexpJson d.hyp),
    ("lhs", Json.arr (d.lhs.map bexpJson).toArray), ("rhs", Json.arr (d.rhs.map bexpJson).toArray)]

def identityOf (j : Json) : Except String Identity := do
  pure ⟨← j.getObjValAs? String "name", ← j.getObjValAs? Nat "inputs", ← bexpOf (← j.getObjVal? "hyp"),
    ← (← (← j.getObjVal? "lhs").getArr?).toList.mapM bexpOf, ← (← (← j.getObjVal? "rhs").getArr?).toList.mapM bexpOf⟩

/-- The law of an identity receipt: the format and the encoding. -/
def identityLaw : String := "lrat@1 / Obend.Judge.Identity.encode v1 (Tseitin)"

def refusalName : Judge.Lrat.Refusal → String
  | .noConflict => "noConflict" | .missingHint i => s!"missingHint {i}" | .notUnit i => s!"notUnit {i}"
  | .ratHint i => s!"ratHint {i}" | .noEmptyClause => "noEmptyClause" | .satisfiable => "satisfiable"
  | .notAModel i => s!"notAModel {i}"

/-- The consumer's core: re-encode the statement, re-run the checker on the certificate. -/
def verifyIdentityCore (d : Identity) (cert : Judge.Lrat.Cert) (grade : Nat) : Bool :=
  Judge.Lrat.check grade (encode d) cert == .ok

/-- **An accepted identity receipt's statement holds.** -/
theorem verifyIdentityCore_sound {d : Identity} {cert : Judge.Lrat.Cert} {grade : Nat}
    (h : verifyIdentityCore d cert grade = true) : d.Holds :=
  encode_sound d (Judge.Lrat.check_sound (by simpa [verifyIdentityCore] using h))

def certGrade : Judge.Lrat.Cert → Nat
  | .refutation steps => steps.length
  | .model _ => 0

/-- Produce the identity receipt from the statement and the solver's certificate text. -/
def identityReceipt (d : Identity) (certText : String) (prev : Digest) : Except String Json := do
  let cert ← Judge.Lrat.parseCert certText
  let v := Judge.Lrat.check (certGrade cert) (encode d) cert
  return Json.mkObj [
    ("schema", "obend.receipt.v1"), ("kind", "identity"),
    ("law", toJson (digest identityLaw)), ("pre", toJson genesis), ("post", toJson genesis),
    ("row", toJson (digestJson (identityJson d))), ("pins", Json.arr #[]), ("openings", Json.arr #[]),
    ("verdict", outcomeJson refusalName (Outcome.ofVerdict v)), ("quantifier", "forAll"),
    ("trust", supportsJson [("lrat-certificate", .checked "lrat" "1" .compiled)]),
    ("dated", toJson (0 : Nat)), ("prev", toJson prev),
    ("statement", identityJson d), ("cnf", toJson (digest (encode d).toDimacs)),
    ("certificate", toJson certText)]

/-- What the identity verifier runs itself: the certificate, re-checked by the compiled checker. -/
def identitySupports : List (String × Trust) := [("lrat-certificate", .checked "lrat" "1" .compiled)]

/-- The quantifier a law establishes, checked against the receipt's label rather than read from it. -/
def checkQuantifier (j : Json) (established : Shape) : Except String Unit := do
  let q ← shapeOf (← j.getObjValAs? String "quantifier")
  unless q == established do
    throw s!"quantifier: the law establishes {shapeName established}, the receipt says {shapeName q}"

/-- The trust line, from the ceiling the verifier derives (`Obend.Receipt.ceiling`). -/
def trustLine (ran : List (String × Trust)) (j : Json) : Except String String := do
  match ← ceiling ran (← supportsOf (← j.getObjVal? "trust")) with
  | some (s, .attested p r) => pure s!"attested by {p}@{r} (support {s})"
  | _ => pure "checked"

def verifyIdentity (j : Json) : Except String String := do
  let d ← identityOf (← j.getObjVal? "statement")
  unless (← j.getObjValAs? String "law") == digest identityLaw do throw "law: not lrat@1 over the Tseitin encoding"
  checkQuantifier j .forAll
  unless (← j.getObjValAs? String "row") == digestJson (identityJson d) do throw "row: the statement's digest differs"
  unless (← j.getObjValAs? String "cnf") == digest (encode d).toDimacs do
    throw "cnf: the certificate was produced for another encoding"
  let cert ← Judge.Lrat.parseCert (← j.getObjValAs? String "certificate")
  let claimed ← outcomeOf (fun _ => .ok ()) (← j.getObjVal? "verdict")
  let v := Judge.Lrat.check (certGrade cert) (encode d) cert
  let said := match v with
    | .ok => "accepted"
    | .refused k p => s!"refused: {refusalName k} at {p}"
    | .uncovered => "uncovered"
  unless claimed.isOk == (v == .ok) do
    throw s!"verdict: the receipt says {if claimed.isOk then "ok" else "not ok"}, the checker says {said}"
  let trust ← trustLine identitySupports j
  match v with
  | .ok => return s!"identity {d.name}: holds (lrat@1, {certGrade cert} steps, trust {trust}, base compiled)"
  | _ => return s!"identity {d.name}: a refusal, as recorded ({said}); the statement is not established"

/-! ## The world-transition receipt -/

def pinJson : Fact × Option (Nat × Bool) → Json
  | (f, none) => Json.mkObj [("cell", toJson (factName f)), ("pin", Json.null)]
  | (f, some (c, b)) => Json.mkObj [("cell", toJson (factName f)), ("pin", Json.arr #[toJson c, toJson b])]

def pinOf (j : Json) : Except String (Fact × Option (Nat × Bool)) := do
  let f ← factOf (← j.getObjValAs? String "cell")
  match ← j.getObjVal? "pin" with
  | .null => pure (f, none)
  | p =>
    let a ← p.getArr?
    let (some c, some b) := (a[0]?, a[1]?) | throw "pin: (clock, value)"
    pure (f, some (← c.getNat?, ← b.getBool?))

def openingJson (o : NRead × Bool) : Json := Json.mkObj [("read", toJson (readName o.1)), ("value", toJson o.2)]

def openingOf (j : Json) : Except String (NRead × Bool) := do
  pure (← readOf (← j.getObjValAs? String "read"), ← j.getObjValAs? Bool "value")

def openingProofJson (o : Merkle.Opening) : Json :=
  Json.mkObj [("size", toJson o.size), ("index", toJson o.index), ("value", toJson o.value),
    ("path", Json.arr (o.path.map toJson).toArray)]

def openingProofOf (j : Json) : Except String Merkle.Opening := do
  pure ⟨← j.getObjValAs? Nat "size", ← j.getObjValAs? Nat "index", ← j.getObjValAs? Nat "value",
    ← (← (← j.getObjVal? "path").getArr?).toList.mapM (·.getNat?)⟩

def worldReceiptJson (R : Receipt Fact (Nat × Bool) NRead Obend.Run.Clause) (disclosure : Json) : Json :=
  Json.mkObj [
    ("schema", "obend.receipt.v1"), ("kind", "world-transition"),
    ("law", toJson R.law), ("pre", toJson R.pre), ("post", toJson R.post), ("row", toJson R.row),
    ("pins", Json.arr (R.pins.map pinJson).toArray), ("openings", Json.arr (R.openings.map openingJson).toArray),
    ("verdict", outcomeJson clauseName R.verdict), ("quantifier", toJson (shapeName R.quantifier)),
    ("trust", supportsJson R.trust), ("dated", toJson R.dated),
    ("proofs", Json.arr (R.proofs.map openingProofJson).toArray), ("prev", toJson R.prev),
    ("disclosure", disclosure)]

def worldReceiptOf (j : Json) : Except String (Receipt Fact (Nat × Bool) NRead Obend.Run.Clause) := do
  pure {
    pre := ← j.getObjValAs? String "pre", post := ← j.getObjValAs? String "post",
    row := ← j.getObjValAs? String "row", law := ← j.getObjValAs? String "law",
    pins := ← (← (← j.getObjVal? "pins").getArr?).toList.mapM pinOf,
    openings := ← (← (← j.getObjVal? "openings").getArr?).toList.mapM openingOf,
    verdict := ← outcomeOf clauseOf (← j.getObjVal? "verdict"),
    quantifier := ← shapeOf (← j.getObjValAs? String "quantifier"),
    trust := ← supportsOf (← j.getObjVal? "trust"),
    dated := ← j.getObjValAs? Nat "dated",
    proofs := ← (← (← j.getObjVal? "proofs").getArr?).toList.mapM openingProofOf,
    prev := ← j.getObjValAs? String "prev" }

/-- Produce the receipt of row 4: `cited` discloses the rest and the row; `full` the log up to it.
`shift` moves the world's clock before issuing (Astra's probe: an honestly issued receipt at another
view, whose root is not the expected one); `0` is the receipt of the run. -/
def negotiationReceipt (full : Bool) (prev : Digest) (shift : Nat := 0) : Json :=
  let R := if shift == 0 then receipt4 prev else
    issue admission naming ({ acc4.1 with clock := acc4.1.clock + shift }, acc4.2) row4 .existsRun trust4 prev
  let disclosure := if full then
      Json.mkObj [("dial", "full"), ("log", Json.arr ((log.take 5).map rowJson).toArray)]
    else Json.mkObj [("dial", "cited"), ("rest", restJson acc4.2), ("rowData", rowJson row4)]
  worldReceiptJson R disclosure

/-- The token opening the receipt carries (the host's word, not a pin). Absent, the capability is not
live: the verifier fails closed. -/
def capOpening (os : List (NRead × Bool)) : Bool :=
  match os.find? (fun o => o.1 == .inr .cap) with
  | some o => o.2
  | none => false

/-- What the world-transition verifier runs itself: the fold, re-executed (`recheck`, or the replay
at `full`), and the view, every opening against the dated root. -/
def worldSupports : List (String × Trust) := trust4

/-- Verify a world-transition receipt against `root`, the expected root of the view (the verifier's,
from an authority it chose, never the receipt's). -/
def verifyWorld (j : Json) (root : Option Nat) : Except String String := do
  let R ← worldReceiptOf j
  unless R.law == digest lawId do throw "law: not the negotiation's Legal fold"
  checkQuantifier j .existsRun
  let some expected := root | throw "root: no expected root given; a receipt's own root is the producer's word"
  unless R.dated == expected do throw "root: the receipt is dated at a view whose root is not the expected root"
  let disc ← j.getObjVal? "disclosure"
  let dial ← disc.getObjValAs? String "dial"
  let (rest, row) ← match dial with
    | "cited" => pure (← restOf (← disc.getObjVal? "rest"), ← rowOf (← disc.getObjVal? "rowData"))
    | "full" => do
      let rows ← (← (← disc.getObjVal? "log").getArr?).toList.mapM rowOf
      let some row := rows.getLast? | throw "full: an empty log"
      match admission.run start rows.dropLast with
      | .ok a =>
        unless (admission.run start rows).toBool == R.verdict.isOk do throw "full: the replay disagrees with the verdict"
        pure (a.2, row)
      | .error k => throw s!"full: the prefix is refused by {clauseName k}"
    | d => throw s!"unknown dial {d}"
  unless naming.root rest == R.pre do throw "pre: the disclosed rest is not the receipt's root"
  unless naming.rowDigest row == R.row do throw "row: the disclosed row is not the receipt's"
  -- every world opening is computed from its pin
  for o in R.openings do
    match o.1 with
    | .inl f =>
      match R.pins.lookup f with
      | some p => unless World.holdsOfPin (V := Wv) f p f == o.2 do throw s!"opening {factName f}: not what its pin reads"
      | none => throw s!"opening {factName f}: no pin"
    | .inr _ => pure ()
  let w' := realize R.pins (capOpening R.openings)
  unless R.openings.map Prod.fst == admission.reads (w', rest) row do
    throw "openings: the receipt does not open exactly what the row reads"
  unless recheck admission naming rest row w' R do
    throw "recheck: the row, judged at the view the pins realize, does not give the receipt's verdict and post root"
  -- the view: every opening against the dated root
  unless datedOpens Obend.Core.Digest.deployed R do
    throw "dated: an opening proof does not open against the dated root"
  unless nreading.matched R do
    throw "dated: an opening is not the value its proof commits"
  for (o, p) in R.openings.zip R.proofs do
    match o.1 with
    | .inl f =>
      unless pinCode ((R.pins.lookup f).getD none) == p.value do
        throw s!"dated: the pin of {factName f} is not the pin the dated view committed"
    | .inr _ => pure ()
  let overall ← trustLine worldSupports j
  return s!"world-transition ({dial}): {repr R.verdict.isOk} at the expected view {(hex (Obend.Digest.Cshake256.natBytesBE R.dated)).take 16}…; trust {overall}"

/-! ## The consumer -/

/-- Verify a receipt and, given its predecessor, the link. `root` is the expected root of a
world-transition's view; a predecessor that is a world-transition is checked against its own
expected root, which this command is not given, so it is refused. -/
def verify (j : Json) (prev : Option Json) (root : Option Nat) : Except String (List String) := do
  let schema ← j.getObjValAs? String "schema"
  unless schema == "obend.receipt.v1" do throw s!"schema {schema}"
  let line ← match ← j.getObjValAs? String "kind" with
    | "identity" => verifyIdentity j
    | "world-transition" => verifyWorld j root
    | k => throw s!"unknown kind {k}"
  let p ← j.getObjValAs? String "prev"
  match prev with
  | none => return [line, s!"prev {p} (not checked: no predecessor given)"]
  | some pj =>
    unless receiptDigest pj == p do throw "prev: the predecessor's digest differs"
    let earlier ← match ← pj.getObjValAs? String "kind" with
      | "identity" => verifyIdentity pj
      | "world-transition" => verifyWorld pj none
      | k => throw s!"predecessor: unknown kind {k}"
    return [line, s!"prev: {earlier}", "chain: linked"]

end Obend.Receipt.Export
end
