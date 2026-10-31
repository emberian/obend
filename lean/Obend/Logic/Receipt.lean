module
/-
# Obend.Logic.Receipt — the receipt of a claim, and its re-check from the receipt alone

`review/PROGRAM-LOGIC-20261101.md` §4.3. One receipt per claim, kind `claim`, schema
`obend.receipt.v1`:

    claim       ReviewMember.Twice.repeated
    statement   the quoted claim, its address, the quoted object, layer, arity
    regime      semidecidable; judgment HoldsEq (partial); shape forAll   -- the rewrite certificate
    certificate rewrite@1: the claim's address and the derivation
    supports    member ↦ provider, with the unfolded body
    ground      instances run to true: regime decidable, judgment Holds, shape existsRun
    verdict     ok | refuted (with the instance)

`verifyClaim` re-checks it with no producer state: the statement is decoded by the registered
format (`claimFormat.decodeObj`, refused `malformed` when the stated address is not the quoted
claim's), the certificate must name the same address, `claimFormat.checkBytes` replays it, the
supports are recomputed and compared, and each ground row is re-run. A refuted receipt is re-run at
its instance and must run to `false`.
-/
public import Obend.Logic.Program
@[expose] public section
namespace Obend.Logic.Receipt
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Logic
open Lean (Json toJson)
set_option autoImplicit false

def genesis : String := String.ofList (List.replicate 64 '0')

def natsJson (ds : List Nat) : Json := Json.arr (ds.map fun n => toJson n).toArray

def supportJson (sp : Support) : Json :=
  match sp.unfolded with
  | some (layer, u) => Json.mkObj [("member", toJson sp.member), ("layer", toJson layer), ("unfolded", termJson u)]
  | none => Json.mkObj [("member", toJson sp.member), ("layer", Json.null)]

/-- The ground grade a receipt's instances are run at. -/
def groundFuel : Nat := 1000000

/-- A ground row: the instance and what it ran to. -/
def groundRow (o : ClaimObj) (ds : List Nat) : Json :=
  let v := groundCheck groundFuel ⟨instantiateClaim o.claim o.comp o.layer, ds.map .natural⟩ ()
  let verdict := match v with
    | .ok => "ok"
    | .refused _ _ => "refuted"
    | .uncovered => "uncovered"
  Json.mkObj [("args", natsJson ds), ("verdict", toJson verdict)]

/-- The receipt of a checked claim. -/
def checkedReceipt (name : String) (o : ClaimObj) (steps : List RStep) (ground : List (List Nat)) : Json :=
  Json.mkObj [("schema", toJson "obend.receipt.v1"), ("kind", toJson "claim"), ("claim", toJson name),
    ("statement", statementJson o), ("verdict", toJson "ok"),
    ("format", toJson "rewrite@1"), ("regime", toJson "semidecidable"), ("judgment", toJson "HoldsEq"),
    ("shape", toJson "forAll"), ("trust", toJson "compiled"),
    ("certificate", Json.mkObj [("address", toJson (toString (Obend.Core.Code.address o.claim))),
      ("steps", Json.arr (steps.map rstepJson).toArray)]),
    ("supports", Json.arr ((supports o steps).map supportJson).toArray),
    ("ground", Json.mkObj [("regime", toJson "decidable"), ("judgment", toJson "Holds"), ("shape", toJson "existsRun"),
      ("rows", Json.arr (ground.map (groundRow o)).toArray)]),
    ("prev", toJson genesis)]

/-- The receipt of a refuted claim. -/
def refutedReceipt (name : String) (o : ClaimObj) (ds : List Nat) : Json :=
  Json.mkObj [("schema", toJson "obend.receipt.v1"), ("kind", toJson "claim"), ("claim", toJson name),
    ("statement", statementJson o), ("verdict", toJson "refuted"),
    ("regime", toJson "decidable"), ("judgment", toJson "Holds"), ("shape", toJson "existsRun"), ("trust", toJson "compiled"),
    ("refutation", Json.mkObj [("args", natsJson ds)]), ("prev", toJson genesis)]

def natsOf (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM fun x => x.getNat?

def supportLine (sp : Support) : String :=
  match sp.unfolded with
  | some (layer, _) => s!"{sp.member} ↦ {layer}"
  | none => s!"{sp.member} ↦ (no provider)"

/-- **Re-check a claim receipt** from the receipt and its quoted statement alone. -/
def verifyClaim (j : Json) : Except String (List String) := do
  let name ← j.getObjValAs? String "claim"
  let stmtText := (← j.getObjVal? "statement").compress
  let o ← match claimFormat.decodeObj stmtText with
    | .ok o => pure o
    | .error e => throw s!"malformed: statement: {e}"
  let arity := o.arity
  match ← j.getObjValAs? String "verdict" with
  | "refuted" =>
    let ds ← natsOf (← (← j.getObjVal? "refutation").getObjVal? "args")
    unless ds.length == arity do throw "refutation: the instance does not have the claim's arity"
    match groundCheck groundFuel ⟨instantiateClaim o.claim o.comp o.layer, ds.map .natural⟩ () with
    | .refused .falseAt _ => return [s!"claim {name}: refuted at {ds} (ground, decidable, Holds is false there)"]
    | _ => throw s!"refutation: the claim does not run to false at {ds}"
  | "ok" =>
    let format ← j.getObjValAs? String "format"
    unless format == "rewrite@1" do throw s!"unknown format {format}"
    let cert ← j.getObjVal? "certificate"
    let certAddr ← cert.getObjValAs? String "address"
    unless certAddr == toString (Obend.Core.Code.address o.claim) do
      throw "statementMismatch: the certificate names another claim's address"
    let steps ← match claimFormat.decodeCert cert.compress with
      | .ok s => pure s
      | .error e => throw s!"malformed: certificate: {e}"
    match claimFormat.checkBytes (sizeList steps) stmtText cert.compress with
    | .ok => pure ()
    | _ => match claimCheck (sizeList steps) o steps with
      | .refused k p => throw s!"refused: {repr k} at {p}"
      | _ => throw "refused: the claim checker does not accept the certificate"
    let listed ← (← j.getObjVal? "supports").getArr?
    let computed := supports o steps
    unless listed.size == computed.length do throw "supports: the listed supports are not the derivation's"
    for (l, sp) in listed.toList.zip computed do
      unless (← l.getObjValAs? String "member") == sp.member do throw "supports: a member differs"
      match sp.unfolded, (l.getObjValAs? String "layer").toOption with
      | some (layer, u), some layer' =>
        unless layer == layer' do throw s!"supports: {sp.member} is provided by {layer}, not {layer'}"
        let u' ← termOf (← l.getObjVal? "unfolded")
        unless Obend.Law.termEq u u' do throw s!"supports: {sp.member} unfolds otherwise"
      | none, none => pure ()
      | _, _ => throw s!"supports: {sp.member} differs"
    let mut lines := [s!"claim {name}: HoldsEq for every instance (rewrite@1, {sizeList steps} steps, semidecidable, trust compiled)",
      s!"statement: address {certAddr}, layer {o.layer}, arity {arity}",
      "supports: " ++ ", ".intercalate (computed.map supportLine)]
    let rows ← (← (← j.getObjVal? "ground").getObjVal? "rows").getArr?
    for row in rows.toList do
      let ds ← natsOf (← row.getObjVal? "args")
      let stated ← row.getObjValAs? String "verdict"
      let again := (groundRow o ds).getObjValAs? String "verdict" |>.toOption.getD ""
      unless stated == again do throw s!"ground: {ds} ran to {again}, not {stated}"
      lines := lines ++ [s!"ground {ds}: {again} (decidable, Holds)"]
    return lines
  | v => throw s!"unknown verdict {v}"

end Obend.Logic.Receipt
end
