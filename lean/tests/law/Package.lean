/-
A package's `law NAME: EXPR` lines become Law terms (Obend.Spec.LawCompile). Run from `lean/`,
after `lake build Obend`:

    lake env lean tests/law/Package.lean

It lowers a one-module package through the front end (`FrontEnd.lower`, as `obend capture` and
`obend run` do), takes its laws as the Law terms a kernel installs on an object of declared state
type `Tally` (`Lowering.lawTerms`), checks each at `lawTy Tally` with the bidirectional checker and
no annotations, and runs each on concrete writes with the reference step (`Obend.Law.run`),
checking that every verdict is the fragment's meaning (`LawExpr.denote`). It fails loudly on any
mismatch.
-/
import Obend.Spec.FrontEnd
import Obend.Law.Run
import Obend.Law.Proofs.Typing

open Lean (Json)
open Obend.Law Obend.Spec Obend.Spec.FrontEnd Obend.Spec.LawCompile Obend.Core.Data Obend.Core.Ty

def source : String := "edition ObjectiveBend 1
record Tally:
  total: Nat
  open: Bool
law bounded: new.total <= 1000 and monotone(total)
law gated: new.open == 0 implies new.total <= request.height
law once: writeOnce(total) or request.caller == 7
def seed() -> Nat:
  0n
"

def tallyTy : Ty := .field "open" .boolean (.field "total" .natural .emptyRow)
def st (o : Bool) (t : Nat) : Data := .record [("open", .boolean o), ("total", .natural t)]

def check (what : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"ok   {what}" else throw (IO.userError s!"FAIL {what}")

def verdict (law : Obend.Core.Term.Term) (o n rq : Data) : Option Bool :=
  let r := run 20000 (applyLaw law o n rq)
  if okB r then some true else if (refusalOf r).isSome then some false else none

#eval show IO Unit from do
  let m : SourceModule := ⟨"Tally", source, "", []⟩
  let limits := Json.mkObj [("heap", "100"), ("stack", "100"), ("ticks", "100")]
  let l ← match lower [m] 0 "seed" (Json.arr #[]) (Json.arr #[]) limits "application" with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"lowering refused: {d.message}")
  check "three laws, by name, in source order" (l.laws.map (·.1) == ["bounded", "gated", "once"])
  let terms := l.lawTerms tallyTy
  for (name, t) in terms do
    check s!"{name}: checks at lawTy Tally, no annotations"
      (Obend.Core.Bidirectional.checkAgainst ⟨t, Obend.Law.Typing.noAnn, {}⟩ [] (lawTy tallyTy)).toBool
  let facts : Obend.Spec.Law.Facts := ⟨some 1, some 7, 50, 3⟩
  let other : Obend.Spec.Law.Facts := ⟨some 1, some 2, 50, 3⟩
  let writes : List (Data × Data) :=
    [(st false 5, st false 7), (st false 5, st false 4), (st true 5, st true 2000), (st false 0, st false 60),
     (st true 9, st true 9), (st true 9, st true 10)]
  for ((name, e), (_, t)) in l.laws.zip terms do
    for fs in [facts, other] do
      for (o, n) in writes do
        let rq := reqOf "ann" "ann" 0 9 writeO fs
        check s!"{name}: write {repr (e.denote fs (some o) n)}"
          (verdict t o n rq == some (e.denote fs (some o) n))
        let rb := reqOf "ann" "ann" 0 9 birthO fs
        check s!"{name}: birth {repr (e.denote fs none n)}"
          (verdict t o n rb == some (e.denote fs none n))
      check s!"{name}: relaw admitted" (verdict t (st false 1) (st false 1) (reqOf "ann" "ann" 0 9 (relawO "L") fs) == some true)
  -- A law outside the fragment refuses at lowering, by name of the construct.
  let bad : SourceModule := ⟨"Bad", source.replace "law once: writeOnce(total)" "law once: old.total == 1", "", []⟩
  check "a law outside the fragment refuses"
    (match lower [bad] 0 "seed" (Json.arr #[]) (Json.arr #[]) limits "application" with
      | .error d => d.message.startsWith Obend.Spec.Law.refusalPrefix || (d.message.splitOn "enforced fragment").length > 1
      | .ok _ => false)
