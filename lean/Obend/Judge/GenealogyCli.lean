module
/-
# `obend genealogy` — a genealogy of judges over the record, on the command line

    obend genealogy genesis JUDGE.json [--store CELL=N]…
        start a genealogy in `genealogy.json` (the working directory): the judge, refused unless well
        formed (`wellFormed`) and its floors hold of the initial store, which is the operator's home.
    obend genealogy show
        the chain, genesis first, each judge with its floors, its checker and its basis; the labels the
        chain carries (its Löb cost); the state.
    obend genealogy succeed JUDGE.json [--lob TRUST]…
        propose a successor to the current judge, labelled with the trust bases it adds; checked by the
        registered format `judge-succession@1` (`Format.checkBytes`), and refused with its reason.
    obend genealogy act (write CELL N | revert | forget) [--as NAME] [--says TEXT]
        propose an action to the current judge (`admits`, under `Exec.faithful`): admitted, or refused
        naming the floor it would break. The proposer and what it says are carried in the proposal and
        read by nothing (`cage_not_inhabitant`).

Exit 0 when admitted, 3 when refused, 2 on a malformed input.
-/
public import Obend.Judge.Genealogy
public section

namespace Obend.Judge.GenealogyCli

open Lean (Json)
open Obend.Judge.Genealogy

set_option autoImplicit false

/-- The genealogy on disk: genesis, the admitted successions, the state. -/
structure Chain where
  genesis : Gate record
  steps : List (Succession record)
  state : Rec

def Chain.judge (c : Chain) : Gate record := lastJudge c.genesis c.steps

def stepJson (σ : Succession record) : Json :=
  Json.mkObj [("state", recJson σ.state), ("next", gateJson σ.next),
    ("lob", Json.arr (σ.labels.map (Json.str ∘ trustText)).toArray)]

def chainJson (c : Chain) : Json :=
  Json.mkObj [("genesis", gateJson c.genesis), ("steps", Json.arr (c.steps.map stepJson).toArray),
    ("state", recJson c.state)]

def chainOf (j : Json) : Except String Chain := do
  let steps ← (← (← j.getObjVal? "steps").getArr?).toList.mapM fun s => do
    return (⟨← recOf (← s.getObjVal? "state"), ← gateOf (← s.getObjVal? "next"),
      ← (← strsOf s "lob").mapM trustOf⟩ : Succession record)
  return ⟨← gateOf (← j.getObjVal? "genesis"), steps, ← recOf (← j.getObjVal? "state")⟩

def file : System.FilePath := "genealogy.json"

def load : IO (Except String Chain) := do
  unless ← file.pathExists do return .error "no genealogy here (obend genealogy genesis JUDGE.json)"
  return (Json.parse (← IO.FS.readFile file)) >>= chainOf

def save (c : Chain) : IO Unit := IO.FS.writeFile file ((chainJson c).pretty ++ "\n")

/-! ## Rendering -/

def storeText (st : Store) : String :=
  if st.isEmpty then "(empty)" else ", ".intercalate (st.map fun (k, v) => s!"{k} = {v}")

def plural (n : Nat) (one many : String) : String := if n = 1 then s!"1 {one}" else s!"{n} {many}"

def stateText (r : Rec) : String :=
  s!"state: {storeText r.store} ({plural r.past.length "judged state" "judged states"} behind; home: {storeText r.home})"

/-- The checker per format: one method for every floor, or each floor's. -/
def checkerText (G : Gate record) : String :=
  "; ".intercalate <| G.formats.map fun f =>
    let ms := G.floors.map fun φ => (φ, G.method f φ)
    let text : Option Method → String := fun | some m => m.text | none => "unchecked"
    match ms with
    | (_, m) :: rest => if rest.all (·.2 == m) then s!"{f} by {text m}"
      else s!"{f} by " ++ ", ".intercalate (ms.map fun (φ, m) => s!"{text m} on {φ}")
    | [] => f

def gateLines (G : Gate record) : List String :=
  [s!"  floors: {", ".intercalate (G.floors.map RecFloor.text)}", s!"  checker: {checkerText G}"]

def basisText (G : Gate record) : String := ", ".intercalate (G.basis.map trustText)

def chainLines (c : Chain) : List String := Id.run do
  let mut out := [s!"genesis {c.genesis.name} (basis {basisText c.genesis})"] ++ gateLines c.genesis
  let mut prev := c.genesis
  let mut i := 1
  for σ in c.steps do
    let lab := if σ.labels.isEmpty then "" else s!", labelled {", ".intercalate (σ.labels.map trustText)}"
    out := out ++ [s!"{i}. {σ.next.name} succeeds {prev.name}{lab} (basis {basisText σ.next})"] ++ gateLines σ.next
    prev := σ.next
    i := i + 1
  let cost := labels c.steps
  out := out ++ [if cost.isEmpty then "Löb cost: none" else s!"Löb cost: {", ".intercalate (cost.map trustText)}"]
  return out ++ [stateText c.state]

def printChain (c : Chain) : IO Unit := for l in chainLines c do IO.println l

def actText : RecAct → String
  | .write c v => s!"write {c} {v}"
  | .revert => "revert"
  | .forget => "forget"

/-- Why the judge refuses an action: the format, or the first floor not discharged. -/
def actRefusal (G : Gate record) (r : Rec) (a : RecAct) : Option String :=
  if !G.formats.contains a.format then some s!"{G.name} does not admit {a.format}"
  else match G.floors.find? (fun φ => !discharge Exec.faithful G r a φ) with
    | some (.home h) => some s!"{actText a} would break `home {h}`: the operator could no longer bring the system home within {h} reverts"
    | some φ => some s!"{actText a} would break `{φ}`"
    | none => none

/-! ## Commands -/

def parseStore : List String → Except String Store
  | [] => .ok []
  | "--store" :: kv :: rest => do
    let st ← parseStore rest
    match kv.splitOn "=" with
    | [k, v] => match v.toNat? with
      | some n => return st.set k n
      | none => throw s!"--store {kv}: `{v}` is not a number"
    | _ => throw s!"--store {kv}: expected CELL=N"
  | a :: _ => .error s!"unexpected argument {a}"

def readGate (path : String) : IO (Except String (Gate record)) := do
  unless ← System.FilePath.pathExists path do return .error s!"no file {path}"
  return (Json.parse (← IO.FS.readFile path)) >>= gateOf

def fail (msg : String) : IO UInt32 := do IO.eprintln msg; return 2

def cmdGenesis (path : String) (rest : List String) : IO UInt32 := do
  let .ok G ← readGate path | fail s!"{path}: not a judge"
  let .ok st := parseStore rest | fail "usage: obend genealogy genesis JUDGE.json [--store CELL=N]…"
  let r : Rec := ⟨st, [], st⟩
  match wellFormed G with
  | .error e => IO.eprintln s!"refused: {e.text G G}"; return 3
  | .ok () =>
    match G.floors.find? (fun φ => !decide (φ.holds r)) with
    | some φ => IO.eprintln s!"refused: the floor `{φ}` of {G.name} does not hold of the initial store"; return 3
    | none =>
      let c : Chain := ⟨G, [], r⟩
      save c
      printChain c
      return 0

def parseLob : List String → Except String (List TrustBase)
  | [] => .ok []
  | "--lob" :: t :: rest => do return (← trustOf t) :: (← parseLob rest)
  | a :: _ => .error s!"unexpected argument {a}"

def cmdSucceed (path : String) (rest : List String) : IO UInt32 := do
  let .ok c ← load | fail "no genealogy here (obend genealogy genesis JUDGE.json)"
  let .ok G' ← readGate path | fail s!"{path}: not a judge"
  let .ok L := parseLob rest | fail "usage: obend genealogy succeed JUDGE.json [--lob TRUST]…"
  let obj := (objJson c.judge c.state).compress
  let cert := (certJson G' L).compress
  match successionFormat.checkBytes 0 obj cert with
  | .ok =>
    let c' : Chain := { c with steps := c.steps ++ [⟨c.state, G', L⟩] }
    save c'
    IO.println (s!"admitted: {G'.name} succeeds {c.judge.name}" ++
      (if L.isEmpty then "" else s!", labelled {", ".intercalate (L.map trustText)}"))
    printChain c'
    return 0
  | _ =>
    IO.eprintln s!"refused: {successionFormat.explain 0 obj cert}"
    return 3

def cmdAct (a : RecAct) (rest : List String) : IO UInt32 := do
  let .ok c ← load | fail "no genealogy here (obend genealogy genesis JUDGE.json)"
  let rec opts : List String → Option (String × String)
    | [] => some ("", "")
    | "--as" :: n :: r => (opts r).map fun (_, s) => (n, s)
    | "--says" :: s :: r => (opts r).map fun (n, _) => (n, s)
    | _ => none
  let some (who, says) := opts rest | fail "usage: obend genealogy act ACTION [--as NAME] [--says TEXT]"
  let p : Proposal record String := ⟨who, .act a, says⟩
  let sys : Sys record := ⟨c.judge, c.state, labels c.steps⟩
  let sys' := sys.step Exec.faithful p
  match actRefusal c.judge c.state a with
  | some why => IO.eprintln s!"refused by {c.judge.name}: {why}"; return 3
  | none =>
    save { c with state := sys'.state }
    IO.println s!"admitted by {c.judge.name}: {actText a}"
    IO.println (stateText sys'.state)
    return 0

def actOf : List String → Option (RecAct × List String)
  | "write" :: cell :: n :: rest => n.toNat?.map fun v => (.write cell v, rest)
  | "revert" :: rest => some (.revert, rest)
  | "forget" :: rest => some (.forget, rest)
  | _ => none

public def main? : List String → Option (IO UInt32)
  | "genealogy" :: "genesis" :: path :: rest => some (cmdGenesis path rest)
  | ["genealogy", "show"] => some do
    let .ok c ← load | fail "no genealogy here (obend genealogy genesis JUDGE.json)"
    printChain c; return 0
  | "genealogy" :: "succeed" :: path :: rest => some (cmdSucceed path rest)
  | "genealogy" :: "act" :: rest => some <| match actOf rest with
    | some (a, rest) => cmdAct a rest
    | none => fail "usage: obend genealogy act (write CELL N | revert | forget) [--as NAME] [--says TEXT]"
  | _ => none

end Obend.Judge.GenealogyCli

end
