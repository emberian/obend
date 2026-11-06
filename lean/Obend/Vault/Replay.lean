module
/-
# Obend.Vault.Replay — the deployed entry's world is the replay of its log

`obend open` and every command after it (`Obend.Vault.Cli`, `Obend.Ledger.Cli`) change the world beside a
vault by TURNS, and only by turns: each is encoded (`encodeTurn`), admitted by the log
(`Obend.Vault.Log.admit` at `deployed`), appended to `.obend/log` as a record, and only then are its
files written. The world a command serves is the step of the DECODED turn, so the process and a later
replay of the log step the same bytes the same way. The turns:

* `opened`: an open, with the files it read (`readingOf`: each file's text where it differs from the
  text the world last saw, else none; `open_replays`: the record replays as the open of exactly those
  files) and the environment it read, when that changed;
* `member`, `wrote` (the owner's post), `posted` (a member's), `selected`, `recited`, `merged` (another
  replica's world, as read, merged by `Obend.Vault.Merge.mergeVault`), `resolved` (a merge conflict
  the store keeps, `Store.conflicts`, resolved by `Merge.resolveIn`); each is the store function its
  command always called, then `settle`;
* `captured`, `abstracted`, `judged`, `filled`: the forms (`Obend.Vault.Form`). The forms a vault
  issued, the receipt chain of the proposals it judged, and the forms it received and the proposals it
  sent are fields of the world; `.obend/forms/*.json` are exports of them, written after the turn;
* `rows`: rows committed to the register, all or none (`Obend.Ledger.Cli.commitRows`): the journal is
  part of the world, and the log is its only record (it was `.obend/ledger.json`);
* `base`: a world from before the log (`.obend/world.json` and `.obend/ledger.json` of a vault opened by
  an earlier `obend`), adopted as the log's first record.

`.obend/checkpoint` holds the world after the log's first records, anchored to the last of them: a
cache (`checkpoint_is_cache`). The theorems are `Obend.Vault.Log`'s at the deployed machine:
`state_eq_replay_log`, `recover_eq_replay_prefix`, `checkpoint_is_cache`, `log_wellLinked`.

Out of scope: migration-time relinking (replaying a log under a changed step); a log is replayed by
the step that wrote it.
-/
public import Obend.Vault.Log
public import Obend.Vault.Json
public import Obend.Ledger.Commit
public import Obend.Vault.Form
public import Obend.Vault.Merge
public import Obend.Digest.Cshake256
@[expose] public section

namespace Obend.Vault.Replay

set_option autoImplicit false

open Lean (Json toJson fromJson?)
open Obend.Vault Obend.Vault.Json Obend.Vault.Log
open Obend.Ledger Obend.Ledger.Json
open Obend.Ledger.Cli (registerLaws commitRows RowFiles)

/-- The deployed byte hash of a vault's cites (cSHAKE256, as `lean/tests/doc/RoundTrip.lean`). -/
def H : Obend.Digest.HashBytes.Hash := Obend.Digest.Cshake256.cshake256Bytes []

/-- The log's digest: cSHAKE256 customized `obend-log`. -/
def logHash (b : Bytes) : Bytes := Obend.Digest.Cshake256.cshake256Bytes "obend-log".toUTF8.toList b

/-! ## The world and its turns -/

deriving instance DecidableEq for Page
deriving instance DecidableEq for PageWrite
deriving instance DecidableEq for PageConflict
deriving instance DecidableEq for Store
deriving instance DecidableEq for Journal
deriving instance DecidableEq for Obend.Vault.Form.Cell
deriving instance DecidableEq for Obend.Vault.Form.Form

open Obend.Vault.Form (Form Grant Assignment Admitted)
open Obend.Vault.Rehydration (WitnessReceipt)

/-- The world beside a vault: the store of its pages and members (with the merges' open conflicts),
the register's journal, the forms it issued, the receipt chain of the proposals it judged, and the
forms it received and the proposals it sent (each by form name, the text it exports). -/
structure World where
  store : Store := {}
  journal : Journal := Journal.empty
  forms : List Form := []
  receipts : List WitnessReceipt := []
  received : List (String × String) := []
  sent : List (String × String) := []
deriving DecidableEq

/-- One turn of the deployed entry. -/
inductive Turn
  | base (w : World)
  | opened (files : List (String × Option String)) (env : Option (List String))
  | member (name : String) (grants : List (String × String))
  | wrote (page text : String)
  | posted (who page text : String)
  | selected (who : Option String) (page : String) (k i : Nat)
  | recited (who : Option String) (page : String)
  | merged (label : String) (other : Store) (skipLedger : Bool)
  | resolved (k : Nat) (right : Bool)
  | rows (rs : List Row)
  | captured (situation name : String) (g : Grant) (src dst : String) (amount : Nat) (field : String)
      (refs : List String)
  | abstracted (name value hole : String)
  | judged (name digest : String) (hops : List Grant) (a : Assignment)
  | filled (name received sent : String)

/-- What a turn says beside the world it leaves (a command's store before `settle`, where it reports
on it, as it always did). -/
inductive Outcome
  | quiet
  | opened (f : Forgotten) (o : Opened)
  | wrote (unsettled : Store) (version : Nat)
  | changed (unsettled : Store)
  | recited (unsettled : Store) (n : Nat)
  | merged (unsettled : Store) (notes : List String)
  | resolved (unsettled : Store) (receipt : String)
  | rows (files : List RowFiles)
  | form (f : Form) (culled : Nat)
  | judged (unsettled : Store) (ad : Admitted) (t : VaultTurn) (r : WitnessReceipt) (count : Nat)

/-- The text the world last saw of a page's file. -/
def seenOf (s : Store) (n : String) : Option String := (s.page? n).bind (·.seen)

/-- **What an open read, as its record carries it**: each file by name, with its text where it is not
the text the world last saw of it. -/
def readingOf (s : Store) (V : List (String × String)) : List (String × Option String) :=
  V.map fun (n, t) => (n, if seenOf s n == some t then none else some t)

/-- The files a record of an open names, read back against the world before it. -/
def reconstruct (s : Store) (files : List (String × Option String)) : List (String × String) :=
  files.map fun (n, o) => (n, o.getD ((seenOf s n).getD ""))

/-- The environment an open read, as its record carries it: none when it is the world's. -/
def envOf (s : Store) (env : Environment) : Option (List String) :=
  if env == s.environment then none else some env.toList

/-- The record of an open carries exactly the files it read. -/
theorem reconstruct_readingOf (s : Store) (V : List (String × String)) :
    reconstruct s (readingOf s V) = V := by
  induction V with
  | nil => rfl
  | cons x V ih =>
    obtain ⟨n, t⟩ := x
    simp only [reconstruct, readingOf, List.map_cons] at ih ⊢
    rw [ih]
    by_cases h : seenOf s n = some t <;> simp [h]

/-- ... and the environment. -/
theorem envOf_read (s : Store) (env : Environment) :
    ((envOf s env).map List.toArray).getD s.environment = env := by
  unfold envOf
  by_cases h : env = s.environment
  · simp [h]
  · simp [h]

/-- **The step of a turn**: the store function its command calls, or a refusal (a refused turn is
never logged). -/
def stepTurn (w : World) : Turn → Except String (World × Outcome)
  | .base w' => .ok (w', .quiet)
  | .opened files env =>
    let V := reconstruct w.store files
    let s := { w.store with environment := (env.map List.toArray).getD w.store.environment }
    let f := forgetMissing s V
    let o := openVault H f.store V
    .ok ({ w with store := o.store }, .opened f o)
  | .member name grants =>
    match addMember w.store name grants with
    | .ok s => .ok ({ w with store := s }, .quiet)
    | .error e => .error e
  | .wrote page text =>
    match w.store.page? page with
    | none => .error ("refused: no page named " ++ page)
    | some p =>
      let ch := judgeAt H w.store.entries w.store p text
      match ch.note with
      | some why => .error (page ++ ": " ++ why)
      | none =>
        let s := w.store.setPage (p.withChange ch)
        .ok ({ w with store := settle H s }, .wrote s ch.history.length)
  | .posted who page text =>
    match w.store.actor (some who) >>= fun a => postAs H w.store a page text with
    | .ok s => .ok ({ w with store := settle H s }, .changed s)
    | .error e => .error e
  | .selected who page k i =>
    match w.store.actor who >>= fun a => selectIn w.store a page k i with
    | .ok s => .ok ({ w with store := settle H s }, .changed s)
    | .error e => .error e
  | .recited who page =>
    match w.store.actor who >>= fun a => reciteIn H w.store a page with
    | .ok (s, n) => .ok ({ w with store := settle H s }, .recited s n)
    | .error e => .error e
  | .merged label other skipLedger =>
    let (s, notes) := Merge.mergeVault w.store other label
      (skip := if skipLedger then Obend.Ledger.Cli.ledgerOwned else fun _ => false)
    .ok ({ w with store := settle H s }, .merged s notes)
  | .resolved k right =>
    match Merge.resolveIn w.store k (if right then .right else .left) with
    | .ok (s, receipt) => .ok ({ w with store := settle H s }, .resolved s receipt)
    | .error e => .error ("not resolved: " ++ e)
  | .captured situation name g src dst amount field refs =>
    if w.forms.any (·.name == name) then .error ("refused: a form named " ++ name ++ " exists") else
    match Form.captureFrom w.store situation name g src dst amount field refs with
    | .ok (f, culled) => .ok ({ w with forms := w.forms ++ [f] }, .form f culled)
    | .error e => .error ("refused: " ++ e)
  | .abstracted name value hole =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name)
    | some f =>
      match f.abstract value hole with
      | .ok g => .ok ({ w with forms := w.forms.map fun x => if x.name == name then g else x }, .form g 0)
      | .error e => .error ("refused: " ++ e)
  | .judged name digest hops a =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name ++ " here")
    | some f =>
      if digest != Form.formDigest H f then
        .error (name ++ ": refused: the form has changed since this proposal's copy was sent; send the form again")
      else
        match Form.judgeProposal H w.store f hops a with
        | .error e => .error (name ++ ": " ++ e)
        | .ok (s, ad, t) =>
          let r := Form.receiptFor H w.receipts.getLast? f a ad t
          .ok ({ w with store := settle H s, receipts := w.receipts ++ [r] },
            .judged s ad t r (w.receipts.length + 1))
  | .filled name received sent =>
    .ok ({ w with received := (w.received.filter (·.1 != name)) ++ [(name, received)],
                  sent := (w.sent.filter (·.1 != name)) ++ [(name, sent)] }, .quiet)
  | .rows rs =>
    match registerLaws w.store with
    | .error e => .error e
    | .ok laws =>
      match commitRows laws w.journal rs with
      | .ok (J, fs) => .ok ({ w with journal := J }, .rows fs)
      | .error e => .error e

/-- **An open's record replays as that open**: the turn an open of the files `V`, with the
environment `env`, appends steps the world exactly as the open of `V` under `env`. -/
theorem open_replays (w : World) (V : List (String × String)) (env : Environment) :
    stepTurn w (.opened (readingOf w.store V) (envOf w.store env)) =
      let f := forgetMissing { w.store with environment := env } V
      let o := openVault H f.store V
      .ok ({ w with store := o.store }, .opened f o) := by
  simp only [stepTurn, reconstruct_readingOf, envOf_read]

/-! ## Bytes -/

def strsJson (xs : List String) : Json := Json.arr (xs.map Json.str).toArray

def strsOf (j : Json) : Except String (List String) := do
  (← j.getArr?).toList.mapM fun e => e.getStr?

def pairsJson (xs : List (String × String)) : Json :=
  Json.arr (xs.map fun (a, b) => Json.arr #[Json.str a, Json.str b]).toArray

def pairsOf (j : Json) : Except String (List (String × String)) := do
  (← j.getArr?).toList.mapM fun e => do
    return (← (← e.getArrVal? 0).getStr?, ← (← e.getArrVal? 1).getStr?)

def optStrJson : Option String → Json
  | some s => Json.str s
  | none => Json.null

def optStrOf (j : Json) : Except String (Option String) :=
  match j with
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error "a string or null"

/-- A store with its environment (which `.obend/world.json` never kept: it was read at every open). -/
def fullStoreJson (s : Store) : Json :=
  (storeJson s).setObjVal! "environment" (strsJson s.environment.toList)

def fullStoreOf (j : Json) : Except String Store := do
  let s ← storeOf j
  let env ← match j.getObjVal? "environment" with
    | .ok e => strsOf e
    | .error _ => pure []
  return { s with environment := env.toArray }

def namedTextsJson (xs : List (String × String)) : Json := pairsJson xs

def worldJson (w : World) : Json :=
  Json.mkObj [("store", fullStoreJson w.store), ("journal", journalJson w.journal),
    ("forms", Json.arr (w.forms.map Form.formJson).toArray),
    ("receipts", Json.arr (w.receipts.map Form.receiptJson).toArray),
    ("received", pairsJson w.received), ("sent", pairsJson w.sent)]

def worldOf (j : Json) : Except String World := do
  let store ← fullStoreOf (← j.getObjVal? "store")
  let journal ← journalOf (← j.getObjVal? "journal")
  let forms ← (← j.getObjValAs? (Array Json) "forms").toList.mapM Form.formOf
  let receipts ← (← j.getObjValAs? (Array Json) "receipts").toList.mapM Form.receiptOf
  let received ← pairsOf (← j.getObjVal? "received")
  let sent ← pairsOf (← j.getObjVal? "sent")
  return ⟨store, journal, forms, receipts, received, sent⟩

def turnJson : Turn → Json
  | .base w => Json.mkObj [("turn", "base"), ("world", worldJson w)]
  | .opened files env => Json.mkObj [("turn", "open"),
      ("files", Json.arr (files.map fun (n, t) => Json.arr #[Json.str n, optStrJson t]).toArray),
      ("environment", match env with | some e => strsJson e | none => Json.null)]
  | .member name grants => Json.mkObj [("turn", "member"), ("name", Json.str name), ("grants", pairsJson grants)]
  | .wrote page text => Json.mkObj [("turn", "write"), ("page", Json.str page), ("text", Json.str text)]
  | .posted who page text => Json.mkObj [("turn", "post"), ("as", Json.str who), ("page", Json.str page),
      ("text", Json.str text)]
  | .selected who page k i => Json.mkObj [("turn", "select"), ("as", optStrJson who), ("page", Json.str page),
      ("section", toJson k), ("candidate", toJson i)]
  | .recited who page => Json.mkObj [("turn", "recite"), ("as", optStrJson who), ("page", Json.str page)]
  | .merged label other skip => Json.mkObj [("turn", "merge"), ("label", Json.str label), ("other", storeJson other),
      ("skipLedger", toJson skip)]
  | .resolved k right => Json.mkObj [("turn", "resolve"), ("conflict", toJson k), ("right", toJson right)]
  | .rows rs => Json.mkObj [("turn", "rows"), ("rows", Json.arr (rs.map rowJson).toArray)]
  | .captured situation name g src dst amount field refs => Json.mkObj [("turn", "capture"),
      ("situation", Json.str situation), ("name", Json.str name), ("grant", Form.grantJson g),
      ("src", Json.str src), ("dst", Json.str dst), ("amount", toJson amount), ("field", Json.str field),
      ("refs", strsJson refs)]
  | .abstracted name value hole => Json.mkObj [("turn", "abstract"), ("name", Json.str name),
      ("value", Json.str value), ("hole", Json.str hole)]
  | .judged name digest hops a => Json.mkObj [("turn", "judge"), ("name", Json.str name),
      ("digest", Json.str digest), ("hops", Json.arr (hops.map Form.grantJson).toArray),
      ("fill", Form.assignmentJson a)]
  | .filled name received sent => Json.mkObj [("turn", "fill"), ("name", Json.str name),
      ("received", Json.str received), ("sent", Json.str sent)]

def turnOf (j : Json) : Except String Turn := do
  match ← j.getObjValAs? String "turn" with
  | "base" => return .base (← worldOf (← j.getObjVal? "world"))
  | "open" =>
    let files ← (← j.getObjValAs? (Array Json) "files").toList.mapM fun e => do
      return (← (← e.getArrVal? 0).getStr?, ← optStrOf (← e.getArrVal? 1))
    let env ← match ← j.getObjVal? "environment" with
      | .null => pure none
      | e => some <$> strsOf e
    return .opened files env
  | "member" => return .member (← j.getObjValAs? String "name") (← pairsOf (← j.getObjVal? "grants"))
  | "write" => return .wrote (← j.getObjValAs? String "page") (← j.getObjValAs? String "text")
  | "post" =>
    let who ← j.getObjValAs? String "as"
    let page ← j.getObjValAs? String "page"
    return .posted who page (← j.getObjValAs? String "text")
  | "select" =>
    let who ← optStrOf (← j.getObjVal? "as")
    let page ← j.getObjValAs? String "page"
    let k ← j.getObjValAs? Nat "section"
    return .selected who page k (← j.getObjValAs? Nat "candidate")
  | "recite" => return .recited (← optStrOf (← j.getObjVal? "as")) (← j.getObjValAs? String "page")
  | "merge" =>
    let label ← j.getObjValAs? String "label"
    let other ← storeOf (← j.getObjVal? "other")
    return .merged label other (← j.getObjValAs? Bool "skipLedger")
  | "resolve" => return .resolved (← j.getObjValAs? Nat "conflict") (← j.getObjValAs? Bool "right")
  | "rows" => return .rows (← (← j.getObjValAs? (Array Json) "rows").toList.mapM rowOf)
  | "capture" =>
    let situation ← j.getObjValAs? String "situation"
    let name ← j.getObjValAs? String "name"
    let g ← Form.grantOf (← j.getObjVal? "grant")
    let src ← j.getObjValAs? String "src"
    let dst ← j.getObjValAs? String "dst"
    let amount ← j.getObjValAs? Nat "amount"
    let field ← j.getObjValAs? String "field"
    return .captured situation name g src dst amount field (← strsOf (← j.getObjVal? "refs"))
  | "abstract" =>
    let name ← j.getObjValAs? String "name"
    let value ← j.getObjValAs? String "value"
    return .abstracted name value (← j.getObjValAs? String "hole")
  | "judge" =>
    let name ← j.getObjValAs? String "name"
    let digest ← j.getObjValAs? String "digest"
    let hops ← (← j.getObjValAs? (Array Json) "hops").toList.mapM Form.grantOf
    return .judged name digest hops (← Form.assignmentOf (← j.getObjVal? "fill"))
  | "fill" =>
    let name ← j.getObjValAs? String "name"
    let received ← j.getObjValAs? String "received"
    return .filled name received (← j.getObjValAs? String "sent")
  | t => throw ("not a turn: " ++ t)

def textBytes (s : String) : Bytes := s.toUTF8.toList

def bytesText (b : Bytes) : Option String := String.fromUTF8? ⟨b.toArray⟩

/-- A turn's bytes: its JSON, compressed, in UTF-8. -/
def encodeTurn (t : Turn) : Bytes := textBytes (turnJson t).compress

def decodeTurn (b : Bytes) : Except String Turn := do
  let some s := bytesText b | throw "a turn is not UTF-8"
  turnOf (← Json.parse s)

/-- **The world's canonical bytes**, whose digest a receipt names as its commitment, and which a
checkpoint holds. -/
def encodeWorld (w : World) : Bytes := textBytes (worldJson w).compress

def decodeWorld (b : Bytes) : Option World :=
  (bytesText b).bind fun s => (Json.parse s >>= worldOf).toOption

/-- The name of a turn, said. -/
def Turn.kind : Turn → String
  | .base _ => "base"
  | .opened .. => "open"
  | .member .. => "member"
  | .wrote .. => "write"
  | .posted .. => "post"
  | .selected .. => "select"
  | .recited .. => "recite"
  | .merged .. => "merge"
  | .resolved .. => "resolve"
  | .rows .. => "rows"
  | .captured .. => "capture"
  | .abstracted .. => "abstract"
  | .judged .. => "judge"
  | .filled .. => "fill"

/-! ## The deployed machine and its theorems -/

/-- **The deployed machine**: a record's bytes are decoded to a turn and stepped by `stepTurn`. -/
def deployed : Machine World Outcome where
  step w b := do stepTurn w (← decodeTurn b)
  encW := encodeWorld

/-- The world before any turn. -/
def genesis : World := {}

/-- A process's session over a vault: the world it serves and the records it appended. -/
abbrev Session := Log.Session World

/-- The sessions the deployed entry passes through: genesis, then turns it admitted. -/
abbrev Reachable : Session → Prop := Log.Reachable logHash deployed genesis

/-- **`state_eq_replay_log`**: the world the deployed entry serves after any sequence of admitted turns
is the replay of its log. -/
theorem state_eq_replay_log {S : Session} (h : Reachable S) : S.world = replay deployed genesis S.log :=
  Log.state_eq_replay_log h

/-- The log the deployed entry writes is Pillar 1's receipt chain: newest first, `wellLinked`. -/
theorem log_wellLinked {S : Session} (h : Reachable S) :
    Obend.Vault.Rehydration.wellLinked (Hr logHash) (S.log.map (·.receipt)).reverse :=
  Log.log_wellLinked h

/-- **`recover_eq_replay_prefix`**: a crash at any byte of the deployed entry's log recovers the replay
of the longest prefix of whole records, a world the entry served, and names the rest a torn tail. -/
theorem recover_eq_replay_prefix {S : Session} (h : Reachable S) (k : Nat) :
    let m := whole logHash S.log k
    let tail := ((encodeAll logHash S.log).take k).drop (encodeAll logHash (S.log.take m)).length
    recover logHash deployed genesis ((encodeAll logHash S.log).take k) =
        ⟨replay deployed genesis (S.log.take m), m, tail, tornWhy tail⟩ ∧
      Reachable ⟨replay deployed genesis (S.log.take m), S.log.take m⟩ :=
  Log.recover_eq_replay_prefix h k

/-- **`checkpoint_is_cache`**: at every truncation of the deployed entry's log, recovering from a
checkpoint it wrote is recovering from genesis. The premise is the check the entry makes before it
writes a checkpoint: the world's bytes decode to the world. -/
theorem checkpoint_is_cache {S : Session} (h : Reachable S) {n : Nat} (hn0 : 0 < n) (hn : n ≤ S.log.length)
    (hcache : decodeWorld (encodeWorld (replay deployed genesis (S.log.take n))) =
      some (replay deployed genesis (S.log.take n))) (k : Nat) :
    recoverWith logHash deployed decodeWorld genesis (checkpointAt logHash deployed genesis S.log n)
        ((encodeAll logHash S.log).take k) =
      recover logHash deployed genesis ((encodeAll logHash S.log).take k) :=
  Log.checkpoint_is_cache h hn0 hn hcache k

end Obend.Vault.Replay

end
