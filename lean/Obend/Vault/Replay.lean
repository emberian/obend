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
* `issued`, `offered`, `granted`, `revoked`, `transported`, `proposed`, `confirmed`: the transport of
  forms (`Obend.Vault.Transport`): the basis a form is issued under and its continuity contract, the
  vault's standing grants, a form carried across a change of its laws, a fill sent with the identity
  of its intent (an outstanding obligation of the store that sent it), and a receipt for it confirmed.
  A `judged` turn with an intent is judged by the effect consumer (`judgeEffect`: values, laws,
  membrane, authority, contract, then the store's judge of the fresh capture) and refused as a
  duplicate when its intent has landed (`judge_refuses_duplicate`, `judge_by_identity`); a `merged`
  turn carrying the other replica's grants and landings joins the grants (revocation wins) and lands
  none of its landings whose grants were revoked here or whose intent landed here. Obligations and
  landings are world state: every turn but `confirmed` keeps the first (`outstanding_kept`), every
  turn keeps the second (`landed_kept`), and a crash keeps both (`obligations_survive_crash`);
* `forget`, `compacted`, `forked`: retention (`Obend.Vault.Retention`): a forget declares a retention
  contract (refused while anything needs the prefix, `forget_refused_when_needed`); the log is then
  replaced by one `compacted` record carrying the world, the anchor the records after it follow and
  the forgotten prefix's digest (`forget_sound`); a declared branch holds a forget back until it
  merges; a proposal or merge resting on the forgotten prefix is refused naming the contract
  (`late_correction_refused`);
* `reasoned`, `justified`: the vault's reasons (`Obend.Reasons`): an observation, an assumption, an
  explanation, a defeater or a proposed action, stepped by `Obend.Reasons.State.step`, which keeps the
  judgment the well-founded model of the current base (`Obend.Reasons.from_scratch_consistent`); and a
  proposal whose fill carries a justification, judged as a `judged` turn (a landing with its intent,
  refused as a duplicate or as late like any other) only while that justification is supported now
  (`justified_needs_support`), and refused by its reasons, by name, otherwise. The reasons are world
  state, so a `compacted` record carries them whole and a `forget` keeps them (`forget_keeps_reasons`);
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
public import Obend.Vault.Transport
public import Obend.Vault.Retention
public import Obend.Vault.Merge
public import Obend.Digest.Cshake256
public import Obend.Reasons
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
open Obend.Vault.Transport (Issue Grants Standing Landing Obligation Contract)

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
  /-- what the vault keeps of each form it issued: its contract and its basis (`Obend.Vault.Transport`) -/
  issues : List Issue := []
  /-- the grants it issued and revoked -/
  grants : Grants := {}
  /-- the proposals it landed, by the identity of their intent -/
  landed : List Landing := []
  /-- the proposals it sent and has no receipt for -/
  outstanding : List Obligation := []
  /-- how many proposals it has sent -/
  minted : Nat := 0
  /-- the retention contracts its `forget` turns declared (`Obend.Vault.Retention`) -/
  retention : List Retention.Contract := []
  /-- the branches it declared (`obend fork`) -/
  forks : List Retention.Fork := []
  /-- its reasons: what it observed, assumed, explained, defeated and proposed, and the judgment -/
  reasons : Obend.Reasons.State := {}
deriving DecidableEq

/-- One turn of the deployed entry. -/
inductive Turn
  | base (w : World)
  | opened (files : List (String × Option String)) (env : Option (List String))
  /-- an open of the files the world has seen, by the same names: only the files whose text moved -/
  | reopened (changed : List (String × String)) (env : Option (List String))
  | member (name : String) (grants : List (String × String))
  | wrote (page text : String)
  | posted (who page text : String)
  | selected (who : Option String) (page : String) (k i : Nat)
  | recited (who : Option String) (page : String)
  | merged (label : String) (other : Store) (skipLedger : Bool) (otherGrants : Option Grants := none)
      (otherLanded : List Landing := []) (reaches : Option Bool := none)
  | resolved (k : Nat) (right : Bool)
  | rows (rs : List Row)
  | captured (situation name : String) (g : Grant) (src dst : String) (amount : Nat) (field : String)
      (refs : List String)
  | abstracted (name value hole : String)
  | judged (name digest : String) (hops : List Grant) (a : Assignment) (intent : Option String := none)
  | filled (name received sent : String)
  | issued (name : String)
  | offered (name : String) (K : Contract)
  | granted (id : String) (g : Grant)
  | revoked (id : String)
  | transported (name : String)
  | proposed (name received digest vault : String) (hops : List Grant) (a : Assignment) (holder : String)
      (because : Option String := none)
  | confirmed (intent : String) (effects : Nat)
  | forget (c : Retention.Contract)
  | compacted (count digest anchor : Nat) (w : World)
  | forked (name : String)
  | reasoned (e : Obend.Reasons.Event)
  | justified (name digest : String) (hops : List Grant) (a : Assignment) (intent : Option String) (because : String)

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
  | offered (performed : Nat)
  | transported (v : Transport.Verdict) (performed : Nat) (moved : List Transport.Moved)
  | proposed (intent text : String)

/-- The text the world last saw of a page's file. -/
def seenOf (s : Store) (n : String) : Option String := (s.page? n).bind (·.seen)

/-- **What an open read, as its record carries it**: each file by name, with its text where it is not
the text the world last saw of it. -/
def readingOf (s : Store) (V : List (String × String)) : List (String × Option String) :=
  V.map fun (n, t) => (n, if seenOf s n == some t then none else some t)

/-- The files a record of an open names, read back against the world before it. -/
def reconstruct (s : Store) (files : List (String × Option String)) : List (String × String) :=
  files.map fun (n, o) => (n, o.getD ((seenOf s n).getD ""))

/-- The names of the files the world has seen, in the order a vault is read (by name). -/
def seenNames (s : Store) : List String :=
  (s.pages.filterMap fun p => p.seen.map fun _ => p.name).mergeSort fun a b => decide (a ≤ b)

/-- **What an open of the files the world has seen read**: only the files whose text is not the
text the world last saw of them (the record of an open that changed one page names one page). -/
def changedOf (s : Store) (V : List (String × String)) : List (String × String) :=
  V.filter fun (n, t) => seenOf s n != some t

/-- The files a record of such an open names, read back against the world before it: every file
the world has seen, with the changed ones' new text. -/
def reconstructSeen (s : Store) (changed : List (String × String)) : List (String × String) :=
  (seenNames s).map fun n => (n, (changed.lookup n).getD ((seenOf s n).getD ""))

theorem lookup_mem_pair {l : List (String × String)} {a b : String} (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have hb : (a == k) = false := by simp [hk]
      simp only [List.lookup, hb] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_changedOf (s : Store) : ∀ {V : List (String × String)}, (V.map Prod.fst).Nodup →
    ∀ {n t : String}, (n, t) ∈ V → (changedOf s V).lookup n = if seenOf s n = some t then none else some t
  | [], _, _, _, h => by cases h
  | (m, u) :: V, hnd, n, t, hm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hmV, hnd⟩ := hnd
    simp only [changedOf, List.filter_cons] at *
    have hnone : (V.filter fun x => seenOf s x.1 != some x.2).lookup m = none := by
      cases hl : (V.filter fun x => seenOf s x.1 != some x.2).lookup m with
      | none => rfl
      | some v =>
        exfalso
        have := lookup_mem_pair hl
        exact hmV ⟨(m, v), (List.mem_filter.1 this).1, rfl⟩
    rcases List.mem_cons.1 hm with he | hV
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      by_cases hs : seenOf s n = some t
      · simp [hs, hnone]
      · simp [hs]
    · have hne : n ≠ m := fun h => hmV ⟨(n, t), hV, h⟩
      have ih := lookup_changedOf s (V := V) hnd hV
      by_cases hc : (seenOf s m != some u) = true
      · simp only [hc, ↓reduceIte, List.lookup, show (n == m) = false from by simp [hne]]
        exact ih
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- **The record of an open of the files the world has seen carries exactly the files it read.** -/
theorem reconstructSeen_changedOf (s : Store) (V : List (String × String))
    (hV : V.map Prod.fst = seenNames s) (hnd : (V.map Prod.fst).Nodup) :
    reconstructSeen s (changedOf s V) = V := by
  simp only [reconstructSeen, ← hV, List.map_map]
  conv => rhs; rw [← List.map_id V]
  apply List.map_congr_left
  intro ⟨n, t⟩ hm
  simp only [Function.comp, id]
  rw [lookup_changedOf s hnd hm]
  by_cases hs : seenOf s n = some t <;> simp [hs]

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

/-- The issue a vault keeps of a form; a form issued before issues were kept is read as issued under
the laws as they stand. -/
def issueOf (w : World) (f : Form) : Issue :=
  (w.issues.find? (·.form == f.name)).getD { form := f.name, basis := Transport.basisOf w.store f }

def setIssue (w : World) (i : Issue) : World :=
  { w with issues := (w.issues.filter (·.form != i.form)) ++ [i] }

/-- A duplicate, said: the intent and where it landed. -/
def dupText (w : World) (name : String) (l : Landing) : String :=
  name ++ ": refused: a duplicate: intent " ++ l.intent ++ " has landed " ++
    (match w.receipts[l.receipt - 1]? with
      | some r => if l.receipt == 0 then "on another replica" else
          "here as receipt " ++ Form.hex16 (Form.receiptDigest H r) ++ " (" ++ toString l.receipt ++ " in the chain)"
      | none => "on another replica") ++ "; it is not landed again"

/-- The grants that stand behind a form, said. -/
def supportsText (w : World) (f : Form) : String :=
  let sups := Transport.supportsFor w.grants f
  let gone := w.grants.revoked.filter fun r => w.grants.standing.any fun s => s.id == r && s.grant.holder == Transport.holderOf f
  (if sups.isEmpty then "no grant stands for " ++ Transport.holderOf f
   else ", ".intercalate (sups.map fun s => s.id ++ " (" ++ Form.showAuths s.grant.held ++ " on " ++
     ", ".intercalate s.grant.patterns ++ ")") ++ " " ++ (if sups.length == 1 then "stands" else "stand")) ++
  (if gone.isEmpty then "" else "; " ++ ", ".intercalate gone ++ " revoked")

/-- The value moves among what moved: a field the form reads, or a page gone for good. -/
def valueMoves (ms : List Transport.Moved) : List Transport.Moved :=
  ms.filter fun | .value .. | .gone _ false => true | _ => false

/-- A captured page gone with its history kept: it may come back. -/
def waiting (ms : List Transport.Moved) : List Transport.Moved :=
  ms.filter fun | .gone _ true => true | _ => false

/-- **The effect consumer's judgment of a proposal**: the form's values (a value that moved makes it
stale; a captured page gone with its history kept makes it wait), the laws it was issued or
transported under, the membrane's gate, the pages the fill writes (one gone with its history kept
waits), the authority of
a grant that stands behind it, its contract's offer, then the store's judge of the fresh capture
(`Obend.Vault.Transport.judge_recapture_iff`: the form's own admission at the vault's context). It
does not read the proposal's intent: the intent decides only whether the proposal is a duplicate. -/
def judgeEffect (w : World) (f : Form) (hops : List Grant) (a : Assignment) :
    Except String (Store × Admitted × VaultTurn × List String) := do
  let ms := Transport.cellMoves w.store f
  if let m :: _ := waiting ms then
    throw ("waits: " ++ m.text ++ "; nothing landed, and the proposal may be judged again when it returns")
  let vs := valueMoves ms
  unless vs.isEmpty do
    throw ("refused: stale (value): the form read " ++ ", ".intercalate (vs.map Transport.Moved.text) ++ "; capture it again")
  let iss := issueOf w f
  let ls := Transport.lawMoves w.store f iss.basis
  unless ls.isEmpty do
    throw ("refused: the laws over " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
      " moved since it was issued; transport it first")
  -- the membrane first, as the store's judge has it (`judgeProposal_gate_first`)
  if let .error r := Form.gate (Form.ownerViewer f) f hops (f.fill a) then throw (Form.refusalText f r)
  let pages := Transport.fillPages f a
  let live := stateStore w.store.entries
  for p in pages do
    if (live p).isNone && w.store.tombs.any (·.name == p) then
      throw ("waits: " ++ p ++ " is not here now: its file is gone, its history kept; nothing landed, and " ++
        "the proposal may be judged again when it returns")
  let am := Transport.authorityMoves w.grants f pages
  unless am.isEmpty do
    throw ("refused: stale (authority): no grant that stands lets " ++ Transport.holderOf f ++ " write " ++
      ", ".intercalate (am.map Transport.Moved.text) ++ " (" ++ supportsText w f ++ ")")
  if let some K := iss.contract then
    if let some x := a.nats.lookup K.hole then
      unless K.offer.contains x do
        throw ("refused: " ++ K.hole ++ " = " ++ toString x ++ " is outside its offer (" ++
          Transport.runsText K.offer ++ ")")
  match Form.judgeProposal H w.store (Transport.recapture live f) hops a with
  | .error e => throw e
  | .ok (s, ad, t) => return (s, ad, t, (Transport.supportsFor w.grants f).map (·.id))

/-- The proposal a fill sends, with the identity of its intent. -/
def proposalJson (name digest vault : String) (hops : List Grant) (a : Assignment) (holder intent : String)
    (because : Option String := none) : Json :=
  Json.mkObj ([("proposal", Json.str name), ("digest", Json.str digest), ("vault", Json.str vault),
    ("hops", Json.arr (hops.map Form.grantJson).toArray), ("fill", Form.assignmentJson a), ("by", Json.str holder),
    ("intent", Json.str intent)] ++ (match because with | some c => [("because", Json.str c)] | none => []))

/-- The contract that retired a form, if one did. -/
def retiredBy (w : World) (name : String) : Option Retention.Contract :=
  w.retention.find? (·.retire.contains name)

/-- A proposal for a retired form, refused: it rests on what the contract forgot. -/
def lateText (name : String) (c : Retention.Contract) : String :=
  name ++ ": refused: late: the form was retired by the retention contract " ++ c.name ++
    "; a proposal for it rests on a forgotten prefix of the log"

/-- **A proposal judged, its intent aside**: the form it names, as issued, then `judgeEffect`; the world
with the proposal landed and its receipt on the chain, and its landing (the intent left blank). -/
def judgeNew (w : World) (name digest : String) (hops : List Grant) (a : Assignment) :
    Except String (World × Outcome × Landing) :=
  match retiredBy w name with
  | some c => .error (lateText name c)
  | none =>
  match w.forms.find? (·.name == name) with
  | none => .error ("refused: no form named " ++ name ++ " here")
  | some f =>
    if digest != Form.formDigest H f then
      .error (name ++ ": refused: the form has changed since this proposal's copy was sent; send the form again")
    else
      match judgeEffect w f hops a with
      | .error e => .error (name ++ ": " ++ e)
      | .ok (s, ad, t, sups) =>
        let r := Form.receiptFor H w.receipts.getLast? f a ad t
        .ok ({ w with store := settle H s, receipts := w.receipts ++ [r] }, .judged s ad t r (w.receipts.length + 1),
          ⟨"", name, ad.holder, Transport.fillPages f a, sups, w.receipts.length + 1⟩)

/-- What a merge does with the other replica's landings (those this replica does not hold already):
each whose intent landed here is a duplicate; each none of whose grants stands after the merge (revocation wins,
`Obend.Vault.Transport.merge_revocation_wins`) is refused; the rest are admitted. -/
def sortLandings (w : World) (G : Grants) (theirs0 : List Landing) : List Landing × List Landing × List Landing :=
  -- a landing both replicas hold (from before they parted, or merged since) is no act of the other's
  let theirs := theirs0.filter fun l => !w.landed.contains l
  let fresh := theirs.filter fun l => (Transport.duplicateOf w.landed l.intent).isNone
  let dups := theirs.filter fun l => (Transport.duplicateOf w.landed l.intent).isSome
  let refused := fresh.filter fun l => !(l.supports.any fun id => G.live.any (·.id == id))
  let admitted := fresh.filter fun l => l.supports.any fun id => G.live.any (·.id == id)
  (admitted, refused, dups)

/-- The merge of another replica's store (with its grants and landings, when the record carries them). -/
def mergeStep (w : World) (label : String) (other : Store) (skipLedger : Bool) (og : Option Grants)
    (theirs : List Landing) : Except String (World × Outcome) :=
  match og, theirs with
  | none, _ =>
      let (s, notes) := Merge.mergeVault w.store other label
        (skip := if skipLedger then Obend.Ledger.Cli.ledgerOwned else fun _ => false)
      .ok ({ w with store := settle H s }, .merged s notes)
  | some og, theirs =>
      let G := w.grants.merge og
      let (admitted, refused, dups) := sortLandings w G theirs
      let held := (refused ++ dups).flatMap (·.pages)
      let (s, notes) := Merge.mergeVault w.store other label
        (skip := fun n => (skipLedger && Obend.Ledger.Cli.ledgerOwned n) || held.contains n)
      let said := refused.map (fun l => ", ".intercalate l.pages ++ ": not merged from " ++ label ++ ": the landing of " ++
          l.form ++ " (intent " ++ l.intent ++ ", by " ++ l.holder ++ ") rested on " ++ ", ".intercalate l.supports ++
          ", revoked here") ++
        dups.map (fun l => ", ".intercalate l.pages ++ ": not merged from " ++ label ++ ": the landing of " ++ l.form ++
          " (intent " ++ l.intent ++ ") is the one landed here; not landed twice")
      .ok ({ w with store := settle H s, grants := G,
                    landed := w.landed ++ admitted.map fun l => { l with receipt := 0 } }, .merged s (said ++ notes))

/-- A merge that rests on a forgotten prefix: from a branch the contract abandoned, or from a replica
whose log does not reach the horizon (`reaches`: what the command read of the other log). -/
def lateMerge (w : World) (label : String) (reaches : Option Bool) : Option String :=
  match w.retention.find? (·.abandon.contains label), w.retention.getLast?, reaches with
  | some c, _, _ => some ("not merged: late: " ++ label ++ " was abandoned by the retention contract " ++ c.name)
  | none, some c, some false => some ("not merged: late: " ++ label ++ "'s log does not reach the horizon of the " ++
      "retention contract " ++ c.name ++ " (it forked before the prefix forgotten here); its corrections " ++
      "would arrive later than the contract allows")
  | _, _, _ => none

def markMerged (bs : List Retention.Fork) (label : String) : List Retention.Fork :=
  bs.map fun b => if b.name == label then { b with merged := true } else b

/-- **What still needs the prefix a `forget` would forget**, the first of it, said: a proposal sent
from here with no receipt (an obligation), a form issued here that stands and that the contract does
not retire, a retired form whose continuity contract promised what retiring it would break, a branch
declared here that has not merged and that the contract does not abandon. -/
def needs (w : World) (c : Retention.Contract) : Option String :=
  match w.outstanding with
  | o :: _ => some ("refused: the proposal " ++ o.intent ++ " of " ++ o.form ++ " sent from here awaits its " ++
      "receipt: an obligation reaches into the prefix")
  | [] =>
  match w.forms.filter (fun f => (retiredBy w f.name).isNone && !c.retire.contains f.name) with
  | f :: _ => some ("refused: the form " ++ f.name ++ " was issued against the prefix and stands; retire it " ++
      "(--retire " ++ f.name ++ ") or keep the prefix")
  | [] =>
  match c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome) with
  | n :: _ => some ("refused: the form " ++ n ++ " has a continuity contract: what it promised reaches past " ++
      "the horizon, and retiring it would break it")
  | [] =>
  match w.forks.filter (fun b => !b.merged && !c.abandon.contains b.name) with
  | b :: _ => some ("refused: the branch " ++ b.name ++ " forked from the prefix and has not merged; merge it " ++
      "or abandon it (--abandon " ++ b.name ++ ")")
  | [] => none

/-- **A proposal judged**: with an intent, refused as a duplicate when it landed here, else `judgeNew`
and its landing kept under its intent; without one, refused as late when its form was retired, else
the form's own judgment (`Form.judgeProposal`). -/
def judgeTurn (w : World) (name digest : String) (hops : List Grant) (a : Assignment) :
    Option String → Except String (World × Outcome)
  | some i =>
    match Transport.duplicateOf w.landed i with
    | some l => .error (dupText w name l)
    | none =>
      match judgeNew w name digest hops a with
      | .error e => .error e
      | .ok (w', o, l) => .ok ({ w' with landed := w.landed ++ [{ l with intent := i }] }, o)
  | none =>
    match retiredBy w name with
    | some c => .error (lateText name c)
    | none =>
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
  | .reopened changed env =>
    let V := reconstructSeen w.store changed
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
  | .merged label other skipLedger og theirs reaches =>
    match lateMerge w label reaches with
    | some e => .error e
    | none =>
      match mergeStep w label other skipLedger og theirs with
      | .ok (w', o) => .ok ({ w' with forks := markMerged w'.forks label }, o)
      | .error e => .error e
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
  | .judged name digest hops a intent => judgeTurn w name digest hops a intent
  | .filled name received sent =>
    .ok ({ w with received := (w.received.filter (·.1 != name)) ++ [(name, received)],
                  sent := (w.sent.filter (·.1 != name)) ++ [(name, sent)] }, .quiet)
  | .issued name =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name)
    | some f =>
      if w.issues.any (·.form == name) then .error ("refused: " ++ name ++ " was issued already") else
      let G := match f.grants.head? with
        | some g => if w.grants.standing.any (·.id == name) then w.grants else w.grants.issue ⟨name, g⟩
        | none => w.grants
      .ok ({ setIssue w { form := name, basis := Transport.basisOf w.store f } with grants := G }, .quiet)
  | .offered name K =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name)
    | some f =>
      if f.holes != [(K.hole, .nat)] then
        .error ("refused: a contract is declared on a form whose one hole is a natural; " ++ name ++ " has " ++
          toString f.holes.length ++ " hole(s)")
      else if K.offer.isEmpty then .error "refused: the offer is empty"
      else if !(K.promise.all K.offer.contains) then .error "refused: it promises what it does not offer"
      else if !Transport.valuesHoldB (stateStore w.store.entries) f then
        .error ("refused: stale (value): " ++ ", ".intercalate ((valueMoves (Transport.cellMoves w.store f)).map Transport.Moved.text) ++
          "; capture it again")
      else
        let Γ := Transport.kernelCtx H w.store f
        match K.offer.find? (fun x => !Transport.admitsAt Γ f [] (K.fill x)) with
        | some x => .error ("refused: the laws now refuse " ++ K.hole ++ " = " ++ toString x ++
            "; a form offers what the vault admits")
        | none =>
          .ok (setIssue w { form := name, contract := some K, basis := Transport.basisOf w.store f },
            .offered K.offer.length)
  | .granted id g =>
    if w.grants.standing.any (·.id == id) || w.grants.revoked.contains id then
      .error ("refused: a grant named " ++ id ++ " was issued already")
    else .ok ({ w with grants := w.grants.issue ⟨id, g⟩ }, .quiet)
  | .revoked id =>
    if !(w.grants.live.any (·.id == id)) then .error ("refused: no grant named " ++ id ++ " stands")
    else .ok ({ w with grants := w.grants.revoke id }, .quiet)
  | .transported name =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name)
    | some f =>
      let ms := Transport.cellMoves w.store f
      if let m :: _ := waiting ms then .error ("waits: " ++ m.text) else
      let vs := valueMoves ms
      if !vs.isEmpty then
        .error ("refused: stale (value): the form read " ++ ", ".intercalate (vs.map Transport.Moved.text) ++ "; capture it again")
      else
        let iss := issueOf w f
        let ls := Transport.lawMoves w.store f iss.basis
        if ls.isEmpty then .error ("nothing to transport: the laws over its pages are those it was issued under")
        else match iss.contract with
          | none => .ok (setIssue w { iss with basis := Transport.basisOf w.store f }, .transported Transport.Verdict.continues 0 ls)
          | some K =>
            match Transport.transport (Transport.kernelCtx H w.store f) K f with
            | (.refused x, _) =>
              .error ("refused by its contract: the laws over " ++ ", ".intercalate (ls.map Transport.Moved.text) ++
                " no longer admit " ++ K.hole ++ " = " ++ toString x ++ ", which it promised (" ++
                Transport.runsText K.promise ++ ")")
            | (v, K') =>
              .ok (setIssue w { iss with contract := some K', basis := Transport.basisOf w.store f },
                .transported v K.offer.length ls)
  | .proposed name received digest vault hops a holder because =>
    let i := Transport.mintIntent H digest holder a w.minted
    let text := (proposalJson name digest vault hops a holder i because).pretty ++ "\n"
    .ok ({ w with received := (w.received.filter (·.1 != name)) ++ [(name, received)],
                  sent := (w.sent.filter (·.1 != name)) ++ [(name, text)],
                  outstanding := w.outstanding ++ [⟨i, name, digest, vault, holder, a⟩],
                  minted := w.minted + 1 }, .proposed i text)
  | .forget c =>
    match c.retire.find? (fun n => !w.forms.any (·.name == n)) with
    | some n => .error ("refused: no form named " ++ n ++ " to retire")
    | none =>
    match needs w c with
    | some e => .error e
    | none => .ok ({ w with retention := w.retention ++ [c] }, .quiet)
  | .compacted _ _ _ w' => .ok (w', .quiet)
  | .forked name =>
    if w.forks.any (fun b => b.name == name && !b.merged) then .error ("refused: the branch " ++ name ++ " is out already")
    else .ok ({ w with forks := (w.forks.filter (·.name != name)) ++ [⟨name, false⟩] }, .quiet)
  | .reasoned e =>
    match w.reasons.step e with
    | .error err => .error err
    | .ok r => .ok ({ w with reasons := r }, .quiet)
  | .justified name digest hops a intent because =>
    match w.reasons.justify because with
    | .error e => .error (name ++ ": refused by its reasons: " ++ e)
    | .ok () => judgeTurn w name digest hops a intent
  | .confirmed i effects =>
    match w.outstanding.find? (·.intent == i) with
    | none => .error ("refused: no proposal sent from here awaits a receipt for intent " ++ i)
    | some o =>
      if effects != Transport.effectsOf H o then
        .error ("refused: the receipt is not of the proposal " ++ i ++ " sent from here")
      else .ok ({ w with outstanding := w.outstanding.filter (·.intent != i) }, .quiet)
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

/-- **An open of the files the world has seen replays as that open**, from a record naming only the
files that moved: the same step as the record naming every file (`open_replays`). -/
theorem reopen_replays (w : World) (V : List (String × String)) (env : Environment)
    (hV : V.map Prod.fst = seenNames w.store) (hnd : (V.map Prod.fst).Nodup) :
    stepTurn w (.reopened (changedOf w.store V) (envOf w.store env)) =
      stepTurn w (.opened (readingOf w.store V) (envOf w.store env)) := by
  simp only [stepTurn, reconstruct_readingOf, reconstructSeen_changedOf w.store V hV hnd]

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
    ("received", pairsJson w.received), ("sent", pairsJson w.sent)] |>.mergeObj (Json.mkObj (
    (if w.issues.isEmpty then [] else [("issues", Json.arr (w.issues.map Transport.issueJson).toArray)]) ++
    (if w.grants == {} then [] else [("grants", Transport.grantsJson w.grants)]) ++
    (if w.landed.isEmpty then [] else [("landed", Json.arr (w.landed.map Transport.landingJson).toArray)]) ++
    (if w.outstanding.isEmpty then [] else
      [("outstanding", Json.arr (w.outstanding.map Transport.obligationJson).toArray)]) ++
    (if w.minted == 0 then [] else [("minted", toJson w.minted)]) ++
    (if w.retention.isEmpty then [] else [("retention", Json.arr (w.retention.map Retention.contractJson).toArray)]) ++
    (if w.forks.isEmpty then [] else [("forks", Json.arr (w.forks.map Retention.forkJson).toArray)]) ++
    (if w.reasons == {} then [] else [("reasons", Obend.Reasons.stateJson w.reasons)])))

def worldOf (j : Json) : Except String World := do
  let store ← fullStoreOf (← j.getObjVal? "store")
  let journal ← journalOf (← j.getObjVal? "journal")
  let forms ← (← j.getObjValAs? (Array Json) "forms").toList.mapM Form.formOf
  let receipts ← (← j.getObjValAs? (Array Json) "receipts").toList.mapM Form.receiptOf
  let received ← pairsOf (← j.getObjVal? "received")
  let sent ← pairsOf (← j.getObjVal? "sent")
  let opt {α : Type} (k : String) (d : α) (g : Json → Except String α) : Except String α :=
    match j.getObjVal? k with
    | .ok v => g v
    | .error _ => pure d
  let issues ← opt "issues" [] fun v => do (← v.getArr?).toList.mapM Transport.issueOf
  let grants ← opt "grants" {} Transport.grantsOf
  let landed ← opt "landed" [] fun v => do (← v.getArr?).toList.mapM Transport.landingOf
  let outstanding ← opt "outstanding" [] fun v => do (← v.getArr?).toList.mapM Transport.obligationOf
  let minted ← opt "minted" 0 fun v => v.getNat?
  let retention ← opt "retention" [] fun v => do (← v.getArr?).toList.mapM Retention.contractOf
  let forks ← opt "forks" [] fun v => do (← v.getArr?).toList.mapM Retention.forkOf
  let reasons ← opt "reasons" {} Obend.Reasons.stateOf
  return ⟨store, journal, forms, receipts, received, sent, issues, grants, landed, outstanding, minted, retention, forks,
    reasons⟩

def turnJson : Turn → Json
  | .base w => Json.mkObj [("turn", "base"), ("world", worldJson w)]
  | .opened files env => Json.mkObj [("turn", "open"),
      ("files", Json.arr (files.map fun (n, t) => Json.arr #[Json.str n, optStrJson t]).toArray),
      ("environment", match env with | some e => strsJson e | none => Json.null)]
  | .reopened changed env => Json.mkObj [("turn", "reopen"), ("changed", pairsJson changed),
      ("environment", match env with | some e => strsJson e | none => Json.null)]
  | .member name grants => Json.mkObj [("turn", "member"), ("name", Json.str name), ("grants", pairsJson grants)]
  | .wrote page text => Json.mkObj [("turn", "write"), ("page", Json.str page), ("text", Json.str text)]
  | .posted who page text => Json.mkObj [("turn", "post"), ("as", Json.str who), ("page", Json.str page),
      ("text", Json.str text)]
  | .selected who page k i => Json.mkObj [("turn", "select"), ("as", optStrJson who), ("page", Json.str page),
      ("section", toJson k), ("candidate", toJson i)]
  | .recited who page => Json.mkObj [("turn", "recite"), ("as", optStrJson who), ("page", Json.str page)]
  | .merged label other skip og theirs reaches => Json.mkObj ([("turn", Json.str "merge"), ("label", Json.str label),
      ("other", storeJson other), ("skipLedger", toJson skip)] ++
      (match og with
        | some g => [("otherGrants", Transport.grantsJson g),
            ("otherLanded", Json.arr (theirs.map Transport.landingJson).toArray)]
        | none => []) ++
      (match reaches with | some b => [("reaches", toJson b)] | none => []))
  | .resolved k right => Json.mkObj [("turn", "resolve"), ("conflict", toJson k), ("right", toJson right)]
  | .rows rs => Json.mkObj [("turn", "rows"), ("rows", Json.arr (rs.map rowJson).toArray)]
  | .captured situation name g src dst amount field refs => Json.mkObj [("turn", "capture"),
      ("situation", Json.str situation), ("name", Json.str name), ("grant", Form.grantJson g),
      ("src", Json.str src), ("dst", Json.str dst), ("amount", toJson amount), ("field", Json.str field),
      ("refs", strsJson refs)]
  | .abstracted name value hole => Json.mkObj [("turn", "abstract"), ("name", Json.str name),
      ("value", Json.str value), ("hole", Json.str hole)]
  | .judged name digest hops a intent => Json.mkObj ([("turn", Json.str "judge"), ("name", Json.str name),
      ("digest", Json.str digest), ("hops", Json.arr (hops.map Form.grantJson).toArray),
      ("fill", Form.assignmentJson a)] ++ (match intent with | some i => [("intent", Json.str i)] | none => []))
  | .filled name received sent => Json.mkObj [("turn", "fill"), ("name", Json.str name),
      ("received", Json.str received), ("sent", Json.str sent)]
  | .issued name => Json.mkObj [("turn", "issue"), ("name", Json.str name)]
  | .offered name K => Json.mkObj [("turn", "offer"), ("name", Json.str name), ("contract", Transport.contractJson K)]
  | .granted id g => Json.mkObj [("turn", "grant"), ("id", Json.str id), ("grant", Form.grantJson g)]
  | .revoked id => Json.mkObj [("turn", "revoke"), ("id", Json.str id)]
  | .transported name => Json.mkObj [("turn", "transport"), ("name", Json.str name)]
  | .proposed name received digest vault hops a holder because => Json.mkObj ([("turn", Json.str "propose"),
      ("name", Json.str name), ("received", Json.str received), ("digest", Json.str digest), ("vault", Json.str vault),
      ("hops", Json.arr (hops.map Form.grantJson).toArray), ("fill", Form.assignmentJson a), ("by", Json.str holder)] ++
      (match because with | some c => [("because", Json.str c)] | none => []))
  | .confirmed i effects => Json.mkObj [("turn", "confirm"), ("intent", Json.str i), ("effects", toJson effects)]
  | .forget c => Json.mkObj [("turn", "forget"), ("contract", Retention.contractJson c)]
  | .compacted count digest anchor w => Json.mkObj [("turn", "compacted"), ("count", toJson count),
      ("digest", toJson digest), ("anchor", toJson anchor), ("world", worldJson w)]
  | .forked name => Json.mkObj [("turn", "fork"), ("name", Json.str name)]
  | .reasoned e => Json.mkObj [("turn", "reason"), ("event", Obend.Reasons.eventJson e)]
  | .justified name digest hops a intent because => Json.mkObj ([("turn", Json.str "justified"), ("name", Json.str name),
      ("digest", Json.str digest), ("hops", Json.arr (hops.map Form.grantJson).toArray),
      ("fill", Form.assignmentJson a), ("because", Json.str because)] ++
      (match intent with | some i => [("intent", Json.str i)] | none => []))

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
  | "reopen" =>
    let env ← match ← j.getObjVal? "environment" with
      | .null => pure none
      | e => some <$> strsOf e
    return .reopened (← pairsOf (← j.getObjVal? "changed")) env
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
    let skip ← j.getObjValAs? Bool "skipLedger"
    match j.getObjVal? "otherGrants" with
    | .ok g =>
      let theirs ← (← j.getObjValAs? (Array Json) "otherLanded").toList.mapM Transport.landingOf
      let reaches := (j.getObjValAs? Bool "reaches").toOption
      return .merged label other skip (some (← Transport.grantsOf g)) theirs reaches
    | .error _ => return .merged label other skip none [] (j.getObjValAs? Bool "reaches").toOption
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
    let a ← Form.assignmentOf (← j.getObjVal? "fill")
    return .judged name digest hops a (j.getObjValAs? String "intent").toOption
  | "fill" =>
    let name ← j.getObjValAs? String "name"
    let received ← j.getObjValAs? String "received"
    return .filled name received (← j.getObjValAs? String "sent")
  | "issue" => return .issued (← j.getObjValAs? String "name")
  | "offer" => return .offered (← j.getObjValAs? String "name") (← Transport.contractOf (← j.getObjVal? "contract"))
  | "grant" => return .granted (← j.getObjValAs? String "id") (← Form.grantOf (← j.getObjVal? "grant"))
  | "revoke" => return .revoked (← j.getObjValAs? String "id")
  | "transport" => return .transported (← j.getObjValAs? String "name")
  | "propose" =>
    let name ← j.getObjValAs? String "name"
    let received ← j.getObjValAs? String "received"
    let digest ← j.getObjValAs? String "digest"
    let vault ← j.getObjValAs? String "vault"
    let hops ← (← j.getObjValAs? (Array Json) "hops").toList.mapM Form.grantOf
    let a ← Form.assignmentOf (← j.getObjVal? "fill")
    return .proposed name received digest vault hops a (← j.getObjValAs? String "by")
      (j.getObjValAs? String "because").toOption
  | "confirm" => return .confirmed (← j.getObjValAs? String "intent") (← j.getObjValAs? Nat "effects")
  | "forget" => return .forget (← Retention.contractOf (← j.getObjVal? "contract"))
  | "compacted" =>
    let count ← j.getObjValAs? Nat "count"
    let digest ← j.getObjValAs? Nat "digest"
    let anchor ← j.getObjValAs? Nat "anchor"
    return .compacted count digest anchor (← worldOf (← j.getObjVal? "world"))
  | "fork" => return .forked (← j.getObjValAs? String "name")
  | "reason" => return .reasoned (← Obend.Reasons.eventOf (← j.getObjVal? "event"))
  | "justified" =>
    let name ← j.getObjValAs? String "name"
    let digest ← j.getObjValAs? String "digest"
    let hops ← (← j.getObjValAs? (Array Json) "hops").toList.mapM Form.grantOf
    let a ← Form.assignmentOf (← j.getObjVal? "fill")
    return .justified name digest hops a (j.getObjValAs? String "intent").toOption (← j.getObjValAs? String "because")
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
  | .reopened .. => "open"
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
  | .issued .. => "issue"
  | .offered .. => "offer"
  | .granted .. => "grant"
  | .revoked .. => "revoke"
  | .transported .. => "transport"
  | .proposed .. => "propose"
  | .confirmed .. => "confirm"
  | .forget .. => "forget"
  | .compacted .. => "compacted"
  | .forked .. => "fork"
  | .reasoned .. => "reason"
  | .justified .. => "justified"

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

/-! ## Obligations and the identity of an intent, at the deployed machine -/

/-- **A proposal judged again is refused by its intent**: once an intent has landed, the same proposal
is refused as a duplicate, whatever it says, and nothing lands twice. -/
theorem judge_refuses_duplicate (w : World) (name digest : String) (hops : List Grant) (a : Assignment)
    {i : String} {l : Landing} (h : Transport.duplicateOf w.landed i = some l) :
    stepTurn w (.judged name digest hops a (some i)) = .error (dupText w name l) := by
  simp only [stepTurn, judgeTurn, h]

/-- **By identity, not by content**: a proposal whose intent has not landed is judged on what it says
(`judgeNew`, which does not read the intent), and its landing is recorded under its intent. Two
proposals alike in content and different in intent are judged alike: both land, or both are refused
with the same words. -/
theorem judge_by_identity (w : World) (name digest : String) (hops : List Grant) (a : Assignment) {i : String}
    (h : Transport.duplicateOf w.landed i = none) :
    stepTurn w (.judged name digest hops a (some i)) =
      match judgeNew w name digest hops a with
      | .error e => .error e
      | .ok (w', o, l) => .ok ({ w' with landed := w.landed ++ [{ l with intent := i }] }, o) := by
  simp only [stepTurn, judgeTurn, h]

theorem judge_content_alike (w : World) (name digest : String) (hops : List Grant) (a : Assignment) {i j : String}
    (hi : Transport.duplicateOf w.landed i = none) (hj : Transport.duplicateOf w.landed j = none) :
    (∀ e, stepTurn w (.judged name digest hops a (some i)) = .error e ↔
      stepTurn w (.judged name digest hops a (some j)) = .error e) := by
  intro e
  rw [judge_by_identity w name digest hops a hi, judge_by_identity w name digest hops a hj]
  cases judgeNew w name digest hops a <;> simp

theorem judgeNew_keeps {w w1 : World} {name digest : String} {hops : List Grant} {a : Assignment} {o : Outcome}
    {l : Landing} (h : judgeNew w name digest hops a = .ok (w1, o, l)) :
    w1.outstanding = w.outstanding ∧ w1.landed = w.landed := by
  unfold judgeNew at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem judgeTurn_keeps {w w' : World} {o : Outcome} {name digest : String} {hops : List Grant} {a : Assignment}
    {intent : Option String} (h : judgeTurn w name digest hops a intent = .ok (w', o)) :
    (∀ x ∈ w.outstanding, x ∈ w'.outstanding) ∧ (∀ x ∈ w.landed, x ∈ w'.landed) := by
  cases intent with
  | none =>
    simp only [judgeTurn] at h
    repeat' split at h
    all_goals first
      | contradiction
      | (cases h; done)
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
         exact ⟨fun x hx => hx, fun x hx => hx⟩)
  | some i =>
    simp only [judgeTurn] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i w1 o1 l1 hj
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have := judgeNew_keeps hj
        exact ⟨fun x hx => by simp [this.1, hx], fun x hx => by simp [hx]⟩

theorem judged_keeps {w w' : World} {o : Outcome} {name digest : String} {hops : List Grant} {a : Assignment}
    {intent : Option String} (h : stepTurn w (.judged name digest hops a intent) = .ok (w', o)) :
    (∀ x ∈ w.outstanding, x ∈ w'.outstanding) ∧ (∀ x ∈ w.landed, x ∈ w'.landed) :=
  judgeTurn_keeps h

/-- **A justified proposal is judged only while its justification is supported**: the vault's reasons,
as it keeps them, say the justification is supported now, and then the proposal is judged as any
other (`judgeTurn`: by its intent, refused as a duplicate or as late, landed with its intent). -/
theorem justified_needs_support {w w' : World} {o : Outcome} {name digest because : String}
    {hops : List Grant} {a : Assignment} {intent : Option String}
    (h : stepTurn w (.justified name digest hops a intent because) = .ok (w', o)) :
    w.reasons.status because = .supported ∧ judgeTurn w name digest hops a intent = .ok (w', o) := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · rename_i hj
    exact ⟨(Obend.Reasons.justify_ok_iff _ _).1 hj, h⟩

/-- …and, where the reasons the vault keeps are consistent (every `reasoned` turn keeps them so,
`reasoned_consistent`), supported in the well-founded model of its current observations and
assumptions. -/
theorem justified_supported_now {w w' : World} {o : Outcome} {name digest because : String}
    {hops : List Grant} {a : Assignment} {intent : Option String} (hc : w.reasons.Consistent)
    (h : stepTurn w (.justified name digest hops a intent because) = .ok (w', o)) :
    Obend.Reasons.status w.reasons.base because = .supported := by
  rw [← Obend.Reasons.State.status_eq hc]
  exact (justified_needs_support h).1

/-- **A refused justification refuses the proposal**: while the justification is not supported, the
proposal is refused by its reasons, whatever the form would say. -/
theorem justified_refused {w : World} {name digest because : String} {hops : List Grant} {a : Assignment}
    {intent : Option String} (hn : w.reasons.status because ≠ .supported) :
    ∃ e, stepTurn w (.justified name digest hops a intent because) = .error e := by
  simp only [stepTurn]
  split
  · exact ⟨_, rfl⟩
  · rename_i hj
    exact absurd ((Obend.Reasons.justify_ok_iff _ _).1 hj) hn

/-- **A justified proposal with an intent is a landing like any other**: refused as a duplicate once
its intent landed here, and, when it lands, landed under its intent. -/
theorem justified_by_identity {w w' : World} {o : Outcome} {name digest because i : String} {hops : List Grant}
    {a : Assignment} (h : stepTurn w (.justified name digest hops a (some i) because) = .ok (w', o)) :
    Transport.duplicateOf w.landed i = none ∧ ∃ l : Landing, w'.landed = w.landed ++ [{ l with intent := i }] := by
  have h2 := (justified_needs_support h).2
  simp only [judgeTurn] at h2
  split at h2
  · cases h2
  · rename_i hd
    split at h2
    · cases h2
    · rename_i w1 o1 l1 _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      exact ⟨hd, l1, rfl⟩

theorem justified_keeps {w w' : World} {o : Outcome} {name digest because : String} {hops : List Grant}
    {a : Assignment} {intent : Option String}
    (h : stepTurn w (.justified name digest hops a intent because) = .ok (w', o)) :
    (∀ x ∈ w.outstanding, x ∈ w'.outstanding) ∧ (∀ x ∈ w.landed, x ∈ w'.landed) :=
  judgeTurn_keeps (justified_needs_support h).2

/-- **A `reasoned` turn keeps the vault's reasons consistent**: its kept judgment stays the
well-founded model of its base (`Obend.Reasons.step_consistent`). -/
theorem reasoned_consistent {w w' : World} {o : Outcome} {e : Obend.Reasons.Event} (hc : w.reasons.Consistent)
    (h : stepTurn w (.reasoned e) = .ok (w', o)) : w'.reasons.Consistent := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · rename_i r hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Obend.Reasons.step_consistent hc hr

theorem mergeStep_keeps {w w1 : World} {label : String} {other : Store} {skip : Bool} {og : Option Grants}
    {theirs : List Landing} {o : Outcome} (h : mergeStep w label other skip og theirs = .ok (w1, o)) :
    w1.outstanding = w.outstanding ∧ ∀ x ∈ w.landed, x ∈ w1.landed := by
  unfold mergeStep at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h) <;>
    exact ⟨rfl, fun x hx => by simp [hx]⟩

theorem merged_keeps {w w' : World} {o : Outcome} {label : String} {other : Store} {skip : Bool}
    {og : Option Grants} {theirs : List Landing} {reaches : Option Bool}
    (h : stepTurn w (.merged label other skip og theirs reaches) = .ok (w', o)) :
    (∀ x ∈ w.outstanding, x ∈ w'.outstanding) ∧ (∀ x ∈ w.landed, x ∈ w'.landed) := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · split at h
    · rename_i w1 o1 hm
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have := mergeStep_keeps hm
      exact ⟨fun x hx => by simp [this.1, hx], fun x hx => this.2 x hx⟩
    · cases h

/-- **An obligation outlives every turn but its confirmation**: a revision, a transport, a merge, a
judgment or a crash's recovery (which replays turns) keeps every proposal sent and not yet confirmed;
only `confirmed` takes one away, and `base` and `compacted` stand only first in a log, for the world
of what came before. -/
theorem outstanding_kept {w w' : World} {o : Outcome} {t : Turn} (h : stepTurn w t = .ok (w', o))
    (hb : ∀ w0, t ≠ .base w0) (hk : ∀ n d a w0, t ≠ .compacted n d a w0) (hc : ∀ i e, t ≠ .confirmed i e) :
    ∀ x ∈ w.outstanding, x ∈ w'.outstanding := by
  intro x hx
  cases t
  all_goals first
    | exact (hb _ rfl).elim
    | exact (hk _ _ _ _ rfl).elim
    | exact (hc _ _ rfl).elim
    | exact (judged_keeps h).1 x hx
    | exact (justified_keeps h).1 x hx
    | exact (merged_keeps h).1 x hx
    | skip
  all_goals
    simp only [stepTurn] at h
    repeat' split at h
    all_goals first
      | contradiction
      | (cases h; done)
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; first | exact hx | simp [hx])
      | (cases h <;> first | exact hx | simp [hx])

/-- **A landing is never forgotten**: every turn but `base` keeps every proposal landed, so a duplicate
stays a duplicate. -/
theorem landed_kept {w w' : World} {o : Outcome} {t : Turn} (h : stepTurn w t = .ok (w', o))
    (hb : ∀ w0, t ≠ .base w0) (hk : ∀ n d a w0, t ≠ .compacted n d a w0) : ∀ x ∈ w.landed, x ∈ w'.landed := by
  intro x hx
  cases t
  all_goals first
    | exact (hb _ rfl).elim
    | exact (hk _ _ _ _ rfl).elim
    | exact (judged_keeps h).2 x hx
    | exact (justified_keeps h).2 x hx
    | exact (merged_keeps h).2 x hx
    | skip
  all_goals
    simp only [stepTurn] at h
    repeat' split at h
    all_goals first
      | contradiction
      | (cases h; done)
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; first | exact hx | simp [hx])
      | (cases h <;> first | exact hx | simp [hx])

/-- **A crash keeps what was sent and what landed**: the world recovered from any truncation of the log
is the replay of its longest prefix of whole records, so its obligations and landings are that
replay's. -/
theorem obligations_survive_crash {S : Session} (h : Reachable S) (k : Nat) :
    let m := whole logHash S.log k
    (recover logHash deployed genesis ((encodeAll logHash S.log).take k)).world.outstanding =
        (replay deployed genesis (S.log.take m)).outstanding ∧
      (recover logHash deployed genesis ((encodeAll logHash S.log).take k)).world.landed =
        (replay deployed genesis (S.log.take m)).landed := by
  have := (recover_eq_replay_prefix h k).1
  simp only at this ⊢
  rw [this]
  exact ⟨rfl, rfl⟩

/-! ## Retention, at the deployed machine (`Obend.Vault.Retention`) -/

/-- The anchor a record's turn names: a checkpoint record's (`compacted`), standing for a forgotten
prefix that ended at that receipt digest. -/
def anchorOfTurn (b : Bytes) : Option Nat :=
  match decodeTurn b with
  | .ok (.compacted _ _ a _) => some a
  | _ => none

/-- **`forget_sound`**: a session's log compacted after its first `n` records (the checkpoint record,
then the records after them) replays to the world the session serves, which is the replay of its
whole log; and a crash at any byte of the compacted log recovers the replay of its longest prefix of
whole records, a world the session served after the same records of its whole log, the rest dropped
as a torn tail. -/
theorem forget_sound {S : Session} (h : Reachable S) {n : Nat} {cp : Record}
    (hc : Retention.Compacts logHash deployed anchorOfTurn genesis S n cp) (k : Nat) :
    S.world = replay deployed genesis (cp :: S.log.drop n) ∧
      let C := cp :: S.log.drop n
      let m := whole logHash C k
      let tail := ((encodeAll logHash C).take k).drop (encodeAll logHash (C.take m)).length
      Retention.recoverLog logHash deployed anchorOfTurn genesis ((encodeAll logHash C).take k) =
          ⟨replay deployed genesis (C.take m), m, tail, tornWhy tail⟩ ∧
        replay deployed genesis (C.take m) = replay deployed genesis (S.log.take (if m = 0 then 0 else n + (m - 1))) ∧
        Reachable ⟨replay deployed genesis (C.take m), S.log.take (if m = 0 then 0 else n + (m - 1))⟩ :=
  ⟨Retention.state_eq_replay_compacted h hc, Retention.recover_eq_replay_prefix_compacted h hc k⟩

/-- A log never compacted reads, through `Retention.recoverLog`, exactly as `recover` reads it
(`recover_eq_replay_prefix` stands for it unchanged). -/
theorem recover_plain {S : Session} (h : Reachable S) (hplain : ∀ r ∈ S.log, anchorOfTurn r.payload = none)
    (k : Nat) :
    Retention.recoverLog logHash deployed anchorOfTurn genesis ((encodeAll logHash S.log).take k) =
      recover logHash deployed genesis ((encodeAll logHash S.log).take k) :=
  Retention.recoverLog_plain h hplain k

/-- **What a `forget` needs to be admitted**: nothing reaches into the prefix. No proposal sent from
here awaits its receipt; every form issued here is retired already or by this contract; no form it
retires has a continuity contract; every branch declared here has merged or is abandoned by it. -/
theorem needs_none_iff (w : World) (c : Retention.Contract) :
    needs w c = none ↔
      w.outstanding = [] ∧ (∀ f ∈ w.forms, (retiredBy w f.name).isSome ∨ f.name ∈ c.retire) ∧
        (∀ n ∈ c.retire, ((w.issues.find? (·.form == n)).bind (·.contract)) = none) ∧
        (∀ b ∈ w.forks, b.merged = true ∨ b.name ∈ c.abandon) := by
  unfold needs
  split
  · rename_i heq; simp [heq]
  · rename_i hout
    split
    · rename_i f rest hf
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ hall
      have hm : f ∈ w.forms.filter (fun f => (retiredBy w f.name).isNone && !c.retire.contains f.name) := by
        rw [hf]; simp
      simp only [List.mem_filter, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hm
      rcases hall f hm.1 with h1 | h1
      · rw [hm.2.1] at h1; simp at h1
      · exact absurd h1 (by simpa using hm.2.2)
    · rename_i hnf
      split
      · rename_i n rest hn
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ hall
        have hm : n ∈ c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome) := by
          rw [hn]; simp
        simp only [List.mem_filter, Option.isSome_iff_ne_none] at hm
        exact absurd (hall n hm.1) hm.2
      · rename_i hnn
        split
        · rename_i b rest hb
          simp only [reduceCtorEq, false_iff, not_and]
          intro _ _ _ hall
          have hm : b ∈ w.forks.filter (fun b => !b.merged && !c.abandon.contains b.name) := by
            rw [hb]; simp
          simp at hm
          rcases hall b hm.1 with h1 | h1
          · rw [hm.2.1] at h1; cases h1
          · exact absurd h1 (by simpa using hm.2.2)
        · rename_i hnb
          simp only [true_iff]
          refine ⟨by cases hout' : w.outstanding <;> simp_all, ?_, ?_, ?_⟩
          · intro f hf
            have : f ∉ w.forms.filter (fun f => (retiredBy w f.name).isNone && !c.retire.contains f.name) := by
              rw [hnf]; simp
            simp [hf] at this
            by_cases hr : retiredBy w f.name = none
            · exact .inr (by simpa using this hr)
            · exact .inl (Option.isSome_iff_ne_none.2 hr)
          · intro n hn
            have : n ∉ c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome) := by
              rw [hnn]; simp
            simp only [List.mem_filter, hn, true_and, Option.isSome_iff_ne_none] at this
            simpa using this
          · intro b hb
            have : b ∉ w.forks.filter (fun b => !b.merged && !c.abandon.contains b.name) := by
              rw [hnb]; simp
            simp [hb] at this
            by_cases hm : b.merged = true
            · exact .inl hm
            · exact .inr (by simpa using this (by simpa using hm))

/-- **`forget_refused_when_needed`**: a forget is refused, by name, while anything still reaches into
the prefix it would forget (`needs`: an obligation, an issued form it does not retire, a retired form
with a continuity contract, an unmerged branch it does not abandon); and a forget admitted needed
nothing. -/
theorem forget_refused_when_needed (w : World) (c : Retention.Contract) :
    (∀ e, needs w c = some e → (∀ n ∈ c.retire, w.forms.any (·.name == n)) → stepTurn w (.forget c) = .error e) ∧
      (∀ w' o, stepTurn w (.forget c) = .ok (w', o) → needs w c = none ∧ w'.retention = w.retention ++ [c]) := by
  constructor
  · intro e he hr
    have hf : c.retire.find? (fun n => !w.forms.any (·.name == n)) = none := by
      rw [List.find?_eq_none]; intro n hn; simp [hr n hn]
    simp only [stepTurn, hf, he]
  · intro w' o h
    simp only [stepTurn] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hn
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨hn, by rw [← h.1]⟩

/-- **A `forget` keeps the reasons**: they are world state, not a reading of the log, so a forget
leaves them as they were (and the `compacted` record that follows carries the world whole, reasons
and all). A proposed action admissible before a forget is admissible after it: no justification
reaches into the forgotten prefix, so `needs` names none. -/
theorem forget_keeps_reasons {w w' : World} {o : Outcome} {c : Retention.Contract}
    (h : stepTurn w (.forget c) = .ok (w', o)) :
    w'.reasons = w.reasons ∧ ∀ name, w'.reasons.admit name = w.reasons.admit name := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, fun _ => rfl⟩

/-- **`late_correction_refused`**: after a retention contract, a proposal for a form it retired is
refused naming the contract, by intent or without one; a merge from a branch it abandoned, or from a
replica whose log does not reach its horizon, is refused naming it. Never landed, never dropped in
silence: the turn is an error with the contract's name. -/
theorem late_correction_refused (w : World) :
    (∀ name digest hops a c, retiredBy w name = some c →
      stepTurn w (.judged name digest hops a none) = .error (lateText name c) ∧
      ∀ i, Transport.duplicateOf w.landed i = none →
        stepTurn w (.judged name digest hops a (some i)) = .error (lateText name c)) ∧
    (∀ label other skip og theirs reaches e, lateMerge w label reaches = some e →
      stepTurn w (.merged label other skip og theirs reaches) = .error e) ∧
    (∀ label c, w.retention.getLast? = some c → w.retention.find? (·.abandon.contains label) = none →
      lateMerge w label (some false) = some ("not merged: late: " ++ label ++ "'s log does not reach the horizon of the " ++
        "retention contract " ++ c.name ++ " (it forked before the prefix forgotten here); its corrections " ++
        "would arrive later than the contract allows")) := by
  refine ⟨fun name digest hops a c hc => ⟨?_, fun i hi => ?_⟩, fun label other skip og theirs reaches e he => ?_,
    fun label c hc hab => ?_⟩
  · simp only [stepTurn, judgeTurn, hc]
  · simp only [stepTurn, judgeTurn, hi, judgeNew, hc]
  · simp only [stepTurn, he]
  · simp only [lateMerge, hab, hc]

end Obend.Vault.Replay

end
