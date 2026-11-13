module
import all Obend.Vault.Log
import all Obend.Vault.WorldTree
public import Obend.Vault.Log
public import Obend.Vault.Json
public import Obend.Ledger.Commit
public import Obend.Vault.Form
public import Obend.Vault.FormCheckCache
public import Obend.Vault.Transport
public import Obend.Vault.Retention
public import Obend.Vault.Merge
public import Obend.Vault.WorldTree
public import Obend.Digest.Cshake256
public import Obend.Reasons
public import Obend.Run.Durable
public import Obend.Run.Proofs.Durable
public import Obend.Core.Ty
public import Obend.Core.Data
import all Obend.Run.Durable
import all Obend.Core.Data

public section
set_option pp.maxDepth 6
set_option pp.maxSteps 200

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

open Obend.Vault.Form (Form Grant Assignment Admitted)
open Obend.Vault.Rehydration (WitnessReceipt)
open Obend.Vault.Transport (Issue Grants Standing Landing Obligation Contract)

/-- The world beside a vault (`Obend.Vault.ChunkedWorld.World`). -/
abbrev World := Obend.Vault.ChunkedWorld.World

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
      (otherReasons : Option Obend.Reasons.State := none) (member : Option String := none)
  | resolved (k : Nat) (right : Bool)
  | rows (rs : List Row)
  | captured (situation name : String) (g : Grant) (src dst : String) (amount : Nat) (field : String)
      (refs : List String)
  | abstracted (name value hole : String)
  | briefed (page name : String) (g : Grant) (lits : List (String × String)) (holes : List (String × String))
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
  /-- a proposal sent from here and refused where it was judged, released by its sender by name: it awaits
  no receipt (2026-11-06: rowan's refused landing intent stayed outstanding in its fork for good) -/
  | released (intent : String)
  | forget (c : Retention.Contract)
  | compacted (count digest anchor : Nat) (w : World)
  | forked (name : String) (member : Option String := none)
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

/-! Batch lookups use one ordered index for the whole reconstruction. -/

def readingOfIndexed (s : Store) (V : List (String × String)) : List (String × Option String) :=
  let pages := Index.ofList Page.name s.pages
  V.map fun (n, t) => (n, if (Index.first pages n).bind Page.seen == some t then none else some t)

@[csimp] theorem readingOf_eq_indexed : @readingOf = @readingOfIndexed := by
  funext s V
  simp only [readingOf, readingOfIndexed, seenOf, Store.page?, Index.first_ofList] <;> rfl

def reconstructIndexed (s : Store) (files : List (String × Option String)) : List (String × String) :=
  let pages := Index.ofList Page.name s.pages
  files.map fun (n, o) => (n, o.getD (((Index.first pages n).bind Page.seen).getD ""))

@[csimp] theorem reconstruct_eq_indexed : @reconstruct = @reconstructIndexed := by
  funext s files
  simp only [reconstruct, reconstructIndexed, seenOf, Store.page?, Index.first_ofList]

def changedOfIndexed (s : Store) (V : List (String × String)) : List (String × String) :=
  let pages := Index.ofList Page.name s.pages
  V.filter fun (n, t) => (Index.first pages n).bind Page.seen != some t

@[csimp] theorem changedOf_eq_indexed : @changedOf = @changedOfIndexed := by
  funext s V
  simp only [changedOf, changedOfIndexed, seenOf, Store.page?, Index.first_ofList]

def reconstructSeenIndexed (s : Store) (changed : List (String × String)) : List (String × String) :=
  let pages := Index.ofList Page.name s.pages
  let files := Index.ofList Prod.fst changed
  (seenNames s).map fun n =>
    (n, ((Index.first files n).map Prod.snd).getD (((Index.first pages n).bind Page.seen).getD ""))

@[csimp] theorem reconstructSeen_eq_indexed : @reconstructSeen = @reconstructSeenIndexed := by
  funext s changed
  simp only [reconstructSeen, reconstructSeenIndexed, Index.first_pairs_lookup]
  simp only [seenOf, Store.page?, Index.first_ofList] <;> rfl

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
  match Form.judgeFill H w.store (Transport.recapture live f) hops a with
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

/-- A landing of ours come back: the other replica holds it as merged in from elsewhere (`receipt` 0)
and its intent landed here. -/
def returned (w : World) (l : Landing) : Bool :=
  l.receipt == 0 && (Transport.duplicateOf w.landed l.intent).isSome

/-- What a merge does with the other replica's landings (those this replica does not hold already):
each whose intent landed here is a duplicate; each none of whose grants stands after the merge (revocation wins,
`Obend.Vault.Transport.merge_revocation_wins`) is refused; the rest are admitted. -/
def sortLandings (w : World) (G : Grants) (theirs0 : List Landing) : List Landing × List Landing × List Landing :=
  -- a landing both replicas hold (from before they parted, or merged since) is no act of the other's;
  -- nor is a landing of ours that the other pulled in and brings back (2026-11-06: a fork that merged
  -- the tip after its taker's acceptance landed there, then merged back, had every later write to the
  -- landing's pages, its spent runs among them, dropped as "not landed twice")
  let theirs := theirs0.filter fun l => !w.landed.contains l && !returned w l
  let fresh := theirs.filter fun l => (Transport.duplicateOf w.landed l.intent).isNone
  let dups := theirs.filter fun l => (Transport.duplicateOf w.landed l.intent).isSome
  let refused := fresh.filter fun l => !(l.supports.any fun id => G.live.any (·.id == id))
  let admitted := fresh.filter fun l => l.supports.any fun id => G.live.any (·.id == id)
  (admitted, refused, dups)

/-- **A landing of ours that comes back is not the other's**: it is neither admitted, refused nor held
as a duplicate, so the merge skips none of its pages and the other replica's later writes to them
come in. -/
theorem sortLandings_returned (w : World) (G : Grants) (theirs : List Landing) (l : Landing)
    (h : returned w l = true) :
    l ∉ (sortLandings w G theirs).1 ∧ l ∉ (sortLandings w G theirs).2.1 ∧ l ∉ (sortLandings w G theirs).2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sortLandings, h]

/-- A sturdyref granting write standing over `cell`. -/
def mkWriteRef (uri cell : String) : Rehydration.Sturdyref Obend.Core.Data.Data :=
  { uri := uri, surface := [], log := [],
    lineage := { held := [.write], permits := fun _ => true },
    cellId := cell }

/-- Build `Merge.ForkAuth` at the tip for an optional member-attributed fork (`obend fork --for MEMBER`). -/
def forkAuthFor (here other : Store) (G : Grants) (who? : Option String) : Merge.ForkAuth :=
  match who? with
  | none => {}
  | some who =>
    if who == "" || who == "owner" then {} else
    let names := Merge.namesOf here other
    let mem? := here.member? who
    let memGrants := (mem?.map (·.grants)).getD []
    let memId := (mem?.map (·.id)).getD (here.members.length + 1)
    let liveSups := G.supports who
    let revSups := G.standing.filter fun s => G.revoked.contains s.id && s.grant.holder == who
    let memRefs := names.filterMap fun c =>
      if (mem?.map (fun m => m.may "write" c)) == some true then
        some (mkWriteRef ("member:" ++ who ++ ":write:" ++ c) c)
      else none
    let liveGrantRefs := names.flatMap fun c =>
      liveSups.filterMap fun s =>
        if Form.mayWrite (s.grant.viewer names) c then
          some (mkWriteRef ("grant:" ++ s.id ++ ":" ++ c) c)
        else none
    let revGrantRefs := names.flatMap fun c =>
      revSups.filterMap fun s =>
        if Form.mayWrite (s.grant.viewer names) c then
          some (mkWriteRef ("grant:" ++ s.id ++ ":" ++ c) c, ("grant:" ++ s.id ++ ":" ++ c, "owner"))
        else none
    let allRefs := memRefs ++ liveGrantRefs ++ revGrantRefs.map (·.1)
    let allRev := revGrantRefs.map (·.2)
    let tipAuth : Branch.Authority := { refs := allRefs, revoked := allRev }
    let reliesOf : String → Bool → List String := fun c isRelaw =>
      if isRelaw && (mem?.map (fun m => m.may "relaw" c)) != some true then []
      else
        let liveUris := (allRefs.filter fun sr => sr.cellId == c && tipAuth.live sr.uri).map (·.uri)
        if !liveUris.isEmpty then liveUris
        else (allRefs.filter fun sr => sr.cellId == c).map (·.uri)
    let extraWrite := (names.filter fun c => liveSups.any fun s => Form.mayWrite (s.grant.viewer names) c).map
      ("write", ·)
    { actor := who
      tipAuth := tipAuth
      reliesOf := reliesOf
      actorRef := .member ⟨who, memId, memGrants ++ extraWrite⟩ }

/-- The merge of another replica's store (with its grants and landings, when the record carries them). -/
def mergeStep (w : World) (label : String) (other : Store) (skipLedger : Bool) (og : Option Grants)
    (theirs : List Landing) (auth : Merge.ForkAuth := {}) : Except String (World × Outcome) :=
  match og, theirs with
  | none, _ =>
      let (s, notes) := Merge.mergeVault H w.store other label
        (skip := if skipLedger then Obend.Ledger.Cli.ledgerOwned else fun _ => false)
        (auth := auth)
      .ok ({ w with store := settle H s }, .merged s notes)
  | some og, theirs =>
      let G := w.grants.merge og
      let (admitted, refused, dups) := sortLandings w G theirs
      let held := (refused ++ dups).flatMap (·.pages)
      let (s, notes) := Merge.mergeVault H w.store other label
        (skip := fun n => (skipLedger && Obend.Ledger.Cli.ledgerOwned n) || held.contains n)
        (auth := auth)
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
not retire, a retired form whose continuity contract promised what retiring it would break (and no fill of it landed here), a branch
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
  -- a promise is discharged when a fill of its form landed here: the job it offered was taken
  -- (2026-11-06: both jobs landed and both forks merged, and the workshop's log could never be forgotten)
  match c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome &&
      !w.landed.any (·.form == n)) with
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
        match Form.judgeFill H w.store f hops a with
        | .error e => .error (name ++ ": " ++ e)
        | .ok (s, ad, t) =>
          let r := Form.receiptFor H w.receipts.getLast? f a ad t
          .ok ({ w with store := settle H s, receipts := w.receipts ++ [r] },
            .judged s ad t r (w.receipts.length + 1))

/-! ## What a merge keeps of a refused page, and the reasons that come with it -/

/-- `src` with its frontmatter field `k` set to `v` (the line replaced, or added before the closing `---`). -/
def setFrontField (src k v : String) : String :=
  match src.splitOn "\n" with
  | first :: rest =>
    if trim first == "---" then
      let fm := rest.takeWhile fun l => trim l != "---"
      let after := rest.dropWhile fun l => trim l != "---"
      let isK : String → Bool := fun l => ((splitColon l).map (·.1)) == some k
      let fm' := if fm.any isK then fm.map (fun l => if isK l then k ++ ": " ++ v else l) else fm ++ [k ++ ": " ++ v]
      "\n".intercalate (first :: fm' ++ after)
    else src
  | [] => src

/-- The frontmatter fields (not law lines) the other replica changed on a page since the base. -/
def fieldsMoved (base other : String) : List (String × String) :=
  let b := frontFields base
  (frontFields other).filter fun (k, v) => (lawKey k).isNone && b.lookup k != some v

/-- **A refused page keeps what it can.** A page the other replica moved past the base, whose write did
not land here (refused at the tip, alone or merged with here's): here's versions stand (a pair refused
together must not undo what here had landed), then each field the other replica changed since the base
is written here alone, judged by the page's laws as they stand, and kept when admitted (a spent count,
an evidence field: what happened stays recorded); the whole of the other's change, set on here's text,
stays the page's pending write with the refusal that names why. (2026-11-06: rowan's job page carried
its proposal and its `spent: 2`; the proposal broke `onbase`, the page did not come in, and the tip said
`spent: 0`; the tip's own law change on the page was rolled back to the base with it.) -/
def salvage (here other s : Store) (label n : String) : Store × List String × Bool :=
  match here.page? n, other.page? n, s.page? n with
  | some hp, some op, some sp =>
    let bp := Merge.sharedPrefix (Merge.historyIn here n) (Merge.historyIn other n)
    if op.history == bp || sp.history.length > hp.history.length then (s, [], false) else
    match hp.render?, op.render?, (bp.getLast?.map fun G => render G n op.who) with
    | some hText, some oText, some bText =>
      -- a field here's moves set too is the other's to move only if the other saw here's value (its
      -- history passes through it) and moved on; otherwise here's stands (2026-11-06: a fork that never
      -- saw its job landed brought `state: proposed` back over `landed`)
      let seenThere : String → List String := fun k =>
        op.history.filterMap fun G => (frontFields (render G n op.who)).lookup k
      let hf := frontFields hText
      let bf := frontFields bText
      let all := fieldsMoved bText oText
      let theirsToMove := fun (kv : String × String) =>
        hf.lookup kv.1 == bf.lookup kv.1 || ((hf.lookup kv.1).map fun hv => (seenThere kv.1).contains hv) == some true
      let moved := all.filter theirsToMove
      let contested := (all.filter (!theirsToMove ·)).map fun (k, v) =>
        k ++ " (here " ++ ((hf.lookup k).getD "unset") ++ ", " ++ label ++ " " ++ v ++ ")"
      if moved.isEmpty && contested.isEmpty then (s, [], false) else
      let restored := sp.history.length < hp.history.length
      let s0 := if restored then s.setPage hp else s
      let step := fun (acc : Store × List (String × String) × List String) (kv : String × String) =>
        let (st, kept, refused) := acc
        match st.page? n with
        | some p =>
          match p.render? with
          | some cur =>
            let ch := ownerWrite H st.entries st.turn p (setFrontField cur kv.1 kv.2) (env := st.environment)
            if ch.note.isNone && ch.history.length > p.history.length then
              (st.setPage (p.withChange ch), kept ++ [kv], refused)
            else (st, kept, refused ++ [kv.1])
          | none => (st, kept, refused ++ [kv.1])
        | none => (st, kept, refused ++ [kv.1])
      let (s1, kept, refused) := moved.foldl step (s0, [], [])
      let (s2, why) := match s1.page? n with
        | some p =>
          match p.render? with
          | some cur =>
            let whole := moved.foldl (fun t kv => setFrontField t kv.1 kv.2) cur
            if whole == cur then (s1, none) else
            let ch := ownerWrite H s1.entries s1.turn p whole (env := s1.environment)
            if ch.note.isNone && ch.history.length > p.history.length then (s1.setPage (p.withChange ch), none)
            else (s1.setPage (p.withChange ch), ch.note)
          | none => (s1, none)
        | none => (s1, none)
      let keptText := ", ".intercalate (kept.map fun (k, v) =>
        k ++ " " ++ ((hText |> frontFields |>.lookup k).getD "unset") ++ " → " ++ v)
      let lines := (if restored then [n ++ ": here's write stands (landed here before the merge)"] else []) ++
        (if contested.isEmpty then [] else [n ++ ": here's stands where " ++ label ++ " did not see it move: " ++
          ", ".intercalate contested]) ++
        (if kept.isEmpty then [] else [n ++ ": kept from " ++ label ++ ": " ++ keptText]) ++
        (match why with
          | some w => [n ++ ": pending here, as " ++ label ++ " wrote it on this page as it is (" ++
              ", ".intercalate refused ++ "): " ++ w]
          | none => [])
      (s2, lines, restored)
    | _, _, _ => (s, [], false)
  | _, _, _ => (s, [], false)

/-- **What a fork has not seen**: for each page both replicas moved since their base (the pages the
fork worked on), the fields here's moves set that the other left as they were at the base, and the law
lines here added that the other's page lacks. A fork that wrote a page to the tip's terms is not
behind on it. -/
def behindOn (here other : Store) : List (String × List String) :=
  here.pages.filterMap fun p =>
    let bp := Merge.sharedPrefix (Merge.historyIn here p.name) (Merge.historyIn other p.name)
    match bp.getLast?, p.render?, (other.page? p.name).bind (·.render?) with
    | some B, some cur, some theirs =>
      if Merge.liveHistory here p.name == bp || Merge.liveHistory other p.name == bp then none else
      let bt := render B p.name p.who
      let bf := frontFields bt
      let tf := frontFields theirs
      -- a field here's moves set and the other left as it was at the base: the other has not seen it
      -- (a field the other changed itself is its own; a merge may have brought it here already)
      let fields := ((frontFields cur).filter fun (k, v) => (lawKey k).isNone && bf.lookup k != some v &&
        tf.lookup k != some v && tf.lookup k == bf.lookup k).map (·.1)
      let laws := ((lawLines cur).filter fun l => !(lawLines bt).contains l && !(lawLines theirs).contains l).map
        (fun (k, _) => "law " ++ k)
      if fields.isEmpty && laws.isEmpty then none else some (p.name, fields ++ laws)
    | _, _, _ => none

/-- An event of the reasons, said. -/
def eventText : Obend.Reasons.Event → String
  | .observe o => "observation " ++ o.name
  | .assume a => "assumption " ++ a
  | .withdraw a => "withdrawal of " ++ a
  | .explain r => "explanation " ++ r.name ++ " (" ++ Obend.Reasons.ruleText r ++ ")"
  | .defeat d => "defeat of " ++ d.target ++ " by " ++ d.by'
  | .propose a => "proposal " ++ a.name

/-- A replica's bookkeeping of what another has seen (`behind-LABEL`, `stale-LABEL`): its own, never
joined elsewhere, and no part of what an explanation says (an explanation that went out and came back
with another replica's flag on it is the same explanation). -/
def bookkeeping (a : String) : Bool := a.startsWith "behind-" || a.startsWith "stale-"

/-- **A fork's reasons come back with it**: what the other replica observed, assumed, explained,
defeated and proposed that this one does not hold joins this one's reasons, each event stepped here,
so the judgment is this vault's over the union (`Obend.Reasons.State.step`: consistent after each);
an event this vault refuses (a name it uses for something else) is said and left out. -/
def joinReasons (label : String) (r o : Obend.Reasons.State) (behind : List (String × List String) := []) :
    Obend.Reasons.State × List String :=
  let b := o.base
  -- the other's explanations hold here only while it is not behind the tip: `behind-LABEL`, an
  -- assumption this merge holds while some page moved here that the other has not seen
  let flag := "behind-" ++ label
  let (r, flagNotes) : Obend.Reasons.State × List String :=
    if !behind.isEmpty && !b.explanations.isEmpty && !r.base.held.contains flag then
      match r.step (.assume flag) with
      | .ok st => (st, [flag ++ ": assumed here, " ++ label ++ " has not seen " ++ "; ".intercalate (behind.map fun (n, fs) =>
          n ++ " " ++ ", ".intercalate fs) ++ "; its explanations hold here only without it"])
      | .error _ => (r, [])
    else if behind.isEmpty && r.base.held.contains flag then
      match r.step (.withdraw flag) with
      | .ok st =>
        -- what the other explained before it saw what moved here does not hold again now that it has:
        -- each of its explanations joined here in an earlier merge (they carry the flag) is defeated by
        -- `stale-LABEL`, held from now on; what it explains anew joins as any explanation does
        let stale := "stale-" ++ label
        let olds := (st.base.explanations.filter fun e => e.neg.contains flag &&
          !st.base.defeaters.contains ⟨e.name, stale⟩).map (·.name)
        if olds.isEmpty then (st, [flag ++ ": withdrawn, " ++ label ++ " has seen what moved here"]) else
        let st1 := if st.base.held.contains stale then st else (st.step (.assume stale)).toOption.getD st
        let st2 := olds.foldl (fun acc n => (acc.step (.defeat ⟨n, stale⟩)).toOption.getD acc) st1
        (st2, [flag ++ ": withdrawn, " ++ label ++ " has seen what moved here; what it explained before ("
          ++ ", ".intercalate olds ++ ") is defeated by " ++ stale ++ ": explain it anew to count"])
      | .error _ => (r, [])
    else (r, [])
  let mine := r.base
  let clash := (b.observations.filter fun x => mine.observations.any fun y => y.name == x.name && y != x).map
      (fun x => label ++ "'s observation " ++ x.name ++ ": not joined: observed here otherwise") ++
    (b.explanations.filter fun x => mine.explanations.any fun y =>
        y.name == x.name && { y with neg := y.neg.filter (!bookkeeping ·) } != { x with neg := x.neg.filter (!bookkeeping ·) }).map
      (fun x => label ++ "'s explanation " ++ x.name ++ ": not joined: a different explanation has that name here")
  let evs : List Obend.Reasons.Event :=
    (b.observations.filter fun x => !mine.observations.any (·.name == x.name)).map .observe ++
    (b.held.filter fun a => !mine.held.contains a && !bookkeeping a).map .assume ++
    (b.explanations.filter fun e => !mine.explanations.any (·.name == e.name)).map
      (fun e => .explain { e with neg := e.neg ++ [flag] }) ++
    (b.defeaters.filter fun d => !mine.defeaters.contains d).map .defeat ++
    (b.actions.filter fun a => !mine.actions.any (·.name == a.name)).map .propose
  let (r', notes) := evs.foldl (fun (acc : Obend.Reasons.State × List String) e =>
    match acc.1.step e with
    | .ok st => (st, acc.2 ++ [label ++ "'s " ++ eventText e ++ ": joined here"])
    | .error err => (acc.1, acc.2 ++ [label ++ "'s " ++ eventText e ++ ": not joined: " ++ err])) (r, [])
  let concls := (evs.filterMap fun e => match e with | .explain x => some x.concl | _ => none).eraseDups
  (r', flagNotes ++ clash ++ notes ++ concls.map fun c => "  judged here: " ++ r'.line c)

/-- After a merge: the pages it refused keep what they can (`salvage`), and the other's reasons join. -/
def afterMerge (w0 w : World) (o : Outcome) (label : String) (other : Store)
    (rs : Option Obend.Reasons.State) (held : String → Bool := fun _ => false) : World × Outcome :=
  -- a page the merge held back on purpose (a landing whose grants were revoked here, a duplicate, the
  -- ledger's register) is not the merge's refusal: nothing of it is kept
  let moved := (other.pages.map (·.name)).filter (!held ·)
  let (s, lines, restored) := moved.foldl (fun (acc : Store × List String × List String) n =>
    let (st, ls, r) := salvage w0.store other acc.1 label n
    (st, acc.2.1 ++ ls, if r then acc.2.2 ++ [n] else acc.2.2)) (w.store, [], [])
  let (r, rlines) := match rs with
    | some r => joinReasons label w.reasons r (behindOn w0.store other)
    | none => (w.reasons, [])
  let o' := match o with
    | .merged _ notes =>
      let notes' := notes.filter fun l => !restored.any fun n => l.startsWith (n ++ ": here's write was ")
      Outcome.merged s (notes' ++ lines ++ rlines)
    | x => x
  ({ w with store := if lines.isEmpty then w.store else settle H s, reasons := r }, o')

/-- After a merge, what is outstanding and what landed are as the merge left them. -/
theorem afterMerge_outstanding (w0 w : World) (o : Outcome) (label : String) (other : Store)
    (rs : Option Obend.Reasons.State) (held : String → Bool) :
    (afterMerge w0 w o label other rs held).1.outstanding = w.outstanding := by
  unfold afterMerge; rfl

theorem afterMerge_landed (w0 w : World) (o : Outcome) (label : String) (other : Store)
    (rs : Option Obend.Reasons.State) (held : String → Bool) :
    (afterMerge w0 w o label other rs held).1.landed = w.landed := by
  unfold afterMerge; rfl

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
  | .merged label other skipLedger og theirs reaches rs member =>
    match lateMerge w label reaches with
    | some e => .error e
    | none =>
      let effWho := member.orElse fun _ => w.forkMembers.lookup label
      let mergedG := match og with | some g => w.grants.merge g | none => w.grants
      let auth := forkAuthFor w.store other mergedG effWho
      match mergeStep w label other skipLedger og theirs auth with
      | .ok (w', o) =>
        let held : List String := match og with
          | some g => let (_, refused, dups) := sortLandings w (w.grants.merge g) theirs
                      (refused ++ dups).flatMap (·.pages)
          | none => []
        let unauth : String → Bool := fun n =>
          auth.actor != "owner" && !(auth.reliesOf n false).any (auth.tipAuth.live ·)
        let (w'', o') := afterMerge w w' o label other rs
          (fun n => held.contains n || unauth n || (skipLedger && Obend.Ledger.Cli.ledgerOwned n))
        let hasRefusal := match o' with
          | .merged _ ns => ns.any fun l => (l.splitOn ": not merged").length > 1
          | _ => false
        let nextForkMembers := if hasRefusal then w''.forkMembers else w''.forkMembers.filter (·.1 != label)
        .ok ({ w'' with forks := markMerged w''.forks label, forkMembers := nextForkMembers }, o')
      | .error e => .error e
  | .resolved k right =>
    match Merge.resolveIn w.store k (if right then .right else .left) with
    | .ok (s, receipt) => .ok ({ w with store := settle H s }, .resolved s receipt)
    | .error e => .error ("not resolved: " ++ e)
  | .captured situation name g src dst amount field refs =>
    if w.forms.any (·.name == name) then .error ("refused: a form named " ++ name ++ " exists") else
    match Form.captureFrom w.store situation name g src dst amount field refs with
    | .ok (f, culled) =>
      .ok ({ w with forms := w.forms ++ [f],
                    checked := w.checked.filter (·.form != name) ++ (f.checksAt H w.store).map (·.record) }, .form f culled)
    | .error e => .error ("refused: " ++ e)
  | .briefed page name g lits holes =>
    if w.forms.any (·.name == name) then .error ("refused: a form named " ++ name ++ " exists") else
    match Form.briefFrom w.store page name g lits (holes.map fun (h, t) => (h, Form.holeTyOf t)) with
    | .ok (f, culled) => .ok ({ w with forms := w.forms ++ [f] }, .form f culled)
    | .error e => .error ("refused: " ++ e)
  | .abstracted name value hole =>
    match w.forms.find? (·.name == name) with
    | none => .error ("refused: no form named " ++ name)
    | some f =>
      match f.abstract value hole with
      | .ok g =>
        .ok ({ w with forms := w.forms.map fun x => if x.name == name then g else x,
                      checked := w.checked.filter (·.form != name) ++ (g.checksAt H w.store).map (·.record) }, .form g 0)
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
  | .forked name member =>
    if w.forks.any (fun b => b.name == name && !b.merged) then .error ("refused: the branch " ++ name ++ " is out already")
    else
      let fm := (w.forkMembers.filter (·.1 != name)) ++
        (match member with | some m => if m == "" || m == "owner" then [] else [(name, m)] | none => [])
      .ok ({ w with forks := (w.forks.filter (·.name != name)) ++ [⟨name, false⟩], forkMembers := fm }, .quiet)
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
  | .released i =>
    if w.outstanding.any (·.intent == i) then
      .ok ({ w with outstanding := w.outstanding.filter (·.intent != i) }, .quiet)
    else .error ("refused: no proposal sent from here awaits a receipt for intent " ++ i)
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
    (if w.reasons == {} then [] else [("reasons", Obend.Reasons.stateJson w.reasons)]) ++
    (if w.checked.isEmpty then [] else [("checked", Json.arr (w.checked.map Form.checkedJson).toArray)]) ++
    (if w.forkMembers.isEmpty then [] else [("forkMembers", pairsJson w.forkMembers)])))

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
  -- a check read back is checked again: only what the checker accepts here is kept
  let checked ← opt "checked" [] fun v => do
    (← v.getArr?).toList.mapM Form.checkedOf
  let forkMembers ← opt "forkMembers" [] pairsOf
  return ⟨store, journal, forms, receipts, received, sent, issues, grants, landed, outstanding, minted, retention, forks,
    reasons, checked, forkMembers⟩

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
  | .merged label other skip og theirs reaches rs member => Json.mkObj ([("turn", Json.str "merge"), ("label", Json.str label),
      ("other", storeJson other), ("skipLedger", toJson skip)] ++
      (match rs with | some r => [("otherReasons", Obend.Reasons.stateJson r)] | none => []) ++
      (match og with
        | some g => [("otherGrants", Transport.grantsJson g),
            ("otherLanded", Json.arr (theirs.map Transport.landingJson).toArray)]
        | none => []) ++
      (match reaches with | some b => [("reaches", toJson b)] | none => []) ++
      (match member with | some m => [("for", Json.str m)] | none => []))
  | .resolved k right => Json.mkObj [("turn", "resolve"), ("conflict", toJson k), ("right", toJson right)]
  | .rows rs => Json.mkObj [("turn", "rows"), ("rows", Json.arr (rs.map rowJson).toArray)]
  | .captured situation name g src dst amount field refs => Json.mkObj [("turn", "capture"),
      ("situation", Json.str situation), ("name", Json.str name), ("grant", Form.grantJson g),
      ("src", Json.str src), ("dst", Json.str dst), ("amount", toJson amount), ("field", Json.str field),
      ("refs", strsJson refs)]
  | .briefed page name g lits holes => Json.mkObj [("turn", "brief"), ("page", Json.str page),
      ("name", Json.str name), ("grant", Form.grantJson g),
      ("set", Json.arr (lits.map fun (f, v) => Json.mkObj [("field", Json.str f), ("value", Json.str v)]).toArray),
      ("holes", Json.arr (holes.map fun (h, t) => Json.mkObj [("hole", Json.str h), ("type", Json.str t)]).toArray)]
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
  | .released i => Json.mkObj [("turn", "release"), ("intent", Json.str i)]
  | .forget c => Json.mkObj [("turn", "forget"), ("contract", Retention.contractJson c)]
  | .compacted count digest anchor w => Json.mkObj [("turn", "compacted"), ("count", toJson count),
      ("digest", toJson digest), ("anchor", toJson anchor), ("world", worldJson w)]
  | .forked name member => Json.mkObj ([("turn", Json.str "fork"), ("name", Json.str name)] ++
      (match member with | some m => [("for", Json.str m)] | none => []))
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
    let member := (j.getObjValAs? String "for").toOption
    match j.getObjVal? "otherGrants" with
    | .ok g =>
      let theirs ← (← j.getObjValAs? (Array Json) "otherLanded").toList.mapM Transport.landingOf
      let reaches := (j.getObjValAs? Bool "reaches").toOption
      let rs ← match j.getObjVal? "otherReasons" with
        | .ok r => some <$> Obend.Reasons.stateOf r
        | .error _ => pure none
      return .merged label other skip (some (← Transport.grantsOf g)) theirs reaches rs member
    | .error _ => return .merged label other skip none [] (j.getObjValAs? Bool "reaches").toOption none member
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
  | "brief" =>
    let page ← j.getObjValAs? String "page"
    let name ← j.getObjValAs? String "name"
    let g ← Form.grantOf (← j.getObjVal? "grant")
    let lits ← (← j.getObjValAs? (Array Json) "set").toList.mapM fun x => do
      return (← x.getObjValAs? String "field", ← x.getObjValAs? String "value")
    let holes ← (← j.getObjValAs? (Array Json) "holes").toList.mapM fun x => do
      return (← x.getObjValAs? String "hole", ← x.getObjValAs? String "type")
    return .briefed page name g lits holes
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
  | "release" => return .released (← j.getObjValAs? String "intent")
  | "forget" => return .forget (← Retention.contractOf (← j.getObjVal? "contract"))
  | "compacted" =>
    let count ← j.getObjValAs? Nat "count"
    let digest ← j.getObjValAs? Nat "digest"
    let anchor ← j.getObjValAs? Nat "anchor"
    return .compacted count digest anchor (← worldOf (← j.getObjVal? "world"))
  | "fork" => return .forked (← j.getObjValAs? String "name") (j.getObjValAs? String "for").toOption
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

/-- A world in the encoding before histories were written as growth: what a record written by an
earlier binary commits to (`fullHistories`). -/
def encodeWorldFull (w : World) : Bytes :=
  let j := worldJson w
  textBytes ((match j.getObjVal? "store" with
    | .ok st => j.setObjVal! "store" (fullHistories st)
    | .error _ => j).compress)

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
  | .briefed .. => "brief"
  | .judged .. => "judge"
  | .filled .. => "fill"
  | .issued .. => "issue"
  | .offered .. => "offer"
  | .granted .. => "grant"
  | .revoked .. => "revoke"
  | .transported .. => "transport"
  | .proposed .. => "propose"
  | .confirmed .. => "confirm"
  | .released .. => "release"
  | .forget .. => "forget"
  | .compacted .. => "compacted"
  | .forked .. => "fork"
  | .reasoned .. => "reason"
  | .justified .. => "justified"

/-! ## The deployed machine and its theorems -/

/-- **The deployed machine**: a record's bytes are decoded to a turn and stepped by `stepTurn`;
its world commitment is the canonical Merkleized manifest (`ChunkedWorld.manifestBytes`). -/
def deployed : Machine World Outcome where
  step w b := do stepTurn w (← decodeTurn b)
  encW := ChunkedWorld.manifestBytes

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

/-- **A check a session keeps is the log's**: every check record the world a session serves holds is
one the replay of its log makes (`state_eq_replay_log`), and the checks a command uses are made again
from those records by the checker (`Form.checksOf`); no file the vault reads stands for one. -/
theorem checks_replayed {S : Session} (h : Reachable S) :
    ∀ r ∈ S.world.checked, r ∈ (replay deployed genesis S.log).checked :=
  fun r hr => state_eq_replay_log h ▸ hr

/-- **A capture's checks are the capture's**: the turn that captures a form keeps the records of the
checks of the judgments a fill of it makes at the store it was captured from (`Form.checksAt`), in
place of any it kept under that name before; made again, they are those checks
(`Form.checksOf_records`). -/
theorem captured_checks {w w' : World} {o : Outcome} {situation name : String} {g : Form.Grant} {src dst : String}
    {amount : Nat} {field : String} {refs : List String}
    (h : stepTurn w (.captured situation name g src dst amount field refs) = .ok (w', o)) :
    ∃ f culled, Form.captureFrom w.store situation name g src dst amount field refs = .ok (f, culled) ∧
      w'.checked = w.checked.filter (·.form != name) ++ (f.checksAt H w.store).map (·.record) := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · split at h
    · rename_i f culled hf
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨f, culled, hf, rfl⟩
    · cases h

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

/-- Decode a checkpoint's world bytes: sharded Merkle manifest when present, falling back to legacy
monolithic JSON (`decodeWorld`). -/
def decodeCheckpointWorld (store : String → Option Bytes) (b : Bytes) : Option World :=
  match ChunkedWorld.decodeManifestWith store b with
  | .ok w => some w
  | .error _ => decodeWorld b

/-- **`checkpoint_is_cache`**: at every truncation of the deployed entry's log, recovering from a
checkpoint it wrote is recovering from genesis. The premise is the check the entry makes before it
writes a checkpoint: the world's bytes decode to the world. -/
theorem checkpoint_is_cache {S : Session} (h : Reachable S) {n : Nat} (hn0 : 0 < n) (hn : n ≤ S.log.length)
    {decW : Bytes → Option World}
    (hcache : decW (deployed.encW (replay deployed genesis (S.log.take n))) =
      some (replay deployed genesis (S.log.take n))) (k : Nat) :
    recoverWith logHash deployed decW genesis (checkpointAt logHash deployed genesis S.log n)
        ((encodeAll logHash S.log).take k) =
      recover logHash deployed genesis ((encodeAll logHash S.log).take k) :=
  Log.checkpoint_is_cache h hn0 hn hcache k

/-- **`sharded_checkpoint_is_cache`**: at every truncation of the deployed entry's log, when the
shard store holds the shards named by the checkpoint's world, recovering from the sharded checkpoint
equals recovering from genesis — with NO unproved JSON round-trip premise (`hcache` is discharged
universally by `ChunkedWorld.decodeManifestWith_manifestBytes`). -/
theorem sharded_checkpoint_is_cache {S : Session} (h : Reachable S) {n : Nat} (hn0 : 0 < n)
    (hn : n ≤ S.log.length) (store : String → Option Bytes)
    (hstore : ∀ k sb,
      (k, sb) ∈ (ChunkedWorld.encodeShardedWorld (replay deployed genesis (S.log.take n))).shards →
        store k = some sb)
    (k : Nat) :
    recoverWith logHash deployed (decodeCheckpointWorld store) genesis
        (checkpointAt logHash deployed genesis S.log n) ((encodeAll logHash S.log).take k) =
      recover logHash deployed genesis ((encodeAll logHash S.log).take k) := by
  apply Log.checkpoint_is_cache h hn0 hn ?_ k
  have hm := ChunkedWorld.decodeManifestWith_manifestBytes (replay deployed genesis (S.log.take n)) store hstore
  change decodeCheckpointWorld store (ChunkedWorld.manifestBytes (replay deployed genesis (S.log.take n))) = _
  simp [decodeCheckpointWorld, hm]

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
    {theirs : List Landing} {auth : Merge.ForkAuth} {o : Outcome}
    (h : mergeStep w label other skip og theirs auth = .ok (w1, o)) :
    w1.outstanding = w.outstanding ∧ ∀ x ∈ w.landed, x ∈ w1.landed := by
  unfold mergeStep at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h) <;>
    exact ⟨rfl, fun x hx => by simp [hx]⟩

theorem merged_keeps {w w' : World} {o : Outcome} {label : String} {other : Store} {skip : Bool}
    {og : Option Grants} {theirs : List Landing} {reaches : Option Bool} {rs : Option Obend.Reasons.State}
    {member : Option String}
    (h : stepTurn w (.merged label other skip og theirs reaches rs member) = .ok (w', o)) :
    (∀ x ∈ w.outstanding, x ∈ w'.outstanding) ∧ (∀ x ∈ w.landed, x ∈ w'.landed) := by
  simp only [stepTurn] at h
  split at h
  · cases h
  · split at h
    · rename_i w1 o1 hm
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have := mergeStep_keeps hm
      exact ⟨fun x hx => by simp [afterMerge_outstanding, this.1, hx],
        fun x hx => by simp only [afterMerge_landed]; exact this.2 x hx⟩
    · cases h

/-- **An obligation outlives every turn but its confirmation**: a revision, a transport, a merge, a
judgment or a crash's recovery (which replays turns) keeps every proposal sent and not yet confirmed;
only `confirmed` takes one away, and `released`, its sender's release of it by name, and `base` and `compacted` stand only first in a log, for the world
of what came before. -/
theorem outstanding_kept {w w' : World} {o : Outcome} {t : Turn} (h : stepTurn w t = .ok (w', o))
    (hb : ∀ w0, t ≠ .base w0) (hk : ∀ n d a w0, t ≠ .compacted n d a w0) (hc : ∀ i e, t ≠ .confirmed i e)
    (hr : ∀ i, t ≠ .released i) :
    ∀ x ∈ w.outstanding, x ∈ w'.outstanding := by
  intro x hx
  cases t
  all_goals first
    | exact (hb _ rfl).elim
    | exact (hk _ _ _ _ rfl).elim
    | exact (hc _ _ rfl).elim
    | exact (hr _ rfl).elim
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
retires has a continuity contract no fill of it discharged by landing here; every branch declared here
has merged or is abandoned by it. -/
theorem needs_none_iff (w : World) (c : Retention.Contract) :
    needs w c = none ↔
      w.outstanding = [] ∧ (∀ f ∈ w.forms, (retiredBy w f.name).isSome ∨ f.name ∈ c.retire) ∧
        (∀ n ∈ c.retire, ((w.issues.find? (·.form == n)).bind (·.contract)) = none ∨
          w.landed.any (·.form == n) = true) ∧
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
        have hm : n ∈ c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome &&
            !w.landed.any (·.form == n)) := by
          rw [hn]; simp
        simp only [List.mem_filter, Bool.and_eq_true, Option.isSome_iff_ne_none, Bool.not_eq_true'] at hm
        rcases hall n hm.1 with h1 | h1
        · exact absurd h1 hm.2.1
        · rw [hm.2.2] at h1; cases h1
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
            have : n ∉ c.retire.filter (fun n => ((w.issues.find? (·.form == n)).bind (·.contract)).isSome &&
                !w.landed.any (·.form == n)) := by
              rw [hnn]; simp
            simp only [List.mem_filter, hn, true_and, Bool.and_eq_true, Option.isSome_iff_ne_none,
              Bool.not_eq_true', not_and] at this
            by_cases h : ((w.issues.find? (·.form == n)).bind (·.contract)) = none
            · exact .inl h
            · exact .inr (by simpa using this h)
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
    (∀ label other skip og theirs reaches rs member e, lateMerge w label reaches = some e →
      stepTurn w (.merged label other skip og theirs reaches rs member) = .error e) ∧
    (∀ label c, w.retention.getLast? = some c → w.retention.find? (·.abandon.contains label) = none →
      lateMerge w label (some false) = some ("not merged: late: " ++ label ++ "'s log does not reach the horizon of the " ++
        "retention contract " ++ c.name ++ " (it forked before the prefix forgotten here); its corrections " ++
        "would arrive later than the contract allows")) := by
  refine ⟨fun name digest hops a c hc => ⟨?_, fun i hi => ?_⟩,
    fun label other skip og theirs reaches rs member e he => ?_,
    fun label c hc hab => ?_⟩
  · simp only [stepTurn, judgeTurn, hc]
  · simp only [stepTurn, judgeTurn, hi, judgeNew, hc]
  · simp only [stepTurn, he]
  · simp only [lateMerge, hab, hc]

end Obend.Vault.Replay

/-
# Obend.Run.VaultDurableBridge — Segmented Disk Log → `Run.Durable` Simulation & `Transferable` Plans

1. **Part A (`SegmentLog` → `Run.Durable`):** Forward simulation (`SegmentedSimInv`,
   `segmentedStep_refines_durable`) between fixed-width `SegmentLog` disk blocks of `OBL1` frames
   and `Run.Durable`, proving multi-segment rotation (`segmented_append_rotates_across_boundary`),
   torn-tail crash recovery (`parseFrom_committed_with_torn_frame`,
   `segmented_torn_crash_recover_idempotent`), and `segmented_exposed_once`.
2. **Part B (`Ty.isTransferable` + `CapTable` Sealing Across `.perform`):** Extends `Ty.isData` /
   `Ty.isPlan` with `.custody` leaves while forbidding higher-order types, and proves exact linear
   capability dehydration/rehydration round-trip (`rehydrate_dehydrate_roundtrip`), custody
   conservation (`transfer_conserves_custody_exact`), and deterministic forgery/tamper refusals.
-/


set_option autoImplicit false

/-! ## Part B.1 — `Ty.isTransferable` on `Obend.Core.Ty` -/

namespace Obend.Core.Ty

/-- First-order transferable types: `Ty.isData` extended with linear `.custody` leaves. -/
def Ty.isTransferable : Ty → Bool
  | .natural | .label | .boolean | .emptyRow | .custody _ => true
  | .field _ member tail => member.isTransferable && tail.isTransferable
  | .variant row => row.isTransferable
  | _ => false

/-- A capability-carrying Plan is a variant sum over `isTransferable` action payloads. -/
def Ty.isTransferablePlan : Ty → Bool
  | .variant row => row.isTransferable
  | _ => false

theorem isData_imp_isTransferable : ∀ (ty : Ty), ty.isData = true → ty.isTransferable = true
  | .natural, _ | .label, _ | .boolean, _ | .emptyRow, _ => rfl
  | .field _ member tail, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp [Ty.isTransferable, isData_imp_isTransferable member h.1, isData_imp_isTransferable tail h.2]
  | .variant row, h => by
    simp only [Ty.isData] at h; simp [Ty.isTransferable, isData_imp_isTransferable row h]

theorem isPlan_imp_isTransferablePlan (ty : Ty) (h : ty.isPlan = true) :
    ty.isTransferablePlan = true := by
  cases ty with
  | variant row => exact isData_imp_isTransferable row h
  | _ => cases h

/-- `.custody id` is `isTransferable` (crosses `.perform` via `CapTable`) but not pure `isData`. -/
theorem custody_isTransferable_not_isData (id : Nat) :
    (Ty.custody id).isTransferable = true ∧ (Ty.custody id).isData = false := ⟨rfl, rfl⟩

/-- `isTransferable` forbids closures, activities, prototypes, specifications, and rigid variables. -/
theorem isTransferable_forbids_higher_order (ty : Ty) (h : ty.isTransferable = true) :
    ty.isComputation = false ∧ (∀ r q d c, ty ≠ .arrow r q d c) ∧
    (∀ s t, ty ≠ .prototype s t) ∧ (∀ m e, ty ≠ .specification m e) ∧
    (∀ idx, ty ≠ .variable idx) := by
  cases ty <;> simp_all [Ty.isTransferable, Ty.isComputation]

end Obend.Core.Ty

namespace Obend.Run.VaultDurableBridge

open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Vault.Log (Bytes Record Drop encodeRecord encodeAll parseOne parseFrom
  Linked lastHash dig dig_lt Hr be unbe bound magic)
open Obend.Vault.Rehydration (WitnessReceipt genesisSentinel)
open Obend.Vault.SegmentLog (capacity split split_join)
open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared Obend.Run.Durable

/-! ## Part A — Segmented Disk Log (`SegmentLog`) Refines `Run.Durable` -/

/-- Canonical little-endian variable-length byte encoding of `Nat` (`[]` for `0`). -/
def encodeNatLE : Nat → Bytes
  | 0 => []
  | n + 1 => UInt8.ofNat ((n + 1) % 256) :: encodeNatLE ((n + 1) / 256)
termination_by n => n

/-- Inverse decoder for `encodeNatLE`. -/
def decodeNatLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeNatLE bs

@[simp] theorem decodeNatLE_encodeNatLE (n : Nat) : decodeNatLE (encodeNatLE n) = n := by
  induction n using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [encodeNatLE, decodeNatLE]
    | succ m =>
      rw [encodeNatLE]; simp only [decodeNatLE, UInt8.toNat_ofNat']
      rw [ih ((m + 1) / 256) (by omega)]; omega

/-- A committed durable log entry persisted on disk (`journal` append or `outbox` exposure). -/
inductive DiskEntry (Ev : Type) where
  | journalAppend (ev : Ev)
  | outboxExpose (pos : Nat)
  deriving DecidableEq, Repr

/-- Verified byte-level wire codec for domain joint events `Ev`. -/
structure EventWireCodec (Ev : Type) where
  encodeEv : Ev → Bytes
  decodeEv : Bytes → Option Ev
  decode_encodeEv : ∀ (ev : Ev), decodeEv (encodeEv ev) = some ev

/-- Inhabited canonical `EventWireCodec` for `Nat` payloads. -/
def natEventCodec : EventWireCodec Nat where
  encodeEv := encodeNatLE
  decodeEv := fun bs => some (decodeNatLE bs)
  decode_encodeEv := fun ev => congrArg some (decodeNatLE_encodeNatLE ev)

/-- Encode `DiskEntry Ev` with a 1-byte tag prefix (`0x01` = journal, `0x02` = outbox). -/
def encodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev) : DiskEntry Ev → Bytes
  | .journalAppend ev => (1 : UInt8) :: codec.encodeEv ev
  | .outboxExpose pos => (2 : UInt8) :: encodeNatLE pos

/-- Decode `DiskEntry Ev` from payload bytes. -/
def decodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev) : Bytes → Option (DiskEntry Ev)
  | 1 :: rest => (codec.decodeEv rest).map .journalAppend
  | 2 :: rest => some (.outboxExpose (decodeNatLE rest))
  | _ => none

@[simp] theorem decodeDiskEntry_encodeDiskEntry {Ev : Type} (codec : EventWireCodec Ev)
    (e : DiskEntry Ev) : decodeDiskEntry codec (encodeDiskEntry codec e) = some e := by
  cases e with
  | journalAppend ev => simp [encodeDiskEntry, decodeDiskEntry, codec.decode_encodeEv]
  | outboxExpose pos => simp [encodeDiskEntry, decodeDiskEntry]

/-- Left-to-right fold of decoded `DiskEntry` records into `(journal, outbox)`. -/
def foldDiskEntries {Ev : Type} (codec : EventWireCodec Ev) :
    List Record → List Ev → List Nat → Option (List Ev × List Nat)
  | [], j, o => some (j, o)
  | r :: rs, j, o =>
    match decodeDiskEntry codec r.payload with
    | some (.journalAppend ev) => foldDiskEntries codec rs (j ++ [ev]) o
    | some (.outboxExpose pos) => foldDiskEntries codec rs j (o ++ [pos])
    | none => none

/-- Decode a committed `List Record` into `(journal, outbox)`. -/
def decodeDurableRecords {Ev : Type} (codec : EventWireCodec Ev)
    (rs : List Record) : Option (List Ev × List Nat) :=
  foldDiskEntries codec rs [] []

theorem foldDiskEntries_snoc {Ev : Type} (codec : EventWireCodec Ev) :
    ∀ (rs : List Record) (r : Record) (j : List Ev) (o : List Nat) (j' : List Ev) (o' : List Nat),
      foldDiskEntries codec rs j o = some (j', o') →
      foldDiskEntries codec (rs ++ [r]) j o =
        match decodeDiskEntry codec r.payload with
        | some (.journalAppend ev) => some (j' ++ [ev], o')
        | some (.outboxExpose pos) => some (j', o' ++ [pos])
        | none => none
  | [], r, _, _, _, _, h => by
    simp only [foldDiskEntries, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp only [List.nil_append, foldDiskEntries]
    cases decodeDiskEntry codec r.payload with
    | none => rfl
    | some entry => cases entry <;> rfl
  | x :: xs, r, j, o, j', o', h => by
    simp only [foldDiskEntries] at h
    cases hd : decodeDiskEntry codec x.payload with
    | none => rw [hd] at h; cases h
    | some entry =>
      rw [hd] at h
      cases entry with
      | journalAppend ev =>
        simp only [List.cons_append, foldDiskEntries, hd]
        exact foldDiskEntries_snoc codec xs r (j ++ [ev]) o j' o' h
      | outboxExpose pos =>
        simp only [List.cons_append, foldDiskEntries, hd]
        exact foldDiskEntries_snoc codec xs r j (o ++ [pos]) j' o' h

/-- Construct a well-formed, hash-chained `Vault.Log.Record` following `prev`. -/
def mkChainedRecord (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) : Record :=
  let d := dig Hb payload
  ⟨⟨prev, prev, d, d⟩, payload⟩

theorem mkChainedRecord_wf (Hb : Bytes → Bytes) {prev : Nat} (hp : prev < bound)
    {payload : Bytes} (hlen : payload.length < 256 ^ 4) :
    (mkChainedRecord Hb prev payload).WF Hb :=
  ⟨hp, hp, dig_lt Hb payload, rfl, hlen⟩

theorem mkChainedRecord_prevHash (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) :
    (mkChainedRecord Hb prev payload).receipt.prevHash = prev := by
  rfl

theorem mkChainedRecord_payload (Hb : Bytes → Bytes) (prev : Nat) (payload : Bytes) :
    (mkChainedRecord Hb prev payload).payload = payload := by
  rfl

/-- Append raw frame bytes into fixed-capacity physical disk segments via `SegmentLog.split`. -/
def appendSegmentedBytes (segCap : Nat) (hCap : 0 < segCap) (segments : List Bytes) (bs : Bytes) :
    List Bytes :=
  split segCap hCap (segments.flatten ++ bs)

theorem appendSegmentedBytes_flatten (segCap : Nat) (hCap : 0 < segCap)
    (segments : List Bytes) (bs : Bytes) :
    (appendSegmentedBytes segCap hCap segments bs).flatten = segments.flatten ++ bs :=
  split_join segCap hCap (segments.flatten ++ bs)

/-- **Segment Boundary Rotation**: pushing total bytes past `segCap` rotates into `≥ 2` segments. -/
theorem segmented_append_rotates_across_boundary (segCap : Nat) (hCap : 0 < segCap)
    (segments : List Bytes) (bs : Bytes) (hCross : segCap < (segments.flatten ++ bs).length) :
    2 ≤ (appendSegmentedBytes segCap hCap segments bs).length ∧
    ∃ seg0 rest,
      appendSegmentedBytes segCap hCap segments bs = seg0 :: rest ∧
      seg0.length = segCap ∧ rest ≠ [] := by
  unfold appendSegmentedBytes
  generalize segments.flatten ++ bs = total at hCross
  rw [split]
  have hne : total.isEmpty = false := by
    cases h : total.isEmpty with
    | false => rfl
    | true => rw [List.isEmpty_iff.mp h] at hCross; simp at hCross
  simp only [hne, Bool.false_eq_true, ↓reduceIte]; rw [split]
  have hrem_pos : 0 < (total.drop segCap).length := by simp only [List.length_drop]; omega
  have hrem_ne : (total.drop segCap).isEmpty = false := by
    cases h : (total.drop segCap).isEmpty with
    | false => rfl
    | true => rw [List.isEmpty_iff.mp h] at hrem_pos; simp at hrem_pos
  simp only [hrem_ne, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by simp, total.take segCap, _, rfl, ?_, by simp⟩
  simp only [List.length_take]; omega

/-- Any empty or `parseOne`-rejected trailing bytes are discarded cleanly by `parseFrom`. -/
theorem parseFrom_committed_with_rejected_tail (Hb : Bytes → Bytes) (rs : List Record)
    (hl : Linked Hb genesisSentinel rs) (hwf : ∀ r ∈ rs, r.WF Hb) (tail : Bytes)
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d) :
    (parseFrom Hb genesisSentinel (encodeAll Hb rs ++ tail)).1 = rs := by
  rw [Obend.Vault.Log.parseFrom_encodeAll Hb rs genesisSentinel hl hwf tail]
  rcases hRej with rfl | ⟨d, hd⟩
  · simp [Obend.Vault.Log.parseFrom_nil]
  · by_cases hne : tail = []
    · subst hne; simp [Obend.Vault.Log.parseFrom_nil]
    · rw [Obend.Vault.Log.parseFrom_error Hb hne hd]; simp

/-- **Torn-Frame Crash Recovery**: any torn in-flight frame `k < length` is truncated to `rs`. -/
theorem parseFrom_committed_with_torn_frame (Hb : Bytes → Bytes) (segCap : Nat) (hCap : 0 < segCap)
    (rs : List Record) (hl : Linked Hb genesisSentinel rs) (hwf : ∀ r ∈ rs, r.WF Hb)
    (r_inflight : Record) (hwf_in : r_inflight.WF Hb)
    (k : Nat) (hk : k < (encodeRecord Hb r_inflight).length) :
    let crashedSegs := split segCap hCap (encodeAll Hb rs ++ (encodeRecord Hb r_inflight).take k)
    (parseFrom Hb genesisSentinel crashedSegs.flatten).1 = rs := by
  dsimp only; rw [split_join]
  apply parseFrom_committed_with_rejected_tail Hb rs hl hwf
  by_cases hk0 : k = 0
  · subst hk0; exact .inl (by simp)
  · exact .inr ⟨.torn, Obend.Vault.Log.parseOne_torn Hb hwf_in
      (List.take_append_drop k (encodeRecord Hb r_inflight))
      (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩

/-- Necessity witness: a 5-byte torn `OBL1` header is non-empty garbage flagged as `some .torn`. -/
theorem torn_header_flagged_as_torn (Hb : Bytes → Bytes) :
    let r := mkChainedRecord Hb genesisSentinel [42]
    let tornBytes := (encodeRecord Hb r).take 5
    tornBytes ≠ [] ∧ parseFrom Hb genesisSentinel tornBytes = ([], tornBytes, some .torn) := by
  dsimp only
  have hwf : (mkChainedRecord Hb genesisSentinel [42]).WF Hb :=
    mkChainedRecord_wf Hb (by decide) (by decide)
  have hne : ((encodeRecord Hb (mkChainedRecord Hb genesisSentinel [42])).take 5) ≠ [] := by
    intro h; have := congrArg List.length h
    rw [List.length_take, Obend.Vault.Log.encodeRecord_length] at this
    simp only [mkChainedRecord, List.length_singleton, List.length_nil] at this; omega
  have htorn : parseOne Hb (some genesisSentinel)
      ((encodeRecord Hb (mkChainedRecord Hb genesisSentinel [42])).take 5) = .error .torn :=
    Obend.Vault.Log.parseOne_torn Hb hwf (List.take_append_drop 5 _) (by
      rw [Ne, List.drop_eq_nil_iff, Obend.Vault.Log.encodeRecord_length]
      simp only [mkChainedRecord, List.length_singleton]; omega)
  exact ⟨hne, Obend.Vault.Log.parseFrom_error Hb hne htorn⟩

/-! ### Segmented Durable Host & Forward Simulation to `Obend.Run.Durable` -/

section Simulation
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {i₀ : Ix}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]

/-- Physical host state backed by `Vault.SegmentLog` fixed-width disk blocks plus volatile memory. -/
structure SegmentedDState (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type)
    (P Cand Fact Ob : Type) (i₀ : Ix) where
  segCap : Nat
  segCap_pos : 0 < segCap
  segments : List Bytes
  mem : Option (JCfg L S Hole A P Cand Fact Ob i₀)

/-- Initial segmented host state at block width `segCap`. -/
def SegmentedDState.init (L : Ledger ι W Tok) (segCap : Nat) (hCap : 0 < segCap)
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) : SegmentedDState L S Hole A P Cand Fact Ob i₀ :=
  ⟨segCap, hCap, [], some J₀⟩

/-- Default 64 KiB `SegmentLog.capacity` initial state. -/
def SegmentedDState.initDefault (L : Ledger ι W Tok) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ :=
  SegmentedDState.init L capacity (by decide) J₀

/-- Segmented host events, extending `.crash` with torn/unfsynced trailing frames on disk. -/
inductive SegmentedHEvent (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type)
    (P Cred Cand Fact : Type) where
  | submit (ev : JEv L S Hole A P Cred Cand Fact)
  | expose (n : Nat)
  | tornCrash (r_inflight : Record) (k : Nat)
  | cleanCrash
  | recover

/-- Map a physical `SegmentedHEvent` to its abstract `Obend.Run.Durable.HEvent` counterpart. -/
def SegmentedHEvent.toAbstract {L : Ledger ι W Tok} :
    SegmentedHEvent L S Hole A P Cred Cand Fact → HEvent L S Hole A P Cred Cand Fact
  | .submit ev => .submit ev
  | .expose n => .expose n
  | .tornCrash _ _ | .cleanCrash => .crash
  | .recover => .recover

/-- Refusals of the segmented disk host. -/
inductive SegmentedRefusal (ι Tok : Type) (S : Sig Ix) (Hole : Ix → Type) (P Cand Fact : Type) where
  | host (r : HRefusal ι Tok S Hole P Cand Fact)
  | frameTooLarge
  | dirtyTailNeedsRecovery
  | invalidTornSpec

/-- Decode `(journal, outbox)` from the physical segment list of `disk`. -/
def recoverJournalAndOutbox {L : Ledger ι W Tok} (Hb : Bytes → Bytes)
    (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀) :
    Option (List (JEv L S Hole A P Cred Cand Fact) × List Nat) :=
  decodeDurableRecords codec (parseFrom Hb genesisSentinel disk.segments.flatten).1

/-- One physical step of the segmented durable host (submit/rotate, expose, crash/tear, recover). -/
def segmentedStep (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀)
    (hev : SegmentedHEvent L S Hole A P Cred Cand Fact) :
    Except (SegmentedRefusal ι Tok S Hole P Cand Fact) (SegmentedDState L S Hole A P Cand Fact Ob i₀) :=
  let parsed := parseFrom Hb genesisSentinel disk.segments.flatten
  let rs := parsed.1
  let tail := parsed.2.1
  match hev with
  | .submit ev =>
    if !tail.isEmpty then .error .dirtyTailNeedsRecovery else
    match disk.mem with
    | none => .error (.host .down)
    | some J =>
      let payload := encodeDiskEntry codec (.journalAppend ev)
      if payload.length < 256 ^ 4 then
        match jrun L base sp au k J ev with
        | .ok J' =>
          let newRec := mkChainedRecord Hb (lastHash Hb genesisSentinel rs) payload
          let segs' := appendSegmentedBytes disk.segCap disk.segCap_pos disk.segments (encodeRecord Hb newRec)
          .ok ⟨disk.segCap, disk.segCap_pos, segs', some J'⟩
        | .error r => .error (.host (.joint r))
      else .error .frameTooLarge
  | .expose n =>
    if !tail.isEmpty then .error .dirtyTailNeedsRecovery else
    match decodeDurableRecords codec rs with
    | none => .error (.host .corrupt)
    | some (journal, outbox) =>
      match journal[n]? with
      | some (.dispatch _ _) =>
        if n ∈ outbox then .error (.host (.exposed n)) else
        let payload := encodeDiskEntry codec (.outboxExpose n)
        if payload.length < 256 ^ 4 then
          let newRec := mkChainedRecord Hb (lastHash Hb genesisSentinel rs) payload
          let segs' := appendSegmentedBytes disk.segCap disk.segCap_pos disk.segments (encodeRecord Hb newRec)
          .ok ⟨disk.segCap, disk.segCap_pos, segs', disk.mem⟩
        else .error .frameTooLarge
      | _ => .error (.host (.notDispatch n))
  | .cleanCrash => .ok ⟨disk.segCap, disk.segCap_pos, disk.segments, none⟩
  | .tornCrash r_in bytesWritten =>
    if r_in.receipt.prevHash < bound ∧ r_in.receipt.oldCommit < bound ∧
        r_in.receipt.newCommit < bound ∧ r_in.receipt.effectsHash = dig Hb r_in.payload ∧
        r_in.payload.length < 256 ^ 4 ∧ bytesWritten < (encodeRecord Hb r_in).length then
      let crashedSegs := split disk.segCap disk.segCap_pos
        (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten)
      .ok ⟨disk.segCap, disk.segCap_pos, crashedSegs, none⟩
    else .error .invalidTornSpec
  | .recover =>
    match disk.mem with
    | some _ => .error (.host .up)
    | none =>
      match decodeDurableRecords codec rs with
      | none => .error (.host .corrupt)
      | some (journal, _) =>
        match replay L base sp au k J₀ journal with
        | some J => .ok ⟨disk.segCap, disk.segCap_pos, split disk.segCap disk.segCap_pos (encodeAll Hb rs), some J⟩
        | none => .error (.host .corrupt)

/-- Forward simulation relation coupling `SegmentedDState` on disk to `Obend.Run.Durable.DState`. -/
def SegmentedSimInv (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (disk : SegmentedDState L S Hole A P Cand Fact Ob i₀)
    (s : DState L S Hole A P Cred Cand Fact Ob i₀) : Prop :=
  ∃ committedRecords : List Record,
    Linked Hb genesisSentinel committedRecords ∧
    (∀ r ∈ committedRecords, r.WF Hb) ∧
    (∃ tail : Bytes,
      disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb committedRecords ++ tail) ∧
      (tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel committedRecords)) tail = .error d) ∧
      (disk.mem.isSome = true → tail = [])) ∧
    decodeDurableRecords codec committedRecords = some (s.journal, s.outbox) ∧
    disk.mem = s.mem ∧ HReachable L base sp au k J₀ s

theorem segmentedSimInv_init (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedSimInv L base sp au k Hb codec J₀ (SegmentedDState.init L segCap hCap J₀) (DState.init L J₀) :=
  ⟨[], trivial, by simp, ⟨[], by simp [SegmentedDState.init, split, encodeAll], .inl rfl, fun _ => rfl⟩,
    rfl, by rfl, .init⟩

omit [DecidableEq ι] [DecidableEq Ix] [(i : Ix) → DecidableEq (Hole i)]
  [DecidableEq Tok] [DecidableEq Cand] [DecidableEq ((i : Ix) × S.Op i)] in
theorem segmented_parseFrom_rs {L : Ledger ι W Tok}
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀} {rs : List Record} {tail : Bytes}
    {journal : List (JEv L S Hole A P Cred Cand Fact)} {outbox : List Nat}
    (hLinked : Linked Hb genesisSentinel rs) (hWf : ∀ r ∈ rs, r.WF Hb)
    (hSegs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ tail))
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d)
    (hDec : decodeDurableRecords codec rs = some (journal, outbox)) :
    (parseFrom Hb genesisSentinel disk.segments.flatten).1 = rs ∧
    recoverJournalAndOutbox Hb codec disk = some (journal, outbox) := by
  have hp1 : (parseFrom Hb genesisSentinel disk.segments.flatten).1 = rs := by
    rw [hSegs, split_join]; exact parseFrom_committed_with_rejected_tail Hb rs hLinked hWf tail hRej
  exact ⟨hp1, by unfold recoverJournalAndOutbox; rw [hp1]; exact hDec⟩

omit [DecidableEq ι] [DecidableEq Ix] [(i : Ix) → DecidableEq (Hole i)]
  [DecidableEq Tok] [DecidableEq Cand] [DecidableEq ((i : Ix) × S.Op i)] in
theorem segmented_clean_tail_flatten {L : Ledger ι W Tok} (Hb : Bytes → Bytes)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀} {rs : List Record} {tail : Bytes}
    (hLinked : Linked Hb genesisSentinel rs) (hWf : ∀ r ∈ rs, r.WF Hb)
    (hSegs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ tail))
    (hRej : tail = [] ∨ ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs)) tail = .error d)
    (hEmpty : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty = true) :
    disk.segments.flatten = encodeAll Hb rs := by
  have hflat : disk.segments.flatten = encodeAll Hb rs ++ tail := by rw [hSegs, split_join]
  rw [hflat, Obend.Vault.Log.parseFrom_encodeAll Hb rs genesisSentinel hLinked hWf tail] at hEmpty
  rcases hRej with rfl | ⟨d, hd⟩
  · simpa using hflat
  · by_cases hne : tail = []
    · subst hne; simpa using hflat
    · rw [Obend.Vault.Log.parseFrom_error Hb hne hd] at hEmpty
      exact absurd (List.isEmpty_iff.mp hEmpty) hne

/-- **Forward Simulation Step**: every accepted `segmentedStep` refines `Durable.hstep`. -/
theorem segmentedStep_refines_durable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk disk' : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (hev : SegmentedHEvent L S Hole A P Cred Cand Fact)
    (hSim : SegmentedSimInv L base sp au k Hb codec J₀ disk s)
    (hStep : segmentedStep L base sp au k Hb codec J₀ disk hev = .ok disk') :
    ∃ s', hstep L base sp au k J₀ s hev.toAbstract = .ok s' ∧
      SegmentedSimInv L base sp au k Hb codec J₀ disk' s' := by
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, hClean⟩, hDec, hMem, hReach⟩
  have ⟨hp_rs, _⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  cases hev with
  | submit ev =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases htail_emp : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty with
    | false => simp [htail_emp] at hStep
    | true =>
      simp only [htail_emp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      have hflat_clean := segmented_clean_tail_flatten Hb hLinked hWf hSegs hRej htail_emp
      cases hmem : disk.mem with
      | none => rw [hmem] at hStep; cases hStep
      | some J =>
        rw [hmem] at hStep; dsimp only at hStep; split at hStep
        · rename_i hlen
          cases hj : jrun L base sp au k J ev with
          | error r => rw [hj] at hStep; cases hStep
          | ok J' =>
            rw [hj] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep
            have hs_mem : s.mem = some J := hMem.symm.trans hmem
            have hhstep : hstep L base sp au k J₀ s (.submit ev) =
                .ok ⟨s.journal ++ [ev], s.outbox, some J'⟩ := by unfold hstep; simp [hs_mem, hj]
            refine ⟨⟨s.journal ++ [ev], s.outbox, some J'⟩, hhstep, ?_⟩
            let prev := lastHash Hb genesisSentinel rs
            let payload := encodeDiskEntry codec (.journalAppend ev)
            let newRec := mkChainedRecord Hb prev payload
            have hrec_wf : newRec.WF Hb :=
              mkChainedRecord_wf Hb (Obend.Vault.Log.lastHash_lt Hb (by decide) rs) hlen
            refine ⟨rs ++ [newRec],
              (Obend.Vault.Log.Linked_append Hb genesisSentinel rs [newRec]).mpr ⟨hLinked, rfl, trivial⟩,
              fun r hr => ?_, ⟨[], ?_, .inl rfl, fun _ => rfl⟩, ?_, rfl, .step (.submit ev) hReach hhstep⟩
            · rcases List.mem_append.mp hr with hr | hr
              · exact hWf r hr
              · simp only [List.mem_singleton] at hr; subst hr; exact hrec_wf
            · simp only [appendSegmentedBytes, hflat_clean, Obend.Vault.Log.encodeAll_append,
                encodeAll, List.append_nil]; rfl
            · unfold decodeDurableRecords
              rw [foldDiskEntries_snoc codec rs newRec [] [] s.journal s.outbox hDec]
              simp [newRec, mkChainedRecord, payload]
        · cases hStep
  | expose n =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases htail_emp : (parseFrom Hb genesisSentinel disk.segments.flatten).2.1.isEmpty with
    | false => simp [htail_emp] at hStep
    | true =>
      simp only [htail_emp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      have hflat_clean := segmented_clean_tail_flatten Hb hLinked hWf hSegs hRej htail_emp
      rw [hDec] at hStep; dsimp only at hStep; split at hStep
      · rename_i i o hjn
        split at hStep
        · cases hStep
        · rename_i hnot_out
          split at hStep
          · rename_i hlen
            simp only [Except.ok.injEq] at hStep; subst hStep
            have hhstep : hstep L base sp au k J₀ s (.expose n) =
                .ok ⟨s.journal, s.outbox ++ [n], disk.mem⟩ := by
              unfold hstep; simp [hjn, hnot_out, hMem]
            refine ⟨⟨s.journal, s.outbox ++ [n], disk.mem⟩, hhstep, ?_⟩
            let prev := lastHash Hb genesisSentinel rs
            let payload := encodeDiskEntry codec (.outboxExpose n)
            let newRec := mkChainedRecord Hb prev payload
            have hrec_wf : newRec.WF Hb :=
              mkChainedRecord_wf Hb (Obend.Vault.Log.lastHash_lt Hb (by decide) rs) hlen
            refine ⟨rs ++ [newRec],
              (Obend.Vault.Log.Linked_append Hb genesisSentinel rs [newRec]).mpr ⟨hLinked, rfl, trivial⟩,
              fun r hr => ?_, ⟨[], ?_, .inl rfl, fun _ => rfl⟩, ?_, rfl, .step (.expose n) hReach hhstep⟩
            · rcases List.mem_append.mp hr with hr | hr
              · exact hWf r hr
              · simp only [List.mem_singleton] at hr; subst hr; exact hrec_wf
            · simp only [appendSegmentedBytes, hflat_clean, Obend.Vault.Log.encodeAll_append,
                encodeAll, List.append_nil]; rfl
            · unfold decodeDurableRecords
              rw [foldDiskEntries_snoc codec rs newRec [] [] s.journal s.outbox hDec]
              simp [newRec, mkChainedRecord, payload]
          · cases hStep
      · cases hStep
  | cleanCrash =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract, Except.ok.injEq] at hStep ⊢; subst hStep
    have hhstep : hstep L base sp au k J₀ s .crash = .ok ⟨s.journal, s.outbox, none⟩ := rfl
    exact ⟨⟨s.journal, s.outbox, none⟩, hhstep,
      ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, fun h => by simp at h⟩,
        hDec, rfl, .step .crash hReach hhstep⟩⟩
  | tornCrash r_in bytesWritten =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    split at hStep
    · rename_i hspec
      simp only [Except.ok.injEq] at hStep; subst hStep
      obtain ⟨h0, h1, h2, h3, h4, hk_lt⟩ := hspec
      have hwf_in : r_in.WF Hb := ⟨h0, h1, h2, h3, h4⟩
      have hhstep : hstep L base sp au k J₀ s .crash = .ok ⟨s.journal, s.outbox, none⟩ := rfl
      have hrej' : (encodeRecord Hb r_in).take bytesWritten = [] ∨
          ∃ d, parseOne Hb (some (lastHash Hb genesisSentinel rs))
            ((encodeRecord Hb r_in).take bytesWritten) = .error d := by
        by_cases hb0 : bytesWritten = 0
        · subst hb0; exact .inl (by simp)
        · exact .inr ⟨.torn, Obend.Vault.Log.parseOne_torn Hb hwf_in
            (List.take_append_drop bytesWritten _) (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩
      exact ⟨⟨s.journal, s.outbox, none⟩, hhstep,
        ⟨rs, hLinked, hWf, ⟨(encodeRecord Hb r_in).take bytesWritten, rfl, hrej', fun h => by simp at h⟩,
          hDec, rfl, .step .crash hReach hhstep⟩⟩
    · cases hStep
  | recover =>
    simp only [segmentedStep, SegmentedHEvent.toAbstract] at hStep ⊢; rw [hp_rs] at hStep
    cases hmem : disk.mem with
    | some _ => rw [hmem] at hStep; cases hStep
    | none =>
      rw [hmem, hDec] at hStep; dsimp only at hStep
      cases hrep : replay L base sp au k J₀ s.journal with
      | none => rw [hrep] at hStep; cases hStep
      | some J =>
        rw [hrep] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep
        have hs_mem : s.mem = none := hMem.symm.trans hmem
        have hhstep : hstep L base sp au k J₀ s .recover = .ok ⟨s.journal, s.outbox, some J⟩ := by
          unfold hstep; simp [hs_mem, hrep]
        exact ⟨⟨s.journal, s.outbox, some J⟩, hhstep,
          ⟨rs, hLinked, hWf, ⟨[], by simp, .inl rfl, fun _ => rfl⟩,
            hDec, rfl, .step .recover hReach hhstep⟩⟩

/-- Multi-step segmented trace execution (keeping state on refused steps). -/
def runSegmentedTrace (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ →
    List (SegmentedHEvent L S Hole A P Cred Cand Fact) → SegmentedDState L S Hole A P Cand Fact Ob i₀
  | disk, [] => disk
  | disk, e :: es =>
    match segmentedStep L base sp au k Hb codec J₀ disk e with
    | .ok disk' => runSegmentedTrace L base sp au k Hb codec J₀ disk' es
    | .error _ => runSegmentedTrace L base sp au k Hb codec J₀ disk es

/-- Reachable physical segmented states from `SegmentedDState.init`. -/
inductive SegmentedReachable (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    SegmentedDState L S Hole A P Cand Fact Ob i₀ → Prop
  | init : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ (SegmentedDState.init L segCap hCap J₀)
  | step {d d' : SegmentedDState L S Hole A P Cand Fact Ob i₀}
      (hev : SegmentedHEvent L S Hole A P Cred Cand Fact) :
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀ d →
      segmentedStep L base sp au k Hb codec J₀ d hev = .ok d' →
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀ d'

theorem runSegmentedTrace_reachable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ disk) :
    ∀ (es : List (SegmentedHEvent L S Hole A P Cred Cand Fact)),
      SegmentedReachable L base sp au k Hb codec segCap hCap J₀
        (runSegmentedTrace L base sp au k Hb codec J₀ disk es)
  | [] => hReach
  | e :: es => by
    simp only [runSegmentedTrace]
    cases hs : segmentedStep L base sp au k Hb codec J₀ disk e with
    | ok disk' => exact runSegmentedTrace_reachable L base sp au k Hb codec segCap hCap J₀ (.step e hReach hs) es
    | error _ => exact runSegmentedTrace_reachable L base sp au k Hb codec segCap hCap J₀ hReach es

theorem segmentedReachable_simulates_durable
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap) (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap J₀ disk) :
    ∃ s, SegmentedSimInv L base sp au k Hb codec J₀ disk s := by
  induction hReach with
  | init => exact ⟨DState.init L J₀, segmentedSimInv_init L base sp au k Hb codec segCap hCap J₀⟩
  | step hev _ hs ih =>
    obtain ⟨s, hSim⟩ := ih
    obtain ⟨s', _, hSim'⟩ := segmentedStep_refines_durable L base sp au k Hb codec J₀ hev hSim hs
    exact ⟨s', hSim'⟩

/-- **Torn-Tail Crash Recovery Idempotence**: `.tornCrash` followed by `.recover` restores `disk`. -/
theorem segmented_torn_crash_recover_idempotent
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    {s : DState L S Hole A P Cred Cand Fact Ob i₀} {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (hSim : SegmentedSimInv L base sp au k Hb codec J₀ disk s) (hUp : disk.mem = some J)
    (r_in : Record) (hwf_in : r_in.WF Hb)
    (bytesWritten : Nat) (hk : bytesWritten < (encodeRecord Hb r_in).length) :
    ∃ crashed recovered,
      segmentedStep L base sp au k Hb codec J₀ disk (.tornCrash r_in bytesWritten) = .ok crashed ∧
      segmentedStep L base sp au k Hb codec J₀ crashed .recover = .ok recovered ∧
      recovered = disk ∧
      recoverJournalAndOutbox Hb codec recovered = some (s.journal, s.outbox) := by
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, hClean⟩, hDec, hMem, hReach⟩
  have ⟨hp_rs, hrec_jo⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  obtain ⟨h0, h1, h2, h3, h4⟩ := hwf_in
  have hcrash : segmentedStep L base sp au k Hb codec J₀ disk (.tornCrash r_in bytesWritten) =
      .ok ⟨disk.segCap, disk.segCap_pos,
        split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten),
        none⟩ := by
    unfold segmentedStep; dsimp only; rw [hp_rs]
    split
    · rfl
    · rename_i hneg; exact absurd ⟨h0, h1, h2, h3, h4, hk⟩ hneg
  obtain ⟨J', hrep, _, hm_inv⟩ := (hreach_inv hReach).replays
  have hs_mem : s.mem = some J := hMem.symm.trans hUp
  have hJ_eq : J' = J := by
    rcases hm_inv with hm_inv | hm_inv <;> rw [hm_inv] at hs_mem <;> cases hs_mem; rfl
  subst hJ_eq
  have htail_nil : tail = [] := hClean (by simp [hUp])
  subst htail_nil
  have hdisk_segs : disk.segments = split disk.segCap disk.segCap_pos (encodeAll Hb rs) := by
    simpa using hSegs
  have hrec : segmentedStep L base sp au k Hb codec J₀
      ⟨disk.segCap, disk.segCap_pos,
        split disk.segCap disk.segCap_pos (encodeAll Hb rs ++ (encodeRecord Hb r_in).take bytesWritten),
        none⟩ .recover = .ok disk := by
    unfold segmentedStep; dsimp only
    rw [parseFrom_committed_with_torn_frame Hb disk.segCap disk.segCap_pos
      rs hLinked hWf r_in ⟨h0, h1, h2, h3, h4⟩ bytesWritten hk, hDec]
    dsimp only; rw [hrep]
    cases disk with
    | mk sc scp segs m => dsimp only at hUp hdisk_segs ⊢; subst hUp; rw [← hdisk_segs]
  exact ⟨_, disk, hcrash, hrec, rfl, hrec_jo⟩

/-- **Keystone Chasm 3A Theorem (`segmented_exposed_once`)**: across arbitrary multi-segment
    rotations and torn-tail crash-restart cycles, each linear token `t` is exposed at most once. -/
theorem segmented_exposed_once
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (Hb : Bytes → Bytes) (codec : EventWireCodec (JEv L S Hole A P Cred Cand Fact))
    (segCap : Nat) (hCap : 0 < segCap)
    {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
    {stored₀ : ι → (j : Ix) → Hole j → Option Cand}
    (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    {disk : SegmentedDState L S Hole A P Cand Fact Ob i₀}
    (hReach : SegmentedReachable L base sp au k Hb codec segCap hCap (JCfg.init L d₀ O stored₀) disk)
    {journal : List (JEv L S Hole A P Cred Cand Fact)} {outbox : List Nat}
    (hDisk : recoverJournalAndOutbox Hb codec disk = some (journal, outbox))
    {n m : Nat} (hn : n ∈ outbox) (hm : m ∈ outbox)
    {i j : ι} {o o' : Σ i, S.Op i} {t : Tok}
    (hio : journal[n]? = some (.dispatch i o)) (hjo : journal[m]? = some (.dispatch j o'))
    (ht : (sp i).consumes o.2 = some t) (ht' : (sp j).consumes o'.2 = some t) :
    n = m ∧ i = j := by
  obtain ⟨s, hSim⟩ := segmentedReachable_simulates_durable L base sp au k Hb codec segCap hCap
    (JCfg.init L d₀ O stored₀) hReach
  rcases hSim with ⟨rs, hLinked, hWf, ⟨tail, hSegs, hRej, _⟩, hDec, _, hAbsReach⟩
  have ⟨_, hrec⟩ := segmented_parseFrom_rs Hb codec hLinked hWf hSegs hRej hDec
  rw [hrec] at hDisk; simp only [Option.some.injEq, Prod.mk.injEq] at hDisk
  obtain ⟨rfl, rfl⟩ := hDisk
  exact exposed_once hs₀ hg₀ hAbsReach hn hm hio hjo ht ht'

end Simulation

/-! ## Part B.2 — Linear Capability-Carrying Plans (`TVal`, `DataWire`, `CapTable`, `CapSealFrame`) -/

/-- Live runtime transferable value (`Core.Data` extended with linear `.cap slotId custodyId`). -/
inductive TVal where
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | record (fields : List (String × TVal))
  | variant (tag : String) (payload : TVal)
  | cap (slotId : Nat) (custodyId : Nat)
  deriving Repr

mutual
def tvalBeq : TVal → TVal → Bool
  | .natural a, .natural b => a == b
  | .boolean a, .boolean b => a == b
  | .label a, .label b => a == b
  | .record fa, .record fb => tvalFieldsBeq fa fb
  | .variant ta pa, .variant tb pb => ta == tb && tvalBeq pa pb
  | .cap sa ca, .cap sb cb => sa == sb && ca == cb
  | _, _ => false

def tvalFieldsBeq : List (String × TVal) → List (String × TVal) → Bool
  | [], [] => true
  | (ka, va) :: ra, (kb, vb) :: rb => ka == kb && tvalBeq va vb && tvalFieldsBeq ra rb
  | _, _ => false
end

instance : BEq TVal := ⟨tvalBeq⟩

mutual
def tvalOfData : Data → TVal
  | .natural n => .natural n
  | .boolean b => .boolean b
  | .label s => .label s
  | .record fs => .record (tvalOfDataFields fs)
  | .variant tag p => .variant tag (tvalOfData p)

def tvalOfDataFields : List (String × Data) → List (String × TVal)
  | [] => []
  | (k, v) :: rest => (k, tvalOfData v) :: tvalOfDataFields rest
end

/-- Embed pure `Obend.Core.Data.Data` into `TVal`. -/
def TVal.ofData (d : Data) : TVal := tvalOfData d

mutual
def tvalCapSlots : TVal → List Nat
  | .natural _ | .boolean _ | .label _ => []
  | .cap slotId _ => [slotId]
  | .variant _ p => tvalCapSlots p
  | .record fs => tvalCapSlotsFields fs

def tvalCapSlotsFields : List (String × TVal) → List Nat
  | [] => []
  | (_, v) :: rest => tvalCapSlots v ++ tvalCapSlotsFields rest
end

/-- Collect all capability `slotId`s referenced in `v` in left-to-right order. -/
def TVal.capSlots (v : TVal) : List Nat := tvalCapSlots v

mutual
def tvalConforms : TVal → Ty → Bool
  | .natural _, .natural | .boolean _, .boolean | .label _, .label => true
  | .cap _ cid, .custody expectedId => cid == expectedId
  | .record fields, row =>
    fields.length == (Obend.Core.Data.rowNames row).length &&
    (fields.map Prod.fst).eraseDups.length == fields.length &&
    tvalConformsFields fields row
  | .variant tag payload, .variant row =>
    match Obend.Core.Data.rowMember row tag with
    | some member => tvalConforms payload member
    | none => false
  | _, _ => false

def tvalConformsFields : List (String × TVal) → Ty → Bool
  | [], _ => true
  | (name, val) :: rest, row =>
    (match Obend.Core.Data.rowMember row name with
      | some member => tvalConforms val member
      | none => false) && tvalConformsFields rest row
end

/-- Type conformance of a `TVal` against a `Ty.isTransferable` type. -/
def TVal.conforms (v : TVal) (ty : Ty) : Bool := tvalConforms v ty

/-- Dehydrated wire skeleton: capability leaves replaced by descriptor indices into `CapTable`. -/
inductive DataWire where
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | record (fields : List (String × DataWire))
  | variant (tag : String) (payload : DataWire)
  | sealedCap (capIndex : Nat) (custodyId : Nat)
  deriving Repr

mutual
def dataWireBeq : DataWire → DataWire → Bool
  | .natural a, .natural b => a == b
  | .boolean a, .boolean b => a == b
  | .label a, .label b => a == b
  | .record fa, .record fb => dataWireFieldsBeq fa fb
  | .variant ta pa, .variant tb pb => ta == tb && dataWireBeq pa pb
  | .sealedCap ia ca, .sealedCap ib cb => ia == ib && ca == cb
  | _, _ => false

def dataWireFieldsBeq : List (String × DataWire) → List (String × DataWire) → Bool
  | [], [] => true
  | (ka, va) :: ra, (kb, vb) :: rb => ka == kb && dataWireBeq va vb && dataWireFieldsBeq ra rb
  | _, _ => false
end

instance : BEq DataWire := ⟨dataWireBeq⟩

mutual
def dataWireToData : DataWire → Data
  | .natural n => .variant "wire.nat" (.natural n)
  | .boolean b => .variant "wire.bool" (.boolean b)
  | .label s => .variant "wire.label" (.label s)
  | .record fs => .variant "wire.rec" (.record (dataWireFieldsToData fs))
  | .variant tag p => .variant "wire.var" (.record [("tag", .label tag), ("payload", dataWireToData p)])
  | .sealedCap idx cid => .variant "wire.cap" (.record [("idx", .natural idx), ("cid", .natural cid)])

def dataWireFieldsToData : List (String × DataWire) → List (String × Data)
  | [] => []
  | (k, v) :: rest => (k, dataWireToData v) :: dataWireFieldsToData rest
end

/-- Lower `DataWire` bijectively to pure first-order `Obend.Core.Data.Data`. -/
def DataWire.toData (w : DataWire) : Data := dataWireToData w

mutual
def dataWireOfData? : Data → Option DataWire
  | .variant "wire.nat" (.natural n) => some (.natural n)
  | .variant "wire.bool" (.boolean b) => some (.boolean b)
  | .variant "wire.label" (.label s) => some (.label s)
  | .variant "wire.rec" (.record fs) => (dataWireFieldsOfData? fs).map .record
  | .variant "wire.var" (.record [("tag", .label tag), ("payload", p)]) =>
    (dataWireOfData? p).map (.variant tag)
  | .variant "wire.cap" (.record [("idx", .natural idx), ("cid", .natural cid)]) =>
    some (.sealedCap idx cid)
  | _ => none

def dataWireFieldsOfData? : List (String × Data) → Option (List (String × DataWire))
  | [] => some []
  | (k, v) :: rest =>
    match dataWireOfData? v, dataWireFieldsOfData? rest with
    | some wv, some wrest => some ((k, wv) :: wrest)
    | _, _ => none
end

/-- Parse pure `Obend.Core.Data.Data` back into `DataWire`. -/
def DataWire.ofData? (d : Data) : Option DataWire := dataWireOfData? d

mutual
theorem dataWireOfData_toData : ∀ (w : DataWire), dataWireOfData? (dataWireToData w) = some w
  | .natural _ | .boolean _ | .label _ | .sealedCap _ _ => rfl
  | .record fs => by simp [dataWireToData, dataWireOfData?, dataWireFieldsOfData_toData fs]
  | .variant tag p => by simp [dataWireToData, dataWireOfData?, dataWireOfData_toData p]

theorem dataWireFieldsOfData_toData :
    ∀ (fs : List (String × DataWire)), dataWireFieldsOfData? (dataWireFieldsToData fs) = some fs
  | [] => rfl
  | (k, v) :: rest => by
    simp [dataWireFieldsToData, dataWireFieldsOfData?,
      dataWireOfData_toData v, dataWireFieldsOfData_toData rest]
end

/-- Bijective round-trip of `DataWire` through pure `Obend.Core.Data.Data`. -/
theorem DataWire.ofData_toData (w : DataWire) : DataWire.ofData? w.toData = some w :=
  dataWireOfData_toData w

/-- Live unforgeable linear capability token held in a `CustodyEnv`. -/
structure CapToken where
  slotId : Nat
  custodyId : Nat
  badge : Bytes
  deriving DecidableEq, Repr

/-- Linear custody environment owning live capability tokens. -/
structure CustodyEnv where
  tokens : List CapToken
  deriving DecidableEq, Repr

/-- One sealed entry inside a `CapTable`. -/
structure SealedCapEntry where
  index : Nat
  token : CapToken
  deriving DecidableEq, Repr

/-- Linear Capability Export/Import Table indexing extracted capabilities `0 .. n-1`. -/
structure CapTable where
  entries : List SealedCapEntry
  deriving DecidableEq, Repr

/-- Canonical, unbounded identifiers: no reduction modulo a machine word. -/
def encodeCapTableBytes (nonce : Nat) (tbl : CapTable) : Bytes :=
  Obend.Crypto.leb128 nonce ++ Obend.Crypto.leb128 tbl.entries.length ++
    (tbl.entries.flatMap fun e =>
      Obend.Crypto.leb128 e.index ++ Obend.Crypto.leb128 e.token.slotId ++
      Obend.Crypto.leb128 e.token.custodyId ++ Obend.Crypto.encodeListField e.token.badge)

/-- The authority key stays at the host; only its domain-bound seal crosses the wire. -/
def capFramePreimage (sealKey : ByteArray) (epoch : UInt64) (nonce : Nat) (tbl : CapTable) : Bytes :=
  "OBEND.VAULT.CAP_SEAL/v1".toUTF8.toList ++
    Obend.Crypto.encodeListField sealKey.data.toList ++ Obend.Crypto.leb128 epoch.toNat ++
    encodeCapTableBytes nonce tbl

/-- A full-width seal; security is conditional on the keyed host hash, never on a fixture hash. -/
def computeCapFrameSeal (Hb : Bytes → BitVec 256) (sealKey : ByteArray)
    (epoch : UInt64) (nonce : Nat) (tbl : CapTable) : BitVec 256 :=
  Hb (capFramePreimage sealKey epoch nonce tbl)

structure CapSealFrame where
  nonce : Nat
  epoch : UInt64
  table : CapTable
  sealBytes : BitVec 256
  deriving DecidableEq, Repr

/-- Authenticate under the caller's authority and current epoch. -/
def CapSealFrame.sealValid (Hb : Bytes → BitVec 256) (sealKey : ByteArray)
    (expectedEpoch : UInt64) (frame : CapSealFrame) : Bool :=
  decide (sealKey.size = 32 ∧ frame.epoch = expectedEpoch ∧
    frame.sealBytes = computeCapFrameSeal Hb sealKey frame.epoch frame.nonce frame.table)

/-- Return the first repeated slot, rather than allowing capability shadowing. -/
def duplicateSlot : List Nat → Option Nat
  | [] => none
  | x :: xs => if x ∈ xs then some x else duplicateSlot xs

theorem duplicateSlot_eq_none_iff (slots : List Nat) :
    duplicateSlot slots = none ↔ slots.Nodup := by
  induction slots with
  | nil => simp [duplicateSlot]
  | cons x xs ih => simp [duplicateSlot, List.nodup_cons, ih]

/-- Check consecutive 0-based indices starting at `start`. -/
def indexedFromBool (start : Nat) : List SealedCapEntry → Bool
  | [] => true
  | e :: es => (e.index == start) && indexedFromBool (start + 1) es

/-- Deterministic refusals of `dehydrate` / `rehydrate`. -/
inductive TransferRefusal where
  | missingOrDuplicateSlot (slotId : Nat)
  | custodyIdMismatch (idOrIdx expected actual : Nat)
  | droppedCustody (slotId : Nat)
  | unsealedFrame
  | invalidSealKey
  | malformedCapTable
  | forgedCapIndex (capIndex : Nat)
  | duplicateCapIndex (capIndex : Nat)
  | droppedSealedCap (capIndex : Nat)
  deriving DecidableEq, Repr

/-- Linearly extract and remove the first `CapToken` with `slotId` from `ts`. -/
def takeCapAtSlot (slotId : Nat) : List CapToken → Option (CapToken × List CapToken)
  | [] => none
  | t :: ts =>
    if t.slotId == slotId then some (t, ts)
    else (takeCapAtSlot slotId ts).map fun (found, rest) => (found, t :: rest)

theorem takeCapAtSlot_spec {slotId : Nat} {ts rest : List CapToken} {found : CapToken}
    (h : takeCapAtSlot slotId ts = some (found, rest)) :
    found.slotId = slotId ∧ ts.Perm (found :: rest) := by
  induction ts generalizing rest found with
  | nil => cases h
  | cons t ts ih =>
    simp only [takeCapAtSlot] at h; split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨beq_iff_eq.mp heq, List.Perm.refl _⟩
    · cases hrec : takeCapAtSlot slotId ts with
      | none => rw [hrec] at h; cases h
      | some pair =>
        obtain ⟨f', r'⟩ := pair; rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hid, hp⟩ := ih hrec
        exact ⟨hid, (hp.cons t).trans (List.Perm.swap f' t r')⟩

/-- Linearly extract and remove the `SealedCapEntry` at `capIndex` from `es`. -/
def takeSealedAtIndex (capIndex : Nat) : List SealedCapEntry → Option (SealedCapEntry × List SealedCapEntry)
  | [] => none
  | e :: es =>
    if e.index == capIndex then some (e, es)
    else (takeSealedAtIndex capIndex es).map fun (found, rest) => (found, e :: rest)

theorem takeSealedAtIndex_perm {capIndex : Nat} {es rest : List SealedCapEntry} {found : SealedCapEntry}
    (h : takeSealedAtIndex capIndex es = some (found, rest)) :
    found.index = capIndex ∧ es.Perm (found :: rest) := by
  induction es generalizing rest found with
  | nil => cases h
  | cons e es ih =>
    simp only [takeSealedAtIndex] at h; split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨beq_iff_eq.mp heq, List.Perm.refl _⟩
    · cases hrec : takeSealedAtIndex capIndex es with
      | none => rw [hrec] at h; cases h
      | some pair =>
        obtain ⟨f', r'⟩ := pair; rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hid, hp⟩ := ih hrec
        exact ⟨hid, (hp.cons e).trans (List.Perm.swap f' e r')⟩

mutual
def dehydrateVal (nextIdx : Nat) :
    TVal → List CapToken → Except TransferRefusal (DataWire × List CapToken × List SealedCapEntry)
  | .natural n, rem => .ok (.natural n, rem, [])
  | .boolean b, rem => .ok (.boolean b, rem, [])
  | .label s, rem => .ok (.label s, rem, [])
  | .cap slotId custodyId, rem =>
    match takeCapAtSlot slotId rem with
    | none => .error (.missingOrDuplicateSlot slotId)
    | some (tok, rem') =>
      if tok.custodyId == custodyId then .ok (.sealedCap nextIdx custodyId, rem', [⟨nextIdx, tok⟩])
      else .error (.custodyIdMismatch slotId custodyId tok.custodyId)
  | .variant tag p, rem =>
    match dehydrateVal nextIdx p rem with
    | .ok (wp, rem', ep) => .ok (.variant tag wp, rem', ep)
    | .error e => .error e
  | .record fs, rem =>
    match dehydrateFields nextIdx fs rem with
    | .ok (wfs, rem', efs) => .ok (.record wfs, rem', efs)
    | .error e => .error e

def dehydrateFields (nextIdx : Nat) :
    List (String × TVal) → List CapToken →
      Except TransferRefusal (List (String × DataWire) × List CapToken × List SealedCapEntry)
  | [], rem => .ok ([], rem, [])
  | (k, v) :: rest, rem =>
    match dehydrateVal nextIdx v rem with
    | .error e => .error e
    | .ok (wv, rem₁, e₁) =>
      match dehydrateFields (nextIdx + e₁.length) rest rem₁ with
      | .error e => .error e
      | .ok (wrest, rem₂, e₂) => .ok ((k, wv) :: wrest, rem₂, e₁ ++ e₂)
end

/-- **Dehydrate on `.perform` yield**: extracts linear capabilities into `(DataWire, CapSealFrame)`. -/
def dehydrate (Hb : Bytes → BitVec 256) (sealKey : ByteArray) (epoch : UInt64)
    (nonce : Nat) (env : CustodyEnv) (v : TVal) :
    Except TransferRefusal (DataWire × CapSealFrame) :=
  if sealKey.size ≠ 32 then .error .invalidSealKey else
  match dehydrateVal 0 v env.tokens with
  | .error e => .error e
  | .ok (wire, [], entries) =>
    match duplicateSlot (entries.map (·.token.slotId)) with
    | some slot => .error (.missingOrDuplicateSlot slot)
    | none =>
      let tbl : CapTable := ⟨entries⟩
      .ok (wire, ⟨nonce, epoch, tbl, computeCapFrameSeal Hb sealKey epoch nonce tbl⟩)
  | .ok (_, leftover :: _, _) => .error (.droppedCustody leftover.slotId)

mutual
def rehydrateVal (boundLen : Nat) :
    DataWire → List SealedCapEntry → Except TransferRefusal (TVal × List SealedCapEntry × List CapToken)
  | .natural n, avail => .ok (.natural n, avail, [])
  | .boolean b, avail => .ok (.boolean b, avail, [])
  | .label s, avail => .ok (.label s, avail, [])
  | .sealedCap idx custodyId, avail =>
    if idx ≥ boundLen then .error (.forgedCapIndex idx) else
    match takeSealedAtIndex idx avail with
    | none => .error (.duplicateCapIndex idx)
    | some (entry, avail') =>
      if entry.token.custodyId == custodyId then
        .ok (.cap entry.token.slotId custodyId, avail', [entry.token])
      else .error (.custodyIdMismatch idx custodyId entry.token.custodyId)
  | .variant tag wp, avail =>
    match rehydrateVal boundLen wp avail with
    | .ok (p, avail', toks) => .ok (.variant tag p, avail', toks)
    | .error e => .error e
  | .record wfs, avail =>
    match rehydrateFields boundLen wfs avail with
    | .ok (fs, avail', toks) => .ok (.record fs, avail', toks)
    | .error e => .error e

def rehydrateFields (boundLen : Nat) :
    List (String × DataWire) → List SealedCapEntry →
      Except TransferRefusal (List (String × TVal) × List SealedCapEntry × List CapToken)
  | [], avail => .ok ([], avail, [])
  | (k, wv) :: wrest, avail =>
    match rehydrateVal boundLen wv avail with
    | .error e => .error e
    | .ok (v, avail₁, t₁) =>
      match rehydrateFields boundLen wrest avail₁ with
      | .error e => .error e
      | .ok (rest, avail₂, t₂) => .ok ((k, v) :: rest, avail₂, t₁ ++ t₂)
end

/-- **Rehydrate on `.perform` resume**: verifies seal, reconstructs `(TVal, CustodyEnv)` linearly. -/
def rehydrate (Hb : Bytes → BitVec 256) (sealKey : ByteArray) (expectedEpoch : UInt64)
    (wire : DataWire) (frame : CapSealFrame) : Except TransferRefusal (TVal × CustodyEnv) :=
  if !frame.sealValid Hb sealKey expectedEpoch then .error .unsealedFrame
  else if !indexedFromBool 0 frame.table.entries then .error .malformedCapTable
  else
    match duplicateSlot (frame.table.entries.map (·.token.slotId)) with
    | some slot => .error (.missingOrDuplicateSlot slot)
    | none =>
      match rehydrateVal frame.table.entries.length wire frame.table.entries with
      | .error e => .error e
      | .ok (v, [], imported) => .ok (v, ⟨imported⟩)
      | .ok (_, leftover :: _, _) => .error (.droppedSealedCap leftover.index)

/-! ### Round-Trip & Strict Linear Custody Conservation Proofs -/

theorem indexedFromBool_append :
    ∀ (e₁ e₂ : List SealedCapEntry) (start : Nat),
      indexedFromBool start e₁ = true → indexedFromBool (start + e₁.length) e₂ = true →
      indexedFromBool start (e₁ ++ e₂) = true
  | [], e₂, start, _, h₂ => by simpa using h₂
  | x :: xs, e₂, start, h₁, h₂ => by
    simp only [indexedFromBool, List.cons_append, Bool.and_eq_true] at h₁ ⊢
    have hlen : start + (x :: xs).length = (start + 1) + xs.length := by simp [List.length_cons]; omega
    rw [hlen] at h₂; exact ⟨h₁.1, indexedFromBool_append xs e₂ (start + 1) h₁.2 h₂⟩

mutual
theorem dehydrateVal_spec :
    ∀ (v : TVal) (nextIdx : Nat) (rem rem' : List CapToken) (wire : DataWire)
      (entries : List SealedCapEntry),
      dehydrateVal nextIdx v rem = .ok (wire, rem', entries) →
      indexedFromBool nextIdx entries = true ∧
      rem.Perm (entries.map SealedCapEntry.token ++ rem') ∧
      entries.map (fun e => e.token.slotId) = tvalCapSlots v ∧
      ∀ (boundLen : Nat) (tailAvail : List SealedCapEntry),
        nextIdx + entries.length ≤ boundLen →
        rehydrateVal boundLen wire (entries ++ tailAvail) =
          .ok (v, tailAvail, entries.map SealedCapEntry.token)
  | .natural _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .boolean _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .label _, _, _, _, _, _, h => by
    simp only [dehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | .cap slotId custodyId, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases ht : takeCapAtSlot slotId rem with
    | none => rw [ht] at h; cases h
    | some pair =>
      obtain ⟨tok, r₁⟩ := pair; rw [ht] at h; dsimp only at h; split at h
      · rename_i hcid
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hslot, hperm⟩ := takeCapAtSlot_spec ht
        refine ⟨by simp [indexedFromBool], hperm, by simp [tvalCapSlots, hslot], ?_⟩
        intro boundLen tailAvail hle; simp only [List.length_singleton] at hle
        have hnot_ge : ¬ (nextIdx ≥ boundLen) := by omega
        simp [rehydrateVal, hnot_ge, takeSealedAtIndex, hcid, hslot]
      · cases h
  | .variant tag p, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases hd : dehydrateVal nextIdx p rem with
    | error e => rw [hd] at h; cases h
    | ok res =>
      obtain ⟨wp, r₁, ep⟩ := res; rw [hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hind, hperm, hslots, hrehyd⟩ := dehydrateVal_spec p nextIdx rem r₁ wp ep hd
      refine ⟨hind, hperm, by simpa [tvalCapSlots] using hslots, ?_⟩
      intro boundLen tailAvail hle; simp [rehydrateVal, hrehyd boundLen tailAvail hle]
  | .record fs, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateVal] at h
    cases hd : dehydrateFields nextIdx fs rem with
    | error e => rw [hd] at h; cases h
    | ok res =>
      obtain ⟨wfs, r₁, efs⟩ := res; rw [hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hind, hperm, hslots, hrehyd⟩ := dehydrateFields_spec fs nextIdx rem r₁ wfs efs hd
      refine ⟨hind, hperm, by simpa [tvalCapSlots] using hslots, ?_⟩
      intro boundLen tailAvail hle; simp [rehydrateVal, hrehyd boundLen tailAvail hle]

theorem dehydrateFields_spec :
    ∀ (fs : List (String × TVal)) (nextIdx : Nat) (rem rem' : List CapToken)
      (wfs : List (String × DataWire)) (entries : List SealedCapEntry),
      dehydrateFields nextIdx fs rem = .ok (wfs, rem', entries) →
      indexedFromBool nextIdx entries = true ∧
      rem.Perm (entries.map SealedCapEntry.token ++ rem') ∧
      entries.map (fun e => e.token.slotId) = tvalCapSlotsFields fs ∧
      ∀ (boundLen : Nat) (tailAvail : List SealedCapEntry),
        nextIdx + entries.length ≤ boundLen →
        rehydrateFields boundLen wfs (entries ++ tailAvail) =
          .ok (fs, tailAvail, entries.map SealedCapEntry.token)
  | [], _, _, _, _, _, h => by
    simp only [dehydrateFields, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, List.Perm.refl _, rfl, fun _ _ _ => rfl⟩
  | (k, v) :: rest, nextIdx, rem, _, _, _, h => by
    simp only [dehydrateFields] at h
    cases hd1 : dehydrateVal nextIdx v rem with
    | error e => rw [hd1] at h; cases h
    | ok res1 =>
      obtain ⟨wv, rem₁, e₁⟩ := res1; rw [hd1] at h; dsimp only at h
      cases hd2 : dehydrateFields (nextIdx + e₁.length) rest rem₁ with
      | error e => rw [hd2] at h; cases h
      | ok res2 =>
        obtain ⟨wrest, rem₂, e₂⟩ := res2; rw [hd2] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hi1, hp1, hs1, hr1⟩ := dehydrateVal_spec v nextIdx rem rem₁ wv e₁ hd1
        obtain ⟨hi2, hp2, hs2, hr2⟩ := dehydrateFields_spec rest (nextIdx + e₁.length) rem₁ rem₂ wrest e₂ hd2
        have hperm_all : rem.Perm ((e₁ ++ e₂).map SealedCapEntry.token ++ rem₂) := by
          rw [List.map_append, List.append_assoc]; exact hp1.trans (hp2.append_left _)
        refine ⟨indexedFromBool_append e₁ e₂ nextIdx hi1 hi2, hperm_all, ?_, ?_⟩
        · simp [tvalCapSlotsFields, List.map_append, hs1, hs2]
        · intro boundLen tailAvail hle; rw [List.length_append] at hle; rw [List.append_assoc]
          simp [rehydrateFields, hr1 boundLen (e₂ ++ tailAvail) (by omega),
            hr2 boundLen tailAvail (by omega), List.map_append]
end

mutual
theorem rehydrateVal_perm :
    ∀ (boundLen : Nat) (wire : DataWire) (avail avail' : List SealedCapEntry)
      (v : TVal) (toks : List CapToken),
      rehydrateVal boundLen wire avail = .ok (v, avail', toks) →
      (avail.map SealedCapEntry.token).Perm (toks ++ avail'.map SealedCapEntry.token)
  | _, .natural _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .boolean _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .label _, _, _, _, _, h => by
    simp only [rehydrateVal, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | _, .sealedCap idx _, avail, _, _, _, h => by
    simp only [rehydrateVal] at h; split at h
    · cases h
    · cases ht : takeSealedAtIndex idx avail with
      | none => rw [ht] at h; cases h
      | some pair =>
        obtain ⟨entry, av₁⟩ := pair; rw [ht] at h; dsimp only at h; split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          simpa using (takeSealedAtIndex_perm ht).2.map SealedCapEntry.token
        · cases h
  | boundLen, .variant _ wp, avail, _, _, _, h => by
    simp only [rehydrateVal] at h
    cases hr : rehydrateVal boundLen wp avail with
    | error e => rw [hr] at h; cases h
    | ok res =>
      obtain ⟨p, av₁, t₁⟩ := res; rw [hr] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact rehydrateVal_perm boundLen wp avail av₁ p t₁ hr
  | boundLen, .record wfs, avail, _, _, _, h => by
    simp only [rehydrateVal] at h
    cases hr : rehydrateFields boundLen wfs avail with
    | error e => rw [hr] at h; cases h
    | ok res =>
      obtain ⟨fs, av₁, t₁⟩ := res; rw [hr] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact rehydrateFields_perm boundLen wfs avail av₁ fs t₁ hr

theorem rehydrateFields_perm :
    ∀ (boundLen : Nat) (wfs : List (String × DataWire)) (avail avail' : List SealedCapEntry)
      (fs : List (String × TVal)) (toks : List CapToken),
      rehydrateFields boundLen wfs avail = .ok (fs, avail', toks) →
      (avail.map SealedCapEntry.token).Perm (toks ++ avail'.map SealedCapEntry.token)
  | _, [], _, _, _, _, h => by
    simp only [rehydrateFields, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact List.Perm.refl _
  | boundLen, (_, wv) :: wrest, avail, _, _, _, h => by
    simp only [rehydrateFields] at h
    cases hr1 : rehydrateVal boundLen wv avail with
    | error e => rw [hr1] at h; cases h
    | ok res1 =>
      obtain ⟨v, av₁, t₁⟩ := res1; rw [hr1] at h; dsimp only at h
      cases hr2 : rehydrateFields boundLen wrest av₁ with
      | error e => rw [hr2] at h; cases h
      | ok res2 =>
        obtain ⟨rest, av₂, t₂⟩ := res2; rw [hr2] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        rw [List.append_assoc]
        exact (rehydrateVal_perm boundLen wv avail av₁ v t₁ hr1).trans
          ((rehydrateFields_perm boundLen wrest av₁ av₂ rest t₂ hr2).append_left t₁)
end

/-- Successful dehydration exposes both the linear extraction and the authority checks. -/
theorem dehydrate_ok_inv {Hb : Bytes → BitVec 256} {key : ByteArray} {epoch : UInt64}
    {nonce : Nat} {src : CustodyEnv} {v : TVal} {wire : DataWire} {frame : CapSealFrame}
    (h : dehydrate Hb key epoch nonce src v = .ok (wire, frame)) :
    key.size = 32 ∧ dehydrateVal 0 v src.tokens = .ok (wire, [], frame.table.entries) ∧
    duplicateSlot (frame.table.entries.map (·.token.slotId)) = none ∧
    frame.nonce = nonce ∧ frame.epoch = epoch ∧
    frame.sealBytes = computeCapFrameSeal Hb key epoch nonce frame.table := by
  unfold dehydrate at h
  split at h
  · cases h
  · rename_i hk
    cases hd : dehydrateVal 0 v src.tokens with
    | error e => simp [hd] at h
    | ok res =>
      obtain ⟨w, rem, entries⟩ := res
      cases rem with
      | cons t ts => simp [hd] at h
      | nil =>
        cases hs : duplicateSlot (entries.map (·.token.slotId)) with
        | some slot => simp [hd, hs] at h
        | none =>
          simp only [hd, hs, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simpa using hk, hd, hs, rfl, rfl, rfl⟩

/-- Successful restore authenticates the epoch and consumes every sealed token once. -/
theorem rehydrate_ok_inv {Hb : Bytes → BitVec 256} {key : ByteArray} {epoch : UInt64}
    {wire : DataWire} {frame : CapSealFrame} {v : TVal} {env : CustodyEnv}
    (h : rehydrate Hb key epoch wire frame = .ok (v, env)) :
    frame.sealValid Hb key epoch = true ∧
    duplicateSlot (frame.table.entries.map (·.token.slotId)) = none ∧
    rehydrateVal frame.table.entries.length wire frame.table.entries = .ok (v, [], env.tokens) := by
  unfold rehydrate at h
  split at h
  · cases h
  · rename_i hs
    have hs' : frame.sealValid Hb key epoch = true := by simpa using hs
    split at h
    · cases h
    · cases hd : duplicateSlot (frame.table.entries.map (·.token.slotId)) with
      | some slot => simp [hd] at h
      | none =>
        rw [hd] at h
        cases hr : rehydrateVal frame.table.entries.length wire frame.table.entries with
        | error e => simp [hr] at h
        | ok res =>
          obtain ⟨vr, rem, imported⟩ := res
          cases rem with
          | cons e es => simp [hr] at h
          | nil =>
            simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hs', hd, hr⟩

theorem rehydrate_dehydrate_roundtrip (Hb : Bytes → BitVec 256) (key : ByteArray)
    (epoch : UInt64) (nonce : Nat) (srcEnv : CustodyEnv) (v : TVal)
    {wire : DataWire} {frame : CapSealFrame}
    (hDehyd : dehydrate Hb key epoch nonce srcEnv v = .ok (wire, frame)) :
    rehydrate Hb key epoch wire frame = .ok (v, ⟨frame.table.entries.map SealedCapEntry.token⟩) ∧
    (frame.table.entries.map SealedCapEntry.token).Perm srcEnv.tokens := by
  obtain ⟨hk, hd, hn, hnonce, hepoch, hseal⟩ := dehydrate_ok_inv hDehyd
  obtain ⟨hind, hp, _, hr⟩ := dehydrateVal_spec v 0 srcEnv.tokens [] wire frame.table.entries hd
  rw [List.append_nil] at hp
  have hs : frame.sealValid Hb key epoch = true := by
    simp [CapSealFrame.sealValid, hk, hepoch, hnonce, hseal]
  have hr' := hr frame.table.entries.length [] (by omega)
  rw [List.append_nil] at hr'
  exact ⟨by simp [rehydrate, hs, hind, hn, hr'], hp.symm⟩

theorem transfer_conserves_custody_exact (Hb : Bytes → BitVec 256) (key : ByteArray)
    (epoch : UInt64) (nonce : Nat)
    (srcEnv dstEnv : CustodyEnv) (v v' : TVal) (wire wire' : DataWire) (frame : CapSealFrame)
    (hDehyd : dehydrate Hb key epoch nonce srcEnv v = .ok (wire, frame))
    (hRehyd : rehydrate Hb key epoch wire' frame = .ok (v', dstEnv)) :
    dstEnv.tokens.Perm srcEnv.tokens ∧
    dstEnv.tokens.length = srcEnv.tokens.length ∧
    (∀ tok : CapToken, dstEnv.tokens.count tok = srcEnv.tokens.count tok) ∧
    (srcEnv.tokens.map CapToken.slotId).Perm v.capSlots ∧
    ((srcEnv.tokens.map CapToken.slotId).Nodup → v.capSlots.Nodup) := by
  have hd := (dehydrate_ok_inv hDehyd).2.1
  have hr := (rehydrate_ok_inv hRehyd).2.2
  obtain ⟨_, hp, hslots, _⟩ := dehydrateVal_spec v 0 srcEnv.tokens [] wire frame.table.entries hd
  have hq := rehydrateVal_perm frame.table.entries.length wire' frame.table.entries [] v' dstEnv.tokens hr
  simp only [List.map_nil, List.append_nil] at hp hq
  have hboth := hq.symm.trans hp.symm
  have hslot : (srcEnv.tokens.map CapToken.slotId).Perm v.capSlots := by
    have hm := hp.map CapToken.slotId
    simpa only [List.map_map, Function.comp_def, hslots] using hm
  exact ⟨hboth, hboth.length_eq, fun tok => hboth.count_eq tok,
    hslot, fun hnd => hslot.nodup_iff.mp hnd⟩

theorem rehydrate_restores_nodup_slots {Hb : Bytes → BitVec 256} {key : ByteArray}
    {epoch : UInt64} {wire : DataWire} {frame : CapSealFrame} {v : TVal} {env : CustodyEnv}
    (h : rehydrate Hb key epoch wire frame = .ok (v, env)) :
    (env.tokens.map (·.slotId)).Nodup := by
  obtain ⟨_, hn, hr⟩ := rehydrate_ok_inv h
  have hp := rehydrateVal_perm frame.table.entries.length wire frame.table.entries [] v env.tokens hr
  simp only [List.map_nil, List.append_nil] at hp
  have hm := hp.map CapToken.slotId
  have nd := (duplicateSlot_eq_none_iff _).mp hn
  exact hm.nodup_iff.mp (by simpa only [List.map_map, Function.comp_def] using nd)

/-- Binding reduction for two authority contexts accepting the same full-width seal.
This is a collision reduction, not an unconditional MAC-unforgeability assertion. -/
theorem rehydrate_binds_sealKey_epoch_or_collision
    {Hb : Bytes → BitVec 256} {key₁ key₂ : ByteArray} {epoch₁ epoch₂ : UInt64}
    {wire₁ wire₂ : DataWire} {frame₁ frame₂ : CapSealFrame}
    {v₁ v₂ : TVal} {env₁ env₂ : CustodyEnv}
    (h₁ : rehydrate Hb key₁ epoch₁ wire₁ frame₁ = .ok (v₁, env₁))
    (h₂ : rehydrate Hb key₂ epoch₂ wire₂ frame₂ = .ok (v₂, env₂))
    (hseal : frame₁.sealBytes = frame₂.sealBytes) :
    (key₁ = key₂ ∧ epoch₁ = epoch₂) ∨
      ∃ a b : Bytes, a ≠ b ∧ Hb a = Hb b := by
  have hs₁ := (rehydrate_ok_inv h₁).1
  have hs₂ := (rehydrate_ok_inv h₂).1
  simp only [CapSealFrame.sealValid, decide_eq_true_eq] at hs₁ hs₂
  have he : computeCapFrameSeal Hb key₁ frame₁.epoch frame₁.nonce frame₁.table =
      computeCapFrameSeal Hb key₂ frame₂.epoch frame₂.nonce frame₂.table :=
    hs₁.2.2.symm.trans (hseal.trans hs₂.2.2)
  by_cases hp : capFramePreimage key₁ frame₁.epoch frame₁.nonce frame₁.table =
      capFramePreimage key₂ frame₂.epoch frame₂.nonce frame₂.table
  · unfold capFramePreimage at hp
    simp only [List.append_assoc, List.append_cancel_left_eq] at hp
    obtain ⟨hk, ht⟩ := Obend.Crypto.encodeListField_prefix_inj hp
    obtain ⟨hepoch, _⟩ := Obend.Crypto.leb128_prefix_inj ht
    exact .inl ⟨Obend.Crypto.byteArray_eq_of_toList_eq hk,
      hs₁.2.1.symm.trans ((UInt64.toNat_inj.mp hepoch).trans hs₂.2.1)⟩
  · exact .inr ⟨_, _, hp, he⟩

theorem forged_cap_index_refused (Hb : Bytes → BitVec 256) (key : ByteArray)
    (epoch : UInt64) (frame : CapSealFrame)
    (hSeal : frame.sealValid Hb key epoch = true) (hIdx : indexedFromBool 0 frame.table.entries = true)
    (hSlots : duplicateSlot (frame.table.entries.map (·.token.slotId)) = none)
    (idx custodyId : Nat) (hForged : idx ≥ frame.table.entries.length) :
    rehydrate Hb key epoch (.sealedCap idx custodyId) frame = .error (.forgedCapIndex idx) := by
  simp [rehydrate, hSeal, hIdx, hSlots, rehydrateVal, hForged]

theorem unsealed_frame_refused (Hb : Bytes → BitVec 256) (key : ByteArray) (epoch : UInt64)
    (wire : DataWire) (frame : CapSealFrame) (hBad : frame.sealValid Hb key epoch = false) :
    rehydrate Hb key epoch wire frame = .error .unsealedFrame := by simp [rehydrate, hBad]

theorem stale_epoch_refused (Hb : Bytes → BitVec 256) (key : ByteArray) (epoch : UInt64)
    (wire : DataWire) (frame : CapSealFrame) (h : frame.epoch ≠ epoch) :
    rehydrate Hb key epoch wire frame = .error .unsealedFrame := by
  simp [rehydrate, CapSealFrame.sealValid, h]

theorem duplicate_cap_slot_refused (Hb : Bytes → BitVec 256) (key : ByteArray)
    (epoch : UInt64) (nonce slotId cid : Nat) (badge : Bytes) (hk : key.size = 32) :
    let env : CustodyEnv := ⟨[⟨slotId, cid, badge⟩]⟩
    let dupPlan : TVal := .record [("first", .cap slotId cid), ("second", .cap slotId cid)]
    dehydrate Hb key epoch nonce env dupPlan = .error (.missingOrDuplicateSlot slotId) := by
  simp [dehydrate, hk, dehydrateVal, dehydrateFields, takeCapAtSlot]

theorem dropped_custody_refused (Hb : Bytes → BitVec 256) (key : ByteArray)
    (epoch : UInt64) (nonce slotId cid : Nat) (badge : Bytes) (hk : key.size = 32) :
    let env : CustodyEnv := ⟨[⟨slotId, cid, badge⟩]⟩
    dehydrate Hb key epoch nonce env (.natural 7) = .error (.droppedCustody slotId) := by
  simp [dehydrate, hk, dehydrateVal]

/-! ### Inhabited Module Witnesses -/

/-- Non-cryptographic fixture covering every input byte; never a production authority. -/
def sampleIdentityHash (bs : Bytes) : BitVec 256 :=
  bs.foldl (fun h b => h * 257 + BitVec.ofNat 256 b.toNat) 0

def sampleSealKey : ByteArray := ⟨(List.replicate 32 (0x5a : UInt8)).toArray⟩

def samplePlanVal : TVal :=
  .variant "transferSturdyref"
    (.record [("badgeCap", .cap 10 1), ("coReceipt", .cap 20 2), ("epoch", .natural 9)])

def sampleCustodyEnv : CustodyEnv := ⟨[⟨10, 1, [0xaa, 0xbb]⟩, ⟨20, 2, [0xcc, 0xdd]⟩]⟩

def sampleRoundtripCheck : Bool :=
  match dehydrate sampleIdentityHash sampleSealKey 9 42 sampleCustodyEnv samplePlanVal with
  | .ok (wire, frame) =>
    DataWire.ofData? wire.toData == some wire &&
    frame.sealValid sampleIdentityHash sampleSealKey 9 &&
    indexedFromBool 0 frame.table.entries &&
    match rehydrate sampleIdentityHash sampleSealKey 9 wire frame with
    | .ok (v', env') => v' == samplePlanVal && env' == sampleCustodyEnv
    | .error _ => false
  | .error _ => false

example : (Ty.variant (.field "badgeCap" (.custody 1) (.field "epoch" .natural .emptyRow))).isTransferablePlan = true := by decide
example : (Ty.variant (.field "badgeCap" (.custody 1) (.field "epoch" .natural .emptyRow))).isPlan = false := by decide
example : TVal.conforms samplePlanVal
    (.variant (.field "transferSturdyref"
      (.field "badgeCap" (.custody 1) (.field "coReceipt" (.custody 2) (.field "epoch" .natural .emptyRow)))
      .emptyRow)) = true := by decide
example : sampleRoundtripCheck = true := by
  simp [sampleRoundtripCheck, dehydrate, sampleSealKey, samplePlanVal, sampleCustodyEnv,
    dehydrateVal, dehydrateFields, takeCapAtSlot, duplicateSlot,
    rehydrate, CapSealFrame.sealValid, indexedFromBool, rehydrateVal, rehydrateFields,
    takeSealedAtIndex, DataWire.toData, dataWireToData, dataWireFieldsToData,
    DataWire.ofData?, dataWireOfData?, dataWireFieldsOfData?,
    dataWireBeq, dataWireFieldsBeq, tvalBeq, tvalFieldsBeq]

/-- Constructive two-capability transfer with a real authority context and distinct live slots. -/
theorem transfer_inhabited :
    ∃ wire frame env,
      dehydrate sampleIdentityHash sampleSealKey 9 42 sampleCustodyEnv samplePlanVal = .ok (wire, frame) ∧
      rehydrate sampleIdentityHash sampleSealKey 9 wire frame = .ok (samplePlanVal, env) := by
  let wire : DataWire := .variant "transferSturdyref"
    (.record [("badgeCap", .sealedCap 0 1), ("coReceipt", .sealedCap 1 2), ("epoch", .natural 9)])
  let table : CapTable := ⟨[⟨0, ⟨10, 1, [0xaa, 0xbb]⟩⟩, ⟨1, ⟨20, 2, [0xcc, 0xdd]⟩⟩]⟩
  let frame : CapSealFrame := ⟨42, 9, table, computeCapFrameSeal sampleIdentityHash sampleSealKey 9 42 table⟩
  have hd : dehydrate sampleIdentityHash sampleSealKey 9 42 sampleCustodyEnv samplePlanVal =
      .ok (wire, frame) := by rfl
  exact ⟨wire, frame, _, hd,
    (rehydrate_dehydrate_roundtrip sampleIdentityHash sampleSealKey 9 42
      sampleCustodyEnv samplePlanVal hd).1⟩

end Obend.Run.VaultDurableBridge

namespace Obend.Vault.VerkleSnapshotBridge
open Obend.Digest.HashBytes (Hash be ofBE ofBE_lt)
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness)
open Obend.Crypto (AjtaiParams NonPigeonholeSISParams ModuleSISHard BoundedCollision
  cshake32ByteArray cshake32ByteArray_size encodeListField leb128 Short ShortNormBound
  ajtaiCommit extractShortDiffSISWitness inhabitedAjtaiParams inhabitedAjtaiParams_sisHard)
open Obend.Polis (ExtRam treeCustomization treeHash tagOf leafPreimage nodePreimage
  leafTag nodeTag nibbleAt insertAt insertAt_inj climbStep climb verifyOpening
  encodeFields encodeFields_injective map_toList_injective)
open Obend.Vault
open Obend.Vault.Rehydration (genesisSentinel)
set_option autoImplicit false
/-! ## 6. Crash-Safe Torn-Write WAL Recovery Idempotence & Multi-Epoch `ValidSnapshotTrace` -/
private theorem unbe_take32_lt_bound (s : Log.Bytes) : Log.unbe (s.take 32) < Log.bound := by
  unfold Log.bound
  exact Nat.lt_of_lt_of_le (Log.unbe_lt (s.take 32))
    (Nat.pow_le_pow_right (by decide) (List.length_take_le 32 s))
/-- Every `OBL1` record accepted by `Log.parseOne` is automatically well-formed (`Record.WF Hb`). -/
theorem parseOne_ok_wf (Hb : Log.Bytes → Log.Bytes) {prev : Option Nat}
    {bs rest : Log.Bytes} {r : Log.Record}
    (h : Log.parseOne Hb prev bs = .ok (r, rest)) : r.WF Hb := by
  have heff := (Log.parseOne_ok_inv Hb h).2.1
  unfold Log.parseOne at h
  cases e1 : Log.takeN 136 bs with
  | none => rw [e1] at h; cases h
  | some x =>
    obtain ⟨hd, tl⟩ := x
    rw [e1] at h; dsimp only at h
    split at h
    · cases h
    · cases e2 : Log.takeN (Log.unbe ((hd.drop 4).take 4) + 32) tl with
      | none => rw [e2] at h; cases h
      | some y =>
        obtain ⟨bd, tl'⟩ := y
        rw [e2] at h; dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
              refine ⟨unbe_take32_lt_bound _, unbe_take32_lt_bound _, unbe_take32_lt_bound _, heff, ?_⟩
              have hlen4 : Log.unbe ((hd.drop 4).take 4) < 256 ^ 4 :=
                Nat.lt_of_lt_of_le (Log.unbe_lt ((hd.drop 4).take 4))
                  (Nat.pow_le_pow_right (by decide) (List.length_take_le 4 _))
              exact Nat.lt_of_le_of_lt (List.length_take_le _ _) hlen4
/-- Every record parsed from any raw byte sequence by `Log.parseFrom` satisfies `Record.WF Hb`. -/
theorem parseFrom_wf (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (bs : Log.Bytes) :
    ∀ r ∈ (Log.parseFrom Hb prev bs).1, r.WF Hb := by
  induction h : bs.length using Nat.strongRecOn generalizing prev bs with
  | ind n ih =>
    by_cases hne : bs = []
    · subst hne; simp [Log.parseFrom_nil]
    · cases hp : Log.parseOne Hb (some prev) bs with
      | error d => rw [Log.parseFrom_error Hb hne hp]; simp
      | ok x =>
        obtain ⟨r, rest⟩ := x; rw [Log.parseFrom_ok Hb hp]
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact parseOne_ok_wf Hb hp
        · exact ih rest.length (h ▸ Log.parseOne_rest Hb hp) (Log.Hr Hb r.receipt) rest rfl y hy'
/-- **Open-World WAL Frame Filter Completeness (`walDrop_complete_iff_invalid_frame`)**:
    `Log.parseFrom` drops a non-empty suffix iff `Log.parseOne` rejects it at the ending anchor. -/
theorem walDrop_complete_iff_invalid_frame (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (bs : Log.Bytes) :
    let parsed := Log.parseFrom Hb prev bs
    parsed.2.1 ≠ [] ↔ ∃ d : Log.Drop, parsed.2.2 = some d ∧
      Log.parseOne Hb (some (Log.lastHash Hb prev parsed.1)) parsed.2.1 = .error d := by
  induction h : bs.length using Nat.strongRecOn generalizing prev bs with
  | ind n ih =>
    by_cases hne : bs = []
    · subst hne; simp [Log.parseFrom_nil]
    · cases hp : Log.parseOne Hb (some prev) bs with
      | error d => rw [Log.parseFrom_error Hb hne hp]; simp [Log.lastHash, hne, hp]
      | ok x =>
        obtain ⟨r, rest⟩ := x
        have ih' := ih rest.length (h ▸ Log.parseOne_rest Hb hp) (Log.Hr Hb r.receipt) rest rfl
        rw [Log.parseFrom_ok Hb hp]; simpa [Log.lastHash] using ih'
/-- Trailing WAL bytes lacking a valid linked commit frame at `anchor`. -/
def UncommittedWalTail (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    (tail : Log.Bytes) : Prop :=
  tail = [] ∨ ∃ d : Log.Drop, Log.parseOne Hb (some anchor) tail = .error d
/-- Any proper byte prefix `(encodeRecord Hb r).take k` satisfies `UncommittedWalTail`. -/
theorem tornRecordPrefix_is_uncommitted (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    {r : Log.Record} (hwf : r.WF Hb) {k : Nat} (hk : k < (Log.encodeRecord Hb r).length) :
    UncommittedWalTail Hb anchor ((Log.encodeRecord Hb r).take k) := by
  by_cases hk0 : k = 0
  · subst hk0; exact .inl rfl
  · exact .inr ⟨.torn, Log.parseOne_torn Hb hwf (List.take_append_drop k _)
      (by rw [Ne, List.drop_eq_nil_iff]; omega)⟩
theorem parseFrom_uncommittedWalTail (Hb : Log.Bytes → Log.Bytes) (anchor : Nat)
    {tail : Log.Bytes} (hu : UncommittedWalTail Hb anchor tail) :
    (Log.parseFrom Hb anchor tail).1 = [] ∧ (Log.parseFrom Hb anchor tail).2.1 = tail := by
  rcases hu with rfl | ⟨d, hd⟩
  · simp [Log.parseFrom_nil]
  · by_cases hne : tail = []
    · subst hne; simp [Log.parseFrom_nil]
    · rw [Log.parseFrom_error Hb hne hd]; exact ⟨rfl, rfl⟩
/-- Outcome of crash-safe WAL recovery. -/
structure WalRecoveryResult where
  cleanDisk : Log.Bytes
  snapshot : AuthenticatedWorldSnapshot
  committedCount : Nat
  droppedTail : Log.Bytes
  dropReason : Option Log.Drop
  deriving DecidableEq
/-- Canonical WAL byte truncation: encodes committed `OBL1` frames and drops any uncommitted tail. -/
def recoverWalBytes (rawDisk : Log.Bytes) : Log.Bytes :=
  Log.encodeAll Replay.logHash (Log.parseFrom Replay.logHash genesisSentinel rawDisk).1
/-- Full WAL crash recovery over a world machine `M` (defaulting to `Replay.deployed`). -/
def recoverWalSnapshot {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World)
    (rawDisk : Log.Bytes) : WalRecoveryResult :=
  let parsed := Log.parseFrom Replay.logHash genesisSentinel rawDisk
  { cleanDisk := Log.encodeAll Replay.logHash parsed.1
    snapshot := buildAuthenticatedSnapshot pp hCols (Log.replay M w0 parsed.1)
    committedCount := parsed.1.length, droppedTail := parsed.2.1, dropReason := parsed.2.2 }
/-- Re-parsing the encoded records recovered by `Log.parseFrom` yields `(qs, [], none)`. -/
theorem parseFrom_encodeAll_recovered (Hb : Log.Bytes → Log.Bytes) (prev : Nat) (rawDisk : Log.Bytes) :
    Log.parseFrom Hb prev (Log.encodeAll Hb (Log.parseFrom Hb prev rawDisk).1) =
      ((Log.parseFrom Hb prev rawDisk).1, [], none) := by
  let qs := (Log.parseFrom Hb prev rawDisk).1
  simpa [qs, List.append_nil, Log.parseFrom_nil] using
    Log.parseFrom_encodeAll Hb qs prev (Log.parseFrom_sound Hb prev rawDisk).1
      (parseFrom_wf Hb prev rawDisk) []
/-- **Unconditional Byte-Level WAL Truncation Idempotence (`recoverWalBytes_idempotent`)**. -/
theorem recoverWalBytes_idempotent (rawDisk : Log.Bytes) :
    recoverWalBytes (recoverWalBytes rawDisk) = recoverWalBytes rawDisk := by
  unfold recoverWalBytes; rw [parseFrom_encodeAll_recovered]
/-- **Unconditional Snapshot WAL Recovery Idempotence (`walCrashRecovery_idempotent`)**. -/
theorem walCrashRecovery_idempotent {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World) (rawDisk : Log.Bytes) :
    recoverWalSnapshot pp hCols M w0 (recoverWalSnapshot pp hCols M w0 rawDisk).cleanDisk =
      { recoverWalSnapshot pp hCols M w0 rawDisk with droppedTail := [], dropReason := none } := by
  unfold recoverWalSnapshot; dsimp only; rw [parseFrom_encodeAll_recovered]
/-- One admitted epoch turn in a multi-epoch snapshot trace. -/
structure SnapshotEpoch where
  turnBytes : Log.Bytes
  record : Log.Record
  deriving DecidableEq
/-- **Multi-Epoch Snapshot & WAL Trace Invariant (`ValidSnapshotTrace`)**. -/
inductive ValidSnapshotTrace {O : Type} (pp : AjtaiParams) (hCols : pp.cols = 64)
    (M : Log.Machine ChunkedWorld.World O) (w0 : ChunkedWorld.World) :
    List SnapshotEpoch → Log.Session ChunkedWorld.World → AuthenticatedWorldSnapshot → Prop where
  | genesis : ValidSnapshotTrace pp hCols M w0 [] ⟨w0, []⟩ (buildAuthenticatedSnapshot pp hCols w0)
  | commitEpoch {epochs : List SnapshotEpoch} {S S' : Log.Session ChunkedWorld.World}
      {snap : AuthenticatedWorldSnapshot} {turnBytes : Log.Bytes} {rec : Log.Record} :
      ValidSnapshotTrace pp hCols M w0 epochs S snap →
      S.admit Replay.logHash M turnBytes = .ok S' → S'.log = S.log ++ [rec] →
      ValidSnapshotTrace pp hCols M w0 (epochs ++ [⟨turnBytes, rec⟩])
        S' (syncSnapshotWorld pp hCols snap S'.world)
/-- Specialization of `ValidSnapshotTrace` to `Replay.deployed`. -/
abbrev DeployedSnapshotTrace (pp : AjtaiParams) (hCols : pp.cols = 64) (w0 : ChunkedWorld.World) :=
  ValidSnapshotTrace pp hCols Replay.deployed w0
theorem validSnapshotTrace_invariants {O : Type} {pp : AjtaiParams} {hCols : pp.cols = 64}
    {M : Log.Machine ChunkedWorld.World O} {w0 : ChunkedWorld.World}
    {epochs : List SnapshotEpoch} {S : Log.Session ChunkedWorld.World}
    {snap : AuthenticatedWorldSnapshot}
    (htr : ValidSnapshotTrace pp hCols M w0 epochs S snap) :
    Log.Reachable Replay.logHash M w0 S ∧ S.log.length = epochs.length ∧
    SnapshotWF pp hCols snap ∧ snap.world = S.world ∧
    snap.verkleRoot = fullVerkleCommitWorld S.world := by
  induction htr with
  | genesis =>
    exact ⟨.genesis, rfl, buildAuthenticatedSnapshot_wf pp hCols w0, rfl,
      buildAuthenticatedSnapshot_verkleRoot pp hCols w0⟩
  | @commitEpoch epochs S S' snap turnBytes rec _ hadm hlog ih =>
    obtain ⟨hreach, hlen, hwf, _, _⟩ := ih
    obtain ⟨hwf', hw', hroot'⟩ := syncSnapshotWorld_wf_and_eq_fullCommit hwf S'.world
    refine ⟨.admit hreach hadm, ?_, hwf', hw', hroot'⟩
    rw [hlog, List.length_append, List.length_append, hlen]; rfl

/-- Pure multi-epoch deterministic machine witnessing non-vacuity of `ValidSnapshotTrace`. -/
def bumpMintedMachine : Log.Machine ChunkedWorld.World Unit where
  step w bs := .ok ({ w with minted := w.minted + bs.length + 1 }, ())
  encW := ChunkedWorld.manifestBytes

/-- **Multi-Epoch Trace Inhabitedness Witness (`validSnapshotTrace_multiEpoch_inhabited`)**. -/
theorem validSnapshotTrace_multiEpoch_inhabited :
    ∃ (epochs : List SnapshotEpoch) (S : Log.Session ChunkedWorld.World)
      (snap : AuthenticatedWorldSnapshot), epochs.length = 2 ∧
      ValidSnapshotTrace defaultChunkAjtaiParams defaultChunkAjtaiParams_cols
        bumpMintedMachine Replay.genesis epochs S snap := by
  let S0 : Log.Session ChunkedWorld.World := ⟨Replay.genesis, []⟩
  let b1 : Log.Bytes := [0x01]
  let b2 : Log.Bytes := [0x02, 0x03]
  let w1 : ChunkedWorld.World := { Replay.genesis with minted := 2 }
  let r1 : Log.Record := ⟨⟨Log.lastHash Replay.logHash genesisSentinel [],
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes Replay.genesis),
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w1), Log.dig Replay.logHash b1⟩, b1⟩
  let S1 : Log.Session ChunkedWorld.World := ⟨w1, [r1]⟩
  let w2 : ChunkedWorld.World := { w1 with minted := 5 }
  let r2 : Log.Record := ⟨⟨Log.lastHash Replay.logHash genesisSentinel [r1],
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w1),
    Log.dig Replay.logHash (ChunkedWorld.manifestBytes w2), Log.dig Replay.logHash b2⟩, b2⟩
  let S2 : Log.Session ChunkedWorld.World := ⟨w2, [r1, r2]⟩
  have ha1 := Log.admit_of_step Replay.logHash bumpMintedMachine (w := Replay.genesis) (w' := w1)
    (o := ()) (prev := Log.lastHash Replay.logHash genesisSentinel []) (b := b1) (by decide) rfl rfl
  have hadm1 : S0.admit Replay.logHash bumpMintedMachine b1 = .ok S1 := by
    unfold Log.Session.admit S0; dsimp only; rw [ha1]; rfl
  have ha2 := Log.admit_of_step Replay.logHash bumpMintedMachine (w := w1) (w' := w2)
    (o := ()) (prev := Log.lastHash Replay.logHash genesisSentinel [r1]) (b := b2) (by decide) rfl rfl
  have hadm2 : S1.admit Replay.logHash bumpMintedMachine b2 = .ok S2 := by
    unfold Log.Session.admit S1; dsimp only; rw [ha2]; rfl
  have tr0 := ValidSnapshotTrace.genesis (pp := defaultChunkAjtaiParams)
    (hCols := defaultChunkAjtaiParams_cols) (M := bumpMintedMachine) (w0 := Replay.genesis)
  exact ⟨[⟨b1, r1⟩, ⟨b2, r2⟩], S2, _, rfl,
    ValidSnapshotTrace.commitEpoch (ValidSnapshotTrace.commitEpoch tr0 hadm1 rfl) hadm2 rfl⟩

/-- **Headline Theorem 3**: across any multi-epoch `ValidSnapshotTrace` and any uncommitted or
    torn WAL tail, `recoverWalSnapshot` truncates the tail, is idempotent, and restores the exact
    committed `ChunkedWorld` and 256-bit `VerkleUmem` root. -/
theorem walCrashReplay_restores_verkle_consistent_world {O : Type}
    {pp : AjtaiParams} {hCols : pp.cols = 64}
    {M : Log.Machine ChunkedWorld.World O} {w0 : ChunkedWorld.World}
    {epochs : List SnapshotEpoch} {S : Log.Session ChunkedWorld.World}
    {snap : AuthenticatedWorldSnapshot}
    (htr : ValidSnapshotTrace pp hCols M w0 epochs S snap) {tornTail : Log.Bytes}
    (htorn : UncommittedWalTail Replay.logHash
      (Log.lastHash Replay.logHash genesisSentinel S.log) tornTail) :
    let crashDisk := Log.encodeAll Replay.logHash S.log ++ tornTail
    let out := recoverWalSnapshot pp hCols M w0 crashDisk
    out.cleanDisk = Log.encodeAll Replay.logHash S.log ∧
    out.committedCount = epochs.length ∧ out.droppedTail = tornTail ∧
    recoverWalBytes (recoverWalBytes crashDisk) = out.cleanDisk ∧
    (recoverWalSnapshot pp hCols M w0 out.cleanDisk).cleanDisk = out.cleanDisk ∧
    (recoverWalSnapshot pp hCols M w0 out.cleanDisk).snapshot = out.snapshot ∧
    SnapshotWF pp hCols out.snapshot ∧ out.snapshot.world = S.world ∧
    out.snapshot.verkleRoot = snap.verkleRoot ∧
    out.snapshot.verkleRoot = fullVerkleCommitWorld S.world := by
  obtain ⟨hreach, hlen, _, _, hsnapRoot⟩ := validSnapshotTrace_invariants htr
  obtain ⟨hlinked, hwfLog⟩ := Log.log_sound hreach
  have hparseEnc := Log.parseFrom_encodeAll Replay.logHash S.log genesisSentinel hlinked hwfLog tornTail
  obtain ⟨htailRecs, htailRest⟩ := parseFrom_uncommittedWalTail Replay.logHash _ htorn
  have hparseFull : (Log.parseFrom Replay.logHash genesisSentinel
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).1 = S.log := by
    rw [hparseEnc, htailRecs, List.append_nil]
  have hparseDrop : (Log.parseFrom Replay.logHash genesisSentinel
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).2.1 = tornTail := by
    rw [hparseEnc]; exact htailRest
  have hreplayEq : Log.replay M w0 S.log = S.world := (Log.state_eq_replay_log hreach).symm
  have hidem := walCrashRecovery_idempotent pp hCols M w0 (Log.encodeAll Replay.logHash S.log ++ tornTail)
  have hbytesIdem := recoverWalBytes_idempotent (Log.encodeAll Replay.logHash S.log ++ tornTail)
  dsimp only
  have hclean : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).cleanDisk =
      Log.encodeAll Replay.logHash S.log := by unfold recoverWalSnapshot; dsimp only; rw [hparseFull]
  have hcnt : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).committedCount = epochs.length := by
    unfold recoverWalSnapshot; dsimp only; rw [hparseFull, hlen]
  have hdrop : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).droppedTail = tornTail := by
    unfold recoverWalSnapshot; dsimp only; exact hparseDrop
  have hsnapEq : (recoverWalSnapshot pp hCols M w0
      (Log.encodeAll Replay.logHash S.log ++ tornTail)).snapshot =
      buildAuthenticatedSnapshot pp hCols S.world := by
    unfold recoverWalSnapshot; dsimp only; rw [hparseFull, hreplayEq]
  refine ⟨hclean, hcnt, hdrop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbytesIdem]; unfold recoverWalBytes; rw [hparseFull, hclean]
  · rw [hidem]
  · rw [hidem]
  · rw [hsnapEq]; exact buildAuthenticatedSnapshot_wf pp hCols S.world
  · rw [hsnapEq]; rfl
  · rw [hsnapEq, buildAuthenticatedSnapshot_verkleRoot, hsnapRoot]
  · rw [hsnapEq, buildAuthenticatedSnapshot_verkleRoot]

end Obend.Vault.VerkleSnapshotBridge

end
