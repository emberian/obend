import Obend.Vault.Branch

/-!
# The branch walkthrough: two stores fork from one, post offline, and merge at the tip

`Obend.Vault.Branch`'s gate. One base store with five pages and two sturdyrefs; alice forks `left`,
bob forks `right`; each posts offline, and each branch's own run admits everything it posted. Then
they merge:

* alice's `Alpha` and bob's `Beta` (disjoint) land as one receipted history after the base's;
* both wrote `Shared`: a conflict, kept in the tip's state with both candidates, neither landed;
  `resolve` lands alice's and names bob's as dropped;
* alice's write of `board/Bob` relied on `sr:board`, which bob revoked on his branch: refused at the
  tip, by name, though her own branch admitted it;
* alice gave `Ledger` a law over its links (`dated: not (linked.date == 0)`) listing `notes/Gamma`;
  bob, on his branch, undated `notes/Gamma`: refused at the tip by `Ledger: dated`, alice's law,
  judged at `notes/Gamma`.

Then the refusal channel `Obend.Vault.Branch` names and does not close: a write whose law over links
reads a hidden page lands or not by that page's state.

Planted mutation (run by hand when this file was written): `authRefusal` made to return `none`
always (the tip check removed) turns the `board/Bob` guards red. `#guard`s are tests, not theorems.
-/

namespace Obend.Tests.VaultBranch

open Obend.Vault Obend.Vault.Branch
open Obend.Core.Data (Data)

def rec1 (f : String) (n : Nat) : Data := .record [(f, .natural n)]

def ok? {α : Type} (d : α) : Except String α → α
  | .ok a => a
  | .error _ => d

def noLaws (owner : String) (links : List String := []) : PageLaws := { owner := owner, links := links }

/-- A sturdyref granting a write of `cell`. -/
def srWrite (uri cell : String) : Rehydration.Sturdyref Data :=
  { uri := uri, surface := [], log := [], lineage := { held := [.write], permits := fun _ => true },
    cellId := cell }

def baseStore : VaultStore := fun c =>
  if c == "notes/Alpha" then some (rec1 "count" 1)
  else if c == "notes/Beta" then some (rec1 "count" 1)
  else if c == "Shared" then some (rec1 "v" 0)
  else if c == "board/Bob" then some (rec1 "posts" 0)
  else if c == "notes/Gamma" then some (rec1 "date" 3)
  else if c == "Ledger" then some (rec1 "date" 1)
  else none

def baseBook : LawBook :=
  [("notes/Alpha", noLaws "alice"), ("notes/Beta", noLaws "bob"), ("Shared", noLaws "alice"),
   ("board/Bob", noLaws "bob"), ("notes/Gamma", noLaws "bob"), ("Ledger", noLaws "alice")]

def base : Config :=
  { store := baseStore, book := baseBook,
    auth := { refs := [srWrite "sr:board" "board/Bob", srWrite "sr:shared" "Shared"] },
    history := [⟨0, "genesis", "open", []⟩] }

/-- A write of one page, from `o` to `n`, read at nothing else. -/
def w1 (label actor page : String) (o n : Data) (relies : List String := []) : Act :=
  .write { label := label, actor := actor, turn := writeTurn page o n [] (.record []), relies := relies }

def ledgerLaws : PageLaws :=
  ok? (noLaws "alice") (PageLaws.ofLines "Ledger" "alice" ["notes/Gamma"] [("dated", "not (linked.date == 0)")])

def left : Branch :=
  ((((fork base "left").post (w1 "alpha" "alice" "notes/Alpha" (rec1 "count" 1) (rec1 "count" 2))).post
    (w1 "shared-a" "alice" "Shared" (rec1 "v" 0) (rec1 "v" 1))).post
    (w1 "post-on-board" "alice" "board/Bob" (rec1 "posts" 0) (rec1 "posts" 1) ["sr:board"])).post
    (.relaw "list-gamma" "alice" "Ledger" ledgerLaws)

def right : Branch :=
  ((((fork base "right").post (w1 "beta" "bob" "notes/Beta" (rec1 "count" 1) (rec1 "count" 5))).post
    (w1 "shared-b" "bob" "Shared" (rec1 "v" 0) (rec1 "v" 2) ["sr:shared"])).post
    (.revoke "revoke-board" "bob" "sr:board")).post
    (w1 "undate-gamma" "bob" "notes/Gamma" (rec1 "date" 3) (rec1 "date" 0))

/-! ## Offline, each branch admits all it posted -/

#guard (left.run base).refused.isEmpty
#guard (right.run base).refused.isEmpty
#guard (left.run base).landed.map (·.2.label) == ["alpha", "shared-a", "post-on-board", "list-gamma"]
#guard (right.run base).landed.map (·.2.label) == ["beta", "shared-b", "revoke-board", "undate-gamma"]

/-! ## The merge -/

def merged : Merged := ok? ⟨base, [], [], []⟩ (merge base left right)

#guard (merge base left right).toBool

def natOf (s : VaultStore) (c f : String) : Option Nat := (s c).map (natAt · f)

def refusalOf (label : String) : Option String :=
  (merged.refused.find? (·.2.1 == label)).map (·.2.2.text)

-- the disjoint turns land as one receipted history, after the base's
#guard merged.tip.history.map (fun r => (r.seq, r.origin, r.label)) ==
  [(0, "genesis", "open"), (1, "left", "list-gamma"), (2, "right", "revoke-board"),
   (3, "left", "alpha"), (4, "right", "beta")]
#guard natOf merged.tip.store "notes/Alpha" "count" == some 2
#guard natOf merged.tip.store "notes/Beta" "count" == some 5

-- the conflicting pair is a conflict state: both candidates kept, neither landed, Shared at its base
#guard merged.tip.conflicts.map Conflict.text ==
  ["conflict at Shared: left's shared-a and right's shared-b (both kept as candidates; neither landed)"]
#guard natOf merged.tip.store "Shared" "v" == some 0
#guard !(merged.landed.any (·.2.label == "shared-a")) && !(merged.landed.any (·.2.label == "shared-b"))

-- the turn relying on the revoked sturdyref is refused at the tip, by name
#guard refusalOf "post-on-board" ==
  some "relied on the sturdyref sr:board, revoked at the tip by right's revoke-board"
#guard natOf merged.tip.store "board/Bob" "posts" == some 0

-- the law over links alice wrote refuses bob's write, by name: the law, whose, and the page
#guard refusalOf "undate-gamma" ==
  some "refused by Ledger: dated (alice's law `not (linked.date == 0)`), judged at notes/Gamma"
#guard natOf merged.tip.store "notes/Gamma" "date" == some 3

-- nothing else was refused
#guard merged.refused.map (·.2.1) == ["post-on-board", "undate-gamma"]

/-! ## Resolving the conflict lands one candidate and names the dropped one -/

def resolved : Config := ok? base (resolve merged.tip 0 .left)

#guard (resolve merged.tip 0 .left).toBool
#guard natOf resolved.store "Shared" "v" == some 1
#guard resolved.conflicts.isEmpty
#guard resolved.history.getLast?.map (·.label) == some "shared-a (resolving; dropped right's shared-b)"

/-! ## The channel left open: a law over links into a hidden page

`P` links to `hidden/H` with a law over its links. Two bases differ only at `hidden/H`, which the
left's membrane does not show. The left's write of `P` lands against one and is refused against the
other: whether it lands tells the left something of `hidden/H`. `merge_confines_hidden` assumes the
left's writes access no hidden cell; a page they write linking into one is exactly this. -/

def probeLaws : PageLaws :=
  ok? (noLaws "alice") (PageLaws.ofLines "P" "alice" ["hidden/H"] [("open", "not (linked.ok == 0)")])

def probeBase (hidden : Nat) : Config :=
  { store := fun c => if c == "P" then some (rec1 "n" 0) else if c == "hidden/H" then some (rec1 "ok" hidden)
      else none,
    book := [("P", probeLaws), ("hidden/H", noLaws "bob")] }

def probe (hidden : Nat) : Merged :=
  ok? ⟨probeBase 0, [], [], []⟩ (merge (probeBase hidden)
    ((fork (probeBase hidden) "left").post (w1 "probe" "alice" "P" (rec1 "n" 0) (rec1 "n" 1)))
    (fork (probeBase hidden) "right"))

#guard (probe 1).refused.isEmpty
#guard (probe 0).refused.map (·.2.2.text) ==
  ["refused by P: open (alice's law `not (linked.ok == 0)`), judged at hidden/H"]

/-! ## Their laws agree: a counter both sides incremented merges by its law

`Counter` declares `merge count: add` and its laws (`monotone(count)`, `not (new.count <= 0)`) are
I-confluent for it; `Capped` declares the same merge but its law `new.count <= 5` (an upper bound
under `add`) is not, so its two writes stay a conflict. `Same` has no declaration; both sides made
the same write, and it lands once. -/

def lawsOf (page owner : String) (lines : List (String × String)) (merges : List (String × MergeKind)) :
    PageLaws :=
  { ok? (noLaws owner) (PageLaws.ofLines page owner [] lines) with merges := merges }

def base2 : Config :=
  { store := fun c => if c == "Counter" || c == "Capped" then some (rec1 "count" 1)
      else if c == "Same" then some (rec1 "v" 0) else none,
    book := [("Counter", lawsOf "Counter" "alice" [("up", "monotone(count)"), ("pos", "not (new.count <= 0)")]
                [("count", .add)]),
             ("Capped", lawsOf "Capped" "alice" [("cap", "new.count <= 5")] [("count", .add)]),
             ("Same", noLaws "alice")],
    auth := { refs := [srWrite "sr:counter" "Counter", srWrite "sr:capped" "Capped", srWrite "sr:same" "Same"] },
    history := [⟨0, "genesis", "open", []⟩] }

def left2 : Branch :=
  (((fork base2 "left").post (w1 "inc-a" "alice" "Counter" (rec1 "count" 1) (rec1 "count" 3))).post
    (w1 "cap-a" "alice" "Capped" (rec1 "count" 1) (rec1 "count" 3))).post
    (w1 "same-a" "alice" "Same" (rec1 "v" 0) (rec1 "v" 7))

def right2 : Branch :=
  (((fork base2 "right").post (w1 "inc-b" "bob" "Counter" (rec1 "count" 1) (rec1 "count" 4) ["sr:counter"])).post
    (w1 "cap-b" "bob" "Capped" (rec1 "count" 1) (rec1 "count" 4) ["sr:capped"])).post
    (w1 "same-b" "bob" "Same" (rec1 "v" 0) (rec1 "v" 7) ["sr:same"])

-- every law line above parses (a line that did not would leave its page lawless)
#guard (PageLaws.ofLines "Counter" "alice" [] [("up", "monotone(count)"), ("pos", "not (new.count <= 0)")]).toBool
#guard (PageLaws.ofLines "Capped" "alice" [] [("cap", "new.count <= 5")]).toBool
#guard (PageLaws.ofLines "H" "bob" [] [("late", "new.x <= ledger.height")]).toBool
#guard ledgerLaws.laws.length == 1 && probeLaws.laws.length == 1

def merged2 : Merged := ok? ⟨base2, [], [], []⟩ (merge base2 left2 right2)

-- the counter: 1 + (3 - 1) + (4 - 1), one receipt for the pair
#guard natOf merged2.tip.store "Counter" "count" == some 6
-- the same write on both sides lands once
#guard natOf merged2.tip.store "Same" "v" == some 7
#guard merged2.tip.history.map (fun r => (r.origin, r.label)) ==
  [("genesis", "open"), ("left+right", "inc-a + inc-b"), ("left+right", "same-a + same-b")]
-- the capped counter's law is not I-confluent for `add`: a conflict, at its base
#guard merged2.tip.conflicts.map Conflict.text ==
  ["conflict at Capped: left's cap-a and right's cap-b (both kept as candidates; neither landed)"]
#guard natOf merged2.tip.store "Capped" "count" == some 1
#guard merged2.refused.isEmpty

/-! ## The authority reason is never hidden behind a stale pin

alice's write of `board/Bob` read a state bob's page never had (`posts 9`), and relied on `sr:board`,
which bob revoked: the refusal names the revoked sturdyref first, and the stale pin after it. -/

def left3 : Branch :=
  (fork base "left").post (w1 "stale-post" "alice" "board/Bob" (rec1 "posts" 9) (rec1 "posts" 10) ["sr:board"])

def right3 : Branch := (fork base "right").post (.revoke "revoke-board" "bob" "sr:board")

#guard ((ok? ⟨base, [], [], []⟩ (merge base left3 right3)).refused.map (·.2.2.text)) ==
  ["relied on the sturdyref sr:board, revoked at the tip by right's revoke-board; and stale: it read board/Bob as it was on its branch (posts 9 → 0)"]

/-! ## Order: where `merge base L R` and `merge base R L` differ

The tip settles the non-write acts left first. One side grants `sr:g`, the other revokes it: with the
grant on the left the revocation lands, with it on the right the revocation finds nothing to revoke.
So the tip's authority depends on which side is called left. -/

def baseG : Config :=
  { store := fun c => if c == "G" then some (rec1 "n" 0) else none, book := [("G", noLaws "bob")] }

def grantL : Branch := (fork baseG "granting").post (.grant "grant-g" "bob" (srWrite "sr:g" "G"))
def revokeR : Branch := (fork baseG "revoking").post (.revoke "revoke-g" "bob" "sr:g")

#guard ((ok? ⟨baseG, [], [], []⟩ (merge baseG grantL revokeR)).tip.auth.live "sr:g") == false
#guard ((ok? ⟨baseG, [], [], []⟩ (merge baseG revokeR grantL)).tip.auth.live "sr:g") == true
#guard ((ok? ⟨baseG, [], [], []⟩ (merge baseG revokeR grantL)).refused.map (·.2.2.text)) ==
  ["relied on sr:g, which no one granted here"]

/-! A write is judged at the height of the history when it lands, and the left's writes land first.
`H`'s law `new.x <= ledger.height` admits bob's write when it lands second (height 2) and refuses it
when it lands first (height 1). -/

def baseH : Config :=
  { store := fun c => if c == "H" then some (rec1 "x" 0) else if c == "A" then some (rec1 "n" 0) else none,
    book := [("H", lawsOf "H" "bob" [("late", "new.x <= ledger.height")] []), ("A", noLaws "alice")],
    history := [⟨0, "genesis", "open", []⟩] }

def writeA : Branch := (fork baseH "a").post (w1 "a" "alice" "A" (rec1 "n" 0) (rec1 "n" 1))
def writeH : Branch := (fork baseH "h").post (w1 "h" "bob" "H" (rec1 "x" 0) (rec1 "x" 2))

#guard ((ok? ⟨baseH, [], [], []⟩ (merge baseH writeA writeH)).refused.isEmpty)
#guard ((ok? ⟨baseH, [], [], []⟩ (merge baseH writeH writeA)).refused.map (·.2.1)) == ["h"]

end Obend.Tests.VaultBranch
