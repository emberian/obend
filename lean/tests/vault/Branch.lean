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

def noLaws (owner : String) (links : List String := []) : PageLaws := ⟨owner, [], links⟩

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

end Obend.Tests.VaultBranch
