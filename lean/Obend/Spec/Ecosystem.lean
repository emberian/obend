module
/-
# Obend.Spec.Ecosystem — names are intentions, hashes are extensions (DESIGN §4)

A package root is a specification; `package Garden extends commons/record@^2, bells@0x…` names
other packages' roots as its parents. The two forms of a parent are the two halves of LTUO §9.3.7:

* `NAME@0xHASH` is an EXTENSION: the release whose content hash is `HASH`, fixed forever;
* `NAME@^MAJOR` is an INTENTION: a slot (`Obend.Slot`) whose candidates are `NAME`'s releases,
  whose chooser is `NAME`'s owner, and whose filling cites one support, "the owner's record names
  version `v` of line `MAJOR` at pin `p`" (`Named`). Resolving it at a view is reading the record
  (`resolve`); a new version is a new pin on the record: a repair offered to every turn that
  resolved the old one, applied to none of them.

The package intention is an instance of the one `Obend.Intention` (`packages`): its pins are `Pin`s,
its supports the record lines they read (`Named`), its resolution `resolve`; `intentionSlot` and
`Pin.current` are that intention's slot and currency, and `stale_iff_blocked` its generic theorem.

Intentions resolve inside a workspace's ECOSYSTEM ROOT (a `View`: the releases it can reach and the
owners' records it reads), not a universal namespace: two workspaces with different views extend
the same intention differently. `close` takes the entry release and resolves every parent root
transitively, choosing one release per intention (a diamond reaches its base once; two routes that
resolve one name to two releases refuse by name), and linearizes the package graph by C4
(`Obend.Spec.C4.linearize`): the entry's precedence list over packages, which the elaborator turns
into one knot of package layers (`Obend.Spec.Elaborate.packageKnot`).

A recorded `Turn` keeps the entry and every pin the closure resolved. `admit` re-derives: a pin that
moved since the turn is `stale`, by its name, before anything is re-derived; with every pin current,
it re-closes and requires the same pins and order. The theorems are `Obend.Spec.Proofs.Ecosystem`.
-/
public import Obend.Spec.Syntax
public import Obend.Spec.C4
public import Obend.Slot
public import Obend.Intention
@[expose] public section
namespace Obend.Spec.Ecosystem
open Obend.Spec.Syntax (ParentRef)
set_option autoImplicit false

/-- A published release of a package: its intention name, version, major line, content hash and
the parent roots its root module declares. -/
structure Release where
  name : String
  version : String
  major : Nat
  hash : String
  parents : List ParentRef
  deriving Inhabited, Repr, DecidableEq

/-- One line of an owner's record: for intention `name`, major line `major`, the version the owner
names (`none` once the owner retired the line) at pin `pin`. -/
structure RecordLine where
  name : String
  major : Nat
  pin : Nat
  fill : Option String
  owner : String
  deriving Inhabited, Repr, DecidableEq

/-- A workspace's ecosystem root: the releases it reaches and the records it reads. -/
structure View where
  releases : List Release
  lines : List RecordLine
  deriving Inhabited, Repr

def View.line (v : View) (name : String) (major : Nat) : Option RecordLine :=
  v.lines.find? fun l => l.name == name && l.major == major

/-- What a turn retains of a resolved root. -/
inductive Pin where
  /-- `name@^major` filled with `version` (content `hash`) because the record named it at `pin` -/
  | intention (name : String) (major pin : Nat) (version hash : String)
  /-- `name@0xhash`: no record is read -/
  | extension (name hash : String)
  deriving Inhabited, Repr, DecidableEq

def Pin.name : Pin → String
  | .intention n .. => n
  | .extension n _ => n

def Pin.hash : Pin → String
  | .intention _ _ _ _ h => h
  | .extension _ h => h

inductive Refusal where
  | unknownIntention (name : String) (major : Nat)
  | retired (name : String) (major pin : Nat)
  | missingRelease (name version : String)
  | outsideLine (name : String) (major : Nat) (version : String)
  | unknownHash (name hash : String)
  /-- two routes resolve one intention to two releases -/
  | incompatible (name first second : String)
  /-- a package is its own ancestor: `first` extends `second`, which reaches `first` -/
  | cycle (first second : String)
  | c4 (package : String) (refusal : Obend.Spec.C4.Refusal)
  | fuel
  /-- the closure's own check (`covered`) failed: a package on the precedence list is unpinned -/
  | unpinned (name : String)
  deriving Inhabited, Repr, DecidableEq

def Refusal.message : Refusal → String
  | .unknownIntention n m => "refused (unknown-intention): " ++ n ++ "@^" ++ toString m ++ " has no record line in this workspace"
  | .retired n m p => "refused (retired): the owner of " ++ n ++ " retired line ^" ++ toString m ++ " at pin " ++ toString p
  | .missingRelease n v => "refused (missing-release): the record of " ++ n ++ " names " ++ v ++ ", which this workspace does not reach"
  | .outsideLine n m v => "refused (outside-line): " ++ n ++ " line ^" ++ toString m ++ " names " ++ v ++ ", whose major is not " ++ toString m
  | .unknownHash n h => "refused (unknown-extension): no release of " ++ n ++ " has content hash 0x" ++ h
  | .incompatible n a b => "refused (incompatible-revisions): " ++ n ++ " is resolved to " ++ a ++ " by one route and " ++ b ++ " by another"
  | .cycle a b => "refused (package-cycle): " ++ a ++ " extends " ++ b ++ ", which extends " ++ a
  | .c4 p r => "refused (package-precedence): C4 linearization of " ++ p ++ " refused: " ++ r.message
  | .fuel => "refused (closure-fuel)"
  | .unpinned n => "refused (unpinned): " ++ n ++ " is on the precedence list but no pin resolved it"

/-! ## An intention is a slot -/

/-- The support an intention's fill cites: the owner's record names `version` on line `major` of
`name` at pin `pin`. -/
structure Named where
  name : String
  major : Nat
  pin : Nat
  version : String
  deriving Inhabited, Repr, DecidableEq

/-- Whether the record at view `v` says what `f` says. -/
def holds (v : View) (f : Named) : Bool :=
  match v.line f.name f.major with
  | some l => l.pin == f.pin && l.fill == some f.version
  | none => false

/-! ## Resolution -/

/-- Resolve one parent root at a view: an intention reads its record line and takes the release it
names (the fill), an extension takes the release with its hash. -/
def resolve (v : View) : ParentRef → Except Refusal (Release × Pin)
  | .intention n major =>
    match v.line n major with
    | none => .error (.unknownIntention n major)
    | some l =>
      match l.fill with
      | none => .error (.retired n major l.pin)
      | some version =>
        match v.releases.find? (fun r => r.name == n && r.version == version) with
        | none => .error (.missingRelease n version)
        | some r =>
          if r.major == major then .ok (r, .intention n major l.pin version r.hash)
          else .error (.outsideLine n major version)
  | .extension n h =>
    match v.releases.find? (fun r => r.name == n && r.hash == h) with
    | none => .error (.unknownHash n h)
    | some r => .ok (r, .extension n h)

/-- The parent a pin resolves. -/
def Pin.ref : Pin → ParentRef
  | .intention n m _ _ _ => .intention n m
  | .extension n h => .extension n h

/-- What a pin cites: an intention, the record line it read; an extension, nothing. -/
def Pin.supports : Pin → List Named
  | .intention n m p v _ => [⟨n, m, p, v⟩]
  | .extension _ _ => []

theorem resolve_ref (v : View) (r : ParentRef) (rel : Release) (p : Pin) (h : resolve v r = .ok (rel, p)) :
    p.ref = r := by
  cases r with
  | intention n major =>
    simp only [resolve] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; rfl
          · cases h
  | extension n hash =>
    simp only [resolve] at h
    split at h
    · cases h
    · cases h; rfl

theorem resolve_holds (v : View) (r : ParentRef) (rel : Release) (p : Pin) (h : resolve v r = .ok (rel, p)) :
    ∀ f ∈ p.supports, holds v f = true := by
  cases r with
  | intention n major =>
    simp only [resolve] at h
    split at h
    · cases h
    · rename_i l hl
      split at h
      · cases h
      · rename_i version hv
        split at h
        · cases h
        · split at h
          · cases h
            intro f hf
            simp only [Pin.supports, List.mem_cons, List.not_mem_nil, or_false] at hf
            subst hf
            simp [holds, hl, hv]
          · cases h
  | extension n hash =>
    simp only [resolve] at h
    split at h
    · cases h
    · cases h; intro f hf; cases hf

/-- **The package intention** (`Obend.Intention`): a parent root resolved at a workspace's view. Its
pins are what a turn retains, an intention pin cites the record line it read, an extension pin
nothing; resolving is reading the record. -/
def packages : Obend.Intention View ParentRef Pin Named Refusal where
  ref := Pin.ref
  supports := Pin.supports
  holds := holds
  resolve v r := (resolve v r).map (·.2)
  resolve_ref v r p h := by
    cases hr : resolve v r with
    | error e => rw [hr] at h; cases h
    | ok x => rw [hr] at h; cases h; exact resolve_ref v r x.1 x.2 hr
  resolve_holds v r p h := by
    cases hr : resolve v r with
    | error e => rw [hr] at h; cases h
    | ok x => rw [hr] at h; cases h; exact resolve_holds v r x.1 x.2 hr

/-- The slot of intention `name@^major`: its candidates are fills (pins), a fill cites the record
line it read, and its judge is the line (a fill of another intention or major is rejected). -/
def intentionSlot (name : String) (major : Nat) : Obend.Slot.Slot Named Pin :=
  packages.slot (.intention name major)

/-- A pin is CURRENT at a view when the record still names the same version at the same pin. An
extension pin reads no record, so it is current at every view. -/
def Pin.current (v : View) (p : Pin) : Bool := packages.current v p

/-- A closure under construction: the release chosen for each package (the entry's first), every
pin resolved, and each visited package's precedence list. -/
structure Closure where
  entry : Release
  chosen : List Release
  pins : List Pin
  precedence : List (String × List String)
  /-- the entry's precedence list over packages, most specific first -/
  order : List String := []
  deriving Inhabited, Repr, DecidableEq

/-- Record a resolved parent: the first release chosen for a name stays chosen; another route to the
same name must reach the same content. -/
def choose (cl : Closure) (r : Release) (pin : Pin) : Except Refusal Closure :=
  let pins := if cl.pins.contains pin then cl.pins else cl.pins ++ [pin]
  match cl.chosen.find? (·.name == r.name) with
  | some prior =>
    if prior.hash == r.hash then .ok { cl with pins } else .error (.incompatible r.name prior.version r.version)
  | none => .ok { cl with chosen := cl.chosen ++ [r], pins }

def packageGraph (cl : Closure) : Obend.Spec.C4.Graph :=
  ⟨fun k => (cl.precedence.lookup k).getD [k], fun _ => false⟩

mutual
/-- Visit a release: resolve its parents, visit each, then linearize it over them. `stack` is the
path of packages being visited, for the cycle refusal. -/
def visit (v : View) : Nat → List String → Closure → Release → Except Refusal Closure
  | 0, _, _, _ => .error .fuel
  | fuel + 1, stack, cl, r =>
    if (cl.precedence.lookup r.name).isSome then .ok cl
    else if stack.contains r.name then .error (.cycle (stack.headD r.name) r.name)
    else do
      let cl ← visitParents v fuel (r.name :: stack) cl r.parents
      match Obend.Spec.C4.linearize (packageGraph cl) [r.name] [r.parents.map ParentRef.name] with
      | .ok (l, _) => .ok { cl with precedence := cl.precedence ++ [(r.name, l)] }
      | .error e => .error (.c4 r.name e)

def visitParents (v : View) : Nat → List String → Closure → List ParentRef → Except Refusal Closure
  | 0, _, _, _ => .error .fuel
  | _ + 1, _, cl, [] => .ok cl
  | fuel + 1, stack, cl, ref :: rest => do
    let (r, pin) ← resolve v ref
    let cl ← choose cl r pin
    let cl ← visit v fuel stack cl r
    visitParents v fuel stack cl rest
end

/-- Every package on the precedence list other than the entry is pinned, every chosen release is on
it, and every pin is current: the check `close` makes before it returns. -/
def covered (v : View) (entry : String) (cl : Closure) (order : List String) : Option Refusal :=
  match order.find? (fun n => n != entry && !cl.pins.any (·.name == n)) with
  | some n => some (.unpinned n)
  | none =>
    match cl.chosen.find? (fun r => !order.contains r.name) with
    | some r => some (.unpinned r.name)
    | none =>
      match cl.pins.find? (fun p => !p.current v) with
      | some p => some (.unpinned p.name)
      | none => none

/-- The workspace closure of `entry` at view `v`. -/
def close (v : View) (entry : Release) : Except Refusal Closure := do
  -- A recursion path visits each package at most once (the cycle check) and walks at most every
  -- parent list once per package on it: the fuel is that bound, from the input.
  let parentCount := ((entry :: v.releases).map (·.parents.length)).sum
  let fuel := 2 * (v.releases.length + 2) * (v.releases.length + parentCount + 2)
  let cl ← visit v fuel [] ⟨entry, [entry], [], [], []⟩ entry
  let order := (cl.precedence.lookup entry.name).getD [entry.name]
  match covered v entry.name cl order with
  | some refusal => .error refusal
  | none => .ok { cl with entry, order }

/-! ## Turns -/

/-- What a recorded turn retains of its workspace: the entry, every pin it resolved, the order. -/
structure Turn where
  entry : Release
  pins : List Pin
  order : List String
  deriving Inhabited, Repr, DecidableEq

def Closure.turn (cl : Closure) : Turn := ⟨cl.entry, cl.pins, cl.order⟩

inductive Admission where
  | admitted (cl : Closure)
  /-- a pin moved since the turn: named -/
  | stale (pin : Pin)
  /-- re-closing refused -/
  | refused (r : Refusal)
  /-- every pin current, yet the re-derived closure differs (the record grew a parent the turn did
  not resolve) -/
  | diverged
  deriving Inhabited, Repr, DecidableEq

/-- Admission re-derives the turn's closure at the view: a moved pin is stale by name; otherwise the
closure at the view must be the turn's. -/
def admit (v : View) (t : Turn) : Admission :=
  match t.pins.find? (fun p => !p.current v) with
  | some p => .stale p
  | none =>
    match close v t.entry with
    | .error r => .refused r
    | .ok cl => if cl.pins == t.pins && cl.order == t.order then .admitted cl else .diverged

/-- A step of the records: every line persists, its pin never goes back, and a retired line stays
retired (nano's `stale_behind_forever`, the tombstone case). -/
def Step (v v' : View) : Prop :=
  ∀ n m l, v.line n m = some l → ∃ l', v'.line n m = some l' ∧ l.pin ≤ l'.pin ∧ (l.fill = none → l'.fill = none)

end Obend.Spec.Ecosystem

end
