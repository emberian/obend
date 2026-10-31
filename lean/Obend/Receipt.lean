module
/-
# Obend.Receipt — the receipt type

`review/GENERALIZATION-20261031.md` G4; `review/GENERATED-20261031.md` §0 (the inventory found no
receipt type) and §2.4; `review/VISION-CLAUDE-20261031.md` §8. A receipt is a claim with evidence:

    { pre post : Root; row; law : Digest; pins : List (Cell × Option Pin); openings; verdict;
      quantifier : Shape; trust : per support, checked | attested; dated : View; proofs; prev : Digest }

`dated` is the VIEW: the root of the Merkle map the ledger's view commits (`Obend.Receipt.Merkle`),
and `proofs` are the openings of what the row read against it.

- `Outcome`: a judge's verdict (`ok | refused clause path | uncovered`) and Astra's refusal outcomes
  (`noAdmissible | awaitingChoice | preferenceKept | candidateRejected | staleEvidence |
  executionFrozen`, `astra/ASTRA-SELECTION-20261031.md` line 225), which a selection reports and a
  judge does not.
- `Trust` is per support; `Receipt.overall` is `attested` as soon as one support is, and names it.
  A verifier does not read the ceiling off the list: `ceiling` derives it from the supports the
  verifier ran, refusing a missing one (so `[]` is never `checked`) and a `checked` claim it did not
  run (`ceiling_checked`, `ceiling_empty`).
- `issue`: the receipt of one row of an audited fold (`Obend.Fold.Admission`). `receipt_sufficient`
  (`Obend.Fold.receipt_sufficient`, restated): at any world agreeing with the receipt's openings, the
  row is judged as the receipt says and reaches its `post` root; `recheck` is what a stranger runs,
  and `recheck_issued` says it accepts every honestly issued receipt at every such world. `recheck`
  computes that the openings cover the row's reads (`recheck_covers`), so `dated_sound` holds of ANY
  receipt the stranger accepts, not only an issued one.
- With a `World` (`Obend.Slot.World`): the openings are COMPUTED from the pins by `holdsOfPin`
  (`openings_of_pins`, `rfl`), and equal pins suffice (`pins_sufficient`).
- Dated openings (`datedOpens`, `Reading`, `Reading.matched`): each opening of the receipt is
  matched by a proof that opens against `dated` at its key's position. `openings_checked`: when
  `dated` is the root of a world's view, the openings are that world's, or the hash collides;
  `dated_verdict`: the receipt's verdict and post root are the row's at that world, or the hash
  collides. So the view a receipt read is a CHECKED support: a stranger holding the root needs no
  word from the host. `issue_checks`: an honestly issued receipt passes both checks.
- `chained`: each receipt names its predecessor's digest; under a binding digest a verified chain is
  determined by its head and length (`chain_binds`).
- The disclosure dial (`GENERATED` §2.4): `full` (the log, replayed by a follower), `cited` (the
  receipt with its openings, re-checked: `accepts_cited_sound`), `bit` (the roots and one bit, the
  only setting that trusts the producer). `dial_invariant`: for an honest receipt the bit is the same
  at all three.
-/
public import Obend.Fold
public import Obend.Judge.Class
public import Obend.Slot.World
public import Obend.Receipt.Merkle

@[expose] public section
namespace Obend.Receipt
open Obend.Fold
open Obend.Slot (World)
set_option autoImplicit false

abbrev Digest := String

/-- The quantifier shape of what a receipt claims (`astra/ASTRA-VISION-20261031.md` §5.1,
`GENERALIZATION` §1.4). -/
inductive Shape where
  /-- this run happened and was admitted: `∃M ∃run` -/
  | existsRun
  /-- one plan survives every declared model and run: `∃plan ∀M ∀r` -/
  | planForAll
  /-- a policy survives: `∃policy ∀M ∀r` -/
  | policyForAll
  /-- for every model some plan: `∀M ∃plan` -/
  | forAllPlan
  /-- an identity over every input -/
  | forAll
  deriving DecidableEq, Repr

/-- The trust of one support. -/
inductive Trust where
  /-- a certificate checked by a registered format, with what its run trusts -/
  | checked (format version : String) (base : Judge.TrustBase)
  /-- a named party's say-so, at its revision -/
  | attested (principal revision : String)
  deriving DecidableEq, Repr

/-- What a receipt reports. -/
inductive Outcome (Clause : Type) where
  | ok
  | refused (clause : Clause) (path : List Nat)
  | uncovered
  /-- no candidate was admissible among those searched (not: none exists) -/
  | noAdmissible
  /-- the chooser must choose; nothing is unusable -/
  | awaitingChoice
  /-- a preference kept the incumbent; no support failed -/
  | preferenceKept
  /-- the candidate was judged and rejected -/
  | candidateRejected
  /-- the evidence the decision cited is stale at this view -/
  | staleEvidence
  /-- the execution is frozen at a recorded dispatch -/
  | executionFrozen
  deriving DecidableEq, Repr

namespace Outcome
variable {Clause : Type}

def ofVerdict : Judge.Verdict Clause → Outcome Clause
  | .ok => .ok
  | .refused k p => .refused k p
  | .uncovered => .uncovered

def ofExcept {α : Type} : Except Clause α → Outcome Clause
  | .ok _ => .ok
  | .error k => .refused k []

def isOk : Outcome Clause → Bool
  | .ok => true
  | _ => false

theorem ofVerdict_ok {v : Judge.Verdict Clause} : (ofVerdict v).isOk = true ↔ v = .ok := by
  cases v <;> simp [ofVerdict, isOk]

theorem ofExcept_isOk {α : Type} (x : Except Clause α) : (ofExcept x).isOk = x.toBool := by
  cases x <;> rfl

end Outcome

/-- **A receipt.** -/
structure Receipt (Cell Pin Fact Clause : Type) where
  /-- the accumulator's root before and after the row -/
  pre : Digest
  post : Digest
  /-- the row's digest -/
  row : Digest
  /-- the effective law's identity -/
  law : Digest
  /-- the pins of the cells the row read -/
  pins : List (Cell × Option Pin)
  /-- what the row read, with its value -/
  openings : List (Fact × Bool)
  verdict : Outcome Clause
  quantifier : Shape
  /-- each support's trust, by name -/
  trust : List (String × Trust)
  /-- the VIEW it was issued at: the root of the ledger view's commitment (`Merkle.Commit.dated`),
  never a local clock -/
  dated : Nat
  /-- the openings of what the row read, against `dated` -/
  proofs : List Merkle.Opening
  /-- the producer's previous receipt -/
  prev : Digest
  deriving Repr

namespace Receipt
variable {Cell Pin Fact Clause : Type}

/-- Per-support trust, as a whole: checked when every support is, else attested by the first
attested support, named. -/
def overall (R : Receipt Cell Pin Fact Clause) : Option (String × Trust) :=
  R.trust.find? fun p => match p.2 with
    | .attested .. => true
    | .checked .. => false

theorem overall_none_checked (R : Receipt Cell Pin Fact Clause) (h : R.overall = none) :
    ∀ s ∈ R.trust, ∃ f v b, s.2 = .checked f v b := by
  intro s hs
  have := List.find?_eq_none.1 h s hs
  revert this
  cases s.2 with
  | checked f v b => exact fun _ => ⟨f, v, b, rfl⟩
  | attested p r => simp

end Receipt

def Trust.isAttested : Trust → Bool
  | .attested .. => true
  | .checked .. => false

/-- A support the verifier ran, as the receipt names it: present, at the mode it ran or lower. -/
def namedAsRun (claimed : List (String × Trust)) (s : String × Trust) : Bool :=
  match claimed.lookup s.1 with
  | some t' => t' == s.2 || t'.isAttested
  | none => false

/-- A support the receipt names: one the verifier ran, or attested by a named principal. -/
def standsBehind (ran : List (String × Trust)) (c : String × Trust) : Bool :=
  (ran.lookup c.1).isSome || c.2.isAttested

/-- Why a receipt's support list is refused, if it is. -/
def ceilingRefusal (ran claimed : List (String × Trust)) : Option String :=
  match ran.find? (fun s => !namedAsRun claimed s) with
  | some (s, _) => some (match claimed.lookup s with
      | none => s!"trust: the support {s} has no entry"
      | some _ => s!"trust: the support {s} claims a check this verifier does not run")
  | none => match claimed.find? (fun c => !standsBehind ran c) with
    | some (s, _) => some s!"trust: the support {s} claims checked, and this verifier runs no check for it"
    | none => none

/-- **The trust ceiling a verifier derives.** `ran` is what the verifier itself checked, by support
name and mode; `claimed` is the receipt's list. Every support the verifier ran must be named by the
receipt, at the mode it ran or lower (`attested`); a support the receipt names that the verifier did
not run must be `attested`, by a named principal: a `checked` claim no check stands behind is refused.
The ceiling is the first attested entry, else `none` (checked throughout). So an empty list never
reads as `checked` when the verifier ran anything: each of its supports is missing. -/
def ceiling (ran claimed : List (String × Trust)) : Except String (Option (String × Trust)) :=
  match ceilingRefusal ran claimed with
  | some e => .error e
  | none => .ok (claimed.find? fun p => p.2.isAttested)

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] : ∀ {l : List (α × β)} {a : α} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (k, v) :: rest, a, b, h => by
    by_cases e : a = k
    · subst e; simp [List.lookup] at h; subst h; simp
    · have : (a == k) = false := by simpa using e
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **A `checked` ceiling is earned**: every support the verifier ran is named by the receipt at
exactly the mode it ran, and nothing the receipt names is attested. With `ran` nonempty, the
receipt's list is nonempty. -/
theorem ceiling_checked {ran claimed : List (String × Trust)} (h : ceiling ran claimed = .ok none) :
    (∀ s ∈ ran, claimed.lookup s.1 = some s.2) ∧ ∀ c ∈ claimed, c.2.isAttested = false := by
  unfold ceiling at h
  split at h
  · cases h
  rename_i hr
  simp only [Except.ok.injEq] at h
  have none_att : ∀ c ∈ claimed, c.2.isAttested = false := by
    intro c hc
    have := List.find?_eq_none.1 h c hc
    simpa using this
  refine ⟨fun s hs => ?_, none_att⟩
  unfold ceilingRefusal at hr
  split at hr
  · cases hr
  rename_i hf
  have := List.find?_eq_none.1 hf s hs
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, namedAsRun] at this
  revert this
  cases hl : claimed.lookup s.1 with
  | none => simp
  | some t' =>
    have hatt := none_att _ (lookup_mem hl)
    simp only at hatt
    simp [hatt]

/-- The empty list is refused whenever the verifier ran a support. -/
theorem ceiling_empty {ran : List (String × Trust)} (h : ran ≠ []) : ∃ e, ceiling ran [] = .error e := by
  cases ran with
  | nil => exact absurd rfl h
  | cons s rest =>
    simp [ceiling, ceilingRefusal, namedAsRun]

/-! ## The receipt of a row of an audited fold -/

section Fold
variable {W Rest Row Fact Clause Cell Pin : Type}

/-- What a producer signs into a receipt besides the fold: how roots, rows and pins are named. -/
structure Naming (W Rest Row Fact Cell Pin : Type) where
  root : Rest → Digest
  rowDigest : Row → Digest
  law : Digest
  pinsOf : W → List Fact → List (Cell × Option Pin)
  /-- the view's root at a world -/
  dated : W → Nat
  /-- the openings of the facts read, against the root -/
  proofsOf : W → List Fact → List Merkle.Opening

/-- The receipt of row `r` judged at accumulator `a`. -/
def issue (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a : W × Rest) (r : Row)
    (quantifier : Shape) (trust : List (String × Trust)) (prev : Digest) :
    Receipt Cell Pin Fact Clause where
  pre := N.root a.2
  post := match A.step a r with
    | .ok b => N.root b.2
    | .error _ => N.root a.2
  row := N.rowDigest r
  law := N.law
  pins := N.pinsOf a.1 (A.reads a r)
  openings := A.openings a r
  verdict := Outcome.ofExcept (A.step a r)
  quantifier := quantifier
  trust := trust
  dated := N.dated a.1
  proofs := N.proofsOf a.1 (A.reads a r)
  prev := prev

/-- The post root a step reaches. -/
def postOf (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a : W × Rest) (r : Row) : Digest :=
  match A.step a r with
  | .ok b => N.root b.2
  | .error _ => N.root a.2

/-- **A receipt suffices** (`Obend.Fold.receipt_sufficient`): at any world agreeing with the
receipt's openings, the row is judged as the receipt says, reaching its post root. -/
theorem receipt_sufficient (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) {q : Shape} {t : List (String × Trust)} {p : Digest}
    (w' : W) (hw : ∀ o ∈ (issue A N a r q t p).openings, A.look w' o.1 = o.2) :
    Outcome.ofExcept (A.step (w', a.2) r) = (issue A N a r q t p).verdict ∧
      postOf A N (w', a.2) r = (issue A N a r q t p).post := by
  have h := Fold.receipt_sufficient A a r hm w' hw
  simp only [issue, postOf]
  rw [h]
  cases A.step a r <;> exact ⟨rfl, rfl⟩

/-- What a stranger runs: the receipt names the row being replayed (`N.rowDigest r = R.row`, so a
receipt is never replayed against another row); the pre root of the rest it was handed; the openings COVER the row's reads
at its world, in order (`R.openings.map Prod.fst = A.reads (w', rest) r`), so a producer cannot omit a
read it would rather not show; each opening is what its world says; the verdict and the post root
recomputed. -/
def recheck [DecidableEq Clause] [DecidableEq Fact] (A : Admission W Rest Row Fact Clause)
    (N : Naming W Rest Row Fact Cell Pin)
    (rest : Rest) (r : Row) (w' : W) (R : Receipt Cell Pin Fact Clause) : Bool :=
  N.rowDigest r == R.row && N.root rest == R.pre && R.openings.map Prod.fst == A.reads (w', rest) r &&
    R.openings.all (fun o => A.look w' o.1 == o.2) &&
    Outcome.ofExcept (A.step (w', rest) r) == R.verdict && postOf A N (w', rest) r == R.post

/-- What `recheck` establishes: the receipt names the row replayed and the rest handed, and the row,
judged at the stranger's world over that rest, has the receipt's verdict and post root. -/
theorem recheck_sound [DecidableEq Clause] [DecidableEq Fact] {A : Admission W Rest Row Fact Clause}
    {N : Naming W Rest Row Fact Cell Pin}
    {rest : Rest} {r : Row} {w' : W} {R : Receipt Cell Pin Fact Clause} (h : recheck A N rest r w' R = true) :
    N.rowDigest r = R.row ∧ N.root rest = R.pre ∧ Outcome.ofExcept (A.step (w', rest) r) = R.verdict ∧
      postOf A N (w', rest) r = R.post := by
  simp only [recheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.2, h.2⟩

/-- The coverage and the openings `recheck` establishes. -/
theorem recheck_covers [DecidableEq Clause] [DecidableEq Fact] {A : Admission W Rest Row Fact Clause}
    {N : Naming W Rest Row Fact Cell Pin}
    {rest : Rest} {r : Row} {w' : W} {R : Receipt Cell Pin Fact Clause} (h : recheck A N rest r w' R = true) :
    R.openings.map Prod.fst = A.reads (w', rest) r ∧ ∀ o ∈ R.openings, A.look w' o.1 = o.2 := by
  simp only [recheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.2, h.1.1.2⟩

/-- **The stranger accepts every honest receipt** at every world agreeing with its openings, where
the row reads what it read when issued (`hr`; at the issuing world itself, `rfl`). -/
theorem recheck_issued [DecidableEq Clause] [DecidableEq Fact] (A : Admission W Rest Row Fact Clause)
    (N : Naming W Rest Row Fact Cell Pin)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) (q : Shape) (t : List (String × Trust)) (p : Digest)
    (w' : W) (hw : ∀ o ∈ (issue A N a r q t p).openings, A.look w' o.1 = o.2)
    (hr : A.reads (w', a.2) r = A.reads a r) :
    recheck A N a.2 r w' (issue A N a r q t p) = true := by
  obtain ⟨hv, hp⟩ := receipt_sufficient A N a r hm w' hw
  simp only [recheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨rfl, rfl⟩, ?_⟩, fun o ho => hw o ho⟩, hv⟩, hp⟩
  simp [issue, Admission.openings, hr, Function.comp_def]

/-- At the issuing world the stranger accepts the honest receipt with no further premise. -/
theorem recheck_issued_self [DecidableEq Clause] [DecidableEq Fact] (A : Admission W Rest Row Fact Clause)
    (N : Naming W Rest Row Fact Cell Pin)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) (q : Shape) (t : List (String × Trust)) (p : Digest) :
    recheck A N a.2 r a.1 (issue A N a r q t p) = true :=
  recheck_issued A N a r hm q t p a.1 (fun o ho => by
    simp only [issue, Admission.openings, List.mem_map] at ho
    obtain ⟨f, _, rfl⟩ := ho; rfl) rfl

end Fold

/-! ## Pins: the reads computed from pins -/

section Pins
variable {V Fact Rest Row Clause : Type} [World V Fact]

/-- The pins of the cells of the facts read. -/
def pinsOf (v : V) (fs : List Fact) : List (World.Cell V × Option (World.Pin V)) :=
  fs.map fun f => (World.cell f, World.pin (Fact := Fact) v (World.cell f))

/-- **A stranger computes the read from the pins**: a world-backed opening is `holdsOfPin` at the
recorded pin. -/
theorem openings_of_pins (v : V) (f : Fact) :
    World.holdsAt v f = World.holdsOfPin (World.cell f) (World.pin (Fact := Fact) v (World.cell f)) f := rfl

/-- **Equal pins suffice**: for an admission whose look is the world's read, two worlds agreeing on
the pins of the cells a row reads give it the same verdict (`Obend.Fold.step_of_pins` with
`World.holds_congr`). -/
theorem pins_sufficient (A : Admission V Rest Row Fact Clause) (hlook : A.look = World.holdsAt)
    (a : V × Rest) (r : Row) (hm : A.moves r = false) (w' : V)
    (hp : ∀ f ∈ A.reads a r, World.pin (Fact := Fact) a.1 (World.cell f) = World.pin (Fact := Fact) w' (World.cell f)) :
    A.step (w', a.2) r = (A.step a r).map fun b => (w', b.2) :=
  Fold.step_of_pins A World.cell (fun w c => World.pin (Fact := Fact) w c)
    (fun w w' f h => by rw [hlook]; exact World.holds_congr w w' f h) a r hm w' hp

end Pins

/-! ## The dated view: openings checked against the root -/

section Dated
open Obend.Receipt.Merkle
open Obend.Digest.HashBytes (Hash Collision)
variable {W Rest Row Fact Clause Cell Pin Key : Type}

/-- **What a stranger checks of the dated root**: every opening proof opens against it. -/
def datedOpens (H : Hash) (R : Receipt Cell Pin Fact Clause) : Bool :=
  R.proofs.all fun o => opens H o R.dated

/-- How a committed view is read: the committed map, the key of the fact an opening reads, and how a
committed value reads as that opening. -/
structure Reading (W Fact Key : Type) where
  C : Commit W Key
  key : Fact → Key
  bit : Fact → Nat → Bool

/-- The committed values read as the admission's look. -/
def Reading.Coherent (D : Reading W Fact Key) (look : W → Fact → Bool) : Prop :=
  ∀ w f, D.bit f (D.C.val w (D.key f)) = look w f

/-- Each opening is matched, in order, by its proof: the key's position in the schema, the map's
size, a value that reads as the opening. -/
def Reading.matched [BEq Key] (D : Reading W Fact Key) (R : Receipt Cell Pin Fact Clause) : Bool :=
  R.openings.length == R.proofs.length &&
  (R.openings.zip R.proofs).all fun op =>
    D.C.keys.idxOf? (D.key op.1.1) == some op.2.index && op.2.size == D.C.keys.length &&
      D.bit op.1.1 op.2.value == op.1.2

/-- **The openings are the dated view's**: when `dated` is the root of world `w`'s view and the
stranger's two checks pass, every opening is what `w` says of its fact, or the hash collides. -/
theorem openings_checked [BEq Key] [LawfulBEq Key] {H : Hash} (hb : Bounded H) (D : Reading W Fact Key)
    {look : W → Fact → Bool} (hco : D.Coherent look) (w : W) (R : Receipt Cell Pin Fact Clause)
    (hd : R.dated = D.C.dated H w) (hc : datedOpens H R = true) (hm : D.matched R = true) :
    (∀ o ∈ R.openings, look w o.1 = o.2) ∨ Collision H := by
  by_cases hcol : Collision H
  · exact .inr hcol
  left
  intro o ho
  simp only [Reading.matched, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hm
  obtain ⟨hlen, hall⟩ := hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  have hk' : k < R.proofs.length := hlen ▸ hk
  have hz : (R.openings[k], R.proofs[k]) ∈ R.openings.zip R.proofs := by
    have := List.getElem_mem (l := R.openings.zip R.proofs) (n := k) (by simp; omega)
    simpa using this
  obtain ⟨⟨hidx, hsize⟩, hbit⟩ := hall _ hz
  have hp : opens H R.proofs[k] R.dated = true := by
    simp only [datedOpens, List.all_eq_true] at hc; exact hc _ (List.getElem_mem hk')
  obtain ⟨hlt, hkey, _⟩ := List.idxOf?_eq_some_iff.1 hidx
  rw [hd] at hp
  rcases Commit.opens_val hb D.C w hp hsize hlt with hv | c
  · rw [← hbit, hv, hkey, hco]
  · exact absurd c hcol

/-- **The receipt's verdict is the dated view's**: a receipt issued for a row, whose dated root is
the root of world `w`'s view and whose openings pass the stranger's checks, has the verdict and the
post root the row has at `w`, or the hash collides. -/
theorem dated_verdict [BEq Key] [LawfulBEq Key] {H : Hash} (hb : Bounded H)
    (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (D : Reading W Fact Key)
    (hco : D.Coherent A.look) (a : W × Rest) (r : Row) (hm : A.moves r = false)
    {q : Shape} {t : List (String × Trust)} {p : Digest} (w : W)
    (hd : (issue A N a r q t p).dated = D.C.dated H w) (hc : datedOpens H (issue A N a r q t p) = true)
    (hmt : D.matched (issue A N a r q t p) = true) :
    (Outcome.ofExcept (A.step (w, a.2) r) = (issue A N a r q t p).verdict ∧
      postOf A N (w, a.2) r = (issue A N a r q t p).post) ∨ Collision H := by
  rcases openings_checked hb D hco w _ hd hc hmt with ho | c
  · exact .inl (receipt_sufficient A N a r hm w ho)
  · exact .inr c

/-- **A receipt the stranger accepts has the dated view's verdict**, for ANY receipt, not only an
honestly issued one: when `recheck` passes at the stranger's view `w'` (which computes that the
openings cover the row's reads there) and the dated checks pass against a root that is the root of
world `w`'s view, the row judged at `w` has the receipt's verdict and post root, or the hash
collides. The coverage that `dated_verdict` gets from `issue` is here computed by `recheck`. -/
theorem dated_sound [DecidableEq Clause] [DecidableEq Fact] [BEq Key] [LawfulBEq Key] {H : Hash}
    (hb : Bounded H) (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin)
    (D : Reading W Fact Key) (hco : D.Coherent A.look) (rest : Rest) (r : Row) (hm : A.moves r = false)
    (w' w : W) (R : Receipt Cell Pin Fact Clause) (hr : recheck A N rest r w' R = true)
    (hd : R.dated = D.C.dated H w) (hc : datedOpens H R = true) (hmt : D.matched R = true) :
    (Outcome.ofExcept (A.step (w, rest) r) = R.verdict ∧ postOf A N (w, rest) r = R.post) ∨ Collision H := by
  rcases openings_checked hb D hco w R hd hc hmt with ho | c
  · left
    obtain ⟨_, _, hv, hp⟩ := recheck_sound hr
    obtain ⟨hcov, hw'⟩ := recheck_covers hr
    have agree : ∀ f ∈ A.reads (w', rest) r, A.look (w', rest).1 f = A.look w f := by
      intro f hf
      rw [← hcov, List.mem_map] at hf
      obtain ⟨o, hoR, rfl⟩ := hf
      exact (hw' o hoR).trans (ho o hoR).symm
    have hs := A.step_of_reads (w', rest) w r hm agree
    simp only at hs
    refine ⟨?_, ?_⟩
    · rw [hs, ← hv]; cases A.step (w', rest) r <;> rfl
    · rw [← hp]; simp only [postOf, hs]; cases A.step (w', rest) r <;> rfl
  · exact .inr c

/-- The naming whose dated root and opening proofs come from a committed view. -/
def Naming.ofReading [BEq Key] (H : Hash) (D : Reading W Fact Key) (root : Rest → Digest) (rowDigest : Row → Digest)
    (law : Digest) (pinsOf : W → List Fact → List (Cell × Option Pin)) : Naming W Rest Row Fact Cell Pin where
  root := root
  rowDigest := rowDigest
  law := law
  pinsOf := pinsOf
  dated := D.C.dated H
  proofsOf w fs := fs.filterMap fun f => D.C.opening H w (D.key f)

theorem filterMap_eq_map_of {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, h x (by simp), List.map_cons,
      filterMap_eq_map_of xs (fun y hy => h y (by simp [hy]))]

/-- **An honestly issued receipt passes both checks**, when every fact the row reads has its key in
the schema and the committed values read as the admission's look. -/
theorem issue_checks [BEq Key] [LawfulBEq Key] {H : Hash} (hb : Bounded H) (A : Admission W Rest Row Fact Clause)
    (D : Reading W Fact Key) (hco : D.Coherent A.look) (hs : D.C.keys.length < 2 ^ 256)
    (root : Rest → Digest) (rowDigest : Row → Digest) (law : Digest) (pinsOf : W → List Fact → List (Cell × Option Pin))
    (a : W × Rest) (r : Row) (hk : ∀ f ∈ A.reads a r, D.key f ∈ D.C.keys)
    (q : Shape) (t : List (String × Trust)) (p : Digest) :
    datedOpens H (issue A (Naming.ofReading H D root rowDigest law pinsOf) a r q t p) = true ∧
      D.matched (issue A (Naming.ofReading H D root rowDigest law pinsOf) a r q t p) = true := by
  have hsome : ∀ f ∈ A.reads a r, ∃ j, D.C.keys.idxOf? (D.key f) = some j := fun f hf => by
    have := (List.isSome_idxOf? (l := D.C.keys) (a := D.key f)).2 (hk f hf)
    exact Option.isSome_iff_exists.1 this
  constructor
  · simp only [datedOpens, issue, Naming.ofReading, List.all_eq_true, List.mem_filterMap]
    rintro o ⟨f, _, ho⟩
    exact Commit.opening_opens hb D.C a.1 (D.key f) ho hs
  · simp only [Reading.matched, issue, Naming.ofReading, Admission.openings, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true]
    -- the proofs are one per read, in order
    have hfm : (A.reads a r).filterMap (fun f => D.C.opening H a.1 (D.key f)) =
        (A.reads a r).map fun f => mapOpening H (D.C.values a.1) ((D.C.keys.idxOf? (D.key f)).getD 0) := by
      apply filterMap_eq_map_of
      intro f hf
      obtain ⟨j, hj⟩ := hsome f hf
      simp [Commit.opening, hj]
    rw [hfm]
    refine ⟨by simp, ?_⟩
    intro op hop
    rw [List.zip_map, List.mem_map] at hop
    obtain ⟨⟨f, f'⟩, hff, rfl⟩ := hop
    have hff' : f = f' := by
      obtain ⟨k, hk, he⟩ := List.getElem_of_mem hff
      simp only [List.getElem_zip, Prod.mk.injEq] at he
      rw [← he.1, ← he.2]
    subst hff'
    have hf := (List.of_mem_zip hff).1
    obtain ⟨j, hj⟩ := hsome f hf
    obtain ⟨hlt, hkey, _⟩ := List.idxOf?_eq_some_iff.1 hj
    simp only [Prod.map, hj, Option.getD_some, mapOpening, Commit.values, List.length_map, true_and,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some, hkey]
    exact hco a.1 f

end Dated

/-! ## Chaining -/

section Chain
variable {Cell Pin Fact Clause : Type}

/-- Newest first: each receipt names its predecessor's digest; the oldest names `genesis`. -/
def chained (d : Receipt Cell Pin Fact Clause → Digest) (genesis : Digest) : List (Receipt Cell Pin Fact Clause) → Bool
  | [] => true
  | [r] => r.prev == genesis
  | r :: s :: rest => r.prev == d s && chained d genesis (s :: rest)

/-- The digest binds: equal digests are equal receipts (an assumption about the hash, discharged
for any particular pair by `Obend.Core.Digest.binds_or_collides` up to a collision). -/
def Binds (d : Receipt Cell Pin Fact Clause → Digest) : Prop := ∀ r r', d r = d r' → r = r'

/-- **A verified chain is determined by its head and its length**, under a binding digest. -/
theorem chain_binds (d : Receipt Cell Pin Fact Clause → Digest) (genesis : Digest) (hb : Binds d) :
    ∀ (l l' : List (Receipt Cell Pin Fact Clause)), chained d genesis l = true → chained d genesis l' = true →
      l.length = l'.length → l.head? = l'.head? → l = l'
  | [], [], _, _, _, _ => rfl
  | [r], [r'], _, _, _, hh => by simp at hh; rw [hh]
  | r :: s :: rest, r' :: s' :: rest', h, h', hl, hh => by
    simp only [chained, Bool.and_eq_true, beq_iff_eq] at h h'
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hs : s = s' := hb s s' (h.1.symm.trans h'.1)
    subst hs
    have := chain_binds d genesis hb (s :: rest) (s :: rest') h.2 h'.2 (by simpa using hl) rfl
    rw [this]
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl
  | [_], _ :: _ :: _, _, _, hl, _ | _ :: _ :: _, [_], _, _, hl, _ => by simp at hl

end Chain

/-! ## The disclosure dial -/

section Dial
variable {W Rest Row Fact Clause Cell Pin : Type}

inductive Dial where
  | full
  | cited
  | bit
  deriving DecidableEq, Repr

/-- The receipt of the last row of a log folded from `a₀`, when its prefix folds. -/
def issueLast (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a₀ : W × Rest)
    (pre : List Row) (r : Row) (q : Shape) (t : List (String × Trust)) (p : Digest) :
    Option (Receipt Cell Pin Fact Clause) :=
  match A.run a₀ pre with
  | .ok a => some (issue A N a r q t p)
  | .error _ => none

/-- What a stranger holds at the `cited` setting: how roots and rows are named, the hash and the
committed reading of views, the view it realizes, and the supports it runs itself. -/
structure Stranger (W Rest Row Fact Cell Pin Key : Type) where
  N : Naming W Rest Row Fact Cell Pin
  H : Obend.Digest.HashBytes.Hash
  D : Reading W Fact Key
  view : W
  ran : List (String × Trust)

/-- The bit at each setting of the dial. `full` replays the log. `cited` runs the stranger's checks
(`recheck` with its coverage, the dated openings, the support list's ceiling) over the prefix's
accumulator and then reads the verdict, skipping only certificate re-execution. `bit` is the only
setting that takes the producer's bit on trust. -/
def accepts [DecidableEq Clause] [DecidableEq Fact] {Key : Type} [BEq Key] (A : Admission W Rest Row Fact Clause)
    (S : Stranger W Rest Row Fact Cell Pin Key) (a₀ : W × Rest) (pre : List Row) (r : Row) :
    Dial → Receipt Cell Pin Fact Clause → Bool
  | .full, _ => (A.run a₀ (pre ++ [r])).toBool
  | .cited, R => match A.run a₀ pre with
    | .ok a => recheck A S.N a.2 r S.view R && datedOpens S.H R && S.D.matched R &&
        (ceiling S.ran R.trust).toBool && R.verdict.isOk
    | .error _ => false
  | .bit, R => R.verdict.isOk

/-- **What `cited` acceptance establishes**: the row, judged over the prefix's accumulator at any
world whose view has the receipt's dated root, is admitted with the receipt's post root, or the hash
collides. -/
theorem accepts_cited_sound [DecidableEq Clause] [DecidableEq Fact] {Key : Type} [BEq Key] [LawfulBEq Key]
    (A : Admission W Rest Row Fact Clause) (S : Stranger W Rest Row Fact Cell Pin Key)
    (hb : Merkle.Bounded S.H) (hco : S.D.Coherent A.look) (a₀ : W × Rest) (pre : List Row) (r : Row)
    (hm : A.moves r = false) (R : Receipt Cell Pin Fact Clause) (h : accepts A S a₀ pre r .cited R = true)
    (w : W) (hd : R.dated = S.D.C.dated S.H w) :
    ∃ a, A.run a₀ pre = .ok a ∧
      ((Outcome.ofExcept (A.step (w, a.2) r) = .ok ∧ postOf A S.N (w, a.2) r = R.post) ∨
        Obend.Digest.HashBytes.Collision S.H) := by
  simp only [accepts] at h
  split at h
  · rename_i a hrun
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hc⟩, hmt⟩, _⟩, hok⟩ := h
    refine ⟨a, hrun, ?_⟩
    rcases dated_sound hb A S.N S.D hco a.2 r hm S.view w R hr hd hc hmt with ⟨hv, hp⟩ | c
    · left; refine ⟨?_, hp⟩; rw [hv]; revert hok; cases R.verdict <;> simp [Outcome.isOk]
    · exact .inr c
  · cases h

/-- **Acceptance is invariant under the dial** for an honestly issued receipt: the follower
replaying the log, the stranger running the cited checks at a view agreeing with the receipt's
openings and reads, and the holder of one bit agree, when the receipt's support list meets the
stranger's ceiling. The cited setting is not a projection of the bit: it re-runs every check but the
certificate's. -/
theorem dial_invariant [DecidableEq Clause] [DecidableEq Fact] {Key : Type} [BEq Key] [LawfulBEq Key]
    (A : Admission W Rest Row Fact Clause) {H : Obend.Digest.HashBytes.Hash} (hb : Merkle.Bounded H)
    (D : Reading W Fact Key) (hco : D.Coherent A.look) (hs : D.C.keys.length < 2 ^ 256)
    (root : Rest → Digest) (rowDigest : Row → Digest) (law : Digest) (pinsOf : W → List Fact → List (Cell × Option Pin))
    (a₀ : W × Rest) (pre : List Row) (r : Row) (hm : A.moves r = false) {q : Shape} {t : List (String × Trust)}
    {p : Digest} {a : W × Rest} (hrun : A.run a₀ pre = .ok a) (hk : ∀ f ∈ A.reads a r, D.key f ∈ D.C.keys)
    (view : W) (ran : List (String × Trust))
    (hw : ∀ o ∈ (issue A (Naming.ofReading H D root rowDigest law pinsOf) a r q t p).openings, A.look view o.1 = o.2)
    (hr : A.reads (view, a.2) r = A.reads a r) (ht : (ceiling ran t).toBool = true) (dial : Dial) :
    accepts A ⟨Naming.ofReading H D root rowDigest law pinsOf, H, D, view, ran⟩ a₀ pre r dial
        (issue A (Naming.ofReading H D root rowDigest law pinsOf) a r q t p) =
      (issue A (Naming.ofReading H D root rowDigest law pinsOf) a r q t p).verdict.isOk := by
  cases dial with
  | bit => rfl
  | cited =>
    obtain ⟨hc, hmt⟩ := issue_checks hb A D hco hs root rowDigest law pinsOf a r hk q t p
    simp only [accepts, hrun, recheck_issued A _ a r hm q t p view hw hr, hc, hmt, Bool.true_and]
    show ((ceiling ran t).toBool && _) = _
    rw [ht, Bool.true_and]
  | full =>
    simp only [accepts, Admission.run, List.foldlM_append] at hrun ⊢
    rw [hrun]
    simp only [issue, Outcome.ofExcept_isOk, List.foldlM_cons, List.foldlM_nil]
    show (A.step a r >>= pure).toBool = (A.step a r).toBool
    cases A.step a r <;> rfl

end Dial

end Obend.Receipt
end
