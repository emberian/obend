module
/-
# Obend.Receipt — the receipt type

`review/GENERALIZATION-20261031.md` G4; `review/GENERATED-20261031.md` §0 (the inventory found no
receipt type) and §2.4; `review/VISION-CLAUDE-20261031.md` §8. A receipt is a claim with evidence:

    { pre post : Root; row; law : Digest; pins : List (Cell × Option Pin); openings; verdict;
      quantifier : Shape; trust : per support, checked | attested; dated : View; prev : Digest }

- `Outcome`: a judge's verdict (`ok | refused clause path | uncovered`) and Astra's refusal outcomes
  (`noAdmissible | awaitingChoice | preferenceKept | candidateRejected | staleEvidence |
  executionFrozen`, `astra/ASTRA-SELECTION-20261031.md` line 225), which a selection reports and a
  judge does not.
- `Trust` is per support; `Receipt.overall` is `attested` as soon as one support is, and names it.
- `issue`: the receipt of one row of an audited fold (`Obend.Fold.Admission`). `receipt_sufficient`
  (`Obend.Fold.receipt_sufficient`, restated): at any world agreeing with the receipt's openings, the
  row is judged as the receipt says and reaches its `post` root; `recheck` is what a stranger runs,
  and `recheck_issued` says it accepts every honestly issued receipt at every such world.
- With a `World` (`Obend.Slot.World`): the openings are COMPUTED from the pins by `holdsOfPin`
  (`openings_of_pins`, `rfl`), and equal pins suffice (`pins_sufficient`).
- `chained`: each receipt names its predecessor's digest; under a binding digest a verified chain is
  determined by its head and length (`chain_binds`).
- The disclosure dial (`GENERATED` §2.4): `full` (the log, replayed by a follower), `cited` (the
  receipt with its openings), `bit` (the roots and one bit). `dial_invariant`: the bit is the same
  at all three.
-/
public import Obend.Fold
public import Obend.Judge.Class
public import Obend.Slot.World

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
  /-- the shared ledger's view it was issued at (never a local clock) -/
  dated : Nat
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

/-! ## The receipt of a row of an audited fold -/

section Fold
variable {W Rest Row Fact Clause Cell Pin : Type}

/-- What a producer signs into a receipt besides the fold: how roots, rows and pins are named. -/
structure Naming (W Rest Row Fact Cell Pin : Type) where
  root : Rest → Digest
  rowDigest : Row → Digest
  law : Digest
  pinsOf : W → List Fact → List (Cell × Option Pin)

/-- The receipt of row `r` judged at accumulator `a`. -/
def issue (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a : W × Rest) (r : Row)
    (quantifier : Shape) (trust : List (String × Trust)) (dated : Nat) (prev : Digest) :
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
  dated := dated
  prev := prev

/-- The post root a step reaches. -/
def postOf (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a : W × Rest) (r : Row) : Digest :=
  match A.step a r with
  | .ok b => N.root b.2
  | .error _ => N.root a.2

/-- **A receipt suffices** (`Obend.Fold.receipt_sufficient`): at any world agreeing with the
receipt's openings, the row is judged as the receipt says, reaching its post root. -/
theorem receipt_sufficient (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) {q : Shape} {t : List (String × Trust)} {d : Nat} {p : Digest}
    (w' : W) (hw : ∀ o ∈ (issue A N a r q t d p).openings, A.look w' o.1 = o.2) :
    Outcome.ofExcept (A.step (w', a.2) r) = (issue A N a r q t d p).verdict ∧
      postOf A N (w', a.2) r = (issue A N a r q t d p).post := by
  have h := Fold.receipt_sufficient A a r hm w' hw
  simp only [issue, postOf]
  rw [h]
  cases A.step a r <;> exact ⟨rfl, rfl⟩

/-- What a stranger runs: the pre root of the rest it was handed, the openings at its world, the
verdict and the post root recomputed. -/
def recheck [DecidableEq Clause] (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin)
    (rest : Rest) (r : Row) (w' : W) (R : Receipt Cell Pin Fact Clause) : Bool :=
  N.root rest == R.pre && R.openings.all (fun o => A.look w' o.1 == o.2) &&
    Outcome.ofExcept (A.step (w', rest) r) == R.verdict && postOf A N (w', rest) r == R.post

/-- What `recheck` establishes: the row, judged at the stranger's world over the handed rest, has
the receipt's verdict and post root. -/
theorem recheck_sound [DecidableEq Clause] {A : Admission W Rest Row Fact Clause} {N : Naming W Rest Row Fact Cell Pin}
    {rest : Rest} {r : Row} {w' : W} {R : Receipt Cell Pin Fact Clause} (h : recheck A N rest r w' R = true) :
    N.root rest = R.pre ∧ Outcome.ofExcept (A.step (w', rest) r) = R.verdict ∧ postOf A N (w', rest) r = R.post := by
  simp only [recheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

/-- **The stranger accepts every honest receipt** at every world agreeing with its openings. -/
theorem recheck_issued [DecidableEq Clause] (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) (q : Shape) (t : List (String × Trust)) (d : Nat) (p : Digest)
    (w' : W) (hw : ∀ o ∈ (issue A N a r q t d p).openings, A.look w' o.1 = o.2) :
    recheck A N a.2 r w' (issue A N a r q t d p) = true := by
  obtain ⟨hv, hp⟩ := receipt_sufficient A N a r hm w' hw
  simp only [recheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  exact ⟨⟨⟨rfl, fun o ho => hw o ho⟩, hv⟩, hp⟩

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
    (pre : List Row) (r : Row) (q : Shape) (t : List (String × Trust)) (d : Nat) (p : Digest) :
    Option (Receipt Cell Pin Fact Clause) :=
  match A.run a₀ pre with
  | .ok a => some (issue A N a r q t d p)
  | .error _ => none

/-- The bit at each setting of the dial: `full` replays the log, `cited` reads the receipt's verdict,
`bit` reads the one bit. -/
def accepts (A : Admission W Rest Row Fact Clause) (a₀ : W × Rest) (pre : List Row) (r : Row) :
    Dial → Receipt Cell Pin Fact Clause → Bool
  | .full, _ => (A.run a₀ (pre ++ [r])).toBool
  | .cited, R => R.verdict.isOk
  | .bit, R => R.verdict.isOk

/-- **Acceptance is invariant under the dial**: for the receipt of a row whose prefix folds, the
follower replaying the log, the stranger reading the openings and the holder of one bit agree. -/
theorem dial_invariant (A : Admission W Rest Row Fact Clause) (N : Naming W Rest Row Fact Cell Pin) (a₀ : W × Rest)
    (pre : List Row) (r : Row) {q : Shape} {t : List (String × Trust)} {d : Nat} {p : Digest}
    {R : Receipt Cell Pin Fact Clause} (h : issueLast A N a₀ pre r q t d p = some R) (dial : Dial) :
    accepts A a₀ pre r dial R = R.verdict.isOk := by
  cases dial with
  | cited | bit => rfl
  | full =>
    simp only [issueLast] at h
    cases hrun : A.run a₀ pre with
    | error e => rw [hrun] at h; cases h
    | ok a =>
      rw [hrun] at h; cases h
      simp only [accepts, Admission.run, List.foldlM_append] at hrun ⊢
      rw [hrun]
      simp only [issue, Outcome.ofExcept_isOk, List.foldlM_cons, List.foldlM_nil]
      show (A.step a r >>= pure).toBool = (A.step a r).toBool
      cases A.step a r <;> rfl

end Dial

end Obend.Receipt
end
