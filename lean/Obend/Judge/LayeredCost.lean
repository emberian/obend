module
/- The cost of a layered object, through its flattening (contract C4, the `super` decision of
2026-11-01).

The two-stage rule settles a recursive body's template with `self` open, and binds a β argument by
the ordinary rules, so the inner layer of `mix l u` (`l self super`, an argument to `u`) is
evaluated with `self` open and loses its fields that read `self`: a layered object
`fix (compose …) {seed}` (`Obend.Logic.Composition.object`) has no derivation of such a member.
Its flattening (`Obend.Leaf.Flatten`) has: one record, `self` its own vtable, every `super.p`
resolved statically, so a member reading `self` or `super` is a literal or a selection from `self`,
in the fragment of `Obend.Equiv.Demand`.

So the cost of a layered object is stated through its compilation (`LayeredCost`): the selection
from the flattening is derivable within `k`, and it is `≈b` the selection from the object
(`flatten_sound`). The judge `layeredCost` checks it with a demand run of the flattening as the
certificate; it refutes a bound below the demand (`layered_refuted`). What it does not claim: a
clairvoyant derivation of `C.object` itself, nor that `≈b` preserves cost (it does not; `≈c` is
the relation that does, and the object and its flattening are not `Sim`-related). -/
public import Obend.Judge.Cost
public import Obend.Leaf.Flatten
@[expose] public section
namespace Obend.Judge.LayeredCost
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Judge.Cost
open Obend.Equiv.Demand (FE obj demand demand_exists demand_minimal)
set_option autoImplicit false

/-- **The cost of a member of a layered object, through its compilation**: the flattening's member
costs at most `k`, and is `≈b` the object's. -/
def LayeredCost (C : Composition) (m : String) (k : Nat) : Prop :=
  CostAtMost (.get C.flatten m) k ∧ (Term.get C.flatten m ≈b .get C.object m)

inductive LayeredClause where
  /-- the composition is outside `flatten_sound`'s scope -/
  | notClosed
  /-- the flattening's member fails the cost check -/
  | cost (c : CostClause)
  deriving DecidableEq, Repr

def layeredCheck (r : Nat) (o : Composition × String × Nat) (c : DemandCert) : Verdict LayeredClause :=
  if o.1.closedB then
    match costCheck r (.get o.1.flatten o.2.1, o.2.2) c with
    | .ok => .ok
    | .refused k p => .refused (.cost k) p
    | .uncovered => .uncovered
  else .refused .notClosed []

def layeredRefutes : LayeredClause → Bool
  | .cost c => costRefutes c
  | .notClosed => false

theorem layered_sound {r : Nat} {o : Composition × String × Nat} {c : DemandCert}
    (h : layeredCheck r o c = .ok) : LayeredCost o.1 o.2.1 o.2.2 := by
  simp only [layeredCheck] at h
  split at h
  · rename_i hc
    split at h
    · rename_i hk
      exact ⟨(cost_sound (o := (_, _)) hk).1, Obend.Leaf.flatten_sound o.1 hc o.2.1⟩
    · cases h
    · cases h
  · cases h

/-- A refused cost check that refutes: no derivation of the flattening's member is that cheap. -/
theorem layered_refuted {r : Nat} {o : Composition × String × Nat} {c : DemandCert} {k : LayeredClause}
    {p : List Nat} (h : layeredCheck r o c = .refused k p) (hk : layeredRefutes k = true) :
    ∀ _ : DemandCert, ¬ LayeredCost o.1 o.2.1 o.2.2 := by
  intro c' hm
  simp only [layeredCheck] at h
  split at h
  · split at h
    · cases h
    · rename_i k' p' hk'
      cases h
      exact cost_refuted (o := (_, _)) hk' hm.1
    · cases h
  · cases h; simp [layeredRefutes] at hk

/-- **The layered cost judge.** Objects are a closed composition, a member and a bound; a
certificate is a demand run of the flattening. -/
instance layeredCost : Judge (Composition × String × Nat) DemandCert where
  Clause := LayeredClause
  Meaning o _ := LayeredCost o.1 o.2.1 o.2.2
  check := layeredCheck
  sound := layered_sound
  refutes := layeredRefutes
  refuted := layered_refuted
  Fragment o := o.1.closedB = true ∧ ∃ fs, (fs.map Prod.fst).Nodup ∧ fs.length ≤ 97 ∧ o.1.flatten = obj fs
  complete := by
    rintro ⟨C, m, k⟩ ⟨hc, fs, nd, hlen, e⟩ ⟨_, hm, _⟩
    obtain ⟨w, j, run, le⟩ := hm
    change CV (.get C.flatten m) w j at run
    change j ≤ k at le
    change C.flatten = obj fs at e
    rw [e] at run
    obtain ⟨v, n, hd, _, low⟩ := demand_minimal nd run
    refine ⟨⟨fs, m⟩, 0, ?_⟩
    change C.closedB = true at hc
    simp only [layeredCheck, hc, ite_true, costCheck, e, termBeq_refl, nd, hlen, hd]
    simp [show n ≤ k by omega]
  mono := by
    intro r r' o c _ _
    simp only [layeredCheck, costCheck]

/-! ## A layered object -/

/-- The inner layer `{a = 7}`. -/
def inner : Layer := { name := "inner", metadata := .record [], fields := [("a", .nat 7)] }
/-- The outer layer `{b = self.a, c = super.a}`, over it. -/
def outer : Layer :=
  { name := "outer", metadata := .record [], fields := [("b", .get (.bound 1) "a"), ("c", .get (.bound 0) "a")] }
/-- `fix (compose outer inner) {}`. -/
def layered : Composition := ⟨outer, [inner], []⟩

/-- Its flattening is the object `{b = self.a, c = 7, a = 7}`: `super.a` resolved statically. -/
def layeredFields : List (String × FE) := [("b", .ref "a"), ("c", .lit 7), ("a", .lit 7)]

theorem layered_closed : layered.closedB = true := by decide +kernel

theorem layered_flatten : layered.flatten = obj layeredFields :=
  termBeq_sound (by decide +kernel : termBeq layered.flatten (obj layeredFields) = true)

/-- **The layered member reading `self` is costed**: `layered.b` costs at most 7 through its
flattening, and `≈b` that flattening's member; at most 6 is refuted. -/
theorem layered_b_cost :
    layeredCheck 0 (layered, "b", 7) ⟨layeredFields, "b"⟩ = .ok ∧
      layeredCheck 0 (layered, "b", 6) ⟨layeredFields, "b"⟩ = .refused (.cost .overBudget) [] := by
  constructor <;> decide +kernel

theorem layered_b : LayeredCost layered "b" 7 := layered_sound layered_b_cost.1

end Obend.Judge.LayeredCost
end
