module
/-
# Obend.Logic.Frame — the claim judge and T3 `claim_frame`

`review/PROGRAM-LOGIC-20261101.md` §2.6, §2.7, §5.3 T3. A claim `λself. λsuper. λp₁ … λpₖ. l == r`
of layer `j` of a composition `C` is checked by replaying a derivation from `l` to `r` with `self`
and `super` left as the variables they are in the claim's body (`k + 1` and `k`). Weak-head `run`
steps cannot unfold a variable, so the derivation meets the composition only where it says so: a
`lateBinding m L` step at `self.m` asks the composition what its last provider of `m` gives, with
`self` still the variable (`symUnfold`, through `late_binding_at`). `super` stays inert: a claim
cannot unfold `super.m` (accepted design, `REPORT-LOGIC-20261101.md`).

`claim_sound`: an accepted derivation establishes the partial judgment `HoldsEq` of the claim's two
sides at every data instance, with `self := C.object` and `super := C.superAt j`
(`claimMeaning`); `claim_holds` turns it into `Holds` given a ground observation of the left side.

**T3 `claim_frame`**: the check reads the composition only through `symUnfold` at the derivation's
members (`replay_frame`). So an accepted derivation is accepted, unchanged, for any other
composition (any layer index for the claim) that unfolds those members to the same provider and
the same body: specification inheritance as certificate transport. The members with what they
unfold to are the certificate's **supports** (`supports`, `Support.holds`); a composition that
re-provides one of them withdraws it by name (`Obend.Logic.Obligation`).
-/
public import Obend.Logic.Rewrite
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
set_option autoImplicit false

/-- A claim of a layer of a composition: its code `λself. λsuper. λp₁ … λpₖ. body` and `k`. -/
structure ClaimObj where
  comp : Composition
  layer : Nat
  claim : Term
  arity : Nat

namespace ClaimObj

/-- `self`'s index in the claim's body. -/
def self (o : ClaimObj) : Nat := o.arity + 1

/-- The claim's body, and the sides of its `==`. -/
def sides (o : ClaimObj) : Option (EqKind × Term × Term) := (unlams (o.arity + 2) o.claim).bind equationSides

/-- What the meaning needs of the composition, decided: the claim, the object, the claim's `super`,
the composition's operands and seed are closed; the object and the `super` ask no metadata. -/
def wellFormed (o : ClaimObj) : Bool :=
  Obend.Law.closedB o.claim && Obend.Law.closedB o.comp.object && Obend.Law.closedB (o.comp.superAt o.layer) &&
    Obend.Law.closedB (composeTerm o.comp.top o.comp.below) && Obend.Law.closedB (.record o.comp.seed) &&
    !observes o.comp.object && !observes (o.comp.superAt o.layer) && decide (o.layer < o.comp.layers.length)

/-- The arguments a data instance gives the claim: `self`, `super`, the data. -/
def args (o : ClaimObj) (ds : List Data) : List Term := o.comp.object :: o.comp.superAt o.layer :: ds.map Data.term

end ClaimObj

/-- What `self.m` unfolds to with `self` the variable `s`: the provider's name and body. -/
def symUnfold (C : Composition) (s : Nat) (m : String) : Option (String × Term) :=
  (unfoldIn (.bound s) C.seed C.layers.length C.layers m).map fun (j, u) => (layerName C.layers j, u)

/-- The claim judge's resolver: only `self.m` unfolds. -/
def claimResolver (C : Composition) (s : Nat) : Resolver := fun X m =>
  match X with
  | .bound i => if i == s then symUnfold C s m else none
  | _ => none

inductive ClaimClause where
  /-- the claim or composition is not closed, or asks metadata, or the layer is missing -/
  | illFormed
  /-- the claim's body is not an elaborated `==` -/
  | notAnEquation
  /-- the derivation was refused -/
  | rewrite (clause : RClause)
  deriving DecidableEq, Repr

/-- A rewrite verdict as a claim verdict (`Judge.Verdict.map`, with its body visible to the kernel). -/
def liftVerdict : Judge.Verdict RClause → Judge.Verdict ClaimClause
  | .ok => .ok
  | .refused c p => .refused (.rewrite c) p
  | .uncovered => .uncovered

theorem liftVerdict_ok {v : Judge.Verdict RClause} (h : liftVerdict v = .ok) : v = .ok := by
  cases v <;> simp_all [liftVerdict]

/-- **The claim checker.** -/
def claimCheck (k : Nat) (o : ClaimObj) (steps : List RStep) : Judge.Verdict ClaimClause :=
  if o.wellFormed then
    match o.sides with
    | some (_, l, r) => liftVerdict (rewriteWith (claimResolver o.comp o.self) k l r steps)
    | none => .refused .notAnEquation []
  else .refused .illFormed []

/-- What an accepted claim derivation establishes: at every instance of the arity, the two sides,
with `self`, `super` and the data substituted, have the same completed runs. -/
def claimMeaning (o : ClaimObj) : Prop :=
  match o.sides with
  | some (_, l, r) => ∀ ds : List Data, ds.length = o.arity →
      HoldsEq (l.substitute (argSubst (o.args ds))) (r.substitute (argSubst (o.args ds)))
  | none => False

/-! ## Soundness -/

theorem wellFormed_parts {o : ClaimObj} (h : o.wellFormed = true) :
    Closed o.claim ∧ Closed o.comp.object ∧ Closed (o.comp.superAt o.layer) ∧
      Closed (composeTerm o.comp.top o.comp.below) ∧ Closed (.record o.comp.seed) ∧
      observes o.comp.object = false ∧ observes (o.comp.superAt o.layer) = false := by
  simp only [ClaimObj.wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨closed_of_closedB h.1.1.1.1.1.1.1, closed_of_closedB h.1.1.1.1.1.1.2, closed_of_closedB h.1.1.1.1.1.2,
    closed_of_closedB h.1.1.1.1.2, closed_of_closedB h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem argSubst_obsFree {args : List Term} (h : ∀ a ∈ args, ObsFree a) : SubstFree (argSubst args) := by
  intro i
  unfold argSubst
  split
  · rename_i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact h _ (List.getElem_mem _)
  · exact .bound _

theorem argSubst_self (o : ClaimObj) (ds : List Data) (hl : ds.length = o.arity) :
    argSubst (o.args ds) o.self = o.comp.object := by
  simp only [argSubst, ClaimObj.args, ClaimObj.self, List.length_cons, List.length_map, hl]
  simp

theorem claimResolver_sound (o : ClaimObj) (hw : o.wellFormed = true) (ds : List Data) (hl : ds.length = o.arity) :
    RSound (claimResolver o.comp o.self) (argSubst (o.args ds)) := by
  obtain ⟨_, _, _, hct, hseed, _, _⟩ := wellFormed_parts hw
  intro X m layer u h
  cases X with
  | bound i =>
    simp only [claimResolver] at h
    split at h
    · rename_i hi
      have hi : i = o.self := by simpa using hi
      subst hi
      obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      have hs := steps_substitute (argSubst (o.args ds))
        (unfoldIn_steps (.bound o.self) o.comp.seed m _ o.comp.layers hu)
      have e1 : (Term.get (superBelow (.bound o.self) o.comp.seed o.comp.layers) m).substitute (argSubst (o.args ds)) =
          .get (superBelow o.comp.object o.comp.seed o.comp.layers) m := by
        simp only [Composition.layers, superBelow, Term.substitute, closed_subst hct, closed_subst hseed,
          argSubst_self o ds hl]
      rw [e1] at hs
      simp only [Term.substitute, argSubst_self o ds hl]
      exact steps_trans (object_get o.comp m) hs
    · cases h
  | _ => simp [claimResolver] at h

/-- **`claim_sound`.** An accepted claim derivation establishes `claimMeaning`. -/
theorem claim_sound {k : Nat} {o : ClaimObj} {steps : List RStep} (h : claimCheck k o steps = .ok) :
    claimMeaning o := by
  unfold claimCheck at h
  split at h
  · rename_i hw
    unfold claimMeaning
    split at h
    · rename_i kind l r hs
      intro ds hl
      obtain ⟨_, hO, hS, _, _, hoO, hoS⟩ := wellFormed_parts hw
      have hfree : SubstFree (argSubst (o.args ds)) := argSubst_obsFree (by
        intro a ha
        simp only [ClaimObj.args, List.mem_cons, List.mem_map] at ha
        rcases ha with rfl | rfl | ⟨d, _, rfl⟩
        · exact obsFree_of_observes _ hoO
        · exact obsFree_of_observes _ hoS
        · exact data_obsFree d)
      have hr := rewriteWith_ok (liftVerdict_ok h)
      exact holdsEq_of_observed (replay_sound _ (k := .b) ⟨.inl rfl, fun _ => hfree⟩
        (claimResolver_sound o hw ds hl) steps (fun e => by cases e) hr)
    · cases h
  · cases h

theorem rename_lift_subst (t : Term) (σ : Nat → Term) :
    (t.rename Nat.succ).substitute (liftSubstitution σ) = (t.substitute σ).rename Nat.succ := by
  rw [Obend.Core.TermTraverse.rename_substitute, Obend.Core.TermTraverse.substitute_rename]
  rfl

theorem unshift_rename (x : Term) : unshift (x.rename Nat.succ) = some x := by
  have e : (x.rename Nat.succ).substitute unshiftSubst = x := by
    rw [Obend.Core.TermTraverse.rename_substitute]
    exact substitute_bound x
  unfold unshift
  rw [e, termEq_refl']
  rfl

/-- **`claim_holds`.** With a ground observation of its left side at an instance, an accepted claim
holds there: `Holds (c O (superAt j)) d⃗`. -/
theorem claim_holds {k : Nat} {o : ClaimObj} {steps : List RStep} (h : claimCheck k o steps = .ok)
    {kind : EqKind} {l r : Term} (hs : o.sides = some (kind, l, r)) (ds : List Data) (hl : ds.length = o.arity)
    {obs : Observation} (hk : kind.accepts obs = true) (hlo : Halts (l.substitute (argSubst (o.args ds))) obs) :
    Holds (instantiateClaim o.claim o.comp o.layer) ds := by
  have hm := claim_sound h
  unfold claimMeaning at hm
  rw [hs] at hm
  have hw : o.wellFormed = true := by
    unfold claimCheck at h; split at h
    · assumption
    · cases h
  obtain ⟨hc, hO, hS, _, _, _, _⟩ := wellFormed_parts hw
  unfold ClaimObj.sides at hs
  obtain ⟨body, hb, he⟩ := Option.bind_eq_some_iff.1 hs
  have hcl := unlams_some hb
  have hargs : ∀ a ∈ o.args ds, Closed a := by
    intro a ha
    simp only [ClaimObj.args, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | rfl | ⟨d, _, rfl⟩
    · exact hO
    · exact hS
    · exact data_closed d
  have hlen : (o.args ds).length = o.arity + 2 := by simp [ClaimObj.args, hl]
  have hβ := betaAll_lams (o.args ds) body hargs
  rw [hlen, ← hcl] at hβ
  have e : apps (instantiateClaim o.claim o.comp o.layer) (ds.map Data.term) = apps o.claim (o.args ds) := rfl
  have he' : equationSides (body.substitute (argSubst (o.args ds))) =
      some (kind, l.substitute (argSubst (o.args ds)), r.substitute (argSubst (o.args ds))) := by
    unfold equationSides at he
    split at he
    · cases he; simp [equationSides]
    · cases he; simp [equationSides]
    · rename_i l' r'
      obtain ⟨l0, hu, e⟩ := Option.map_eq_some_iff.1 he
      cases e
      have := unshift_some hu
      subst this
      simp only [Term.substitute, equationSides, liftSubstitution]
      rw [rename_lift_subst, unshift_rename]
      rfl
    · cases he
  exact holds_of_holdsEq (e ▸ hβ) he' (hm ds hl) hk hlo

/-! ## T3: the frame -/

/-- **T3 `claim_frame`.** An accepted claim derivation is accepted, unchanged, for any composition
`C'` (and any layer index `j'` for the claim) that unfolds each of the derivation's members to the
same provider and body, given that `C'` is well formed. -/
theorem claim_frame {k : Nat} {o : ClaimObj} {steps : List RStep} (h : claimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat}
    (hsup : ∀ m ∈ membersList steps, symUnfold C' o.self m = symUnfold o.comp o.self m)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    claimCheck k { o with comp := C', layer := j' } steps = .ok := by
  unfold claimCheck at h ⊢
  rw [hwf]
  split at h
  · simp only [ite_true]
    have hside : ({ o with comp := C', layer := j' } : ClaimObj).sides = o.sides := rfl
    rw [hside]
    split at h
    · rename_i kind l r hs
      change liftVerdict (rewriteWith (claimResolver C' o.self) k l r steps) = .ok
      unfold rewriteWith at h ⊢
      rw [replay_frame steps (R := claimResolver C' o.self) (R' := claimResolver o.comp o.self) (by
        intro X m hm
        cases X with
        | bound i =>
          simp only [claimResolver]
          split
          · exact hsup m hm
          · rfl
        | _ => rfl) l]
      exact h
    · cases h
  · cases h

end Obend.Logic
end
