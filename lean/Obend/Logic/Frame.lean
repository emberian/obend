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
public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Obend.Core.TermTraverse (encode)
set_option autoImplicit false

/-- A claim of a layer of a composition: its code `λself. λsuper. λp₁ … λpₖ. body` and `k`. -/
structure ClaimObj where
  comp : Composition
  layer : Nat
  claim : Term
  arity : Nat

namespace ClaimObj

/-- `self`'s index in the claim's body. -/
@[expose] def self (o : ClaimObj) : Nat := o.arity + 1

/-- The claim's body, and the sides of its `==`. -/
@[expose] def sides (o : ClaimObj) : Option (EqKind × Term × Term) := (unlams (o.arity + 2) o.claim).bind equationSides

/-- What the meaning needs of the composition, decided: the claim, the object, the claim's `super`,
the composition's operands and seed are closed; the object and the `super` ask no metadata. -/
@[expose] def wellFormed (o : ClaimObj) : Bool :=
  Obend.Law.closedB o.claim && Obend.Law.closedB o.comp.object && Obend.Law.closedB (o.comp.superAt o.layer) &&
    Obend.Law.closedB (composeTerm o.comp.top o.comp.below) && Obend.Law.closedB (.record o.comp.seed) &&
    !observes o.comp.object && !observes (o.comp.superAt o.layer) && decide (o.layer < o.comp.layers.length)

/-- The arguments a data instance gives the claim: `self`, `super`, the data. -/
@[expose] def args (o : ClaimObj) (ds : List Data) : List Term := o.comp.object :: o.comp.superAt o.layer :: ds.map Data.term

end ClaimObj

/-- What `self.m` unfolds to with `self` the variable `s`: the provider's name and body. -/
@[expose] def symUnfold (C : Composition) (s : Nat) (m : String) : Option (String × Term) :=
  (unfoldIn (.bound s) C.seed C.layers.length C.layers m).map fun (j, u) => (layerName C.layers j, u)

/-- The claim judge's resolver: only `self.m` unfolds. -/
@[expose] def claimResolver (C : Composition) (s : Nat) : Resolver := fun X m =>
  match X with
  | .bound i => if i == s then symUnfold C s m else none
  | _ => none

inductive ClaimClause where
  /-- the claim or composition is not closed, or asks metadata, or the layer is missing -/
  | illFormed
  /-- The object itself is malformed, independently of its certificate. -/
  | malformedObject
  /-- Closed scalar literals denote different completed observations. -/
  | groundMismatch
  /-- the claim's body is not an elaborated `==` -/
  | notAnEquation
  /-- the derivation was refused -/
  | rewrite (clause : RClause)
  deriving DecidableEq, Repr

/-- A rewrite verdict as a claim verdict (`Judge.Verdict.map`, with its body visible to the kernel). -/
@[expose] def liftVerdict : Judge.Verdict RClause → Judge.Verdict ClaimClause
  | .ok => .ok
  | .refused c p => .refused (.rewrite c) p
  | .uncovered => .uncovered

theorem liftVerdict_ok {v : Judge.Verdict RClause} (h : liftVerdict v = .ok) : v = .ok := by
  cases v <;> simp_all [liftVerdict]

/-- Exactly the ground observations supported by the partial equation semantics. -/
def groundLiteral : Term → Option Observation
  | .nat n => some (.natural n)
  | .boolean b => some (.boolean b)
  | .label s => some (.label s)
  | _ => none

def groundMismatch (arity : Nat) (l r : Term) : Bool :=
  arity == 0 && match groundLiteral l, groundLiteral r with
    | some a, some b => decide (a ≠ b)
    | _, _ => false

@[simp] theorem groundMismatch_refl (arity : Nat) (t : Term) :
    groundMismatch arity t t = false := by
  unfold groundMismatch
  cases groundLiteral t <;> simp

/-- **The claim checker.** -/
@[expose] def claimCheck (k : Nat) (o : ClaimObj) (steps : List RStep) : Judge.Verdict ClaimClause :=
  if o.wellFormed then
    match o.sides with
    | some (_, l, r) =>
      if groundMismatch o.arity l r then .refused .groundMismatch []
      else liftVerdict (rewriteWith (claimResolver o.comp o.self) k l r steps)
    | none => .refused .notAnEquation []
  else .refused .illFormed []

/-- What an accepted claim derivation establishes: at every instance of the arity, the two sides,
with `self`, `super` and the data substituted, have the same completed runs. -/
@[expose] def claimMeaning (o : ClaimObj) : Prop :=
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
      split at h
      · cases h
      rename_i hground
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
      split at h
      · cases h
      rename_i hg
      simp only [show ({ o with comp := C', layer := j' } : ClaimObj).arity = o.arity from rfl, hg, ite_false]
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

theorem liftVerdict_ne {v : Judge.Verdict RClause} (h : liftVerdict v ≠ .uncovered) : v ≠ .uncovered := by
  cases v <;> simp_all [liftVerdict]


/-! ## 1. Symbolic Unfolding of `super.m` and `superClaimResolver` -/

/-- Symbolic unfolding of `super.m` at layer `layer` of `C`, keeping dynamic `self` bound to
`.bound selfIdx` (open recursion) while resolving `m` in the inherited suffix `C.layers.drop (layer + 1)`. -/
@[expose] def superSymUnfold (C : Composition) (selfIdx layer : Nat) (m : String) :
    Option (String × Term) :=
  let ls := C.layers.drop (layer + 1)
  (unfoldIn (.bound selfIdx) C.seed ls.length ls m).map fun (j, u) => (layerName ls j, u)

/-- Vertical + horizontal claim resolver:
- `.bound selfIdx` (`self`) unfolds through the whole composition `C` (`symUnfold`),
- `.bound (selfIdx - 1)` (`super`, at index `o.arity` when `selfIdx = o.arity + 1`) unfolds through
  the layers strictly below `layer` (`superSymUnfold`), keeping dynamic `self` at `.bound selfIdx`. -/
@[expose] def superClaimResolver (C : Composition) (selfIdx layer : Nat) : Resolver := fun X m =>
  match X with
  | .bound i =>
    if i == selfIdx then symUnfold C selfIdx m
    else if selfIdx > 0 && i == selfIdx - 1 then superSymUnfold C selfIdx layer m
    else none
  | _ => none

/-! ## 2. Soundness (`superClaimResolver_sound`, `superClaim_sound`, `superClaim_holds`) -/

/-- `argSubst (o.args ds)` maps `o.arity` (`o.self - 1`) to `o.comp.superAt o.layer`. -/
theorem argSubst_super (o : ClaimObj) (ds : List Data) (hl : ds.length = o.arity) :
    argSubst (o.args ds) o.arity = o.comp.superAt o.layer := by
  simp only [argSubst, ClaimObj.args, List.length_cons, List.length_map, hl]
  have hlt : o.arity < o.arity + 1 + 1 := by omega
  simp [hlt]

/-- Every non-empty suffix `next :: rest = (top :: below).drop k` of a closed `composeTerm`
is itself closed. -/
theorem closed_composeTerm_drop :
    ∀ (top : Layer) (below : List Layer),
      Closed (composeTerm top below) →
      ∀ (k : Nat) (next : Layer) (rest : List Layer),
        (top :: below).drop k = next :: rest → Closed (composeTerm next rest)
  | top, below, hct, 0, next, rest, hdrop => by
    simp only [List.drop_zero, List.cons.injEq] at hdrop
    rcases hdrop with ⟨rfl, rfl⟩
    exact hct
  | _, [], _, _ + 1, _, _, hdrop => by
    simp at hdrop
  | top, b0 :: bs, hct, k + 1, next, rest, hdrop => by
    have hct' := hct
    unfold Closed Obend.Core.TermTraverse.Scoped Obend.Core.Traverse.Tree.Scoped at hct'
    simp only [composeTerm, composeWith, composeStep, encode, Obend.Core.Traverse.Tree.All] at hct'
    have hmix := hct' (.node .mix [encode (composeWith Layer.term b0 bs), encode top.term])
      (by simp)
    simp only [Obend.Core.Traverse.Tree.All] at hmix
    have hsub : Closed (composeTerm b0 bs) :=
      hmix (encode (composeWith Layer.term b0 bs)) (by simp)
    exact closed_composeTerm_drop b0 bs hsub k next rest hdrop

theorem superBelow_subst_argSubst (o : ClaimObj) (hw : o.wellFormed = true)
    (ds : List Data) (hl : ds.length = o.arity) :
    (superBelow (.bound o.self) o.comp.seed (o.comp.layers.drop (o.layer + 1))).substitute
        (argSubst (o.args ds)) =
      o.comp.superAt o.layer := by
  obtain ⟨_, _, _, hct, hseed, _, _⟩ := wellFormed_parts hw
  unfold Composition.superAt
  cases hdrop : o.comp.layers.drop (o.layer + 1) with
  | nil =>
    simp only [superBelow]
    exact closed_subst hseed _
  | cons next rest =>
    have hcNext : Closed (composeTerm next rest) :=
      closed_composeTerm_drop o.comp.top o.comp.below hct (o.layer + 1) next rest hdrop
    simp only [superBelow, Term.substitute, closed_subst hcNext, closed_subst hseed,
      argSubst_self o ds hl]

/-- **Resolver Soundness (`superClaimResolver_sound`)**:
Both `self.m` and `super.m` unfoldings in `superClaimResolver` soundly step under
`argSubst (o.args ds)` for every data tuple `ds` of length `o.arity`. -/
theorem superClaimResolver_sound (o : ClaimObj) (hw : o.wellFormed = true)
    (ds : List Data) (hl : ds.length = o.arity) :
    RSound (superClaimResolver o.comp o.self o.layer) (argSubst (o.args ds)) := by
  obtain ⟨_, _, _, hct, hseed, _, _⟩ := wellFormed_parts hw
  intro X m layer u h
  cases X with
  | bound i =>
    simp only [superClaimResolver] at h
    by_cases hself : (i == o.self) = true
    · simp only [hself, ite_true] at h
      have hi : i = o.self := beq_iff_eq.1 hself
      subst hi
      obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      have hs := steps_substitute (argSubst (o.args ds))
        (unfoldIn_steps (.bound o.self) o.comp.seed m _ o.comp.layers hu)
      have e1 : (Term.get (superBelow (.bound o.self) o.comp.seed o.comp.layers) m).substitute
          (argSubst (o.args ds)) =
          .get (superBelow o.comp.object o.comp.seed o.comp.layers) m := by
        simp only [Composition.layers, superBelow, Term.substitute, closed_subst hct,
          closed_subst hseed, argSubst_self o ds hl]
      rw [e1] at hs
      simp only [Term.substitute, argSubst_self o ds hl]
      exact steps_trans (object_get o.comp m) hs
    · simp only [hself, Bool.false_eq_true, ite_false] at h
      by_cases hsup : (decide (o.self > 0) && (i == o.self - 1)) = true
      · simp only [hsup, ite_true] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsup
        have hi : i = o.arity := by
          have : o.self = o.arity + 1 := rfl
          omega
        subst hi
        obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
        cases e
        let ls := o.comp.layers.drop (o.layer + 1)
        have hs := steps_substitute (argSubst (o.args ds))
          (unfoldIn_steps (.bound o.self) o.comp.seed m ls.length ls hu)
        have e2 : (Term.get (superBelow (.bound o.self) o.comp.seed ls) m).substitute
            (argSubst (o.args ds)) =
            .get (o.comp.superAt o.layer) m := by
          simp only [ls, Term.substitute, superBelow_subst_argSubst o hw ds hl]
        rw [e2] at hs
        simpa only [Term.substitute, argSubst_super o ds hl] using hs
      · simp [hsup] at h
  | _ => simp [superClaimResolver] at h

/-! ## 3. Exact Receiver-Traced Supports & `T3_super_claim_frame` -/

-- Monotonicity of `replay` / `apply` under resolver extension (`∀ X m v, R X m = some v → R' X m = some v`).
mutual
theorem replay_of_resolver_extends {R R' : Resolver}
    (hext : ∀ X m v, R X m = some v → R' X m = some v) :
    ∀ (steps : List RStep) {t t' : Term},
      replay R steps t = .ok t' → replay R' steps t = .ok t'
  | [], _, _, h => h
  | s :: rest, t, t', h => by
    simp only [replay] at h ⊢
    cases ha : apply R s t with
    | error p => rw [ha] at h; cases h
    | ok u =>
      rw [ha] at h
      simp only [apply_of_resolver_extends hext s ha] at h ⊢
      cases hr : replay R rest u with
      | error p => rw [hr] at h; cases h
      | ok v =>
        rw [hr] at h
        simp only [replay_of_resolver_extends hext rest hr] at h ⊢
        exact h

theorem apply_of_resolver_extends {R R' : Resolver}
    (hext : ∀ X m v, R X m = some v → R' X m = some v) :
    ∀ (s : RStep) {t t' : Term},
      apply R s t = .ok t' → apply R' s t = .ok t'
  | .run _, _, _, h => h
  | .assoc _, _, _, h => h
  | .composeAssoc _, _, _, h => h
  | .lateBinding m lay, t, t', h => by
    simp only [apply] at h ⊢
    cases t with
    | get X m' =>
      simp only [unfoldAt] at h ⊢
      by_cases hm : (m' == m) = true
      · simp only [hm, ite_true] at h ⊢
        cases hR : R X m with
        | none => rw [hR] at h; cases h
        | some pair =>
          rw [hR] at h
          simp only [hext X m pair hR] at h ⊢
          exact h
      · simp [hm] at h
    | _ => simp [unfoldAt] at h
  | .congr ctx a inner, t, t', h => by
    simp only [apply] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ite_true]
      cases hr : replay R inner a with
      | error p => rw [hr] at h; cases h
      | ok a' =>
        rw [hr] at h
        simp only [replay_of_resolver_extends hext inner hr] at h ⊢
        exact h
    · cases h
  | .trans first second, t, t', h => by
    simp only [apply] at h ⊢
    cases hr1 : replay R first t with
    | error p => rw [hr1] at h; cases h
    | ok u =>
      rw [hr1] at h
      simp only [replay_of_resolver_extends hext first hr1] at h ⊢
      exact replay_of_resolver_extends hext second h
end

end Obend.Logic
end
