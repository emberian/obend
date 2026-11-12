module
/-
# Obend.Logic.SuperRefines — Vertical `super.m` Spec-Refinement & Target-Qualified Frame Transport

Unlocks vertical specification refinement (`super.m`) in `Obend.Logic` claims while preserving
certificate frame transport (`T3_super_claim_frame`).

## Summary of Constructions & Theorems

1. **`superSymUnfold` & `superClaimResolver`**:
   - In `Obend.Logic.Frame`, `claimResolver` only unfolds `self.m` (`X == .bound o.self`) and
     leaves `super` (`X == .bound o.arity`) completely inert.
   - `superSymUnfold C selfIdx layer m` unfolds `m` in the inherited stack `C.layers.drop (layer + 1)`
     beneath `layer` while keeping dynamic `self` bound to `.bound selfIdx` (open recursion!),
     matching `C.superAt layer` exactly.
   - `superClaimResolver C selfIdx layer` dispatches `.bound selfIdx` to `symUnfold` and
     `.bound (selfIdx - 1)` (`o.arity`) to `superSymUnfold`.

2. **Soundness (`superClaimResolver_sound`, `superClaim_sound`, `superClaim_holds`)**:
   - Proves `closed_composeTerm_drop` and `argSubst_super`, establishing
     `superClaimResolver_sound : RSound (superClaimResolver o.comp o.self o.layer) (argSubst (o.args ds))`,
     `superClaim_sound : superClaimCheck k o steps = .ok → claimMeaning o`,
     `superClaim_holds`, and `superClaimJudge : Judge ClaimObj (List RStep)`.

3. **Target-Qualified Supports & `T3_super_claim_frame` (Vertical + Horizontal Frame Transport)**:
   - Traces exact `(X, m)` late-binding queries along `replay` (`traceReplay`, `traceReplay_frame`),
     partitioning a certificate's footprint into `selfSupports` (`ReceiverKind.selfReceiver`) and
     `superSupports` (`ReceiverKind.superReceiver`) inside `SuperClaimCert`.
   - **`T3_super_claim_frame`**: Any accepted `superClaimCheck` certificate remains accepted
     **unchanged** (with identical traced supports) in any well-formed extended composition `(C', j')`
     where `selfSupports` agree on `symUnfold C'` and `superSupports` agree on `superSymUnfold C' _ j'`
     — even when outer wrapper layers above `j'` override members in `superSupports`!

4. **Concrete 2-Layer & 3-Layer Witnesses + Universal Impossibility Under Old `claimCheck`**:
   - Proves `verticalLimit_impossible_claimCheck`: `∀ k steps, claimCheck k verticalLimitClaimObj steps ≠ .ok`
     (no derivation of any size can prove `self.limit - super.limit == 10` under inert-`super` `claimCheck`),
     whereas `superClaimCheck` accepts `verticalLimitSteps`!
   - Proves `verticalOpenRec_accepted` (`arity = 1`, combining `super.apply` + symbolic β + open
     recursion `self.scale`) and transports it unchanged via `T3_super_claim_frame` across a 3rd
     layer `auditWrapperLayer` that overrides `"apply"`!
-/

public import Obend.Logic.Frame
public import Obend.Logic.Obligation

public section

namespace Obend.Logic

open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Core.TermTraverse (encode)
open Obend.Equiv

set_option autoImplicit false

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

/-- **The vertical-refinement claim checker (`superClaimCheck`).** -/
@[expose] def superClaimCheck (k : Nat) (o : ClaimObj) (steps : List RStep) :
    Judge.Verdict ClaimClause :=
  if o.wellFormed then
    match o.sides with
    | some (_, l, r) =>
      liftVerdict (rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps)
    | none => .refused .notAnEquation []
  else .refused .illFormed []

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

/-- **`superClaim_sound`**: An accepted `superClaimCheck` certificate establishes `claimMeaning o`
across all ground data instances `ds` of length `o.arity`. -/
theorem superClaim_sound {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok) : claimMeaning o := by
  unfold superClaimCheck at h
  split at h
  · rename_i hw
    unfold claimMeaning
    cases hs : o.sides with
    | none => rw [hs] at h; cases h
    | some triple =>
      obtain ⟨kind, l, r⟩ := triple
      rw [hs] at h
      intro ds hl
      obtain ⟨_, _, _, _, _, hoO, hoS⟩ := wellFormed_parts hw
      have hfree : SubstFree (argSubst (o.args ds)) := argSubst_obsFree (by
        intro a ha
        simp only [ClaimObj.args, List.mem_cons, List.mem_map] at ha
        rcases ha with rfl | rfl | ⟨d, _, rfl⟩
        · exact obsFree_of_observes _ hoO
        · exact obsFree_of_observes _ hoS
        · exact data_obsFree d)
      have hr := rewriteWith_ok (liftVerdict_ok h)
      exact holdsEq_of_observed (replay_sound _ (k := .b) ⟨.inl rfl, fun _ => hfree⟩
        (superClaimResolver_sound o hw ds hl) steps (fun e => by cases e) hr)
  · cases h

/-- **`superClaim_holds`**: Together with a ground observation of the claim's left side at `ds`,
an accepted `superClaimCheck` derivation establishes `Holds (instantiateClaim o.claim o.comp o.layer) ds`. -/
theorem superClaim_holds {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {kind : EqKind} {l r : Term} (hs : o.sides = some (kind, l, r))
    (ds : List Data) (hl : ds.length = o.arity)
    {obs : Observation} (hk : kind.accepts obs = true)
    (hlo : Halts (l.substitute (argSubst (o.args ds))) obs) :
    Holds (instantiateClaim o.claim o.comp o.layer) ds := by
  have hm := superClaim_sound h
  unfold claimMeaning at hm
  rw [hs] at hm
  have hw : o.wellFormed = true := by
    unfold superClaimCheck at h
    split at h
    · assumption
    · cases h
  obtain ⟨_, hO, hS, _, _, _, _⟩ := wellFormed_parts hw
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
  have e : apps (instantiateClaim o.claim o.comp o.layer) (ds.map Data.term) =
      apps o.claim (o.args ds) := rfl
  have he' : equationSides (body.substitute (argSubst (o.args ds))) =
      some (kind, l.substitute (argSubst (o.args ds)), r.substitute (argSubst (o.args ds))) := by
    unfold equationSides at he
    split at he
    · cases he; simp [equationSides]
    · cases he; simp [equationSides]
    · obtain ⟨l0, hu, eq0⟩ := Option.map_eq_some_iff.1 he
      cases eq0
      have := unshift_some hu
      subst this
      simp only [Term.substitute, equationSides, liftSubstitution]
      rw [rename_lift_subst, unshift_rename]
      rfl
    · cases he
  exact holds_of_holdsEq (e ▸ hβ) he' (hm ds hl) hk hlo

theorem superClaimCheck_mono {k k' : Nat} {o : ClaimObj} {steps : List RStep} (le : k ≤ k')
    (hne : superClaimCheck k o steps ≠ .uncovered) :
    superClaimCheck k' o steps = superClaimCheck k o steps := by
  unfold superClaimCheck at hne ⊢
  by_cases hw : o.wellFormed = true
  · simp only [hw, ite_true] at hne ⊢
    cases hs : o.sides with
    | none => rfl
    | some x =>
      obtain ⟨_, l, r⟩ := x
      rw [hs] at hne
      simp only
      rw [rewriteWith_mono le (liftVerdict_ne hne)]
  · simp only [hw] at hne ⊢; rfl

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

/-- **Conservative Extension (`superClaimCheck_of_claimCheck`)**:
Every derivation accepted by `claimCheck` is accepted unchanged by `superClaimCheck`. -/
theorem superClaimCheck_of_claimCheck {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : claimCheck k o steps = .ok) : superClaimCheck k o steps = .ok := by
  unfold claimCheck at h
  unfold superClaimCheck
  split at h
  · rename_i hw
    simp only [hw, ite_true]
    cases hs : o.sides with
    | none => rw [hs] at h; cases h
    | some triple =>
      obtain ⟨kind, l, r⟩ := triple
      rw [hs] at h
      have hrw := liftVerdict_ok h
      have hrep := rewriteWith_ok hrw
      unfold rewriteWith at hrw ⊢
      split at hrw
      · rename_i hsz
        simp only [hsz, ite_true]
        have hext : ∀ X m v, claimResolver o.comp o.self X m = some v →
            superClaimResolver o.comp o.self o.layer X m = some v := by
          intro X m v hv
          cases X with
          | bound i =>
            simp only [claimResolver, superClaimResolver] at hv ⊢
            split at hv
            · rename_i hi; simp [hi, hv]
            · cases hv
          | _ => simp [claimResolver] at hv
        simp only [replay_of_resolver_extends hext steps hrep, termEq_refl', ite_true]
        rfl
      · cases hrw
  · cases h

/-- **`superClaimJudge`**: Complete `Judge` instance for vertical-refinement claims. -/
instance superClaimJudge : Judge ClaimObj (List RStep) where
  Clause := ClaimClause
  Meaning o _ := claimMeaning o
  check := superClaimCheck
  sound := by intro k o steps h; exact superClaim_sound h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ hk; cases hk
  Fragment o := ∃ steps k, superClaimCheck k o steps = .ok
  complete := by rintro o ⟨steps, k, h⟩ _; exact ⟨steps, k, h⟩
  mono := by intro k k' o steps le hne; exact superClaimCheck_mono le hne

/-- Which receiver a late-binding support belongs to (`self` vs `super`). -/
inductive ReceiverKind where
  | selfReceiver
  | superReceiver
  deriving DecidableEq, Repr

/-- A receiver-qualified late-binding support: records whether `self.m` or `super.m` was unfolded,
along with the provider layer name and unfolded body `Option (String × Term)`. -/
structure SuperSupport where
  receiver : ReceiverKind
  member   : String
  unfolded : Option (String × Term)

-- Exact trace of `(X, m)` resolver queries performed during `replay R steps t`.
mutual
def traceReplay (R : Resolver) : List RStep → Term → List (Term × String)
  | [], _ => []
  | s :: rest, t =>
    let q1 := traceApply R s t
    match apply R s t with
    | .ok t' => q1 ++ traceReplay R rest t'
    | .error _ => q1

def traceApply (R : Resolver) : RStep → Term → List (Term × String)
  | .run _, _ => []
  | .assoc _, _ => []
  | .composeAssoc _, _ => []
  | .lateBinding m _, t =>
    match t with
    | .get X m' => if m' == m then [(X, m)] else []
    | _ => []
  | .congr C a inner, t =>
    if Obend.Law.termEq t (instantiate C a) && !observes C then
      traceReplay R inner a
    else []
  | .trans first second, t =>
    let q1 := traceReplay R first t
    match replay R first t with
    | .ok t' => q1 ++ traceReplay R second t'
    | .error _ => q1
end

-- Exact Query-Trace Frame Lemma (`traceReplay_frame`):
-- Two resolvers that agree on every `(X, m)` pair in `traceReplay R steps t` produce the exact
-- same `replay` result AND the exact same query trace.
mutual
theorem traceReplay_frame {R R' : Resolver} :
    ∀ (steps : List RStep) (t : Term),
      (∀ p ∈ traceReplay R steps t, R p.1 p.2 = R' p.1 p.2) →
      replay R steps t = replay R' steps t ∧ traceReplay R steps t = traceReplay R' steps t
  | [], _, _ => ⟨rfl, rfl⟩
  | s :: rest, t, h => by
    have h1 : ∀ p ∈ traceApply R s t, R p.1 p.2 = R' p.1 p.2 := by
      intro p hp
      apply h p
      simp only [traceReplay]
      split
      · exact List.mem_append_left _ hp
      · exact hp
    obtain ⟨happ, htr1⟩ := traceApply_frame s t h1
    simp only [replay, traceReplay, ← happ, ← htr1]
    cases ha : apply R s t with
    | error e => exact ⟨rfl, rfl⟩
    | ok t' =>
      have h2 : ∀ p ∈ traceReplay R rest t', R p.1 p.2 = R' p.1 p.2 := by
        intro p hp
        apply h p
        simp only [traceReplay, ha]
        exact List.mem_append_right _ hp
      obtain ⟨hrep, htr2⟩ := traceReplay_frame rest t' h2
      simp [hrep, htr2]

theorem traceApply_frame {R R' : Resolver} :
    ∀ (s : RStep) (t : Term),
      (∀ p ∈ traceApply R s t, R p.1 p.2 = R' p.1 p.2) →
      apply R s t = apply R' s t ∧ traceApply R s t = traceApply R' s t
  | .run _, _, _ => ⟨rfl, rfl⟩
  | .assoc _, _, _ => ⟨rfl, rfl⟩
  | .composeAssoc _, _, _ => ⟨rfl, rfl⟩
  | .lateBinding m lay, t, h => by
    refine ⟨?_, rfl⟩
    simp only [apply]
    cases t with
    | get X m' =>
      simp only [unfoldAt]
      by_cases hm : (m' == m) = true
      · simp only [hm, ite_true]
        have hq : (X, m) ∈ traceApply R (.lateBinding m lay) (.get X m') := by
          simp [traceApply, hm]
        rw [h (X, m) hq]
      · simp [hm]
    | _ => rfl
  | .congr C a inner, t, h => by
    simp only [apply, traceApply] at h ⊢
    by_cases hc : (Obend.Law.termEq t (instantiate C a) && !observes C) = true
    · simp only [hc, ite_true] at h ⊢
      obtain ⟨hrep, htr⟩ := traceReplay_frame inner a h
      simp [hrep, htr]
    · simp [hc]
  | .trans first second, t, h => by
    have h1 : ∀ p ∈ traceReplay R first t, R p.1 p.2 = R' p.1 p.2 := by
      intro p hp
      apply h p
      simp only [traceApply]
      split
      · exact List.mem_append_left _ hp
      · exact hp
    obtain ⟨hrep1, htr1⟩ := traceReplay_frame first t h1
    simp only [apply, traceApply, ← hrep1, ← htr1]
    cases hr1 : replay R first t with
    | error e => exact ⟨rfl, rfl⟩
    | ok t' =>
      have h2 : ∀ p ∈ traceReplay R second t', R p.1 p.2 = R' p.1 p.2 := by
        intro p hp
        apply h p
        simp only [traceApply, hr1]
        exact List.mem_append_right _ hp
      obtain ⟨hrep2, htr2⟩ := traceReplay_frame second t' h2
      simp [hrep2, htr2]
end

/-- Classify a queried `(X, m)` pair at claim arity `arity` (`selfIdx = arity + 1`) into a
`SuperSupport`, ignoring non-`self`/non-`super` variables (where `superClaimResolver` is `none`). -/
def queryToSuperSupport (C : Composition) (arity layer : Nat) : Term × String → Option SuperSupport
  | (.bound i, m) =>
    let selfIdx := arity + 1
    if i == selfIdx then
      some ⟨.selfReceiver, m, symUnfold C selfIdx m⟩
    else if i == arity then
      some ⟨.superReceiver, m, superSymUnfold C selfIdx layer m⟩
    else none
  | _ => none

/-- Extract the exact receiver-qualified `SuperSupport` list of `(o, steps)`. -/
def superSupports (o : ClaimObj) (steps : List RStep) : List SuperSupport :=
  match o.sides with
  | some (_, l, _) =>
    (traceReplay (superClaimResolver o.comp o.self o.layer) steps l).filterMap
      (queryToSuperSupport o.comp o.arity o.layer)
  | none => []

/-- Whether a `SuperSupport` holds at composition `C'` and layer index `j'` for claim arity `arity`. -/
@[expose] def SuperSupport.holds (C' : Composition) (arity j' : Nat) (sp : SuperSupport) : Bool :=
  let selfIdx := arity + 1
  match sp.receiver with
  | .selfReceiver  => optEq (symUnfold C' selfIdx sp.member) sp.unfolded
  | .superReceiver => optEq (superSymUnfold C' selfIdx j' sp.member) sp.unfolded

/-- Packaged vertical-refinement claim certificate recording its `selfSupports` and `superSupports`
explicitly for $O(1)$ support-sheaf transport (`Obend.Slot.SupportSheaf`). -/
structure SuperClaimCert where
  claim         : Term
  arity         : Nat
  grade         : Nat
  steps         : List RStep
  selfSupports  : List Support
  superSupports : List Support

/-- Build a `SuperClaimCert` from a `ClaimObj` and `steps`, splitting `superSupports o steps`
into explicit `selfSupports` and `superSupports` lists. -/
def mkSuperClaimCert (k : Nat) (o : ClaimObj) (steps : List RStep) : SuperClaimCert :=
  let sps := superSupports o steps
  { claim := o.claim
    arity := o.arity
    grade := k
    steps := steps
    selfSupports := sps.filterMap fun sp =>
      match sp.receiver with
      | .selfReceiver => some ⟨sp.member, sp.unfolded⟩
      | .superReceiver => none
    superSupports := sps.filterMap fun sp =>
      match sp.receiver with
      | .selfReceiver => none
      | .superReceiver => some ⟨sp.member, sp.unfolded⟩ }

/-- Combined receiver-qualified support list of a `SuperClaimCert`. -/
@[expose] def SuperClaimCert.allSupports (cert : SuperClaimCert) : List SuperSupport :=
  (cert.selfSupports.map fun s => ⟨.selfReceiver, s.member, s.unfolded⟩) ++
  (cert.superSupports.map fun s => ⟨.superReceiver, s.member, s.unfolded⟩)

theorem mkSuperClaimCert_arity (k : Nat) (o : ClaimObj) (steps : List RStep) :
    (mkSuperClaimCert k o steps).arity = o.arity := by
  unfold mkSuperClaimCert; rfl

theorem mkSuperClaimCert_steps (k : Nat) (o : ClaimObj) (steps : List RStep) :
    (mkSuperClaimCert k o steps).steps = steps := by
  unfold mkSuperClaimCert; rfl

theorem mem_allSupports_of_mem_superSupports {k : Nat} {o : ClaimObj} {steps : List RStep}
    {sp : SuperSupport} (h : sp ∈ superSupports o steps) :
    sp ∈ (mkSuperClaimCert k o steps).allSupports := by
  simp only [SuperClaimCert.allSupports, mkSuperClaimCert, List.mem_append, List.mem_map,
    List.mem_filterMap]
  cases sp with
  | mk rcv m unf =>
    cases rcv with
    | selfReceiver =>
      left
      exact ⟨⟨m, unf⟩, ⟨⟨.selfReceiver, m, unf⟩, h, rfl⟩, rfl⟩
    | superReceiver =>
      right
      exact ⟨⟨m, unf⟩, ⟨⟨.superReceiver, m, unf⟩, h, rfl⟩, rfl⟩

theorem mem_superSupports_of_mem_allSupports {k : Nat} {o : ClaimObj} {steps : List RStep}
    {sp : SuperSupport} (h : sp ∈ (mkSuperClaimCert k o steps).allSupports) :
    sp ∈ superSupports o steps := by
  simp only [SuperClaimCert.allSupports, mkSuperClaimCert, List.mem_append, List.mem_map] at h
  rcases h with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · simp only [List.mem_filterMap] at hs
    obtain ⟨sp0, h0, hmap⟩ := hs
    cases sp0 with
    | mk rcv m unf =>
      cases rcv <;> simp at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h0
  · simp only [List.mem_filterMap] at hs
    obtain ⟨sp0, h0, hmap⟩ := hs
    cases sp0 with
    | mk rcv m unf =>
      cases rcv <;> simp at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h0

theorem optEq_refl (x : Option (String × Term)) : optEq x x = true := by
  cases x with
  | none => rfl
  | some p => simp [optEq, termEq_refl']

theorem superSupports_holds_self (o : ClaimObj) (steps : List RStep) :
    ∀ sp ∈ superSupports o steps, SuperSupport.holds o.comp o.arity o.layer sp = true := by
  intro sp hsp
  simp only [superSupports] at hsp
  split at hsp
  · simp only [List.mem_filterMap] at hsp
    obtain ⟨q, _, hq⟩ := hsp
    cases q with
    | mk X m =>
      cases X with
      | bound i =>
        simp only [queryToSuperSupport] at hq
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true, Option.some.injEq] at hq
          subst hq
          simp [SuperSupport.holds, optEq_refl]
        · simp only [hi1, Bool.false_eq_true, ite_false] at hq
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true, Option.some.injEq] at hq
            subst hq
            simp [SuperSupport.holds, optEq_refl]
          · simp [hi2] at hq
      | _ => simp [queryToSuperSupport] at hq
  · cases hsp

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.filterMap f = xs.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **Coarse Member-List Frame Rule (`superClaim_frame_members`)**:
If both `symUnfold` and `superSymUnfold` agree on every member named in `membersList steps`,
an accepted `superClaimCheck` derivation remains accepted unchanged at `(C', j')`. -/
theorem superClaim_frame_members {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat}
    (hself : ∀ m ∈ membersList steps, symUnfold C' o.self m = symUnfold o.comp o.self m)
    (hsuper : ∀ m ∈ membersList steps,
      superSymUnfold C' o.self j' m = superSymUnfold o.comp o.self o.layer m)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok := by
  unfold superClaimCheck at h ⊢
  rw [hwf]
  split at h
  · simp only [ite_true]
    have hside : ({ o with comp := C', layer := j' } : ClaimObj).sides = o.sides := rfl
    rw [hside]
    split at h
    · rename_i kind l r hs
      change liftVerdict (rewriteWith (superClaimResolver C' o.self j') k l r steps) = .ok
      have hsame : rewriteWith (superClaimResolver C' o.self j') k l r steps =
          rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps := by
        unfold rewriteWith
        rw [replay_frame steps (R := superClaimResolver C' o.self j')
          (R' := superClaimResolver o.comp o.self o.layer) (by
          intro X m hm
          cases X with
          | bound i =>
            simp only [superClaimResolver]
            rw [hself m hm, hsuper m hm]
          | _ => rfl) l]
      rw [hsame]
      exact h
    · cases h
  · cases h

/-- **`T3_super_claim_frame` (Exact Receiver-Qualified Vertical + Horizontal Frame Transport)**:
An accepted `superClaimCheck` certificate remains accepted **unchanged** (and traces the exact
same `superSupports`) in ANY well-formed composition `C'` at layer `j'` where every traced
`SuperSupport` holds — even if outer layers above `j'` in `C'` override members in `superSupports`! -/
theorem T3_super_claim_frame {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok)
    {C' : Composition} {j' : Nat}
    (hsup : ∀ sp ∈ superSupports o steps, SuperSupport.holds C' o.arity j' sp = true)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok ∧
    superSupports { o with comp := C', layer := j' } steps = superSupports o steps := by
  have hw0 : o.wellFormed = true := by
    unfold superClaimCheck at h
    split at h
    · assumption
    · cases h
  unfold superClaimCheck at h ⊢
  simp only [hw0, hwf, ite_true] at h ⊢
  have hside : ({ o with comp := C', layer := j' } : ClaimObj).sides = o.sides := rfl
  rw [hside]
  cases hs : o.sides with
  | none => rw [hs] at h; cases h
  | some triple =>
    obtain ⟨kind, l, r⟩ := triple
    rw [hs] at h
    have hq_agree : ∀ p ∈ traceReplay (superClaimResolver o.comp o.self o.layer) steps l,
        superClaimResolver o.comp o.self o.layer p.1 p.2 =
          superClaimResolver C' o.self j' p.1 p.2 := by
      intro ⟨X, m⟩ hp
      cases X with
      | bound i =>
        simp only [superClaimResolver, ClaimObj.self]
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true]
          have hmem : (⟨.selfReceiver, m, symUnfold o.comp (o.arity + 1) m⟩ : SuperSupport) ∈
              superSupports o steps := by
            simp only [superSupports, hs, List.mem_filterMap]
            exact ⟨(.bound i, m), hp, by simp [queryToSuperSupport, hi1]⟩
          exact (optEq_sound (hsup _ hmem)).symm
        · simp only [hi1, Bool.false_eq_true, ite_false]
          have hpos : o.arity + 1 > 0 := Nat.zero_lt_succ o.arity
          simp only [hpos, decide_true, Bool.true_and, Nat.add_sub_cancel]
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true]
            have hmem : (⟨.superReceiver, m, superSymUnfold o.comp (o.arity + 1) o.layer m⟩ : SuperSupport) ∈
                superSupports o steps := by
              simp only [superSupports, hs, List.mem_filterMap]
              exact ⟨(.bound i, m), hp, by simp [queryToSuperSupport, hi1, hi2]⟩
            exact (optEq_sound (hsup _ hmem)).symm
          · simp [hi2]
      | _ => rfl
    obtain ⟨hrep, htr⟩ := traceReplay_frame steps l hq_agree
    refine ⟨?_, ?_⟩
    · change liftVerdict (rewriteWith (superClaimResolver C' o.self j') k l r steps) = .ok
      have hrw : rewriteWith (superClaimResolver C' o.self j') k l r steps =
          rewriteWith (superClaimResolver o.comp o.self o.layer) k l r steps := by
        unfold rewriteWith
        rw [← hrep]
      rw [hrw]
      exact h
    · simp only [superSupports, hside, hs] at htr ⊢
      have hself_eq : ({ o with comp := C', layer := j' } : ClaimObj).self = o.self := rfl
      rw [hself_eq, ← htr]
      apply filterMap_congr_mem
      intro ⟨X, m⟩ hp
      cases X with
      | bound i =>
        simp only [queryToSuperSupport]
        by_cases hi1 : (i == o.arity + 1) = true
        · simp only [hi1, ite_true]
          have heq := hq_agree (.bound i, m) hp
          simp only [superClaimResolver, ClaimObj.self, hi1, ite_true] at heq
          rw [heq]
        · simp only [hi1, Bool.false_eq_true, ite_false]
          by_cases hi2 : (i == o.arity) = true
          · simp only [hi2, ite_true]
            have heq := hq_agree (.bound i, m) hp
            have hpos : o.arity + 1 > 0 := Nat.zero_lt_succ o.arity
            simp only [superClaimResolver, ClaimObj.self, hi1, Bool.false_eq_true, ite_false,
              hpos, decide_true, Bool.true_and, Nat.add_sub_cancel, hi2, ite_true] at heq
            rw [heq]
          · simp [hi2]
      | _ => rfl

/-- Slot formulation of `superClaimCheck` over `SuperSupport`. -/
def superClaimSlot (o : ClaimObj) (k : Nat) : Obend.Slot.Slot SuperSupport (List RStep) where
  supports := superSupports o
  judge steps := superClaimCheck k o steps == .ok

/-- Reading `.usable` from `superClaimSlot` at `(C', j')` guarantees `superClaimCheck = .ok` at `(C', j')`. -/
theorem superUsable_checks {o : ClaimObj} {k : Nat} {steps : List RStep}
    {C' : Composition} {j' : Nat} {ev : List (SuperSupport × Bool)}
    (h : (superClaimSlot o k).read (SuperSupport.holds C' o.arity j') (some steps) = .usable steps ev)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := C', layer := j' } steps = .ok := by
  have ⟨hj, hall⟩ := (Obend.Slot.read_usable_supports _ _ steps).1 ⟨ev, h⟩
  have hok : superClaimCheck k o steps = .ok := by simpa [superClaimSlot] using hj
  exact (T3_super_claim_frame hok hall hwf).1

/-! ## 4. Concrete 2-Layer & 3-Layer Vertical Refinement Witnesses & Old-`claimCheck` Impossibility -/

/-- Base layer `"Base"`: `limit = 10`, `scale = 2`, `apply = λx. self.scale * x` (open recursion). -/
@[expose] def verticalBaseLayer : Layer where
  name := "Base"
  metadata := .inject "declared" (.record [("name", .label "Base")])
  fields :=
    [ ("limit", .nat 10)
    , ("scale", .nat 2)
    , ("apply", .lam (.binary .multiply (.get (.bound 2) "scale") (.bound 0))) ]

/-- Refined layer `"Refined"`: overrides `limit = 20`, `scale = 3`, and refines `apply` via `super.apply`. -/
@[expose] def verticalRefinedLayer : Layer where
  name := "Refined"
  metadata := .inject "declared" (.record [("name", .label "Refined")])
  fields :=
    [ ("limit", .nat 20)
    , ("scale", .nat 3)
    , ("apply", .lam (.binary .add (.app (.get (.bound 1) "apply") (.bound 0)) (.nat 1))) ]

/-- Two-layer composition `⟨Refined, [Base], []⟩`. -/
@[expose] def verticalComp : Composition :=
  ⟨verticalRefinedLayer, [verticalBaseLayer], []⟩

/-- Vertical spec-refinement claim (`arity = 0`) on `"Refined"` (`layer = 0`):
`λself. λsuper. (self.limit - super.limit) == 10`. -/
def verticalLimitClaimObj : ClaimObj where
  comp := verticalComp
  layer := 0
  claim := .lam (.lam
    (.binary .equal
      (.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit"))
      (.nat 10)))
  arity := 0

/-- Derivation proving `self.limit - super.limit == 10` under `superClaimCheck`:
unfold `self.limit` in `"Refined"` (`20`), unfold `super.limit` in `"Base"` (`10`), step `20 - 10 → 10`. -/
def verticalLimitSteps : List RStep :=
  [ .congr (.binary .subtract (.bound 0) (.get (.bound 1) "limit")) (.get (.bound 1) "limit")
      [.lateBinding "limit" "Refined"]
  , .congr (.binary .subtract (.nat 20) (.bound 0)) (.get (.bound 0) "limit")
      [.lateBinding "limit" "Base"]
  , .run 1 ]

def optTermEqB : Option Term → Option Term → Bool
  | none, none => true
  | some a, some b => Obend.Law.termEq a b
  | _, _ => false

theorem optTermEqB_sound {x y : Option Term} (h : optTermEqB x y = true) : x = y := by
  cases x with
  | none => cases y <;> simp [optTermEqB] at h; rfl
  | some a =>
    cases y with
    | none => simp [optTermEqB] at h
    | some b =>
      simp only [optTermEqB] at h
      exact congrArg some (termEq_sound' h)

/-- **Inhabited Witness 1 (`superClaimCheck` accepts vertical `super.limit` claim)**:
`verticalLimitSteps` is accepted by `superClaimCheck` and establishes `Holds` at `[]`. -/
theorem verticalLimit_superClaim_accepted :
    superClaimCheck 10 verticalLimitClaimObj verticalLimitSteps = .ok ∧
    Holds (instantiateClaim verticalLimitClaimObj.claim verticalComp 0) [] := by
  have hok : superClaimCheck 10 verticalLimitClaimObj verticalLimitSteps = .ok := by
    decide +kernel
  have hrun : Obend.Law.run 100
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute
        (argSubst (verticalLimitClaimObj.args []))) = some (.nat 10) :=
    optTermEqB_sound (by decide +kernel)
  have hhalts : Halts
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute
        (argSubst (verticalLimitClaimObj.args []))) (.natural 10) :=
    ⟨.nat 10, Obend.Law.run_sound 100 hrun, .natural 10⟩
  exact ⟨hok, superClaim_holds hok rfl [] rfl rfl hhalts⟩

/-- Countermodel substitution fixing `self := verticalComp.object` (`limit = 20`) while varying
`super := { limit = 0 }`, witnessing that `claimResolver` is completely blind to `super`. -/
def altSuperSubst : Nat → Term
  | 0 => .record [("limit", .nat 0)]
  | 1 => verticalComp.object
  | n + 2 => .bound n

theorem altSuperSubst_free : SubstFree altSuperSubst := by
  intro n
  match n with
  | 0 => exact obsFree_of_observes (.record [("limit", .nat 0)]) (by decide +kernel)
  | 1 => exact obsFree_of_observes verticalComp.object (by decide +kernel)
  | k + 2 => exact .bound k

theorem altSuperSubst_claimResolver_sound :
    RSound (claimResolver verticalComp 1) altSuperSubst := by
  have hw : verticalLimitClaimObj.wellFormed = true := by decide +kernel
  obtain ⟨_, _, _, hct, hseed, _, _⟩ := wellFormed_parts hw
  intro X m layer u h
  cases X with
  | bound i =>
    simp only [claimResolver] at h
    split at h
    · rename_i hi
      have hi1 : i = 1 := beq_iff_eq.1 hi
      subst hi1
      obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      have hs := steps_substitute altSuperSubst
        (unfoldIn_steps (.bound 1) verticalComp.seed m _ verticalComp.layers hu)
      have hctEq : (composeTerm verticalComp.top verticalComp.below).substitute altSuperSubst =
          composeTerm verticalComp.top verticalComp.below :=
        closed_subst hct altSuperSubst
      have hseedEq : (Term.record verticalComp.seed).substitute altSuperSubst =
          .record verticalComp.seed :=
        closed_subst hseed altSuperSubst
      have e1 : (Term.get (superBelow (.bound 1) verticalComp.seed verticalComp.layers) m).substitute
          altSuperSubst =
          .get (superBelow verticalComp.object verticalComp.seed verticalComp.layers) m := by
        rw [show verticalComp.layers = verticalComp.top :: verticalComp.below from rfl]
        simp only [superBelow, Term.substitute]
        have hrecNil : List.map (fun field : String × Term => (field.1, field.2.substitute altSuperSubst))
            verticalComp.seed = verticalComp.seed := by
          have := hseedEq
          simpa only [Term.substitute, Term.record.injEq] using this
        rw [hctEq, hrecNil]
        rfl
      rw [e1] at hs
      simpa only [Term.substitute, altSuperSubst] using steps_trans (object_get verticalComp m) hs
    · cases h
  | _ => simp [claimResolver] at h

/-- **Universal Separation Theorem (`verticalLimit_impossible_claimCheck`)**:
For EVERY grade `k` and EVERY derivation `steps`, old `claimCheck` CANNOT accept
`verticalLimitClaimObj` (`claimCheck k verticalLimitClaimObj steps ≠ .ok`), whereas
`superClaimCheck` proves it in 3 steps! -/
theorem verticalLimit_impossible_claimCheck (k : Nat) (steps : List RStep) :
    claimCheck k verticalLimitClaimObj steps ≠ .ok := by
  intro hok
  have hw : verticalLimitClaimObj.wellFormed = true := by decide +kernel
  have hside : verticalLimitClaimObj.sides =
      some (.nat, .binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit"), .nat 10) := rfl
  unfold claimCheck at hok
  simp only [hw, ite_true, hside, ClaimObj.self] at hok
  have hrep := rewriteWith_ok (liftVerdict_ok hok)
  have heq : HoldsEq
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst)
      ((Term.nat 10).substitute altSuperSubst) :=
    holdsEq_of_observed (replay_sound (claimResolver verticalComp 1) (k := .b)
      ⟨.inl rfl, fun _ => altSuperSubst_free⟩ altSuperSubst_claimResolver_sound steps
      (fun e => by cases e) hrep)
  have hrun20 : Obend.Law.run 100
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst) =
      some (.nat 20) := optTermEqB_sound (by decide +kernel)
  have hhalts20 : Halts
      ((Term.binary .subtract (.get (.bound 1) "limit") (.get (.bound 0) "limit")).substitute altSuperSubst)
      (.natural 20) :=
    ⟨.nat 20, Obend.Law.run_sound 100 hrun20, .natural 20⟩
  obtain ⟨v, hvEval, hvObs⟩ := (heq (.natural 20)).1 hhalts20
  cases hvObs
  simp only [Term.substitute] at hvEval
  have h10_eq_20 : Term.nat 10 = Term.nat 20 :=
    Obend.Law.evaluates_unique ⟨.refl _, .natural 10⟩ hvEval
  cases h10_eq_20

/-- Open-recursion + vertical-refinement claim (`arity = 1`) on `"Refined"` (`layer = 0`):
`∀ x, (super.apply x) + 1 == (3 * x) + 1`, where `Base.apply` calls `self.scale` (overridden to `3`
in `"Refined"`!). -/
@[expose] def verticalOpenRecClaimObj : ClaimObj where
  comp := verticalComp
  layer := 0
  claim := .lam (.lam (.lam
    (.binary .equal
      (.binary .add (.app (.get (.bound 1) "apply") (.bound 0)) (.nat 1))
      (.binary .add (.binary .multiply (.nat 3) (.bound 0)) (.nat 1)))))
  arity := 1

/-- Derivation proving `∀ x, (super.apply x) + 1 == (3 * x) + 1`:
1. unfold `super.apply` in `"Base"` (yielding `λx. self.scale * x` with `self` kept at `.bound 2`),
2. symbolically β-reduce `(λx. self.scale * x) x` to `self.scale * x`,
3. unfold `self.scale` in `"Refined"` (`3`). -/
def verticalOpenRecSteps : List RStep :=
  [ .congr (.binary .add (.app (.bound 0) (.bound 1)) (.nat 1))
      (.get (.bound 1) "apply")
      [.lateBinding "apply" "Base"]
  , .congr (.binary .add (.bound 0) (.nat 1))
      (.app (.lam (.binary .multiply (.get (.bound 3) "scale") (.bound 0))) (.bound 0))
      [.run 1]
  , .congr (.binary .add (.binary .multiply (.bound 0) (.bound 1)) (.nat 1))
      (.get (.bound 2) "scale")
      [.lateBinding "scale" "Refined"] ]

/-- The `selfSupports` member footprint of `verticalOpenRecClaimObj` is `[ "scale" ]`
(`"apply"` is recorded in `superSupports`, NOT `selfSupports`!). -/
theorem verticalOpenRec_selfSupport_members :
    (mkSuperClaimCert 15 verticalOpenRecClaimObj verticalOpenRecSteps).selfSupports.map (·.member) =
      ["scale"] := by
  decide +kernel

/-- Outer wrapper layer `"AuditWrapper"` overriding `"apply"` (`λx. 999`) while leaving `"scale"` alone. -/
@[expose] def auditWrapperLayer : Layer where
  name := "AuditWrapper"
  metadata := .inject "declared" (.record [("name", .label "AuditWrapper")])
  fields :=
    [ ("apply", .lam (.nat 999))
    , ("auditTag", .label "v1") ]

/-- Extended 3-layer composition `⟨AuditWrapper, [Refined, Base], []⟩` shifting `"Refined"` to `layer = 1`. -/
def wrappedVerticalComp : Composition :=
  ⟨auditWrapperLayer, [verticalRefinedLayer, verticalBaseLayer], []⟩

/-- **Inhabited Witness 2 (`T3_super_claim_frame` across `"apply"`-overriding wrapper)**:
1. `verticalOpenRecSteps` is accepted at `verticalComp` (`layer = 0`), establishing `claimMeaning`
   across ALL data instances `ds`, and
2. `T3_super_claim_frame` transports `verticalOpenRecSteps` **unchanged** to `wrappedVerticalComp`
   at `layer = 1`, even though `auditWrapperLayer` overrides `"apply"` (`symUnfold` of `"apply"` changed,
   while `superSymUnfold` of `"apply"` at `layer = 1` and `symUnfold` of `"scale"` remain intact!). -/
theorem verticalOpenRec_frame_transport_accepted :
    superClaimCheck 15 verticalOpenRecClaimObj verticalOpenRecSteps = .ok ∧
    symUnfold wrappedVerticalComp 2 "apply" ≠ symUnfold verticalComp 2 "apply" ∧
    superClaimCheck 15 { verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 }
      verticalOpenRecSteps = .ok := by
  have hok0 : superClaimCheck 15 verticalOpenRecClaimObj verticalOpenRecSteps = .ok := by
    decide +kernel
  have hdiff : symUnfold wrappedVerticalComp 2 "apply" ≠ symUnfold verticalComp 2 "apply" := by
    intro heq
    have hneq : optEq (symUnfold wrappedVerticalComp 2 "apply")
        (symUnfold verticalComp 2 "apply") = false := by decide +kernel
    rw [heq] at hneq
    have hrefl : optEq (symUnfold verticalComp 2 "apply")
        (symUnfold verticalComp 2 "apply") = true := by decide +kernel
    rw [hrefl] at hneq
    cases hneq
  have hsup : ∀ sp ∈ superSupports verticalOpenRecClaimObj verticalOpenRecSteps,
      SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1 sp = true := by
    have hall : (superSupports verticalOpenRecClaimObj verticalOpenRecSteps).all
        (SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1) = true := by
      decide +kernel
    exact List.all_eq_true.1 hall
  have hwf : ({ verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 } : ClaimObj).wellFormed = true := by
    decide +kernel
  exact ⟨hok0, hdiff, (T3_super_claim_frame hok0 hsup hwf).1⟩

/-- **Refutation Tooth (`wrongSuperProvider_refused`)**:
Naming `"Refined"` instead of `"Base"` when unfolding `super.limit` is refused with `.stepMismatch`! -/
def wrongSuperProviderSteps : List RStep :=
  [ .congr (.binary .subtract (.nat 20) (.bound 0)) (.get (.bound 0) "limit")
      [.lateBinding "limit" "Refined"] ]

theorem wrongSuperProvider_refused :
    superClaimCheck 10 verticalLimitClaimObj wrongSuperProviderSteps =
      .refused (.rewrite .stepMismatch) [0] := by
  decide +kernel

end Obend.Logic

end
