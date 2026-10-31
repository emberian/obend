module
/- Yields under `Ahead`, and `≈b` over `Interaction` traces (`review/EQUIV-PLAN-20261031.md` §5,
lane 1). A term that yields is stuck, so a term ahead of it yields at once, in a related context
with a related plan (`yields_behind`); a term behind a yielding term reaches a related yield by
reduction (`yields_ahead`). Plugging a response into related contexts gives related terms, so every
turn of an activity transfers both ways (`interaction_behind`, `interaction_ahead`).

`IEquiv` is `≈b` with the turns counted: under every substitution and context, the two plugged
terms have the same interaction traces, with the same responses, equivalent plans (`≈b`), and the
same final observation. It implies `≈b` (`IEquiv.bequiv`: the trace with no turns), and
`mix` is associative for it (`mix_assoc_interaction`). -/
public import Obend.Equiv.Behaviour
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

/-! ## Related evaluation contexts -/

/-- Two lists related position by position. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.snoc {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} {a : α} {b : β}
    (h : ListRel R as bs) (hab : R a b) : ListRel R (as ++ [a]) (bs ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hx _ ih => exact .cons hx ih

/-- Two evaluation frames of the same kind whose terms are related by `Ahead`. -/
inductive FrameAhead : SourceFrame → SourceFrame → Prop where
  | application {a a' : Term} : Ahead a a' → FrameAhead (.application a) (.application a')
  | field (name : String) : FrameAhead (.field name) (.field name)
  | extend {fs fs' : List (String × Term)} : fs.map Prod.fst = fs'.map Prod.fst →
      (∀ p ∈ fs.zip fs', Ahead p.1.2 p.2.2) → FrameAhead (.extend fs) (.extend fs')
  | binaryLeft (op : Primitive) {r r' : Term} : Ahead r r' → FrameAhead (.binaryLeft op r) (.binaryLeft op r')
  | binaryRight (op : Primitive) {l l' : Term} : Ahead l l' →
      FrameAhead (.binaryRight op l) (.binaryRight op l')
  | condition {z z' s s' : Term} : Ahead z z' → Ahead s s' →
      FrameAhead (.condition z s) (.condition z' s')
  | case {arms arms' : List (String × Term)} : arms.map Prod.fst = arms'.map Prod.fst →
      (∀ p ∈ arms.zip arms', Ahead p.1.2 p.2.2) → FrameAhead (.case arms) (.case arms')
  | ifBool {x x' y y' : Term} : Ahead x x' → Ahead y y' → FrameAhead (.ifBool x y) (.ifBool x' y')
  | reflect : FrameAhead .reflect .reflect
  | metadata : FrameAhead .metadata .metadata
  | project : FrameAhead .project .project

theorem FrameAhead.plug {f f' : SourceFrame} {h h' : Term} (hf : FrameAhead f f') (hh : Ahead h h') :
    Ahead (f.plug h) (f'.plug h') := by
  cases hf with
  | application ha => exact .app hh ha
  | field name => exact .get name hh
  | extend names rel => exact .extend hh names rel
  | binaryLeft op hr => exact .binary op hh hr
  | binaryRight op hl => exact .binary op hl hh
  | condition hz hs => exact .ifZero hh hz hs
  | case names rel => exact .case hh names rel
  | ifBool hx hy => exact .ifBool hh hx hy
  | reflect => exact .reflect hh
  | metadata => exact .metadata hh
  | project => exact .project hh

/-- Contexts related frame by frame. -/
abbrev ContextAhead (ctx ctx' : List SourceFrame) : Prop := ListRel FrameAhead ctx ctx'

theorem ContextAhead.plug {ctx ctx' : List SourceFrame} (hc : ContextAhead ctx ctx') :
    ∀ {h h' : Term}, Ahead h h' → Ahead (Obend.Core.Term.plug ctx h) (Obend.Core.Term.plug ctx' h') := by
  induction hc with
  | nil => intro h h' hh; exact hh
  | cons hf _ ih => intro h h' hh; exact ih (hf.plug hh)

theorem ContextAhead.snoc {ctx ctx' : List SourceFrame} {f f' : SourceFrame}
    (hc : ContextAhead ctx ctx') (hf : FrameAhead f f') : ContextAhead (ctx ++ [f]) (ctx' ++ [f']) :=
  ListRel.snoc hc hf

/-! ## Yields transfer both ways -/

/-- A term ahead of a yielding term yields, with no reduction, in a related context. -/
theorem yields_behind {t t' : Term} (h : Ahead t t') :
    ∀ {plan : Term} {ctx : List SourceFrame}, Yields t plan ctx →
      ∃ plan' ctx', Yields t' plan' ctx' ∧ Ahead plan plan' ∧ ContextAhead ctx ctx' := by
  induction h with
  | run s _ ih =>
    intro plan ctx y
    cases s with
    | refl => exact ih y
    | next st _ => exact absurd st (yields_no_step y _)
  | perform hp => intro plan ctx y; cases y; exact ⟨_, _, .perform _, hp, .nil⟩
  | app hf ha ihf _ =>
    intro plan ctx y
    cases y with
    | application _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ihf inner
      exact ⟨p, _, .application _ y', hp, hc.snoc (.application ha)⟩
  | get name hg ih =>
    intro plan ctx y
    cases y with
    | field _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ih inner
      exact ⟨p, _, .field _ y', hp, hc.snoc (.field name)⟩
  | extend hi names rel ih _ =>
    intro plan ctx y
    cases y with
    | extend _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ih inner
      exact ⟨p, _, .extend _ y', hp, hc.snoc (.extend names rel)⟩
  | binary op hl hr ihl ihr =>
    intro plan ctx y
    cases y with
    | binaryLeft _ _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ihl inner
      exact ⟨p, _, .binaryLeft _ _ y', hp, hc.snoc (.binaryLeft op hr)⟩
    | binaryRight _ v inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ihr inner
      exact ⟨p, _, .binaryRight _ (inv_value_behind v hl) y', hp, hc.snoc (.binaryRight op hl)⟩
  | ifZero hv hz hs ihv _ _ =>
    intro plan ctx y
    cases y with
    | condition _ _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ihv inner
      exact ⟨p, _, .condition _ _ y', hp, hc.snoc (.condition hz hs)⟩
  | case hsc names rel ih _ =>
    intro plan ctx y
    cases y with
    | case _ inner =>
      obtain ⟨p, c, y', hp, hc⟩ := ih inner
      exact ⟨p, _, .case _ y', hp, hc.snoc (.case names rel)⟩
  | ifBool hc hx hy ih _ _ =>
    intro plan ctx y
    cases y with
    | ifBool _ _ inner =>
      obtain ⟨p, c, y', hp, hctx⟩ := ih inner
      exact ⟨p, _, .ifBool _ _ y', hp, hctx.snoc (.ifBool hx hy)⟩
  | reflect hp ih =>
    intro plan ctx y
    cases y with
    | reflect inner =>
      obtain ⟨p, c, y', hpl, hc⟩ := ih inner
      exact ⟨p, _, .reflect y', hpl, hc.snoc .reflect⟩
  | metadata hp ih =>
    intro plan ctx y
    cases y with
    | metadata inner =>
      obtain ⟨p, c, y', hpl, hc⟩ := ih inner
      exact ⟨p, _, .metadata y', hpl, hc.snoc .metadata⟩
  | project hp ih =>
    intro plan ctx y
    cases y with
    | project inner =>
      obtain ⟨p, c, y', hpl, hc⟩ := ih inner
      exact ⟨p, _, .project y', hpl, hc.snoc .project⟩
  | hole => intro plan ctx y; cases y
  | bound => intro plan ctx y; cases y
  | lam => intro plan ctx y; cases y
  | mix => intro plan ctx y; cases y
  | fix => intro plan ctx y; cases y
  | specification => intro plan ctx y; cases y
  | prototype => intro plan ctx y; cases y
  | nat => intro plan ctx y; cases y
  | boolean => intro plan ctx y; cases y
  | label => intro plan ctx y; cases y
  | record => intro plan ctx y; cases y
  | inject => intro plan ctx y; cases y
  | done => intro plan ctx y; cases y

/-- A term behind a yielding term reaches, by reduction, a yield with a related plan and context. -/
theorem yields_ahead {t t' : Term} (h : Ahead t t') :
    ∀ {plan' : Term} {ctx' : List SourceFrame}, Yields t' plan' ctx' →
      ∃ u plan ctx, Steps t u ∧ Yields u plan ctx ∧ Ahead plan plan' ∧ ContextAhead ctx ctx' := by
  induction h with
  | run s _ ih =>
    intro plan' ctx' y
    obtain ⟨u, p, c, s2, y', hp, hc⟩ := ih y
    exact ⟨u, p, c, steps_trans s s2, y', hp, hc⟩
  | perform hp => intro plan' ctx' y; cases y; exact ⟨_, _, _, .refl _, .perform _, hp, .nil⟩
  | app hf ha ihf _ =>
    intro plan' ctx' y
    cases y with
    | application _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ihf inner
      exact ⟨_, p, _, steps_app _ s, .application _ y', hp, hc.snoc (.application ha)⟩
  | get name hg ih =>
    intro plan' ctx' y
    cases y with
    | field _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ih inner
      exact ⟨_, p, _, steps_get _ s, .field _ y', hp, hc.snoc (.field name)⟩
  | extend hi names rel ih _ =>
    intro plan' ctx' y
    cases y with
    | extend _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ih inner
      exact ⟨_, p, _, steps_extend _ s, .extend _ y', hp, hc.snoc (.extend names rel)⟩
  | binary op hl hr ihl ihr =>
    intro plan' ctx' y
    cases y with
    | binaryLeft _ _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ihl inner
      exact ⟨_, p, _, steps_binaryLeft _ _ s, .binaryLeft _ _ y', hp, hc.snoc (.binaryLeft op hr)⟩
    | binaryRight _ v inner =>
      obtain ⟨l0, sl, vl, al⟩ := inv_value_ahead v hl
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ihr inner
      exact ⟨_, p, _, steps_trans (steps_binaryLeft _ _ sl) (steps_binaryRight _ vl s),
        .binaryRight _ vl y', hp, hc.snoc (.binaryRight op al)⟩
  | ifZero hv hz hs ihv _ _ =>
    intro plan' ctx' y
    cases y with
    | condition _ _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ihv inner
      exact ⟨_, p, _, steps_ifZero _ _ s, .condition _ _ y', hp, hc.snoc (.condition hz hs)⟩
  | case hsc names rel ih _ =>
    intro plan' ctx' y
    cases y with
    | case _ inner =>
      obtain ⟨u, p, c, s, y', hp, hc⟩ := ih inner
      exact ⟨_, p, _, steps_case _ s, .case _ y', hp, hc.snoc (.case names rel)⟩
  | ifBool hc hx hy ih _ _ =>
    intro plan' ctx' y
    cases y with
    | ifBool _ _ inner =>
      obtain ⟨u, p, c, s, y', hp, hctx⟩ := ih inner
      exact ⟨_, p, _, steps_ifBool _ _ s, .ifBool _ _ y', hp, hctx.snoc (.ifBool hx hy)⟩
  | reflect hp ih =>
    intro plan' ctx' y
    cases y with
    | reflect inner =>
      obtain ⟨u, p, c, s, y', hpl, hc⟩ := ih inner
      exact ⟨_, p, _, steps_reflect s, .reflect y', hpl, hc.snoc .reflect⟩
  | metadata hp ih =>
    intro plan' ctx' y
    cases y with
    | metadata inner =>
      obtain ⟨u, p, c, s, y', hpl, hc⟩ := ih inner
      exact ⟨_, p, _, steps_metadata s, .metadata y', hpl, hc.snoc .metadata⟩
  | project hp ih =>
    intro plan' ctx' y
    cases y with
    | project inner =>
      obtain ⟨u, p, c, s, y', hpl, hc⟩ := ih inner
      exact ⟨_, p, _, steps_project s, .project y', hpl, hc.snoc .project⟩
  | hole => intro plan' ctx' y; cases y
  | bound => intro plan' ctx' y; cases y
  | lam => intro plan' ctx' y; cases y
  | mix => intro plan' ctx' y; cases y
  | fix => intro plan' ctx' y; cases y
  | specification => intro plan' ctx' y; cases y
  | prototype => intro plan' ctx' y; cases y
  | nat => intro plan' ctx' y; cases y
  | boolean => intro plan' ctx' y; cases y
  | label => intro plan' ctx' y; cases y
  | record => intro plan' ctx' y; cases y
  | inject => intro plan' ctx' y; cases y
  | done => intro plan' ctx' y; cases y

/-! ## Reduction sequences transfer -/

theorem steps_behind {t t' u : Term} (h : Ahead t t') (s : Steps t u) : ∃ u', Steps t' u' ∧ Ahead u u' := by
  induction s generalizing t' with
  | refl => exact ⟨t', .refl _, h⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_behind h st
    obtain ⟨u', s2, a2⟩ := ih a
    exact ⟨u', steps_trans s1 s2, a2⟩

theorem steps_ahead {t t' u' : Term} (h : Ahead t t') (s : Steps t' u') : ∃ u, Steps t u ∧ Ahead u u' := by
  induction s generalizing t with
  | refl => exact ⟨t, .refl _, h⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_ahead h st
    obtain ⟨u, s2, a2⟩ := ih a
    exact ⟨u, steps_trans s1 s2, a2⟩

/-! ## Interaction traces transfer -/

/-- Turn lists with the same responses and plans related by `Ahead`. -/
abbrev TurnsAhead (turns turns' : List (Term × Term)) : Prop :=
  ListRel (fun x y => Ahead x.1 y.1 ∧ x.2 = y.2) turns turns'

theorem interaction_value {t : Term} {turns : List (Term × Term)} {v : Term}
    (run : Interaction t turns v) : Value v := by
  induction run with
  | finish e => exact e.2
  | turn _ _ _ ih => exact ih

/-- Every interaction of the term behind is matched by one of the term ahead. -/
theorem interaction_ahead_of_behind {t : Term} {turns : List (Term × Term)} {v : Term}
    (run : Interaction t turns v) : ∀ {t' : Term}, Ahead t t' →
      ∃ turns' v', Interaction t' turns' v' ∧ TurnsAhead turns turns' ∧ Ahead v v' := by
  induction run with
  | finish e =>
    intro t' h
    obtain ⟨v', e', a⟩ := evaluates_behind h e
    exact ⟨[], v', .finish e', .nil, a⟩
  | turn s y _ ih =>
    intro t' h
    obtain ⟨u', s', a⟩ := steps_behind h s
    obtain ⟨p', c', y', hp, hc⟩ := yields_behind a y
    obtain ⟨turns', v', run', ht, hv⟩ := ih (hc.plug (Ahead.refl _))
    exact ⟨_, v', .turn s' y' run', .cons ⟨hp, rfl⟩ ht, hv⟩

/-- Every interaction of the term ahead is matched by one of the term behind. -/
theorem interaction_behind_of_ahead {t' : Term} {turns' : List (Term × Term)} {v' : Term}
    (run : Interaction t' turns' v') : ∀ {t : Term}, Ahead t t' →
      ∃ turns v, Interaction t turns v ∧ TurnsAhead turns turns' ∧ Ahead v v' := by
  induction run with
  | finish e =>
    intro t h
    obtain ⟨v, e', a⟩ := evaluates_ahead h e
    exact ⟨[], v, .finish e', .nil, a⟩
  | turn s y _ ih =>
    intro t h
    obtain ⟨u, s1, a⟩ := steps_ahead h s
    obtain ⟨u2, p, c, s2, y', hp, hc⟩ := yields_ahead a y
    obtain ⟨turns, v, run', ht, hv⟩ := ih (hc.plug (Ahead.refl _))
    exact ⟨_, v, .turn (steps_trans s1 s2) y' run', .cons ⟨hp, rfl⟩ ht, hv⟩

/-! ## `≈b` with turns -/

/-- An interaction that completes with a ground observation. -/
def IHalts (t : Term) (turns : List (Term × Term)) (o : Observation) : Prop :=
  ∃ v, Interaction t turns v ∧ Observes v o

/-- An interaction that completes with some value. -/
def IConverges (t : Term) (turns : List (Term × Term)) : Prop := ∃ v, Interaction t turns v

/-- Turn lists with the same responses and `≈b`-equivalent plans. -/
abbrev TurnsEquiv (turns turns' : List (Term × Term)) : Prop :=
  ListRel (fun x y => x.1 ≈b y.1 ∧ x.2 = y.2) turns turns'

theorem TurnsEquiv.refl : ∀ turns : List (Term × Term), TurnsEquiv turns turns
  | [] => .nil
  | _ :: rest => .cons ⟨BEquiv.refl _, rfl⟩ (TurnsEquiv.refl rest)

theorem TurnsEquiv.symm {turns turns' : List (Term × Term)} (h : TurnsEquiv turns turns') :
    TurnsEquiv turns' turns := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons ⟨hx.1.symm, hx.2.symm⟩ ih

theorem TurnsEquiv.trans {a b c : List (Term × Term)} (h : TurnsEquiv a b) :
    TurnsEquiv b c → TurnsEquiv a c := by
  induction h generalizing c with
  | nil => intro h'; cases h'; exact .nil
  | cons hx _ ih =>
    intro h'
    cases h' with
    | cons hy rest => exact .cons ⟨hx.1.trans hy.1, hx.2.trans hy.2⟩ (ih rest)

theorem TurnsAhead.equiv {turns turns' : List (Term × Term)} (h : TurnsAhead turns turns') :
    TurnsEquiv turns turns' := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons ⟨bequiv_of_ahead hx.1, hx.2⟩ ih

/-- One direction of `SameInteractions`: every trace of `t` is matched by a trace of `t'`. -/
structure InteractionsCovered (t t' : Term) : Prop where
  halts : ∀ turns o, IHalts t turns o → ∃ turns', TurnsEquiv turns turns' ∧ IHalts t' turns' o
  converges : ∀ turns, IConverges t turns → ∃ turns', TurnsEquiv turns turns' ∧ IConverges t' turns'

/-- Two terms have the same interaction traces, up to `≈b` on plans. -/
structure SameInteractions (t t' : Term) : Prop where
  forward : InteractionsCovered t t'
  backward : InteractionsCovered t' t

theorem InteractionsCovered.trans {a b c : Term} (h : InteractionsCovered a b) (h' : InteractionsCovered b c) :
    InteractionsCovered a c where
  halts turns o run := by
    obtain ⟨tb, eb, rb⟩ := h.halts turns o run
    obtain ⟨tc, ec, rc⟩ := h'.halts tb o rb
    exact ⟨tc, eb.trans ec, rc⟩
  converges turns run := by
    obtain ⟨tb, eb, rb⟩ := h.converges turns run
    obtain ⟨tc, ec, rc⟩ := h'.converges tb rb
    exact ⟨tc, eb.trans ec, rc⟩

theorem sameInteractions_of_ahead {t t' : Term} (h : Ahead t t') : SameInteractions t t' where
  forward :=
    { halts := by
        rintro turns o ⟨v, run, obs⟩
        obtain ⟨turns', v', run', ht, hv⟩ := interaction_ahead_of_behind run h
        rw [inv_literal_behind (observes_literal obs) hv] at run'
        exact ⟨turns', ht.equiv, v, run', obs⟩
      converges := by
        rintro turns ⟨v, run⟩
        obtain ⟨turns', v', run', ht, _⟩ := interaction_ahead_of_behind run h
        exact ⟨turns', ht.equiv, v', run'⟩ }
  backward :=
    { halts := by
        rintro turns' o ⟨v', run, obs⟩
        obtain ⟨turns, v, run', ht, hv⟩ := interaction_behind_of_ahead run h
        have same := value_steps_eq (interaction_value run') (inv_literal_ahead (observes_literal obs) hv)
        subst same
        exact ⟨turns, ht.equiv.symm, v', run', obs⟩
      converges := by
        rintro turns' ⟨v', run⟩
        obtain ⟨turns, v, run', ht, _⟩ := interaction_behind_of_ahead run h
        exact ⟨turns, ht.equiv.symm, v, run'⟩ }

theorem SameInteractions.symm {t t' : Term} (h : SameInteractions t t') : SameInteractions t' t :=
  ⟨h.backward, h.forward⟩

theorem SameInteractions.trans {a b c : Term} (h : SameInteractions a b) (h' : SameInteractions b c) :
    SameInteractions a c :=
  ⟨h.forward.trans h'.forward, h'.backward.trans h.backward⟩

/-- `t ≈b t'` with the turns counted: for every substitution and context, the plugged terms have the
same interaction traces (same responses, `≈b` plans, same final observation). -/
def IEquiv (t t' : Term) : Prop :=
  ∀ (ρ : Nat → Term) (C : Term),
    SameInteractions (instantiate C (t.substitute ρ)) (instantiate C (t'.substitute ρ))

theorem IEquiv.refl (t : Term) : IEquiv t t := fun _ _ =>
  ⟨⟨fun turns _ r => ⟨turns, .refl _, r⟩, fun turns r => ⟨turns, .refl _, r⟩⟩,
   ⟨fun turns _ r => ⟨turns, .refl _, r⟩, fun turns r => ⟨turns, .refl _, r⟩⟩⟩

theorem IEquiv.symm {t t' : Term} (h : IEquiv t t') : IEquiv t' t := fun ρ C => (h ρ C).symm

theorem IEquiv.trans {a b c : Term} (h : IEquiv a b) (h' : IEquiv b c) : IEquiv a c :=
  fun ρ C => (h ρ C).trans (h' ρ C)

theorem iequiv_of_ahead {t t' : Term} (h : Ahead t t') : IEquiv t t' := fun ρ C =>
  sameInteractions_of_ahead (ahead_instantiate (Ahead.refl C)
    (ahead_substitute h (fun n => Ahead.refl (ρ n))))

theorem interaction_nil_iff {t v : Term} : Interaction t [] v ↔ Evaluates t v :=
  ⟨fun h => by cases h with | finish e => exact e, fun e => .finish e⟩

theorem turnsEquiv_nil {turns : List (Term × Term)} (h : TurnsEquiv [] turns) : turns = [] := by
  cases h; rfl

/-- The trace with no turns: `IEquiv` refines `≈b`. -/
theorem IEquiv.bequiv {t t' : Term} (h : IEquiv t t') : t ≈b t' := fun ρ C =>
  have same := h ρ C
  { halts := fun o =>
      ⟨fun ⟨v, e, obs⟩ => by
        obtain ⟨turns', eq, v', run, obs'⟩ := same.forward.halts [] o ⟨v, .finish e, obs⟩
        cases turnsEquiv_nil eq
        exact ⟨v', interaction_nil_iff.1 run, obs'⟩,
       fun ⟨v, e, obs⟩ => by
        obtain ⟨turns', eq, v', run, obs'⟩ := same.backward.halts [] o ⟨v, .finish e, obs⟩
        cases turnsEquiv_nil eq
        exact ⟨v', interaction_nil_iff.1 run, obs'⟩⟩
    converges :=
      ⟨fun ⟨v, e⟩ => by
        obtain ⟨turns', eq, v', run⟩ := same.forward.converges [] ⟨v, .finish e⟩
        cases turnsEquiv_nil eq
        exact ⟨v', interaction_nil_iff.1 run⟩,
       fun ⟨v, e⟩ => by
        obtain ⟨turns', eq, v', run⟩ := same.backward.converges [] ⟨v, .finish e⟩
        cases turnsEquiv_nil eq
        exact ⟨v', interaction_nil_iff.1 run⟩⟩ }

/-- **`mix` is associative over interaction traces**: the two associations yield the same plans
(up to `≈b`), take the same responses, and finish alike, in every context. -/
theorem mix_assoc_interaction (a b c : Term) : IEquiv (.mix (.mix a b) c) (.mix a (.mix b c)) :=
  (iequiv_of_ahead (mix_assoc_left_ahead a b c)).trans
    (iequiv_of_ahead (mix_assoc_right_ahead a b c)).symm

/-! ## The turns are seen: `IEquiv` tells plans apart -/

theorem perform_one_turn (p r : Nat) :
    IHalts (.perform (.nat p)) [(.nat p, .nat r)] (.natural r) :=
  ⟨.nat r, .turn (.refl _) (.perform _) (.finish ⟨.refl _, .natural r⟩), .natural r⟩

theorem nat_not_bequiv {m n : Nat} (ne : m ≠ n) : ¬ (Term.nat m ≈b Term.nat n) := by
  intro h
  have := ((h.sameRuns).halts (.natural m)).1 ⟨.nat m, ⟨.refl _, .natural m⟩, .natural m⟩
  obtain ⟨v, ⟨s, _⟩, obs⟩ := this
  rw [value_steps_eq (.natural n) s] at obs
  cases obs; exact ne rfl

/-- Two programs that yield different plans are not `IEquiv`, though neither has a completed run
without a turn: the turns are what tell them apart. -/
theorem perform_plans_distinguished : ¬ IEquiv (.perform (.nat 0)) (.perform (.nat 1)) := by
  intro h
  have same := h Term.bound (.bound 0)
  simp only [instantiate, Term.substitute, substitute_bound] at same
  obtain ⟨turns', eq, v, run, _⟩ := same.forward.halts _ _ (perform_one_turn 0 5)
  cases eq with
  | cons hx rest =>
    cases rest
    cases run with
    | turn s y _ =>
      cases s with
      | refl =>
        cases y
        exact nat_not_bequiv (by decide) hx.1
      | next st _ => cases st

end Obend.Equiv
end
