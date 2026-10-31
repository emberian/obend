module
/-
# Obend.Logic.Rewrite — rewrite derivations, their checker, and T2 `rewrite_sound`

`review/PROGRAM-LOGIC-20261101.md` §2.4, §3, §5.3 T2. A derivation is a list of steps replayed from
the left side of an equation; the checker accepts when the replay reaches the right side. Each step
is a library theorem:

| step | rewrites the current term | by |
|---|---|---|
| `run n` | `n` weak-head steps (`Law.step?`) | `bequiv_of_steps` |
| `lateBinding m L` | `X.m` to what the resolver says layer `L` gives `m` | T1 `late_binding` |
| `assoc dir` | `mix (mix a b) c` ↔ `mix a (mix b c)` | `mix_assoc` |
| `composeAssoc dir` | `compose (compose a b) c` ↔ `compose a (compose b c)`, operands observer-free | `compose_assoc_b` |
| `congr C a inner` | `C[a]` to `C[a']` where `inner` takes `a` to `a'`; `C` of census `b` | `observed_plug` (`rewrite_sound_below`'s licence) |
| `trans first second` | `first` then `second` | `Observed.trans` |

`replay_sound` is proved at a level `k`: at `b` under every observer-free substitution, and at `r`
(full `≈b`, every substitution and context) when the derivation uses no `composeAssoc`, which is
the only step that holds at `b` alone (`compose_not_assoc_r`). So `rewrite_sound` concludes
`l ≈[b] r`, and `rewrite_sound_r` concludes `l ≈b r` for derivations without `composeAssoc`
(Gemini's checkpoint review 20261101b §1).

The checker is generic in a **resolver**: what `X.m` unfolds to. The rewrite judge's resolver reads
`X` as a composition (`decodeObject`) and unfolds by late binding; the claim judge
(`Obend.Logic.Frame`) unfolds the object *variable* of a claim through its composition.
`replay_frame`: a derivation consults its resolver only at the members it unfolds (its supports).

The judge never refutes: a rejected derivation says nothing about the equation. The planted bad
derivation (`badDerivation`) names the wrong layer at its late-binding step and is refused
`stepMismatch` at that step's index.
-/
public import Obend.Logic.Claim
public import Obend.Judge.Class
public import Obend.Law.Proofs.Run
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Obend.Judge.Cost (termBeq termBeq_sound termBeq_refl)
set_option autoImplicit false

/-! ## Steps -/

/-- One step of a rewrite derivation. -/
inductive RStep where
  /-- `n` weak-head reduction steps of the current term -/
  | run (n : Nat)
  /-- the current term is `X.m`: unfold it by late binding through layer `layer` -/
  | lateBinding (member layer : String)
  /-- re-associate the `mix` at the head, left to right or back -/
  | assoc (leftToRight : Bool)
  /-- re-associate the `compose` at the head (`Equiv.Quote.compose`); its operands observer-free -/
  | composeAssoc (leftToRight : Bool)
  /-- the current term is `context[hole]`: rewrite `hole` by `inner` (`context` of census `b`) -/
  | congr (context hole : Term) (inner : List RStep)
  /-- `first`, then `second` -/
  | trans (first second : List RStep)
  deriving Repr

/-- What `X.m` unfolds to: the providing layer's name and the unfolded term. -/
abbrev Resolver := Term → String → Option (String × Term)

/-- `n` reference steps. -/
def stepN : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, t => (Obend.Law.step? t).bind (stepN n)

theorem stepN_steps : ∀ (n : Nat) {t t' : Term}, stepN n t = some t' → Steps t t'
  | 0, t, t', h => by simp only [stepN, Option.some.injEq] at h; subst h; exact .refl _
  | n + 1, t, t', h => by
    simp only [stepN] at h
    obtain ⟨u, hu, hn⟩ := Option.bind_eq_some_iff.1 h
    exact .next (Obend.Law.step?_sound t hu) (stepN_steps n hn)

/-- Re-associate the head `mix`. -/
def reassoc : Bool → Term → Option Term
  | true, .mix (.mix a b) c => some (.mix a (.mix b c))
  | false, .mix a (.mix b c) => some (.mix (.mix a b) c)
  | _, _ => none

/-- Read `Equiv.Quote.compose a b` back. -/
def composeOf : Term → Option (Term × Term)
  | .specification (.inject "composed" (.record [("inherited", .metadata a), ("wrapping", .metadata b)]))
      (.mix a' b') => if termBeq a a' && termBeq b b' then some (a, b) else none
  | _ => none

theorem composeOf_some {t a b : Term} (h : composeOf t = some (a, b)) : t = compose a b := by
  unfold composeOf at h
  split at h
  · split at h
    · rename_i hb; cases h
      simp only [Bool.and_eq_true] at hb
      rw [termBeq_sound hb.1, termBeq_sound hb.2]; rfl
    · cases h
  · cases h

/-- Re-associate the head `compose` when all three operands ask no metadata. -/
def recompose (d : Bool) (t : Term) : Option Term :=
  let free := fun (x : Term) => !observes x
  if d then
    (composeOf t).bind fun (ab, c) => (composeOf ab).bind fun (a, b) =>
      if free a && free b && free c then some (compose a (compose b c)) else none
  else
    (composeOf t).bind fun (a, bc) => (composeOf bc).bind fun (b, c) =>
      if free a && free b && free c then some (compose (compose a b) c) else none

/-- Unfold `X.m` through the named layer. -/
def unfoldAt (R : Resolver) (m layer : String) : Term → Option Term
  | .get X m' => if m' == m then
      match R X m with
      | some (layer', u) => if layer' == layer then some u else none
      | none => none
    else none
  | _ => none

mutual
/-- Replay a derivation from `t`: the term reached, or the path (step indices, outermost first) of
the step that does not apply. -/
def replay (R : Resolver) : List RStep → Term → Except (List Nat) Term
  | [], t => .ok t
  | s :: rest, t =>
    match apply R s t with
    | .ok t' => match replay R rest t' with
      | .ok t'' => .ok t''
      | .error p => .error (match p with | [] => [] | i :: q => (i + 1) :: q)
    | .error p => .error (0 :: p)
/-- Apply one step. -/
def apply (R : Resolver) : RStep → Term → Except (List Nat) Term
  | .run n, t => match stepN n t with
    | some t' => .ok t'
    | none => .error []
  | .lateBinding m layer, t => match unfoldAt R m layer t with
    | some t' => .ok t'
    | none => .error []
  | .assoc d, t => match reassoc d t with
    | some t' => .ok t'
    | none => .error []
  | .composeAssoc d, t => match recompose d t with
    | some t' => .ok t'
    | none => .error []
  | .congr C a inner, t =>
    if termBeq t (instantiate C a) && !observes C then
      match replay R inner a with
      | .ok a' => .ok (instantiate C a')
      | .error p => .error p
    else .error []
  | .trans first second, t => match replay R first t with
    | .ok t' => replay R second t'
    | .error p => .error p
end

mutual
/-- The number of steps, nested ones counted. -/
def RStep.size : RStep → Nat
  | .congr _ _ inner => sizeList inner + 1
  | .trans first second => sizeList first + sizeList second + 1
  | _ => 1
def sizeList : List RStep → Nat
  | [] => 0
  | s :: rest => s.size + sizeList rest
end

mutual
/-- The members a derivation unfolds by late binding: its supports. -/
def RStep.members : RStep → List String
  | .lateBinding m _ => [m]
  | .congr _ _ inner => membersList inner
  | .trans first second => membersList first ++ membersList second
  | _ => []
def membersList : List RStep → List String
  | [] => []
  | s :: rest => s.members ++ membersList rest
end

mutual
/-- The derivation re-associates a `compose`: it holds at `b` only. -/
def RStep.atB : RStep → Bool
  | .composeAssoc _ => true
  | .congr _ _ inner => atBList inner
  | .trans first second => atBList first || atBList second
  | _ => false
def atBList : List RStep → Bool
  | [] => false
  | s :: rest => s.atB || atBList rest
end

/-! ## Soundness -/

/-- The resolver is sound under `σ`: what it unfolds `X.m` to, `X.m` reduces to, after `σ`. -/
def RSound (R : Resolver) (σ : Nat → Term) : Prop :=
  ∀ X m layer u, R X m = some (layer, u) → Steps ((Term.get X m).substitute σ) (u.substitute σ)

/-- A substitution of observer-free terms. -/
def SubstFree (σ : Nat → Term) : Prop := ∀ n, ObsFree (σ n)

/-- The two levels a derivation is sound at, and what each asks. -/
structure Licence (k : Level) (σ : Nat → Term) : Prop where
  level : k = .b ∨ k = .r
  free : k = .b → SubstFree σ

theorem observed_of_bequiv {k : Level} {t t' : Term} (hk : k = .b ∨ k = .r) (h : t ≈b t') : Observed k t t' := by
  have hr : Observed .r t t' := fun ρ C _ => h ρ C
  rcases hk with rfl | rfl
  · exact observed_mono (k' := .r) (by decide) hr
  · exact hr

theorem observed_of_steps {k : Level} {t t' : Term} (hk : k = .b ∨ k = .r) (h : Steps t t') : Observed k t t' :=
  observed_of_bequiv hk (bequiv_of_steps h)

theorem reassoc_sound {k : Level} (hk : k = .b ∨ k = .r) {d : Bool} {t t' : Term} (h : reassoc d t = some t')
    (σ : Nat → Term) : Observed k (t.substitute σ) (t'.substitute σ) := by
  unfold reassoc at h
  split at h
  · cases h; simp only [Term.substitute]; exact observed_of_bequiv hk (mix_assoc _ _ _)
  · cases h; simp only [Term.substitute]; exact observed_of_bequiv hk (mix_assoc _ _ _).symm
  · cases h

theorem compose_substitute (a b : Term) (σ : Nat → Term) :
    (compose a b).substitute σ = compose (a.substitute σ) (b.substitute σ) := by
  simp [compose, Term.substitute]

theorem free_subst {a : Term} (ha : observes a = false) {σ : Nat → Term} (hσ : SubstFree σ) :
    ObsFree (a.substitute σ) :=
  blind_substitute (obsFree_of_observes a ha) hσ

theorem recompose_sound {d : Bool} {t t' : Term} (h : recompose d t = some t') {σ : Nat → Term}
    (hσ : SubstFree σ) : Observed .b (t.substitute σ) (t'.substitute σ) := by
  unfold recompose at h
  cases d
  · simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨⟨a, bc⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨b, c⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rename_i hf
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      simp only at h2 ⊢
      rw [composeOf_some h1, composeOf_some h2]
      simp only [compose_substitute]
      exact Observed.symm (compose_assoc_b (free_subst hf.1.1 hσ) (free_subst hf.1.2 hσ) (free_subst hf.2 hσ))
    · cases h
  · simp only [ite_true] at h
    obtain ⟨⟨ab, c⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨a, b⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rename_i hf
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      simp only at h2 ⊢
      rw [composeOf_some h1, composeOf_some h2]
      simp only [compose_substitute]
      exact compose_assoc_b (free_subst hf.1.1 hσ) (free_subst hf.1.2 hσ) (free_subst hf.2 hσ)
    · cases h

theorem unfoldAt_sound {k : Level} (hk : k = .b ∨ k = .r) {R : Resolver} {m layer : String} {t t' : Term}
    (h : unfoldAt R m layer t = some t') {σ : Nat → Term} (hR : RSound R σ) :
    Observed k (t.substitute σ) (t'.substitute σ) := by
  cases t with
  | get X m' =>
    simp only [unfoldAt] at h
    by_cases hm : m' = m
    · subst hm
      cases hr : R X m' with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨layer', u⟩ := p
        simp only [hr, beq_self_eq_true, ite_true] at h
        by_cases hl : layer' = layer
        · simp only [hl, beq_self_eq_true, ite_true, Option.some.injEq] at h
          subst h
          exact observed_of_steps hk (hR X m' layer' _ hr)
        · simp [hl] at h
    · simp [hm] at h
  | _ => simp [unfoldAt] at h

theorem congr_sound {k : Level} {σ : Nat → Term} (L : Licence k σ) {C a a' : Term} (hC : observes C = false)
    (h : Observed k (a.substitute σ) (a'.substitute σ)) :
    Observed k ((instantiate C a).substitute σ) ((instantiate C a').substitute σ) := by
  rw [instantiate_substitute, instantiate_substitute]
  exact observed_plug h _ (fun hb => blind_substitute (obsFree_of_observes C hC) (blind_lift (L.free hb)))

mutual
theorem replay_sound (R : Resolver) {k : Level} {σ : Nat → Term} (L : Licence k σ) (hR : RSound R σ) :
    ∀ (steps : List RStep), (k = .r → atBList steps = false) →
      ∀ {t t' : Term}, replay R steps t = .ok t' → Observed k (t.substitute σ) (t'.substitute σ)
  | [], _, t, t', h => by
    simp only [replay, Except.ok.injEq] at h; subst h; exact Observed.refl k _
  | s :: rest, hb, t, t', h => by
    simp only [atBList, Bool.or_eq_false_iff] at hb
    simp only [replay] at h
    split at h
    · rename_i u hu
      split at h
      · rename_i v hv
        cases h
        exact Observed.trans (apply_sound R L hR s (fun e => (hb e).1) hu)
          (replay_sound R L hR rest (fun e => (hb e).2) hv)
      · cases h
    · cases h
theorem apply_sound (R : Resolver) {k : Level} {σ : Nat → Term} (L : Licence k σ) (hR : RSound R σ) :
    ∀ (s : RStep), (k = .r → s.atB = false) →
      ∀ {t t' : Term}, apply R s t = .ok t' → Observed k (t.substitute σ) (t'.substitute σ)
  | .run n, _, t, t', h => by
    simp only [apply] at h; split at h
    · cases h; exact observed_of_steps L.level (steps_substitute σ (stepN_steps n (by assumption)))
    · cases h
  | .lateBinding m layer, _, t, t', h => by
    simp only [apply] at h; split at h
    · cases h; exact unfoldAt_sound L.level (by assumption) hR
    · cases h
  | .assoc d, _, t, t', h => by
    simp only [apply] at h; split at h
    · cases h; exact reassoc_sound L.level (by assumption) σ
    · cases h
  | .composeAssoc d, hb, t, t', h => by
    simp only [apply] at h; split at h
    · cases h
      rcases L.level with e | e
      · subst e; exact recompose_sound (by assumption) (L.free rfl)
      · exact absurd (hb e) (by simp [RStep.atB])
    · cases h
  | .congr C a inner, hb, t, t', h => by
    simp only [apply] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have e := termBeq_sound hc.1
      subst e
      split at h
      · rename_i a' ha
        cases h
        exact congr_sound L hc.2 (replay_sound R L hR inner (fun e => by simpa [RStep.atB] using hb e) ha)
      · cases h
    · cases h
  | .trans first second, hb, t, t', h => by
    simp only [apply] at h
    split at h
    · rename_i u hu
      have hb' : k = .r → atBList first = false ∧ atBList second = false := fun e => by
        simpa [RStep.atB] using hb e
      exact Observed.trans (replay_sound R L hR first (fun e => (hb' e).1) hu)
        (replay_sound R L hR second (fun e => (hb' e).2) h)
    · cases h
end

/-! ## The frame of a derivation: it reads its resolver only at its supports -/

mutual
theorem replay_frame {R R' : Resolver} :
    ∀ (steps : List RStep), (∀ X, ∀ m ∈ membersList steps, R X m = R' X m) →
      ∀ t, replay R steps t = replay R' steps t
  | [], _, _ => rfl
  | s :: rest, h, t => by
    simp only [membersList, List.mem_append] at h
    simp only [replay]
    rw [apply_frame s (fun X m hm => h X m (.inl hm)) t]
    split
    · rw [replay_frame rest (fun X m hm => h X m (.inr hm))]
    · rfl
theorem apply_frame {R R' : Resolver} :
    ∀ (s : RStep), (∀ X, ∀ m ∈ s.members, R X m = R' X m) → ∀ t, apply R s t = apply R' s t
  | .run _, _, _ => rfl
  | .lateBinding m layer, h, t => by
    simp only [apply]
    have : unfoldAt R m layer t = unfoldAt R' m layer t := by
      unfold unfoldAt
      split
      · rename_i X m'
        rw [h X m (by simp [RStep.members])]
      · rfl
    rw [this]
  | .assoc _, _, _ => rfl
  | .composeAssoc _, _, _ => rfl
  | .congr C a inner, h, t => by
    simp only [apply]
    rw [replay_frame inner (fun X m hm => h X m (by simpa [RStep.members] using hm))]
  | .trans first second, h, t => by
    simp only [RStep.members, List.mem_append] at h
    simp only [apply]
    rw [replay_frame first (fun X m hm => h X m (.inl hm))]
    split
    · exact replay_frame second (fun X m hm => h X m (.inr hm)) _
    · rfl
end

/-! ## Reading compositions back -/

/-- A layer's name, from its declared metadata. -/
def metaName : Term → String
  | .inject _ (.record (("name", .label n) :: _)) => n
  | _ => ""

/-- The body of `λself. λsuper. body`: its fields, and whether it is the flat record. -/
def decodeBody : Term → Option (List (String × Term) × Bool)
  | .extend (.bound 0) fields => some (fields, false)
  | .record fields => some (fields, true)
  | _ => none

theorem decodeBody_some {body : Term} {fs : List (String × Term)} {flat : Bool}
    (h : decodeBody body = some (fs, flat)) :
    body = if flat then .record fs else .extend (.bound 0) fs := by
  unfold decodeBody at h
  split at h <;> (try cases h) <;> rfl

/-- Read a layer back from its term, either shape. -/
def decodeLayer : Term → Option Layer
  | .specification md (.lam (.lam body)) => (decodeBody body).map fun (fs, flat) => { name := metaName md, metadata := md, fields := fs, flat := flat }
  | _ => none

theorem decodeLayer_term {t : Term} {L : Layer} (h : decodeLayer t = some L) : L.term = t := by
  unfold decodeLayer at h
  split at h
  · obtain ⟨⟨fs, flat⟩, hb, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    rw [decodeBody_some hb]
    cases flat <;> simp [Layer.term, Layer.extension, Layer.provide]
  · cases h

/-- Read a composition back from its term, outermost layer first. -/
def decodeCompose : Term → Option (Layer × List Layer)
  | .specification md (.mix x y) =>
    match decodeCompose x, decodeLayer y with
    | some (top, below), some L => some ({ L with composeMeta := md }, top :: below)
    | _, _ => none
  | t => (decodeLayer t).map fun L => (L, [])

theorem decodeCompose_term {t : Term} {top : Layer} {below : List Layer}
    (h : decodeCompose t = some (top, below)) : composeTerm top below = t := by
  fun_induction decodeCompose t generalizing top below with
  | case1 md x y top' below' L hy hx ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [composeTerm, composeWith, composeStep]
    rw [show composeWith Layer.term top' below' = x from ih hx]
    have := decodeLayer_term hy
    simp only [Layer.term, Layer.extension, Layer.provide] at this ⊢
    rw [← this]
  | case2 => cases h
  | case3 t _ =>
    obtain ⟨L, hL, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact decodeLayer_term hL

/-- Read an object back: `fix (compose …) {seed}`. -/
def decodeObject : Term → Option Composition
  | .fix S (.record seed) => (decodeCompose S).map fun (top, below) => ⟨top, below, seed⟩
  | _ => none

theorem decodeObject_object {X : Term} {C : Composition} (h : decodeObject X = some C) : C.object = X := by
  unfold decodeObject at h
  split at h
  · rename_i S seed
    obtain ⟨⟨top, below⟩, hd, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    simp only [Composition.object, decodeCompose_term hd]
  · cases h

/-- The name of a layer of the stack. -/
def layerName (layers : List Layer) (j : Nat) : String := (layers[j]?.map (·.name)).getD ""

/-- The rewrite judge's resolver: `X` read as a composition, unfolded by late binding. -/
def objectResolver : Resolver := fun X m =>
  (decodeObject X).bind fun C => (C.unfold m).map fun (j, u) => (layerName C.layers j, u)

theorem objectResolver_sound (σ : Nat → Term) : RSound objectResolver σ := by
  intro X m layer u h
  obtain ⟨C, hC, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨j, u'⟩, hu, e⟩ := Option.map_eq_some_iff.1 h
  cases e
  rw [← decodeObject_object hC]
  exact steps_substitute σ (late_binding_unfold hu)

/-! ## The rewrite judge -/

/-- Why a derivation is rejected. -/
inductive RClause where
  /-- the step at this path does not apply where the previous one ended -/
  | stepMismatch
  /-- the derivation ends elsewhere than the right side -/
  | endMismatch
  deriving DecidableEq, Repr

/-- Replay a derivation with a resolver and compare with the right side. -/
def rewriteWith (R : Resolver) (k : Nat) (l r : Term) (steps : List RStep) : Judge.Verdict RClause :=
  if sizeList steps ≤ k then
    match replay R steps l with
    | .ok t => if termBeq t r then .ok else .refused .endMismatch []
    | .error p => .refused .stepMismatch p
  else .uncovered

theorem rewriteWith_ok {R : Resolver} {k : Nat} {l r : Term} {steps : List RStep}
    (h : rewriteWith R k l r steps = .ok) : replay R steps l = .ok r := by
  unfold rewriteWith at h
  split at h
  · split at h
    · rename_i t ht
      split at h
      · rename_i hb; rw [ht, termBeq_sound hb]
      · cases h
    · cases h
  · cases h

theorem rewriteWith_mono {R : Resolver} {k k' : Nat} {l r : Term} {steps : List RStep} (le : k ≤ k')
    (hne : rewriteWith R k l r steps ≠ .uncovered) : rewriteWith R k' l r steps = rewriteWith R k l r steps := by
  unfold rewriteWith at hne ⊢
  split at hne
  · rename_i h; simp [Nat.le_trans h le, h]
  · exact absurd rfl hne

/-- The rewrite checker. -/
def rewriteCheck (k : Nat) (o : Term × Term) (steps : List RStep) : Judge.Verdict RClause :=
  rewriteWith objectResolver k o.1 o.2 steps

theorem replay_object_b {steps : List RStep} {l r : Term} (h : replay objectResolver steps l = .ok r) : l ≈[.b] r := by
  have := replay_sound objectResolver (k := .b) (σ := Term.bound) ⟨.inl rfl, fun _ n => .bound n⟩
    (objectResolver_sound _) steps (fun e => by cases e) h
  simp only [substitute_bound] at this
  exact this

/-- **T2 `rewrite_sound`.** An accepted derivation is an equation of the logic at `b`: `l ≈[b] r`. -/
theorem rewrite_sound {l r : Term} {steps : List RStep} {k : Nat}
    (h : rewriteCheck k (l, r) steps = .ok) : l ≈[.b] r :=
  replay_object_b (rewriteWith_ok h)

/-- **T2 at `r`.** A derivation without `composeAssoc` proves full `≈b`: every substitution, every
context, metadata observers included. -/
theorem rewrite_sound_r {l r : Term} {steps : List RStep} {k : Nat}
    (h : rewriteCheck k (l, r) steps = .ok) (hb : atBList steps = false) : l ≈b r := by
  have := replay_sound objectResolver (k := .r) (σ := Term.bound) ⟨.inr rfl, fun e => by cases e⟩
    (objectResolver_sound _) steps (fun _ => hb) (rewriteWith_ok h)
  intro ρ C
  simpa [substitute_bound] using this ρ C trivial

/-- **`holdsEq_of_rewrite`.** A claim reducing to an elaborated `==` whose sides have an accepted
derivation between them holds partially: the two sides have the same completed runs. No
convergence is claimed. -/
theorem holdsEq_of_rewrite {l r : Term} {steps : List RStep} {k : Nat}
    (h : rewriteCheck k (l, r) steps = .ok) : HoldsEq l r :=
  holdsEq_of_observed (rewrite_sound h)

/-- **The rewrite judge.** Objects are equations, certificates derivations; the grade bounds their
size. It never refutes. -/
instance rewrite : Judge (Term × Term) (List RStep) where
  Clause := RClause
  Meaning o _ := o.1 ≈[.b] o.2
  check := rewriteCheck
  sound := by intro r o steps h; exact rewrite_sound (l := o.1) (r := o.2) h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := ∃ steps, replay objectResolver steps o.1 = .ok o.2
  complete := by
    rintro o ⟨steps, hrun⟩ _
    exact ⟨steps, sizeList steps, by simp [rewriteCheck, rewriteWith, hrun, termBeq_refl]⟩
  mono := by intro r r' o steps le hne; exact rewriteWith_mono le hne

/-! ## A derivation, accepted and planted -/

/-- `λself. λsuper. extend super {m = n}`. -/
def constLayer (name : String) (n : Nat) : Layer :=
  { name, metadata := .inject "declared" (.record [("name", .label name)]), fields := [("m", .nat n)] }

/-- `fix(compose(Inner, Outer), {})`, both providing `m`. -/
def twoProviders : Composition := ⟨constLayer "Outer" 2, [constLayer "Inner" 1], []⟩

/-- `O.m` unfolds through `Outer`, to `2`. -/
def goodDerivation : List RStep := [.lateBinding "m" "Outer"]

/-- The planted bad derivation: it names `Inner`, the earlier provider. -/
def badDerivation : List RStep := [.lateBinding "m" "Inner"]

theorem badDerivation_refused :
    rewriteCheck 1 (.get twoProviders.object "m", .nat 1) badDerivation = .refused .stepMismatch [0] := by
  simp [rewriteCheck, rewriteWith, sizeList, badDerivation, RStep.size, replay, apply, unfoldAt, objectResolver,
    decodeObject, twoProviders, Composition.object, composeTerm, composeWith, composeStep, decodeCompose,
    constLayer, Layer.term, Layer.extension,
    Layer.provide, decodeLayer, decodeBody, metaName, Composition.unfold, unfoldIn, Composition.layers,
    providesLast, Layer.provides, bodyAt, Layer.body, layerName, isDelegation, openTerm, Term.substitute]

theorem goodDerivation_accepted :
    rewriteCheck 1 (.get twoProviders.object "m", .nat 2) goodDerivation = .ok := by
  simp [rewriteCheck, rewriteWith, sizeList, goodDerivation, RStep.size, replay, apply, unfoldAt, objectResolver,
    decodeObject, twoProviders, Composition.object, composeTerm, composeWith, composeStep, decodeCompose,
    termBeq_refl, constLayer, Layer.term, Layer.extension,
    Layer.provide, decodeLayer, decodeBody, metaName, Composition.unfold, unfoldIn, Composition.layers,
    providesLast, Layer.provides, bodyAt, Layer.body, layerName, isDelegation, openTerm, Term.substitute]

end Obend.Logic
end
