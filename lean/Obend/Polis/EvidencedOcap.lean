module
/-
# Obend.Polis.EvidencedOcap — S-K partial combinatory algebras, evidenced frames, sealers, Kleene caveats

Supersedes §1 of `Obend.Trailblaze.Polis`, whose `PCA` carried `k_step` only (its `sComb` was an
unconstrained constant, and its concrete `apply` returned `none` on a saturated `S`) and whose
`Assembly` kept realizers under `∃`.

1. `PCA`: application is a deterministic relation `App f a r` (partiality is the absence of a result),
   and `K`, `S` and their partial applications are data (`k1`, `s1`, `s2`), so no realizer is ever
   chosen. `CombTerm.lamCode` is bracket abstraction as a total function into codes, and
   `CombTerm.abst_eval` is combinatory completeness.
2. `capPCA`: a term model whose extra constants are capability tokens, attenuators and guards.
   `CapApp` is the big-step relation; `capApply` is the fuel-bounded evaluator, sound and complete
   for it.
3. `EvidencedFrame`, after Cohen, Miquey and Tate, *Evidenced Frames: A Unifying Framework Broadening
   Realizability Models* (LICS 2021; the axioms are written from memory of that paper):
   `Leads φ e ψ` with evidence `e` as data, uniform in the propositions. `realizabilityFrame P` builds
   one from any `PCA`; every evidence operation there is a code computed by `lamCode`, which is where
   `S` is used.
4. `SealCap`, `authority`: Morris's sealer/unsealer pair. `authority_spec` characterizes the fold
   bit by bit; `amplify_superadditive` and `authority_not_additive` follow from it.
5. `KleenePred3`, `Caveat`: strong Kleene connectives, and `Caveat.eval_refines`: evaluation is
   monotone in the information order, so an accepted caveat stays accepted and a refused one stays
   refused when more variables are bound, and `not3` never turns `unbound3` into an accept.
-/

public section
namespace Obend.Polis

set_option autoImplicit false

universe u v

/-! ## 1. Partial combinatory algebras -/

/-- A partial combinatory algebra. `App f a r` reads "`f` applied to `a` is defined and equals `r`".
The partial applications of `k` and `s` are functions on codes, so the structure never asks for an
existence proof to be opened. -/
structure PCA where
  Code : Type
  App : Code → Code → Code → Prop
  app_det : ∀ {f a r r' : Code}, App f a r → App f a r' → r = r'
  k : Code
  s : Code
  k1 : Code → Code
  s1 : Code → Code
  s2 : Code → Code → Code
  k_app : ∀ a, App k a (k1 a)
  k1_app : ∀ a b, App (k1 a) b a
  s_app : ∀ f, App s f (s1 f)
  s1_app : ∀ f g, App (s1 f) g (s2 f g)
  s2_app : ∀ f g x r, App (s2 f g) x r ↔ ∃ fx gx, App f x fx ∧ App g x gx ∧ App fx gx r

namespace PCA
variable (P : PCA)

/-- `k · x` is defined, and `(k · x) · y = x`. -/
theorem k_step (x y : P.Code) : ∃ kx, P.App P.k x kx ∧ P.App kx y x :=
  ⟨P.k1 x, P.k_app x, P.k1_app x y⟩

/-- `s · f` and `(s · f) · g` are defined, and `((s · f) · g) · x` is `(f · x) · (g · x)` as a
Kleene equation: defined exactly when the right side is, with the same value. -/
theorem s_step (f g x r : P.Code) :
    ∃ sf sfg, P.App P.s f sf ∧ P.App sf g sfg ∧
      (P.App sfg x r ↔ ∃ fx gx, P.App f x fx ∧ P.App g x gx ∧ P.App fx gx r) :=
  ⟨P.s1 f, P.s2 f g, P.s_app f, P.s1_app f g, P.s2_app f g x r⟩

theorem k1_app_iff (a b r : P.Code) : P.App (P.k1 a) b r ↔ r = a :=
  ⟨fun h => P.app_det h (P.k1_app a b), fun h => h ▸ P.k1_app a b⟩

/-- The identity code `S K K`. -/
@[expose] def i : P.Code := P.s2 P.k P.k

theorem i_app (a r : P.Code) : P.App P.i a r ↔ r = a := by
  unfold i
  rw [P.s2_app]
  constructor
  · rintro ⟨fx, gx, h1, _, h3⟩
    obtain rfl := P.app_det h1 (P.k_app a)
    exact P.app_det h3 (P.k1_app a gx)
  · rintro rfl
    exact ⟨P.k1 r, P.k1 r, P.k_app r, P.k_app r, P.k1_app r _⟩

/-- An environment with `x` rebound to `a`. -/
@[expose] def update {P : PCA} (ρ : Nat → P.Code) (x : Nat) (a : P.Code) : Nat → P.Code :=
  fun y => if y = x then a else ρ y

theorem update_same {P : PCA} (ρ : Nat → P.Code) (x : Nat) (a : P.Code) : update ρ x a x = a := by
  simp [update]

theorem update_other {P : PCA} (ρ : Nat → P.Code) {x y : Nat} (a : P.Code) (h : y ≠ x) :
    update ρ x a y = ρ y := by
  simp [update, h]

end PCA

/-- Combinatory terms over a PCA: variables, codes, application. -/
inductive CombTerm (P : PCA) where
  | var (n : Nat)
  | const (c : P.Code)
  | ap (t u : CombTerm P)

namespace CombTerm
variable {P : PCA}

/-- Big-step evaluation of a term in an environment. -/
@[expose] def Eval (ρ : Nat → P.Code) : CombTerm P → P.Code → Prop
  | .var n, r => r = ρ n
  | .const c, r => r = c
  | .ap t u, r => ∃ f a, Eval ρ t f ∧ Eval ρ u a ∧ P.App f a r

theorem eval_det (ρ : Nat → P.Code) (t : CombTerm P) {r r' : P.Code}
    (h : t.Eval ρ r) (h' : t.Eval ρ r') : r = r' := by
  induction t generalizing r r' with
  | var n => simp only [Eval] at h h'; rw [h, h']
  | const c => simp only [Eval] at h h'; rw [h, h']
  | ap t u iht ihu =>
    simp only [Eval] at h h'
    obtain ⟨f, a, hf, ha, hr⟩ := h
    obtain ⟨f', a', hf', ha', hr'⟩ := h'
    obtain rfl := iht hf hf'
    obtain rfl := ihu ha ha'
    exact P.app_det hr hr'

/-- Bracket abstraction `λ*x. t` as a term: `S K K` at `x`, `K y` at other leaves, `S` at nodes. -/
@[expose] def abst (x : Nat) : CombTerm P → CombTerm P
  | .var n =>
    if n = x then .ap (.ap (.const P.s) (.const P.k)) (.const P.k) else .ap (.const P.k) (.var n)
  | .const c => .ap (.const P.k) (.const c)
  | .ap t u => .ap (.ap (.const P.s) (abst x t)) (abst x u)

/-- The code `λ*x. t` denotes in `ρ`, computed without evaluating anything. -/
@[expose] def lamCode (x : Nat) (ρ : Nat → P.Code) : CombTerm P → P.Code
  | .var n => if n = x then P.i else P.k1 (ρ n)
  | .const c => P.k1 c
  | .ap t u => P.s2 (lamCode x ρ t) (lamCode x ρ u)

/-- `λ*x. t` is always defined, and its value is `lamCode`. -/
theorem eval_abst (x : Nat) (ρ : Nat → P.Code) (t : CombTerm P) :
    (t.abst x).Eval ρ (t.lamCode x ρ) := by
  induction t with
  | var n =>
    by_cases h : n = x
    · subst h
      simp only [abst, lamCode, eq_self, ↓reduceIte, Eval]
      exact ⟨P.s1 P.k, P.k, ⟨P.s, P.k, rfl, rfl, P.s_app _⟩, rfl, P.s1_app _ _⟩
    · simp only [abst, lamCode, h, ↓reduceIte, Eval]
      exact ⟨P.k, ρ n, rfl, rfl, P.k_app _⟩
  | const c =>
    simp only [abst, lamCode, Eval]
    exact ⟨P.k, c, rfl, rfl, P.k_app _⟩
  | ap t u iht ihu =>
    simp only [abst, lamCode, Eval]
    exact ⟨P.s1 (t.lamCode x ρ), u.lamCode x ρ,
      ⟨P.s, t.lamCode x ρ, rfl, iht, P.s_app _⟩, ihu, P.s1_app _ _⟩

/-- β for `lamCode`: applying `λ*x. t` to `a` is evaluating `t` with `x := a`, as a Kleene equation. -/
theorem lamCode_app (x : Nat) (ρ : Nat → P.Code) (t : CombTerm P) (a r : P.Code) :
    P.App (t.lamCode x ρ) a r ↔ t.Eval (PCA.update ρ x a) r := by
  induction t generalizing r with
  | var n =>
    by_cases h : n = x
    · subst h
      simp only [lamCode, eq_self, ↓reduceIte, Eval, PCA.update_same, P.i_app]
    · simp only [lamCode, h, ↓reduceIte, Eval, PCA.update_other ρ a h, P.k1_app_iff]
  | const c => simp only [lamCode, Eval, P.k1_app_iff]
  | ap t u iht ihu => simp only [lamCode, Eval, P.s2_app, iht, ihu]

/-- **Combinatory completeness.** For every term `t` and variable `x` the term `abst x t` evaluates,
in every environment, to a code `f` with `f · a ≃ t[x := a]` for all `a`. -/
theorem abst_eval (x : Nat) (ρ : Nat → P.Code) (t : CombTerm P) :
    ∃ f, (t.abst x).Eval ρ f ∧ ∀ a r, P.App f a r ↔ t.Eval (PCA.update ρ x a) r :=
  ⟨t.lamCode x ρ, eval_abst x ρ t, lamCode_app x ρ t⟩

/-- The abstraction binds `x`: its code does not depend on the environment at `x`. -/
theorem lamCode_update (x : Nat) (ρ : Nat → P.Code) (b : P.Code) (t : CombTerm P) :
    t.lamCode x (PCA.update ρ x b) = t.lamCode x ρ := by
  induction t with
  | var n =>
    by_cases h : n = x
    · subst h; simp only [lamCode, eq_self, ↓reduceIte]
    · simp only [lamCode, h, ↓reduceIte, PCA.update_other ρ b h]
  | const c => rfl
  | ap t u iht ihu => simp only [lamCode, iht, ihu]

/-- The term pairing `A` with `B`: `S (S I (K A)) (K B)`, built by application so that it can sit
under an abstraction. -/
@[expose] def pairT (A B : CombTerm P) : CombTerm P :=
  .ap (.ap (.const P.s) (.ap (.ap (.const P.s) (.const P.i)) (.ap (.const P.k) A)))
    (.ap (.const P.k) B)

end CombTerm

/-! ## 2. Pairing and evidence codes of an arbitrary PCA -/

namespace PCA
variable (P : PCA)
open CombTerm

/-- The pair of `a` and `b`: `λ*z. z a b`. -/
@[expose] def pairCode (a b : P.Code) : P.Code := P.s2 (P.s2 P.i (P.k1 a)) (P.k1 b)

/-- `λ*p. p c`. -/
theorem selfApp_iff (c p r : P.Code) : P.App (P.s2 P.i (P.k1 c)) p r ↔ P.App p c r := by
  rw [P.s2_app]
  constructor
  · rintro ⟨fx, gx, h1, h2, h3⟩
    rw [(P.i_app p fx).1 h1, (P.k1_app_iff c p gx).1 h2] at h3
    exact h3
  · intro h
    exact ⟨p, c, (P.i_app p p).2 rfl, P.k1_app c p, h⟩

theorem pairCode_app (a b z r : P.Code) :
    P.App (P.pairCode a b) z r ↔ ∃ fx, P.App z a fx ∧ P.App fx b r := by
  unfold pairCode
  rw [P.s2_app]
  constructor
  · rintro ⟨fx, gx, h1, h2, h3⟩
    rw [(P.k1_app_iff b z gx).1 h2] at h3
    exact ⟨fx, (P.selfApp_iff a z fx).1 h1, h3⟩
  · rintro ⟨fx, h1, h3⟩
    exact ⟨fx, b, (P.selfApp_iff a z fx).2 h1, P.k1_app b z, h3⟩

/-- First projection `λ*p. p K`. -/
@[expose] def fstCode : P.Code := P.s2 P.i (P.k1 P.k)

/-- Second projection `λ*p. p (K I)`. -/
@[expose] def sndCode : P.Code := P.s2 P.i (P.k1 (P.k1 P.i))

theorem fst_pair (a b : P.Code) : P.App P.fstCode (P.pairCode a b) a :=
  (P.selfApp_iff P.k (P.pairCode a b) a).2
    ((P.pairCode_app a b P.k a).2 ⟨P.k1 a, P.k_app a, P.k1_app a b⟩)

theorem snd_pair (a b : P.Code) : P.App P.sndCode (P.pairCode a b) b :=
  (P.selfApp_iff (P.k1 P.i) (P.pairCode a b) b).2
    ((P.pairCode_app a b (P.k1 P.i) b).2 ⟨P.i, P.k1_app P.i a, (P.i_app b b).2 rfl⟩)

theorem eval_pairT {ρ : Nat → P.Code} {A B : CombTerm P} {a b : P.Code}
    (hA : A.Eval ρ a) (hB : B.Eval ρ b) : (pairT A B).Eval ρ (P.pairCode a b) := by
  simp only [pairT, Eval]
  exact ⟨P.s1 (P.s2 P.i (P.k1 a)), P.k1 b,
    ⟨P.s, P.s2 P.i (P.k1 a), rfl,
      ⟨P.s1 P.i, P.k1 a, ⟨P.s, P.i, rfl, rfl, P.s_app _⟩, ⟨P.k, a, rfl, hA, P.k_app _⟩,
        P.s1_app _ _⟩,
      P.s_app _⟩,
    ⟨P.k, b, rfl, hB, P.k_app _⟩, P.s1_app _ _⟩

/-- Sequential composition `λ*x. e' (e x)`. -/
@[expose] def seqCode (e e' : P.Code) : P.Code := P.s2 (P.k1 e') e

theorem seqCode_app {e e' x y z : P.Code} (h : P.App e x y) (h' : P.App e' y z) :
    P.App (P.seqCode e e') x z :=
  (P.s2_app _ _ _ _).2 ⟨e', y, P.k1_app e' x, h, h'⟩

/-- Pairing of evidence `λ*x. ⟨e₁ x, e₂ x⟩`. -/
@[expose] def pairEv (e₁ e₂ : P.Code) : P.Code :=
  (pairT (.ap (.const e₁) (.var 0)) (.ap (.const e₂) (.var 0))).lamCode 0 (fun _ => P.k)

theorem pairEv_app {e₁ e₂ x a b : P.Code} (h₁ : P.App e₁ x a) (h₂ : P.App e₂ x b) :
    P.App (P.pairEv e₁ e₂) x (P.pairCode a b) := by
  unfold pairEv
  rw [lamCode_app]
  refine P.eval_pairT ?_ ?_
  · simp only [Eval]
    exact ⟨e₁, x, rfl, (update_same _ 0 x).symm, h₁⟩
  · simp only [Eval]
    exact ⟨e₂, x, rfl, (update_same _ 0 x).symm, h₂⟩

/-- The body of a curried evidence: `e ⟨x₀, x₁⟩`. -/
@[expose] def curryBody (e : P.Code) : CombTerm P := .ap (.const e) (pairT (.var 0) (.var 1))

/-- Currying of evidence `λ*a. λ*b. e ⟨a, b⟩`. -/
@[expose] def lamEv (e : P.Code) : P.Code := ((P.curryBody e).abst 1).lamCode 0 (fun _ => P.k)

/-- The closure `lamEv e` returns on `a`. -/
@[expose] def lamEvAt (e a : P.Code) : P.Code :=
  (P.curryBody e).lamCode 1 (update (fun _ => P.k) 0 a)

theorem lamEv_app (e a : P.Code) : P.App (P.lamEv e) a (P.lamEvAt e a) := by
  unfold lamEv lamEvAt
  rw [lamCode_app]
  exact eval_abst 1 _ _

theorem lamEvAt_app {e a b r : P.Code} (h : P.App e (P.pairCode a b) r) :
    P.App (P.lamEvAt e a) b r := by
  unfold lamEvAt
  rw [lamCode_app]
  simp only [curryBody, Eval]
  refine ⟨e, P.pairCode a b, rfl, P.eval_pairT ?_ ?_, h⟩
  · simp only [Eval]
    rw [update_other _ b (by decide : (0 : Nat) ≠ 1), update_same]
  · simp only [Eval]
    rw [update_same]

/-- Evaluation evidence `λ*p. (fst p) (snd p)`. -/
@[expose] def evalCode : P.Code := P.s2 P.fstCode P.sndCode

theorem evalCode_app {f a r : P.Code} (h : P.App f a r) :
    P.App P.evalCode (P.pairCode f a) r :=
  (P.s2_app _ _ _ _).2 ⟨f, a, P.fst_pair f a, P.snd_pair f a, h⟩

/-- `e` leads from `φ` to `ψ`: it is defined on every realizer of `φ` and lands in `ψ`. One code
serves every realizer. -/
@[expose] def RLeads (φ : P.Code → Prop) (e : P.Code) (ψ : P.Code → Prop) : Prop :=
  ∀ a, φ a → ∃ r, P.App e a r ∧ ψ r

end PCA

/-! ## 3. Evidenced frames -/

/-- An evidenced frame: propositions `Ω`, evidence `E`, and `Leads φ e ψ`. Every law names the
evidence it produces as a function of the evidence it is given; none says only that some evidence
exists. `uimp φ Φ` is implication into every member of the family `Φ` at once. -/
structure EvidencedFrame where
  Ω : Type u
  E : Type v
  Leads : Ω → E → Ω → Prop
  eid : E
  leads_refl : ∀ φ, Leads φ eid φ
  seq : E → E → E
  leads_trans : ∀ {φ₁ φ₂ φ₃ e e'}, Leads φ₁ e φ₂ → Leads φ₂ e' φ₃ → Leads φ₁ (seq e e') φ₃
  top : Ω
  etop : E
  leads_top : ∀ φ, Leads φ etop top
  conj : Ω → Ω → Ω
  pair : E → E → E
  efst : E
  esnd : E
  leads_fst : ∀ φ₁ φ₂, Leads (conj φ₁ φ₂) efst φ₁
  leads_snd : ∀ φ₁ φ₂, Leads (conj φ₁ φ₂) esnd φ₂
  leads_pair : ∀ {φ φ₁ φ₂ e₁ e₂}, Leads φ e₁ φ₁ → Leads φ e₂ φ₂ → Leads φ (pair e₁ e₂) (conj φ₁ φ₂)
  uimp : Ω → (Ω → Prop) → Ω
  lam : E → E
  eeval : E
  leads_lam : ∀ {φ₁ φ₂ Φ e}, (∀ φ, Φ φ → Leads (conj φ₁ φ₂) e φ) → Leads φ₁ (lam e) (uimp φ₂ Φ)
  leads_eval : ∀ {φ₁ Φ φ}, Φ φ → Leads (conj (uimp φ₁ Φ) φ₁) eeval φ

namespace EvidencedFrame
variable (F : EvidencedFrame)

/-- Conjunction commutes, with evidence `⟨snd, fst⟩`. -/
theorem leads_conj_comm (φ ψ : F.Ω) : F.Leads (F.conj φ ψ) (F.pair F.esnd F.efst) (F.conj ψ φ) :=
  F.leads_pair (F.leads_snd φ ψ) (F.leads_fst φ ψ)

/-- Curry, then apply: the evidence `⟨fst ; λe, snd⟩ ; eval` leads wherever `e` did. -/
theorem leads_beta {φ₁ φ₂ ψ : F.Ω} {e : F.E} (h : F.Leads (F.conj φ₁ φ₂) e ψ) :
    F.Leads (F.conj φ₁ φ₂) (F.seq (F.pair (F.seq F.efst (F.lam e)) F.esnd) F.eeval) ψ :=
  F.leads_trans
    (F.leads_pair
      (F.leads_trans (F.leads_fst φ₁ φ₂)
        (F.leads_lam (Φ := fun χ => χ = ψ) (fun _ hχ => hχ ▸ h)))
      (F.leads_snd φ₁ φ₂))
    (F.leads_eval rfl)

end EvidencedFrame

/-- The realizability evidenced frame of a PCA: propositions are predicates on codes, evidence is
a code, and every operation is one of the codes of §2. -/
@[expose] def realizabilityFrame (P : PCA) : EvidencedFrame where
  Ω := P.Code → Prop
  E := P.Code
  Leads := P.RLeads
  eid := P.i
  leads_refl := fun _ a ha => ⟨a, (P.i_app a a).2 rfl, ha⟩
  seq := P.seqCode
  leads_trans := fun h h' a ha =>
    let ⟨b, hb, hφb⟩ := h a ha
    let ⟨c, hc, hφc⟩ := h' b hφb
    ⟨c, P.seqCode_app hb hc, hφc⟩
  top := fun _ => True
  etop := P.i
  leads_top := fun _ a _ => ⟨a, (P.i_app a a).2 rfl, trivial⟩
  conj := fun φ ψ c => ∃ a b, φ a ∧ ψ b ∧ c = P.pairCode a b
  pair := P.pairEv
  efst := P.fstCode
  esnd := P.sndCode
  leads_fst := fun _ _ _ hc =>
    let ⟨a, b, ha, _, hcab⟩ := hc
    ⟨a, hcab ▸ P.fst_pair a b, ha⟩
  leads_snd := fun _ _ _ hc =>
    let ⟨a, b, _, hb, hcab⟩ := hc
    ⟨b, hcab ▸ P.snd_pair a b, hb⟩
  leads_pair := fun h₁ h₂ x hx =>
    let ⟨a, ha, hφa⟩ := h₁ x hx
    let ⟨b, hb, hφb⟩ := h₂ x hx
    ⟨P.pairCode a b, P.pairEv_app ha hb, a, b, hφa, hφb, rfl⟩
  uimp := fun φ Φ f => ∀ ψ, Φ ψ → ∀ a, φ a → ∃ r, P.App f a r ∧ ψ r
  lam := P.lamEv
  eeval := P.evalCode
  leads_lam := fun {_ _ _ e} H a ha =>
    ⟨P.lamEvAt e a, P.lamEv_app e a, fun ψ hψ b hb =>
      let ⟨r, hr, hψr⟩ := H ψ hψ (P.pairCode a b) ⟨a, b, ha, hb, rfl⟩
      ⟨r, P.lamEvAt_app hr, hψr⟩⟩
  leads_eval := fun {_ _ ψ} hψ _ hc =>
    let ⟨f, a, hf, ha, hcfa⟩ := hc
    let ⟨r, hr, hψr⟩ := hf ψ hψ a ha
    ⟨r, hcfa ▸ P.evalCode_app (f := f) hr, hψr⟩

/-! ## 4. A capability term model -/

/-- `a ⊆ b` on 64-bit rights masks. -/
@[expose] def subMask (a b : UInt64) : Bool := a &&& b == a

theorem subMask_refl (a : UInt64) : subMask a a = true := by
  simp [subMask]

theorem subMask_trans {a b c : UInt64} (hab : subMask a b = true) (hbc : subMask b c = true) :
    subMask a c = true := by
  simp only [subMask, beq_iff_eq] at *
  rw [← hab, UInt64.and_assoc, hbc]

theorem subMask_and_left (a m : UInt64) : subMask (a &&& m) a = true := by
  simp only [subMask, beq_iff_eq]
  rw [UInt64.and_comm (a &&& m) a, ← UInt64.and_assoc, UInt64.and_self]

/-- Codes of the capability model: the combinators with their partial applications, capability
tokens carrying a rights mask, attenuators, and guards. -/
inductive CapCode where
  | k
  | k1 (a : CapCode)
  | s
  | s1 (f : CapCode)
  | s2 (f g : CapCode)
  | cap (rights : UInt64)
  | attenuate (mask : UInt64)
  | guard (need : UInt64)
  deriving @[expose] DecidableEq, Repr

/-- Big-step application. An attenuator narrows a token; a guard answers a token with the Church
boolean of `need ⊆ rights`; either applied to anything else has no result. -/
inductive CapApp : CapCode → CapCode → CapCode → Prop where
  | k (a : CapCode) : CapApp .k a (.k1 a)
  | k1 (a b : CapCode) : CapApp (.k1 a) b a
  | s (f : CapCode) : CapApp .s f (.s1 f)
  | s1 (f g : CapCode) : CapApp (.s1 f) g (.s2 f g)
  | s2 {f g x fx gx r : CapCode} :
      CapApp f x fx → CapApp g x gx → CapApp fx gx r → CapApp (.s2 f g) x r
  | attenuate (mask rights : UInt64) : CapApp (.attenuate mask) (.cap rights) (.cap (rights &&& mask))
  | guardGrant {need rights : UInt64} :
      subMask need rights = true → CapApp (.guard need) (.cap rights) .k
  | guardDeny {need rights : UInt64} :
      subMask need rights = false → CapApp (.guard need) (.cap rights) (.k1 (.s2 .k .k))

theorem CapApp.det {f a r r' : CapCode} (h : CapApp f a r) (h' : CapApp f a r') : r = r' := by
  induction h generalizing r' with
  | k a => cases h'; rfl
  | k1 a b => cases h'; rfl
  | s f => cases h'; rfl
  | s1 f g => cases h'; rfl
  | s2 _ _ _ ih1 ih2 ih3 =>
    cases h' with
    | s2 h1 h2 h3 =>
      obtain rfl := ih1 h1
      obtain rfl := ih2 h2
      exact ih3 h3
  | attenuate mask rights => cases h'; rfl
  | guardGrant hg =>
    cases h' with
    | guardGrant _ => rfl
    | guardDeny hd => rw [hg] at hd; cases hd
  | guardDeny hd =>
    cases h' with
    | guardGrant hg => rw [hd] at hg; cases hg
    | guardDeny _ => rfl

/-- The capability PCA. -/
@[expose] def capPCA : PCA where
  Code := CapCode
  App := CapApp
  app_det := CapApp.det
  k := .k
  s := .s
  k1 := .k1
  s1 := .s1
  s2 := .s2
  k_app := .k
  k1_app := .k1
  s_app := .s
  s1_app := .s1
  s2_app := fun _ _ _ _ =>
    ⟨fun h => by cases h with | s2 h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩,
     fun ⟨_, _, h1, h2, h3⟩ => .s2 h1 h2 h3⟩

/-- Fuel-bounded application: the evaluator a host runs. -/
@[expose] def capApply : Nat → CapCode → CapCode → Option CapCode
  | 0, _, _ => none
  | _ + 1, .k, a => some (.k1 a)
  | _ + 1, .k1 a, _ => some a
  | _ + 1, .s, f => some (.s1 f)
  | _ + 1, .s1 f, g => some (.s2 f g)
  | n + 1, .s2 f g, x =>
    match capApply n f x, capApply n g x with
    | some fx, some gx => capApply n fx gx
    | _, _ => none
  | _ + 1, .attenuate mask, a =>
    match a with
    | .cap rights => some (.cap (rights &&& mask))
    | _ => none
  | _ + 1, .guard need, a =>
    match a with
    | .cap rights => some (if subMask need rights then .k else .k1 (.s2 .k .k))
    | _ => none
  | _ + 1, .cap _, _ => none

/-- Whatever the evaluator returns is a `CapApp` result. -/
theorem capApply_sound : ∀ (n : Nat) (f a r : CapCode), capApply n f a = some r → CapApp f a r
  | 0, _, _, _, h => by simp [capApply] at h
  | n + 1, f, a, r, h => by
    cases f with
    | k => simp only [capApply, Option.some.injEq] at h; subst h; exact .k a
    | k1 b => simp only [capApply, Option.some.injEq] at h; subst h; exact .k1 _ _
    | s => simp only [capApply, Option.some.injEq] at h; subst h; exact .s a
    | s1 f' => simp only [capApply, Option.some.injEq] at h; subst h; exact .s1 _ _
    | s2 f' g' =>
      simp only [capApply] at h
      cases h1 : capApply n f' a with
      | none => simp [h1] at h
      | some fx =>
        cases h2 : capApply n g' a with
        | none => simp [h1, h2] at h
        | some gx =>
          simp only [h1, h2] at h
          exact .s2 (capApply_sound n _ _ _ h1) (capApply_sound n _ _ _ h2)
            (capApply_sound n _ _ _ h)
    | cap rights => simp [capApply] at h
    | attenuate mask =>
      cases a with
      | cap rights =>
        simp only [capApply, Option.some.injEq] at h; subst h; exact .attenuate _ _
      | _ => simp [capApply] at h
    | guard need =>
      cases a with
      | cap rights =>
        simp only [capApply, Option.some.injEq] at h
        subst h
        by_cases hs : subMask need rights = true
        · simp only [hs, ↓reduceIte]; exact .guardGrant hs
        · simp only [hs]; exact .guardDeny (by simpa using hs)
      | _ => simp [capApply] at h

private theorem exists_succ_of_pos {m : Nat} (h : 1 ≤ m) : ∃ m', m = m' + 1 :=
  ⟨m - 1, by omega⟩

/-- Every `CapApp` result is returned by the evaluator from some fuel on. -/
theorem capApply_complete {f a r : CapCode} (h : CapApp f a r) :
    ∃ n, ∀ m, n ≤ m → capApply m f a = some r := by
  induction h with
  | k a =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply]
  | k1 a b =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply]
  | s f =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply]
  | s1 f g =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply]
  | s2 _ _ _ ih1 ih2 ih3 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    obtain ⟨n3, h3⟩ := ih3
    refine ⟨n1 + n2 + n3 + 1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos (by omega : 1 ≤ m)
    simp only [capApply, h1 m (by omega), h2 m (by omega)]
    exact h3 m (by omega)
  | attenuate mask rights =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply]
  | guardGrant hg =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply, hg]
  | guardDeny hd =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := exists_succ_of_pos hm
    simp [capApply, hd]

/-- The proposition "is the token with exactly these rights". -/
@[expose] def holdsCap (rights : UInt64) : CapCode → Prop := fun c => c = .cap rights

/-- Attenuation is evidence in the realizability frame of `capPCA`, and it only narrows. -/
theorem attenuate_leads (rights mask : UInt64) :
    (realizabilityFrame capPCA).Leads (holdsCap rights) (CapCode.attenuate mask)
      (holdsCap (rights &&& mask)) ∧ subMask (rights &&& mask) rights = true := by
  refine ⟨?_, subMask_and_left rights mask⟩
  intro a ha
  exact ⟨.cap (rights &&& mask), ha ▸ CapApp.attenuate mask rights, rfl⟩

/-- Two attenuations compose by the frame's `seq`, with the evidence computed. -/
theorem attenuate_seq_leads (rights m₁ m₂ : UInt64) :
    (realizabilityFrame capPCA).Leads (holdsCap rights)
      ((realizabilityFrame capPCA).seq (CapCode.attenuate m₁) (CapCode.attenuate m₂))
      (holdsCap (rights &&& m₁ &&& m₂)) :=
  (realizabilityFrame capPCA).leads_trans (attenuate_leads rights m₁).1
    (attenuate_leads (rights &&& m₁) m₂).1

/-! ## 5. Morris sealer/unsealer: authority is not additive -/

/-- Bit `i` of a rights mask. -/
@[expose] def hasRight (m : UInt64) (i : Nat) : Prop := m.toBitVec.getLsbD i = true

theorem hasRight_or (a b : UInt64) (i : Nat) : hasRight (a ||| b) i ↔ hasRight a i ∨ hasRight b i := by
  simp [hasRight]

theorem not_hasRight_zero (i : Nat) : ¬ hasRight 0 i := by
  simp [hasRight]

theorem eq_of_hasRight_iff {a b : UInt64} (h : ∀ i, hasRight a i ↔ hasRight b i) : a = b :=
  UInt64.toBitVec_inj.1 (BitVec.eq_of_getLsbD_eq fun i _ => Bool.eq_iff_iff.2 (h i))

/-- What a holder may hold: plain rights, a box sealed under a brand, or that brand's unsealer. -/
inductive SealCap where
  | direct (rights : UInt64)
  | sealBox (brand : UInt64) (payload : UInt64)
  | unsealer (brand : UInt64)
  deriving @[expose] DecidableEq, Repr

/-- One step of the authority fold, against the whole holding `h`. -/
@[expose] def authorityStep (h : List SealCap) (acc : UInt64) : SealCap → UInt64
  | .direct r => acc ||| r
  | .sealBox b p => if h.contains (.unsealer b) then acc ||| p else acc
  | .unsealer _ => acc

/-- The authority of a holding: its direct rights, and the payload of every box whose unsealer is
also held. The unsealer lookup is a scan of the holding, so this is quadratic in the number of
boxes times unsealers. -/
@[expose] def authority (h : List SealCap) : UInt64 := h.foldl (authorityStep h) 0

private theorem authority_fold_spec (h l : List SealCap) (acc : UInt64) (i : Nat) :
    hasRight (l.foldl (authorityStep h) acc) i ↔
      hasRight acc i ∨ (∃ r, .direct r ∈ l ∧ hasRight r i) ∨
        (∃ b p, .sealBox b p ∈ l ∧ .unsealer b ∈ h ∧ hasRight p i) := by
  induction l generalizing acc with
  | nil => simp
  | cons c rest ih =>
    rw [List.foldl_cons, ih]
    cases c with
    | direct r =>
      simp only [authorityStep, hasRight_or, List.mem_cons, SealCap.direct.injEq, reduceCtorEq,
        false_or]
      constructor
      · rintro ((h1 | h1) | ⟨r', h1, h2⟩ | h1)
        · exact .inl h1
        · exact .inr (.inl ⟨r, .inl rfl, h1⟩)
        · exact .inr (.inl ⟨r', .inr h1, h2⟩)
        · exact .inr (.inr h1)
      · rintro (h1 | ⟨r', h1 | h1, h2⟩ | h1)
        · exact .inl (.inl h1)
        · exact .inl (.inr (h1 ▸ h2))
        · exact .inr (.inl ⟨r', h1, h2⟩)
        · exact .inr (.inr h1)
    | sealBox b p =>
      simp only [authorityStep, List.mem_cons, SealCap.sealBox.injEq, reduceCtorEq, false_or]
      by_cases hu : h.contains (.unsealer b) = true
      · have hmem : SealCap.unsealer b ∈ h := by simpa using hu
        simp only [hu, ↓reduceIte, hasRight_or]
        constructor
        · rintro ((h1 | h1) | h1 | ⟨b', p', h1, h2, h3⟩)
          · exact .inl h1
          · exact .inr (.inr ⟨b, p, .inl ⟨rfl, rfl⟩, hmem, h1⟩)
          · exact .inr (.inl h1)
          · exact .inr (.inr ⟨b', p', .inr h1, h2, h3⟩)
        · rintro (h1 | h1 | ⟨b', p', ⟨rfl, rfl⟩ | h1, h2, h3⟩)
          · exact .inl (.inl h1)
          · exact .inr (.inl h1)
          · exact .inl (.inr h3)
          · exact .inr (.inr ⟨b', p', h1, h2, h3⟩)
      · have hmem : SealCap.unsealer b ∉ h := by simpa using hu
        simp only [hu]
        constructor
        · rintro (h1 | h1 | ⟨b', p', h1, h2, h3⟩)
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact .inr (.inr ⟨b', p', .inr h1, h2, h3⟩)
        · rintro (h1 | h1 | ⟨b', p', ⟨rfl, rfl⟩ | h1, h2, h3⟩)
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact absurd h2 hmem
          · exact .inr (.inr ⟨b', p', h1, h2, h3⟩)
    | unsealer b =>
      simp only [authorityStep, List.mem_cons, reduceCtorEq, false_or]

/-- **The authority fold, bit by bit.** A right is held exactly when a direct capability carries
it, or a sealed box carries it and the holding also contains that box's unsealer. -/
theorem authority_spec (h : List SealCap) (i : Nat) :
    hasRight (authority h) i ↔
      (∃ r, .direct r ∈ h ∧ hasRight r i) ∨
        (∃ b p, .sealBox b p ∈ h ∧ .unsealer b ∈ h ∧ hasRight p i) := by
  unfold authority
  rw [authority_fold_spec]
  constructor
  · rintro (h1 | h1)
    · exact absurd h1 (not_hasRight_zero i)
    · exact h1
  · exact .inr

/-- Holding more never loses authority. -/
theorem authority_mono {h₁ h₂ : List SealCap} (hsub : ∀ c, c ∈ h₁ → c ∈ h₂) (i : Nat)
    (hi : hasRight (authority h₁) i) : hasRight (authority h₂) i := by
  rw [authority_spec] at hi ⊢
  rcases hi with ⟨r, h1, h2⟩ | ⟨b, p, h1, h2, h3⟩
  · exact .inl ⟨r, hsub _ h1, h2⟩
  · exact .inr ⟨b, p, hsub _ h1, hsub _ h2, h3⟩

/-- Joining two holdings yields at least the join of their authorities. -/
theorem authority_join_ge (h₁ h₂ : List SealCap) (i : Nat)
    (hi : hasRight (authority h₁ ||| authority h₂) i) : hasRight (authority (h₁ ++ h₂)) i := by
  rcases (hasRight_or _ _ i).1 hi with hi | hi
  · exact authority_mono (fun c hc => List.mem_append.2 (.inl hc)) i hi
  · exact authority_mono (fun c hc => List.mem_append.2 (.inr hc)) i hi

/-- A sealed box alone confers nothing. -/
theorem authority_sealBox (brand payload : UInt64) : authority [.sealBox brand payload] = 0 := by
  refine eq_of_hasRight_iff fun i => ?_
  rw [authority_spec]
  simp [not_hasRight_zero]

/-- An unsealer alone confers nothing. -/
theorem authority_unsealer (brand : UInt64) : authority [.unsealer brand] = 0 := by
  refine eq_of_hasRight_iff fun i => ?_
  rw [authority_spec]
  simp [not_hasRight_zero]

/-- Box and matching unsealer together confer exactly the payload. -/
theorem authority_sealed_pair (brand payload : UInt64) :
    authority [.sealBox brand payload, .unsealer brand] = payload := by
  refine eq_of_hasRight_iff fun i => ?_
  rw [authority_spec]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, reduceCtorEq, false_and, exists_false,
    false_or, SealCap.sealBox.injEq, SealCap.unsealer.injEq]
  constructor
  · rintro ⟨b, p, ⟨_, hp⟩, _, h⟩
    exact hp ▸ h
  · intro h
    exact ⟨brand, payload, ⟨rfl, rfl⟩, rfl, h⟩

/-- An unsealer of another brand opens nothing. -/
theorem authority_wrong_brand (brand brand' payload : UInt64) (hne : brand ≠ brand') :
    authority [.sealBox brand payload, .unsealer brand'] = 0 := by
  refine eq_of_hasRight_iff fun i => ?_
  rw [authority_spec]
  simp [not_hasRight_zero, hne]

/-- **Rights amplification.** Every right of the payload is held by the joined holding and by
neither part, so authority of a join strictly exceeds the join of authorities. -/
theorem amplify_superadditive (brand payload : UInt64) (i : Nat) (hp : hasRight payload i) :
    hasRight (authority ([.sealBox brand payload] ++ [.unsealer brand])) i ∧
      ¬ hasRight (authority [.sealBox brand payload] ||| authority [.unsealer brand]) i := by
  constructor
  · rw [List.singleton_append, authority_sealed_pair]; exact hp
  · rw [authority_sealBox, authority_unsealer, hasRight_or]
    exact fun h => h.elim (not_hasRight_zero i) (not_hasRight_zero i)

/-- **Authority is not a sum of per-capability weights.** No valuation of single capabilities
reproduces `authority` on every holding, which is what a linear, conserved resource would require. -/
theorem authority_not_additive :
    ¬ ∃ w : SealCap → UInt64, ∀ h : List SealCap,
        authority h = h.foldl (fun acc c => acc ||| w c) 0 := by
  rintro ⟨w, hw⟩
  have h1 := hw [.sealBox 0 1]
  have h2 := hw [.unsealer 0]
  have h3 := hw [.sealBox 0 1, .unsealer 0]
  rw [authority_sealBox] at h1
  rw [authority_unsealer] at h2
  rw [authority_sealed_pair] at h3
  simp only [List.foldl_cons, List.foldl_nil, UInt64.zero_or] at h1 h2 h3
  rw [← h1, ← h2] at h3
  exact absurd h3 (by decide)

/-! ## 6. Kleene three-valued caveats -/

/-- A caveat verdict: true, false, or not determined by the facts at hand. -/
inductive KleenePred3 where
  | true3
  | false3
  | unbound3
  deriving @[expose] DecidableEq, Repr

namespace KleenePred3

/-- Strong Kleene conjunction. -/
@[expose] def and3 : KleenePred3 → KleenePred3 → KleenePred3
  | false3, _ => false3
  | _, false3 => false3
  | true3, true3 => true3
  | _, _ => unbound3

/-- Strong Kleene disjunction. -/
@[expose] def or3 : KleenePred3 → KleenePred3 → KleenePred3
  | true3, _ => true3
  | _, true3 => true3
  | false3, false3 => false3
  | _, _ => unbound3

/-- Negation. `unbound3` stays `unbound3`. -/
@[expose] def not3 : KleenePred3 → KleenePred3
  | true3 => false3
  | false3 => true3
  | unbound3 => unbound3

/-- Fail-closed acceptance: only `true3`. -/
@[expose] def accepts : KleenePred3 → Bool
  | true3 => true
  | _ => false

/-- The information order: `unbound3` may become anything, a decided verdict stays. -/
@[expose] def Refines (p q : KleenePred3) : Prop := p = unbound3 ∨ p = q

/-- **Negation safety.** A negation is accepted only when its operand is decided false. -/
theorem accepts_not3 (p : KleenePred3) : accepts (not3 p) = true ↔ p = false3 := by
  cases p <;> simp [accepts, not3]

theorem accepts_and3 (p q : KleenePred3) : accepts (and3 p q) = (accepts p && accepts q) := by
  cases p <;> cases q <;> rfl

theorem and3_eq_false3_left (p q : KleenePred3) (h : p = false3) : and3 p q = false3 := by
  subst h; rfl

theorem not3_refines {p q : KleenePred3} (h : Refines p q) : Refines (not3 p) (not3 q) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem and3_refines {p p' q q' : KleenePred3} (hp : Refines p p') (hq : Refines q q') :
    Refines (and3 p q) (and3 p' q') := by
  cases p <;> cases p' <;> cases q <;> cases q' <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (rcases hp with h | h <;> cases h <;> done)
    | (rcases hq with h | h <;> cases h <;> done)

theorem or3_refines {p p' q q' : KleenePred3} (hp : Refines p p') (hq : Refines q q') :
    Refines (or3 p q) (or3 p' q') := by
  cases p <;> cases p' <;> cases q <;> cases q' <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (rcases hp with h | h <;> cases h <;> done)
    | (rcases hq with h | h <;> cases h <;> done)

end KleenePred3

/-- Caveat expressions over numbered facts. -/
inductive Caveat where
  | atom (v : Nat)
  | const (b : Bool)
  | and (a b : Caveat)
  | or (a b : Caveat)
  | not (a : Caveat)
  deriving @[expose] DecidableEq, Repr

namespace Caveat
open KleenePred3

/-- Evaluate a caveat against a partial assignment of its facts. -/
@[expose] def eval (ρ : Nat → KleenePred3) : Caveat → KleenePred3
  | .atom v => ρ v
  | .const b => if b then true3 else false3
  | .and a b => and3 (eval ρ a) (eval ρ b)
  | .or a b => or3 (eval ρ a) (eval ρ b)
  | .not a => not3 (eval ρ a)

/-- **Fail-closed monotonicity.** Binding more facts refines the verdict and never reverses it. -/
theorem eval_refines {ρ ρ' : Nat → KleenePred3} (h : ∀ v, Refines (ρ v) (ρ' v)) (c : Caveat) :
    Refines (c.eval ρ) (c.eval ρ') := by
  induction c with
  | atom v => exact h v
  | const b => exact Or.inr rfl
  | and a b iha ihb => exact and3_refines iha ihb
  | or a b iha ihb => exact or3_refines iha ihb
  | not a iha => exact not3_refines iha

/-- An accepted caveat stays accepted however the missing facts are later bound. -/
theorem accepts_stable {ρ ρ' : Nat → KleenePred3} (h : ∀ v, Refines (ρ v) (ρ' v)) (c : Caveat)
    (hacc : accepts (c.eval ρ) = true) : accepts (c.eval ρ') = true := by
  rcases eval_refines h c with hu | he
  · rw [hu] at hacc; cases hacc
  · rw [← he]; exact hacc

/-- A refused caveat stays refused however the missing facts are later bound. -/
theorem refuses_stable {ρ ρ' : Nat → KleenePred3} (h : ∀ v, Refines (ρ v) (ρ' v)) (c : Caveat)
    (hrej : c.eval ρ = false3) : c.eval ρ' = false3 := by
  rcases eval_refines h c with hu | he
  · rw [hu] at hrej; cases hrej
  · rw [← he]; exact hrej

end Caveat

end Obend.Polis
end
