module
/-
# Obend.Reasons — observations, assumptions, explanations, defeaters and proposed actions, with
# current usability a derived judgment

A shared substrate in which a process (to begin with, the swarm's own) keeps its reasons: what it
OBSERVED (a line of a build log, verbatim, with where it was read), what it ASSUMED (an abducible: a
hypothesis it may withdraw), the EXPLANATIONS it proposed (each derives a conclusion from premises,
unless one of its defeaters is supported), the DEFEATERS it declared against an explanation, and the
ACTIONS it proposed, each with its justification. Nothing stores "this conclusion holds": whether a
conclusion is usable now is computed from the observations, the assumptions held and the theory, and
so is whether an action is admissible.

This is the substrate. It does not model minds, valence, consciousness or experience; it is what a
process can keep its reasons in so that they stay checkable while its conclusions change.

**The judgment is the well-founded model (an instance, cited).** The explanations are the rules of a
normal logic program (`p ← q₁ … qₙ, not d₁ … not dₘ`, a premise list and a defeater list); the
observations and the assumptions held are its facts. A conclusion is SUPPORTED, UNDEFINED or
UNSUPPORTED as it is true, undefined or false in the well-founded model of Van Gelder, Ross and
Schlipf (*The Well-Founded Semantics for General Logic Programs*, JACM 38(3), 1991), computed by Van
Gelder's alternating fixpoint (*The Alternating Fixpoint of Logic Programs with Negation*, PODS 1989;
JCSS 47(1), 1993): `Γ J` is the least model of the program with every rule defeated by `J` removed
(the Gelfond–Lifschitz reduct, *The Stable Model Semantics for Logic Programming*, ICLP 1988), the
supported atoms are the least fixpoint of `Γ ∘ Γ`, and the atoms not even possible are those outside
`Γ` of it. What is proved here of the computation: `Γ J` is the least fixpoint of the reduct's
immediate consequence (`gamma_fix`, `gamma_least`), the rounds reach a fixpoint of `Γ ∘ Γ` that is
below every other (`rounds_fix`, `rounds_least`), and a conclusion is supported exactly when one of
its explanations stands (`supported_iff`). That this alternating fixpoint is VGRS's unfounded-set
definition is Van Gelder's theorem, cited and not re-proved.

**Where this departs from the brief, and why.** The brief asked that a conclusion whose only support
is a cycle through itself be UNDEFINED. In the well-founded semantics it is FALSE: a cycle of
premises with no well-founded entry is an unfounded set, and VGRS put an unfounded set at false
precisely so that an unsupported cycle cannot create a conclusion. `no_conclusion_from_cycles` says
that (unsupported, so never supported). UNDEFINED is what the semantics gives a cycle through DEFEAT:
two explanations each defeated by the other's conclusion, with no evidence to choose. That is the
competing-explanations case, and the walkthrough shows it: the well-founded model declines to choose
where the stable models (Gelfond–Lifschitz) would offer one model per choice.

**Lifetime with many supporters.** A conclusion stands while any one of its explanations stands
(`supported_iff`): the lifetime of an assertion with several supporters in Syndicate (Garnock-Jones,
*Conversational Concurrency*, 2017, §5.6, transfer without a spurious absence) and the many
environments of de Kleer's ATMS (*An Assumption-based TMS*, AIJ 28, 1986), where withdrawing one
environment of a node's label leaves the node in while another environment holds. The ATMS label
itself (the minimal environments) is not computed: a judgment here is over the assumptions held now,
and a withdrawal is judged incrementally (`State.step`) rather than read off precomputed labels.
`survives_one_support`: withdrawing one of two supports leaves the conclusion supported, and since
the judgment anyone reads is the state's, replaced in one step, there is no state in which it is
absent.

**Defeat only by evidence.** The judgment is a function of the observations, the assumptions held,
the explanations and the defeaters (`defeat_only_by_evidence`); a proposed action is not an input of
it, so proposing or admitting actions changes no status (`propose_keeps_judgment`). For a fixed
theory a status moves only with an observation or an assumption, and only inside that atom's cone
(`evidence_local`): what does not depend on it keeps its status, by the locality of the well-founded
model over a set closed under dependence (`wf_local`).

**Incremental equals from scratch.** The state keeps the judgment as last computed beside the base.
An action changes neither; an observation or an assumption recomputes only the cone of its atom (the
atoms that depend on it), over the program restricted to what that cone depends on, and keeps every
other status; a new explanation or defeater recomputes all. `from_scratch_consistent`: after every
step the kept judgment is the well-founded model of the current base. The cone and its closure are
computed by bounded iteration and CHECKED (`upClosedB`, `closedB`) before they are used; a check that
fails falls back to the whole recomputation, so the theorem rests on the checks, not on the
iteration's bound. `run_consistent`: every state a run of events reaches from the empty one keeps the
base's judgment. (The splitting-set refinement, Lifschitz and Turner, *Splitting a Logic Program*,
ICLP 1994, which would recompute the cone alone with the statuses below it frozen, is not done: the
cone is recomputed over everything it depends on.)

**Actions need support now.** `action_needs_support`: a proposed action is admitted only when its
justification is supported in the current judgment, and refused by name otherwise, with the reason
(`whyNot`: the withdrawn assumption, the premise that is not supported, the defeater that is, the
cycle a premise rests on). The vault's judge consumes the same check: a form's fill may carry a
justification, and `Obend.Vault.Replay` lands it only while it is supported
(`Obend.Vault.Replay.justified_needs_support`).

**Not here.** Abduction as search (proposing explanations from integrity constraints, Kakas,
Kowalski and Toni, *Abductive Logic Programming*, JLC 2(6), 1992) is not done: explanations are
proposed by whoever reasons, and the substrate judges them. AGM revision (Alchourrón, Gärdenfors,
Makinson 1985) is not modelled; withdrawal is of an assumption, not contraction of a theory. Elkan
(*A Rational Reconstruction of Nonmonotonic Truth Maintenance Systems*, AIJ 43, 1990) is the reason
the judgment is a semantics computed from the base and not a labelling maintained by dependency
bookkeeping. Hennix: the 1979 *17 Points on Intensional Logics for Intransitive Experiences* is
located in a bibliography and not read; nothing here is attributed to it.
-/
public import Lean.Data.Json
public import Std.Data.TreeMap
public section

namespace Obend.Reasons

set_option autoImplicit false

/-! ## 1. Explanations as rules, and the judgment as the well-founded model -/

/-- **An explanation**: `concl` follows from the premises `pos`, unless one of the defeaters `neg` is
supported. -/
structure Rule where
  name : String
  concl : String
  pos : List String
  neg : List String := []
deriving DecidableEq, Repr

/-- A program: its facts (what is observed and what is assumed now) and its rules. -/
structure Program where
  facts : List String
  rules : List Rule

/-- A rule fires at `I` against `J`: every premise is in `I`, no defeater is in `J`. -/
@[expose] def fires (J I : List String) (r : Rule) : Bool :=
  r.pos.all (fun p => I.contains p) && r.neg.all (fun d => !J.contains d)

/-- The immediate consequence of the program with the rules `J` defeats removed. -/
@[expose] def T (P : Program) (J I : List String) : List String :=
  P.facts ++ (P.rules.filter (fires J I)).map (·.concl)

/-- Its stages, from nothing. -/
@[expose] def stage (P : Program) (J : List String) : Nat → List String
  | 0 => []
  | n + 1 => T P J (stage P J n)

/-- The atoms a program can name as true: its facts and its rules' conclusions. -/
abbrev atomsOf (P : Program) : List String := P.facts ++ P.rules.map (·.concl)

/-- Enough stages and rounds: one more than the universe is long. -/
abbrev bound (P : Program) : Nat := (atomsOf P).length + 1

/-- **`Γ J`**: the least model of the program with the rules defeated by `J` removed. -/
abbrev gamma (P : Program) (J : List String) : List String := stage P J (bound P)

/-- **The alternating fixpoint**: `t₀ = ∅`, `tₖ₊₁ = Γ (Γ tₖ)`. -/
@[expose] def rounds (P : Program) : Nat → List String
  | 0 => []
  | k + 1 => gamma P (gamma P (rounds P k))

/-- **The well-founded model**: the supported atoms, and the possible ones (supported or undefined). -/
@[expose] def wf (P : Program) : List String × List String :=
  let t := rounds P (bound P)
  (t, gamma P t)

inductive Status where
  | supported
  | undefined
  | unsupported
deriving DecidableEq, Repr

@[expose] def Status.text : Status → String
  | .supported => "supported"
  | .undefined => "undefined"
  | .unsupported => "unsupported"

/-- A status read off a judgment (supported atoms, possible atoms). -/
@[expose] def statusIn (j : List String × List String) (x : String) : Status :=
  if j.1.contains x then .supported else if j.2.contains x then .undefined else .unsupported

/-! ## 2. Sets as lists, read by membership -/

/-- Two lists with the same members. -/
abbrev Same (I I' : List String) : Prop := ∀ x, x ∈ I ↔ x ∈ I'

/-- `I ⊆ I'` by members. -/
abbrev Sub (I I' : List String) : Prop := ∀ x, x ∈ I → x ∈ I'

theorem Same.refl (I : List String) : Same I I := fun _ => Iff.rfl
theorem Same.symm {I I' : List String} (h : Same I I') : Same I' I := fun x => (h x).symm
theorem Same.trans {I I' I'' : List String} (h : Same I I') (h' : Same I' I'') : Same I I'' :=
  fun x => (h x).trans (h' x)

theorem contains_eq_of_same {I I' : List String} (h : Same I I') (x : String) :
    I.contains x = I'.contains x := by
  have := h x
  cases h1 : I.contains x <;> cases h2 : I'.contains x <;> simp_all

theorem fires_congr {J J' I I' : List String} (hJ : Same J J') (hI : Same I I') (r : Rule) :
    fires J I r = fires J' I' r := by
  simp only [fires, contains_eq_of_same hJ, contains_eq_of_same hI]

theorem T_congr (P : Program) {J J' I I' : List String} (hJ : Same J J') (hI : Same I I') :
    T P J I = T P J' I' := by
  simp only [T]
  congr 2
  exact List.filter_congr fun r _ => fires_congr hJ hI r

theorem stage_congr (P : Program) {J J' : List String} (hJ : Same J J') :
    ∀ n, stage P J n = stage P J' n
  | 0 => rfl
  | n + 1 => by simp only [stage]; rw [stage_congr P hJ n]; exact T_congr P hJ (Same.refl _)

theorem gamma_congr (P : Program) {J J' : List String} (hJ : Same J J') : gamma P J = gamma P J' :=
  stage_congr P hJ _

theorem mem_T {P : Program} {J I : List String} {x : String} :
    x ∈ T P J I ↔ x ∈ P.facts ∨ ∃ r ∈ P.rules, fires J I r = true ∧ r.concl = x := by
  simp [T, List.mem_map, List.mem_filter, and_assoc]

theorem fires_iff {J I : List String} {r : Rule} :
    fires J I r = true ↔ (∀ p ∈ r.pos, p ∈ I) ∧ (∀ d ∈ r.neg, d ∉ J) := by
  simp [fires, List.all_eq_true]

theorem fires_mono {J J' I I' : List String} (hJ : Sub J' J) (hI : Sub I I') {r : Rule}
    (h : fires J I r = true) : fires J' I' r = true := by
  rw [fires_iff] at h ⊢
  exact ⟨fun p hp => hI p (h.1 p hp), fun d hd hd' => h.2 d hd (hJ d hd')⟩

theorem T_mono (P : Program) {J J' I I' : List String} (hJ : Sub J' J) (hI : Sub I I') :
    Sub (T P J I) (T P J' I') := by
  intro x hx
  rw [mem_T] at hx ⊢
  rcases hx with h | ⟨r, hr, hf, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, hr, fires_mono hJ hI hf, hc⟩

theorem T_universe (P : Program) (J I : List String) : Sub (T P J I) (atomsOf P) := by
  intro x hx
  rw [mem_T] at hx
  simp only [atomsOf, List.mem_append, List.mem_map]
  rcases hx with h | ⟨r, hr, -, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, hr, hc⟩

theorem stage_universe (P : Program) (J : List String) : ∀ n, Sub (stage P J n) (atomsOf P)
  | 0 => fun _ h => by simp [stage] at h
  | _ + 1 => T_universe P J _

theorem stage_step (P : Program) (J : List String) : ∀ n, Sub (stage P J n) (stage P J (n + 1))
  | 0 => fun _ h => by simp [stage] at h
  | n + 1 => T_mono P (fun _ h => h) (stage_step P J n)

theorem stage_anti (P : Program) {J J' : List String} (hJ : Sub J' J) :
    ∀ n, Sub (stage P J n) (stage P J' n)
  | 0 => fun _ h => h
  | n + 1 => T_mono P hJ (stage_anti P hJ n)

/-! ## 3. Every rising sequence in a finite atomsOf stops rising

The one counting argument: a sequence of member-sets of `U` that rises, and whose next term depends
only on the members of this one, stops within `U.length` steps, and stays. Used three times: for the
stages of `Γ`, for the rounds of the alternating fixpoint, and nowhere else (the cone and its
closure are checked, not counted). -/

theorem filter_length_le {L : List String} {p q : String → Bool} (h : ∀ x ∈ L, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a (List.mem_cons_self ..)
    by_cases hp : p a = true <;> by_cases hq : q a = true <;>
      simp_all <;> omega

theorem filter_length_lt {L : List String} {p q : String → Bool} (h : ∀ x ∈ L, p x = true → q x = true)
    {y : String} (hy : y ∈ L) (hq : q y = true) (hp : p y = false) :
    (L.filter p).length < (L.filter q).length := by
  induction L with
  | nil => simp at hy
  | cons a L ih =>
    have hL : ∀ x ∈ L, p x = true → q x = true := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ha := h a (List.mem_cons_self ..)
    rcases List.mem_cons.1 hy with rfl | hy'
    · have := filter_length_le hL
      simp_all
      omega
    · have := ih hL hy'
      by_cases hpa : p a = true <;> by_cases hqa : q a = true <;>
        simp_all <;> omega

/-- The count of `U`'s entries in `I`. -/
def count (U I : List String) : Nat := (U.filter (fun x => I.contains x)).length

theorem count_le (U I : List String) : count U I ≤ U.length := List.length_filter_le _ _

theorem count_lt {U I I' : List String} (hsub : Sub I I') {y : String} (hyU : y ∈ U) (hy : y ∈ I')
    (hy' : y ∉ I) : count U I < count U I' := by
  apply filter_length_lt (fun x _ h => by simp only [List.contains_iff_mem] at h ⊢; exact hsub x h) hyU
  · simpa [List.contains_iff_mem] using hy
  · simpa [List.contains_iff_mem] using hy'

/-- **A rising sequence in `U` stops.** If `seq (n+1) = F (seq n)` with `F` reading only members,
`seq` rises and stays in `U`, then from `U.length` on it has the members of `seq U.length`. -/
theorem stabilizes (U : List String) (F : List String → List String) (seq : Nat → List String)
    (hF : ∀ n, seq (n + 1) = F (seq n)) (hcongr : ∀ I I', Same I I' → F I = F I')
    (hrise : ∀ n, Sub (seq n) (seq (n + 1))) (hU : ∀ n, Sub (seq n) U) :
    ∀ m, U.length ≤ m → Same (seq m) (seq U.length) := by
  -- some step does not rise
  have hflat : ∃ n, n ≤ U.length ∧ Same (seq (n + 1)) (seq n) := by
    refine Classical.byContradiction fun hno => ?_
    have hgrow : ∀ n, n ≤ U.length + 1 → n ≤ count U (seq n) := by
      intro n
      induction n with
      | zero => intro _; exact Nat.zero_le _
      | succ n ih =>
        intro hn
        have ih := ih (by omega)
        have hns : ¬ Same (seq (n + 1)) (seq n) := fun hs => hno ⟨n, by omega, hs⟩
        have : ∃ y, y ∈ seq (n + 1) ∧ y ∉ seq n := by
          refine Classical.byContradiction fun hall => hns fun x => ⟨fun hx => ?_, fun hx => hrise n x hx⟩
          exact Classical.byContradiction fun hx' => hall ⟨x, hx, hx'⟩
        obtain ⟨y, hy, hy'⟩ := this
        have := count_lt (hrise n) (hU (n + 1) y hy) hy hy'
        omega
    have := hgrow (U.length + 1) (Nat.le_refl _)
    have := count_le U (seq (U.length + 1))
    omega
  obtain ⟨n, hn, hs⟩ := hflat
  -- from there on it is constant
  have hconst : ∀ j, seq (n + 1 + j) = seq (n + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, hF, ih, hcongr _ _ hs, hF n]
  have hall : ∀ m, n ≤ m → Same (seq m) (seq n) := by
    intro m hm
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact Same.refl _
    · have := hconst (m - n - 1)
      rw [show n + 1 + (m - n - 1) = m by omega] at this
      rw [this]; exact hs
  intro m hm
  exact (hall m (by omega)).trans (hall U.length hn).symm

/-! ## 4. `Γ` is the least model of the reduct; the rounds reach the least fixpoint of `Γ ∘ Γ` -/

theorem stage_stable (P : Program) (J : List String) :
    ∀ m, (atomsOf P).length ≤ m → Same (stage P J m) (stage P J (atomsOf P).length) :=
  stabilizes (atomsOf P) (T P J) (stage P J) (fun _ => rfl)
    (fun _ _ h => T_congr P (Same.refl J) h) (stage_step P J) (stage_universe P J)

/-- Any stage past the atomsOf's length is `Γ`. -/
theorem stage_gamma (P : Program) (J : List String) {m : Nat} (hm : (atomsOf P).length ≤ m) :
    Same (stage P J m) (gamma P J) :=
  (stage_stable P J m hm).trans (stage_stable P J (bound P) (by simp [bound])).symm

/-- **`Γ J` is a fixpoint** of the reduct's immediate consequence. -/
theorem gamma_fix (P : Program) (J : List String) : Same (T P J (gamma P J)) (gamma P J) :=
  stage_gamma P J (m := bound P + 1) (by simp [bound]; omega)

/-- **…and the least**: below every set the reduct's consequence does not leave. -/
theorem gamma_least (P : Program) (J I : List String) (h : Sub (T P J I) I) : Sub (gamma P J) I := by
  have : ∀ n, Sub (stage P J n) I := by
    intro n
    induction n with
    | zero => intro _ h; simp [stage] at h
    | succ n ih => exact fun x hx => h x (T_mono P (fun _ h => h) ih x hx)
  exact this _

theorem mem_gamma {P : Program} {J : List String} {x : String} :
    x ∈ gamma P J ↔ x ∈ P.facts ∨ ∃ r ∈ P.rules, r.concl = x ∧ (∀ p ∈ r.pos, p ∈ gamma P J) ∧
      (∀ d ∈ r.neg, d ∉ J) := by
  rw [← gamma_fix P J x, mem_T]
  simp only [fires_iff]
  constructor
  · rintro (h | ⟨r, hr, ⟨hp, hn⟩, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hc, hp, hn⟩
  · rintro (h | ⟨r, hr, hc, hp, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, ⟨hp, hn⟩, hc⟩

/-- **`Γ` is antitone**: defeating more yields less. -/
theorem gamma_anti (P : Program) {J J' : List String} (h : Sub J' J) : Sub (gamma P J) (gamma P J') :=
  stage_anti P h _

theorem gamma_universe (P : Program) (J : List String) : Sub (gamma P J) (atomsOf P) :=
  stage_universe P J _

theorem rounds_step (P : Program) : ∀ k, Sub (rounds P k) (rounds P (k + 1))
  | 0 => fun _ h => by simp [rounds] at h
  | k + 1 => gamma_anti P (gamma_anti P (rounds_step P k))

theorem rounds_universe (P : Program) : ∀ k, Sub (rounds P k) (atomsOf P)
  | 0 => fun _ h => by simp [rounds] at h
  | _ + 1 => gamma_universe P _

theorem rounds_stable (P : Program) :
    ∀ m, (atomsOf P).length ≤ m → Same (rounds P m) (rounds P (atomsOf P).length) :=
  stabilizes (atomsOf P) (fun I => gamma P (gamma P I)) (rounds P) (fun _ => rfl)
    (fun _ _ h => by rw [gamma_congr P h]) (rounds_step P) (rounds_universe P)

theorem rounds_wf (P : Program) {m : Nat} (hm : (atomsOf P).length ≤ m) :
    Same (rounds P m) (wf P).1 :=
  (rounds_stable P m hm).trans (rounds_stable P (bound P) (by simp [bound])).symm

/-- **The supported atoms are a fixpoint of `Γ ∘ Γ`.** -/
theorem rounds_fix (P : Program) : Same (gamma P (gamma P (wf P).1)) (wf P).1 :=
  rounds_wf P (m := bound P + 1) (by simp [bound]; omega)

/-- **…below every other**: the least fixpoint of `Γ ∘ Γ`, the well-founded model's true atoms by
the alternating fixpoint characterization. -/
theorem rounds_least (P : Program) (X : List String) (h : Sub (gamma P (gamma P X)) X) :
    Sub (wf P).1 X := by
  have : ∀ k, Sub (rounds P k) X := by
    intro k
    induction k with
    | zero => intro _ h; simp [rounds] at h
    | succ k ih => exact fun x hx => h x (gamma_anti P (gamma_anti P ih) x hx)
  exact this _

/-- The supported atoms are among the possible ones: a status is one of three, consistently. -/
theorem supported_possible (P : Program) : Sub (wf P).1 (wf P).2 := by
  -- tₖ ⊆ Γ tₖ for every round
  have : ∀ k, Sub (rounds P k) (gamma P (rounds P k)) := by
    intro k
    induction k with
    | zero => intro _ h; simp [rounds] at h
    | succ k ih =>
      have h1 : Sub (rounds P (k + 1)) (gamma P (rounds P k)) := gamma_anti P ih
      exact fun x hx => gamma_anti P h1 x hx
  exact this _

/-! ## 4b. Unboxed indexed execution (`gammaExec`, `wfExec`) with early fixpoint termination -/

theorem gamma_eq_T_self (P : Program) (J : List String) :
    gamma P J = T P J (gamma P J) := by
  change stage P J ((atomsOf P).length + 1) = T P J (gamma P J)
  simp only [stage]
  exact T_congr P (Same.refl J) (stage_gamma P J (Nat.le_refl _))

theorem wf_fst_eq_T (P : Program) :
    (wf P).1 = T P (wf P).2 (wf P).1 :=
  calc (wf P).1
    _ = gamma P (gamma P (rounds P (atomsOf P).length)) := rfl
    _ = gamma P (wf P).2 := by rw [gamma_congr P (rounds_wf P (Nat.le_refl _))]; rfl
    _ = T P (wf P).2 (gamma P (wf P).2) := gamma_eq_T_self P (wf P).2
    _ = T P (wf P).2 (wf P).1 := T_congr P (Same.refl _) (rounds_fix P)

theorem wf_snd_eq_T (P : Program) :
    (wf P).2 = T P (wf P).1 (wf P).2 :=
  gamma_eq_T_self P (wf P).1

theorem stage_const_of_same (P : Program) (J : List String) {n : Nat}
    (hs : Same (stage P J (n + 1)) (stage P J n)) :
    Same (stage P J n) (gamma P J) := by
  have hconst : ∀ k, stage P J (n + 1 + k) = stage P J (n + 1) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 by omega]
      simp only [stage, ih]
      exact T_congr P (Same.refl J) hs
  let m := (n + 1) + (atomsOf P).length
  have hm : stage P J m = stage P J (n + 1) := hconst (atomsOf P).length
  exact hs.symm.trans (hm ▸ stage_gamma P J (m := m) (by omega))

theorem rounds_const_of_same (P : Program) {k : Nat}
    (hs : Same (rounds P (k + 1)) (rounds P k)) :
    Same (rounds P k) (wf P).1 := by
  have hconst : ∀ j, rounds P (k + 1 + j) = rounds P (k + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show k + 1 + (j + 1) = (k + 1 + j) + 1 by omega]
      change gamma P (gamma P (rounds P (k + 1 + j))) = rounds P (k + 1)
      rw [ih]
      exact congrArg (gamma P) (gamma_congr P hs)
  let m := (k + 1) + (atomsOf P).length
  have hm : rounds P m = rounds P (k + 1) := hconst (atomsOf P).length
  exact hs.symm.trans (hm ▸ rounds_wf P (m := m) (by omega))

/-- Dense `0 .. U - 1` atom interning table backed by `Std.TreeMap String Nat` + `Array String`. -/
structure AtomTable where
  toIdx : Std.TreeMap String Nat := ∅
  ofIdx : Array String := #[]

def AtomTable.WF (tab : AtomTable) : Prop :=
  ∀ (s : String) (i : Nat), tab.toIdx[s]? = some i ↔ tab.ofIdx[i]? = some s

def internAtom (tab : AtomTable) (s : String) : AtomTable :=
  match tab.toIdx[s]? with
  | some _ => tab
  | none =>
    let idx := tab.ofIdx.size
    { toIdx := tab.toIdx.insert s idx, ofIdx := tab.ofIdx.push s }

def internAll (xs : List String) : AtomTable :=
  xs.foldl internAtom {}

theorem empty_atomTable_wf : ({} : AtomTable).WF := by
  intro s i
  simp

theorem internAtom_wf {tab : AtomTable} (hwf : tab.WF) (s : String) :
    (internAtom tab s).WF ∧ ∃ i, (internAtom tab s).toIdx[s]? = some i := by
  open Std in
  unfold internAtom
  cases hs : tab.toIdx[s]? with
  | some k =>
    exact ⟨hwf, k, hs⟩
  | none =>
    dsimp only
    refine ⟨?_, tab.ofIdx.size, by simp⟩
    intro q i
    rw [Std.TreeMap.getElem?_insert, Array.getElem?_push]
    simp only [Std.compare_eq_iff_eq]
    by_cases hsq : s = q
    · subst hsq
      by_cases hi : i = tab.ofIdx.size
      · subst hi; simp
      · have hne : tab.ofIdx.size ≠ i := fun e => hi e.symm
        simp only [Option.some.injEq, hi, hne, ↓reduceIte, false_iff]
        intro hget
        have hsome := (hwf s i).2 hget
        rw [hs] at hsome
        cases hsome
    · simp only [hsq, ↓reduceIte]
      by_cases hi : i = tab.ofIdx.size
      · subst hi
        simp only [↓reduceIte, Option.some.injEq]
        constructor
        · intro hq
          have hget := (hwf q tab.ofIdx.size).1 hq
          have hlt : tab.ofIdx.size < tab.ofIdx.size := (Array.getElem?_eq_some_iff.1 hget).1
          omega
        · intro heq; exact absurd heq hsq
      · simp only [hi, ↓reduceIte]
        exact hwf q i

theorem internAtom_preserves {tab : AtomTable} (s q : String) (i : Nat)
    (hq : tab.toIdx[q]? = some i) :
    (internAtom tab s).toIdx[q]? = some i := by
  unfold internAtom
  cases hs : tab.toIdx[s]? with
  | some _ => exact hq
  | none =>
    dsimp only
    rw [Std.TreeMap.getElem?_insert]
    simp only [Std.compare_eq_iff_eq]
    by_cases hsq : s = q
    · subst hsq; rw [hs] at hq; cases hq
    · simp [hsq, hq]

theorem foldl_internAtom_wf :
    ∀ (xs : List String) (tab : AtomTable), tab.WF →
      (xs.foldl internAtom tab).WF ∧
      (∀ (s : String) (i : Nat), tab.toIdx[s]? = some i → (xs.foldl internAtom tab).toIdx[s]? = some i) ∧
      (∀ x ∈ xs, ∃ i, (xs.foldl internAtom tab).toIdx[x]? = some i)
  | [], tab, hwf => ⟨hwf, fun _ _ h => h, fun _ hx => nomatch hx⟩
  | x :: xs, tab, hwf => by
    obtain ⟨hwf1, i0, hi0⟩ := internAtom_wf hwf x
    obtain ⟨hwf2, hpres2, hmem2⟩ := foldl_internAtom_wf xs (internAtom tab x) hwf1
    refine ⟨hwf2, fun s i hs => hpres2 s i (internAtom_preserves x s i hs), ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hyt
    · exact ⟨i0, hpres2 y i0 hi0⟩
    · exact hmem2 y hyt

theorem internAll_wf (xs : List String) :
    (internAll xs).WF ∧ ∀ x ∈ xs, ∃ i, (internAll xs).toIdx[x]? = some i := by
  obtain ⟨hwf, _, hmem⟩ := foldl_internAtom_wf xs {} empty_atomTable_wf
  exact ⟨hwf, hmem⟩

def progAtoms (P : Program) (extra : List String) : List String :=
  extra ++ P.facts ++ P.rules.flatMap (fun r => r.concl :: (r.pos ++ r.neg))

/-- Bitset invariant: `bits[i]` holds iff `tab.ofIdx[i] ∈ I`. -/
def Represents (tab : AtomTable) (bits : Array Bool) (I : List String) : Prop :=
  ∃ hsz : bits.size = tab.ofIdx.size,
    ∀ (i : Nat) (hi : i < tab.ofIdx.size),
      bits[i]'(by omega) = true ↔ tab.ofIdx[i]'hi ∈ I

theorem represents_congr {tab : AtomTable} {bits : Array Bool} {I I' : List String}
    (h : Represents tab bits I) (hs : Same I I') : Represents tab bits I' :=
  ⟨h.1, fun i hi => (h.2 i hi).trans (hs _)⟩

def encodeBits (tab : AtomTable) (xs : List String) : Array Bool :=
  xs.foldl (fun acc x =>
    match tab.toIdx[x]? with
    | some i => acc.setIfInBounds i true
    | none => acc) (Array.replicate tab.ofIdx.size false)

theorem encodeBits_step {tab : AtomTable} (hwf : tab.WF) {acc : Array Bool} {I : List String}
    (hrep : Represents tab acc I) (x : String) :
    Represents tab (match tab.toIdx[x]? with | some i => acc.setIfInBounds i true | none => acc) (x :: I) := by
  obtain ⟨hsz, hiff⟩ := hrep
  cases hx : tab.toIdx[x]? with
  | none =>
    refine ⟨hsz, fun i hi => ?_⟩
    rw [hiff i hi, List.mem_cons]
    refine ⟨Or.inr, fun h => h.elim (fun heq => ?_) id⟩
    have hsome : tab.toIdx[x]? = some i := (hwf x i).2 (by rw [Array.getElem?_eq_getElem hi, heq])
    rw [hx] at hsome; cases hsome
  | some idx =>
    dsimp only
    have hget := (hwf x idx).1 hx
    obtain ⟨hidx, hxEq⟩ := Array.getElem?_eq_some_iff.1 hget
    have hidxAcc : idx < acc.size := by omega
    refine ⟨by simp [hsz], fun i hi => ?_⟩
    have hiAcc : i < acc.size := by omega
    rw [List.mem_cons]
    by_cases heq : idx = i
    · subst heq
      simp [hxEq]
    · rw [Array.getElem_setIfInBounds_ne hiAcc heq, hiff i hi]
      refine ⟨Or.inr, fun h => h.elim (fun hxs => ?_) id⟩
      have h1 : tab.toIdx[x]? = some i := (hwf x i).2 (by rw [Array.getElem?_eq_getElem hi, hxs])
      rw [hx] at h1; injection h1 with h2; exact absurd h2 heq

theorem encodeBits_represents {tab : AtomTable} (hwf : tab.WF) (xs : List String) :
    Represents tab (encodeBits tab xs) xs := by
  unfold encodeBits
  have hgen : ∀ (ys : List String) (acc : Array Bool) (I : List String),
      Represents tab acc I →
      Represents tab (ys.foldl (fun a x => match tab.toIdx[x]? with | some i => a.setIfInBounds i true | none => a) acc)
        (ys.reverse ++ I) := by
    intro ys
    induction ys with
    | nil => intro acc I h; simpa using h
    | cons y rest ih =>
      intro acc I h
      rw [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      exact ih _ (y :: I) (encodeBits_step hwf h y)
  have h0 : Represents tab (Array.replicate tab.ofIdx.size false) [] := by
    refine ⟨by simp, fun i hi => ?_⟩
    simp
  have hf := hgen xs (Array.replicate tab.ofIdx.size false) [] h0
  rw [List.append_nil] at hf
  exact represents_congr hf (fun z => List.mem_reverse)

theorem bits_eq_implies_same {tab : AtomTable} (hwf : tab.WF) {U : List String}
    (hcov : ∀ x ∈ U, ∃ i, tab.toIdx[x]? = some i)
    {b1 b2 : Array Bool} {I1 I2 : List String}
    (hr1 : Represents tab b1 I1) (hr2 : Represents tab b2 I2)
    (hU1 : Sub I1 U) (hU2 : Sub I2 U) (heq : b1 = b2) :
    Same I1 I2 := by
  subst heq
  obtain ⟨hsz1, hiff1⟩ := hr1
  obtain ⟨_, hiff2⟩ := hr2
  intro x
  constructor
  · intro hx1
    obtain ⟨i, hi⟩ := hcov x (hU1 x hx1)
    obtain ⟨hilt, hix⟩ := Array.getElem?_eq_some_iff.1 ((hwf x i).1 hi)
    have hb : b1[i]'(by omega) = true := (hiff1 i hilt).2 (hix ▸ hx1)
    exact hix ▸ (hiff2 i hilt).1 hb
  · intro hx2
    obtain ⟨i, hi⟩ := hcov x (hU2 x hx2)
    obtain ⟨hilt, hix⟩ := Array.getElem?_eq_some_iff.1 ((hwf x i).1 hi)
    have hb : b1[i]'(by omega) = true := (hiff2 i hilt).2 (hix ▸ hx2)
    exact hix ▸ (hiff1 i hilt).1 hb

/-- Unboxed indexed rule over dense atom IDs `0 .. U - 1`. -/
structure IndexedRule where
  concl : Nat
  pos : Array Nat
  neg : Array Nat

structure IndexedProg where
  tab : AtomTable
  factBits : Array Bool
  rules : Array IndexedRule

def compileRule (tab : AtomTable) (r : Rule) : IndexedRule :=
  { concl := tab.toIdx[r.concl]?.getD 0
    pos := (r.pos.map fun p => tab.toIdx[p]?.getD 0).toArray
    neg := (r.neg.map fun d => tab.toIdx[d]?.getD 0).toArray }

def compileProg (P : Program) (extra : List String) : IndexedProg :=
  let tab := internAll (progAtoms P extra)
  { tab := tab
    factBits := encodeBits tab P.facts
    rules := (P.rules.map (compileRule tab)).toArray }

def firesBits (jBits iBits : Array Bool) (ir : IndexedRule) : Bool :=
  ir.pos.all (fun p => iBits.getD p false) && ir.neg.all (fun d => !jBits.getD d false)

theorem getD_represents {tab : AtomTable} (hwf : tab.WF) {bits : Array Bool} {I : List String}
    (hrep : Represents tab bits I) {x : String} {idx : Nat} (hx : tab.toIdx[x]? = some idx) :
    bits.getD idx false = I.contains x := by
  obtain ⟨hsz, hiff⟩ := hrep
  obtain ⟨hilt, hix⟩ := Array.getElem?_eq_some_iff.1 ((hwf x idx).1 hx)
  have hb : idx < bits.size := by omega
  have hgd : bits.getD idx false = bits[idx]'hb := by simp [Array.getD, hb]
  rw [hgd]
  apply Bool.eq_iff_iff.2
  exact (hiff idx hilt).trans (by rw [hix, List.contains_iff_mem])

theorem all_congr_mem {α : Type} {f g : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.all f = xs.all g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x List.mem_cons_self,
      all_congr_mem xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem firesBits_eq {tab : AtomTable} (hwf : tab.WF)
    {jBits iBits : Array Bool} {J I : List String}
    (hJ : Represents tab jBits J) (hI : Represents tab iBits I)
    {r : Rule}
    (hpos : ∀ p ∈ r.pos, ∃ i, tab.toIdx[p]? = some i)
    (hneg : ∀ d ∈ r.neg, ∃ i, tab.toIdx[d]? = some i) :
    firesBits jBits iBits (compileRule tab r) = fires J I r := by
  unfold firesBits compileRule fires
  rw [← Array.all_toList, ← Array.all_toList]
  simp only [List.all_map]
  have hp : r.pos.all ((fun p => iBits.getD p false) ∘ fun p => tab.toIdx[p]?.getD 0) =
      r.pos.all (fun p => I.contains p) := by
    apply all_congr_mem r.pos
    intro p hpMem
    obtain ⟨idx, hidx⟩ := hpos p hpMem
    simp only [Function.comp_apply, hidx, Option.getD_some]
    exact getD_represents hwf hI hidx
  have hn : r.neg.all ((fun d => !jBits.getD d false) ∘ fun d => tab.toIdx[d]?.getD 0) =
      r.neg.all (fun d => !J.contains d) := by
    apply all_congr_mem r.neg
    intro d hdMem
    obtain ⟨idx, hidx⟩ := hneg d hdMem
    simp only [Function.comp_apply, hidx, Option.getD_some]
    rw [getD_represents hwf hJ hidx]
  rw [hp, hn]

def stepBits (ip : IndexedProg) (jBits iBits : Array Bool) : Array Bool :=
  ip.rules.foldl (fun acc ir =>
    if firesBits jBits iBits ir then acc.setIfInBounds ir.concl true else acc) ip.factBits

theorem rule_atoms_in_progAtoms (P : Program) (extra : List String) {r : Rule} (hr : r ∈ P.rules) :
    r.concl ∈ progAtoms P extra ∧
    (∀ p ∈ r.pos, p ∈ progAtoms P extra) ∧
    (∀ d ∈ r.neg, d ∈ progAtoms P extra) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [progAtoms, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, List.mem_cons_self⟩
  · intro p hp
    simp only [progAtoms, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, List.mem_cons_of_mem _ (List.mem_append_left _ hp)⟩
  · intro d hd
    simp only [progAtoms, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, List.mem_cons_of_mem _ (List.mem_append_right _ hd)⟩

theorem stepBits_represents (P : Program) (extra : List String)
    {jBits iBits : Array Bool} {J I : List String}
    (hJ : Represents (compileProg P extra).tab jBits J)
    (hI : Represents (compileProg P extra).tab iBits I) :
    Represents (compileProg P extra).tab (stepBits (compileProg P extra) jBits iBits) (T P J I) := by
  obtain ⟨hwf, hmem⟩ := internAll_wf (progAtoms P extra)
  have htab : (compileProg P extra).tab = internAll (progAtoms P extra) := rfl
  unfold stepBits
  rw [← Array.foldl_toList]
  have hrEq : (compileProg P extra).rules.toList = P.rules.map (compileRule (compileProg P extra).tab) := by
    simp [compileProg]
  rw [hrEq, List.foldl_map]
  have hfact : Represents (compileProg P extra).tab (compileProg P extra).factBits P.facts :=
    encodeBits_represents (htab ▸ hwf) P.facts
  have hloop : ∀ (rs : List Rule), (∀ r ∈ rs, r ∈ P.rules) →
      ∀ (acc : Array Bool) (L : List String), Represents (compileProg P extra).tab acc L →
        Represents (compileProg P extra).tab
          (rs.foldl (fun a r => if firesBits jBits iBits (compileRule (compileProg P extra).tab r) then
            a.setIfInBounds (compileRule (compileProg P extra).tab r).concl true else a) acc)
          (L ++ (rs.filter (fires J I)).map (·.concl)) := by
    intro rs
    induction rs with
    | nil => intro _ acc L hL; simpa using hL
    | cons r rest ih =>
      intro hrs acc L hL
      have hrP : r ∈ P.rules := hrs r List.mem_cons_self
      have hrestP : ∀ q ∈ rest, q ∈ P.rules := fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      obtain ⟨hrc, hrp, hrn⟩ := rule_atoms_in_progAtoms P extra hrP
      have hfb : firesBits jBits iBits (compileRule (compileProg P extra).tab r) = fires J I r :=
        firesBits_eq (htab ▸ hwf) hJ hI
          (fun p hp => htab ▸ hmem p (hrp p hp))
          (fun d hd => htab ▸ hmem d (hrn d hd))
      simp only [List.foldl_cons, List.filter_cons, hfb]
      by_cases hf : fires J I r = true
      · simp only [hf, ↓reduceIte, List.map_cons]
        obtain ⟨cIdx, hcIdx⟩ := hmem r.concl hrc
        have hcIdx' : (compileProg P extra).tab.toIdx[r.concl]? = some cIdx := htab ▸ hcIdx
        have hcEq : (compileRule (compileProg P extra).tab r).concl = cIdx := by simp [compileRule, hcIdx']
        rw [hcEq]
        have hstep0 := encodeBits_step (htab ▸ hwf) hL r.concl
        rw [hcIdx'] at hstep0
        dsimp only at hstep0
        have hstep1 : Represents (compileProg P extra).tab (acc.setIfInBounds cIdx true) (L ++ [r.concl]) :=
          represents_congr hstep0 (fun z => by simp [or_comm])
        have hrec := ih hrestP (acc.setIfInBounds cIdx true) (L ++ [r.concl]) hstep1
        simpa [List.append_assoc] using hrec
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact ih hrestP acc L hL
  exact hloop P.rules (fun _ h => h) (compileProg P extra).factBits P.facts hfact

def gammaBitsLoop (ip : IndexedProg) (jBits : Array Bool) : Nat → Array Bool → Array Bool
  | 0, cur => cur
  | fuel + 1, cur =>
    let next := stepBits ip jBits cur
    if next == cur then cur
    else gammaBitsLoop ip jBits fuel next

def gammaBits (P : Program) (ip : IndexedProg) (jBits : Array Bool) : Array Bool :=
  gammaBitsLoop ip jBits (bound P) (encodeBits ip.tab (stage P [] 0))

theorem stage_sub_progAtoms (P : Program) (J : List String) :
    ∀ n, Sub (stage P J n) (progAtoms P (stage P [] 0))
  | 0 => fun x hx => by
    have h0 : stage P J 0 = stage P [] 0 := rfl
    rw [h0] at hx
    simp only [progAtoms, List.mem_append]
    exact Or.inl (Or.inl hx)
  | n + 1 => fun x hx => by
    have hU := T_universe P J (stage P J n) x hx
    simp only [atomsOf, List.mem_append, List.mem_map] at hU
    simp only [progAtoms, List.mem_append, List.mem_flatMap]
    rcases hU with hf | ⟨r, hr, hc⟩
    · exact Or.inl (Or.inr hf)
    · exact Or.inr ⟨r, hr, hc ▸ List.mem_cons_self⟩

theorem gammaBits_represents (P : Program) {jBits : Array Bool} {J : List String}
    (hJ : Represents (compileProg P (stage P [] 0)).tab jBits J) :
    Represents (compileProg P (stage P [] 0)).tab (gammaBits P (compileProg P (stage P [] 0)) jBits) (gamma P J) := by
  obtain ⟨hwf, hmem⟩ := internAll_wf (progAtoms P (stage P [] 0))
  have htab : (compileProg P (stage P [] 0)).tab = internAll (progAtoms P (stage P [] 0)) := rfl
  have hloop : ∀ (fuel n : Nat) (cur : Array Bool),
      n + fuel = bound P →
      Represents (compileProg P (stage P [] 0)).tab cur (stage P J n) →
      Represents (compileProg P (stage P [] 0)).tab
        (gammaBitsLoop (compileProg P (stage P [] 0)) jBits fuel cur) (gamma P J) := by
    intro fuel
    induction fuel with
    | zero =>
      intro n cur hsum hcur
      have hn : n = bound P := by omega
      subst hn
      exact hcur
    | succ fuel ih =>
      intro n cur hsum hcur
      unfold gammaBitsLoop
      dsimp only
      have hnext : Represents (compileProg P (stage P [] 0)).tab
          (stepBits (compileProg P (stage P [] 0)) jBits cur) (stage P J (n + 1)) :=
        stepBits_represents P (stage P [] 0) hJ hcur
      by_cases heq : (stepBits (compileProg P (stage P [] 0)) jBits cur == cur) = true
      · rw [ite_eq_left_iff.2 (fun h => absurd heq h)]
        have heq' : stepBits (compileProg P (stage P [] 0)) jBits cur = cur := beq_iff_eq.1 heq
        have hsame : Same (stage P J (n + 1)) (stage P J n) :=
          bits_eq_implies_same (htab ▸ hwf) (fun x hx => htab ▸ hmem x hx) hnext hcur
            (stage_sub_progAtoms P J (n + 1)) (stage_sub_progAtoms P J n) heq'
        exact represents_congr hcur (stage_const_of_same P J hsame)
      · rw [ite_eq_right_iff.2 (fun h => absurd h heq)]
        exact ih (n + 1) _ (by omega) hnext
  have hinit : Represents (compileProg P (stage P [] 0)).tab
      (encodeBits (compileProg P (stage P [] 0)).tab (stage P [] 0)) (stage P J 0) :=
    encodeBits_represents (htab ▸ hwf) (stage P [] 0)
  exact hloop (bound P) 0 _ (by omega) hinit

def materializeT (P : Program) (ip : IndexedProg) (jBits iBits : Array Bool) : List String :=
  P.facts ++ ((P.rules.zip ip.rules.toList).filter fun (_, ir) => firesBits jBits iBits ir).map (·.1.concl)

theorem zip_map_filter_concl {α β : Type} (xs : List α) (f : α → β) (p : β → Bool) (q : α → Bool)
    (h : ∀ x ∈ xs, p (f x) = q x) :
    ((xs.zip (xs.map f)).filter fun (_, b) => p b) = (xs.filter q).map fun x => (x, f x) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x List.mem_cons_self
    have hrest : ∀ y ∈ rest, p (f y) = q y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons, hx, ih hrest]
    cases q x <;> rfl

theorem materializeT_eq (P : Program) (extra : List String)
    {jBits iBits : Array Bool} {J I : List String}
    (hJ : Represents (compileProg P extra).tab jBits J)
    (hI : Represents (compileProg P extra).tab iBits I) :
    materializeT P (compileProg P extra) jBits iBits = T P J I := by
  obtain ⟨hwf, hmem⟩ := internAll_wf (progAtoms P extra)
  have htab : (compileProg P extra).tab = internAll (progAtoms P extra) := rfl
  unfold materializeT T
  congr 1
  have hrEq : (compileProg P extra).rules.toList = P.rules.map (compileRule (compileProg P extra).tab) := by
    simp [compileProg]
  rw [hrEq, zip_map_filter_concl P.rules (compileRule (compileProg P extra).tab) (firesBits jBits iBits) (fires J I)]
  · simp [List.map_map]
  · intro r hr
    obtain ⟨_, hrp, hrn⟩ := rule_atoms_in_progAtoms P extra hr
    exact firesBits_eq (htab ▸ hwf) hJ hI
      (fun p hp => htab ▸ hmem p (hrp p hp))
      (fun d hd => htab ▸ hmem d (hrn d hd))

/-- Fast unboxed execution of `Γ`: compiles `P` once to dense indices, iterates over `Array Bool`
with immediate fixpoint stop, and materializes the canonical `List String` in one linear pass. -/
def gammaExec (P : Program) (J : List String) : List String :=
  let ip := compileProg P (stage P [] 0)
  let jBits := encodeBits ip.tab J
  let gBits := gammaBits P ip jBits
  materializeT P ip jBits gBits

theorem gammaExec_eq (P : Program) (J : List String) :
    gammaExec P J = gamma P J := by
  obtain ⟨hwf, _⟩ := internAll_wf (progAtoms P (stage P [] 0))
  have htab : (compileProg P (stage P [] 0)).tab = internAll (progAtoms P (stage P [] 0)) := rfl
  have hJ : Represents (compileProg P (stage P [] 0)).tab
      (encodeBits (compileProg P (stage P [] 0)).tab J) J :=
    encodeBits_represents (htab ▸ hwf) J
  have hG := gammaBits_represents P hJ
  unfold gammaExec
  rw [materializeT_eq P (stage P [] 0) hJ hG, ← gamma_eq_T_self P J]

def roundsBitsLoop (P : Program) (ip : IndexedProg) : Nat → Array Bool → Array Bool × Array Bool
  | 0, cur =>
    let g1 := gammaBits P ip cur
    (cur, g1)
  | fuel + 1, cur =>
    let g1 := gammaBits P ip cur
    if g1 == cur then (cur, g1)
    else
      let next := gammaBits P ip g1
      if next == cur then (cur, g1)
      else roundsBitsLoop P ip fuel next

/-- Fast unboxed execution of `wf`: interns atoms once in `O(|P| log U)` (`U = |atomsOf P|`),
evaluates alternating `gammaBits` passes over `Array Bool` with early fixpoint stop in
`O(rounds · depth · |P|)` (`O(U² · |P|)` worst-case on deep unstratified chains), and
materializes `(supported, possible)` in a single pass. -/
def wfExec (P : Program) : List String × List String :=
  let ip := compileProg P (stage P [] 0)
  let (tBits, pBits) := roundsBitsLoop P ip (bound P) (encodeBits ip.tab (rounds P 0))
  (materializeT P ip pBits tBits, materializeT P ip tBits pBits)

theorem rounds_sub_progAtoms (P : Program) :
    ∀ k, Sub (rounds P k) (progAtoms P (stage P [] 0))
  | 0 => fun _ hx => by simp [rounds] at hx
  | _ + 1 => stage_sub_progAtoms P _ (bound P)

theorem wfExec_eq (P : Program) :
    wfExec P = wf P := by
  obtain ⟨hwf, hmem⟩ := internAll_wf (progAtoms P (stage P [] 0))
  have htab : (compileProg P (stage P [] 0)).tab = internAll (progAtoms P (stage P [] 0)) := rfl
  have hloop : ∀ (fuel k : Nat) (cur : Array Bool),
      k + fuel = bound P →
      Represents (compileProg P (stage P [] 0)).tab cur (rounds P k) →
      Represents (compileProg P (stage P [] 0)).tab
        (roundsBitsLoop P (compileProg P (stage P [] 0)) fuel cur).1 (wf P).1 ∧
      Represents (compileProg P (stage P [] 0)).tab
        (roundsBitsLoop P (compileProg P (stage P [] 0)) fuel cur).2 (wf P).2 := by
    intro fuel
    induction fuel with
    | zero =>
      intro k cur hsum hcur
      have hk : k = bound P := by omega
      subst hk
      unfold roundsBitsLoop
      exact ⟨hcur, gammaBits_represents P hcur⟩
    | succ fuel ih =>
      intro k cur hsum hcur
      unfold roundsBitsLoop
      dsimp only
      have hg1 : Represents (compileProg P (stage P [] 0)).tab
          (gammaBits P (compileProg P (stage P [] 0)) cur) (gamma P (rounds P k)) :=
        gammaBits_represents P hcur
      by_cases hg : (gammaBits P (compileProg P (stage P [] 0)) cur == cur) = true
      · rw [ite_eq_left_iff.2 (fun h => absurd hg h)]
        dsimp only
        have hgEq : gammaBits P (compileProg P (stage P [] 0)) cur = cur := beq_iff_eq.1 hg
        have hs1 : Same (gamma P (rounds P k)) (rounds P k) :=
          bits_eq_implies_same (htab ▸ hwf) (fun x hx => htab ▸ hmem x hx) hg1 hcur
            (stage_sub_progAtoms P _ (bound P)) (rounds_sub_progAtoms P k) hgEq
        have hsRound : Same (rounds P (k + 1)) (rounds P k) := by
          simp only [rounds, gamma_congr P hs1]
          exact hs1
        have hwf1 : Same (rounds P k) (wf P).1 := rounds_const_of_same P hsRound
        have hwf2 : Same (gamma P (rounds P k)) (wf P).2 := by
          show Same (gamma P (rounds P k)) (gamma P (wf P).1)
          rw [gamma_congr P hwf1]
          exact Same.refl _
        exact ⟨represents_congr hcur hwf1, represents_congr hg1 hwf2⟩
      · rw [ite_eq_right_iff.2 (fun h => absurd h hg)]
        have hnext : Represents (compileProg P (stage P [] 0)).tab
            (gammaBits P (compileProg P (stage P [] 0)) (gammaBits P (compileProg P (stage P [] 0)) cur))
            (rounds P (k + 1)) := gammaBits_represents P hg1
        by_cases hn : (gammaBits P (compileProg P (stage P [] 0))
            (gammaBits P (compileProg P (stage P [] 0)) cur) == cur) = true
        · rw [ite_eq_left_iff.2 (fun h => absurd hn h)]
          dsimp only
          have hnEq := beq_iff_eq.1 hn
          have hsRound : Same (rounds P (k + 1)) (rounds P k) :=
            bits_eq_implies_same (htab ▸ hwf) (fun x hx => htab ▸ hmem x hx) hnext hcur
              (rounds_sub_progAtoms P (k + 1)) (rounds_sub_progAtoms P k) hnEq
          have hwf1 : Same (rounds P k) (wf P).1 := rounds_const_of_same P hsRound
          have hwf2 : Same (gamma P (rounds P k)) (wf P).2 := by
            show Same (gamma P (rounds P k)) (gamma P (wf P).1)
            rw [gamma_congr P hwf1]
            exact Same.refl _
          exact ⟨represents_congr hcur hwf1, represents_congr hg1 hwf2⟩
        · rw [ite_eq_right_iff.2 (fun h => absurd h hn)]
          exact ih (k + 1) _ (by omega) hnext
  have h0 : Represents (compileProg P (stage P [] 0)).tab
      (encodeBits (compileProg P (stage P [] 0)).tab (rounds P 0)) (rounds P 0) :=
    encodeBits_represents (htab ▸ hwf) (rounds P 0)
  obtain ⟨ht, hp⟩ := hloop (bound P) 0 _ (by omega) h0
  unfold wfExec
  dsimp only
  exact Prod.ext
    ((materializeT_eq P (stage P [] 0) hp ht).trans (wf_fst_eq_T P).symm)
    ((materializeT_eq P (stage P [] 0) ht hp).trans (wf_snd_eq_T P).symm)

theorem wfExec_same (P : Program) :
    Same (wfExec P).1 (wf P).1 ∧ Same (wfExec P).2 (wf P).2 := by
  rw [wfExec_eq P]
  exact ⟨Same.refl _, Same.refl _⟩

theorem wfExec_statusIn (P : Program) (x : String) :
    statusIn (wfExec P) x = statusIn (wf P) x := by
  rw [wfExec_eq P]

@[csimp]
theorem gamma_eq_gammaExec : @gamma = @gammaExec := by
  funext P J
  exact (gammaExec_eq P J).symm

@[csimp]
theorem wf_eq_wfExec : @wf = @wfExec := by
  funext P
  exact (wfExec_eq P).symm

/-! ## 5. The base: what was observed, assumed, explained, defeated, proposed -/

/-- An observation: its name (the atom), the line as read, and where it was read. -/
structure Observation where
  name : String
  text : String
  source : String
deriving DecidableEq, Repr

/-- A defeater: the explanation `target` is defeated while `by'` is supported. -/
structure Defeater where
  target : String
  by' : String
deriving DecidableEq, Repr

/-- A proposed action and its justification. -/
structure Action where
  name : String
  because : String
deriving DecidableEq, Repr

structure Base where
  observations : List Observation := []
  /-- the abducibles declared, in order -/
  assumptions : List String := []
  /-- those withdrawn and not assumed again -/
  withdrawn : List String := []
  explanations : List Rule := []
  defeaters : List Defeater := []
  actions : List Action := []
deriving DecidableEq, Repr

/-- The assumptions held now. -/
abbrev Base.held (b : Base) : List String := b.assumptions.filter fun a => !b.withdrawn.contains a

/-- An explanation with the defeaters declared against it. -/
abbrev Base.rule (b : Base) (e : Rule) : Rule :=
  { e with neg := e.neg ++ (b.defeaters.filter (·.target == e.name)).map (·.by') }

/-- **The program a base denotes**: the observations and the assumptions held are its facts; the
explanations, each with its defeaters, its rules. The actions are not in it. -/
abbrev Base.program (b : Base) : Program :=
  { facts := b.observations.map (·.name) ++ b.held, rules := b.explanations.map b.rule }

/-- **The judgment of a base, from scratch.** -/
abbrev judge (b : Base) : List String × List String := wf b.program

@[expose] def status (b : Base) (x : String) : Status := statusIn (judge b) x

/-- A base changes by an event. -/
inductive Event where
  | observe (o : Observation)
  | assume (a : String)
  | withdraw (a : String)
  | explain (r : Rule)
  | defeat (d : Defeater)
  | propose (act : Action)
deriving DecidableEq, Repr

/-- The atoms a base names. -/
def Base.atoms (b : Base) : List String :=
  (b.observations.map (·.name) ++ b.assumptions ++ b.explanations.flatMap (fun e => e.concl :: e.pos ++ e.neg) ++
    b.defeaters.map (·.by')).eraseDups

@[expose] def Base.step (b : Base) : Event → Except String Base
  | .observe o =>
    if b.observations.any (·.name == o.name) then .error ("refused: " ++ o.name ++ " is observed already")
    else if b.assumptions.contains o.name then .error ("refused: " ++ o.name ++ " is an assumption, not an observation")
    else .ok { b with observations := b.observations ++ [o] }
  | .assume a =>
    if b.observations.any (·.name == a) then .error ("refused: " ++ a ++ " is observed, not assumed")
    else if b.held.contains a then .error ("refused: " ++ a ++ " is assumed already")
    else .ok { b with assumptions := if b.assumptions.contains a then b.assumptions else b.assumptions ++ [a],
                      withdrawn := b.withdrawn.filter (· != a) }
  | .withdraw a =>
    if !b.held.contains a then .error ("refused: " ++ a ++ " is not an assumption held")
    else .ok { b with withdrawn := b.withdrawn ++ [a] }
  | .explain r =>
    if b.explanations.any (·.name == r.name) then .error ("refused: an explanation named " ++ r.name ++ " exists")
    else .ok { b with explanations := b.explanations ++ [r] }
  | .defeat d =>
    if !b.explanations.any (·.name == d.target) then .error ("refused: no explanation named " ++ d.target)
    else if b.defeaters.contains d then .error ("refused: " ++ d.by' ++ " defeats " ++ d.target ++ " already")
    else .ok { b with defeaters := b.defeaters ++ [d] }
  | .propose act =>
    if b.actions.any (·.name == act.name) then .error ("refused: an action named " ++ act.name ++ " was proposed")
    else .ok { b with actions := b.actions ++ [act] }

/-! ## 6. Defeat only by evidence -/

/-- **The judgment is a function of the evidence and the theory**: two bases with the same
observations (by name), the same assumptions held, the same explanations and the same defeaters have
the same judgment, whatever actions either proposed and whatever either withdrew and assumed again
on the way. So no action defeats anything, and, for a fixed theory, a status moves only with an
observation or an assumption. -/
theorem defeat_only_by_evidence (b b' : Base)
    (hobs : b.observations.map (·.name) = b'.observations.map (·.name)) (hheld : b.held = b'.held)
    (hexp : b.explanations = b'.explanations) (hdef : b.defeaters = b'.defeaters) :
    status b = status b' := by
  have hr : b.rule = b'.rule := by funext e; simp only [Base.rule, hdef]
  have : b.program = b'.program := by
    simp only [Base.program, hr, hobs, hheld, hexp]
  funext x
  simp only [status, judge, this]

/-- Proposing an action changes no status. -/
theorem propose_keeps_status {b b' : Base} {act : Action} (h : b.step (.propose act) = .ok b') :
    status b' = status b := by
  simp only [Base.step] at h
  split at h
  · cases h
  · cases h
    exact defeat_only_by_evidence _ _ rfl rfl rfl rfl

/-! ## 7. No conclusion from cycles; one support suffices -/

/-- **An unsupported cycle cannot create a conclusion.** If no atom of `S` is observed or assumed,
and every explanation of an atom of `S` has a premise in `S` (each rests, through the others, on
itself), then every atom of `S` is unsupported: not supported, and not even undefined. In the
well-founded model this is an unfounded set, which is false. -/
theorem no_conclusion_from_cycles (b : Base) (S : List String)
    (hfact : ∀ x ∈ S, x ∉ b.program.facts)
    (hcyc : ∀ r ∈ b.program.rules, r.concl ∈ S → ∃ p ∈ r.pos, p ∈ S) :
    ∀ x ∈ S, status b x = .unsupported := by
  -- no stage of any `Γ` reaches `S`
  have hst : ∀ J n, ∀ x ∈ S, x ∉ stage b.program J n := by
    intro J n
    induction n with
    | zero => intro x _ h; simp [stage] at h
    | succ n ih =>
      intro x hx h
      rcases mem_T.1 h with hf | ⟨r, hr, hfire, hc⟩
      · exact hfact x hx hf
      · obtain ⟨p, hp, hpS⟩ := hcyc r hr (hc ▸ hx)
        exact ih p hpS ((fires_iff.1 hfire).1 p hp)
  intro x hx
  have h2 : x ∉ (judge b).2 := hst _ _ x hx
  have h1 : x ∉ (judge b).1 := fun h => h2 (supported_possible _ x h)
  simp [status, statusIn, h1, h2]

theorem status_supported_iff (b : Base) (x : String) : status b x = .supported ↔ x ∈ (judge b).1 := by
  unfold status statusIn
  by_cases h : x ∈ (judge b).1
  · simp [h]
  · simp only [List.contains_iff_mem, h, ite_false]
    split <;> simp

theorem status_unsupported_iff (b : Base) (x : String) :
    status b x = .unsupported ↔ x ∉ (judge b).2 := by
  unfold status statusIn
  by_cases h : x ∈ (judge b).2
  · have : (x ∈ (judge b).1) ∨ ¬ x ∈ (judge b).1 := Classical.em _
    rcases this with h1 | h1 <;> simp [h, h1]
  · have h1 : x ∉ (judge b).1 := fun h1 => h (supported_possible _ x h1)
    simp [h, h1]

/-- **A conclusion is supported exactly when one of its explanations stands**: it is observed or
assumed, or some explanation of it has every premise supported and every defeater unsupported. The
lifetime of an assertion with several supporters: it stands while any one does. -/
theorem supported_iff (b : Base) (x : String) :
    status b x = .supported ↔ x ∈ b.program.facts ∨
      ∃ r ∈ b.program.rules, r.concl = x ∧ (∀ p ∈ r.pos, status b p = .supported) ∧
        (∀ d ∈ r.neg, status b d = .unsupported) := by
  simp only [status_supported_iff, status_unsupported_iff, judge]
  have hfix := rounds_fix b.program
  rw [← hfix x, mem_gamma]
  constructor
  · rintro (h | ⟨r, hr, hc, hp, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hc, fun p h => (hfix p).1 (hp p h), hn⟩
  · rintro (h | ⟨r, hr, hc, hp, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hc, fun p h => (hfix p).2 (hp p h), hn⟩

/-! ## 8. Locality: what does not depend on an atom does not move with it -/

/-- `d` is closed under dependence in `P`: every premise and defeater of a rule concluding an atom
of `d` is in `d`. -/
def Closed (P : Program) (d : String → Bool) : Prop :=
  ∀ r ∈ P.rules, d r.concl = true → ∀ p ∈ r.pos ++ r.neg, d p = true

/-- Two programs agree on `d`: the same facts there, the same rules concluding there. -/
def AgreeOn (d : String → Bool) (P Q : Program) : Prop :=
  (∀ x, d x = true → (x ∈ P.facts ↔ x ∈ Q.facts)) ∧ (∀ r : Rule, d r.concl = true → (r ∈ P.rules ↔ r ∈ Q.rules))

/-- Two sets with the same members in `d`. -/
def SameOn (d : String → Bool) (I I' : List String) : Prop := ∀ x, d x = true → (x ∈ I ↔ x ∈ I')

theorem fires_local {d : String → Bool} {J J' I I' : List String} (hJ : SameOn d J J') (hI : SameOn d I I')
    {r : Rule} (hr : ∀ p ∈ r.pos ++ r.neg, d p = true) : fires J I r = fires J' I' r := by
  have h1 : fires J I r = true ↔ fires J' I' r = true := by
    rw [fires_iff, fires_iff]
    constructor
    · rintro ⟨hp, hn⟩
      exact ⟨fun p h => (hI p (hr p (List.mem_append_left _ h))).1 (hp p h),
        fun q h hq => hn q h ((hJ q (hr q (List.mem_append_right _ h))).2 hq)⟩
    · rintro ⟨hp, hn⟩
      exact ⟨fun p h => (hI p (hr p (List.mem_append_left _ h))).2 (hp p h),
        fun q h hq => hn q h ((hJ q (hr q (List.mem_append_right _ h))).1 hq)⟩
  cases h : fires J I r <;> cases h' : fires J' I' r <;> simp_all

theorem T_local {P Q : Program} {d : String → Bool} (hc : Closed P d) (ha : AgreeOn d P Q)
    {J J' I I' : List String} (hJ : SameOn d J J') (hI : SameOn d I I') : SameOn d (T P J I) (T Q J' I') := by
  intro x hx
  rw [mem_T, mem_T, ha.1 x hx]
  constructor
  · rintro (h | ⟨r, hr, hf, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, (ha.2 r hx).1 hr, (fires_local hJ hI (hc r hr hx)) ▸ hf, rfl⟩
  · rintro (h | ⟨r, hr, hf, rfl⟩)
    · exact Or.inl h
    · have hr' := (ha.2 r hx).2 hr
      exact Or.inr ⟨r, hr', (fires_local hJ hI (hc r hr' hx)).symm ▸ hf, rfl⟩

theorem stage_local {P Q : Program} {d : String → Bool} (hc : Closed P d) (ha : AgreeOn d P Q)
    {J J' : List String} (hJ : SameOn d J J') : ∀ n, SameOn d (stage P J n) (stage Q J' n)
  | 0 => fun _ _ => Iff.rfl
  | n + 1 => T_local hc ha hJ (stage_local hc ha hJ n)

theorem gamma_local {P Q : Program} {d : String → Bool} (hc : Closed P d) (ha : AgreeOn d P Q)
    {J J' : List String} (hJ : SameOn d J J') : SameOn d (gamma P J) (gamma Q J') := by
  intro x hx
  let m := (atomsOf P).length + (atomsOf Q).length
  rw [← stage_gamma P J (m := m) (by omega) x, ← stage_gamma Q J' (m := m) (by omega) x]
  exact stage_local hc ha hJ m x hx

theorem rounds_local {P Q : Program} {d : String → Bool} (hc : Closed P d) (ha : AgreeOn d P Q) :
    ∀ k, SameOn d (rounds P k) (rounds Q k)
  | 0 => fun _ _ => Iff.rfl
  | k + 1 => gamma_local hc ha (gamma_local hc ha (rounds_local hc ha k))

/-- **The well-founded model is local**: on a set closed under dependence, two programs that agree
there have the same supported and the same possible atoms there. -/
theorem wf_local {P Q : Program} {d : String → Bool} (hc : Closed P d) (ha : AgreeOn d P Q) :
    SameOn d (wf P).1 (wf Q).1 ∧ SameOn d (wf P).2 (wf Q).2 := by
  have h1 : SameOn d (wf P).1 (wf Q).1 := by
    intro x hx
    let m := (atomsOf P).length + (atomsOf Q).length
    rw [← rounds_wf P (m := m) (by omega) x, ← rounds_wf Q (m := m) (by omega) x]
    exact rounds_local hc ha m x hx
  exact ⟨h1, gamma_local hc ha h1⟩

theorem statusIn_local {d : String → Bool} {j j' : List String × List String}
    (h1 : SameOn d j.1 j'.1) (h2 : SameOn d j.2 j'.2) {x : String} (hx : d x = true) :
    statusIn j x = statusIn j' x := by
  unfold statusIn
  have e1 : j.1.contains x = j'.1.contains x := by
    have := h1 x hx; cases a : j.1.contains x <;> cases b : j'.1.contains x <;> simp_all
  have e2 : j.2.contains x = j'.2.contains x := by
    have := h2 x hx; cases a : j.2.contains x <;> cases b : j'.2.contains x <;> simp_all
  rw [e1, e2]

/-- The atom an observation or an assumption is about. -/
def Event.evidence : Event → Option String
  | .observe o => some o.name
  | .assume a => some a
  | .withdraw a => some a
  | _ => none

/-- **Evidence moves only the facts it names**: an observation or an assumption changes no rule and
no fact but its own atom. -/
theorem evidence_step {b b' : Base} {e : Event} {a : String} (he : e.evidence = some a)
    (h : b.step e = .ok b') :
    b'.program.rules = b.program.rules ∧ ∀ x, x ≠ a → (x ∈ b.program.facts ↔ x ∈ b'.program.facts) := by
  cases e with
  | observe o =>
    simp only [Event.evidence, Option.some.injEq] at he
    subst he
    simp only [Base.step] at h
    split at h; · cases h
    split at h; · cases h
    cases h
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [Base.held, List.map_append, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | ⟨o', rfl, rfl⟩) | h)
      · exact Or.inl h
      · exact absurd rfl hx
      · exact Or.inr h
  | assume a' =>
    simp only [Event.evidence, Option.some.injEq] at he
    subst he
    simp only [Base.step] at h
    split at h; · cases h
    split at h; · cases h
    cases h
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [Base.held, List.mem_append, List.mem_filter, List.contains_iff_mem]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨?_, ?_⟩
        · split <;> simp_all
        · simp_all
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨?_, ?_⟩
        · split at h1 <;> simp_all
        · simp_all
  | withdraw a' =>
    simp only [Event.evidence, Option.some.injEq] at he
    subst he
    simp only [Base.step] at h
    split at h; · cases h
    cases h
    refine ⟨rfl, fun x hx => ?_⟩
    simp_all
  | explain _ => simp [Event.evidence] at he
  | defeat _ => simp [Event.evidence] at he
  | propose _ => simp [Event.evidence] at he

/-- **Evidence is local**: an observation or an assumption about `a` leaves the status of every atom
of a set closed under dependence that does not contain `a`; a status moves only inside the cone of
the atom the evidence is about. -/
theorem evidence_local {b b' : Base} {e : Event} {a : String} (he : e.evidence = some a)
    (h : b.step e = .ok b') {d : String → Bool} (hd : d a = false) (hc : Closed b.program d) :
    ∀ x, d x = true → status b' x = status b x := by
  obtain ⟨hr, hf⟩ := evidence_step he h
  have ha : AgreeOn d b.program b'.program :=
    ⟨fun x hx => hf x (fun hxa => by subst hxa; simp_all), fun r _ => by rw [hr]⟩
  obtain ⟨h1, h2⟩ := wf_local hc ha
  intro x hx
  exact (statusIn_local h1 h2 hx).symm

/-! ## 9. The state: the base and the judgment as last computed; incremental equals from scratch -/

/-- Iterate. -/
def iter (f : List String → List String) : Nat → List String → List String
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- Iterate with immediate early exit once `f x == x`. -/
def iterFix (f : List String → List String) : Nat → List String → List String
  | 0, x => x
  | n + 1, x =>
    let x' := f x
    if x' == x then x else iterFix f n x'

theorem iter_of_fix (f : List String → List String) {x : List String} (hx : f x = x) :
    ∀ n, iter f n x = x
  | 0 => rfl
  | n + 1 => by simp only [iter, hx]; exact iter_of_fix f hx n

theorem iterFix_eq_iter (f : List String → List String) :
    ∀ (n : Nat) (x : List String), iterFix f n x = iter f n x
  | 0, _ => rfl
  | n + 1, x => by
    unfold iterFix iter
    by_cases h : (f x == x) = true
    · simp only [h, ↓reduceIte]
      have hx : f x = x := beq_iff_eq.1 h
      rw [hx, iter_of_fix f hx n]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact iterFix_eq_iter f n (f x)

@[csimp]
theorem iter_eq_iterFix : @iter = @iterFix := by
  funext f n x
  exact (iterFix_eq_iter f n x).symm

/-- **The cone of `a`**: the atoms that depend on it (through a premise or a defeater), by bounded
iteration; `upClosedB` checks it before it is used. -/
def cone (P : Program) (a : String) : List String :=
  iter (fun C => (C ++ (P.rules.filter fun r => (r.pos ++ r.neg).any C.contains).map (·.concl)).eraseDups)
    (P.rules.length + 1) [a]

/-- **What a set depends on**, by bounded iteration; `closedB` checks it before it is used. -/
def closure (P : Program) (C : List String) : List String :=
  iter (fun D => (D ++ (P.rules.filter fun r => D.contains r.concl).flatMap fun r => r.pos ++ r.neg).eraseDups)
    (P.rules.length + 1) C

/-- No rule concluding outside `C` reads inside it. -/
def upClosedB (P : Program) (C : List String) : Bool :=
  P.rules.all fun r => C.contains r.concl || !(r.pos ++ r.neg).any C.contains

/-- Every rule concluding inside `D` reads only inside it. -/
def closedB (P : Program) (D : List String) : Bool :=
  P.rules.all fun r => !D.contains r.concl || (r.pos ++ r.neg).all D.contains

def Program.restrict (P : Program) (D : List String) : Program :=
  { facts := P.facts.filter D.contains, rules := P.rules.filter fun r => D.contains r.concl }

theorem closed_of_upClosedB {P : Program} {C : List String} (h : upClosedB P C = true) :
    Closed P (fun x => !C.contains x) := by
  intro r hr hc p hp
  have := List.all_eq_true.1 h r hr
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc
  simp only [hc, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at this
  simpa using this p hp

theorem closed_of_closedB {P : Program} {D : List String} (h : closedB P D = true) :
    Closed P (fun x => D.contains x) := by
  intro r hr hc p hp
  have := List.all_eq_true.1 h r hr
  simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  exact this p hp

theorem agree_restrict (P : Program) (D : List String) : AgreeOn (fun x => D.contains x) P (P.restrict D) := by
  refine ⟨fun x hx => ?_, fun r hr => ?_⟩
  · have hx' : x ∈ D := by simpa using hx
    simp [Program.restrict, List.mem_filter, hx']
  · simp only [Program.restrict, List.mem_filter, hr, and_true]

/-- The checks that let a cone be recomputed alone. -/
def coneOk (P : Program) (a : String) (C D : List String) : Bool :=
  C.contains a && upClosedB P C && C.all D.contains && closedB P D

/-- **Recompute the cone of `a` only**: every status outside the cone is kept; the cone's statuses
are read off the well-founded model of the program restricted to what the cone depends on. Where a
check fails, everything is recomputed. -/
def localUpdate (kept : List String × List String) (P : Program) (a : String) : List String × List String :=
  let C := cone P a
  let D := closure P C
  if coneOk P a C D then
    let sub := wfExec (P.restrict D)
    (kept.1.filter (fun x => !C.contains x) ++ sub.1.filter C.contains,
     kept.2.filter (fun x => !C.contains x) ++ sub.2.filter C.contains)
  else wfExec P

/-- How many atoms a step judged anew: the cone's closure, or all of them. -/
def localWork (P : Program) (a : String) : Nat :=
  let C := cone P a
  let D := closure P C
  if coneOk P a C D then D.length else (atomsOf P).eraseDups.length + 1

structure State where
  base : Base := {}
  /-- the judgment as last computed: the supported atoms and the possible ones -/
  kept : List String × List String := ([], [])
deriving DecidableEq, Repr

/-- A status as the state keeps it. -/
@[expose] def State.status (s : State) (x : String) : Status := statusIn s.kept x

/-- The kept judgment is the base's, from scratch. -/
abbrev State.Consistent (s : State) : Prop := Same s.kept.1 (judge s.base).1 ∧ Same s.kept.2 (judge s.base).2

def State.update (s : State) (e : Event) (b' : Base) : List String × List String :=
  match e with
  | .propose _ => s.kept
  | .observe o => localUpdate s.kept b'.program o.name
  | .assume a => localUpdate s.kept b'.program a
  | .withdraw a => localUpdate s.kept b'.program a
  | .explain _ => wfExec b'.program
  | .defeat _ => wfExec b'.program

/-- **A step**: the base by the event, and the judgment updated (not recomputed, where it need not be). -/
@[expose] def State.step (s : State) (e : Event) : Except String State :=
  match s.base.step e with
  | .error err => .error err
  | .ok b' => .ok { base := b', kept := s.update e b' }

/-- How many atoms a step judged anew, and of how many, at the base after it. -/
def workOf (b' : Base) (e : Event) : Nat × Nat :=
  let total := b'.atoms.length
  match e with
  | .propose _ => (0, total)
  | .observe o => (localWork b'.program o.name, total)
  | .assume a => (localWork b'.program a, total)
  | .withdraw a => (localWork b'.program a, total)
  | _ => (total, total)

theorem State.status_eq {s : State} (hs : s.Consistent) (x : String) : s.status x = Obend.Reasons.status s.base x :=
  statusIn_local (d := fun _ => true) (fun y _ => hs.1 y) (fun y _ => hs.2 y) rfl

theorem init_consistent : ({} : State).Consistent := by
  have : judge ({} : Base) = ([], []) := rfl
  simp only [State.Consistent, this]
  exact ⟨Same.refl _, Same.refl _⟩

theorem localUpdate_consistent {s : State} (hs : s.Consistent) {b' : Base} {a : String}
    (hr : b'.program.rules = s.base.program.rules)
    (hf : ∀ x, x ≠ a → (x ∈ s.base.program.facts ↔ x ∈ b'.program.facts)) :
    State.Consistent { base := b', kept := localUpdate s.kept b'.program a } := by
  simp only [State.Consistent, localUpdate, wfExec_eq]
  split
  · rename_i hok
    simp only [coneOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hca, hup⟩, hCD⟩, hcl⟩ := hok
    -- outside the cone: the old judgment is the new one
    have hcO := closed_of_upClosedB hup
    have hcO' : Closed s.base.program (fun x => !(cone b'.program a).contains x) := by
      intro r hr' hc p hp; exact hcO r (hr ▸ hr') hc p hp
    have haO : AgreeOn (fun x => !(cone b'.program a).contains x) s.base.program b'.program := by
      refine ⟨fun x hx => hf x ?_, fun r _ => by rw [hr]⟩
      rintro rfl; simp_all
    obtain ⟨o1, o2⟩ := wf_local hcO' haO
    -- inside: the restricted program's judgment is the whole one's
    have hcI := closed_of_closedB hcl
    obtain ⟨i1, i2⟩ := wf_local hcI (agree_restrict b'.program (closure b'.program (cone b'.program a)))
    have hin : ∀ x, (cone b'.program a).contains x = true →
        (closure b'.program (cone b'.program a)).contains x = true := fun x hx =>
      List.all_eq_true.1 hCD x (by simpa using hx)
    constructor
    · intro x
      simp only [List.mem_append, List.mem_filter]
      by_cases hx : (cone b'.program a).contains x = true
      · simp only [hx, Bool.not_true, Bool.false_eq_true, and_false, and_true, false_or]
        exact ((i1 x (hin x hx)).symm)
      · simp only [Bool.not_eq_true] at hx
        simp only [hx, Bool.not_false, and_true, Bool.false_eq_true, and_false, or_false]
        exact (hs.1 x).trans (o1 x (by simpa using hx))
    · intro x
      simp only [List.mem_append, List.mem_filter]
      by_cases hx : (cone b'.program a).contains x = true
      · simp only [hx, Bool.not_true, Bool.false_eq_true, and_false, and_true, false_or]
        exact ((i2 x (hin x hx)).symm)
      · simp only [Bool.not_eq_true] at hx
        simp only [hx, Bool.not_false, and_true, Bool.false_eq_true, and_false, or_false]
        exact (hs.2 x).trans (o2 x (by simpa using hx))
  · exact ⟨Same.refl _, Same.refl _⟩

/-- A step keeps the kept judgment the base's. -/
theorem step_consistent {s s' : State} {e : Event} (hs : s.Consistent) (h : s.step e = .ok s') :
    s'.Consistent := by
  simp only [State.step] at h
  split at h
  · cases h
  · rename_i b' hb
    cases h
    cases e with
    | propose act =>
      have : judge b' = judge s.base := by
        simp only [judge, Base.program]
        simp only [Base.step] at hb; split at hb <;> cases hb; rfl
      simp only [State.Consistent, State.update, this]; exact hs
    | observe o =>
      obtain ⟨hr, hf⟩ := evidence_step (e := .observe o) rfl hb
      exact localUpdate_consistent hs hr hf
    | assume a =>
      obtain ⟨hr, hf⟩ := evidence_step (e := .assume a) rfl hb
      exact localUpdate_consistent hs hr hf
    | withdraw a =>
      obtain ⟨hr, hf⟩ := evidence_step (e := .withdraw a) rfl hb
      exact localUpdate_consistent hs hr hf
    | explain _ => simp only [State.Consistent, State.update, wfExec_eq, judge]; exact ⟨Same.refl _, Same.refl _⟩
    | defeat _ => simp only [State.Consistent, State.update, wfExec_eq, judge]; exact ⟨Same.refl _, Same.refl _⟩

/-- **Incremental equals from scratch.** After any step from a state whose kept judgment is its
base's, the kept judgment is the new base's well-founded model: an action kept it, an observation or
an assumption recomputed only its cone, a new explanation or defeater recomputed all, and in every
case it is what recomputing from the current observations and assumptions gives. -/
theorem from_scratch_consistent {s s' : State} {e : Event} (hs : s.Consistent) (h : s.step e = .ok s') :
    ∀ x, s'.status x = status s'.base x :=
  State.status_eq (step_consistent hs h)

/-- The state after a run of events from the empty one. -/
def State.run (es : List Event) : Except String State := es.foldlM State.step {}

theorem foldl_consistent : ∀ (es : List Event) {s s' : State}, s.Consistent →
    es.foldlM State.step s = .ok s' → s'.Consistent
  | [], _, _, hs, h => by cases h; exact hs
  | e :: es, s, s', hs, h => by
    simp only [List.foldlM_cons] at h
    cases hstep : s.step e with
    | error err => rw [hstep] at h; cases h
    | ok s1 =>
      rw [hstep] at h
      exact foldl_consistent es (step_consistent hs hstep) h

/-- **Every state a run reaches keeps the base's judgment**: from the empty state, whatever was
observed, assumed, withdrawn, explained, defeated and proposed, in whatever order, the judgment kept
is the well-founded model of the base. -/
theorem run_consistent {es : List Event} {s : State} (h : State.run es = .ok s) :
    ∀ x, s.status x = status s.base x :=
  State.status_eq (foldl_consistent es init_consistent h)

/-- **Proposing an action changes no status the state keeps.** -/
theorem propose_keeps_judgment {s s' : State} {act : Action} (h : s.step (.propose act) = .ok s') :
    s'.kept = s.kept := by
  simp only [State.step] at h
  split at h
  · cases h
  · cases h; rfl

/-- **Withdrawing one of two supports leaves the conclusion supported.** If `x` has an explanation
`r` that stands now (every premise supported, every defeater unsupported) and whose premises and
defeaters lie in a set closed under dependence that does not contain the assumption `a`, then `x`
is supported in the judgment the state keeps before withdrawing `a` and in the one it keeps after;
the step replaces the one by the other, so there is no state in which `x` is absent, whatever other
support of `x` rested on `a`. -/
theorem survives_one_support {s s' : State} {a x : String} {r : Rule} (hs : s.Consistent)
    (h : s.step (.withdraw a) = .ok s') (hr : r ∈ s.base.program.rules) (hc : r.concl = x)
    (hpos : ∀ p ∈ r.pos, s.status p = .supported) (hneg : ∀ d ∈ r.neg, s.status d = .unsupported)
    (d : String → Bool) (hd : d a = false) (hcl : Closed s.base.program d)
    (hin : ∀ p ∈ r.pos ++ r.neg, d p = true) :
    s.status x = .supported ∧ s'.status x = .supported := by
  have hstep := h
  simp only [State.step] at h
  split at h
  · cases h
  · rename_i b' hb
    cases h
    have hloc := evidence_local (e := .withdraw a) rfl hb hd hcl
    have hrules := (evidence_step (e := .withdraw a) rfl hb).1
    refine ⟨?_, ?_⟩
    · rw [State.status_eq hs, supported_iff]
      exact Or.inr ⟨r, hr, hc, fun p hp => (State.status_eq hs p) ▸ hpos p hp,
        fun q hq => (State.status_eq hs q) ▸ hneg q hq⟩
    · rw [from_scratch_consistent hs hstep, supported_iff]
      refine Or.inr ⟨r, hrules ▸ hr, hc, fun p hp => ?_, fun q hq => ?_⟩
      · rw [hloc p (hin p (List.mem_append_left _ hp)), ← State.status_eq hs]; exact hpos p hp
      · rw [hloc q (hin q (List.mem_append_right _ hq)), ← State.status_eq hs]; exact hneg q hq

/-! ## 10. Actions need support now -/

/-- The explanations of `x`, with their defeaters. -/
abbrev Base.rulesFor (b : Base) (x : String) : List Rule := b.program.rules.filter (·.concl == x)

/-- **Why `x` is not supported now**, said by name: withdrawn, never supported, or, for each of its
explanations, the premise that is not supported (and the cycle it rests on, if it rests on `x`) or
the defeater that is not unsupported. -/
@[expose] def whyNot (s : State) (x : String) : List String :=
  let st := s.status
  let b := s.base
  if b.withdrawn.contains x && !b.held.contains x then [x ++ " was withdrawn"]
  else if (b.rulesFor x).isEmpty then ["nothing explains " ++ x]
  else (b.rulesFor x).filterMap fun r =>
    match r.pos.find? (st · != .supported) with
    | some p =>
      let tail := if (closure b.program [p]).contains x then "; it rests on " ++ x ++ " itself, an unfounded cycle"
        else if b.withdrawn.contains p && !b.held.contains p then ", withdrawn" else ""
      some (r.name ++ " lacks " ++ p ++ " (" ++ (st p).text ++ tail ++ ")")
    | none =>
      match r.neg.find? (st · != .unsupported) with
      | some q => some (r.name ++ (if st q == .supported then " is defeated by " else " is contested by ") ++
          q ++ " (" ++ (st q).text ++ ")")
      | none => none

/-- **Admit a justification**: only while it is supported in the judgment kept now. -/
def State.justify (s : State) (because : String) : Except String Unit :=
  if s.status because == .supported then .ok ()
  else .error ("its justification " ++ because ++ " is " ++ (s.status because).text ++ " now: " ++
    "; ".intercalate (whyNot s because))

/-- **Admit a proposed action by name.** -/
def State.admit (s : State) (name : String) : Except String Action :=
  match s.base.actions.find? (·.name == name) with
  | none => .error ("refused: no action named " ++ name ++ " was proposed")
  | some act =>
    match s.justify act.because with
    | .ok () => .ok act
    | .error e => .error ("refused: " ++ name ++ " is not admissible: " ++ e)

theorem justify_ok_iff (s : State) (because : String) :
    s.justify because = .ok () ↔ s.status because = .supported := by
  unfold State.justify
  by_cases h : s.status because = .supported <;> simp [h]

/-- **An action is admitted only when its justification is supported now**: in the judgment the
state keeps, which is the current base's (`from_scratch_consistent`). -/
theorem action_needs_support {s : State} (hs : s.Consistent) {name : String} {act : Action}
    (h : s.admit name = .ok act) :
    act ∈ s.base.actions ∧ act.name = name ∧ status s.base act.because = .supported := by
  unfold State.admit at h
  split at h
  · cases h
  · rename_i act' hfind
    split at h
    · rename_i hj
      cases h
      have hm := List.mem_of_find?_eq_some hfind
      have hn := List.find?_some hfind
      refine ⟨hm, by simpa using hn, ?_⟩
      rw [← State.status_eq hs]
      exact (justify_ok_iff s _).1 hj
    · cases h

/-! ## 11. On the wire -/

open Lean (Json toJson)

def strs (xs : List String) : Json := Json.arr (xs.map Json.str).toArray

def strsOf (j : Json) : Except String (List String) := do (← j.getArr?).toList.mapM fun e => e.getStr?

def ruleJson (r : Rule) : Json :=
  Json.mkObj [("name", r.name), ("concl", r.concl), ("pos", strs r.pos), ("neg", strs r.neg)]

def ruleOf (j : Json) : Except String Rule := do
  return ⟨← j.getObjValAs? String "name", ← j.getObjValAs? String "concl", ← strsOf (← j.getObjVal? "pos"),
    ← strsOf (← j.getObjVal? "neg")⟩

def eventJson : Event → Json
  | .observe o => Json.mkObj [("event", "observe"), ("name", o.name), ("text", o.text), ("source", o.source)]
  | .assume a => Json.mkObj [("event", "assume"), ("name", a)]
  | .withdraw a => Json.mkObj [("event", "withdraw"), ("name", a)]
  | .explain r => Json.mkObj [("event", "explain"), ("rule", ruleJson r)]
  | .defeat d => Json.mkObj [("event", "defeat"), ("target", d.target), ("by", d.by')]
  | .propose a => Json.mkObj [("event", "propose"), ("name", a.name), ("because", a.because)]

def eventOf (j : Json) : Except String Event := do
  match ← j.getObjValAs? String "event" with
  | "observe" => return .observe ⟨← j.getObjValAs? String "name", ← j.getObjValAs? String "text",
      ← j.getObjValAs? String "source"⟩
  | "assume" => return .assume (← j.getObjValAs? String "name")
  | "withdraw" => return .withdraw (← j.getObjValAs? String "name")
  | "explain" => return .explain (← ruleOf (← j.getObjVal? "rule"))
  | "defeat" => return .defeat ⟨← j.getObjValAs? String "target", ← j.getObjValAs? String "by"⟩
  | "propose" => return .propose ⟨← j.getObjValAs? String "name", ← j.getObjValAs? String "because"⟩
  | t => throw ("not a reasons event: " ++ t)

def stateJson (s : State) : Json :=
  Json.mkObj [("observations", Json.arr (s.base.observations.map fun o =>
      Json.mkObj [("name", o.name), ("text", o.text), ("source", o.source)]).toArray),
    ("assumptions", strs s.base.assumptions), ("withdrawn", strs s.base.withdrawn),
    ("explanations", Json.arr (s.base.explanations.map ruleJson).toArray),
    ("defeaters", Json.arr (s.base.defeaters.map fun d => Json.mkObj [("target", d.target), ("by", d.by')]).toArray),
    ("actions", Json.arr (s.base.actions.map fun a => Json.mkObj [("name", a.name), ("because", a.because)]).toArray),
    ("supported", strs s.kept.1), ("possible", strs s.kept.2)]

def stateOf (j : Json) : Except String State := do
  let obs ← (← j.getObjValAs? (Array Json) "observations").toList.mapM fun o => do
    return (⟨← o.getObjValAs? String "name", ← o.getObjValAs? String "text", ← o.getObjValAs? String "source"⟩ : Observation)
  let exps ← (← j.getObjValAs? (Array Json) "explanations").toList.mapM ruleOf
  let defs ← (← j.getObjValAs? (Array Json) "defeaters").toList.mapM fun d => do
    return (⟨← d.getObjValAs? String "target", ← d.getObjValAs? String "by"⟩ : Defeater)
  let acts ← (← j.getObjValAs? (Array Json) "actions").toList.mapM fun a => do
    return (⟨← a.getObjValAs? String "name", ← a.getObjValAs? String "because"⟩ : Action)
  return { base := { observations := obs, assumptions := ← strsOf (← j.getObjVal? "assumptions"),
                     withdrawn := ← strsOf (← j.getObjVal? "withdrawn"), explanations := exps,
                     defeaters := defs, actions := acts },
           kept := (← strsOf (← j.getObjVal? "supported"), ← strsOf (← j.getObjVal? "possible")) }

/-! ## 12. Said to a person -/

/-- The atoms a state names, in the order they were introduced. -/
def State.atoms (s : State) : List String := s.base.atoms

def ruleText (r : Rule) : String :=
  r.concl ++ " ⇐ " ++ (if r.pos.isEmpty then "(nothing)" else ", ".intercalate r.pos) ++
    (if r.neg.isEmpty then "" else " unless " ++ ", ".intercalate r.neg)

/-- The explanation `x` stands on now, if it is supported by one: the first to fire for it in the
stages of `Γ` of the possible atoms, so a well-founded support, never one that rests on `x` itself. -/
def State.standing (s : State) (x : String) : Option String :=
  let P := s.base.program
  let J := s.kept.2
  (List.range (bound P)).findSome? fun n =>
    ((P.rules.filter fun r => r.concl == x && fires J (stage P J n) r).head?).map (·.name)

/-- One atom, its status and what it stands on (or why not), said. -/
def State.line (s : State) (x : String) : String :=
  let st := s.status x
  match s.base.observations.find? (·.name == x) with
  | some o => x ++ ": " ++ st.text ++ " (observed at " ++ o.source ++ ")"
  | none =>
    if s.base.held.contains x then x ++ ": " ++ st.text ++ " (assumed)"
    else if st == .supported then x ++ ": supported by " ++ (s.standing x).getD "?"
    else x ++ ": " ++ st.text ++ ": " ++ "; ".intercalate (whyNot s x)

/-- What moved between two states, said: each atom whose status changed. -/
def changes (s s' : State) : List String :=
  s'.atoms.filterMap fun x =>
    let a := s.status x
    let c := s'.status x
    if a == c then none else some (x ++ ": " ++ c.text ++ " (was " ++ a.text ++ ")")

/-! ## 13. Cycle-Safe Dialectical Defeat & Blocker Chains -/

/-- Structured multi-hop blocker certificate explaining why a target atom is not `.supported` in `State`,
terminating cleanly on arbitrary cyclic positive/negative defeat graphs via explicit visited-path cycle
detection. -/
inductive BlockerChain where
  | alreadySupported
  | withdrawnAssumption (atom : String)
  | unexplained (atom : String)
  | cyclicDependency (cycleAtom : String) (visitedPath : List String)
  | defeatedByEvidence (ruleName : String) (defeaterAtom : String)
  | contestedByUndefined (ruleName : String) (defeaterAtom : String) (next : BlockerChain)
  | missingPremise (ruleName : String) (premiseAtom : String) (next : BlockerChain)
  | fuelExhausted (atom : String)
deriving DecidableEq, Repr

/-- Fuel-and-visited-set bounded dialectical blocker walker. -/
def traceBlockerAux (s : State) : Nat → List String → String → BlockerChain
  | 0, _, x =>
    if s.status x == .supported then .alreadySupported else .fuelExhausted x
  | fuel + 1, visited, x =>
    if s.status x == .supported then
      .alreadySupported
    else if visited.contains x then
      .cyclicDependency x visited
    else if s.base.withdrawn.contains x && !s.base.held.contains x then
      .withdrawnAssumption x
    else
      match (s.base.rulesFor x).head? with
      | none => .unexplained x
      | some r =>
        match r.pos.find? (fun p => s.status p != .supported) with
        | some p =>
          if (x :: visited).contains p then
            .cyclicDependency p (x :: visited)
          else
            .missingPremise r.name p (traceBlockerAux s fuel (x :: visited) p)
        | none =>
          match r.neg.find? (fun q => s.status q != .unsupported) with
          | some q =>
            if s.status q == .supported then
              .defeatedByEvidence r.name q
            else if (x :: visited).contains q then
              .cyclicDependency q (x :: visited)
            else
              .contestedByUndefined r.name q (traceBlockerAux s fuel (x :: visited) q)
          | none => .unexplained x

/-- Compute a cycle-safe multi-hop dialectical blocker certificate for `x` at state `s`. -/
def traceUnsupportedRoot (s : State) (x : String) : BlockerChain :=
  traceBlockerAux s (s.atoms.length + 2) [] x

theorem traceBlockerAux_eq_alreadySupported_iff (s : State) :
    ∀ (fuel : Nat) (visited : List String) (x : String),
      traceBlockerAux s fuel visited x = .alreadySupported ↔ s.status x = .supported
  | 0, _, x => by
    unfold traceBlockerAux
    by_cases h : s.status x = .supported <;> simp [h]
  | fuel + 1, visited, x => by
    unfold traceBlockerAux
    by_cases h : s.status x = .supported
    · simp [h]
    · have hne : (s.status x == .supported) = false := beq_false_of_ne h
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro heq
        split at heq
        · cases heq
        · split at heq
          · cases heq
          · split at heq
            · cases heq
            · split at heq
              · split at heq <;> cases heq
              · split at heq
                · split at heq
                  · cases heq
                  · split at heq <;> cases heq
                · cases heq
      · intro hs
        exact absurd hs h

theorem traceUnsupportedRoot_eq_alreadySupported_iff (s : State) (x : String) :
    traceUnsupportedRoot s x = .alreadySupported ↔ s.status x = .supported :=
  traceBlockerAux_eq_alreadySupported_iff s (s.atoms.length + 2) [] x

/-- Soundness of `traceUnsupportedRoot`: whenever `s` is consistent and `traceUnsupportedRoot s x`
returns any non-`.alreadySupported` blocker certificate, `x` is genuinely not `.supported` in `s.base`. -/
theorem traceUnsupportedRoot_sound {s : State} {x : String} {chain : BlockerChain}
    (hc : s.Consistent) (h : traceUnsupportedRoot s x = chain) (hne : chain ≠ .alreadySupported) :
    status s.base x ≠ .supported := by
  rw [← State.status_eq hc x]
  intro hsup
  have heq : traceUnsupportedRoot s x = .alreadySupported :=
    (traceUnsupportedRoot_eq_alreadySupported_iff s x).2 hsup
  exact hne (h.symm.trans heq)

/-- Non-trivial inhabitedness witness for `traceUnsupportedRoot`: on an odd self-defeating base
(`p ← not p`), `traceUnsupportedRoot` terminates without looping and pinpoints the exact cyclic
dependency `.cyclicDependency "p" ["p"]`. -/
theorem traceUnsupportedRoot_inhabited :
    let bOdd : Base := { explanations := [{ name := "self_defeat", concl := "p", pos := [], neg := ["p"] }] }
    let sOdd : State := { base := bOdd, kept := judge bOdd }
    sOdd.Consistent ∧
    traceUnsupportedRoot sOdd "p" = .cyclicDependency "p" ["p"] := by
  refine ⟨⟨Same.refl _, Same.refl _⟩, ?_⟩
  decide

end Obend.Reasons

end
