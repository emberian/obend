module
public import Obend.Reasons.UnifiedEquilibrium
import all Obend.Reasons.UnifiedEquilibrium
public import Obend.Crypto.Multilinear
public import Obend.Tactic.Tooth

public section
set_option autoImplicit false
namespace Obend.SymbolicZk.Ranked
open Obend.Reasons

/-- Specification ranks, separate from the finite array certificate below. -/
structure SemanticRanks where
  stage : String → Nat
  rankT : String → Nat
  rankU : String → Nat

/-- Strict alternating descent; negative dependencies may not stay in the same stage. -/
@[expose] def earlier (a b : Nat) : Prop := a < b

/-- Positive truths may descend within a stage. -/
@[expose] def lexEarlier (s r s' r' : Nat) : Prop := s < s' ∨ s = s' ∧ r < r'

/-- False positive cycles may be eliminated simultaneously. -/
@[expose] def noLater (a b : Nat) : Prop := a ≤ b

instance (a b : Nat) : Decidable (earlier a b) := inferInstanceAs (Decidable (a < b))
instance (a b : Nat) : Decidable (noLater a b) := inferInstanceAs (Decidable (a ≤ b))
instance (s r s' r' : Nat) : Decidable (lexEarlier s r s' r') :=
  inferInstanceAs (Decidable (s < s' ∨ s = s' ∧ r < r'))

/-- Least reduct model: closure plus finite, strictly descending support. -/
def RankedGamma (P : Program) (j m : List String) (rank : String → Nat) : Prop :=
  Sub (T P j m) m ∧ ∀ a, a ∈ m →
    a ∈ P.facts ∨ ∃ r ∈ P.rules, r.concl = a ∧
      (∀ d ∈ r.neg, d ∉ j) ∧
      (∀ b ∈ r.pos, b ∈ m ∧ earlier (rank b) (rank a))

theorem rankedGamma_sound {P : Program} {j m : List String} {rank : String → Nat}
    (h : RankedGamma P j m rank) : Same m (gamma P j) := by
  have grounded : ∀ n a, rank a = n → a ∈ m → a ∈ gamma P j := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a ha hm
      rcases h.2 a hm with hf | ⟨r, hr, hc, hn, hp⟩
      · exact mem_gamma.mpr (Or.inl hf)
      · apply mem_gamma.mpr
        exact Or.inr ⟨r, hr, hc, fun b hb =>
          ih (rank b) (by simpa [earlier, ha] using (hp b hb).2) b rfl (hp b hb).1, hn⟩
  exact fun a => ⟨grounded (rank a) a rfl, gamma_least P j m h.1 a⟩

/-- A finite search has a least successful index; used only in witness existence proofs. -/
theorem least_index {p : Nat → Prop} (h : ∃ n, p n) :
    ∃ n, p n ∧ ∀ k, p k → n ≤ k := by
  classical
  obtain ⟨n, hn⟩ := h
  have aux : ∀ n, p n → ∃ m, p m ∧ ∀ k, p k → m ≤ k := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hsmall : ∃ k, k < n ∧ p k
      · obtain ⟨k, hk, hp⟩ := hsmall
        exact ih k hk hp
      · exact ⟨n, hn, fun k hk => by
          by_cases hle : n ≤ k
          · exact hle
          · exact False.elim (hsmall ⟨k, by omega, hk⟩)⟩
  exact aux n hn

noncomputable def firstIndex (p : Nat → Prop) : Nat :=
  open Classical in
  if h : ∃ n, p n then Classical.choose (least_index h) else 0

theorem firstIndex_spec {p : Nat → Prop} (h : ∃ n, p n) : p (firstIndex p) := by
  classical
  simpa [firstIndex, h] using (Classical.choose_spec (least_index h)).1

theorem firstIndex_le {p : Nat → Prop} {n : Nat} (h : p n) : firstIndex p ≤ n := by
  classical
  simpa [firstIndex, show ∃ n, p n from ⟨n, h⟩] using
    (Classical.choose_spec (least_index (show ∃ n, p n from ⟨n, h⟩))).2 n h

theorem stage_sub_gamma (P : Program) (j : List String) : ∀ n, Sub (stage P j n) (gamma P j) := by
  intro n
  induction n with
  | zero => intro a ha; simp [stage] at ha
  | succ n ih =>
    exact fun a ha => (gamma_fix P j a).1 (T_mono P (fun _ h => h) ih a ha)

theorem rankedGamma_complete (P : Program) (j m : List String) (hm : Same m (gamma P j)) :
    ∃ rank, RankedGamma P j m rank := by
  classical
  let rank := fun a => firstIndex (fun n => a ∈ stage P j n)
  refine ⟨rank, ?_, ?_⟩
  · intro a ha
    exact (hm a).2 ((gamma_fix P j a).1
      (T_mono P (fun _ h => h) (fun b hb => (hm b).1 hb) a ha))
  · intro a ha
    have hfirst : a ∈ stage P j (rank a) := firstIndex_spec (p := fun n => a ∈ stage P j n) ⟨bound P, (hm a).1 ha⟩
    cases heq : rank a with
    | zero => simp [heq, stage] at hfirst
    | succ n =>
      rw [heq] at hfirst
      rcases mem_T.mp hfirst with hf | ⟨r, hr, hfire, hc⟩
      · exact Or.inl hf
      · obtain ⟨hp, hn⟩ := fires_iff.mp hfire
        refine Or.inr ⟨r, hr, hc, hn, fun b hb => ⟨(hm b).2 (stage_sub_gamma P j n b (hp b hb)), ?_⟩⟩
        have hle : rank b ≤ n := firstIndex_le (hp b hb)
        simp only [earlier]
        omega

theorem rankedGamma_iff (P : Program) (j m : List String) :
    (∃ rank, RankedGamma P j m rank) ↔ Same m (gamma P j) :=
  ⟨fun ⟨_, h⟩ => rankedGamma_sound h, rankedGamma_complete P j m⟩

theorem rankedGLStable_iff (P : Program) (m : List String) :
    (∃ rank, RankedGamma P m m rank) ↔
      Obend.Reasons.UnifiedEquilibrium.IsGLStableModel P m := rankedGamma_iff P m m

/-- C1–C4 over the complete program. Facts participate in both closures. -/
def RankedWFS (P : Program) (t u : List String) (c : SemanticRanks) : Prop :=
  Sub t u ∧
  (∀ a, a ∈ t → a ∈ P.facts ∨ ∃ r ∈ P.rules, r.concl = a ∧
    (∀ b ∈ r.pos, b ∈ t ∧ lexEarlier (c.stage b) (c.rankT b) (c.stage a) (c.rankT a)) ∧
    (∀ d ∈ r.neg, d ∉ u ∧ earlier (c.stage d) (c.stage a))) ∧
  (Sub P.facts u ∧ ∀ r ∈ P.rules, r.concl ∉ u →
    (∃ d ∈ r.neg, d ∈ t ∧ noLater (c.stage d) (c.stage r.concl)) ∨
    (∃ b ∈ r.pos, b ∉ u ∧ noLater (c.stage b) (c.stage r.concl))) ∧
  (∀ a, a ∈ u → a ∈ P.facts ∨ ∃ r ∈ P.rules, r.concl = a ∧
    (∀ d ∈ r.neg, d ∉ t) ∧
    (∀ b ∈ r.pos, b ∈ u ∧ earlier (c.rankU b) (c.rankU a))) ∧
  Sub (T P u t) t

/-- C2 and C3 identify the upper component with the least reduct, including unfounded sets. -/
theorem rankedWFS_upper {P : Program} {t u : List String} {c : SemanticRanks}
    (h : RankedWFS P t u c) : Same u (gamma P t) := by
  apply rankedGamma_sound (rank := c.rankU)
  refine ⟨?_, h.2.2.2.1⟩
  intro a ha
  rcases mem_T.mp ha with hf | ⟨r, hr, hfire, rfl⟩
  · exact h.2.2.1.1 a hf
  · by_cases hout : r.concl ∈ u
    · exact hout
    apply False.elim
    obtain ⟨hp, hn⟩ := fires_iff.mp hfire
    rcases h.2.2.1.2 r hr hout with ⟨d, hd, hdt, _⟩ | ⟨b, hb, hbu, _⟩
    · exact hn d hd hdt
    · exact hbu (hp b hb)

/-- The stage induction alternates true derivations with an unfounded-set exclusion.
In particular no acyclic ranking of false positive dependencies is assumed. -/
theorem rankedWFS_sound {P : Program} {t u : List String} {c : SemanticRanks}
    (h : RankedWFS P t u c) : Same t (wf P).1 ∧ Same u (wf P).2 := by
  have hu := rankedWFS_upper h
  have hleast : Sub (wf P).1 t := by
    apply rounds_least P t
    have hclosed : Sub (gamma P u) t := gamma_least P u t h.2.2.2.2
    intro a ha
    exact hclosed a (by simpa only [gamma_congr P hu] using ha)
  have hfacts : ∀ a, a ∈ P.facts → a ∈ (wf P).1 := by
    intro a ha
    exact (rounds_fix P a).1 (mem_gamma.mpr (Or.inl ha))
  have stages : ∀ k,
      (∀ a, a ∈ t → c.stage a ≤ k → a ∈ (wf P).1) ∧
      (∀ a, a ∉ u → c.stage a ≤ k → a ∉ (wf P).2) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      have truths : ∀ n a, c.rankT a = n → a ∈ t → c.stage a ≤ k → a ∈ (wf P).1 := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihr =>
          intro a hra hat hsa
          by_cases hsk : c.stage a < k
          · exact (ih (c.stage a) hsk).1 a hat (Nat.le_refl _)
          have hska : c.stage a = k := by omega
          rcases h.2.1 a hat with hf | ⟨r, hr, hc, hp, hn⟩
          · exact hfacts a hf
          · apply (rounds_fix P a).1
            apply mem_gamma.mpr
            refine Or.inr ⟨r, hr, hc, fun b hb => ?_, fun d hd => ?_⟩
            · have hp' := hp b hb
              apply (rounds_fix P b).2
              rcases hp'.2 with hlt | ⟨heq, hlt⟩
              · exact (ih (c.stage b) (by omega)).1 b hp'.1 (Nat.le_refl _)
              · exact ihr (c.rankT b) (by simpa [hra] using hlt) b rfl hp'.1 (by omega)
            · have hn' := hn d hd
              exact (ih (c.stage d) (by simpa [earlier, hska] using hn'.2)).2 d hn'.1 (Nat.le_refl _)
      have ht : ∀ a, a ∈ t → c.stage a ≤ k → a ∈ (wf P).1 := fun a => truths (c.rankT a) a rfl
      refine ⟨ht, ?_⟩
      have exclude : ∀ n a, a ∉ u → c.stage a ≤ k → a ∉ stage P (wf P).1 n := by
        intro n
        induction n with
        | zero => simp [stage]
        | succ n ihn =>
          intro a hau hak ha
          rcases mem_T.mp ha with hf | ⟨r, hr, hfire, hc⟩
          · exact hau (h.2.2.1.1 a hf)
          · obtain ⟨hp, hn⟩ := fires_iff.mp hfire
            rcases h.2.2.1.2 r hr (by simpa [hc] using hau) with ⟨d, hd, hdt, hds⟩ | ⟨b, hb, hbu, hbs⟩
            · exact hn d hd (ht d hdt (by unfold noLater at hds; rw [hc] at hds; omega))
            · exact ihn b hbu (by unfold noLater at hbs; rw [hc] at hbs; omega) (hp b hb)
      exact exclude (bound P)
  have ht : Same t (wf P).1 := fun a => ⟨fun ha => (stages (c.stage a)).1 a ha (Nat.le_refl _), hleast a⟩
  exact ⟨ht, hu.trans (fun a => by rw [gamma_congr P ht]; rfl)⟩

theorem rounds_sub_wf (P : Program) : ∀ k, Sub (rounds P k) (wf P).1 := by
  intro k
  induction k with
  | zero => intro a ha; simp [rounds] at ha
  | succ k ih => exact fun a ha => (rounds_fix P a).1 (gamma_anti P (gamma_anti P ih) a ha)

/-- Canonical first alternating appearance/disappearance stages. Witness generation is
noncomputable here; the verifier below never evaluates these searches. -/
noncomputable def trueStage (P : Program) (a : String) := firstIndex (fun k => a ∈ rounds P k)
noncomputable def falseStage (P : Program) (a : String) := firstIndex (fun k => a ∉ gamma P (rounds P k))
noncomputable def trueRank (P : Program) (a : String) :=
  firstIndex (fun n => a ∈ stage P (gamma P (rounds P (trueStage P a - 1))) n)

private theorem trueStage_mem {P : Program} {a : String} (h : a ∈ (wf P).1) :
    a ∈ rounds P (trueStage P a) :=
  firstIndex_spec (p := fun k => a ∈ rounds P k) ⟨bound P, h⟩

private theorem trueStage_pos {P : Program} {a : String} (h : a ∈ (wf P).1) :
    0 < trueStage P a := by
  have hm := trueStage_mem h
  cases he : trueStage P a with
  | zero => simp [he, rounds] at hm
  | succ n => omega

private theorem falseStage_out {P : Program} {a : String} (h : a ∉ (wf P).2) :
    a ∉ gamma P (rounds P (falseStage P a)) :=
  firstIndex_spec (p := fun k => a ∉ gamma P (rounds P k)) ⟨bound P, h⟩

/-- Completeness constructs first-occurrence ranks and universal blockers from the actual
alternating sequence, rather than adding the desired semantics to the certificate. -/
theorem rankedWFS_complete (P : Program) : ∃ c, RankedWFS P (wf P).1 (wf P).2 c := by
  classical
  obtain ⟨ru, hru⟩ := rankedGamma_complete P (wf P).1 (wf P).2 (Same.refl _)
  let s := fun a => if a ∈ (wf P).1 then trueStage P a else falseStage P a
  let c : SemanticRanks := ⟨s, trueRank P, ru⟩
  have st {a} (ha : a ∈ (wf P).1) : s a = trueStage P a := by simp [s, ha]
  have sf {a} (ha : a ∉ (wf P).2) : s a = falseStage P a :=
    by simp [s, show a ∉ (wf P).1 from fun ht => ha (supported_possible P a ht)]
  refine ⟨c, supported_possible P, ?_, ⟨?_, ?_⟩, hru.2, ?_⟩
  · intro a ha
    have ham := trueStage_mem ha
    have hap := trueStage_pos ha
    have hs : trueStage P a - 1 + 1 = trueStage P a := by omega
    have hag : a ∈ gamma P (gamma P (rounds P (trueStage P a - 1))) := by
      rw [← hs] at ham
      exact ham
    have har : a ∈ stage P (gamma P (rounds P (trueStage P a - 1))) (trueRank P a) :=
      firstIndex_spec (p := fun n => a ∈ stage P (gamma P (rounds P (trueStage P a - 1))) n) ⟨bound P, hag⟩
    cases he : trueRank P a with
    | zero => simp [he, stage] at har
    | succ n =>
      rw [he] at har
      rcases mem_T.mp har with hf | ⟨r, hr, hfire, hc⟩
      · exact Or.inl hf
      · obtain ⟨hp, hn⟩ := fires_iff.mp hfire
        refine Or.inr ⟨r, hr, hc, ?_, ?_⟩
        · intro b hb
          have hbg := stage_sub_gamma P _ n b (hp b hb)
          have hbr : b ∈ rounds P (trueStage P a) := by
            rw [← hs]
            exact hbg
          have hbt := rounds_sub_wf P _ b hbr
          have hbs : trueStage P b ≤ trueStage P a := firstIndex_le hbr
          refine ⟨hbt, ?_⟩
          change lexEarlier (s b) (trueRank P b) (s a) (trueRank P a)
          rw [st hbt, st ha]
          by_cases hlt : trueStage P b < trueStage P a
          · exact Or.inl hlt
          · have heq : trueStage P b = trueStage P a := by omega
            refine Or.inr ⟨heq, ?_⟩
            have hle : trueRank P b ≤ n := firstIndex_le (by simpa only [heq] using hp b hb)
            omega
        · intro d hd
          have hdout : d ∉ (wf P).2 := fun hdU => hn d hd
            (gamma_anti P (rounds_sub_wf P _) d hdU)
          refine ⟨hdout, ?_⟩
          change earlier (s d) (s a)
          rw [sf hdout, st ha]
          have hle : falseStage P d ≤ trueStage P a - 1 := firstIndex_le (hn d hd)
          unfold earlier
          omega
  · intro a ha
    exact mem_gamma.mpr (Or.inl ha)
  · intro r hr hout
    have hnot := falseStage_out hout
    by_cases hneg : ∃ d ∈ r.neg, d ∈ rounds P (falseStage P r.concl)
    · obtain ⟨d, hd, hdm⟩ := hneg
      have hdt := rounds_sub_wf P _ d hdm
      refine Or.inl ⟨d, hd, hdt, ?_⟩
      change noLater (s d) (s r.concl)
      rw [st hdt, sf hout]
      exact firstIndex_le hdm
    · have hp : ∃ b ∈ r.pos, b ∉ gamma P (rounds P (falseStage P r.concl)) := by
        by_cases hex : ∃ b ∈ r.pos, b ∉ gamma P (rounds P (falseStage P r.concl))
        · exact hex
        · apply False.elim
          apply hnot
          apply mem_gamma.mpr
          refine Or.inr ⟨r, hr, rfl, ?_, ?_⟩
          · intro b hb
            by_cases hm : b ∈ gamma P (rounds P (falseStage P r.concl))
            · exact hm
            · exact False.elim (hex ⟨b, hb, hm⟩)
          · intro d hd hm
            exact hneg ⟨d, hd, hm⟩
      obtain ⟨b, hb, hbm⟩ := hp
      have hbu : b ∉ (wf P).2 := fun hm => hbm (gamma_anti P (rounds_sub_wf P _) b hm)
      refine Or.inr ⟨b, hb, hbu, ?_⟩
      change noLater (s b) (s r.concl)
      rw [sf hbu, sf hout]
      exact firstIndex_le hbm
  · intro a ha
    exact (rounds_fix P a).1 ((gamma_fix P (wf P).2 a).1
      (T_mono P (fun _ h => h) (fun b hb => (rounds_fix P b).2 hb) a ha))

/-- Exact VGRS semantics, with both directions and no stratification restriction. -/
theorem rankedWFS_iff (P : Program) (t u : List String) :
    (∃ c, RankedWFS P t u c) ↔ Same t (wf P).1 ∧ Same u (wf P).2 := by
  constructor
  · exact fun ⟨_, h⟩ => rankedWFS_sound h
  · rintro ⟨ht, hu⟩
    obtain ⟨c, hc⟩ := rankedWFS_complete P
    refine ⟨c, ?_⟩
    change ∀ a, a ∈ t ↔ a ∈ (wf P).1 at ht
    change ∀ a, a ∈ u ↔ a ∈ (wf P).2 at hu
    unfold RankedWFS at hc ⊢
    simpa only [Reasons.Sub, ht, hu, T_congr P hu ht] using hc

/-- Facts are empty-body rules, so the universal blocker check cannot hide them. -/
structure ArithRule where
  head : Nat
  pos : Array Nat := #[]
  neg : Array Nat := #[]
  deriving Repr, Inhabited, DecidableEq

structure ArithProgram where
  numAtoms : Nat
  rules : Array ArithRule
  deriving Repr, Inhabited

@[expose] def WFProgram (p : ArithProgram) : Bool :=
  p.rules.all fun r => r.head < p.numAtoms &&
    r.pos.all (· < p.numAtoms) && r.neg.all (· < p.numAtoms)

/-- Finite certificates; every selector and all ranks are serialized array entries. -/
structure ArrayCert where
  stage : Array Nat
  rankT : Array Nat
  rankU : Array Nat
  supportT : Array Nat
  supportU : Array Nat
  /-- `(negative?, literal index)` for each full-program rule. -/
  blockers : Array (Bool × Nat)
  deriving Repr, Inhabited

@[expose] def bit (m : Array Bool) (a : Nat) : Bool := m[a]?.getD false
@[expose] def rankAt (r : Array Nat) (a : Nat) : Nat := r[a]?.getD 0

@[expose] def firesFast (r : ArithRule) (j m : Array Bool) : Bool :=
  r.pos.all (bit m) && r.neg.all (fun d => !bit j d)

@[expose] def checkClosure (p : ArithProgram) (j m : Array Bool) : Bool :=
  p.rules.all fun r => !firesFast r j m || bit m r.head

@[expose] def checkSupport (p : ArithProgram) (j m : Array Bool)
    (rank support : Array Nat) (a : Nat) : Bool :=
  match p.rules[rankAt support a]? with
  | none => false
  | some r => r.head == a && r.neg.all (fun d => !bit j d) &&
      r.pos.all (fun b => bit m b && decide (earlier (rankAt rank b) (rankAt rank a)))

def checkRankedGamma (p : ArithProgram) (j m : Array Bool) (rank support : Array Nat) : Bool :=
  WFProgram p && j.size == p.numAtoms && m.size == p.numAtoms &&
  rank.size == p.numAtoms && support.size == p.numAtoms && checkClosure p j m &&
  (Array.range p.numAtoms).all (fun a => !bit m a || checkSupport p j m rank support a)

def checkRankedGLStable (p : ArithProgram) (m : Array Bool) (rank support : Array Nat) : Bool :=
  checkRankedGamma p m m rank support

@[expose] def checkTrueSupport (p : ArithProgram) (t u : Array Bool) (c : ArrayCert) (a : Nat) : Bool :=
  match p.rules[rankAt c.supportT a]? with
  | none => false
  | some r => r.head == a &&
    r.pos.all (fun b => bit t b && decide (lexEarlier (rankAt c.stage b) (rankAt c.rankT b)
      (rankAt c.stage a) (rankAt c.rankT a))) &&
    r.neg.all (fun d => !bit u d && decide (earlier (rankAt c.stage d) (rankAt c.stage a)))

@[expose] def checkBlocker (r : ArithRule) (t u : Array Bool) (s : Array Nat) (b : Bool × Nat) : Bool :=
  if b.1 then
    match r.neg[b.2]? with
    | none => false
    | some d => bit t d && decide (noLater (rankAt s d) (rankAt s r.head))
  else
    match r.pos[b.2]? with
    | none => false
    | some d => !bit u d && decide (noLater (rankAt s d) (rankAt s r.head))

/-- Single pass over atoms, selected supports, and the entire rule table. Selected support
heads are checked before their bodies, so each rule body is visited at most once per phase. -/
def checkRankedWFS (p : ArithProgram) (t u : Array Bool) (c : ArrayCert) : Bool :=
  WFProgram p && t.size == p.numAtoms && u.size == p.numAtoms &&
  c.stage.size == p.numAtoms && c.rankT.size == p.numAtoms && c.rankU.size == p.numAtoms &&
  c.supportT.size == p.numAtoms && c.supportU.size == p.numAtoms && c.blockers.size == p.rules.size &&
  (Array.range p.numAtoms).all (fun a => (!bit t a || bit u a) &&
    (!bit t a || checkTrueSupport p t u c a) &&
    (!bit u a || checkSupport p t u c.rankU c.supportU a)) &&
  (Array.range p.rules.size).all (fun i =>
    let r := p.rules[i]!
    bit u r.head || checkBlocker r t u c.stage (c.blockers[i]?.getD (false, 0))) &&
  checkClosure p u t

/-- Unary names are used only by the specification bridge, never by the verifier. -/
@[expose] def atomName (a : Nat) : String := String.ofList (List.replicate a 'a')

@[simp] theorem atomName_length (a : Nat) : (atomName a).length = a := by
  simp [atomName]

theorem atomName_injective {a b : Nat} (h : atomName a = atomName b) : a = b := by
  simpa using congrArg String.length h

@[expose] def toReasonsRule (r : ArithRule) : Rule :=
  ⟨"", atomName r.head, r.pos.toList.map atomName, r.neg.toList.map atomName⟩

@[expose] def toReasonsProgram (p : ArithProgram) : Program :=
  ⟨[], p.rules.toList.map toReasonsRule⟩

@[expose] def decodeBits (m : Array Bool) : List String :=
  ((List.range m.size).filter (bit m)).map atomName

@[simp] theorem mem_decodeBits (m : Array Bool) (a : Nat) :
    atomName a ∈ decodeBits m ↔ bit m a = true := by
  simp only [decodeBits, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨b, ⟨_, hb⟩, he⟩
    exact atomName_injective he ▸ hb
  · intro h
    have hb : a < m.size := by
      by_cases hn : a < m.size
      · exact hn
      · simp [bit, Array.getElem?_eq_none (xs := m) (i := a) (by omega)] at h
    exact ⟨a, ⟨hb, h⟩, rfl⟩

theorem decodeBits_cases {m : Array Bool} {s : String} (h : s ∈ decodeBits m) :
    ∃ a, a < m.size ∧ bit m a = true ∧ s = atomName a := by
  simpa only [decodeBits, List.mem_map, List.mem_filter, List.mem_range, and_assoc,
    eq_comm] using h

theorem program_bounds {p : ArithProgram} (h : WFProgram p = true)
    {r : ArithRule} (hr : r ∈ p.rules) :
    r.head < p.numAtoms ∧ (∀ a ∈ r.pos, a < p.numAtoms) ∧
      (∀ a ∈ r.neg, a < p.numAtoms) := by
  simp only [WFProgram, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at h
  exact h r hr

private theorem support_of_check {p : ArithProgram} {j m : Array Bool}
    {rank support : Array Nat} {a : Nat}
    (h : checkSupport p j m rank support a = true) :
    ∃ r ∈ p.rules, r.head = a ∧ (∀ d ∈ r.neg, bit j d = false) ∧
      (∀ b ∈ r.pos, bit m b = true ∧ earlier (rankAt rank b) (rankAt rank a)) := by
  unfold checkSupport at h
  split at h
  · cases h
  · rename_i r he
    have hm : r ∈ p.rules := Array.mem_of_getElem? he
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
    exact ⟨r, hm, h.1.1, h.1.2, h.2⟩

private theorem closure_to_spec {p : ArithProgram} {j m : Array Bool}
    (h : checkClosure p j m = true) :
    Sub (T (toReasonsProgram p) (decodeBits j) (decodeBits m)) (decodeBits m) := by
  intro a ha
  rcases mem_T.mp ha with hf | ⟨r, hr, hf, hc⟩
  · cases hf
  · obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr
    have hh := (Array.all_eq_true_iff_forall_mem.mp h) r (by simpa using hr0)
    have fire : firesFast r j m = true := by
      obtain ⟨hp, hn⟩ := fires_iff.mp hf
      simp only [firesFast, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
      constructor
      · intro b hb
        exact (mem_decodeBits m b).mp (hp (atomName b) (List.mem_map.mpr ⟨b, by simpa using hb, rfl⟩))
      · intro d hd
        have hnot := hn (atomName d) (List.mem_map.mpr ⟨d, by simpa using hd, rfl⟩)
        cases hb : bit j d
        · rfl
        · exact False.elim (hnot ((mem_decodeBits j d).mpr hb))
    have hm : bit m r.head = true := by simpa [fire] using hh
    rw [← hc]
    exact (mem_decodeBits m r.head).mpr hm

/-- The selected array supports refine the semantic rank certificate. -/
theorem checkRankedGamma_sound {p : ArithProgram} {j m : Array Bool}
    {rank support : Array Nat} (h : checkRankedGamma p j m rank support = true) :
    Same (decodeBits m) (gamma (toReasonsProgram p) (decodeBits j)) := by
  simp only [checkRankedGamma, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, _, hm, _, _, hc, hs⟩ := h
  apply rankedGamma_sound (rank := fun s => rankAt rank s.length)
  refine ⟨closure_to_spec hc, ?_⟩
  intro a ha
  obtain ⟨i, hi, hb, rfl⟩ := decodeBits_cases ha
  have hsi := (Array.all_eq_true_iff_forall_mem.mp hs) i (by simp [← hm, hi])
  have hsupport : checkSupport p j m rank support i = true := by simpa [hb] using hsi
  obtain ⟨r, hr, he, hn, hp⟩ := support_of_check hsupport
  refine Or.inr ⟨toReasonsRule r, by exact List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩, by simp [toReasonsRule, he], ?_, ?_⟩
  · intro d hd
    obtain ⟨d, hd0, rfl⟩ := List.mem_map.mp hd
    simp [hn d (by simpa using hd0)]
  · intro b hb'
    obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb'
    obtain ⟨hbm, hbr⟩ := hp b (by simpa using hb0)
    exact ⟨(mem_decodeBits m b).mpr hbm, by simpa using hbr⟩

theorem checkRankedGLStable_sound {p : ArithProgram} {m : Array Bool}
    {rank support : Array Nat} (h : checkRankedGLStable p m rank support = true) :
    Obend.Reasons.UnifiedEquilibrium.IsGLStableModel (toReasonsProgram p) (decodeBits m) :=
  checkRankedGamma_sound h

example : checkRankedGamma ⟨1, #[⟨0, #[], #[]⟩]⟩ #[false] #[true] #[0] #[0] = true := by
  simp only [checkRankedGamma, WFProgram, checkClosure, firesFast,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp [checkSupport, rankAt, bit, Array.mem_range]

@[simp] theorem rankAt_ofFn {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    rankAt (Array.ofFn f) i.val = f i := by
  simp [rankAt, i.isLt]

/-- Serialize an arbitrary finite family of natural witnesses. -/
theorem chooseArray {n : Nat} {P : Nat → Nat → Prop}
    (h : ∀ i, i < n → ∃ j, P i j) :
    ∃ a : Array Nat, a.size = n ∧ ∀ i, i < n → P i (rankAt a i) := by
  classical
  let f := fun i : Fin n => Classical.choose (h i.val i.isLt)
  refine ⟨Array.ofFn f, by simp, ?_⟩
  intro i hi
  rw [rankAt_ofFn f ⟨i, hi⟩]
  exact Classical.choose_spec (h i hi)

private theorem closure_of_spec {p : ArithProgram} {j m : Array Bool}
    (h : Sub (T (toReasonsProgram p) (decodeBits j) (decodeBits m)) (decodeBits m)) :
    checkClosure p j m = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro r hr
  by_cases hf : firesFast r j m = true
  · have fire : fires (decodeBits j) (decodeBits m) (toReasonsRule r) = true := by
      apply fires_iff.mpr
      simp only [firesFast, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hf
      constructor
      · intro b hb
        obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb
        exact (mem_decodeBits m b).mpr (hf.1 b (by simpa using hb0))
      · intro d hd
        obtain ⟨d, hd0, rfl⟩ := List.mem_map.mp hd
        simp [hf.2 d (by simpa using hd0)]
    have hm := h (atomName r.head) (mem_T.mpr (Or.inr ⟨toReasonsRule r,
      List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩, fire, rfl⟩))
    simp [hf, (mem_decodeBits m r.head).mp hm]
  · simp [Bool.eq_false_iff.mpr hf]

/-- Completeness constructs finite ranks and selected rule indices from the least model. -/
theorem checkRankedGamma_complete (p : ArithProgram) (j m : Array Bool)
    (hw : WFProgram p = true) (hj : j.size = p.numAtoms) (hm : m.size = p.numAtoms)
    (he : Same (decodeBits m) (gamma (toReasonsProgram p) (decodeBits j))) :
    ∃ rank support, checkRankedGamma p j m rank support = true := by
  classical
  obtain ⟨rho, hc, hs⟩ := rankedGamma_complete (toReasonsProgram p) (decodeBits j) (decodeBits m) he
  let rank := Array.ofFn (fun a : Fin p.numAtoms => rho (atomName a.val))
  have rankval (a : Nat) (ha : a < p.numAtoms) : rankAt rank a = rho (atomName a) :=
    rankAt_ofFn _ ⟨a, ha⟩
  have choices : ∀ a, a < p.numAtoms → ∃ idx,
      ∀ support : Array Nat, rankAt support a = idx →
        (!bit m a || checkSupport p j m rank support a) = true := by
    intro a ha
    by_cases hbit : bit m a = true
    · rcases hs (atomName a) ((mem_decodeBits m a).mpr hbit) with hf | ⟨r, hr, heq, hn, hp⟩
      · cases hf
      · obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr
        have hrm : r ∈ p.rules := by simpa using hr0
        obtain ⟨idx, hi, hridx⟩ := Array.mem_iff_getElem.mp hrm
        have hhead : r.head = a := atomName_injective heq
        refine ⟨idx, ?_⟩
        intro support hidx
        have hlookup : p.rules[idx]? = some r := by
          rw [Array.getElem?_eq_some_getElem p.rules idx hi, hridx]
        simp only [hbit, Bool.not_true, Bool.false_or, checkSupport, hidx, hlookup,
          hhead, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
          Array.all_eq_true_iff_forall_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
        constructor
        · intro d hd
          have hh := hn (atomName d) (List.mem_map.mpr ⟨d, by simpa using hd, rfl⟩)
          exact Bool.eq_false_iff.mpr (fun hb => hh ((mem_decodeBits j d).mpr hb))
        · intro b hb
          have hh := hp (atomName b) (List.mem_map.mpr ⟨b, by simpa using hb, rfl⟩)
          exact ⟨(mem_decodeBits m b).mp hh.1, by
            rw [rankval b ((program_bounds hw hrm).2.1 b hb), rankval a ha]
            exact hh.2⟩
    · exact ⟨0, fun _ _ => by simp [Bool.eq_false_iff.mpr hbit]⟩
  obtain ⟨support, hsize, hsupport⟩ := chooseArray choices
  refine ⟨rank, support, ?_⟩
  simp only [checkRankedGamma, Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨hw, hj, hm, by simp [rank], hsize, closure_of_spec hc, ?_⟩
  exact Array.all_eq_true_iff_forall_mem.mpr (fun a ha => hsupport a (by simpa using ha) support rfl)

private theorem trueSupport_of_check {p : ArithProgram} {t u : Array Bool}
    {c : ArrayCert} {a : Nat} (h : checkTrueSupport p t u c a = true) :
    ∃ r ∈ p.rules, r.head = a ∧
      (∀ b ∈ r.pos, bit t b = true ∧ lexEarlier (rankAt c.stage b) (rankAt c.rankT b)
        (rankAt c.stage a) (rankAt c.rankT a)) ∧
      (∀ d ∈ r.neg, bit u d = false ∧ earlier (rankAt c.stage d) (rankAt c.stage a)) := by
  unfold checkTrueSupport at h
  split at h
  · cases h
  · rename_i r he
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
    exact ⟨r, Array.mem_of_getElem? he, h.1.1, h.1.2, h.2⟩

private theorem blocker_of_check {r : ArithRule} {t u : Array Bool} {s : Array Nat}
    {b : Bool × Nat} (h : checkBlocker r t u s b = true) :
    (∃ d ∈ r.neg, bit t d = true ∧ noLater (rankAt s d) (rankAt s r.head)) ∨
    (∃ d ∈ r.pos, bit u d = false ∧ noLater (rankAt s d) (rankAt s r.head)) := by
  unfold checkBlocker at h
  split at h
  · split at h
    · cases h
    · rename_i d he
      exact Or.inl ⟨d, Array.mem_of_getElem? he, by simpa using h⟩
  · split at h
    · cases h
    · rename_i d he
      exact Or.inr ⟨d, Array.mem_of_getElem? he, by simpa using h⟩

/-- A successful single-pass checker identifies the exact least alternating fixpoint. -/
theorem checkRankedWFS_sound {p : ArithProgram} {t u : Array Bool} {c : ArrayCert}
    (h : checkRankedWFS p t u c = true) :
    Same (decodeBits t) (wf (toReasonsProgram p)).1 ∧
      Same (decodeBits u) (wf (toReasonsProgram p)).2 := by
  simp only [checkRankedWFS, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, ht, hu, _, _, _, _, _, _, ha, hb, hc⟩ := h
  have atoms (a : Nat) (hi : a < p.numAtoms) :=
    (Array.all_eq_true_iff_forall_mem.mp ha) a (by simpa using hi)
  apply rankedWFS_sound (c := ⟨fun s => rankAt c.stage s.length,
    fun s => rankAt c.rankT s.length, fun s => rankAt c.rankU s.length⟩)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, closure_to_spec hc⟩
  · intro a hm
    obtain ⟨i, hi, hbit, rfl⟩ := decodeBits_cases hm
    have hh := atoms i (by omega)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hh
    exact (mem_decodeBits u i).mpr (hh.1.1.resolve_left (by simp [hbit]))
  · intro a hm
    obtain ⟨i, hi, hbit, rfl⟩ := decodeBits_cases hm
    have hh := atoms i (by omega)
    have hs : checkTrueSupport p t u c i = true := by simpa [hbit] using (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hh).1).2
    obtain ⟨r, hr, he, hp, hn⟩ := trueSupport_of_check hs
    refine Or.inr ⟨toReasonsRule r, List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩,
      by simp [toReasonsRule, he], ?_, ?_⟩
    · intro b hb'
      obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨hbm, hbr⟩ := hp b (by simpa using hb0)
      exact ⟨(mem_decodeBits t b).mpr hbm, by simpa using hbr⟩
    · intro d hd
      obtain ⟨d, hd0, rfl⟩ := List.mem_map.mp hd
      obtain ⟨hdm, hdr⟩ := hn d (by simpa using hd0)
      exact ⟨by simp [hdm], by simpa using hdr⟩
  · intro a hf
    cases hf
  · intro r hr hout
    obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr
    have hrm : r ∈ p.rules := by simpa using hr0
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hrm
    have hh := (Array.all_eq_true_iff_forall_mem.mp hb) i (by simpa using hi)
    have hi' : p.rules[i]! = r := by simp [getElem!_pos, hi, he]
    have hout' : bit u r.head = false := by
      have hn : ¬ bit u r.head = true := fun h => hout ((mem_decodeBits u r.head).mpr h)
      exact Bool.eq_false_iff.mpr hn
    rw [hi'] at hh
    simp only [hout', Bool.false_or] at hh
    rcases blocker_of_check hh with ⟨d, hd, hdt, hs⟩ | ⟨b, hp, hbu, hs⟩
    · exact Or.inl ⟨atomName d, List.mem_map.mpr ⟨d, by simpa using hd, rfl⟩,
        (mem_decodeBits t d).mpr hdt, by simpa [toReasonsRule] using hs⟩
    · exact Or.inr ⟨atomName b, List.mem_map.mpr ⟨b, by simpa using hp, rfl⟩,
        by simp [hbu], by simpa [toReasonsRule] using hs⟩
  · intro a hm
    obtain ⟨i, hi, hbit, rfl⟩ := decodeBits_cases hm
    have hh := atoms i (by omega)
    have hs : checkSupport p t u c.rankU c.supportU i = true := by
      simpa [hbit] using (Bool.and_eq_true_iff.mp hh).2
    obtain ⟨r, hr, he, hn, hp⟩ := support_of_check hs
    refine Or.inr ⟨toReasonsRule r, List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩,
      by simp [toReasonsRule, he], ?_, ?_⟩
    · intro d hd
      obtain ⟨d, hd0, rfl⟩ := List.mem_map.mp hd
      simp [hn d (by simpa using hd0)]
    · intro b hb'
      obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨hbm, hbr⟩ := hp b (by simpa using hb0)
      exact ⟨(mem_decodeBits u b).mpr hbm, by simpa using hbr⟩

example : checkRankedWFS ⟨0, #[]⟩ #[] #[] ⟨#[], #[], #[], #[], #[], #[]⟩ = true := by
  simp [checkRankedWFS, WFProgram, checkClosure, Array.range_eq_range']

/-- Completeness for any correctly sized encoding of the exact WFS pair. -/
theorem checkRankedWFS_complete (p : ArithProgram) (t u : Array Bool)
    (hw : WFProgram p = true) (ht : t.size = p.numAtoms) (hu : u.size = p.numAtoms)
    (hmodel : Same (decodeBits t) (wf (toReasonsProgram p)).1 ∧
      Same (decodeBits u) (wf (toReasonsProgram p)).2) :
    ∃ c, checkRankedWFS p t u c = true := by
  classical
  obtain ⟨cs, hs⟩ := (rankedWFS_iff (toReasonsProgram p) (decodeBits t) (decodeBits u)).mpr hmodel
  obtain ⟨ru, su, hgamma⟩ := checkRankedGamma_complete p t u hw ht hu (rankedWFS_upper hs)
  simp only [checkRankedGamma, Bool.and_eq_true, beq_iff_eq, and_assoc] at hgamma
  obtain ⟨_, _, _, hru, hsu, _, hupper⟩ := hgamma
  let stage := Array.ofFn (fun a : Fin p.numAtoms => cs.stage (atomName a.val))
  let rt := Array.ofFn (fun a : Fin p.numAtoms => cs.rankT (atomName a.val))
  have sv (a : Nat) (ha : a < p.numAtoms) : rankAt stage a = cs.stage (atomName a) := rankAt_ofFn _ ⟨a,ha⟩
  have rv (a : Nat) (ha : a < p.numAtoms) : rankAt rt a = cs.rankT (atomName a) := rankAt_ofFn _ ⟨a,ha⟩
  let base : ArrayCert := ⟨stage, rt, ru, #[], su, #[]⟩
  have choices : ∀ a, a < p.numAtoms → ∃ idx,
      ∀ support : Array Nat, rankAt support a = idx →
        (!bit t a || checkTrueSupport p t u {base with supportT := support} a) = true := by
    intro a ha
    by_cases hbit : bit t a = true
    · rcases hs.2.1 (atomName a) ((mem_decodeBits t a).mpr hbit) with hf | ⟨r, hr, he, hp, hn⟩
      · cases hf
      · obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr
        have hrm : r ∈ p.rules := by simpa using hr0
        obtain ⟨idx, hi, hridx⟩ := Array.mem_iff_getElem.mp hrm
        have hhead : r.head = a := atomName_injective he
        refine ⟨idx, ?_⟩
        intro support hidx
        have hlookup : p.rules[idx]? = some r := by rw [Array.getElem?_eq_some_getElem p.rules idx hi, hridx]
        simp only [hbit, Bool.not_true, Bool.false_or, checkTrueSupport, hidx, hlookup,
          hhead, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
          Array.all_eq_true_iff_forall_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
        constructor
        · intro b hb
          have hh := hp (atomName b) (List.mem_map.mpr ⟨b, by simpa using hb, rfl⟩)
          refine ⟨(mem_decodeBits t b).mp hh.1, ?_⟩
          change lexEarlier (rankAt stage b) (rankAt rt b) (rankAt stage a) (rankAt rt a)
          rw [sv b ((program_bounds hw hrm).2.1 b hb), rv b ((program_bounds hw hrm).2.1 b hb), sv a ha, rv a ha]
          exact hh.2
        · intro d hd
          have hh := hn (atomName d) (List.mem_map.mpr ⟨d, by simpa using hd, rfl⟩)
          refine ⟨Bool.eq_false_iff.mpr (fun hb => hh.1 ((mem_decodeBits u d).mpr hb)), ?_⟩
          change earlier (rankAt stage d) (rankAt stage a)
          rw [sv d ((program_bounds hw hrm).2.2 d hd), sv a ha]
          exact hh.2
    · exact ⟨0, fun _ _ => by simp [Bool.eq_false_iff.mpr hbit]⟩
  obtain ⟨st, hst, hsupport⟩ := chooseArray choices
  have blockers : ∀ i : Fin p.rules.size, ∃ b : Bool × Nat,
      (bit u p.rules[i.val].head || checkBlocker p.rules[i.val] t u stage b) = true := by
    intro i
    let r := p.rules[i.val]
    have hr : r ∈ p.rules := Array.getElem_mem i.isLt
    by_cases hbit : bit u r.head = true
    · exact ⟨(false,0), by simp [r] at hbit ⊢; simp [hbit]⟩
    · have hout : atomName r.head ∉ decodeBits u := fun hb => hbit ((mem_decodeBits u r.head).mp hb)
      have hm := hs.2.2.1.2 (toReasonsRule r) (List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩) hout
      rcases hm with ⟨d, hd, hdt, hds⟩ | ⟨b, hb, hbu, hbs⟩
      · obtain ⟨d, hd0, rfl⟩ := List.mem_map.mp hd
        have hdm : d ∈ r.neg := by simpa using hd0
        obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hdm
        have hlookup : r.neg[j]? = some d := by rw [Array.getElem?_eq_some_getElem r.neg j hj, he]
        refine ⟨(true,j), ?_⟩
        change (bit u r.head || checkBlocker r t u stage (true,j)) = true
        simp only [checkBlocker, ↓reduceIte, hlookup, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq]
        right
        refine ⟨(mem_decodeBits t d).mp hdt, ?_⟩
        rw [sv d ((program_bounds hw hr).2.2 d hdm), sv r.head (program_bounds hw hr).1]
        exact hds
      · obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb
        have hbm : b ∈ r.pos := by simpa using hb0
        obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hbm
        have hlookup : r.pos[j]? = some b := by rw [Array.getElem?_eq_some_getElem r.pos j hj, he]
        refine ⟨(false,j), ?_⟩
        change (bit u r.head || checkBlocker r t u stage (false,j)) = true
        simp only [checkBlocker, Bool.false_eq_true, ↓reduceIte, hlookup, Bool.or_eq_true,
          Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
        right
        refine ⟨Bool.eq_false_iff.mpr (fun hm => hbu ((mem_decodeBits u b).mpr hm)), ?_⟩
        rw [sv b ((program_bounds hw hr).2.1 b hbm), sv r.head (program_bounds hw hr).1]
        exact hbs
  let bs := Array.ofFn (fun i : Fin p.rules.size => Classical.choose (blockers i))
  let c : ArrayCert := ⟨stage, rt, ru, st, su, bs⟩
  refine ⟨c, ?_⟩
  simp only [checkRankedWFS, Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨hw, ht, hu, by simp [c, stage], by simp [c, rt], hru, hst, hsu,
    by simp [c, bs], ?_, ?_, closure_of_spec hs.2.2.2.2⟩
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro a ha
    have hai : a < p.numAtoms := by simpa using ha
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, (Array.all_eq_true_iff_forall_mem.mp hupper) a ha⟩
    · by_cases hbit : bit t a = true
      · have hh := hs.1 (atomName a) ((mem_decodeBits t a).mpr hbit)
        simp [hbit, (mem_decodeBits u a).mp hh]
      · simp [Bool.eq_false_iff.mpr hbit]
    · exact hsupport a hai st rfl
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    have hib : i < p.rules.size := by simpa using hi
    have hb := Classical.choose_spec (blockers ⟨i,hib⟩)
    simpa [c, bs, getElem!_pos, hib, Array.getElem?_eq_some_getElem] using hb

def encodeAtoms (n : Nat) (xs : List String) : Array Bool :=
  Array.ofFn (fun a : Fin n => xs.contains (atomName a.val))

private theorem bit_encode (n : Nat) (xs : List String) (a : Nat) (ha : a < n) :
    bit (encodeAtoms n xs) a = xs.contains (atomName a) := by
  simp [encodeAtoms, bit, ha]

private theorem decode_encode (n : Nat) (xs : List String)
    (hx : ∀ s ∈ xs, ∃ a, a < n ∧ s = atomName a) : Same (decodeBits (encodeAtoms n xs)) xs := by
  intro s
  constructor
  · intro hs
    obtain ⟨a, ha, hb, rfl⟩ := decodeBits_cases hs
    have hai : a < n := by simpa [encodeAtoms] using ha
    simpa [bit_encode n xs a hai] using hb
  · intro hs
    obtain ⟨a, ha, rfl⟩ := hx s hs
    apply (mem_decodeBits _ _).mpr
    simpa [bit_encode n xs a ha] using hs

private theorem atoms_named {p : ArithProgram} (hw : WFProgram p = true)
    {s : String} (hs : s ∈ atomsOf (toReasonsProgram p)) :
    ∃ a, a < p.numAtoms ∧ s = atomName a := by
  simp only [atomsOf, toReasonsProgram, List.nil_append, List.mem_map] at hs
  obtain ⟨r, ⟨r0, hr, rfl⟩, he⟩ := hs
  exact ⟨r0.head, (program_bounds hw (by simpa using hr)).1, he.symm⟩

def tWf (p : ArithProgram) : Array Bool := encodeAtoms p.numAtoms (wf (toReasonsProgram p)).1
def uWf (p : ArithProgram) : Array Bool := encodeAtoms p.numAtoms (wf (toReasonsProgram p)).2

theorem checkRankedWFS_canonical_complete (p : ArithProgram) (hw : WFProgram p = true) :
    ∃ c, checkRankedWFS p (tWf p) (uWf p) c = true := by
  apply checkRankedWFS_complete p _ _ hw (by simp [tWf, encodeAtoms]) (by simp [uWf, encodeAtoms])
  constructor
  · exact decode_encode _ _ (fun s hs => atoms_named hw (rounds_universe _ _ s hs))
  · exact decode_encode _ _ (fun s hs => atoms_named hw (gamma_universe _ _ s hs))

@[expose] def evenCycleArith : ArithProgram := ⟨2, #[⟨0, #[], #[1]⟩, ⟨1, #[], #[0]⟩]⟩

theorem evenCycle_exec_rejected (c : ArrayCert) :
    checkRankedWFS evenCycleArith #[true,false] #[true,false] c = false := by
  cases hh : checkRankedWFS evenCycleArith #[true,false] #[true,false] c
  · rfl
  · have hs := (checkRankedWFS_sound hh).1 (atomName 0)
    have hin : atomName 0 ∈ decodeBits #[true,false] := (mem_decodeBits _ _).mpr (by simp [bit])
    have hout : atomName 0 ∉ (wf (toReasonsProgram evenCycleArith)).1 := by
      simp [wf, rounds, gamma, stage, bound, atomsOf, toReasonsProgram, toReasonsRule,
        evenCycleArith, T, fires, atomName]
    exact False.elim (hout (hs.mp hin))

open Obend.Crypto in
/-- Three quadratic equations; `z` is a separate wire, never inlined to make a cubic. -/
@[expose] def quadraticFiresGate (delta head w z : Goldilocks) : Bool :=
  decide (z = CommRingOps.sub CommRingOps.one (CommRingOps.mul delta w) ∧
    CommRingOps.mul delta z = CommRingOps.zero ∧
    CommRingOps.mul z (CommRingOps.sub CommRingOps.one head) = CommRingOps.zero)

open Obend.Crypto CommRingOps LawfulCommRing in
/-- Closure soundness needs no inverse or no-zero-divisor assumption. -/
theorem quadraticFiresGate_sound {delta head w z : Goldilocks}
    (h : quadraticFiresGate delta head w z = true) :
    (delta = zero → head = one) ∧ (delta = zero ↔ z = one) := by
  have hh := of_decide_eq_true h
  constructor
  · intro hd
    have hz : z = one := by simpa [hd, zero_mul, sub_zero] using hh.1
    have hm : sub one head = zero := by simpa [hz, one_mul] using hh.2.2
    have he := add_sub_cancel_left head (one : Goldilocks)
    simpa [hm, add_zero] using he
  · constructor
    · intro hd; simpa [hd, zero_mul, sub_zero] using hh.1
    · intro hz; simpa [hz, mul_one] using hh.2.1

open Obend.Crypto CommRingOps LawfulCommRing in
/-- Completeness with an explicit unit witness for a nonzero count. This theorem
keeps inverse existence visible instead of assuming that a ring instance is a field. -/
theorem quadraticFiresGate_complete (delta head : Goldilocks)
    (unit : delta = zero ∨ ∃ w, mul delta w = one)
    (closure : delta = zero → head = one) :
    ∃ w z, quadraticFiresGate delta head w z = true := by
  rcases unit with hz | ⟨w, hw⟩
  · refine ⟨zero, one, ?_⟩
    simp [quadraticFiresGate, hz, closure hz, zero_mul, one_mul, sub_zero, sub_self]
  · refine ⟨w, zero, ?_⟩
    simp [quadraticFiresGate, hw, sub_self, mul_zero, zero_mul]

open Obend.Crypto CommRingOps in
example : quadraticFiresGate zero one zero one = true := by
  simp [quadraticFiresGate, LawfulCommRing.zero_mul, LawfulCommRing.one_mul,
    LawfulCommRing.sub_self, LawfulCommRing.sub_zero]

open Obend.Crypto CommRingOps in
/-- The count bound prevents modular wraparound from turning a missing premise into
an apparent zero. This is separate from inverse-witness existence. -/
theorem missingCount_gate_sound (count : Nat) (head w z : Goldilocks)
    (hbound : count < Obend.Apps.ZkNtt.goldilocksPrime)
    (hgate : quadraticFiresGate (Goldilocks.ofNat count) head w z = true) :
    (z = one ↔ count = 0) ∧ (count = 0 → head = one) := by
  have hz : Goldilocks.ofNat count = zero ↔ count = 0 := by
    constructor
    · intro h
      have hv := congrArg Goldilocks.val h
      simpa [Goldilocks.ofNat, CommRingOps.zero, Goldilocks.zero, Nat.mod_eq_of_lt hbound] using hv
    · intro h; subst count; rfl
  have hh := quadraticFiresGate_sound hgate
  exact ⟨hh.2.symm.trans hz, fun h => hh.1 (hz.mpr h)⟩

example : checkRankedGLStable ⟨1, #[⟨0, #[], #[]⟩]⟩ #[true] #[0] #[0] = true := by
  simp only [checkRankedGLStable, checkRankedGamma, WFProgram, checkClosure, firesFast,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp [checkSupport, rankAt, bit, Array.mem_range]

/-- Interning is witness preparation. All facts, heads and both body polarities enter the
symbol table. The verifier consumes the resulting integer program and never scans strings. -/
def internReasonsProgram (p : Program) : Array String × ArithProgram := Id.run do
  let names := (p.facts ++ p.rules.flatMap (fun r => r.concl :: (r.pos ++ r.neg))).eraseDups.toArray
  let index := fun s => names.toList.idxOf s
  let facts := p.facts.toArray.map (fun a => ArithRule.mk (index a) #[] #[])
  let rules := p.rules.toArray.map fun r =>
    ArithRule.mk (index r.concl) (r.pos.toArray.map index) (r.neg.toArray.map index)
  return (names, ⟨names.size, facts ++ rules⟩)

/-- The semantic even-cycle refutation is universal in all ranks, not a bounded search. -/
@[expose] def evenCycleReasons : Program :=
  ⟨[], [⟨"ab", "a", [], ["b"]⟩, ⟨"ba", "b", [], ["a"]⟩]⟩

theorem evenCycle_cheating_fixpoint_rejected (c : SemanticRanks) :
    ¬ RankedWFS evenCycleReasons ["a"] ["a"] c := by
  intro h
  have h1 := h.2.1 "a" (by simp)
  have h2 := h.2.2.1.2 ⟨"ba", "b", [], ["a"]⟩ (by simp [evenCycleReasons]) (by simp)
  have hs : noLater (c.stage "a") (c.stage "b") := by simpa using h2
  rcases h1 with hf | ⟨r, hr, hc, _, hn⟩
  · cases hf
  · have hr' : r = ⟨"ab", "a", [], ["b"]⟩ ∨ r = ⟨"ba", "b", [], ["a"]⟩ := by
      simpa [evenCycleReasons] using hr
    rcases hr' with rfl | rfl
    · have hn' := (hn "b" (by simp)).2
      unfold earlier noLater at *
      omega
    · simp at hc

end Obend.SymbolicZk.Ranked
