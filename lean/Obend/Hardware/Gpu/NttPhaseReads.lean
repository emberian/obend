module
public import Obend.Hardware.Gpu.NttPhaseMetadata
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt

/-- The invariant is required only for iterations actually present in the list. -/
theorem forIn_preserves_mem {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (P : β → Prop) (step : ∀ a, a ∈ xs → ∀ b st, P b → P ((body a b).run st).1.value)
    (b : β) (st : Build) (hb : P b) : P ((forIn xs b body).run st).1 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a (by simp) b st hb
    cases he : (body a b).run st with
    | mk result st' =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih (fun x hx => step x (by simp [hx])) out st' hp

def ReadsWhere (P : Read → Prop) (reads : List Read) : Prop := ∀ r, r ∈ reads → P r

theorem readsWhere_append (P : Read → Prop) (reads : List Read) (r : Read)
    (h : ReadsWhere P reads) (hr : P r) : ReadsWhere P (reads++[r]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · have : x=r := by simpa using hx
    subst x
    exact hr

abbrev inputExponent (n count p radix stride r : Nat) : Ix :=
  .mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n

abbrev roundExponent (n count done radix stride round j : Nat) : Ix :=
  mulI (addI (.mod .lane stride) (.lit ((j%(radix/2^(round+1)))*stride)))
    (2^(done+round)*(n/count))

/-- Exhaustive actual source read shapes. The read-register number is unrestricted
here; allocation freshness is a separate structural contract. -/
def ReadOrigin (n count p done degree src : Nat) (first : Bool) (r : Read) : Prop :=
  let radix := 2^degree
  let stride := count/(2^done*radix)
  (r.array=src ∧ ∃ slot, slot<radix ∧ r.index=phaseLoadIndex n count radix stride first slot) ∨
  (r.array=4 ∧ ∃ slot, slot<radix ∧ r.index=inputExponent n count p radix stride slot) ∨
  (r.array=4 ∧ ∃ round, round<degree ∧ ∃ pair, pair<radix/2 ∧
    r.index=roundExponent n count done radix stride round pair)

theorem load_reads_where (P : Read → Prop) (src : Nat) (index : Nat → Ix) (xs : List Nat)
    (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hload : ∀ slot, slot ∈ xs → ∀ wire, P ⟨wire,src,index slot⟩) :
    ReadsWhere P ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro slot hslot ss st hs
  simp only [loadBody,bind_run,pure_run,ForInStep.value]
  exact readsWhere_append P ss.1 _ hs (hload slot hslot _)

theorem input_reads_where (P : Read → Prop) (n count p radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ slot, slot ∈ xs → ∀ wire, P ⟨wire,4,inputExponent n count p radix stride slot⟩) :
    ReadsWhere P ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro slot hslot ss st hs
  simp only [inputBody,bind_run,pure_run,ForInStep.value]
  exact readsWhere_append P ss.1 _ hs (hread slot hslot _)

theorem butterfly_read_origin (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read=some r) :
    ∃ exponent, twiddle=some exponent ∧ r.array=4 ∧ r.index=exponent := by
  cases twiddle with
  | none => simp only [butterfly,bind_run,pure_run] at hr; cases hr
  | some exponent =>
    simp only [butterfly,bind_run,pure_run,Option.some.injEq] at hr
    exact ⟨exponent,rfl,by rw [←hr],by rw [←hr]⟩

theorem pair_reads_where (P : Read → Prop) (n count done radix stride : Nat) (k : GlConsts)
    (round j : Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ wire, P ⟨wire,4,roundExponent n count done radix stride round j⟩) :
    ReadsWhere P ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,bind_run]
  split
  · exact h
  · rename_i r hr
    apply readsWhere_append P s.1 r h
    obtain ⟨exponent,ht,ha,hi⟩ := butterfly_read_origin _ _ _ _ _ r hr
    split at ht
    · cases ht
    · simp only [Option.some.injEq] at ht
      cases r with
      | mk dst array index =>
        simp only at ha hi
        subst array
        subst index
        rw [←ht]
        exact hread dst

theorem rounds_reads_where (P : Read → Prop) (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PairState) (st : Build) (h : ReadsWhere P s.1)
    (hread : ∀ round, round ∈ xs → ∀ pair, pair < radix/2 → ∀ wire,
      P ⟨wire,4,roundExponent n count done radix stride round pair⟩) :
    ReadsWhere P ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_preserves_mem xs _ (fun ss => ReadsWhere P ss.1) _ s st h
  intro round hround ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves_mem (List.range (radix/2)) _ (fun ss => ReadsWhere P ss.1) _ ss st hs
  intro pair hpair ss st hs
  exact pair_reads_where P n count done radix stride k round pair ss st hs
    (hread round hround pair (List.mem_range.mp hpair))

/-- All reads in the sole phase builder are accounted for by its three source
read sites, with the actual loop membership bounds. -/
theorem phaseAction_reads_where (P : Read → Prop) (n count p done degree src : Nat)
    (first : Bool) (st : Build)
    (hload : ∀ slot, slot<2^degree → ∀ wire,
      P ⟨wire,src,phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first slot⟩)
    (hinput : ∀ slot, slot<2^degree → ∀ wire,
      P ⟨wire,4,inputExponent n count p (2^degree) (count/(2^done*2^degree)) slot⟩)
    (hround : ∀ round, round<degree → ∀ pair, pair<2^degree/2 → ∀ wire,
      P ⟨wire,4,roundExponent n count done (2^degree) (count/(2^done*2^degree)) round pair⟩) :
    ReadsWhere P ((phaseAction n count p done degree src first).run st).1.1 := by
  have hl := load_reads_where P src
    (phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first)
    (List.range (2^degree)) ([],#[]) st
    (by intro r hr; cases hr) (fun slot hslot => hload slot (List.mem_range.mp hslot))
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false]
  all_goals
    apply rounds_reads_where
    · first
      | apply input_reads_where
        · exact hl
        · intro slot hslot
          exact hinput slot (List.mem_range.mp hslot)
      | exact hl
    · intro round hround' pair hpair
      exact hround round (List.mem_range.mp hround') pair hpair

theorem phaseAction_read_origin (n count p done degree src : Nat) (first : Bool)
    (st : Build) (r : Read) (hr : r ∈ ((phaseAction n count p done degree src first).run st).1.1) :
    ReadOrigin n count p done degree src first r := by
  apply phaseAction_reads_where (ReadOrigin n count p done degree src first) n count p done degree src first st
    (fun slot hs wire => Or.inl ⟨rfl,slot,hs,rfl⟩)
    (fun slot hs wire => Or.inr (Or.inl ⟨rfl,slot,hs,rfl⟩))
    (fun round hr pair hp wire => Or.inr (Or.inr ⟨rfl,round,hr,pair,hp,rfl⟩)) r hr

/-- The emitted phase's actual reads have only the three exhaustively proved
source index forms. -/
theorem phase_read_origin (n count bits p done degree src dst : Nat) (first last : Bool)
    (r : Read) (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    ReadOrigin n count p done degree src first r :=
  phaseAction_read_origin n count p done degree src first {} r hr

/-- Every actual read is bounded in its declared source or full twiddle row.
All loop, lane, and transform premises are ordinary numeric shape bounds. -/
theorem phase_read_index_bound (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (hb : bits ≤ total) (h : done+degree ≤ bits)
    (hg : group < 2^total/2^bits) (hl : lane < 2^bits/2^degree)
    (r : Read) (hr : r ∈ (phase (2^total) (2^bits) bits p done degree src dst first last).reads) :
    (r.array=src ∧ r.index.eval group lane < (if first then 2^total else 2^bits)) ∨
      (r.array=4 ∧ r.index.eval group lane < 2^total) := by
  have ho := phase_read_origin (2^total) (2^bits) bits p done degree src dst first last r hr
  rcases ho with ⟨ha,slot,hslot,hi⟩ | ⟨ha,slot,hslot,hi⟩ | ⟨ha,round,hround,pair,hpair,hi⟩
  · left
    refine ⟨ha,?_⟩
    rw [hi]
    cases first with
    | false => exact phase_load_later_lt (2^total) bits done degree group lane slot h hl hslot
    | true => exact phase_load_first_lt total bits done degree group lane slot hb h hg hl hslot
  · right
    refine ⟨ha,?_⟩
    rw [hi]
    exact Nat.mod_lt _ (Nat.two_pow_pos total)
  · right
    refine ⟨ha,?_⟩
    rw [hi]
    exact phase_round_exponent_lt total bits done degree round lane pair hb h hround

end Obend.Hardware.Gpu.Ntt.PhaseMetadata
