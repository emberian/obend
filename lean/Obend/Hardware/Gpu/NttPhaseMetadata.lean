module
public import Obend.Hardware.Gpu.NttPhaseIndex
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.PhaseMetadata
open ArrayKernel ArrayBuild GoldilocksSource BlockNtt

theorem bind_run {α β : Type} (x : BuildM α) (f : α → BuildM β) (st : Build) :
    (x >>= f).run st = (f (x.run st).1).run (x.run st).2 := rfl

theorem pure_run {α : Type} (x : α) (st : Build) :
    (pure x : BuildM α).run st = (x,st) := rfl

/-- Structural invariants of the actual source's stateful loops. The underlying
arithmetic builder is unrestricted; only the returned loop state is observed. -/
theorem forIn_preserves {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (P : β → Prop) (step : ∀ a b st, P b → P ((body a b).run st).1.value)
    (b : β) (st : Build) (hb : P b) : P ((forIn xs b body).run st).1 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st hb
    cases he : (body a b).run st with
    | mk result st' =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih out st' hp

/-- A yielding loop whose visible measure increments once per iteration. -/
theorem forIn_measure {α β : Type} (xs : List α) (body : α → β → BuildM (ForInStep β))
    (measure : β → Nat)
    (step : ∀ a b st, ∃ out st', (body a b).run st = (.yield out,st') ∧ measure out = measure b+1)
    (b : β) (st : Build) : measure ((forIn xs b body).run st).1 = measure b+xs.length := by
  induction xs generalizing b st with
  | nil => simp only [List.forIn_nil,pure_run,List.length_nil,Nat.add_zero]
  | cons a xs ih =>
    obtain ⟨out,st',he,hm⟩ := step a b st
    rw [List.forIn_cons,bind_run,he]
    change measure ((forIn xs out body).run st').1 = _
    rw [ih,hm,List.length_cons]
    omega

abbrev PairState := List Read × Array Nat

def GoodReads (src : Nat) (reads : List Read) : Prop :=
  ∀ r, r ∈ reads → r.array=src ∨ r.array=4

theorem goodReads_append (src : Nat) (reads : List Read) (r : Read)
    (h : GoodReads src reads) (hr : r.array=src ∨ r.array=4) : GoodReads src (reads++[r]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · have : x=r := by simpa using hx
    subst x
    exact hr

/-- Proof-side names for the exact loop bodies elaborated from `phaseAction`.
They are abbreviations, and the action equation below ties them to that sole
source construction. No alternative runtime NTT construction is introduced. -/
abbrev loadBody (src : Nat) (index : Nat → Ix) (r : Nat) (s : PairState) : BuildM (ForInStep PairState) := do
  let a ← newWire 1
  pure (.yield (s.1++[⟨a,src,index r⟩],s.2.push a))

abbrev canonBody (k : GlConsts) (r : Nat) (regs : Array Nat) : BuildM (ForInStep (Array Nat)) := do
  let a ← glCanon 1 k regs[r]!
  pure (.yield (regs.set! r a))

abbrev inputBody (n count p radix stride : Nat) (k : GlConsts) (r : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let tw ← newWire 1
  let exponent := Ix.mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n
  let v ← glMul 1 k s.2[r]! tw
  pure (.yield (s.1++[⟨tw,4,exponent⟩],s.2.set! r v))

abbrev pairBody (n count done radix stride : Nat) (k : GlConsts) (round j : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let bit := radix/2^(round+1)
  let di := j%bit
  let i0 := 2*j-di
  let i1 := i0+bit
  let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride))) (2^(done+round)*(n/count))
  let result ← butterfly k s.2[i0]! s.2[i1]!
    (if stride==1 && di==0 then none else some exponent)
  match result.read with
  | none => pure (.yield (s.1,(s.2.set! i0 result.sum).set! i1 result.high))
  | some r => pure (.yield (s.1++[r],(s.2.set! i0 result.sum).set! i1 result.high))

abbrev roundBody (n count done radix stride : Nat) (k : GlConsts) (round : Nat) (s : PairState) :
    BuildM (ForInStep PairState) := do
  let s ← forIn (List.range (radix/2)) s (pairBody n count done radix stride k round)
  pure (.yield s)

theorem load_size (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (loadBody src index)).run st).1.2.size = s.2.size+xs.length := by
  apply forIn_measure xs (loadBody src index) (fun s => s.2.size)
  intro r s st
  refine ⟨_,_,rfl,?_⟩
  simp

theorem load_reads (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build)
    (h : GoodReads src s.1) : GoodReads src ((forIn xs s (loadBody src index)).run st).1.1 := by
  apply forIn_preserves xs (loadBody src index) (fun s => GoodReads src s.1) _ s st h
  intro r s st hs
  simp only [loadBody,bind_run,pure_run,ForInStep.value]
  exact goodReads_append src s.1 _ hs (Or.inl rfl)

theorem canon_size (k : GlConsts) (xs : List Nat) (regs : Array Nat) (st : Build) :
    ((forIn xs regs (canonBody k)).run st).1.size = regs.size := by
  apply forIn_preserves xs (canonBody k) (fun rs => rs.size=regs.size) _ regs st rfl
  intro r rs st hs
  simpa only [canonBody,bind_run,pure_run,ForInStep.value,Array.size_set!] using hs

theorem input_size (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (inputBody n count p radix stride k)).run st).1.2.size = s.2.size := by
  apply forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro r ss st hs
  simpa only [inputBody,bind_run,pure_run,ForInStep.value,Array.size_set!] using hs

theorem input_reads (src n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((forIn xs s (inputBody n count p radix stride k)).run st).1.1 := by
  apply forIn_preserves xs _ (fun ss => GoodReads src ss.1) _ s st h
  intro r ss st hs
  simp only [inputBody,bind_run,pure_run,ForInStep.value]
  exact goodReads_append src ss.1 _ hs (Or.inr rfl)

theorem butterfly_read (k : GlConsts) (a b : Nat) (twiddle : Option Ix) (st : Build)
    (r : Read) (hr : ((butterfly k a b twiddle).run st).1.read = some r) : r.array=4 := by
  cases twiddle with
  | none => simp only [butterfly,bind_run,pure_run] at hr; cases hr
  | some exponent =>
    simp only [butterfly,bind_run,pure_run,Option.some.injEq] at hr
    rw [←hr]

theorem pair_size (n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) :
    ((pairBody n count done radix stride k round j s).run st).1.value.2.size = s.2.size := by
  simp only [pairBody,bind_run]
  split <;> simp only [pure_run,ForInStep.value,Array.size_set!]

theorem pair_reads (src n count done radix stride : Nat) (k : GlConsts) (round j : Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [pairBody,bind_run]
  split
  · exact h
  · rename_i r hr
    apply goodReads_append src s.1 r h
    exact Or.inr (butterfly_read _ _ _ _ _ r hr)

theorem rounds_size (n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) :
    ((forIn xs s (roundBody n count done radix stride k)).run st).1.2.size = s.2.size := by
  apply forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro round ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves (List.range (radix/2)) _ (fun ss => ss.2.size=s.2.size) _ ss st hs
  intro j ss st hs
  rw [pair_size]
  exact hs

theorem rounds_reads (src n count done radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PairState) (st : Build) (h : GoodReads src s.1) :
    GoodReads src ((forIn xs s (roundBody n count done radix stride k)).run st).1.1 := by
  apply forIn_preserves xs _ (fun ss => GoodReads src ss.1) _ s st h
  intro round ss st hs
  simp only [roundBody,bind_run,pure_run,ForInStep.value]
  apply forIn_preserves (List.range (radix/2)) _ (fun ss => GoodReads src ss.1) _ ss st hs
  exact fun j ss st hs => pair_reads src n count done radix stride k round j ss st hs

/-- Definitional decomposition of the sole source action into its actual loops.
This is a proof interface; each loop retains the original source body. -/
theorem phaseAction_run (n count p done degree src : Nat) (first : Bool) (st : Build) :
    (phaseAction n count p done degree src first).run st =
    let radix := 2^degree
    let stride := count/(2^done*radix)
    let loaded := (forIn (List.range radix) ([],#[])
      (loadBody src (phaseLoadIndex n count radix stride first))).run st
    let constants := (glConsts 1).run loaded.2
    let canonical := if first && p==1 then
      (forIn (List.range radix) loaded.1.2 (canonBody constants.1)).run constants.2
      else (loaded.1.2,constants.2)
    let twisted := if first && p>1 then
      (forIn (List.range radix) (loaded.1.1,canonical.1)
        (inputBody n count p radix stride constants.1)).run canonical.2
      else ((loaded.1.1,canonical.1),canonical.2)
    let transformed := (forIn (List.range degree) twisted.1
      (roundBody n count done radix stride constants.1)).run twisted.2
    ((transformed.1.1,transformed.1.2.toList),transformed.2) := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction,hc,ht,Bool.false_eq_true,ite_true,ite_false,bind_run,pure_run] <;> rfl

/-- Every source action emits one output register per radix position. -/
theorem phaseAction_length (n count p done degree src : Nat) (first : Bool) (st : Build) :
    ((phaseAction n count p done degree src first).run st).1.2.length = 2^degree := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp [phaseAction_run,hc,ht,rounds_size,input_size,canon_size,load_size]

/-- Reads added by any source phase are exactly input or twiddle-array reads. -/
theorem phaseAction_reads (n count p done degree src : Nat) (first : Bool) (st : Build) :
    GoodReads src ((phaseAction n count p done degree src first).run st).1.1 := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false] <;>
    apply rounds_reads
  all_goals first | apply input_reads | skip
  all_goals
    apply load_reads
    intro r hr
    cases hr

/-- Actual emitted phase width, discharged from construction rather than an
admission oracle. -/
theorem phase_writes_length (n count bits p done degree src dst : Nat) (first last : Bool) :
    (phase n count bits p done degree src dst first last).writes.length = 2^degree := by
  change (((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).length = _
  simp only [List.length_map,List.length_zipIdx,phaseAction_length]


end Obend.Hardware.Gpu.Ntt.PhaseMetadata
