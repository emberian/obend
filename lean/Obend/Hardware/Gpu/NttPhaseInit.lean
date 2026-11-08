module
public import Obend.Hardware.Gpu.NttPhaseArithmetic
@[expose] public section
namespace Obend.Hardware.Gpu.Ntt.PhaseInit
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open ArrayKernel ArrayBuild GoldilocksSource GoldilocksSourceCorrect NttFieldCorrect
open BlockNtt RegisterValues PhaseArithmetic
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Allocated register values before canonicalization may be arbitrary words. -/
structure RawValue (st : Build) (env : Nat → Word) (r value : Nat) : Prop where
  bound : r < st.lengths.size
  value_eq : (evalBuild st env r).toNat=value

def RawRegs (st : Build) (env : Nat → Word) (regs : Array Nat) (values : Nat → Nat) : Prop :=
  ∀ i, i < regs.size → RawValue st env regs[i]! (values i)

theorem RawValue.mono {st after : Build} {env : Nat → Word} {r value : Nat}
    (h : RawValue st env r value) (he : BuildExtends st after) : RawValue after env r value :=
  ⟨Nat.lt_of_lt_of_le h.bound he.size_le,
    (congrArg BitVec.toNat (he.frame env r h.bound)).trans h.value_eq⟩

theorem RawRegs.mono {st after : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (he : BuildExtends st after) : RawRegs after env regs v :=
  fun i hi => (h i hi).mono he

theorem RawRegs.set {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (i r value : Nat) (hi : i < regs.size)
    (hr : RawValue st env r value) : RawRegs st env (regs.set! i r) (update v i value) := by
  intro j hj
  simp only [Array.size_set!] at hj
  by_cases he : i=j
  · subst j; rw [Array.getElem!_set!_self regs i r hi]; simpa [update] using hr
  · rw [Array.getElem!_set!_ne regs i j r he]; simpa [update,Ne.symm he] using h j hj

theorem RawRegs.canonical {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RawRegs st env regs v) (hc : ∀ i, i < regs.size → v i < goldilocksP) :
    RegValues st env regs v := fun i hi => ⟨(h i hi).bound,(h i hi).value_eq,hc i hi⟩

/-- Mathematical denotation of a once-per-register preparation pass. -/
def prepareValues (xs : List Nat) (f : Nat → Nat → Nat) (v : Nat → Nat) : Nat → Nat :=
  xs.foldl (fun w i => update w i (f i (w i))) v

theorem prepareValues_at (xs : List Nat) (f : Nat → Nat → Nat) (v : Nat → Nat)
    (hn : xs.Nodup) (i : Nat) :
    prepareValues xs f v i = if i ∈ xs then f i (v i) else v i := by
  induction xs generalizing v with
  | nil => simp [prepareValues]
  | cons j xs ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [prepareValues,List.foldl_cons]
    change prepareValues xs f (update v j (f j (v j))) i = _
    rw [ih _ hn'.2]
    by_cases hi : i=j
    · subst i; simp [hn'.1,update]
    · simp [hi,update]

theorem canon_step (k : GlConsts) (r : Nat) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) (hr : r < regs.size) :
    let out := (PhaseMetadata.canonBody k r regs).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.value
      (update values r (values r%goldilocksP)) := by
  obtain ⟨result,heq⟩ : ∃ result, (glCanon 1 k regs[r]!).run st = result := ⟨_,rfl⟩
  have he := glCanon_extends st 1 k regs[r]!
  have hs := glCanon_sound st env 1 k regs[r]! (hv r hr).bound hk
  have hc := glCanon_coordinates st 1 k regs[r]!
  rw [heq] at he hs hc
  have hrval : RawValue result.2 env result.1 (values r%goldilocksP) :=
    ⟨by omega,by simpa only [(hv r hr).value_eq,goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using hs.2⟩
  simp only [PhaseMetadata.canonBody,bind_run,heq,pure_run,ForInStep.value]
  exact ⟨he,(hv.mono he).set r result.1 _ hr hrval⟩

theorem canon_loop (k : GlConsts) (xs : List Nat) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) (hb : ∀ r, r ∈ xs → r < regs.size) :
    let out := (forIn xs regs (PhaseMetadata.canonBody k)).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1
      (prepareValues xs (fun _ v => v%goldilocksP) values) := by
  induction xs generalizing st regs values with
  | nil => simpa only [List.forIn_nil,pure_run,prepareValues,List.foldl_nil] using And.intro (BuildExtends.refl st) hv
  | cons r xs ih =>
    obtain ⟨result,heq⟩ : ∃ result, (glCanon 1 k regs[r]!).run st = result := ⟨_,rfl⟩
    have hstep := canon_step k r regs st env values hk hv (hb r (by simp))
    simp only [PhaseMetadata.canonBody,bind_run,heq,pure_run,ForInStep.value] at hstep
    have htail := ih (regs.set! r result.1) result.2 (update values r (values r%goldilocksP))
      (hk.mono hstep.1) hstep.2 (fun i hi => by simpa only [Array.size_set!] using hb i (by simp [hi]))
    simp only [List.forIn_cons,bind_run,PhaseMetadata.canonBody,heq,pure_run,prepareValues,List.foldl_cons]
    exact ⟨hstep.1.trans htail.1,htail.2⟩

theorem canon_all (k : GlConsts) (regs : Array Nat) (st : Build)
    (env : Nat → Word) (values : Nat → Nat) (hk : ConstsAt st env k)
    (hv : RawRegs st env regs values) :
    let out := (forIn (List.range regs.size) regs (PhaseMetadata.canonBody k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1 (fun i => values i%goldilocksP) := by
  have h := canon_loop k (List.range regs.size) regs st env values hk hv (fun _ hi => List.mem_range.mp hi)
  have hsize := PhaseMetadata.canon_size k (List.range regs.size) regs st
  refine ⟨h.1,?_⟩
  intro i hi
  have hib : i < regs.size := by simpa only [hsize] using hi
  have hr := h.2 i hi
  have hp := prepareValues_at (List.range regs.size) (fun _ v => v%goldilocksP) values
    List.nodup_range i
  simp only [List.mem_range,if_pos hib] at hp
  rw [hp] at hr
  exact ⟨hr.bound,hr.value_eq,Nat.mod_lt _ (by decide)⟩

def inputExponent (n count p radix stride r : Nat) : Ix :=
  .mod (.mul (phaseIndex radix stride r) (mulI (.mod .group p) (n/count/p))) n

theorem input_step (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values) (hr : r < s.2.size)
    (hreads : Twiddles env
      ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 table) :
    let out := (PhaseMetadata.inputBody n count p radix stride k r s).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.value.2
      (update values r ((values r*table (inputExponent n count p radix stride r))%goldilocksP)) := by
  let tw := (newWire 1).run st
  obtain ⟨result,heq⟩ : ∃ result, (glMul 1 k s.2[r]! tw.1).run tw.2 = result := ⟨_,rfl⟩
  have ht := newWire_extends st 1
  have hm := glMul_extends tw.2 1 k s.2[r]! tw.1
  have hc := glMul_coordinates tw.2 1 k s.2[r]! tw.1
  have htw : tw.1 < tw.2.lengths.size := by simp [tw,newWire_run]
  have ha := (hv r hr).mono ht
  have hs := glMul_sound tw.2 env 1 k s.2[r]! tw.1 ha.bound htw (hk.mono ht)
  rw [heq] at hm hc hs
  dsimp only [tw] at heq
  have hread : (env tw.1).toNat=table (inputExponent n count p radix stride r) := by
    apply hreads ⟨tw.1,4,inputExponent n count p radix stride r⟩ _ rfl
    simp only [PhaseMetadata.inputBody,bind_run,heq,pure_run,ForInStep.value]
    simp [tw,inputExponent]
  have htv : evalBuild tw.2 env tw.1 = env tw.1 := by
    change evalBuild st env tw.1 = env tw.1
    exact hstart.fresh_value env tw.1 (by simp [tw,newWire_run])
  have hraw : RawValue result.2 env result.1
      ((values r*table (inputExponent n count p radix stride r))%goldilocksP) := by
    refine ⟨by omega,?_⟩
    have haValue : (evalBuild tw.2 env s.2[r]!).toNat=values r := ha.value_eq
    rw [haValue,htv,hread] at hs
    simpa only [goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using hs.2
  simp only [PhaseMetadata.inputBody,bind_run,heq,pure_run,ForInStep.value]
  exact ⟨ht.trans hm,(hv.mono (ht.trans hm)).set r result.1 _ hr hraw⟩

theorem input_reads_mono (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) (read : Read) (hr : read ∈ s.1) :
    read ∈ ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 := by
  simp only [PhaseMetadata.inputBody,bind_run,pure_run,ForInStep.value]
  exact List.mem_append_left _ hr

theorem inputLoop_reads_mono (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro j ss before hh
  exact input_reads_mono n count p radix stride k j ss before r hh

theorem input_yield (n count p radix stride : Nat) (k : GlConsts) (r : Nat)
    (s : PhaseMetadata.PairState) (st : Build) :
    ∃ after out, (PhaseMetadata.inputBody n count p radix stride k r s).run st = (.yield out,after) := by
  simp only [PhaseMetadata.inputBody,bind_run,pure_run]
  exact ⟨_,_,rfl⟩

theorem input_loop (n count p radix stride : Nat) (k : GlConsts) (xs : List Nat)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values) (hb : ∀ r, r ∈ xs → r < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.inputBody n count p radix stride k)).run st
    BuildExtends st out.2 ∧ RawRegs out.2 env out.1.2
      (prepareValues xs (fun r v => (v*table (inputExponent n count p radix stride r))%goldilocksP) values) := by
  induction xs generalizing st s values with
  | nil => simpa only [List.forIn_nil,pure_run,prepareValues,List.foldl_nil] using And.intro (BuildExtends.refl st) hv
  | cons r xs ih =>
    obtain ⟨after,ss,heq⟩ := input_yield n count p radix stride k r s st
    have hrun : (forIn (r::xs) s (PhaseMetadata.inputBody n count p radix stride k)).run st =
        (forIn xs ss (PhaseMetadata.inputBody n count p radix stride k)).run after := by
      rw [List.forIn_cons,bind_run,heq]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((PhaseMetadata.inputBody n count p radix stride k r s).run st).1.value.1 table := by
      rw [heq]
      intro read hmem ha
      exact hreads read (inputLoop_reads_mono n count p radix stride k xs ss after read hmem) ha
    have hstep := input_step n count p radix stride k r s st env values table hstart hk hv
      (hb r (by simp)) hheadReads
    rw [heq] at hstep
    have hsize : ss.2.size=s.2.size := by
      have h := PhaseMetadata.input_size n count p radix stride k [r] s st
      simpa only [List.forIn_cons,bind_run,heq,List.forIn_nil,pure_run] using h
    have htail := ih ss after (update values r ((values r*table (inputExponent n count p radix stride r))%goldilocksP))
      (hstart.trans hstep.1) (hk.mono hstep.1) hstep.2
      (fun i hi => by simpa only [hsize] using hb i (by simp [hi])) hreads
    dsimp only
    rw [hrun]
    exact ⟨hstep.1.trans htail.1,htail.2⟩

theorem input_all (n count p radix stride : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hv : RawRegs st env s.2 values)
    (hreads : Twiddles env
      ((forIn (List.range s.2.size) s (PhaseMetadata.inputBody n count p radix stride k)).run st).1.1 table) :
    let out := (forIn (List.range s.2.size) s (PhaseMetadata.inputBody n count p radix stride k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (fun i => (values i*table (inputExponent n count p radix stride i))%goldilocksP) := by
  have h := input_loop n count p radix stride k (List.range s.2.size) s st env values table hstart hk hv
    (fun _ hi => List.mem_range.mp hi) hreads
  have hsize := PhaseMetadata.input_size n count p radix stride k (List.range s.2.size) s st
  refine ⟨h.1,?_⟩
  intro i hi
  have hib : i < s.2.size := by simpa only [hsize] using hi
  have hr := h.2 i hi
  have hp := prepareValues_at (List.range s.2.size)
    (fun r v => (v*table (inputExponent n count p radix stride r))%goldilocksP) values
    List.nodup_range i
  simp only [List.mem_range,if_pos hib] at hp
  rw [hp] at hr
  exact ⟨hr.bound,hr.value_eq,Nat.mod_lt _ (by decide)⟩

/-- The exact initial load loop of the source, before constants or arithmetic. -/
abbrev initialLoads (n count done degree src : Nat) (first : Bool) : PhaseMetadata.PairState × Build :=
  (forIn (List.range (2^degree)) ([],#[])
    (PhaseMetadata.loadBody src (phaseLoadIndex n count (2^degree)
      (count/(2^done*2^degree)) first))).run {}

def preparedValues (n count p done degree : Nat) (first : Bool)
    (inputs : Nat → Nat) (table : Ix → Nat) : Nat → Nat :=
  if first then
    if p=1 then fun i => inputs i%goldilocksP
    else fun i => (inputs i*table (inputExponent n count p (2^degree) (count/(2^done*2^degree)) i))%goldilocksP
  else inputs

def roundResultValues (n count done degree : Nat) (table : Ix → Nat) (values : Nat → Nat) : Nat → Nat :=
  (List.range degree).foldl (fun v round => roundValues (2^degree/2) (2^degree/2^(round+1))
    (fun j => pairTwiddle n count done (2^degree) (count/(2^done*2^degree)) round j table) v) values

def phaseResultValues (n count p done degree : Nat) (first : Bool)
    (inputs : Nat → Nat) (table : Ix → Nat) : Nat → Nat :=
  roundResultValues n count done degree table (preparedValues n count p done degree first inputs table)

theorem initialLoads_extends (n count done degree src : Nat) (first : Bool) :
    BuildExtends {} (initialLoads n count done degree src first).2 := by
  apply forIn_extends
  intro r s st
  simpa only [PhaseMetadata.loadBody,bind_run,pure_run] using newWire_extends st 1

theorem initialLoads_size (n count done degree src : Nat) (first : Bool) :
    (initialLoads n count done degree src first).1.2.size = 2^degree := by
  simpa only [Array.size_empty,List.length_range,Nat.zero_add] using
    PhaseMetadata.load_size src (phaseLoadIndex n count (2^degree) (count/(2^done*2^degree)) first)
      (List.range (2^degree)) ([],#[]) {}

theorem finish_rounds (n count done degree : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hvalues : RegValues st env s.2 values) (hsize : s.2.size=2^degree)
    (hreads : Twiddles env ((forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st).1.1 table) :
    let out := (forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st
    BuildExtends {} out.2 ∧ ∀ i, i < 2^degree →
      FieldValue out.2 env out.1.2.toList[i]! (roundResultValues n count done degree table values i) := by
  have hr := rounds_values n count done (2^degree) (count/(2^done*2^degree)) k
    (List.range degree) s st env values table hstart hk hvalues
    (fun round hround j hj => by rw [hsize]; exact phase_register_bounds degree round j (List.mem_range.mp hround) hj)
    hreads
  refine ⟨hstart.trans hr.1,?_⟩
  intro i hi
  have hsz := PhaseMetadata.rounds_size n count done (2^degree) (count/(2^done*2^degree)) k
    (List.range degree) s st
  have hib : i < ((forIn (List.range degree) s
      (PhaseMetadata.roundBody n count done (2^degree) (count/(2^done*2^degree)) k)).run st).1.2.size := by
    rw [hsz,hsize]; exact hi
  simpa only [Array.getElem!_toList,roundResultValues] using hr.2 i hib

/-- Full source-action arithmetic refinement. The premises concern only the
loaded inputs and concrete constant-buffer reads; every computed register and
output follows from the actual shared field builders and actual source loops. -/
theorem phaseAction_values (n count p done degree src : Nat) (first : Bool)
    (env : Nat → Word) (inputs : Nat → Nat) (table : Ix → Nat) (hp : 0 < p)
    (hinputs : RawRegs (initialLoads n count done degree src first).2 env
      (initialLoads n count done degree src first).1.2 inputs)
    (hcanonical : first=false → ∀ i, i < 2^degree → inputs i < goldilocksP)
    (hreads : Twiddles env ((phaseAction n count p done degree src first).run {}).1.1 table) :
    let out := (phaseAction n count p done degree src first).run {}
    BuildExtends {} out.2 ∧ ∀ i, i < 2^degree →
      FieldValue out.2 env out.1.2[i]! (phaseResultValues n count p done degree first inputs table i) := by
  let loaded := initialLoads n count done degree src first
  let constants := (glConsts 1).run loaded.2
  have hl := initialLoads_extends n count done degree src first
  have hc := glConsts_extends loaded.2 1 (by decide)
  have hk := glConsts_sound loaded.2 env 1 (by decide)
  have hs := initialLoads_size n count done degree src first
  have hraw := hinputs.mono hc
  cases first with
  | false =>
    have hv : RegValues constants.2 env loaded.1.2 inputs := hraw.canonical (by
      intro i hi
      apply hcanonical rfl i
      simpa only [hs] using hi)
    have hrun := PhaseMetadata.phaseAction_run n count p done degree src false {}
    simp only [Bool.false_and,Bool.false_eq_true,ite_false] at hrun
    rw [hrun] at hreads ⊢
    exact finish_rounds n count done degree constants.1 loaded.1 constants.2 env inputs table
      (hl.trans hc) hk hv hs hreads
  | true =>
    by_cases hp1 : p=1
    · subst p
      let canonical := (forIn (List.range (2^degree)) loaded.1.2 (PhaseMetadata.canonBody constants.1)).run constants.2
      have hcan := canon_all constants.1 loaded.1.2 constants.2 env inputs hk hraw
      have hs' : loaded.1.2.size=2^degree := hs
      rw [hs'] at hcan
      have hcs := PhaseMetadata.canon_size constants.1 (List.range (2^degree)) loaded.1.2 constants.2
      have hrun := PhaseMetadata.phaseAction_run n count 1 done degree src true {}
      simp only [Bool.true_and,Nat.reduceBEq,show decide (1>1)=false by decide,Bool.false_eq_true,ite_true,ite_false] at hrun
      rw [hrun] at hreads ⊢
      have hf := finish_rounds n count done degree constants.1 (loaded.1.1,canonical.1) canonical.2 env
        (fun i => inputs i%goldilocksP) table ((hl.trans hc).trans hcan.1) (hk.mono hcan.1) hcan.2
        (hcs.trans hs') hreads
      simpa only [phaseResultValues,preparedValues,ite_true] using hf
    · have hpgt : 1 < p := by omega
      let twisted := (forIn (List.range (2^degree)) loaded.1
        (PhaseMetadata.inputBody n count p (2^degree) (count/(2^done*2^degree)) constants.1)).run constants.2
      have hrun := PhaseMetadata.phaseAction_run n count p done degree src true {}
      have hpne : (p==1)=false := by exact beq_eq_false_iff_ne.mpr hp1
      have hpg : decide (p>1)=true := decide_eq_true hpgt
      simp only [Bool.true_and,hpne,Bool.false_eq_true,hpg,ite_true,ite_false] at hrun
      rw [hrun] at hreads ⊢
      have htwreads : Twiddles env twisted.1.1 table := by
        intro r hmem ha
        exact hreads r (rounds_reads_mono n count done (2^degree) (count/(2^done*2^degree))
          constants.1 (List.range degree) twisted.1 twisted.2 r hmem) ha
      have htw := input_all n count p (2^degree) (count/(2^done*2^degree)) constants.1 loaded.1 constants.2
        env inputs table (hl.trans hc) hk hraw (by rw [show loaded.1.2.size=2^degree from hs]; exact htwreads)
      have hs' : loaded.1.2.size=2^degree := hs
      rw [hs'] at htw
      have hts := PhaseMetadata.input_size n count p (2^degree) (count/(2^done*2^degree)) constants.1
        (List.range (2^degree)) loaded.1 constants.2
      have hf := finish_rounds n count done degree constants.1 twisted.1 twisted.2 env
        (fun i => (inputs i*table (inputExponent n count p (2^degree) (count/(2^done*2^degree)) i))%goldilocksP)
        table ((hl.trans hc).trans htw.1) (hk.mono htw.1) htw.2 (hts.trans hs') hreads
      simpa only [phaseResultValues,preparedValues,ite_true,hp1,ite_false] using hf

end Obend.Hardware.Gpu.Ntt.PhaseInit
end
