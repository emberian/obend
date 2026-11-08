module
public import Obend.Hardware.Gpu.NttPhaseMetadata
public import Obend.Hardware.Gpu.NttFieldCorrect
public import Obend.Hardware.Gpu.NttRegisterValues
@[expose] public section
namespace Obend.Hardware.Gpu.Ntt.PhaseArithmetic
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open ArrayKernel ArrayBuild GoldilocksSource GoldilocksSourceCorrect NttFieldCorrect
open BlockNtt RegisterValues
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The actual source register array represents these canonical field values. -/
def RegValues (st : Build) (env : Nat → Word) (regs : Array Nat) (values : Nat → Nat) : Prop :=
  ∀ i, i < regs.size → FieldValue st env regs[i]! (values i)

theorem RegValues.mono {st after : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RegValues st env regs v) (he : BuildExtends st after) : RegValues after env regs v :=
  fun i hi => (h i hi).mono he

theorem RegValues.set {st : Build} {env : Nat → Word} {regs : Array Nat} {v : Nat → Nat}
    (h : RegValues st env regs v) (i r value : Nat) (hi : i < regs.size)
    (hr : FieldValue st env r value) :
    RegValues st env (regs.set! i r) (update v i value) := by
  intro j hj
  simp only [Array.size_set!] at hj
  by_cases he : i=j
  · subst j
    rw [Array.getElem!_set!_self regs i r hi]
    simpa [update] using hr
  · rw [Array.getElem!_set!_ne regs i j r he]
    simpa [update,Ne.symm he] using h j hj

/-- A concrete pair step, including optional constant-buffer input, updates
exactly the two source registers. The twiddle hypothesis concerns the fresh
loaded input register only; all arithmetic and preservation are conclusions. -/
theorem pair_correct (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (twiddle : Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hregs : RegValues st env s.2 values)
    (h0 : 2*j-j%(radix/2^(round+1)) < s.2.size)
    (h1 : 2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (htw : (stride==1 && j%(radix/2^(round+1))==0)=false →
      (env (st.lengths.size+10)).toNat=twiddle)
    (hone : (stride==1 && j%(radix/2^(round+1))==0)=true → twiddle=1) :
    let bit := radix/2^(round+1)
    let i0 := 2*j-j%bit
    let i1 := i0+bit
    let out := (PhaseMetadata.pairBody n count done radix stride k round j s).run st
    BuildExtends st out.2 ∧
      RegValues out.2 env out.1.value.2
        (update (update values i0 ((values i0+values i1)%goldilocksP)) i1
          ((((values i0+goldilocksP-values i1)%goldilocksP)*twiddle)%goldilocksP)) := by
  let bit := radix/2^(round+1)
  let di := j%bit
  let i0 := 2*j-di
  let i1 := i0+bit
  let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride))) (2^(done+round)*(n/count))
  have ha := hregs i0 h0
  have hb := hregs i1 h1
  cases hu : (stride==1 && di==0) with
  | false =>
    have h := butterfly_some st env k s.2[i0]! s.2[i1]! (values i0) (values i1)
      exponent hstart hk ha hb
    obtain ⟨result,hr⟩ : ∃ r, (butterfly k s.2[i0]! s.2[i1]! (some exponent)).run st = r := ⟨_,rfl⟩
    dsimp only at h
    rw [hr] at h
    have ht := htw hu
    have high := h.2.2.2
    rw [ht] at high
    have hv := ((hregs.mono h.1).set i0 result.1.sum _ h0 h.2.2.1).set
      i1 result.1.high _ (by simpa only [Array.size_set!] using h1) high
    dsimp only [i0,i1,di,bit,exponent] at hr hu
    dsimp only
    simp only [PhaseMetadata.pairBody,hu,Bool.false_eq_true,ite_false,bind_run,hr,h.2.1,pure_run,ForInStep.value]
    change BuildExtends st result.2 ∧ RegValues result.2 env _ _
    exact ⟨h.1,hv⟩
  | true =>
    have h := butterfly_none st env k s.2[i0]! s.2[i1]! (values i0) (values i1) hk ha hb
    obtain ⟨result,hr⟩ : ∃ r, (butterfly k s.2[i0]! s.2[i1]! none).run st = r := ⟨_,rfl⟩
    dsimp only at h
    rw [hr] at h
    have ht := hone hu
    have high := h.2.2.2
    have hv := ((hregs.mono h.1).set i0 result.1.sum _ h0 h.2.2.1).set
      i1 result.1.high _ (by simpa only [Array.size_set!] using h1) high
    dsimp only [i0,i1,di,bit] at hr hu
    dsimp only
    simp only [PhaseMetadata.pairBody,hu,ite_true,bind_run,hr,h.2.1,pure_run,ForInStep.value]
    change BuildExtends st result.2 ∧ RegValues result.2 env _ _
    simpa only [i0,i1,di,bit,ht,Nat.mul_one,Nat.mod_mod,goldilocksP,Obend.Apps.ZkNtt.goldilocksPrime] using And.intro h.1 hv

/-- Input-only agreement with the constant-buffer reads present in the actual
source action. This says nothing about any computed register or output. -/
def Twiddles (env : Nat → Word) (reads : List Read) (table : Ix → Nat) : Prop :=
  ∀ r, r ∈ reads → r.array=4 → (env r.dst).toNat=table r.index

def pairExponent (n count done radix stride round j : Nat) : Ix :=
  mulI (addI (.mod .lane stride) (.lit (j%(radix/2^(round+1))*stride)))
    (2^(done+round)*(n/count))

def pairTwiddle (n count done radix stride round j : Nat) (table : Ix → Nat) : Nat :=
  if stride==1 && j%(radix/2^(round+1))==0 then 1
  else table (pairExponent n count done radix stride round j)

theorem pair_twiddle_read (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build)
    (hu : (stride==1 && j%(radix/2^(round+1))==0)=false) :
    (⟨st.lengths.size+10,4,pairExponent n count done radix stride round j⟩ : Read) ∈
      ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 := by
  have h := (butterfly_coordinates st k
    s.2[2*j-j%(radix/2^(round+1))]!
    s.2[2*j-j%(radix/2^(round+1))+radix/2^(round+1)]!
    (some (pairExponent n count done radix stride round j))).2.2.2
  simp only [Option.map_some] at h
  dsimp only [pairExponent] at h ⊢
  simp only [PhaseMetadata.pairBody,hu,Bool.false_eq_true,ite_false,bind_run,h,pure_run,ForInStep.value]
  simp

theorem pair_values (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word) (values : Nat → Nat)
    (table : Ix → Nat) (hstart : BuildExtends {} st) (hk : ConstsAt st env k)
    (hregs : RegValues st env s.2 values)
    (h0 : 2*j-j%(radix/2^(round+1)) < s.2.size)
    (h1 : 2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 table) :
    let out := (PhaseMetadata.pairBody n count done radix stride k round j s).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.value.2
      (pairStep (radix/2^(round+1)) (pairTwiddle n count done radix stride round j table) j values) := by
  apply pair_correct n count done radix stride round j k s st env values
    (pairTwiddle n count done radix stride round j table) hstart hk hregs h0 h1
  · intro hu
    have h := hreads _ (pair_twiddle_read n count done radix stride round j k s st hu) rfl
    simpa only [pairTwiddle,hu,Bool.false_eq_true,ite_false] using h
  · intro hu
    simp only [pairTwiddle,hu,ite_true]

theorem pair_yield (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) :
    ∃ after out, (PhaseMetadata.pairBody n count done radix stride k round j s).run st = (.yield out,after) := by
  simp only [PhaseMetadata.pairBody,bind_run]
  split <;> exact ⟨_,_,rfl⟩

theorem pair_reads_mono (n count done radix stride round j : Nat) (k : GlConsts)
    (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 := by
  simp only [PhaseMetadata.pairBody,bind_run]
  split
  · exact hr
  · exact List.mem_append_left _ hr

theorem pairLoop_reads_mono (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro j ss before hh
  exact pair_reads_mono n count done radix stride round j k ss before r hh

/-- Universal refinement of the actual stateful pair loop. The only value
premise beyond its input register values binds its concrete constant reads. -/
theorem pairLoop_values (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word)
    (values : Nat → Nat) (table : Ix → Nat) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (hregs : RegValues st env s.2 values)
    (hbounds : ∀ j, j ∈ xs →
      2*j-j%(radix/2^(round+1)) < s.2.size ∧
      2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (xs.foldl (fun v j => pairStep (radix/2^(round+1))
        (pairTwiddle n count done radix stride round j table) j v) values) := by
  induction xs generalizing s st values with
  | nil =>
    simpa only [List.forIn_nil,pure_run,List.foldl_nil] using And.intro (BuildExtends.refl st) hregs
  | cons j xs ih =>
    obtain ⟨after,ss,hr⟩ := pair_yield n count done radix stride round j k s st
    have hrun : (forIn (j::xs) s (PhaseMetadata.pairBody n count done radix stride k round)).run st =
        (forIn xs ss (PhaseMetadata.pairBody n count done radix stride k round)).run after := by
      rw [List.forIn_cons,bind_run,hr]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((PhaseMetadata.pairBody n count done radix stride k round j s).run st).1.value.1 table := by
      rw [hr]
      intro r hmem ha
      exact hreads r (pairLoop_reads_mono n count done radix stride round k xs ss after r hmem) ha
    have hhead := pair_values n count done radix stride round j k s st env values table hstart hk hregs
      (hbounds j (by simp)).1 (hbounds j (by simp)).2 hheadReads
    rw [hr] at hhead
    have hsize := PhaseMetadata.pair_size n count done radix stride k round j s st
    rw [hr] at hsize
    change ss.2.size = s.2.size at hsize
    have htailBounds : ∀ j, j ∈ xs →
        2*j-j%(radix/2^(round+1)) < ss.2.size ∧
        2*j-j%(radix/2^(round+1))+radix/2^(round+1) < ss.2.size := by
      intro jj hj
      simpa only [hsize] using hbounds jj (by simp [hj])
    have htail := ih ss after
      (pairStep (radix/2^(round+1)) (pairTwiddle n count done radix stride round j table) j values)
      (hstart.trans hhead.1) (hk.mono hhead.1) hhead.2 htailBounds hreads
    dsimp only
    rw [hrun,List.foldl_cons]
    exact ⟨hhead.1.trans htail.1,htail.2⟩

theorem pairLoop_size (n count done radix stride round : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) :
    ((forIn xs s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.2.size = s.2.size := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => ss.2.size=s.2.size) _ s st rfl
  intro j ss before hh
  rw [PhaseMetadata.pair_size]
  exact hh

theorem rounds_reads_mono (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (r : Read) (hr : r ∈ s.1) :
    r ∈ ((forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st).1.1 := by
  apply PhaseMetadata.forIn_preserves xs _ (fun ss => r ∈ ss.1) _ s st hr
  intro round ss before hh
  simp only [PhaseMetadata.roundBody,bind_run,pure_run,ForInStep.value]
  exact pairLoop_reads_mono n count done radix stride round k _ ss before r hh

/-- The actual nested round loops implement the ordered mathematical field
rounds. All memory values enter only through their concrete source reads. -/
theorem rounds_values (n count done radix stride : Nat) (k : GlConsts)
    (xs : List Nat) (s : PhaseMetadata.PairState) (st : Build) (env : Nat → Word)
    (values : Nat → Nat) (table : Ix → Nat) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (hregs : RegValues st env s.2 values)
    (hbounds : ∀ round, round ∈ xs → ∀ j, j < radix/2 →
      2*j-j%(radix/2^(round+1)) < s.2.size ∧
      2*j-j%(radix/2^(round+1))+radix/2^(round+1) < s.2.size)
    (hreads : Twiddles env
      ((forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st).1.1 table) :
    let out := (forIn xs s (PhaseMetadata.roundBody n count done radix stride k)).run st
    BuildExtends st out.2 ∧ RegValues out.2 env out.1.2
      (xs.foldl (fun v round => roundValues (radix/2) (radix/2^(round+1))
        (fun j => pairTwiddle n count done radix stride round j table) v) values) := by
  induction xs generalizing s st values with
  | nil =>
    simpa only [List.forIn_nil,pure_run,List.foldl_nil] using And.intro (BuildExtends.refl st) hregs
  | cons round xs ih =>
    obtain ⟨ss,after,hr⟩ : ∃ ss after,
        (forIn (List.range (radix/2)) s (PhaseMetadata.pairBody n count done radix stride k round)).run st =
          (ss,after) := ⟨_,_,rfl⟩
    have hrun : (forIn (round::xs) s (PhaseMetadata.roundBody n count done radix stride k)).run st =
        (forIn xs ss (PhaseMetadata.roundBody n count done radix stride k)).run after := by
      simp only [List.forIn_cons,bind_run,PhaseMetadata.roundBody,pure_run,hr]
    rw [hrun] at hreads
    have hheadReads : Twiddles env
        ((forIn (List.range (radix/2)) s (PhaseMetadata.pairBody n count done radix stride k round)).run st).1.1 table := by
      rw [hr]
      intro r hmem ha
      exact hreads r (rounds_reads_mono n count done radix stride k xs ss after r hmem) ha
    have hhead := pairLoop_values n count done radix stride round k (List.range (radix/2)) s st env values table
      hstart hk hregs (fun j hj => hbounds round (by simp) j (List.mem_range.mp hj)) hheadReads
    rw [hr] at hhead
    have hsize := pairLoop_size n count done radix stride round k (List.range (radix/2)) s st
    rw [hr] at hsize
    change ss.2.size = s.2.size at hsize
    have htailBounds : ∀ rr, rr ∈ xs → ∀ j, j < radix/2 →
        2*j-j%(radix/2^(rr+1)) < ss.2.size ∧
        2*j-j%(radix/2^(rr+1))+radix/2^(rr+1) < ss.2.size := by
      intro rr hrr j hj
      simpa only [hsize] using hbounds rr (by simp [hrr]) j hj
    have htail := ih ss after
      (roundValues (radix/2) (radix/2^(round+1))
        (fun j => pairTwiddle n count done radix stride round j table) values)
      (hstart.trans hhead.1) (hk.mono hhead.1) hhead.2 htailBounds hreads
    dsimp only
    rw [hrun,List.foldl_cons]
    exact ⟨hhead.1.trans htail.1,htail.2⟩

end Obend.Hardware.Gpu.Ntt.PhaseArithmetic
end
