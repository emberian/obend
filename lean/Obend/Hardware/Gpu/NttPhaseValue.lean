module
public import Obend.Hardware.Gpu.NttPhaseStages
public import Obend.Hardware.Gpu.NttReadAllocation
public import Obend.Hardware.Gpu.NttPhaseInit
public import Obend.Hardware.Gpu.NttLoadCorrect
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open ArrayHypergraph ArrayKernel ArrayBuild GoldilocksSource BlockNtt
open PhaseMetadata PhaseArithmetic NttFieldCorrect

/-- The actual phase loader supplies the initial environment of its emitted code. -/
def phaseEnv (ph : Phase) (mem : Memory) (group lane : Nat) : Nat → Word :=
  fun wire => (loadRegisters ph mem group lane).getD wire 0#64

theorem phaseEnv_read (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane : Nat) (r : Read)
    (hr : r ∈ (phase n count bits p done degree src dst first last).reads) :
    phaseEnv (phase n count bits p done degree src dst first last) mem group lane r.dst =
      (mem.getD r.array #[]).getD (r.index.eval group lane) 0#64 :=
  phase_loadRegisters_value n count bits p done degree src dst first last mem group lane r hr

/-- Actual HashMap execution and the actual builder interpreter are the same
register program, with the actual loaded environment. -/
theorem phase_runRegisters (n count bits p done degree src dst : Nat) (first last : Bool)
    (mem : Memory) (group lane wire : Nat) :
    (runRegisters (phase n count bits p done degree src dst first last).code
      (loadRegisters (phase n count bits p done degree src dst first last) mem group lane)).getD wire 0#64 =
    evalBuild ((phaseAction n count p done degree src first).run {}).2
      (phaseEnv (phase n count bits p done degree src dst first last) mem group lane) wire := by
  exact runRegisters_sound _ _ wire

/-- The actual loader discharges the register arithmetic's input-only twiddle
agreement from the actual constant buffer. No computed-value premise is used. -/
theorem phaseEnv_twiddles (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (hb : bits≤total) (hdegree : done+degree≤bits)
    (hg : group<2^total/2^bits) (hl : lane<2^bits/2^degree)
    (htable : ∀ i, i<2^total → ((mem.getD 4 #[]).getD i 0#64).toNat = modPow (rootOfUnity (2^total)) i) :
    Twiddles (phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)
      ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.1
      (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane)) := by
  intro r hr ha
  have hm : r ∈ (phase (2^total) (2^bits) bits p done degree src dst first last).reads := hr
  have hbounds := phase_read_index_bound total bits p done degree src dst group lane first last
    hb hdegree hg hl r hm
  have hi : r.index.eval group lane < 2^total := by
    rcases hbounds with ⟨_,hi⟩ | ⟨_,hi⟩
    · have hs : (if first then 2^total else 2^bits) ≤ 2^total := by
        split
        · exact Nat.le_refl _
        · exact Nat.pow_le_pow_of_le (by decide) hb
      exact Nat.lt_of_lt_of_le hi hs
    · exact hi
  rw [phaseEnv_read _ _ _ _ _ _ _ _ _ _ _ _ _ r hm,ha]
  exact htable _ hi

/-- Initial source loads remain in the final phase's read list. -/
theorem phase_initial_read_mem (n count p done degree src : Nat) (first : Bool) (r : Read)
    (hr : r ∈ (PhaseInit.initialLoads n count done degree src first).1.1) :
    r ∈ ((phaseAction n count p done degree src first).run {}).1.1 := by
  by_cases hc : (first && p==1)=true <;> by_cases ht : (first && decide (p>1))=true <;>
    simp only [phaseAction_run,hc,ht,Bool.false_eq_true,ite_true,ite_false]
  all_goals
    apply rounds_reads_mono
    first
    | apply PhaseInit.inputLoop_reads_mono; exact hr
    | exact hr

/-- The real input loader supplies the raw register values required by the
shared arithmetic proof; initial allocation emits no arithmetic instructions. -/
theorem phase_initial_raw (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (hdegree : done+degree≤bits) (hlane : lane<2^bits/2^degree)
    (hentry : ∀ i, i<2^bits →
      ((mem.getD src #[]).getD (if first then group+i*(2^total/2^bits) else i) 0#64).toNat=entry i) :
    PhaseInit.RawRegs (PhaseInit.initialLoads (2^total) (2^bits) done degree src first).2
      (phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)
      (PhaseInit.initialLoads (2^total) (2^bits) done degree src first).1.2
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) := by
  let loaded := PhaseInit.initialLoads (2^total) (2^bits) done degree src first
  intro r hr
  have hs := PhaseInit.initialLoads_size (2^total) (2^bits) done degree src first
  have hrr : r<2^degree := by simpa only [hs] using hr
  have hget : loaded.1.2.getD r 0 = loaded.1.2[r]! := by
    simp [Array.getD_eq_getD_getElem?,show r<loaded.1.2.size from hr]
  have hm := NttLoadCorrect.load_reg_read src
    (phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first)
    (2^degree) {} r hrr
  change (⟨loaded.1.2.getD r 0,src,
    phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first r⟩ : Read) ∈ loaded.1.1 at hm
  rw [hget] at hm
  have hfinal := phase_initial_read_mem (2^total) (2^bits) p done degree src first _ hm
  have halloc : ReadAllocation loaded.2 loaded.1.1 :=
    load_allocation src _ _ ([],#[]) {} ⟨by simp,by intro r hr; cases hr⟩
  refine ⟨halloc.bound _ hm,?_⟩
  have he := NttLoadCorrect.load_edges src
    (phaseLoadIndex (2^total) (2^bits) (2^degree) (2^bits/(2^done*2^degree)) first)
    (List.range (2^degree)) ([],#[]) ({} : Build)
  change loaded.2.edges = #[] at he
  have hcode : ∀ env wire, evalBuild loaded.2 env wire=env wire := by
    intro env wire
    simp [evalBuild,registerCode,he,ArrayHypergraph.runCode]
  rw [hcode]
  have henv := phaseEnv_read (2^total) (2^bits) bits p done degree src dst first last mem group lane _ hfinal
  rw [henv,phaseLoadIndex_eval]
  exact hentry _ (phase_index_lt bits done degree lane r hdegree hlane hrr)

/-- The source action's mathematical result is exactly the fused whole-tile
stage result, including the actual first-phase input preparation. -/
theorem phaseResultValues_stages (total bits p done degree group lane : Nat)
    (first : Bool) (entry : Nat → Nat) (ht : total≤32) (hb : bits≤total)
    (hdegree : done+degree≤bits) (hlane : lane<2^bits/2^degree)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP) :
    ∀ r, r<2^degree →
    PhaseInit.phaseResultValues (2^total) (2^bits) p done degree first
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
      (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane)) r =
      difStages bits done degree (preparedInput (2^total) (2^bits) p group first entry)
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  unfold PhaseInit.phaseResultValues PhaseInit.roundResultValues
  apply phase_rounds_stages total bits done degree degree group lane ht hb hdegree (Nat.le_refl _) hlane
  · intro r hr
    have h := prepared_register_eq total bits p done degree group lane r first entry
      (fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) ht rfl
    cases first <;> by_cases hp1 : p=1 <;>
      simpa [PhaseInit.preparedValues,PhaseInit.inputExponent,PhaseMetadata.inputExponent,mulMod,hp1] using h
  · exact preparedInput_canonical _ _ _ _ _ first entry hcanonical

/-- Actual emitted register execution has the exact fused DIF value. All
premises concern transform shape, input memory, and the initial twiddle table. -/
theorem phase_register_value (total bits p done degree src dst group lane : Nat)
    (first last : Bool) (mem : Memory) (entry : Nat → Nat)
    (ht : total≤32) (hb : bits≤total) (hp : 0<p) (hdegree : done+degree≤bits)
    (hg : group<2^total/2^bits) (hlane : lane<2^bits/2^degree)
    (hentry : ∀ i, i<2^bits →
      ((mem.getD src #[]).getD (if first then group+i*(2^total/2^bits) else i) 0#64).toNat=entry i)
    (hcanonical : first=false → ∀ i, i<2^bits → entry i<goldilocksP)
    (htable : ∀ i, i<2^total → ((mem.getD 4 #[]).getD i 0#64).toNat=modPow (rootOfUnity (2^total)) i)
    (r : Nat) (hr : r<2^degree) :
    ((runRegisters (phase (2^total) (2^bits) bits p done degree src dst first last).code
      (loadRegisters (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane)).getD
      (((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.getD r 0) 0#64).toNat =
      difStages bits done degree (preparedInput (2^total) (2^bits) p group first entry)
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  let env := phaseEnv (phase (2^total) (2^bits) bits p done degree src dst first last) mem group lane
  let inputs := fun r => entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)
  let table := fun (ix : Ix) => modPow (rootOfUnity (2^total)) (ix.eval group lane)
  have hraw := phase_initial_raw total bits p done degree src dst group lane first last mem entry hdegree hlane hentry
  have htw := phaseEnv_twiddles total bits p done degree src dst group lane first last mem hb hdegree hg hlane htable
  have hv := PhaseInit.phaseAction_values (2^total) (2^bits) p done degree src first env inputs table hp hraw
    (fun hf i hi => hcanonical hf _ (phase_index_lt bits done degree lane i hdegree hlane hi)) htw
  have hfield := hv.2 r hr
  have hget : ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.getD r 0 =
      ((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2[r]! := by
    have hlen := phaseAction_length (2^total) (2^bits) p done degree src first {}
    simp [List.getD_eq_getElem?_getD,show r<((phaseAction (2^total) (2^bits) p done degree src first).run {}).1.2.length by omega]
  rw [hget,phase_runRegisters]
  rw [hfield.value_eq]
  exact phaseResultValues_stages total bits p done degree group lane first entry ht hb hdegree hlane hcanonical r hr

end Obend.Hardware.Gpu.Ntt
