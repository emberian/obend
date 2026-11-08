module
public import Obend.Hardware.Gpu.NttBatchCorrect
@[expose] public section

/-! Exact phase scheduling and unconditional row framing for the actual NTT
upload builder. Batching changes indices but never the destination array. -/
namespace Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Hardware.Gpu.NttBatchCorrect
open Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

theorem phaseDegrees_sum (degree : Nat) : (phaseDegrees degree).sum = degree := by
  have hm := Nat.mod_lt degree (by decide : 0 < 2)
  have hd := Nat.div_add_mod degree 2
  by_cases h : degree%2=0
  · simp [phaseDegrees,h,List.sum_replicate_nat]
    omega
  · have h1 : degree%2=1 := by omega
    simp [phaseDegrees,h1,List.sum_replicate_nat]
    omega

theorem phaseDegrees_member (degree chunk : Nat) (h : chunk ∈ phaseDegrees degree) :
    chunk = 1 ∨ chunk = 2 := by
  unfold phaseDegrees at h
  rcases List.mem_append.mp h with hr | ht
  · exact Or.inr (List.eq_of_mem_replicate hr)
  · split at ht <;> simp_all

theorem phaseDegrees_ne_nil (degree : Nat) (h : 0 < degree) : phaseDegrees degree ≠ [] := by
  intro he
  have hs := phaseDegrees_sum degree
  rw [he] at hs
  simp at hs
  omega

def phaseOutput (bits dst done input chunk : Nat) : Nat :=
  if done+chunk == bits then dst else if input == 2 then 3 else 2

def finalPhaseBuffer (bits dst : Nat) : Nat → Nat → List Nat → Nat
  | _, input, [] => input
  | done, input, chunk::rest =>
      finalPhaseBuffer bits dst (done+chunk) (phaseOutput bits dst done input chunk) rest

theorem finalPhaseBuffer_complete (bits dst done input : Nat) (chunks : List Nat)
    (hne : chunks ≠ []) (h : done+chunks.sum = bits) :
    finalPhaseBuffer bits dst done input chunks = dst := by
  induction chunks generalizing done input with
  | nil => exact False.elim (hne rfl)
  | cons chunk rest ih =>
    cases rest with
    | nil =>
      have he : done+chunk = bits := by simpa using h
      simp [finalPhaseBuffer,phaseOutput,he]
    | cons next rest =>
      change finalPhaseBuffer bits dst (done+chunk) (phaseOutput bits dst done input chunk) (next::rest) = dst
      apply ih _ _ (by simp)
      simp only [List.sum_cons] at h ⊢
      omega

theorem buildPhases_length (n bits p dst done input : Nat) (chunks : List Nat) :
    (buildPhases n bits p dst done input chunks).length = chunks.length := by
  induction chunks generalizing done input with
  | nil => rfl
  | cons chunk rest ih => simp [buildPhases,ih]

/-- The opaque register construction does not affect the output-array metadata. -/
theorem phase_write_array (n count bits p done degree src dst : Nat) (first last : Bool)
    (w : Write) (hw : w ∈ (phase n count bits p done degree src dst first last).writes) :
    w.array = dst := by
  unfold phase at hw
  dsimp only at hw
  obtain ⟨item,_,he⟩ := List.mem_map.mp hw
  subst w
  rfl

theorem buildPhases_write_arrays (n bits p dst done input : Nat) (chunks : List Nat)
    (ph : Phase) (hph : ph ∈ buildPhases n bits p dst done input chunks)
    (w : Write) (hw : w ∈ ph.writes) : w.array = dst ∨ w.array = 2 ∨ w.array = 3 := by
  induction chunks generalizing done input with
  | nil => simp [buildPhases] at hph
  | cons chunk rest ih =>
    simp only [buildPhases,List.mem_cons] at hph
    rcases hph with he | ht
    · subst ph
      have ha := phase_write_array n (2^bits) bits p done chunk input _ _ _ w hw
      by_cases hl : done+chunk = bits
      · simp [hl] at ha
        exact Or.inl ha
      · by_cases hs : input=2
        · simp [hl,hs] at ha
          exact Or.inr (Or.inr ha)
        · simp [hl,hs] at ha
          exact Or.inr (Or.inl ha)
    · exact ih _ _ ht

/-- An out-of-row store cannot affect that row, even for malformed memory sizes.
This frame fact therefore needs no admission receipt. -/
theorem applyWrite_row_frame (mem : Memory) (w : Nat × Nat × Word) (a : Nat)
    (h : w.1 ≠ a) : (applyWrite mem w).getD a #[] = mem.getD a #[] := by
  simp [applyWrite,Array.getD_eq_getD_getElem?,Array.getElem?_modify,h]

theorem foldWrites_row_frame (ws : List (Nat × Nat × Word)) (mem : Memory) (a : Nat)
    (h : ∀ w ∈ ws, w.1 ≠ a) : (ws.foldl applyWrite mem).getD a #[] = mem.getD a #[] := by
  induction ws generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih (applyWrite mem w) (fun x hx => h x (by simp [hx]))]
    exact applyWrite_row_frame mem w a (h w (by simp))

theorem evalPhase_row_frame (ph : Phase) (g : Nat) (mem : Memory) (a : Nat)
    (h : ∀ w ∈ ph.writes, w.array ≠ a) : (evalPhase ph g mem).getD a #[] = mem.getD a #[] := by
  apply foldWrites_row_frame
  intro w hw
  obtain ⟨l,_,hl⟩ := List.mem_flatMap.mp hw
  obtain ⟨out,ho,he⟩ := List.mem_map.mp hl
  subst w
  exact h out ho

theorem evalPhases_row_frame (phases : List Phase) (g : Nat) (mem : Memory) (a : Nat)
    (h : ∀ ph ∈ phases, ∀ w ∈ ph.writes, w.array ≠ a) :
    (phases.foldl (fun m ph => evalPhase ph g m) mem).getD a #[] = mem.getD a #[] := by
  induction phases generalizing mem with
  | nil => rfl
  | cons ph phases ih =>
    rw [List.foldl_cons,ih (evalPhase ph g mem) (fun p hp => h p (by simp [hp]))]
    exact evalPhase_row_frame ph g mem a (h ph (by simp))

theorem evalDispatch_row_frame (d : Dispatch) (mem : Memory) (a : Nat)
    (h : ∀ ph ∈ d.phases, ∀ w ∈ ph.writes, w.array ≠ a) :
    (evalDispatch d mem).getD a #[] = mem.getD a #[] := by
  unfold evalDispatch
  generalize List.range d.groups = groups
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih]
    exact evalPhases_row_frame d.phases g mem a h

/-- A real packed upload preserves every row except its output and its two
shared workspaces. In particular all other device arrays and twiddles are framed. -/
theorem dispatch_row_frame (n logP degree src dst stride : Nat) (mem : Memory) (a : Nat)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (evalDispatch (batchTiles stride (dispatch n logP degree src dst)) mem).getD a #[] =
      mem.getD a #[] := by
  apply evalDispatch_row_frame
  intro ph hph w hw
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,he⟩ := List.mem_map.mp hph
  subst ph
  obtain ⟨out,hw',he⟩ := List.mem_map.mp hw
  subst w
  have ha := buildPhases_write_arrays n degree (2^logP) dst 0 src (phaseDegrees degree)
    original ho out hw'
  dsimp only
  rcases ha with ha | ha | ha <;> omega


/-- The actual Stockham destination address after final bit reversal. -/
def outputAddress (p count group r : Nat) : Nat :=
  group/p*(p*count)+group%p+r*p

theorem outputAddress_split (p count group r : Nat) :
    outputAddress p count group r = p*((group/p)*count+r)+group%p := by
  simp [outputAddress,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem outputAddress_div (p count group r : Nat) (hp : 0 < p) :
    outputAddress p count group r / p = (group/p)*count+r := by
  rw [outputAddress_split,Nat.mul_add_div hp,Nat.div_eq_of_lt (Nat.mod_lt group hp),Nat.add_zero]

theorem outputAddress_mod (p count group r : Nat) :
    outputAddress p count group r % p = group%p := by
  rw [outputAddress_split]
  simp

theorem outputAddress_register (p count group r : Nat) (hp : 0 < p) (hr : r < count) :
    outputAddress p count group r / p % count = r := by
  rw [outputAddress_div _ _ _ _ hp]
  exact Nat.mul_add_mod_of_lt hr

theorem outputAddress_group (p count group r : Nat) (hp : 0 < p) (hr : r < count) :
    (outputAddress p count group r / p / count)*p + outputAddress p count group r % p = group := by
  rw [outputAddress_div _ _ _ _ hp,outputAddress_mod]
  have hd : ((group/p)*count+r)/count = group/p := by
    rw [Nat.mul_comm (group/p),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hr,Nat.add_zero]
  rw [hd]
  simpa [Nat.mul_comm] using Nat.div_add_mod group p

/-- Distinct workgroups never alias their final device scatter; no source
admission receipt or concrete transform size is used by this arithmetic fact. -/
theorem outputAddress_injective (p count g h r s : Nat) (hp : 0 < p)
    (hr : r < count) (hs : s < count)
    (he : outputAddress p count g r = outputAddress p count h s) : g=h ∧ r=s := by
  constructor
  · have hg := outputAddress_group p count g r hp hr
    have hh := outputAddress_group p count h s hp hs
    rw [he] at hg
    omega
  · have hg := outputAddress_register p count g r hp hr
    have hh := outputAddress_register p count h s hp hs
    rw [he] at hg
    omega

theorem outputAddress_bound (p count tiles g r : Nat) (hp : 0 < p)
    (hg : g < p*tiles) (hr : r < count) : outputAddress p count g r < p*count*tiles := by
  have hq : g/p < tiles := Nat.div_lt_of_lt_mul hg
  have hm := Nat.mul_le_mul_right count (Nat.succ_le_of_lt hq)
  simp only [Nat.succ_mul] at hm
  have hd : outputAddress p count g r / p < tiles*count := by
    rw [outputAddress_div _ _ _ _ hp]
    omega
  have hb := (Nat.div_lt_iff_lt_mul hp).mp hd
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb


/-- Induction principle for the actual barrier-separated, batched phase list.
The invariant may record every tile simultaneously; the step is a real evalPhase. -/
theorem buildPhases_invariant (n bits p dst stride k group : Nat)
    (I : Nat → Nat → Memory → Prop)
    (step : ∀ done input chunk, 0 < chunk → chunk ≤ 2 → done+chunk ≤ bits →
      ∀ mem, I done input mem →
      I (done+chunk) (phaseOutput bits dst done input chunk)
        (evalPhase (batchPhase stride k
          (phase n (2^bits) bits p done chunk input (phaseOutput bits dst done input chunk)
            (done == 0) (done+chunk == bits))) group mem))
    (done input : Nat) (chunks : List Nat)
    (hchunks : ∀ chunk ∈ chunks, 0 < chunk ∧ chunk ≤ 2)
    (hbound : done+chunks.sum ≤ bits) (mem : Memory) (hmem : I done input mem) :
    I (done+chunks.sum) (finalPhaseBuffer bits dst done input chunks)
      (((buildPhases n bits p dst done input chunks).map (batchPhase stride k)).foldl
        (fun m ph => evalPhase ph group m) mem) := by
  induction chunks generalizing done input mem with
  | nil => simpa [buildPhases,finalPhaseBuffer] using hmem
  | cons chunk rest ih =>
    have hc := hchunks chunk (by simp)
    have hb : done+chunk ≤ bits := by simp only [List.sum_cons] at hbound; omega
    have hs := step done input chunk hc.1 hc.2 hb mem hmem
    have ht := ih (done+chunk) (phaseOutput bits dst done input chunk)
      (fun c hc => hchunks c (by simp [hc]))
      (by simp only [List.sum_cons] at hbound; omega) _ hs
    simpa only [buildPhases,finalPhaseBuffer,List.map_cons,List.foldl_cons,List.sum_cons,
      phaseOutput,Nat.add_assoc] using ht

/-- Exact composition endpoint for one packed upload: the schedule covers all
layers and its last phase uses the declared destination array. -/
theorem dispatch_phases_invariant (n logP degree src dst stride group : Nat)
    (hdegree : 0 < degree) (I : Nat → Nat → Memory → Prop)
    (step : ∀ done input chunk, 0 < chunk → chunk ≤ 2 → done+chunk ≤ degree →
      ∀ mem, I done input mem →
      I (done+chunk) (phaseOutput degree dst done input chunk)
        (evalPhase (batchPhase stride (packing (dispatch n logP degree src dst))
          (phase n (2^degree) degree (2^logP) done chunk input
            (phaseOutput degree dst done input chunk) (done == 0) (done+chunk == degree))) group mem))
    (mem : Memory) (hmem : I 0 src mem) :
    I degree dst (evalGroup (batchTiles stride (dispatch n logP degree src dst)) group mem) := by
  have h := buildPhases_invariant n degree (2^logP) dst stride
    (packing (dispatch n logP degree src dst)) group I step 0 src (phaseDegrees degree)
    (fun c hc => by rcases phaseDegrees_member degree c hc with rfl | rfl <;> decide)
    (by rw [phaseDegrees_sum]; omega) mem hmem
  have hf := finalPhaseBuffer_complete degree dst 0 src (phaseDegrees degree)
    (phaseDegrees_ne_nil degree hdegree) (by rw [phaseDegrees_sum]; omega)
  simpa only [phaseDegrees_sum,Nat.zero_add,hf,evalGroup,batchTiles_phases,dispatch] using h


/-- A store at a different coordinate frames this cell, including out-of-bounds
stores. This is a property of the source evaluator, independent of admission. -/
theorem applyWrite_cell_frame (mem : Memory) (w : Nat × Nat × Word) (a i : Nat)
    (h : (w.1,w.2.1) ≠ (a,i)) : valueAt (applyWrite mem w) a i = valueAt mem a i := by
  by_cases ha : w.1 = a
  · have hi : w.2.1 ≠ i := by intro he; exact h (Prod.ext ha he)
    by_cases hb : a < mem.size
    · simp [applyWrite,valueAt,Array.getD_eq_getD_getElem?,Array.getElem?_modify,Array.getElem_modify,ha,hb,
        Array.getElem?_setIfInBounds,hi]
    · simp [applyWrite,valueAt,Array.getD_eq_getD_getElem?,Array.getElem?_modify,ha,hb]
  · exact congrArg (fun row => row.getD i 0#64) (applyWrite_row_frame mem w a ha)

theorem foldWrites_cell_frame (ws : List (Nat × Nat × Word)) (mem : Memory) (a i : Nat)
    (h : ∀ w ∈ ws, (w.1,w.2.1) ≠ (a,i)) :
    valueAt (ws.foldl applyWrite mem) a i = valueAt mem a i := by
  induction ws generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih (applyWrite mem w) (fun x hx => h x (by simp [hx]))]
    exact applyWrite_cell_frame mem w a i (h w (by simp))

theorem evalPhase_cell_frame (ph : Phase) (g : Nat) (mem : Memory) (a i : Nat)
    (h : (a,i) ∉ ph.writeAddresses g) :
    valueAt (evalPhase ph g mem) a i = valueAt mem a i := by
  apply foldWrites_cell_frame
  intro w hw he
  apply h
  rw [← phaseWrites_locations ph mem g]
  exact List.mem_map.mpr ⟨w,hw,he⟩

/-- Pointwise framing composes through the actual phases, with no assumptions
about the values calculated by any other invocation. -/
theorem evalPhases_cell_frame (phases : List Phase) (g : Nat) (mem : Memory) (a i : Nat)
    (h : ∀ ph ∈ phases, (a,i) ∉ ph.writeAddresses g) :
    valueAt (phases.foldl (fun m ph => evalPhase ph g m) mem) a i = valueAt mem a i := by
  induction phases generalizing mem with
  | nil => rfl
  | cons ph phases ih =>
    rw [List.foldl_cons,ih (evalPhase ph g mem) (fun p hp => h p (by simp [hp]))]
    exact evalPhase_cell_frame ph g mem a i (h ph (by simp))

end Obend.Hardware.Gpu.NttDispatchCorrect
end
