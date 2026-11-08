module
public import Obend.Hardware.Gpu.NttCompose
public import Obend.Hardware.Gpu.NttDispatchCorrect
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.ArrayKernel Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open GoldilocksSource Stockham

/-- The exact value contract of an actual batched upload. This is an interface
for proof composition, not an alternative evaluator or an emitted certificate. -/
def UploadDFT (bits done degree src dst : Nat) (mem : Memory) : Prop :=
  let n := 2^bits
  let d := BlockNtt.dispatch n done degree src dst
  let result := evalDispatch (BlockNtt.batchTiles (BlockNtt.tileSize d) d) mem
  ∀ g, g < n/(2^degree) → ∀ r, r < 2^degree →
    (valueAt result dst (g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done))).toNat =
      dft (2^degree) (rootOfUnity (2^degree))
        (fun t => mulMod (valueAt mem src (g+t*(n/2^degree))).toNat
          (modPow (rootOfUnity n) (t*(g%(2^done))*(n/2^degree/2^done)))) r

def TwiddleMemory (n : Nat) (mem : Memory) : Prop :=
  ∀ i, i < n → (valueAt mem 4 i).toNat = modPow (rootOfUnity n) i

structure StageInvariant (bits : Nat) (input : Nat → Nat) (done current : Nat) (mem : Memory) : Prop where
  device : current ≤ 1
  good : BlockLower.Good (nttBlockProgram (2^bits)) mem
  twiddles : TwiddleMemory (2^bits) mem
  values : LayoutValues (2^done) (2^bits/2^done) (rootOfUnity (2^bits)) input
    (fun i => (valueAt mem current i).toNat)
  canonical : 0 < done → ∀ i, i < 2^bits → (valueAt mem current i).toNat < goldilocksP

/-- One actual upload advances the whole-program invariant. All source indices,
bit reversal and register arithmetic enter through the upload value theorem. -/
theorem StageInvariant.step (bits done degree current : Nat) (input : Nat → Nat) (mem : Memory)
    (hbits : bits ≤ 32) (hd : done+degree ≤ bits) (hdegree : 0 < degree)
    (before : StageInvariant bits input done current mem)
    (execute : UploadDFT bits done degree current (1-current) mem) :
    StageInvariant bits input (done+degree) (1-current)
      (evalDispatch (BlockNtt.batchTiles
        (BlockNtt.tileSize (BlockNtt.dispatch (2^bits) done degree current (1-current)))
        (BlockNtt.dispatch (2^bits) done degree current (1-current))) mem) := by
  constructor
  · omega
  · exact dispatch_good _ _ _ before.good
  · intro i hi
    have hf := NttDispatchCorrect.dispatch_row_frame (2^bits) done degree current (1-current)
      (BlockNtt.tileSize (BlockNtt.dispatch (2^bits) done degree current (1-current))) mem 4
      (by omega) (by decide) (by decide)
    simpa only [valueAt,hf] using before.twiddles i hi
  · exact layout_upload_bits bits done degree hbits hd input _ _ before.values execute
  · intro _ i hi
    obtain ⟨g,hg,r,hr,he⟩ := output_cover_bits bits done degree i hd hi
    rw [←he,execute g hg r hr]
    exact Nat.mod_lt _ (by decide)

/-- Whole-source composition. The remaining premise is precisely the actual
upload lemma, universally quantified over its represented memories; the final
public NTT theorem discharges it with the register/phase proof. -/
theorem program_value_of_uploads (bits : Nat) (hbits : bits ≤ 25) (hpos : 0 < bits)
    (input : Array Word) (hinput : input.size = 2^bits)
    (uploads : ∀ done degree current mem,
      degree ∈ uploadSchedule (2^bits) → done+degree ≤ bits → current ≤ 1 →
      BlockNtt.dispatch (2^bits) done degree current (1-current) ∈ (sourceUploads (2^bits)).1 →
      BlockLower.Good (nttBlockProgram (2^bits)) mem → TwiddleMemory (2^bits) mem →
      UploadDFT bits done degree current (1-current) mem)
    (i : Nat) (hi : i < 2^bits) :
    (valueAt (evalProgram (nttBlockProgram (2^bits))
      (initialMemory (nttBlockProgram (2^bits)) [input])) (sourceUploads (2^bits)).2 i).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (fun j => (input.getD j 0#64).toNat) i := by
  let n := 2^bits
  let values := fun j => (input.getD j 0#64).toNat
  let initial := initialMemory (nttBlockProgram n) [input]
  have hs : (uploadSchedule n).sum = bits := by simpa [n,Nat.log2_two_pow] using uploadSchedule_sum n
  have init : StageInvariant bits values 0 0 initial := by
    constructor
    · decide
    · exact initial_good n input hinput
    · exact initial_twiddle_value n input
    · simpa only [Nat.pow_zero,Nat.div_one,valueAt,initial,initial_input,n,values] using
        layout_initial n (rootOfUnity n) values
    · omega
  let transform := fun d => BlockNtt.batchTiles (BlockNtt.tileSize d) d
  have final := buildUploads_invariant n (uploadSchedule n) transform (StageInvariant bits values) bits
    (sourceUploads n).1 (by
      intro degree hdegree done current mem hmember hbound before
      have hp : 0 < degree := uploadDegrees_positive _ _ _ (by split <;> decide) degree hdegree
      exact before.step bits done degree current values mem (by omega) hbound hp
        (uploads done degree current mem hdegree hbound before.device hmember before.good before.twiddles))
    0 0 initial (fun _ h => h) (by omega) init
  rw [hs,Nat.zero_add] at final
  change StageInvariant bits values bits (sourceUploads n).2
    (evalProgram (nttBlockProgram n) initial) at final
  have hv := layout_final n (rootOfUnity n) values
    (fun j => (valueAt (evalProgram (nttBlockProgram n) initial) (sourceUploads n).2 j).toNat)
    (by simpa only [Nat.div_self (Nat.two_pow_pos bits)] using final.values) i hi
  rw [Nat.mod_eq_of_lt (final.canonical hpos i hi)] at hv
  exact hv

end Obend.Hardware.Gpu.Ntt
