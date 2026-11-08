module
public import Obend.Hardware.Gpu.NttPairFold
public import Obend.Hardware.Gpu.NttPhaseArithmetic
public import Obend.Hardware.Gpu.NttPhaseReads
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource ArrayKernel BlockNtt RegisterValues PhaseArithmetic

theorem difLayer_canonical (bits level : Nat) (hl : level<bits) (input : Nat → Nat)
    (i : Nat) (hi : i<2^bits) : difLayer bits level input i < goldilocksP := by
  induction bits generalizing level input i with
  | zero => omega
  | succ bits ih =>
    have hp : 2^(bits+1)=2^bits+2^bits := by rw [Nat.pow_succ]; omega
    cases level with
    | zero =>
      simp only [difLayer]
      split <;> exact Nat.mod_lt _ (by decide)
    | succ level =>
      simp only [difLayer]
      split
      · rename_i h
        exact ih level (by omega) input i h
      · exact ih level (by omega) _ _ (by rw [hp] at hi; omega)

theorem difStages_canonical (bits start count : Nat) (hc : start+count≤bits) (input : Nat → Nat)
    (hinput : ∀ i, i<2^bits → input i<goldilocksP) (i : Nat) (hi : i<2^bits) :
    difStages bits start count input i < goldilocksP := by
  cases count with
  | zero => exact hinput i hi
  | succ count => exact difLayer_canonical bits (start+count) (by omega) _ i hi

/-- The source's omitted unit-twiddle load has exactly the same power-table value. -/
theorem pairTwiddle_power (n count done radix stride round j group lane : Nat) :
    pairTwiddle n count done radix stride round j
      (fun ix => modPow (rootOfUnity n) (ix.eval group lane)) =
      modPow (rootOfUnity n)
        (phasePairOffset stride lane j (radix/2^(round+1)) * (2^(done+round)*(n/count))) := by
  unfold pairTwiddle
  split
  · rename_i h
    have hh : stride=1 ∧ j%(radix/2^(round+1))=0 := by simpa using h
    simp [phasePairOffset,hh.1,hh.2,Nat.mod_one]
  · rfl

/-- A prefix of the actual register-round fold equals the same prefix of the
whole-vector levels, allowing arbitrary fused register degrees. -/
theorem phase_rounds_stages (total bits done degree rounds group lane : Nat)
    (ht : total≤32) (hb : bits≤total) (hdegree : done+degree≤bits) (hrounds : rounds≤degree)
    (hlane : lane<2^bits/2^degree) (input values : Nat → Nat)
    (hvalues : ∀ r, r<2^degree → values r=input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
    (hinput : ∀ i, i<2^bits → input i<goldilocksP) :
    ∀ r, r<2^degree →
    ((List.range rounds).foldl (fun v round => roundValues (2^degree/2) (2^degree/2^(round+1))
      (fun j => pairTwiddle (2^total) (2^bits) done (2^degree) (2^bits/(2^done*2^degree)) round j
        (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane))) v) values) r =
    difStages bits done rounds input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  induction rounds with
  | zero => exact hvalues
  | succ rounds ih =>
    intro r hr
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    have htw : (fun j => pairTwiddle (2^total) (2^bits) done (2^degree)
        (2^bits/(2^done*2^degree)) rounds j
        (fun ix => modPow (rootOfUnity (2^total)) (ix.eval group lane))) =
        (fun j => modPow (rootOfUnity (2^total))
          (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(rounds+1)) *
            (2^(done+rounds)*(2^total/2^bits)))) := by
      funext j
      exact pairTwiddle_power _ _ _ _ _ _ _ _ _
    rw [htw]
    apply phase_roundValues_layer total bits done degree rounds lane r ht hb hdegree (by omega) hlane hr
    · exact ih (by omega)
    · intro rr hrr
      rw [ih (by omega) rr hrr]
      exact difStages_canonical bits done rounds (by omega) input hinput _
        (phase_index_lt bits done degree lane rr hdegree hlane hrr)

/-- The first phase's common mathematical input for both canonicalization and
nontrivial input twiddle branches. -/
def preparedInput (n count p group : Nat) (first : Bool) (entry : Nat → Nat) (i : Nat) : Nat :=
  if first then mulMod (entry i) (modPow (rootOfUnity n) (i*(group%p)*(n/count/p))) else entry i

theorem preparedInput_canonical (n count p group bound : Nat) (first : Bool) (entry : Nat → Nat)
    (h : first=false → ∀ i, i<bound → entry i<goldilocksP) :
    ∀ i, i<bound → preparedInput n count p group first entry i < goldilocksP := by
  intro i hi
  cases first with
  | false => exact h rfl i hi
  | true => exact Nat.mod_lt _ (by decide)

theorem inputExponent_power (total bits p done degree group lane r : Nat) (ht : total≤32) :
    modPow (rootOfUnity (2^total))
      ((PhaseMetadata.inputExponent (2^total) (2^bits) p (2^degree)
        (2^bits/(2^done*2^degree)) r).eval group lane) =
      modPow (rootOfUnity (2^total))
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r *
          (group%p)*(2^total/2^bits/p)) := by
  change modPow (rootOfUnity (2^total))
    ((laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r *
      (group%p*(2^total/2^bits/p))) % 2^total) = _
  rw [←root_periodic total ht]
  congr 1
  exact (Nat.mul_assoc _ _ _).symm

/-- The actual initialization branches have the same whole-tile input function. -/
theorem prepared_register_eq (total bits p done degree group lane r : Nat) (first : Bool)
    (entry values : Nat → Nat) (ht : total≤32)
    (hv : values r=entry (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r)) :
    (if first then if p=1 then values r%goldilocksP else
      mulMod (values r) (modPow (rootOfUnity (2^total))
        ((PhaseMetadata.inputExponent (2^total) (2^bits) p (2^degree)
          (2^bits/(2^done*2^degree)) r).eval group lane)) else values r) =
      preparedInput (2^total) (2^bits) p group first entry
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  cases first with
  | false => exact hv
  | true =>
    by_cases hp : p=1
    · simp [hp,preparedInput,hv,mulMod,Nat.mod_one]
    · simp only [ite_true,if_neg hp,preparedInput]
      rw [inputExponent_power _ _ _ _ _ _ _ _ ht,hv]

end Obend.Hardware.Gpu.Ntt
