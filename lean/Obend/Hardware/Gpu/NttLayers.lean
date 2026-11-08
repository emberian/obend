module
public import Obend.Hardware.Gpu.NttIndex
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource

/-- One whole-vector DIF level. Later levels act independently in the two
halves. The closed index formula below identifies the ordinary flattened loop. -/
def difLayer : Nat → Nat → (Nat → Nat) → Nat → Nat
  | 0, _, input, i => input i
  | bits+1, 0, input, i =>
      if i < 2^bits then addMod (input i) (input (2^bits+i))
      else mulMod (subMod (input (i-2^bits)) (input i))
        (modPow (rootOfUnity (2^(bits+1))) (i-2^bits))
  | bits+1, level+1, input, i =>
      if i < 2^bits then difLayer bits level input i
      else difLayer bits level (fun j => input (2^bits+j)) (i-2^bits)

/-- Sequential whole-vector layers, with a start level so register fusion is
ordinary function composition rather than a separate arithmetic semantics. -/
def difStages (bits start : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, input => input
  | count+1, input => difLayer bits (start+count) (difStages bits start count input)

theorem difStages_fuse (bits start a b : Nat) (input : Nat → Nat) :
    difStages bits start (a+b) input =
      difStages bits (start+a) b (difStages bits start a input) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change difLayer bits (start+(a+b)) (difStages bits start (a+b) input) =
      difLayer bits ((start+a)+b) (difStages bits (start+a) b (difStages bits start a input))
    rw [ih,Nat.add_assoc]

theorem difLayer_congr (bits level : Nat) (input other : Nat → Nat)
    (h : ∀ i, i < 2^bits → input i = other i) (i : Nat) (hi : i < 2^bits) :
    difLayer bits level input i = difLayer bits level other i := by
  induction bits generalizing level input other i with
  | zero => exact h i hi
  | succ bits ih =>
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
    cases level with
    | zero =>
      simp only [difLayer]
      split
      · rename_i hh
        rw [h i hi,h (2^bits+i) (by rw [hp]; omega)]
      · rw [h (i-2^bits) (by rw [hp]; omega),h i hi]
    | succ level =>
      simp only [difLayer]
      split
      · rename_i hh
        exact ih level input other (fun j hj => h j (by rw [hp]; omega)) i hh
      · exact ih level _ _ (fun j hj => h (2^bits+j) (by rw [hp]; omega)) _ hi'

theorem difStages_congr (bits start count : Nat) (input other : Nat → Nat)
    (h : ∀ i, i < 2^bits → input i = other i) (i : Nat) (hi : i < 2^bits) :
    difStages bits start count input i = difStages bits start count other i := by
  induction count generalizing i with
  | zero => exact h i hi
  | succ count ih =>
    exact difLayer_congr bits (start+count) _ _
      (fun j hj => ih j hj) i hi

/-- Remaining whole-vector levels project to the lower half's level sequence. -/
theorem difStages_low (bits start count : Nat) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    difStages (bits+1) (start+1) count input i = difStages bits start count input i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [difStages]
    have he : start+1+count = (start+count)+1 := by omega
    rw [he,difLayer,if_pos hi]
    apply difLayer_congr
    · exact fun j hj => ih j hj
    · exact hi

/-- Remaining whole-vector levels project to the upper half's level sequence. -/
theorem difStages_high (bits start count : Nat) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    difStages (bits+1) (start+1) count input (2^bits+i) =
      difStages bits start count (fun j => input (2^bits+j)) i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [difStages]
    have he : start+1+count = (start+count)+1 := by omega
    rw [he,difLayer,if_neg (by omega : ¬ 2^bits+i < 2^bits),Nat.add_sub_cancel_left]
    apply difLayer_congr
    · exact fun j hj => ih j hj
    · exact hi

/-- Every sequential DIF level has the recursive network semantics. The sole
canonical-input premise accounts for the zero-layer size-one transform. -/
theorem difStages_eq_storage (bits : Nat) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    difStages bits 0 bits input i = difStorage bits input i := by
  induction bits generalizing input i with
  | zero =>
    have hz : i=0 := by simpa using hi
    subst i
    simp only [difStages,difStorage]
    exact (Nat.mod_eq_of_lt (canonical 0 hi)).symm
  | succ bits ih =>
    have hp : 2^(bits+1) = 2^bits+2^bits := by rw [Nat.pow_succ]; omega
    have hsplit := difStages_fuse (bits+1) 0 1 bits input
    have he : bits+1=1+bits := by omega
    rw [← he] at hsplit
    rw [hsplit]
    change difStages (bits+1) 1 bits (difLayer (bits+1) 0 input) i = _
    by_cases h : i < 2^bits
    · rw [difStages_low bits 0 bits _ i h]
      have hstage := difStages_congr bits 0 bits (difLayer (bits+1) 0 input)
        (fun j => addMod (input j) (input (2^bits+j)))
        (by intro j hj; simp only [difLayer,if_pos hj]) i h
      rw [hstage, ih _ (by intro j hj; exact Nat.mod_lt _ (by decide)) i h]
      simp only [difStorage,if_pos h]
    · have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
      have he : i = 2^bits+(i-2^bits) := by omega
      conv => lhs; rw [he]
      rw [difStages_high bits 0 bits _ _ hi']
      have hstage := difStages_congr bits 0 bits
        (fun j => difLayer (bits+1) 0 input (2^bits+j))
        (fun j => mulMod (subMod (input j) (input (2^bits+j)))
          (modPow (rootOfUnity (2^(bits+1))) j))
        (by intro j hj; simp only [difLayer,if_neg (by omega : ¬ 2^bits+j < 2^bits),Nat.add_sub_cancel_left])
        (i-2^bits) hi'
      rw [hstage, ih _ (by intro j hj; exact Nat.mod_lt _ (by decide)) _ hi']
      simp only [difStorage,if_neg h]

/-- Closed flattened butterfly addressing. `half` is the current pair distance;
all blocks execute the same pair operation from one immutable input snapshot. -/
def flatButterfly (half root : Nat) (input : Nat → Nat) (i : Nat) : Nat :=
  let within :=  i % (2*half)
  let low := i-within + within%half
  if within < half then addMod (input low) (input (low+half))
  else mulMod (subMod (input low) (input (low+half))) (modPow root (within%half))

theorem flatButterfly_shift (half root offset : Nat) (input : Nat → Nat)
    (aligned : offset % (2*half) = 0) (i : Nat) :
    flatButterfly half root input (offset+i) =
      flatButterfly half root (fun j => input (offset+j)) i := by
  have hm : (offset+i)%(2*half) = i%(2*half) := by
    rw [Nat.add_mod,aligned]
    simp
  have hl := Nat.mod_le i (2*half)
  have he : offset+i-i%(2*half) = offset+(i-i%(2*half)) := by omega
  simp only [flatButterfly,hm,he,Nat.add_assoc]

/-- Point readback for the lower write of one flattened butterfly pair. -/
theorem flatButterfly_pair_low (half root base j : Nat) (input : Nat → Nat)
    (aligned : base % (2*half) = 0) (hj : j < half) :
    flatButterfly half root input (base+j) =
      addMod (input (base+j)) (input (base+j+half)) := by
  rw [flatButterfly_shift half root base input aligned j]
  have hj2 : j < 2*half := by omega
  simp only [flatButterfly,Nat.mod_eq_of_lt hj2,Nat.mod_eq_of_lt hj,
    Nat.sub_self,Nat.zero_add,if_pos hj,Nat.add_assoc]

/-- Point readback for the upper write of one flattened butterfly pair. -/
theorem flatButterfly_pair_high (half root base j : Nat) (input : Nat → Nat)
    (aligned : base % (2*half) = 0) (hj : j < half) :
    flatButterfly half root input (base+j+half) =
      mulMod (subMod (input (base+j)) (input (base+j+half))) (modPow root j) := by
  rw [Nat.add_assoc base j half,flatButterfly_shift half root base input aligned (j+half)]
  have hj2 : j+half < 2*half := by omega
  have hm : (j+half)%half=j := by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hj]
  have hn : ¬ j+half < half := by omega
  simp only [flatButterfly,Nat.mod_eq_of_lt hj2,hm,Nat.sub_self,Nat.zero_add,
    if_neg hn,Nat.add_assoc]

/-- The recursive level description is the ordinary flat pair-address loop. -/
theorem difLayer_flat (bits level : Nat) (input : Nat → Nat)
    (hl : level < bits) (i : Nat) (hi : i < 2^bits) :
    difLayer bits level input i =
      flatButterfly (2^(bits-level-1)) (rootOfUnity (2^(bits-level))) input i := by
  induction bits generalizing level input i with
  | zero => omega
  | succ bits ih =>
    have hp : 2^(bits+1) = 2*2^bits := by rw [Nat.pow_succ,Nat.mul_comm]
    cases level with
    | zero =>
      have him : i%(2*2^bits)=i := Nat.mod_eq_of_lt (by rw [←hp]; exact hi)
      simp only [Nat.sub_zero,Nat.add_sub_cancel,difLayer,flatButterfly,him,Nat.sub_self,Nat.zero_add]
      by_cases h : i<2^bits
      · simp only [if_pos h,Nat.mod_eq_of_lt h]
        rw [Nat.add_comm i]
      · have hrest : i-2^bits < 2^bits := by rw [hp] at hi; omega
        have hm : i%2^bits=i-2^bits := by
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hrest]
        have he : i-2^bits+2^bits=i := by omega
        simp only [if_neg h,hm,he]
    | succ level =>
      have hl' : level<bits := by omega
      have hs : bits+1-(level+1) = bits-level := by omega
      simp only [hs,difLayer]
      by_cases h : i<2^bits
      · rw [if_pos h]
        exact ih level input hl' i h
      · have hi' : i-2^bits < 2^bits := by rw [hp] at hi; omega
        rw [if_neg h,ih level _ hl' _ hi']
        have hpow : 2 * 2^(bits-level-1) = 2^(bits-level) := by
          rw [Nat.mul_comm,← Nat.pow_succ]
          congr 1
          omega
        have halign : 2^bits % (2*2^(bits-level-1)) = 0 := by
          rw [hpow]
          exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
        have he : i=2^bits+(i-2^bits) := by omega
        conv => rhs; rw [he]
        exact (flatButterfly_shift _ _ _ input halign _).symm

/-- Full flat-level execution is the DFT in bit-reversed storage. -/
theorem difStages_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    difStages bits 0 bits input i = dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [difStages_eq_storage bits input canonical i hi,difStorage_eq_dft bits hbits input i hi]

/-- Direct flattened-layer semantics for the register schedule. -/
def flatStages (bits start : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, input => input
  | count+1, input => flatButterfly (2^(bits-(start+count)-1))
      (rootOfUnity (2^(bits-(start+count)))) (flatStages bits start count input)

theorem flatStages_eq (bits start count : Nat) (hc : start+count ≤ bits)
    (input : Nat → Nat) (i : Nat) (hi : i < 2^bits) :
    flatStages bits start count input i = difStages bits start count input i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [flatStages,difStages]
    rw [← difLayer_flat bits (start+count) _ (by omega) i hi]
    exact difLayer_congr bits (start+count) _ _ (fun j hj => ih (by omega) j hj) i hi

/-- Consecutive fused flattened passes denote one uninterrupted level sequence. -/
theorem flatStages_fuse (bits start a b : Nat) (hc : start+a+b ≤ bits)
    (input : Nat → Nat) (i : Nat) (hi : i < 2^bits) :
    flatStages bits (start+a) b (flatStages bits start a input) i =
      flatStages bits start (a+b) input i := by
  rw [flatStages_eq bits (start+a) b hc _ i hi,
    flatStages_eq bits start (a+b) (by omega) input i hi,difStages_fuse]
  exact difStages_congr bits (start+a) b _ _
    (fun j hj => flatStages_eq bits start a (by omega) input j hj) i hi

theorem flatStages_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (canonical : ∀ i, i < 2^bits → input i < goldilocksP)
    (i : Nat) (hi : i < 2^bits) :
    flatStages bits 0 bits input i = dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [flatStages_eq bits 0 bits (by omega) input i hi,difStages_eq_dft bits hbits input canonical i hi]

/-- Arbitrary word inputs are reduced by the actual first-stage canonicalizer;
the canonicalized flat network still denotes their original modular DFT. -/
theorem flatStages_canonical_eq_dft (bits : Nat) (hbits : bits ≤ 32) (input : Nat → Nat)
    (i : Nat) (hi : i < 2^bits) :
    flatStages bits 0 bits (fun j => input j % goldilocksP) i =
      dft (2^bits) (rootOfUnity (2^bits)) input (reverseIndex bits i) := by
  rw [flatStages_eq_dft bits hbits _ (by intro j hj; exact Nat.mod_lt _ (by decide)) i hi,dft_input_mod]

end Obend.Hardware.Gpu.Ntt
