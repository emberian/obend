module
public import Obend.Hardware.Gpu.NttStockham
public import Obend.Hardware.Gpu.NttMemory
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource Stockham

/-- Initial raw words need not be canonical; the invariant observes residues,
matching the source's first register canonicalization. -/
theorem layout_initial (n ω : Nat) (input : Nat → Nat) :
    LayoutValues 1 n ω input input := by
  intro b hb k hk
  have hk0 : k=0 := by omega
  simp [hk0,initial]

/-- At full size the partial-transform invariant is exactly the natural-order
DFT, with no input or output permutation left to a consumer. -/
theorem layout_final (n ω : Nat) (input values : Nat → Nat)
    (h : LayoutValues n 1 ω input values) (k : Nat) (hk : k < n) :
    values k % goldilocksP = dft n ω input k := by
  have hv := h 0 (by decide) k hk
  simpa [partialTransform,dft,sumMod] using hv

/-- Bit-count specialization of the Stockham algebra, in exactly the division
and twiddle coordinates used by the source upload. -/
theorem layout_upload_bits (bits done degree : Nat) (hbits : bits ≤ 32)
    (hd : done+degree ≤ bits) (input before after : Nat → Nat)
    (previous : LayoutValues (2^done) (2^bits / 2^done)
      (rootOfUnity (2^bits)) input before)
    (execute : ∀ g, g < 2^bits / 2^degree → ∀ r, r < 2^degree →
      after (g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done)) =
        dft (2^degree) (rootOfUnity (2^degree))
          (fun t => mulMod (before (g+t*(2^bits/2^degree)))
            (modPow (rootOfUnity (2^bits)) (t*(g%(2^done))*(2^bits/2^degree/2^done)))) r) :
    LayoutValues (2^(done+degree)) (2^bits / 2^(done+degree))
      (rootOfUnity (2^bits)) input after := by
  let m := 2^(bits-(done+degree))
  have hp : 0 < 2^done := Nat.two_pow_pos done
  have hc : 0 < 2^degree := Nat.two_pow_pos degree
  have hdone : done ≤ bits := by omega
  have hdegree : degree ≤ bits := by omega
  have hpm : 2^done*m = 2^(bits-degree) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcm : 2^degree*m = 2^(bits-done) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hn : 2^done*2^degree*m = 2^bits := by
    rw [← Nat.pow_add,← Nat.pow_add]
    congr 1
    omega
  have hdv : 2^bits/2^degree = 2^done*m := by
    rw [Nat.pow_div hdegree (by decide),hpm]
  have hpv : 2^bits/2^done = 2^degree*m := by
    rw [Nat.pow_div hdone (by decide),hcm]
  have hmv : 2^bits/2^degree/2^done = m := by rw [hdv,Nat.mul_div_right m hp]
  have hnew : 2^bits/2^(done+degree) = m := Nat.pow_div hd (by decide)
  have hroot : modPow (rootOfUnity (2^bits)) (2^done*m) = rootOfUnity (2^degree) := by
    rw [hpm]
    exact root_subtransform bits degree hdegree hbits
  have hperiod : modPow (rootOfUnity (2^bits)) (2^done*2^degree*m) = 1 := by
    rw [hn]
    exact root_full bits hbits
  rw [hpv] at previous
  have h := layout_upload (2^done) (2^degree) m (rootOfUnity (2^bits)) input before after
    hp hc hperiod previous (by
      intro g hg r hr
      have he := execute g (by simpa [hdv] using hg) r hr
      simpa only [hmv,hdv,hroot,Nat.mul_div_right m hp] using he)
  simpa only [← Nat.pow_add,hnew] using h

theorem output_cover_bits (bits done degree i : Nat) (hd : done+degree ≤ bits)
    (hi : i < 2^bits) :
    ∃ g, g < 2^bits/2^degree ∧ ∃ r, r < 2^degree ∧
      g/(2^done)*(2^done*2^degree)+g%(2^done)+r*(2^done) = i := by
  let m := 2^(bits-(done+degree))
  have hn : 2^done*2^degree*m = 2^bits := by
    rw [← Nat.pow_add,← Nat.pow_add]
    congr 1
    omega
  have hpm : 2^done*m = 2^(bits-degree) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdv : 2^bits/2^degree = 2^done*m := by
    rw [Nat.pow_div (by omega : degree ≤ bits) (by decide),hpm]
  obtain ⟨g,hg,r,hr,he⟩ := output_cover (2^done) (2^degree) m i
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) (by simpa [hn] using hi)
  exact ⟨g,by simpa [hdv] using hg,r,hr,he⟩

end Obend.Hardware.Gpu.Ntt
