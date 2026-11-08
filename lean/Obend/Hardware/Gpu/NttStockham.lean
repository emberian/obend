module
public import Obend.Hardware.Gpu.NttRoots
public import Obend.Hardware.Gpu.NttDFTSpec
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.Stockham
open GoldilocksSource

/-- The value invariant after `p` transformed digits. The remaining digits are
strided by `stride`; it specializes to the DFT when `stride = 1`. -/
def partialTransform (p stride : Nat) (ω : Nat) (input : Nat → Nat) (b k : Nat) : Nat :=
  Sum.sum p (fun j => input (b+j*stride) * modPow ω (j*k*stride)) % goldilocksP

theorem initial (ω : Nat) (input : Nat → Nat) (b k stride : Nat) :
    partialTransform 1 stride ω input b k = input b % goldilocksP := by
  simp [partialTransform,Sum.sum]

theorem period_multiple (ω n e q : Nat) (hn : modPow ω n = 1) :
    modPow ω (e+n*q) = modPow ω e := by
  rw [modPow_add,modPow_mul,hn,modPow_one_base]
  simp [modPow_eq]

/-- The exponent identity of one Stockham upload, including the discarded full
period. This is universal in all coordinates, rather than a checked table. -/
theorem exponent (p c m j t k r : Nat) :
    (j*c+t)*(k+r*p)*m =
      j*k*(c*m) + t*k*m + t*r*(p*m) + (p*c*m)*(j*r) := by
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- One term of the strided partial DFT after combining an upload. -/
theorem term (p c m ω j t k r q : Nat) (input : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1) :
    ((input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
      modPow ω (t*k*m)) * modPow ω (t*r*(p*m))) % goldilocksP =
    (input (q+(j*c+t)*m) * modPow ω ((j*c+t)*(k+r*p)*m)) % goldilocksP := by
  have hi : q+t*m+j*(c*m) = q+(j*c+t)*m := by
    simp [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [hi,exponent,period_multiple _ _ _ _ hperiod]
  simp [modPow_add,Nat.mul_assoc]

/-- A radix-`c` Stockham upload: each old partial transform is twiddled, then
transformed across the next digit. This is the exact algebraic invariant used
by the fused load/store permutation of `BlockNtt.phase`. -/
theorem upload (p c m ω q k r : Nat) (input : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1) :
    Sum.sum c (fun t =>
      partialTransform p (c*m) ω input (q+t*m) k *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP =
      partialTransform (p*c) m ω input q (k+r*p) := by
  unfold partialTransform
  have expand : ∀ t,
      ((Sum.sum p (fun j => input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m))) % goldilocksP) *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP =
      Sum.sum p (fun j => input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
        modPow ω (t*k*m) * modPow ω (t*r*(p*m))) % goldilocksP := by
    intro t
    rw [Sum.mul_right,Sum.mul_right]
    simp [Nat.mul_assoc]
  calc
    _ = Sum.sum c (fun t => Sum.sum p (fun j =>
          input (q+t*m+j*(c*m)) * modPow ω (j*k*(c*m)) *
            modPow ω (t*k*m) * modPow ω (t*r*(p*m)))) % goldilocksP :=
      Sum.cong_mod _ _ _ _ (fun t _ => expand t)
    _ = Sum.sum c (fun t => Sum.sum p (fun j =>
          input (q+(j*c+t)*m) * modPow ω ((j*c+t)*(k+r*p)*m))) % goldilocksP := by
      apply Sum.cong_mod
      intro t ht
      apply Sum.cong_mod
      intro j hj
      exact term p c m ω j t k r q input hperiod
    _ = _ := by
      rw [Sum.swap]
      exact congrArg (fun v => v % goldilocksP)
        (Sum.blocks p c (fun j => input (q+j*m) * modPow ω (j*(k+r*p)*m))).symm

/-- The upload factorization stated with the shared DFT specification. The
input view is exactly the strided load view of a Stockham workgroup. -/
theorem upload_dft (p c m ω q k r : Nat) (input values : Nat → Nat)
    (hperiod : modPow ω (p*c*m) = 1)
    (hvalues : ∀ t, t < c → values t % goldilocksP =
      partialTransform p (c*m) ω input (q+t*m) k) :
    dft c (modPow ω (p*m))
      (fun t => mulMod (values t) (modPow ω (t*k*m))) r =
      partialTransform (p*c) m ω input q (k+r*p) := by
  rw [← upload p c m ω q k r input hperiod]
  unfold dft sumMod
  apply Sum.cong_mod
  intro t ht
  have hp : modPow (modPow ω (p*m)) (t*r) = modPow ω (t*r*(p*m)) := by
    rw [← modPow_mul,Nat.mul_comm (p*m)]
  rw [hp,← hvalues t ht]
  simp [mulMod,Nat.mul_assoc]

/-- Canonical output indexing after one upload. These coordinates account for
all outputs, including the transpose fused into each final register store. -/
theorem output_index (p c m q k r : Nat) (hp : 0 < p) (hk : k < p)
    (hr : r < c) (hq : q < m) :
    let g := q*p+k
    g/p*(p*c) + g%p + r*p = q*(p*c)+(k+r*p) ∧
      k+r*p < p*c ∧ q*(p*c)+(k+r*p) < p*c*m := by
  have hd : (q*p+k)/p = q := by
    rw [Nat.mul_comm q p,Nat.mul_add_div hp,Nat.div_eq_of_lt hk,Nat.add_zero]
  have hm : (q*p+k)%p = k := Nat.mul_add_mod_of_lt hk
  have hkr : k+r*p < p*c := by
    have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul,Nat.mul_comm c p] at h
    omega
  dsimp only
  rw [hd,hm]
  constructor
  · omega
  constructor
  · exact hkr
  · have h := Nat.mul_le_mul_right (p*c) (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m (p*c)] at h
    omega

/-- Input addressing of a workgroup exposes one next-digit sequence of the old
partial transforms, with no gather table or intermediate global transpose. -/
theorem input_index (p m q k t : Nat) :
    q*p+k+t*(p*m) = (q+t*m)*p+k := by
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Natural-order partial transforms in the physical Stockham device layout. -/
def LayoutValues (p stride ω : Nat) (input values : Nat → Nat) : Prop :=
  ∀ b, b < stride → ∀ k, k < p → values (b*p+k) % goldilocksP =
    partialTransform p stride ω input b k

/-- The permutation and twiddle theorem lifted from a single workgroup to its
whole device array. `execute` is the tile-DFT interface discharged by the actual
phase/register proof; no DFT values are supplied to construction or emission. -/
theorem layout_upload (p c m ω : Nat) (input before after : Nat → Nat)
    (hp : 0 < p) (hc : 0 < c) (hperiod : modPow ω (p*c*m) = 1)
    (previous : LayoutValues p (c*m) ω input before)
    (execute : ∀ g, g < p*m → ∀ r, r < c →
      after (g/p*(p*c)+g%p+r*p) =
        dft c (modPow ω (p*m))
          (fun t => mulMod (before (g+t*(p*m))) (modPow ω (t*(g%p)*m))) r) :
    LayoutValues (p*c) m ω input after := by
  intro q hq k hk
  let low := k%p
  let high := k/p
  have hlo : low < p := Nat.mod_lt k hp
  have hhi : high < c := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hk)
  have hsplit : low+high*p = k := by
    simpa [low,high,Nat.mul_comm] using Nat.mod_add_div k p
  let g := q*p+low
  have hg : g < p*m := by
    have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m p] at h
    omega
  have hgm : g%p = low := Nat.mul_add_mod_of_lt hlo
  have hgi := (output_index p c m q low high hp hlo hhi hq).1
  have he := execute g hg high hhi
  rw [hgm] at he
  have indexEq : g/p*(p*c)+g%p+high*p = q*(p*c)+k := by
    simpa only [hsplit] using hgi
  rw [hgm] at indexEq
  rw [indexEq] at he
  have values : ∀ t, t < c → before (g+t*(p*m)) % goldilocksP =
      partialTransform p (c*m) ω input (q+t*m) low := by
    intro t ht
    have hb : q+t*m < c*m := by
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt ht)
      rw [Nat.succ_mul] at h
      omega
    change before (q*p+low+t*(p*m)) % goldilocksP = _
    rw [input_index]
    exact previous (q+t*m) hb low hlo
  have hu := upload_dft p c m ω q low high input (fun t => before (g+t*(p*m))) hperiod values
  rw [hsplit] at hu
  rw [he,hu]
  simp [partialTransform]

/-- The upload's natural output permutation covers every device position. -/
theorem output_cover (p c m i : Nat) (hp : 0 < p) (hc : 0 < c) (hi : i < p*c*m) :
    ∃ g, g < p*m ∧ ∃ r, r < c ∧ g/p*(p*c)+g%p+r*p = i := by
  let q := i/(p*c)
  let k := i%(p*c)
  have hpc : 0 < p*c := Nat.mul_pos hp hc
  have hq : q < m := (Nat.div_lt_iff_lt_mul hpc).mpr (by simpa [Nat.mul_comm] using hi)
  have hk : k < p*c := Nat.mod_lt i hpc
  let low := k%p
  let high := k/p
  have hlo : low < p := Nat.mod_lt k hp
  have hhi : high < c := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hk)
  have hs : low+high*p = k := by simpa [low,high,Nat.mul_comm] using Nat.mod_add_div k p
  have hiq : q*(p*c)+k = i := by simpa [q,k,Nat.mul_comm] using Nat.div_add_mod i (p*c)
  refine ⟨q*p+low,?_,high,hhi,?_⟩
  · have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul,Nat.mul_comm m p] at h
    omega
  · rw [(output_index p c m q low high hp hlo hhi hq).1,hs,hiq]

theorem output_bounded (p c m bound : Nat) (after : Nat → Nat) (hp : 0 < p) (hc : 0 < c)
    (written : ∀ g, g < p*m → ∀ r, r < c → after (g/p*(p*c)+g%p+r*p) < bound)
    (i : Nat) (hi : i < p*c*m) : after i < bound := by
  obtain ⟨g,hg,r,hr,he⟩ := output_cover p c m i hp hc hi
  rw [← he]
  exact written g hg r hr

end Obend.Hardware.Gpu.Ntt.Stockham
