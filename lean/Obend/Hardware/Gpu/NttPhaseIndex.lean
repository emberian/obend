module
public import Obend.Hardware.Gpu.NttLayers
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open ArrayKernel GoldilocksSource

/-- Numeric denotation of the actual lane/register source index. -/
def laneRegisterIndex (radix stride lane r : Nat) : Nat :=
  lane/stride*(radix*stride) + lane%stride + r*stride

theorem phaseIndex_eval (radix stride r group lane : Nat) :
    (BlockNtt.phaseIndex radix stride r).eval group lane = laneRegisterIndex radix stride lane r := rfl

theorem laneRegisterIndex_decomp (radix stride lane r : Nat) :
    laneRegisterIndex radix stride lane r = stride*(radix*(lane/stride)+r)+lane%stride := by
  simp only [laneRegisterIndex,Nat.mul_add]
  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem laneRegisterIndex_div (radix stride lane r : Nat) (hs : 0 < stride) :
    laneRegisterIndex radix stride lane r / stride = radix*(lane/stride)+r := by
  rw [laneRegisterIndex_decomp,Nat.mul_add_div hs]
  have hm := Nat.mod_lt lane hs
  rw [Nat.div_eq_of_lt hm,Nat.add_zero]

theorem laneRegisterIndex_mod (radix stride lane r : Nat) :
    laneRegisterIndex radix stride lane r % stride = lane%stride := by
  rw [laneRegisterIndex_decomp]
  simp

/-- Register coordinate recovered from the actual physical index. -/
theorem laneRegisterIndex_register (radix stride lane r : Nat) (hs : 0 < stride) (hr : r < radix) :
    laneRegisterIndex radix stride lane r / stride % radix = r := by
  rw [laneRegisterIndex_div _ _ _ _ hs]
  simp [Nat.mod_eq_of_lt hr]

/-- Lane coordinate recovered from the actual physical index. -/
theorem laneRegisterIndex_lane (radix stride lane r : Nat) (hs : 0 < stride) (hr : r < radix) :
    (laneRegisterIndex radix stride lane r / stride / radix)*stride +
      laneRegisterIndex radix stride lane r % stride = lane := by
  rw [laneRegisterIndex_div _ _ _ _ hs,laneRegisterIndex_mod,
    Nat.mul_add_div (by omega : 0 < radix),Nat.div_eq_of_lt hr,Nat.add_zero]
  have h := Nat.mod_add_div lane stride
  rw [Nat.mul_comm (lane/stride) stride]
  omega

/-- The lane/register map is injective; no pair of distinct invocations writes
the same tile position. This is an actual source-coordinate fact. -/
theorem laneRegisterIndex_injective (radix stride lane lane' r r' : Nat)
    (hs : 0 < stride) (hr : r < radix) (hr' : r' < radix)
    (h : laneRegisterIndex radix stride lane r = laneRegisterIndex radix stride lane' r') :
    lane=lane' ∧ r=r' := by
  constructor
  · have hl := laneRegisterIndex_lane radix stride lane r hs hr
    have hl' := laneRegisterIndex_lane radix stride lane' r' hs hr'
    rw [h] at hl
    omega
  · have hl := laneRegisterIndex_register radix stride lane r hs hr
    have hl' := laneRegisterIndex_register radix stride lane' r' hs hr'
    rw [h] at hl
    omega

theorem laneRegisterIndex_lt (radix stride blocks lane r : Nat)
    (hs : 0 < stride) (hl : lane < blocks*stride) (hr : r < radix) :
    laneRegisterIndex radix stride lane r < (radix*blocks)*stride := by
  apply (Nat.div_lt_iff_lt_mul hs).mp
  rw [laneRegisterIndex_div _ _ _ _ hs]
  have hb : lane/stride < blocks := (Nat.div_lt_iff_lt_mul hs).mpr hl
  calc
    radix*(lane/stride)+r < radix*(lane/stride)+radix := Nat.add_lt_add_left hr _
    _ = radix*(lane/stride+1) := by simp [Nat.mul_add]
    _ ≤ radix*blocks := Nat.mul_le_mul_left _ (by omega)

/-- Every tile cell has an explicit lane/register preimage. -/
theorem laneRegisterIndex_cover (radix stride i : Nat) (hs : 0 < stride) (hr : 0 < radix) :
    laneRegisterIndex radix stride ((i/stride/radix)*stride+i%stride) (i/stride%radix) = i := by
  have hm := Nat.mod_lt i hs
  have hl : ((i/stride/radix)*stride+i%stride)/stride = i/stride/radix := by
    rw [Nat.mul_comm (i/stride/radix),Nat.mul_add_div hs,Nat.div_eq_of_lt hm,Nat.add_zero]
  have hmod : ((i/stride/radix)*stride+i%stride)%stride = i%stride := by simp
  rw [laneRegisterIndex_decomp,hl,hmod]
  have h1 := Nat.mod_add_div (i/stride) radix
  have h2 := Nat.mod_add_div i stride
  have he : radix*(i/stride/radix)+i/stride%radix=i/stride := by omega
  rw [he]
  omega

/-- Preimage lanes lie in the launched domain, rather than merely in an
unbounded arithmetic extension of the index map. -/
theorem laneRegisterIndex_cover_lane_lt (radix stride blocks i : Nat)
    (hs : 0 < stride) (hr : 0 < radix) (hi : i < (radix*blocks)*stride) :
    (i/stride/radix)*stride+i%stride < blocks*stride := by
  have hq : i/stride < radix*blocks := (Nat.div_lt_iff_lt_mul hs).mpr hi
  have hb : i/stride/radix < blocks := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa [Nat.mul_comm] using hq)
  have hm := Nat.mod_lt i hs
  have hl := Nat.mul_le_mul_right stride (by omega : i/stride/radix+1 ≤ blocks)
  rw [Nat.add_mul] at hl
  omega

/-- The actual stride division is exact for a supported fused round count. -/
theorem phase_stride (bits done degree : Nat) (h : done+degree ≤ bits) :
    2^bits / (2^done * 2^degree) = 2^(bits-done-degree) := by
  rw [← Nat.pow_add,Nat.pow_div h (by decide)]
  congr 1
  omega

/-- Source load expression, including the first upload's strided input map. -/
theorem phaseLoadIndex_eval (n count radix stride r group lane : Nat) (first : Bool) :
    (BlockNtt.phaseLoadIndex n count radix stride first r).eval group lane =
      if first then group+laneRegisterIndex radix stride lane r*(n/count)
      else laneRegisterIndex radix stride lane r := by
  cases first <;> rfl

/-- Source output expression, including its actual bit-reversal permutation. -/
theorem phaseSaveIndex_eval (count bits p radix stride r group lane : Nat) (last : Bool)
    (hi : laneRegisterIndex radix stride lane r < 2^bits) :
    (BlockNtt.phaseSaveIndex count bits p radix stride last r).eval group lane =
      if last then group/p*(p*count)+group%p+reverseIndex bits (laneRegisterIndex radix stride lane r)*p
      else laneRegisterIndex radix stride lane r := by
  cases last with
  | false => rfl
  | true =>
    simp only [BlockNtt.phaseSaveIndex,ite_true,BlockNtt.addI,BlockNtt.mulI,Ix.eval]
    rw [reverseBits_eval bits group lane (BlockNtt.phaseIndex radix stride r) hi]
    rfl

/-- Source pair-register arithmetic, before multiplying by the physical stride. -/
theorem pair_register_low (j bit : Nat) :
    2*j-j%bit = 2*(bit*(j/bit))+j%bit := by
  have h := Nat.mod_add_div j bit
  omega

def phasePairBase (radix stride lane j bit : Nat) : Nat :=
  lane/stride*(radix*stride) + 2*(bit*(j/bit))*stride

def phasePairOffset (stride lane j bit : Nat) : Nat :=
  lane%stride + j%bit*stride

theorem phase_pair_low_index (radix stride lane j bit : Nat) :
    laneRegisterIndex radix stride lane (2*j-j%bit) =
      phasePairBase radix stride lane j bit + phasePairOffset stride lane j bit := by
  rw [laneRegisterIndex,pair_register_low,Nat.add_mul]
  simp [phasePairBase,phasePairOffset,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem phase_pair_high_index (radix stride lane j bit : Nat) :
    laneRegisterIndex radix stride lane (2*j-j%bit+bit) =
      phasePairBase radix stride lane j bit + phasePairOffset stride lane j bit + bit*stride := by
  have h := phase_pair_low_index radix stride lane j bit
  simpa only [laneRegisterIndex,Nat.add_mul,Nat.add_assoc] using congrArg (· + bit*stride) h

theorem phase_pair_offset_lt (stride lane j bit : Nat) (hs : 0 < stride) (hb : 0 < bit) :
    phasePairOffset stride lane j bit < bit*stride := by
  have hm := Nat.mod_lt lane hs
  have hj := Nat.mod_lt j hb
  have hx := Nat.mul_le_mul_right stride (by omega : j%bit+1 ≤ bit)
  rw [Nat.add_mul,Nat.one_mul] at hx
  unfold phasePairOffset
  omega

theorem phase_pair_aligned (radix stride lane j bit : Nat) (hd : 2*bit ∣ radix) :
    phasePairBase radix stride lane j bit % (2*(bit*stride)) = 0 := by
  obtain ⟨q,hq⟩ := hd
  have he : phasePairBase radix stride lane j bit =
      (2*(bit*stride))*((lane/stride)*q+j/bit) := by
    simp [phasePairBase,hq,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  rw [he,Nat.mul_mod_right]

/-- The flattened level at the source's exact lower register coordinate. -/
theorem phase_pair_low_value (radix stride lane j bit root : Nat) (input : Nat → Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) :
    flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (2*j-j%bit)) =
      addMod (input (laneRegisterIndex radix stride lane (2*j-j%bit)))
        (input (laneRegisterIndex radix stride lane (2*j-j%bit+bit))) := by
  rw [phase_pair_low_index,phase_pair_high_index]
  exact flatButterfly_pair_low _ _ _ _ input
    (phase_pair_aligned radix stride lane j bit hd) (phase_pair_offset_lt stride lane j bit hs hb)

/-- The flattened level at the source's exact upper register coordinate. -/
theorem phase_pair_high_value (radix stride lane j bit root : Nat) (input : Nat → Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) :
    flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (2*j-j%bit+bit)) =
      mulMod (subMod (input (laneRegisterIndex radix stride lane (2*j-j%bit)))
        (input (laneRegisterIndex radix stride lane (2*j-j%bit+bit))))
        (modPow root (phasePairOffset stride lane j bit)) := by
  rw [phase_pair_low_index,phase_pair_high_index]
  exact flatButterfly_pair_high _ _ _ _ input
    (phase_pair_aligned radix stride lane j bit hd) (phase_pair_offset_lt stride lane j bit hs hb)

/-- Source register pair distance is the whole-vector level's exact half-size. -/
theorem phase_pair_distance (bits done degree round : Nat)
    (h : done+degree ≤ bits) (hr : round < degree) :
    (2^degree / 2^(round+1)) * (2^bits / (2^done*2^degree)) =
      2^(bits-(done+round)-1) := by
  rw [phase_stride bits done degree h,Nat.pow_div (by omega) (by decide),←Nat.pow_add]
  congr 1
  omega

/-- Source global-table twiddle is exactly the root used by the flattened level. -/
theorem phase_twiddle (total bits done round offset : Nat)
    (ht : total ≤ 32) (hb : bits ≤ total) (hl : done+round ≤ bits) :
    modPow (rootOfUnity (2^total)) (offset*(2^(done+round)*(2^total/2^bits))) =
      modPow (rootOfUnity (2^(bits-(done+round)))) offset := by
  rw [root_layer_twiddle bits (done+round) offset hl (by omega)]
  have hr := root_subtransform total bits hb ht
  rw [←hr,←modPow_mul,Nat.pow_div hb (by decide)]
  congr 1
  simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Both registers of a source butterfly use the same already-proved transpose
map (radix two), making disjointness and coverage reusable facts. -/
theorem pair_register_as_index (j bit side : Nat) :
    2*j-j%bit+side*bit = laneRegisterIndex 2 bit j side := by
  rw [pair_register_low,laneRegisterIndex_decomp]
  simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem pair_register_injective (j j' bit side side' : Nat) (hb : 0 < bit)
    (hs : side < 2) (hs' : side' < 2)
    (h : 2*j-j%bit+side*bit = 2*j'-j'%bit+side'*bit) : j=j' ∧ side=side' := by
  simp only [pair_register_as_index] at h
  exact laneRegisterIndex_injective 2 bit j j' side side' hb hs hs' h

theorem pair_register_bounds (radix j bit : Nat) (hb : 0 < bit)
    (hd : 2*bit ∣ radix) (hj : j < radix/2) :
    2*j-j%bit < radix ∧ 2*j-j%bit+bit < radix := by
  obtain ⟨q,hq⟩ := hd
  have hj' : j < q*bit := by
    rw [hq] at hj
    have he : (2*bit*q)/2 = q*bit := by
      rw [Nat.mul_assoc,Nat.mul_div_right _ (by decide : 0<2),Nat.mul_comm]
    rwa [he] at hj
  have bound (side : Nat) (hs : side < 2) : 2*j-j%bit+side*bit < radix := by
    rw [pair_register_as_index]
    have h := laneRegisterIndex_lt 2 bit q j side hb hj' hs
    have he : (2*q)*bit = radix := by rw [hq]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rwa [he] at h
  constructor
  · simpa using bound 0 (by decide)
  · simpa using bound 1 (by decide)

/-- The source's computed bit distance is positive and divides its radix. -/
theorem phase_bit (degree round : Nat) (hr : round < degree) :
    0 < 2^degree/2^(round+1) ∧ 2*(2^degree/2^(round+1)) ∣ 2^degree := by
  rw [Nat.pow_div (by omega) (by decide)]
  constructor
  · exact Nat.two_pow_pos _
  · have he : 2 * 2^(degree-(round+1)) = 2^(degree-round) := by
      rw [Nat.mul_comm,←Nat.pow_succ]
      congr 1
      omega
    rw [he]
    exact Nat.pow_dvd_pow 2 (by omega)

/-- Bounds needed by the actual `regs[i0]!` and `regs[i1]!` accesses. -/
theorem phase_register_bounds (degree round j : Nat) (hr : round < degree)
    (hj : j < 2^degree/2) :
    2*j-j%(2^degree/2^(round+1)) < 2^degree ∧
      2*j-j%(2^degree/2^(round+1)) + 2^degree/2^(round+1) < 2^degree := by
  have hb := phase_bit degree round hr
  exact pair_register_bounds (2^degree) j _ hb.1 hb.2 hj

/-- Actual launched lanes and allocated radix imply a bounded shared-tile index. -/
theorem phase_index_lt (bits done degree lane r : Nat)
    (h : done+degree ≤ bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r < 2^bits := by
  rw [phase_stride bits done degree h]
  have he : 2^bits = (2^degree*2^done)*2^(bits-done-degree) := by
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  have hlanes : 2^bits/2^degree = 2^done*2^(bits-done-degree) := by
    conv => lhs; rw [he,Nat.mul_assoc,Nat.mul_div_right _ (Nat.two_pow_pos degree)]
  rw [hlanes] at hl
  have hb := laneRegisterIndex_lt (2^degree) (2^(bits-done-degree)) (2^done) lane r
    (Nat.two_pow_pos _) hl hr
  rwa [←he] at hb

/-- Actual first-phase strided loads stay within the original transform input. -/
theorem phase_load_first_lt (total bits done degree group lane r : Nat)
    (hb : bits ≤ total) (h : done+degree ≤ bits)
    (hg : group < 2^total/2^bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    (BlockNtt.phaseLoadIndex (2^total) (2^bits) (2^degree)
      (2^bits/(2^done*2^degree)) true r).eval group lane < 2^total := by
  rw [phaseLoadIndex_eval]
  simp only [ite_true]
  have hi := phase_index_lt bits done degree lane r h hl hr
  have hp : 2^bits*(2^total/2^bits) = 2^total :=
    Nat.mul_div_cancel_left' (Nat.pow_dvd_pow 2 hb)
  have hx := Nat.mul_le_mul_right (2^total/2^bits) (by omega :
    laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r+1 ≤ 2^bits)
  rw [Nat.add_mul,Nat.one_mul,hp] at hx
  omega

/-- Later-phase shared loads stay within the tile. -/
theorem phase_load_later_lt (n bits done degree group lane r : Nat)
    (h : done+degree ≤ bits) (hl : lane < 2^bits/2^degree) (hr : r < 2^degree) :
    (BlockNtt.phaseLoadIndex n (2^bits) (2^degree)
      (2^bits/(2^done*2^degree)) false r).eval group lane < 2^bits :=
  phase_index_lt bits done degree lane r h hl hr

/-- Every actual register-round exponent is below the complete twiddle table. -/
theorem phase_round_exponent_lt (total bits done degree round lane j : Nat)
    (hb : bits ≤ total) (h : done+degree ≤ bits) (hr : round < degree) :
    phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
      (2^(done+round)*(2^total/2^bits)) < 2^total := by
  have hs : 0 < 2^bits/(2^done*2^degree) := by
    rw [phase_stride bits done degree h]
    exact Nat.two_pow_pos _
  have hbit := (phase_bit degree round hr).1
  have hoff := phase_pair_offset_lt _ lane j _ hs hbit
  rw [phase_pair_distance bits done degree round h hr] at hoff
  have hscale : 0 < 2^(done+round)*(2^total/2^bits) := by
    rw [Nat.pow_div hb (by decide)]
    exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hx := Nat.mul_lt_mul_of_pos_right hoff hscale
  have he : 2^(bits-(done+round)-1)*(2^(done+round)*(2^total/2^bits)) = 2^(total-1) := by
    rw [Nat.pow_div hb (by decide),←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  rw [he] at hx
  exact Nat.lt_trans hx (Nat.pow_lt_pow_of_lt (by decide) (by omega))

end Obend.Hardware.Gpu.Ntt
