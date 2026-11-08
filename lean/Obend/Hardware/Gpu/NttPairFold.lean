module
public import Obend.Hardware.Gpu.NttRegisterValues
public import Obend.Hardware.Gpu.NttPhaseIndex
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.RegisterValues
open GoldilocksSource

abbrev pairIndex (bit j side : Nat) : Nat := 2*j-j%bit+side*bit

theorem pairStep_low (bit twiddle j : Nat) (hb : 0 < bit) (values : Nat → Nat) :
    pairStep bit twiddle j values (2*j-j%bit) =
      (values (2*j-j%bit)+values (2*j-j%bit+bit))%goldilocksP := by
  simp [pairStep,update,show bit ≠ 0 by omega]

theorem pairStep_high (bit twiddle j : Nat) (values : Nat → Nat) :
    pairStep bit twiddle j values (2*j-j%bit+bit) =
      (((values (2*j-j%bit)+goldilocksP-values (2*j-j%bit+bit))%goldilocksP)*twiddle)%goldilocksP := by
  simp [pairStep,update]

/-- A different pair cannot change either register of this pair. -/
theorem pairStep_frame_other (bit twiddle j target side : Nat) (hb : 0 < bit)
    (hs : side < 2) (hne : j ≠ target) (values : Nat → Nat) :
    pairStep bit twiddle j values (pairIndex bit target side) = values (pairIndex bit target side) := by
  have hl : pairIndex bit target side ≠ 2*j-j%bit := by
    intro he
    have hx := pair_register_injective target j bit side 0 hb hs (by decide) (by simpa using he)
    exact hne hx.1.symm
  have hh : pairIndex bit target side ≠ 2*j-j%bit+bit := by
    intro he
    have hx := pair_register_injective target j bit side 1 hb hs (by decide) (by simpa using he)
    exact hne hx.1.symm
  simp [pairStep,update,hl,hh]

theorem pairStep_pair_congr (bit twiddle j side : Nat) (hb : 0 < bit) (hs : side < 2)
    (v w : Nat → Nat) (h0 : v (2*j-j%bit)=w (2*j-j%bit))
    (h1 : v (2*j-j%bit+bit)=w (2*j-j%bit+bit)) :
    pairStep bit twiddle j v (pairIndex bit j side) = pairStep bit twiddle j w (pairIndex bit j side) := by
  have hside : side=0 ∨ side=1 := by omega
  rcases hside with rfl | rfl
  · simpa only [pairIndex,Nat.zero_mul,Nat.add_zero,pairStep_low bit twiddle j hb,h0,h1]
  · simpa only [pairIndex,Nat.one_mul,pairStep_high,h0,h1]

private theorem fold_frame (xs : List Nat) (bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (hne : ∀ j, j ∈ xs → j ≠ target) :
    (xs.foldl (fun v j => pairStep bit (twiddle j) j v) values) (pairIndex bit target side) =
      values (pairIndex bit target side) := by
  induction xs generalizing values with
  | nil => rfl
  | cons j xs ih =>
    rw [List.foldl_cons,ih _ (fun k hk => hne k (by simp [hk]))]
    exact pairStep_frame_other bit _ j target side hb hs (hne j (by simp)) values

/-- Sequential updates read the original pair values because pair footprints
are disjoint. This identifies the actual order-preserving fold, not a parallel oracle. -/
theorem fold_pair (xs : List Nat) (bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (hu : xs.Nodup) (ht : target ∈ xs) :
    (xs.foldl (fun v j => pairStep bit (twiddle j) j v) values) (pairIndex bit target side) =
      pairStep bit (twiddle target) target values (pairIndex bit target side) := by
  induction xs generalizing values with
  | nil => cases ht
  | cons j xs ih =>
    have hn := List.nodup_cons.mp hu
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ht with he | htail
    · subst target
      apply fold_frame xs bit j side hb hs twiddle
      intro k hk he
      subst k
      exact hn.1 hk
    · rw [ih _ hn.2 htail]
      have hne : j ≠ target := fun he => hn.1 (he.symm ▸ htail)
      apply pairStep_pair_congr bit _ target side hb hs
      · simpa [pairIndex] using pairStep_frame_other bit (twiddle j) j target 0 hb (by decide) hne values
      · simpa [pairIndex] using pairStep_frame_other bit (twiddle j) j target 1 hb (by decide) hne values

theorem roundValues_pair (pairs bit target side : Nat) (hb : 0 < bit) (hs : side < 2)
    (twiddle values : Nat → Nat) (ht : target < pairs) :
    roundValues pairs bit twiddle values (pairIndex bit target side) =
      pairStep bit (twiddle target) target values (pairIndex bit target side) :=
  fold_pair _ bit target side hb hs twiddle values (List.nodup_range) (List.mem_range.mpr ht)

/-- Both source pair writes have the whole-vector flattened butterfly value. -/
theorem roundValues_flat_pair (radix stride lane bit root j side : Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hj : j < radix/2) (hside : side < 2)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<radix → values r=input (laneRegisterIndex radix stride lane r))
    (canonical : ∀ r, r<radix → values r<goldilocksP) :
    roundValues (radix/2) bit (fun j => modPow root (phasePairOffset stride lane j bit)) values (pairIndex bit j side) =
      flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane (pairIndex bit j side)) := by
  rw [roundValues_pair _ _ _ _ hb hside _ _ hj]
  have hr := pair_register_bounds radix j bit hb hd hj
  have h0 := hvalues _ hr.1
  have h1 := hvalues _ hr.2
  have hc := canonical _ hr.2
  have hcases : side=0 ∨ side=1 := by omega
  rcases hcases with rfl | rfl
  · simp only [pairIndex,Nat.zero_mul,Nat.add_zero,pairStep_low bit _ j hb,
      phase_pair_low_value radix stride lane j bit root input hs hb hd]
    simpa only [addMod,h0,h1]
  · simp only [pairIndex,Nat.one_mul,pairStep_high,
      phase_pair_high_value radix stride lane j bit root input hs hb hd]
    rw [←h0,←h1,subMod_eq_nat _ _ hc]
    rfl

theorem pair_cover (radix bit r : Nat) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hr : r < radix) :
    ∃ j, j<radix/2 ∧ ∃ side, side<2 ∧ pairIndex bit j side=r := by
  obtain ⟨q,hq⟩ := hd
  have he : radix=(2*q)*bit := by rw [hq]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hcount : radix/2=q*bit := by
    rw [he,Nat.mul_assoc,Nat.mul_div_right _ (by decide : 0<2)]
  refine ⟨(r/bit/2)*bit+r%bit,?_,r/bit%2,Nat.mod_lt _ (by decide),?_⟩
  · rw [hcount]
    exact laneRegisterIndex_cover_lane_lt 2 bit q r hb (by decide) (by rwa [←he])
  · rw [pairIndex,pair_register_as_index]
    exact laneRegisterIndex_cover 2 bit r hb (by decide)

/-- A complete sequential source pair loop is exactly the simultaneous flat DIF
layer at every register position. No restriction to sampled radices is used. -/
theorem roundValues_flat (radix stride lane bit root r : Nat)
    (hs : 0 < stride) (hb : 0 < bit) (hd : 2*bit ∣ radix) (hr : r<radix)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<radix → values r=input (laneRegisterIndex radix stride lane r))
    (canonical : ∀ r, r<radix → values r<goldilocksP) :
    roundValues (radix/2) bit (fun j => modPow root (phasePairOffset stride lane j bit)) values r =
      flatButterfly (bit*stride) root input (laneRegisterIndex radix stride lane r) := by
  obtain ⟨j,hj,side,hside,he⟩ := pair_cover radix bit r hb hd hr
  rw [←he]
  exact roundValues_flat_pair radix stride lane bit root j side hs hb hd hj hside input values hvalues canonical

/-- The actual register-round arithmetic and actual global-table exponents denote
one whole-vector DIF level, at the source's exact lane/register coordinates. -/
theorem phase_roundValues_layer (total bits done degree round lane r : Nat)
    (ht : total ≤ 32) (hb : bits ≤ total) (hdegree : done+degree ≤ bits)
    (hround : round<degree) (hlane : lane < 2^bits/2^degree) (hr : r<2^degree)
    (input values : Nat → Nat)
    (hvalues : ∀ r, r<2^degree → values r=input
      (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r))
    (canonical : ∀ r, r<2^degree → values r<goldilocksP) :
    roundValues (2^degree/2) (2^degree/2^(round+1))
      (fun j => modPow (rootOfUnity (2^total))
        (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
          (2^(done+round)*(2^total/2^bits)))) values r =
      difLayer bits (done+round) input
        (laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) lane r) := by
  have hi := phase_index_lt bits done degree lane r hdegree hlane hr
  rw [difLayer_flat bits (done+round) input (by omega) _ hi]
  have twiddle_eq : (fun j => modPow (rootOfUnity (2^total))
      (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)) *
        (2^(done+round)*(2^total/2^bits)))) =
      (fun j => modPow (rootOfUnity (2^(bits-(done+round))))
        (phasePairOffset (2^bits/(2^done*2^degree)) lane j (2^degree/2^(round+1)))) := by
    funext j
    exact phase_twiddle total bits done round _ ht hb (by omega)
  rw [twiddle_eq,←phase_pair_distance bits done degree round hdegree hround]
  have hs : 0 < 2^bits/(2^done*2^degree) := by
    rw [phase_stride bits done degree hdegree]
    exact Nat.two_pow_pos _
  have hbit := phase_bit degree round hround
  exact roundValues_flat (2^degree) _ lane _ _ r hs hbit.1 hbit.2 hr input values hvalues canonical

end Obend.Hardware.Gpu.Ntt.RegisterValues
