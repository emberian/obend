module
public import Obend.Hardware.Gpu.NttPhaseIndex
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt

/-- Every tile position is covered by an actually launched lane and register
of the source phase, including its computed stride. -/
theorem phase_index_cover (bits done degree i : Nat)
    (h : done + degree ≤ bits) (hi : i < 2^bits) :
    ∃ lane, lane < 2^bits / 2^degree ∧ ∃ r, r < 2^degree ∧
      laneRegisterIndex (2^degree) (2^bits / (2^done * 2^degree)) lane r = i := by
  rw [phase_stride bits done degree h]
  have he : 2^bits = (2^degree * 2^done) * 2^(bits-done-degree) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hlanes : 2^bits / 2^degree = 2^done * 2^(bits-done-degree) := by
    conv => lhs; rw [he, Nat.mul_assoc, Nat.mul_div_right _ (Nat.two_pow_pos degree)]
  refine ⟨(i / 2^(bits-done-degree) / 2^degree) * 2^(bits-done-degree) +
    i % 2^(bits-done-degree), ?_, i / 2^(bits-done-degree) % 2^degree, ?_, ?_⟩
  · rw [hlanes]
    apply laneRegisterIndex_cover_lane_lt _ _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    rwa [← he]
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact laneRegisterIndex_cover _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _)

end Obend.Hardware.Gpu.Ntt
end
