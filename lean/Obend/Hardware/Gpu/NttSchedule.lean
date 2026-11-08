module
public import Obend.Hardware.Gpu.Ntt
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt

/-- Positive integer ceiling division never produces an empty or oversized
piece when the dividend and divisor are both positive. -/
theorem ceil_bounds (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    0 < (n+d-1)/d ∧ (n+d-1)/d ≤ n := by
  constructor
  · apply Nat.div_pos
    · omega
    · exact hd
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have hmul : n ≤ n*d := Nat.le_mul_of_pos_right n hd
    rw [Nat.succ_mul]
    omega

theorem ceil_covers (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    n ≤ d*((n+d-1)/d) := by
  have h := Nat.mod_add_div (n+d-1) d
  have hr := Nat.mod_lt (n+d-1) hd
  omega

theorem uploadDegree_bounds (maximum remaining : Nat) (hm : 0 < maximum)
    (hr : 0 < remaining) :
    0 < uploadDegree maximum remaining ∧ uploadDegree maximum remaining ≤ remaining := by
  have h := ceil_bounds remaining maximum hr hm
  exact ceil_bounds remaining _ hr h.1

theorem uploadDegree_le_maximum (maximum remaining : Nat) (hm : 0 < maximum)
    (hr : 0 < remaining) : uploadDegree maximum remaining ≤ maximum := by
  let uploads := (remaining+maximum-1)/maximum
  have hu : 0 < uploads := (ceil_bounds remaining maximum hr hm).1
  have hc : remaining ≤ maximum*uploads := ceil_covers remaining maximum hr hm
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hu).mpr
  rw [Nat.succ_mul]
  omega

/-- Every scheduled upload makes progress; the schedule covers all binary
layers for every transform size, not just the benchmark sizes. -/
theorem uploadDegrees_sum (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (hf : remaining ≤ fuel) : (uploadDegrees maximum fuel remaining).sum = remaining := by
  induction fuel generalizing remaining with
  | zero =>
    have hz : remaining = 0 := by omega
    simp [uploadDegrees,hz]
  | succ fuel ih =>
    simp only [uploadDegrees]
    split
    · rename_i hz; simp [hz]
    · rename_i hz
      have hb := uploadDegree_bounds maximum remaining hm (by omega)
      rw [List.sum_cons,ih (remaining-uploadDegree maximum remaining) (by omega)]
      omega

theorem uploadDegrees_positive (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (degree : Nat) (hd : degree ∈ uploadDegrees maximum fuel remaining) : 0 < degree := by
  induction fuel generalizing remaining with
  | zero => simp [uploadDegrees] at hd
  | succ fuel ih =>
    simp only [uploadDegrees] at hd
    split at hd
    · simp at hd
    · rename_i hn
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact (uploadDegree_bounds maximum remaining hm (by omega)).1
      · exact ih _ hd

theorem uploadDegrees_bounded (maximum fuel remaining : Nat) (hm : 0 < maximum)
    (degree : Nat) (hd : degree ∈ uploadDegrees maximum fuel remaining) : degree ≤ maximum := by
  induction fuel generalizing remaining with
  | zero => simp [uploadDegrees] at hd
  | succ fuel ih =>
    simp only [uploadDegrees] at hd
    split at hd
    · simp at hd
    · rename_i hn
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact uploadDegree_le_maximum maximum remaining hm (by omega)
      · exact ih _ hd

open Obend.Hardware.ArrayKernel

/-- Composition along the actual constructed list of upload dispatches. The
invariant is indexed by the processed bit count and the current device buffer. -/
theorem buildUploads_invariant (n : Nat) (degrees : List Nat)
    (transform : Dispatch → Dispatch) (I : Nat → Nat → Memory → Prop) (limit : Nat)
    (available : List Dispatch)
    (step : ∀ degree ∈ degrees, ∀ done input mem,
      BlockNtt.dispatch n done degree input (1-input) ∈ available →
      done+degree ≤ limit → I done input mem →
      I (done+degree) (1-input)
        (evalDispatch (transform (BlockNtt.dispatch n done degree input (1-input))) mem))
    (done input : Nat) (mem : Memory)
    (members : ∀ d ∈ (buildUploads n degrees done input).1, d ∈ available)
    (hlimit : done+degrees.sum ≤ limit) (hi : I done input mem) :
    I (done+degrees.sum) (buildUploads n degrees done input).2
      (((buildUploads n degrees done input).1.map transform).foldl
        (fun m d => evalDispatch d m) mem) := by
  induction degrees generalizing done input mem with
  | nil => simpa [buildUploads] using hi
  | cons degree degrees ih =>
    have hs := step degree (by simp) done input mem
      (members _ (by simp [buildUploads]))
      (by simp only [List.sum_cons] at hlimit; omega) hi
    have ht := ih (fun d hd => step d (by simp [hd])) (done+degree) (1-input) _
      (fun d hd => members d (by simp [buildUploads,hd]))
      (by simpa [List.sum_cons,Nat.add_assoc] using hlimit) hs
    simpa [buildUploads,Nat.add_assoc] using ht

/-- Ping-pong device allocation always ends in one of the two device arrays. -/
theorem buildUploads_output (n : Nat) (degrees : List Nat) (done input : Nat)
    (hi : input ≤ 1) : (buildUploads n degrees done input).2 ≤ 1 := by
  induction degrees generalizing done input with
  | nil => exact hi
  | cons degree degrees ih => exact ih (done+degree) (1-input) (by omega)

end Obend.Hardware.Gpu.Ntt
