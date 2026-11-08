module
public import Obend.Hardware.Gpu.NttRoots
@[expose] public section
namespace Obend.Hardware.Gpu.Ntt
open GoldilocksSource Obend.Hardware.ArrayHypergraph

theorem powersLoop_values (ω count start : Nat) (xs : Array Word) :
    (powersLoop ω count xs (modPow ω start)).toList = xs.toList ++
      (List.range' start count).map (fun e => BitVec.ofNat 64 (modPow ω e)) := by
  induction count generalizing start xs with
  | zero => simp [powersLoop]
  | succ count ih =>
    have next : modPow ω start * ω % goldilocksP = modPow ω (start+1) := by
      rw [modPow_add,modPow_one]
      simp
    simp only [powersLoop,next,ih,List.range'_succ,List.map_cons,Array.toList_push]
    simp [List.append_assoc]

/-- The actual linear-time source table contains the certified root powers. -/
theorem twiddlePowers_values (n ω : Nat) :
    (twiddlePowers n ω).toList =
      (List.range n).map (fun e => BitVec.ofNat 64 (modPow ω e)) := by
  have h := powersLoop_values ω n 0 #[]
  simpa [twiddlePowers,List.range_eq_range'] using h

theorem twiddlePowers_size (n ω : Nat) : (twiddlePowers n ω).size = n := by
  have h := congrArg List.length (twiddlePowers_values n ω)
  simpa using h

theorem twiddlePowers_getD (n ω i : Nat) (hi : i < n) :
    (twiddlePowers n ω).getD i 0#64 = BitVec.ofNat 64 (modPow ω i) := by
  have h := congrArg (fun xs : List Word => xs[i]?) (twiddlePowers_values n ω)
  simp only [Array.getElem?_toList,List.getElem?_map,List.getElem?_range hi,Option.map_some] at h
  simp [Array.getD_eq_getD_getElem?,h]

theorem twiddlePowers_toNat (n ω i : Nat) (hi : i < n) :
    ((twiddlePowers n ω).getD i 0#64).toNat = modPow ω i := by
  rw [twiddlePowers_getD n ω i hi]
  apply Nat.mod_eq_of_lt
  have h := modPow_lt ω i
  have hp : goldilocksP < 2^64 := by decide
  omega

open Obend.Hardware.ArrayKernel

/-- Actual program initialization preserves the generated constant table. -/
theorem initial_twiddles (n : Nat) (input : Array Word) :
    (initialMemory (nttBlockProgram n) [input]).getD 4 #[] =
      twiddlePowers n (rootOfUnity n) := by
  simp [initialMemory,nttBlockProgram]

end Obend.Hardware.Gpu.Ntt
