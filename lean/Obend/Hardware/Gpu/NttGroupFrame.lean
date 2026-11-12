module
public import Obend.Hardware.Gpu.NttDispatchGeometry
@[expose] public section
namespace Obend.Hardware.Gpu.NttGroupFrame
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttDispatchGeometry Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

/-- A packed phase's device stores belong only to the original groups packed
into its own workgroup. Shared-row writes cannot alias a device destination. -/
theorem batch_phase_other_group (n bits p done degree src out dst stride k g G r : Nat)
    (first last : Bool) (hp : 0 < p) (hk : 0 < k) (hdst : dst ≤ 1)
    (hdegree : done+degree ≤ bits) (hr : r < 2^bits) (hgroup : G/k ≠ g)
    (hdevice : last=true → out=dst) (hshared : last=false → out=2 ∨ out=3) :
    (dst,outputAddress p (2^bits) G r) ∉
      (batchPhase stride k (phase n (2^bits) bits p done degree src out first last)).writeAddresses g := by
  rw [batch_phase_addresses]
  intro hmem
  obtain ⟨lane,hlane,hmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨reg,hreg,he⟩ := List.mem_map.mp hmem
  have hout : out=dst := congrArg Prod.fst he
  have haddr := congrArg Prod.snd he
  have hl := List.mem_range.mp hlane
  have hreg := List.mem_range.mp hreg
  cases last with
  | false => have h := hshared rfl; omega
  | true =>
    subst out
    let lanes := 2^bits/2^degree
    have hlanes : 0 < lanes := by
      dsimp [lanes]
      rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
      exact Nat.two_pow_pos _
    have htile : lane/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [lanes,Nat.mul_comm] using hl)
    have hlocal := Nat.mod_lt lane hlanes
    have hindex := phase_index_lt bits done degree (lane%lanes) reg hdegree hlocal hreg
    rw [batchIndex_eval] at haddr
    change tileIndex stride (lane/lanes) dst _ = outputAddress p (2^bits) G r at haddr
    have h2 : dst ≠ 2 := by omega
    have h3 : dst ≠ 3 := by omega
    simp only [tileIndex,show (dst==2 || dst==3)=false by simp [h2,h3],Bool.false_eq_true,ite_false] at haddr
    rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hindex] at haddr
    change outputAddress p (2^bits) (g*k+lane/lanes) _ = outputAddress p (2^bits) G r at haddr
    have hg := (outputAddress_injective p (2^bits) _ _ _ _ hp
      (reverseIndex_lt bits _ hindex) hr haddr).1
    apply hgroup
    rw [←hg,Nat.mul_comm g k,Nat.mul_add_div hk,Nat.div_eq_of_lt htile,Nat.add_zero]

/-- The actual source phase list satisfies group separation at every local
layer, including the alternating shared rows before its final device write. -/
theorem buildPhases_other_group (n bits p dst stride k g G r done input : Nat)
    (chunks : List Nat) (hp : 0 < p) (hk : 0 < k) (hdst : dst ≤ 1)
    (hbound : done+chunks.sum ≤ bits) (hr : r < 2^bits) (hgroup : G/k ≠ g) :
    ∀ ph ∈ buildPhases n bits p dst done input chunks,
      (dst,outputAddress p (2^bits) G r) ∉ (batchPhase stride k ph).writeAddresses g := by
  induction chunks generalizing done input with
  | nil => intro ph hph; cases hph
  | cons chunk chunks ih =>
    intro ph hph
    simp only [buildPhases,List.mem_cons] at hph
    rcases hph with hph | hph
    · subst ph
      apply batch_phase_other_group n bits p done chunk input _ dst stride k g G r _ _ hp hk hdst
        (by simp only [List.sum_cons] at hbound; omega) hr hgroup
      · intro hlast; simp only [hlast,ite_true]
      · intro hlast
        simp only [hlast,Bool.false_eq_true,ite_false]
        split <;> simp
    · apply ih (done+chunk) _ (by simp only [List.sum_cons] at hbound; omega) ph hph

/-- Every actual packed workgroup preserves destination cells assigned to all
other packed workgroups. No value or memory-bound assumption is needed. -/
theorem group_other_output (n logP bits src dst stride g G r : Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hgroup : G/packing (dispatch n logP bits src dst) ≠ g) :
    valueAt (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem)
      dst (outputAddress (2^logP) (2^bits) G r) =
      valueAt mem dst (outputAddress (2^logP) (2^bits) G r) := by
  apply evalPhases_cell_frame
  intro ph hph
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hph
  apply buildPhases_other_group n bits (2^logP) dst stride
    (packing (dispatch n logP bits src dst)) g G r 0 src (phaseDegrees bits)
    (Nat.two_pow_pos _) (packing_pos _) hdst (by rw [phaseDegrees_sum]; omega) hr hgroup original ho

/-- A group preserves all rows except its destination and the two shared rows. -/
theorem group_row_frame (n logP bits src dst stride g a : Nat) (mem : Memory)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD a #[] = mem.getD a #[] := by
  apply evalPhases_row_frame
  intro ph hph w hw
  rw [batchTiles_phases] at hph
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hph
  obtain ⟨out,hw',rfl⟩ := List.mem_map.mp hw
  have ha := buildPhases_write_arrays n bits (2^logP) dst 0 src (phaseDegrees bits) original ho out hw'
  dsimp only
  rcases ha with ha | ha | ha <;> omega

theorem group_source_frame (n logP bits src dst stride g : Nat) (mem : Memory)
    (hsrc : src ≤ 1) (hne : src ≠ dst) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD src #[] = mem.getD src #[] :=
  group_row_frame n logP bits src dst stride g src mem hne (by omega) (by omega)

theorem group_twiddle_frame (n logP bits src dst stride g : Nat) (mem : Memory) (hdst : dst ≤ 1) :
    (evalGroup (batchTiles stride (dispatch n logP bits src dst)) g mem).getD 4 #[] = mem.getD 4 #[] :=
  group_row_frame n logP bits src dst stride g 4 mem (by omega) (by decide) (by decide)

theorem groups_other_output (n logP bits src dst stride G r : Nat) (groups : List Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hgroups : ∀ g, g ∈ groups → G/packing (dispatch n logP bits src dst) ≠ g) :
    valueAt (groups.foldl (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem)
      dst (outputAddress (2^logP) (2^bits) G r) = valueAt mem dst (outputAddress (2^logP) (2^bits) G r) := by
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih _ (fun gg hg => hgroups gg (by simp [hg]))]
    exact group_other_output n logP bits src dst stride g G r mem hdst hr (hgroups g (by simp))

/-- Row framing also holds through arbitrary group prefixes or suffixes. -/
theorem groups_row_frame (n logP bits src dst stride a : Nat) (groups : List Nat) (mem : Memory)
    (hd : a ≠ dst) (h2 : a ≠ 2) (h3 : a ≠ 3) :
    (groups.foldl (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem).getD a #[] =
      mem.getD a #[] := by
  induction groups generalizing mem with
  | nil => rfl
  | cons g groups ih =>
    rw [List.foldl_cons,ih]
    exact group_row_frame n logP bits src dst stride g a mem hd h2 h3

/-- The full actual dispatch retains the output established by the unique
packed group responsible for this original group. Its prefix state is explicit. -/
theorem dispatch_output_at_group (n logP bits src dst stride G r : Nat) (mem : Memory)
    (hdst : dst ≤ 1) (hr : r < 2^bits)
    (hg : G/packing (dispatch n logP bits src dst) <
      (batchTiles stride (dispatch n logP bits src dst)).groups) :
    valueAt (evalDispatch (batchTiles stride (dispatch n logP bits src dst)) mem)
      dst (outputAddress (2^logP) (2^bits) G r) =
    valueAt (evalGroup (batchTiles stride (dispatch n logP bits src dst))
      (G/packing (dispatch n logP bits src dst))
      ((List.range (G/packing (dispatch n logP bits src dst))).foldl
        (fun m g => evalGroup (batchTiles stride (dispatch n logP bits src dst)) g m) mem))
      dst (outputAddress (2^logP) (2^bits) G r) := by
  let d := batchTiles stride (dispatch n logP bits src dst)
  let owner := G/packing (dispatch n logP bits src dst)
  let suffix := (List.range (d.groups-(owner+1))).map ((owner+1)+·)
  have hsplit : List.range d.groups = List.range (owner+1) ++ suffix := by
    calc
      List.range d.groups = List.range ((owner+1)+(d.groups-(owner+1))) := by congr 1; dsimp [d,owner]; omega
      _ = _ := List.range_add
  change valueAt (evalDispatch d mem) _ _ = _
  unfold evalDispatch
  rw [hsplit,List.foldl_append]
  have hf := groups_other_output n logP bits src dst stride G r suffix
    ((List.range (owner+1)).foldl (fun m g => evalGroup d g m) mem) hdst hr (by
      intro g hmem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
      change owner ≠ owner+1+i
      omega)
  change valueAt (suffix.foldl (fun m g => evalGroup d g m)
    ((List.range (owner+1)).foldl (fun m g => evalGroup d g m) mem)) _ _ = _
  rw [hf]
  simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

end Obend.Hardware.Gpu.NttGroupFrame
end
