module
public import Obend.Hardware.Gpu.NttGroupValue
public import Obend.Hardware.Gpu.NttGroupFrame
public import Obend.Hardware.Gpu.NttValue
@[expose] public section
namespace Obend.Hardware.Gpu.NttDispatchValue
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
open Obend.Hardware.Gpu.NttGroupValue Obend.Hardware.Gpu.NttGroupFrame
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem groups_good (p : Program) (d : Dispatch) (groups : List Nat) (mem : Memory)
    (hg : Good p mem) : Good p (groups.foldl (fun m g => evalGroup d g m) mem) := by
  induction groups generalizing mem with
  | nil => exact hg
  | cons g groups ih =>
    exact ih (evalGroup d g mem) (evalGroup_good p d g mem hg)

/-- Universal value theorem for the real packed dispatch. Prefix groups retain
its input and constants; suffix groups retain its established output cells. -/
theorem dispatch_value (total logP bits src dst : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hg : Good (nttBlockProgram (2^total)) mem)
    (htable : TwiddleMemory (2^total) mem)
    (G : Nat) (hG : G<2^total/2^bits) (r : Nat) (hr : r<2^bits) :
    (valueAt (evalDispatch (batchTiles (tileSize (dispatch (2^total) logP bits src dst))
      (dispatch (2^total) logP bits src dst)) mem) dst
      (outputAddress (2^logP) (2^bits) G r)).toNat =
      dft (2^bits) (rootOfUnity (2^bits)) (tileInput total bits logP src G mem) r := by
  let d := dispatch (2^total) logP bits src dst
  let stride := tileSize d
  let packed := batchTiles stride d
  let owner := G/packing d
  let tile := G%packing d
  let beforeGroup := (List.range owner).foldl (fun m g => evalGroup packed g m) mem
  have hsplit := packed_group_split d G hG
  have howner : owner < packed.groups := hsplit.1
  have htile : tile < packing d := hsplit.2.1
  have hjoin : owner*packing d+tile=G := hsplit.2.2
  have hgood : Good (nttBlockProgram (2^total)) beforeGroup := groups_good _ packed (List.range owner) mem hg
  have hsource : beforeGroup.getD src #[] = mem.getD src #[] :=
    groups_row_frame (2^total) logP bits src dst stride src (List.range owner) mem hne (by omega) (by omega)
  have hconstants : beforeGroup.getD 4 #[] = mem.getD 4 #[] :=
    groups_row_frame (2^total) logP bits src dst stride 4 (List.range owner) mem (by omega) (by decide) (by decide)
  have htable' : TwiddleMemory (2^total) beforeGroup := by
    intro i hi
    simpa only [valueAt,hconstants] using htable i hi
  have hv := group_value total logP bits src dst owner beforeGroup ht hp hb hsrc hdst hne hm
    howner hgood htable' tile htile r hr
  change (valueAt (evalGroup packed owner beforeGroup) dst
    (outputAddress (2^logP) (2^bits) (owner*packing d+tile) r)).toNat = _ at hv
  rw [hjoin] at hv
  have hframe := dispatch_output_at_group (2^total) logP bits src dst stride G r mem hdst hr howner
  change valueAt (evalDispatch packed mem) dst _ = valueAt (evalGroup packed owner beforeGroup) dst _ at hframe
  rw [hframe,hv]
  apply congrArg (fun f => dft (2^bits) (rootOfUnity (2^bits)) f r)
  funext i
  simp only [tileInput,preparedInput,ite_true,valueAt,hsource]

/-- The actual-upload contract required by whole-program Stockham composition,
with its checker and computed-value premises completely discharged. -/
theorem upload_dft (total logP bits src dst : Nat) (mem : Memory)
    (ht : total≤32) (hp : logP+bits≤total) (hb : 0<bits)
    (hsrc : src≤1) (hdst : dst≤1) (hne : src≠dst)
    (hm : dispatch (2^total) logP bits src dst ∈ (sourceUploads (2^total)).1)
    (hg : Good (nttBlockProgram (2^total)) mem)
    (htable : TwiddleMemory (2^total) mem) : UploadDFT total logP bits src dst mem := by
  intro G hG r hr
  exact dispatch_value total logP bits src dst mem ht hp hb hsrc hdst hne hm hg htable G hG r hr

end Obend.Hardware.Gpu.NttDispatchValue
end
