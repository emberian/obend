module
public import Obend.Hardware.Gpu.NttPhaseMetadata
@[expose] public section

/-! The actual phase initialization pairs every returned input register with
its declared load index. Allocation emits no arithmetic instructions. -/
namespace Obend.Hardware.Gpu.NttLoadCorrect
open Obend.Hardware.ArrayBuild Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt.PhaseMetadata
set_option autoImplicit false

theorem loadBody_run (src : Nat) (index : Nat → Ix) (r : Nat) (s : PairState) (st : Build) :
    (loadBody src index r s).run st =
      (.yield (s.1++[⟨st.lengths.size,src,index r⟩],s.2.push st.lengths.size),
        {st with lengths := st.lengths.push 1}) := rfl

/-- General loop receipt: the appended reads and registers have identical
ordering, and every appended read records the corresponding source index. -/
theorem load_suffix (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ∃ regs : List Nat,
      regs.length = xs.length ∧
      ((forIn xs s (loadBody src index)).run st).1.1 =
        s.1 ++ (regs.zip xs).map (fun (a,r) => ⟨a,src,index r⟩) ∧
      ((forIn xs s (loadBody src index)).run st).1.2.toList = s.2.toList ++ regs ∧
      ((forIn xs s (loadBody src index)).run st).2.edges = st.edges := by
  induction xs generalizing s st with
  | nil =>
    refine ⟨[], rfl, ?_, ?_, ?_⟩
    · change s.1 = s.1 ++ []
      exact (List.append_nil _).symm
    · change s.2.toList = s.2.toList ++ []
      exact (List.append_nil _).symm
    · rfl
  | cons r xs ih =>
    rw [List.forIn_cons,bind_run,loadBody_run]
    change ∃ regs : List Nat, _
    obtain ⟨regs,hl,hr,hg,he⟩ := ih
      (s.1++[⟨st.lengths.size,src,index r⟩],s.2.push st.lengths.size)
      {st with lengths := st.lengths.push 1}
    refine ⟨st.lengths.size::regs,by simp [hl],?_,?_,he⟩
    · simpa [List.append_assoc] using hr
    · simpa [List.append_assoc] using hg

theorem load_reads_eq (src : Nat) (index : Nat → Ix) (radix : Nat) (st : Build) :
    ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.1 =
      (((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.2.toList.zip
        (List.range radix)).map (fun (a,r) => ⟨a,src,index r⟩) := by
  obtain ⟨regs,_,hr,hg,_⟩ := load_suffix src index (List.range radix) ([],#[]) st
  simp only [List.nil_append,Array.toList_empty] at hr hg
  rw [hg]
  exact hr

theorem load_edges (src : Nat) (index : Nat → Ix) (xs : List Nat) (s : PairState) (st : Build) :
    ((forIn xs s (loadBody src index)).run st).2.edges = st.edges := by
  obtain ⟨_,_,_,_,he⟩ := load_suffix src index xs s st
  exact he

/-- Every returned register slot is exactly the destination of its declared
source load. This input binding is independent of later arithmetic. -/
theorem load_reg_read (src : Nat) (index : Nat → Ix) (radix : Nat) (st : Build)
    (r : Nat) (hr : r < radix) :
    (⟨((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.2.getD r 0,
       src,index r⟩ : Read) ∈ ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1.1 := by
  let loaded := ((forIn (List.range radix) ([],#[]) (loadBody src index)).run st).1
  have hs : loaded.2.size = radix := by simpa [loaded] using load_size src index (List.range radix) ([],#[]) st
  have hbound : r < loaded.2.size := by omega
  have hzip : r < (loaded.2.toList.zip (List.range radix)).length := by simp [hs,hr]
  have hm := List.getElem_mem (l := loaded.2.toList.zip (List.range radix)) hzip
  have he : (loaded.2.toList.zip (List.range radix))[r] = (loaded.2.getD r 0,r) := by
    simp [List.getElem_zip,Array.getD_eq_getD_getElem?,hbound]
  rw [he] at hm
  rw [load_reads_eq]
  exact List.mem_map.mpr ⟨(loaded.2.getD r 0,r),hm,rfl⟩

end Obend.Hardware.Gpu.NttLoadCorrect
end
