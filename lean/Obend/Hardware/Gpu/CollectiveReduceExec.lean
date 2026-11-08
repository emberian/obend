module
public import Obend.Hardware.Gpu.CollectiveExecute
public import Obend.Hardware.Gpu.CollectiveBuildFacts
@[expose] public section

/-! The pruned reduction hierarchy executes its ordered descriptor reductions.
Finished result slots are framed while only unfinished descriptors recurse. -/
namespace Obend.Hardware.Gpu.CollectiveReduceExec
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.CollectiveCompose
open Obend.Hardware.Gpu.CollectiveExecute Obend.Hardware.Gpu.CollectiveBuildFacts
set_option autoImplicit false

/-- Universal execution and point frame for the actual pruned recursive builder.
Bounds and unique scatters come solely from admission of the final program. -/
theorem reduceChunks_correct (p : Program) (hc : p.check = .ok ()) (op : ReduceOp)
    (tree : Trees) (src dst : Nat) (cs : List Chunk) (fuel : Nat) (before after : Build)
    (hrun : (reduceChunksInto op tree (2^tree.depth) src dst cs fuel).run before = .ok ((),after))
    (htrace : TraceIn p after.dispatches.toList)
    (hsrcid : src < before.buffers.size) (hdstid : dst < before.buffers.size)
    (hsrc : Outside tree src) (hdst : Outside tree dst) (hne : src ≠ dst)
    (hrows : RowsBelow tree before.buffers.size) (hlayout : Layout cs)
    (mem : Memory) (hg : Good p mem) :
    (∀ c ∈ cs, valueAt (evalTail before after mem) dst c.result =
      foldRange op (valueAt mem src) c.start c.length op.identity) ∧
    (∀ a < before.buffers.size, Outside tree a → ∀ i,
      (a = dst → ∀ c ∈ cs, i ≠ c.result) →
      valueAt (evalTail before after mem) a i = valueAt mem a i) := by
  induction fuel generalizing src dst cs before after mem with
  | zero =>
    change (Except.error "collective reduction: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at hrun
    cases hrun
  | succ fuel ih =>
    let small := cs.filter (·.length ≤ 2^tree.depth)
    let large := cs.filter (2^tree.depth < ·.length)
    let parts := splitChunks (2^tree.depth) large
    let summaries := summaryChunks (2^tree.depth) large
    have hsdesc := descriptors_small tree cs hlayout
    have hlarge := layout_filter cs (2^tree.depth < ·.length) hlayout
    have hpdesc := descriptors_split tree large hlarge
    have hsummary := layout_summary (2^tree.depth) large hlarge
    unfold reduceChunksInto at hrun
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ hrun
    cases u
    have he0 := localReduce_extends op tree src dst small before s0 hs
    have hsize0 := extends_buffer_size before s0 he0
    split at hrest
    · rename_i hnonempty
      obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s2,hl,hr⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have hfresh := allocate_fresh parts.length .device s0 s1 total ha
      have he1 := hfresh.2.2.2
      have he2 := localReduce_extends op tree src total parts s1 s2 hl
      have he3 := reduceChunksInto_extends op tree (2^tree.depth) total dst summaries fuel s2 after hr
      have he02 := extends_trans _ _ _ he1 he2
      have he0a := extends_trans _ _ _ he02 he3
      have hsTrace := traceIn_localReduce p op tree src dst small before s0 hs
        (stateTraceIn_before p s0 after he0a htrace)
      have hpTrace := traceIn_localReduce p op tree src total parts s1 s2 hl
        (stateTraceIn_before p s2 after he3 htrace)
      let m0 := evalTail before s0 mem
      let m2 := evalTail s1 s2 m0
      have hm0 : m0 = evalTrace (reduceDispatches op tree src dst small) mem :=
        localReduce_evalTail op tree src dst small before s0 hs mem
      have hm2 : m2 = evalTrace (reduceDispatches op tree src total parts) m0 :=
        localReduce_evalTail op tree src total parts s1 s2 hl m0
      have hg0 : Good p m0 := evalTail_good p before s0 mem hg
      have hg2 : Good p m2 := evalTail_good p s1 s2 m0 hg0
      have houts : Outside tree total := outside_of_rowsBelow tree before.buffers.size total hrows (by omega)
      have hsrcTotal : src ≠ total := by omega
      have hdstTotal : dst ≠ total := by omega
      have hsmall := local_reduce p hc op tree src dst small mem hg hsdesc hsrc hdst hne hsTrace
      have hparts := local_reduce p hc op tree src total parts m0 hg0 hpdesc hsrc houts hsrcTotal hpTrace
      have hread0 : valueAt m0 src = valueAt mem src := by
        funext i
        rw [hm0]
        exact hsmall.2 src hsrc hne i
      have hsize2 := extends_buffer_size s1 s2 he2
      have hrows2 := rowsBelow_mono tree before.buffers.size s2.buffers.size hrows (by omega)
      have hrec := ih total dst summaries s2 after hr htrace (by omega) (by omega)
        houts hdst hdstTotal.symm hrows2 hsummary m2 hg2
      have halloc : ∀ m, evalTail s0 s1 m = m := by
        obtain ⟨_,rfl⟩ := allocate_success parts.length .device s0 s1 total ha
        exact allocate_evalTail parts.length .device s0
      have hwhole : evalTail before after mem = evalTail s2 after m2 := by
        rw [evalTail_trans before s0 after he0 he0a,
          evalTail_trans s0 s1 after he1 (extends_trans _ _ _ he2 he3), halloc,
          evalTail_trans s1 s2 after he2 he3]
      constructor
      · intro c hcc
        rw [hwhole]
        by_cases hsmallc : c.length ≤ 2^tree.depth
        · have hcs : c ∈ small := List.mem_filter.mpr ⟨hcc,by simpa using hsmallc⟩
          have hkeep : ∀ d ∈ summaries, c.result ≠ d.result := by
            intro d hd he
            have hdmap : d.result ∈ summaries.map (·.result) := List.mem_map.mpr ⟨d,hd,rfl⟩
            simp only [summaries,summaryChunks,summaryChunksFrom_results] at hdmap
            obtain ⟨e,helarge,heres⟩ := List.mem_map.mp hdmap
            have hecs := (List.mem_filter.mp helarge).1
            have hlen := (List.mem_filter.mp helarge).2
            have hce := result_injective cs hlayout.unique c e hcc hecs (he.trans heres.symm)
            subst e
            have hbig : 2^tree.depth < c.length := by simpa using hlen
            omega
          rw [hrec.2 dst (by omega) hdst c.result (fun _ => hkeep), hm2]
          rw [hparts.2 dst hdst hdstTotal c.result, hm0]
          exact hsmall.1 c hcs
        · have hcl : c ∈ large := List.mem_filter.mpr ⟨hcc,by simp; omega⟩
          apply split_reduce_compose op (valueAt mem src) (valueAt m2 total)
            (valueAt (evalTail s2 after m2) dst) (2^tree.depth) 0 large (Nat.two_pow_pos _) ?_ hrec.1 c hcl
          intro d hd
          rw [hm2]
          exact (hparts.1 d hd).trans (by rw [hread0])
      · intro a hab hoa i hout
        rw [hwhole]
        have hsumm : a = dst → ∀ c ∈ summaries, i ≠ c.result := by
          intro he c hcc
          have hm : c.result ∈ summaries.map (·.result) := List.mem_map.mpr ⟨c,hcc,rfl⟩
          simp only [summaries,summaryChunks,summaryChunksFrom_results] at hm
          obtain ⟨d,hd,hde⟩ := List.mem_map.mp hm
          rw [← hde]
          exact hout he d (List.mem_filter.mp hd).1
        rw [hrec.2 a (by omega) hoa i hsumm, hm2,
          hparts.2 a hoa (by omega) i, hm0]
        exact local_reduce_point_frame p hc op tree src dst small mem hg hsdesc hsTrace a i hoa
          (fun he c hc => hout he c (List.mem_filter.mp hc).1)
    · rename_i hemptyCond
      have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      have hsTrace := traceIn_localReduce p op tree src dst small before s0 hs htrace
      have hsmall := local_reduce p hc op tree src dst small mem hg hsdesc hsrc hdst hne hsTrace
      have hempty : large = [] := by simpa [large] using hemptyCond
      rw [localReduce_evalTail op tree src dst small before s0 hs mem]
      constructor
      · intro c hcc
        apply hsmall.1 c
        apply List.mem_filter.mpr
        refine ⟨hcc,?_⟩
        by_cases hh : c.length ≤ 2^tree.depth
        · simpa using hh
        · have hc : c ∈ large := List.mem_filter.mpr ⟨hcc,by simp; omega⟩
          rw [hempty] at hc
          contradiction
      · intro a ha hoa i hout
        exact local_reduce_point_frame p hc op tree src dst small mem hg hsdesc hsTrace a i hoa
          (fun he c hc => hout he c (List.mem_filter.mp hc).1)

end Obend.Hardware.Gpu.CollectiveReduceExec
end
