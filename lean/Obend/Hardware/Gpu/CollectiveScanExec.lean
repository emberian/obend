module
public import Obend.Hardware.Gpu.CollectiveExecute
public import Obend.Hardware.Gpu.CollectiveBuildFacts
@[expose] public section

/-! Actual pruned scan hierarchy: short descriptors finish once, and only long
ones participate in recursive summary scans and seeded local fix-up. -/
namespace Obend.Hardware.Gpu.CollectiveScanExec
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect Obend.Hardware.Gpu.CollectiveCompose
open Obend.Hardware.Gpu.CollectiveExecute Obend.Hardware.Gpu.CollectiveBuildFacts
set_option autoImplicit false

/-- Universal execution and point frame for the actual pruned scan builder. -/
theorem scanChunks_correct (p : Program) (hc : p.check = .ok ()) (op : ReduceOp)
    (tree : Trees) (mode : ScanMode) (src dst : Nat) (cs : List Chunk) (fuel : Nat) (before after : Build)
    (hrun : (scanChunksInto op mode tree (2^tree.depth) src dst cs fuel).run before = .ok ((),after))
    (htrace : TraceIn p after.dispatches.toList)
    (hsrcid : src < before.buffers.size) (hdstid : dst < before.buffers.size)
    (hsrc : Outside tree src) (hdst : Outside tree dst) (hne : src ≠ dst)
    (hrows : RowsBelow tree before.buffers.size) (hsplit : Split tree) (hlayout : Layout cs)
    (mem : Memory) (hg : Good p mem) :
    (∀ c ∈ cs, ∀ i < c.length, valueAt (evalTail before after mem) dst (c.start+i) =
      foldRange op (valueAt mem src) c.start (i+mode.extra) op.identity) ∧
    (∀ a < before.buffers.size, Outside tree a → ∀ i,
      (a = dst → ∀ c ∈ cs, i < c.start ∨ c.start+c.length ≤ i) →
      valueAt (evalTail before after mem) a i = valueAt mem a i) := by
  induction fuel generalizing mode src dst cs before after mem with
  | zero =>
    change (Except.error "collective scan: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at hrun
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
    unfold scanChunksInto at hrun
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ hrun
    cases u
    have he0 := localScan_extends op mode tree src dst small none before s0 hs
    have hsize0 := extends_buffer_size before s0 he0
    split at hrest
    · rename_i hnonempty
      obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨prefixes,s2,hb,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s3,hl,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      obtain ⟨u,s4,hr,hfinal⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have hfresh := allocate_fresh parts.length .device s0 s1 total ha
      have pfresh := allocate_fresh parts.length .device s1 s2 prefixes hb
      have he1 := hfresh.2.2.2
      have he2 := pfresh.2.2.2
      have he3 := localReduce_extends op tree src total parts s2 s3 hl
      have he4 := scanChunksInto_extends op .exclusive tree (2^tree.depth) total prefixes summaries fuel s3 s4 hr
      have he5 := localScan_extends op mode tree src dst parts (some prefixes) s4 after hfinal
      have he3a := extends_trans _ _ _ he4 he5
      have he2a := extends_trans _ _ _ he3 he3a
      have he1a := extends_trans _ _ _ he2 he2a
      have he0a := extends_trans _ _ _ he1 he1a
      have hsTrace := traceIn_localScan p op mode tree src dst small none before s0 hs
        (stateTraceIn_before p s0 after he0a htrace)
      have hpTrace := traceIn_localReduce p op tree src total parts s2 s3 hl
        (stateTraceIn_before p s3 after he3a htrace)
      have hfTrace := traceIn_localScan p op mode tree src dst parts (some prefixes) s4 after hfinal htrace
      let m0 := evalTail before s0 mem
      let m3 := evalTail s2 s3 m0
      let m4 := evalTail s3 s4 m3
      have hm0 : m0 = evalTrace (scanDispatches op mode tree src dst small none) mem :=
        localScan_evalTail op mode tree src dst small none before s0 hs mem
      have hm3 : m3 = evalTrace (reduceDispatches op tree src total parts) m0 :=
        localReduce_evalTail op tree src total parts s2 s3 hl m0
      have hmfinal : evalTail s4 after m4 = evalTrace (scanDispatches op mode tree src dst parts (some prefixes)) m4 :=
        localScan_evalTail op mode tree src dst parts (some prefixes) s4 after hfinal m4
      have hg0 : Good p m0 := evalTail_good p before s0 mem hg
      have hg3 : Good p m3 := evalTail_good p s2 s3 m0 hg0
      have hg4 : Good p m4 := evalTail_good p s3 s4 m3 hg3
      have htotal : Outside tree total := outside_of_rowsBelow tree before.buffers.size total hrows (by omega)
      have hprefix : Outside tree prefixes := outside_of_rowsBelow tree before.buffers.size prefixes hrows (by omega)
      have hsrcTotal : src ≠ total := by omega
      have hsrcPrefix : src ≠ prefixes := by omega
      have hdstTotal : dst ≠ total := by omega
      have hdstPrefix : dst ≠ prefixes := by omega
      have htotalPrefix : total ≠ prefixes := by omega
      have hsize3 := extends_buffer_size s2 s3 he3
      have hrows3 := rowsBelow_mono tree before.buffers.size s3.buffers.size hrows (by omega)
      have hsmall := local_scan p hc op mode tree src dst small none mem hg hsdesc hsplit hsrc hdst hne
        (by intro a ha; cases ha) hsTrace
      have hparts := local_reduce p hc op tree src total parts m0 hg0 hpdesc hsrc htotal hsrcTotal hpTrace
      have hread0 : valueAt m0 src = valueAt mem src := by
        funext i
        rw [hm0]
        exact hsmall.2 src hsrc hne i
      have hread3 : valueAt m3 src = valueAt mem src := by
        funext i
        rw [hm3,hparts.2 src hsrc hsrcTotal i,hread0]
      have hrec := ih .exclusive total prefixes summaries s3 s4 hr
        (stateTraceIn_before p s4 after he5 htrace) (by omega) (by omega)
        htotal hprefix htotalPrefix hrows3 hsummary m3 hg3
      have hread4 : valueAt m4 src = valueAt mem src := by
        funext i
        rw [hrec.2 src (by omega) hsrc i (by intro he; exact False.elim (hsrcPrefix he)),hread3]
      have hfix := local_scan p hc op mode tree src dst parts (some prefixes) m4 hg4 hpdesc hsplit hsrc hdst hne
        (by intro a ha; cases ha; exact ⟨hprefix,hdstPrefix.symm⟩) hfTrace
      have halloc1 : ∀ m, evalTail s0 s1 m = m := by
        obtain ⟨_,rfl⟩ := allocate_success parts.length .device s0 s1 total ha
        exact allocate_evalTail parts.length .device s0
      have halloc2 : ∀ m, evalTail s1 s2 m = m := by
        obtain ⟨_,rfl⟩ := allocate_success parts.length .device s1 s2 prefixes hb
        exact allocate_evalTail parts.length .device s1
      have hwhole : evalTail before after mem = evalTail s4 after m4 := by
        rw [evalTail_trans before s0 after he0 he0a,
          evalTail_trans s0 s1 after he1 he1a,halloc1,
          evalTail_trans s1 s2 after he2 he2a,halloc2,
          evalTail_trans s2 s3 after he3 he3a,
          evalTail_trans s3 s4 after he4 he5]
      have outside_parts : ∀ c ∈ small, ∀ i < c.length, ∀ d ∈ parts,
          c.start+i < d.start ∨ d.start+d.length ≤ c.start+i := by
        intro c hcs i hi d hd
        obtain ⟨orig,ho,hbounds⟩ := splitChunksFrom_origin (2^tree.depth) 0 large (Nat.two_pow_pos _) d hd
        have hcsm := List.mem_filter.mp hcs
        have holg := List.mem_filter.mp ho
        by_cases hlow : c.start+i < d.start
        · exact Or.inl hlow
        · apply Or.inr
          by_cases hhigh : d.start+d.length ≤ c.start+i
          · exact hhigh
          · have he := hlayout.disjoint c hcsm.1 orig holg.1 i hi
              (c.start+i-orig.start) (by omega) (by omega)
            subst orig
            have hsmalllen : c.length ≤ 2^tree.depth := by simpa using hcsm.2
            have hbiglen : 2^tree.depth < c.length := by simpa using holg.2
            omega
      constructor
      · intro c hcc i hi
        rw [hwhole]
        by_cases hsmallc : c.length ≤ 2^tree.depth
        · have hcs : c ∈ small := List.mem_filter.mpr ⟨hcc,by simpa using hsmallc⟩
          rw [hmfinal,local_scan_point_frame p hc op mode tree src dst parts (some prefixes) m4 hg4 hpdesc hfTrace
            dst (c.start+i) hdst (fun _ => outside_parts c hcs i hi)]
          rw [hrec.2 dst (by omega) hdst (c.start+i) (by intro he; exact False.elim (hdstPrefix he)),hm3,
            hparts.2 dst hdst hdstTotal (c.start+i),hm0]
          simpa only [prefixValue] using hsmall.1 c hcs i hi
        · have hcl : c ∈ large := List.mem_filter.mpr ⟨hcc,by simp; omega⟩
          apply split_scan_compose op mode (valueAt mem src) (valueAt m3 total)
            (valueAt m4 prefixes) (valueAt (evalTail s4 after m4) dst) (2^tree.depth) 0 large (Nat.two_pow_pos _) ?_ ?_ ?_ c hcl i hi
          · intro d hd
            rw [hm3]
            exact (hparts.1 d hd).trans (by rw [hread0])
          · intro d hd j hj
            simpa [ScanMode.extra] using hrec.1 d hd j hj
          · intro d hd j hj
            rw [hmfinal]
            simpa only [prefixValue,hread4] using hfix.1 d hd j hj
      · intro a hab hoa i hout
        rw [hwhole,hmfinal]
        have hpout : a = dst → ∀ d ∈ parts, i < d.start ∨ d.start+d.length ≤ i := by
          intro he d hd
          obtain ⟨orig,ho,hbounds⟩ := splitChunksFrom_origin (2^tree.depth) 0 large (Nat.two_pow_pos _) d hd
          have hh := hout he orig (List.mem_filter.mp ho).1
          omega
        rw [local_scan_point_frame p hc op mode tree src dst parts (some prefixes) m4 hg4 hpdesc hfTrace a i hoa hpout,
          hrec.2 a (by omega) hoa i (by intro he; exfalso; omega),hm3,
          hparts.2 a hoa (by omega) i,hm0]
        exact local_scan_point_frame p hc op mode tree src dst small none mem hg hsdesc hsTrace a i hoa
          (fun he c hc => hout he c (List.mem_filter.mp hc).1)
    · rename_i hemptyCond
      have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      have hsTrace := traceIn_localScan p op mode tree src dst small none before s0 hs htrace
      have hsmall := local_scan p hc op mode tree src dst small none mem hg hsdesc hsplit hsrc hdst hne
        (by intro a ha; cases ha) hsTrace
      have hempty : large = [] := by simpa [large] using hemptyCond
      rw [localScan_evalTail op mode tree src dst small none before s0 hs mem]
      constructor
      · intro c hcc i hi
        have hcs : c ∈ small := by
          apply List.mem_filter.mpr
          refine ⟨hcc,?_⟩
          by_cases hh : c.length ≤ 2^tree.depth
          · simpa using hh
          · have hc : c ∈ large := List.mem_filter.mpr ⟨hcc,by simp; omega⟩
            rw [hempty] at hc
            contradiction
        simpa only [prefixValue] using hsmall.1 c hcs i hi
      · intro a ha hoa i hout
        exact local_scan_point_frame p hc op mode tree src dst small none mem hg hsdesc hsTrace a i hoa
          (fun he c hc => hout he c (List.mem_filter.mp hc).1)

end Obend.Hardware.Gpu.CollectiveScanExec
end
