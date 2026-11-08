module
public import Obend.Hardware.Gpu.CollectiveWork
public import Obend.Hardware.Gpu.CollectiveBuildCorrect
@[expose] public section

/-! Global source-action bounds for the actual pruned collective builder.
Work counts every emitted dispatch group and its real phases, including loads,
scalar instructions, and stores. Allocating metadata itself emits no GPU work. -/
namespace Obend.Hardware.Gpu.CollectiveWorkBuild
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveBuildFacts Obend.Hardware.Gpu.CollectiveReduceBuild
open Obend.Hardware.Gpu.CollectiveWork Obend.Hardware.Gpu.CollectiveBuildCorrect
set_option autoImplicit false

def dispatchWork (d : Dispatch) : Nat := d.groups * work d.phases
def traceWork (ds : List Dispatch) : Nat := (ds.map dispatchWork).sum
def programWork (p : Program) : Nat := traceWork p.dispatches

def words (cs : List Chunk) : Nat := (cs.map (·.length)).sum

theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]; omega

theorem sum_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem sum_zero {α : Type} (xs : List α) : (xs.map (fun _ => 0 : α → Nat)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  have loop : ∀ as bs : List Nat, bs.Nodup →
      (List.eraseDupsBy.loop (· == ·) as bs).Nodup := by
    intro as
    induction as with
    | nil =>
      intro bs hb
      exact List.pairwise_reverse.mpr (List.Pairwise.imp (fun h => Ne.symm h) hb)
    | cons a as ih =>
      intro bs hb
      unfold List.eraseDupsBy.loop
      split
      · exact ih bs hb
      · rename_i hnone
        apply ih (a::bs)
        apply List.nodup_cons.mpr
        refine ⟨?_,hb⟩
        intro ha
        have hh : bs.any (fun b => a == b) = true := List.any_eq_true.mpr ⟨a,ha,by simp⟩
        simp_all
  exact loop xs [] (by simp)

theorem sum_indicator (keys : List Nat) (target value : Nat) (hu : keys.Nodup)
    (ht : target ∈ keys) : (keys.map fun k => if target = k then value else 0).sum = value := by
  induction keys with
  | nil => simp at ht
  | cons k ks ih =>
    have huniq := List.nodup_cons.mp hu
    by_cases he : target = k
    · subst target
      have hz : (ks.map fun j => if k = j then value else 0).sum = 0 := by
        have hm : ks.map (fun j => if k = j then value else 0) = ks.map (fun _ => 0) := by
          apply List.map_congr_left
          intro j hj
          have hne : k ≠ j := by intro he; subst j; exact huniq.1 hj
          simp [hne]
        rw [hm,sum_zero]
      simp [hz]
    · have ht' : target ∈ ks := by simpa [he] using ht
      simp [he,ih huniq.2 ht']

/-- Every descriptor contributes once to its unique length bucket. -/
theorem bucket_partition (cs : List Chunk) (keys : List Nat) (hu : keys.Nodup)
    (hcover : ∀ c ∈ cs, c.length ∈ keys) (f : Nat → Nat) :
    (keys.map fun n => (cs.filter (·.length == n)).length * f n).sum =
      (cs.map fun c => f c.length).sum := by
  induction cs with
  | nil => simpa using sum_zero keys
  | cons c cs ih =>
    have ht := ih (by intro d hd; exact hcover d (by simp [hd]))
    have hm : (keys.map fun n => ((c::cs).filter (·.length == n)).length * f n) =
        keys.map (fun n => (if c.length = n then f c.length else 0) +
          (cs.filter (·.length == n)).length*f n) := by
      apply List.map_congr_left
      intro n _
      by_cases he : c.length = n
      · simp [he,Nat.add_mul,Nat.add_comm]
      · simp [he]
    rw [hm,sum_add,sum_indicator keys c.length (f c.length) hu (hcover c (by simp)),ht]
    rfl

theorem buckets_weight (cs : List Chunk) (f : Nat → Nat) :
    ((buckets cs).map fun b => b.2.length*f b.1).sum = (cs.map fun c => f c.length).sum := by
  unfold buckets
  rw [List.map_map]
  apply bucket_partition
  · exact eraseDups_nodup _
  · intro c hc
    exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨c,hc,rfl⟩)

@[simp] theorem traceWork_append (xs ys : List Dispatch) : traceWork (xs++ys) = traceWork xs+traceWork ys := by
  simp [traceWork]

theorem traceWork_flatMap {α : Type} (xs : List α) (f : α → List Dispatch) :
    traceWork (xs.flatMap f) = (xs.map fun x => traceWork (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,traceWork_append,List.map_cons,List.sum_cons,ih]

theorem traceWork_emitted (groups : Nat) (phases : List Phase) :
    traceWork (emitted groups phases) = groups * work phases := by
  by_cases hg : groups = 0
  · simp [hg,emitted,traceWork]
  · by_cases hp : phases = []
    · simp [hp,emitted,traceWork,work]
    · have hpos : 0 < groups := by omega
      simp [emitted,hpos,hp,traceWork,dispatchWork]

/-- All actual local scan dispatches cost at most 26 actions per valid word. -/
theorem localScan_work (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (prefixBuffer : Option Nat) :
    traceWork (scanDispatches op mode tree src dst cs prefixBuffer) ≤ 26*words cs := by
  rw [scanDispatches,traceWork_flatMap]
  have hbound := sum_le (buckets cs)
    (fun (b : Nat × List Chunk) => traceWork (if b.1 > 0 then
      emitted b.2.length (scanPhases op mode tree src dst b.1 (tileDepth b.1)
        (descriptor b.2 (·.start)) (prefixBuffer.map fun a => (a,descriptor b.2 (·.result)))) else []))
    (fun b => b.2.length * (26*b.1)) (by
      intro b _
      by_cases h : 0 < b.1
      · simp only [if_pos h,traceWork_emitted]
        exact Nat.mul_le_mul_left b.2.length (scan_linear op mode tree src dst b.1 _ _ h)
      · simp only [if_neg h,traceWork,List.map_nil,List.sum_nil]
        omega)
  have he : ((buckets cs).map fun b => b.2.length*(26*b.1)).sum = 26*words cs := by
    rw [buckets_weight cs (fun n => 26*n)]
    simpa only [List.map_map,Function.comp_def,words] using sum_scale (cs.map (·.length)) 26
  rw [he] at hbound
  exact hbound

/-- Empty reductions cost a constant amount; nonempty ones scale with length. -/
theorem localReduce_work (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk) :
    traceWork (reduceDispatches op tree src dst cs) ≤ 12*((cs.map fun c => max 1 c.length).sum) := by
  rw [reduceDispatches,traceWork_flatMap]
  simp only [traceWork_emitted]
  have hbound := sum_le (buckets cs)
    (fun b => b.2.length * work (reducePhases op tree src dst b.1 (tileDepth b.1)
      (descriptor b.2 (·.start)) (descriptor b.2 (·.result))))
    (fun b => b.2.length * (12*max 1 b.1)) (by
      intro b _
      exact Nat.mul_le_mul_left b.2.length (reduce_linear op tree src dst b.1 _ _))
  have he : ((buckets cs).map fun b => b.2.length*(12*max 1 b.1)).sum =
      12*((cs.map fun c => max 1 c.length).sum) := by
    rw [buckets_weight cs (fun n => 12*max 1 n)]
    simpa only [List.map_map,Function.comp_def] using sum_scale (cs.map fun c => max 1 c.length) 12
  rw [he] at hbound
  exact hbound

@[simp] theorem words_append (as bs : List Chunk) : words (as++bs) = words as+words bs := by
  simp [words]

theorem chunk_lengths_prefix (tile len count : Nat) :
    ((List.range count).map fun j => min tile (len-j*tile)).sum = min len (count*tile) := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,ih]
    rw [Nat.succ_mul]
    omega

theorem segmentChunks_words (tile start result len : Nat) (htile : 0 < tile) :
    words (segmentChunks tile start result len) = len := by
  simp only [words,segmentChunks,List.map_map,Function.comp_def]
  rw [chunk_lengths_prefix,Nat.min_eq_left (chunk_count_covers tile len htile)]

theorem splitChunksFrom_words (tile result : Nat) (cs : List Chunk) (htile : 0 < tile) :
    words (splitChunksFrom tile result cs) = words cs := by
  induction cs generalizing result with
  | nil => rfl
  | cons c cs ih =>
    rw [splitChunksFrom,words_append,segmentChunks_words tile c.start result c.length htile,ih]
    rfl

theorem splitChunksFrom_positive (tile result : Nat) (cs : List Chunk) (htile : 0 < tile) :
    ∀ c ∈ splitChunksFrom tile result cs, 0 < c.length := by
  induction cs generalizing result with
  | nil => simp [splitChunksFrom]
  | cons c cs ih =>
    intro d hd
    simp only [splitChunksFrom,List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
      exact chunk_positive tile c.length j htile (List.mem_range.mp hj)
    · exact ih (result+(c.length+tile-1)/tile) d hd

theorem localReduce_positive_work (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (hpos : ∀ c ∈ cs, 0 < c.length) :
    traceWork (reduceDispatches op tree src dst cs) ≤ 12*words cs := by
  have h := localReduce_work op tree src dst cs
  have he : cs.map (fun c => max 1 c.length) = cs.map (·.length) := by
    apply List.map_congr_left
    intro c hc
    exact Nat.max_eq_right (hpos c hc)
  simpa only [he,words] using h

theorem localReduce_general_work (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk) :
    traceWork (reduceDispatches op tree src dst cs) ≤ 12*(words cs+cs.length) := by
  have hmax : (cs.map fun c => max 1 c.length).sum ≤ words cs+cs.length := by
    induction cs with
    | nil => exact Nat.le_refl _
    | cons c cs ih =>
      simp only [List.map_cons,List.sum_cons,words,List.length_cons] at *
      omega
  exact Nat.le_trans (localReduce_work op tree src dst cs) (Nat.mul_le_mul_left 12 hmax)

/-- Every unfinished descriptor's summary is at most two thirds its length. -/
theorem chunk_shrink (tile len : Nat) (htile : 2 ≤ tile) (hlarge : tile < len) :
    3*((len+tile-1)/tile) ≤ 2*len := by
  have hcap : len ≤ ((len+1)/2)*tile := by
    have hm := Nat.mul_le_mul_left ((len+1)/2) htile
    omega
  have h := chunk_count_le tile len ((len+1)/2) (by omega) hcap
  omega

theorem summary_words (tile : Nat) (cs : List Chunk) :
    words (summaryChunks tile cs) = (cs.map fun c => (c.length+tile-1)/tile).sum := by
  unfold words summaryChunks
  rw [summaryChunksFrom_lengths]

theorem summary_length (tile : Nat) (cs : List Chunk) :
    (summaryChunks tile cs).length = cs.length := by
  have h := congrArg List.length (summaryChunksFrom_results tile 0 cs)
  simpa [summaryChunks] using h

theorem summary_shrink (tile : Nat) (cs : List Chunk) (htile : 2 ≤ tile)
    (hlarge : ∀ c ∈ cs, tile < c.length) :
    3*words (summaryChunks tile cs) ≤ 2*words cs := by
  rw [summary_words]
  have h := sum_le cs (fun c => 3*((c.length+tile-1)/tile)) (fun c => 2*c.length)
    (by intro c hc; exact chunk_shrink tile c.length htile (hlarge c hc))
  have hleft := sum_scale (cs.map fun c => (c.length+tile-1)/tile) 3
  have hright := sum_scale (cs.map (·.length)) 2
  simp only [List.map_map,Function.comp_def] at hleft hright
  simpa only [hleft,hright,words] using h

theorem words_small_large (tile : Nat) (cs : List Chunk) :
    words (cs.filter (·.length ≤ tile)) + words (cs.filter (tile < ·.length)) = words cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c.length ≤ tile
    · have hn : ¬tile < c.length := by omega
      simp [List.filter_cons,h,hn,words] at *
      omega
    · have hl : tile < c.length := by omega
      simp [List.filter_cons,h,hl,words] at *
      omega

theorem length_small_large (tile : Nat) (cs : List Chunk) :
    (cs.filter (·.length ≤ tile)).length + (cs.filter (tile < ·.length)).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c.length ≤ tile
    · have hn : ¬tile < c.length := by omega
      simp [h,hn]
      omega
    · have hl : tile < c.length := by omega
      simp [h,hl,ih]
      omega

def stateWork (s : Build) : Nat := traceWork s.dispatches.toList

@[simp] theorem stateWork_append (s : Build) (ds : List Dispatch) :
    stateWork (appendTrace s ds) = stateWork s + traceWork ds := by
  simp [stateWork,appendTrace]

theorem allocate_work (size : Nat) (before after : Build) (id : Nat)
    (h : (allocate size .device).run before = .ok (id,after)) : stateWork after = stateWork before := by
  obtain ⟨_,rfl⟩ := allocate_success size .device before after id h
  rfl

theorem localReduce_state_work (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (before after : Build) (h : (localReduce op tree src dst cs).run before = .ok ((),after)) :
    stateWork after = stateWork before + traceWork (reduceDispatches op tree src dst cs) := by
  rw [localReduce_success op tree src dst cs before after h,stateWork_append]

theorem localScan_state_work (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (seed : Option Nat) (before after : Build)
    (h : (localScan op mode tree src dst cs seed).run before = .ok ((),after)) :
    stateWork after = stateWork before + traceWork (scanDispatches op mode tree src dst cs seed) := by
  rw [localScan_success op mode tree src dst cs seed before after h,stateWork_append]

/-- Total actual emitted work of the pruned reduction hierarchy. Finished
segments are charged once; unfinished summary lengths shrink geometrically. -/
theorem reduceChunks_work (op : ReduceOp) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) (fuel : Nat) (before after : Build) (htile : 2 ≤ tile)
    (h : (reduceChunksInto op tree tile src dst cs fuel).run before = .ok ((),after)) :
    stateWork after ≤ stateWork before + 36*(words cs+cs.length) := by
  induction fuel generalizing src dst cs before after with
  | zero =>
    change (Except.error "collective reduction: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    let small := cs.filter (·.length ≤ tile)
    let large := cs.filter (tile < ·.length)
    let parts := splitChunks tile large
    let summaries := summaryChunks tile large
    have hwords := words_small_large tile cs
    have hlength := length_small_large tile cs
    change words small+words large = words cs at hwords
    change small.length+large.length = cs.length at hlength
    have hshrink : 3*words summaries ≤ 2*words large :=
      summary_shrink tile large htile (by intro c hc; simpa using (List.mem_filter.mp hc).2)
    have hsummarylen : summaries.length = large.length := summary_length tile large
    have hpartwords : words parts = words large := splitChunksFrom_words tile 0 large (by omega)
    unfold reduceChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have hsmall := localReduce_general_work op tree src dst small
    have hswork := localReduce_state_work op tree src dst small before s0 hs
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s2,hl,hr⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have hawork := allocate_work parts.length s0 s1 total ha
      have hlwork := localReduce_state_work op tree src total parts s1 s2 hl
      have hparts := localReduce_positive_work op tree src total parts
        (splitChunksFrom_positive tile 0 large (by omega))
      have hrec := ih total dst summaries s2 after hr
      rw [hpartwords] at hparts
      rw [hsummarylen] at hrec
      omega
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      omega

/-- Total actual emitted work of the pruned scan hierarchy. Each unfinished
level charges 12 actions/word for summaries and 26 for seeded local scans. -/
theorem scanChunks_work (op : ReduceOp) (mode : ScanMode) (tree : Trees) (tile src dst : Nat)
    (cs : List Chunk) (fuel : Nat) (before after : Build) (htile : 2 ≤ tile)
    (h : (scanChunksInto op mode tree tile src dst cs fuel).run before = .ok ((),after)) :
    stateWork after ≤ stateWork before + 114*words cs := by
  induction fuel generalizing mode src dst cs before after with
  | zero =>
    change (Except.error "collective scan: insufficient hierarchy depth" : Except String (Unit × Build)) = .ok ((),after) at h
    cases h
  | succ fuel ih =>
    let small := cs.filter (·.length ≤ tile)
    let large := cs.filter (tile < ·.length)
    let parts := splitChunks tile large
    let summaries := summaryChunks tile large
    have hwords := words_small_large tile cs
    change words small+words large = words cs at hwords
    have hshrink : 3*words summaries ≤ 2*words large :=
      summary_shrink tile large htile (by intro c hc; simpa using (List.mem_filter.mp hc).2)
    have hpartwords : words parts = words large := splitChunksFrom_words tile 0 large (by omega)
    unfold scanChunksInto at h
    obtain ⟨u,s0,hs,hrest⟩ := bind_success _ _ _ _ _ h
    cases u
    have hsmall := localScan_work op mode tree src dst small none
    have hswork := localScan_state_work op mode tree src dst small none before s0 hs
    split at hrest
    · obtain ⟨total,s1,ha,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨prefixes,s2,hb,hrest⟩ := bind_success _ _ _ _ _ hrest
      obtain ⟨u,s3,hl,hrest⟩ := bind_success _ _ _ _ _ hrest
      cases u
      obtain ⟨u,s4,hr,hfinal⟩ := bind_success _ _ _ _ _ hrest
      cases u
      have hawork := allocate_work parts.length s0 s1 total ha
      have hbwork := allocate_work parts.length s1 s2 prefixes hb
      have hlwork := localReduce_state_work op tree src total parts s2 s3 hl
      have hparts := localReduce_positive_work op tree src total parts
        (splitChunksFrom_positive tile 0 large (by omega))
      have hrec := ih .exclusive total prefixes summaries s3 s4 hr
      have hfwork := localScan_state_work op mode tree src dst parts (some prefixes) s4 after hfinal
      have hfix := localScan_work op mode tree src dst parts (some prefixes)
      rw [hpartwords] at hparts hfix
      omega
    · have he : s0 = after := congrArg Prod.snd (Except.ok.inj hrest)
      subst after
      omega

/-- Public program work bound on actual dispatch groups and actual phase
loads/scalar instructions/stores. Empty reduction descriptors add constant work;
empty scan descriptors emit no GPU work. -/
theorem build_work (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) :
    programWork p ≤ match shape.mode with
      | none => 36*(shape.inputLen+shape.segments.length)
      | some _ => 114*shape.inputLen := by
  have ht := build_tile_bounds op shape depth p hbuild
  have htile : 2 ≤ 2^depth := by
    cases depth with
    | zero => omega
    | succ n => have hp := Nat.two_pow_pos n; simp only [Nat.pow_succ]; omega
  obtain ⟨state,hrun,hp⟩ := build_success op shape depth p ht hbuild
  rw [buildAction_initial] at hrun
  have hwords : words (segments shape.segments) = shape.inputLen := by
    unfold words segments
    rw [CollectiveCompose.segmentsFrom_lengths]
    cases shape <;> simp [FoldShape.segments,FoldShape.inputLen]
  have hlength : (segments shape.segments).length = shape.segments.length := segmentsFrom_length 0 0 _
  cases hm : shape.mode with
  | none =>
    simp only [hm,Option.isSome_none,ite_false] at hrun ⊢
    have h := reduceChunks_work op (initialTree depth) (2^depth) 0 1 (segments shape.segments)
      _ _ state htile hrun
    simpa [programWork,hp,toProgram,stateWork,initialBuild,traceWork,hwords,hlength] using h
  | some mode =>
    simp only [hm,Option.isSome_some,ite_true] at hrun ⊢
    have h := scanChunks_work op mode (initialTree depth) (2^depth) 0 1 (segments shape.segments)
      _ _ state htile hrun
    simpa [programWork,hp,toProgram,stateWork,initialBuild,traceWork,hwords] using h

end Obend.Hardware.Gpu.CollectiveWorkBuild
end
