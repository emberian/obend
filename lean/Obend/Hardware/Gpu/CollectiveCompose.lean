module
public import Obend.Hardware.Gpu.CollectiveCorrect
public import Obend.Hardware.Gpu.CollectiveTrace
public import Obend.Hardware.Gpu.CollectiveHierarchy
@[expose] public section

/-! Composition of actual collective dispatches and builder traces. The generic
fold lemmas lift local execution contracts; all local contracts are discharged
by the concrete phase theorems, not admitted as final output hypotheses. -/
namespace Obend.Hardware.Gpu.CollectiveCompose
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
open Obend.Hardware.Gpu.CollectiveBlock Obend.Hardware.Gpu.CollectiveTree
open Obend.Hardware.Gpu.CollectiveTrace Obend.Hardware.Gpu.CollectiveHierarchy
open Obend.Hardware.Gpu.CollectiveCorrect
set_option autoImplicit false

/-- Seed value selected from an optional concrete prefix buffer. -/
def prefixValue (op : ReduceOp) (mem : Memory) (prefixBuffer : Option Nat) (i : Nat) : Word :=
  match prefixBuffer with
  | none => op.identity
  | some a => valueAt mem a i

/-- A source memory invariant survives an actual sequence of groups/actions. -/
theorem foldl_invariant {α β : Type} (step : β → α → β) (xs : List α)
    (P : β → Prop) (before : β) (hp : P before)
    (hstep : ∀ x ∈ xs, ∀ state, P state → P (step state x)) :
    P (xs.foldl step before) := by
  induction xs generalizing before with
  | nil => exact hp
  | cons x xs ih =>
    exact ih (step before x) (hstep x (by simp) before hp)
      (by intro y hy; exact hstep y (by simp [hy]))

/-- One group establishes a point; later groups preserve it. This uses the
actual foldl execution order and also permits earlier groups to touch it. -/
theorem foldl_point {α β γ : Type}
    (step : β → α → β) (xs : List α) (key : α)
    (P : β → Prop) (observe : β → γ) (value : γ) (before : β)
    (hp : P before) (hkey : key ∈ xs)
    (hstep : ∀ x ∈ xs, ∀ state, P state → P (step state x))
    (hwrite : ∀ state, P state → observe (step state key) = value)
    (hframe : ∀ x ∈ xs, x ≠ key → ∀ state, P state →
      observe (step state x) = observe state) :
    observe (xs.foldl step before) = value := by
  classical
  induction xs generalizing before with
  | nil => simp at hkey
  | cons x xs ih =>
    have hnext := hstep x (by simp) before hp
    by_cases htail : key ∈ xs
    · exact ih (step before x) hnext htail
        (by intro y hy; exact hstep y (by simp [hy]))
        (by intro y hy; exact hframe y (by simp [hy]))
    · have hx : x = key := ((List.mem_cons.mp hkey).resolve_right htail).symm
      subst x
      have hw := hwrite before hp
      have hall : P (xs.foldl step (step before key)) ∧
          observe (xs.foldl step (step before key)) = value := by
        apply foldl_invariant step xs (fun s => P s ∧ observe s = value)
          (step before key) ⟨hnext,hw⟩
        intro y hy state hs
        have hne : y ≠ key := by intro he; subst y; exact htail hy
        exact ⟨hstep y (by simp [hy]) state hs.1,
          (hframe y (by simp [hy]) hne state hs.1).trans hs.2⟩
      exact hall.2

/-- Lift a concrete group's readback to its complete dispatch. Source-buffer
invariants supply the same input values before every group, while nonowner
groups frame the selected output location. -/
theorem dispatch_point (p : Program) (d : Dispatch) (mem : Memory)
    (P : Memory → Prop) (hp : P mem) (g a i : Nat) (value : Word) (hg : g < d.groups)
    (hstep : ∀ k < d.groups, ∀ m, P m → P (evalGroup d k m))
    (hwrite : ∀ m, P m → valueAt (evalGroup d g m) a i = value)
    (hframe : ∀ k < d.groups, k ≠ g → ∀ m, P m →
      valueAt (evalGroup d k m) a i = valueAt m a i) :
    valueAt (evalDispatch d mem) a i = value := by
  exact foldl_point (fun m k => evalGroup d k m) (List.range d.groups) g P
    (fun m => valueAt m a i) value mem hp (List.mem_range.mpr hg)
    (by intro k hk; exact hstep k (List.mem_range.mp hk)) hwrite
    (by intro k hk; exact hframe k (List.mem_range.mp hk))

/-- Every group in a reduction bucket writes the reduction selected by its
actual descriptor. Scratch reuse cannot change the source between groups. -/
theorem reduceBucket_value (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst valid depth : Nat) (cs : List Chunk) (mem : Memory)
    (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hsrc : ∀ k ≤ depth, tree.up+k ≠ src)
    (hdst : ∀ k ≤ depth, tree.up+k ≠ dst) (hne : src ≠ dst)
    (hunique : (cs.map (·.result)).Nodup)
    (hb : ∀ g < cs.length, ∀ ph ∈ reducePhases op tree src dst valid depth
        (descriptor cs (·.start)) (descriptor cs (·.result)), PhaseInBounds p ph g)
    (hn : ∀ g < cs.length, ∀ ph ∈ reducePhases op tree src dst valid depth
        (descriptor cs (·.start)) (descriptor cs (·.result)), (ph.writeAddresses g).Nodup)
    (g : Nat) (hgl : g < cs.length) :
    valueAt (evalDispatch ⟨cs.length,reducePhases op tree src dst valid depth
      (descriptor cs (·.start)) (descriptor cs (·.result))⟩ mem) dst cs[g].result =
      foldRange op (valueAt mem src) cs[g].start valid op.identity := by
  let phases := reducePhases op tree src dst valid depth
    (descriptor cs (·.start)) (descriptor cs (·.result))
  let dispatch : Dispatch := ⟨cs.length,phases⟩
  let P := fun m => Good p m ∧ ∀ i, valueAt m src i = valueAt mem src i
  have hp : P mem := ⟨hg,fun _ => rfl⟩
  have hoff : ∀ k (hk : k < cs.length) l, (descriptor cs (·.start)).eval k l = cs[k].start := by
    intro k hk l
    exact descriptor_eval_member cs (·.start) k l hk
  have hstep : ∀ k < cs.length, ∀ m, P m → P (evalGroup dispatch k m) := by
    intro k hk m hm
    constructor
    · exact evalGroup_good p dispatch k m hm.1
    · intro i
      have hf := reduceGroup_frame p op tree src dst valid depth k
        (descriptor cs (·.start)) (descriptor cs (·.result)) m hm.1 (hb k hk)
        src i hsrc (by intro he; exact False.elim (hne he))
      exact hf.trans (hm.2 i)
  apply dispatch_point p dispatch mem P hp g dst cs[g].result _ hgl hstep
  · intro m hm
    have hh := reduceGroup_value p op tree src dst valid depth g cs[g].start
      (descriptor cs (·.start)) (descriptor cs (·.result)) m hm.1 hv
      (fun l _ => hoff g hgl l) (hb g hgl) (hn g hgl)
    rw [descriptor_eval_member cs (·.result) g 0 hgl] at hh
    have he : valueAt m src = valueAt mem src := funext hm.2
    simpa only [dispatch, phases, evalGroup, he] using hh
  · intro k hk hkg m hm
    have hresult : (descriptor cs (·.result)).eval k 0 ≠ cs[g].result := by
      rw [descriptor_eval_member cs (·.result) k 0 hk]
      intro he
      apply hkg
      apply hunique.eq_of_getElem_eq (by simpa using hk) (by simpa using hgl)
      simpa using he
    exact reduceGroup_frame p op tree src dst valid depth k
      (descriptor cs (·.start)) (descriptor cs (·.result)) m hm.1 (hb k hk)
      dst cs[g].result hdst (by intro _; exact hresult)

/-- Reduction dispatch frame, used to preserve input arrays, prefix buffers,
and results written by earlier buckets. -/
theorem reduceBucket_frame (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst valid depth : Nat) (cs : List Chunk) (mem : Memory) (hg : Good p mem)
    (hb : ∀ g < cs.length, ∀ ph ∈ reducePhases op tree src dst valid depth
        (descriptor cs (·.start)) (descriptor cs (·.result)), PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ depth, tree.up+k ≠ a)
    (hout : a = dst → ∀ c ∈ cs, i ≠ c.result) :
    valueAt (evalDispatch ⟨cs.length,reducePhases op tree src dst valid depth
      (descriptor cs (·.start)) (descriptor cs (·.result))⟩ mem) a i = valueAt mem a i := by
  let dispatch : Dispatch := ⟨cs.length,reducePhases op tree src dst valid depth
    (descriptor cs (·.start)) (descriptor cs (·.result))⟩
  have h := foldl_invariant (fun m g => evalGroup dispatch g m) (List.range cs.length)
    (fun m => Good p m ∧ valueAt m a i = valueAt mem a i) mem ⟨hg,rfl⟩
    (by
      intro g hg' m hm
      have hgl := List.mem_range.mp hg'
      constructor
      · exact evalGroup_good p dispatch g m hm.1
      · have hf := reduceGroup_frame p op tree src dst valid depth g
          (descriptor cs (·.start)) (descriptor cs (·.result)) m hm.1 (hb g hgl) a i hup
          (by intro he; rw [descriptor_eval_member cs (·.result) g 0 hgl]; exact (hout he cs[g] (List.getElem_mem hgl)).symm)
        exact hf.trans hm.2)
  exact h.2

/-- A scan bucket preserves every array outside its scratch rows and output
intervals. This includes its original input and optional prefix buffer. -/
theorem scanBucket_frame (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth : Nat) (cs : List Chunk) (prefixBuffer : Option Nat)
    (mem : Memory) (hg : Good p mem)
    (hb : ∀ g < cs.length, ∀ ph ∈ scanPhases op mode tree src dst valid depth
      (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result))), PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ depth, tree.up+k ≠ a) (hdown : ∀ k ≤ depth, tree.down+k ≠ a)
    (hout : a = dst → ∀ c ∈ cs, i < c.start ∨ c.start+valid ≤ i) :
    valueAt (evalDispatch ⟨cs.length,scanPhases op mode tree src dst valid depth
      (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result)))⟩ mem) a i =
      valueAt mem a i := by
  let dispatch : Dispatch := ⟨cs.length,scanPhases op mode tree src dst valid depth
    (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result)))⟩
  have h := foldl_invariant (fun m g => evalGroup dispatch g m) (List.range cs.length)
    (fun m => Good p m ∧ valueAt m a i = valueAt mem a i) mem ⟨hg,rfl⟩
    (by
      intro g hg' m hm
      have hgl := List.mem_range.mp hg'
      constructor
      · exact evalGroup_good p dispatch g m hm.1
      · have hf := scanGroup_frame p op mode tree src dst valid depth g cs[g].start
          (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result))) m hm.1
          (fun l _ => descriptor_eval_member cs (·.start) g l hgl) (hb g hgl) a i hup hdown
          (by intro he; exact hout he cs[g] (List.getElem_mem hgl))
        exact hf.trans hm.2)
  exact h.2

/-- Complete scan bucket readback. The original source and optional prefix
buffer stay fixed across groups; prior output intervals survive scratch reuse. -/
theorem scanBucket_value (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst valid depth : Nat) (cs : List Chunk) (prefixBuffer : Option Nat)
    (mem : Memory) (hg : Good p mem) (hv : valid ≤ 2^depth)
    (hsplit : ∀ k ≤ depth, ∀ j ≤ depth, tree.up+k ≠ tree.down+j)
    (hsrcup : ∀ k ≤ depth, tree.up+k ≠ src)
    (hsrcdown : ∀ k ≤ depth, tree.down+k ≠ src) (hne : src ≠ dst)
    (hdstup : ∀ k ≤ depth, tree.up+k ≠ dst)
    (hdstdown : ∀ k ≤ depth, tree.down+k ≠ dst)
    (hpre : ∀ a, prefixBuffer = some a → a ≠ dst ∧
      (∀ k ≤ depth, tree.up+k ≠ a) ∧ (∀ k ≤ depth, tree.down+k ≠ a))
    (hdisjoint : ∀ g (hg : g < cs.length) k (hk : k < cs.length), g ≠ k →
      ∀ i < valid, ∀ j < valid, cs[g].start+i ≠ cs[k].start+j)
    (hb : ∀ g < cs.length, ∀ ph ∈ scanPhases op mode tree src dst valid depth
      (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result))), PhaseInBounds p ph g)
    (hn : ∀ g < cs.length, ∀ ph ∈ scanPhases op mode tree src dst valid depth
      (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result))), (ph.writeAddresses g).Nodup)
    (g : Nat) (hgl : g < cs.length) (i : Nat) (hi : i < valid) :
    valueAt (evalDispatch ⟨cs.length,scanPhases op mode tree src dst valid depth
      (descriptor cs (·.start)) (prefixBuffer.map fun a => (a,descriptor cs (·.result)))⟩ mem)
      dst (cs[g].start+i) = foldRange op (valueAt mem src) cs[g].start (i+mode.extra)
        (prefixValue op mem prefixBuffer cs[g].result) := by
  let seed := prefixBuffer.map fun a => (a,descriptor cs (·.result))
  let dispatch : Dispatch := ⟨cs.length,scanPhases op mode tree src dst valid depth (descriptor cs (·.start)) seed⟩
  let P := fun m => Good p m ∧ (∀ i, valueAt m src i = valueAt mem src i) ∧
    ∀ a, prefixBuffer = some a → ∀ i, valueAt m a i = valueAt mem a i
  have hp : P mem := ⟨hg,(fun _ => rfl),fun _ _ _ => rfl⟩
  have frame : ∀ k (hk : k < cs.length) m, Good p m → ∀ a,
      (∀ j ≤ depth, tree.up+j ≠ a) → (∀ j ≤ depth, tree.down+j ≠ a) →
      a ≠ dst → ∀ i, valueAt (evalGroup dispatch k m) a i = valueAt m a i := by
    intro k hk m hm a hu hd hne' i
    exact scanGroup_frame p op mode tree src dst valid depth k cs[k].start
      (descriptor cs (·.start)) seed m hm
      (fun l _ => descriptor_eval_member cs (·.start) k l hk) (hb k hk) a i hu hd
      (by intro he; exact False.elim (hne' he))
  have hstep : ∀ k < cs.length, ∀ m, P m → P (evalGroup dispatch k m) := by
    intro k hk m hm
    refine ⟨evalGroup_good p dispatch k m hm.1, ?_, ?_⟩
    · intro j
      exact (frame k hk m hm.1 src hsrcup hsrcdown hne j).trans (hm.2.1 j)
    · intro a ha j
      have hpa := hpre a ha
      exact (frame k hk m hm.1 a hpa.2.1 hpa.2.2 hpa.1 j).trans (hm.2.2 a ha j)
  apply dispatch_point p dispatch mem P hp g dst (cs[g].start+i) _ hgl hstep
  · intro m hm
    have hs : ∀ a ix, seed = some (a,ix) → ∀ k ≤ depth, tree.up+k ≠ a := by
      intro a ix he
      cases hpref : prefixBuffer with
      | none => simp [seed,hpref] at he
      | some b =>
        simp only [seed,hpref,Option.map_some,Option.some.injEq,Prod.mk.injEq] at he
        obtain ⟨rfl,_⟩ := he
        exact (hpre b hpref).2.1
    have hh := scanGroup_value p op mode tree src dst valid depth g cs[g].start
      (descriptor cs (·.start)) seed m hm.1 hv
      (fun l _ => descriptor_eval_member cs (·.start) g l hgl) hsplit hs (hb g hgl) (hn g hgl) i hi
    have he : valueAt m src = valueAt mem src := funext hm.2.1
    rw [he] at hh
    cases hpref : prefixBuffer with
    | none => simpa only [dispatch, evalGroup, seedValue, prefixValue, seed,hpref,Option.map_none] using hh
    | some a =>
      simpa only [dispatch, evalGroup, seedValue, prefixValue, seed,hpref,Option.map_some,descriptor_eval_member cs (·.result) g 0 hgl,hm.2.2 a hpref] using hh
  · intro k hk hkg m hm
    apply scanGroup_frame p op mode tree src dst valid depth k cs[k].start
      (descriptor cs (·.start)) seed m hm.1
      (fun l _ => descriptor_eval_member cs (·.start) k l hk) (hb k hk)
      dst (cs[g].start+i) hdstup hdstdown
    intro _
    by_cases hlow : cs[g].start+i < cs[k].start
    · exact Or.inl hlow
    · apply Or.inr
      by_cases hhigh : cs[k].start+valid ≤ cs[g].start+i
      · exact hhigh
      · have hj : cs[g].start+i-cs[k].start < valid := by omega
        have hneq := hdisjoint g hgl k hk hkg.symm i hi
          (cs[g].start+i-cs[k].start) hj
        omega

theorem bucket_filter (cs bucket : List Chunk) (valid : Nat)
    (hb : (valid,bucket) ∈ buckets cs) : bucket = cs.filter (·.length == valid) := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  cases he
  rfl

theorem bucket_results_nodup (cs bucket : List Chunk) (valid : Nat)
    (hb : (valid,bucket) ∈ buckets cs) (hu : (cs.map (·.result)).Nodup) :
    (bucket.map (·.result)).Nodup := by
  rw [bucket_filter cs bucket valid hb]
  exact List.Nodup.sublist (List.Sublist.map Chunk.result (List.filter_sublist (p := fun c : Chunk => c.length == valid) (l := cs))) hu

/-- Actual localReduce dispatch trace, across all length buckets. This is the
contract consumed by the recursive builder proof. -/
theorem localReduce_trace_value (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (mem : Memory) (hg : Good p mem)
    (hdepth : ∀ valid bucket, (valid,bucket) ∈ buckets cs → tileDepth valid ≤ tree.depth)
    (hsrc : ∀ k ≤ tree.depth, tree.up+k ≠ src)
    (hdst : ∀ k ≤ tree.depth, tree.up+k ≠ dst) (hne : src ≠ dst)
    (hunique : (cs.map (·.result)).Nodup)
    (hb : ∀ valid bucket, (valid,bucket) ∈ buckets cs → ∀ g < bucket.length,
      ∀ ph ∈ reducePhases op tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (descriptor bucket (·.result)), PhaseInBounds p ph g)
    (hn : ∀ valid bucket, (valid,bucket) ∈ buckets cs → ∀ g < bucket.length,
      ∀ ph ∈ reducePhases op tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (descriptor bucket (·.result)), (ph.writeAddresses g).Nodup)
    (c : Chunk) (hc : c ∈ cs) :
    valueAt (evalTrace (reduceDispatches op tree src dst cs) mem) dst c.result =
      foldRange op (valueAt mem src) c.start c.length op.identity := by
  let key := (c.length,cs.filter (·.length == c.length))
  let step := fun m (b : Nat × List Chunk) => evalDispatch
    ⟨b.2.length,reducePhases op tree src dst b.1 (tileDepth b.1)
      (descriptor b.2 (·.start)) (descriptor b.2 (·.result))⟩ m
  let P := fun m => Good p m ∧ ∀ i, valueAt m src i = valueAt mem src i
  have hkey : key ∈ buckets cs := buckets_complete cs c hc
  have hstep : ∀ b ∈ buckets cs, ∀ m, P m → P (step m b) := by
    intro b hb' m hm
    constructor
    · exact evalDispatch_good p _ m hm.1
    · intro i
      have hf := reduceBucket_frame p op tree src dst b.1 (tileDepth b.1) b.2 m hm.1
        (hb b.1 b.2 hb') src i
        (fun k hk => hsrc k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
        (by intro he; exact False.elim (hne he))
      exact hf.trans (hm.2 i)
  have hwrite : ∀ m, P m → valueAt (step m key) dst c.result =
      foldRange op (valueAt mem src) c.start c.length op.identity := by
    intro m hm
    have hck : c ∈ key.2 := by simp [key,hc]
    obtain ⟨g,hg',he⟩ := List.getElem_of_mem hck
    have hh := reduceBucket_value p op tree src dst c.length (tileDepth c.length) key.2 m hm.1
      (tileDepth_covers c.length)
      (fun k hk => hsrc k (Nat.le_trans hk (hdepth key.1 key.2 hkey)))
      (fun k hk => hdst k (Nat.le_trans hk (hdepth key.1 key.2 hkey))) hne
      (bucket_results_nodup cs key.2 key.1 hkey hunique)
      (hb key.1 key.2 hkey) (hn key.1 key.2 hkey) g hg'
    have hr : valueAt m src = valueAt mem src := funext hm.2
    simpa only [he,hr] using hh
  have hframe : ∀ b ∈ buckets cs, b ≠ key → ∀ m, P m →
      valueAt (step m b) dst c.result = valueAt m dst c.result := by
    intro b hb' hnekey m hm
    apply reduceBucket_frame p op tree src dst b.1 (tileDepth b.1) b.2 m hm.1
      (hb b.1 b.2 hb') dst c.result
      (fun k hk => hdst k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
    intro _ d hd hsame
    have hdc := bucket_member cs b.2 b.1 hb' d hd
    have he : c = d := result_injective cs hunique c d hc hdc.1 hsame
    subst d
    apply hnekey
    have hf := bucket_filter cs b.2 b.1 hb'
    apply Prod.ext
    · exact hdc.2.symm
    · simpa only [key,hdc.2] using hf
  have hh := foldl_point step (buckets cs) key P (fun m => valueAt m dst c.result)
    (foldRange op (valueAt mem src) c.start c.length op.identity) mem
    ⟨hg,fun _ => rfl⟩ hkey hstep hwrite hframe
  simpa only [reduceDispatches,evalTrace_flatMap,evalTrace_emitted,step] using hh

/-- All reduction buckets preserve cells outside their scratch and result slots. -/
theorem localReduce_trace_frame (p : Program) (op : ReduceOp) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (mem : Memory) (hg : Good p mem)
    (hdepth : ∀ valid bucket, (valid,bucket) ∈ buckets cs → tileDepth valid ≤ tree.depth)
    (hb : ∀ valid bucket, (valid,bucket) ∈ buckets cs → ∀ g < bucket.length,
      ∀ ph ∈ reducePhases op tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (descriptor bucket (·.result)), PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ tree.depth, tree.up+k ≠ a)
    (hout : a = dst → ∀ c ∈ cs, i ≠ c.result) :
    valueAt (evalTrace (reduceDispatches op tree src dst cs) mem) a i = valueAt mem a i := by
  let step := fun m (b : Nat × List Chunk) => evalDispatch
    ⟨b.2.length,reducePhases op tree src dst b.1 (tileDepth b.1)
      (descriptor b.2 (·.start)) (descriptor b.2 (·.result))⟩ m
  have h := foldl_invariant step (buckets cs)
    (fun m => Good p m ∧ valueAt m a i = valueAt mem a i) mem ⟨hg,rfl⟩
    (by
      intro b hb' m hm
      constructor
      · exact evalDispatch_good p _ m hm.1
      · have hf := reduceBucket_frame p op tree src dst b.1 (tileDepth b.1) b.2 m hm.1
          (hb b.1 b.2 hb') a i
          (fun k hk => hup k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
          (by intro he c hc; exact hout he c (bucket_member cs b.2 b.1 hb' c hc).1)
        exact hf.trans hm.2)
  simpa only [reduceDispatches,evalTrace_flatMap,evalTrace_emitted,step] using h.2

theorem bucket_key_of_member (cs : List Chunk) (b : Nat × List Chunk)
    (hb : b ∈ buckets cs) (c : Chunk) (hc : c ∈ b.2) :
    b = (c.length,cs.filter (·.length == c.length)) := by
  have hm := bucket_member cs b.2 b.1 hb c hc
  have hf := bucket_filter cs b.2 b.1 hb
  apply Prod.ext
  · exact hm.2.symm
  · simpa only [hm.2] using hf

/-- The actual localScan trace across every length bucket. The disjointness
premise is the proved property of segments/chunks, independent of input values. -/
theorem localScan_trace_value (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (prefixBuffer : Option Nat) (mem : Memory) (hg : Good p mem)
    (hdepth : ∀ valid bucket, (valid,bucket) ∈ buckets cs → tileDepth valid ≤ tree.depth)
    (hsplit : ∀ k ≤ tree.depth, ∀ j ≤ tree.depth, tree.up+k ≠ tree.down+j)
    (hsrcup : ∀ k ≤ tree.depth, tree.up+k ≠ src)
    (hsrcdown : ∀ k ≤ tree.depth, tree.down+k ≠ src) (hne : src ≠ dst)
    (hdstup : ∀ k ≤ tree.depth, tree.up+k ≠ dst)
    (hdstdown : ∀ k ≤ tree.depth, tree.down+k ≠ dst)
    (hpre : ∀ a, prefixBuffer = some a → a ≠ dst ∧
      (∀ k ≤ tree.depth, tree.up+k ≠ a) ∧ (∀ k ≤ tree.depth, tree.down+k ≠ a))
    (hunique : (cs.map (·.result)).Nodup)
    (hdisjoint : ∀ c ∈ cs, ∀ d ∈ cs, ∀ i < c.length, ∀ j < d.length,
      c.start+i = d.start+j → c = d)
    (hb : ∀ valid bucket, (valid,bucket) ∈ buckets cs → 0 < valid → ∀ g < bucket.length,
      ∀ ph ∈ scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))), PhaseInBounds p ph g)
    (hn : ∀ valid bucket, (valid,bucket) ∈ buckets cs → 0 < valid → ∀ g < bucket.length,
      ∀ ph ∈ scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))), (ph.writeAddresses g).Nodup)
    (c : Chunk) (hc : c ∈ cs) (i : Nat) (hi : i < c.length) :
    valueAt (evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem) dst (c.start+i) =
      foldRange op (valueAt mem src) c.start (i+mode.extra)
        (prefixValue op mem prefixBuffer c.result) := by
  let key := (c.length,cs.filter (·.length == c.length))
  let step := fun m (b : Nat × List Chunk) => if 0 < b.1 then evalDispatch
    ⟨b.2.length,scanPhases op mode tree src dst b.1 (tileDepth b.1)
      (descriptor b.2 (·.start)) (prefixBuffer.map fun a => (a,descriptor b.2 (·.result)))⟩ m else m
  let P := fun m => Good p m ∧ (∀ i, valueAt m src i = valueAt mem src i) ∧
    ∀ a, prefixBuffer = some a → ∀ i, valueAt m a i = valueAt mem a i
  have hkey : key ∈ buckets cs := buckets_complete cs c hc
  have hpos : 0 < c.length := by omega
  have preserve : ∀ b ∈ buckets cs, ∀ m, Good p m → ∀ a,
      (∀ k ≤ tree.depth, tree.up+k ≠ a) → (∀ k ≤ tree.depth, tree.down+k ≠ a) →
      a ≠ dst → ∀ i, valueAt (step m b) a i = valueAt m a i := by
    intro b hb' m hm a hu hd ha j
    dsimp only [step]
    split
    · rename_i hv
      exact scanBucket_frame p op mode tree src dst b.1 (tileDepth b.1) b.2 prefixBuffer m hm
        (hb b.1 b.2 hb' hv) a j
        (fun k hk => hu k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
        (fun k hk => hd k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
        (by intro he; exact False.elim (ha he))
    · rfl
  have hstep : ∀ b ∈ buckets cs, ∀ m, P m → P (step m b) := by
    intro b hb' m hm
    refine ⟨?_,?_,?_⟩
    · dsimp only [step]; split
      · exact evalDispatch_good p _ m hm.1
      · exact hm.1
    · intro j
      exact (preserve b hb' m hm.1 src hsrcup hsrcdown hne j).trans (hm.2.1 j)
    · intro a ha j
      have hpa := hpre a ha
      exact (preserve b hb' m hm.1 a hpa.2.1 hpa.2.2 hpa.1 j).trans (hm.2.2 a ha j)
  have hwrite : ∀ m, P m → valueAt (step m key) dst (c.start+i) =
      foldRange op (valueAt mem src) c.start (i+mode.extra)
        (prefixValue op mem prefixBuffer c.result) := by
    intro m hm
    have hck : c ∈ key.2 := by simp [key,hc]
    obtain ⟨g,hg',he⟩ := List.getElem_of_mem hck
    have hd := hdepth key.1 key.2 hkey
    have hwithin : ∀ k, k ≤ tileDepth c.length → k ≤ tree.depth := fun k hk => Nat.le_trans hk hd
    have hu := bucket_results_nodup cs key.2 key.1 hkey hunique
    have hbd : ∀ g (hg : g < key.2.length) k (hk : k < key.2.length), g ≠ k →
        ∀ i < c.length, ∀ j < c.length, key.2[g].start+i ≠ key.2[k].start+j := by
      intro g hg'' k hk hne' i' hi' j hj heq
      have hcg := bucket_member cs key.2 key.1 hkey key.2[g] (List.getElem_mem hg'')
      have hck' := bucket_member cs key.2 key.1 hkey key.2[k] (List.getElem_mem hk)
      have hcd := hdisjoint key.2[g] hcg.1 key.2[k] hck'.1 i' (by simpa [hcg.2] using hi')
        j (by simpa [hck'.2] using hj) heq
      apply hne'
      apply hu.eq_of_getElem_eq (by simpa using hg'') (by simpa using hk)
      simpa using congrArg Chunk.result hcd
    have hh := scanBucket_value p op mode tree src dst c.length (tileDepth c.length) key.2 prefixBuffer m hm.1
      (tileDepth_covers c.length)
      (fun k hk j hj => hsplit k (hwithin k hk) j (hwithin j hj))
      (fun k hk => hsrcup k (hwithin k hk)) (fun k hk => hsrcdown k (hwithin k hk)) hne
      (fun k hk => hdstup k (hwithin k hk)) (fun k hk => hdstdown k (hwithin k hk))
      (by intro a ha; have h := hpre a ha; exact ⟨h.1,fun k hk => h.2.1 k (hwithin k hk),fun k hk => h.2.2 k (hwithin k hk)⟩)
      hbd (hb key.1 key.2 hkey hpos) (hn key.1 key.2 hkey hpos) g hg' i hi
    have hr : valueAt m src = valueAt mem src := funext hm.2.1
    rw [he,hr] at hh
    have hseed : prefixValue op m prefixBuffer c.result = prefixValue op mem prefixBuffer c.result := by
      cases hpref : prefixBuffer with
      | none => rfl
      | some a => exact hm.2.2 a hpref _
    rw [hseed] at hh
    simpa only [step,key,if_pos hpos] using hh
  have hframe : ∀ b ∈ buckets cs, b ≠ key → ∀ m, P m →
      valueAt (step m b) dst (c.start+i) = valueAt m dst (c.start+i) := by
    intro b hb' hnekey m hm
    dsimp only [step]
    split
    · rename_i hv
      apply scanBucket_frame p op mode tree src dst b.1 (tileDepth b.1) b.2 prefixBuffer m hm.1
        (hb b.1 b.2 hb' hv) dst (c.start+i)
        (fun k hk => hdstup k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
        (fun k hk => hdstdown k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
      intro _ d hd
      have hdc := bucket_member cs b.2 b.1 hb' d hd
      by_cases hlow : c.start+i < d.start
      · exact Or.inl hlow
      · apply Or.inr
        by_cases hhigh : d.start+b.1 ≤ c.start+i
        · exact hhigh
        · have hj : c.start+i-d.start < d.length := by omega
          have he := hdisjoint c hc d hdc.1 i hi (c.start+i-d.start) hj (by omega)
          subst d
          exact False.elim (hnekey (bucket_key_of_member cs b hb' c hd))
    · rfl
  have hh := foldl_point step (buckets cs) key P (fun m => valueAt m dst (c.start+i))
    (foldRange op (valueAt mem src) c.start (i+mode.extra)
      (prefixValue op mem prefixBuffer c.result)) mem
    ⟨hg,(fun _ => rfl),fun _ _ _ => rfl⟩ hkey hstep hwrite hframe
  have heval : evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem =
      (buckets cs).foldl step mem := by
    rw [scanDispatches,evalTrace_flatMap]
    congr 1
    funext m b
    cases b with
    | mk valid bucket =>
      dsimp only [step]
      split <;> simp [evalTrace_emitted]
  rw [heval]
  exact hh

/-- All scan buckets preserve cells outside their scratch and descriptor
intervals, including earlier segment outputs. -/
theorem localScan_trace_frame (p : Program) (op : ReduceOp) (mode : ScanMode) (tree : Trees)
    (src dst : Nat) (cs : List Chunk) (prefixBuffer : Option Nat) (mem : Memory) (hg : Good p mem)
    (hdepth : ∀ valid bucket, (valid,bucket) ∈ buckets cs → tileDepth valid ≤ tree.depth)
    (hb : ∀ valid bucket, (valid,bucket) ∈ buckets cs → 0 < valid → ∀ g < bucket.length,
      ∀ ph ∈ scanPhases op mode tree src dst valid (tileDepth valid)
        (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result))), PhaseInBounds p ph g)
    (a i : Nat) (hup : ∀ k ≤ tree.depth, tree.up+k ≠ a)
    (hdown : ∀ k ≤ tree.depth, tree.down+k ≠ a)
    (hout : a = dst → ∀ c ∈ cs, i < c.start ∨ c.start+c.length ≤ i) :
    valueAt (evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem) a i = valueAt mem a i := by
  let step := fun m (b : Nat × List Chunk) => if 0 < b.1 then evalDispatch
    ⟨b.2.length,scanPhases op mode tree src dst b.1 (tileDepth b.1)
      (descriptor b.2 (·.start)) (prefixBuffer.map fun a => (a,descriptor b.2 (·.result)))⟩ m else m
  have hh := foldl_invariant step (buckets cs)
    (fun m => Good p m ∧ valueAt m a i = valueAt mem a i) mem ⟨hg,rfl⟩
    (by
      intro b hb' m hm
      dsimp only [step]
      split
      · rename_i hv
        constructor
        · exact evalDispatch_good p _ m hm.1
        · have hf := scanBucket_frame p op mode tree src dst b.1 (tileDepth b.1) b.2 prefixBuffer m hm.1
            (hb b.1 b.2 hb' hv) a i
            (fun k hk => hup k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
            (fun k hk => hdown k (Nat.le_trans hk (hdepth b.1 b.2 hb')))
            (by
              intro he c hc
              have hm := bucket_member cs b.2 b.1 hb' c hc
              simpa only [hm.2] using hout he c hm.1)
          exact hf.trans hm.2
      · exact hm)
  have heval : evalTrace (scanDispatches op mode tree src dst cs prefixBuffer) mem =
      (buckets cs).foldl step mem := by
    rw [scanDispatches,evalTrace_flatMap]
    congr 1
    funext m b
    cases b with
    | mk valid bucket => dsimp only [step]; split <;> simp [evalTrace_emitted]
  rw [heval]
  exact hh.2

/-- A trace is an actual portion of the checked final program. -/
def TraceIn (p : Program) (ds : List Dispatch) : Prop := ∀ d ∈ ds, d ∈ p.dispatches

theorem reduceTrace_checked (p : Program) (hcheck : p.check = .ok ())
    (op : ReduceOp) (tree : Trees) (src dst : Nat) (cs : List Chunk)
    (htrace : TraceIn p (reduceDispatches op tree src dst cs))
    (valid : Nat) (bucket : List Chunk) (hbucket : (valid,bucket) ∈ buckets cs)
    (g : Nat) (hg : g < bucket.length) (ph : Phase)
    (hph : ph ∈ reducePhases op tree src dst valid (tileDepth valid)
      (descriptor bucket (·.start)) (descriptor bucket (·.result))) :
    PhaseInBounds p ph g ∧ (ph.writeAddresses g).Nodup := by
  let phases := reducePhases op tree src dst valid (tileDepth valid)
    (descriptor bucket (·.start)) (descriptor bucket (·.result))
  have hp : phases.isEmpty = false := by
    dsimp only [phases,reducePhases]
    split <;> simp
  have hpos : bucket.length > 0 := by omega
  have hd : (⟨bucket.length,phases⟩ : Dispatch) ∈ reduceDispatches op tree src dst cs := by
    apply List.mem_flatMap.mpr
    refine ⟨(valid,bucket),hbucket,?_⟩
    simp [emitted,hpos,hp,phases]
  exact checkedPhase p hcheck _ (htrace _ hd) g hg ph hph

theorem scanTrace_checked (p : Program) (hcheck : p.check = .ok ())
    (op : ReduceOp) (mode : ScanMode) (tree : Trees) (src dst : Nat)
    (cs : List Chunk) (prefixBuffer : Option Nat)
    (htrace : TraceIn p (scanDispatches op mode tree src dst cs prefixBuffer))
    (valid : Nat) (bucket : List Chunk) (hbucket : (valid,bucket) ∈ buckets cs) (hv : 0 < valid)
    (g : Nat) (hg : g < bucket.length) (ph : Phase)
    (hph : ph ∈ scanPhases op mode tree src dst valid (tileDepth valid)
      (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result)))) :
    PhaseInBounds p ph g ∧ (ph.writeAddresses g).Nodup := by
  let phases := scanPhases op mode tree src dst valid (tileDepth valid)
    (descriptor bucket (·.start)) (prefixBuffer.map fun a => (a,descriptor bucket (·.result)))
  have hp : phases.isEmpty = false := by simp [phases,scanPhases]
  have hpos : bucket.length > 0 := by omega
  have hd : (⟨bucket.length,phases⟩ : Dispatch) ∈ scanDispatches op mode tree src dst cs prefixBuffer := by
    apply List.mem_flatMap.mpr
    refine ⟨(valid,bucket),hbucket,?_⟩
    simp [emitted,hv,hpos,hp,phases]
  exact checkedPhase p hcheck _ (htrace _ hd) g hg ph hph

/-- Bucket depth follows from concrete descriptor capacities; no data-dependent
or output-equality condition enters the tree allocation proof. -/
theorem bucket_depth_le (cs : List Chunk) (depth : Nat)
    (hcap : ∀ c ∈ cs, c.length ≤ 2^depth) (valid : Nat) (bucket : List Chunk)
    (hb : (valid,bucket) ∈ buckets cs) : tileDepth valid ≤ depth := by
  obtain ⟨n,hn,he⟩ := List.mem_map.mp hb
  cases he
  obtain ⟨c,hc,he⟩ := List.mem_map.mp (List.mem_eraseDups.mp hn)
  rw [← he]
  exact tileDepth_le c.length depth (hcap c hc)

theorem segmentsFrom_lengths (start result : Nat) (ns : List Nat) :
    (segmentsFrom start result ns).map (·.length) = ns := by
  induction ns generalizing start result with
  | nil => rfl
  | cons n ns ih => simp [segmentsFrom,ih]

theorem segments_capacity (ns : List Nat) (depth : Nat)
    (h : ∀ n ∈ ns, n ≤ 2^depth) : ∀ c ∈ segments ns, c.length ≤ 2^depth := by
  intro c hc
  apply h c.length
  rw [← segmentsFrom_lengths 0 0 ns]
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

theorem chunks_capacity (tile : Nat) (ns : List Nat) : ∀ c ∈ chunks tile ns, c.length ≤ tile := by
  have all : ∀ start result, ∀ c ∈ chunksFrom tile start result ns, c.length ≤ tile := by
    induction ns with
    | nil => intro start result c hc; simp [chunksFrom] at hc
    | cons n ns ih =>
      intro start result c hc
      simp only [chunksFrom,List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hc
        exact Nat.min_le_left _ _
      · exact ih (start+n) (result+(n+tile-1)/tile) c hc
  exact all 0 0

end Obend.Hardware.Gpu.CollectiveCompose
end
