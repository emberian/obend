module
/-
Whole-dispatch G4 composition. Workgroup memory is renamed by its instance; storage addresses stay
shared across groups. Thread labels are globally distinct. This file lifts the admitted local
barrier witnesses into the concatenated shape and uses source scatter ownership between groups.
-/
public import Obend.Hardware.Gpu.SourceProtocol
public import Obend.Hardware.ArrayKernelOwnership
@[expose] public section

namespace Obend.Hardware.Gpu.DispatchProtocol
open Obend.Hardware.Gpu.Memory
open Obend.Hardware.ArrayKernel
set_option autoImplicit false

/-- Interleave group tags instead of reserving an unproved maximum local address. -/
def tag (groups group localIdx : Nat) : Nat := localIdx * groups + group

theorem tag_group (groups group localIdx : Nat) (hg : group < groups) :
    tag groups group localIdx % groups = group := by
  simp [tag, Nat.add_mod, Nat.mod_eq_of_lt hg]

theorem tag_injective (groups g h a b : Nat) (hg : g < groups) (hh : h < groups)
    (he : tag groups g a = tag groups h b) : g = h ∧ a = b := by
  have hgh := congrArg (· % groups) he
  rw [tag_group groups g a hg, tag_group groups h b hh] at hgh
  subst h
  have hab : a * groups = b * groups := by unfold tag at he; omega
  exact ⟨rfl, (Nat.mul_right_cancel (show 0 < groups by omega) hab)⟩

def tagLoc (groups group : Nat) (l : Loc) : Loc :=
  match l.space with
  | .storage => l
  | .workgroup => ⟨.workgroup, tag groups group l.idx⟩

def tagEvent (groups group : Nat) : Ev → Ev
  | .write l v a => .write (tagLoc groups group l) v a
  | .read l a => .read (tagLoc groups group l) a
  | .rmw l op => .rmw (tagLoc groups group l) op
  | .barrier i sems => .barrier i sems

def tagNode (groups group : Nat) (n : Node) : Node :=
  { id := ⟨tag groups group n.id.t, n.id.i⟩, wg := group,
    ev := tagEvent groups group n.ev }

def tagShape (groups group : Nat) (P : Shape) : Shape :=
  { threads := P.threads.map fun t =>
      { id := tag groups group t.id, wg := group, prog := t.prog.map (tagEvent groups group) } }

/-- Workgroups have independent input snapshots. Race freedom quantifies over all of them. -/
def dispatchTrace (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width : Nat) : Shape :=
  { threads := (List.range d.groups).flatMap fun g =>
      (tagShape d.groups g (Workgroup.sourceTrace p d (mem g) g width)).threads }

@[simp] theorem tagEvent_loc (groups g : Nat) (e : Ev) :
    (tagEvent groups g e).loc? = e.loc?.map (tagLoc groups g) := by
  cases e <;> rfl
@[simp] theorem tagEvent_write (groups g : Nat) (e : Ev) :
    (tagEvent groups g e).isWrite = e.isWrite := by cases e <;> rfl
@[simp] theorem tagEvent_read (groups g : Nat) (e : Ev) :
    (tagEvent groups g e).isRead = e.isRead := by cases e <;> rfl
@[simp] theorem tagEvent_spaces (groups g : Nat) (e : Ev) (spaces : List Space) :
    (tagEvent groups g e).inSpaces spaces = e.inSpaces spaces := by
  cases e with
  | write l v a | read l a | rmw l op =>
    cases l with | mk space idx => cases space <;> rfl
  | barrier i sems => rfl

private theorem map_getD {α β : Type} (xs : List α) (f : α → β) (i : Nat) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> rfl

@[simp] private theorem tagEvent_getD (groups g : Nat) (xs : List Ev) (i : Nat) :
    (xs.map (tagEvent groups g)).getD i (.barrier 0 []) =
      tagEvent groups g (xs.getD i (.barrier 0 [])) :=
  map_getD xs (tagEvent groups g) i (.barrier 0 [])

theorem tagShape_nodes (groups g : Nat) (P : Shape) :
    (tagShape groups g P).nodes = P.nodes.map (tagNode groups g) := by
  simp only [Shape.nodes, tagShape, Thread.nodes, List.flatMap_map, List.map_flatMap,
    List.length_map, List.map_map, Function.comp_def, tagEvent_getD, tagNode]

/-- Prefix offsets of an arbitrary finite collection of event lists. -/
def rowBase {α : Type} : List (List α) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | xs :: rest, i + 1 => xs.length + rowBase rest i

private theorem row_embed {α : Type} (rows : List (List α)) (g i : Nat)
    (hg : g < rows.length) (hi : i < (rows.getD g []).length) (fallback : α) :
    rowBase rows g + i < rows.flatten.length ∧
    rows.flatten.getD (rowBase rows g + i) fallback = (rows.getD g []).getD i fallback := by
  induction rows generalizing g with
  | nil => simp at hg
  | cons row rows ih =>
    cases g with
    | zero =>
      simp only [rowBase, List.getD_cons_zero, Nat.zero_add] at *
      constructor
      · simp only [List.flatten_cons, List.length_append]; omega
      · simp [List.flatten_cons, List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    | succ g =>
      simp only [List.getD_cons_succ, List.length_cons] at hg hi ⊢
      obtain ⟨hb, he⟩ := ih g (by omega) hi
      constructor
      · simp only [rowBase, List.flatten_cons, List.length_append]; omega
      · simp only [rowBase, List.flatten_cons, List.getD_eq_getElem?_getD,
          List.getElem?_append]
        rw [if_neg (by omega)]
        simpa only [Nat.add_assoc, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD] using he

private theorem row_origin {α : Type} (rows : List (List α)) (i : Nat)
    (hi : i < rows.flatten.length) :
    ∃ g j, g < rows.length ∧ j < (rows.getD g []).length ∧ i = rowBase rows g + j := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    by_cases hh : i < row.length
    · exact ⟨0, i, by simp, hh, by simp [rowBase]⟩
    · have hb : i - row.length < rows.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hi
        omega
      obtain ⟨g, j, hg, hj, he⟩ := ih (i-row.length) hb
      refine ⟨g+1, j, by simp; omega, ?_, ?_⟩
      · simpa using hj
      · simp only [rowBase]
        omega

def groupRows (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width : Nat) : List (List Node) :=
  (List.range d.groups).map fun g =>
    (Workgroup.sourceTrace p d (mem g) g width).nodes.map (tagNode d.groups g)

theorem dispatchTrace_nodes (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width : Nat) : (dispatchTrace p d mem width).nodes = (groupRows p d mem width).flatten := by
  change ((List.range d.groups).flatMap fun g =>
    (tagShape d.groups g (Workgroup.sourceTrace p d (mem g) g width)).threads).flatMap
      Thread.nodes = _
  rw [List.flatMap_assoc]
  change (List.range d.groups).flatMap (fun g =>
    (tagShape d.groups g (Workgroup.sourceTrace p d (mem g) g width)).nodes) = _
  simp only [tagShape_nodes, groupRows, List.flatMap_def]

theorem groupRows_get (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width g : Nat) (hg : g < d.groups) :
    (groupRows p d mem width).getD g [] =
      (Workgroup.sourceTrace p d (mem g) g width).nodes.map (tagNode d.groups g) := by
  simp [groupRows, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg]

def groupBase (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory) (width g : Nat) : Nat :=
  rowBase (groupRows p d mem width) g

theorem dispatch_embed (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width g i : Nat) (hg : g < d.groups)
    (hi : i < (Workgroup.sourceTrace p d (mem g) g width).nodes.length) :
    groupBase p d mem width g + i < (dispatchTrace p d mem width).nodes.length ∧
    (dispatchTrace p d mem width).nodes.getD (groupBase p d mem width g + i) default =
      tagNode d.groups g ((Workgroup.sourceTrace p d (mem g) g width).nodes.getD i default) := by
  have hrow := row_embed (groupRows p d mem width) g i
    (by simpa [groupRows] using hg) (by rw [groupRows_get p d mem width g hg]; simpa only [List.length_map] using hi)
    (default : Node)
  rw [groupRows_get p d mem width g hg] at hrow
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at hrow
  simpa only [groupBase, dispatchTrace_nodes, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using hrow

theorem dispatch_origin (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width i : Nat) (hi : i < (dispatchTrace p d mem width).nodes.length) :
    ∃ g j, g < d.groups ∧ j < (Workgroup.sourceTrace p d (mem g) g width).nodes.length ∧
      i = groupBase p d mem width g + j := by
  rw [dispatchTrace_nodes] at hi
  obtain ⟨g,j,hg,hj,he⟩ := row_origin (groupRows p d mem width) i hi
  have hgg : g < d.groups := by simpa [groupRows] using hg
  refine ⟨g,j,hgg,?_,he⟩
  rw [groupRows_get p d mem width g hgg] at hj
  simpa only [List.length_map] using hj

theorem tagLoc_injective (groups g : Nat) (hg : g < groups) (l m : Loc)
    (he : tagLoc groups g l = tagLoc groups g m) : l = m := by
  cases l with | mk ls li =>
    cases m with | mk ms mi =>
      cases ls <;> cases ms <;> simp only [tagLoc, Loc.mk.injEq, and_true, true_and] at he ⊢
      · exact he
      · cases he.1
      · cases he.1
      · exact (tag_injective groups g g li mi hg hg he).2

/-- Equal locations from distinct workgroups can only be shared device storage. -/
theorem tagLoc_cross (groups g h : Nat) (hg : g < groups) (hh : h < groups) (hne : g ≠ h)
    (l m : Loc) (he : tagLoc groups g l = tagLoc groups h m) :
    l.space = .storage ∧ m = l := by
  cases l with | mk ls li =>
    cases m with | mk ms mi =>
      cases ls <;> cases ms <;> simp only [tagLoc, Loc.mk.injEq, and_true, true_and] at he ⊢
      · exact he.symm
      · cases he.1
      · cases he.1
      · exact False.elim (hne (tag_injective groups g h li mi hg hh he).1)

/-- A memory event's source occurrence, independent of values and local register arithmetic. -/
def SourceAccess (p : Program) (d : Dispatch) (g : Nat) (loc : Loc) (writing : Bool) : Prop :=
  ∃ ph ∈ d.phases, ∃ lane, lane < ph.lanes ∧
    ((writing = false ∧ ∃ r ∈ ph.reads,
      loc = Workgroup.arrayLoc p.buffers r.array (r.index.eval g lane)) ∨
     (writing = true ∧ ∃ w ∈ ph.writes,
      loc = Workgroup.arrayLoc p.buffers w.array (w.index.eval g lane)))

private theorem lane_origin (p : Program) (ph : Phase) (m : ArrayKernel.Memory)
    (g lane : Nat) (e : Ev) (he : e ∈ Workgroup.sourceLaneEvents p.buffers ph m g lane)
    (loc : Loc) (hl : e.loc? = some loc) :
    (e.isWrite = false ∧ ∃ r ∈ ph.reads,
      loc = Workgroup.arrayLoc p.buffers r.array (r.index.eval g lane)) ∨
    (e.isWrite = true ∧ ∃ w ∈ ph.writes,
      loc = Workgroup.arrayLoc p.buffers w.array (w.index.eval g lane)) := by
  simp only [Workgroup.sourceLaneEvents, List.mem_append, List.mem_map, laneWrites] at he
  rcases he with ⟨r,hr,rfl⟩ | ⟨⟨a,i,v⟩,hw,rfl⟩
  · simp only [Ev.loc?, Option.some.injEq] at hl
    exact Or.inl ⟨rfl,r,hr,hl.symm⟩
  · obtain ⟨w,hw,heq⟩ := hw
    cases heq
    simp only [Ev.loc?, Option.some.injEq] at hl
    exact Or.inr ⟨rfl,w,hw,hl.symm⟩

private theorem thread_origin (p : Program) (ps : List Phase) (m : ArrayKernel.Memory)
    (g width lane inst : Nat) (e : Ev)
    (he : e ∈ Workgroup.tracePhases (Workgroup.sourcePhases p.buffers ps m g width) lane inst)
    (loc : Loc) (hl : e.loc? = some loc) :
    SourceAccess p {groups := 0, phases := ps} g loc e.isWrite := by
  induction ps generalizing m inst with
  | nil => simp [Workgroup.sourcePhases, Workgroup.tracePhases] at he
  | cons ph ps ih =>
    simp only [Workgroup.sourcePhases, Workgroup.tracePhases, List.mem_append,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with (hphase | (hbar | hbar)) | hrest
    · obtain ⟨logical,hlogical,hevent⟩ := List.mem_flatMap.mp hphase
      have hbound : logical < ph.lanes := List.mem_range.mp (List.mem_filter.mp hlogical).1
      exact ⟨ph,by simp,logical,hbound,lane_origin p ph m g logical e hevent loc hl⟩
    · subst e; simp [Ev.loc?] at hl
    · subst e; simp [Ev.loc?] at hl
    · obtain ⟨q,hq,l,hb,ho⟩ := ih _ _ hrest
      exact ⟨q,by simp only [List.mem_cons]; exact Or.inr hq,l,hb,ho⟩

/-- Every memory event in the concrete source trace has an admitted source read/write origin. -/
theorem source_origin (p : Program) (d : Dispatch) (m : ArrayKernel.Memory)
    (g width a : Nat) (ha : a < (Workgroup.sourceTrace p d m g width).nodes.length)
    (loc : Loc) (hl : ((Workgroup.sourceTrace p d m g width).nodes.getD a default).ev.loc? = some loc) :
    SourceAccess p d g loc ((Workgroup.sourceTrace p d m g width).nodes.getD a default).ev.isWrite := by
  have hn : (Workgroup.sourceTrace p d m g width).nodes.getD a default ∈
      (Workgroup.sourceTrace p d m g width).nodes := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
      using List.getElem_mem ha
  obtain ⟨t,ht,i,hi,hn⟩ := (by simpa only [Shape.nodes, Thread.nodes,
    List.mem_flatMap, List.mem_map] using hn :
      ∃ t ∈ (Workgroup.sourceTrace p d m g width).threads, ∃ i ∈ List.range t.prog.length,
      ({id := ⟨t.id,i⟩, wg:=t.wg, ev:=t.prog.getD i (.barrier 0 [])} : Node) =
        (Workgroup.sourceTrace p d m g width).nodes.getD a default)
  obtain ⟨lane,hlane,ht⟩ := List.mem_map.mp ht
  subst t
  have hib := List.mem_range.mp hi
  have hem : (Workgroup.tracePhases (Workgroup.sourcePhases p.buffers d.phases m g width) lane 0).getD
      i (.barrier 0 []) ∈ Workgroup.tracePhases (Workgroup.sourcePhases p.buffers d.phases m g width) lane 0 := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib, Option.getD_some]
      using List.getElem_mem hib
  have hev := congrArg Node.ev hn
  rw [← hev] at hl ⊢
  exact thread_origin p d.phases m g width lane 0 _ hem loc hl

private theorem mem_pairs {n a b : Nat} {f : Nat → Nat → Bool}
    (ha : a < n) (hb : b < n) (hf : f a b = true) : (a,b) ∈ pairs n f := by
  simp only [pairs, List.mem_flatMap, List.mem_range]
  refine ⟨a,ha,List.mem_filterMap.mpr ⟨b,List.mem_range.mpr hb,?_⟩⟩
  simp [hf]

private theorem mem_bound (P : Shape) (a : Nat) (h : a ∈ P.static.mems) :
    a < P.nodes.length := List.mem_range.mp (List.mem_filter.mp h).1

/-- Lift the actual three-edge workgroup barrier witness into the whole dispatch. No closure
embedding or sequential-consistency assumption is needed: G4 derives the same scoped path there. -/
theorem lift_phase_hb (p : Program) (d : Dispatch) (mem : Nat → ArrayKernel.Memory)
    (width g : Nat) (hg : g < d.groups) (c : Workgroup.PhaseLayout)
    (hc : c.geometry (Workgroup.sourceTrace p d (mem g) g width) = true)
    (a b : Nat)
    (ha : a ∈ (Workgroup.sourceTrace p d (mem g) g width).static.mems)
    (hb : b ∈ (Workgroup.sourceTrace p d (mem g) g width).static.mems)
    (hphase : c.phase a < c.phase b) (space : Space)
    (ham : ((Workgroup.sourceTrace p d (mem g) g width).nodes.getD a default).ev.inSpaces [space] = true)
    (hbm : ((Workgroup.sourceTrace p d (mem g) g width).nodes.getD b default).ev.inSpaces [space] = true) :
    (Obend.Hardware.Gpu.Memory.hb (dispatchTrace p d mem width).nodes).has
      (groupBase p d mem width g + a) (groupBase p d mem width g + b) = true := by
  let P := dispatchTrace p d mem width
  let Q := Workgroup.sourceTrace p d (mem g) g width
  let off := groupBase p d mem width g
  have hs : space ∈ [.storage,.workgroup] := by cases space <;> simp
  have hga := List.all_eq_true.mp (List.all_eq_true.mp hc a ha) space hs
  have hgb := List.all_eq_true.mp (List.all_eq_true.mp hc b hb) space hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hga hgb
  have hentry := Workgroup.boundary_facts Q c a (c.phase a) space false hga.1
  have hexit := Workgroup.boundary_facts Q c b (c.phase a) space true
    (hgb.2 _ (List.mem_range.mpr hphase))
  dsimp only at hentry hexit
  obtain ⟨he,hev,_,_,hat,hai⟩ := hentry
  obtain ⟨hl,hlv,_,_,hbt,hbi⟩ := hexit
  simp only [Bool.false_eq_true, ↓reduceIte] at hai hbi
  let ei := c.barrier (c.phase a) (Q.nodes.getD a default).id.t space
  let li := c.barrier (c.phase a) (Q.nodes.getD b default).id.t space
  obtain ⟨hag,hae⟩ := dispatch_embed p d mem width g a hg (mem_bound Q a ha)
  obtain ⟨hbg,hbe⟩ := dispatch_embed p d mem width g b hg (mem_bound Q b hb)
  obtain ⟨heg,hee⟩ := dispatch_embed p d mem width g ei hg he
  obtain ⟨hlg,hle⟩ := dispatch_embed p d mem width g li hg hl
  have hat' : (P.nodes.getD (off+a) default).id.t = (P.nodes.getD (off+ei) default).id.t := by
    simp only [P,off,hae,hee,tagNode]
    exact congrArg (tag d.groups g) hat
  have hbt' : (P.nodes.getD (off+li) default).id.t = (P.nodes.getD (off+b) default).id.t := by
    simp only [P,off,hle,hbe,tagNode]
    exact congrArg (tag d.groups g) hbt.symm
  have hai' : (P.nodes.getD (off+a) default).id.i < (P.nodes.getD (off+ei) default).id.i := by
    simpa only [P,off,hae,hee,tagNode] using hai
  have hbi' : (P.nodes.getD (off+li) default).id.i < (P.nodes.getD (off+b) default).id.i := by
    simpa only [P,off,hle,hbe,tagNode] using hbi
  by_cases hi : ei = li
  · have hpo : (po P.nodes).has (off+a) (off+b) = true := by
      apply List.contains_iff_mem.mpr
      apply mem_pairs hag hbg
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      rw [hi] at hat' hai'
      exact ⟨hat'.trans hbt',Nat.lt_trans hai' hbi'⟩
    exact Workgroup.ordered_hb P.nodes (off+a) (off+b)
      (by simp only [Workgroup.ordered,hpo,Bool.true_or])
  · apply Workgroup.barrier_orders P.nodes (off+a) (off+b) (off+ei) (off+li)
      (2*c.phase a + if space = .storage then 1 else 0) space hag hbg heg hlg (by omega)
    · simp only [P,off,hee,tagNode]
      rw [hev]
      rfl
    · simp only [P,off,hle,tagNode]
      rw [hlv]
      rfl
    · simp only [P,off,hee,hle,tagNode]
    · exact hat'
    · exact hai'
    · exact hbt'
    · exact hbi'
    · simpa only [P,off,hae,tagNode,tagEvent_spaces] using ham
    · simpa only [P,off,hbe,tagNode,tagEvent_spaces] using hbm

private theorem arrayLoc_space (p : Program) (a i : Nat) (ha : a < p.buffers.length) :
    (Workgroup.arrayLoc p.buffers a i).space =
      if (p.buffers.getD a default).storage == .shared then .workgroup else .storage := by
  simp [Workgroup.arrayLoc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]

private theorem write_is_device (p : Program) (hc : p.check = .ok ()) (d : Dispatch)
    (hd : d ∈ p.dispatches) (ph : Phase) (hph : ph ∈ d.phases) (w : Write) (hw : w ∈ ph.writes)
    (i : Nat) (ha : w.array < p.buffers.length)
    (hs : (Workgroup.arrayLoc p.buffers w.array i).space = .storage) :
    (p.buffers.getD w.array default).storage = .device := by
  have hn := p.check_noConstantWrite hc d hd ph hph w hw
  rw [arrayLoc_space p w.array i ha] at hs
  cases he : (p.buffers.getD w.array default).storage with
  | device => rfl
  | shared =>
      simp only [he, beq_self_eq_true, ↓reduceIte] at hs
      cases hs
  | constant => exact False.elim (hn he)

private theorem read_write_ne (p : Program) (hc : p.check = .ok ()) (d : Dispatch)
    (hd : d ∈ p.dispatches) (g h : Nat) (hg : g < d.groups) (hh : h < d.groups)
    (rp wp : Phase) (hrp : rp ∈ d.phases) (hwp : wp ∈ d.phases)
    (rl wl : Nat) (hrl : rl < rp.lanes) (hwl : wl < wp.lanes)
    (r : Read) (hr : r ∈ rp.reads) (w : Write) (hw : w ∈ wp.writes)
    (hs : (Workgroup.arrayLoc p.buffers w.array (w.index.eval h wl)).space = .storage) :
    Workgroup.arrayLoc p.buffers r.array (r.index.eval g rl) ≠
      Workgroup.arrayLoc p.buffers w.array (w.index.eval h wl) := by
  intro he
  have hbr := (BlockLower.boundsSafe_sound p (p.check_boundsSafe hc) d hd g hg rp hrp).1 rl hrl r hr
  have hbw := (BlockLower.boundsSafe_sound p (p.check_boundsSafe hc) d hd h hh wp hwp).2 wl hwl w hw
  have hcoords := SourceProtocol.arrayLoc_injective p r.array (r.index.eval g rl)
    w.array (w.index.eval h wl) hbr hbw he
  have hws := write_is_device p hc d hd wp hwp w hw _ hbw.1 hs
  have hrs : (p.buffers.getD r.array default).storage = .device := by rw [hcoords.1]; exact hws
  exact (p.check_deviceReadWrite_disjoint hc d hd rp hrp r hr hrs h hh wp hwp wl hwl w hw hws) hcoords.1

/-- Source admission rules out every conflicting storage access between distinct workgroups. -/
theorem sourceAccess_cross_disjoint (p : Program) (hc : p.check = .ok ()) (d : Dispatch)
    (hd : d ∈ p.dispatches) (g h : Nat) (hg : g < d.groups) (hh : h < d.groups) (hgh : g ≠ h)
    (l m : Loc) (wa wb : Bool) (ha : SourceAccess p d g l wa) (hb : SourceAccess p d h m wb)
    (hs : l.space = .storage) (hw : (wa || wb) = true) : l ≠ m := by
  intro he
  subst m
  obtain ⟨pa,hpa,la,hla,ha⟩ := ha
  obtain ⟨pb,hpb,lb,hlb,hb⟩ := hb
  rcases ha with ⟨hwa,r,hr,hlr⟩ | ⟨hwa,w,hw',hlw⟩
  · rcases hb with ⟨hwb,s,hs',hls⟩ | ⟨hwb,v,hv,hlv⟩
    · simp [hwa,hwb] at hw
    · exact read_write_ne p hc d hd g h hg hh pa pb hpa hpb la lb hla hlb r hr v hv
        (by rw [← hlv]; exact hs) (hlr.symm.trans hlv)
  · rcases hb with ⟨hwb,s,hs',hls⟩ | ⟨hwb,v,hv,hlv⟩
    · exact read_write_ne p hc d hd h g hh hg pb pa hpb hpa lb la hlb hla s hs' w hw'
        (by rw [← hlw]; exact hs) (hls.symm.trans hlw)
    · have hbw := (BlockLower.boundsSafe_sound p (p.check_boundsSafe hc) d hd g hg pa hpa).2 la hla w hw'
      have hbv := (BlockLower.boundsSafe_sound p (p.check_boundsSafe hc) d hd h hh pb hpb).2 lb hlb v hv
      have hcoords := SourceProtocol.arrayLoc_injective p w.array (w.index.eval g la)
        v.array (v.index.eval h lb) hbw hbv (hlw.symm.trans hlv)
      have hws := write_is_device p hc d hd pa hpa w hw' _ hbw.1 (by rw [← hlw]; exact hs)
      have hvs := write_is_device p hc d hd pb hpb v hv _ hbv.1 (by rw [← hlv]; exact hs)
      exact (p.check_deviceWrites_crossGroup hc d hd g h hg hh hgh pa pb hpa hpb la lb hla hlb
        w v hw' hv hws hvs) (by simp only [Prod.mk.injEq]; exact hcoords)


/-- Tags preserve the local address space. -/
@[simp] theorem tagLoc_space (groups g : Nat) (l : Loc) :
    (tagLoc groups g l).space = l.space := by
  cases l with | mk s i => cases s <;> rfl

private theorem sameLoc_origins (groups g h : Nat) (x y : Node)
    (he : (tagNode groups g x).sameLoc (tagNode groups h y) = true) :
    ∃ l m, x.ev.loc? = some l ∧ y.ev.loc? = some m ∧
      tagLoc groups g l = tagLoc groups h m := by
  simp only [Node.sameLoc, tagNode, tagEvent_loc] at he
  cases hx : x.ev.loc? with
  | none => simp only [hx, Option.map_none, Bool.false_eq_true] at he
  | some l =>
    cases hy : y.ev.loc? with
    | none => simp only [hy, Option.map_none, hx, Option.map_some, Bool.false_eq_true] at he
    | some m => exact ⟨l,m,rfl,rfl,by simpa only [hx,hy,Option.map_some,beq_iff_eq] using he⟩

private theorem local_mem (P : Shape) (i : Nat) (hi : i < P.nodes.length)
    (l : Loc) (hl : (P.nodes.getD i default).ev.loc? = some l) : i ∈ P.static.mems := by
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp only [hl, Option.isSome_some]⟩

/-- Source admission and the checked per-group barrier geometry compose to the actual whole
Vulkan dispatch race verdict. Shared locations are private to their workgroup; every potentially
conflicting device access belongs to one group by the source ownership check. -/
theorem checkProgram_not_racy (p : Program) (hc : p.check = .ok ()) (width : Nat)
    (hp : SourceProtocol.checkProgram p width = true)
    (d : Dispatch) (hd : d ∈ p.dispatches) (mem : Nat → ArrayKernel.Memory) :
    (dispatchTrace p d mem width).static.racy = false := by
  let P := dispatchTrace p d mem width
  apply Bool.eq_false_iff.mpr
  intro hr
  simp only [Static.racy, List.any_eq_true, Bool.and_eq_true] at hr
  obtain ⟨a,ha,b,hb,⟨⟨⟨⟨⟨hne,hloc⟩,hwrite⟩,_⟩,hnab⟩,hnba⟩⟩ := hr
  have hab : a < P.nodes.length := mem_bound P a ha
  have hbb : b < P.nodes.length := mem_bound P b hb
  obtain ⟨g,i,hg,hi,hai⟩ := dispatch_origin p d mem width a hab
  obtain ⟨h,j,hh,hj,hbj⟩ := dispatch_origin p d mem width b hbb
  have hea := (dispatch_embed p d mem width g i hg hi).2
  have heb := (dispatch_embed p d mem width h j hh hj).2
  let Q := Workgroup.sourceTrace p d (mem g) g width
  let R := Workgroup.sourceTrace p d (mem h) h width
  have heLoc : (tagNode d.groups g (Q.nodes.getD i default)).sameLoc
      (tagNode d.groups h (R.nodes.getD j default)) = true := by
    change (P.nodes.getD a default).sameLoc (P.nodes.getD b default) = true at hloc
    simpa only [P,hai,hbj,hea,heb] using hloc
  obtain ⟨l,m,hl,hm,he⟩ := sameLoc_origins d.groups g h _ _ heLoc
  have hw : ((Q.nodes.getD i default).ev.isWrite || (R.nodes.getD j default).ev.isWrite) = true := by
    change ((P.nodes.getD a default).ev.isWrite || (P.nodes.getD b default).ev.isWrite) = true at hwrite
    simpa only [P,hai,hbj,hea,heb,tagNode,tagEvent_write] using hwrite
  by_cases hgh : g = h
  · subst h
    change (Q.nodes.getD j default).ev.loc? = some m at hm
    change ((Q.nodes.getD i default).ev.isWrite || (Q.nodes.getD j default).ev.isWrite) = true at hw
    have hlm : l = m := tagLoc_injective d.groups g hg l m he
    subst m
    have hmi := local_mem Q i hi l hl
    have hmj := local_mem Q j hj l hm
    have heq : Q.static.sameLoc i j = true := by
      change (Q.nodes.getD i default).sameLoc (Q.nodes.getD j default) = true
      simp only [Node.sameLoc,hl,hm,beq_self_eq_true]
    have hij : i ≠ j := by
      intro hij
      have hab' : a = b := by rw [hai,hbj,hij]
      simp only [hab',bne_self_eq_false,Bool.false_eq_true] at hne
    let c := Workgroup.sourceProtocolLayout p d g width
    have hs := SourceProtocol.checkProgram_group p width hp d hd g hg
    have hgQ : c.geometry Q = true := by
      rw [← Workgroup.geometry_erase, Workgroup.sourceTrace_erase, ← Workgroup.geometryFast_eq]
      exact hs.1
    have hsQ : c.Separated Q := by
      apply (Workgroup.separated_erase Q c).mp
      rw [Workgroup.sourceTrace_erase]
      exact hs.2
    have hphase := hsQ i hmi j hmj hij heq hw
    have hsp_i : (Q.nodes.getD i default).ev.inSpaces [l.space] = true := by
      simp only [Ev.inSpaces,hl,List.contains_cons,beq_self_eq_true,Bool.true_or]
    have hsp_j : (Q.nodes.getD j default).ev.inSpaces [l.space] = true := by
      simp only [Ev.inSpaces,hm,List.contains_cons,beq_self_eq_true,Bool.true_or]
    have hloc' : (P.nodes.getD a default).sameLoc (P.nodes.getD b default) = true := hloc
    have hlocRev : (P.nodes.getD b default).sameLoc (P.nodes.getD a default) = true := by
      simp only [P,hai,hbj,hea,heb,Node.sameLoc,tagNode,tagEvent_loc]
      change (match (Q.nodes.getD j default).ev.loc?.map (tagLoc d.groups g),
        (Q.nodes.getD i default).ev.loc?.map (tagLoc d.groups g) with
        | some l, some m => l == m | _, _ => false) = true
      simp only [hl,hm,Option.map_some,beq_self_eq_true]
    rcases Nat.lt_or_gt_of_ne hphase with hlt | hgt
    · have hhb := lift_phase_hb p d mem width g hg c hgQ i j hmi hmj hlt l.space hsp_i hsp_j
      have hord : P.static.locord.has a b = true := by
        apply List.contains_iff_mem.mpr
        apply mem_pairs hab hbb
        simp only [Bool.and_eq_true]
        exact ⟨hloc',by simpa only [P,hai,hbj] using hhb⟩
      simp only [Bool.not_eq_true'] at hnab
      exact Bool.noConfusion (hnab.symm.trans hord)
    · have hhb := lift_phase_hb p d mem width g hg c hgQ j i hmj hmi hgt l.space hsp_j hsp_i
      have hord : P.static.locord.has b a = true := by
        apply List.contains_iff_mem.mpr
        apply mem_pairs hbb hab
        simp only [Bool.and_eq_true]
        exact ⟨hlocRev,by simpa only [P,hai,hbj] using hhb⟩
      simp only [Bool.not_eq_true'] at hnba
      exact Bool.noConfusion (hnba.symm.trans hord)
  · have hcLoc := tagLoc_cross d.groups g h hg hh hgh l m he
    have hsrc_i := source_origin p d (mem g) g width i hi l hl
    have hsrc_j := source_origin p d (mem h) h width j hj m hm
    exact sourceAccess_cross_disjoint p hc d hd g h hg hh hgh l m _ _ hsrc_i hsrc_j hcLoc.1 hw hcLoc.2.symm

end Obend.Hardware.Gpu.DispatchProtocol
