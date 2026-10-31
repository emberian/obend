module
public import Obend.Core.TypeGraph
@[expose] public section
namespace Obend.Core.RowSearch
set_option autoImplicit false

inductive Step (α β : Type) where
  | stop
  | emit (payload : β)
  | skip (next : α)

inductive Hit {α β : Type} (step : α → Step α β) : α → β → Nat → Prop where
  | emit (x : α) (p : β) (observed : step x = .emit p) : Hit step x p 0
  | skip (x y : α) (p : β) (n : Nat) (observed : step x = .skip y)
      (nested : Hit step y p n) : Hit step x p (n + 1)

theorem hit_unique {α β : Type} {step : α → Step α β} {x : α} {p q : β} {n m : Nat}
    (one : Hit step x p n) (two : Hit step x q m) : p = q ∧ n = m := by
  induction one generalizing q m with
  | emit x p observed =>
    cases two with
    | emit _ q observed' =>
      rw [observed] at observed'
      cases observed'
      exact ⟨rfl, rfl⟩
    | skip _ y q m observed' nested =>
      rw [observed] at observed'
      contradiction
  | skip x y p n observed nested ih =>
    cases two with
    | emit _ q observed' =>
      rw [observed] at observed'
      contradiction
    | skip _ y' q m observed' nested' =>
      rw [observed] at observed'
      cases observed'
      obtain ⟨same, distance⟩ := ih nested'
      exact ⟨same, congrArg (fun k => k + 1) distance⟩

def find {α β : Type} [DecidableEq α] (step : α → Step α β)
    (remaining : List α) (x : α) : Option β :=
  match step x with
  | .stop => none
  | .emit p => if x ∈ remaining then some p else none
  | .skip y => if present : x ∈ remaining then find step (remaining.erase x) y else none
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

theorem find_sound {α β : Type} [DecidableEq α] (step : α → Step α β)
    (remaining : List α) (x : α) (p : β) (found : find step remaining x = some p) :
    ∃ n, Hit step x p n := by
  cases observed : step x with
  | stop => rw [find, observed] at found; contradiction
  | emit payload =>
    rw [find, observed] at found
    simp only at found
    split at found
    · cases found
      exact ⟨0, .emit x p observed⟩
    · contradiction
  | skip y =>
    rw [find, observed] at found
    simp only at found
    split at found
    · rename_i present
      obtain ⟨n, nested⟩ := find_sound step (remaining.erase x) y p found
      exact ⟨n + 1, .skip x y p n observed nested⟩
    · contradiction
termination_by remaining.length
decreasing_by
  have present : x ∈ remaining := by assumption
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- The rank invariant is what permits a finite visited search to realize an
unbounded finite path. An already erased state has strictly greater distance;
determinism prevents it from also occurring on the shorter remaining path. -/
theorem find_complete {α β : Type} [DecidableEq α] (step : α → Step α β)
    (nodes remaining : List α)
    (closed : ∀ x y, x ∈ nodes → step x = .skip y → y ∈ nodes)
    {x : α} {p : β} {n : Nat} (hit : Hit step x p n) (root : x ∈ nodes)
    (covers : ∀ y q m, y ∈ nodes → Hit step y q m → m ≤ n → y ∈ remaining) :
    find step remaining x = some p := by
  cases hit with
  | emit x p observed =>
    have present := covers x p 0 root (.emit x p observed) (Nat.le_refl 0)
    rw [find, observed]
    simp only [present, ↓reduceIte]
  | skip x y p n observed nested =>
    have present := covers x p (n + 1) root (.skip x y p n observed nested) (Nat.le_refl _)
    rw [find, observed]
    simp only [present, ↓reduceDIte]
    apply find_complete step nodes (remaining.erase x) closed nested (closed x y root observed)
    intro z q m inside path smaller
    have different : z ≠ x := by
      intro same
      subst z
      have distance := (hit_unique (.skip x y p n observed nested) path).2
      omega
    exact (List.mem_erase_of_ne different).mpr
      (covers z q m inside path (by omega))
termination_by n

 theorem find_iff_hit {α β : Type} [DecidableEq α] (step : α → Step α β)
    (nodes : List α)
    (closed : ∀ x y, x ∈ nodes → step x = .skip y → y ∈ nodes)
    {x : α} {p : β} (root : x ∈ nodes) :
    find step nodes x = some p ↔ ∃ n, Hit step x p n := by
  constructor
  · exact find_sound step nodes x p
  · rintro ⟨n, hit⟩
    exact find_complete step nodes nodes closed hit root (fun _ _ _ inside _ _ => inside)

inductive SkipPath {α β : Type} (step : α → Step α β) : α → α → Prop where
  | refl (x : α) : SkipPath step x x
  | cons (x y z : α) (observed : step x = .skip y)
      (nested : SkipPath step y z) : SkipPath step x z

theorem hit_skip_iff {α β : Type} {step : α → Step α β} {x y : α} {p : β}
    (observed : step x = .skip y) :
    (∃ n, Hit step x p n) ↔ ∃ n, Hit step y p n := by
  constructor
  · rintro ⟨n, hit⟩
    cases hit with
    | emit _ _ other => rw [observed] at other; contradiction
    | skip _ z _ n other nested =>
      rw [observed] at other
      cases other
      exact ⟨n, nested⟩
  · rintro ⟨n, nested⟩
    exact ⟨n + 1, .skip x y p n observed nested⟩

theorem hit_path_iff {α β : Type} {step : α → Step α β} {x y : α} {p : β}
    (path : SkipPath step x y) :
    (∃ n, Hit step x p n) ↔ ∃ n, Hit step y p n := by
  induction path with
  | refl _ => exact Iff.rfl
  | cons _ _ _ observed _ ih => exact (hit_skip_iff observed).trans ih

theorem find_path_eq {α β : Type} [DecidableEq α] {step : α → Step α β}
    (left right : List α)
    (leftClosed : ∀ x y, x ∈ left → step x = .skip y → y ∈ left)
    (rightClosed : ∀ x y, x ∈ right → step x = .skip y → y ∈ right)
    {x y : α} (hx : x ∈ left) (hy : y ∈ right) (path : SkipPath step x y) :
    find step left x = find step right y := by
  have same (p : β) : find step left x = some p ↔ find step right y = some p :=
    (find_iff_hit step left leftClosed hx).trans
      ((hit_path_iff path).trans (find_iff_hit step right rightClosed hy).symm)
  cases one : find step left x with
  | none =>
    cases two : find step right y with
    | none => rfl
    | some p => have impossible := (same p).mpr two; rw [one] at impossible; contradiction
  | some p => exact ((same p).mp one).symm

/-- Equal deterministic observations transport a finite hit without traversing
its continuation: the continuation state itself is already shared. -/
theorem hit_of_step_eq {α β : Type} {step : α → Step α β}
    {x y : α} {p : β} {n : Nat} (same : step x = step y)
    (hit : Hit step x p n) : Hit step y p n := by
  cases hit with
  | emit _ _ observed => exact .emit y p (same.symm.trans observed)
  | skip _ next _ n observed nested =>
    exact .skip y next p n (same.symm.trans observed) nested

 theorem find_step_eq {α β : Type} [DecidableEq α] {step : α → Step α β}
    (left right : List α)
    (leftClosed : ∀ x y, x ∈ left → step x = .skip y → y ∈ left)
    (rightClosed : ∀ x y, x ∈ right → step x = .skip y → y ∈ right)
    {x y : α} (hx : x ∈ left) (hy : y ∈ right) (heads : step x = step y) :
    find step left x = find step right y := by
  have hits (p : β) : (∃ n, Hit step x p n) ↔ ∃ n, Hit step y p n := by
    constructor
    · rintro ⟨n, hit⟩
      exact ⟨n, hit_of_step_eq heads hit⟩
    · rintro ⟨n, hit⟩
      exact ⟨n, hit_of_step_eq heads.symm hit⟩
  have same (p : β) : find step left x = some p ↔ find step right y = some p :=
    (find_iff_hit step left leftClosed hx).trans
      ((hits p).trans (find_iff_hit step right rightClosed hy).symm)
  cases one : find step left x with
  | none =>
    cases two : find step right y with
    | none => rfl
    | some p => have impossible := (same p).mpr two; rw [one] at impossible; contradiction
  | some p => exact ((same p).mp one).symm

end Obend.Core.RowSearch

namespace Obend.Core.TypeGraph.RowHit
open Obend.Core.Ty Obend.Core.Check Obend.Core.AliasExposure
namespace Search
export Obend.Core.RowSearch (Step Hit SkipPath find find_sound find_iff_hit find_path_eq)
end Search
set_option autoImplicit false

def step (a : Assumptions) (label : String) (first : Bool) (row : Ty) :
    Search.Step Ty (Ty × Ty) :=
  match expose a row with
  | .constructor observation =>
    match observation.tag, observation.children with
    | .field name, [member, tail] =>
      if name == label && (first || !RR.shareable a member) then .emit (member, tail)
      else .skip tail
    | _, _ => .stop
  | _ => .stop

def emission : RR.StreamStep → Option (Ty × Ty)
  | .end _ => none
  | .emit member tail => some (member, tail)

 theorem scan_projection (a : Assumptions) (remaining : List Ty)
    (label : String) (first : Bool) (row : Ty) :
    emission (Obend.Core.RecursiveRows.scanStream a remaining label first row) =
      Search.find (step a label first) remaining row := by
  rw [Obend.Core.RecursiveRows.scanStream]
  split
  · rename_i index exposed
    rw [Search.find, step, exposed]
    rfl
  · rename_i index exposed
    rw [Search.find, step, exposed]
    rfl
  · rename_i observation exposed
    split
    · rw [Search.find, step, exposed]
      simp_all [emission]
    · rename_i name member tail tag children
      have shape : observation = ⟨.field name, [member, tail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      rw [Search.find, step, exposed]
      by_cases present : row ∈ remaining
      · by_cases matched : (name == label && (first || !RR.shareable a member)) = true
        · simp only [present, matched, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, emission]
        · simp only [present, matched, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
          exact scan_projection a (remaining.erase row) label first tail
      · by_cases matched : (name == label && (first || !RR.shareable a member)) = true
        · simp only [present, matched, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, emission]
        · simp only [present, matched, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, emission]
    · rw [Search.find, step, exposed]
      simp_all [emission]
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

 theorem step_skip_support (a : Assumptions) (left right row tail : Ty)
    (label : String) (first : Bool) (present : row ∈ support a left right)
    (skipped : step a label first row = .skip tail) : tail ∈ support a left right := by
  rw [step] at skipped
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at skipped
      · contradiction
      · have same : fieldTail = tail := Obend.Core.RowSearch.Step.skip.inj skipped
        rw [← same]
        exact expose_children_support present exposed fieldTail (by simp)
    · contradiction
  · contradiction

 theorem step_emit_support (a : Assumptions) (left right row member tail : Ty)
    (label : String) (first : Bool) (present : row ∈ support a left right)
    (emitted : step a label first row = .emit (member, tail)) :
    member ∈ support a left right ∧ tail ∈ support a left right := by
  rw [step] at emitted
  split at emitted
  · rename_i observation exposed
    split at emitted
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name, [fieldMember, fieldTail]⟩ := by
        cases observation
        simp_all
      rw [shape] at exposed
      split at emitted
      · have same : (fieldMember, fieldTail) = (member, tail) :=
          Obend.Core.RowSearch.Step.emit.inj emitted
        have sameMember : fieldMember = member := congrArg Prod.fst same
        have sameTail : fieldTail = tail := congrArg Prod.snd same
        rw [← sameMember, ← sameTail]
        exact ⟨expose_children_support present exposed fieldMember (by simp),
          expose_children_support present exposed fieldTail (by simp)⟩
      · contradiction
    · contradiction
  · contradiction

/-- A true-mode skip is nonmatching, hence also a false-mode skip. -/
 theorem true_skip_false (a : Assumptions) (label : String) (row tail : Ty)
    (skipped : step a label true row = .skip tail) : step a label false row = .skip tail := by
  rw [step] at skipped ⊢
  split at skipped
  · rename_i observation exposed
    split at skipped
    · rename_i name member fieldTail tag children
      have shape : observation = ⟨.field name, [member, fieldTail]⟩ := by
        cases observation
        simp_all
      split at skipped
      · contradiction
      · rename_i different
        have different' : (name == label) = false := by simpa using different
        have same : fieldTail = tail := Obend.Core.RowSearch.Step.skip.inj skipped
        simp only [different', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact congrArg Obend.Core.RowSearch.Step.skip same
    · simp_all
  · simp_all

/-- A shareable true-mode emission becomes exactly one false-mode skip. -/
 theorem true_emit_false_skip (a : Assumptions) (label : String) (row member tail : Ty)
    (shareable : RR.shareable a member = true)
    (emitted : step a label true row = .emit (member, tail)) :
    step a label false row = .skip tail := by
  rw [step] at emitted ⊢
  split at emitted
  · rename_i observation exposed
    split at emitted
    · rename_i name fieldMember fieldTail tag children
      have shape : observation = ⟨.field name, [fieldMember, fieldTail]⟩ := by
        cases observation
        simp_all
      split at emitted
      · have same : (fieldMember, fieldTail) = (member, tail) :=
          Obend.Core.RowSearch.Step.emit.inj emitted
        have sameMember : fieldMember = member := congrArg Prod.fst same
        have sameTail : fieldTail = tail := congrArg Prod.snd same
        rw [sameMember, sameTail]
        simp only [shareable, Bool.not_true, Bool.false_or, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
      · contradiction
    · simp_all
  · simp_all

 theorem shareable_hit_path_aux (a : Assumptions) (label : String)
    {row : Ty} {payload : Ty × Ty} {n : Nat}
    (hit : Search.Hit (step a label true) row payload n)
    (shareable : RR.shareable a payload.1 = true) :
    Search.SkipPath (step a label false) row payload.2 := by
  revert shareable
  induction hit with
  | emit row payload observed =>
    intro shareable
    cases payload with
    | mk member tail =>
      exact .cons row tail tail
        (true_emit_false_skip a label row member tail shareable observed) (.refl tail)
  | skip row next payload n observed nested ih =>
    intro shareable
    exact .cons row next payload.2 (true_skip_false a label row next observed) (ih shareable)

 theorem shareable_hit_path (a : Assumptions) (label : String)
    {row member tail : Ty} {n : Nat}
    (hit : Search.Hit (step a label true) row (member, tail) n)
    (shareable : RR.shareable a member = true) :
    Search.SkipPath (step a label false) row tail :=
  shareable_hit_path_aux a label hit shareable

/-- Resetting the finite epsilon budget after hiding a shareable visible member
preserves every possible emission. Infinite skip cycles yield `none` on both
sides; recurring resourceful emissions are retained as subsequent graph states. -/
 theorem shareable_reset (a : Assumptions) (label : String) (row member tail : Ty)
    (emitted : RR.streamStep a row label true = .emit member tail)
    (shareable : RR.shareable a member = true) :
    emission (RR.streamStep a row label false) = emission (RR.streamStep a tail label false) := by
  have projected : Search.find (step a label true) (support a row row) row = some (member, tail) := by
    rw [← scan_projection]
    exact congrArg emission emitted
  obtain ⟨n, hit⟩ := Search.find_sound _ _ _ _ projected
  have path := shareable_hit_path a label hit shareable
  have same := Search.find_path_eq (support a row row) (support a tail tail)
    (fun x y present skipped => step_skip_support a row row x y label false present skipped)
    (fun x y present skipped => step_skip_support a tail tail x y label false present skipped)
    (left_mem_support a row row) (left_mem_support a tail tail) path
  simpa only [RR.streamStep, scan_projection] using same

 theorem hide_emit_shareable (a : Assumptions) (label : String) (row member tail : Ty)
    (emitted : RR.streamStep a row label true = .emit member tail)
    (shareable : RR.shareable a member = true) :
    FP.Bisimilar (graph a) (.stream row label false) (.stream tail label false) := by
  have same := shareable_reset a label row member tail emitted shareable
  have observations : observe a (.stream row label false) = observe a (.stream tail label false) := by
    cases one : RR.streamStep a row label false <;>
      cases two : RR.streamStep a tail label false <;>
      simp_all [emission, observe]
  apply Obend.Core.FinitePresentation.bisimilar_of_children
  · exact congrArg Prod.fst observations
  · rw [show (graph a).successors (.stream row label false) =
        (graph a).successors (.stream tail label false) from congrArg Prod.snd observations]
    exact Obend.Core.FiniteBisimulation.children_mono
      (fun x y equal => by subst y; exact (FP.bisimilar_equivalence (graph a)).refl x)
      (Obend.Core.FiniteBisimulation.children_refl _)

 theorem stream_emission_expose_eq (a : Assumptions) (label : String) (first : Bool)
    (left right : Ty) (heads : expose a left = expose a right) :
    emission (RR.streamStep a left label first) =
      emission (RR.streamStep a right label first) := by
  have observed : step a label first left = step a label first right := by
    unfold step
    rw [heads]
  have same := Obend.Core.RowSearch.find_step_eq (support a left left) (support a right right)
    (fun x y present skipped => step_skip_support a left left x y label first present skipped)
    (fun x y present skipped => step_skip_support a right right x y label first present skipped)
    (left_mem_support a left left) (left_mem_support a right right) observed
  simpa only [RR.streamStep, scan_projection] using same

 theorem stream_observe_expose_eq (a : Assumptions) (label : String) (first : Bool)
    (left right : Ty) (heads : expose a left = expose a right) :
    observe a (.stream left label first) = observe a (.stream right label first) := by
  have same := stream_emission_expose_eq a label first left right heads
  cases one : RR.streamStep a left label first <;>
    cases two : RR.streamStep a right label first <;>
    simp_all [emission, observe]

/-- A skipped prefix may reset its epsilon budget without changing the graph
observation, for either visible or hidden stream mode. -/
 theorem stream_skip_observe_eq (a : Assumptions) (label : String) (first : Bool)
    (row tail : Ty) (skipped : step a label first row = .skip tail) :
    observe a (.stream row label first) = observe a (.stream tail label first) := by
  have path : Search.SkipPath (step a label first) row tail :=
    .cons row tail tail skipped (.refl tail)
  have found := Search.find_path_eq (support a row row) (support a tail tail)
    (fun x y present skipped => step_skip_support a row row x y label first present skipped)
    (fun x y present skipped => step_skip_support a tail tail x y label first present skipped)
    (left_mem_support a row row) (left_mem_support a tail tail) path
  have same : emission (RR.streamStep a row label first) =
      emission (RR.streamStep a tail label first) := by
    simpa only [RR.streamStep, scan_projection] using found
  cases one : RR.streamStep a row label first <;>
    cases two : RR.streamStep a tail label first <;>
    simp_all [emission, observe]

/-- A direct emitting step is always available in its complete support. -/
 theorem stream_emit_observe_eq (a : Assumptions) (label : String) (first : Bool)
    (row member tail : Ty) (emitted : step a label first row = .emit (member, tail)) :
    observe a (.stream row label first) =
      (.streamEmit, [.type member, .stream tail label false]) := by
  have projected : emission (RR.streamStep a row label first) = some (member, tail) := by
    change emission (Obend.Core.RecursiveRows.scanStream a (support a row row) label first row) = _
    rw [scan_projection, Search.find, emitted]
    simp only [left_mem_support, ↓reduceIte]
  cases returned : RR.streamStep a row label first <;>
    simp_all [emission, observe]

end Obend.Core.TypeGraph.RowHit
