module
public import Obend.Core.RecursiveAgreement
@[expose] public section
namespace Obend.Core.FiniteBisimulation
set_option autoImplicit false

/-- Boolean reflection commutes with proof transport. This equation lets the
simplifier evaluate the worklist without inspecting its semantic evidence. -/
theorem decide_transport {P Q : Prop} (d : Decidable P) (h : P ↔ Q) :
    @decide Q (@decidable_of_iff Q P h d) = @decide P d := by
  cases d <;> rfl

/-- An explicit Boolean view of the existing proved visited decision. -/
def worklistBool {Label : Type} [DecidableEq Label] {n : Nat} (g : Graph Label n)
    (visited pending : List (Pair n)) (distinct : visited.Nodup)
    (valid : VisitedInvariant g visited pending) : Bool :=
  @decide (Covered g (visited ++ pending)) (worklist g visited pending distinct valid)

@[simp] theorem worklistBool_nil {Label : Type} [DecidableEq Label] {n : Nat}
    (g : Graph Label n) (visited : List (Pair n)) (distinct : visited.Nodup)
    (valid : VisitedInvariant g visited []) :
    worklistBool g visited [] distinct valid = true := by
  unfold worklistBool
  rw [worklist]
  rfl

/-- Boolean step equation justified by the same visited invariants as the
worklist. Rewriting it does not evaluate the opaque accessibility witness. -/
theorem worklistBool_cons {Label : Type} [DecidableEq Label] {n : Nat}
    (g : Graph Label n) (visited : List (Pair n)) (p : Pair n)
    (pending : List (Pair n)) (distinct : visited.Nodup)
    (valid : VisitedInvariant g visited (p :: pending)) :
    worklistBool g visited (p :: pending) distinct valid =
      if seen : p ∈ visited then
        worklistBool g visited pending distinct (visited_skip valid seen)
      else if compatible : g.label p.1 = g.label p.2 ∧
          (g.successors p.1).length = (g.successors p.2).length then
        worklistBool g (p :: visited)
          ((g.successors p.1).zip (g.successors p.2) ++ pending)
          (List.nodup_cons.mpr ⟨seen,distinct⟩)
          (visited_advance valid compatible.1 compatible.2)
      else false := by
  split
  · rename_i seen
    apply Obend.Core.FiniteSafety.bool_ext
    simpa only [worklistBool, decide_eq_true_eq] using
      covered_skip g visited p pending seen
  · rename_i unseen
    split
    · apply Obend.Core.FiniteSafety.bool_ext
      simpa only [worklistBool, decide_eq_true_eq] using
        covered_advance g visited p pending
    · rename_i incompatible
      apply Obend.Core.FiniteSafety.bool_ext
      simp only [worklistBool, decide_eq_true_eq, Bool.false_eq_true]
      constructor
      · rintro ⟨R,closed,contains⟩
        obtain ⟨labels,children⟩ := closed _ _ (contains p (by simp))
        exact incompatible ⟨labels,((children_iff_zip _ _).mp children).1⟩
      · intro impossible
        exact False.elim impossible

theorem visitedSame_eq_worklistBool {Label : Type} [DecidableEq Label] {n : Nat}
    (g : Graph Label n) (x y : Fin n) :
    visitedSame g x y = worklistBool g [] [(x,y)] (by simp)
      (by intro p hp; simp at hp) := rfl

namespace ReductionProbes
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- These proofs exercise equation reduction, not semantic bisimulation proofs,
-- VM evaluation, or native_decide.
theorem cycle : visitedSame Probes.differentPeriods 0 1 = true := by
  simp [visitedSame_eq_worklistBool,worklistBool_cons,Probes.differentPeriods]

theorem mismatch : visitedSame Probes.reachableMismatch 0 1 = false := by
  simp [visitedSame_eq_worklistBool,worklistBool_cons,Probes.reachableMismatch] <;> decide

end ReductionProbes
end Obend.Core.FiniteBisimulation

namespace Obend.Core.FinitePresentation.ClosedSupport
set_option autoImplicit false

/-- Keep the presentation symbolic during evaluation. Decoding an index cancels
without enumerating support; visited equality likewise compares source nodes. -/
@[simp] theorem index_eq_iff {α Label : Type} [DecidableEq α]
    {g : Obend.Core.FinitePresentation.Graph α Label}
    (P : Obend.Core.FinitePresentation.ClosedSupport g)
    (x y : α) (hx : x ∈ P.nodes) (hy : y ∈ P.nodes) :
    P.index x hx = P.index y hy ↔ x = y := by
  constructor
  · intro equal
    have decoded := congrArg P.decode equal
    simpa only [decode_index] using decoded
  · intro equal
    subst y
    rfl

/-- First abstract the decoded source independently of its finite index. This
allows substitution through the dependent attach/map without rewriting casts. -/
theorem successors_of_decode {α Label : Type} [DecidableEq α]
    {g : Obend.Core.FinitePresentation.Graph α Label}
    (P : Obend.Core.FinitePresentation.ClosedSupport g)
    (i : Fin P.nodes.length) (x : α) (hx : x ∈ P.nodes)
    (equal : P.decode i = x) :
    P.finiteGraph.successors i =
      (g.successors x).attach.map
        (fun child => P.index child.val (P.closed x hx child.val child.property)) := by
  subst x
  rfl

/-- Expose just the reached successor list, keeping the graph and support
symbolic in the recursive worklist argument. -/
theorem successors_index {α Label : Type} [DecidableEq α]
    {g : Obend.Core.FinitePresentation.Graph α Label}
    (P : Obend.Core.FinitePresentation.ClosedSupport g)
    (x : α) (hx : x ∈ P.nodes) :
    P.finiteGraph.successors (P.index x hx) =
      (g.successors x).attach.map
        (fun child => P.index child.val (P.closed x hx child.val child.property)) :=
  successors_of_decode P (P.index x hx) x hx (decode_index P x hx)

/-- A fixed membership predicate makes source-list simplification independent
of the mapping function's type. The attach/map implementation is unchanged. -/
theorem successors_index_pmap {α Label : Type} [DecidableEq α]
    {g : Obend.Core.FinitePresentation.Graph α Label}
    (P : Obend.Core.FinitePresentation.ClosedSupport g)
    (x : α) (hx : x ∈ P.nodes) :
    P.finiteGraph.successors (P.index x hx) =
      (g.successors x).pmap (fun child member => P.index child member)
        (fun child member => P.closed x hx child member) := by
  rw [successors_index, List.pmap_eq_map_attach]

end Obend.Core.FinitePresentation.ClosedSupport

namespace Obend.Core.DecisionReduction
open Obend.Core
open Obend.Core.FiniteBisimulation
open Obend.Core.FinitePresentation.ClosedSupport
open Obend.Core.AliasExposure

/-! Field equations for the observation graphs. The reduction below rewrites a graph's `label` and
`successors` by these and never unfolds the graph itself: `TypeGraph.graph`, `ResourceSemantics.graph`
and `FiniteSafety.mirror` also occur as the index of the closed supports (`ClosedSupport (graph _)`)
whose `finiteGraph`, `index` and membership proofs the worklist carries, and unfolding them there
leaves terms that agree only at `.default` transparency. -/

@[simp] theorem typeGraph_label (assumptions : Check.Assumptions) (node : TypeGraph.Node) :
    (TypeGraph.graph assumptions).label node = (TypeGraph.observe assumptions node).1 := rfl

@[simp] theorem typeGraph_successors (assumptions : Check.Assumptions) (node : TypeGraph.Node) :
    (TypeGraph.graph assumptions).successors node = (TypeGraph.observe assumptions node).2 := rfl

@[simp] theorem resourceGraph_label (assumptions : Check.Assumptions) (t : Ty.Ty) :
    (ResourceSemantics.graph assumptions).label t = (ResourceSemantics.head assumptions t).1 := rfl

@[simp] theorem resourceGraph_successors (assumptions : Check.Assumptions) (t : Ty.Ty) :
    (ResourceSemantics.graph assumptions).successors t = (ResourceSemantics.head assumptions t).2 := rfl

@[simp] theorem mirror_label {α : Type} (g : FinitePresentation.Graph α Bool) (node : α × Bool) :
    (FiniteSafety.mirror g).label node = if node.2 then true else g.label node.1 := rfl

@[simp] theorem mirror_successors {α : Type} (g : FinitePresentation.Graph α Bool) (node : α × Bool) :
    (FiniteSafety.mirror g).successors node = (g.successors node.1).map (fun child => (child, node.2)) := rfl

/-- Kernel-checked computation for closed graph queries. Supply the local
constants defining the environment and roots. All recursion goes through
proved equations; the visited worklist and its termination proof are unchanged.
The graphs, the supports (`support`, `subterms`, the node lists) and the presentations are never
unfolded: they stay in the closed-support indices as written, and only the field equations above
and the index lemmas (`finite_label`, `successors_index_pmap`, `decode_index`, `index_eq_iff`)
touch them.

Example: `unfold environment actual expected; equirec_reduce`.
-/
-- Proof reduction uses the exact graph equation even when the executable
-- wrapper first tries a sound historical comparison. This keeps its kernel
-- normalization independent of runtime shortcuts and legacy sorting guards.
macro "equirec_reduce" : tactic =>
  `(tactic| simp [ Check.sameType, EquiRecursiveAgreement.agrees_eq_candidate,
    TypeGraph.candidate,
    typeGraph_label, typeGraph_successors, TypeGraph.observe, TypeGraph.rowObservation,
    TypeGraph.rowChildren, TypeGraph.rowTag, TypeGraph.tailKind, TypeGraph.tailChildren,
    agreement, finite_label, successors_index_pmap, decode_index, index_eq_iff,
    visitedSame_eq_worklistBool, worklistBool_cons,
    RecursiveRows.labels, RecursiveRows.scanLabels, RecursiveRows.insertLabel,
    RecursiveRows.residual, RecursiveRows.scanResidual,
    RecursiveRows.streamStep, RecursiveRows.scanStream, RecursiveRows.fieldLabels,
    RecursiveRows.shareable, ResourceSemantics.shareable,
    resourceGraph_label, resourceGraph_successors, ResourceSemantics.head,
    FiniteSafety.decision,
    mirror_label, mirror_successors,
    expose, exposeWalk, constructorHead, cycleRepresentative, support, subterms,
    Obend.Core.Check.Assumptions.alias, Obend.Core.Ty.Ty.isComputation, List.lookup, Fin.ofNat])
end Obend.Core.DecisionReduction

namespace Obend.Core.DecisionReduction.Probes
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Obend.Core

theorem atomic_mismatch :
    TypeGraph.candidate ⟨[],[],[]⟩ .natural .boolean = false := by
  equirec_reduce

theorem redundant_shadow :
    TypeGraph.candidate ⟨[],[],[]⟩
      (.field "a" .natural (.field "a" .natural .emptyRow))
      (.field "a" .natural .emptyRow) = true := by
  equirec_reduce

theorem checker_atomic_mismatch :
    Check.sameType ⟨[],[],[]⟩ .natural .boolean = false := by
  equirec_reduce

end Obend.Core.DecisionReduction.Probes

