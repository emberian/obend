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

/-- Kernel-checked computation for closed graph queries. Supply the local
constants defining the environment and roots. All recursion goes through
proved equations; the visited worklist and its termination proof are unchanged.

Example: `unfold environment actual expected; equirec_reduce`.
-/
-- The simp set unfolds definitions that also occur as implicit indices (`ClosedSupport (graph _)`,
-- membership proofs over `support`), so a partly-unfolded goal is coherent only up to `.default`
-- transparency. Lean v4.35 checks implicit arguments at `.implicit`
-- (`backward.isDefEq.respectTransparency`); this tactic keeps the v4.30 check for its own simp
-- call. Kernel checking of the result is unaffected.
-- Proof reduction uses the exact graph equation even when the executable
-- wrapper first tries a sound historical comparison. This keeps its kernel
-- normalization independent of runtime shortcuts and legacy sorting guards.
macro "equirec_reduce" : tactic =>
  `(tactic| set_option backward.isDefEq.respectTransparency false in simp [ Check.sameType, EquiRecursiveAgreement.agrees_eq_candidate,
    TypeGraph.candidate,
    TypeGraph.graph, TypeGraph.observe, TypeGraph.rowObservation,
    TypeGraph.rowChildren, TypeGraph.rowTag, TypeGraph.tailKind, TypeGraph.tailChildren,
    agreement, finite_label, successors_index_pmap, decode_index, index_eq_iff,
    visitedSame_eq_worklistBool, worklistBool_cons,
    RecursiveRows.labels, RecursiveRows.scanLabels, RecursiveRows.insertLabel,
    RecursiveRows.residual, RecursiveRows.scanResidual,
    RecursiveRows.streamStep, RecursiveRows.scanStream, RecursiveRows.fieldLabels,
    RecursiveRows.shareable, ResourceSemantics.shareable,
    ResourceSemantics.graph, ResourceSemantics.head,
    FiniteSafety.decision,
    FiniteSafety.mirror,
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
