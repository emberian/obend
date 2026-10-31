module
/- Named poles for the Objective Bend families the hypothesis ledger reads.

`scripts/HypothesisLedger.lean` now imports the `ObjectiveProofs` modules (through
`Kernel.ObjectiveResumeContract`, whose resume contract `ForcingTransparent` is now proved at
every lexically valid yield), so it reads
four families it never saw before, each consumed and each TOOTHLESS: no named instance
showed it can hold AND can fail. These are those instances, one satisfying and one
refuting per family, over the real definitions. -/
public import Obend.Core.Proofs.Preservation
namespace Obend.Core.Proofs.LedgerPoles
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
open Obend.Core.Proofs.Adequacy (MeaningsScoped EvaluatingSegment)
open Obend.Core.MachineTyping (ConversionPath)
open Obend.Core.Ty (Ty)
open Obend.Core.Check (Assumptions)
set_option autoImplicit false

/-! ## `MeaningsScoped` -/

/-- No address is allocated below 0: any meaning is scoped there. -/
theorem meaningsScoped_unallocated : MeaningsScoped 0 (fun _ => .bound 0) :=
  fun _ below => absurd below (Nat.not_lt_zero _)

/-- An allocated address meaning an open term is not scoped. -/
theorem not_meaningsScoped_open : ¬ MeaningsScoped 1 (fun _ => .bound 0) := by
  intro allScoped
  have := allScoped 0 (by decide)
  simp at this

/-! ## `EvaluatingSegment` -/

@[expose] public def poleEntered : State := ⟨#[.suspended ⟨.nat 1, []⟩], .enter 0, []⟩

/-- Entering a suspended cell starts its evaluating segment. -/
theorem evaluatingSegment_started :
    EvaluatingSegment 0 ⟨.nat 1, []⟩ poleEntered (stepRaw poleEntered) :=
  .start rfl rfl

theorem evaluatingSegment_entry_cell {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) :
    entered.heap[address]? = some (.suspended origin) := by
  induction segment with
  | start _ found => exact found
  | next _ _ ih => exact ih

/-- No segment starts at an address the heap does not hold. -/
theorem not_evaluatingSegment_unallocated (state : State) :
    ¬ EvaluatingSegment 0 ⟨.nat 1, []⟩ ⟨#[], .enter 0, []⟩ state := by
  intro segment
  have := evaluatingSegment_entry_cell segment
  simp at this

/-! ## `ConversionPath` -/

theorem conversionPath_natural : ConversionPath ({} : Assumptions) .natural .natural := .refl _

/-- Conversion preserves the exposed constructor class, while recursively
related components may have different finite canonical syntax. -/
theorem conversionPath_head {assumptions : Assumptions} {first last : Ty}
    (path : ConversionPath assumptions first last) :
    Obend.Core.TypeGraph.labelHead ((Obend.Core.TypeGraph.graph assumptions).label (.type first)) =
      Obend.Core.TypeGraph.labelHead ((Obend.Core.TypeGraph.graph assumptions).label (.type last)) := by
  induction path with
  | refl => rfl
  | step _ agreement ih =>
    exact ih.trans (Obend.Core.TypeGraph.equivalent_head
      ((Obend.Core.Check.sameType_iff _ _ _).mp agreement))

/-- No conversion path turns a natural into a boolean. -/
theorem not_conversionPath_natural_boolean : ¬ ConversionPath ({} : Assumptions) .natural .boolean := by
  intro path
  have same := conversionPath_head path
  simp [Obend.Core.TypeGraph.labelHead, Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe,
    Obend.Core.AliasExposure.expose, Obend.Core.AliasExposure.exposeWalk,
    Obend.Core.AliasExposure.constructorHead, Obend.Core.TypeGraph.rowTag] at same

/-! ## `StepCases` -/

theorem stepCases_trivial : StepCases (fun _ => True) := by
  constructor <;> intros <;> trivial

theorem not_stepCases_false : ¬ StepCases (fun _ => False) :=
  fun cases => cases.complete ⟨#[], .complete (.natural 0), []⟩ (.natural 0) rfl

end Obend.Core.Proofs.LedgerPoles
