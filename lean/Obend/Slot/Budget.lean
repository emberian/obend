module
public import Obend.Slot.Core4
public import Obend.Slot.Integrity
public import Obend.Slot.Selection
public import Obend.Slot.SupportSheaf
public import Obend.Intention
public import Obend.Kind
public import Obend.Equiv.Ahead
public import Obend.Equiv.Behaviour
public import Obend.Equiv.Cost

public section
namespace Obend.Slot
open Obend.Core.Check Obend.Core.Ty
open Obend.Core.Proofs.Substitution

/-- The toy World declares the grant available at a view. Retirement and typing
remain their existing meanings; this grant prices one checker invocation in
`Obend.Elab.Work.checkWork` units: the filling's two nodes plus the two types of the
annotation the checker reads at its lambda cost four. -/
def toyBudget (view : Nat) : Core4.Budget := ⟨if view = 0 then 1 else 1 + 3⟩

def budgetType : Ty := .arrow .reusable .unrestricted .natural .natural

def budgetSlot (view : Nat) : Slot Member AnnotatedTerm :=
  Core4.slotOf (toyBudget view) fuelContext budgetType (fun _ => [.bob])

section BudgetFixtures
attribute [local irreducible] Obend.Core.Check.sameType
  Obend.Core.EquiRecursiveAgreement.agrees Obend.Core.TypeGraph.candidate
attribute [local congr] Obend.Tactic.MonadicReduction.except_bind_source_congr
  Obend.Tactic.MonadicReduction.except_map_source_congr
attribute [local simp ↓] Obend.Tactic.MonadicReduction.except_monad_bind
  Obend.Tactic.MonadicReduction.except_functor_map
attribute [local simp] Obend.Tactic.MonadicReduction.except_bind_ok
  Obend.Tactic.MonadicReduction.except_bind_error
  Obend.Tactic.MonadicReduction.except_map_ok
  Obend.Tactic.MonadicReduction.except_map_error

/-- The four-unit grant admits the filling through the single bidirectional judge. -/
theorem budget_filling_admitted : Core4.judge 4 fuelContext fuelFilling budgetType = true := by
  simp [Core4.judge, Core4.checkWork, Obend.Elab.Work.checkWork, Obend.Elab.Work.termWork,
    Obend.Elab.Work.annotationWork, Obend.Elab.Work.tyNodes, fuelContext, fuelFilling, budgetType,
    Obend.Core.Bidirectional.checkAgainst, Obend.Core.Bidirectional.checkAt,
    Obend.Core.Bidirectional.elaborate, Obend.Core.Bidirectional.finish,
    Obend.Core.Bidirectional.checkedSynth, Obend.Core.Bidirectional.need,
    sameType_refl, safeUses, safeQuantity, Quantity.fits, linearFree, validContext, reusableAllowed,
    reusableCaptures, zeroUses, variableUses, addUses, Ty.shareableUnder,
    Ty.shareable, Ty.isComputation, Assumptions.valid,
    List.range_succ, List.zipWith, List.getElem?_cons_zero,
    Except.toBool, pure, Except.pure]

/-- The same filling has live supports at both views. The short grant refuses
by name; the combined grant makes it usable. This is a budget tooth, not a
counterexample to semantic substitution. -/
theorem budget_tooth :
    (budgetSlot 1).usable (World.holdsAt 1) fuelFilling = true ∧
    (match Core4.admit (toyBudget 0) fuelContext budgetType fuelFilling with
      | .error (.uncovered r) => r == 1
      | .ok _ => false) = true := by
  constructor
  · apply (usable_iff _ _ _).2
    constructor
    · change Core4.judge 4 fuelContext fuelFilling budgetType = true
      exact budget_filling_admitted
    · intro member supported
      change member ∈ [Member.bob] at supported
      simp only [List.mem_singleton] at supported
      subst member
      rfl
  · rfl

theorem budget_uncovered :
    Core4.admit (toyBudget 0) fuelContext budgetType fuelFilling = .error (.uncovered 1) := by rfl

theorem budget_filling_typed : Core4.Typed fuelContext fuelFilling budgetType :=
  (Core4.slotOf_usable (toyBudget 1) fuelContext budgetType (fun _ => [Member.bob])
    (World.holdsAt 1) fuelFilling budget_tooth.1).1

end BudgetFixtures

/-! ## The integrity-preserving filler on a checker's slot -/

section
variable {V Fact : Type} [World V Fact]
open World

/-- A Core4 filling selected by the integrity-preserving filler has semantic typing, independently
of the budget used to discover its certificate. -/
theorem slotFiller_typed (budget : Core4.Budget) (Ψ : Context) (A : Ty)
    (supports : AnnotatedTerm → List Fact) (v : V) (order : List AnnotatedTerm) (t : AnnotatedTerm)
    (h : (slotFiller : Filler V Fact AnnotatedTerm).fill
      (Core4.slotOf budget Ψ A supports) v order = .ok t) : Core4.Typed Ψ t A := by
  obtain ⟨_, hu, _⟩ := select_ok h
  exact (Core4.slotOf_usable budget Ψ A supports (holdsAt v) t hu).1

/-- When a budgeted slot refuses a candidate whose ordinary supports all hold, its named
explanation is precisely `uncovered` at the declared grade. This connects admission diagnostics to
the actual integrity-preserving filler. -/
theorem slotFiller_uncovered (budget : Core4.Budget) (Ψ : Context) (A : Ty)
    (supports : AnnotatedTerm → List Fact) (v : V) (order : List AnnotatedTerm) (t : AnnotatedTerm)
    (w : Refusal Fact AnnotatedTerm)
    (h : (slotFiller : Filler V Fact AnnotatedTerm).fill
      (Core4.slotOf budget Ψ A supports) v order = .error w)
    (member : t ∈ order) (live : ∀ f ∈ supports t, holdsAt v f = true) :
    Core4.admit budget Ψ A t = .error (.uncovered budget.grade) := by
  have refused := (select_error h).1 t member
  have dead : (Core4.slotOf budget Ψ A supports).dead (holdsAt v) t = [] :=
    (dead_eq_nil_iff _ _ _).2 live
  unfold Slot.usable at refused
  rw [dead] at refused
  have checkFalse : Core4.judge budget.grade Ψ t A = false := by
    simpa only [Core4.slotOf, List.isEmpty_nil, Bool.and_true] using refused
  simp [Core4.admit, checkFalse]

end

/-! ## Author ≠ Integrator Schelling Slot & Certified Intention Realization Calculus -/

namespace Budget

/-- Pointwise relational lifting over lists (`Forall₂` without Mathlib). -/
inductive RelList {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : RelList R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → RelList R as bs → RelList R (a :: as) (b :: bs)

/-- Author-declared open Schelling slot interface: specifies nominal `Obend.Kind` identity,
open `Obend.Intention` reference, per-slot Clairvoyant `Core4.Budget` ceiling, reference behavioral
specification `specTerm`, and gluing overlap dependencies `(peerSlotId, sharedInterfaceTag)`. -/
structure OpenSlotInterface where
  slotId : String
  expectedKind : String
  intentionRef : String
  budget : Core4.Budget
  fuel : Nat
  specTerm : Obend.Core.Term.Term
  peerDeps : List (String × String) := []

/-- Integrator-supplied concrete candidate implementation for an `OpenSlotInterface`. -/
structure SlotCandidate (Pin : Type) where
  candId : String
  slotId : String
  kindPin : Obend.Kind.KindPin
  intentionPin : Pin
  implTerm : Obend.Core.Term.Term
  gluingTags : List (String × String) := []
  sharedResourceIds : List String := []

/-- Bound `(Author interface, Integrator candidate)` pair inside a glued realization. -/
structure BoundSlot (Pin : Type) where
  iface : OpenSlotInterface
  cand : SlotCandidate Pin

/-- Multi-party negotiation input for a single open slot: Author interface + priority-ranked
Integrator candidates. -/
structure SlotProposal (Pin : Type) where
  iface : OpenSlotInterface
  candidates : List (SlotCandidate Pin)

/-- Pinpointed local contract failure reason for a single candidate binding. -/
inductive LocalSlotFailure where
  | wrongSlotId (expected actual : String)
  | wrongNominalKind (expected actual : String)
  | staleKindLineage (pin : Obend.Kind.KindPin)
  | wrongIntentionRef (expected actual : String)
  | staleIntentionSupports
  | duplicateGluingTags
  | missingSelfGluingTag (slotId : String)
  | costOrObservationContractFailed (budget : Nat)
  deriving DecidableEq, Repr

/-- Structured multi-party negotiation refusal certificate. -/
inductive NegotiationRefusal where
  | malformedSlotGraph (slotIds : List String)
  | localContractEmpty (slotId : String) (candidateFailures : List (String × LocalSlotFailure))
  | arcConsistencyPrunedEmpty (slotId : String) (roundsUsed : Nat)
  | cyclicGluingConflict (roundsUsed : Nat) (participatingSlots : List String)
  deriving DecidableEq, Repr

/-- Certified Intention Realizer produced by multi-party slot negotiation: carries the glued
slot bindings together with the number of monotone domain-pruning rounds executed. -/
structure IntentionRealizer (Pin : Type) where
  bindings : List (BoundSlot Pin)
  roundsUsed : Nat

/-- Pairwise-distinct check on string identifiers (`slotId`s and `gluingTags` keys). -/
@[expose] def uniqueStrings : List String → Bool
  | [] => true
  | s :: rest => !rest.contains s && uniqueStrings rest

theorem uniqueStrings_iff_nodup :
    ∀ (xs : List String), uniqueStrings xs = true ↔ xs.Nodup
  | [] => by simp [uniqueStrings]
  | x :: xs => by
    have hNotMem : (!xs.contains x) = true ↔ x ∉ xs := by
      constructor
      · intro h hx
        have hc : xs.contains x = true := List.contains_iff_mem.2 hx
        rw [hc] at h; cases h
      · intro hx
        cases hc : xs.contains x
        · rfl
        · exfalso; exact hx (List.contains_iff_mem.1 hc)
    simp only [uniqueStrings, Bool.and_eq_true, hNotMem, List.nodup_cons, uniqueStrings_iff_nodup xs]

/-- Structural lookup of a gluing interface tag. -/
@[expose] def lookupGluingTag : List (String × String) → String → Option String
  | [], _ => none
  | (k', v) :: rest, k => if k' == k then some v else lookupGluingTag rest k

/-- Directed gluing compatibility: every `(peerId, tag)` declared on `iface₁` targeting `iface₂`
must carry identical tag values on `c₁` and `c₂`. -/
@[expose] def directedGluingCompatible {Pin : Type}
    (iface₁ : OpenSlotInterface) (c₁ : SlotCandidate Pin)
    (iface₂ : OpenSlotInterface) (c₂ : SlotCandidate Pin) : Bool :=
  iface₁.peerDeps.all fun dep =>
    if dep.1 == iface₂.slotId then
      match lookupGluingTag c₁.gluingTags dep.2, lookupGluingTag c₂.gluingTags dep.2 with
      | some v₁, some v₂ => v₁ == v₂
      | _, _ => false
    else
      true

/-- Audit a single Integrator candidate `c` against Author interface `iface`, nominal registry `ks`,
and open Intention `I` at world `w`. Returns `none` iff all contracts pass, or `some reason` naming
the exact violated contract. -/
@[expose] def auditCandidateLocal {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (iface : OpenSlotInterface) (c : SlotCandidate Pin) : Option LocalSlotFailure :=
  if c.slotId != iface.slotId then
    some (.wrongSlotId iface.slotId c.slotId)
  else if c.kindPin.name != iface.expectedKind then
    some (.wrongNominalKind iface.expectedKind c.kindPin.name)
  else if (Obend.Kind.pinnedPrecedence ks c.kindPin).isOk == false then
    some (.staleKindLineage c.kindPin)
  else if I.ref c.intentionPin != iface.intentionRef then
    some (.wrongIntentionRef iface.intentionRef (I.ref c.intentionPin))
  else if !(I.slot iface.intentionRef).usable (I.holds w) c.intentionPin then
    some .staleIntentionSupports
  else if !uniqueStrings (c.gluingTags.map Prod.fst) then
    some .duplicateGluingTags
  else if !directedGluingCompatible iface c iface c then
    some (.missingSelfGluingTag iface.slotId)
  else if !Obend.Equiv.checkSlotCostContract iface.fuel iface.budget.grade c.implTerm iface.specTerm then
    some (.costOrObservationContractFailed iface.budget.grade)
  else
    none

/-- Boolean local contract checker induced by `auditCandidateLocal`. -/
@[expose] def checkCandidateLocal {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (iface : OpenSlotInterface) (c : SlotCandidate Pin) : Bool :=
  (auditCandidateLocal ks I w iface c).isNone

/-- Concrete inhabitedness witness for `checkCandidateLocal`. -/
theorem checkCandidateLocal_inhabited :
    let ks : Obend.Kind.Kinds :=
      ⟨[{ name := "Codec", version := 1, layout := [], init := .natural 0,
          law := .boolean true, parents := [] }]⟩
    let I₀ : Obend.Intention Unit String String Unit String :=
      { ref := id
        supports := fun _ => [()]
        holds := fun _ _ => true
        resolve := fun _ r => .ok r
        resolve_ref := fun _ _ _ h => by cases h; rfl
        resolve_holds := fun _ _ _ _ _ _ => rfl }
    let iface : OpenSlotInterface :=
      { slotId := "s0", expectedKind := "Codec", intentionRef := "codec@^1",
        budget := ⟨2⟩, fuel := 1, specTerm := .nat 7 }
    let cand : SlotCandidate String :=
      { candId := "c0", slotId := "s0", kindPin := ⟨"Codec", 1, []⟩,
        intentionPin := "codec@^1", implTerm := .nat 7 }
    checkCandidateLocal ks I₀ () iface cand = true := by
  decide

/-- Soundness of `checkCandidateLocal`: passing local audit certifies slot alignment, nominal `Kind`
identity + live C4 lineage precedence, `SupportSheaf.IntentionPin` usability at `w`, and Clairvoyant
`CV` observation + `CostAtMost` within `iface.budget.grade`. -/
theorem checkCandidateLocal_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {iface : OpenSlotInterface} {c : SlotCandidate Pin}
    (h : checkCandidateLocal ks I w iface c = true) :
    c.slotId = iface.slotId ∧
    c.kindPin.name = iface.expectedKind ∧
    (Obend.Kind.pinnedPrecedence ks c.kindPin).isOk = true ∧
    (Obend.Kind.kindRefs (Law := Obend.Core.Term.Term)).current ks c.kindPin = true ∧
    I.ref c.intentionPin = iface.intentionRef ∧
    SupportSheaf.SupportSheaf.usable (W := W)
      (Obj := SupportSheaf.IntentionPin I iface.intentionRef) w ⟨c.intentionPin⟩ = true ∧
    (∃ v ki ks',
      Obend.Equiv.CV c.implTerm v ki ∧
      Obend.Equiv.CV iface.specTerm v ks' ∧
      ki ≤ iface.budget.grade ∧
      Obend.Equiv.CostAtMost c.implTerm iface.budget.grade) := by
  unfold checkCandidateLocal auditCandidateLocal at h
  by_cases h1 : (c.slotId != iface.slotId) = true
  · simp [h1] at h
  · simp only [h1] at h
    have hSlot : c.slotId = iface.slotId := by simpa [bne_iff_ne] using h1
    by_cases h2 : (c.kindPin.name != iface.expectedKind) = true
    · simp [h2] at h
    · simp only [h2] at h
      have hKind : c.kindPin.name = iface.expectedKind := by simpa [bne_iff_ne] using h2
      by_cases h3 : ((Obend.Kind.pinnedPrecedence ks c.kindPin).isOk == false) = true
      · simp [h3] at h
      · simp only [h3] at h
        have hPrec : (Obend.Kind.pinnedPrecedence ks c.kindPin).isOk = true := by
          cases hok : (Obend.Kind.pinnedPrecedence ks c.kindPin).isOk
          · simp [hok] at h3
          · rfl
        have hKindCur :
            (Obend.Kind.kindRefs (Law := Obend.Core.Term.Term)).current ks c.kindPin = true := by
          unfold Obend.Kind.pinnedPrecedence at hPrec
          cases hcur : (Obend.Kind.kindRefs (Law := Obend.Core.Term.Term)).current ks c.kindPin
          · simp [hcur, Except.isOk, Except.toBool] at hPrec
          · rfl
        by_cases h4 : (I.ref c.intentionPin != iface.intentionRef) = true
        · simp [h4] at h
        · simp only [h4] at h
          have hRef : I.ref c.intentionPin = iface.intentionRef := by simpa [bne_iff_ne] using h4
          by_cases h5 : (!(I.slot iface.intentionRef).usable (I.holds w) c.intentionPin) = true
          · simp [h5] at h
          · simp only [h5] at h
            have hUsable : (I.slot iface.intentionRef).usable (I.holds w) c.intentionPin = true := by
              cases hu : (I.slot iface.intentionRef).usable (I.holds w) c.intentionPin
              · simp [hu] at h5
              · rfl
            by_cases h5a : (!uniqueStrings (c.gluingTags.map Prod.fst)) = true
            · simp [h5a] at h
            · simp only [h5a] at h
              by_cases h5b : (!directedGluingCompatible iface c iface c) = true
              · simp [h5b] at h
              · simp only [h5b] at h
                by_cases h6 :
                    (!Obend.Equiv.checkSlotCostContract iface.fuel iface.budget.grade
                      c.implTerm iface.specTerm) = true
                · simp [h6] at h
                · have hCost :
                      Obend.Equiv.checkSlotCostContract iface.fuel iface.budget.grade
                        c.implTerm iface.specTerm = true := by
                    cases hc : Obend.Equiv.checkSlotCostContract iface.fuel iface.budget.grade
                        c.implTerm iface.specTerm
                    · simp [hc] at h6
                    · rfl
                  exact ⟨hSlot, hKind, hPrec, hKindCur, hRef, hUsable,
                    Obend.Equiv.checkSlotCostContract_sound hCost⟩

/-- Tag-uniqueness & self-dependency closure soundness of `checkCandidateLocal`. -/
theorem checkCandidateLocal_self_gluing_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {iface : OpenSlotInterface} {c : SlotCandidate Pin}
    (h : checkCandidateLocal ks I w iface c = true) :
    (c.gluingTags.map Prod.fst).Nodup ∧
    directedGluingCompatible iface c iface c = true := by
  unfold checkCandidateLocal auditCandidateLocal at h
  by_cases h1 : (c.slotId != iface.slotId) = true
  · simp [h1] at h
  · simp only [h1] at h
    by_cases h2 : (c.kindPin.name != iface.expectedKind) = true
    · simp [h2] at h
    · simp only [h2] at h
      by_cases h3 : ((Obend.Kind.pinnedPrecedence ks c.kindPin).isOk == false) = true
      · simp [h3] at h
      · simp only [h3] at h
        by_cases h4 : (I.ref c.intentionPin != iface.intentionRef) = true
        · simp [h4] at h
        · simp only [h4] at h
          by_cases h5 : (!(I.slot iface.intentionRef).usable (I.holds w) c.intentionPin) = true
          · simp [h5] at h
          · simp only [h5] at h
            by_cases h5a : (!uniqueStrings (c.gluingTags.map Prod.fst)) = true
            · simp [h5a] at h
            · simp only [h5a] at h
              have hUniq : uniqueStrings (c.gluingTags.map Prod.fst) = true := by
                cases hu : uniqueStrings (c.gluingTags.map Prod.fst)
                · simp [hu] at h5a
                · rfl
              by_cases h5b : (!directedGluingCompatible iface c iface c) = true
              · simp [h5b] at h
              · have hSelf : directedGluingCompatible iface c iface c = true := by
                  cases hs : directedGluingCompatible iface c iface c
                  · simp [hs] at h5b
                  · rfl
                exact ⟨(uniqueStrings_iff_nodup _).1 hUniq, hSelf⟩

/-- Exact converse on `auditCandidateLocal`: `some failure` implies `checkCandidateLocal = false`. -/
theorem auditCandidateLocal_some_refuses {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {iface : OpenSlotInterface} {c : SlotCandidate Pin} {f : LocalSlotFailure}
    (h : auditCandidateLocal ks I w iface c = some f) :
    checkCandidateLocal ks I w iface c = false := by
  simp [checkCandidateLocal, h]

/-- Symmetric pairwise gluing compatibility across overlap edges in either direction. -/
@[expose] def gluingCompatible {Pin : Type}
    (iface₁ : OpenSlotInterface) (c₁ : SlotCandidate Pin)
    (iface₂ : OpenSlotInterface) (c₂ : SlotCandidate Pin) : Bool :=
  directedGluingCompatible iface₁ c₁ iface₂ c₂ &&
  directedGluingCompatible iface₂ c₂ iface₁ c₁

theorem gluingCompatible_symm {Pin : Type}
    (iface₁ : OpenSlotInterface) (c₁ : SlotCandidate Pin)
    (iface₂ : OpenSlotInterface) (c₂ : SlotCandidate Pin) :
    gluingCompatible iface₁ c₁ iface₂ c₂ = gluingCompatible iface₂ c₂ iface₁ c₁ := by
  simp [gluingCompatible, Bool.and_comm]

/-- Whether `b` is gluing-compatible with every bound slot in `bs`. -/
@[expose] def compatWithAll {Pin : Type} (b : BoundSlot Pin) (bs : List (BoundSlot Pin)) : Bool :=
  bs.all fun b' => gluingCompatible b.iface b.cand b'.iface b'.cand

/-- Pairwise gluing compatibility across an entire bound realization. -/
@[expose] def allPairsGluingCompatible {Pin : Type} : List (BoundSlot Pin) → Bool
  | [] => true
  | b :: bs => compatWithAll b bs && allPairsGluingCompatible bs

/-- Slot-graph structural well-formedness: pairwise distinct `slotId`s and closed `peerDeps`
(every declared peer dependency targets a slot present in `ifaces`, including self-edges). -/
@[expose] def slotGraphWellFormed (ifaces : List OpenSlotInterface) : Bool :=
  let slotIds := ifaces.map (·.slotId)
  uniqueStrings slotIds &&
  ifaces.all fun iface => iface.peerDeps.all fun dep => slotIds.contains dep.1

/-- Full world-independent gluing & dependency-closure invariant on a bound realization:
unique `slotId`s, closed `peerDeps`, valid self-edge tags, and pairwise overlap compatibility. -/
@[expose] def realizerGraphValid {Pin : Type} (bs : List (BoundSlot Pin)) : Bool :=
  slotGraphWellFormed (bs.map (·.iface)) &&
  (bs.all fun b => directedGluingCompatible b.iface b.cand b.iface b.cand) &&
  allPairsGluingCompatible bs

/-! ### `SupportSheaf` Gluing Construction for `IntentionRealizer` -/

/-- Every glued `IntentionRealizer` forms a genuine `SupportSheaf` over world `W` with
deduplicated (`Intention.dedupSupports`) union footprint across all bound slots, enforcing
world-independent `realizerGraphValid` (unique slot IDs, closed peer dependencies, and overlap
gluing compatibility) alongside per-slot `Intention` usability! -/
@[instance_reducible] def intentionRealizerSupportSheaf {W Pin Fact Err : Type} [DecidableEq Fact]
    (I : Obend.Intention W String Pin Fact Err) :
    SupportSheaf.SupportSheaf W Fact (IntentionRealizer Pin) where
  supports r :=
    Obend.Intention.dedupSupports (r.bindings.flatMap fun b => I.supports b.cand.intentionPin)
  holds := I.holds
  usable w r :=
    realizerGraphValid r.bindings &&
    r.bindings.all fun b => (I.slot b.iface.intentionRef).usable (I.holds w) b.cand.intentionPin
  usable_supports w r hu f hf := by
    rw [Bool.and_eq_true] at hu
    obtain ⟨_, huSlots⟩ := hu
    have hfRaw := (Obend.Intention.mem_dedupSupports_iff _ f).1 hf
    rw [List.mem_flatMap] at hfRaw
    obtain ⟨b, hbMem, hfSlot⟩ := hfRaw
    rw [List.all_eq_true] at huSlots
    have hbUsable := huSlots b hbMem
    exact ((usable_iff (I.slot b.iface.intentionRef) (I.holds w) b.cand.intentionPin).1 hbUsable).2 f hfSlot
  holds_frame {w₁ w₂ r} h := by
    apply congrArg (realizerGraphValid r.bindings && ·)
    suffices ∀ (bs : List (BoundSlot Pin)),
        (∀ f ∈ Obend.Intention.dedupSupports (bs.flatMap fun b => I.supports b.cand.intentionPin),
          I.holds w₁ f = I.holds w₂ f) →
        (bs.all fun b => (I.slot b.iface.intentionRef).usable (I.holds w₁) b.cand.intentionPin) =
        (bs.all fun b => (I.slot b.iface.intentionRef).usable (I.holds w₂) b.cand.intentionPin) from
      this r.bindings h
    intro bs hbs
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      have hbAgree : ∀ f ∈ I.supports b.cand.intentionPin, I.holds w₁ f = I.holds w₂ f := by
        intro f hf
        apply hbs f
        rw [Obend.Intention.mem_dedupSupports_iff, List.mem_flatMap]
        exact ⟨b, List.mem_cons_self, hf⟩
      have hbDead :
          (I.slot b.iface.intentionRef).dead (I.holds w₁) b.cand.intentionPin =
          (I.slot b.iface.intentionRef).dead (I.holds w₂) b.cand.intentionPin := by
        unfold Slot.dead
        apply List.filter_congr
        intro f hf
        exact congrArg Bool.not (hbAgree f hf)
      have hbEq :
          (I.slot b.iface.intentionRef).usable (I.holds w₁) b.cand.intentionPin =
          (I.slot b.iface.intentionRef).usable (I.holds w₂) b.cand.intentionPin := by
        simp only [Slot.usable, hbDead]
      have hbsAgree :
          ∀ f ∈ Obend.Intention.dedupSupports (bs.flatMap fun b' => I.supports b'.cand.intentionPin),
            I.holds w₁ f = I.holds w₂ f := by
        intro f hf
        have hf' := (Obend.Intention.mem_dedupSupports_iff _ f).1 hf
        rw [List.mem_flatMap] at hf'
        obtain ⟨b', hb'Mem, hf'⟩ := hf'
        apply hbs f
        rw [Obend.Intention.mem_dedupSupports_iff, List.mem_flatMap]
        exact ⟨b', List.mem_cons_of_mem _ hb'Mem, hf'⟩
      simp only [List.all_cons, hbEq, ih hbsAgree]

/-! ### Monotone Multi-Party Domain Pruning & Priority-Ordered Consistent Assignment -/

/-- Sum of remaining candidate counts across all slot domains. -/
def domainCard {Pin : Type} : List (OpenSlotInterface × List (SlotCandidate Pin)) → Nat
  | [] => 0
  | (_, cs) :: rest => cs.length + domainCard rest

/-- Whether candidate `c` for `iface` has at least one gluing-compatible partner in every other
slot's current domain in `allDoms`. -/
def hasSupportInAllPeers {Pin : Type}
    (allDoms : List (OpenSlotInterface × List (SlotCandidate Pin)))
    (iface : OpenSlotInterface) (c : SlotCandidate Pin) : Bool :=
  allDoms.all fun (iface', cs') =>
    if iface'.slotId == iface.slotId then true
    else cs'.any fun c' => gluingCompatible iface c iface' c'

/-- One synchronous multi-party arc-consistency pruning round across `doms`. -/
def pruneOneRoundAux {Pin : Type}
    (allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    List (OpenSlotInterface × List (SlotCandidate Pin)) →
    List (OpenSlotInterface × List (SlotCandidate Pin))
  | [] => []
  | (iface, cs) :: rest =>
    (iface, cs.filter (hasSupportInAllPeers allDoms iface)) :: pruneOneRoundAux allDoms rest

def pruneOneRound {Pin : Type}
    (doms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    List (OpenSlotInterface × List (SlotCandidate Pin)) :=
  pruneOneRoundAux doms doms

theorem filter_eq_self_of_length_eq {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length = xs.length → xs.filter p = xs
  | [], _ => rfl
  | x :: xs, hlen => by
    simp only [List.filter_cons, List.length_cons] at hlen ⊢
    cases hp : p x <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hlen ⊢
    · have hle := List.length_filter_le p xs
      omega
    · simp only [List.length_cons] at hlen
      exact congrArg (x :: ·) (filter_eq_self_of_length_eq p xs (by omega))

theorem pruneOneRoundAux_card_le {Pin : Type}
    (allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    ∀ doms, domainCard (pruneOneRoundAux allDoms doms) ≤ domainCard doms
  | [] => Nat.le_refl 0
  | (iface, cs) :: rest => by
    simp only [pruneOneRoundAux, domainCard]
    have h1 := List.length_filter_le (hasSupportInAllPeers allDoms iface) cs
    have h2 := pruneOneRoundAux_card_le allDoms rest
    omega

theorem pruneOneRound_card_le {Pin : Type}
    (doms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    domainCard (pruneOneRound doms) ≤ domainCard doms :=
  pruneOneRoundAux_card_le doms doms

theorem pruneOneRoundAux_eq_self_of_card_eq {Pin : Type}
    (allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    ∀ doms, domainCard (pruneOneRoundAux allDoms doms) = domainCard doms →
      pruneOneRoundAux allDoms doms = doms
  | [], _ => rfl
  | (iface, cs) :: rest, hcard => by
    simp only [pruneOneRoundAux, domainCard] at hcard ⊢
    have h1 := List.length_filter_le (hasSupportInAllPeers allDoms iface) cs
    have h2 := pruneOneRoundAux_card_le allDoms rest
    have hcsEq : (cs.filter (hasSupportInAllPeers allDoms iface)).length = cs.length := by omega
    have hrestEq : domainCard (pruneOneRoundAux allDoms rest) = domainCard rest := by omega
    rw [filter_eq_self_of_length_eq _ cs hcsEq,
        pruneOneRoundAux_eq_self_of_card_eq allDoms rest hrestEq]

theorem pruneOneRound_eq_self_of_card_eq {Pin : Type}
    {doms : List (OpenSlotInterface × List (SlotCandidate Pin))}
    (hcard : domainCard (pruneOneRound doms) = domainCard doms) :
    pruneOneRound doms = doms :=
  pruneOneRoundAux_eq_self_of_card_eq doms doms hcard

/-- Bounded monotone fixed-point iteration of `pruneOneRound`, returning `(stabilizedDoms, roundsUsed)`. -/
def pruneDomainsLoop {Pin : Type} :
    Nat → List (OpenSlotInterface × List (SlotCandidate Pin)) →
    List (OpenSlotInterface × List (SlotCandidate Pin)) × Nat
  | 0, doms => (doms, 0)
  | fuel + 1, doms =>
    let next := pruneOneRound doms
    if domainCard next == domainCard doms then
      (doms, 0)
    else
      let (finalDoms, moreRounds) := pruneDomainsLoop fuel next
      (finalDoms, moreRounds + 1)

theorem pruneDomainsLoop_converges {Pin : Type} :
    ∀ (fuel : Nat) (doms : List (OpenSlotInterface × List (SlotCandidate Pin))),
      domainCard doms ≤ fuel →
      let res := pruneDomainsLoop fuel doms
      pruneOneRound res.1 = res.1 ∧ res.2 ≤ fuel ∧ domainCard res.1 ≤ domainCard doms
  | 0, doms, hle => by
    simp only [pruneDomainsLoop]
    have h0 : domainCard doms = 0 := by omega
    have h1 := pruneOneRound_card_le doms
    have hEq : domainCard (pruneOneRound doms) = domainCard doms := by omega
    exact ⟨pruneOneRound_eq_self_of_card_eq hEq, Nat.le_refl 0, Nat.le_refl _⟩
  | fuel + 1, doms, hle => by
    simp only [pruneDomainsLoop]
    by_cases hEqB : (domainCard (pruneOneRound doms) == domainCard doms) = true
    · simp only [hEqB, ↓reduceIte]
      have hEq : domainCard (pruneOneRound doms) = domainCard doms := eq_of_beq hEqB
      exact ⟨pruneOneRound_eq_self_of_card_eq hEq, Nat.zero_le _, Nat.le_refl _⟩
    · simp only [hEqB, Bool.false_eq_true, ↓reduceIte]
      have hNe : domainCard (pruneOneRound doms) ≠ domainCard doms := by
        intro heq; exact hEqB (beq_iff_eq.2 heq)
      have hLe := pruneOneRound_card_le doms
      have hStrict : domainCard (pruneOneRound doms) ≤ fuel := by omega
      obtain ⟨hFix, hRounds, hCard⟩ := pruneDomainsLoop_converges fuel (pruneOneRound doms) hStrict
      exact ⟨hFix, by omega, Nat.le_trans hCard hLe⟩

/-- Structural priority-ordered consistent tuple search over pruned domains. -/
def searchConsistentWith {Pin : Type} (ok : BoundSlot Pin → Bool) :
    List (OpenSlotInterface × List (SlotCandidate Pin)) →
    Option (List (BoundSlot Pin))
  | [] => some []
  | (iface, cs) :: rest =>
    let rec tryCands : List (SlotCandidate Pin) → Option (List (BoundSlot Pin))
      | [] => none
      | c :: cs' =>
        let b : BoundSlot Pin := ⟨iface, c⟩
        if ok b then
          match searchConsistentWith
              (fun b' => ok b' && gluingCompatible b.iface b.cand b'.iface b'.cand) rest with
          | some tailSol => some (b :: tailSol)
          | none => tryCands cs'
        else
          tryCands cs'
    tryCands cs

theorem searchConsistentWith_sound {Pin : Type} :
    ∀ (doms : List (OpenSlotInterface × List (SlotCandidate Pin)))
      (ok : BoundSlot Pin → Bool) (sol : List (BoundSlot Pin)),
      searchConsistentWith ok doms = some sol →
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) doms sol ∧
      (∀ b ∈ sol, ok b = true) ∧
      allPairsGluingCompatible sol = true
  | [], ok, sol, h => by
    simp only [searchConsistentWith, Option.some.injEq] at h
    subst h
    refine ⟨.nil, ?_, rfl⟩
    intro _ hm
    cases hm
  | (iface, cs) :: rest, ok, sol, h => by
    simp only [searchConsistentWith] at h
    suffices ∀ (sub : List (SlotCandidate Pin)),
        (∀ x ∈ sub, x ∈ cs) →
        searchConsistentWith.tryCands ok iface rest sub = some sol →
        RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) ((iface, cs) :: rest) sol ∧
        (∀ b ∈ sol, ok b = true) ∧
        allPairsGluingCompatible sol = true by
      exact this cs (fun _ hx => hx) h
    intro sub hSub hTry
    induction sub with
    | nil => simp [searchConsistentWith.tryCands] at hTry
    | cons c cs' ih =>
      simp only [searchConsistentWith.tryCands] at hTry
      by_cases hOk : ok ⟨iface, c⟩ = true
      · simp only [hOk, ↓reduceIte] at hTry
        cases hRec : searchConsistentWith
            (fun b' => ok b' && gluingCompatible iface c b'.iface b'.cand) rest <;>
          rw [hRec] at hTry
        · exact ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)) hTry
        · rename_i tailSol
          simp only [Option.some.injEq] at hTry
          subst hTry
          obtain ⟨hF2, hTailOk, hTailGlue⟩ :=
            searchConsistentWith_sound rest _ tailSol hRec
          have hCompat : compatWithAll ⟨iface, c⟩ tailSol = true := by
            rw [compatWithAll, List.all_eq_true]
            intro b' hb'
            exact (Eq.mp (Bool.and_eq_true _ _) (hTailOk b' hb')).2
          refine ⟨.cons ⟨rfl, hSub c List.mem_cons_self⟩ hF2, ?_, ?_⟩
          · intro b' hb'
            rcases List.mem_cons.1 hb' with rfl | hb'Tail
            · exact hOk
            · exact (Eq.mp (Bool.and_eq_true _ _) (hTailOk b' hb'Tail)).1
          · simp [allPairsGluingCompatible, hCompat, hTailGlue]
      · simp only [hOk, Bool.false_eq_true, ↓reduceIte] at hTry
        exact ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)) hTry

theorem searchConsistentWith_complete {Pin : Type} :
    ∀ (doms : List (OpenSlotInterface × List (SlotCandidate Pin)))
      (ok : BoundSlot Pin → Bool) (wit : List (BoundSlot Pin)),
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) doms wit →
      (∀ b ∈ wit, ok b = true) →
      allPairsGluingCompatible wit = true →
      ∃ sol, searchConsistentWith ok doms = some sol
  | [], _, [], .nil, _, _ => ⟨[], by simp [searchConsistentWith]⟩
  | (iface, cs) :: rest, ok, b₀ :: witTail, .cons ⟨hIface, hMem⟩ hF2Tail, hOkAll, hGlueAll => by
    cases b₀ with
    | mk bIface c₀ =>
      dsimp only at hIface hMem
      cases hIface.symm
      simp only [allPairsGluingCompatible, Bool.and_eq_true] at hGlueAll
      obtain ⟨hCompat₀, hGlueTail⟩ := hGlueAll
      rw [compatWithAll, List.all_eq_true] at hCompat₀
      have hOk₀ : ok ⟨iface, c₀⟩ = true := hOkAll ⟨iface, c₀⟩ List.mem_cons_self
      have hTailOk' :
          ∀ b' ∈ witTail,
            (ok b' && gluingCompatible iface c₀ b'.iface b'.cand) = true := by
        intro b' hb'
        rw [Bool.and_eq_true]
        exact ⟨hOkAll b' (List.mem_cons_of_mem _ hb'), hCompat₀ b' hb'⟩
      obtain ⟨tailSol, hRecSome⟩ :=
        searchConsistentWith_complete rest _ witTail hF2Tail hTailOk' hGlueTail
      simp only [searchConsistentWith]
      suffices ∀ (sub : List (SlotCandidate Pin)),
          c₀ ∈ sub →
          ∃ sol, searchConsistentWith.tryCands ok iface rest sub = some sol by
        exact this cs hMem
      intro sub hInSub
      induction sub with
      | nil => cases hInSub
      | cons c cs' ih =>
        simp only [searchConsistentWith.tryCands]
        rcases List.mem_cons.1 hInSub with rfl | hInTail
        · simp only [hOk₀, ↓reduceIte, hRecSome]
          exact ⟨⟨iface, c₀⟩ :: tailSol, rfl⟩
        · by_cases hOkC : ok ⟨iface, c⟩ = true
          · simp only [hOkC, ↓reduceIte]
            cases hSubRec : searchConsistentWith
                (fun b' => ok b' && gluingCompatible iface c b'.iface b'.cand) rest
            · exact ih hInTail
            · rename_i ts
              exact ⟨⟨iface, c⟩ :: ts, rfl⟩
          · simp only [hOkC, Bool.false_eq_true, ↓reduceIte]
            exact ih hInTail

/-- Build initial locally audited domains, or return the first slot whose local candidate domain is
empty together with every candidate's exact `LocalSlotFailure` diagnosis. -/
def buildLocalDomains {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W) :
    List (SlotProposal Pin) →
    Except NegotiationRefusal (List (OpenSlotInterface × List (SlotCandidate Pin)))
  | [] => .ok []
  | prop :: rest =>
    let passed := prop.candidates.filter (checkCandidateLocal ks I w prop.iface)
    if passed.isEmpty then
      let failures := prop.candidates.filterMap fun c =>
        (auditCandidateLocal ks I w prop.iface c).map fun reason => (c.candId, reason)
      .error (.localContractEmpty prop.iface.slotId failures)
    else
      match buildLocalDomains ks I w rest with
      | .error e => .error e
      | .ok tailDoms => .ok ((prop.iface, passed) :: tailDoms)

/-- Find the first slot whose domain became empty after arc-consistency pruning, if any. -/
def findEmptyDomain {Pin : Type} :
    List (OpenSlotInterface × List (SlotCandidate Pin)) → Option String
  | [] => none
  | (iface, cs) :: rest => if cs.isEmpty then some iface.slotId else findEmptyDomain rest

/-- **Deadlock-Free Multi-Party Slot Negotiation (`negotiateSlots`)**:
1. Validates `slotGraphWellFormed` (pairwise distinct `slotId`s and closed `peerDeps`).
2. Filters each slot's Integrator candidates through `checkCandidateLocal ks I w`.
3. Executes monotone multi-party arc-consistency domain pruning (`pruneDomainsLoop`) bounded by
   total candidate cardinality `domainCard localDoms`.
4. Selects a priority-ordered globally compatible tuple (`searchConsistentWith`), returning either a
   certified `IntentionRealizer` or a structured `NegotiationRefusal` blame certificate. -/
@[expose] def negotiateSlots {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (proposals : List (SlotProposal Pin)) :
    Except NegotiationRefusal (IntentionRealizer Pin) :=
  if !slotGraphWellFormed (proposals.map (·.iface)) then
    .error (.malformedSlotGraph (proposals.map (·.iface.slotId)))
  else
    match buildLocalDomains ks I w proposals with
    | .error ref => .error ref
    | .ok localDoms =>
      let (prunedDoms, roundsUsed) := pruneDomainsLoop (domainCard localDoms) localDoms
      match findEmptyDomain prunedDoms with
      | some emptySlotId => .error (.arcConsistencyPrunedEmpty emptySlotId roundsUsed)
      | none =>
        match searchConsistentWith (fun _ => true) prunedDoms with
        | some bindings => .ok ⟨bindings, roundsUsed⟩
        | none => .error (.cyclicGluingConflict roundsUsed (prunedDoms.map (·.1.slotId)))

/-! ### Compositional Budget & Shared-Resource Subadditivity Accounting -/

/-- Sum of Author-declared per-slot Clairvoyant budgets. -/
@[expose] def totalDeclaredSlotBudget {Pin : Type} : List (BoundSlot Pin) → Nat
  | [] => 0
  | b :: bs => b.iface.budget.grade + totalDeclaredSlotBudget bs

/-- Cost of initializing/verifying a list of named shared resources. -/
def sumResourceCosts (costOf : String → Nat) : List String → Nat
  | [] => 0
  | r :: rs => costOf r + sumResourceCosts costOf rs

/-- Unglued (naive independent) shared-resource cost across bound slots. -/
def ungluedResourceCost {Pin : Type} (costOf : String → Nat) : List (BoundSlot Pin) → Nat
  | [] => 0
  | b :: bs => sumResourceCosts costOf b.cand.sharedResourceIds + ungluedResourceCost costOf bs

/-- Glued shared-resource cost across bound slots: each shared resource is paid once via
`Obend.Intention.dedupSupports`. -/
def gluedSharedResourceCost {Pin : Type} (costOf : String → Nat) (bs : List (BoundSlot Pin)) : Nat :=
  sumResourceCosts costOf
    (Obend.Intention.dedupSupports (bs.flatMap fun b => b.cand.sharedResourceIds))

theorem sumResourceCosts_append (costOf : String → Nat) :
    ∀ xs ys, sumResourceCosts costOf (xs ++ ys) =
      sumResourceCosts costOf xs + sumResourceCosts costOf ys
  | [], _ => by simp [sumResourceCosts]
  | x :: xs, ys => by
    simp only [List.cons_append, sumResourceCosts, sumResourceCosts_append costOf xs ys]
    omega

theorem sumResourceCosts_dedup_le (costOf : String → Nat) :
    ∀ rs, sumResourceCosts costOf (Obend.Intention.dedupSupports rs) ≤ sumResourceCosts costOf rs
  | [] => by simp [Obend.Intention.dedupSupports, sumResourceCosts]
  | r :: rs => by
    simp only [Obend.Intention.dedupSupports, sumResourceCosts]
    have ih := sumResourceCosts_dedup_le costOf rs
    by_cases hmem : r ∈ Obend.Intention.dedupSupports rs
    · simp only [hmem, ↓reduceIte]; omega
    · simp only [hmem, ↓reduceIte, sumResourceCosts]; omega

theorem sumResourceCosts_flatMap_eq_unglued {Pin : Type} (costOf : String → Nat) :
    ∀ (bs : List (BoundSlot Pin)),
      sumResourceCosts costOf (bs.flatMap fun b => b.cand.sharedResourceIds) =
      ungluedResourceCost costOf bs
  | [] => rfl
  | b :: bs => by
    simp only [List.flatMap_cons, sumResourceCosts_append, ungluedResourceCost,
      sumResourceCosts_flatMap_eq_unglued costOf bs]

theorem gluedSharedResourceCost_subadditive {Pin : Type}
    (costOf : String → Nat) (bs : List (BoundSlot Pin)) :
    gluedSharedResourceCost costOf bs ≤ ungluedResourceCost costOf bs := by
  unfold gluedSharedResourceCost
  rw [← sumResourceCosts_flatMap_eq_unglued costOf bs]
  exact sumResourceCosts_dedup_le costOf _

/-- **Strict Shared-Resource Budget Subadditivity (`sumResourceCosts_dedup_lt_of_shared`)**:
when two bound slots share a resource `r₀` of positive cost `0 < costOf r₀`, the glued realization
strictly saves budget over independent per-slot execution. -/
theorem sumResourceCosts_dedup_lt_of_shared (costOf : String → Nat)
    {xs ys : List String} {r₀ : String}
    (hx : r₀ ∈ xs) (hy : r₀ ∈ ys) (hpos : 0 < costOf r₀) :
    sumResourceCosts costOf (Obend.Intention.dedupSupports (xs ++ ys)) <
      sumResourceCosts costOf xs + sumResourceCosts costOf ys := by
  rw [← sumResourceCosts_append costOf xs ys]
  induction xs with
  | nil => cases hx
  | cons x xs ih =>
    simp only [List.cons_append, Obend.Intention.dedupSupports, sumResourceCosts]
    by_cases heq : x = r₀
    · subst heq
      have hInRest : x ∈ Obend.Intention.dedupSupports (xs ++ ys) :=
        (Obend.Intention.mem_dedupSupports_iff (xs ++ ys) x).2 (List.mem_append_right xs hy)
      simp only [hInRest, ↓reduceIte]
      have hSub := sumResourceCosts_dedup_le costOf (xs ++ ys)
      omega
    · have hx' : r₀ ∈ xs := by
        rcases List.mem_cons.1 hx with rfl | hmem
        · exact absurd rfl heq
        · exact hmem
      have hLt := ih hx'
      by_cases hInRest : x ∈ Obend.Intention.dedupSupports (xs ++ ys)
      · simp only [hInRest, ↓reduceIte]; omega
      · simp only [hInRest, ↓reduceIte, sumResourceCosts]; omega

/-! ### Domain Inclusion & Completeness Helper Lemmas for `negotiateSlots` -/

theorem buildLocalDomains_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W} :
    ∀ {proposals : List (SlotProposal Pin)}
      {doms : List (OpenSlotInterface × List (SlotCandidate Pin))},
      buildLocalDomains ks I w proposals = .ok doms →
      RelList
        (fun prop d =>
          d.1 = prop.iface ∧
          ∀ c ∈ d.2, c ∈ prop.candidates ∧ checkCandidateLocal ks I w prop.iface c = true)
        proposals doms ∧
      domainCard doms ≤ domainCard (proposals.map fun p => (p.iface, p.candidates))
  | [], _, h => by
    cases h
    exact ⟨.nil, Nat.le_refl 0⟩
  | prop :: rest, _, h => by
    simp only [buildLocalDomains] at h
    by_cases hEmp : (prop.candidates.filter (checkCandidateLocal ks I w prop.iface)).isEmpty = true
    · simp only [hEmp, ↓reduceIte] at h
      cases h
    · simp only [hEmp, Bool.false_eq_true, ↓reduceIte] at h
      cases hTail : buildLocalDomains ks I w rest <;> rw [hTail] at h
      · cases h
      · rename_i tailDoms
        cases h
        obtain ⟨hF2, hCardTail⟩ := buildLocalDomains_sound hTail
        have hSub :
            ∀ c ∈ prop.candidates.filter (checkCandidateLocal ks I w prop.iface),
              c ∈ prop.candidates ∧ checkCandidateLocal ks I w prop.iface c = true := by
          intro c hc
          exact List.mem_filter.1 hc
        have hLenLe := List.length_filter_le (checkCandidateLocal ks I w prop.iface) prop.candidates
        refine ⟨.cons ⟨rfl, hSub⟩ hF2, ?_⟩
        simp only [List.map_cons, domainCard]
        omega

theorem pruneOneRoundAux_sub {Pin : Type}
    (allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))) :
    ∀ doms,
      RelList (fun d₁ d₂ => d₂.1 = d₁.1 ∧ ∀ c ∈ d₂.2, c ∈ d₁.2)
        doms (pruneOneRoundAux allDoms doms)
  | [] => .nil
  | (_, _) :: rest =>
    .cons ⟨rfl, fun _ hc => (List.mem_filter.1 hc).1⟩ (pruneOneRoundAux_sub allDoms rest)

theorem forall2_sub_trans {Pin : Type} :
    ∀ {xs ys zs : List (OpenSlotInterface × List (SlotCandidate Pin))},
      RelList (fun d₁ d₂ => d₂.1 = d₁.1 ∧ ∀ c ∈ d₂.2, c ∈ d₁.2) xs ys →
      RelList (fun d₁ d₂ => d₂.1 = d₁.1 ∧ ∀ c ∈ d₂.2, c ∈ d₁.2) ys zs →
      RelList (fun d₁ d₂ => d₂.1 = d₁.1 ∧ ∀ c ∈ d₂.2, c ∈ d₁.2) xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons ⟨h1, hs1⟩ t1, .cons ⟨h2, hs2⟩ t2 =>
    .cons ⟨h2.trans h1, fun c hc => hs1 c (hs2 c hc)⟩ (forall2_sub_trans t1 t2)

theorem pruneDomainsLoop_sub {Pin : Type} :
    ∀ (fuel : Nat) (doms : List (OpenSlotInterface × List (SlotCandidate Pin))),
      RelList (fun d₁ d₂ => d₂.1 = d₁.1 ∧ ∀ c ∈ d₂.2, c ∈ d₁.2)
        doms (pruneDomainsLoop fuel doms).1
  | 0, [] => .nil
  | 0, _ :: rest =>
    .cons ⟨rfl, fun _ hc => hc⟩ (pruneDomainsLoop_sub 0 rest)
  | fuel + 1, doms => by
    simp only [pruneDomainsLoop]
    by_cases hEq : (domainCard (pruneOneRound doms) == domainCard doms) = true
    · simp only [hEq, ↓reduceIte]
      exact pruneDomainsLoop_sub 0 doms
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      exact forall2_sub_trans (pruneOneRoundAux_sub doms doms)
        (pruneDomainsLoop_sub fuel (pruneOneRound doms))

/-- Non-trivial inhabitedness witness for `negotiateSlots`: two coupled Author slots (`Codec` and
`Transport`) negotiating over shared `"wire" = "v1"` gluing tags when `Codec`'s top choice (`"v2"`)
is pruned by arc-consistency! -/
theorem negotiateSlots_inhabited :
    let ks : Obend.Kind.Kinds :=
      ⟨[{ name := "Codec", version := 1, layout := [], init := .natural 0,
          law := .boolean true, parents := [] },
        { name := "Transport", version := 1, layout := [], init := .natural 0,
          law := .boolean true, parents := [] }]⟩
    let I₀ : Obend.Intention Unit String String Unit String :=
      { ref := id
        supports := fun _ => [()]
        holds := fun _ _ => true
        resolve := fun _ r => .ok r
        resolve_ref := fun _ _ _ h => by cases h; rfl
        resolve_holds := fun _ _ _ _ _ _ => rfl }
    let ifaceA : OpenSlotInterface :=
      { slotId := "codec", expectedKind := "Codec", intentionRef := "codec@^1",
        budget := ⟨2⟩, fuel := 1, specTerm := .nat 7, peerDeps := [("transport", "wire")] }
    let ifaceB : OpenSlotInterface :=
      { slotId := "transport", expectedKind := "Transport", intentionRef := "transport@^1",
        budget := ⟨2⟩, fuel := 1, specTerm := .nat 9, peerDeps := [("codec", "wire")] }
    let candA_v2 : SlotCandidate String :=
      { candId := "codec-v2", slotId := "codec", kindPin := ⟨"Codec", 1, []⟩,
        intentionPin := "codec@^1", implTerm := .nat 7,
        gluingTags := [("wire", "v2")], sharedResourceIds := ["keccak-lut"] }
    let candA_v1 : SlotCandidate String :=
      { candId := "codec-v1", slotId := "codec", kindPin := ⟨"Codec", 1, []⟩,
        intentionPin := "codec@^1", implTerm := .nat 7,
        gluingTags := [("wire", "v1")], sharedResourceIds := ["keccak-lut"] }
    let candB_v1 : SlotCandidate String :=
      { candId := "transport-v1", slotId := "transport", kindPin := ⟨"Transport", 1, []⟩,
        intentionPin := "transport@^1", implTerm := .nat 9,
        gluingTags := [("wire", "v1")], sharedResourceIds := ["keccak-lut"] }
    let res := negotiateSlots ks I₀ () [⟨ifaceA, [candA_v2, candA_v1]⟩, ⟨ifaceB, [candB_v1]⟩]
    res = .ok ⟨[⟨ifaceA, candA_v1⟩, ⟨ifaceB, candB_v1⟩], 1⟩ := by
  dsimp only
  simp (config := { decide := true }) [negotiateSlots, buildLocalDomains, domainCard,
    pruneDomainsLoop, pruneOneRound, pruneOneRoundAux, findEmptyDomain,
    searchConsistentWith, searchConsistentWith.tryCands]

theorem relList_map_iface {Pin : Type} :
    ∀ {proposals : List (SlotProposal Pin)} {bs : List (BoundSlot Pin)},
      RelList (fun prop b => b.iface = prop.iface ∧ b.cand ∈ prop.candidates) proposals bs →
      bs.map (·.iface) = proposals.map (·.iface)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons ⟨hIf, _⟩ hTail => by
    simp [hIf, relList_map_iface hTail]

theorem eq_of_mem_nodup_map {α β : Type} {f : α → β} :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b
  | [], _, a, ha, _, _, _ => nomatch ha
  | _ :: xs, hnd, a, ha, b, hb, hfeq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exfalso; exact hnd.1 (hfeq ▸ List.mem_map_of_mem hb')
    · exfalso; exact hnd.1 (hfeq.symm ▸ List.mem_map_of_mem ha')
    · exact eq_of_mem_nodup_map hnd.2 a ha' b hb' hfeq

/-- Constructive per-slot Clairvoyant witness-cost accounting across every bound slot in a realizer:
produces a 1-to-1 cost list `slotCosts` where each `kᵢ` is an actual `CV bᵢ.cand.implTerm vᵢ kᵢ`
evaluation cost `≤ bᵢ.iface.budget.grade`, and `slotCosts.foldr (· + ·) 0 ≤ totalDeclaredSlotBudget bs`. -/
theorem bindings_clairvoyant_budget_conserved {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W} :
    ∀ {bs : List (BoundSlot Pin)},
      (∀ b ∈ bs, checkCandidateLocal ks I w b.iface b.cand = true) →
      ∃ slotCosts : List Nat,
        RelList (fun b k => ∃ v, Obend.Equiv.CV b.cand.implTerm v k ∧ k ≤ b.iface.budget.grade)
          bs slotCosts ∧
        slotCosts.foldr (· + ·) 0 ≤ totalDeclaredSlotBudget bs ∧
        ∀ b ∈ bs, Obend.Equiv.CostAtMost b.cand.implTerm b.iface.budget.grade
  | [], _ => ⟨[], .nil, Nat.le_refl 0, fun _ hm => by cases hm⟩
  | b :: bs, hall => by
    have hb := checkCandidateLocal_sound (hall b List.mem_cons_self)
    obtain ⟨v, ki, _, hCV, _, hkiLe, hCostAtMost⟩ := hb.2.2.2.2.2.2
    obtain ⟨restCosts, hRelRest, hRestLe, hRestCost⟩ :=
      bindings_clairvoyant_budget_conserved (fun b' hb' => hall b' (List.mem_cons_of_mem _ hb'))
    refine ⟨ki :: restCosts, .cons ⟨v, hCV, hkiLe⟩ hRelRest, ?_, ?_⟩
    · simp only [List.foldr_cons, totalDeclaredSlotBudget]
      omega
    · intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'Tail
      · exact hCostAtMost
      · exact hRestCost b' hb'Tail

/-- **Main Theorem (`negotiateSlots_converges_and_conserves_budget`)**:
Whenever multi-party slot negotiation succeeds (`negotiateSlots ks I w proposals = .ok realizer`):
1. **Bounded Monotone Convergence**: Domain pruning converged to an arc-consistent fixed point in
   `realizer.roundsUsed ≤ domainCard (proposals.map ...)` steps ($\le \sum_i |\text{cands}_i|$).
2. **Exact Interface & Candidate Membership**: `realizer.bindings` matches `proposals` 1-to-1, choosing
   each bound candidate from its proposal's candidate list.
3. **Certified `Kind` + `Intention` + `SupportSheaf` + `Equiv.Cost` + Dependency Closure**: Every bound slot
   satisfies `checkCandidateLocal ks I w b.iface b.cand = true`, `realizerGraphValid realizer.bindings = true`,
   `allPairsGluingCompatible`, and `SupportSheaf.usable (intentionRealizerSupportSheaf I) w realizer = true`.
4. **Compositional Budget Conservation & Subadditivity**: Per-slot Clairvoyant witness costs `slotCosts`
   satisfy `CV b.cand.implTerm v k ∧ k ≤ b.iface.budget.grade` with sum `≤ totalDeclaredSlotBudget realizer.bindings`,
   and glued shared-resource cost is subadditive (`gluedSharedResourceCost ≤ ungluedResourceCost`). -/
theorem negotiateSlots_converges_and_conserves_budget {W Pin Fact Err : Type} [DecidableEq Fact]
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {proposals : List (SlotProposal Pin)} {realizer : IntentionRealizer Pin}
    (costOf : String → Nat)
    (hNeg : negotiateSlots ks I w proposals = .ok realizer) :
    realizer.roundsUsed ≤ domainCard (proposals.map fun p => (p.iface, p.candidates)) ∧
    RelList (fun prop b => b.iface = prop.iface ∧ b.cand ∈ prop.candidates)
      proposals realizer.bindings ∧
    (∀ b ∈ realizer.bindings, checkCandidateLocal ks I w b.iface b.cand = true) ∧
    realizerGraphValid realizer.bindings = true ∧
    allPairsGluingCompatible realizer.bindings = true ∧
    (intentionRealizerSupportSheaf I).usable w realizer = true ∧
    (∃ slotCosts : List Nat,
      RelList (fun b k => ∃ v, Obend.Equiv.CV b.cand.implTerm v k ∧ k ≤ b.iface.budget.grade)
        realizer.bindings slotCosts ∧
      slotCosts.foldr (· + ·) 0 ≤ totalDeclaredSlotBudget realizer.bindings ∧
      ∀ b ∈ realizer.bindings, Obend.Equiv.CostAtMost b.cand.implTerm b.iface.budget.grade) ∧
    gluedSharedResourceCost costOf realizer.bindings ≤
      ungluedResourceCost costOf realizer.bindings := by
  unfold negotiateSlots at hNeg
  by_cases hBadGraph : (!slotGraphWellFormed (proposals.map (·.iface))) = true
  · simp [hBadGraph] at hNeg
  · simp only [hBadGraph, Bool.false_eq_true, ↓reduceIte] at hNeg
    have hPropGraph : slotGraphWellFormed (proposals.map (·.iface)) = true := by
      cases hg : slotGraphWellFormed (proposals.map (·.iface))
      · simp [hg] at hBadGraph
      · rfl
    cases hLocal : buildLocalDomains ks I w proposals <;> rw [hLocal] at hNeg
    · cases hNeg
    · rename_i localDoms
      obtain ⟨hF2Local, hCardLocal⟩ := buildLocalDomains_sound hLocal
      have hConv := pruneDomainsLoop_converges (domainCard localDoms) localDoms (Nat.le_refl _)
      have hSubPrune := pruneDomainsLoop_sub (domainCard localDoms) localDoms
      dsimp only at hNeg
      cases hEmpty : findEmptyDomain (pruneDomainsLoop (domainCard localDoms) localDoms).1 <;>
        rw [hEmpty] at hNeg
      · cases hSearch :
            searchConsistentWith (fun _ => true)
              (pruneDomainsLoop (domainCard localDoms) localDoms).1 <;>
          rw [hSearch] at hNeg
        · cases hNeg
        · rename_i bindings
          cases hNeg
          obtain ⟨hF2Search, hOkTriv, hGlue⟩ := searchConsistentWith_sound _ _ bindings hSearch
          generalize hPrunedEq : (pruneDomainsLoop (domainCard localDoms) localDoms).1 = prunedDoms
            at hSubPrune hF2Search
          have hF2Pruned :
              RelList
                (fun prop d =>
                  d.1 = prop.iface ∧
                  ∀ c ∈ d.2, c ∈ prop.candidates ∧ checkCandidateLocal ks I w prop.iface c = true)
                proposals prunedDoms := by
            clear hPrunedEq hEmpty hF2Search hSearch hGlue hOkTriv bindings hConv hCardLocal hLocal hPropGraph hBadGraph
            induction hF2Local generalizing prunedDoms with
            | nil => cases hSubPrune; exact .nil
            | cons hHead hTail ih =>
              cases hSubPrune with
              | cons hSubHead hSubTail =>
                refine .cons ⟨hSubHead.1.trans hHead.1, fun c hc => hHead.2 c (hSubHead.2 c hc)⟩
                  (ih _ hSubTail)
          have hF2Final :
              RelList
                (fun prop b =>
                  b.iface = prop.iface ∧ b.cand ∈ prop.candidates ∧
                  checkCandidateLocal ks I w b.iface b.cand = true)
                proposals bindings := by
            clear hPrunedEq hEmpty hSearch hGlue hOkTriv hConv hCardLocal hLocal hSubPrune hF2Local hPropGraph hBadGraph
            induction hF2Pruned generalizing bindings with
            | nil => cases hF2Search; exact .nil
            | cons hHead hTail ih =>
              cases hF2Search with
              | cons hSHead hSTail =>
                obtain ⟨hMemC, hChkC⟩ := hHead.2 _ hSHead.2
                have hIfEq : _ = _ := hSHead.1.trans hHead.1
                exact .cons ⟨hIfEq, hMemC, hIfEq ▸ hChkC⟩ (ih _ hSTail)
          have hF2Weak :
              RelList (fun prop b => b.iface = prop.iface ∧ b.cand ∈ prop.candidates)
                proposals bindings := by
            clear hPrunedEq hEmpty hSearch hGlue hOkTriv hConv hCardLocal hLocal hSubPrune hF2Pruned hF2Search hF2Local hPropGraph hBadGraph
            induction hF2Final with
            | nil => exact .nil
            | cons hHead hTail ih => exact .cons ⟨hHead.1, hHead.2.1⟩ ih
          have hAllLocal : ∀ b ∈ bindings, checkCandidateLocal ks I w b.iface b.cand = true := by
            clear hPrunedEq hF2Weak hEmpty hSearch hGlue hOkTriv hConv hCardLocal hLocal hSubPrune hF2Pruned hF2Search hF2Local hPropGraph hBadGraph
            induction hF2Final with
            | nil => intro _ hm; cases hm
            | cons hHead hTail ih =>
              intro b hb
              rcases List.mem_cons.1 hb with rfl | hbTail
              · exact hHead.2.2
              · exact ih b hbTail
          have hSelfAll :
              (bindings.all fun b => directedGluingCompatible b.iface b.cand b.iface b.cand) = true :=
            List.all_eq_true.2 fun b hb => (checkCandidateLocal_self_gluing_sound (hAllLocal b hb)).2
          have hBindGraph : realizerGraphValid bindings = true := by
            simp only [realizerGraphValid, relList_map_iface hF2Weak, hPropGraph, hSelfAll, hGlue,
              Bool.and_self]
          have hSlotsUsable :
              (bindings.all fun b =>
                (I.slot b.iface.intentionRef).usable (I.holds w) b.cand.intentionPin) = true := by
            rw [List.all_eq_true]
            intro b hb
            exact (checkCandidateLocal_sound (hAllLocal b hb)).2.2.2.2.2.1
          have hSheafUsable :
              (intentionRealizerSupportSheaf I).usable w
                ⟨bindings, (pruneDomainsLoop (domainCard localDoms) localDoms).2⟩ = true := by
            show (realizerGraphValid bindings &&
              bindings.all fun b =>
                (I.slot b.iface.intentionRef).usable (I.holds w) b.cand.intentionPin) = true
            simp [hBindGraph, hSlotsUsable]
          exact ⟨Nat.le_trans hConv.2.1 hCardLocal, hF2Weak, hAllLocal, hBindGraph, hGlue,
            hSheafUsable, bindings_clairvoyant_budget_conserved hAllLocal,
            gluedSharedResourceCost_subadditive costOf bindings⟩
      · dsimp only at hNeg
        cases hNeg

/-! ### Deadlock-Free Completeness & Dependency Closure -/

theorem allPairs_symm_lookup {Pin : Type} :
    ∀ {wit : List (BoundSlot Pin)},
      allPairsGluingCompatible wit = true →
      ∀ b₁ ∈ wit, ∀ b₂ ∈ wit, b₁.iface.slotId ≠ b₂.iface.slotId →
        gluingCompatible b₁.iface b₁.cand b₂.iface b₂.cand = true
  | [], _, b₁, hb₁, _, _, _ => nomatch hb₁
  | b :: bs, hGlue, b₁, hb₁, b₂, hb₂, hNe => by
    simp only [allPairsGluingCompatible, Bool.and_eq_true] at hGlue
    obtain ⟨hHead, hTail⟩ := hGlue
    rw [compatWithAll, List.all_eq_true] at hHead
    rcases List.mem_cons.1 hb₁ with rfl | hb₁'
    · rcases List.mem_cons.1 hb₂ with rfl | hb₂'
      · exact absurd rfl hNe
      · exact hHead b₂ hb₂'
    · rcases List.mem_cons.1 hb₂ with rfl | hb₂'
      · rw [gluingCompatible_symm]
        exact hHead b₁ hb₁'
      · exact allPairs_symm_lookup hTail b₁ hb₁' b₂ hb₂' hNe

/-- **Dependency Closure Theorem (`realizerGraphValid_dependency_closure`)**:
Whenever `realizerGraphValid bs = true`, all bound `slotId`s are pairwise distinct (`Nodup`), and
every declared dependency `(peerId, tag) ∈ b.iface.peerDeps` (including self-edges!) resolves to a
**unique** bound slot `bPeer ∈ bs` carrying an identical concrete gluing tag value `some val`. -/
theorem realizerGraphValid_dependency_closure {Pin : Type}
    {bs : List (BoundSlot Pin)} (hValid : realizerGraphValid bs = true) :
    (bs.map (·.iface.slotId)).Nodup ∧
    ∀ b ∈ bs, ∀ dep ∈ b.iface.peerDeps,
      ∃ bPeer ∈ bs,
        bPeer.iface.slotId = dep.1 ∧
        (∀ b' ∈ bs, b'.iface.slotId = dep.1 → b' = bPeer) ∧
        ∃ val,
          lookupGluingTag b.cand.gluingTags dep.2 = some val ∧
          lookupGluingTag bPeer.cand.gluingTags dep.2 = some val := by
  simp only [realizerGraphValid, slotGraphWellFormed, List.map_map, Bool.and_eq_true] at hValid
  obtain ⟨⟨⟨hUniq, hClosed⟩, hSelfAll⟩, hPairs⟩ := hValid
  have hMapEq : (bs.map (OpenSlotInterface.slotId ∘ BoundSlot.iface)) = bs.map (·.iface.slotId) := rfl
  rw [hMapEq] at hUniq hClosed
  have hNodup : (bs.map (·.iface.slotId)).Nodup := (uniqueStrings_iff_nodup _).1 hUniq
  refine ⟨hNodup, fun b hb dep hDep => ?_⟩
  rw [List.all_eq_true] at hClosed hSelfAll
  have hbClosed := hClosed b.iface (List.mem_map_of_mem hb)
  rw [List.all_eq_true] at hbClosed
  have hContains := hbClosed dep hDep
  have hInIds : dep.1 ∈ bs.map (·.iface.slotId) := List.contains_iff_mem.1 hContains
  obtain ⟨bPeer, hbPeer, hPeerId⟩ := List.mem_map.1 hInIds
  have hUnique : ∀ b' ∈ bs, b'.iface.slotId = dep.1 → b' = bPeer :=
    fun b' hb' hb'Id => eq_of_mem_nodup_map hNodup b' hb' bPeer hbPeer (hb'Id.trans hPeerId.symm)
  refine ⟨bPeer, hbPeer, hPeerId, hUnique, ?_⟩
  have hDir : directedGluingCompatible b.iface b.cand bPeer.iface bPeer.cand = true := by
    by_cases hSame : b.iface.slotId = bPeer.iface.slotId
    · have hbEq : b = bPeer := eq_of_mem_nodup_map hNodup b hb bPeer hbPeer hSame
      subst hbEq
      exact hSelfAll b hb
    · have hSym := allPairs_symm_lookup hPairs b hb bPeer hbPeer hSame
      exact (Eq.mp (Bool.and_eq_true _ _) hSym).1
  unfold directedGluingCompatible at hDir
  rw [List.all_eq_true] at hDir
  have hEdge := hDir dep hDep
  have hBeq : (dep.1 == bPeer.iface.slotId) = true := beq_iff_eq.2 hPeerId.symm
  simp only [hBeq, ↓reduceIte] at hEdge
  cases hv1 : lookupGluingTag b.cand.gluingTags dep.2 <;>
    cases hv2 : lookupGluingTag bPeer.cand.gluingTags dep.2 <;>
    simp [hv1, hv2] at hEdge
  rename_i val₁ val₂
  exact ⟨val₁, rfl, congrArg some hEdge.symm⟩

theorem witness_hasSupportInAllPeers {Pin : Type}
    {allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))}
    {wit : List (BoundSlot Pin)}
    (hF2 : RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) allDoms wit)
    (hGlue : allPairsGluingCompatible wit = true)
    {b : BoundSlot Pin} (hb : b ∈ wit) :
    hasSupportInAllPeers allDoms b.iface b.cand = true := by
  unfold hasSupportInAllPeers
  rw [List.all_eq_true]
  have hEx : ∀ d ∈ allDoms, ∃ b' ∈ wit, b'.iface = d.1 ∧ b'.cand ∈ d.2 := by
    clear hGlue hb
    induction hF2 with
    | nil => intro _ hm; cases hm
    | cons hH hT ih =>
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd'
      · exact ⟨_, List.mem_cons_self, hH⟩
      · obtain ⟨b', hb', hEq⟩ := ih d hd'
        exact ⟨b', List.mem_cons_of_mem _ hb', hEq⟩
  intro d hd
  rcases d with ⟨iface', cs'⟩
  by_cases hSame : (iface'.slotId == b.iface.slotId) = true
  · simp [hSame]
  · simp only [hSame, Bool.false_eq_true, ↓reduceIte, List.any_eq_true]
    obtain ⟨b', hb'Mem, hb'If, hb'Cand⟩ := hEx (iface', cs') hd
    dsimp only at hb'If hb'Cand
    have hNe : b.iface.slotId ≠ b'.iface.slotId := by
      intro heq
      rw [hb'If] at heq
      exact hSame (beq_iff_eq.2 heq.symm)
    exact ⟨b'.cand, hb'Cand, hb'If ▸ allPairs_symm_lookup hGlue b hb b' hb'Mem hNe⟩

theorem witness_survives_pruneOneRoundAux {Pin : Type}
    {allDoms : List (OpenSlotInterface × List (SlotCandidate Pin))}
    {witAll : List (BoundSlot Pin)}
    (hF2All : RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) allDoms witAll)
    (hGlueAll : allPairsGluingCompatible witAll = true) :
    ∀ {doms : List (OpenSlotInterface × List (SlotCandidate Pin))}
      {wit : List (BoundSlot Pin)},
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) doms wit →
      (∀ b ∈ wit, b ∈ witAll) →
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2)
        (pruneOneRoundAux allDoms doms) wit
  | [], [], .nil, _ => .nil
  | (iface, cs) :: rest, b :: ws, .cons ⟨hIf, hMem⟩ hTail, hSub => by
    refine .cons ⟨hIf, List.mem_filter.2 ⟨hMem, ?_⟩⟩
      (witness_survives_pruneOneRoundAux hF2All hGlueAll hTail
        (fun x hx => hSub x (List.mem_cons_of_mem _ hx)))
    have hSupp := witness_hasSupportInAllPeers hF2All hGlueAll (hSub b List.mem_cons_self)
    rwa [hIf] at hSupp

theorem witness_survives_pruneDomainsLoop {Pin : Type} :
    ∀ (fuel : Nat) (doms : List (OpenSlotInterface × List (SlotCandidate Pin)))
      (wit : List (BoundSlot Pin)),
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) doms wit →
      allPairsGluingCompatible wit = true →
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2)
        (pruneDomainsLoop fuel doms).1 wit
  | 0, _, _, hF2, _ => hF2
  | fuel + 1, doms, wit, hF2, hGlue => by
    simp only [pruneDomainsLoop]
    by_cases hEq : (domainCard (pruneOneRound doms) == domainCard doms) = true
    · simp [hEq, hF2]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have hNext := witness_survives_pruneOneRoundAux hF2 hGlue hF2 (fun _ hx => hx)
      exact witness_survives_pruneDomainsLoop fuel (pruneOneRound doms) wit hNext hGlue

theorem findEmptyDomain_eq_none_of_witness {Pin : Type} :
    ∀ {doms : List (OpenSlotInterface × List (SlotCandidate Pin))}
      {wit : List (BoundSlot Pin)},
      RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) doms wit →
      findEmptyDomain doms = none
  | [], [], .nil => rfl
  | (iface, cs) :: rest, _ :: _, .cons ⟨_, hMem⟩ hTail => by
    have hNonEmpty : cs.isEmpty = false := by
      cases cs with
      | nil => cases hMem
      | cons _ _ => rfl
    simp [findEmptyDomain, hNonEmpty, findEmptyDomain_eq_none_of_witness hTail]

theorem buildLocalDomains_complete_of_witness {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W} :
    ∀ {proposals : List (SlotProposal Pin)} {wit : List (BoundSlot Pin)},
      RelList
        (fun prop b =>
          b.iface = prop.iface ∧ b.cand ∈ prop.candidates ∧
          checkCandidateLocal ks I w prop.iface b.cand = true)
        proposals wit →
      ∃ localDoms,
        buildLocalDomains ks I w proposals = .ok localDoms ∧
        RelList (fun d b => b.iface = d.1 ∧ b.cand ∈ d.2) localDoms wit
  | [], [], .nil => ⟨[], rfl, .nil⟩
  | prop :: rest, b :: ws, .cons ⟨hIf, hMem, hChk⟩ hTail => by
    obtain ⟨tailDoms, hTailOk, hTailF2⟩ := buildLocalDomains_complete_of_witness hTail
    have hInFilter : b.cand ∈ prop.candidates.filter (checkCandidateLocal ks I w prop.iface) :=
      List.mem_filter.2 ⟨hMem, hChk⟩
    have hNonEmpty :
        (prop.candidates.filter (checkCandidateLocal ks I w prop.iface)).isEmpty = false := by
      cases hList : prop.candidates.filter (checkCandidateLocal ks I w prop.iface) with
      | nil => rw [hList] at hInFilter; cases hInFilter
      | cons _ _ => rfl
    refine ⟨(prop.iface, prop.candidates.filter (checkCandidateLocal ks I w prop.iface)) :: tailDoms,
      ?_, .cons ⟨hIf, hInFilter⟩ hTailF2⟩
    simp [buildLocalDomains, hNonEmpty, hTailOk]

/-- **Deadlock-Free Completeness (`negotiateSlots_complete_no_deadlock`)**:
Whenever `proposals` has a well-formed slot graph (`slotGraphWellFormed`) and admits *any* valid
compatible realization `wit`, `negotiateSlots` never deadlocks or falsely refuses: it is guaranteed
to return `.ok realizer`. -/
theorem negotiateSlots_complete_no_deadlock {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {proposals : List (SlotProposal Pin)} {wit : List (BoundSlot Pin)}
    (hGraph : slotGraphWellFormed (proposals.map (·.iface)) = true)
    (hWit : RelList
      (fun prop b =>
        b.iface = prop.iface ∧ b.cand ∈ prop.candidates ∧
        checkCandidateLocal ks I w prop.iface b.cand = true)
      proposals wit)
    (hGlue : allPairsGluingCompatible wit = true) :
    ∃ realizer, negotiateSlots ks I w proposals = .ok realizer := by
  obtain ⟨localDoms, hBuild, hF2Local⟩ := buildLocalDomains_complete_of_witness hWit
  have hF2Pruned :=
    witness_survives_pruneDomainsLoop (domainCard localDoms) localDoms wit hF2Local hGlue
  have hNoEmpty := findEmptyDomain_eq_none_of_witness hF2Pruned
  obtain ⟨sol, hSearch⟩ :=
    searchConsistentWith_complete _ (fun _ => true) wit hF2Pruned (fun _ _ => rfl) hGlue
  refine ⟨⟨sol, (pruneDomainsLoop (domainCard localDoms) localDoms).2⟩, ?_⟩
  simp [negotiateSlots, hGraph, hBuild, hNoEmpty, hSearch]

/-- **Refusal Soundness (`negotiateSlots_refusal_sound`)**:
Whenever `negotiateSlots` returns `.error refusal`, either the declared slot graph is malformed
(`slotGraphWellFormed = false`) or no valid pairwise-gluing-compatible tuple of candidates satisfying
`checkCandidateLocal` exists anywhere in `proposals`. -/
theorem negotiateSlots_refusal_sound {W Pin Fact Err : Type}
    {ks : Obend.Kind.Kinds} {I : Obend.Intention W String Pin Fact Err} {w : W}
    {proposals : List (SlotProposal Pin)} {refusal : NegotiationRefusal}
    (hErr : negotiateSlots ks I w proposals = .error refusal) :
    ¬ (slotGraphWellFormed (proposals.map (·.iface)) = true ∧
      ∃ wit : List (BoundSlot Pin),
        RelList
          (fun prop b =>
            b.iface = prop.iface ∧ b.cand ∈ prop.candidates ∧
            checkCandidateLocal ks I w prop.iface b.cand = true)
          proposals wit ∧
        allPairsGluingCompatible wit = true) := by
  rintro ⟨hGraph, wit, hWit, hGlue⟩
  obtain ⟨realizer, hOk⟩ := negotiateSlots_complete_no_deadlock hGraph hWit hGlue
  rw [hErr] at hOk
  cases hOk

/-- **Strict Shared-Resource Savings Across Distinct Bound Slots (`gluedSharedResourceCost_lt_of_shared_bindings`)**:
Whenever two bound slots `b₁` and `b₂` in `b₁ :: b₂ :: rest` share a resource `r₀` with `0 < costOf r₀`,
the glued realization strictly saves budget over independent per-slot execution. -/
theorem gluedSharedResourceCost_lt_of_shared_bindings {Pin : Type}
    (costOf : String → Nat) (b₁ b₂ : BoundSlot Pin) (rest : List (BoundSlot Pin))
    {r₀ : String}
    (h₁ : r₀ ∈ b₁.cand.sharedResourceIds)
    (h₂ : r₀ ∈ b₂.cand.sharedResourceIds)
    (hpos : 0 < costOf r₀) :
    gluedSharedResourceCost costOf (b₁ :: b₂ :: rest) <
      ungluedResourceCost costOf (b₁ :: b₂ :: rest) := by
  unfold gluedSharedResourceCost
  rw [← sumResourceCosts_flatMap_eq_unglued costOf (b₁ :: b₂ :: rest)]
  simp only [List.flatMap_cons]
  have h₂' : r₀ ∈ b₂.cand.sharedResourceIds ++ List.flatMap (fun b => b.cand.sharedResourceIds) rest :=
    List.mem_append_left _ h₂
  have hLt := sumResourceCosts_dedup_lt_of_shared costOf h₁ h₂' hpos
  rwa [← sumResourceCosts_append] at hLt

/-- **Behavioral `Ahead` Horizon Bridge (`ahead_slot_refinement_bequiv`)**:
Author-to-Integrator `Obend.Equiv.Ahead` refinements induce full `BEquiv` contextual equivalence
transitively across multi-stage slot lowerings. -/
theorem ahead_slot_refinement_bequiv {impl mid spec : Obend.Core.Term.Term}
    (h₁ : Obend.Equiv.Ahead impl mid) (h₂ : Obend.Equiv.Ahead mid spec) :
    Obend.Equiv.BEquiv impl spec :=
  Obend.Equiv.BEquiv.trans (Obend.Equiv.bequiv_of_ahead h₁) (Obend.Equiv.bequiv_of_ahead h₂)

theorem pickMinCost_zero_const {Cand : Type} :
    ∀ (cs : List Cand) (best : Cand), pickMinCost (fun _ => 0) best cs = best
  | [], best => rfl
  | _ :: cs, best => by
    simp only [pickMinCost, Nat.lt_irrefl, ↓reduceIte]
    exact pickMinCost_zero_const cs best

/-- **Uncoupled Singleton Priority Agreement (`negotiateSlots_singleton_agrees_prioritySelect`)**:
On a single uncoupled slot (`iface.peerDeps = []`), `negotiateSlots` succeeds iff `prioritySelect`
over the induced local-contract `Slot` finds a usable candidate, selecting the exact same
top-priority Integrator choice. -/
theorem negotiateSlots_singleton_agrees_prioritySelect {W Pin Fact Err : Type}
    (ks : Obend.Kind.Kinds) (I : Obend.Intention W String Pin Fact Err) (w : W)
    (iface : OpenSlotInterface) (cands : List (SlotCandidate Pin))
    (hUncoupled : iface.peerDeps = []) :
    let localSlot : Slot Fact (SlotCandidate Pin) :=
      { supports := fun _ => []
        judge := checkCandidateLocal ks I w iface }
    (negotiateSlots ks I w [⟨iface, cands⟩]).toOption.map (fun r => r.bindings.map BoundSlot.cand) =
      (prioritySelect localSlot (I.holds w) cands).toOption.map (fun c => [c]) := by
  dsimp only
  have hGraph : slotGraphWellFormed [iface] = true := by
    simp [slotGraphWellFormed, uniqueStrings, hUncoupled]
  unfold negotiateSlots buildLocalDomains prioritySelect Slot.alternatives
  simp only [List.map_cons, List.map_nil, hGraph, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hEqPred :
      ({ supports := fun _ => ([] : List Fact)
         judge := checkCandidateLocal ks I w iface } : Slot Fact (SlotCandidate Pin)).usable
        (I.holds w) = checkCandidateLocal ks I w iface := by
    funext c
    simp [Slot.usable, Slot.dead]
  rw [hEqPred]
  cases hFilt : cands.filter (checkCandidateLocal ks I w iface) with
  | nil =>
    simp [Except.toOption]
  | cons c cs =>
    have hPruneId :
        ∀ n, pruneDomainsLoop n [(iface, c :: cs)] = ([(iface, c :: cs)], 0) := by
      intro n
      cases n with
      | zero => rfl
      | succ m =>
        have hFilterId :
            (c :: cs).filter (hasSupportInAllPeers [(iface, c :: cs)] iface) = c :: cs := by
          rw [List.filter_eq_self]
          intro x _
          simp [hasSupportInAllPeers]
        simp [pruneDomainsLoop, pruneOneRound, pruneOneRoundAux, hFilterId, domainCard]
    simp only [buildLocalDomains, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [hPruneId]
    simp [findEmptyDomain, searchConsistentWith, searchConsistentWith.tryCands,
      pickMinCost_zero_const, Except.toOption]

end Budget

end Obend.Slot

end
