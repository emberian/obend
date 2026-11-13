module
/-
# Obend.Spec.CrossPackage — Cross-Package Open Recursion (`OB5` / `LT5`) & Per-Slot Proof/Specialization Survival

Formalizes Faré's `OB5` / `LT5` open-recursion modularity requirements across package boundaries:
1. `overlayModifiedFields` and `linkComposition`: linking a child package's override layer `L`
   onto a base package's open-recursive composition `C`.
2. `symUnfold_linkComposition_of_not_mem`: any member `m ∉ overlayModifiedFields L` of a non-flat
   overlay `L` preserves its exact symbolic unfolding (`symUnfold`), winning provenance layer
   (`provenance`), and specialization cone pin (`memberConePin`) under `linkComposition C L`.
3. `crossPackage_disjoint_override_preserves_transportedSlot_and_specSlot`: when a cross-package
   override layer `L` modifies only fields disjoint from a slot's read-support cone
   `slotReadCone C member` and a `TransportCert`'s method supports, BOTH the per-slot specialized
   code (`Candidate.slotBook` in `specSlot`) AND the transported proof certificate (`transportSlot`)
   remain `.usable` across the package boundary without re-running `checkL` or re-emitting the slot.
4. `crossPackage_intersecting_override_pinpoints_stale`: when a cross-package override modifies a
   member `m ∈ slotReadCone C member` (or a supported method in `c.supports`), the slot read
   transitions to `.blocked` and names the exact invalidated pin `memberConePin C m`
   (and `methodSupport m providerLayer f_lean`).
-/
public import Obend.Leaf.Specialize
public import Obend.Lower.Transport
public import Obend.Equiv.Clairvoyant
public import Obend.Tactic.Tooth
@[expose] public section
namespace Obend.Spec.CrossPackage
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
set_option autoImplicit false

/-- The list of member names modified (provided) by an overlay layer `L`. -/
def overlayModifiedFields (L : Layer) : List String :=
  L.fields.map Prod.fst

/-- Link a cross-package override layer `L` on top of an existing open-recursive composition `C`. -/
def linkComposition (C : Composition) (L : Layer) : Composition where
  top := L
  below := C.layers
  seed := C.seed

/-- Descriptor for a cross-package open-recursive link (`OB5` / `LT5`) between a base package
composition `baseComp` and a child package's overlay layer `overlay`. -/
structure CrossPackageLink where
  basePkg : String
  childPkg : String
  objectName : String
  member : String
  baseComp : Composition
  overlay : Layer
  defItem : LeafDef
  transportObj : TransportObj
  transportCert : TransportCert

namespace CrossPackageLink

/-- The linked cross-package composition `linkComposition lnk.baseComp lnk.overlay`. -/
def linkedComp (lnk : CrossPackageLink) : Composition :=
  linkComposition lnk.baseComp lnk.overlay

/-- The per-slot specialization candidate for `lnk.member` pinned only to its read-support cone. -/
def slotCandidate (lnk : CrossPackageLink) : Candidate :=
  .slotBook lnk.objectName lnk.member lnk.baseComp lnk.defItem

end CrossPackageLink

/-- If `m ∉ overlayModifiedFields L`, then `L.provides m = false`. -/
theorem provides_false_of_not_mem_overlayModifiedFields {L : Layer} {m : String}
    (hnot : m ∉ overlayModifiedFields L) :
    L.provides m = false := by
  simp only [Layer.provides, List.any_eq_false]
  intro f hf hfm
  have hmem : f.1 ∈ overlayModifiedFields L := List.mem_map.2 ⟨f, hf, rfl⟩
  have heq : f.1 = m := beq_iff_eq.1 hfm
  rw [heq] at hmem
  exact hnot hmem

/-- In a non-flat cross-package overlay `L`, any member `m ∉ overlayModifiedFields L` has the
exact same `flatRow` entry in `linkComposition C L` as in `C`. -/
theorem flatRow_find_linkComposition_of_not_mem (C : Composition) (L : Layer) (m : String)
    (hflat : L.flat = false) (hnot : m ∉ overlayModifiedFields L) :
    (flatRow (linkComposition C L).seed (linkComposition C L).layers).find? (·.1 == m) =
    (flatRow C.seed C.layers).find? (·.1 == m) := by
  have hn : L.provides m = false := provides_false_of_not_mem_overlayModifiedFields hnot
  simp only [linkComposition, Composition.layers, flatRow, hflat, Bool.false_eq_true, ite_false]
  rw [find_extendFields, find_mapFields_none _ (body_none hn)]

/-- **`symUnfold_linkComposition_of_not_mem` (`OB5` Frame Invariance for Unmodified Members)**:
If a cross-package overlay layer `L` is non-flat (`L.flat = false`) and does not modify `m`
(`m ∉ overlayModifiedFields L`), then linking `L` onto `C` preserves:
1. the symbolic unfolding `(linkComposition C L).symUnfold m = C.symUnfold m`,
2. the winning provenance layer `(linkComposition C L).provenance m = C.provenance m`, and
3. the per-member specialization pin `memberConePin (linkComposition C L) m = memberConePin C m`. -/
theorem symUnfold_linkComposition_of_not_mem (C : Composition) (L : Layer) (m : String)
    (hflat : L.flat = false) (hnot : m ∉ overlayModifiedFields L) :
    (linkComposition C L).symUnfold m = C.symUnfold m ∧
    (linkComposition C L).provenance m = C.provenance m ∧
    memberConePin (linkComposition C L) m = memberConePin C m := by
  have hn : L.provides m = false := provides_false_of_not_mem_overlayModifiedFields hnot
  have hfind := flatRow_find_linkComposition_of_not_mem C L m hflat hnot
  have hsym : (linkComposition C L).symUnfold m = C.symUnfold m := by
    simp only [Composition.symUnfold, hfind]
  have hprov : (linkComposition C L).provenance m = C.provenance m := by
    simp only [Composition.provenance, linkComposition, Composition.layers, provLayers,
      hn, hflat, Bool.false_eq_true, ite_false]
  have hpin : memberConePin (linkComposition C L) m = memberConePin C m := by
    simp only [memberConePin, hprov, hsym]
  exact ⟨hsym, hprov, hpin⟩

/-- If every member `m ∈ cone` is disjoint from `overlayModifiedFields L`, then `coneSupports`
at `linkComposition C L` is identical to `coneSupports` at `C`. -/
theorem coneSupports_linkComposition_of_disjoint (C : Composition) (L : Layer) (cone : List String)
    (hflat : L.flat = false) (hdisj : ∀ m ∈ cone, m ∉ overlayModifiedFields L) :
    coneSupports (linkComposition C L) cone = coneSupports C cone := by
  unfold coneSupports
  apply List.map_congr_left
  intro m hm
  exact (symUnfold_linkComposition_of_not_mem C L m hflat (hdisj m hm)).2.2

/-- When `L` does not collide with key `k` and `splitScopedLayerKey k` resolves a member
`m' ∉ overlayModifiedFields L`, `resolveLayerDecl (linkComposition C L) k = resolveLayerDecl C k`. -/
theorem resolveLayerDecl_linkComposition_of_not_mem
    (C : Composition) (L : Layer) (k : String)
    (hflat : L.flat = false)
    (hlname : (L.name == k) = false)
    (hsplit : ∀ prov m', splitScopedLayerKey k = some (prov, m') → m' ∉ overlayModifiedFields L) :
    resolveLayerDecl (linkComposition C L) k = resolveLayerDecl C k := by
  have hlayers : (linkComposition C L).layers = L :: C.layers := rfl
  unfold resolveLayerDecl
  rw [hlayers, List.find?_cons, hlname]
  cases (C.layers.find? (·.name == k)).map Layer.code with
  | some c => rfl
  | none =>
    cases hsk : splitScopedLayerKey k with
    | none => rfl
    | some pm =>
      obtain ⟨prov, m'⟩ := pm
      have hm' : m' ∉ overlayModifiedFields L := hsplit prov m' hsk
      have ⟨hsym', hprov', _⟩ := symUnfold_linkComposition_of_not_mem C L m' hflat hm'
      simp only [hprov', hsym']

/-- When `L` does not collide with the scoped key `C.provenance m ++ "." ++ m` and `splitScopedLayerKey`
resolves `m' ∉ overlayModifiedFields L`, `holdsAt` on `memberConePin C m` is invariant between
`viewOf k objectName (linkComposition C L)` and `viewOf k objectName C`. -/
theorem holdsAt_viewOf_linkComposition_of_not_mem
    (k : Nat) (objectName : String) (C : Composition) (L : Layer) (m : String)
    (hflat : L.flat = false)
    (hlname : (L.name == C.provenance m ++ "." ++ m) = false)
    (hsplit : ∀ prov m',
      splitScopedLayerKey (C.provenance m ++ "." ++ m) = some (prov, m') →
      m' ∉ overlayModifiedFields L) :
    holdsAt (viewOf k objectName (linkComposition C L)) (memberConePin C m) =
    holdsAt (viewOf k objectName C) (memberConePin C m) := by
  rw [holdsAt_eq, holdsAt_eq]
  simp only [viewOf, memberConePin,
    resolveLayerDecl_linkComposition_of_not_mem C L (C.provenance m ++ "." ++ m) hflat hlname hsplit]

/-- **`crossPackage_disjoint_override_preserves_transportedSlot_and_specSlot` (`OB5` / `LT5`)**:
When a cross-package override layer `L` (`L.flat = false`) modifies only fields disjoint from
`slotReadCone C member` and preserves `Obend.Logic.symUnfold` on `c.supports`:
1. every member in `slotReadCone C member` preserves its symbolic unfolding and provenance in `linkComposition C L`,
2. the cone support pins `coneSupports (linkComposition C L) (slotReadCone C member)` equal `coneSupports C (slotReadCone C member)`,
3. `Candidate.slotBook objectName member C defItem` remains `.usable` in `specSlot` under any view `v'` agreeing with `v` on the cone pins, and
4. `c : TransportCert` remains `.usable` in `transportSlot o` at `linkComposition C L` and preserves `TransportMeaning o c` without re-running `checkL`. -/
theorem crossPackage_disjoint_override_preserves_transportedSlot_and_specSlot
    {objectName member : String} {C : Composition} {L : Layer} {defItem : LeafDef}
    {v v' : LeafView} {o : TransportObj} {c : TransportCert} {s : Nat}
    (hflat : L.flat = false)
    (hcone_disj : ∀ m ∈ slotReadCone C member, m ∉ overlayModifiedFields L)
    (hview_agree : ∀ m ∈ slotReadCone C member,
      holdsAt v' (memberConePin C m) = holdsAt v (memberConePin C m))
    (hspec_us : specSlot.usable (holdsAt v) (.slotBook objectName member C defItem) = true)
    (htrans_us : (transportSlot o).usable (Support.holds C s) c = true)
    (htrans_disj : ∀ sp ∈ c.supports,
      Obend.Logic.symUnfold (linkComposition C L) s sp.member = Obend.Logic.symUnfold C s sp.member) :
    (∀ m ∈ slotReadCone C member,
      (linkComposition C L).symUnfold m = C.symUnfold m ∧
      (linkComposition C L).provenance m = C.provenance m) ∧
    coneSupports (linkComposition C L) (slotReadCone C member) =
      coneSupports C (slotReadCone C member) ∧
    specSlot.usable (holdsAt v') (.slotBook objectName member C defItem) = true ∧
    (transportSlot o).usable (Support.holds (linkComposition C L) s) c = true ∧
    TransportMeaning o c := by
  have hcone_inv : ∀ m ∈ slotReadCone C member,
      (linkComposition C L).symUnfold m = C.symUnfold m ∧
      (linkComposition C L).provenance m = C.provenance m := by
    intro m hm
    have h := symUnfold_linkComposition_of_not_mem C L m hflat (hcone_disj m hm)
    exact ⟨h.1, h.2.1⟩
  have hpins_eq : coneSupports (linkComposition C L) (slotReadCone C member) =
      coneSupports C (slotReadCone C member) :=
    coneSupports_linkComposition_of_disjoint C L (slotReadCone C member) hflat hcone_disj
  obtain ⟨hj, hall⟩ := (usable_iff specSlot (holdsAt v) (.slotBook objectName member C defItem)).1 hspec_us
  have hall' : ∀ p ∈ (Candidate.slotBook objectName member C defItem).supports, holdsAt v' p = true := by
    intro p hp
    simp only [Candidate.supports, coneSupports, List.mem_map] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    rw [hview_agree m hm]
    exact hall (memberConePin C m) (by
      simp only [ specSlot, Candidate.supports, coneSupports, List.mem_map]
      exact ⟨m, hm, rfl⟩)
  have hspec_us' : specSlot.usable (holdsAt v') (.slotBook objectName member C defItem) = true :=
    (usable_iff specSlot (holdsAt v') (.slotBook objectName member C defItem)).2 ⟨hj, hall'⟩
  have htrans := transportSlot_usable_of_disjoint_overlay htrans_us htrans_disj
  exact ⟨hcone_inv, hpins_eq, hspec_us', htrans.1, htrans.2.1⟩

/-- **`crossPackage_intersecting_override_pinpoints_stale` (`OB5` / `LT5` Negative Counterpart)**:
When a cross-package override modifies a member `m ∈ slotReadCone C member` so that its cone pin
`memberConePin C m` no longer holds at `v'` (`holdsAt v' (memberConePin C m) = false`), AND
overrides a method support `methodSupport m provLayer f_lean ∈ c.supports` with a body `u` where
`termEq u (lowerT f_lean) = false`:
1. `specSlot.read` on `Candidate.slotBook objectName member C defItem` returns `.blocked` and names
   `memberConePin C m` in the dead pin list, and
2. `(transportSlot o).read` on `c` at `linkComposition C L` returns `.blocked` and names
   `methodSupport m provLayer f_lean` in the dead support list. -/
theorem crossPackage_intersecting_override_pinpoints_stale
    {objectName member : String} {C : Composition} {L : Layer} {defItem : LeafDef}
    {v' : LeafView} {o : TransportObj} {c : TransportCert} (s : Nat)
    (m provLayer newLayer : String) (f_lean : LExpr) (u : Term)
    (hcl : C.closedB = true)
    (hm_cone : m ∈ slotReadCone C member)
    (hpin_dead : holdsAt v' (memberConePin C m) = false)
    (hok : transportCheck 0 o c = .ok)
    (hmem_sup : methodSupport m provLayer f_lean ∈ c.supports)
    (hunf : Obend.Logic.symUnfold (linkComposition C L) s m = some (newLayer, u))
    (hdiff : Obend.Law.termEq u (lowerT f_lean) = false) :
    (∃ deadPins,
      specSlot.read (holdsAt v') (some (.slotBook objectName member C defItem)) =
        .blocked (.slotBook objectName member C defItem) deadPins ∧
      memberConePin C m ∈ deadPins) ∧
    (∃ deadSupports,
      (transportSlot o).read (Support.holds (linkComposition C L) s) (some c) =
        .blocked c deadSupports ∧
      methodSupport m provLayer f_lean ∈ deadSupports) := by
  have hp_mem : memberConePin C m ∈ (Candidate.slotBook objectName member C defItem).supports := by
    simp only [Candidate.supports, coneSupports, List.mem_map]
    exact ⟨m, hm_cone, rfl⟩
  obtain ⟨deadPins, hread, hmem_dead, _⟩ := slotBook_moved_pin_blocks hcl hp_mem hpin_dead
  have htrans_blocked :=
    transportSlot_blocked_on_override (linkComposition C L) s m provLayer newLayer f_lean u
      hok hmem_sup hunf hdiff
  exact ⟨⟨deadPins, hread, hmem_dead⟩, htrans_blocked⟩

/-! ## Bisimilar / Clairvoyant Intersecting Overrides (`EquivOverrideCert`, `rebindEquivPin`) -/

/-- Context composition for `instantiate`: plugging `F[X]` into `C` equals plugging `X` into `compContext C F`. -/
def compContext (C F : Term) : Term :=
  C.substitute (fun
    | 0 => F
    | k + 1 => .bound (k + 1))

theorem instantiate_compContext (C F X : Term) :
    instantiate (compContext C F) X = instantiate C (instantiate F X) := by
  simp only [compContext, instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ k => simp [single]

/-- Observational equivalence (`≈b`) is a congruence under any 1-hole context `instantiate Frame ·`. -/
theorem bEquiv_instantiate (Frame : Term) {u1 u2 : Term} (h : u1 ≈b u2) :
    instantiate Frame u1 ≈b instantiate Frame u2 := by
  intro ρ C
  have hFrame1 : (instantiate Frame u1).substitute ρ =
      instantiate (Frame.substitute (liftSubstitution ρ)) (u1.substitute ρ) := by
    simp only [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
    congr 1
    funext i
    cases i with
    | zero => simp [single, liftSubstitution]
    | succ k =>
      simp [liftSubstitution, single, Obend.Core.TermTraverse.rename_substitute, substitute_bound]
  have hFrame2 : (instantiate Frame u2).substitute ρ =
      instantiate (Frame.substitute (liftSubstitution ρ)) (u2.substitute ρ) := by
    simp only [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
    congr 1
    funext i
    cases i with
    | zero => simp [single, liftSubstitution]
    | succ k =>
      simp [liftSubstitution, single, Obend.Core.TermTraverse.rename_substitute, substitute_bound]
  rw [hFrame1, hFrame2, ← instantiate_compContext, ← instantiate_compContext]
  exact h ρ (compContext C (Frame.substitute (liftSubstitution ρ)))

/-- Certificate witnessing that an intersecting cross-package override `L` modifies helper method `m`
to an observationally equivalent (`≈b`) implementation:
1. `(linkComposition C L).symUnfold m ≈b C.symUnfold m` (symbolic unfolding equivalence), and
2. `.get (linkComposition C L).object m ≈b .get C.object m` (runtime object projection equivalence). -/
structure EquivOverrideCert (C : Composition) (L : Layer) (m : String) where
  newCode : Term := (linkComposition C L).symUnfold m
  newCode_eq : newCode = (linkComposition C L).symUnfold m := by rfl
  symUnfold_bEquiv : (linkComposition C L).symUnfold m ≈b C.symUnfold m
  get_bEquiv : .get (linkComposition C L).object m ≈b .get C.object m

/-- Construct an `EquivOverrideCert C L m` from Clairvoyant dead-let elimination (`deadLetBind deadExpr body → body`),
together with a strict Clairvoyant heap/step cost reduction witness (`k < k + 2`). -/
def clairvoyantDeadLetEquivOverrideCert
    (C : Composition) (L : Layer) (m : String) (deadExpr body : Term)
    (hsym_base : C.symUnfold m = deadLetBind deadExpr body)
    (hsym_link : (linkComposition C L).symUnfold m = body)
    (hget_base : Steps (.get C.object m) (deadLetBind deadExpr body))
    (hget_link : Steps (.get (linkComposition C L).object m) body) :
    EquivOverrideCert C L m where
  newCode := body
  newCode_eq := hsym_link.symm
  symUnfold_bEquiv := by
    rw [hsym_base, hsym_link]
    exact (clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper deadExpr body).1.symm
  get_bEquiv := by
    have h1 : .get (linkComposition C L).object m ≈b body := bequiv_of_steps hget_link
    have h2 : body ≈b deadLetBind deadExpr body :=
      (clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper deadExpr body).1.symm
    have h3 : deadLetBind deadExpr body ≈b .get C.object m := (bequiv_of_steps hget_base).symm
    exact h1.trans (h2.trans h3)

/-- Re-pin a `LeafPin` `p` for member `m` using an `EquivOverrideCert C L m`:
replaces `memberConePin C m` with the equivalence-certified pin `memberConePin (linkComposition C L) m`. -/
def rebindEquivPin {C : Composition} {L : Layer} {m : String}
    (_cert : EquivOverrideCert C L m) (p : LeafPin) : LeafPin :=
  if p.cell == (memberConePin C m).cell && Obend.Law.termEq p.code (memberConePin C m).code then
    memberConePin (linkComposition C L) m
  else
    p

theorem rebindEquivPin_memberConePin {C : Composition} {L : Layer} {m : String}
    (cert : EquivOverrideCert C L m) :
    rebindEquivPin cert (memberConePin C m) = memberConePin (linkComposition C L) m := by
  simp [rebindEquivPin, Obend.Logic.termEq_refl']

/-- Re-pin a `Support` `sp` for overridden member `m` to its new equivalence-certified unfolding
at `(linkComposition C L, s)`. -/
def rebindEquivSupport {C : Composition} {L : Layer} {m : String}
    (_cert : EquivOverrideCert C L m) (s : Nat) (sp : Support) : Support :=
  if sp.member == m then
    ⟨m, Obend.Logic.symUnfold (linkComposition C L) s m⟩
  else
    sp

/-- Re-pin all supports of a `TransportCert` `c` using `rebindEquivSupport cert s`. -/
def rebindEquivTransportCert {C : Composition} {L : Layer} {m : String}
    (cert : EquivOverrideCert C L m) (s : Nat) (c : TransportCert) : TransportCert :=
  { c with supports := c.supports.map (rebindEquivSupport cert s) }

/-- Re-pin a `Candidate.slotBook` for `target` across an equivalence-certified override `cert`. -/
def rebindEquivSlotCandidate (objectName target : String) {C : Composition} {L : Layer} {m : String}
    (_cert : EquivOverrideCert C L m) (defItem : LeafDef) : Candidate :=
  .slotBook objectName target (linkComposition C L) defItem

theorem optEq_refl (x : Option (String × Term)) : optEq x x = true := by
  cases x with
  | none => rfl
  | some p =>
    obtain ⟨a, t⟩ := p
    simp [optEq, Obend.Logic.termEq_refl']

/-- **`crossPackage_bEquiv_override_preserves_semantics` (`OB5` / `LT5` Bisimilar Override Preservation)**:
When an intersecting cross-package override `L` modifies helper method `m ∈ slotReadCone C target`
and supplies `cert : EquivOverrideCert C L m`, any target method `target` whose body `Frame` reads
`self.m` preserves its exact observational meaning (`≈b`) across the package boundary:
1. `instantiate Frame ((linkComposition C L).symUnfold m) ≈b instantiate Frame (C.symUnfold m)`,
2. `.get (linkComposition C L).object target ≈b .get C.object target`, and
3. both objects halt with identical observations on `target`. -/
theorem crossPackage_bEquiv_override_preserves_semantics
    {C : Composition} {L : Layer} {m target : String}
    (cert : EquivOverrideCert C L m)
    (Frame : Term)
    (htarget_base : .get C.object target ≈b instantiate Frame (.get C.object m))
    (htarget_link : .get (linkComposition C L).object target ≈b
      instantiate Frame (.get (linkComposition C L).object m)) :
    (instantiate Frame ((linkComposition C L).symUnfold m) ≈b instantiate Frame (C.symUnfold m)) ∧
    (.get (linkComposition C L).object target ≈b .get C.object target) ∧
    (∀ obs : Observation,
      Halts (.get (linkComposition C L).object target) obs ↔ Halts (.get C.object target) obs) := by
  have hsym_frame : instantiate Frame ((linkComposition C L).symUnfold m) ≈b instantiate Frame (C.symUnfold m) :=
    bEquiv_instantiate Frame cert.symUnfold_bEquiv
  have hget_frame : instantiate Frame (.get (linkComposition C L).object m) ≈b
      instantiate Frame (.get C.object m) :=
    bEquiv_instantiate Frame cert.get_bEquiv
  have htarget_eq : .get (linkComposition C L).object target ≈b .get C.object target :=
    htarget_link.trans (hget_frame.trans htarget_base.symm)
  exact ⟨hsym_frame, htarget_eq, fun obs => htarget_eq.sameRuns.halts obs⟩

/-- **`crossPackage_bEquiv_rebinds_slot_usable` (`OB5` / `LT5` Equivalence-Certified Re-Pinning)**:
When an intersecting override `L` modifies `m ∈ slotReadCone C target` and supplies
`cert : EquivOverrideCert C L m`, re-pinning `m` to its new equivalence-certified hash via
`rebindEquivPin` (and `rebindEquivSlotCandidate` / `rebindEquivTransportCert`) restores
`specSlot.usable = true` and `transportSlot.usable = true` at `linkComposition C L` while
preserving `TransportMeaning o` and the exact observational meaning
`.get (linkComposition C L).object target ≈b .get C.object target`! -/
theorem crossPackage_bEquiv_rebinds_slot_usable
    {objectName target m : String} {C : Composition} {L : Layer} {defItem : LeafDef}
    {v' : LeafView} {o : TransportObj} {c : TransportCert} {s : Nat}
    (cert : EquivOverrideCert C L m)
    (Frame : Term)
    (htarget_base : .get C.object target ≈b instantiate Frame (.get C.object m))
    (htarget_link : .get (linkComposition C L).object target ≈b
      instantiate Frame (.get (linkComposition C L).object m))
    (hcl_link : (linkComposition C L).closedB = true)
    (hpin_m : holdsAt v' (rebindEquivPin cert (memberConePin C m)) = true)
    (hcone_rest : ∀ m' ∈ slotReadCone (linkComposition C L) target, m' ≠ m →
      holdsAt v' (memberConePin (linkComposition C L) m') = true)
    (htrans_us : (transportSlot o).usable (Support.holds C s) c = true)
    (htrans_rest : ∀ sp ∈ c.supports, sp.member ≠ m →
      Obend.Logic.symUnfold (linkComposition C L) s sp.member = Obend.Logic.symUnfold C s sp.member) :
    holdsAt v' (memberConePin (linkComposition C L) m) = true ∧
    specSlot.usable (holdsAt v') (rebindEquivSlotCandidate objectName target cert defItem) = true ∧
    (transportSlot o).usable (Support.holds (linkComposition C L) s) (rebindEquivTransportCert cert s c) = true ∧
    TransportMeaning o (rebindEquivTransportCert cert s c) ∧
    (.get (linkComposition C L).object target ≈b .get C.object target) := by
  have hpin_m' : holdsAt v' (memberConePin (linkComposition C L) m) = true := by
    rwa [rebindEquivPin_memberConePin cert] at hpin_m
  have hspec_all : ∀ p ∈ (rebindEquivSlotCandidate objectName target cert defItem).supports,
      holdsAt v' p = true := by
    intro p hp
    simp only [rebindEquivSlotCandidate, Candidate.supports, coneSupports, List.mem_map] at hp
    obtain ⟨m', hm', rfl⟩ := hp
    by_cases heq : m' = m
    · subst heq; exact hpin_m'
    · exact hcone_rest m' hm' heq
  have hspec_us : specSlot.usable (holdsAt v') (rebindEquivSlotCandidate objectName target cert defItem) = true :=
    (usable_iff specSlot (holdsAt v') (rebindEquivSlotCandidate objectName target cert defItem)).2
      ⟨hcl_link, hspec_all⟩
  obtain ⟨hj, hall⟩ := (usable_iff (transportSlot o) (Support.holds C s) c).1 htrans_us
  have hj' : (transportSlot o).judge (rebindEquivTransportCert cert s c) = true := hj
  have hall' : ∀ sp' ∈ (transportSlot o).supports (rebindEquivTransportCert cert s c),
      Support.holds (linkComposition C L) s sp' = true := by
    intro sp' hsp'
    simp only [transportSlot, rebindEquivTransportCert, List.mem_map] at hsp'
    obtain ⟨sp, hsp, rfl⟩ := hsp'
    unfold rebindEquivSupport
    by_cases hmem : (sp.member == m) = true
    · simp only [hmem, ite_true, Support.holds]
      exact optEq_refl _
    · simp only [hmem, Bool.false_eq_true, ite_false]
      have hne : sp.member ≠ m := fun he => by simp [he] at hmem
      have h1 := hall sp hsp
      have heq := htrans_rest sp hsp hne
      simpa only [Support.holds, heq] using h1
  have htrans_us' :
      (transportSlot o).usable (Support.holds (linkComposition C L) s) (rebindEquivTransportCert cert s c) = true :=
    (usable_iff (transportSlot o) (Support.holds (linkComposition C L) s) (rebindEquivTransportCert cert s c)).2
      ⟨hj', hall'⟩
  have hok' : transportCheck 0 o (rebindEquivTransportCert cert s c) = .ok := by
    simpa [transportSlot] using hj'
  have hmean' : TransportMeaning o (rebindEquivTransportCert cert s c) :=
    transportJudge.sound hok'
  have hsem := crossPackage_bEquiv_override_preserves_semantics cert Frame htarget_base htarget_link
  exact ⟨hpin_m', hspec_us, htrans_us', hmean', hsem.2.1⟩

end Obend.Spec.CrossPackage
end
