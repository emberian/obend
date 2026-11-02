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
@[expose] public section
namespace Obend.Spec.CrossPackage
open Obend.Core.Term
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

end Obend.Spec.CrossPackage
end
