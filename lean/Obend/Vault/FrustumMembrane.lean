module
import all Obend.Polis.BlumRam
/- Capability reachability, sealed-slot binding and ideal-oracle salt hiding, living screenshot
cuts, confined replay and atomic conserving regraft. ROM hiding is separate from cSHAKE binding. -/
public import Obend.Vault.Form
public import Obend.Polis.BlumRam
public section
namespace Obend.Vault.FrustumMembrane
set_option autoImplicit false
open Obend.Core.Data (Data)
open Obend.Spec.Law (Facts)
open Obend.Vault (natAt)
open Obend.Vault.Affordance (Auth fireGate fireGate_iff_subset GatedAffordance projectGatedFor)
open Obend.Vault.Rehydration (AttestedRoot Interaction InteractionLog confined Rehydration classify
  replayedDeterministic_iff_confined MembraneViewer Membrane.reshare reshare_some_attenuates)
open Obend.Vault.Form (NExpr PRef Known Agrees Assignment addN subN putNat eval_subst_peval)
open Obend.Crypto (cshake32ByteArray cshake32ByteArray_size encodeListField
  encodeListField_prefix_inj leb128 leb128_prefix_inj)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.HashBytes (CollisionAmong)
open Obend.Polis (cshake32_binds)
/-! ## 1. Sealed slots: a secret shown only as its commitment -/
/-- The cleartext of a sealed slot, held by the cell's owner. -/
structure SealedSlot where
  secret : List UInt8
  salt : List UInt8
deriving DecidableEq, Repr
/-- Customization string of the sealed-slot hash. -/
def sealCustomization : List UInt8 := "OBEND.VAULT.FRUSTUM.SEAL/v1".toUTF8.data.toList
/-- What is hashed: the secret and the salt, each length-framed. -/
def sealPreimage (s : SealedSlot) : List UInt8 :=
  encodeListField s.secret ++ encodeListField s.salt
/-- The 32-byte commitment a frustum shows in place of a sealed slot. -/
def sealCommit (s : SealedSlot) : ByteArray := cshake32ByteArray sealCustomization (sealPreimage s)
theorem sealPreimage_injective {s₁ s₂ : SealedSlot} (h : sealPreimage s₁ = sealPreimage s₂) :
    s₁ = s₂ := by
  unfold sealPreimage at h
  obtain ⟨h1, h2⟩ := encodeListField_prefix_inj h
  obtain ⟨h3, _⟩ := encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h2)
  cases s₁; cases s₂; simp_all
theorem sealCommit_size (s : SealedSlot) : (sealCommit s).size = 32 :=
  cshake32ByteArray_size _ _
/-- Equal commitments hide equal slots, or these two preimages collide under the seal hash. -/
theorem sealCommit_binds {s₁ s₂ : SealedSlot} (h : sealCommit s₁ = sealCommit s₂) :
    s₁ = s₂ ∨ CollisionAmong (cshake256Bytes sealCustomization)
      (fun x => x = sealPreimage s₁ ∨ x = sealPreimage s₂) :=
  (cshake32_binds sealCustomization h).imp sealPreimage_injective id
/-! ## 2. The world, and what a viewer may reach -/
abbrev CellId := String
/-- A capability: a target cell and the rights held over it. -/
structure Cap where
  target : CellId
  rights : List Auth
deriving DecidableEq, Repr
/-- A cell as its owner holds it. -/
structure CellRecord where
  state : Data
  sealed : List (String × SealedSlot) := []
  caps : List Cap := []
  surface : List (GatedAffordance Unit) := []
  epoch : Nat := 0
/-- The public face of a cell: its sealed slots are commitments. A frustum reads only this. -/
structure CellPub where
  state : Data
  sealed : List (String × ByteArray)
  caps : List Cap
  surface : List (GatedAffordance Unit)
  epoch : Nat
def CellRecord.pub (r : CellRecord) : CellPub :=
  { state := r.state, sealed := r.sealed.map fun e => (e.1, sealCommit e.2), caps := r.caps,
    surface := r.surface, epoch := r.epoch }
/-- A finite ledger of cells: every cell that exists is listed in `ids`. -/
structure World where
  ids : List CellId
  facts : Facts
  cell : CellId → Option CellRecord
  covered : ∀ c, (cell c).isSome = true → c ∈ ids
def World.pub (w : World) (c : CellId) : Option CellPub := (w.cell c).map CellRecord.pub
theorem World.mem_ids_of_pub {w : World} {c : CellId} (h : (w.pub c).isSome = true) : c ∈ w.ids :=
  w.covered c (by simpa [World.pub] using h)
theorem mem_keys_of_lookup {β : Type} : ∀ (l : List (CellId × β)) (c : CellId),
    (l.lookup c).isSome = true → c ∈ l.map (·.1)
  | [], _, h => by simp at h
  | (k, v) :: rest, c, h => by
    by_cases hk : c = k
    · subst hk; simp
    · have hne : (c == k) = false := by simpa using hk
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (mem_keys_of_lookup rest c h)
/-- A world from a list of cells; the first entry for an id is the cell. -/
def World.ofList (facts : Facts) (cells : List (CellId × CellRecord)) : World :=
  { ids := cells.map (·.1), facts := facts, cell := fun c => cells.lookup c,
    covered := mem_keys_of_lookup cells }
/-- A capability lets its holder crawl to its target only if it carries `read`. -/
def capObserves (cap : Cap) : Bool := cap.rights.contains Auth.read
/-- One step of the crawl: `c` holds a read-bearing capability to `d`, and `d` is on the ledger. -/
def Edge (w : World) (c d : CellId) : Prop :=
  ∃ p cap, w.pub c = some p ∧ cap ∈ p.caps ∧ capObserves cap = true ∧ cap.target = d ∧
    (w.pub d).isSome = true
theorem Edge.source_live {w : World} {c d : CellId} (e : Edge w c d) : (w.pub c).isSome = true := by
  obtain ⟨p, _, hp, _⟩ := e
  simp [hp]
theorem Edge.target_live {w : World} {c d : CellId} (e : Edge w c d) : (w.pub d).isSome = true := by
  obtain ⟨_, _, _, _, _, _, hd⟩ := e
  exact hd
/-- **The specification of the frustum's extent**: the cells a viewer's capabilities reach. -/
inductive Reach (w : World) : CellId → CellId → Prop where
  | refl {c : CellId} : (w.pub c).isSome = true → Reach w c c
  | head {c m d : CellId} : Edge w c m → Reach w m d → Reach w c d
theorem Reach.source_live {w : World} {c d : CellId} (h : Reach w c d) : (w.pub c).isSome = true := by
  cases h with
  | refl h => exact h
  | head e _ => exact e.source_live
theorem Reach.target_live {w : World} {c d : CellId} (h : Reach w c d) : (w.pub d).isSome = true := by
  induction h with
  | refl h => exact h
  | head _ _ ih => exact ih
theorem Reach.trans {w : World} {a b c : CellId} (h₁ : Reach w a b) (h₂ : Reach w b c) :
    Reach w a c := by
  induction h₁ with
  | refl _ => exact h₂
  | head e _ ih => exact .head e (ih h₂)
theorem Reach.tail {w : World} {a b c : CellId} (h : Reach w a b) (e : Edge w b c) : Reach w a c :=
  h.trans (.head e (.refl e.target_live))
/-- A walk of `n` steps through cells of `live`. -/
inductive WalkIn (w : World) (live : List CellId) : CellId → CellId → Nat → Prop where
  | here {c : CellId} : c ∈ live → WalkIn w live c c 0
  | cons {c m d : CellId} {n : Nat} :
      c ∈ live → Edge w c m → WalkIn w live m d n → WalkIn w live c d (n + 1)
theorem WalkIn.head_mem {w : World} {live : List CellId} {c d : CellId} {n : Nat}
    (h : WalkIn w live c d n) : c ∈ live := by
  cases h <;> assumption
theorem WalkIn.mono {w : World} {l l' : List CellId} {c d : CellId} {n : Nat}
    (hs : ∀ x, x ∈ l → x ∈ l') (h : WalkIn w l c d n) : WalkIn w l' c d n := by
  induction h with
  | here hc => exact .here (hs _ hc)
  | cons hc e _ ih => exact .cons (hs _ hc) e ih
theorem Reach.walk {w : World} {c d : CellId} (h : Reach w c d) : ∃ n, WalkIn w w.ids c d n := by
  induction h with
  | refl hc => exact ⟨0, .here (World.mem_ids_of_pub hc)⟩
  | head e _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .cons (World.mem_ids_of_pub e.source_live) e hn⟩
/-- A walk either avoids `x`, ends at `x`, or continues from a successor of `x` without it. -/
theorem WalkIn.avoid {w : World} {l : List CellId} {c d : CellId} {n : Nat} (x : CellId)
    (h : WalkIn w l c d n) :
    (∃ k, WalkIn w (l.filter (· != x)) c d k) ∨ d = x ∨
      ∃ x' k, Edge w x x' ∧ WalkIn w (l.filter (· != x)) x' d k := by
  induction h with
  | @here c hc =>
    by_cases hx : c = x
    · exact .inr (.inl hx)
    · exact .inl ⟨0, .here (List.mem_filter.mpr ⟨hc, by simpa using hx⟩)⟩
  | @cons c m d n hc e _ ih =>
    rcases ih with ⟨k, hk⟩ | hd | hrest
    · by_cases hx : c = x
      · exact .inr (.inr ⟨m, k, hx ▸ e, hk⟩)
      · exact .inl ⟨k + 1, .cons (List.mem_filter.mpr ⟨hc, by simpa using hx⟩) e hk⟩
    · exact .inr (.inl hd)
    · exact .inr (.inr hrest)
/-- A walk through `live` can be shortened below the size of `live`. -/
theorem WalkIn.short {w : World} : ∀ (m : Nat) (l : List CellId) (c d : CellId) (n : Nat),
    l.length ≤ m → WalkIn w l c d n → ∃ k, k < m ∧ WalkIn w l c d k
  | 0, l, c, d, n, hl, h => by
    have hc := h.head_mem
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp at hc
  | m + 1, l, c, d, n, hl, h => by
    have hc := h.head_mem
    have hlt : (l.filter (· != c)).length < l.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨c, hc, by simp⟩
    have hsub : ∀ y, y ∈ l.filter (· != c) → y ∈ l := fun y hy => (List.mem_filter.mp hy).1
    rcases h.avoid c with ⟨k, hk⟩ | hd | ⟨x', k, e, hk⟩
    · have hmem := hk.head_mem
      simp at hmem
    · subst hd
      exact ⟨0, by omega, .here hc⟩
    · obtain ⟨k', hk', hw⟩ := WalkIn.short m _ x' d k (by omega) hk
      exact ⟨k' + 1, by omega, .cons hc e (hw.mono hsub)⟩
/-- The successors of a cell on the ledger. -/
def World.succs (w : World) (c : CellId) : List CellId :=
  match w.pub c with
  | some p => ((p.caps.filter capObserves).map (·.target)).filter fun d => (w.pub d).isSome
  | none => []
theorem mem_succs {w : World} {c d : CellId} : d ∈ w.succs c ↔ Edge w c d := by
  unfold World.succs Edge
  cases hp : w.pub c with
  | none => simp
  | some p =>
    simp only [List.mem_filter, List.mem_map, Option.some.injEq]
    constructor
    · rintro ⟨⟨cap, ⟨hcap, hobs⟩, rfl⟩, hd⟩
      exact ⟨p, cap, rfl, hcap, hobs, rfl, hd⟩
    · rintro ⟨p', cap, hp', hcap, hobs, rfl, hd⟩
      cases hp'
      exact ⟨⟨cap, ⟨hcap, hobs⟩, rfl⟩, hd⟩
/-- Append the elements of the second list not already present. -/
def addNew : List CellId → List CellId → List CellId
  | acc, [] => acc
  | acc, x :: xs => if acc.contains x then addNew acc xs else addNew (acc ++ [x]) xs
theorem mem_addNew {y : CellId} : ∀ (xs acc : List CellId), y ∈ addNew acc xs ↔ y ∈ acc ∨ y ∈ xs
  | [], acc => by simp [addNew]
  | x :: xs, acc => by
    unfold addNew
    split
    · rename_i h
      have hx : x ∈ acc := by simpa using h
      rw [mem_addNew xs acc, List.mem_cons]
      exact ⟨fun h => h.elim .inl (.inr ∘ .inr),
        fun h => h.elim .inl fun h => h.elim (fun e => .inl (e ▸ hx)) .inr⟩
    · rw [mem_addNew xs (acc ++ [x]), List.mem_append, List.mem_singleton, List.mem_cons]
      exact or_assoc
/-- One round: the set, and every successor of a member. -/
def World.expand (w : World) (S : List CellId) : List CellId := addNew S (S.flatMap w.succs)
theorem mem_expand {w : World} {S : List CellId} {y : CellId} :
    y ∈ w.expand S ↔ y ∈ S ∨ ∃ c, c ∈ S ∧ Edge w c y := by
  unfold World.expand
  rw [mem_addNew, List.mem_flatMap]
  constructor
  · rintro (h | ⟨c, hc, hy⟩)
    · exact .inl h
    · exact .inr ⟨c, hc, mem_succs.mp hy⟩
  · rintro (h | ⟨c, hc, hy⟩)
    · exact .inl h
    · exact .inr ⟨c, hc, mem_succs.mpr hy⟩
def World.saturate (w : World) : Nat → List CellId → List CellId
  | 0, S => S
  | n + 1, S => w.saturate n (w.expand S)
theorem subset_saturate {w : World} : ∀ (n : Nat) (S : List CellId) (y : CellId),
    y ∈ S → y ∈ w.saturate n S
  | 0, _, _, h => h
  | n + 1, S, y, h => subset_saturate n (w.expand S) y (mem_expand.mpr (.inl h))
theorem saturate_sound {w : World} : ∀ (n : Nat) (S : List CellId) (y : CellId),
    y ∈ w.saturate n S → y ∈ S ∨ ∃ c m, c ∈ S ∧ Edge w c m ∧ Reach w m y
  | 0, _, _, h => .inl h
  | n + 1, S, y, h => by
    rcases saturate_sound n (w.expand S) y h with hy | ⟨c, m, hc, e, hr⟩
    · rcases mem_expand.mp hy with hy | ⟨c, hc, e⟩
      · exact .inl hy
      · exact .inr ⟨c, y, hc, e, .refl e.target_live⟩
    · rcases mem_expand.mp hc with hc | ⟨c₀, hc₀, e₀⟩
      · exact .inr ⟨c, m, hc, e, hr⟩
      · exact .inr ⟨c₀, c, hc₀, e₀, .head e hr⟩
theorem saturate_complete {w : World} {l : List CellId} {c d : CellId} {k : Nat}
    (h : WalkIn w l c d k) :
    ∀ (n : Nat) (S : List CellId), c ∈ S → k ≤ n → d ∈ w.saturate n S := by
  induction h with
  | here _ => intro n S hc _; exact subset_saturate n S _ hc
  | cons _ e _ ih =>
    intro n S hc hk
    cases n with
    | zero => omega
    | succ n => exact ih n (w.expand S) (mem_expand.mpr (.inr ⟨_, hc, e⟩)) (by omega)
/-- The cells a viewer may crawl: its own cell, saturated along read-bearing capabilities. -/
def World.visible (w : World) (viewer : CellId) : List CellId :=
  if (w.pub viewer).isSome then w.saturate w.ids.length [viewer] else []
/-- **The frustum's extent, as a check.** -/
def World.canObserve (w : World) (viewer c : CellId) : Bool := (w.visible viewer).contains c
/-- **The check is the specification**: nothing unreachable is observed, nothing reachable missed. -/
theorem canObserve_iff {w : World} {viewer c : CellId} :
    w.canObserve viewer c = true ↔ Reach w viewer c := by
  unfold World.canObserve World.visible
  constructor
  · intro h
    split at h
    · rename_i hv
      have hmem : c ∈ w.saturate w.ids.length [viewer] := by simpa using h
      rcases saturate_sound _ _ _ hmem with hc | ⟨c₀, m, hc₀, e, hr⟩
      · have hcv : c = viewer := by simpa using hc
        subst hcv
        exact .refl hv
      · have hcv : c₀ = viewer := by simpa using hc₀
        subst hcv
        exact .head e hr
    · simp at h
  · intro h
    simp only [h.source_live, ↓reduceIte]
    obtain ⟨n, hn⟩ := h.walk
    obtain ⟨k, hk, hw⟩ := WalkIn.short w.ids.length w.ids viewer c n (Nat.le_refl _) hn
    have hmem := saturate_complete hw w.ids.length [viewer] (by simp) (by omega)
    simpa using hmem
/-! ## 3. The projection -/
/-- What a viewer holds of one cell; `lit` names the affordances it may fire now. -/
structure CellView where
  state : Data
  sealed : List (String × ByteArray)
  caps : List Cap
  lit : List String
  epoch : Nat
/-- A viewer's view of the world. -/
structure Frustum where
  viewer : CellId
  cells : List (CellId × CellView)
/-- The rights the viewer's own c-list holds over `d`. Reading a cell confers none of its rights. -/
def World.heldOn (w : World) (viewer d : CellId) : List Auth :=
  match w.pub viewer with
  | some p => (p.caps.filter (·.target == d)).flatMap (·.rights)
  | none => []
def viewCell (facts : Facts) (held : List Auth) (p : CellPub) : CellView :=
  { state := p.state, sealed := p.sealed, caps := p.caps,
    lit := (projectGatedFor held facts none p.state p.surface).map (·.aff.name),
    epoch := p.epoch }
/-- What the viewer sees of `c`: nothing unless it may observe it. -/
def World.look (w : World) (viewer c : CellId) : Option CellView :=
  if w.canObserve viewer c then (w.pub c).map (viewCell w.facts (w.heldOn viewer c)) else none
/-- **Project the world through the viewer's authority.** -/
def Frustum.project (w : World) (viewer : CellId) : Frustum :=
  { viewer := viewer, cells := w.ids.filterMap fun c => (w.look viewer c).map fun v => (c, v) }
/-- Read one cell through a frustum. -/
def Frustum.reflect (f : Frustum) (c : CellId) : Option CellView := f.cells.lookup c
theorem lookup_filterMap_keyed {β : Type} (g : CellId → Option β) (c : CellId) :
    ∀ ids : List CellId,
      (ids.filterMap fun x => (g x).map fun v => (x, v)).lookup c = if c ∈ ids then g c else none
  | [] => by simp
  | x :: xs => by
    have ih := lookup_filterMap_keyed g c xs
    by_cases hx : c = x
    · subst hx
      cases hg : g c with
      | none =>
        rw [List.filterMap_cons_none (by simp [hg]), ih]
        simp [hg]
      | some v =>
        rw [List.filterMap_cons_some (b := (c, v)) (by simp [hg])]
        simp [List.lookup]
    · have hne : (c == x) = false := by simpa using hx
      cases hg : g x with
      | none =>
        rw [List.filterMap_cons_none (by simp [hg]), ih]
        simp [hx]
      | some v =>
        rw [List.filterMap_cons_some (b := (x, v)) (by simp [hg])]
        simp only [List.lookup, hne, ih]
        simp [hx]
theorem reflect_project (w : World) (viewer c : CellId) :
    (Frustum.project w viewer).reflect c = w.look viewer c := by
  unfold Frustum.reflect Frustum.project
  rw [lookup_filterMap_keyed (w.look viewer) c w.ids]
  split
  · rfl
  · rename_i hc
    unfold World.look
    cases hp : w.pub c with
    | none => simp
    | some p => exact absurd (World.mem_ids_of_pub (by simp [hp])) hc
/-- **An unreachable cell is absent**: reading it through the frustum finds nothing. -/
theorem frustum_unobservable_absent {w : World} {viewer c : CellId} (h : ¬ Reach w viewer c) :
    (Frustum.project w viewer).reflect c = none := by
  rw [reflect_project]
  unfold World.look
  have hno : w.canObserve viewer c = false := by
    cases hb : w.canObserve viewer c with
    | false => rfl
    | true => exact absurd (canObserve_iff.mp hb) h
  simp [hno]
/-- **A reachable cell is present**, with its public face seen through the viewer's rights. -/
theorem frustum_observable_present {w : World} {viewer c : CellId} {r : CellRecord}
    (h : Reach w viewer c) (hc : w.cell c = some r) :
    (Frustum.project w viewer).reflect c = some (viewCell w.facts (w.heldOn viewer c) r.pub) := by
  rw [reflect_project]
  simp [World.look, canObserve_iff.mpr h, World.pub, hc]
/-- A sealed slot of a reachable cell is shown as its commitment, and as nothing else. -/
theorem frustum_sealed_slot_shows_commitment {w : World} {viewer c : CellId} {r : CellRecord}
    (h : Reach w viewer c) (hc : w.cell c = some r) :
    ∃ v, (Frustum.project w viewer).reflect c = some v ∧
      v.sealed = r.sealed.map fun e => (e.1, sealCommit e.2) :=
  ⟨_, frustum_observable_present h hc, by simp [viewCell, CellRecord.pub]⟩

/-- Worlds the viewer cannot tell apart: the same ids and facts, the same public face on every
cell the viewer reaches, and no cell in the second that the first lacks. -/
structure ViewEquiv (w w' : World) (viewer : CellId) : Prop where
  ids : w'.ids = w.ids
  facts : w'.facts = w.facts
  kept : ∀ c, Reach w viewer c → w'.pub c = w.pub c
  noBirth : ∀ c, (w'.pub c).isSome = true → (w.pub c).isSome = true

theorem ViewEquiv.forward {w w' : World} {viewer : CellId} (h : ViewEquiv w w' viewer)
    {c d : CellId} (hv : Reach w viewer c) (hr : Reach w c d) : Reach w' c d := by
  induction hr with
  | refl hc => exact .refl (by rw [h.kept _ hv]; exact hc)
  | head e _ ih =>
    have hm := hv.tail e
    obtain ⟨p, cap, hp, hcap, hobs, ht, hd⟩ := e
    exact .head ⟨p, cap, by rw [h.kept _ hv]; exact hp, hcap, hobs, ht,
      by rw [h.kept _ hm]; exact hd⟩ (ih hm)

theorem ViewEquiv.backward {w w' : World} {viewer : CellId} (h : ViewEquiv w w' viewer)
    {c d : CellId} (hv : Reach w viewer c) (hr : Reach w' c d) : Reach w c d := by
  induction hr with
  | refl _ => exact .refl hv.target_live
  | head e _ ih =>
    obtain ⟨p, cap, hp, hcap, hobs, ht, hd⟩ := e
    have e' : Edge w _ _ :=
      ⟨p, cap, by rw [← h.kept _ hv]; exact hp, hcap, hobs, ht, h.noBirth _ hd⟩
    exact .head e' (ih (hv.tail e'))

theorem ViewEquiv.reach_iff {w w' : World} {viewer : CellId} (h : ViewEquiv w w' viewer)
    {c : CellId} : Reach w' viewer c ↔ Reach w viewer c :=
  ⟨fun hr => h.backward (.refl (h.noBirth _ hr.source_live)) hr,
   fun hr => h.forward (.refl hr.source_live) hr⟩

/-- **Noninterference of the frustum.** Worlds the viewer cannot tell apart project to the same
frustum: the same cells, in the same order, with the same views. -/
theorem frustum_noninterference {w w' : World} {viewer : CellId} (h : ViewEquiv w w' viewer) :
    Frustum.project w' viewer = Frustum.project w viewer := by
  have hobs : w'.canObserve viewer = w.canObserve viewer := by
    funext c
    rw [Bool.eq_iff_iff, canObserve_iff, canObserve_iff]
    exact h.reach_iff
  have hheld : ∀ d, w'.heldOn viewer d = w.heldOn viewer d := by
    intro d
    unfold World.heldOn
    cases hv : w.pub viewer with
    | some p => rw [h.kept viewer (.refl (by simp [hv])), hv]
    | none =>
      cases hv' : w'.pub viewer with
      | none => rfl
      | some _ => have hb := h.noBirth viewer (by simp [hv']); simp [hv] at hb
  have hlook : w'.look viewer = w.look viewer := by
    funext c
    unfold World.look
    rw [hobs, h.facts, hheld]
    split
    · rename_i hc
      rw [h.kept c (canObserve_iff.mp hc)]
    · rfl
  unfold Frustum.project
  rw [h.ids, hlook]

/-- Overwrite a cell that exists. -/
def World.set (w : World) (h : CellId) (r : CellRecord) : World :=
  { ids := w.ids, facts := w.facts,
    cell := fun c => if c = h then (w.cell h).map (fun _ => r) else w.cell c,
    covered := by
      intro c hc
      by_cases hch : c = h
      · subst hch
        exact w.covered c (by simpa using hc)
      · exact w.covered c (by simpa [hch] using hc) }

/-- Delete a cell. -/
def World.erase (w : World) (h : CellId) : World :=
  { ids := w.ids, facts := w.facts,
    cell := fun c => if c = h then none else w.cell c,
    covered := by
      intro c hc
      by_cases hch : c = h
      · simp [hch] at hc
      · exact w.covered c (by simpa [hch] using hc) }

theorem World.set_cell_ne {w : World} {h c : CellId} (r : CellRecord) (hne : c ≠ h) :
    (w.set h r).cell c = w.cell c := by
  simp [World.set, hne]

/-- **A hidden cell may be rewritten or deleted and the viewer's frustum is the same frustum.** -/
theorem hidden_cell_mutation_invisible {w : World} {viewer h : CellId}
    (hhid : ¬ Reach w viewer h) (r : CellRecord) :
    Frustum.project (w.set h r) viewer = Frustum.project w viewer ∧
    Frustum.project (w.erase h) viewer = Frustum.project w viewer := by
  have hne : ∀ c, Reach w viewer c → c ≠ h := fun c hc hch => hhid (hch ▸ hc)
  constructor
  · apply frustum_noninterference
    refine ⟨rfl, rfl, fun c hc => by simp [World.pub, World.set, hne c hc], fun c hc => ?_⟩
    by_cases hch : c = h
    · subst hch
      cases hw : w.cell c with
      | none => simp [World.pub, World.set, hw] at hc
      | some _ => simp [World.pub, hw]
    · simpa [World.pub, World.set, hch] using hc
  · apply frustum_noninterference
    refine ⟨rfl, rfl, fun c hc => by simp [World.pub, World.erase, hne c hc], fun c hc => ?_⟩
    by_cases hch : c = h
    · simp [World.pub, World.erase, hch] at hc
    · simpa [World.pub, World.erase, hch] using hc

/-- Projection respects equality of commitments. This algebraic lemma asserts no secrecy. -/
theorem frustum_equal_commitments_project_eq (w : World) (viewer h : CellId) (r : CellRecord)
    (sealed' : List (String × SealedSlot))
    (hcommit : sealed'.map (fun e => (e.1, sealCommit e.2)) =
      r.sealed.map (fun e => (e.1, sealCommit e.2))) :
    Frustum.project (w.set h { r with sealed := sealed' }) viewer =
      Frustum.project (w.set h r) viewer := by
  apply frustum_noninterference
  have hpub : ∀ c, (w.set h { r with sealed := sealed' }).pub c = (w.set h r).pub c := by
    intro c
    by_cases hch : c = h
    · subst hch
      cases hw : w.cell c with
      | none => simp [World.pub, World.set, hw]
      | some _ => simp [World.pub, World.set, hw, CellRecord.pub, hcommit]
    · simp [World.pub, World.set, hch]
  exact ⟨rfl, rfl, fun c _ => hpub c, fun c hc => by rw [← hpub c]; exact hc⟩

/-- Uniform salt coins: exactly 2^256 choices, encoded as 32 bytes. -/
abbrev SaltCoin := Fin (2 ^ 256)
def saltedPreimage (secret : List UInt8) (salt : SaltCoin) : List UInt8 :=
  sealPreimage ⟨secret, Obend.Digest.HashBytes.be 32 salt.val⟩
theorem saltedPreimage_injective (secret : List UInt8) {a b : SaltCoin}
    (h : saltedPreimage secret a = saltedPreimage secret b) : a = b := by
  have hs := congrArg SealedSlot.salt (sealPreimage_injective h)
  apply Fin.ext
  exact Obend.Digest.HashBytes.be_injective (by simpa using a.isLt) (by simpa using b.isLt) hs

/-- Lazy random-oracle execution, with a fixed public commitment and fixed random reply tape.
The adversary sees the entire transcript. Repeated queries reuse their first answer. Neither
`next` nor `coins` receives the secret salt. Programming changes only the challenge preimage. -/
abbrev ROTranscript := List (List UInt8 × BitVec 256)
def lazyRO (next : ROTranscript → List UInt8) (coins : Nat → BitVec 256)
    (program : Option (List UInt8 × BitVec 256)) : Nat → ROTranscript → ROTranscript
  | 0, _ => []
  | q + 1, seen =>
    let x := next seen
    let y := match program with
      | some (target, commitment) => if x = target then commitment
          else (seen.lookup x).getD (coins seen.length)
      | none => (seen.lookup x).getD (coins seen.length)
    (x, y) :: lazyRO next coins program q (seen ++ [(x, y)])
theorem lazyRO_length (next : ROTranscript → List UInt8) (coins : Nat → BitVec 256)
    (program : Option (List UInt8 × BitVec 256)) (q : Nat) (seen : ROTranscript) :
    (lazyRO next coins program q seen).length = q := by
  induction q generalizing seen with
  | zero => rfl
  | succ q ih => simp only [lazyRO, List.length_cons, ih]

/-- The programmed and unprogrammed transcripts coincide until the first challenge query. -/
theorem lazyRO_program_unseen (next : ROTranscript → List UInt8) (coins : Nat → BitVec 256)
    (target : List UInt8) (commitment : BitVec 256) (q : Nat) (seen : ROTranscript)
    (h : target ∉ (lazyRO next coins none q seen).map Prod.fst) :
    lazyRO next coins (some (target, commitment)) q seen = lazyRO next coins none q seen := by
  induction q generalizing seen with
  | zero => rfl
  | succ q ih =>
    simp only [lazyRO, List.map_cons, List.mem_cons, not_or] at h
    simp only [lazyRO, Ne.symm h.1, ite_false]
    rw [ih _ h.2]

/-- Exact bad-coin set for a fixed adaptive oracle execution. Uniform salt selects from all
2^256 coins; counting needs no measure theory and no collision-resistance premise. -/
def hitSalts (secret : List UInt8) (queries : List (List UInt8)) : List SaltCoin :=
  (List.finRange (2 ^ 256)).filter fun salt => queries.any (fun x => decide (x = saltedPreimage secret salt))
/-- Constructive subset counting using decidable byte-string equality. -/
private theorem distinct_subset_length {xs ys : List (List UInt8)}
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hn
    have hm := hs (List.mem_cons_self)
    have sub : xs ⊆ ys.eraseP (fun z => decide (z = x)) := by
      intro y hy
      have hne : ¬decide (y = x) = true := fun he => hx (of_decide_eq_true he ▸ hy)
      exact (List.mem_eraseP_of_neg (p := fun z => decide (z = x)) hne).mpr (hs (.tail _ hy))
    have hi := ih ht sub
    have hl : (ys.eraseP (fun z => decide (z = x))).length = ys.length - 1 :=
      List.length_eraseP_of_mem hm (decide_eq_true rfl)
    have hp := List.length_pos_of_mem hm
    simp only [List.length_cons]; omega

theorem hitSalts_bound (secret : List UInt8) (queries : List (List UInt8)) :
    (hitSalts secret queries).length ≤ queries.length := by
  have hn : ((hitSalts secret queries).map (saltedPreimage secret)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    have hf : (hitSalts secret queries).Nodup :=
      List.Pairwise.filter _ (List.nodup_finRange (n := 2 ^ 256))
    exact hf.imp (fun hab he => hab (saltedPreimage_injective secret he))
  have hs : (hitSalts secret queries).map (saltedPreimage secret) ⊆ queries := by
    intro x hx
    obtain ⟨salt, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, hx, he⟩ := List.any_eq_true.mp (List.mem_filter.mp hm).2
    exact of_decide_eq_true he ▸ hx
  simpa only [List.length_map] using distinct_subset_length hn hs

/-- ROM salt hiding: for every fixed public commitment and adaptive Q-query adversary/reply
coins, at most Q of the 2^256 uniform salts can distinguish programming the secret's seal.
This is an ideal-oracle theorem, not a claim that deterministic cSHAKE is a random oracle. -/
theorem frustum_committed_field_hides_value (secret : List UInt8)
    (next : ROTranscript → List UInt8) (coins : Nat → BitVec 256)
    (commitment : BitVec 256) (Q : Nat) :
    (List.finRange (2 ^ 256)).length = 2 ^ 256 ∧
    (hitSalts secret ((lazyRO next coins none Q []).map Prod.fst)).length ≤ Q ∧
    ∀ salt : SaltCoin, salt ∉ hitSalts secret ((lazyRO next coins none Q []).map Prod.fst) →
      lazyRO next coins (some (saltedPreimage secret salt, commitment)) Q [] =
        lazyRO next coins none Q [] := by
  refine ⟨by simp, ?_, ?_⟩
  · simpa only [List.length_map, lazyRO_length] using
      hitSalts_bound secret ((lazyRO next coins none Q []).map Prod.fst)
  · intro salt hs
    apply lazyRO_program_unseen
    intro hm
    apply hs
    exact List.mem_filter.mpr ⟨by simp, List.any_eq_true.mpr
      ⟨saltedPreimage secret salt, hm, decide_eq_true rfl⟩⟩

/-! ## 4. The cut: boundary pins and their four faces -/

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toByteArray.data.toList

theorem utf8_injective : ∀ {s₁ s₂ : String}, utf8 s₁ = utf8 s₂ → s₁ = s₂
  | ⟨⟨⟨l₁⟩⟩, _⟩, ⟨⟨⟨l₂⟩⟩, _⟩, h => by
    change l₁ = l₂ at h
    subst h
    rfl

/-- The natural slots of a public state: what a severed pin freezes. -/
def natSlots : Data → List (String × Nat)
  | .record fs => fs.filterMap fun e => match e.2 with
    | .natural v => some (e.1, v)
    | _ => none
  | _ => []

/-- Each slot tagged and framed; the list closed by a zero tag. -/
def encodeSlots : List (String × Nat) → List UInt8
  | [] => [0]
  | e :: rest => 1 :: (encodeListField (utf8 e.1) ++ (leb128 e.2 ++ encodeSlots rest))

theorem encodeSlots_injective : ∀ (a b : List (String × Nat)), encodeSlots a = encodeSlots b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encodeSlots] at h
  | _ :: _, [], h => by simp [encodeSlots] at h
  | (n₁, v₁) :: r₁, (n₂, v₂) :: r₂, h => by
    simp only [encodeSlots, List.cons.injEq, true_and] at h
    obtain ⟨hn, h⟩ := encodeListField_prefix_inj h
    obtain ⟨hv, h⟩ := leb128_prefix_inj h
    rw [utf8_injective hn, hv, encodeSlots_injective r₁ r₂ h]

/-- Customization string of the pin hash. -/
def pinCustomization : List UInt8 := "OBEND.VAULT.FRUSTUM.PIN/v1".toUTF8.data.toList

/-- What a severed pin hashes: the target's id, its epoch, and its natural slots, all framed. -/
def pinPreimage (target : CellId) (reading : Nat × List (String × Nat)) : List UInt8 :=
  encodeListField (utf8 target) ++ (leb128 reading.1 ++ encodeSlots reading.2)

theorem pinPreimage_injective {t₁ t₂ : CellId} {r₁ r₂ : Nat × List (String × Nat)}
    (h : pinPreimage t₁ r₁ = pinPreimage t₂ r₂) : t₁ = t₂ ∧ r₁ = r₂ := by
  unfold pinPreimage at h
  obtain ⟨ht, h⟩ := encodeListField_prefix_inj h
  obtain ⟨he, h⟩ := leb128_prefix_inj h
  exact ⟨utf8_injective ht, Prod.ext he (encodeSlots_injective _ _ h)⟩

/-- The 32-byte snapshot a severed pin carries. -/
def pinDigest (target : CellId) (reading : Nat × List (String × Nat)) : ByteArray :=
  cshake32ByteArray pinCustomization (pinPreimage target reading)

theorem pinDigest_size (target : CellId) (reading : Nat × List (String × Nat)) :
    (pinDigest target reading).size = 32 := cshake32ByteArray_size _ _

theorem pinDigest_binds {t : CellId} {r₁ r₂ : Nat × List (String × Nat)}
    (h : pinDigest t r₁ = pinDigest t r₂) :
    r₁ = r₂ ∨ CollisionAmong (cshake256Bytes pinCustomization)
      (fun x => x = pinPreimage t r₁ ∨ x = pinPreimage t r₂) :=
  (cshake32_binds pinCustomization h).imp (fun hp => (pinPreimage_injective hp).2) id

/-- What a pin reads of its target: epoch and natural slots; of an unobservable cell, nothing. -/
def readingOf : Option CellView → Nat × List (String × Nat)
  | some v => (v.epoch, natSlots v.state)
  | none => (0, [])

/-- What the cutter asks for at one crossing capability. -/
inductive Disposition where
  | sever (log : InteractionLog)
  | attenuate (ask : MembraneViewer) (expr : NExpr)
  | interpose (mock : Data)
  | tether

/-- What stands at the cut in place of a crossing capability. -/
inductive PinFace where
  | severed (reading : Nat × List (String × Nat)) (snapshot : ByteArray) (log : InteractionLog)
  | attenuated (membrane : MembraneViewer) (residual : NExpr)
  | interposed (mock : Data)
  | tethered

def PinFace.isTethered : PinFace → Bool
  | .tethered => true
  | _ => false

/-- The liveness of a face. A severed pin has no live source: its tier is read off its log. -/
def PinFace.liveness : PinFace → Rehydration
  | .severed _ _ log => classify log false
  | .attenuated _ _ => classify [] true
  | .interposed _ => classify [] false
  | .tethered => classify [] true

/-- Freeze what the frustum shows of `target`. -/
def severFace (f : Frustum) (target : CellId) (log : InteractionLog) : PinFace :=
  .severed (readingOf (f.reflect target)) (pinDigest target (readingOf (f.reflect target))) log

/-- The holder's membrane over one capability: its rights, with the target named. -/
def pinHolder (cap : Cap) : MembraneViewer :=
  { held := cap.rights, permits := fun _ => true, activeNames := [cap.target] }

/-- An ask that may not name the backing cell. -/
def hideBacking (target : CellId) (ask : MembraneViewer) : MembraneViewer :=
  { ask with permits := fun n => ask.permits n && n != target }

/-- What the frustum knows of a pin's target, as a form's knowledge. -/
def backingKnown (f : Frustum) (target : CellId) : Known :=
  fun n => if n = target then (f.reflect target).map (·.state) else none

/-- The face a disposition makes. A refused attenuation falls back to a severed pin. -/
def makeFace (f : Frustum) (cap : Cap) : Disposition → PinFace
  | .sever log => severFace f cap.target log
  | .attenuate ask expr =>
    match f.reflect cap.target, Membrane.reshare (pinHolder cap) (hideBacking cap.target ask) with
    | some _, some m => .attenuated m (expr.peval (backingKnown f cap.target))
    | _, _ => severFace f cap.target []
  | .interpose mock => .interposed mock
  | .tether => .tethered

/-- A capability reified at the cut. -/
structure BoundaryPin where
  holder : CellId
  target : CellId
  rights : List Auth
  face : PinFace

/-- An interior cell as captured, and as edited since. -/
structure Captured where
  id : CellId
  epoch : Nat
  base : Data
  now : Data

/-- A living screenshot: the interior, the pins at its edge, and the fields it must conserve. -/
structure Screenshot where
  viewer : CellId
  interior : List Captured
  pins : List BoundaryPin
  conserved : List String

/-- **The cut boundary**: every capability a cell of the set holds to a cell outside it. -/
def Frustum.cut (f : Frustum) (F : List CellId) : List (CellId × Cap) :=
  F.flatMap fun c => match f.reflect c with
    | some v => (v.caps.filter fun cap => !F.contains cap.target).map fun cap => (c, cap)
    | none => []

theorem mem_cut {f : Frustum} {F : List CellId} {c : CellId} {cap : Cap} :
    (c, cap) ∈ f.cut F ↔ c ∈ F ∧ ∃ v, f.reflect c = some v ∧ cap ∈ v.caps ∧ cap.target ∉ F := by
  unfold Frustum.cut
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨c', hc', hmem⟩
    cases hv : f.reflect c' with
    | none => simp [hv] at hmem
    | some v =>
      simp only [hv, List.mem_map, List.mem_filter, Prod.mk.injEq] at hmem
      obtain ⟨cap', ⟨hcap, hout⟩, rfl, rfl⟩ := hmem
      exact ⟨hc', v, hv, hcap, by simpa using hout⟩
  · rintro ⟨hc, v, hv, hcap, hout⟩
    refine ⟨c, hc, ?_⟩
    simp only [hv, List.mem_map, List.mem_filter, Prod.mk.injEq]
    exact ⟨cap, ⟨hcap, by simpa using hout⟩, by simp⟩

/-- **Snip a living screenshot out of a frustum.** It is computed from the frustum alone. -/
def Frustum.snip (f : Frustum) (F : List CellId) (policy : CellId → Cap → Disposition)
    (conserved : List String) : Screenshot :=
  { viewer := f.viewer,
    interior := F.filterMap fun c => (f.reflect c).map fun v => ⟨c, v.epoch, v.state, v.state⟩,
    pins := (f.cut F).map fun e => ⟨e.1, e.2.target, e.2.rights, makeFace f e.2 (policy e.1 e.2)⟩,
    conserved := conserved }

/-- **Every capability crossing the cut is reified as a pin, and every pin is such a capability.** -/
theorem snip_reifies_cut (f : Frustum) (F : List CellId) (policy : CellId → Cap → Disposition)
    (conserved : List String) :
    (∀ c cap, (c, cap) ∈ f.cut F → ∃ pin, pin ∈ (f.snip F policy conserved).pins ∧
      pin.holder = c ∧ pin.target = cap.target ∧ pin.rights = cap.rights ∧
      pin.face = makeFace f cap (policy c cap)) ∧
    (∀ pin, pin ∈ (f.snip F policy conserved).pins → pin.holder ∈ F ∧ pin.target ∉ F) := by
  constructor
  · intro c cap h
    have hmem : (⟨c, cap.target, cap.rights, makeFace f cap (policy c cap)⟩ : BoundaryPin) ∈
        (f.snip F policy conserved).pins := List.mem_map.mpr ⟨(c, cap), h, rfl⟩
    exact ⟨_, hmem, rfl, rfl, rfl, rfl⟩
  · intro pin h
    obtain ⟨⟨c, cap⟩, hmem, rfl⟩ := List.mem_map.mp h
    obtain ⟨hc, _, _, _, hout⟩ := mem_cut.mp hmem
    exact ⟨hc, hout⟩

/-- **Severing promotes a pin to `ReplayedDeterministic` exactly when its witness log is confined.**
The severed face carries the 256-bit snapshot of what the frustum showed, and is never `Live`. -/
theorem sever_promotes_replayed_deterministic (f : Frustum) (cap : Cap) (log : InteractionLog) :
    (makeFace f cap .tether).liveness = .Live ∧
    (makeFace f cap (.sever log)).liveness ≠ .Live ∧
    ((makeFace f cap (.sever log)).liveness = .ReplayedDeterministic ↔ confined log = true) ∧
    makeFace f cap (.sever log) = .severed (readingOf (f.reflect cap.target))
      (pinDigest cap.target (readingOf (f.reflect cap.target))) log := by
  refine ⟨by simp [makeFace, PinFace.liveness, classify], ?_, ?_, by simp [makeFace, severFace]⟩
  · simp only [makeFace, severFace, PinFace.liveness, classify]
    cases confined log <;> simp
  · simp only [makeFace, severFace, PinFace.liveness]
    exact replayedDeterministic_iff_confined log

/-- Does an expression read the page `t` by name? -/
def reads (t : String) : NExpr → Bool
  | .lit _ => false
  | .hole _ => false
  | .field (.page n) _ => n == t
  | .field (.hole _) _ => false
  | .add x y => reads t x || reads t y
  | .sub x y => reads t x || reads t y

theorem reads_addN (t : String) (x y : NExpr) (hx : reads t x = false) (hy : reads t y = false) :
    reads t (addN x y) = false := by
  cases x <;> cases y <;> simp_all [addN, reads]
theorem reads_subN (t : String) (x y : NExpr) (hx : reads t x = false) (hy : reads t y = false) :
    reads t (subN x y) = false := by
  cases x <;> cases y <;> simp_all [subN, reads] <;> split <;> simp [reads]

/-- The residual of an expression reads no page its knowledge covered. -/
theorem reads_peval {k : Known} {t : String} (ht : (k t).isSome = true) :
    ∀ e : NExpr, reads t (e.peval k) = false
  | .lit _ => rfl
  | .hole _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases h : k n with
    | none =>
      have hne : n ≠ t := fun hnt => by rw [hnt] at h; simp [h] at ht
      simpa [reads] using hne
    | some _ => rfl
  | .field (.hole _) _ => rfl
  | .add x y => by
    simp only [NExpr.peval]
    exact reads_addN t _ _ (reads_peval ht x) (reads_peval ht y)
  | .sub x y => by
    simp only [NExpr.peval]
    exact reads_subN t _ _ (reads_peval ht x) (reads_peval ht y)

theorem mem_of_lookup {α : Type} : ∀ (l : List (String × α)) (h : String) (n : α),
    l.lookup h = some n → (h, n) ∈ l
  | [], _, _, hl => by simp at hl
  | (k, v) :: rest, h, n, hl => by
    by_cases hk : h = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
      simp [hl]
    · have hne : (h == k) = false := by simpa using hk
      simp only [List.lookup, hne] at hl
      exact List.mem_cons_of_mem _ (mem_of_lookup rest h n hl)

/-- A fill a membrane admits: every page it names is one the membrane permits. -/
def fillAdmitted (m : MembraneViewer) (a : Assignment) : Bool := a.pages.all fun p => m.permits p.2

/-- Filling holes with pages other than `t` does not make an expression read `t`. -/
theorem reads_subst {t : String} {a : Assignment} (ha : ∀ p, p ∈ a.pages → p.2 ≠ t) :
    ∀ e : NExpr, reads t e = false → reads t (e.subst a) = false
  | .lit _, _ => rfl
  | .hole h, _ => by
    simp only [NExpr.subst]
    split <;> rfl
  | .field (.page _) _, h => h
  | .field (.hole h) _, _ => by
    simp only [NExpr.subst, PRef.subst]
    cases hl : a.pages.lookup h with
    | none => rfl
    | some n => simpa [reads] using ha _ (mem_of_lookup _ _ _ hl)
  | .add x y, h => by
    simp only [reads, Bool.or_eq_false_iff] at h
    simp [NExpr.subst, reads, reads_subst ha x h.1, reads_subst ha y h.2]
  | .sub x y, h => by
    simp only [reads, Bool.or_eq_false_iff] at h
    simp [NExpr.subst, reads, reads_subst ha x h.1, reads_subst ha y h.2]

/-- An expression that does not read `t` evaluates alike under knowledge that differs only at `t`. -/
theorem eval_congr_off {t : String} {k₁ k₂ : Known} (hk : ∀ n, n ≠ t → k₁ n = k₂ n) :
    ∀ e : NExpr, reads t e = false → e.eval k₁ = e.eval k₂
  | .lit _, _ => rfl
  | .hole _, _ => rfl
  | .field (.page n) f, h => by
    have hne : n ≠ t := by simpa [reads] using h
    simp [NExpr.eval, hk n hne]
  | .field (.hole _) _, _ => rfl
  | .add x y, h => by
    simp only [reads, Bool.or_eq_false_iff] at h
    simp only [NExpr.eval, eval_congr_off hk x h.1, eval_congr_off hk y h.2]
  | .sub x y, h => by
    simp only [reads, Bool.or_eq_false_iff] at h
    simp only [NExpr.eval, eval_congr_off hk x h.1, eval_congr_off hk y h.2]

/-- **An attenuated pin hides the backing cell.** Its membrane holds no more than the crossing
capability and does not permit the backing cell; the residual reads the backing cell nowhere; and
under every admitted fill its value is the same whatever the backing cell holds at evaluation. -/
theorem attenuate_peval_hides_backing_slots {f : Frustum} {cap : Cap} {ask m : MembraneViewer}
    {expr residual : NExpr}
    (h : makeFace f cap (.attenuate ask expr) = .attenuated m residual) :
    m.held ⊆ cap.rights ∧ m.permits cap.target = false ∧
    residual = expr.peval (backingKnown f cap.target) ∧
    reads cap.target residual = false ∧
    ∀ (a : Assignment) (k₁ k₂ : Known), fillAdmitted m a = true →
      (∀ n, n ≠ cap.target → k₁ n = k₂ n) →
      (residual.subst a).eval k₁ = (residual.subst a).eval k₂ := by
  unfold makeFace at h
  cases hv : f.reflect cap.target with
  | none => simp [hv, severFace] at h
  | some v =>
    cases hm : Membrane.reshare (pinHolder cap) (hideBacking cap.target ask) with
    | none => simp [hv, hm, severFace] at h
    | some m' =>
      simp only [hv, hm, PinFace.attenuated.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hatt := reshare_some_attenuates (φ := Unit) hm
      have hperm : m'.permits cap.target = false := by
        unfold Membrane.reshare at hm
        split at hm
        · simp only [Option.some.injEq] at hm
          subst hm
          simp [hideBacking]
        · simp at hm
      have hknown : (backingKnown f cap.target cap.target).isSome = true := by
        simp [backingKnown, hv]
      have hreads := reads_peval hknown expr
      refine ⟨hatt.1, hperm, rfl, hreads, fun a k₁ k₂ ha hk => ?_⟩
      apply eval_congr_off hk
      apply reads_subst _ _ hreads
      intro p hp hpt
      have hpp := List.all_eq_true.mp ha p hp
      rw [hpt, hperm] at hpp
      exact absurd hpp (by simp)

/-- **Attenuation preserves the meaning on what stays public**: the residual evaluates as the
original does, under any knowledge agreeing with what the frustum showed of the backing cell. -/
theorem attenuate_preserves_public_semantics (f : Frustum) (target : CellId) (expr : NExpr)
    (a : Assignment) (k : Known) (hk : Agrees (backingKnown f target) k) :
    ((expr.peval (backingKnown f target)).subst a).eval k = (expr.subst a).eval k :=
  eval_subst_peval hk a expr

/-! ## 5. Turns against a screenshot -/

/-- One natural field of a cell written, and its epoch advanced. -/
def World.poke (w : World) (c : CellId) (field : String) (value : Nat) : World :=
  match w.cell c with
  | some r => w.set c { r with state := putNat r.state field value, epoch := r.epoch + 1 }
  | none => w

theorem World.poke_cell_ne {w : World} {c u : CellId} (field : String) (value : Nat) (hne : u ≠ c) :
    (w.poke c field value).cell u = w.cell u := by
  unfold World.poke
  split
  · exact World.set_cell_ne _ hne
  · rfl

/-- A turn taken by the holder of a screenshot. -/
inductive LocalTurn where
  | edit (cell : CellId) (field : String) (value : Nat)
  | viaPin (holder target : CellId) (field : String) (value : Nat)

/-- The world upstream and a screenshot cut from it. -/
structure Sys where
  upstream : World
  shot : Screenshot

def pinMatches (holder target : CellId) (p : BoundaryPin) : Bool :=
  p.holder == holder && p.target == target

/-- A write through a pin reaches upstream only if a matching pin is tethered and carries `write`. -/
def tetherWrites (pins : List BoundaryPin) (holder target : CellId) : Bool :=
  pins.any fun p => pinMatches holder target p && p.face.isTethered && p.rights.contains Auth.write

/-- A write through an interposed pin lands on its local stand-in. -/
def writeMock (holder target : CellId) (field : String) (value : Nat) (p : BoundaryPin) :
    BoundaryPin :=
  if pinMatches holder target p && p.rights.contains Auth.write then
    match p.face with
    | .interposed mock => { p with face := .interposed (putNat mock field value) }
    | _ => p
  else p

def editCaptured (c : CellId) (field : String) (value : Nat) (x : Captured) : Captured :=
  if x.id == c then { x with now := putNat x.now field value } else x

def stepSys (s : Sys) : LocalTurn → Sys
  | .edit c field value =>
    { s with shot := { s.shot with interior := s.shot.interior.map (editCaptured c field value) } }
  | .viaPin holder target field value =>
    { upstream :=
        if tetherWrites s.shot.pins holder target then s.upstream.poke target field value
        else s.upstream,
      shot := { s.shot with pins := s.shot.pins.map (writeMock holder target field value) } }

def runSys (s : Sys) (ts : List LocalTurn) : Sys := ts.foldl stepSys s

/-- No pin onto `u` is tethered. -/
def UntetheredAt (pins : List BoundaryPin) (u : CellId) : Prop :=
  ∀ p, p ∈ pins → p.target = u → p.face.isTethered = false

/-- Pin for pin, the same holder, target and rights, tethered only where it was. -/
def PinsWithin (pins' pins : List BoundaryPin) : Prop :=
  ∀ p', p' ∈ pins' → ∃ p, p ∈ pins ∧ p'.holder = p.holder ∧ p'.target = p.target ∧
    p'.rights = p.rights ∧ p'.face.isTethered = p.face.isTethered

theorem writeMock_same (holder target : CellId) (field : String) (value : Nat) (p : BoundaryPin) :
    (writeMock holder target field value p).holder = p.holder ∧
    (writeMock holder target field value p).target = p.target ∧
    (writeMock holder target field value p).rights = p.rights ∧
    (writeMock holder target field value p).face.isTethered = p.face.isTethered := by
  unfold writeMock
  split
  · split <;> simp_all [PinFace.isTethered]
  · simp

theorem stepSys_pinsWithin (s : Sys) (t : LocalTurn) : PinsWithin (stepSys s t).shot.pins s.shot.pins := by
  intro p' hp'
  cases t with
  | edit c field value => exact ⟨p', hp', rfl, rfl, rfl, rfl⟩
  | viaPin holder target field value =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    exact ⟨p, hp, writeMock_same holder target field value p⟩

theorem stepSys_untouched (s : Sys) (t : LocalTurn) (u : CellId) (h : UntetheredAt s.shot.pins u) :
    (stepSys s t).upstream.cell u = s.upstream.cell u := by
  cases t with
  | edit c field value => rfl
  | viaPin holder target field value =>
    simp only [stepSys]
    split
    · rename_i hw
      obtain ⟨p, hp, hcond⟩ := List.any_eq_true.mp hw
      simp only [Bool.and_eq_true, pinMatches, beq_iff_eq] at hcond
      have hne : u ≠ target := by
        intro hut
        have := h p hp (hcond.1.1.2.trans hut.symm)
        rw [hcond.1.2] at this
        exact absurd this (by simp)
      exact World.poke_cell_ne field value hne
    · rfl

/-- **Turns against a screenshot never touch a cell behind an untethered pin.** If every pin onto
`u` is severed, attenuated or interposed, then after any list of turns `u` is upstream as it was,
no pin onto `u` is tethered, and the pins confer nothing they did not confer at the start. -/
theorem interposed_frustum_never_touches_severed_upstream (ts : List LocalTurn) :
    ∀ (s : Sys) (u : CellId), UntetheredAt s.shot.pins u →
      (runSys s ts).upstream.cell u = s.upstream.cell u ∧
      UntetheredAt (runSys s ts).shot.pins u ∧
      PinsWithin (runSys s ts).shot.pins s.shot.pins := by
  induction ts with
  | nil => intro s u h; exact ⟨rfl, h, fun p hp => ⟨p, hp, rfl, rfl, rfl, rfl⟩⟩
  | cons t ts ih =>
    intro s u h
    have hwithin := stepSys_pinsWithin s t
    have hstep : UntetheredAt (stepSys s t).shot.pins u := by
      intro p' hp' ht
      obtain ⟨p, hp, _, htar, _, hteth⟩ := hwithin p' hp'
      rw [hteth]
      exact h p hp (htar ▸ ht)
    obtain ⟨hcell, hunt, hpins⟩ := ih (stepSys s t) u hstep
    refine ⟨?_, hunt, ?_⟩
    · show (runSys (stepSys s t) ts).upstream.cell u = s.upstream.cell u
      rw [hcell, stepSys_untouched s t u h]
    · intro p'' hp''
      obtain ⟨p', hp', h1, h2, h3, h4⟩ := hpins p'' hp''
      obtain ⟨p, hp, g1, g2, g3, g4⟩ := hwithin p' hp'
      exact ⟨p, hp, h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

/-! ## 6. The return: re-grafting a screenshot onto the world as it is now -/

/-- An interior cell may land: it is upstream at the captured epoch, under a held `write`. -/
def interiorFresh (w : World) (viewer : CellId) (x : Captured) : Bool :=
  match w.cell x.id with
  | some r => r.epoch == x.epoch && (w.heldOn viewer x.id).contains Auth.write
  | none => false

/-- A severed pin is fresh when its target reads now, through the viewer, as its snapshot says. -/
def pinFresh (w : World) (viewer : CellId) (p : BoundaryPin) : Bool :=
  match p.face with
  | .severed _ snapshot _ => decide (pinDigest p.target (readingOf (w.look viewer p.target)) = snapshot)
  | _ => true

def nodupIds : List Captured → Bool
  | [] => true
  | x :: xs => !(xs.any fun y => y.id == x.id) && nodupIds xs

/-- The value of a natural field of a cell; zero where there is no cell. -/
def World.balance (w : World) (f : String) (c : CellId) : Nat :=
  match w.cell c with
  | some r => natAt r.state f
  | none => 0

/-- A field's total over a list of cells. -/
def World.total (w : World) (f : String) (cells : List CellId) : Nat := (cells.map (w.balance f)).sum

/-- The edited interior holds, in total, what the same cells hold upstream now. -/
def balanced (w : World) (interior : List Captured) (f : String) : Bool :=
  (interior.map fun x => natAt x.now f).sum == (interior.map fun x => w.balance f x.id).sum

/-- Why a screenshot was not re-grafted. -/
inductive RegraftRefusal where
  | staleInterior (cell : CellId)
  | staleBoundary (holder target : CellId)
  | duplicateInterior
  | unbalanced (field : String)
deriving DecidableEq, Repr

/-- The interior's edits landed: each interior cell takes its edited state and the next epoch. -/
def graft (w : World) (interior : List Captured) : World :=
  { ids := w.ids, facts := w.facts,
    cell := fun c => match interior.find? (fun x => x.id == c) with
      | some x => (w.cell c).map fun r => { r with state := x.now, epoch := r.epoch + 1 }
      | none => w.cell c,
    covered := by
      intro c hc
      apply w.covered
      split at hc
      · simpa using hc
      · exact hc }

/-- **Re-graft a screenshot**, or say why not. -/
def regraftFrustum (w : World) (s : Screenshot) : Except RegraftRefusal World :=
  match s.interior.find? (fun x => !interiorFresh w s.viewer x) with
  | some x => .error (.staleInterior x.id)
  | none =>
    match s.pins.find? (fun p => !pinFresh w s.viewer p) with
    | some p => .error (.staleBoundary p.holder p.target)
    | none =>
      if nodupIds s.interior then
        match s.conserved.find? (fun f => !balanced w s.interior f) with
        | some f => .error (.unbalanced f)
        | none => .ok (graft w s.interior)
      else .error .duplicateInterior

/-- What an admitted re-graft checked. -/
theorem regraft_ok {w w' : World} {s : Screenshot} (h : regraftFrustum w s = .ok w') :
    (∀ x, x ∈ s.interior → interiorFresh w s.viewer x = true) ∧
    (∀ p, p ∈ s.pins → pinFresh w s.viewer p = true) ∧
    nodupIds s.interior = true ∧
    (∀ f, f ∈ s.conserved → balanced w s.interior f = true) ∧
    w' = graft w s.interior := by
  unfold regraftFrustum at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · rename_i h3
        split at h
        · cases h
        · rename_i h4
          simp only [Except.ok.injEq] at h
          refine ⟨fun x hx => ?_, fun p hp => ?_, h3, fun f hf => ?_, h.symm⟩
          · simpa using List.find?_eq_none.mp h1 x hx
          · simpa using List.find?_eq_none.mp h2 p hp
          · simpa using List.find?_eq_none.mp h4 f hf
      · cases h

theorem find_of_nodupIds : ∀ (l : List Captured) (x : Captured), nodupIds l = true → x ∈ l →
    l.find? (fun y => y.id == x.id) = some x
  | [], _, _, hx => by simp at hx
  | y :: ys, x, hn, hx => by
    simp only [nodupIds, Bool.and_eq_true, Bool.not_eq_true'] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [List.find?]
    · have hne : (y.id == x.id) = false := by
        cases hb : (y.id == x.id) with
        | false => rfl
        | true =>
          have hany : (ys.any fun z => z.id == y.id) = true :=
            List.any_eq_true.mpr ⟨x, hx, by simpa using (beq_iff_eq.mp hb).symm⟩
          rw [hn.1] at hany
          exact absurd hany (by simp)
      simp only [List.find?, hne]
      exact find_of_nodupIds ys x hn.2 hx

/-- **Re-grafting is atomic and conserving.** An admitted re-graft lands every interior cell with
its edited state and the next epoch, against its captured epoch and under a `write` the viewer holds
now; leaves every other cell, whatever happened to it since the cut, as the world has it; and keeps
each conserved field's total over the interior and any cells beside it. A refusal returns no world. -/
theorem regraftFrustum_atomic_conserving {w w' : World} {s : Screenshot}
    (h : regraftFrustum w s = .ok w') :
    (∀ x, x ∈ s.interior → ∃ r, w.cell x.id = some r ∧ r.epoch = x.epoch ∧
      Auth.write ∈ w.heldOn s.viewer x.id ∧
      w'.cell x.id = some { r with state := x.now, epoch := r.epoch + 1 }) ∧
    (∀ c, (∀ x, x ∈ s.interior → x.id ≠ c) → w'.cell c = w.cell c) ∧
    (∀ f, f ∈ s.conserved → ∀ rest : List CellId,
      (∀ c, c ∈ rest → ∀ x, x ∈ s.interior → x.id ≠ c) →
      w'.total f (s.interior.map (·.id) ++ rest) = w.total f (s.interior.map (·.id) ++ rest)) ∧
    w'.ids = w.ids := by
  obtain ⟨hfresh, _, hnodup, hbal, rfl⟩ := regraft_ok h
  have hin : ∀ x, x ∈ s.interior → ∃ r, w.cell x.id = some r ∧ r.epoch = x.epoch ∧
      Auth.write ∈ w.heldOn s.viewer x.id ∧
      (graft w s.interior).cell x.id = some { r with state := x.now, epoch := r.epoch + 1 } := by
    intro x hx
    have hf := hfresh x hx
    unfold interiorFresh at hf
    cases hr : w.cell x.id with
    | none => simp [hr] at hf
    | some r =>
      simp only [hr, Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hf
      refine ⟨r, rfl, hf.1, hf.2, ?_⟩
      simp [graft, find_of_nodupIds s.interior x hnodup hx, hr]
  have hout : ∀ c, (∀ x, x ∈ s.interior → x.id ≠ c) → (graft w s.interior).cell c = w.cell c := by
    intro c hc
    have hnone : s.interior.find? (fun x => x.id == c) = none :=
      List.find?_eq_none.mpr fun x hx => by simpa using hc x hx
    simp [graft, hnone]
  refine ⟨hin, hout, fun f hf rest hrest => ?_, rfl⟩
  have hb := hbal f hf
  simp only [balanced, beq_iff_eq] at hb
  have hint : (s.interior.map fun x => (graft w s.interior).balance f x.id) =
      s.interior.map fun x => natAt x.now f := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨r, _, _, _, hg⟩ := hin x hx
    simp [World.balance, hg]
  have hrest' : rest.map ((graft w s.interior).balance f) = rest.map (w.balance f) := by
    apply List.map_congr_left
    intro c hc
    simp [World.balance, hout c (hrest c hc)]
  simp only [World.total, List.map_append, List.map_map, List.sum_append_nat, hrest']
  have hcomp : ((graft w s.interior).balance f ∘ fun x : Captured => x.id) =
      fun x => (graft w s.interior).balance f x.id := rfl
  have hcomp' : (w.balance f ∘ fun x : Captured => x.id) = fun x => w.balance f x.id := rfl
  rw [hcomp, hcomp', hint, hb]

/-- **A stale interior is refused, and the refusal names a stale cell**: one gone upstream, moved
past its captured epoch, or no longer writable by the viewer. -/
theorem regraft_refuses_stale_interior {w : World} {s : Screenshot} {x : Captured}
    (hx : x ∈ s.interior) (hstale : interiorFresh w s.viewer x = false) :
    ∃ y, y ∈ s.interior ∧ interiorFresh w s.viewer y = false ∧
      regraftFrustum w s = .error (.staleInterior y.id) := by
  unfold regraftFrustum
  cases hf : s.interior.find? (fun x => !interiorFresh w s.viewer x) with
  | none =>
    have := List.find?_eq_none.mp hf x hx
    simp [hstale] at this
  | some y =>
    have hy := List.find?_some hf
    exact ⟨y, List.mem_of_find?_eq_some hf, by simpa using hy, rfl⟩

/-- **A moved boundary is refused**, naming a severed pin whose target no longer reads as cut. -/
theorem regraft_refuses_stale_boundary {w : World} {s : Screenshot} {p : BoundaryPin}
    (hint : ∀ x, x ∈ s.interior → interiorFresh w s.viewer x = true)
    (hp : p ∈ s.pins) (hstale : pinFresh w s.viewer p = false) :
    ∃ q, q ∈ s.pins ∧ pinFresh w s.viewer q = false ∧
      regraftFrustum w s = .error (.staleBoundary q.holder q.target) := by
  unfold regraftFrustum
  have h1 : s.interior.find? (fun x => !interiorFresh w s.viewer x) = none :=
    List.find?_eq_none.mpr fun x hx => by simp [hint x hx]
  rw [h1]
  cases hf : s.pins.find? (fun p => !pinFresh w s.viewer p) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    simp [hstale] at this
  | some q =>
    have hq := List.find?_some hf
    exact ⟨q, List.mem_of_find?_eq_some hf, by simpa using hq, rfl⟩

/-- **An admitted severed pin's target has not moved, or the pin hash collided.** For a pin whose
snapshot digests its recorded reading (every pin `Frustum.snip` makes), an admitted re-graft found
the target's epoch and natural slots equal to that reading, or the two readings collide. -/
theorem regraft_boundary_fresh_or_collision {w w' : World} {s : Screenshot}
    (h : regraftFrustum w s = .ok w') {p : BoundaryPin} (hp : p ∈ s.pins)
    {reading : Nat × List (String × Nat)} {log : InteractionLog}
    (hface : p.face = .severed reading (pinDigest p.target reading) log) :
    readingOf (w.look s.viewer p.target) = reading ∨
      CollisionAmong (cshake256Bytes pinCustomization) (fun x =>
        x = pinPreimage p.target (readingOf (w.look s.viewer p.target)) ∨
        x = pinPreimage p.target reading) := by
  have hf := (regraft_ok h).2.1 p hp
  unfold pinFresh at hf
  rw [hface] at hf
  exact pinDigest_binds (by simpa using hf)

/-! ## 7. Replay: confinement is what makes it a function of the trace -/

/-- The replay: a left fold of a step over the witnessed trace. -/
def replayState {σ : Type} (step : σ → Interaction → σ) (s₀ : σ) (trace : InteractionLog) : σ :=
  trace.foldl step s₀

/-- A replay step that reads the witness on an attested interaction and the environment on an
ambient one: the only way a reconstruction can depend on what its trace does not carry. -/
def envStep {σ ε : Type} (base : σ → AttestedRoot → σ) (amb : σ → ε → σ) (env : ε) :
    σ → Interaction → σ :=
  fun s i => match i with
    | .attested ar => base s ar
    | .ambient => amb s env

/-- **A confined trace replays the same under every environment.** The premise is used: without
it the conclusion fails (`ambient_replay_env_dependent`). -/
theorem confined_replay_env_independent {σ ε : Type} (base : σ → AttestedRoot → σ)
    (amb : σ → ε → σ) (env₁ env₂ : ε) (trace : InteractionLog) (s₀ : σ)
    (h : confined trace = true) :
    replayState (envStep base amb env₁) s₀ trace = replayState (envStep base amb env₂) s₀ trace := by
  induction trace generalizing s₀ with
  | nil => rfl
  | cons i rest ih =>
    simp only [confined, List.all_cons, Bool.and_eq_true] at h
    cases i with
    | attested ar =>
      simp only [replayState, List.foldl_cons, envStep]
      exact ih (base s₀ ar) (by simpa [confined] using h.2)
    | ambient => simp [Interaction.isWitnessed] at h

/-- **One ambient step makes the replay depend on the environment**: after any prefix, a trace
ending in an ambient step that adopts the environment replays differently, and is not confined. -/
theorem ambient_replay_env_dependent {ε : Type} (base : ε → AttestedRoot → ε)
    (pre : InteractionLog) (s₀ env₁ env₂ : ε) (hne : env₁ ≠ env₂) :
    confined (pre ++ [Interaction.ambient]) = false ∧
    replayState (envStep base (fun _ e => e) env₁) s₀ (pre ++ [Interaction.ambient]) ≠
      replayState (envStep base (fun _ e => e) env₂) s₀ (pre ++ [Interaction.ambient]) := by
  constructor
  · simp [confined, Interaction.isWitnessed]
  · simp only [replayState, List.foldl_append, List.foldl_cons, List.foldl_nil, envStep]
    exact hne

/-! ## 8. Negotiation: the meet of what is held and what is asked -/

/-- The circumstances a capability is exercised in. -/
structure NegCtx where
  height : Nat
  amount : Nat
deriving DecidableEq, Repr

/-- A restriction on the exercise of a capability. -/
inductive Caveat where
  | notAfter (height : Nat)
  | amountAtMost (limit : Nat)
deriving DecidableEq, Repr

def Caveat.admits : Caveat → NegCtx → Bool
  | .notAfter h, ctx => decide (ctx.height ≤ h)
  | .amountAtMost n, ctx => decide (ctx.amount ≤ n)

/-- A capability as negotiated: a target, rights over it, and caveats on their exercise. -/
structure NegCap where
  target : CellId
  rights : List Auth
  caveats : List Caveat
deriving DecidableEq, Repr

/-- **What a capability confers**: right `a` over target `t` in circumstances `ctx`. -/
def NegCap.confers (c : NegCap) (t : CellId) (a : Auth) (ctx : NegCtx) : Bool :=
  c.target == t && c.rights.contains a && c.caveats.all (·.admits ctx)

/-- `c` confers nothing `d` does not. -/
def NegCap.Attenuates (c d : NegCap) : Prop :=
  ∀ t a ctx, c.confers t a ctx = true → d.confers t a ctx = true

/-- **The negotiated capability**, `held ⊓ ask`: the granter's target, the rights both name (none
if the ask names another target), under the caveats of both. -/
def negotiate (held ask : NegCap) : NegCap :=
  { target := held.target,
    rights := if ask.target = held.target then held.rights.filter ask.rights.contains else [],
    caveats := held.caveats ++ ask.caveats }

/-- **The meet law.** The negotiated capability confers exactly what both confer. -/
theorem negotiate_confers (held ask : NegCap) (t : CellId) (a : Auth) (ctx : NegCtx) :
    (negotiate held ask).confers t a ctx = (held.confers t a ctx && ask.confers t a ctx) := by
  rw [Bool.eq_iff_iff]
  simp only [NegCap.confers, negotiate, Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem,
    decide_eq_true_eq, List.all_append]
  constructor
  · rintro ⟨⟨ht, hr⟩, hc₁, hc₂⟩
    split at hr
    · rename_i hat
      rw [List.mem_filter] at hr
      exact ⟨⟨⟨ht, hr.1⟩, hc₁⟩, ⟨hat.trans ht, by simpa using hr.2⟩, hc₂⟩
    · simp at hr
  · rintro ⟨⟨⟨ht, hr⟩, hc₁⟩, ⟨hat, hr'⟩, hc₂⟩
    refine ⟨⟨ht, ?_⟩, hc₁, hc₂⟩
    split
    · rw [List.mem_filter]
      exact ⟨hr, by simpa using hr'⟩
    · rename_i hn
      exact absurd (hat.trans ht.symm) hn

/-- **The negotiated capability attenuates both parties, and is the greatest that does.** -/
theorem negotiated_attenuates (held ask : NegCap) :
    (negotiate held ask).Attenuates held ∧ (negotiate held ask).Attenuates ask ∧
    ∀ c : NegCap, c.Attenuates held → c.Attenuates ask → c.Attenuates (negotiate held ask) := by
  refine ⟨fun t a ctx h => ?_, fun t a ctx h => ?_, fun c h₁ h₂ t a ctx h => ?_⟩
  · rw [negotiate_confers, Bool.and_eq_true] at h; exact h.1
  · rw [negotiate_confers, Bool.and_eq_true] at h; exact h.2
  · rw [negotiate_confers, Bool.and_eq_true]; exact ⟨h₁ t a ctx h, h₂ t a ctx h⟩

/-- The meet is idempotent, commutative and associative in what it confers. -/
theorem negotiate_meet_laws (x y z : NegCap) (t : CellId) (a : Auth) (ctx : NegCtx) :
    (negotiate x x).confers t a ctx = x.confers t a ctx ∧
    (negotiate x y).confers t a ctx = (negotiate y x).confers t a ctx ∧
    (negotiate (negotiate x y) z).confers t a ctx =
      (negotiate x (negotiate y z)).confers t a ctx := by
  simp only [negotiate_confers]
  refine ⟨Bool.and_self _, Bool.and_comm _ _, Bool.and_assoc _ _ _⟩

/-- **No confused deputy.** Whatever is asked, the negotiated capability confers nothing over a
target or right the granter does not hold, and names the granter's own target. -/
theorem deputy_confers_no_unheld_target (held ask : NegCap) (t : CellId) (a : Auth) (ctx : NegCtx)
    (hunheld : held.confers t a ctx = false) :
    (negotiate held ask).confers t a ctx = false ∧ (negotiate held ask).target = held.target := by
  refine ⟨?_, rfl⟩
  rw [negotiate_confers, hunheld, Bool.false_and]

/-- An ask aimed at a cell the granter's capability does not name confers nothing over it. -/
theorem deputy_cannot_retarget (held ask : NegCap) (t : CellId) (hne : held.target ≠ t) (a : Auth)
    (ctx : NegCtx) : (negotiate held ask).confers t a ctx = false :=
  (deputy_confers_no_unheld_target held ask t a ctx (by simp [NegCap.confers, hne])).1

/-- A chain of negotiations: each party asks of what the last one got. -/
def negotiateChain (held : NegCap) (asks : List NegCap) : NegCap := asks.foldl negotiate held

theorem negotiateChain_confers (t : CellId) (a : Auth) (ctx : NegCtx) :
    ∀ (asks : List NegCap) (held : NegCap),
      (negotiateChain held asks).confers t a ctx =
        (held.confers t a ctx && asks.all (·.confers t a ctx))
  | [], held => by simp [negotiateChain]
  | x :: xs, held => by
    have ih := negotiateChain_confers t a ctx xs (negotiate held x)
    simp only [negotiateChain, List.foldl_cons] at ih ⊢
    rw [ih, negotiate_confers, List.all_cons, Bool.and_assoc]

/-- **Negotiation is path-independent**: a chain confers the same in any order and grouping of its
asks, and never more than the first holder held. -/
theorem negotiation_path_independent (held : NegCap) (asks asks' : List NegCap)
    (hperm : asks.Perm asks') (t : CellId) (a : Auth) (ctx : NegCtx) :
    (negotiateChain held asks).confers t a ctx = (negotiateChain held asks').confers t a ctx ∧
    (∀ pre post : List NegCap, asks = pre ++ post →
      (negotiateChain held asks).confers t a ctx =
        (negotiateChain (negotiateChain held pre) post).confers t a ctx) ∧
    ((negotiateChain held asks).confers t a ctx = true → held.confers t a ctx = true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [negotiateChain_confers, negotiateChain_confers]
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun h x hx => h x (hperm.mem_iff.mpr hx), fun h x hx => h x (hperm.mem_iff.mp hx)⟩
  · rintro pre post rfl
    simp only [negotiateChain, List.foldl_append]
  · intro h
    rw [negotiateChain_confers, Bool.and_eq_true] at h
    exact h.1

/-! ## 9. The premises are inhabited -/

/-- A three-cell world: `alice` reads and writes `bob`; `vault` is named by no one. -/
def demoWorld : World :=
  World.ofList ⟨none, none, 0, 0⟩
    [("alice", { state := .record [("balance", .natural 5)],
                 caps := [⟨"bob", [.read, .write]⟩, ⟨"alice", [.read, .write]⟩] }),
     ("bob", { state := .record [("balance", .natural 7)],
               sealed := [("pin", ⟨[1, 2, 3], [9]⟩)] }),
     ("vault", { state := .record [("balance", .natural 100)] })]

example : Reach demoWorld "alice" "bob" := canObserve_iff.mp (by decide)

example : ¬ Reach demoWorld "alice" "vault" := fun h => by
  have := canObserve_iff.mpr h
  revert this
  decide

example : ViewEquiv demoWorld (demoWorld.erase "vault") "alice" := by
  refine ⟨rfl, rfl, fun c hc => ?_, fun c hc => ?_⟩
  · have hne : c ≠ "vault" := fun hcv => by
      have := canObserve_iff.mpr (hcv ▸ hc)
      revert this
      decide
    simp [World.pub, World.erase, hne]
  · by_cases hcv : c = "vault"
    · simp [World.pub, World.erase, hcv] at hc
    · simpa [World.pub, World.erase, hcv] using hc

example : ∃ trace : InteractionLog, trace ≠ [] ∧ confined trace = true :=
  ⟨[.attested ⟨0, true, true⟩], by simp, by decide⟩

example : ∃ c d : NegCap, c ≠ d ∧ c.Attenuates d :=
  ⟨⟨"bob", [.read], []⟩, ⟨"bob", [.read, .write], []⟩, by decide,
    fun t a ctx h => by
      simp only [NegCap.confers, Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem,
        decide_eq_true_eq] at h ⊢
      exact ⟨⟨h.1.1, by rcases h.1.2 with _ | ⟨_, h⟩ <;> simp_all⟩, h.2⟩⟩

example : ∃ (m : MembraneViewer) (a : Assignment), a.pages ≠ [] ∧ fillAdmitted m a = true :=
  ⟨⟨[], fun _ => true, []⟩, { pages := [("p", "bob")] }, by simp, by simp [fillAdmitted]⟩

end Obend.Vault.FrustumMembrane

end
