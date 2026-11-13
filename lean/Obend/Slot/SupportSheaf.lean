module
/-
# Obend.Slot.SupportSheaf — Unified Footprint Sheaf & Coalgebraic Delta-Lens Transport

Unifies the contextual support-tracking copies across `Obend` (`Obend.Slot`, `Obend.Intention`,
`Obend.Logic.Obligation`, `Obend.Logic.SuperRefines`, ecosystem/section pins, and book pins) under
two Mathlib-free typeclasses:

1. **`SupportSheaf W Fact Obj`**:
   - Captures footprint extraction `supports : Obj → List Fact`, world satisfaction
     `holds : W → Fact → Bool`, usability `usable : W → Obj → Bool`, support soundness
     `usable_supports`, and sheaf locality / frame invariance `holds_frame`.

2. **`RepairableSheaf W Δ Fact Obj extends SupportSheaf W Fact Obj`**:
   - Clarke coalgebraic Delta-Lens pushforward `transport : Δ → Obj → Except Err Obj` over world
     transitions `applyDelta : Δ → W → W`, with locus footprint `changed : Δ → List Locus`,
     **zero-cost identity fast-path** (`transport_disjoint_fastpath`) when
     `disjoint (changed δ) (supports x)` holds, and **functorial composition** (`transport_comp`).
   - Proves universal $O(1)$ disjoint transport (`disjoint_transport_sound`,
     `disjoint_comp_transport_sound`) without re-running any underlying checker.

3. **Verified Instances & Witnesses**:
   - **`Obend.Slot` (`SlotFill S`)**: `SupportSheaf` over arbitrary `(Fact → Bool)` views and
     `RepairableSheaf` over keyed worlds `KeyedWorld K V` / `KeyedDelta K V`.
   - **`Obend.Intention` (`IntentionPin I r` & `RegPin`)**: `SupportSheaf` for every `Intention`,
     plus an active-rebinding coalgebraic `RepairableSheaf` (`RegPin`) that takes the identity
     fast-path on untouched packages, actively rebinds compatible minor updates, and refuses major
     breakages or yanks.
   - **`SuperClaimCert` (`PointedComp` & `OverlayDelta`)**: `RepairableSheaf` for vertical
     `super.m` refinement certificates from `Obend.Logic.SuperRefines`, proving that outer wrapper
     layers disjoint from `selfSupports` (even when overriding `superSupports`!) transport
     certificates in $O(1)$ via the identity fast-path without re-running `superClaimCheck`.
-/

public import Obend.Slot
public import Obend.Intention
public import Obend.Logic.Obligation
import all Obend.Logic.Obligation

public section

namespace Obend.Slot.SupportSheaf

open Obend.Core.Term
open Obend.Logic

set_option autoImplicit false

/-! ## 1. `SupportSheaf` & `RepairableSheaf` Typeclasses -/

/-- Sheaf of contextual footprints: usability at world `w` implies all cited `supports` hold at `w`,
and depends on `w` exclusively through the restriction of `holds w` to `supports x`. -/
class SupportSheaf (W : Type) (Fact : outParam Type) (Obj : Type) where
  supports : Obj → List Fact
  holds : W → Fact → Bool
  usable : W → Obj → Bool
  usable_supports : ∀ (w : W) (x : Obj),
    usable w x = true → ∀ f ∈ supports x, holds w f = true
  holds_frame : ∀ {w₁ w₂ : W} {x : Obj},
    (∀ f ∈ supports x, holds w₁ f = holds w₂ f) → usable w₁ x = usable w₂ x

/-- Dead supports of `x` at world `w`: those cited in `supports x` where `holds w` is `false`. -/
def deadSupports {W Fact Obj : Type} [S : SupportSheaf W Fact Obj]
    (w : W) (x : Obj) : List Fact :=
  (S.supports x).filter fun f => !S.holds w f

/-- Evidence table pairing each cited support of `x` with its Boolean truth value at `w`. -/
def supportEvidence {W Fact Obj : Type} [S : SupportSheaf W Fact Obj]
    (w : W) (x : Obj) : List (Fact × Bool) :=
  (S.supports x).map fun f => (f, S.holds w f)

/-- Monotone frame corollary: if `x` is usable at `w₁` and every support of `x` that holds at `w₁`
still holds at `w₂`, then `x` remains usable at `w₂`. -/
theorem usable_of_supports_preserved {W Fact Obj : Type} [S : SupportSheaf W Fact Obj]
    {w₁ w₂ : W} {x : Obj}
    (hu : S.usable w₁ x = true)
    (hkeep : ∀ f ∈ S.supports x, S.holds w₁ f = true → S.holds w₂ f = true) :
    S.usable w₂ x = true := by
  have hagree : ∀ f ∈ S.supports x, S.holds w₁ f = S.holds w₂ f := by
    intro f hf
    have h1 := S.usable_supports w₁ x hu f hf
    have h2 := hkeep f hf h1
    rw [h1, h2]
  rw [← S.holds_frame hagree]
  exact hu

/-- Any single dead support blocks usability and appears in `deadSupports`. -/
theorem dead_blocks_usable {W Fact Obj : Type} [S : SupportSheaf W Fact Obj]
    {w : W} {x : Obj} {f : Fact}
    (hf : f ∈ S.supports x) (hdead : S.holds w f = false) :
    S.usable w x = false ∧ f ∈ deadSupports w x := by
  refine ⟨?_, List.mem_filter.2 ⟨hf, by simp [hdead]⟩⟩
  cases hu : S.usable w x with
  | false => rfl
  | true =>
    have htrue := S.usable_supports w x hu f hf
    rw [htrue] at hdead
    cases hdead

/-- `deadSupports` is itself frame-invariant over `supports x`. -/
theorem deadSupports_frame {W Fact Obj : Type} [S : SupportSheaf W Fact Obj]
    {w₁ w₂ : W} {x : Obj}
    (h : ∀ f ∈ S.supports x, S.holds w₁ f = S.holds w₂ f) :
    deadSupports w₁ x = deadSupports w₂ x := by
  unfold deadSupports
  apply List.filter_congr
  intro f hf
  rw [h f hf]

/-- Clarke coalgebraic Delta-Lens pushforward over a `SupportSheaf`:
worlds evolve by deltas `Δ` (`applyDelta`), each delta reports its mutated loci (`changed`),
and objects push forward via `transport : Δ → Obj → Except Err Obj` with a zero-cost identity
fast-path when `changed δ` is disjoint from `supports x`, plus functorial delta composition. -/
class RepairableSheaf (W Δ : Type) (Fact : outParam Type) (Obj : Type)
    extends SupportSheaf W Fact Obj where
  Locus : outParam Type
  Err : outParam Type
  [decEqLocus : DecidableEq Locus]
  factLocus : Fact → Locus
  changed : Δ → List Locus
  idDelta : Δ
  compDelta : Δ → Δ → Δ
  applyDelta : Δ → W → W
  transport : Δ → Obj → Except Err Obj
  applyDelta_id : ∀ (w : W), applyDelta idDelta w = w
  applyDelta_comp : ∀ (δ₂ δ₁ : Δ) (w : W),
    applyDelta (compDelta δ₂ δ₁) w = applyDelta δ₂ (applyDelta δ₁ w)
  changed_id : changed idDelta = []
  changed_comp_sub : ∀ (δ₂ δ₁ : Δ) (loc : Locus),
    loc ∈ changed (compDelta δ₂ δ₁) → loc ∈ changed δ₁ ∨ loc ∈ changed δ₂
  delta_frame_fact : ∀ (δ : Δ) (w : W) (f : Fact),
    factLocus f ∉ changed δ → holds (applyDelta δ w) f = holds w f
  transport_disjoint_fastpath : ∀ (δ : Δ) (x : Obj),
    (∀ f ∈ supports x, factLocus f ∉ changed δ) → transport δ x = .ok x
  transport_comp : ∀ (δ₂ δ₁ : Δ) (x : Obj),
    transport (compDelta δ₂ δ₁) x = (transport δ₁ x).bind (transport δ₂)

@[expose, instance_reducible, instance] def instDecEqRepairableLocus
    {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj] : DecidableEq S.Locus :=
  S.decEqLocus

/-- Boolean footprint disjointness test between a delta's `changed` loci and `supports x`. -/
@[expose] def disjoint {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj]
    (loci : List S.Locus) (sps : List Fact) : Bool :=
  sps.all fun f => decide (S.factLocus f ∉ loci)

theorem disjoint_eq_true_iff {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj]
    (loci : List S.Locus) (sps : List Fact) :
    disjoint (S := S) loci sps = true ↔ ∀ f ∈ sps, S.factLocus f ∉ loci := by
  simp [disjoint, List.all_eq_true]

/-- Identity pushforward law, derived directly from `changed_id` + `transport_disjoint_fastpath`. -/
theorem transport_id {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj] (x : Obj) :
    S.transport S.idDelta x = .ok x := by
  apply S.transport_disjoint_fastpath
  intro f _
  rw [S.changed_id]
  intro hmem
  cases hmem

/-- **Universal $O(1)$ Disjoint Fast-Path Soundness (`disjoint_transport_sound`)**:
When `x` is usable at `w` and `disjoint (changed δ) (supports x)` holds, `transport δ x` returns
`.ok x` immediately (identity fast-path) and `x` remains usable at `applyDelta δ w` without
re-running any underlying checker. -/
theorem disjoint_transport_sound {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj]
    {w : W} {δ : Δ} {x : Obj}
    (hu : S.usable w x = true)
    (hdisj : disjoint (S := S) (S.changed δ) (S.supports x) = true) :
    S.transport δ x = .ok x ∧ S.usable (S.applyDelta δ w) x = true := by
  have hnot := (disjoint_eq_true_iff (S := S) (S.changed δ) (S.supports x)).1 hdisj
  refine ⟨S.transport_disjoint_fastpath δ x hnot, ?_⟩
  have hagree : ∀ f ∈ S.supports x, S.holds (S.applyDelta δ w) f = S.holds w f :=
    fun f hf => S.delta_frame_fact δ w f (hnot f hf)
  rw [S.holds_frame hagree]
  exact hu

/-- Sequential composition of disjoint deltas preserves both the identity fast-path and usability. -/
theorem disjoint_comp_transport_sound {W Δ Fact Obj : Type} [S : RepairableSheaf W Δ Fact Obj]
    {w : W} {δ₂ δ₁ : Δ} {x : Obj}
    (hu : S.usable w x = true)
    (hd₁ : disjoint (S := S) (S.changed δ₁) (S.supports x) = true)
    (hd₂ : disjoint (S := S) (S.changed δ₂) (S.supports x) = true) :
    disjoint (S := S) (S.changed (S.compDelta δ₂ δ₁)) (S.supports x) = true ∧
    S.transport (S.compDelta δ₂ δ₁) x = .ok x ∧
    S.usable (S.applyDelta (S.compDelta δ₂ δ₁) w) x = true := by
  have hn₁ := (disjoint_eq_true_iff (S := S) (S.changed δ₁) (S.supports x)).1 hd₁
  have hn₂ := (disjoint_eq_true_iff (S := S) (S.changed δ₂) (S.supports x)).1 hd₂
  have hcomp : disjoint (S := S) (S.changed (S.compDelta δ₂ δ₁)) (S.supports x) = true := by
    rw [disjoint_eq_true_iff]
    intro f hf hmem
    rcases S.changed_comp_sub δ₂ δ₁ (S.factLocus f) hmem with h1 | h2
    · exact hn₁ f hf h1
    · exact hn₂ f hf h2
  obtain ⟨htr, hus⟩ := disjoint_transport_sound hu hcomp
  exact ⟨hcomp, htr, hus⟩

/-! ## 2. Instance 1: `Obend.Slot` (`SlotFill` & Keyed World Deltas) -/

/-- Candidate wrapper associating a value `cand : Cand` with a specific `S : Obend.Slot.Slot Fact Cand`. -/
structure SlotFill {Fact Cand : Type} (S : Obend.Slot.Slot Fact Cand) where
  cand : Cand
  deriving DecidableEq, Repr

/-- Every `Obend.Slot.Slot Fact Cand` forms a `SupportSheaf` over Boolean fact-views `Fact → Bool`. -/
instance slotViewSheaf {Fact Cand : Type} (S : Obend.Slot.Slot Fact Cand) :
    SupportSheaf (Fact → Bool) Fact (SlotFill S) where
  supports x := S.supports x.cand
  holds view f := view f
  usable view x := S.usable view x.cand
  usable_supports view x hu := ((Obend.Slot.usable_iff S view x.cand).1 hu).2
  holds_frame {v₁ v₂ x} h := by
    have hdead : S.dead v₁ x.cand = S.dead v₂ x.cand := by
      unfold Obend.Slot.Slot.dead
      apply List.filter_congr
      intro f hf
      rw [h f hf]
    simp only [Obend.Slot.Slot.usable, hdead]

/-- Keyed world `K → Option V` for concrete delta transitions over `Obend.Slot`. -/
structure KeyedWorld (K V : Type) where
  lookup : K → Option V

/-- Keyed support fact asserting `w.lookup key = expected`. -/
structure KeyedFact (K V : Type) where
  key      : K
  expected : Option V
  deriving DecidableEq, Repr

/-- Keyed world delta: chronological sequence of `(K × Option V)` updates. -/
structure KeyedDelta (K V : Type) where
  edits : List (K × Option V)
  deriving DecidableEq, Repr

/-- Evaluate a `KeyedFact` at a `KeyedWorld`. -/
@[expose] def keyedHolds {K V : Type} [DecidableEq V]
    (w : KeyedWorld K V) (f : KeyedFact K V) : Bool :=
  decide (w.lookup f.key = f.expected)

/-- Apply one `(K × Option V)` edit to a `KeyedWorld`. -/
def applyKeyedEdit {K V : Type} [DecidableEq K]
    (e : K × Option V) (w : KeyedWorld K V) : KeyedWorld K V :=
  ⟨fun k => if k = e.1 then e.2 else w.lookup k⟩

/-- Apply a `KeyedDelta` sequentially to a `KeyedWorld`. -/
@[expose] def applyKeyedDelta {K V : Type} [DecidableEq K]
    (δ : KeyedDelta K V) (w : KeyedWorld K V) : KeyedWorld K V :=
  δ.edits.foldl (fun acc e => applyKeyedEdit e acc) w

/-- $O(|δ| \cdot |\text{supports}|)$ pushforward of a `SlotFill S` across `KeyedDelta`:
returns `.ok x` when no edit touches a cited key, or `.error badKey` naming the first touched key. -/
def transportSlotFill {K V Cand : Type} [DecidableEq K]
    (S : Obend.Slot.Slot (KeyedFact K V) Cand)
    (δ : KeyedDelta K V) (x : SlotFill S) : Except K (SlotFill S) :=
  match δ.edits.findSome? (fun e =>
      ((S.supports x.cand).find? (fun f => decide (f.key = e.1))).map KeyedFact.key) with
  | some badKey => .error badKey
  | none => .ok x

theorem keyedHolds_foldl_unchanged {K V : Type} [DecidableEq K] [DecidableEq V]
    (f : KeyedFact K V) :
    ∀ (edits : List (K × Option V)) (w : KeyedWorld K V),
      f.key ∉ edits.map Prod.fst →
      keyedHolds (edits.foldl (fun acc e => applyKeyedEdit e acc) w) f = keyedHolds w f
  | [], _, _ => rfl
  | e :: rest, w, hnot => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    have hstep : (applyKeyedEdit e w).lookup f.key = w.lookup f.key := by
      simp [applyKeyedEdit, hnot.1]
    rw [List.foldl_cons, keyedHolds_foldl_unchanged f rest (applyKeyedEdit e w) hnot.2]
    simp [keyedHolds, hstep]

/-- Verified `RepairableSheaf` instance for any `Obend.Slot` over `KeyedWorld K V` and `KeyedDelta K V`. -/
instance slotKeyedRepairableSheaf {K V Cand : Type} [DecidableEq K] [DecidableEq V]
    (S : Obend.Slot.Slot (KeyedFact K V) Cand) :
    RepairableSheaf (KeyedWorld K V) (KeyedDelta K V) (KeyedFact K V) (SlotFill S) where
  supports x := S.supports x.cand
  holds w f := keyedHolds w f
  usable w x := S.usable (keyedHolds w) x.cand
  usable_supports w x hu := ((Obend.Slot.usable_iff S (keyedHolds w) x.cand).1 hu).2
  holds_frame {w₁ w₂ x} h := by
    have hdead : S.dead (keyedHolds w₁) x.cand = S.dead (keyedHolds w₂) x.cand := by
      unfold Obend.Slot.Slot.dead
      apply List.filter_congr
      intro f hf
      rw [h f hf]
    simp only [Obend.Slot.Slot.usable, hdead]
  Locus := K
  Err := K
  factLocus := KeyedFact.key
  changed δ := δ.edits.map Prod.fst
  idDelta := ⟨[]⟩
  compDelta δ₂ δ₁ := ⟨δ₁.edits ++ δ₂.edits⟩
  applyDelta := applyKeyedDelta
  transport := transportSlotFill S
  applyDelta_id _ := rfl
  applyDelta_comp δ₂ δ₁ w := by
    simp [applyKeyedDelta, List.foldl_append]
  changed_id := rfl
  changed_comp_sub δ₂ δ₁ loc hmem := by
    simpa [List.map_append, List.mem_append] using hmem
  delta_frame_fact δ w f hnot := keyedHolds_foldl_unchanged f δ.edits w hnot
  transport_disjoint_fastpath δ x hnot := by
    unfold transportSlotFill
    have hnone : δ.edits.findSome? (fun e =>
        ((S.supports x.cand).find? (fun f => decide (f.key = e.1))).map KeyedFact.key) = none := by
      rw [List.findSome?_eq_none_iff]
      intro e he
      cases hfind : (S.supports x.cand).find? (fun f => decide (f.key = e.1)) with
      | none => rfl
      | some f =>
        have hmem := List.mem_of_find?_eq_some hfind
        have hkeq : f.key = e.1 :=
          of_decide_eq_true (@List.find?_some _ (fun x : KeyedFact K V => decide (x.key = e.1)) _ _ hfind)
        have hin : f.key ∈ δ.edits.map Prod.fst :=
          List.mem_map.2 ⟨e, he, hkeq.symm⟩
        exact False.elim (hnot f hmem hin)
    rw [hnone]
  transport_comp δ₂ δ₁ x := by
    unfold transportSlotFill
    rw [List.findSome?_append]
    cases h1 : δ₁.edits.findSome? (fun e =>
        ((S.supports x.cand).find? (fun f => decide (f.key = e.1))).map KeyedFact.key) with
    | some badKey => rfl
    | none =>
      simp only [Option.none_or, Except.bind]

/-! ## 3. Instance 2: `Obend.Intention` (`IntentionPin` & Active-Rebinding `RegPin`) -/

/-- Pin candidate anchored to reference `r` in an arbitrary `Obend.Intention`. -/
structure IntentionPin {W Ref Pin Fact Err : Type}
    (I : Obend.Intention W Ref Pin Fact Err) (r : Ref) where
  pin : Pin

/-- Every `Obend.Intention` induces a `SupportSheaf` at each reference `r : Ref`. -/
instance intentionSupportSheaf {W Ref Pin Fact Err : Type} [DecidableEq Ref]
    (I : Obend.Intention W Ref Pin Fact Err) (r : Ref) :
    SupportSheaf W Fact (IntentionPin I r) where
  supports p := I.supports p.pin
  holds := I.holds
  usable w p := (I.slot r).usable (I.holds w) p.pin
  usable_supports w p hu := ((Obend.Slot.usable_iff (I.slot r) (I.holds w) p.pin).1 hu).2
  holds_frame {w₁ w₂ p} h := by
    have hdead : (I.slot r).dead (I.holds w₁) p.pin = (I.slot r).dead (I.holds w₂) p.pin := by
      unfold Obend.Slot.Slot.dead
      apply List.filter_congr
      intro f hf
      exact congrArg Bool.not (h f hf)
    simp only [Obend.Slot.Slot.usable, hdead]

/-- Versioned package entry in a concrete `Intention` registry (`NAME@^MAJOR`). -/
structure RegEntry where
  major  : Nat
  minor  : Nat
  digest : Nat
  deriving DecidableEq, Repr

/-- Registry world mapping package names to published `RegEntry` records. -/
structure RegWorld where
  entries : String → Option RegEntry

/-- Support fact cited by a `RegPin`: package `target` currently resolves to `expected`. -/
structure RegFact where
  target   : String
  expected : RegEntry
  deriving DecidableEq, Repr

/-- Retained `Intention` pin for reference `(target, major)` locked to `locked : RegEntry`. -/
structure RegPin where
  target : String
  major  : Nat
  locked : RegEntry
  deriving DecidableEq, Repr

/-- Concrete `Obend.Intention` for `NAME@^MAJOR` package resolution against `RegWorld`. -/
def registryIntention : Obend.Intention RegWorld (String × Nat) RegPin RegFact String where
  ref p := (p.target, p.major)
  supports p := [⟨p.target, p.locked⟩]
  holds w f := decide (w.entries f.target = some f.expected)
  resolve w req :=
    match w.entries req.1 with
    | some entry =>
      if entry.major = req.2 then .ok ⟨req.1, req.2, entry⟩
      else .error s!"major mismatch for {req.1}"
    | none => .error s!"missing package {req.1}"
  resolve_ref w req p h := by
    cases hw : w.entries req.1 <;> simp [hw] at h
    rename_i entry
    split at h <;> simp at h
    subst h; rfl
  resolve_holds w req p h := by
    cases hw : w.entries req.1 <;> simp [hw] at h
    rename_i entry
    split at h <;> simp at h
    subst h
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    simp [hw]

/-- Atomic registry transition: publish a new version or yank a package. -/
inductive RegOp where
  | publish (pkg : String) (entry : RegEntry)
  | yank    (pkg : String)
  deriving DecidableEq, Repr

/-- Package locus mutated by a `RegOp`. -/
def RegOp.pkg : RegOp → String
  | .publish name _ => name
  | .yank name => name

/-- Apply one `RegOp` to `RegWorld`. -/
def applyRegOp (op : RegOp) (w : RegWorld) : RegWorld :=
  match op with
  | .publish name entry => ⟨fun k => if k = name then some entry else w.entries k⟩
  | .yank name => ⟨fun k => if k = name then none else w.entries k⟩

/-- Registry delta: chronological sequence of `RegOp` operations. -/
structure RegDelta where
  ops : List RegOp
  deriving DecidableEq, Repr

/-- Apply a `RegDelta` to `RegWorld`. -/
@[expose] def applyRegDelta (δ : RegDelta) (w : RegWorld) : RegWorld :=
  δ.ops.foldl (fun acc op => applyRegOp op acc) w

/-- Refusal reasons when pushing a `RegPin` forward across an incompatible `RegDelta`. -/
inductive RegRepairErr where
  | majorBroken (pkg : String) (expectedMajor actualMajor : Nat)
  | packageYanked (pkg : String)
  deriving DecidableEq, Repr

/-- Single-step coalgebraic Delta-Lens pushforward of `RegPin`:
- untouched package (`name ≠ p.target`): zero-cost identity `.ok p`,
- compatible publish (`entry.major = p.major`): active rebinding `.ok { p with locked := entry }`,
- incompatible major or yank: explicit refusal `.error ...`. -/
def stepRegPin (op : RegOp) (p : RegPin) : Except RegRepairErr RegPin :=
  match op with
  | .publish name entry =>
    if name = p.target then
      if entry.major = p.major then .ok { p with locked := entry }
      else .error (.majorBroken name p.major entry.major)
    else .ok p
  | .yank name =>
    if name = p.target then .error (.packageYanked name)
    else .ok p

/-- Coalgebraic pushforward of `RegPin` across a composite `RegDelta`. -/
def transportRegPin (δ : RegDelta) (p : RegPin) : Except RegRepairErr RegPin :=
  δ.ops.foldlM (fun cur op => stepRegPin op cur) p

/-- Usability of `RegPin` in `RegWorld`: matches `(registryIntention.slot (p.target, p.major)).usable`. -/
def regPinUsable (w : RegWorld) (p : RegPin) : Bool :=
  decide (p.locked.major = p.major) && registryIntention.holds w ⟨p.target, p.locked⟩

theorem regHolds_foldl_unchanged (f : RegFact) :
    ∀ (ops : List RegOp) (w : RegWorld),
      f.target ∉ ops.map RegOp.pkg →
      registryIntention.holds (ops.foldl (fun acc op => applyRegOp op acc) w) f =
        registryIntention.holds w f
  | [], _, _ => rfl
  | op :: rest, w, hnot => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    have h1 : (applyRegOp op w).entries f.target = w.entries f.target := by
      cases op with
      | publish name entry =>
        have hne : f.target ≠ name := hnot.1
        simp [applyRegOp, hne]
      | yank name =>
        have hne : f.target ≠ name := hnot.1
        simp [applyRegOp, hne]
    rw [List.foldl_cons, regHolds_foldl_unchanged f rest (applyRegOp op w) hnot.2]
    simp [registryIntention, h1]

theorem transportRegPin_disjoint_ops (p : RegPin) :
    ∀ (ops : List RegOp),
      p.target ∉ ops.map RegOp.pkg →
      ops.foldlM (fun cur op => stepRegPin op cur) p = .ok p
  | [], _ => rfl
  | op :: rest, hnot => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    have hstep : stepRegPin op p = .ok p := by
      cases op with
      | publish name entry =>
        have hne : name ≠ p.target := Ne.symm hnot.1
        simp [stepRegPin, hne]
      | yank name =>
        have hne : name ≠ p.target := Ne.symm hnot.1
        simp [stepRegPin, hne]
    simp only [List.foldlM_cons, hstep, bind, Except.bind]
    exact transportRegPin_disjoint_ops p rest hnot.2

theorem foldlM_except_append {α β ε : Type} (g : β → α → Except ε β) :
    ∀ (xs ys : List α) (init : β),
      (xs ++ ys).foldlM g init = (xs.foldlM g init).bind (fun b => ys.foldlM g b)
  | [], _, init => by simp [pure, Except.pure, Except.bind]
  | x :: xs, ys, init => by
    simp only [List.cons_append, List.foldlM_cons, bind, Except.bind]
    cases g init x with
    | error e => rfl
    | ok b' => exact foldlM_except_append g xs ys b'

/-- Verified `RepairableSheaf` instance for `RegPin` (`Obend.Intention` with active coalgebraic repair). -/
instance regPinRepairableSheaf :
    RepairableSheaf RegWorld RegDelta RegFact RegPin where
  supports := registryIntention.supports
  holds := registryIntention.holds
  usable := regPinUsable
  usable_supports w p hu f hf := by
    simp only [regPinUsable, Bool.and_eq_true] at hu
    simp only [registryIntention, List.mem_singleton] at hf
    subst hf
    exact hu.2
  holds_frame {w₁ w₂ p} h := by
    have hf := h ⟨p.target, p.locked⟩ (by simp [registryIntention])
    simp only [regPinUsable, hf]
  Locus := String
  Err := RegRepairErr
  factLocus := RegFact.target
  changed δ := δ.ops.map RegOp.pkg
  idDelta := ⟨[]⟩
  compDelta δ₂ δ₁ := ⟨δ₁.ops ++ δ₂.ops⟩
  applyDelta := applyRegDelta
  transport := transportRegPin
  applyDelta_id _ := rfl
  applyDelta_comp δ₂ δ₁ w := by
    simp [applyRegDelta, List.foldl_append]
  changed_id := rfl
  changed_comp_sub δ₂ δ₁ loc hmem := by
    simpa [List.map_append, List.mem_append] using hmem
  delta_frame_fact δ w f hnot := regHolds_foldl_unchanged f δ.ops w hnot
  transport_disjoint_fastpath δ p hnot := by
    apply transportRegPin_disjoint_ops p δ.ops
    exact hnot ⟨p.target, p.locked⟩ (by simp [registryIntention])
  transport_comp δ₂ δ₁ p := by
    unfold transportRegPin
    exact foldlM_except_append (fun cur op => stepRegPin op cur) δ₁.ops δ₂.ops p

/-- **Active Coalgebraic Pushforward Soundness (`regPin_transport_sound`)**:
Even when `δ` mutates `p.target` (non-disjoint compatible minor bump!), if `regPinUsable w p = true`
and `transportRegPin δ p = .ok p'`, then `p'` resolves the same `(target, major)` intention and is
immediately usable in `applyRegDelta δ w` without re-querying the world. -/
theorem regPin_transport_sound {w : RegWorld} {δ : RegDelta} {p p' : RegPin}
    (hu : regPinUsable w p = true)
    (htr : transportRegPin δ p = .ok p') :
    regPinUsable (applyRegDelta δ w) p' = true ∧
    registryIntention.ref p' = registryIntention.ref p := by
  have go : ∀ (ops : List RegOp) (w₀ : RegWorld) (p₀ p₁ : RegPin),
      regPinUsable w₀ p₀ = true →
      ops.foldlM (fun cur op => stepRegPin op cur) p₀ = .ok p₁ →
      regPinUsable (ops.foldl (fun acc op => applyRegOp op acc) w₀) p₁ = true ∧
      registryIntention.ref p₁ = registryIntention.ref p₀ := by
    intro ops
    induction ops with
    | nil =>
      intro w₀ p₀ p₁ hu₀ hok
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hok
      subst hok
      exact ⟨hu₀, rfl⟩
    | cons op rest ih =>
      intro w₀ p₀ p₁ hu₀ hok
      simp only [List.foldlM_cons, bind, Except.bind] at hok
      cases hs : stepRegPin op p₀ with
      | error e => rw [hs] at hok; cases hok
      | ok pm =>
        rw [hs] at hok
        have hstep : regPinUsable (applyRegOp op w₀) pm = true ∧
            registryIntention.ref pm = registryIntention.ref p₀ := by
          cases op with
          | publish name entry =>
            simp only [stepRegPin] at hs
            by_cases hname : name = p₀.target
            · simp only [hname, ite_true] at hs
              by_cases hmaj : entry.major = p₀.major
              · simp only [hmaj, ite_true, Except.ok.injEq] at hs
                subst hs
                refine ⟨?_, rfl⟩
                simp [regPinUsable, registryIntention, applyRegOp, hname, hmaj]
              · simp [hmaj] at hs
            · simp only [hname, ite_false, Except.ok.injEq] at hs
              subst hs
              have hne : p₀.target ≠ name := Ne.symm hname
              refine ⟨?_, rfl⟩
              simpa [regPinUsable, registryIntention, applyRegOp, hne] using hu₀
          | yank name =>
            simp only [stepRegPin] at hs
            by_cases hname : name = p₀.target
            · simp [hname] at hs
            · simp only [hname, ite_false, Except.ok.injEq] at hs
              subst hs
              have hne : p₀.target ≠ name := Ne.symm hname
              refine ⟨?_, rfl⟩
              simpa [regPinUsable, registryIntention, applyRegOp, hne] using hu₀
        obtain ⟨hu₁, href₁⟩ := ih (applyRegOp op w₀) pm p₁ hstep.1 hok
        exact ⟨hu₁, href₁.trans hstep.2⟩
  exact go δ.ops w p p' hu htr

/-! ## 4. Instance 3: `SuperClaimCert` (`PointedComp` & `OverlayDelta` from `SuperRefines.lean`) -/

/-- Composition stack focused at a target `Layer` (`above` layers sit above `target`; `below` sit
beneath `target`). Prepending outer wrapper layers onto `above` shifts `layerIdx = above.length`
automatically while leaving the inherited suffix `below` invariant! -/
structure PointedComp where
  above  : List Layer
  target : Layer
  below  : List Layer
  seed   : List (String × Term)

/-- Underlying `Composition` of a `PointedComp`. -/
def PointedComp.toComp (P : PointedComp) : Composition :=
  match P.above with
  | [] => ⟨P.target, P.below, P.seed⟩
  | top :: rest => ⟨top, rest ++ (P.target :: P.below), P.seed⟩

/-- Index of `P.target` in `P.toComp.layers` (counting from outermost `0`). -/
def PointedComp.layerIdx (P : PointedComp) : Nat := P.above.length

/-- Build the `ClaimObj` for `claim` of `arity` at `P.target` in `P`. -/
def PointedComp.claimObj (P : PointedComp) (claim : Term) (arity : Nat) : ClaimObj :=
  ⟨P.toComp, P.layerIdx, claim, arity⟩

theorem PointedComp.toComp_layers (P : PointedComp) :
    P.toComp.layers = P.above ++ (P.target :: P.below) := by
  unfold PointedComp.toComp
  cases P.above <;> rfl

theorem PointedComp.toComp_seed (P : PointedComp) :
    P.toComp.seed = P.seed := by
  unfold PointedComp.toComp
  cases P.above <;> rfl

theorem drop_append_cons {α : Type} :
    ∀ (xs : List α) (y : α) (ys : List α),
      (xs ++ (y :: ys)).drop (xs.length + 1) = ys
  | [], _, _ => rfl
  | _ :: xs, y, ys => drop_append_cons xs y ys

theorem PointedComp.drop_layerIdx_succ (P : PointedComp) :
    P.toComp.layers.drop (P.layerIdx + 1) = P.below := by
  rw [P.toComp_layers, PointedComp.layerIdx]
  exact drop_append_cons P.above P.target P.below

/-- `providesLast ls m = some j` implies `j < ls.length`. -/
theorem providesLast_lt :
    ∀ (ls : List Layer) (m : String) {j : Nat},
      providesLast ls m = some j → j < ls.length
  | [], _, _, h => by simp [providesLast] at h
  | L :: rest, m, j, h => by
    simp only [providesLast] at h
    by_cases hp : L.provides m = true
    · simp only [hp, ite_true, Option.some.injEq] at h
      subst h
      simp
    · simp only [hp, Bool.false_eq_true, ite_false] at h
      by_cases hf : L.flat = true
      · simp [hf] at h
      · simp only [hf, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨k, hk, rfl⟩ := h
        have hlt := providesLast_lt rest m hk
        simp
        omega

/-- `unfoldIn` is independent of `fuel` once `ls.length ≤ fuel`. -/
theorem unfoldIn_fuel_irrel (O : Term) (seed : List (String × Term)) (m : String) :
    ∀ (n : Nat) (ls : List Layer) {f₁ f₂ : Nat},
      ls.length ≤ n → ls.length ≤ f₁ → ls.length ≤ f₂ →
      unfoldIn O seed f₁ ls m = unfoldIn O seed f₂ ls m
  | 0, ls, f₁, f₂, hn, _, _ => by
    have hnil : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    have empty_none : ∀ f, unfoldIn O seed f [] m = none := by
      intro f; cases f <;> rfl
    rw [empty_none f₁, empty_none f₂]
  | n + 1, [], f₁, f₂, _, _, _ => by
    have empty_none : ∀ f, unfoldIn O seed f [] m = none := by
      intro f; cases f <;> rfl
    rw [empty_none f₁, empty_none f₂]
  | n + 1, L :: rest, f₁, f₂, hn, hf₁, hf₂ => by
    cases f₁ with
    | zero => simp at hf₁
    | succ f₁' =>
      cases f₂ with
      | zero => simp at hf₂
      | succ f₂' =>
        simp only [unfoldIn]
        cases hp : providesLast (L :: rest) m with
        | none => rfl
        | some j =>
          have hj : j < (L :: rest).length := providesLast_lt (L :: rest) m hp
          simp only
          cases hb : bodyAt (L :: rest) j m with
          | none => rfl
          | some b =>
            simp only
            by_cases hd : isDelegation b m = true
            · simp only [hd, ite_true]
              have hlen_n : ((L :: rest).drop (j + 1)).length ≤ n := by
                simp at hj hn ⊢; omega
              have hlen_1 : ((L :: rest).drop (j + 1)).length ≤ f₁' := by
                simp at hj hf₁ ⊢; omega
              have hlen_2 : ((L :: rest).drop (j + 1)).length ≤ f₂' := by
                simp at hj hf₂ ⊢; omega
              rw [unfoldIn_fuel_irrel O seed m n ((L :: rest).drop (j + 1)) hlen_n hlen_1 hlen_2]
            · simp [hd]

/-- Prepending a non-flat layer `L` (`L.flat = false`) that does not provide `m` (`L.provides m = false`)
preserves named late-binding unfolding identically! -/
theorem unfoldNamed_cons_nonFlat (O : Term) (seed : List (String × Term))
    (L : Layer) (ls : List Layer) (m : String)
    (hflat : L.flat = false) (hprov : L.provides m = false) :
    ((unfoldIn O seed (L :: ls).length (L :: ls) m).map fun (j, u) => (layerName (L :: ls) j, u)) =
      ((unfoldIn O seed ls.length ls m).map fun (j, u) => (layerName ls j, u)) := by
  cases ls with
  | nil =>
    simp [unfoldIn, providesLast, hprov, hflat]
  | cons L₀ rest =>
    let ls := L₀ :: rest
    have hpl : providesLast (L :: ls) m = (providesLast ls m).map (· + 1) := by
      simp [providesLast, hprov, hflat]
    change ((unfoldIn O seed (rest.length + 1 + 1) (L :: ls) m).map fun (j, u) => (layerName (L :: ls) j, u)) =
      ((unfoldIn O seed (rest.length + 1) ls m).map fun (j, u) => (layerName ls j, u))
    conv => lhs; arg 2; unfold unfoldIn
    conv => rhs; arg 2; unfold unfoldIn
    rw [hpl]
    cases hp : providesLast ls m with
    | none => rfl
    | some j =>
      have hj : j < ls.length := providesLast_lt ls m hp
      simp only [Option.map_some]
      have hbody : bodyAt (L :: ls) (j + 1) m = bodyAt ls j m := rfl
      have hdrop : (L :: ls).drop (j + 1 + 1) = ls.drop (j + 1) := rfl
      rw [hbody, hdrop]
      cases hb : bodyAt ls j m with
      | none => rfl
      | some b =>
        simp only
        by_cases hd : isDelegation b m = true
        · simp only [hd, ite_true, Option.map_map]
          have hlen1 : (ls.drop (j + 1)).length ≤ rest.length + 1 := by
            simp [ls] at hj ⊢; omega
          have hlen2 : (ls.drop (j + 1)).length ≤ rest.length := by
            simp [ls]
          rw [unfoldIn_fuel_irrel O seed m (rest.length + 1) (ls.drop (j + 1)) hlen1 hlen1 hlen2]
          apply congrArg (Option.map · _)
          funext ⟨i, u⟩
          have hidx : i + (j + 1) + 1 = (i + j + 1) + 1 := by omega
          simp only [Function.comp_apply, hidx]
          rfl
        · simp only [hd, Bool.false_eq_true, ite_false, Option.map_some]
          rfl

/-- Arity-tagged `SuperSupport` fact so `SupportSheaf.holds` evaluates `SuperClaimCert` supports of any arity. -/
structure CertSupport where
  arity   : Nat
  support : SuperSupport

/-- Non-flat wrapper layer added above `PointedComp.target`. -/
structure OverlayStep where
  layer   : Layer
  nonFlat : layer.flat = false

/-- Delta prepending a sequence of non-flat wrapper layers above `PointedComp.target`. -/
structure OverlayDelta where
  steps : List OverlayStep

/-- Prepend a single `OverlayStep` onto `PointedComp.above`. -/
def applyOverlayStep (s : OverlayStep) (P : PointedComp) : PointedComp :=
  { P with above := s.layer :: P.above }

/-- Apply an `OverlayDelta` sequentially to a `PointedComp`. -/
@[expose] def applyOverlay (δ : OverlayDelta) (P : PointedComp) : PointedComp :=
  δ.steps.foldl (fun acc s => applyOverlayStep s acc) P

/-- Receiver-qualified loci mutated by one `OverlayStep`:
ONLY `(.selfReceiver, m)` for `m` provided by `s.layer` — NEVER `(.superReceiver, _)`! -/
def stepChangedLoci (s : OverlayStep) : List (ReceiverKind × String) :=
  s.layer.fields.map fun kv => (.selfReceiver, kv.1)

/-- Refusal reason when an `OverlayDelta` overrides a member cited in `cert.selfSupports`. -/
inductive SuperTransportErr where
  | overriddenSelf (layerName : String) (member : String)
  deriving DecidableEq, Repr

/-- $O(1)$-per-support pushforward of `SuperClaimCert` across `OverlayDelta`:
checks ONLY `cert.selfSupports` against `s.layer.provides` (ignoring `cert.superSupports` completely,
since outer layers never affect `P.below`!), returning `.ok cert` unchanged when disjoint. -/
def transportSuperCert (δ : OverlayDelta) (cert : SuperClaimCert) :
    Except SuperTransportErr SuperClaimCert :=
  match δ.steps.findSome? (fun s =>
      (cert.selfSupports.find? (fun sp => s.layer.provides sp.member)).map
        (fun sp => SuperTransportErr.overriddenSelf s.layer.name sp.member)) with
  | some err => .error err
  | none => .ok cert

/-- Footprint of a `SuperClaimCert` as `List CertSupport`. -/
@[expose] def superCertSupports (cert : SuperClaimCert) : List CertSupport :=
  cert.allSupports.map fun sp => ⟨cert.arity, sp⟩

/-- Satisfaction of a `CertSupport` at `P : PointedComp`. -/
@[expose] def certSupportHolds (P : PointedComp) (f : CertSupport) : Bool :=
  SuperSupport.holds P.toComp f.arity P.layerIdx f.support

/-- Usability of a `SuperClaimCert` at `P : PointedComp`. -/
@[expose] def superCertUsable (P : PointedComp) (cert : SuperClaimCert) : Bool :=
  (superCertSupports cert).all (certSupportHolds P)

theorem not_provides_of_not_mem_stepChanged (s : OverlayStep) (m : String)
    (hnot : (.selfReceiver, m) ∉ stepChangedLoci s) :
    s.layer.provides m = false := by
  unfold Layer.provides
  cases hany : s.layer.fields.any (·.1 == m) with
  | false => rfl
  | true =>
    obtain ⟨kv, hkv, heq⟩ := List.any_eq_true.1 hany
    have hm : kv.1 = m := by simpa using heq
    have hmem : (.selfReceiver, m) ∈ stepChangedLoci s :=
      List.mem_map.2 ⟨kv, hkv, by rw [hm]⟩
    exact False.elim (hnot hmem)

theorem certSupportHolds_step_frame (s : OverlayStep) (P : PointedComp) (f : CertSupport)
    (hnot : (f.support.receiver, f.support.member) ∉ stepChangedLoci s) :
    certSupportHolds (applyOverlayStep s P) f = certSupportHolds P f := by
  unfold certSupportHolds SuperSupport.holds
  cases hr : f.support.receiver with
  | selfReceiver =>
    simp only
    have hprov : s.layer.provides f.support.member = false :=
      not_provides_of_not_mem_stepChanged s f.support.member (hr ▸ hnot)
    have hsym : symUnfold (applyOverlayStep s P).toComp (f.arity + 1) f.support.member =
        symUnfold P.toComp (f.arity + 1) f.support.member := by
      unfold symUnfold
      rw [(applyOverlayStep s P).toComp_seed, P.toComp_seed,
        (applyOverlayStep s P).toComp_layers, P.toComp_layers]
      exact unfoldNamed_cons_nonFlat (.bound (f.arity + 1)) P.seed s.layer
        (P.above ++ (P.target :: P.below)) f.support.member s.nonFlat hprov
    rw [hsym]
  | superReceiver =>
    simp only
    have hsup : superSymUnfold (applyOverlayStep s P).toComp (f.arity + 1)
          (applyOverlayStep s P).layerIdx f.support.member =
        superSymUnfold P.toComp (f.arity + 1) P.layerIdx f.support.member := by
      unfold superSymUnfold
      rw [(applyOverlayStep s P).toComp_seed, P.toComp_seed,
        (applyOverlayStep s P).drop_layerIdx_succ, P.drop_layerIdx_succ]
      rfl
    rw [hsup]

theorem certSupportHolds_foldl_frame (f : CertSupport) :
    ∀ (steps : List OverlayStep) (P : PointedComp),
      (f.support.receiver, f.support.member) ∉ steps.flatMap stepChangedLoci →
      certSupportHolds (steps.foldl (fun acc s => applyOverlayStep s acc) P) f =
        certSupportHolds P f
  | [], _, _ => rfl
  | s :: rest, P, hnot => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at hnot
    rw [List.foldl_cons, certSupportHolds_foldl_frame f rest (applyOverlayStep s P) hnot.2,
      certSupportHolds_step_frame s P f hnot.1]

/-- Verified `RepairableSheaf` instance for `SuperClaimCert` over `PointedComp` and `OverlayDelta`. -/
instance superClaimCertRepairableSheaf :
    RepairableSheaf PointedComp OverlayDelta CertSupport SuperClaimCert where
  supports := superCertSupports
  holds := certSupportHolds
  usable := superCertUsable
  usable_supports P cert hu := List.all_eq_true.1 hu
  holds_frame {P₁ P₂ cert} h := by
    unfold superCertUsable
    cases hu1 : (superCertSupports cert).all (certSupportHolds P₁) with
    | true =>
      symm
      rw [List.all_eq_true]
      intro f hf
      rw [← h f hf]
      exact List.all_eq_true.1 hu1 f hf
    | false =>
      symm
      cases hu2 : (superCertSupports cert).all (certSupportHolds P₂) with
      | false => rfl
      | true =>
        have hall1 : (superCertSupports cert).all (certSupportHolds P₁) = true := by
          rw [List.all_eq_true]
          intro f hf
          rw [h f hf]
          exact List.all_eq_true.1 hu2 f hf
        rw [hu1] at hall1
        cases hall1
  Locus := ReceiverKind × String
  Err := SuperTransportErr
  factLocus f := (f.support.receiver, f.support.member)
  changed δ := δ.steps.flatMap stepChangedLoci
  idDelta := ⟨[]⟩
  compDelta δ₂ δ₁ := ⟨δ₁.steps ++ δ₂.steps⟩
  applyDelta := applyOverlay
  transport := transportSuperCert
  applyDelta_id _ := rfl
  applyDelta_comp δ₂ δ₁ P := by
    simp [applyOverlay, List.foldl_append]
  changed_id := rfl
  changed_comp_sub δ₂ δ₁ loc hmem := by
    simpa [List.flatMap_append, List.mem_append] using hmem
  delta_frame_fact δ P f hnot := certSupportHolds_foldl_frame f δ.steps P hnot
  transport_disjoint_fastpath δ cert hnot := by
    unfold transportSuperCert
    have hnone : δ.steps.findSome? (fun s =>
        (cert.selfSupports.find? (fun sp => s.layer.provides sp.member)).map
          (fun sp => SuperTransportErr.overriddenSelf s.layer.name sp.member)) = none := by
      rw [List.findSome?_eq_none_iff]
      intro s hs
      cases hfind : cert.selfSupports.find? (fun sp => s.layer.provides sp.member) with
      | none => rfl
      | some sp =>
        have hsp_mem : sp ∈ cert.selfSupports := List.mem_of_find?_eq_some hfind
        have hprov : s.layer.provides sp.member = true :=
          @List.find?_some _ (fun x : Support => s.layer.provides x.member) _ _ hfind
        obtain ⟨kv, hkv, hkeq⟩ := List.any_eq_true.1 hprov
        have hm : kv.1 = sp.member := by simpa using hkeq
        have hcert_mem : (⟨cert.arity, ⟨.selfReceiver, sp.member, sp.unfolded⟩⟩ : CertSupport) ∈
            superCertSupports cert := by
          simp only [superCertSupports, SuperClaimCert.allSupports, List.mem_map, List.mem_append]
          exact ⟨⟨.selfReceiver, sp.member, sp.unfolded⟩, .inl ⟨sp, hsp_mem, rfl⟩, rfl⟩
        have hloc_mem : (.selfReceiver, sp.member) ∈ δ.steps.flatMap stepChangedLoci := by
          rw [List.mem_flatMap]
          exact ⟨s, hs, List.mem_map.2 ⟨kv, hkv, by rw [hm]⟩⟩
        exact False.elim (hnot _ hcert_mem hloc_mem)
    rw [hnone]
  transport_comp δ₂ δ₁ cert := by
    unfold transportSuperCert
    rw [List.findSome?_append]
    cases δ₁.steps.findSome? (fun s =>
        (cert.selfSupports.find? (fun sp => s.layer.provides sp.member)).map
          (fun sp => SuperTransportErr.overriddenSelf s.layer.name sp.member)) with
    | some err => rfl
    | none =>
      simp only [Option.none_or, Except.bind]

/-- At its origin `PointedComp`, any `mkSuperClaimCert` is immediately usable. -/
theorem mkSuperClaimCert_origin_usable (P : PointedComp) (k : Nat) (claim : Term)
    (arity : Nat) (steps : List RStep) :
    superCertUsable P (mkSuperClaimCert k (P.claimObj claim arity) steps) = true := by
  rw [superCertUsable, List.all_eq_true]
  intro f hf
  simp only [superCertSupports, List.mem_map] at hf
  obtain ⟨sp, hsp_all, rfl⟩ := hf
  have hsp : sp ∈ superSupports (P.claimObj claim arity) steps :=
    mem_superSupports_of_mem_allSupports hsp_all
  have hholds := superSupports_holds_self (P.claimObj claim arity) steps sp hsp
  simpa only [certSupportHolds, mkSuperClaimCert_arity, PointedComp.claimObj] using hholds

/-- Any `transportSuperCert δ cert = .ok cert'` implies `cert' = cert` and `disjoint (changed δ) (supports cert) = true`. -/
theorem transportSuperCert_ok_disjoint {δ : OverlayDelta} {cert cert' : SuperClaimCert}
    (htr : transportSuperCert δ cert = .ok cert') :
    cert' = cert ∧
    disjoint (S := superClaimCertRepairableSheaf)
      (RepairableSheaf.changed (Obj := SuperClaimCert) δ) (superCertSupports cert) = true := by
  unfold transportSuperCert at htr
  cases hfind : δ.steps.findSome? (fun s =>
      (cert.selfSupports.find? (fun sp => s.layer.provides sp.member)).map
        (fun sp => SuperTransportErr.overriddenSelf s.layer.name sp.member)) with
  | some err => rw [hfind] at htr; cases htr
  | none =>
    rw [hfind] at htr
    injection htr with heq
    subst heq
    refine ⟨rfl, ?_⟩
    rw [disjoint_eq_true_iff]
    intro f hf hloc
    simp only [superCertSupports, SuperClaimCert.allSupports, List.mem_map, List.mem_append] at hf
    obtain ⟨sp, hsp, rfl⟩ := hf
    rcases hsp with ⟨s0, hs0, rfl⟩ | ⟨s0, _, rfl⟩
    · simp only [RepairableSheaf.changed, List.mem_flatMap] at hloc
      obtain ⟨step, hstep, hmem⟩ := hloc
      simp only [stepChangedLoci, List.mem_map] at hmem
      obtain ⟨kv, hkv, hkveq⟩ := hmem
      injection hkveq with _ hm
      have hprov : step.layer.provides s0.member = true :=
        List.any_eq_true.2 ⟨kv, hkv, by simp [hm]⟩
      have hstepNone := List.findSome?_eq_none_iff.1 hfind step hstep
      cases hc : cert.selfSupports.find? (fun sp => step.layer.provides sp.member) with
      | none =>
        have hfalse := List.find?_eq_none.1 hc s0 hs0
        simp [hprov] at hfalse
      | some _ => simp [hc] at hstepNone
    · simp only [RepairableSheaf.changed, List.mem_flatMap, stepChangedLoci, List.mem_map] at hloc
      obtain ⟨_, _, _, _, hkveq⟩ := hloc
      cases hkveq

/-- **$O(1)$ Certificate Transport Soundness (`superCert_transport_sound`)**:
Once `superClaimCheck k (P.claimObj claim arity) steps = .ok` is established at `P`, pushing
`cert := mkSuperClaimCert k (P.claimObj claim arity) steps` across ANY `OverlayDelta` `δ` with
`transportSuperCert δ cert = .ok cert'` guarantees in $O(1)$ (without re-running `superClaimCheck`!)
that `cert' = cert` AND at `P' := applyOverlay δ P` (when well-formed):
1. `superClaimCheck k (P'.claimObj claim arity) cert'.steps = .ok`, and
2. `claimMeaning (P'.claimObj claim arity)` holds across all ground instances! -/
theorem superCert_transport_sound {P : PointedComp} {k : Nat} {claim : Term} {arity : Nat}
    {steps : List RStep} {δ : OverlayDelta} {cert' : SuperClaimCert}
    (hOrigin : superClaimCheck k (P.claimObj claim arity) steps = .ok)
    (htr : transportSuperCert δ (mkSuperClaimCert k (P.claimObj claim arity) steps) = .ok cert')
    (hwf : ((applyOverlay δ P).claimObj claim arity).wellFormed = true) :
    cert' = mkSuperClaimCert k (P.claimObj claim arity) steps ∧
    superClaimCheck k ((applyOverlay δ P).claimObj claim arity) cert'.steps = .ok ∧
    claimMeaning ((applyOverlay δ P).claimObj claim arity) := by
  let cert := mkSuperClaimCert k (P.claimObj claim arity) steps
  obtain ⟨rfl, hdisj⟩ := transportSuperCert_ok_disjoint htr
  have hu0 : superCertUsable P cert = true :=
    mkSuperClaimCert_origin_usable P k claim arity steps
  have hu1 : superCertUsable (applyOverlay δ P) cert = true :=
    (disjoint_transport_sound (S := superClaimCertRepairableSheaf) hu0 hdisj).2
  have hsup : ∀ sp ∈ superSupports (P.claimObj claim arity) steps,
      SuperSupport.holds (applyOverlay δ P).toComp arity (applyOverlay δ P).layerIdx sp = true := by
    intro sp hsp
    have hall := mem_allSupports_of_mem_superSupports (k := k) hsp
    have hcf : (⟨cert.arity, sp⟩ : CertSupport) ∈ superCertSupports cert :=
      List.mem_map.2 ⟨sp, hall, rfl⟩
    have hch := List.all_eq_true.1 hu1 ⟨cert.arity, sp⟩ hcf
    simpa only [cert, certSupportHolds, mkSuperClaimCert_arity, PointedComp.claimObj] using hch
  have hcheck : superClaimCheck k ((applyOverlay δ P).claimObj claim arity) steps = .ok :=
    (T3_super_claim_frame hOrigin hsup hwf).1
  have hcheckCert : superClaimCheck k ((applyOverlay δ P).claimObj claim arity) cert.steps = .ok := by
    simpa only [cert, mkSuperClaimCert_steps] using hcheck
  exact ⟨rfl, hcheckCert, superClaim_sound hcheck⟩

/-! ## 5. Concrete Inhabited Witnesses & Refutation Theorems (All 3 Instances) -/

/-- Concrete keyed slot requiring `("port", some 8080)`. -/
def portSlot : Obend.Slot.Slot (KeyedFact String Nat) Nat where
  supports n := [⟨"port", some n⟩]
  judge n := decide (n > 1024)

def initialKeyedWorld : KeyedWorld String Nat where
  lookup k := if k = "port" then some 8080 else none

def disjointKeyedDelta : KeyedDelta String Nat := ⟨[("timeout", some 30)]⟩
def conflictingKeyedDelta : KeyedDelta String Nat := ⟨[("port", some 9090)]⟩

/-- Concrete inhabited witness for `disjoint_transport_sound` on `Obend.Slot`. -/
theorem slotDisjoint_inhabited_witness :
    SupportSheaf.usable (Obj := SlotFill portSlot) initialKeyedWorld ⟨8080⟩ = true ∧
    disjoint (S := slotKeyedRepairableSheaf portSlot)
      (RepairableSheaf.changed (Obj := SlotFill portSlot) disjointKeyedDelta)
      (SupportSheaf.supports (W := KeyedWorld String Nat) (⟨8080⟩ : SlotFill portSlot)) = true ∧
    RepairableSheaf.transport (W := KeyedWorld String Nat) disjointKeyedDelta (⟨8080⟩ : SlotFill portSlot) =
      .ok ⟨8080⟩ := by
  exact ⟨by decide +kernel, by decide +kernel, rfl⟩

/-- Refutation witness for `Obend.Slot`: mutating `"port"` is refused by `transportSlotFill` with `.error "port"`. -/
theorem slotConflict_refused :
    RepairableSheaf.transport (W := KeyedWorld String Nat) conflictingKeyedDelta
      (⟨8080⟩ : SlotFill portSlot) = .error "port" := by
  rfl

/-- Concrete registry world with `("codec", ⟨1, 0, 111⟩)`. -/
def initialRegWorld : RegWorld where
  entries k := if k = "codec" then some ⟨1, 0, 111⟩ else none

def codecPinV10 : RegPin := ⟨"codec", 1, ⟨1, 0, 111⟩⟩

def compatibleMinorDelta : RegDelta :=
  ⟨[.publish "logger" ⟨2, 1, 999⟩, .publish "codec" ⟨1, 1, 222⟩]⟩

def breakingMajorDelta : RegDelta :=
  ⟨[.publish "codec" ⟨2, 0, 333⟩]⟩

/-- Concrete inhabited witness for `regPin_transport_sound`: active coalgebraic pin rebinding across a
compatible minor publish (`v1.0` → `v1.1`) preserves usability without re-querying `RegWorld`. -/
theorem regPin_active_rebind_witness :
    regPinUsable initialRegWorld codecPinV10 = true ∧
    transportRegPin compatibleMinorDelta codecPinV10 = .ok ⟨"codec", 1, ⟨1, 1, 222⟩⟩ ∧
    regPinUsable (applyRegDelta compatibleMinorDelta initialRegWorld) ⟨"codec", 1, ⟨1, 1, 222⟩⟩ = true := by
  exact ⟨by decide +kernel, rfl,
    (regPin_transport_sound (w := initialRegWorld) (δ := compatibleMinorDelta)
      (p := codecPinV10) (by decide +kernel) rfl).1⟩

/-- Refutation witness for `RegPin`: publishing breaking `v2.0` for `"codec@^1"` is refused with `.majorBroken`. -/
theorem regPin_majorBreak_refused :
    transportRegPin breakingMajorDelta codecPinV10 = .error (.majorBroken "codec" 1 2) := by
  rfl

/-- Concrete `PointedComp` at `"Refined"` (`above = []`, `target = verticalRefinedLayer`, `below = [verticalBaseLayer]`). -/
def verticalPointedOrigin : PointedComp where
  above  := []
  target := verticalRefinedLayer
  below  := [verticalBaseLayer]
  seed   := []

/-- Non-flat `OverlayDelta` prepending `auditWrapperLayer` (which overrides `"apply"`, cited in
`superSupports`, while leaving `"scale"` in `selfSupports` untouched!). -/
def auditOverlayDelta : OverlayDelta where
  steps := [⟨auditWrapperLayer, rfl⟩]

/-- Conflicting `OverlayDelta` overriding `"scale"` (which IS cited in `selfSupports`). -/
def scaleOverrideLayer : Layer where
  name := "ScaleOverride"
  metadata := .inject "declared" (.record [("name", .label "ScaleOverride")])
  fields := [("scale", .nat 99)]

def conflictingScaleOverlayDelta : OverlayDelta where
  steps := [⟨scaleOverrideLayer, rfl⟩]

/-- Mint the vertical open-recursion certificate at `verticalPointedOrigin`. -/
def verticalOpenRecCert : SuperClaimCert :=
  mkSuperClaimCert 15
    (verticalPointedOrigin.claimObj verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity)
    verticalOpenRecSteps

theorem find_map_support_member {α : Type} (xs : List Support) (p : String → Bool) (f : String → α) :
    (xs.find? (fun sp => p sp.member)).map (fun sp => f sp.member) =
      ((xs.map (·.member)).find? p).map f := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.find?_cons, List.map_cons]
    cases p hd.member <;> simp [ih]

/-- Reduction of `transportSuperCert` on `verticalOpenRecCert` using its verified `["scale"]`
`selfSupports` footprint. -/
theorem transportSuperCert_verticalOpenRecCert (δ : OverlayDelta) :
    transportSuperCert δ verticalOpenRecCert =
      match δ.steps.findSome? (fun s =>
          if s.layer.provides "scale" then some (.overriddenSelf s.layer.name "scale") else none) with
      | some err => .error err
      | none => .ok verticalOpenRecCert := by
  unfold transportSuperCert
  have hmem : verticalOpenRecCert.selfSupports.map (·.member) = ["scale"] :=
    verticalOpenRec_selfSupport_members
  have hfun : (fun s : OverlayStep =>
      (verticalOpenRecCert.selfSupports.find? (fun sp => s.layer.provides sp.member)).map
        (fun sp => SuperTransportErr.overriddenSelf s.layer.name sp.member)) =
      (fun s : OverlayStep =>
        if s.layer.provides "scale" then some (.overriddenSelf s.layer.name "scale") else none) := by
    funext s
    rw [find_map_support_member, hmem]
    cases h : s.layer.provides "scale" <;> simp [List.find?, h]
  rw [hfun]
  rfl

/-- Concrete inhabited witness for `superCert_transport_sound`:
`auditOverlayDelta` overrides `"apply"` (in `superSupports`), yet `disjoint (changed δ) (supports cert)`
is `true`, `transportSuperCert` takes the $O(1)$ identity fast-path `.ok verticalOpenRecCert`, and
`superCert_transport_sound` yields `claimMeaning` in the 3-layer stack! -/
theorem superCert_overlay_fastpath_witness :
    superClaimCheck 15
      (verticalPointedOrigin.claimObj verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity)
      verticalOpenRecSteps = .ok ∧
    disjoint (S := superClaimCertRepairableSheaf)
      (RepairableSheaf.changed (Obj := SuperClaimCert) auditOverlayDelta)
      (superCertSupports verticalOpenRecCert) = true ∧
    transportSuperCert auditOverlayDelta verticalOpenRecCert = .ok verticalOpenRecCert ∧
    claimMeaning ((applyOverlay auditOverlayDelta verticalPointedOrigin).claimObj
      verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity) := by
  have hOrigin : superClaimCheck 15
      (verticalPointedOrigin.claimObj verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity)
      verticalOpenRecSteps = .ok := verticalOpenRec_frame_transport_accepted.1
  have htr : transportSuperCert auditOverlayDelta verticalOpenRecCert = .ok verticalOpenRecCert := by
    rw [transportSuperCert_verticalOpenRecCert]
    rfl
  have hdisj : disjoint (S := superClaimCertRepairableSheaf)
      (RepairableSheaf.changed (Obj := SuperClaimCert) auditOverlayDelta)
      (superCertSupports verticalOpenRecCert) = true :=
    (transportSuperCert_ok_disjoint htr).2
  have hwf : ((applyOverlay auditOverlayDelta verticalPointedOrigin).claimObj
      verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity).wellFormed = true := by
    decide +kernel
  exact ⟨hOrigin, hdisj, htr, (superCert_transport_sound hOrigin htr hwf).2.2⟩

/-- Refutation witness for `SuperClaimCert`: overriding `"scale"` (cited in `selfSupports`) is
immediately refused by `transportSuperCert` in $O(1)$ with `.error (.overriddenSelf "ScaleOverride" "scale")`. -/
theorem superCert_selfOverride_refused :
    transportSuperCert conflictingScaleOverlayDelta verticalOpenRecCert =
      .error (.overriddenSelf "ScaleOverride" "scale") := by
  rw [transportSuperCert_verticalOpenRecCert]
  rfl

end Obend.Slot.SupportSheaf

end
