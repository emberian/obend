module
/-
# Obend.Repair.UpgradeEnvelope — Symmetric Edit Lenses, Lazy Bucket Upgrades & Epoch Log Relinking

Unifies four orthogonal upgrade mechanisms into one kernel-checked `Obend.Repair` spine (`0 sorry`,
`0 axiom`, `0 Classical.choice`):

1. **Hofmann–Pierce–Wagner Symmetric Complemented Edit Lenses (`SymmetricEditLens` — POPL '12):**
   - Bidirectional translation of monoid edit actions `(E₁, act₁) ↔ (E₂, act₂)` across missing/extra
     views via persistent complement `C` (`putr`, `putl`), preserving identity edits (`putr_id`,
     `putl_id`), composite edits (`putr_comp`, `putl_comp`), and relational consistency
     (`Consistent s₁ c s₂`).
   - Strictly generalizes Clarke's `DeltaLens` (`DeltaLens.toSymmetricEditLens`, where `put_get`
     discharges `putl_sound`, `put_put` discharges `putl_comp`, and `get_put` discharges unchanged-view
     stability), composes horizontally (`SymmetricEditLens.comp`), inverts symmetrically
     (`SymmetricEditLens.symm`), and handles peer schema splits (`peerSplitEditLens`) where neither
     state projects onto or bijects with the other.
2. **Law-Strengthening Epistemic Migration & Thor Lazy Per-Bucket Store (`LazyBucketStore` — OOPSLA '03):**
   - Pairs Upstart `pastSO`/`futureSO` law-tightening edit guards (`CheckedUpgradeAdapter`, with
     exact completeness `translateOldEdit_refuses_iff_law_violated` and constructive inhabitedness
     `translateOldEdit_inhabited`) and Boyapati–Liskov–Shrira ownership-encapsulated lazy per-bucket
     upgrades (`VersionedBucket`, `needsBucketUpgrade`).
   - Proves **Multi-Turn Observational Equivalence (`lazyUpgrade_obs_eq_eagerUpgrade`)**: across any
     interleaved sequence of `read`, `write`, and zero-stall $O(1)$ `upgradeEpoch` turns over a
     sharded `Array` bucket store, lazy fault-in upgrades produce the exact same observation trace
     and logical final state as stop-the-world eager migration.
3. **Migration-Time Log Relinking, `Genealogy.Succeeds` (`LobCost`), & Continuation Lifting:**
   - Proves `relinkLogAcrossEpochs_sound`: an epoch-segmented log `(seg₁, UpgradeTurn cert, seg₂)`
     replays deterministically across step-function upgrades, commutes with `putr` log relinking,
     and preserves `Obend.Judge.Genealogy` genesis floors and `revert` corrigibility under explicit
     `LobCost` accounting (with 256-bit `cSHAKE256` `envelopeHeaderDigest_binds_or_collides`), plus
     unbounded multi-upgrade trace monotonicity & floor soundness (`runMultiEpochTrace_floors`).
   - Proves `liftYieldedContinuation_commutes`: suspended `Core.Machine` `.yielded` continuations
     (in memory or persisted as `HeapImage` `ByteArray`s) lift across heap-prefix/environment
     upgrades and commute identically with `stepRaw`, `runBounded`, and multi-yield traces.
-/
public import Obend.Repair.DeltaLensRenew
public import Obend.Judge.Genealogy
public import Obend.Core.HeapImage
public import Obend.Core.Collect
import all Obend.Judge.Genealogy

public section
namespace Obend.Repair

open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Collect
open Obend.Core.HeapImage
open Obend.Digest.HashBytes
open Obend.Core.Digest (Digest256)

set_option autoImplicit false

/-! ## 1. Edit Monoid Modules & Hofmann–Pierce–Wagner Symmetric Edit Lenses -/

/-- A monoid of edits `E` acting sequentially (`comp e₁ e₂` applies `e₁` then `e₂`) on states `S`. -/
structure EditModule (S : Type) (E : Type) where
  idEdit : E
  comp : E → E → E
  apply : E → S → S
  comp_id_left : ∀ e, comp idEdit e = e
  comp_id_right : ∀ e, comp e idEdit = e
  comp_assoc : ∀ a b c, comp (comp a b) c = comp a (comp b c)
  apply_id : ∀ s, apply idEdit s = s
  apply_comp : ∀ e₁ e₂ s, apply (comp e₁ e₂) s = apply e₂ (apply e₁ s)

/-- **Hofmann–Pierce–Wagner Symmetric Complemented Edit Lens (POPL '12).**
    Connects two state/edit modules `(S₁, M₁)` and `(S₂, M₂)` through a persistent complement `C`
    and consistency relation `Consistent : S₁ → C → S₂ → Prop`, translating both states (at
    initialization/migration) and incremental edits bidirectionally while preserving identity and
    composite edits. -/
structure SymmetricEditLens (S₁ S₂ C E₁ E₂ : Type) where
  mod₁ : EditModule S₁ E₁
  mod₂ : EditModule S₂ E₂
  Consistent : S₁ → C → S₂ → Prop
  initRight : S₁ → S₂ × C
  initRight_consistent : ∀ s₁, Consistent s₁ (initRight s₁).2 (initRight s₁).1
  putr : E₁ → C → E₂ × C
  putl : E₂ → C → E₁ × C
  putr_id : ∀ c, putr mod₁.idEdit c = (mod₂.idEdit, c)
  putl_id : ∀ c, putl mod₂.idEdit c = (mod₁.idEdit, c)
  putr_comp : ∀ e₁ e₁' c,
    let r₁ := putr e₁ c
    let r₂ := putr e₁' r₁.2
    putr (mod₁.comp e₁ e₁') c = (mod₂.comp r₁.1 r₂.1, r₂.2)
  putl_comp : ∀ e₂ e₂' c,
    let l₁ := putl e₂ c
    let l₂ := putl e₂' l₁.2
    putl (mod₂.comp e₂ e₂') c = (mod₁.comp l₁.1 l₂.1, l₂.2)
  putr_sound : ∀ {s₁ : S₁} {c : C} {s₂ : S₂} (e₁ : E₁),
    Consistent s₁ c s₂ →
    Consistent (mod₁.apply e₁ s₁) (putr e₁ c).2 (mod₂.apply (putr e₁ c).1 s₂)
  putl_sound : ∀ {s₁ : S₁} {c : C} {s₂ : S₂} (e₂ : E₂),
    Consistent s₁ c s₂ →
    Consistent (mod₁.apply (putl e₂ c).1 s₁) (putl e₂ c).2 (mod₂.apply e₂ s₂)

namespace SymmetricEditLens

/-- Dualize a symmetric edit lens given left-initialization `initLeft : S₂ → S₁ × C`. -/
def symm {S₁ S₂ C E₁ E₂ : Type} (L : SymmetricEditLens S₁ S₂ C E₁ E₂)
    (initLeft : S₂ → S₁ × C)
    (hInit : ∀ s₂, L.Consistent (initLeft s₂).1 (initLeft s₂).2 s₂) :
    SymmetricEditLens S₂ S₁ C E₂ E₁ where
  mod₁ := L.mod₂
  mod₂ := L.mod₁
  Consistent s₂ c s₁ := L.Consistent s₁ c s₂
  initRight := initLeft
  initRight_consistent := hInit
  putr := L.putl
  putl := L.putr
  putr_id := L.putl_id
  putl_id := L.putr_id
  putr_comp := L.putl_comp
  putl_comp := L.putr_comp
  putr_sound e₂ hc := L.putl_sound e₂ hc
  putl_sound e₁ hc := L.putr_sound e₁ hc

/-- Horizontal composition of symmetric edit lenses `S₁ ⇄_{C₁₂} S₂` and `S₂ ⇄_{C₂₃} S₃` over the
    product complement `C₁₂ × C₂₃` (Hofmann–Pierce–Wagner Theorem 3.3). -/
def comp {S₁ S₂ S₃ C₁₂ C₂₃ E₁ E₂ E₃ : Type}
    (L₁₂ : SymmetricEditLens S₁ S₂ C₁₂ E₁ E₂)
    (L₂₃ : SymmetricEditLens S₂ S₃ C₂₃ E₂ E₃)
    (hModEq : L₁₂.mod₂ = L₂₃.mod₁) :
    SymmetricEditLens S₁ S₃ (C₁₂ × C₂₃) E₁ E₃ where
  mod₁ := L₁₂.mod₁
  mod₂ := L₂₃.mod₂
  Consistent s₁ c s₃ := ∃ s₂ : S₂, L₁₂.Consistent s₁ c.1 s₂ ∧ L₂₃.Consistent s₂ c.2 s₃
  initRight s₁ :=
    let r₁ := L₁₂.initRight s₁
    let r₂ := L₂₃.initRight r₁.1
    (r₂.1, (r₁.2, r₂.2))
  initRight_consistent s₁ :=
    ⟨(L₁₂.initRight s₁).1, L₁₂.initRight_consistent s₁, L₂₃.initRight_consistent _⟩
  putr e₁ c :=
    let r₁ := L₁₂.putr e₁ c.1
    let r₂ := L₂₃.putr r₁.1 c.2
    (r₂.1, (r₁.2, r₂.2))
  putl e₃ c :=
    let l₂ := L₂₃.putl e₃ c.2
    let l₁ := L₁₂.putl l₂.1 c.1
    (l₁.1, (l₁.2, l₂.2))
  putr_id c := by
    rcases c with ⟨c₁₂, c₂₃⟩
    have hid : L₁₂.mod₂.idEdit = L₂₃.mod₁.idEdit := congrArg EditModule.idEdit hModEq
    change ((L₂₃.putr (L₁₂.putr L₁₂.mod₁.idEdit c₁₂).1 c₂₃).1,
      ((L₁₂.putr L₁₂.mod₁.idEdit c₁₂).2,
       (L₂₃.putr (L₁₂.putr L₁₂.mod₁.idEdit c₁₂).1 c₂₃).2)) = (L₂₃.mod₂.idEdit, (c₁₂, c₂₃))
    rw [L₁₂.putr_id, hid, L₂₃.putr_id]
  putl_id c := by
    rcases c with ⟨c₁₂, c₂₃⟩
    have hid : L₂₃.mod₁.idEdit = L₁₂.mod₂.idEdit := (congrArg EditModule.idEdit hModEq).symm
    change ((L₁₂.putl (L₂₃.putl L₂₃.mod₂.idEdit c₂₃).1 c₁₂).1,
      ((L₁₂.putl (L₂₃.putl L₂₃.mod₂.idEdit c₂₃).1 c₁₂).2,
       (L₂₃.putl L₂₃.mod₂.idEdit c₂₃).2)) = (L₁₂.mod₁.idEdit, (c₁₂, c₂₃))
    rw [L₂₃.putl_id, hid, L₁₂.putl_id]
  putr_comp e₁ e₁' c := by
    rcases c with ⟨c₁₂, c₂₃⟩
    have hcomp : L₁₂.mod₂.comp = L₂₃.mod₁.comp := congrArg EditModule.comp hModEq
    change ((L₂₃.putr (L₁₂.putr (L₁₂.mod₁.comp e₁ e₁') c₁₂).1 c₂₃).1,
      ((L₁₂.putr (L₁₂.mod₁.comp e₁ e₁') c₁₂).2,
       (L₂₃.putr (L₁₂.putr (L₁₂.mod₁.comp e₁ e₁') c₁₂).1 c₂₃).2)) = _
    rw [L₁₂.putr_comp, hcomp, L₂₃.putr_comp]
  putl_comp e₃ e₃' c := by
    rcases c with ⟨c₁₂, c₂₃⟩
    have hcomp : L₂₃.mod₁.comp = L₁₂.mod₂.comp := (congrArg EditModule.comp hModEq).symm
    change ((L₁₂.putl (L₂₃.putl (L₂₃.mod₂.comp e₃ e₃') c₂₃).1 c₁₂).1,
      ((L₁₂.putl (L₂₃.putl (L₂₃.mod₂.comp e₃ e₃') c₂₃).1 c₁₂).2,
       (L₂₃.putl (L₂₃.mod₂.comp e₃ e₃') c₂₃).2)) = _
    rw [L₂₃.putl_comp, hcomp, L₁₂.putl_comp]
  putr_sound {s₁} {c} {s₃} e₁ hc := by
    rcases c with ⟨c₁₂, c₂₃⟩
    rcases hc with ⟨s₂, hc₁, hc₂⟩
    have h1 := L₁₂.putr_sound e₁ hc₁
    have h2 := L₂₃.putr_sound (L₁₂.putr e₁ c₁₂).1 hc₂
    have happly : L₁₂.mod₂.apply = L₂₃.mod₁.apply := congrArg EditModule.apply hModEq
    rw [happly] at h1
    exact ⟨_, h1, h2⟩
  putl_sound {s₁} {c} {s₃} e₃ hc := by
    rcases c with ⟨c₁₂, c₂₃⟩
    rcases hc with ⟨s₂, hc₁, hc₂⟩
    have h2 := L₂₃.putl_sound e₃ hc₂
    have happly : L₂₃.mod₁.apply = L₁₂.mod₂.apply := (congrArg EditModule.apply hModEq).symm
    rw [happly] at h2
    have h1 := L₁₂.putl_sound (L₂₃.putl e₃ c₂₃).1 hc₁
    exact ⟨_, h1, h2⟩

/-- One step of a multi-turn interleaved bidirectional edit session. -/
inductive BidirEditTurn (E₁ E₂ : Type) where
  | left (e₁ : E₁)
  | right (e₂ : E₂)
  deriving DecidableEq, Repr

/-- Execute a multi-turn sequence of left and right replica edits across `L`. -/
def runBidirEditTrace {S₁ S₂ C E₁ E₂ : Type} (L : SymmetricEditLens S₁ S₂ C E₁ E₂) :
    (S₁ × C × S₂) → List (BidirEditTurn E₁ E₂) → (S₁ × C × S₂)
  | scs, [] => scs
  | (s₁, c, s₂), .left e₁ :: rest =>
    let (e₂, c') := L.putr e₁ c
    runBidirEditTrace L (L.mod₁.apply e₁ s₁, c', L.mod₂.apply e₂ s₂) rest
  | (s₁, c, s₂), .right e₂ :: rest =>
    let (e₁, c') := L.putl e₂ c
    runBidirEditTrace L (L.mod₁.apply e₁ s₁, c', L.mod₂.apply e₂ s₂) rest

/-- **Multi-Turn Bidirectional Consistency Invariant.** Any arbitrarily interleaved trace of
    `S₁`-edits and `S₂`-edits preserves `L.Consistent s₁ c s₂`. -/
theorem runBidirEditTrace_preserves_consistent {S₁ S₂ C E₁ E₂ : Type}
    (L : SymmetricEditLens S₁ S₂ C E₁ E₂) :
    ∀ (turns : List (BidirEditTurn E₁ E₂)) {s₁ : S₁} {c : C} {s₂ : S₂},
      L.Consistent s₁ c s₂ →
      let out := runBidirEditTrace L (s₁, c, s₂) turns
      L.Consistent out.1 out.2.1 out.2.2
  | [], _, _, _, hc => hc
  | .left e₁ :: rest, _, _, _, hc =>
    runBidirEditTrace_preserves_consistent L rest (L.putr_sound e₁ hc)
  | .right e₂ :: rest, _, _, _, hc =>
    runBidirEditTrace_preserves_consistent L rest (L.putl_sound e₂ hc)

end SymmetricEditLens

/-! ### Embedding `DeltaLens` into `SymmetricEditLens` (`DeltaLens.toSymmetricEditLens`) -/

/-- Codiscrete overwrite edit monoid on `α`: `none` is the identity edit, `some a'` overwrites the
    state to `a'`. -/
abbrev OverwriteEdit (α : Type) := Option α

def overwriteEditModule (α : Type) : EditModule α (OverwriteEdit α) where
  idEdit := none
  comp e₁ e₂ := match e₂ with | none => e₁ | some x => some x
  apply e x := match e with | none => x | some x' => x'
  comp_id_left e := by cases e <;> rfl
  comp_id_right _ := rfl
  comp_assoc a b c := by cases c <;> cases b <;> rfl
  apply_id _ := rfl
  apply_comp e₁ e₂ s := by cases e₂ <;> cases e₁ <;> rfl

/-- Forward edit translation helper for `DeltaLens.toSymmetricEditLens` (kept as a top-level `def`
    so `#tooth` can mutate its complement update directly). -/
def deltaPutr {S V : Type} (L : DeltaLens S V) (e₁ : OverwriteEdit S) (c : S) :
    OverwriteEdit V × S :=
  match e₁ with
  | none => (none, c)
  | some s' => (some (L.get s'), s')

/-- Backward edit translation helper for `DeltaLens.toSymmetricEditLens`. -/
def deltaPutl {S V : Type} (L : DeltaLens S V) (e₂ : OverwriteEdit V) (c : S) :
    OverwriteEdit S × S :=
  match e₂ with
  | none => (none, c)
  | some v' =>
    let s' := L.put c v'
    (some s', s')

theorem deltaToSymmetric_putr_sound {S V : Type} (L : DeltaLens S V)
    {s : S} {c : S} {v : V} (e₁ : OverwriteEdit S)
    (hc : c = s ∧ L.get s = v) :
    let r := deltaPutr L e₁ c
    r.2 = (overwriteEditModule S).apply e₁ s ∧
      L.get ((overwriteEditModule S).apply e₁ s) = (overwriteEditModule V).apply r.1 v := by
  cases e₁ with
  | none => exact hc
  | some s' => exact ⟨rfl, rfl⟩

theorem deltaToSymmetric_putl_sound {S V : Type} (L : DeltaLens S V)
    {s : S} {c : S} {v : V} (e₂ : OverwriteEdit V)
    (hc : c = s ∧ L.get s = v) :
    let l := deltaPutl L e₂ c
    l.2 = (overwriteEditModule S).apply l.1 s ∧
      L.get ((overwriteEditModule S).apply l.1 s) = (overwriteEditModule V).apply e₂ v := by
  cases e₂ with
  | none => exact hc
  | some v' => exact ⟨rfl, L.put_get c v'⟩

/-- **Every Clarke `DeltaLens S V` canonically embeds into `SymmetricEditLens`**, using `put_get`
    for `putl_sound` and `put_put` for `putl_comp`. -/
def DeltaLens.toSymmetricEditLens {S V : Type} (L : DeltaLens S V) :
    SymmetricEditLens S V S (OverwriteEdit S) (OverwriteEdit V) where
  mod₁ := overwriteEditModule S
  mod₂ := overwriteEditModule V
  Consistent s c v := c = s ∧ L.get s = v
  initRight s := (L.get s, s)
  initRight_consistent _ := ⟨rfl, rfl⟩
  putr := deltaPutr L
  putl := deltaPutl L
  putr_id _ := rfl
  putl_id _ := rfl
  putr_comp e₁ e₁' c := by cases e₁' <;> cases e₁ <;> rfl
  putl_comp e₂ e₂' c := by
    cases e₂' with
    | none => cases e₂ <;> rfl
    | some v₂ =>
      cases e₂ with
      | none => rfl
      | some v₁ =>
        simp only [deltaPutl, overwriteEditModule]
        rw [L.put_put]
  putr_sound e₁ hc := deltaToSymmetric_putr_sound L e₁ hc
  putl_sound e₂ hc := deltaToSymmetric_putl_sound L e₂ hc

/-- `get_put` recovers unchanged-view stability on `L.toSymmetricEditLens`. -/
theorem DeltaLens.toSymmetricEditLens_unchanged_view {S V : Type} (L : DeltaLens S V)
    {s c : S} {v : V} (hc : (L.toSymmetricEditLens).Consistent s c v) :
    (L.toSymmetricEditLens.putl (some v) c).1 = some s := by
  rcases hc with ⟨rfl, rfl⟩
  simp [DeltaLens.toSymmetricEditLens, deltaPutl, L.get_put]

/-! ### Genuine Non-Projection / Non-Bijection Case Study: Peer Schema Split -/

/-- Schema `V₁`: holds `sharedBalance : Int` and private `legacyNote : String` (absent in `V₂`). -/
structure PeerRecordV1 where
  sharedBalance : Int
  legacyNote : String
  deriving DecidableEq, Repr

/-- Schema `V₂`: holds `sharedBalance : Int` and private `auditFlags : UInt64 × Bool` (absent in `V₁`).
    Neither `DeltaLens PeerRecordV1 PeerRecordV2`, `DeltaLens PeerRecordV2 PeerRecordV1`, nor
    `AlgEquiv` applies cleanly across independent incremental mutations on both sides. -/
structure PeerRecordV2 where
  sharedBalance : Int
  auditFlags : UInt64 × Bool
  deriving DecidableEq, Repr

structure PeerEditV1 where
  deltaBalance : Int
  newNote : Option String
  deriving DecidableEq, Repr

structure PeerEditV2 where
  deltaBalance : Int
  newFlags : Option (UInt64 × Bool)
  deriving DecidableEq, Repr

def peerModV1 : EditModule PeerRecordV1 PeerEditV1 where
  idEdit := ⟨0, none⟩
  comp e₁ e₂ := ⟨e₁.deltaBalance + e₂.deltaBalance,
    match e₂.newNote with | none => e₁.newNote | some n => some n⟩
  apply e s := ⟨s.sharedBalance + e.deltaBalance, e.newNote.getD s.legacyNote⟩
  comp_id_left e := by rcases e with ⟨d, n⟩; cases n <;> simp [Int.zero_add]
  comp_id_right e := by rcases e with ⟨d, n⟩; simp [Int.add_zero]
  comp_assoc a b c := by
    rcases a with ⟨da, na⟩; rcases b with ⟨db, nb⟩; rcases c with ⟨dc, nc⟩
    cases nc <;> cases nb <;> simp [Int.add_assoc]
  apply_id s := by rcases s with ⟨b, n⟩; simp [Int.add_zero]
  apply_comp e₁ e₂ s := by
    rcases e₁ with ⟨d1, n1⟩; rcases e₂ with ⟨d2, n2⟩; rcases s with ⟨b, ns⟩
    cases n2 <;> cases n1 <;> simp [Int.add_assoc]

def peerModV2 : EditModule PeerRecordV2 PeerEditV2 where
  idEdit := ⟨0, none⟩
  comp e₁ e₂ := ⟨e₁.deltaBalance + e₂.deltaBalance,
    match e₂.newFlags with | none => e₁.newFlags | some f => some f⟩
  apply e s := ⟨s.sharedBalance + e.deltaBalance, e.newFlags.getD s.auditFlags⟩
  comp_id_left e := by rcases e with ⟨d, f⟩; cases f <;> simp [Int.zero_add]
  comp_id_right e := by rcases e with ⟨d, f⟩; simp [Int.add_zero]
  comp_assoc a b c := by
    rcases a with ⟨da, fa⟩; rcases b with ⟨db, fb⟩; rcases c with ⟨dc, fc⟩
    cases fc <;> cases fb <;> simp [Int.add_assoc]
  apply_id s := by rcases s with ⟨b, f⟩; simp [Int.add_zero]
  apply_comp e₁ e₂ s := by
    rcases e₁ with ⟨d1, f1⟩; rcases e₂ with ⟨d2, f2⟩; rcases s with ⟨b, fs⟩
    cases f2 <;> cases f1 <;> simp [Int.add_assoc]

abbrev PeerComplement := String × (UInt64 × Bool)

def peerSplitPutr (e₁ : PeerEditV1) (c : PeerComplement) : PeerEditV2 × PeerComplement :=
  (⟨e₁.deltaBalance, none⟩, (e₁.newNote.getD c.1, c.2))

def peerSplitPutl (e₂ : PeerEditV2) (c : PeerComplement) : PeerEditV1 × PeerComplement :=
  (⟨e₂.deltaBalance, none⟩, (c.1, e₂.newFlags.getD c.2))

/-- Concrete `SymmetricEditLens` over diverging peer schemas `PeerRecordV1 ⇄_C PeerRecordV2`
    preserving independent private fields on both sides alongside additive balance deltas. -/
def peerSplitEditLens :
    SymmetricEditLens PeerRecordV1 PeerRecordV2 PeerComplement PeerEditV1 PeerEditV2 where
  mod₁ := peerModV1
  mod₂ := peerModV2
  Consistent s₁ c s₂ :=
    s₁.sharedBalance = s₂.sharedBalance ∧ s₁.legacyNote = c.1 ∧ s₂.auditFlags = c.2
  initRight s₁ := (⟨s₁.sharedBalance, (0, false)⟩, (s₁.legacyNote, (0, false)))
  initRight_consistent _ := ⟨rfl, rfl, rfl⟩
  putr := peerSplitPutr
  putl := peerSplitPutl
  putr_id c := by rcases c with ⟨n, f⟩; rfl
  putl_id c := by rcases c with ⟨n, f⟩; rfl
  putr_comp e₁ e₁' c := by
    rcases e₁ with ⟨d1, n1⟩; rcases e₁' with ⟨d1', n1'⟩; rcases c with ⟨cn, cf⟩
    cases n1' <;> cases n1 <;> simp [peerModV1, peerModV2, peerSplitPutr]
  putl_comp e₂ e₂' c := by
    rcases e₂ with ⟨d2, f2⟩; rcases e₂' with ⟨d2', f2'⟩; rcases c with ⟨cn, cf⟩
    cases f2' <;> cases f2 <;> simp [peerModV1, peerModV2, peerSplitPutl]
  putr_sound e₁ hc := by
    rcases hc with ⟨hb, hn, hf⟩
    refine ⟨by simp [peerModV1, peerModV2, peerSplitPutr, hb], ?_, hf⟩
    cases e₁.newNote <;> simp [peerModV1, peerSplitPutr, hn]
  putl_sound e₂ hc := by
    rcases hc with ⟨hb, hn, hf⟩
    refine ⟨by simp [peerModV1, peerModV2, peerSplitPutl, hb], hn, ?_⟩
    cases e₂.newFlags <;> simp [peerModV2, peerSplitPutl, hf]

theorem peerSplitLens_putr_sound {s₁ : PeerRecordV1} {c : PeerComplement} {s₂ : PeerRecordV2}
    (e₁ : PeerEditV1) (hc : peerSplitEditLens.Consistent s₁ c s₂) :
    peerSplitEditLens.Consistent
      (peerModV1.apply e₁ s₁) (peerSplitPutr e₁ c).2
      (peerModV2.apply (peerSplitPutr e₁ c).1 s₂) :=
  peerSplitEditLens.putr_sound e₁ hc

/-! ## 2. Law-Strengthening Epistemic Migration & Thor Lazy Per-Bucket Store (Condition M1) -/

/-- Typed refusal when an offline `v₁` edit or state violates a strengthened `v₂` invariant. -/
inductive UpgradeRefusal where
  | tightenedLawViolated (epoch : Nat)
  | bucketOutOfBounds (idx : Nat)
  deriving DecidableEq, Repr

/-- Upstart `pastSO`/`futureSO` law-strengthening adapter over a `SymmetricEditLens`: `law₂` on
    `S₂` strengthens `law₁` on `S₁`, and late-arriving `E₁` edits are admitted iff the resulting
    `S₂` state satisfies `law₂`. -/
structure CheckedUpgradeAdapter (S₁ S₂ C E₁ E₂ : Type) where
  lens : SymmetricEditLens S₁ S₂ C E₁ E₂
  targetEpoch : Nat
  law₁ : S₁ → Bool
  law₂ : S₂ → Bool
  law_strengthens : ∀ {s₁ c s₂}, lens.Consistent s₁ c s₂ → law₂ s₂ = true → law₁ s₁ = true

/-- Translate a `v₁` edit across `CheckedUpgradeAdapter` (`pastSO` shadow simulation), checking the
    strengthened post-law `law₂`. -/
def translateOldEdit {S₁ S₂ C E₁ E₂ : Type}
    (A : CheckedUpgradeAdapter S₁ S₂ C E₁ E₂)
    (e₁ : E₁) (c : C) (s₂ : S₂) : Except UpgradeRefusal (E₂ × C × { s₂' : S₂ // A.law₂ s₂' = true }) :=
  let (e₂, c') := A.lens.putr e₁ c
  let s₂' := A.lens.mod₂.apply e₂ s₂
  if hLaw : A.law₂ s₂' = true then
    .ok (e₂, c', ⟨s₂', hLaw⟩)
  else
    .error (.tightenedLawViolated A.targetEpoch)

/-- **Soundness of Law-Strengthening Edit Translation:** every accepted `v₁` edit produces a
    subtype-certified `{ s₂' : S₂ // A.law₂ s₂' = true }` state, maintains `Consistent`, and
    implies `A.law₁` on the stepped `S₁` state. -/
theorem translateOldEdit_sound {S₁ S₂ C E₁ E₂ : Type}
    (A : CheckedUpgradeAdapter S₁ S₂ C E₁ E₂)
    {s₁ : S₁} {c : C} {s₂ : S₂} (hc : A.lens.Consistent s₁ c s₂) (e₁ : E₁)
    {e₂ : E₂} {c' : C} {sub : { s₂' : S₂ // A.law₂ s₂' = true }}
    (hok : translateOldEdit A e₁ c s₂ = .ok (e₂, c', sub)) :
    A.lens.Consistent (A.lens.mod₁.apply e₁ s₁) c' sub.1 ∧
      A.law₂ sub.1 = true ∧
      A.law₁ (A.lens.mod₁.apply e₁ s₁) = true := by
  unfold translateOldEdit at hok
  dsimp only at hok
  split at hok
  · next hLaw =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨he₂, hc', hsub⟩ := hok
    subst he₂; subst hc'; subst hsub
    have hcons := A.lens.putr_sound e₁ hc
    exact ⟨hcons, hLaw, A.law_strengthens hcons hLaw⟩
  · cases hok

/-- **Environment Anti-Narrowing Completeness (`skip_implies_contract_violation`):**
    `translateOldEdit` refuses an edit **if and only if** the translated step genuinely violates
    the strengthened post-law `A.law₂`. -/
theorem translateOldEdit_refuses_iff_law_violated {S₁ S₂ C E₁ E₂ : Type}
    (A : CheckedUpgradeAdapter S₁ S₂ C E₁ E₂)
    (e₁ : E₁) (c : C) (s₂ : S₂) :
    (∃ err, translateOldEdit A e₁ c s₂ = .error err) ↔
      A.law₂ (A.lens.mod₂.apply (A.lens.putr e₁ c).1 s₂) = false := by
  unfold translateOldEdit
  dsimp only
  by_cases hLaw : A.law₂ (A.lens.mod₂.apply (A.lens.putr e₁ c).1 s₂) = true
  · rw [dite_eq_left hLaw]
    simp [hLaw]
  · rw [dite_eq_right hLaw]
    simp [Bool.not_eq_true _ ▸ hLaw]

/-- Completeness / satisfiability of `translateOldEdit`: every `v₁` edit whose translated `v₂`
    post-state satisfies `A.law₂` succeeds with `.ok`. -/
theorem translateOldEdit_complete {S₁ S₂ C E₁ E₂ : Type}
    (A : CheckedUpgradeAdapter S₁ S₂ C E₁ E₂)
    (e₁ : E₁) (c : C) (s₂ : S₂)
    (hLaw : A.law₂ (A.lens.mod₂.apply (A.lens.putr e₁ c).1 s₂) = true) :
    ∃ e₂ c' sub, translateOldEdit A e₁ c s₂ = .ok (e₂, c', sub) := by
  unfold translateOldEdit
  dsimp only
  rw [dite_eq_left hLaw]
  exact ⟨_, _, _, rfl⟩

/-- Concrete law-tightening adapter (`balance >= -100` strengthened to `balance >= 0` at epoch 2)
    witnessing both positive acceptance and tightened-floor refusal of `translateOldEdit`. -/
def peerTightenedAdapter :
    CheckedUpgradeAdapter PeerRecordV1 PeerRecordV2 PeerComplement PeerEditV1 PeerEditV2 where
  lens := peerSplitEditLens
  targetEpoch := 2
  law₁ s₁ := decide (-100 ≤ s₁.sharedBalance)
  law₂ s₂ := decide (0 ≤ s₂.sharedBalance)
  law_strengthens hc h2 := by
    rcases hc with ⟨hb, _, _⟩
    simp only [decide_eq_true_eq] at h2 ⊢
    omega

example : ∃ e₂ c' sub,
    translateOldEdit peerTightenedAdapter ⟨15, some "ok"⟩ ("v1-init", (7, true)) ⟨20, (7, true)⟩ =
      .ok (e₂, c', sub) :=
  translateOldEdit_complete peerTightenedAdapter ⟨15, some "ok"⟩ ("v1-init", (7, true))
    ⟨20, (7, true)⟩ (by decide)

theorem translateOldEdit_inhabited :
    (∃ e₂ c' sub,
      translateOldEdit peerTightenedAdapter ⟨15, some "ok"⟩ ("v1-init", (7, true)) ⟨20, (7, true)⟩ =
        .ok (e₂, c', sub) ∧
      sub.1.sharedBalance = 35) ∧
    translateOldEdit peerTightenedAdapter ⟨-50, none⟩ ("v1-init", (7, true)) ⟨20, (7, true)⟩ =
      .error (.tightenedLawViolated 2) := by
  refine ⟨⟨⟨15, none⟩, ("ok", (7, true)), ⟨⟨35, (7, true)⟩, by decide⟩, rfl, rfl⟩, rfl⟩

/-! ### Thor Lazy Per-Bucket Object Upgrades (`LazyBucketStore`, Boyapati et al. OOPSLA '03) -/

/-- One bucket in a sharded persistent object store: carries its own `epoch` watermark and
    encapsulated `payload` (Thor Condition M1: bucket transform depends solely on `(epoch, payload)`
    of that bucket, never reading sibling buckets). -/
structure VersionedBucket (Val : Type) where
  epoch : Nat
  payload : Val
  deriving DecidableEq, Repr

/-- Per-epoch bucket migration table: `step e v` upgrades a bucket payload from epoch `e` to `e + 1`. -/
structure EpochMigrator (Val : Type) where
  step : Nat → Val → Val

/-- Upgrade a payload across multiple epochs `fromEpoch .. toEpoch`. -/
def migrateSteps {Val : Type} (mig : EpochMigrator Val) : Nat → Nat → Val → Val
  | _, 0, v => v
  | e, k + 1, v => migrateSteps mig (e + 1) k (mig.step e v)

def migrateRange {Val : Type} (mig : EpochMigrator Val) (fromEpoch toEpoch : Nat) (v : Val) : Val :=
  migrateSteps mig fromEpoch (toEpoch - fromEpoch) v

theorem migrateRange_refl {Val : Type} (mig : EpochMigrator Val) (e : Nat) (v : Val) :
    migrateRange mig e e v = v := by
  simp [migrateRange, migrateSteps]

private theorem migrateSteps_snoc {Val : Type} (mig : EpochMigrator Val) :
    ∀ (k e : Nat) (v : Val),
      migrateSteps mig e (k + 1) v = mig.step (e + k) (migrateSteps mig e k v)
  | 0, e, v => by simp [migrateSteps]
  | k + 1, e, v => by
    change migrateSteps mig (e + 1) (k + 1) (mig.step e v) =
      mig.step (e + (k + 1)) (migrateSteps mig (e + 1) k (mig.step e v))
    rw [migrateSteps_snoc mig k (e + 1) (mig.step e v), show e + 1 + k = e + (k + 1) by omega]

theorem migrateRange_step_top {Val : Type} (mig : EpochMigrator Val)
    {e T : Nat} (hle : e ≤ T) (v : Val) :
    migrateRange mig e (T + 1) v = mig.step T (migrateRange mig e T v) := by
  unfold migrateRange
  have hsub : T + 1 - e = (T - e) + 1 := by omega
  have hsum : e + (T - e) = T := by omega
  rw [hsub, migrateSteps_snoc, hsum]

/-- Sharded persistent store holding `Array (VersionedBucket Val)` and a global `targetEpoch`. -/
structure LazyBucketStore (Val : Type) where
  targetEpoch : Nat
  buckets : Array (VersionedBucket Val)
  deriving DecidableEq, Repr

/-- Epoch check guarding lazy fault-in upgrades on bucket access (kept top-level for `#tooth`). -/
def needsBucketUpgrade {Val : Type} (targetEpoch : Nat) (b : VersionedBucket Val) : Bool :=
  decide (b.epoch < targetEpoch)

/-- Fault-in bucket `b` to `targetEpoch` iff `needsBucketUpgrade targetEpoch b` holds. -/
def faultInBucket {Val : Type} (mig : EpochMigrator Val) (targetEpoch : Nat)
    (b : VersionedBucket Val) : VersionedBucket Val :=
  if needsBucketUpgrade targetEpoch b then
    { epoch := targetEpoch, payload := migrateRange mig b.epoch targetEpoch b.payload }
  else
    b

/-- Multi-turn workload operations over the sharded bucket store: point reads, point writes, and
    live schema epoch upgrades. -/
inductive BucketStoreTurn (Val Obs : Type) where
  | read (idx : Nat) (project : Val → Obs)
  | write (idx : Nat) (update : Val → Val)
  | upgradeEpoch

/-- **Lazy execution (`O(1)` zero-stall upgrade):** `upgradeEpoch` bumps `targetEpoch` without
    touching a single cold bucket; `read` and `write` fault-in only the touched bucket `idx`. -/
def stepLazyStore {Val Obs : Type} (mig : EpochMigrator Val)
    (st : LazyBucketStore Val) (turn : BucketStoreTurn Val Obs) :
    LazyBucketStore Val × Option Obs :=
  match turn with
  | .read idx proj =>
    if h : idx < st.buckets.size then
      let b' := faultInBucket mig st.targetEpoch st.buckets[idx]
      ({ st with buckets := st.buckets.set idx b' }, some (proj b'.payload))
    else
      (st, none)
  | .write idx upd =>
    if h : idx < st.buckets.size then
      let b' := faultInBucket mig st.targetEpoch st.buckets[idx]
      let b'' : VersionedBucket Val := { epoch := st.targetEpoch, payload := upd b'.payload }
      ({ st with buckets := st.buckets.set idx b'' }, none)
    else
      (st, none)
  | .upgradeEpoch =>
    ({ st with targetEpoch := st.targetEpoch + 1 }, none)

/-- **Eager reference execution (`O(N)` stop-the-world upgrade):** `upgradeEpoch` immediately
    migrates all `N` buckets in the store. -/
def stepEagerStore {Val Obs : Type} (mig : EpochMigrator Val)
    (st : LazyBucketStore Val) (turn : BucketStoreTurn Val Obs) :
    LazyBucketStore Val × Option Obs :=
  match turn with
  | .read idx proj =>
    if h : idx < st.buckets.size then
      (st, some (proj st.buckets[idx].payload))
    else
      (st, none)
  | .write idx upd =>
    if h : idx < st.buckets.size then
      let b'' : VersionedBucket Val :=
        { epoch := st.targetEpoch, payload := upd st.buckets[idx].payload }
      ({ st with buckets := st.buckets.set idx b'' }, none)
    else
      (st, none)
  | .upgradeEpoch =>
    let T' := st.targetEpoch + 1
    let bs' := st.buckets.map fun b =>
      { epoch := T', payload := mig.step st.targetEpoch b.payload }
    ({ targetEpoch := T', buckets := bs' }, none)

def runLazyStoreTrace {Val Obs : Type} (mig : EpochMigrator Val) :
    LazyBucketStore Val → List (BucketStoreTurn Val Obs) → LazyBucketStore Val × List Obs
  | st, [] => (st, [])
  | st, t :: rest =>
    let (st', mo) := stepLazyStore mig st t
    let (finalSt, obs) := runLazyStoreTrace mig st' rest
    (finalSt, match mo with | some o => o :: obs | none => obs)

def runEagerStoreTrace {Val Obs : Type} (mig : EpochMigrator Val) :
    LazyBucketStore Val → List (BucketStoreTurn Val Obs) → LazyBucketStore Val × List Obs
  | st, [] => (st, [])
  | st, t :: rest =>
    let (st', mo) := stepEagerStore mig st t
    let (finalSt, obs) := runEagerStoreTrace mig st' rest
    (finalSt, match mo with | some o => o :: obs | none => obs)

/-- Flush all remaining cold buckets of a `LazyBucketStore` to `targetEpoch`. -/
def flushLazyBuckets {Val : Type} (mig : EpochMigrator Val)
    (st : LazyBucketStore Val) : LazyBucketStore Val :=
  { st with buckets := st.buckets.map (faultInBucket mig st.targetEpoch) }

/-- Thor M1 simulation invariant relating a mixed-epoch `LazyBucketStore` to the stop-the-world
    `eager` store. -/
structure ThorSimulates {Val : Type} (mig : EpochMigrator Val)
    (lazySt eagerSt : LazyBucketStore Val) : Prop where
  sameEpoch : lazySt.targetEpoch = eagerSt.targetEpoch
  sameSize : lazySt.buckets.size = eagerSt.buckets.size
  bucketRel : ∀ (i : Nat) (hl : i < lazySt.buckets.size) (he : i < eagerSt.buckets.size),
    lazySt.buckets[i].epoch ≤ lazySt.targetEpoch ∧
    eagerSt.buckets[i].epoch = eagerSt.targetEpoch ∧
    migrateRange mig lazySt.buckets[i].epoch lazySt.targetEpoch lazySt.buckets[i].payload =
      eagerSt.buckets[i].payload

private theorem faultInBucket_agrees {Val : Type} (mig : EpochMigrator Val)
    {T : Nat} {b eb : VersionedBucket Val}
    (hle : b.epoch ≤ T)
    (hmig : migrateRange mig b.epoch T b.payload = eb.payload) :
    (faultInBucket mig T b).epoch = T ∧ (faultInBucket mig T b).payload = eb.payload := by
  unfold faultInBucket needsBucketUpgrade
  by_cases hlt : b.epoch < T
  · simp [hlt, hmig]
  · have heq : b.epoch = T := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨heq, ?_⟩
    rw [heq, migrateRange_refl] at hmig
    exact hmig

theorem stepLazyStore_simulates_eager {Val Obs : Type} (mig : EpochMigrator Val)
    {lazySt eagerSt : LazyBucketStore Val}
    (hsim : ThorSimulates mig lazySt eagerSt)
    (turn : BucketStoreTurn Val Obs) :
    let lRes := stepLazyStore mig lazySt turn
    let eRes := stepEagerStore mig eagerSt turn
    lRes.2 = eRes.2 ∧ ThorSimulates mig lRes.1 eRes.1 := by
  rcases hsim with ⟨hEp, hSz, hRel⟩
  cases turn with
  | read idx proj =>
    dsimp only [stepLazyStore, stepEagerStore]
    by_cases hlt : idx < lazySt.buckets.size
    · have hltE : idx < eagerSt.buckets.size := hSz ▸ hlt
      rw [dite_eq_left hlt, dite_eq_left hltE]
      obtain ⟨hle, heEp, hmig⟩ := hRel idx hlt hltE
      obtain ⟨hfEp, hfPay⟩ := faultInBucket_agrees mig hle hmig
      refine ⟨by rw [hfPay], ⟨hEp, by simp [hSz], ?_⟩⟩
      intro i hiL hiE
      simp only [Array.size_set] at hiL
      by_cases hEq : idx = i
      · subst hEq
        simp only [Array.getElem_set_self]
        exact ⟨by omega, heEp, by rw [hfEp, migrateRange_refl, hfPay]⟩
      · simp only [Array.getElem_set, hEq, ↓reduceIte]
        exact hRel i hiL hiE
    · have hltE : ¬ idx < eagerSt.buckets.size := hSz ▸ hlt
      rw [dite_eq_right hlt, dite_eq_right hltE]
      exact ⟨rfl, ⟨hEp, hSz, hRel⟩⟩
  | write idx upd =>
    dsimp only [stepLazyStore, stepEagerStore]
    by_cases hlt : idx < lazySt.buckets.size
    · have hltE : idx < eagerSt.buckets.size := hSz ▸ hlt
      rw [dite_eq_left hlt, dite_eq_left hltE]
      obtain ⟨hle, heEp, hmig⟩ := hRel idx hlt hltE
      obtain ⟨_, hfPay⟩ := faultInBucket_agrees mig hle hmig
      refine ⟨rfl, ⟨hEp, by simp [hSz], ?_⟩⟩
      intro i hiL hiE
      simp only [Array.size_set] at hiL hiE
      by_cases hEq : idx = i
      · subst hEq
        simp [migrateRange_refl, hfPay]
      · simp only [Array.getElem_set, hEq, ↓reduceIte]
        exact hRel i hiL hiE
    · have hltE : ¬ idx < eagerSt.buckets.size := hSz ▸ hlt
      rw [dite_eq_right hlt, dite_eq_right hltE]
      exact ⟨rfl, ⟨hEp, hSz, hRel⟩⟩
  | upgradeEpoch =>
    dsimp only [stepLazyStore, stepEagerStore]
    refine ⟨rfl, ⟨by dsimp only; omega, by simp [hSz], ?_⟩⟩
    intro i hiL hiE
    dsimp only at hiL hiE ⊢
    simp only [Array.size_map] at hiE
    obtain ⟨hle, _, hmig⟩ := hRel i hiL hiE
    simp only [Array.getElem_map]
    refine ⟨by omega, trivial, ?_⟩
    rw [migrateRange_step_top mig hle, hmig, hEp]

theorem flushLazyBuckets_eq_eager {Val : Type} (mig : EpochMigrator Val)
    {lazySt eagerSt : LazyBucketStore Val}
    (hsim : ThorSimulates mig lazySt eagerSt) :
    flushLazyBuckets mig lazySt = eagerSt := by
  rcases lazySt with ⟨lEp, lBs⟩
  rcases eagerSt with ⟨eEp, eBs⟩
  rcases hsim with ⟨hEp, hSz, hRel⟩
  dsimp only at hEp hSz hRel
  subst hEp
  unfold flushLazyBuckets
  congr 1
  apply Array.ext
  · simp [hSz]
  · intro i hiL hiE
    simp only [Array.size_map] at hiL
    simp only [Array.getElem_map]
    obtain ⟨hle, heEp, hmig⟩ := hRel i hiL hiE
    obtain ⟨hfEp, hfPay⟩ := faultInBucket_agrees mig hle hmig
    cases hbi : eBs[i]
    rw [hbi] at heEp hfPay
    dsimp only at heEp hfPay
    cases fl : faultInBucket mig lEp lBs[i]
    rw [fl] at hfEp hfPay
    dsimp only at hfEp hfPay
    subst hfEp; subst heEp; subst hfPay
    rfl

/-- **Thor Condition M1 Multi-Turn Observational Equivalence (`lazyUpgrade_obs_eq_eagerUpgrade`).**
    Starting from any synchronized store `initStore` (all buckets at `initStore.targetEpoch`),
    running ANY multi-turn sequence of point reads, point writes, and live epoch upgrades under
    `LazyBucketStore` produces the **exact same observation list** AND the **exact same flushed
    logical store** as stop-the-world eager migration, while performing zero bucket copies at
    `upgradeEpoch` time. -/
theorem lazyUpgrade_obs_eq_eagerUpgrade {Val Obs : Type} (mig : EpochMigrator Val)
    (initStore : LazyBucketStore Val)
    (hInit : ∀ (i : Nat) (hi : i < initStore.buckets.size),
      initStore.buckets[i].epoch = initStore.targetEpoch)
    (turns : List (BucketStoreTurn Val Obs)) :
    let (lazyFinal, lazyObs) := runLazyStoreTrace mig initStore turns
    let (eagerFinal, eagerObs) := runEagerStoreTrace mig initStore turns
    lazyObs = eagerObs ∧ flushLazyBuckets mig lazyFinal = eagerFinal := by
  have hSim0 : ThorSimulates mig initStore initStore := by
    refine ⟨rfl, rfl, fun i hi _ => ?_⟩
    have he := hInit i hi
    exact ⟨by omega, he, by rw [he, migrateRange_refl]⟩
  suffices hGen : ∀ (lSt eSt : LazyBucketStore Val),
      ThorSimulates mig lSt eSt →
      let (lFin, lObs) := runLazyStoreTrace mig lSt turns
      let (eFin, eObs) := runEagerStoreTrace mig eSt turns
      lObs = eObs ∧ ThorSimulates mig lFin eFin by
    obtain ⟨hObs, hSimFin⟩ := hGen initStore initStore hSim0
    exact ⟨hObs, flushLazyBuckets_eq_eager mig hSimFin⟩
  induction turns with
  | nil => intro lSt eSt hSim; exact ⟨rfl, hSim⟩
  | cons t rest ih =>
    intro lSt eSt hSim
    obtain ⟨hOut, hSim1⟩ := stepLazyStore_simulates_eager mig hSim t
    obtain ⟨hObsRest, hSimFin⟩ := ih _ _ hSim1
    dsimp only [runLazyStoreTrace, runEagerStoreTrace]
    rw [hOut]
    cases (stepEagerStore mig eSt t).2 <;> exact ⟨by simp [hObsRest], hSimFin⟩

/-! ## 3. Migration-Time Log Relinking, `Genealogy.Succeeds` (`LobCost`), & Continuation Lifting -/

section EpochLogRelinking

open Obend.Judge (TrustBase)
open Obend.Judge.Genealogy (Habitat Gate Exec LobCost Succeeds
  wellFormed admits succeed wellFormed_sound succession_sound_meaning revert_admitted)

/-- Domain customization `"OBEND.REPAIR.UPGRADE_ENVELOPE/v1"` as explicit UTF-8 bytes. -/
def upgradeEnvelopeCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x52, 0x45, 0x50, 0x41, 0x49, 0x52, 0x2e,
   0x55, 0x50, 0x47, 0x52, 0x41, 0x44, 0x45, 0x5f, 0x45, 0x4e, 0x56, 0x45, 0x4c,
   0x4f, 0x50, 0x45, 0x2f, 0x76, 0x31]

def upgradeEnvelopeHash : Hash :=
  Obend.Digest.Cshake256.cshake256Bytes upgradeEnvelopeCustomization

/-- Canonical wire header of an upgrade turn for 256-bit `cSHAKE256` commitment binding. -/
structure UpgradeWireHeader where
  fromEpoch : Nat
  toEpoch : Nat
  preGateName : String
  postGateName : String
  lobLabelCount : Nat
  deriving DecidableEq, Repr

def encUpgradeWireHeader (hdr : UpgradeWireHeader) : List UInt8 :=
  encVarNat hdr.fromEpoch ++ encVarNat hdr.toEpoch ++
    encStrSpec hdr.preGateName ++ encStrSpec hdr.postGateName ++
    encVarNat hdr.lobLabelCount

def decUpgradeWireHeader (bs : List UInt8) : Option UpgradeWireHeader :=
  let fuel := bs.length + 1
  match decVarNat fuel bs with
  | none => none
  | some (e1, r1) =>
    match decVarNat fuel r1 with
    | none => none
    | some (e2, r2) =>
      match decStrSpec fuel r2 with
      | none => none
      | some (g1, r3) =>
        match decStrSpec fuel r3 with
        | none => none
        | some (g2, r4) =>
          match decVarNat fuel r4 with
          | some (lc, []) => some ⟨e1, e2, g1, g2, lc⟩
          | _ => none

theorem decUpgradeWireHeader_enc (hdr : UpgradeWireHeader) :
    decUpgradeWireHeader (encUpgradeWireHeader hdr) = some hdr := by
  rcases hdr with ⟨e1, e2, g1, g2, lc⟩
  have hshape : encUpgradeWireHeader ⟨e1, e2, g1, g2, lc⟩ =
      encVarNat e1 ++ (encVarNat e2 ++ (encStrSpec g1 ++ (encStrSpec g2 ++ encVarNat lc))) := by
    simp [encUpgradeWireHeader, List.append_assoc]
  have hlen : (encUpgradeWireHeader ⟨e1, e2, g1, g2, lc⟩).length =
      (encVarNat e1).length + ((encVarNat e2).length + ((encStrSpec g1).length +
        ((encStrSpec g2).length + (encVarNat lc).length))) := by
    rw [hshape]; simp
  unfold decUpgradeWireHeader
  dsimp only
  generalize hfuel : (encUpgradeWireHeader ⟨e1, e2, g1, g2, lc⟩).length + 1 = fuel
  rw [hshape]
  rw [decVarNat_encVarNat e1 fuel _ (by omega)]; dsimp only
  rw [decVarNat_encVarNat e2 fuel _ (by omega)]; dsimp only
  rw [decStrSpec_encStrSpec g1 fuel _ (by omega)]; dsimp only
  rw [decStrSpec_encStrSpec g2 fuel _ (by omega)]; dsimp only
  have hlc := decVarNat_encVarNat lc fuel [] (by omega)
  rw [List.append_nil] at hlc
  rw [hlc]

theorem encUpgradeWireHeader_injective {h₁ h₂ : UpgradeWireHeader}
    (heq : encUpgradeWireHeader h₁ = encUpgradeWireHeader h₂) : h₁ = h₂ := by
  have d := decUpgradeWireHeader_enc h₁
  rw [heq, decUpgradeWireHeader_enc h₂] at d
  exact Option.some.inj d.symm

/-- 256-bit `cSHAKE256` commitment to an `UpgradeWireHeader` (`BitVec 256`, zero narrow welds). -/
def envelopeHeaderDigest (hdr : UpgradeWireHeader) : Digest256 :=
  hashBytesToDigest256 upgradeEnvelopeHash (encUpgradeWireHeader hdr)

theorem envelopeHeaderDigest_binds_or_collides {h₁ h₂ : UpgradeWireHeader}
    (h : envelopeHeaderDigest h₁ = envelopeHeaderDigest h₂) :
    h₁ = h₂ ∨ CollisionAmong upgradeEnvelopeHash
      (fun pre => pre = encUpgradeWireHeader h₁ ∨ pre = encUpgradeWireHeader h₂) := by
  if hp : encUpgradeWireHeader h₁ = encUpgradeWireHeader h₂ then
    exact Or.inl (encUpgradeWireHeader_injective hp)
  else
    have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
    have ha : (upgradeEnvelopeHash (encUpgradeWireHeader h₁)).length = 32 := by
      simp [upgradeEnvelopeHash]
    have hb : (upgradeEnvelopeHash (encUpgradeWireHeader h₂)).length = 32 := by
      simp [upgradeEnvelopeHash]
    have lta : ofBE (upgradeEnvelopeHash (encUpgradeWireHeader h₁)) < 2 ^ 256 := by
      have := ofBE_lt (upgradeEnvelopeHash (encUpgradeWireHeader h₁)); rwa [ha, hpow] at this
    have ltb : ofBE (upgradeEnvelopeHash (encUpgradeWireHeader h₂)) < 2 ^ 256 := by
      have := ofBE_lt (upgradeEnvelopeHash (encUpgradeWireHeader h₂)); rwa [hb, hpow] at this
    have hh := congrArg BitVec.toNat h
    simp only [envelopeHeaderDigest, hashBytesToDigest256, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt lta, Nat.mod_eq_of_lt ltb] at hh
    exact Or.inr ⟨_, _, .inl rfl, .inr rfl, hp, hh⟩

/-- Cross-epoch **Proof-Carrying `UpgradeEnvelope`** bridging Habitat `H₁` (epoch `v₁`) to Habitat
    `H₂` (epoch `v₂`) via a `SymmetricEditLens` and `Obend.Judge.Genealogy` floor/Löb accounting. -/
structure UpgradeEnvelope (H₁ H₂ : Habitat) (C E₁ E₂ : Type) where
  fromEpoch : Nat
  toEpoch : Nat
  lens : SymmetricEditLens H₁.State H₂.State C E₁ E₂
  actToEdit₁ : H₁.Act → H₁.State → E₁
  actToEdit₁_eq : ∀ a₁ s₁, lens.mod₁.apply (actToEdit₁ a₁ s₁) s₁ = H₁.step a₁ s₁
  liftFloor : H₁.Floor → H₂.Floor
  liftFloor_iff : ∀ {φ₁ : H₁.Floor} {s₁ : H₁.State} {c : C} {s₂ : H₂.State},
    lens.Consistent s₁ c s₂ → (H₂.holds (liftFloor φ₁) s₂ ↔ H₁.holds φ₁ s₁)
  anchorGate : Gate H₁ → Gate H₂
  anchorGate_floors : ∀ (G₁ : Gate H₁) (φ₁ : H₁.Floor),
    φ₁ ∈ G₁.floors → liftFloor φ₁ ∈ (anchorGate G₁).floors
  anchorGate_basis : ∀ (G₁ : Gate H₁) (t : TrustBase),
    t ∈ (anchorGate G₁).basis → t ∈ G₁.basis
  nextGate : Gate H₂
  lobLabels : List TrustBase

/-- Executable gate check admitting an `UpgradeEnvelope` at transition state `s₂_mid` (kept as a
    top-level `def` for `#tooth`). -/
def admitUpgradeEnvelope {H₁ H₂ : Habitat} {C E₁ E₂ : Type}
    (env : UpgradeEnvelope H₁ H₂ C E₁ E₂) (G₁ : Gate H₁) (s₂_mid : H₂.State) : Bool :=
  decide (env.fromEpoch < env.toEpoch) &&
    match succeed (env.anchorGate G₁) s₂_mid env.nextGate env.lobLabels with
    | .ok () => true
    | .error _ => false

/-- Replay an epoch-`v₁` log segment under `(H₁, G₁)` (`admits X G₁`). -/
def replayEpochSegment {H : Habitat} (X : Exec) (G : Gate H) :
    H.State → List H.Act → H.State
  | s, [] => s
  | s, a :: rest =>
    replayEpochSegment X G (if admits X G s a then H.step a s else s) rest

theorem replayEpochSegment_preserves_floors {H : Habitat} (X : Exec) (G : Gate H)
    (hwf : wellFormed G = .ok ()) (hb : ∀ t ∈ G.basis, X.Holds t) :
    ∀ (seg : List H.Act) (s : H.State),
      (∀ φ ∈ G.floors, H.holds φ s) →
      ∀ φ ∈ G.floors, H.holds φ (replayEpochSegment X G s seg)
  | [], s, hs, φ, hφ => hs φ hφ
  | a :: rest, s, hs, φ, hφ => by
    unfold replayEpochSegment
    by_cases ha : admits X G s a = true
    · rw [ite_eq_left ha]
      refine replayEpochSegment_preserves_floors X G hwf hb rest (H.step a s) ?_ φ hφ
      intro ψ hψ
      exact wellFormed_sound X G hwf hb s a ha ψ hψ (hs ψ hψ)
    · rw [ite_eq_right ha]
      exact replayEpochSegment_preserves_floors X G hwf hb rest s hs φ hφ

/-- Relink a historical `v₁` log segment directly on `H₂.State × C` using `env.lens.putr`
    (replaying a `v₁` log under the `v₂` carrier without keeping a live `H₁` interpreter). -/
def relinkV1SegmentOnV2 {H₁ H₂ : Habitat} {C E₁ E₂ : Type}
    (X : Exec) (G₁ : Gate H₁) (env : UpgradeEnvelope H₁ H₂ C E₁ E₂) :
    H₁.State → (H₂.State × C) → List H₁.Act → H₁.State × (H₂.State × C)
  | s₁, sc₂, [] => (s₁, sc₂)
  | s₁, (s₂, c), a₁ :: rest =>
    if admits X G₁ s₁ a₁ then
      relinkV1SegmentOnV2 X G₁ env
        (env.lens.mod₁.apply (env.actToEdit₁ a₁ s₁) s₁)
        (env.lens.mod₂.apply (env.lens.putr (env.actToEdit₁ a₁ s₁) c).1 s₂,
         (env.lens.putr (env.actToEdit₁ a₁ s₁) c).2)
        rest
    else
      relinkV1SegmentOnV2 X G₁ env s₁ (s₂, c) rest

/-- Full epoch-segmented replay: `(seg₁ at v₁) ++ UpgradeTurn(env) ++ (seg₂ at v₂)`. -/
def replaySegmentedUpgradeLog {H₁ H₂ : Habitat} {C E₁ E₂ : Type}
    (X : Exec) (G₁ : Gate H₁) (s₁_0 : H₁.State)
    (seg₁ : List H₁.Act) (env : UpgradeEnvelope H₁ H₂ C E₁ E₂) (seg₂ : List H₂.Act) :
    Option (H₂.State × C) :=
  let s₁_mid := replayEpochSegment X G₁ s₁_0 seg₁
  let (s₂_mid, c_mid) := env.lens.initRight s₁_mid
  if admitUpgradeEnvelope env G₁ s₂_mid then
    let s₂_fin := replayEpochSegment X env.nextGate s₂_mid seg₂
    some (s₂_fin, c_mid)
  else
    none

theorem relinkV1SegmentOnV2_consistent {H₁ H₂ : Habitat} {C E₁ E₂ : Type}
    (X : Exec) (G₁ : Gate H₁) (env : UpgradeEnvelope H₁ H₂ C E₁ E₂) :
    ∀ (seg₁ : List H₁.Act) (s₁ : H₁.State) (s₂ : H₂.State) (c : C),
      env.lens.Consistent s₁ c s₂ →
      let res := relinkV1SegmentOnV2 X G₁ env s₁ (s₂, c) seg₁
      res.1 = replayEpochSegment X G₁ s₁ seg₁ ∧
        env.lens.Consistent res.1 res.2.2 res.2.1
  | [], s₁, s₂, c, hc => ⟨rfl, hc⟩
  | a₁ :: rest, s₁, s₂, c, hc => by
    unfold relinkV1SegmentOnV2 replayEpochSegment
    by_cases ha : admits X G₁ s₁ a₁ = true
    · rw [ite_eq_left ha, ite_eq_left ha]
      have hstep := env.actToEdit₁_eq a₁ s₁
      have hc' := env.lens.putr_sound (env.actToEdit₁ a₁ s₁) hc
      obtain ⟨h1, h2⟩ := relinkV1SegmentOnV2_consistent X G₁ env rest _ _ _ hc'
      exact ⟨h1.trans (by rw [hstep]), h2⟩
    · rw [ite_eq_right ha, ite_eq_right ha]
      exact relinkV1SegmentOnV2_consistent X G₁ env rest s₁ s₂ c hc

/-- **Migration-Time Log Relinking & `Genealogy` Floor Soundness (`relinkLogAcrossEpochs_sound`).**
    Whenever `replaySegmentedUpgradeLog` admits `(seg₁, env, seg₂)` from a well-formed genesis
    `(G₁, s₁_0)` and `LobCost X env.lobLabels` holds:
    1. `env.nextGate` satisfies `Genealogy.Succeeds` over `env.anchorGate G₁` at the migration cut;
    2. Relinking `seg₁` step-by-step via `env.lens.putr` remains `Consistent` with `replayEpochSegment`;
    3. **Every** genesis floor `φ₁ ∈ G₁.floors` (transported as `env.liftFloor φ₁ ∈ env.nextGate.floors`)
       holds at the final upgraded state `s₂_fin`;
    4. Operator `H₂.revert` corrigibility remains unconditionally admitted in every `H₂.State`. -/
theorem relinkLogAcrossEpochs_sound {H₁ H₂ : Habitat} {C E₁ E₂ : Type}
    (X : Exec) (G₁ : Gate H₁) (s₁_0 : H₁.State)
    (seg₁ : List H₁.Act) (env : UpgradeEnvelope H₁ H₂ C E₁ E₂) (seg₂ : List H₂.Act)
    {s₂_fin : H₂.State} {c_mid : C}
    (hGenWf : wellFormed G₁ = .ok ())
    (hTrusted : ∀ t ∈ G₁.basis, X.Holds t)
    (hInitFloors : ∀ φ₁ ∈ G₁.floors, H₁.holds φ₁ s₁_0)
    (hLob : LobCost X env.lobLabels)
    (hReplay : replaySegmentedUpgradeLog X G₁ s₁_0 seg₁ env seg₂ = some (s₂_fin, c_mid)) :
    let s₁_mid := replayEpochSegment X G₁ s₁_0 seg₁
    let s₂_mid := (env.lens.initRight s₁_mid).1
    env.fromEpoch < env.toEpoch ∧
    (∀ φ₁ ∈ G₁.floors, H₁.holds φ₁ s₁_mid) ∧
    Succeeds (env.anchorGate G₁) s₂_mid env.nextGate env.lobLabels ∧
    (∀ φ₁ ∈ G₁.floors,
      env.liftFloor φ₁ ∈ env.nextGate.floors ∧ H₂.holds (env.liftFloor φ₁) s₂_fin) ∧
    (∀ s₂' : H₂.State, admits X env.nextGate s₂' H₂.revert = true) ∧
    (let relinked := relinkV1SegmentOnV2 X G₁ env s₁_0
        ((env.lens.initRight s₁_0).1, (env.lens.initRight s₁_0).2) seg₁;
     relinked.1 = s₁_mid ∧ env.lens.Consistent relinked.1 relinked.2.2 relinked.2.1) := by
  have hFloorsMid0 :=
    replayEpochSegment_preserves_floors X G₁ hGenWf hTrusted seg₁ s₁_0 hInitFloors
  unfold replaySegmentedUpgradeLog at hReplay
  generalize hs₁ : replayEpochSegment X G₁ s₁_0 seg₁ = s₁_mid at hReplay hFloorsMid0
  let s₂_mid := (env.lens.initRight s₁_mid).1
  change (if admitUpgradeEnvelope env G₁ s₂_mid = true then
      some (replayEpochSegment X env.nextGate s₂_mid seg₂, (env.lens.initRight s₁_mid).2)
    else none) = some (s₂_fin, c_mid) at hReplay
  by_cases hv : admitUpgradeEnvelope env G₁ s₂_mid = true
  · rw [ite_eq_left hv, Option.some.injEq, Prod.mk.injEq] at hReplay
    obtain ⟨rfl, rfl⟩ := hReplay
    unfold admitUpgradeEnvelope at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hEpochLt, hSuccMatch⟩ := hv
    cases hSucc : succeed (env.anchorGate G₁) s₂_mid env.nextGate env.lobLabels with
    | error _ => simp [hSucc] at hSuccMatch
    | ok u =>
      have hSucceeds := succession_sound_meaning hSucc
      obtain ⟨_, hWfNext, hHoldsMid, hLabelled, _⟩ :=
        Obend.Judge.Genealogy.succeed_parts hSucc
      have hAnchorTrusted : ∀ t ∈ (env.anchorGate G₁).basis, X.Holds t :=
        fun t ht => hTrusted t (env.anchorGate_basis G₁ t ht)
      have hNextTrusted : ∀ t ∈ env.nextGate.basis, X.Holds t := by
        intro t ht
        rcases hLabelled t ht with hA | hL
        · exact hAnchorTrusted t hA
        · exact hLob t hL
      have hFloorsFin :=
        replayEpochSegment_preserves_floors X env.nextGate hWfNext hNextTrusted seg₂ s₂_mid hHoldsMid
      have hRelink := relinkV1SegmentOnV2_consistent X G₁ env seg₁ s₁_0
        (env.lens.initRight s₁_0).1 (env.lens.initRight s₁_0).2
        (env.lens.initRight_consistent s₁_0)
      refine ⟨hEpochLt, hFloorsMid0, hSucceeds, ?_,
        fun s₂' => revert_admitted X env.nextGate hWfNext s₂', ?_⟩
      · intro φ₁ hφ₁
        have hInNext : env.liftFloor φ₁ ∈ env.nextGate.floors :=
          hSucceeds.keeps _ (env.anchorGate_floors G₁ φ₁ hφ₁)
        exact ⟨hInNext, hFloorsFin _ hInNext⟩
      · rw [hs₁] at hRelink
        exact hRelink
  · rw [ite_eq_right hv] at hReplay; cases hReplay

/-- Unbounded multi-epoch trace over a habitat `H`: interleaves arbitrarily many actions and
    epoch-bumping judge/step upgrades while accumulating spent `LobCost` labels. -/
inductive EpochSysTurn (H : Habitat) where
  | act (a : H.Act)
  | upgrade (nextEpoch : Nat) (nextGate : Gate H) (lobLabels : List TrustBase)

structure EpochSysState (H : Habitat) where
  epoch : Nat
  gate : Gate H
  state : H.State
  spentLabels : List TrustBase

def stepEpochSys {H : Habitat} (X : Exec) (st : EpochSysState H)
    (t : EpochSysTurn H) : EpochSysState H :=
  match t with
  | .act a =>
    if admits X st.gate st.state a then { st with state := H.step a st.state } else st
  | .upgrade nextEp G' L =>
    if decide (st.epoch < nextEp) then
      match succeed st.gate st.state G' L with
      | .ok () =>
        { epoch := nextEp, gate := G', state := st.state, spentLabels := st.spentLabels ++ L }
      | .error _ => st
    else st

def runMultiEpochTrace {H : Habitat} (X : Exec) :
    EpochSysState H → List (EpochSysTurn H) → EpochSysState H
  | st, [] => st
  | st, t :: rest => runMultiEpochTrace X (stepEpochSys X st t) rest

private theorem stepEpochSys_spent_subset {H : Habitat} (X : Exec) (st : EpochSysState H)
    (turn : EpochSysTurn H) :
    ∀ lbl ∈ st.spentLabels, lbl ∈ (stepEpochSys X st turn).spentLabels := by
  intro lbl hlbl
  cases turn with
  | act a =>
    by_cases ha : admits X st.gate st.state a = true <;> simp [stepEpochSys, ha, hlbl]
  | upgrade nextEp G' L =>
    by_cases hep : decide (st.epoch < nextEp) = true
    · cases hs : succeed st.gate st.state G' L <;> simp [stepEpochSys, hep, hs, hlbl]
    · simp [stepEpochSys, hep, hlbl]

private theorem runMultiEpochTrace_spent_subset {H : Habitat} (X : Exec) :
    ∀ (turns : List (EpochSysTurn H)) (st : EpochSysState H),
      ∀ lbl ∈ st.spentLabels, lbl ∈ (runMultiEpochTrace X st turns).spentLabels
  | [], _, _, h => h
  | t :: rest, st, lbl, h =>
    runMultiEpochTrace_spent_subset X rest (stepEpochSys X st t) lbl
      (stepEpochSys_spent_subset X st t lbl h)

/-- **Unbounded Multi-Epoch Trace Safety & Monotonicity (`runMultiEpochTrace_floors`).**
    Starting at any `initEpoch`, across any finite trace of interleaved actions and epoch upgrades:
    `epoch` advances monotonically (`initEpoch ≤ fin.epoch`), `revert` stays admitted, and all
    genesis floors hold under `LobCost X fin.spentLabels`. -/
theorem runMultiEpochTrace_floors {H : Habitat} (X : Exec) (initEpoch : Nat)
    (G₀ : Gate H) (s₀ : H.State)
    (hWf₀ : wellFormed G₀ = .ok ())
    (hTrust₀ : ∀ t ∈ G₀.basis, X.Holds t)
    (hFloors₀ : ∀ φ ∈ G₀.floors, H.holds φ s₀)
    (turns : List (EpochSysTurn H))
    (hLob : LobCost X (runMultiEpochTrace X ⟨initEpoch, G₀, s₀, []⟩ turns).spentLabels) :
    let fin := runMultiEpochTrace X ⟨initEpoch, G₀, s₀, []⟩ turns
    initEpoch ≤ fin.epoch ∧
    wellFormed fin.gate = .ok () ∧
    (∀ φ ∈ G₀.floors, φ ∈ fin.gate.floors ∧ H.holds φ fin.state) ∧
    (∀ s' : H.State, admits X fin.gate s' H.revert = true) := by
  suffices hInv : ∀ (turns : List (EpochSysTurn H)) (st : EpochSysState H),
      wellFormed st.gate = .ok () →
      (∀ φ ∈ G₀.floors, φ ∈ st.gate.floors) →
      (∀ φ ∈ st.gate.floors, H.holds φ st.state) →
      (∀ t ∈ st.gate.basis, t ∈ G₀.basis ∨ t ∈ st.spentLabels) →
      LobCost X (runMultiEpochTrace X st turns).spentLabels →
      let fin := runMultiEpochTrace X st turns
      st.epoch ≤ fin.epoch ∧
      wellFormed fin.gate = .ok () ∧
      (∀ φ ∈ G₀.floors, φ ∈ fin.gate.floors) ∧
      (∀ φ ∈ fin.gate.floors, H.holds φ fin.state) by
    obtain ⟨hep, hwf, hk, hh⟩ := hInv turns ⟨initEpoch, G₀, s₀, []⟩ hWf₀ (fun _ h => h) hFloors₀
      (fun t ht => .inl ht) hLob
    exact ⟨hep, hwf, fun φ hφ => ⟨hk φ hφ, hh φ (hk φ hφ)⟩,
      fun s' => revert_admitted X _ hwf s'⟩
  intro ts
  induction ts with
  | nil =>
    intro st hwf hk hh _ _
    exact ⟨Nat.le_refl _, hwf, hk, hh⟩
  | cons turn rest ih =>
    intro st hwf hk hh hb hlobAll
    have hBasisHolds : ∀ t ∈ st.gate.basis, X.Holds t := by
      intro t ht
      rcases hb t ht with h0 | hsp
      · exact hTrust₀ t h0
      · exact hlobAll t (runMultiEpochTrace_spent_subset X (turn :: rest) st t hsp)
    cases turn with
    | act a =>
      dsimp only [runMultiEpochTrace, stepEpochSys] at hlobAll ⊢
      by_cases ha : admits X st.gate st.state a = true
      · rw [ite_eq_left ha] at hlobAll ⊢
        refine ih { st with state := H.step a st.state } hwf hk ?_ hb hlobAll
        intro φ hφ
        exact wellFormed_sound X st.gate hwf hBasisHolds st.state a ha φ hφ (hh φ hφ)
      · rw [ite_eq_right ha] at hlobAll ⊢
        exact ih st hwf hk hh hb hlobAll
    | upgrade nextEp G' L =>
      dsimp only [runMultiEpochTrace, stepEpochSys] at hlobAll ⊢
      by_cases hep : decide (st.epoch < nextEp) = true
      · rw [ite_eq_left hep] at hlobAll ⊢
        have hlt : st.epoch < nextEp := of_decide_eq_true hep
        cases hs : succeed st.gate st.state G' L with
        | error _ =>
          simp only [hs] at hlobAll ⊢
          exact ih st hwf hk hh hb hlobAll
        | ok _ =>
          simp only [hs] at hlobAll ⊢
          obtain ⟨hn, hwf', hh', hl, _⟩ := Obend.Judge.Genealogy.succeed_parts hs
          obtain ⟨hepRest, hwfFin, hkFin, hhFin⟩ :=
            ih { epoch := nextEp, gate := G', state := st.state, spentLabels := st.spentLabels ++ L }
              hwf'
              (fun φ hφ => Obend.Judge.Genealogy.nonRegression_keeps hn φ (hk φ hφ))
              hh' (by
                intro t ht
                rcases hl t ht with hprev | hnew
                · rcases hb t hprev with h0 | hsp
                  · exact .inl h0
                  · exact .inr (List.mem_append_left _ hsp)
                · exact .inr (List.mem_append_right _ hnew)) hlobAll
          exact ⟨by dsimp only at hepRest; omega, hwfFin, hkFin, hhFin⟩
      · rw [ite_eq_right hep] at hlobAll ⊢
        exact ih st hwf hk hh hb hlobAll

end EpochLogRelinking

/-! ## 4. Lifting Suspended `Core.Machine` `.yielded` Continuations Across Heap/Env Upgrades -/

/-- Relocate a `Core.Machine.Control` by shifting every heap address upward by `offset` (kept as a
    top-level `def` so `#tooth` can mutate it). -/
def liftContinuationControl (offset : Nat) (ctrl : Control) : Control :=
  renameControl (offset + ·) ctrl

/-- Lift any `Core.Machine.State` across an in-flight module/environment upgrade that prepends
    `prefixCells` (e.g., newly linked `v₂` prototype/method cells) ahead of the continuation's
    existing heap, relocating all heap, control, and continuation stack addresses by
    `prefixCells.size`. -/
def liftContinuationState (prefixCells : Array Cell) (s : State) : State :=
  let off := prefixCells.size
  { heap := prefixCells ++ s.heap.map (renameCell (off + ·))
    control := liftContinuationControl off s.control
    stack := s.stack.map (renameFrame (off + ·)) }

def liftContinuationOutcome (prefixCells : Array Cell) : Outcome → Outcome
  | .finished val st =>
    .finished (renameValue (prefixCells.size + ·) val) (liftContinuationState prefixCells st)
  | .suspended rsn st =>
    .suspended rsn (liftContinuationState prefixCells st)
  | .divergent addr st =>
    .divergent (prefixCells.size + addr) (liftContinuationState prefixCells st)
  | .refused rsn st =>
    .refused rsn (liftContinuationState prefixCells st)
  | .yielded plan st =>
    .yielded (prefixCells.size + plan) (liftContinuationState prefixCells st)

private theorem getElem?_append_shift {α : Type} (pre post : Array α) (a : Nat) :
    (pre ++ post)[pre.size + a]? = post[a]? := by
  by_cases ha : a < post.size
  · have hlt : pre.size + a < (pre ++ post).size := by simp; omega
    rw [getElem?_pos (pre ++ post) (pre.size + a) hlt, getElem?_pos post a ha,
      Array.getElem_append_right (Nat.le_add_right _ _)]
    simp
  · have hge : ¬ (pre.size + a < (pre ++ post).size) := by simp; omega
    rw [getElem?_neg (pre ++ post) (pre.size + a) hge, getElem?_neg post a ha]

private theorem set!_append_map_shift (pre : Array Cell) (h : Array Cell)
    (a : Nat) (c : Cell) :
    (pre ++ h.map (renameCell (pre.size + ·))).set! (pre.size + a)
      (renameCell (pre.size + ·) c) =
    pre ++ (h.set! a c).map (renameCell (pre.size + ·)) := by
  simp only [Array.set!, Array.setIfInBounds]
  by_cases ha : a < h.size
  · have hpa : pre.size + a < (pre ++ h.map (renameCell (pre.size + ·))).size := by simp; omega
    rw [dite_eq_left hpa, dite_eq_left ha]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      by_cases hp : i < pre.size
      · have hne : ¬ (pre.size + a = i) := by omega
        simp only [Array.getElem_set, hne, ↓reduceIte, Array.getElem_append_left hp]
      · have hge : pre.size ≤ i := by omega
        by_cases heq : pre.size + a = i
        · subst heq
          rw [Array.getElem_set_self, Array.getElem_append_right hge]
          simp
        · have hne : ¬ (a = i - pre.size) := by omega
          simp only [Array.getElem_set, heq, ↓reduceIte, Array.getElem_append_right hge,
            Array.getElem_map, hne]
  · have hpa : ¬ (pre.size + a < (pre ++ h.map (renameCell (pre.size + ·))).size) := by
      simp; omega
    rw [dite_eq_right hpa, dite_eq_right ha]

private theorem push_append_map_shift (pre : Array Cell) (h : Array Cell) (c : Cell) :
    (pre ++ h.map (renameCell (pre.size + ·))).push (renameCell (pre.size + ·) c) =
    pre ++ (h.push c).map (renameCell (pre.size + ·)) := by
  apply Array.toList_inj.1
  simp

private theorem allocateFields_lift (pre : Array Cell) (h : Array Cell)
    (env : Environment) (fs : List (String × Term)) :
    allocateFields (pre ++ h.map (renameCell (pre.size + ·))) (env.map (pre.size + ·)) fs =
      (pre ++ (allocateFields h env fs).1.map (renameCell (pre.size + ·)),
       (allocateFields h env fs).2.map (fun p => (p.1, pre.size + p.2))) := by
  unfold allocateFields
  suffices hFold : ∀ (fs : List (String × Term)) (curH : Array Cell) (acc : List (String × Address)),
      fs.foldl (fun (prior : Array Cell × List (String × Address)) field =>
        (prior.1.push (.suspended ⟨field.2, env.map (pre.size + ·)⟩),
         (field.1, prior.1.size) :: prior.2))
        (pre ++ curH.map (renameCell (pre.size + ·)),
         acc.map (fun p => (p.1, pre.size + p.2))) =
      let r := fs.foldl (fun (prior : Array Cell × List (String × Address)) field =>
        (prior.1.push (.suspended ⟨field.2, env⟩), (field.1, prior.1.size) :: prior.2)) (curH, acc)
      (pre ++ r.1.map (renameCell (pre.size + ·)),
       r.2.map (fun p => (p.1, pre.size + p.2))) by
    have h0 := hFold fs h []
    simp only [List.map_nil] at h0
    rw [h0, List.map_reverse]
  intro fs
  induction fs with
  | nil => intro curH acc; rfl
  | cons field rest ih =>
    intro curH acc
    simp only [List.foldl_cons]
    have hp := push_append_map_shift pre curH (.suspended ⟨field.2, env⟩)
    simp only [renameCell, renameClosure] at hp
    have hsz : (pre ++ curH.map (renameCell (pre.size + ·))).size = pre.size + curH.size := by simp
    rw [hp, hsz]
    exact ih (curH.push (.suspended ⟨field.2, env⟩)) ((field.1, curH.size) :: acc)

private theorem forcingShared_map_rename (f : Nat → Nat) (stk : List Frame) :
    forcingShared (stk.map (renameFrame f)) = forcingShared stk := by
  unfold forcingShared
  rw [List.any_map]
  congr 1
  funext fr
  cases fr <;> rfl

private theorem valueTerm_renameValue (f : Nat → Nat) (v : RuntimeValue) :
    valueTerm (renameValue f v) = valueTerm v := by
  cases v <;> rfl

private theorem renameValue_of_scalarValue (f : Nat → Nat) {res : Term} {v : RuntimeValue}
    (h : scalarValue res = some v) : renameValue f v = v := by
  cases res <;> simp [scalarValue] at h <;> subst h <;> rfl

private theorem find?_named_map (f : Nat → Nat) (name : String) :
    ∀ (fs : List (String × Address)),
      (fs.map (fun p => (p.1, f p.2))).find? (fun field => field.1 == name) =
        (fs.find? (fun field => field.1 == name)).map (fun p => (p.1, f p.2))
  | [] => rfl
  | (k, v) :: rest => by
    simp only [List.map_cons, List.find?_cons]
    cases (k == name)
    · exact find?_named_map f name rest
    · rfl

private theorem filter_named_map (f : Nat → Nat) (pred : String → Bool) :
    ∀ (fs : List (String × Address)),
      (fs.map (fun p => (p.1, f p.2))).filter (fun prior => pred prior.1) =
        (fs.filter (fun prior => pred prior.1)).map (fun p => (p.1, f p.2))
  | [] => rfl
  | (k, v) :: rest => by
    simp only [List.map_cons, List.filter_cons]
    cases pred k <;> simp [filter_named_map f pred rest]

private theorem splitFrames_map_shift (off : Nat) (addrs : List Address) :
    splitFrames (addrs.map (off + ·)) = (splitFrames addrs).map (renameFrame (off + ·)) := by
  simp [splitFrames, renameFrame]

/-- **Exact Single-Step Commutation (`stepRaw_liftContinuationState`).**
    For **every** `Core.Machine.State` (all 25 `Term` constructors, 13 `Frame` constructors, and
    7 `Control` states, with zero validity side conditions), `stepRaw` commutes identically with
    `liftContinuationState prefixCells`. -/
theorem stepRaw_liftContinuationState (prefixCells : Array Cell) (s : State) :
    stepRaw (liftContinuationState prefixCells s) =
      liftContinuationState prefixCells (stepRaw s) := by
  rcases s with ⟨heap, ctrl, stack⟩
  cases ctrl with
  | complete _ | refused _ | blackhole _ | yielded _ =>
    simp [liftContinuationState, liftContinuationControl, renameControl, stepRaw]
  | enter addr =>
    simp only [liftContinuationState, liftContinuationControl, renameControl, stepRaw,
      getElem?_append_shift, Array.getElem?_map]
    cases hcell : heap[addr]? with
    | none => simp
    | some cell =>
      cases cell with
      | evaluating orig => simp [renameCell]
      | cached orig val => simp [renameCell]
      | suspended orig =>
        have hs := set!_append_map_shift prefixCells heap addr (.evaluating orig)
        simp only [renameCell, renameClosure] at hs
        simp only [Option.map_some, renameCell, renameClosure, List.map_cons, renameFrame, hs]
  | evaluate t env =>
    cases t with
    | hole _ _ => simp [liftContinuationState, liftContinuationControl, renameControl, stepRaw]
    | bound idx =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, stepRaw,
        List.getElem?_map]
      cases env[idx]? <;> simp
    | lam _ | nat _ | boolean _ | label _ | done _ =>
      simp [liftContinuationState, liftContinuationControl, renameControl, renameValue, stepRaw]
    | app _ _ | mix _ _ | reflect _ | metadata _ | project _ | get _ _ | extend _ _
    | ifZero _ _ _ | binary _ _ _ | case _ _ | ifBool _ _ _ | split _ _ _ =>
      simp [liftContinuationState, liftContinuationControl, renameControl, renameFrame, stepRaw]
    | fix sp inh =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, stepRaw]
      have hp := push_append_map_shift prefixCells heap
        (.suspended ⟨Term.app (Term.app (sp.rename Nat.succ) (.bound 0)) (inh.rename Nat.succ),
          heap.size :: env⟩)
      simp only [renameCell, renameClosure, List.map_cons] at hp
      have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
          prefixCells.size + heap.size := by simp
      rw [hsz, hp]
    | specification m e =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue, stepRaw]
      have hp1 := push_append_map_shift prefixCells heap (.suspended ⟨m, env⟩)
      have hp2 := push_append_map_shift prefixCells (heap.push (.suspended ⟨m, env⟩))
        (.suspended ⟨e, env⟩)
      simp only [renameCell, renameClosure] at hp1 hp2
      have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
          prefixCells.size + heap.size := by simp
      rw [hsz, hp1, hp2, Nat.add_assoc]
    | prototype sp tgt =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue, stepRaw]
      have hp1 := push_append_map_shift prefixCells heap (.suspended ⟨sp, env⟩)
      have hp2 := push_append_map_shift prefixCells (heap.push (.suspended ⟨sp, env⟩))
        (.suspended ⟨tgt, env⟩)
      simp only [renameCell, renameClosure] at hp1 hp2
      have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
          prefixCells.size + heap.size := by simp
      rw [hsz, hp1, hp2, Nat.add_assoc]
    | record fs =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue, stepRaw]
      rw [allocateFields_lift]
    | inject tag pay =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue, stepRaw]
      have hp := push_append_map_shift prefixCells heap (.suspended ⟨pay, env⟩)
      simp only [renameCell, renameClosure] at hp
      have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
          prefixCells.size + heap.size := by simp
      rw [hsz, hp]
    | perform plan =>
      simp only [liftContinuationState, liftContinuationControl, renameControl, stepRaw,
        forcingShared_map_rename]
      by_cases hf : forcingShared stack = true
      · simp [hf]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        have hp := push_append_map_shift prefixCells heap (.suspended ⟨plan, env⟩)
        simp only [renameCell, renameClosure] at hp
        have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
            prefixCells.size + heap.size := by simp
        rw [hsz, hp]
  | returned val =>
    cases stack with
    | nil =>
      simp [liftContinuationState, liftContinuationControl, renameControl, stepRaw]
    | cons fr rest =>
      cases fr with
      | update addr =>
        simp only [liftContinuationState, liftContinuationControl, renameControl, List.map_cons,
          renameFrame, stepRaw, getElem?_append_shift, Array.getElem?_map]
        cases hcell : heap[addr]? with
        | none => simp
        | some cell =>
          cases cell with
          | suspended _ | cached _ _ =>
            simp [renameCell]
          | evaluating orig =>
            have hs := set!_append_map_shift prefixCells heap addr (.cached orig val)
            simp only [renameCell, renameClosure] at hs
            simp only [Option.map_some, renameCell, renameClosure, hs]
      | reflect | metadata | project =>
        cases val <;> simp [liftContinuationState, liftContinuationControl, renameControl,
          renameValue, renameFrame, stepRaw]
      | argument arg env =>
        cases val with
        | specification m e =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
        | closure body cap =>
          simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            List.map_cons, renameFrame, stepRaw]
          have hp := push_append_map_shift prefixCells heap (.suspended ⟨arg, env⟩)
          simp only [renameCell, renameClosure] at hp
          have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
              prefixCells.size + heap.size := by simp
          rw [hsz, hp]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | field name =>
        cases val with
        | record fs =>
          simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            List.map_cons, renameFrame, stepRaw, find?_named_map]
          cases fs.find? (fun field => field.1 == name) <;> simp
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | extend fs env =>
        cases val with
        | record inh =>
          have hf := filter_named_map (prefixCells.size + ·)
            (fun name => !fs.any fun field => field.1 == name) inh
          simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            List.map_cons, renameFrame, stepRaw, allocateFields_lift, List.map_append]
          rw [hf]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | condition z s env =>
        cases val with
        | natural n =>
          cases n with
          | zero =>
            simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
              renameFrame, stepRaw]
          | succ m =>
            simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
              List.map_cons, renameFrame, stepRaw]
            have hp := push_append_map_shift prefixCells heap (.cached ⟨.nat m, []⟩ (.natural m))
            simp only [renameCell, renameClosure, List.map_nil, renameValue] at hp
            have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
                prefixCells.size + heap.size := by simp
            rw [hsz, hp]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | binaryLeft p r env =>
        simp [liftContinuationState, liftContinuationControl, renameControl, renameFrame, stepRaw]
      | binaryRight p l =>
        simp only [liftContinuationState, liftContinuationControl, renameControl, List.map_cons,
          renameFrame, stepRaw, valueTerm_renameValue]
        cases (valueTerm l).bind (fun lt => (valueTerm val).bind (primitiveResult p lt)) with
        | none => simp
        | some res =>
          cases hs : scalarValue res with
          | none => simp [hs]
          | some sv => simp [hs, renameValue_of_scalarValue (prefixCells.size + ·) hs]
      | case arms env =>
        cases val with
        | variant tag pay =>
          simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            List.map_cons, renameFrame, stepRaw]
          cases arms.find? (fun arm => arm.1 == tag) with
          | none => simp
          | some p =>
            obtain ⟨_, body⟩ := p
            simp only [List.map_cons]
            have hp := push_append_map_shift prefixCells heap (.suspended ⟨.bound 0, [pay]⟩)
            simp only [renameCell, renameClosure, List.map_cons, List.map_nil] at hp
            have hsz : (prefixCells ++ heap.map (renameCell (prefixCells.size + ·))).size =
                prefixCells.size + heap.size := by simp
            rw [hsz, hp]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | ifBool wt wf env =>
        cases val with
        | boolean b =>
          cases b <;> simp [liftContinuationState, liftContinuationControl, renameControl,
            renameValue, renameFrame, stepRaw]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]
      | split names fn env =>
        cases val with
        | record fs =>
          simp only [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            List.map_cons, renameFrame, stepRaw, splitValues_map]
          cases splitValues fs names with
          | none => simp
          | some addrs =>
            simp only [Option.map_some, List.length_map, allocateFields_lift, List.map_append]
            have hmap : ((allocateFields heap addrs (splitCells addrs.length)).2.map
                (fun p => (p.1, prefixCells.size + p.2))).map Prod.snd =
              ((allocateFields heap addrs (splitCells addrs.length)).2.map Prod.snd).map
                (prefixCells.size + ·) := by
              rw [List.map_map, List.map_map]; rfl
            rw [hmap, splitFrames_map_shift]
        | _ =>
          simp [liftContinuationState, liftContinuationControl, renameControl, renameValue,
            renameFrame, stepRaw]

/-- Upgrade a persisted `ByteArray` heap image in place by decoding, prepending `prefixCells`, and
    re-encoding to canonical `ByteArray`. -/
def upgradePersistedHeapImage (prefixCells : Array Cell) (imgBytes : ByteArray) :
    Option ByteArray :=
  (decodeHeapImage imgBytes).map fun s => encodeHeapImage (liftContinuationState prefixCells s)

theorem step_liftContinuationState (prefixCells : Array Cell) (limits : Limits) (s : State) :
    step ⟨limits.heap + prefixCells.size, limits.stack⟩ (liftContinuationState prefixCells s) =
      liftContinuationOutcome prefixCells (step limits s) := by
  unfold step
  cases hc : s.control with
  | complete val =>
    simp [liftContinuationState, hc, liftContinuationControl, renameControl,
      liftContinuationOutcome]
  | blackhole addr =>
    simp [liftContinuationState, hc, liftContinuationControl, renameControl,
      liftContinuationOutcome]
  | refused rsn =>
    simp [liftContinuationState, hc, liftContinuationControl, renameControl,
      liftContinuationOutcome]
  | yielded plan =>
    simp [liftContinuationState, hc, liftContinuationControl, renameControl,
      liftContinuationOutcome]
  | evaluate t env | enter t | returned t =>
    have hraw := stepRaw_liftContinuationState prefixCells s
    have hctrl : (liftContinuationState prefixCells s).control =
        liftContinuationControl prefixCells.size s.control := rfl
    rw [hctrl, hc]
    dsimp only [liftContinuationControl, renameControl]
    rw [hraw]
    have hsz : (liftContinuationState prefixCells (stepRaw s)).heap.size =
        prefixCells.size + (stepRaw s).heap.size := by simp [liftContinuationState]
    have hstk : (liftContinuationState prefixCells (stepRaw s)).stack.length =
        (stepRaw s).stack.length := by simp [liftContinuationState]
    have hcond : (decide ((liftContinuationState prefixCells (stepRaw s)).heap.size ≤
          limits.heap + prefixCells.size) &&
        decide ((liftContinuationState prefixCells (stepRaw s)).stack.length ≤ limits.stack)) =
        (decide ((stepRaw s).heap.size ≤ limits.heap) &&
        decide ((stepRaw s).stack.length ≤ limits.stack)) := by
      rw [hsz, hstk]
      by_cases hh : (stepRaw s).heap.size ≤ limits.heap
      · have hh' : prefixCells.size + (stepRaw s).heap.size ≤ limits.heap + prefixCells.size := by
          omega
        simp [hh, hh']
      · have hh' : ¬ (prefixCells.size + (stepRaw s).heap.size ≤ limits.heap + prefixCells.size) := by
          omega
        simp [hh, hh']
    by_cases hcnd : (decide ((stepRaw s).heap.size ≤ limits.heap) &&
        decide ((stepRaw s).stack.length ≤ limits.stack)) = true
    · have hcnd' : (decide ((liftContinuationState prefixCells (stepRaw s)).heap.size ≤
          limits.heap + prefixCells.size) &&
          decide ((liftContinuationState prefixCells (stepRaw s)).stack.length ≤ limits.stack)) =
          true := hcond.trans hcnd
      simp only [hcnd, hcnd', ↓reduceIte, liftContinuationOutcome]
    · have hcnd' : (decide ((liftContinuationState prefixCells (stepRaw s)).heap.size ≤
          limits.heap + prefixCells.size) &&
          decide ((liftContinuationState prefixCells (stepRaw s)).stack.length ≤ limits.stack)) =
          false := by
        rw [hcond]; exact Bool.not_eq_true _ ▸ hcnd
      have hcndF : (decide ((stepRaw s).heap.size ≤ limits.heap) &&
          decide ((stepRaw s).stack.length ≤ limits.stack)) = false :=
        Bool.not_eq_true _ ▸ hcnd
      simp only [hcndF, hcnd', Bool.false_eq_true, ↓reduceIte, liftContinuationOutcome]

theorem runBounded_liftContinuationState (prefixCells : Array Cell) (limits : Limits) :
    ∀ (ticks : Nat) (s : State),
      runBounded ⟨limits.heap + prefixCells.size, limits.stack⟩ ticks
        (liftContinuationState prefixCells s) =
      liftContinuationOutcome prefixCells (runBounded limits ticks s)
  | 0, s => by
    unfold runBounded
    cases hc : s.control <;>
      simp [liftContinuationState, hc, liftContinuationControl, renameControl,
        liftContinuationOutcome]
  | ticks + 1, s => by
    unfold runBounded
    rw [step_liftContinuationState]
    cases hs : step limits s with
    | finished _ _ | divergent _ _ | refused _ _ | yielded _ _ =>
      rfl
    | suspended rsn next =>
      cases rsn with
      | capacity => rfl
      | ticks =>
        dsimp only [liftContinuationOutcome]
        exact runBounded_liftContinuationState prefixCells limits ticks next

/-- **Yielded-Continuation Lifting Across State/Environment Upgrades (`liftYieldedContinuation_commutes`).**
    Persisting a `Control.yielded planAddr` continuation to a `ByteArray` image, upgrading the
    image by injecting `prefixCells` (`upgradePersistedHeapImage`), rehydrating in the upgraded
    process, and resuming with `response` commutes identically with `resume`, `stepRaw`, and
    `runBounded` across any tick budget. -/
theorem liftYieldedContinuation_commutes (prefixCells : Array Cell)
    {s resumed : State} {plan : Address} (hy : s.control = .yielded plan)
    (response : Term) (hres : resume response s = some resumed)
    (limits : Limits) (ticks : Nat) :
    ∃ upgradedBytes upgradedState upgradedResumed,
      upgradePersistedHeapImage prefixCells (encodeHeapImage s) = some upgradedBytes ∧
      decodeHeapImage upgradedBytes = some upgradedState ∧
      upgradedState.control = .yielded (prefixCells.size + plan) ∧
      resume response upgradedState = some upgradedResumed ∧
      upgradedResumed = liftContinuationState prefixCells resumed ∧
      runBounded ⟨limits.heap + prefixCells.size, limits.stack⟩ ticks upgradedResumed =
        liftContinuationOutcome prefixCells (runBounded limits ticks resumed) := by
  refine ⟨encodeHeapImage (liftContinuationState prefixCells s),
    liftContinuationState prefixCells s,
    liftContinuationState prefixCells resumed,
    ?_, decodeHeapImage_encodeHeapImage _, ?_, ?_, rfl,
    runBounded_liftContinuationState prefixCells limits ticks resumed⟩
  · simp [upgradePersistedHeapImage, decodeHeapImage_encodeHeapImage]
  · simp [liftContinuationState, hy, liftContinuationControl, renameControl]
  · unfold resume at hres ⊢
    rw [hy] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    simp [liftContinuationState, hy, liftContinuationControl, renameControl]

/-! ## 5. Concrete End-to-End Inhabitedness Witnesses -/

/-- Concrete inhabited witness for `lazyUpgrade_obs_eq_eagerUpgrade`: a 3-bucket store undergoing
    two live schema upgrades (`epoch 0 → 1 → 2`) interleaved with point reads and writes. -/
theorem lazyBucketStore_multiEpoch_inhabited :
    let mig : EpochMigrator Nat := ⟨fun e v => v + (e + 1) * 10⟩
    let init : LazyBucketStore Nat := ⟨0, #[⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩]⟩
    let turns : List (BucketStoreTurn Nat Nat) := [
      .upgradeEpoch,
      .read 0 id,
      .write 1 (· + 5),
      .upgradeEpoch,
      .read 1 id,
      .read 2 id
    ]
    let lRes := runLazyStoreTrace mig init turns
    let eRes := runEagerStoreTrace mig init turns
    lRes.2 = eRes.2 ∧ flushLazyBuckets mig lRes.1 = eRes.1 := by
  let mig : EpochMigrator Nat := ⟨fun e v => v + (e + 1) * 10⟩
  let init : LazyBucketStore Nat := ⟨0, #[⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩]⟩
  let turns : List (BucketStoreTurn Nat Nat) := [
    .upgradeEpoch, .read 0 id, .write 1 (· + 5), .upgradeEpoch, .read 1 id, .read 2 id
  ]
  have hInit : ∀ (i : Nat) (hi : i < init.buckets.size),
      init.buckets[i].epoch = init.targetEpoch := by
    intro i hi
    have hlt : i < 3 := by simpa [init] using hi
    match i, hi, hlt with
    | 0, _, _ => simp [init]
    | 1, _, _ => simp [init]
    | 2, _, _ => simp [init]
    | _ + 3, _, hlt => omega
  have hEq := lazyUpgrade_obs_eq_eagerUpgrade mig init hInit turns
  rcases hL : runLazyStoreTrace mig init turns with ⟨lFin, lObs⟩
  rcases hE : runEagerStoreTrace mig init turns with ⟨eFin, eObs⟩
  change (runLazyStoreTrace mig init turns).2 = (runEagerStoreTrace mig init turns).2 ∧
    flushLazyBuckets mig (runLazyStoreTrace mig init turns).1 = (runEagerStoreTrace mig init turns).1
  rw [hL, hE] at hEq ⊢
  exact hEq

/-! ### Non-Identity Cross-Habitat Upgrade Witness (`Rec` → `AuditedRec`, Non-Empty `LobCost`) -/

/-- Richer epoch-2 habitat state: pairs `Genealogy.Rec` with a persistent `auditCount` + `schemaTag`
    slot absent from `Genealogy.record`. -/
abbrev AuditedRec := Obend.Judge.Genealogy.Rec × (Nat × String)

/-- Upgraded epoch-2 habitat extending `Genealogy.record` with write-audit counting. -/
abbrev auditedRecordHabitat : Obend.Judge.Genealogy.Habitat where
  State := AuditedRec
  Act := Obend.Judge.Genealogy.RecAct
  Floor := Obend.Judge.Genealogy.RecFloor
  holds φ s := Obend.Judge.Genealogy.RecFloor.holds φ s.1
  step a s :=
    match a with
    | .write c v => (Obend.Judge.Genealogy.record.step (.write c v) s.1, (s.2.1 + 1, s.2.2))
    | .revert => (Obend.Judge.Genealogy.record.step .revert s.1, s.2)
    | .forget => (Obend.Judge.Genealogy.record.step .forget s.1, s.2)
  format := Obend.Judge.Genealogy.record.format
  proved := Obend.Judge.Genealogy.record.proved
  proved_sound hp a s hf hr := by
    cases a <;> exact Obend.Judge.Genealogy.record.proved_sound hp _ s.1 hf hr
  revert := .revert
  revert_proved := Obend.Judge.Genealogy.record.revert_proved
  bedrock := Obend.Judge.Genealogy.record.bedrock

/-- Non-identity `SymmetricEditLens` bridging `Genealogy.Rec` (epoch 1) and `AuditedRec` (epoch 2)
    via persistent complement `Nat × String` (dualizing `DeltaLens.fst` through `SymmetricEditLens.symm`). -/
def recToAuditedEditLens :
    SymmetricEditLens Obend.Judge.Genealogy.Rec AuditedRec AuditedRec
      (OverwriteEdit Obend.Judge.Genealogy.Rec) (OverwriteEdit AuditedRec) :=
  ((DeltaLens.fst Obend.Judge.Genealogy.Rec (Nat × String)).toSymmetricEditLens).symm
    (fun r => ((r, (0, "audited-v2")), (r, (0, "audited-v2"))))
    (fun _ => ⟨rfl, rfl⟩)

def genesisRecordGate : Obend.Judge.Genealogy.Gate Obend.Judge.Genealogy.record where
  name := "gate@v1"
  formats := ["revert@1", "write@1"]
  floors := [.home 4]
  methods := [
    ("revert@1", .home 4, .lemma),
    ("write@1", .home 4, .eval .kernel)
  ]
  basis := [.kernel]

/-- Epoch-2 gate strengthening floors (`home 4` + `cap "x" 50`) AND extending the trust basis with
    `.compiled` (requiring non-empty `lobLabels := [.compiled]`). -/
def upgradedAuditedGate : Obend.Judge.Genealogy.Gate auditedRecordHabitat where
  name := "gate@v2"
  formats := ["revert@1", "write@1"]
  floors := [.home 4, .cap "x" 50]
  methods := [
    ("revert@1", .home 4, .lemma),
    ("revert@1", .cap "x" 50, .lemma),
    ("write@1", .home 4, .eval .kernel),
    ("write@1", .cap "x" 50, .eval .compiled)
  ]
  basis := [.kernel, .compiled]

def anchorAuditedGate (G₁ : Obend.Judge.Genealogy.Gate Obend.Judge.Genealogy.record) :
    Obend.Judge.Genealogy.Gate auditedRecordHabitat where
  name := G₁.name
  formats := G₁.formats
  floors := G₁.floors
  methods := G₁.methods
  basis := G₁.basis

/-- Non-trivial cross-habitat `UpgradeEnvelope` (`Rec` → `AuditedRec`) with non-identity
    `recToAuditedEditLens`, strengthened `cap "x" 50` floor, and non-empty `lobLabels := [.compiled]`. -/
def recordCrossHabitatEnvelope :
    UpgradeEnvelope Obend.Judge.Genealogy.record auditedRecordHabitat
      AuditedRec
      (OverwriteEdit Obend.Judge.Genealogy.Rec)
      (OverwriteEdit AuditedRec) where
  fromEpoch := 1
  toEpoch := 2
  lens := recToAuditedEditLens
  actToEdit₁ a s := some (Obend.Judge.Genealogy.record.step a s)
  actToEdit₁_eq _ _ := rfl
  liftFloor φ := φ
  liftFloor_iff hc := by
    rcases hc with ⟨_, hs₁⟩
    subst hs₁
    exact Iff.rfl
  anchorGate := anchorAuditedGate
  anchorGate_floors _ _ h := h
  anchorGate_basis _ _ h := h
  nextGate := upgradedAuditedGate
  lobLabels := [.compiled]

theorem recordUpgradeEnvelope_relink_inhabited :
    let X := Obend.Judge.Genealogy.Exec.faithful
    let s₀ : Obend.Judge.Genealogy.Rec := ⟨[], [], []⟩
    let seg₁ : List Obend.Judge.Genealogy.RecAct := [.write "x" 12]
    let seg₂ : List Obend.Judge.Genealogy.RecAct := [.write "x" 30]
    ∃ s₂_fin c_mid,
      replaySegmentedUpgradeLog X genesisRecordGate s₀ seg₁ recordCrossHabitatEnvelope seg₂ =
        some (s₂_fin, c_mid) ∧
      s₂_fin.2 = (1, "audited-v2") ∧
      Obend.Judge.Genealogy.RecFloor.holds (.home 4) s₂_fin.1 ∧
      Obend.Judge.Genealogy.RecFloor.holds (.cap "x" 50) s₂_fin.1 := by
  let X := Obend.Judge.Genealogy.Exec.faithful
  let s₀ : Obend.Judge.Genealogy.Rec := ⟨[], [], []⟩
  have hRun : replaySegmentedUpgradeLog X genesisRecordGate s₀ [.write "x" 12]
      recordCrossHabitatEnvelope [.write "x" 30] =
      some ((⟨[("x", 30)], [[("x", 12)], []], []⟩, (1, "audited-v2")),
            (⟨[("x", 12)], [[]], []⟩, (0, "audited-v2"))) := rfl
  refine ⟨_, _, hRun, rfl, ⟨rfl, by decide⟩, ?_⟩
  intro st hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl <;> decide

end Obend.Repair
end
