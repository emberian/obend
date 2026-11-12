module
/-
# Obend.Metatheory.PinsAndQuiescence — Open Causal Cones, Provenance Nullifiers & Horizon Folding

1. **Birth-Provenance `derivePinNullifier` (`0` `height : Nat`)**: domain-tagged 256-bit cSHAKE256
   nullifier over `(originEvent, portIx)` with constructive `PSum` 2-element `CollisionAmong` extractor.
2. **The 4 Substance Laws (`checkQuiescent ↔ QuiescentValid`)**: zero open borrows, universal asset
   conservation, capability attenuation, and input/output provenance nullifier `Nodup` + freshness.
3. **Horizon Contraction & Coarse-vs-Fine Observer Invariance (`foldHorizon_quiescent_and_observer_invariant`)**:
   folds conflict-free causal cones while preventing internal-spend replay and preserving macro-boundaries.
-/
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Judge.Class

public section
namespace Obend.Metatheory.PinsAndQuiescence

open Obend.Digest

set_option autoImplicit false

/-! ## 1. 256-Bit `TypedPin` & Birth-Provenance `derivePinNullifier` (`0` `height : Nat`) -/

abbrev Digest256 := BitVec 256
abbrev PortIx := UInt64

/-- Substance sort carried on a directed causal pin. -/
inductive PinSort where
  | matter (asset : Nat) (amount : Nat)
  | capability (capId : Nat) (attenuationMask : BitVec 64)
  | pureData (schemaTag : Nat)
  | judgeWitness (formatTag : Nat)
  deriving DecidableEq, Repr

/-- Directed causal wire pin identified by its birth provenance `(originEvent, portIx)` rather than
    any global block or epoch height. -/
structure TypedPin where
  originEvent : Digest256
  portIx      : PortIx
  sort        : PinSort
  payloadHash : Digest256
  deriving DecidableEq, Repr

/-- Domain customization bytes for Houyhnhnm pin nullifiers. -/
def pinNullifierDomain : List UInt8 :=
  "Obend.Metatheory.PinNullifier.v1".toUTF8.toList

/-- Domain-separated cSHAKE256 byte hash for pin nullifiers. -/
def pinNullifierHash : HashBytes.Hash :=
  Cshake256.cshake256Bytes pinNullifierDomain

/-- Exact 40-byte big-endian length-framed birth-provenance preimage `(originEvent, portIx)`. -/
@[expose] def encodePinOrigin (originEvent : Digest256) (portIx : PortIx) : List UInt8 :=
  HashBytes.be 32 originEvent.toNat ++ HashBytes.be 8 portIx.toNat

theorem encodePinOrigin_injective {o₁ o₂ : Digest256} {p₁ p₂ : PortIx}
    (h : encodePinOrigin o₁ p₁ = encodePinOrigin o₂ p₂) :
    o₁ = o₂ ∧ p₁ = p₂ := by
  unfold encodePinOrigin at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [HashBytes.length_be])
  have h32 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have h8  : (256 : Nat) ^ 8  = 2 ^ 64  := by decide
  have ho : o₁.toNat = o₂.toNat :=
    HashBytes.be_injective (h32 ▸ o₁.isLt) (h32 ▸ o₂.isLt) h1
  have hp : p₁.toBitVec.toNat = p₂.toBitVec.toNat :=
    HashBytes.be_injective (h8 ▸ p₁.toBitVec.isLt) (h8 ▸ p₂.toBitVec.isLt) h2
  exact ⟨BitVec.eq_of_toNat_eq ho, UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hp)⟩

/-- Birth-provenance 256-bit nullifier of `(originEvent, portIx)` — zero `height : Nat`! -/
@[expose] def derivePinNullifier (originEvent : Digest256) (portIx : PortIx) : Digest256 :=
  BitVec.ofNat 256 (HashBytes.ofBE (pinNullifierHash (encodePinOrigin originEvent portIx)))

/-- Convenience projection for a `TypedPin`'s provenance nullifier. -/
abbrev TypedPin.nullifier (p : TypedPin) : Digest256 :=
  derivePinNullifier p.originEvent p.portIx

theorem derivePinNullifier_toNat (o : Digest256) (p : PortIx) :
    (derivePinNullifier o p).toNat =
      HashBytes.ofBE (pinNullifierHash (encodePinOrigin o p)) := by
  unfold derivePinNullifier
  rw [BitVec.toNat_ofNat]
  have hlen : (pinNullifierHash (encodePinOrigin o p)).length = 32 := by
    simp [pinNullifierHash]
  have hlt : HashBytes.ofBE (pinNullifierHash (encodePinOrigin o p)) < 256 ^ 32 := by
    simpa [hlen] using HashBytes.ofBE_lt (pinNullifierHash (encodePinOrigin o p))
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  exact Nat.mod_eq_of_lt (hpow ▸ hlt)

/-- Concrete 2-input cSHAKE256 collision witness for distinct birth-provenance pairs. -/
structure PinNullifierCollisionWitness
    (o₁ : Digest256) (p₁ : PortIx) (o₂ : Digest256) (p₂ : PortIx) where
  pre₁  : List UInt8
  pre₂  : List UInt8
  hPre₁ : pre₁ = encodePinOrigin o₁ p₁
  hPre₂ : pre₂ = encodePinOrigin o₂ p₂
  hNe   : pre₁ ≠ pre₂
  hColl : HashBytes.ofBE (pinNullifierHash pre₁) = HashBytes.ofBE (pinNullifierHash pre₂)

/-- **Constructive `PSum` Provenance-Nullifier Binding Extractor (`0 Classical.choice`)**:
    Equal 256-bit nullifiers constructively yield either exact provenance equality
    `o₁ = o₂ ∧ p₁ = p₂` or an explicit 2-preimage cSHAKE256 collision witness. -/
def extractPinNullifierCollision
    (o₁ : Digest256) (p₁ : PortIx) (o₂ : Digest256) (p₂ : PortIx)
    (hEq : derivePinNullifier o₁ p₁ = derivePinNullifier o₂ p₂) :
    PSum (o₁ = o₂ ∧ p₁ = p₂) (PinNullifierCollisionWitness o₁ p₁ o₂ p₂) :=
  if hSame : o₁ = o₂ ∧ p₁ = p₂ then
    .inl hSame
  else
    .inr
      { pre₁  := encodePinOrigin o₁ p₁
        pre₂  := encodePinOrigin o₂ p₂
        hPre₁ := rfl
        hPre₂ := rfl
        hNe   := fun hPreEq => hSame (encodePinOrigin_injective hPreEq)
        hColl := by
          have hNat := congrArg BitVec.toNat hEq
          rwa [derivePinNullifier_toNat, derivePinNullifier_toNat] at hNat }

/-- Every `.inr` witness establishes scoped 2-element `HashBytes.CollisionAmong` (never
    pigeonhole-vacuous global `Collision H`). -/
theorem pinNullifier_collisionAmong
    {o₁ : Digest256} {p₁ : PortIx} {o₂ : Digest256} {p₂ : PortIx}
    (w : PinNullifierCollisionWitness o₁ p₁ o₂ p₂) :
    HashBytes.CollisionAmong pinNullifierHash
      (fun x => x = encodePinOrigin o₁ p₁ ∨ x = encodePinOrigin o₂ p₂) :=
  ⟨w.pre₁, w.pre₂, .inl w.hPre₁, .inr w.hPre₂, w.hNe, w.hColl⟩

/-! ## 2. `OpenEvent`, Matter/Capability Projections & The 4 `QuiescentValid` Substance Laws -/

/-- Amount of `asset` carried on a single `TypedPin`. -/
@[expose] def pinMatter (asset : Nat) (p : TypedPin) : Nat :=
  match p.sort with
  | .matter a amt => if a == asset then amt else 0
  | _ => 0

/-- Total linear matter of `asset` across a pin list. -/
@[expose] def matterTotal (asset : Nat) : List TypedPin → Nat
  | [] => 0
  | p :: ps => pinMatter asset p + matterTotal asset ps

/-- Capability IDs carried across a pin list. -/
@[expose] def capFootprint : List TypedPin → List Nat
  | [] => []
  | p :: ps =>
      match p.sort with
      | .capability capId _ => capId :: capFootprint ps
      | _ => capFootprint ps

/-- Provenance nullifiers across a pin list. -/
abbrev pinNullifiers (ps : List TypedPin) : List Digest256 :=
  ps.map TypedPin.nullifier

/-- Check whether every output capability `(capId, maskOut)` is attenuated from some input
    capability `(capId, maskIn)` (`(maskOut &&& maskIn) = maskOut`). -/
@[expose] def capAttenuatedFrom (inPins : List TypedPin) (p : TypedPin) : Bool :=
  match p.sort with
  | .capability capId maskOut =>
      inPins.any fun q =>
        match q.sort with
        | .capability inId maskIn => (inId == capId) && ((maskOut &&& maskIn) == maskOut)
        | _ => false
  | _ => true

/-- Open symmetric-monoidal event morphing input pins `inPins` to output pins `outPins`. -/
structure OpenEvent where
  eventId      : Digest256
  inPins       : List TypedPin
  outPins      : List TypedPin
  openBorrows  : Nat
  judgeChecked : Bool
  deriving DecidableEq, Repr

/-- **The 4 Substance Laws of Quiescent Open Events (`QuiescentValid`)**:
    1. `noOpenBorrows`: zero dangling linear borrows (`openBorrows = 0`),
    2. `matterConserved`: exact linear conservation of every asset `a : Nat`,
    3. `capsAttenuated`: every output capability is attenuated from an input capability (`outCaps ⊆ inCaps`),
    4. `pinsLinearAndJudged`: duplicate-free `inPins`/`outPins`, distinct input AND output provenance
       nullifiers, provenance-level causal freshness (`p.nullifier ∉ pinNullifiers inPins`), and
       `Judge` acceptance (`judgeChecked = true`). -/
structure QuiescentValid (ev : OpenEvent) : Prop where
  noOpenBorrows        : ev.openBorrows = 0
  matterConserved      : ∀ a : Nat, matterTotal a ev.inPins = matterTotal a ev.outPins
  capsAttenuated       : ∀ p ∈ ev.outPins, capAttenuatedFrom ev.inPins p = true
  inNodup              : ev.inPins.Nodup
  outNodup             : ev.outPins.Nodup
  inNullifiersNodup    : (pinNullifiers ev.inPins).Nodup
  outNullifiersNodup   : (pinNullifiers ev.outPins).Nodup
  causalFreshNullifier : ∀ p ∈ ev.outPins, p.nullifier ∉ pinNullifiers ev.inPins
  judgeAccepted        : ev.judgeChecked = true

/-! ## 3. Decidable `Judge` Instance for Quiescent Event Boundaries (`checkQuiescent ↔ QuiescentValid`) -/

inductive QuiescenceClause where
  | danglingBorrow | matterImbalance (asset : Nat) | amplifiedCapability
  | duplicateOrCyclicPins | unjudgedPayload
  deriving DecidableEq, Repr

def pinsAssets : List TypedPin → List Nat
  | [] => []
  | p :: ps => match p.sort with | .matter a _ => a :: pinsAssets ps | _ => pinsAssets ps

private theorem matterTotal_zero_of_not_mem_pinsAssets {a : Nat} :
    ∀ {ps : List TypedPin}, a ∉ pinsAssets ps → matterTotal a ps = 0
  | [], _ => rfl
  | p :: ps, hNot => by
    cases hs : p.sort with
    | matter b amt =>
      simp only [pinsAssets, hs, List.mem_cons, not_or] at hNot
      have hNe : (b == a) = false := beq_false_of_ne (Ne.symm hNot.1)
      simp [matterTotal, pinMatter, hs, hNe, matterTotal_zero_of_not_mem_pinsAssets hNot.2]
    | _ =>
      simp only [pinsAssets, hs] at hNot
      simp [matterTotal, pinMatter, hs, matterTotal_zero_of_not_mem_pinsAssets hNot]

/-- Decidable quiescence check computing all mentioned assets directly from `ev.inPins` and `ev.outPins`. -/
@[expose] def checkQuiescent (ev : OpenEvent) : Judge.Verdict QuiescenceClause :=
  let assets := pinsAssets ev.inPins ++ pinsAssets ev.outPins
  if ev.openBorrows != 0 then .refused .danglingBorrow []
  else if !(ev.outPins.all (capAttenuatedFrom ev.inPins)) then .refused .amplifiedCapability []
  else if !(decide ev.inPins.Nodup && decide ev.outPins.Nodup &&
            decide (pinNullifiers ev.inPins).Nodup && decide (pinNullifiers ev.outPins).Nodup &&
            ev.outPins.all (fun p => !(pinNullifiers ev.inPins).contains p.nullifier)) then
    .refused .duplicateOrCyclicPins []
  else if !ev.judgeChecked then .refused .unjudgedPayload []
  else match assets.find? (fun a => matterTotal a ev.inPins != matterTotal a ev.outPins) with
    | some badAsset => .refused (.matterImbalance badAsset) []
    | none => .ok

theorem checkQuiescent_ok_iff (ev : OpenEvent) :
    checkQuiescent ev = .ok ↔ QuiescentValid ev := by
  unfold checkQuiescent; dsimp only
  constructor
  · intro h
    split at h; · cases h
    rename_i hB; split at h; · cases h
    rename_i hC; split at h; · cases h
    rename_i hN; split at h; · cases h
    rename_i hJ
    cases hf : (pinsAssets ev.inPins ++ pinsAssets ev.outPins).find?
        (fun a => matterTotal a ev.inPins != matterTotal a ev.outPins) with
    | some bad => rw [hf] at h; cases h
    | none =>
      simp only [bne_iff_ne, Classical.not_not] at hB
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hC hJ
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hN
      have hFresh : ∀ p ∈ ev.outPins, p.nullifier ∉ pinNullifiers ev.inPins :=
        fun p hp hm => Bool.false_ne_true ((hN.2 p hp).symm.trans (List.contains_iff_mem.2 hm))
      refine ⟨hB, ?_, hC, hN.1.1.1.1, hN.1.1.1.2, hN.1.1.2, hN.1.2, hFresh, hJ⟩
      intro a
      by_cases ha : a ∈ pinsAssets ev.inPins ++ pinsAssets ev.outPins
      · simpa [bne_iff_ne] using List.find?_eq_none.1 hf a ha
      · rw [List.mem_append, not_or] at ha
        rw [matterTotal_zero_of_not_mem_pinsAssets ha.1, matterTotal_zero_of_not_mem_pinsAssets ha.2]
  · rintro ⟨hB, hM, hC, hIn, hOut, hInNul, hOutNul, hFresh, hJ⟩
    have hB' : (ev.openBorrows != 0) = false := by simp [hB]
    have hC' : ev.outPins.all (capAttenuatedFrom ev.inPins) = true := List.all_eq_true.2 hC
    have hFresh' : (ev.outPins.all (fun p => !(pinNullifiers ev.inPins).contains p.nullifier)) = true :=
      List.all_eq_true.2 fun p hp => by
        cases hc : (pinNullifiers ev.inPins).contains p.nullifier
        · rfl
        · exact absurd (List.contains_iff_mem.1 hc) (hFresh p hp)
    have hFind : (pinsAssets ev.inPins ++ pinsAssets ev.outPins).find?
        (fun a => matterTotal a ev.inPins != matterTotal a ev.outPins) = none := by
      rw [List.find?_eq_none]; intro a _; simp [hM a]
    simp only [hB', hC', hIn, hOut, hInNul, hOutNul, hFresh', hJ, hFind,
      decide_true, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false]

/-- Inhabited, sound, complete, and refuting `Obend.Judge` instance establishing full `QuiescentValid`. -/
instance quiescentEventJudge : Obend.Judge OpenEvent Unit where
  Clause := QuiescenceClause
  Meaning ev _ := QuiescentValid ev
  check _ ev _ := checkQuiescent ev
  sound h := (checkQuiescent_ok_iff _).1 h
  refutes _ := true
  refuted {r o c k p} hRef _ _ hMean := by
    have hOk := (checkQuiescent_ok_iff o).2 hMean; rw [hOk] at hRef; cases hRef
  Fragment _ := True
  complete _ hEx := let ⟨_, hMean⟩ := hEx; ⟨(), 0, (checkQuiescent_ok_iff _).2 hMean⟩
  mono _ _ := rfl

theorem capAttenuatedFrom_implies_mem_capFootprint {inPins : List TypedPin} {p : TypedPin}
    (hAtt : capAttenuatedFrom inPins p = true) :
    ∀ c, c ∈ capFootprint [p] → c ∈ capFootprint inPins := by
  intro c hc
  unfold capAttenuatedFrom at hAtt
  cases hs : p.sort with
  | matter _ _ | pureData _ | judgeWitness _ =>
    simp [capFootprint, hs] at hc
  | capability cid maskOut =>
    simp only [capFootprint, hs, List.mem_singleton] at hc
    subst hc
    simp only [hs, List.any_eq_true] at hAtt
    obtain ⟨q, hqMem, hqMatch⟩ := hAtt
    induction inPins with
    | nil => cases hqMem
    | cons hd tl ih =>
      rcases List.mem_cons.1 hqMem with rfl | htl
      · cases hqs : q.sort with
        | capability inId maskIn =>
          simp only [hqs, Bool.and_eq_true, beq_iff_eq] at hqMatch
          simp [capFootprint, hqs, hqMatch.1]
        | _ => simp [hqs] at hqMatch
      · have hSub := ih htl
        cases hds : hd.sort <;> simp [capFootprint, hds, hSub]

/-- Under `QuiescentValid`, every capability ID on `ev.outPins` was held on `ev.inPins`. -/
theorem QuiescentValid.capFootprint_subset {ev : OpenEvent} (hq : QuiescentValid ev) :
    ∀ c ∈ capFootprint ev.outPins, c ∈ capFootprint ev.inPins := by
  suffices gen : ∀ (ps : List TypedPin),
      (∀ p ∈ ps, capAttenuatedFrom ev.inPins p = true) →
      ∀ c ∈ capFootprint ps, c ∈ capFootprint ev.inPins from
    gen ev.outPins hq.capsAttenuated
  intro ps hOut c hc
  induction ps with
  | nil => cases hc
  | cons p rest ih =>
    have hp := hOut p List.mem_cons_self
    have hps : ∀ q ∈ rest, capAttenuatedFrom ev.inPins q = true :=
      fun q hqMem => hOut q (List.mem_cons_of_mem p hqMem)
    cases hpsort : p.sort with
    | capability cid m =>
      simp only [capFootprint, hpsort, List.mem_cons] at hc
      rcases hc with rfl | hrest
      · exact capAttenuatedFrom_implies_mem_capFootprint hp c (by simp [capFootprint, hpsort])
      · exact ih hps hrest
    | _ =>
      simp only [capFootprint, hpsort] at hc
      exact ih hps hc

/-! ## 4. Symmetric-Monoidal Cut Contraction & Coarse-vs-Fine Horizon Invariance -/

/-- Boundary observable projection of an `OpenEvent` (inPins, outPins), invariant under internal
    horizon slicing! -/
structure BoundaryPins where
  inPins  : List TypedPin
  outPins : List TypedPin
  deriving DecidableEq, Repr

abbrev OpenEvent.boundary (ev : OpenEvent) : BoundaryPins :=
  ⟨ev.inPins, ev.outPins⟩

/-- Symmetric-monoidal wire contraction of causal boundary `b₁` followed by `b₂`:
    internal matched wires `b₁.outPins ∩ b₂.inPins` cancel, leaving unconsumed external inputs
    and unspent external outputs. -/
@[expose] def contractBoundary (b₁ b₂ : BoundaryPins) : BoundaryPins where
  inPins  := b₁.inPins ++ b₂.inPins.filter (fun p => !b₁.outPins.contains p)
  outPins := b₁.outPins.filter (fun p => !b₂.inPins.contains p) ++ b₂.outPins

/-- Causal conflict-freedom between an upstream event/cone `b₁` and downstream `b₂`, enforced at
    the level of 256-bit birth-provenance nullifiers:
    - `disjointInputs`: no double-spend of the same external input pin,
    - `disjointOutputs` & `outNullifierDisj`: distinct birth provenance on surviving outputs,
    - `noBackwardNullifier`: `b₂` outputs cannot collide with `b₁` input nullifiers,
    - `nullifierDisj`: unmatched `b₂.inPins` do not collide with `b₁.inPins` nullifiers. -/
structure CausalComposable (b₁ b₂ : BoundaryPins) : Prop where
  disjointInputs      : ∀ p ∈ b₁.inPins, p ∉ b₂.inPins
  disjointOutputs     : ∀ p ∈ b₁.outPins, p ∉ b₂.outPins
  outNullifierDisj    : ∀ p ∈ b₁.outPins, p ∉ b₂.inPins → p.nullifier ∉ pinNullifiers b₂.outPins
  noTamperedWire      : ∀ q ∈ b₂.inPins, q ∉ b₁.outPins → q.nullifier ∉ pinNullifiers b₁.outPins
  noBackwardNullifier : ∀ p ∈ b₂.outPins, p.nullifier ∉ pinNullifiers b₁.inPins
  nullifierDisj       : ∀ p ∈ b₂.inPins, p ∉ b₁.outPins → p.nullifier ∉ pinNullifiers b₁.inPins

/-- Compose two `OpenEvent`s into a macro-event tagged with `mergedId`. -/
@[expose] def composeEvents (mergedId : Digest256) (e₁ e₂ : OpenEvent) : OpenEvent :=
  let b := contractBoundary e₁.boundary e₂.boundary
  { eventId      := mergedId
    inPins       := b.inPins
    outPins      := b.outPins
    openBorrows  := e₁.openBorrows + e₂.openBorrows
    judgeChecked := e₁.judgeChecked && e₂.judgeChecked }

private theorem matterTotal_append (a : Nat) (xs ys : List TypedPin) :
    matterTotal a (xs ++ ys) = matterTotal a xs + matterTotal a ys := by
  induction xs with
  | nil => simp [matterTotal]
  | cons x rest ih => simp [matterTotal, ih, Nat.add_assoc]

private theorem matterTotal_filter_part (a : Nat) (pred : TypedPin → Bool) (xs : List TypedPin) :
    matterTotal a xs =
      matterTotal a (xs.filter pred) + matterTotal a (xs.filter (fun p => !pred p)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases hp : pred x <;> simp [List.filter, hp, matterTotal] <;> omega

private theorem erase_matterTotal (a : Nat) {p : TypedPin} :
    ∀ {ys : List TypedPin}, p ∈ ys →
      matterTotal a ys = pinMatter a p + matterTotal a (ys.erase p)
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    by_cases hpy : y == p
    · have hyEq : y = p := beq_iff_eq.1 hpy
      subst hyEq
      simp [List.erase_cons_head, matterTotal]
    · have hne : y ≠ p := fun heq => hpy (beq_iff_eq.2 heq)
      rcases List.mem_cons.1 h with rfl | hmem
      · exact absurd rfl hne
      · have ih := erase_matterTotal a hmem
        have herase : (y :: ys).erase p = y :: ys.erase p := by simp [hpy]
        rw [herase]
        simp only [matterTotal, ih]
        omega

private theorem nodup_append_disj {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ x ∈ xs, x ∉ ys) → (xs ++ ys).Nodup
  | [], _, _, hy, _ => hy
  | x :: xs, ys, hnx, hy, hDisj => by
    cases hnx with
    | cons hxNotXs hnx' =>
      refine List.Pairwise.cons ?_ (nodup_append_disj hnx' hy (fun z hz => hDisj z (List.mem_cons_of_mem x hz)))
      intro z hz heq
      rcases List.mem_append.1 hz with hzXs | hzYs
      · exact hxNotXs z hzXs heq
      · subst heq; exact hDisj x List.mem_cons_self hzYs

private theorem nodup_equiv_matterTotal (a : Nat) :
    ∀ {xs ys : List TypedPin}, xs.Nodup → ys.Nodup →
      (∀ p, p ∈ xs ↔ p ∈ ys) → matterTotal a xs = matterTotal a ys
  | [], ys, _, _, heq => by
    cases ys with
    | nil => rfl
    | cons y _ => exact absurd ((heq y).2 List.mem_cons_self) List.not_mem_nil
  | x :: xs, ys, hnx, hny, heq => by
    cases hnx with
    | cons hxNotMem hnx' =>
      have hxInYs : x ∈ ys := (heq x).1 List.mem_cons_self
      have hEraseYs := erase_matterTotal a hxInYs
      have hny' : (ys.erase x).Nodup := hny.erase x
      have heq' : ∀ p, p ∈ xs ↔ p ∈ ys.erase x := by
        intro p
        by_cases hpx : p = x
        · subst hpx
          exact ⟨fun h => absurd rfl (hxNotMem p h), fun h => by
            have hcnt := List.Nodup.erase_eq_filter hny p
            rw [hcnt, List.mem_filter] at h; simp at h⟩
        · rw [List.Nodup.mem_erase_iff hny]
          exact ⟨fun h => ⟨hpx, (heq p).1 (List.mem_cons_of_mem x h)⟩,
                 fun ⟨_, hy⟩ => by
                   rcases List.mem_cons.1 ((heq p).2 hy) with rfl | hxs
                   · exact absurd rfl hpx
                   · exact hxs⟩
      have ih := nodup_equiv_matterTotal a hnx' hny' heq'
      simp only [matterTotal, hEraseYs, ih]

private theorem matched_matter_eq (a : Nat) {out₁ in₂ : List TypedPin}
    (hOut : out₁.Nodup) (hIn : in₂.Nodup) :
    matterTotal a (out₁.filter (fun p => in₂.contains p)) =
      matterTotal a (in₂.filter (fun p => out₁.contains p)) := by
  apply nodup_equiv_matterTotal a (hOut.filter _) (hIn.filter _)
  intro p
  simp [List.mem_filter, List.contains_eq_mem, And.comm]

private theorem capAttenuatedFrom_mono {xs ys : List TypedPin}
    (hSub : ∀ q ∈ xs, q ∈ ys) {p : TypedPin}
    (hAtt : capAttenuatedFrom xs p = true) :
    capAttenuatedFrom ys p = true := by
  unfold capAttenuatedFrom at hAtt ⊢
  cases hs : p.sort with
  | capability cid maskOut =>
    simp only [hs, List.any_eq_true] at hAtt ⊢
    obtain ⟨q, hqMem, hqOk⟩ := hAtt
    exact ⟨q, hSub q hqMem, hqOk⟩
  | _ => simp

private theorem capAttenuatedFrom_trans {in₁ out₁ : List TypedPin}
    (hStep₁ : ∀ q ∈ out₁, capAttenuatedFrom in₁ q = true)
    {in₂ : List TypedPin} {p : TypedPin}
    (hStep₂ : capAttenuatedFrom in₂ p = true) :
    capAttenuatedFrom (in₁ ++ in₂.filter (fun r => !out₁.contains r)) p = true := by
  unfold capAttenuatedFrom at hStep₂ ⊢
  cases hs : p.sort with
  | capability cid maskOut =>
    simp only [hs, List.any_eq_true] at hStep₂ ⊢
    obtain ⟨q, hqIn₂, hqMatch⟩ := hStep₂
    by_cases hqOut₁ : out₁.contains q = true
    · have hqMemOut₁ : q ∈ out₁ := List.contains_iff_mem.1 hqOut₁
      have hqAtt₁ := hStep₁ q hqMemOut₁
      unfold capAttenuatedFrom at hqAtt₁
      cases hqs : q.sort with
      | capability midId maskMid =>
        simp only [hqs, Bool.and_eq_true, beq_iff_eq] at hqMatch
        simp only [hqs, List.any_eq_true] at hqAtt₁
        obtain ⟨r, hrIn₁, hrMatch⟩ := hqAtt₁
        refine ⟨r, List.mem_append_left _ hrIn₁, ?_⟩
        cases hrs : r.sort with
        | capability rootId maskRoot =>
          simp only [hrs, Bool.and_eq_true, beq_iff_eq] at hrMatch ⊢
          refine ⟨hrMatch.1.trans hqMatch.1, ?_⟩
          calc
            maskOut &&& maskRoot
              = (maskOut &&& maskMid) &&& maskRoot := by rw [hqMatch.2]
            _ = maskOut &&& (maskMid &&& maskRoot) := BitVec.and_assoc _ _ _
            _ = maskOut &&& maskMid := by rw [hrMatch.2]
            _ = maskOut := hqMatch.2
        | _ => simp [hrs] at hrMatch
      | _ => simp [hqs] at hqMatch
    · refine ⟨q, List.mem_append_right _ ?_, hqMatch⟩
      rw [List.mem_filter]
      exact ⟨hqIn₂, by simpa using hqOut₁⟩
  | _ => simp

/-- **Pairwise Quiescence Preservation (`composeEvents_preserves_quiescent`)**:
    Contracting any two causally composable `QuiescentValid` open events yields a `QuiescentValid`
    composite event! -/
theorem composeEvents_preserves_quiescent (mergedId : Digest256)
    {e₁ e₂ : OpenEvent} (hq₁ : QuiescentValid e₁) (hq₂ : QuiescentValid e₂)
    (hComp : CausalComposable e₁.boundary e₂.boundary) :
    QuiescentValid (composeEvents mergedId e₁ e₂) where
  noOpenBorrows := by simp [composeEvents, hq₁.noOpenBorrows, hq₂.noOpenBorrows]
  matterConserved a := by
    simp only [composeEvents, contractBoundary, matterTotal_append]
    have hM₁ := hq₁.matterConserved a; have hM₂ := hq₂.matterConserved a
    have hPart₁ := matterTotal_filter_part a (fun p => e₂.inPins.contains p) e₁.outPins
    have hPart₂ := matterTotal_filter_part a (fun p => e₁.outPins.contains p) e₂.inPins
    have hMatch := matched_matter_eq a hq₁.outNodup hq₂.inNodup
    omega
  capsAttenuated p hp := by
    simp only [composeEvents, contractBoundary, List.mem_append, List.mem_filter] at hp ⊢
    rcases hp with ⟨hpOut₁, _⟩ | hpOut₂
    · exact capAttenuatedFrom_mono (fun q hq => List.mem_append_left _ hq) (hq₁.capsAttenuated p hpOut₁)
    · exact capAttenuatedFrom_trans hq₁.capsAttenuated (hq₂.capsAttenuated p hpOut₂)
  inNodup := by
    simp only [composeEvents, contractBoundary]
    exact nodup_append_disj hq₁.inNodup (hq₂.inNodup.filter _)
      (fun p hp₁ hp₂ => hComp.disjointInputs p hp₁ (List.mem_filter.1 hp₂).1)
  outNodup := by
    simp only [composeEvents, contractBoundary]
    exact nodup_append_disj (hq₁.outNodup.filter _) hq₂.outNodup
      (fun p hp₁ hp₂ => hComp.disjointOutputs p (List.mem_filter.1 hp₁).1 hp₂)
  inNullifiersNodup := by
    simp only [composeEvents, contractBoundary, List.map_append]
    refine nodup_append_disj hq₁.inNullifiersNodup
      (((List.filter_sublist).map TypedPin.nullifier).nodup hq₂.inNullifiersNodup) ?_
    intro nul hNul₁ hNul₂
    rw [List.mem_map] at hNul₂; obtain ⟨p, hpFilt, rfl⟩ := hNul₂; rw [List.mem_filter] at hpFilt
    have hpNotOut₁ : p ∉ e₁.outPins := fun hm => by
      have hc : e₁.outPins.contains p = true := List.contains_iff_mem.2 hm
      rw [hc] at hpFilt; simp at hpFilt
    exact hComp.nullifierDisj p hpFilt.1 hpNotOut₁ hNul₁
  outNullifiersNodup := by
    simp only [composeEvents, contractBoundary, List.map_append]
    refine nodup_append_disj
      (((List.filter_sublist).map TypedPin.nullifier).nodup hq₁.outNullifiersNodup)
      hq₂.outNullifiersNodup ?_
    intro nul hNul₁ hNul₂
    rw [List.mem_map] at hNul₁; obtain ⟨p, hpFilt, rfl⟩ := hNul₁; rw [List.mem_filter] at hpFilt
    have hpNotIn₂ : p ∉ e₂.inPins := fun hm => by
      have hc : e₂.inPins.contains p = true := List.contains_iff_mem.2 hm
      rw [hc] at hpFilt; simp at hpFilt
    exact hComp.outNullifierDisj p hpFilt.1 hpNotIn₂ hNul₂
  causalFreshNullifier p hpOut hNulIn := by
    simp only [composeEvents, contractBoundary, pinNullifiers, List.mem_append, List.mem_filter,
      List.map_append] at hpOut hNulIn
    rcases hpOut with ⟨hpOut₁, _⟩ | hpOut₂
    · rcases hNulIn with hIn₁ | hIn₂
      · exact hq₁.causalFreshNullifier p hpOut₁ hIn₁
      · rw [List.mem_map] at hIn₂; obtain ⟨q, hqFilt, hEqN⟩ := hIn₂; rw [List.mem_filter] at hqFilt
        have hqNotOut₁ : q ∉ e₁.outPins := fun hm => by
          have hc : e₁.outPins.contains q = true := List.contains_iff_mem.2 hm
          rw [hc] at hqFilt; simp at hqFilt
        have hpMem : p.nullifier ∈ pinNullifiers e₁.outPins := List.mem_map_of_mem hpOut₁
        rw [← hEqN] at hpMem
        exact hComp.noTamperedWire q hqFilt.1 hqNotOut₁ hpMem
    · rcases hNulIn with hIn₁ | hIn₂
      · exact hComp.noBackwardNullifier p hpOut₂ hIn₁
      · rw [List.mem_map] at hIn₂; obtain ⟨q, hqFilt, hEqN⟩ := hIn₂; rw [List.mem_filter] at hqFilt
        have hqMem : q.nullifier ∈ pinNullifiers e₂.inPins := List.mem_map_of_mem hqFilt.1
        rw [hEqN] at hqMem
        exact hq₂.causalFreshNullifier p hpOut₂ hqMem
  judgeAccepted := by simp [composeEvents, hq₁.judgeAccepted, hq₂.judgeAccepted]

/-- **Strict Monoidal Associativity of Causal Boundary Contraction (`contractBoundary_assoc`)**. -/
theorem contractBoundary_assoc {b₁ b₂ b₃ : BoundaryPins}
    (hIn₂₃  : ∀ p ∈ b₃.inPins, p ∉ b₂.inPins)
    (hOut₁₂ : ∀ p ∈ b₁.outPins, p ∉ b₂.outPins) :
    contractBoundary (contractBoundary b₁ b₂) b₃ =
      contractBoundary b₁ (contractBoundary b₂ b₃) := by
  unfold contractBoundary
  congr 1
  · rw [List.filter_append, List.append_assoc]
    congr 2; rw [List.filter_filter]; apply List.filter_congr
    intro p hp₃
    have hNotMemIn₂ : p ∉ b₂.inPins := hIn₂₃ p hp₃
    simp [List.contains_eq_mem, List.mem_filter, hNotMemIn₂]
  · rw [List.filter_append, List.append_assoc]
    congr 1; rw [List.filter_filter]; apply List.filter_congr
    intro p hp₁
    have hNotMemOut₂ : p ∉ b₂.outPins := hOut₁₂ p hp₁
    simp [List.contains_eq_mem, List.mem_filter, hNotMemOut₂, Bool.and_comm]

def emptyBoundary : BoundaryPins := ⟨[], []⟩
@[simp] theorem contractBoundary_empty_left (b : BoundaryPins) :
    contractBoundary emptyBoundary b = b := by cases b; simp [contractBoundary, emptyBoundary]
@[simp] theorem contractBoundary_empty_right (b : BoundaryPins) :
    contractBoundary b emptyBoundary = b := by cases b; simp [contractBoundary, emptyBoundary]
@[expose] def foldHorizonBoundaries : List BoundaryPins → BoundaryPins
  | [] => emptyBoundary
  | b :: bs => bs.foldl contractBoundary b
theorem foldHorizonBoundaries_eq_foldl (bs : List BoundaryPins) :
    foldHorizonBoundaries bs = bs.foldl contractBoundary emptyBoundary := by
  cases bs <;> simp [foldHorizonBoundaries]
/-- Pairwise disjointness across an ordered horizon sequence for partition associativity. -/
def PairwiseHorizonDisjoint : List BoundaryPins → Prop
  | [] => True
  | b :: bs =>
      (∀ b' ∈ bs, (∀ p ∈ b'.inPins, p ∉ b.inPins) ∧ (∀ p ∈ b.outPins, p ∉ b'.outPins)) ∧
      PairwiseHorizonDisjoint bs
private theorem mem_inPins_foldl {acc : BoundaryPins} {bs : List BoundaryPins} {p : TypedPin}
    (h : p ∈ (bs.foldl contractBoundary acc).inPins) :
    p ∈ acc.inPins ∨ ∃ b ∈ bs, p ∈ b.inPins := by
  induction bs generalizing acc with
  | nil => exact .inl h
  | cons b rest ih =>
    rcases ih h with hAccB | ⟨b', hb', hp⟩
    · simp only [contractBoundary, List.mem_append, List.mem_filter] at hAccB
      rcases hAccB with hAcc | ⟨hB, _⟩
      · exact .inl hAcc
      · exact .inr ⟨b, List.mem_cons_self, hB⟩
    · exact .inr ⟨b', List.mem_cons_of_mem b hb', hp⟩
private theorem mem_outPins_foldl {acc : BoundaryPins} {bs : List BoundaryPins} {p : TypedPin}
    (h : p ∈ (bs.foldl contractBoundary acc).outPins) :
    p ∈ acc.outPins ∨ ∃ b ∈ bs, p ∈ b.outPins := by
  induction bs generalizing acc with
  | nil => exact .inl h
  | cons b rest ih =>
    rcases ih h with hAccB | ⟨b', hb', hp⟩
    · simp only [contractBoundary, List.mem_append, List.mem_filter] at hAccB
      rcases hAccB with ⟨hAcc, _⟩ | hB
      · exact .inl hAcc
      · exact .inr ⟨b, List.mem_cons_self, hB⟩
    · exact .inr ⟨b', List.mem_cons_of_mem b hb', hp⟩

private theorem foldl_contractBoundary_shift (acc b : BoundaryPins) (bs : List BoundaryPins)
    (hAccB : ∀ p ∈ acc.outPins, p ∉ b.outPins)
    (hAccBs : ∀ b' ∈ bs, (∀ p ∈ b'.inPins, p ∉ acc.inPins) ∧ (∀ p ∈ acc.outPins, p ∉ b'.outPins))
    (hBBs : ∀ b' ∈ bs, (∀ p ∈ b'.inPins, p ∉ b.inPins) ∧ (∀ p ∈ b.outPins, p ∉ b'.outPins))
    (hDisjBs : PairwiseHorizonDisjoint bs) :
    bs.foldl contractBoundary (contractBoundary acc b) =
      contractBoundary acc (bs.foldl contractBoundary b) := by
  induction bs generalizing acc b with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons]
    have hBC := hBBs c List.mem_cons_self
    have hAssoc : contractBoundary (contractBoundary acc b) c =
        contractBoundary acc (contractBoundary b c) :=
      contractBoundary_assoc hBC.1 hAccB
    rw [hAssoc]
    have hAccBC : ∀ p ∈ acc.outPins, p ∉ (contractBoundary b c).outPins := by
      intro p hp hMem
      simp only [contractBoundary, List.mem_append, List.mem_filter] at hMem
      rcases hMem with ⟨hpB, _⟩ | hpC
      · exact hAccB p hp hpB
      · exact (hAccBs c List.mem_cons_self).2 p hp hpC
    have hDisjRest := hDisjBs.2
    have hCRest := hDisjBs.1
    have hBCRest : ∀ b' ∈ rest,
        (∀ p ∈ b'.inPins, p ∉ (contractBoundary b c).inPins) ∧
        (∀ p ∈ (contractBoundary b c).outPins, p ∉ b'.outPins) := by
      intro b' hb'
      refine ⟨fun p hp hMem => ?_, fun p hMem hp => ?_⟩
      · simp only [contractBoundary, List.mem_append, List.mem_filter] at hMem
        rcases hMem with hpB | ⟨hpC, _⟩
        · exact (hBBs b' (List.mem_cons_of_mem c hb')).1 p hp hpB
        · exact (hCRest b' hb').1 p hp hpC
      · simp only [contractBoundary, List.mem_append, List.mem_filter] at hMem
        rcases hMem with ⟨hpB, _⟩ | hpC
        · exact (hBBs b' (List.mem_cons_of_mem c hb')).2 p hpB hp
        · exact (hCRest b' hb').2 p hpC hp
    exact ih acc (contractBoundary b c) hAccBC
      (fun b' hb' => hAccBs b' (List.mem_cons_of_mem c hb')) hBCRest hDisjRest

private theorem pairwiseDisjoint_append_inv {xs ys : List BoundaryPins}
    (h : PairwiseHorizonDisjoint (xs ++ ys)) :
    PairwiseHorizonDisjoint xs ∧ PairwiseHorizonDisjoint ys ∧
    (∀ x ∈ xs, ∀ y ∈ ys, (∀ p ∈ y.inPins, p ∉ x.inPins) ∧ (∀ p ∈ x.outPins, p ∉ y.outPins)) := by
  induction xs with
  | nil => exact ⟨trivial, h, fun _ hx => absurd hx List.not_mem_nil⟩
  | cons x rest ih =>
    simp only [List.cons_append, PairwiseHorizonDisjoint] at h
    obtain ⟨hHead, hTail⟩ := h
    obtain ⟨hRest, hYs, hCross⟩ := ih hTail
    refine ⟨⟨fun x' hx' => hHead x' (List.mem_append_left _ hx'), hRest⟩, hYs, ?_⟩
    intro z hz y hy
    rcases List.mem_cons.1 hz with rfl | hzr
    · exact hHead y (List.mem_append_right _ hy)
    · exact hCross z hzr y hy

/-- Fold a slice of `OpenEvent`s into a single macro-event when non-empty. -/
@[expose] def foldHorizon (sliceId : Digest256) : List OpenEvent → Option OpenEvent
  | [] => none
  | e :: es => some (es.foldl (composeEvents sliceId) e)

theorem composeEvents_boundary (sliceId : Digest256) (e₁ e₂ : OpenEvent) :
    (composeEvents sliceId e₁ e₂).boundary = contractBoundary e₁.boundary e₂.boundary := rfl

/-- Multi-step composable causal cone judgment over `OpenEvent` slices: binds output birth
    provenance (`originEvent = eventId`) and forbids re-spending any previously consumed internal
    or external nullifier (`hNoReplay`). -/
inductive ValidHorizonCone (sliceId : Digest256) : List OpenEvent → OpenEvent → Prop where
  | single {e : OpenEvent} (hq : QuiescentValid e)
      (hBirth : ∀ p ∈ e.outPins, p.originEvent = e.eventId) :
      ValidHorizonCone sliceId [e] e
  | snoc {es : List OpenEvent} {macroPrev next : OpenEvent}
      (hPrev : ValidHorizonCone sliceId es macroPrev) (hqNext : QuiescentValid next)
      (hBirth : ∀ p ∈ next.outPins, p.originEvent = next.eventId)
      (hNoReplay : ∀ prev ∈ es, ∀ p ∈ next.inPins, p.nullifier ∉ pinNullifiers prev.inPins)
      (hComp : CausalComposable macroPrev.boundary next.boundary) :
      ValidHorizonCone sliceId (es ++ [next]) (composeEvents sliceId macroPrev next)

/-- **Flagship Theorem (`foldHorizon_quiescent_and_observer_invariant`)**:
    1. Every `ValidHorizonCone` folds to `some macroEv` satisfying all 4 `QuiescentValid` laws AND
       has globally duplicate-free consumed nullifiers across all internal and external steps
       (`(pinNullifiers (es.flatMap OpenEvent.inPins)).Nodup`).
    2. Arbitrary coarse vs. fine partitions `parts : List (List BoundaryPins)` yield identical
       boundary `inPins`, `outPins`, matter totals, capability footprints, and external nullifiers. -/
theorem foldHorizon_quiescent_and_observer_invariant (sliceId : Digest256) :
    (∀ {es : List OpenEvent} {macroEv : OpenEvent},
      ValidHorizonCone sliceId es macroEv →
      foldHorizon sliceId es = some macroEv ∧ QuiescentValid macroEv ∧
      (pinNullifiers (es.flatMap OpenEvent.inPins)).Nodup) ∧
    (∀ (parts : List (List BoundaryPins)),
      PairwiseHorizonDisjoint parts.flatten →
      foldHorizonBoundaries (parts.map foldHorizonBoundaries) =
        foldHorizonBoundaries parts.flatten) := by
  refine ⟨?_, ?_⟩
  · intro es macroEv hCone
    induction hCone with
    | single hq _ =>
      exact ⟨rfl, hq, by simpa using hq.inNullifiersNodup⟩
    | @snoc esPrev prev next _ hqNext _ hNoReplay hComp ih =>
      obtain ⟨hFoldPrev, hqPrev, hNodupAll⟩ := ih
      have hqComp := composeEvents_preserves_quiescent sliceId hqPrev hqNext hComp
      have hNodupNext : (pinNullifiers ((esPrev ++ [next]).flatMap OpenEvent.inPins)).Nodup := by
        simp only [pinNullifiers, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.map_append]
        refine nodup_append_disj hNodupAll hqNext.inNullifiersNodup ?_
        intro nul hInPrev hInNext
        rw [List.mem_map] at hInNext; obtain ⟨p, hpNext, rfl⟩ := hInNext
        rw [List.mem_map] at hInPrev; obtain ⟨q, hqFlat, hqEq⟩ := hInPrev
        rw [List.mem_flatMap] at hqFlat; obtain ⟨evP, hevP, hqEvP⟩ := hqFlat
        have hqMem : q.nullifier ∈ pinNullifiers evP.inPins := List.mem_map_of_mem hqEvP
        rw [hqEq] at hqMem
        exact hNoReplay evP hevP p hpNext hqMem
      cases esPrev with
      | nil => cases hFoldPrev
      | cons hd tl =>
        simp only [foldHorizon, Option.some.injEq] at hFoldPrev
        subst hFoldPrev
        exact ⟨by simp [foldHorizon, List.foldl_append], hqComp, hNodupNext⟩
  · intro parts hDisj
    rw [foldHorizonBoundaries_eq_foldl, foldHorizonBoundaries_eq_foldl]
    suffices gen : ∀ (acc : BoundaryPins) (ps : List (List BoundaryPins)),
        (∀ z ∈ ps.flatten, (∀ p ∈ z.inPins, p ∉ acc.inPins) ∧ (∀ p ∈ acc.outPins, p ∉ z.outPins)) →
        PairwiseHorizonDisjoint ps.flatten →
        (ps.map foldHorizonBoundaries).foldl contractBoundary acc =
          ps.flatten.foldl contractBoundary acc by
      exact gen emptyBoundary parts
        (fun _ _ => ⟨fun _ _ h => List.not_mem_nil h, fun _ h => absurd h List.not_mem_nil⟩) hDisj
    intro acc ps
    induction ps generalizing acc with
    | nil => intros; rfl
    | cons part rest ih =>
      intro hAcc hFlatDisj
      simp only [List.flatten_cons] at hAcc hFlatDisj
      obtain ⟨hPartDisj, hRestDisj, hCross⟩ := pairwiseDisjoint_append_inv hFlatDisj
      rw [List.map_cons, List.foldl_cons, List.flatten_cons, List.foldl_append]
      have hStep : contractBoundary acc (foldHorizonBoundaries part) =
          part.foldl contractBoundary acc := by
        cases part with
        | nil => simp [foldHorizonBoundaries]
        | cons b bs =>
          simp only [foldHorizonBoundaries, List.foldl_cons]
          have hAccB := hAcc b (List.mem_append_left _ List.mem_cons_self)
          have hAccBs : ∀ b' ∈ bs,
              (∀ p ∈ b'.inPins, p ∉ acc.inPins) ∧ (∀ p ∈ acc.outPins, p ∉ b'.outPins) :=
            fun b' hb' => hAcc b' (List.mem_append_left _ (List.mem_cons_of_mem b hb'))
          exact (foldl_contractBoundary_shift acc b bs hAccB.2 hAccBs hPartDisj.1 hPartDisj.2).symm
      rw [hStep]
      apply ih (part.foldl contractBoundary acc) ?_ hRestDisj
      intro z hz
      refine ⟨fun p hp hMem => ?_, fun p hMem hp => ?_⟩
      · rcases mem_inPins_foldl hMem with hInAcc | ⟨x, hx, hpX⟩
        · exact (hAcc z (List.mem_append_right _ hz)).1 p hp hInAcc
        · exact (hCross x hx z hz).1 p hp hpX
      · rcases mem_outPins_foldl hMem with hOutAcc | ⟨x, hx, hpX⟩
        · exact (hAcc z (List.mem_append_right _ hz)).2 p hOutAcc hp
        · exact (hCross x hx z hz).2 p hpX hp

end Obend.Metatheory.PinsAndQuiescence
end
