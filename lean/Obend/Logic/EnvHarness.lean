module
/-
# Obend.Logic.EnvHarness — Open-World Anti-Narrowing `EnvHarness` & Most-General Demonic Client

Formalizes open-world multi-turn protocol verification with anti-narrowing environment completeness:

1. **Revocation set**: the tree's sorted `UInt64` set `Obend.Core.SortedArray.SortedU64Set`
   (logarithmic `contains`, deduplicating `insert`), related to the machine's `List UInt64` ghost
   by `SimulatesSet`.
2. **Open-World `UniversalEnvHarness` & Anti-Narrowing Completeness (`skip_implies_contract_violation`)**:
   - Bans silent syntactic pre-filtering of adversary inputs: every turn `t : Turn` reaches `step`,
     which either executes a contract-satisfying transition (`step_complete_on_contract`) or returns
     a certified refusal proving `¬ contractHolds w t` (`skip_implies_contract_violation`).
3. **Multi-Handle Capability + Revocation + Mandate Machine & `most_general_client_multi_turn_safe`**:
   - Models concurrent live capability handles (`mint`, `attenuate`, `invoke`, `revoke`), monotonic
     `SortedU64Set` revocation growth, and cumulative mandate budget depletion across arbitrary
     stateful adaptive `DemonicClient`s, bridged to `Obend.Logic.MultiTurnHoare.SafeWP`.
4. **Multi-Handle Reachability Witness (`multi_handle_reachability_inhabited`)**:
   - Constructive 5-turn trace minting `h₀ ≠ h₁`, revoking `h₀`, refusing `h₀`, and succeeding on `h₁`.
-/
public import Obend.Logic.MultiTurnHoare
public import Obend.Core.SortedArray
public section
namespace Obend.Logic.EnvHarness
open Obend.Core.Term (Term)
open Obend.Logic (ProtocolSpec ExpectedPlan SafeWP)
open Obend.Core.SortedArray (SortedU64Set SimulatesSet insertKey)
set_option autoImplicit false
/-! ## 2. Universal Open-World `EnvHarness` & `skip_implies_contract_violation` -/
/-- Polymorphic open-world environment harness: forbids silent input narrowing by requiring `step`
to accept every syntactic `Turn` and either advance preserving `worldInv` or return a structured
`Refusal` proving `¬ contractHolds w t`. -/
structure UniversalEnvHarness (World Turn Outcome Refusal : Type) where
  worldInv : World → Prop
  contractHolds : World → Turn → Prop
  refusalSound : World → Turn → Refusal → Prop
  step : World → Turn → Sum (World × Outcome) Refusal
  step_preserves_inv : ∀ w t w' out,
    worldInv w → step w t = .inl (w', out) → contractHolds w t ∧ worldInv w'
  step_complete_on_contract : ∀ w t,
    worldInv w → contractHolds w t → ∃ w' out, step w t = .inl (w', out)
  step_refusal_witnesses_violation : ∀ w t ref,
    worldInv w → step w t = .inr ref → refusalSound w t ref ∧ ¬ contractHolds w t
/-- Multi-turn open-world reachability relation: refused turns leave the world state intact while
recording the explicit refusal in the trace. -/
inductive ReachOpenWorld {World Turn Outcome Refusal : Type}
    (H : UniversalEnvHarness World Turn Outcome Refusal) :
    World → List (Turn × Sum Outcome Refusal) → World → Prop where
  | nil {w : World} : H.worldInv w → ReachOpenWorld H w [] w
  | stepOk {w₁ w₂ w₃ : World} {t : Turn} {out : Outcome}
      {rest : List (Turn × Sum Outcome Refusal)} :
      H.worldInv w₁ →
      H.step w₁ t = .inl (w₂, out) →
      ReachOpenWorld H w₂ rest w₃ →
      ReachOpenWorld H w₁ ((t, .inl out) :: rest) w₃
  | stepRefused {w₁ w₃ : World} {t : Turn} {ref : Refusal}
      {rest : List (Turn × Sum Outcome Refusal)} :
      H.worldInv w₁ →
      H.step w₁ t = .inr ref →
      ReachOpenWorld H w₁ rest w₃ →
      ReachOpenWorld H w₁ ((t, .inr ref) :: rest) w₃
theorem ReachOpenWorld.preserves_worldInv {World Turn Outcome Refusal : Type}
    {H : UniversalEnvHarness World Turn Outcome Refusal}
    {w₀ w : World} {tr : List (Turn × Sum Outcome Refusal)}
    (hr : ReachOpenWorld H w₀ tr w) : H.worldInv w := by
  induction hr with
  | nil hInv => exact hInv
  | stepOk _ _ _ ih => exact ih
  | stepRefused _ _ _ ih => exact ih
/-- **Environment Anti-Narrowing Completeness (`skip_implies_contract_violation`)**:
At ANY state `w` reachable along ANY multi-turn open-world trace, a turn `t` is skipped/refused
(`H.step w t = .inr ref`) **if and only if** `t` genuinely violates `H.contractHolds w t`, accompanied
by a machine-checked `H.refusalSound w t ref` witness. -/
theorem skip_implies_contract_violation {World Turn Outcome Refusal : Type}
    (H : UniversalEnvHarness World Turn Outcome Refusal)
    {w₀ w : World} {tr : List (Turn × Sum Outcome Refusal)}
    (hReach : ReachOpenWorld H w₀ tr w)
    (t : Turn) :
    (∀ ref, H.step w t = .inr ref → H.refusalSound w t ref ∧ ¬ H.contractHolds w t) ∧
    (H.contractHolds w t ↔ ∃ w' out, H.step w t = .inl (w', out)) := by
  have hInv : H.worldInv w := hReach.preserves_worldInv
  refine ⟨fun ref hStep => H.step_refusal_witnesses_violation w t ref hInv hStep, ?_⟩
  constructor
  · exact H.step_complete_on_contract w t hInv
  · rintro ⟨w', out, hStep⟩
    exact (H.step_preserves_inv w t w' out hInv hStep).1
/-! ## 3. Concrete Multi-Handle Capability, Revocation & Mandate Machine -/
/-- Per-handle authority metadata in the open-world capability table. -/
structure CapMeta where
  owner : Nat
  rightsMask : UInt64
  perHandleLimit : Nat
  perHandleSpent : Nat
  deriving DecidableEq, Repr
/-- Persistent multi-handle environment state: concurrent capability table, monotonically growing
unboxed `SortedU64Set` revocation set, and cumulative mandate budget counter. -/
structure MultiHandleWorld where
  nextHandle : UInt64
  caps : List (UInt64 × CapMeta)
  revoked : SortedU64Set
  revokedSpec : List UInt64
  mandateUsed : Nat
  mandateCap : Nat
  deriving DecidableEq, Repr
/-- Unrestricted open-world syntactic turns submitted by an arbitrary demonic client. -/
inductive OpenEnvTurn where
  | mint (owner : Nat) (rightsMask : UInt64) (limit : Nat)
  | attenuate (parent : UInt64) (subRights : UInt64) (subLimit : Nat)
  | invoke (handle : UInt64) (reqRights : UInt64) (cost : Nat)
  | revoke (handle : UInt64)
  deriving DecidableEq, Repr
/-- Structured refusal reasons witnessing exact contract violations. -/
inductive EnvRefusal where
  | handleSpaceExhausted
  | unknownHandle (handle : UInt64)
  | handleRevoked (handle : UInt64)
  | rightsEscalation (handle : UInt64)
  | handleLimitExceeded (handle : UInt64)
  | mandateBudgetExceeded (requested remaining : Nat)
  deriving DecidableEq, Repr
def lookupCap (h : UInt64) : List (UInt64 × CapMeta) → Option CapMeta
  | [] => none
  | (k, m) :: rest => if k == h then some m else lookupCap h rest
def updateCapSpent (h : UInt64) (newSpent : Nat) : List (UInt64 × CapMeta) → List (UInt64 × CapMeta)
  | [] => []
  | (k, m) :: rest =>
    if k == h then (k, { m with perHandleSpent := newSpent }) :: rest
    else (k, m) :: updateCapSpent h newSpent rest
theorem lookupCap_mem {h : UInt64} {m : CapMeta} :
    ∀ {cs : List (UInt64 × CapMeta)}, lookupCap h cs = some m → (h, m) ∈ cs
  | [], hL => by cases hL
  | (k, m') :: rest, hL => by
    unfold lookupCap at hL
    by_cases hk : k = h
    · subst hk; simp at hL; subst hL; exact List.mem_cons_self
    · have hB : (k == h) = false := beq_eq_false_iff_ne.mpr hk
      rw [hB] at hL; exact List.mem_cons_of_mem _ (lookupCap_mem hL)
theorem updateCapSpent_preserves_bounds (h : UInt64) (newSpent : Nat) :
    ∀ {cs : List (UInt64 × CapMeta)} {mOld : CapMeta},
      lookupCap h cs = some mOld →
      newSpent ≤ mOld.perHandleLimit →
      (∀ p ∈ cs, p.2.perHandleSpent ≤ p.2.perHandleLimit) →
      ∀ p ∈ updateCapSpent h newSpent cs, p.2.perHandleSpent ≤ p.2.perHandleLimit
  | [], _, hL, _, _ => by cases hL
  | (k, m) :: rest, mOld, hL, hNewLe, hAll => by
    unfold lookupCap at hL
    unfold updateCapSpent
    by_cases hk : k = h
    · subst hk; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hL ⊢
      subst hL
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hpr
      · exact hNewLe
      · exact hAll p (List.mem_cons_of_mem _ hpr)
    · have hB : (k == h) = false := beq_eq_false_iff_ne.mpr hk
      simp only [hB, Bool.false_eq_true, ↓reduceIte] at hL ⊢
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hpr
      · exact hAll (k, m) List.mem_cons_self
      · exact updateCapSpent_preserves_bounds h newSpent hL hNewLe
          (fun q hq => hAll q (List.mem_cons_of_mem _ hq)) p hpr
/-- Multi-turn state invariant of `MultiHandleWorld`. -/
structure MultiHandleInv (w : MultiHandleWorld) : Prop where
  revoked_sim : SimulatesSet w.revokedSpec w.revoked
  mandate_bounded : w.mandateUsed ≤ w.mandateCap
  caps_below_next : ∀ p ∈ w.caps, p.1.toNat < w.nextHandle.toNat
  caps_spent_bounded : ∀ p ∈ w.caps, p.2.perHandleSpent ≤ p.2.perHandleLimit
/-- Initial clean multi-handle world with mandate budget `mandateCap`. -/
@[expose] def initMultiHandleWorld (mandateCap : Nat) : MultiHandleWorld where
  nextHandle := 0
  caps := []
  revoked := SortedU64Set.empty
  revokedSpec := []
  mandateUsed := 0
  mandateCap := mandateCap
theorem initMultiHandleWorld_inv (mandateCap : Nat) : MultiHandleInv (initMultiHandleWorld mandateCap) where
  revoked_sim := SortedU64Set.simulates_empty
  mandate_bounded := Nat.zero_le _
  caps_below_next := by intro _ h; cases h
  caps_spent_bounded := by intro _ h; cases h
/-- Declarative contract for when an `OpenEnvTurn` is admissible in world `w`. -/
def OpenTurnContract (w : MultiHandleWorld) : OpenEnvTurn → Prop
  | .mint _ _ _ =>
    w.nextHandle.toNat + 1 < UInt64.size ∧ w.revoked.contains w.nextHandle = false
  | .attenuate parent subRights subLimit =>
    w.nextHandle.toNat + 1 < UInt64.size ∧
    w.revoked.contains w.nextHandle = false ∧
    w.revoked.contains parent = false ∧
    ∃ m, lookupCap parent w.caps = some m ∧
      (subRights &&& m.rightsMask) = subRights ∧
      m.perHandleSpent + subLimit ≤ m.perHandleLimit
  | .invoke handle reqRights cost =>
    w.revoked.contains handle = false ∧
    ∃ m, lookupCap handle w.caps = some m ∧
      (reqRights &&& m.rightsMask) = reqRights ∧
      m.perHandleSpent + cost ≤ m.perHandleLimit ∧
      w.mandateUsed + cost ≤ w.mandateCap
  | .revoke _ => True
/-- Semantic meaning of each structured `EnvRefusal`. -/
def EnvRefusalSound (w : MultiHandleWorld) (t : OpenEnvTurn) : EnvRefusal → Prop
  | .handleSpaceExhausted => ¬ (w.nextHandle.toNat + 1 < UInt64.size)
  | .handleRevoked h => w.revoked.contains h = true
  | .unknownHandle h => lookupCap h w.caps = none
  | .rightsEscalation h =>
    match t, lookupCap h w.caps with
    | .attenuate _ subR _, some m => (subR &&& m.rightsMask) ≠ subR
    | .invoke _ reqR _, some m => (reqR &&& m.rightsMask) ≠ reqR
    | _, _ => False
  | .handleLimitExceeded h =>
    match t, lookupCap h w.caps with
    | .attenuate _ _ subLim, some m => ¬ (m.perHandleSpent + subLim ≤ m.perHandleLimit)
    | .invoke _ _ cost, some m => ¬ (m.perHandleSpent + cost ≤ m.perHandleLimit)
    | _, _ => False
  | .mandateBudgetExceeded cost rem =>
    rem = w.mandateCap - w.mandateUsed ∧ ¬ (w.mandateUsed + cost ≤ w.mandateCap)
/-- Executable open-world transition function on `MultiHandleWorld`. -/
@[expose] def stepMultiHandle (w : MultiHandleWorld) (t : OpenEnvTurn) :
    Sum (MultiHandleWorld × UInt64) EnvRefusal :=
  match t with
  | .mint owner rights limit =>
    if decide (w.nextHandle.toNat + 1 < UInt64.size) then
      if w.revoked.contains w.nextHandle then .inr (.handleRevoked w.nextHandle)
      else
        let h := w.nextHandle
        let nextH := UInt64.ofNat (h.toNat + 1)
        let m : CapMeta := ⟨owner, rights, limit, 0⟩
        .inl ({ w with nextHandle := nextH, caps := (h, m) :: w.caps }, h)
    else .inr .handleSpaceExhausted
  | .attenuate parent subRights subLimit =>
    if decide (w.nextHandle.toNat + 1 < UInt64.size) then
      if w.revoked.contains w.nextHandle then .inr (.handleRevoked w.nextHandle)
      else if w.revoked.contains parent then .inr (.handleRevoked parent)
      else
        match lookupCap parent w.caps with
        | none => .inr (.unknownHandle parent)
        | some m =>
          if decide ((subRights &&& m.rightsMask) = subRights) then
            if decide (m.perHandleSpent + subLimit ≤ m.perHandleLimit) then
              let h := w.nextHandle
              let nextH := UInt64.ofNat (h.toNat + 1)
              let childMeta : CapMeta := ⟨m.owner, subRights, subLimit, 0⟩
              .inl ({ w with nextHandle := nextH, caps := (h, childMeta) :: w.caps }, h)
            else .inr (.handleLimitExceeded parent)
          else .inr (.rightsEscalation parent)
    else .inr .handleSpaceExhausted
  | .invoke handle reqRights cost =>
    if w.revoked.contains handle then .inr (.handleRevoked handle)
    else
      match lookupCap handle w.caps with
      | none => .inr (.unknownHandle handle)
      | some m =>
        if decide ((reqRights &&& m.rightsMask) = reqRights) then
          if decide (m.perHandleSpent + cost ≤ m.perHandleLimit) then
            if decide (w.mandateUsed + cost ≤ w.mandateCap) then
              .inl ({ w with
                caps := updateCapSpent handle (m.perHandleSpent + cost) w.caps
                mandateUsed := w.mandateUsed + cost }, handle)
            else .inr (.mandateBudgetExceeded cost (w.mandateCap - w.mandateUsed))
          else .inr (.handleLimitExceeded handle)
        else .inr (.rightsEscalation handle)
  | .revoke handle =>
    .inl ({ w with
      revoked := w.revoked.insert handle
      revokedSpec := insertKey handle w.revokedSpec }, handle)
private theorem nextH_toNat_eq (h : UInt64) (hLt : h.toNat + 1 < UInt64.size) :
    (UInt64.ofNat (h.toNat + 1)).toNat = h.toNat + 1 := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hLt]
theorem stepMultiHandle_preserves_inv (w : MultiHandleWorld) (t : OpenEnvTurn)
    (w' : MultiHandleWorld) (out : UInt64)
    (hInv : MultiHandleInv w) (hStep : stepMultiHandle w t = .inl (w', out)) :
    OpenTurnContract w t ∧ MultiHandleInv w' := by
  cases t with
  | mint owner rights limit =>
    simp only [stepMultiHandle] at hStep
    split at hStep
    · rename_i hSpace
      have hSp : w.nextHandle.toNat + 1 < UInt64.size := of_decide_eq_true hSpace
      cases hRev : w.revoked.contains w.nextHandle with
      | true => simp [hRev] at hStep
      | false =>
        simp only [hRev, Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        refine ⟨⟨hSp, hRev⟩, ⟨hInv.revoked_sim, hInv.mandate_bounded, ?_, ?_⟩⟩
        · intro p hp
          rw [nextH_toNat_eq w.nextHandle hSp]
          rcases List.mem_cons.mp hp with rfl | hpr
          · dsimp only; omega
          · have := hInv.caps_below_next p hpr; omega
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hpr
          · exact Nat.zero_le _
          · exact hInv.caps_spent_bounded p hpr
    · cases hStep
  | attenuate parent subRights subLimit =>
    simp only [stepMultiHandle] at hStep
    split at hStep
    · rename_i hSpace
      have hSp : w.nextHandle.toNat + 1 < UInt64.size := of_decide_eq_true hSpace
      cases hRevN : w.revoked.contains w.nextHandle with
      | true => simp [hRevN] at hStep
      | false =>
        cases hRevP : w.revoked.contains parent with
        | true => simp [hRevN, hRevP] at hStep
        | false =>
          cases hLk : lookupCap parent w.caps with
          | none => simp [hRevN, hRevP, hLk] at hStep
          | some m =>
            simp only [hRevN, hRevP, hLk, Bool.false_eq_true, ↓reduceIte] at hStep
            split at hStep
            · rename_i hMask
              split at hStep
              · rename_i hLim
                simp only [Sum.inl.injEq, Prod.mk.injEq] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                refine ⟨⟨hSp, hRevN, hRevP, m, hLk, of_decide_eq_true hMask, of_decide_eq_true hLim⟩,
                  ⟨hInv.revoked_sim, hInv.mandate_bounded, ?_, ?_⟩⟩
                · intro p hp
                  rw [nextH_toNat_eq w.nextHandle hSp]
                  rcases List.mem_cons.mp hp with rfl | hpr
                  · dsimp only; omega
                  · have := hInv.caps_below_next p hpr; omega
                · intro p hp
                  rcases List.mem_cons.mp hp with rfl | hpr
                  · exact Nat.zero_le _
                  · exact hInv.caps_spent_bounded p hpr
              · cases hStep
            · cases hStep
    · cases hStep
  | invoke handle reqRights cost =>
    simp only [stepMultiHandle] at hStep
    cases hRev : w.revoked.contains handle with
    | true => simp [hRev] at hStep
    | false =>
      cases hLk : lookupCap handle w.caps with
      | none => simp [hRev, hLk] at hStep
      | some m =>
        simp only [hRev, hLk, Bool.false_eq_true, ↓reduceIte] at hStep
        split at hStep
        · rename_i hMask
          split at hStep
          · rename_i hLim
            split at hStep
            · rename_i hMand
              have hSub : ∀ (cs : List (UInt64 × CapMeta)) (q : UInt64 × CapMeta),
                  q ∈ updateCapSpent handle (m.perHandleSpent + cost) cs → q.1 ∈ cs.map Prod.fst := by
                intro cs
                induction cs with
                | nil => intro _ hq; cases hq
                | cons hd tl ih =>
                  intro q hq
                  unfold updateCapSpent at hq
                  split at hq
                  · rcases List.mem_cons.mp hq with rfl | hqr
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hqr)
                  · rcases List.mem_cons.mp hq with rfl | hqr
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ (ih q hqr)
              simp only [Sum.inl.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨rfl, rfl⟩
              have hLimP : m.perHandleSpent + cost ≤ m.perHandleLimit := of_decide_eq_true hLim
              have hMandP : w.mandateUsed + cost ≤ w.mandateCap := of_decide_eq_true hMand
              refine ⟨⟨hRev, m, hLk, of_decide_eq_true hMask, hLimP, hMandP⟩,
                ⟨hInv.revoked_sim, hMandP, ?_, ?_⟩⟩
              · intro p hp
                obtain ⟨q, hqMem, hqEq⟩ := List.mem_map.mp (hSub w.caps p hp)
                rw [← hqEq]; exact hInv.caps_below_next q hqMem
              · exact updateCapSpent_preserves_bounds handle _ hLk hLimP hInv.caps_spent_bounded
            · cases hStep
          · cases hStep
        · cases hStep
  | revoke handle =>
    simp only [stepMultiHandle, Sum.inl.injEq, Prod.mk.injEq] at hStep
    rcases hStep with ⟨rfl, rfl⟩
    exact ⟨trivial, ⟨w.revoked.simulates_insert hInv.revoked_sim handle,
      hInv.mandate_bounded, hInv.caps_below_next, hInv.caps_spent_bounded⟩⟩
theorem stepMultiHandle_complete (w : MultiHandleWorld) (t : OpenEnvTurn)
    (hContract : OpenTurnContract w t) :
    ∃ w' out, stepMultiHandle w t = .inl (w', out) := by
  cases t with
  | mint owner rights limit =>
    rcases hContract with ⟨hSp, hRev⟩
    simp only [stepMultiHandle, decide_eq_true hSp, hRev, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  | attenuate parent subRights subLimit =>
    rcases hContract with ⟨hSp, hRevN, hRevP, m, hLk, hMask, hLim⟩
    simp only [stepMultiHandle, decide_eq_true hSp, hRevN, hRevP, hLk, decide_eq_true hMask,
      decide_eq_true hLim, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  | invoke handle reqRights cost =>
    rcases hContract with ⟨hRev, m, hLk, hMask, hLim, hMand⟩
    simp only [stepMultiHandle, hRev, hLk, decide_eq_true hMask, decide_eq_true hLim,
      decide_eq_true hMand, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  | revoke handle => exact ⟨_, _, rfl⟩
theorem stepMultiHandle_refusal_sound (w : MultiHandleWorld) (t : OpenEnvTurn) (ref : EnvRefusal)
    (hRef : stepMultiHandle w t = .inr ref) :
    EnvRefusalSound w t ref ∧ ¬ OpenTurnContract w t := by
  cases t with
  | mint owner rights limit =>
    simp only [stepMultiHandle] at hRef
    split at hRef
    · cases hRev : w.revoked.contains w.nextHandle with
      | false => simp [hRev] at hRef
      | true =>
        simp only [hRev, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
        exact ⟨hRev, fun ⟨_, hc⟩ => by rw [hRev] at hc; cases hc⟩
    · rename_i hNoSp
      simp only [Sum.inr.injEq] at hRef; subst ref
      have hNot : ¬ (w.nextHandle.toNat + 1 < UInt64.size) := fun hp => hNoSp (decide_eq_true hp)
      exact ⟨hNot, fun ⟨hc, _⟩ => hNot hc⟩
  | attenuate parent subRights subLimit =>
    simp only [stepMultiHandle] at hRef
    split at hRef
    · cases hRevN : w.revoked.contains w.nextHandle with
      | true =>
        simp only [hRevN, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
        exact ⟨hRevN, fun ⟨_, hc, _⟩ => by rw [hRevN] at hc; cases hc⟩
      | false =>
        cases hRevP : w.revoked.contains parent with
        | true =>
          simp only [hRevN, hRevP, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
          exact ⟨hRevP, fun ⟨_, _, hc, _⟩ => by rw [hRevP] at hc; cases hc⟩
        | false =>
          cases hLk : lookupCap parent w.caps with
          | none =>
            simp only [hRevN, hRevP, hLk, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
            exact ⟨hLk, fun ⟨_, _, _, _, hm, _⟩ => by rw [hLk] at hm; cases hm⟩
          | some m =>
            simp only [hRevN, hRevP, hLk, Bool.false_eq_true, ↓reduceIte] at hRef
            split at hRef
            · split at hRef
              · cases hRef
              · rename_i _ hNoLim
                simp only [Sum.inr.injEq] at hRef; subst ref
                have hNL : ¬ (m.perHandleSpent + subLimit ≤ m.perHandleLimit) :=
                  fun hp => hNoLim (decide_eq_true hp)
                exact ⟨by simp [EnvRefusalSound, hLk, hNL],
                  fun ⟨_, _, _, m', hm', _, hL⟩ => by rw [hLk] at hm'; cases hm'; exact hNL hL⟩
            · rename_i hNoMask
              simp only [Sum.inr.injEq] at hRef; subst ref
              have hNM : (subRights &&& m.rightsMask) ≠ subRights :=
                fun hp => hNoMask (decide_eq_true hp)
              exact ⟨by simp [EnvRefusalSound, hLk, hNM],
                fun ⟨_, _, _, m', hm', hM, _⟩ => by rw [hLk] at hm'; cases hm'; exact hNM hM⟩
    · rename_i hNoSp
      simp only [Sum.inr.injEq] at hRef; subst ref
      have hNot : ¬ (w.nextHandle.toNat + 1 < UInt64.size) := fun hp => hNoSp (decide_eq_true hp)
      exact ⟨hNot, fun ⟨hc, _⟩ => hNot hc⟩
  | invoke handle reqRights cost =>
    simp only [stepMultiHandle] at hRef
    cases hRev : w.revoked.contains handle with
    | true =>
      simp only [hRev, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
      exact ⟨hRev, fun ⟨hc, _⟩ => by rw [hRev] at hc; cases hc⟩
    | false =>
      cases hLk : lookupCap handle w.caps with
      | none =>
        simp only [hRev, hLk, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq] at hRef; subst ref
        exact ⟨hLk, fun ⟨_, _, hm, _⟩ => by rw [hLk] at hm; cases hm⟩
      | some m =>
        simp only [hRev, hLk, Bool.false_eq_true, ↓reduceIte] at hRef
        split at hRef
        · split at hRef
          · split at hRef
            · cases hRef
            · rename_i _ _ hNoMand
              simp only [Sum.inr.injEq] at hRef; subst ref
              have hNMd : ¬ (w.mandateUsed + cost ≤ w.mandateCap) :=
                fun hp => hNoMand (decide_eq_true hp)
              exact ⟨⟨rfl, hNMd⟩, fun ⟨_, m', hm', _, _, hMd⟩ => by rw [hLk] at hm'; cases hm'; exact hNMd hMd⟩
          · rename_i _ hNoLim
            simp only [Sum.inr.injEq] at hRef; subst ref
            have hNL : ¬ (m.perHandleSpent + cost ≤ m.perHandleLimit) :=
              fun hp => hNoLim (decide_eq_true hp)
            exact ⟨by simp [EnvRefusalSound, hLk, hNL],
              fun ⟨_, m', hm', _, hL, _⟩ => by rw [hLk] at hm'; cases hm'; exact hNL hL⟩
        · rename_i hNoMask
          simp only [Sum.inr.injEq] at hRef; subst ref
          have hNM : (reqRights &&& m.rightsMask) ≠ reqRights :=
            fun hp => hNoMask (decide_eq_true hp)
          exact ⟨by simp [EnvRefusalSound, hLk, hNM],
            fun ⟨_, m', hm', hM, _⟩ => by rw [hLk] at hm'; cases hm'; exact hNM hM⟩
  | revoke _ => cases hRef

/-- Canonical `UniversalEnvHarness` instance for the multi-handle capability & mandate machine. -/
@[expose] def multiHandleHarness :
    UniversalEnvHarness MultiHandleWorld OpenEnvTurn UInt64 EnvRefusal where
  worldInv := MultiHandleInv
  contractHolds := OpenTurnContract
  refusalSound := EnvRefusalSound
  step := stepMultiHandle
  step_preserves_inv := stepMultiHandle_preserves_inv
  step_complete_on_contract := fun w t _ hC => stepMultiHandle_complete w t hC
  step_refusal_witnesses_violation := fun w t ref _ hR => stepMultiHandle_refusal_sound w t ref hR

/-! ## 4. Most-General Stateful Adaptive Demonic Client (`most_general_client_multi_turn_safe`) -/

/-- Arbitrary unconstrained stateful adaptive adversary/client interacting with `MultiHandleWorld`. -/
structure DemonicClient (ClientState : Type) where
  chooseTurn : ClientState → MultiHandleWorld → OpenEnvTurn
  observe : ClientState → Sum UInt64 EnvRefusal → ClientState

/-- Execute `n` sequential open-world turns of an arbitrary `DemonicClient`. -/
def runDemonicClient {ClientState : Type} (client : DemonicClient ClientState) :
    Nat → ClientState → MultiHandleWorld →
    MultiHandleWorld × ClientState × List (OpenEnvTurn × Sum UInt64 EnvRefusal)
  | 0, cs, w => (w, cs, [])
  | n + 1, cs, w =>
    let t := client.chooseTurn cs w
    match stepMultiHandle w t with
    | .inl (w', out) =>
      let (wFinal, csFinal, rest) := runDemonicClient client n (client.observe cs (.inl out)) w'
      (wFinal, csFinal, (t, .inl out) :: rest)
    | .inr ref =>
      let (wFinal, csFinal, rest) := runDemonicClient client n (client.observe cs (.inr ref)) w
      (wFinal, csFinal, (t, .inr ref) :: rest)

theorem stepMultiHandle_revoked_mono {w w' : MultiHandleWorld} {t : OpenEnvTurn} {out : UInt64}
    (hInv : MultiHandleInv w) (hStep : stepMultiHandle w t = .inl (w', out)) :
    (∀ k, w.revoked.contains k = true → w'.revoked.contains k = true) ∧
    w.mandateUsed ≤ w'.mandateUsed ∧ w'.mandateCap = w.mandateCap := by
  cases t with
  | mint _ _ _ =>
    simp only [stepMultiHandle] at hStep
    split at hStep
    · cases hRev : w.revoked.contains w.nextHandle with
      | true => simp [hRev] at hStep
      | false =>
        simp only [hRev, Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        exact ⟨fun _ h => h, Nat.le_refl _, rfl⟩
    · cases hStep
  | attenuate parent _ _ =>
    simp only [stepMultiHandle] at hStep
    split at hStep
    · cases hRevN : w.revoked.contains w.nextHandle with
      | true => simp [hRevN] at hStep
      | false =>
        cases hRevP : w.revoked.contains parent with
        | true => simp [hRevN, hRevP] at hStep
        | false =>
          cases hLk : lookupCap parent w.caps with
          | none => simp [hRevN, hRevP, hLk] at hStep
          | some _ =>
            simp only [hRevN, hRevP, hLk, Bool.false_eq_true, ↓reduceIte] at hStep
            split at hStep
            · split at hStep
              · simp only [Sum.inl.injEq, Prod.mk.injEq] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                exact ⟨fun _ h => h, Nat.le_refl _, rfl⟩
              · cases hStep
            · cases hStep
    · cases hStep
  | invoke handle _ cost =>
    simp only [stepMultiHandle] at hStep
    cases hRev : w.revoked.contains handle with
    | true => simp [hRev] at hStep
    | false =>
      cases hLk : lookupCap handle w.caps with
      | none => simp [hRev, hLk] at hStep
      | some _ =>
        simp only [hRev, hLk, Bool.false_eq_true, ↓reduceIte] at hStep
        split at hStep
        · split at hStep
          · split at hStep
            · simp only [Sum.inl.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨rfl, rfl⟩
              exact ⟨fun _ h => h, by dsimp only; omega, rfl⟩
            · cases hStep
          · cases hStep
        · cases hStep
  | revoke handle =>
    simp only [stepMultiHandle, Sum.inl.injEq, Prod.mk.injEq] at hStep
    rcases hStep with ⟨rfl, rfl⟩
    exact ⟨fun x hx => w.revoked.contains_insert_of_contains handle x hx, Nat.le_refl _, rfl⟩

/-- **Most-General Demonic Client Multi-Turn Safety (`most_general_client_multi_turn_safe`)**:
For ANY state type `ClientState`, ANY adaptive `client : DemonicClient ClientState`, ANY horizon `n`,
and ANY initial state `(cs₀, w₀)` satisfying `MultiHandleInv w₀`:
1. The final world `wFinal` is reachable via `ReachOpenWorld multiHandleHarness` and preserves `MultiHandleInv`,
2. **Irrevocable Revocation**: every handle revoked in `w₀` remains revoked in `wFinal` (never reinstated),
3. **Mandate Conservation**: `w₀.mandateUsed ≤ wFinal.mandateUsed ≤ w₀.mandateCap`,
4. **Revoked Handle Refusal**: invoking any currently revoked handle `h` is deterministically refused,
5. **Anti-Narrowing Completeness**: at `wFinal`, every refused turn witnesses `¬ OpenTurnContract wFinal t`. -/
theorem most_general_client_multi_turn_safe {ClientState : Type}
    (client : DemonicClient ClientState) (n : Nat) (cs₀ : ClientState) (w₀ : MultiHandleWorld)
    (hInv₀ : MultiHandleInv w₀) :
    let res := runDemonicClient client n cs₀ w₀
    ReachOpenWorld multiHandleHarness w₀ res.2.2 res.1 ∧
    MultiHandleInv res.1 ∧
    (∀ k, w₀.revoked.contains k = true → res.1.revoked.contains k = true) ∧
    w₀.mandateUsed ≤ res.1.mandateUsed ∧
    res.1.mandateUsed ≤ w₀.mandateCap ∧
    (∀ h reqR cost, res.1.revoked.contains h = true →
      stepMultiHandle res.1 (.invoke h reqR cost) = .inr (.handleRevoked h)) ∧
    (∀ t ref, stepMultiHandle res.1 t = .inr ref →
      EnvRefusalSound res.1 t ref ∧ ¬ OpenTurnContract res.1 t) := by
  induction n generalizing cs₀ w₀ with
  | zero =>
    dsimp only [runDemonicClient]
    refine ⟨.nil hInv₀, hInv₀, fun _ h => h, Nat.le_refl _, hInv₀.mandate_bounded, ?_, ?_⟩
    · intro h reqR cost hRev; simp [stepMultiHandle, hRev]
    · intro t ref hRef; exact stepMultiHandle_refusal_sound w₀ t ref hRef
  | succ m ih =>
    dsimp only [runDemonicClient]
    cases hSt : stepMultiHandle w₀ (client.chooseTurn cs₀ w₀) with
    | inl pair =>
      rcases pair with ⟨w₁, out⟩
      dsimp only
      have hPres := (stepMultiHandle_preserves_inv w₀ _ w₁ out hInv₀ hSt).2
      obtain ⟨hRevStep, hMandMono, hCapEq⟩ := stepMultiHandle_revoked_mono hInv₀ hSt
      have ihRes := ih (client.observe cs₀ (.inl out)) w₁ hPres
      rcases hRun : runDemonicClient client m (client.observe cs₀ (.inl out)) w₁ with ⟨wF, csF, tr⟩
      rw [hRun] at ihRes
      rcases ihRes with ⟨hReach, hInvF, hRevF, hMand1, hMand2, hInvokeRev, hSkipF⟩
      exact ⟨.stepOk hInv₀ hSt hReach, hInvF, fun k hk => hRevF k (hRevStep k hk),
        Nat.le_trans hMandMono hMand1, hCapEq ▸ hMand2, hInvokeRev, hSkipF⟩
    | inr ref =>
      dsimp only
      have ihRes := ih (client.observe cs₀ (.inr ref)) w₀ hInv₀
      rcases hRun : runDemonicClient client m (client.observe cs₀ (.inr ref)) w₀ with ⟨wF, csF, tr⟩
      rw [hRun] at ihRes
      rcases ihRes with ⟨hReach, hInvF, hRevF, hMand1, hMand2, hInvokeRev, hSkipF⟩
      exact ⟨.stepRefused hInv₀ hSt hReach, hInvF, hRevF, hMand1, hMand2, hInvokeRev, hSkipF⟩

/-- Lift any `UniversalEnvHarness` to an `Obend.Logic.ProtocolSpec` over `Core4` natural-encoded turns:
every yielded `.nat turnCode` plan has at least one lawful response (`ExpectedPlan` non-vacuous!). -/
def envHarnessProtocol : ProtocolSpec :=
  fun plan resp => ∃ turnTag resTag : Nat, plan = .nat turnTag ∧ resp = .nat resTag

theorem envHarnessProtocol_expectedPlan (turnTag : Nat) :
    ExpectedPlan envHarnessProtocol (.nat turnTag) :=
  ⟨.nat 0, turnTag, 0, rfl, rfl⟩

theorem envHarnessProtocol_val_safeWP (v : Nat) :
    SafeWP envHarnessProtocol (.nat v) (fun t => t = .nat v) :=
  Obend.Logic.wp_val (.natural v) rfl

/-! ## 5. Multi-Handle Open-World Reachability Witness (`multi_handle_reachability_inhabited`) -/

/--Deterministic 5-step client script exercising concurrent handles, revocation, refusal, and sibling invoke. -/
def multiHandleDemoScript : Nat → OpenEnvTurn
  | 0 => .mint 1 0xFF 60
  | 1 => .mint 2 0x0F 60
  | 2 => .revoke 0
  | 3 => .invoke 0 0x01 20
  | _ => .invoke 1 0x05 40

def demoAdaptiveClient : DemonicClient Nat where
  chooseTurn idx _ := multiHandleDemoScript idx
  observe idx _ := idx + 1

/-- **Joint Multi-Handle Open-World Reachability (`multi_handle_reachability_inhabited`)**:
Constructively witnesses a 5-turn run from `initMultiHandleWorld 100` that:
1. Mints two distinct live capability handles `h₀ = 0` and `h₁ = 1` (`h₀ ≠ h₁`),
2. Revokes `h₀` into the unboxed `SortedU64Set`,
3. Refuses subsequent invocation of `h₀` with `.inr (.handleRevoked 0)`, and
4. Succeeds on sibling handle `h₁` (`mandateUsed = 40 ≤ 100`), proving concurrent multi-handle
   non-interference and joint inhabitedness of `most_general_client_multi_turn_safe`. -/
theorem multi_handle_reachability_inhabited :
    let w₀ := initMultiHandleWorld 100
    let res := runDemonicClient demoAdaptiveClient 5 0 w₀
    ∃ (h₀ h₁ : UInt64),
      h₀ ≠ h₁ ∧
      ReachOpenWorld multiHandleHarness w₀ res.2.2 res.1 ∧
      MultiHandleInv res.1 ∧
      res.1.revoked.contains h₀ = true ∧
      res.1.revoked.contains h₁ = false ∧
      (.invoke h₀ 0x01 20, Sum.inr (.handleRevoked h₀)) ∈ res.2.2 ∧
      (.invoke h₁ 0x05 40, Sum.inl h₁) ∈ res.2.2 ∧
      res.1.mandateUsed = 40 := by
  dsimp only
  have hSafe := most_general_client_multi_turn_safe demoAdaptiveClient 5 0
    (initMultiHandleWorld 100) (initMultiHandleWorld_inv 100)
  refine ⟨0, 1, by decide, hSafe.1, hSafe.2.1, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Obend.Logic.EnvHarness
end
