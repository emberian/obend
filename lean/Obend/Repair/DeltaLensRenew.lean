module
/-
# Obend.Repair.DeltaLensRenew — lenses, step framing, and certificates renewed across a richer state

A state record grows: a field is added, a record is nested in a larger one. What was proved about
the old record `V` should hold of the new one `S` without being proved again. The evolution is a
lens `DeltaLens S V`: `get` reads the old record out of the new one, `put` writes it back.

A `DeltaLens` here is Clarke's asymmetric delta lens between codiscrete categories of states: a
delta out of `get s` is its target `v`, its lift is `put s v`, and the three laws are that the
identity delta lifts to the identity (`get_put`), a lift lies over its delta (`put_get`), and a
composite lifts to the composite (`put_put`). Equivalently it is a coalgebra of the store comonad
(`coalg`, `extract_coalg`, `duplicate_coalg`, `ofCoalg`).

* **Algebra.** `DeltaLens.id`, `comp`, `fst`, `snd`; `DisjointLenses` (the two `put`s commute), from
  which each `get` ignores the other's `put` (`get_left_put_right`) and the two pair into one lens
  (`DisjointLenses.pair`).
* **Step framing.** A step of the view lifts to the state (`modify`, `liftStep` for a relation);
  `get` carries the lifted step to the step (`get_modify`, `liftStep_lifts`), and a disjoint
  component is unchanged by it (`frame_modify`, `frame_run`, `liftStep_frame`).
* **Claims** (`Obend.Logic.Frame`). A claim certificate accepted for a composition is accepted for
  the composition read out of the richer state (`renewClaimAcrossLens`), stays accepted when a
  disjoint component changes (`renewClaimAcrossLens_frame`), and when the composition itself is
  replaced by one with the same supports (`renewClaimAcrossLens_evolve`, through `claim_frame`). The
  derivation is never replayed.
* **Intentions** (`Obend.Intention`). An intention over `V` is one over `S` (`liftIntention`); a
  renewal made at a view is a usable, current fill at every state holding that view
  (`renewIntentionAcrossLens`), and a pin stays current across a disjoint change
  (`liftIntention_frame`, `liftIntention_stays`).
-/
public import Obend.Logic.Frame
public import Obend.Intention
public section
namespace Obend.Repair
set_option autoImplicit false

universe u v w v₁ v₂

/-! ## 1. Lenses -/

/-- A lens from a state `S` onto a view `V`. -/
structure DeltaLens (S : Type u) (V : Type v) where
  /-- the view of a state -/
  get : S → V
  /-- the state with its view replaced -/
  put : S → V → S
  /-- writing back what was read changes nothing -/
  get_put : ∀ s, put s (get s) = s
  /-- what was written is what is read -/
  put_get : ∀ s v, get (put s v) = v
  /-- a second write overwrites the first -/
  put_put : ∀ s v₁ v₂, put (put s v₁) v₂ = put s v₂

namespace DeltaLens
variable {S : Type u} {V : Type v} {W : Type w}

/-- The whole state as its own view. -/
@[expose] protected def id (S : Type u) : DeltaLens S S where
  get s := s
  put _ v := v
  get_put _ := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- A view of a view. -/
@[expose] def comp (outer : DeltaLens S V) (inner : DeltaLens V W) : DeltaLens S W where
  get s := inner.get (outer.get s)
  put s x := outer.put s (inner.put (outer.get s) x)
  get_put s := by rw [inner.get_put, outer.get_put]
  put_get s x := by rw [outer.put_get, inner.put_get]
  put_put s x₁ x₂ := by rw [outer.put_get, outer.put_put, inner.put_put]

/-- The first component of a pair. -/
@[expose] def fst (A : Type u) (B : Type v) : DeltaLens (A × B) A where
  get s := s.1
  put s a := (a, s.2)
  get_put _ := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- The second component of a pair. -/
@[expose] def snd (A : Type u) (B : Type v) : DeltaLens (A × B) B where
  get s := s.2
  put s b := (s.1, b)
  get_put _ := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- A step of the view, made on the state. -/
@[expose] def modify (L : DeltaLens S V) (f : V → V) (s : S) : S := L.put s (f (L.get s))

/-- **`get` carries the lifted step to the step.** -/
theorem get_modify (L : DeltaLens S V) (f : V → V) (s : S) : L.get (L.modify f s) = f (L.get s) :=
  L.put_get s _

theorem modify_id (L : DeltaLens S V) (s : S) : L.modify (fun v => v) s = s := L.get_put s

theorem modify_comp (L : DeltaLens S V) (f g : V → V) (s : S) :
    L.modify g (L.modify f s) = L.modify (fun v => g (f v)) s := by
  simp only [modify]
  rw [L.put_get, L.put_put]

/-- A step relation of the view, on the state: the view steps and nothing else is written. -/
@[expose] def liftStep (L : DeltaLens S V) (R : V → V → Prop) (s s' : S) : Prop :=
  R (L.get s) (L.get s') ∧ s' = L.put s (L.get s')

/-- A lifted step is a step of the view. -/
theorem liftStep_get {L : DeltaLens S V} {R : V → V → Prop} {s s' : S} (h : L.liftStep R s s') :
    R (L.get s) (L.get s') := h.1

/-- **Every step of the view lifts**, to exactly one state. -/
theorem liftStep_lifts (L : DeltaLens S V) (R : V → V → Prop) (s : S) {v' : V} (h : R (L.get s) v') :
    L.liftStep R s (L.put s v') ∧ ∀ s', L.liftStep R s s' → L.get s' = v' → s' = L.put s v' :=
  ⟨⟨by rw [L.put_get]; exact h, by rw [L.put_get]⟩, fun _ hs e => e ▸ hs.2⟩

/-! ### The store comonad -/

/-- The store comonad at `V`: a position and a state for every position. -/
structure Store (V : Type v) (X : Type u) where
  pos : V
  peek : V → X

namespace Store
variable {X : Type u} {Y : Type w}

@[expose] def extract (c : Store V X) : X := c.peek c.pos
@[expose] def map (f : X → Y) (c : Store V X) : Store V Y := ⟨c.pos, fun v => f (c.peek v)⟩
@[expose] def duplicate (c : Store V X) : Store V (Store V X) := ⟨c.pos, fun v => ⟨v, c.peek⟩⟩

end Store

/-- A lens as a coalgebra of the store comonad. -/
@[expose] def coalg (L : DeltaLens S V) (s : S) : Store V S := ⟨L.get s, L.put s⟩

/-- The counit law is `get_put`. -/
theorem extract_coalg (L : DeltaLens S V) (s : S) : (L.coalg s).extract = s := L.get_put s

/-- The comultiplication law is `put_get` with `put_put`. -/
theorem duplicate_coalg (L : DeltaLens S V) (s : S) : (L.coalg s).duplicate = (L.coalg s).map L.coalg := by
  simp only [coalg, Store.duplicate, Store.map]
  congr 1
  funext v
  rw [L.put_get]
  congr 1
  funext v₂
  rw [L.put_put]

/-- **A coalgebra of the store comonad is a lens.** -/
@[expose] def ofCoalg (c : S → Store V S) (h₁ : ∀ s, (c s).extract = s)
    (h₂ : ∀ s, (c s).duplicate = (c s).map c) : DeltaLens S V where
  get s := (c s).pos
  put s v := (c s).peek v
  get_put := h₁
  put_get s v := (congrArg (fun d : Store V (Store V S) => (d.peek v).pos) (h₂ s)).symm
  put_put s v₁ v₂ := (congrArg (fun d : Store V (Store V S) => (d.peek v₁).peek v₂) (h₂ s)).symm

theorem ofCoalg_coalg (L : DeltaLens S V) :
    ofCoalg L.coalg L.extract_coalg L.duplicate_coalg = L := rfl

end DeltaLens

/-! ## 2. Disjoint lenses and the frame -/

/-- Two lenses on one state that do not overlap: their writes commute. -/
structure DisjointLenses {S : Type u} {V₁ : Type v₁} {V₂ : Type v₂} (L₁ : DeltaLens S V₁)
    (L₂ : DeltaLens S V₂) : Prop where
  comm : ∀ s a b, L₁.put (L₂.put s b) a = L₂.put (L₁.put s a) b

namespace DisjointLenses
variable {S : Type u} {V₁ : Type v₁} {V₂ : Type v₂} {L₁ : DeltaLens S V₁} {L₂ : DeltaLens S V₂}

theorem symm (h : DisjointLenses L₁ L₂) : DisjointLenses L₂ L₁ := ⟨fun s b a => (h.comm s a b).symm⟩

/-- **The frame**: a write through one lens is not seen through the other. -/
theorem get_left_put_right (h : DisjointLenses L₁ L₂) (s : S) (b : V₂) : L₁.get (L₂.put s b) = L₁.get s := by
  have e : L₂.put s b = L₁.put (L₂.put s b) (L₁.get s) := by
    rw [h.comm, L₁.get_put]
  rw [e, L₁.put_get]

theorem get_right_put_left (h : DisjointLenses L₁ L₂) (s : S) (a : V₁) : L₂.get (L₁.put s a) = L₂.get s :=
  h.symm.get_left_put_right s a

/-- **A step lifted through one lens frames the other.** -/
theorem frame_modify (h : DisjointLenses L₁ L₂) (f : V₂ → V₂) (s : S) : L₁.get (L₂.modify f s) = L₁.get s :=
  h.get_left_put_right s _

/-- Along any run of steps lifted through one lens, the other's view is unchanged. -/
theorem frame_run (h : DisjointLenses L₁ L₂) (fs : List (V₂ → V₂)) (s : S) :
    L₁.get (fs.foldl (fun s f => L₂.modify f s) s) = L₁.get s := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih => rw [List.foldl_cons, ih, h.frame_modify]

/-- An invariant of one view survives any step lifted through the other. -/
theorem frame_inv (h : DisjointLenses L₁ L₂) (P : V₁ → Prop) (f : V₂ → V₂) {s : S} (hp : P (L₁.get s)) :
    P (L₁.get (L₂.modify f s)) := by
  rw [h.frame_modify]
  exact hp

/-- A relational step lifted through one lens frames the other. -/
theorem liftStep_frame (h : DisjointLenses L₁ L₂) {R : V₂ → V₂ → Prop} {s s' : S} (hs : L₂.liftStep R s s') :
    L₁.get s' = L₁.get s := by
  rw [hs.2, h.get_left_put_right]

/-- Steps lifted through disjoint lenses commute. -/
theorem modify_comm (h : DisjointLenses L₁ L₂) (f : V₁ → V₁) (g : V₂ → V₂) (s : S) :
    L₁.modify f (L₂.modify g s) = L₂.modify g (L₁.modify f s) := by
  simp only [DeltaLens.modify]
  rw [h.get_left_put_right, h.get_right_put_left, h.comm]

/-- Disjoint lenses pair into a lens onto both views. -/
@[expose] def pair (h : DisjointLenses L₁ L₂) : DeltaLens S (V₁ × V₂) where
  get s := (L₁.get s, L₂.get s)
  put s p := L₂.put (L₁.put s p.1) p.2
  get_put s := by
    change L₂.put (L₁.put s (L₁.get s)) (L₂.get s) = s
    rw [L₁.get_put, L₂.get_put]
  put_get s p := by
    change (L₁.get (L₂.put (L₁.put s p.1) p.2), L₂.get (L₂.put (L₁.put s p.1) p.2)) = p
    rw [h.get_left_put_right, L₁.put_get, L₂.put_get]
  put_put s p q := by
    change L₂.put (L₁.put (L₂.put (L₁.put s p.1) p.2) q.1) q.2 = L₂.put (L₁.put s q.1) q.2
    rw [h.comm, L₂.put_put, L₁.put_put]

/-- A lens under one of two disjoint lenses is disjoint from the other. -/
theorem comp_left {W : Type w} (h : DisjointLenses L₁ L₂) (M : DeltaLens V₁ W) :
    DisjointLenses (L₁.comp M) L₂ :=
  ⟨fun s x b => by
    change L₁.put (L₂.put s b) (M.put (L₁.get (L₂.put s b)) x) = L₂.put (L₁.put s (M.put (L₁.get s) x)) b
    rw [h.get_left_put_right, h.comm]⟩

end DisjointLenses

/-- The components of a pair are disjoint. -/
theorem DeltaLens.fst_snd_disjoint (A : Type u) (B : Type v) :
    DisjointLenses (DeltaLens.fst A B) (DeltaLens.snd A B) :=
  ⟨fun _ _ _ => rfl⟩

/-! ## 3. Claims renewed across a lens -/

section Claims
open Obend.Logic
variable {S : Type u} {W : Type w}

/-- **A claim certificate renews across a lens.** A derivation accepted for the claim object `o` is
accepted, and means what it meant, for the composition read back out of any richer state that holds
`o`'s composition. Nothing is replayed. -/
theorem renewClaimAcrossLens (L : DeltaLens S Composition) {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : claimCheck k o steps = .ok) (s : S) :
    claimCheck k { o with comp := L.get (L.put s o.comp) } steps = .ok ∧
      claimMeaning { o with comp := L.get (L.put s o.comp) } := by
  rw [L.put_get]
  exact ⟨h, claim_sound h⟩

/-- **The certificate is framed**: a state whose composition carries an accepted claim still does
after any write through a disjoint lens. -/
theorem renewClaimAcrossLens_frame {L : DeltaLens S Composition} {L' : DeltaLens S W}
    (hd : DisjointLenses L L') {k : Nat} {o : ClaimObj} {steps : List RStep} {s : S}
    (h : claimCheck k { o with comp := L.get s } steps = .ok) (x : W) :
    claimCheck k { o with comp := L.get (L'.put s x) } steps = .ok ∧
      claimMeaning { o with comp := L.get (L'.put s x) } := by
  rw [hd.get_left_put_right]
  exact ⟨h, claim_sound h⟩

/-- **The certificate survives an evolution of the composition itself** that keeps its supports:
written into the state, a composition `C'` that unfolds each member of the derivation as `o`'s does
carries the same accepted derivation (`claim_frame`), at any layer index. -/
theorem renewClaimAcrossLens_evolve (L : DeltaLens S Composition) {k : Nat} {o : ClaimObj}
    {steps : List RStep} (h : claimCheck k o steps = .ok) (s : S) {C' : Composition} {layer' : Nat}
    (hsup : ∀ m ∈ membersList steps, symUnfold C' o.self m = symUnfold o.comp o.self m)
    (hwf : ({ o with comp := C', layer := layer' } : ClaimObj).wellFormed = true) :
    claimCheck k { o with comp := L.get (L.put s C'), layer := layer' } steps = .ok ∧
      claimMeaning { o with comp := L.get (L.put s C'), layer := layer' } := by
  rw [L.put_get]
  have h' := claim_frame h hsup hwf
  exact ⟨h', claim_sound h'⟩

end Claims

/-! ## 4. Intentions renewed across a lens -/

section Intentions
variable {S V W Ref Pin Fact Err : Type}

/-- An intention over the view, as an intention over the state: a fact holds at a state when it
holds at its view, and a reference resolves there as it does at the view. Its two laws are the
view's. -/
@[expose] def DeltaLens.liftIntention (L : DeltaLens S V) (I : Intention V Ref Pin Fact Err) :
    Intention S Ref Pin Fact Err where
  ref := I.ref
  supports := I.supports
  holds s f := I.holds (L.get s) f
  resolve s r := I.resolve (L.get s) r
  resolve_ref s r p h := I.resolve_ref (L.get s) r p h
  resolve_holds s r p h := I.resolve_holds (L.get s) r p h

theorem DeltaLens.liftIntention_current (L : DeltaLens S V) (I : Intention V Ref Pin Fact Err) (s : S)
    (p : Pin) : (L.liftIntention I).current s p = I.current (L.get s) p := rfl

/-- A pin current at a view is current at every state holding that view. -/
theorem DeltaLens.liftIntention_current_put (L : DeltaLens S V) (I : Intention V Ref Pin Fact Err) (s : S)
    (v : V) (p : Pin) : (L.liftIntention I).current (L.put s v) p = I.current v p := by
  rw [L.liftIntention_current, L.put_get]

/-- **An intention renews across a lens.** A renewal made at a view `v` is the renewal at every
state holding `v`, and there it is a usable, current fill of the same reference's slot. -/
theorem renewIntentionAcrossLens [DecidableEq Ref] (L : DeltaLens S V) (I : Intention V Ref Pin Fact Err)
    {v : V} {p p' : Pin} (h : I.renew v p = .ok p') (s : S) :
    (L.liftIntention I).renew (L.put s v) p = .ok p' ∧ I.ref p' = I.ref p ∧
      ((L.liftIntention I).slot (I.ref p)).usable ((L.liftIntention I).holds (L.put s v)) p' = true ∧
      (L.liftIntention I).current (L.put s v) p' = true := by
  have h' : (L.liftIntention I).renew (L.put s v) p = .ok p' := by
    change I.resolve (L.get (L.put s v)) (I.ref p) = .ok p'
    rw [L.put_get]
    exact h
  exact ⟨h', (L.liftIntention I).renew_fill h'⟩

/-- After a step of the view lifted to the state, the renewal at the stepped view repairs the pin. -/
theorem renewIntentionAcrossLens_step [DecidableEq Ref] (L : DeltaLens S V)
    (I : Intention V Ref Pin Fact Err) (step : V → V) {s : S} {p p' : Pin}
    (h : I.renew (step (L.get s)) p = .ok p') :
    (L.liftIntention I).renew (L.modify step s) p = .ok p' ∧
      (L.liftIntention I).current (L.modify step s) p' = true :=
  have r := renewIntentionAcrossLens L I h s
  ⟨r.1, r.2.2.2⟩

/-- **A satisfied intention is framed**: whether a pin is current does not change under a write
through a disjoint lens. -/
theorem DeltaLens.liftIntention_frame {L : DeltaLens S V} {L' : DeltaLens S W} (hd : DisjointLenses L L')
    (I : Intention V Ref Pin Fact Err) (s : S) (x : W) (p : Pin) :
    (L.liftIntention I).current (L'.put s x) p = (L.liftIntention I).current s p := by
  rw [L.liftIntention_current, L.liftIntention_current, hd.get_left_put_right]

/-- A usable pin stays usable under a write through a disjoint lens (`Intention.stays`). -/
theorem DeltaLens.liftIntention_stays [DecidableEq Ref] {L : DeltaLens S V} {L' : DeltaLens S W}
    (hd : DisjointLenses L L') (I : Intention V Ref Pin Fact Err) {r : Ref} {p : Pin} (hr : I.ref p = r)
    {s : S} (hu : ((L.liftIntention I).slot r).usable ((L.liftIntention I).holds s) p = true) (x : W) :
    ((L.liftIntention I).slot r).usable ((L.liftIntention I).holds (L'.put s x)) p = true :=
  (L.liftIntention I).stays hr (fun f _ hf => by
    change I.holds (L.get (L'.put s x)) f = true
    rw [hd.get_left_put_right]
    exact hf) hu

end Intentions

end Obend.Repair
end
