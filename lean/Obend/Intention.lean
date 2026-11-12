module
/-
# Obend.Intention — a named reference resolved against a World

LTUO §9.3.7: a name is an INTENTION, a meeting point whose meaning its owner keeps choosing; a hash
is an EXTENSION, fixed forever. Every reference across a boundary in this tree is the first kind
with the second as its degenerate case: a package parent `NAME@^MAJOR` (`Obend.Spec.Ecosystem`), a
cite of another page (`Obend.Doc.Section`), an instance's kind (`Obend.Kind`). This module is the
one structure they share.

An `Intention W Ref Pin Fact Err` resolves a reference `Ref` at a world `W` to a PIN, what a turn
retains: the owner's current choice (`resolve`), or a refusal `Err`. A pin cites SUPPORTS, facts a
world is asked about ("the record names version `v` at pin `p`"); a pin is CURRENT at a world when
every support holds there. Each reference is a slot (`Obend.Slot`): its candidates are pins, its
judge is "this pin resolves this reference", its supports are the pin's. So:

* `stale_iff_blocked`: a pin is not current at a world exactly when its slot's read there is
  blocked, naming exactly its dead supports. Staleness is the slot vocabulary's blocked read.
* `resolve_fill`: a resolution is a usable fill of its reference's slot, current where it was made.
* `renew`: the one repair. A stale pin is renewed by resolving its reference again at the world;
  the renewal is a usable, current fill of the same slot (`renew_fill`), so a blocked read becomes
  a usable one by that single action (`renew_repairs`). On a package DAG it is `resolve`, on a
  document `recite`, on a lease `renew`: one definition.
* `stays`: a pin whose supports survive a step of the world stays current across it, and its read
  stays usable (an extension, a pinned cite).
* `blocked_names`: a dead support of a pin is named by its blocked read; `blocked_within`: so it is
  by any slot whose candidate carries the pin's supports (a section holding a cite run).

The judge compares references, so `Ref` has decidable equality; nothing else is assumed.
-/
public import Obend.Slot
public section

namespace Obend

open Obend.Slot

/-- A named reference resolved against a world: what a pin resolves, what it cites, whether a cited
fact holds at a world, and the owner's choice at a world, sound by `resolve_ref` and
`resolve_holds`. -/
structure Intention (W Ref Pin Fact Err : Type) where
  /-- the reference a pin resolves -/
  ref : Pin → Ref
  /-- the facts a pin cites: "the record names `v` at `p`" -/
  supports : Pin → List Fact
  /-- whether a fact holds at a world -/
  holds : W → Fact → Bool
  /-- the owner's current choice for a reference at a world, or why there is none -/
  resolve : W → Ref → Except Err Pin
  resolve_ref : ∀ w r p, resolve w r = .ok p → ref p = r
  resolve_holds : ∀ w r p, resolve w r = .ok p → ∀ f ∈ supports p, holds w f = true

namespace Intention

variable {W Ref Pin Fact Err : Type} [DecidableEq Ref] (I : Intention W Ref Pin Fact Err)

/-- The slot of a reference: candidates are pins, the judge is "it resolves `r`", the supports are
the pin's. -/
@[expose] def slot (r : Ref) : Slot Fact Pin where
  supports := I.supports
  judge p := decide (I.ref p = r)

/-- Every support of the pin holds at the world. -/
@[expose] def current (w : W) (p : Pin) : Bool := (I.supports p).all (I.holds w)

/-- The repair: resolve the pin's reference again at the world. -/
@[expose] def renew (w : W) (p : Pin) : Except Err Pin := I.resolve w (I.ref p)

omit [DecidableEq Ref] in
theorem current_iff (w : W) (p : Pin) : I.current w p = true ↔ ∀ f ∈ I.supports p, I.holds w f = true := by
  simp [current, List.all_eq_true]

/-- **Staleness is a blocked read.** A pin of reference `r` is not current at a world exactly when
the read of `r`'s slot there is blocked, naming exactly the pin's supports that do not hold. -/
theorem stale_iff_blocked {r : Ref} {p : Pin} (hr : I.ref p = r) (w : W) :
    I.current w p = false ↔
      (I.slot r).read (I.holds w) (some p) = .blocked p ((I.supports p).filter fun f => !I.holds w f) := by
  have hj : (I.slot r).judge p = true := by simp [slot, hr]
  unfold Slot.read
  simp only [hj, ite_true]
  have hdead : (I.slot r).dead (I.holds w) p = (I.supports p).filter fun f => !I.holds w f := rfl
  rw [hdead]
  cases hf : (I.supports p).filter fun f => !I.holds w f with
  | nil =>
    have : I.current w p = true := by
      rw [current_iff]; intro f hf'
      have := List.filter_eq_nil_iff.1 hf f hf'
      simpa using this
    simp [this]
  | cons g t =>
    have hg : g ∈ (I.supports p).filter fun f => !I.holds w f := by rw [hf]; exact List.mem_cons_self
    obtain ⟨hgs, hgh⟩ := List.mem_filter.1 hg
    have : I.current w p = false := by
      cases hc : I.current w p
      · rfl
      · have := (I.current_iff w p).1 hc g hgs; simp [this] at hgh
    simp [this]

/-- A pin is current exactly when its slot's read is usable. -/
theorem current_iff_usable {r : Ref} {p : Pin} (hr : I.ref p = r) (w : W) :
    I.current w p = true ↔ (I.slot r).usable (I.holds w) p = true := by
  rw [usable_iff, current_iff]
  simp [slot, hr]

/-- **A resolution is a usable fill**: the pin resolves its reference, passes its slot's judge, and
every support it cites holds where it was resolved. -/
theorem resolve_fill {w : W} {r : Ref} {p : Pin} (h : I.resolve w r = .ok p) :
    I.ref p = r ∧ (I.slot r).usable (I.holds w) p = true ∧ I.current w p = true := by
  have hr := I.resolve_ref w r p h
  have hc : I.current w p = true := (I.current_iff w p).2 (I.resolve_holds w r p h)
  exact ⟨hr, (I.current_iff_usable hr w).1 hc, hc⟩

/-- **The renewal is a usable fill of the same slot.** -/
theorem renew_fill {w : W} {p p' : Pin} (h : I.renew w p = .ok p') :
    I.ref p' = I.ref p ∧ (I.slot (I.ref p)).usable (I.holds w) p' = true ∧ I.current w p' = true :=
  I.resolve_fill h

/-- **Renewal is the one repair**: a pin whose read is blocked at a world, once renewed there, reads
usable in the same slot, with its evidence. -/
theorem renew_repairs {w : W} {p p' : Pin} (h : I.renew w p = .ok p') :
    (I.slot (I.ref p)).read (I.holds w) (some p') =
      .usable p' ((I.slot (I.ref p)).evidence (I.holds w) p') :=
  read_of_usable _ _ p' (I.renew_fill h).2.1

/-- **A dead support is named**: a pin of `r` with a support that does not hold reads blocked, and
the blocked read names it. -/
theorem blocked_names {r : Ref} {p : Pin} (hr : I.ref p = r) {w : W} {f : Fact} (hf : f ∈ I.supports p)
    (hd : I.holds w f = false) :
    ∃ d, (I.slot r).read (I.holds w) (some p) = .blocked p d ∧ f ∈ d := by
  have hc : I.current w p = false := by
    cases hc : I.current w p
    · rfl
    · have := (I.current_iff w p).1 hc f hf; rw [this] at hd; cases hd
  exact ⟨_, (I.stale_iff_blocked hr w).1 hc, List.mem_filter.2 ⟨hf, by simp [hd]⟩⟩

omit [DecidableEq Ref] in
/-- **A dead support is named by any slot carrying the pin**: a slot whose candidate `x` passes its
judge and cites every support of `p` reads blocked where a support of `p` is dead, naming it. -/
theorem blocked_within {Cand : Type} (S : Slot Fact Cand) {x : Cand} (hj : S.judge x = true) {p : Pin}
    (hsub : ∀ f ∈ I.supports p, f ∈ S.supports x) {w : W} {f : Fact} (hf : f ∈ I.supports p)
    (hd : I.holds w f = false) : ∃ d, S.read (I.holds w) (some x) = .blocked x d ∧ f ∈ d := by
  have hmem : f ∈ S.dead (I.holds w) x := (mem_dead_iff S _ x f).2 ⟨hsub f hf, hd⟩
  unfold Slot.read
  simp only [hj, ite_true]
  cases hdd : S.dead (I.holds w) x with
  | nil => rw [hdd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩

/-- **A pin whose supports survive a step stays current**, and its read stays usable. -/
theorem stays {r : Ref} {p : Pin} (hr : I.ref p = r) {w w' : W}
    (keep : ∀ f ∈ I.supports p, I.holds w f = true → I.holds w' f = true)
    (hu : (I.slot r).usable (I.holds w) p = true) : (I.slot r).usable (I.holds w') p = true := by
  rw [← I.current_iff_usable hr] at hu ⊢
  rw [current_iff] at hu ⊢
  exact fun f hf => keep f hf (hu f hf)

/-! ## Compositional Intention Algebra & Deduplicated Support Subadditivity -/

omit [DecidableEq Ref] in
/-- Structural support deduplication: shared world facts cited across coupled intentions or slots
are checked once rather than redundantly per consumer. -/
@[expose] def dedupSupports [DecidableEq Fact] : List Fact → List Fact
  | [] => []
  | f :: fs =>
    let rest := dedupSupports fs
    if f ∈ rest then rest else f :: rest

omit [DecidableEq Ref] in
theorem mem_dedupSupports_iff [DecidableEq Fact] (fs : List Fact) (x : Fact) :
    x ∈ dedupSupports fs ↔ x ∈ fs := by
  induction fs generalizing x with
  | nil => simp [dedupSupports]
  | cons f fs ih =>
    simp only [dedupSupports]
    by_cases hmem : f ∈ dedupSupports fs
    · simp only [hmem, ↓reduceIte, ih x, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ (ih f).1 hmem) id⟩
    · simp only [hmem, ↓reduceIte, List.mem_cons, ih x]

omit [DecidableEq Ref] in
theorem dedupSupports_nodup [DecidableEq Fact] (fs : List Fact) :
    (dedupSupports fs).Nodup := by
  induction fs with
  | nil => simp [dedupSupports]
  | cons f fs ih =>
    simp only [dedupSupports]
    by_cases hmem : f ∈ dedupSupports fs
    · simp [hmem, ih]
    · simp [hmem, List.nodup_cons, ih]

omit [DecidableEq Ref] in
theorem dedupSupports_length_le [DecidableEq Fact] (fs : List Fact) :
    (dedupSupports fs).length ≤ fs.length := by
  induction fs with
  | nil => simp [dedupSupports]
  | cons f fs ih =>
    simp only [dedupSupports]
    by_cases hmem : f ∈ dedupSupports fs <;> simp [hmem] <;> omega

omit [DecidableEq Ref] in
theorem dedupSupports_append_subadditive [DecidableEq Fact] (xs ys : List Fact) :
    (dedupSupports (xs ++ ys)).length ≤ xs.length + ys.length := by
  have hle := dedupSupports_length_le (xs ++ ys)
  rw [List.length_append] at hle
  exact hle

omit [DecidableEq Ref] in
/-- **Strict Support Subadditivity (`dedupSupports_append_lt_of_shared`)**:
when two pinned intentions cite at least one common world support `f₀`, deduplicated support
verification strictly saves work over naive independent verification. -/
theorem dedupSupports_append_lt_of_shared [DecidableEq Fact] {xs ys : List Fact} {f₀ : Fact}
    (hx : f₀ ∈ xs) (hy : f₀ ∈ ys) :
    (dedupSupports (xs ++ ys)).length < xs.length + ys.length := by
  induction xs with
  | nil => cases hx
  | cons x xs ih =>
    simp only [List.cons_append, dedupSupports, List.length_cons]
    by_cases heq : x = f₀
    · subst heq
      have hInRest : x ∈ dedupSupports (xs ++ ys) :=
        (mem_dedupSupports_iff (xs ++ ys) x).2 (List.mem_append_right xs hy)
      simp only [hInRest, ↓reduceIte]
      have hSub := dedupSupports_append_subadditive xs ys
      omega
    · have hx' : f₀ ∈ xs := by
        rcases List.mem_cons.1 hx with rfl | hmem
        · exact absurd rfl heq
        · exact hmem
      have hLt := ih hx'
      by_cases hInRest : x ∈ dedupSupports (xs ++ ys) <;> simp [hInRest] <;> omega

omit [DecidableEq Ref] in
/-- Product of two Author intentions over a shared world valuation (`hHolds`), deduplicating
overlapping world supports on combined pins `(p₁, p₂)`. -/
def product {Ref₂ Pin₂ : Type} [DecidableEq Fact]
    (I₁ : Intention W Ref Pin Fact Err) (I₂ : Intention W Ref₂ Pin₂ Fact Err)
    (hHolds : ∀ w f, I₂.holds w f = I₁.holds w f) :
    Intention W (Ref × Ref₂) (Pin × Pin₂) Fact Err where
  ref p := (I₁.ref p.1, I₂.ref p.2)
  supports p := dedupSupports (I₁.supports p.1 ++ I₂.supports p.2)
  holds := I₁.holds
  resolve w r :=
    match I₁.resolve w r.1 with
    | .error e => .error e
    | .ok p₁ =>
      match I₂.resolve w r.2 with
      | .error e => .error e
      | .ok p₂ => .ok (p₁, p₂)
  resolve_ref w r p h := by
    cases h₁ : I₁.resolve w r.1 <;> rw [h₁] at h
    · cases h
    · rename_i p₁
      cases h₂ : I₂.resolve w r.2 <;> rw [h₂] at h
      · cases h
      · rename_i p₂
        cases h
        exact Prod.ext (I₁.resolve_ref w r.1 p₁ h₁) (I₂.resolve_ref w r.2 p₂ h₂)
  resolve_holds w r p h f hf := by
    cases h₁ : I₁.resolve w r.1 <;> rw [h₁] at h
    · cases h
    · rename_i p₁
      cases h₂ : I₂.resolve w r.2 <;> rw [h₂] at h
      · cases h
      · rename_i p₂
        cases h
        have hf' := (mem_dedupSupports_iff _ f).1 hf
        rcases List.mem_append.1 hf' with hf₁ | hf₂
        · exact I₁.resolve_holds w r.1 p₁ h₁ f hf₁
        · rw [← hHolds w f]
          exact I₂.resolve_holds w r.2 p₂ h₂ f hf₂

omit [DecidableEq Ref] in
theorem product_current_eq {Ref₂ Pin₂ : Type} [DecidableEq Fact]
    (I₁ : Intention W Ref Pin Fact Err) (I₂ : Intention W Ref₂ Pin₂ Fact Err)
    (hHolds : ∀ w f, I₂.holds w f = I₁.holds w f)
    (w : W) (p : Pin × Pin₂) :
    (product I₁ I₂ hHolds).current w p = (I₁.current w p.1 && I₂.current w p.2) := by
  apply Bool.eq_iff_iff.2
  rw [current_iff, Bool.and_eq_true, current_iff, current_iff]
  constructor
  · intro hall
    refine ⟨fun f hf => hall f ((mem_dedupSupports_iff _ f).2 (List.mem_append_left _ hf)),
      fun f hf => ?_⟩
    rw [hHolds w f]
    exact hall f ((mem_dedupSupports_iff _ f).2 (List.mem_append_right _ hf))
  · rintro ⟨h₁, h₂⟩ f hf
    have hf' := (mem_dedupSupports_iff _ f).1 hf
    show I₁.holds w f = true
    rcases List.mem_append.1 hf' with hf₁ | hf₂
    · exact h₁ f hf₁
    · rw [← hHolds w f]
      exact h₂ f hf₂

omit [DecidableEq Ref] in
/-- Batch resolution of a finite list of Author references at world `w`, returning either an aligned
list of current pins or the first failing `(ref, err)` pair. -/
def resolveBatch (w : W) : List Ref → Except (Ref × Err) (List Pin)
  | [] => .ok []
  | r :: rs =>
    match I.resolve w r with
    | .error e => .error (r, e)
    | .ok p =>
      match resolveBatch w rs with
      | .error re => .error re
      | .ok ps => .ok (p :: ps)

theorem resolveBatch_inhabited :
    let I₀ : Intention Unit Nat Nat Unit Unit :=
      { ref := id
        supports := fun _ => [()]
        holds := fun _ _ => true
        resolve := fun _ r => .ok r
        resolve_ref := fun _ _ _ h => by cases h; rfl
        resolve_holds := fun _ _ _ _ _ _ => rfl }
    I₀.resolveBatch () [1, 2] = .ok [1, 2] := by
  unfold resolveBatch
  rfl

/-- Soundness of `resolveBatch`: every returned pin resolves its corresponding reference, is
current at `w`, and is usable in its reference's `Slot`. -/
theorem resolveBatch_sound {w : W} {refs : List Ref} {pins : List Pin}
    (h : I.resolveBatch w refs = .ok pins) :
    pins.map I.ref = refs ∧
    ∀ p ∈ pins, I.current w p = true ∧ (I.slot (I.ref p)).usable (I.holds w) p = true := by
  induction refs generalizing pins with
  | nil =>
    cases h
    simp
  | cons r rs ih =>
    simp only [resolveBatch] at h
    cases hr : I.resolve w r <;> rw [hr] at h
    · cases h
    · rename_i p
      cases hrs : I.resolveBatch w rs <;> rw [hrs] at h
      · cases h
      · rename_i ps
        cases h
        obtain ⟨hmap, hall⟩ := ih hrs
        obtain ⟨href, husable, hcur⟩ := I.resolve_fill hr
        refine ⟨by simp [href, hmap], ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq'
        · exact ⟨hcur, href.symm ▸ husable⟩
        · exact hall q hq'

omit [DecidableEq Ref] in
/-- Exact blame on `resolveBatch` refusal: a batch refusal names a reference from `refs` together
with the exact error returned by `I.resolve w`. -/
theorem resolveBatch_refuses_exact {w : W} {refs : List Ref} {badRef : Ref} {err : Err}
    (h : I.resolveBatch w refs = .error (badRef, err)) :
    badRef ∈ refs ∧ I.resolve w badRef = .error err := by
  induction refs with
  | nil => cases h
  | cons r rs ih =>
    simp only [resolveBatch] at h
    cases hr : I.resolve w r <;> rw [hr] at h
    · cases h
      exact ⟨List.mem_cons_self, hr⟩
    · cases hrs : I.resolveBatch w rs <;> rw [hrs] at h
      · cases h
        obtain ⟨hmem, herr⟩ := ih hrs
        exact ⟨List.mem_cons_of_mem _ hmem, herr⟩
      · cases h

end Intention

end Obend

end
