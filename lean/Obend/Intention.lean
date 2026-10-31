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
@[expose] public section

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
def slot (r : Ref) : Slot Fact Pin where
  supports := I.supports
  judge p := decide (I.ref p = r)

/-- Every support of the pin holds at the world. -/
def current (w : W) (p : Pin) : Bool := (I.supports p).all (I.holds w)

/-- The repair: resolve the pin's reference again at the world. -/
def renew (w : W) (p : Pin) : Except Err Pin := I.resolve w (I.ref p)

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

end Intention

end Obend

end
