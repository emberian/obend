module
/-
# Obend.Spec.Proofs.Ecosystem — a turn pins every root it resolved; a moved pin is stale by name

About `Obend.Spec.Ecosystem`:

* `turn_pins_every_root`: a closure that `close` returns pins every package on its precedence list
  except the entry, puts every release it chose on that list, and every pin it holds is current at
  the view it was closed at.
* `resolve_fill`: resolving an intention is a fill of its slot (`intentionSlot`): the pin it returns
  passes the slot's judge and its one support holds at that view.
* `stale_iff_blocked`: an intention pin is not current exactly when its slot's read, at that view,
  is BLOCKED naming its support ("the record names v at p"): staleness is the slot vocabulary's
  dead support, nothing new.
* `extension_current`: an extension pin is current at every view (a hash is fixed forever), so
  `admit_never_stale_extensions`: a turn whose pins are all extensions is never stale.
* `admit_stale_names_moved` / `admit_refuses_moved`: admission refuses `stale p` only for a pin `p`
  of the turn that is not current, and refuses so whenever one is; `admit_admitted` re-derives:
  an admitted turn's closure is `close` at the view, with the turn's pins and order.
* `moved_pin_stale_forever` / `retired_stale_forever`: along record steps (pins never go back, a
  retirement is terminal) a pin the record has moved past, or a retired line, is stale at every
  later view, and so is every turn that pins it (`turn_stale_forever`).
* `closure_law_inherited`: the effective package law of a closure (`Obend.Spec.PackageLaw.effectivePackages`
  over its precedence list) admits a write only if every clause of every chosen package does: a
  parent's package law is an ancestor of the child's, across the package boundary.

`ecosystem_tooth` runs `close` and `admit` on a concrete diamond (a base, two independent
extensions, a fourth extending both) and a record step that moves the base's pin.
-/
public import Obend.Spec.Ecosystem
import all Obend.Spec.Ecosystem
public import Obend.Slot.World
public import Obend.Spec.PackageLaw
public import Obend.Spec.Proofs.PackageLaw
public import Obend.Tactic.Tooth
namespace Obend.Spec.Ecosystem
open Obend.Slot
set_option autoImplicit false

theorem covered_none {v : View} {entry : String} {cl : Closure} {order : List String}
    (h : covered v entry cl order = none) :
    (∀ n ∈ order, n ≠ entry → ∃ p ∈ cl.pins, p.name = n) ∧ (∀ r ∈ cl.chosen, r.name ∈ order) ∧
      ∀ p ∈ cl.pins, p.current v = true := by
  unfold covered at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · cases h
      · rename_i h3
        rw [List.find?_eq_none] at h1 h2 h3
        refine ⟨fun n hn hne => ?_, fun r hr => ?_, fun p hp => ?_⟩
        · have := h1 n hn
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_and, Bool.not_eq_false] at this
          have hany := this hne
          rw [List.any_eq_true] at hany
          obtain ⟨p, hp, hpn⟩ := hany
          exact ⟨p, hp, by simpa using hpn⟩
        · have := h2 r hr
          simpa using this
        · have := h3 p hp
          simpa using this

/-- **A turn pins every root it resolved.** -/
public theorem turn_pins_every_root {v : View} {e : Release} {cl : Closure} (h : close v e = .ok cl) :
    cl.entry = e ∧ (∀ n ∈ cl.order, n ≠ e.name → ∃ p ∈ cl.pins, p.name = n) ∧
      (∀ r ∈ cl.chosen, r.name ∈ cl.order) ∧ ∀ p ∈ cl.pins, p.current v = true := by
  unfold close at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i cl0 _
    split at h
    · cases h
    · rename_i hc
      cases h
      exact ⟨rfl, covered_none hc⟩

/-- Resolving an intention is a fill of its slot: the pin passes the slot's judge, and the support
it cites holds at the view it was resolved at. -/
public theorem resolve_fill {v : View} {n : String} {m : Nat} {r : Release} {p : Pin}
    (h : resolve v (.intention n m) = .ok (r, p)) :
    (intentionSlot n m).usable (holds v) p = true ∧ p.current v = true ∧ p.name = n ∧ r.major = m := by
  simp only [resolve] at h
  split at h
  · cases h
  · rename_i l hl
    split at h
    · cases h
    · rename_i version hv
      split at h
      · cases h
      · rename_i r' _
        split at h
        · rename_i hm
          cases h
          have hm' : r.major = m := by simpa using hm
          refine ⟨?_, ?_, rfl, hm'⟩
          · simp [Slot.usable, Slot.dead, intentionSlot, holds, hl, hv]
          · simp [Pin.current, hl, hv]
        · cases h

/-- **Staleness is a blocked slot read**: an intention pin is not current at a view exactly when the
read of its slot there is blocked, naming its one support. -/
public theorem stale_iff_blocked (v : View) (n : String) (m pin : Nat) (version hash : String) :
    (Pin.intention n m pin version hash).current v = false ↔
      (intentionSlot n m).read (holds v) (some (.intention n m pin version hash)) =
        .blocked (.intention n m pin version hash) [⟨n, m, pin, version⟩] := by
  have hc : (Pin.intention n m pin version hash).current v = holds v ⟨n, m, pin, version⟩ := by
    simp only [Pin.current, holds]
  rw [hc]
  cases hh : holds v ⟨n, m, pin, version⟩ <;>
    simp [Slot.read, Slot.dead, intentionSlot, hh]

/-- An extension pin is current at every view: a hash is fixed forever. -/
public theorem extension_current (v : View) (n h : String) : (Pin.extension n h).current v = true := rfl

/-- **Admission names a moved pin**: `stale p` only for a pin of the turn that is not current. -/
public theorem admit_stale_names_moved {v : View} {t : Turn} {p : Pin} (h : admit v t = .stale p) :
    p ∈ t.pins ∧ p.current v = false := by
  unfold admit at h
  split at h
  · rename_i q hq
    cases h
    have := List.find?_some hq
    exact ⟨List.mem_of_find?_eq_some hq, by simpa using this⟩
  · split at h <;> (try split at h) <;> cases h

/-- **A moved pin is stale**: a turn holding a pin that is not current is refused `stale`, naming a
pin of the turn that is not current. -/
public theorem admit_refuses_moved {v : View} {t : Turn} (h : ∃ p ∈ t.pins, p.current v = false) :
    ∃ p, admit v t = .stale p ∧ p ∈ t.pins ∧ p.current v = false := by
  unfold admit
  cases hf : t.pins.find? (fun p => !p.current v) with
  | none =>
    obtain ⟨p, hp, hc⟩ := h
    rw [List.find?_eq_none] at hf
    have := hf p hp
    simp [hc] at this
  | some q =>
    have := List.find?_some hf
    exact ⟨q, rfl, List.mem_of_find?_eq_some hf, by simpa using this⟩

/-- **Admission re-derives**: an admitted turn's closure is `close` at the view, with the turn's
own pins and precedence order. -/
public theorem admit_admitted {v : View} {t : Turn} {cl : Closure} (h : admit v t = .admitted cl) :
    close v t.entry = .ok cl ∧ cl.pins = t.pins ∧ cl.order = t.order := by
  unfold admit at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i cl' hcl
      split at h
      · rename_i heq
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        exact ⟨hcl, heq.1, heq.2⟩
      · cases h

/-- A turn whose pins are all extensions is never stale. -/
public theorem admit_never_stale_extensions {v : View} {t : Turn}
    (hx : ∀ p ∈ t.pins, ∃ n h, p = .extension n h) (p : Pin) : admit v t ≠ .stale p := by
  intro h
  obtain ⟨hp, hc⟩ := admit_stale_names_moved h
  obtain ⟨n, hh, rfl⟩ := hx p hp
  rw [extension_current] at hc
  cases hc

/-- Along record steps a line persists, its pin never decreases, and a retired line stays retired. -/
theorem line_later {v v' : View} (hr : Reaches Step v v') {n : String} {m : Nat} {l : RecordLine}
    (hl : v.line n m = some l) :
    ∃ l', v'.line n m = some l' ∧ l.pin ≤ l'.pin ∧ (l.fill = none → l'.fill = none) := by
  induction hr with
  | refl => exact ⟨l, hl, Nat.le_refl _, id⟩
  | tail _ step ih =>
    obtain ⟨l1, h1, hp1, hf1⟩ := ih
    obtain ⟨l2, h2, hp2, hf2⟩ := step n m l1 h1
    exact ⟨l2, h2, Nat.le_trans hp1 hp2, fun h => hf2 (hf1 h)⟩

/-- **A pin the record has moved past stays stale**: if at `v` the line's pin is past the turn's,
the turn's pin is not current at any later view. -/
public theorem moved_pin_stale_forever {v v' : View} (hr : Reaches Step v v') {n : String} {m pin : Nat}
    {version hash : String} {l : RecordLine} (hl : v.line n m = some l) (hpast : pin < l.pin) :
    (Pin.intention n m pin version hash).current v' = false := by
  obtain ⟨l', h', hp, _⟩ := line_later hr hl
  have hne : l'.pin ≠ pin := by omega
  simp [Pin.current, h', hne]

/-- **A retired line stays stale**: a pin of a line its owner retired is not current at any later
view. -/
public theorem retired_stale_forever {v v' : View} (hr : Reaches Step v v') {n : String} {m pin : Nat}
    {version hash : String} {l : RecordLine} (hl : v.line n m = some l) (hret : l.fill = none) :
    (Pin.intention n m pin version hash).current v' = false := by
  obtain ⟨l', h', _, hf⟩ := line_later hr hl
  simp [Pin.current, h', hf hret]

/-- A turn pinning a line the record has moved past is refused `stale` at every later view. -/
public theorem turn_stale_forever {v v' : View} (hr : Reaches Step v v') {t : Turn} {n : String}
    {m pin : Nat} {version hash : String} {l : RecordLine}
    (hp : Pin.intention n m pin version hash ∈ t.pins) (hl : v.line n m = some l) (hpast : pin < l.pin) :
    ∃ q, admit v' t = .stale q ∧ q ∈ t.pins ∧ q.current v' = false :=
  admit_refuses_moved ⟨_, hp, moved_pin_stale_forever hr hl hpast⟩

/-- **Package laws inherit across the package boundary**: the effective law of a closure admits a
write only if every clause of every package the closure chose admits it. -/
public theorem closure_law_inherited {v : View} {e : Release} {cl : Closure} (hc : close v e = .ok cl)
    {laws : String → List (String × Obend.Core.Term.Term)} {law : Obend.Core.Term.Term}
    (hl : Obend.Spec.PackageLaw.effectivePackages laws cl.order = .ok law) {o n rq : Obend.Core.Data.Data}
    (ha : Obend.Law.Admits law o n rq) :
    ∀ r ∈ cl.chosen, ∀ c ∈ laws r.name, Obend.Law.Admits c.2 o n rq := by
  obtain ⟨_, _, hchosen, _⟩ := turn_pins_every_root hc
  intro r hr c hcl
  exact (Obend.Spec.PackageLaw.package_law_eval hl o n rq).1 ha r.name (hchosen r hr) c hcl

/-! ## Teeth: a chain closed and admitted; a record step that moves the base; a diamond that
reaches its base twice. (A two-parent C4 merge does not reduce in the kernel: its hash map hashes
strings by an `extern`; the diamond's order is checked on the executable path,
`tests/obend-source/three-package/`.) -/

def baseR : Release := ⟨"base", "1.0.0", 1, "aa", []⟩
def leftR : Release := ⟨"left", "1.0.0", 1, "bb", [.intention "base" 1]⟩
def rightR : Release := ⟨"right", "1.0.0", 1, "cc", [.extension "base" "aa"]⟩
def chainR : Release := ⟨"chain", "0.1.0", 0, "dd", [.intention "left" 1]⟩
def diamondR : Release := ⟨"diamond", "0.1.0", 0, "ff", [.intention "left" 1, .intention "right" 1]⟩
def base2R : Release := ⟨"base", "1.1.0", 1, "ee", []⟩

def view0 : View :=
  ⟨[baseR, leftR, rightR, base2R],
   [⟨"base", 1, 3, some "1.0.0", "ada"⟩, ⟨"left", 1, 1, some "1.0.0", "bo"⟩, ⟨"right", 1, 7, some "1.0.0", "cy"⟩]⟩
/-- The owner of `base` names 1.1.0 at pin 4. -/
def view1 : View :=
  ⟨view0.releases,
   [⟨"base", 1, 4, some "1.1.0", "ada"⟩, ⟨"left", 1, 1, some "1.0.0", "bo"⟩, ⟨"right", 1, 7, some "1.0.0", "cy"⟩]⟩

theorem ecosystem_tooth :
    ((close view0 chainR).toOption.map (·.order)) = some ["chain", "left", "base"] ∧
      ((close view0 chainR).toOption.map (·.pins)) =
        some [.intention "left" 1 1 "1.0.0" "bb", .intention "base" 1 3 "1.0.0" "aa"] ∧
      ((close view0 chainR).toOption.map fun cl => (admit view0 cl.turn) matches .admitted _) = some true ∧
      ((close view0 chainR).toOption.map fun cl => admit view1 cl.turn) =
        some (.stale (.intention "base" 1 3 "1.0.0" "aa")) ∧
      -- at view1 `left` reaches base 1.1.0 by name, `right` base 1.0.0 by hash: two releases, refused
      (match close view1 diamondR with
        | .error e => decide (e = .incompatible "base" "1.1.0" "1.0.0")
        | .ok _ => false) = true := by
  decide +kernel

#tooth turn_pins_every_root by mutation covered := fun _ _ _ _ => none
#tooth admit_refuses_moved by mutation admit := fun _ _ => .diverged
#tooth stale_iff_blocked by mutation holds := fun _ _ => true

end Obend.Spec.Ecosystem
