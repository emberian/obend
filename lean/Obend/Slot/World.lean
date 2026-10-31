module
/-
# Obend.Slot.World — the history a slot's supports are judged against

A slot (`Obend.Slot`) judges a candidate at a VIEW by asking whether each support it cites holds
there. This module says what a view is, abstractly: a `World` has views `V`, cells, and for each view
the PIN a cell holds there (`none` once the cell is retired), a support `Fact` names a cell and holds
or not at a view, and views are joined by an audited `Step`. The laws are fields, each the abstract
shape of a nano kernel theorem:

- `holdsOfPin`: a support's truth is read off the pin its cell holds (`holdsAt` is defined from it,
  `holds_pin` is `rfl`), so `holds_congr` (`receive_congr`, `Kernel/Proofs/Receive.lean`: a
  derivation depends only on the pinned view) is a congruence, and a stranger holding pins computes
  every read;
- `dead_none` (whence `retired_dead`): a support of a retired cell does not hold;
- `retired_step` (the retirement case of `stale_behind_forever`): a tombstone is terminal;
- the VERSION law (`stale_behind_forever`, `Kernel/Proofs/Versions.lean`): a cell's pin is read off
  its VERSION STATE (`Ver`, nano's entry: absent, live at a version, tombstone) by `pinOf`, and an
  audited step keeps a cell's version state or moves it strictly `Past` it (`ver_step`), `Past` a
  strict order. The pin is a function of the version, not conversely: two version states may read
  as one pin, which is a COLLISION (`Collides`) of exactly those two inputs. That is the collision
  stance, explicit: the non-return theorem ends in "or the pin function collides on the two version
  states it compares", nano's `CollidesAmong` over the concrete pin inputs, never a collision among
  some inputs (which pigeonhole proves of any finite digest). An instance whose pin is the version
  itself (or any injective reading of it, `Exact`) owes no disjunct (`stale_behind_forever_exact`).

From these: a support whose cell is retired is dead at every later view (`dead_behind_forever`), a
selection citing it stays blocked by that name (`blocked_forever`), and two views that agree on the
pins of a candidate's supports read and resolve a slot the same (`read_congr`, `select_congr`). From
the version law, with no retirement case: a pin observed at `w₀` and stale at `w` is stale at every
view after `w`, or the pin function collides (`stale_behind_forever`); a support PINNED where it was
observed (it holds only where its cell holds that pin: a citation of a version) and stale is dead at
every later view, or the pin function collides (`stale_dead_forever`), and a selection citing it reads
blocked by its name there (`stale_blocked_forever`). The tooth is a world whose pin returns
(`Returning`): it is lawful only through the collision, and no exact version order exists for it.
-/
public import Obend.Slot
public section

namespace Obend.Slot

/-- Views reachable by zero or more steps of `Step`. -/
inductive Reaches {V : Type} (Step : V → V → Prop) : V → V → Prop
  | refl (v : V) : Reaches Step v v
  | tail {v w w' : V} : Reaches Step v w → Step w w' → Reaches Step v w'

/-- A World: views, cells with the pin each view holds for them, supports about cells, and audited
steps, with the three laws the top clause needs. `Fact` is determined by `V`: a World's views come
with the supports they can be asked about. -/
class World (V : Type) (Fact : outParam Type) where
  /-- a cell (or a row slot: whatever a pin names) -/
  Cell : Type
  /-- a pin: the version a view holds for a cell -/
  Pin : Type
  /-- the cell a support is about -/
  cell : Fact → Cell
  /-- what a view holds for a cell: its pin, or `none` once the cell is retired -/
  pin : V → Cell → Option Pin
  /-- whether a support holds, read off the pin its cell holds (`none`: retired). A stranger holding
  the pins computes every read with this; `holdsAt` is defined from it, so `holds_congr` is a
  congruence, not a law. -/
  holdsOfPin : Cell → Option Pin → Fact → Bool
  /-- one audited step between views -/
  Step : V → V → Prop
  /-- a support of a retired cell does not hold -/
  dead_none : ∀ (f : Fact), holdsOfPin (cell f) none f = false
  /-- a tombstone is terminal: a cell retired at a view is retired after a step -/
  retired_step : ∀ (v v' : V) (c : Cell), Step v v' → pin v c = none → pin v' c = none
  /-- a cell's version state at a view: what its pin is read off (nano's entry) -/
  Ver : Type
  ver : V → Cell → Ver
  /-- `Past a b`: the version state `b` is strictly past `a` -/
  Past : Ver → Ver → Prop
  past_irrefl : ∀ a, ¬ Past a a
  past_trans : ∀ a b c, Past a b → Past b c → Past a c
  /-- the pin a version state of a cell reads as (a digest of it, in a hash-backed instance) -/
  pinOf : Cell → Ver → Option Pin
  pin_ver : ∀ (v : V) (c : Cell), pin v c = pinOf c (ver v c)
  /-- an audited step keeps a cell's version state or moves it strictly forward -/
  ver_step : ∀ (v v' : V) (c : Cell), Step v v' → ver v c = ver v' c ∨ Past (ver v c) (ver v' c)

namespace World

variable {V Fact : Type} [World V Fact]

/-- Whether a support holds at a view: read off the pin its cell holds there. -/
@[expose] def holdsAt (v : V) (f : Fact) : Bool := holdsOfPin (cell f) (pin (Fact := Fact) v (cell f)) f

/-- **The read is computed from pins** (`review/GENERATED-20261031.md` §2.4). -/
theorem holds_pin (v : V) (f : Fact) :
    holdsAt v f = holdsOfPin (cell f) (pin (Fact := Fact) v (cell f)) f := by rfl

/-- A support's truth at a view is a function of the pin its cell holds there (formerly a field). -/
theorem holds_congr (v v' : V) (f : Fact) (h : pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    holdsAt v f = holdsAt v' f := by
  unfold holdsAt; rw [h]

/-- A support of a retired cell does not hold (formerly a field). -/
theorem retired_dead (v : V) (f : Fact) (h : pin (Fact := Fact) v (cell f) = none) : holdsAt v f = false := by
  unfold holdsAt; rw [h]; exact dead_none f

/-- Views reachable by zero or more audited steps. -/
abbrev Later (v v' : V) : Prop := Reaches (World.Step (V := V) (Fact := Fact)) v v'

/-- A retired cell stays retired at every later view. -/
theorem retired_later {v v' : V} (c : World.Cell V) (h : Later (Fact := Fact) v v')
    (hr : pin (Fact := Fact) v c = none) : pin (Fact := Fact) v' c = none := by
  induction h with
  | refl => exact hr
  | tail _ step ih => exact retired_step _ _ c step ih

/-- A support whose cell is retired at a view is dead at every later view. -/
theorem dead_behind_forever {v v' : V} (f : Fact) (hr : pin (Fact := Fact) v (cell f) = none)
    (h : Later (Fact := Fact) v v') : holdsAt v' f = false :=
  retired_dead v' f (retired_later (cell f) h hr)

/-! ## The version law: a pin that moved does not come back, up to a collision -/

/-- Two version states of cell `c` that differ and read as the same pin: a collision of the pin
function among exactly these two inputs. -/
def Collides (c : World.Cell V) (a b : World.Ver V) : Prop :=
  a ≠ b ∧ pinOf (Fact := Fact) c a = pinOf (Fact := Fact) c b

/-- The pin function is injective on every cell's version states: no collision at all. -/
def Exact : Prop :=
  ∀ (c : World.Cell V) (a b : World.Ver V), pinOf (Fact := Fact) c a = pinOf (Fact := Fact) c b → a = b

/-- Along later views a cell's version state is kept or strictly past. -/
theorem ver_later {v v' : V} (c : World.Cell V) (h : Later (Fact := Fact) v v') :
    ver (Fact := Fact) v c = ver (Fact := Fact) v' c ∨
      Past (Fact := Fact) (ver (Fact := Fact) v c) (ver (Fact := Fact) v' c) := by
  induction h with
  | refl => exact .inl rfl
  | tail _ step ih =>
    rcases ih with e | p <;> rcases ver_step _ _ c step with e' | p'
    · exact .inl (e.trans e')
    · exact .inr (e ▸ p')
    · exact .inr (e' ▸ p)
    · exact .inr (past_trans _ _ _ p p')

/-- **A version state that moved never returns**: observed at `w₀`, different at a later `w`, it is
different at every view after `w`. -/
theorem ver_behind_forever {w₀ w w' : V} (c : World.Cell V) (h₁ : Later (Fact := Fact) w₀ w)
    (h₂ : Later (Fact := Fact) w w') (hne : ver (Fact := Fact) w c ≠ ver (Fact := Fact) w₀ c) :
    ver (Fact := Fact) w' c ≠ ver (Fact := Fact) w₀ c := by
  have p₁ : Past (Fact := Fact) (ver (Fact := Fact) w₀ c) (ver (Fact := Fact) w c) :=
    (ver_later c h₁).resolve_left (Ne.symm hne)
  have p : Past (Fact := Fact) (ver (Fact := Fact) w₀ c) (ver (Fact := Fact) w' c) := by
    rcases ver_later c h₂ with e | p₂
    · exact e ▸ p₁
    · exact past_trans _ _ _ p₁ p₂
  intro e
  rw [e] at p
  exact past_irrefl _ p

/-- **A pin observed at `w₀` and stale at `w` is stale for ever after `w`, or the pin function
collides on the two version states compared** (`w₀`'s and `w'`'s): nano's `stale_behind_forever`,
with retirement not a special case (a retired cell's pin is `none`, one more pin). -/
theorem stale_behind_forever {w₀ w w' : V} (c : World.Cell V) (h₁ : Later (Fact := Fact) w₀ w)
    (h₂ : Later (Fact := Fact) w w') (hstale : pin (Fact := Fact) w c ≠ pin (Fact := Fact) w₀ c) :
    pin (Fact := Fact) w' c ≠ pin (Fact := Fact) w₀ c ∨
      Collides (Fact := Fact) c (ver (Fact := Fact) w₀ c) (ver (Fact := Fact) w' c) := by
  have hne : ver (Fact := Fact) w c ≠ ver (Fact := Fact) w₀ c := fun e =>
    hstale (by rw [pin_ver, pin_ver (V := V), e])
  have hne' := ver_behind_forever c h₁ h₂ hne
  by_cases hp : pin (Fact := Fact) w' c = pin (Fact := Fact) w₀ c
  · refine .inr ⟨Ne.symm hne', ?_⟩
    rw [← pin_ver, ← pin_ver]; exact hp.symm
  · exact .inl hp

/-- The exact form: under an injective pin function the disjunct is gone. -/
theorem stale_behind_forever_exact (hx : Exact (V := V) (Fact := Fact)) {w₀ w w' : V}
    (c : World.Cell V) (h₁ : Later (Fact := Fact) w₀ w) (h₂ : Later (Fact := Fact) w w')
    (hstale : pin (Fact := Fact) w c ≠ pin (Fact := Fact) w₀ c) :
    pin (Fact := Fact) w' c ≠ pin (Fact := Fact) w₀ c :=
  (stale_behind_forever c h₁ h₂ hstale).elim id fun ⟨ne, e⟩ => absurd (hx _ _ _ e) ne

/-- A support is PINNED at `w₀` when it holds only where its cell holds the pin it holds at `w₀`:
a citation of a version (a byte cite, a row at its version, nano's pinned derivation). -/
def PinnedAt (f : Fact) (w₀ : V) : Prop :=
  ∀ v : V, holdsAt v f = true → pin (Fact := Fact) v (cell f) = pin (Fact := Fact) w₀ (cell f)

/-- **A pinned support gone stale is dead at every later view, or the pin function collides**:
`dead_behind_forever` from the version law, with no retirement special case. -/
theorem stale_dead_forever {w₀ w w' : V} (f : Fact) (hp : PinnedAt f w₀)
    (h₁ : Later (Fact := Fact) w₀ w) (h₂ : Later (Fact := Fact) w w')
    (hstale : pin (Fact := Fact) w (cell f) ≠ pin (Fact := Fact) w₀ (cell f)) :
    holdsAt w' f = false ∨
      Collides (Fact := Fact) (cell f) (ver (Fact := Fact) w₀ (cell f)) (ver (Fact := Fact) w' (cell f)) := by
  rcases stale_behind_forever (cell f) h₁ h₂ hstale with hne | hc
  · refine .inl ?_
    cases e : holdsAt w' f
    · rfl
    · exact absurd (hp w' e) hne
  · exact .inr hc

section
variable {Cand : Type}

/-- Two views agreeing on the pins of a candidate's supports agree on which of them hold. -/
theorem holds_agree (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    ∀ f ∈ S.supports c, holdsAt v f = holdsAt v' f :=
  fun f hf => holds_congr v v' f (agree f hf)

/-- The dead supports of a candidate are the same at two views agreeing on its supports' pins. -/
theorem dead_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.dead (holdsAt v) c = S.dead (holdsAt v') c := by
  unfold Slot.dead
  exact List.filter_congr fun f hf => by rw [holds_agree S c agree f hf]

/-- Whether a candidate is usable is the same at two views agreeing on its supports' pins. -/
theorem usable_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.usable (holdsAt v) c = S.usable (holdsAt v') c := by
  unfold Slot.usable
  rw [dead_congr S c agree]

/-- A derivation depends only on the pinned view: two views agreeing on the pins of a selection's
supports read it the same. -/
theorem read_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.read (holdsAt v) (some c) = S.read (holdsAt v') (some c) := by
  have ev : S.evidence (holdsAt v) c = S.evidence (holdsAt v') c := by
    unfold Slot.evidence
    exact List.map_congr_left fun f hf => by rw [holds_agree S c agree f hf]
  simp only [Slot.read]
  rw [dead_congr S c agree, ev]

/-- The usable candidates of an order are the same at two views agreeing on the pins of all their
supports. -/
theorem alternatives_congr (S : Slot Fact Cand) {v v' : V} (order : List Cand)
    (agree : ∀ c ∈ order, ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    S.alternatives (holdsAt v) order = S.alternatives (holdsAt v') order := by
  unfold Slot.alternatives
  exact List.filter_congr fun c hc => usable_congr S c (agree c hc)

/-- `permanent_blocked_forever` with retirement for `Permanent`: a selection citing a support whose
cell is retired at `v` reads blocked, by that support's name, at every later view. -/
theorem blocked_forever (S : Slot Fact Cand) {v v' : V} (c : Cand) (f : Fact) (hf : f ∈ S.supports c)
    (hr : pin (Fact := Fact) v (cell f) = none) (h : Later (Fact := Fact) v v') (hj : S.judge c = true) :
    ∃ d, S.read (holdsAt v') (some c) = .blocked c d ∧ f ∈ d := by
  have hdead : holdsAt v' f = false := dead_behind_forever f hr h
  have hmem : f ∈ S.dead (holdsAt v') c := (mem_dead_iff S _ c f).2 ⟨hf, hdead⟩
  unfold Slot.read
  simp only [hj, if_true]
  cases hd : S.dead (holdsAt v') c with
  | nil => rw [hd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hd ▸ hmem⟩

#tooth stale_behind_forever by mutation World.Collides := fun {_ _} [_] _ _ _ => False
#tooth stale_dead_forever by mutation World.PinnedAt := fun {_ _} [_] _ _ => True

/-- `blocked_forever` from the version law: a selection citing a support pinned where it was
observed, and stale since, reads blocked by that support's name at every later view, or the pin
function collides on the cell's version states. -/
theorem stale_blocked_forever (S : Slot Fact Cand) {w₀ w w' : V} (c : Cand) (f : Fact)
    (hf : f ∈ S.supports c) (hp : PinnedAt f w₀) (h₁ : Later (Fact := Fact) w₀ w)
    (h₂ : Later (Fact := Fact) w w') (hstale : pin (Fact := Fact) w (cell f) ≠ pin (Fact := Fact) w₀ (cell f))
    (hj : S.judge c = true) :
    (∃ d, S.read (holdsAt w') (some c) = .blocked c d ∧ f ∈ d) ∨
      Collides (Fact := Fact) (cell f) (ver (Fact := Fact) w₀ (cell f)) (ver (Fact := Fact) w' (cell f)) := by
  rcases stale_dead_forever f hp h₁ h₂ hstale with hdead | hc
  · refine .inl ?_
    have hmem : f ∈ S.dead (holdsAt w') c := (mem_dead_iff S _ c f).2 ⟨hf, hdead⟩
    unfold Slot.read
    simp only [hj, ite_true]
    cases hd : S.dead (holdsAt w') c with
    | nil => rw [hd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hd ▸ hmem⟩
  · exact .inr hc

end

end World

/-! ## The tooth: a pin that returns -/

namespace World.Returning

/-- Heights; one cell; the pin alternates `0, 1, 0, …`; a support is "the cell holds pin `n`". -/
def pinAt (v : Nat) : Nat := v % 2

/-- The returning world, made lawful the only way it can be: its version state is the height,
strictly increasing, and its pin a non-injective reading of it. (Local: views `Nat` belong to other
worlds elsewhere, and `Fact` is an `outParam`.) -/
@[expose, instance_reducible] def returning : World Nat Nat where
  Cell := Unit
  Pin := Nat
  cell := fun _ => ()
  pin v _ := some (pinAt v)
  holdsOfPin _ p n := match p with
    | some m => m == n
    | none => false
  Step v v' := v' = v + 1
  dead_none := fun _ => rfl
  retired_step := fun _ _ _ _ h => by cases h
  Ver := Nat
  ver v _ := v
  Past := (· < ·)
  past_irrefl := Nat.lt_irrefl
  past_trans := fun _ _ _ => Nat.lt_trans
  pinOf _ v := some (pinAt v)
  pin_ver := fun _ _ => rfl
  ver_step := fun v v' _ h => .inr (by subst h; exact Nat.lt_succ_self v)

attribute [local instance] returning

theorem later_succ (v : Nat) : Later (V := Nat) (Fact := Nat) v (v + 1) := .tail (.refl v) rfl

/-- The support "pin 0", observed at height 0, stale at 1, holds again at 2: a stale justification
comes back true, and the version law accounts for it only as the collision of heights 0 and 2. -/
theorem pin_returns :
    holdsAt (V := Nat) 0 0 = true ∧ holdsAt (V := Nat) 1 0 = false ∧ holdsAt (V := Nat) 2 0 = true ∧
      Collides (V := Nat) (Fact := Nat) () (ver (Fact := Nat) 0 ()) (ver (Fact := Nat) 2 ()) :=
  ⟨rfl, rfl, rfl, fun h => (by decide : (0 : Nat) ≠ 2) h, rfl⟩

/-- So the collision disjunct of `stale_dead_forever` is not decoration: without it the statement
is false of this world. -/
theorem collision_needed :
    ¬ ∀ (w₀ w w' : Nat) (f : Nat), PinnedAt (V := Nat) f w₀ → Later (Fact := Nat) w₀ w →
      Later (Fact := Nat) w w' →
      pin (Fact := Nat) w (cell (V := Nat) f) ≠ pin (Fact := Nat) w₀ (cell (V := Nat) f) →
      holdsAt w' f = false := by
  intro h
  have := h 0 1 2 0 (fun v hv => by
      change (pinAt v == 0) = true at hv
      change some (pinAt v) = some (pinAt 0)
      rw [beq_iff_eq.mp hv]; rfl)
    (later_succ 0) (later_succ 1) (fun h => (by decide : some (pinAt 1) ≠ some (pinAt 0)) h)
  exact absurd this (by decide : (pinAt 2 == 0) ≠ false)

/-- And no EXACT version order exists for it: with the pin as its own version state, the step from
pin 0 to pin 1 and back would put each strictly past the other. -/
theorem no_exact_order :
    ¬ ∃ Past : Option Nat → Option Nat → Prop, (∀ a, ¬ Past a a) ∧
      (∀ a b c, Past a b → Past b c → Past a c) ∧
      ∀ v : Nat, some (pinAt v) = some (pinAt (v + 1)) ∨ Past (some (pinAt v)) (some (pinAt (v + 1))) := by
  rintro ⟨P, irr, tr, st⟩
  have h0 : P (some 0) (some 1) := (st 0).resolve_left (by decide)
  have h1 : P (some 1) (some 0) := (st 1).resolve_left (by decide)
  exact irr _ (tr _ _ _ h0 h1)

end World.Returning
end Obend.Slot
end
